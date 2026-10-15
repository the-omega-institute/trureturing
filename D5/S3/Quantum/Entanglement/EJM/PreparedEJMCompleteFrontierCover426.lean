/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover425
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_10_20834_1115801 : frontier 11 ⟨1115801, by decide⟩
    (prefixCache 10 20834) (prefixPartial 10 20834) = false := by
  decide +kernel

theorem node_context_10_20834_1115801 : EJMOriginalGlobalDAGData.nodes 11 ⟨1115801, by decide⟩ =
    .split (coordinate 10) (![⟨1115450, by decide⟩,⟨1115589, by decide⟩,⟨1115682, by decide⟩,⟨1115800, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_20834_1115801 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20834 ⟨1115801, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 20834
    ⟨1115801, by decide⟩ (by decide) (![⟨1115450, by decide⟩,⟨1115589, by decide⟩,⟨1115682, by decide⟩,⟨1115800, by decide⟩]) unmarked_context_10_20834_1115801 node_context_10_20834_1115801
  intro a
  fin_cases a
  · exact context_11_83336_1115450
  · exact context_11_83337_1115589
  · exact context_11_83338_1115682
  · exact context_11_83339_1115800

theorem selected_cut_40899 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 333360) = some ⟨12, 1, 0, 1108174, 333360, 1, 65536⟩ := by
  decide +kernel

theorem context_12_333360_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333360 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 333360 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 333360, 1, 65536⟩
    (by decide) selected_cut_40899

theorem selected_cut_40900 : selected 9 ⟨1115837, by decide⟩
    (prefixPartial 12 333361) = some ⟨12, 2, 0, 1115837, 333361, 2381, 65536⟩ := by
  decide +kernel

theorem context_12_333361_1115837 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333361 ⟨1115837, by decide⟩ :=
  accepted_of_selected 12 333361 ⟨1115837, by decide⟩ ⟨12, 2, 0, 1115837, 333361, 2381, 65536⟩
    (by decide) selected_cut_40900

theorem selected_cut_40901 : selected 9 ⟨1115895, by decide⟩
    (prefixPartial 12 333362) = some ⟨12, 2, 0, 1115895, 333362, 2881, 65536⟩ := by
  decide +kernel

theorem context_12_333362_1115895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333362 ⟨1115895, by decide⟩ :=
  accepted_of_selected 12 333362 ⟨1115895, by decide⟩ ⟨12, 2, 0, 1115895, 333362, 2881, 65536⟩
    (by decide) selected_cut_40901

theorem selected_cut_40902 : selected 9 ⟨1115972, by decide⟩
    (prefixPartial 12 333363) = some ⟨12, 2, 0, 1115972, 333363, 3157, 65536⟩ := by
  decide +kernel

theorem context_12_333363_1115972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333363 ⟨1115972, by decide⟩ :=
  accepted_of_selected 12 333363 ⟨1115972, by decide⟩ ⟨12, 2, 0, 1115972, 333363, 3157, 65536⟩
    (by decide) selected_cut_40902

theorem unmarked_context_11_83340_1115973 : frontier 10 ⟨1115973, by decide⟩
    (prefixCache 11 83340) (prefixPartial 11 83340) = false := by
  decide +kernel

theorem node_context_11_83340_1115973 : EJMOriginalGlobalDAGData.nodes 10 ⟨1115973, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1115837, by decide⟩,⟨1115895, by decide⟩,⟨1115972, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83340_1115973 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83340 ⟨1115973, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83340
    ⟨1115973, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1115837, by decide⟩,⟨1115895, by decide⟩,⟨1115972, by decide⟩]) unmarked_context_11_83340_1115973 node_context_11_83340_1115973
  intro a
  fin_cases a
  · exact context_12_333360_1108174
  · exact context_12_333361_1115837
  · exact context_12_333362_1115895
  · exact context_12_333363_1115972

theorem selected_cut_40903 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 333364) = some ⟨12, 1, 0, 1108174, 333364, 1, 65536⟩ := by
  decide +kernel

theorem context_12_333364_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333364 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 333364 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 333364, 1, 65536⟩
    (by decide) selected_cut_40903

theorem selected_cut_40904 : selected 9 ⟨1116012, by decide⟩
    (prefixPartial 12 333365) = some ⟨12, 2, 0, 1116012, 333365, 2213, 65536⟩ := by
  decide +kernel

theorem context_12_333365_1116012 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333365 ⟨1116012, by decide⟩ :=
  accepted_of_selected 12 333365 ⟨1116012, by decide⟩ ⟨12, 2, 0, 1116012, 333365, 2213, 65536⟩
    (by decide) selected_cut_40904

theorem selected_cut_40905 : selected 9 ⟨1116051, by decide⟩
    (prefixPartial 12 333366) = some ⟨12, 2, 0, 1116051, 333366, 2097, 65536⟩ := by
  decide +kernel

theorem context_12_333366_1116051 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333366 ⟨1116051, by decide⟩ :=
  accepted_of_selected 12 333366 ⟨1116051, by decide⟩ ⟨12, 2, 0, 1116051, 333366, 2097, 65536⟩
    (by decide) selected_cut_40905

theorem selected_cut_40906 : selected 9 ⟨1116090, by decide⟩
    (prefixPartial 12 333367) = some ⟨12, 2, 0, 1116090, 333367, 2205, 65536⟩ := by
  decide +kernel

theorem context_12_333367_1116090 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333367 ⟨1116090, by decide⟩ :=
  accepted_of_selected 12 333367 ⟨1116090, by decide⟩ ⟨12, 2, 0, 1116090, 333367, 2205, 65536⟩
    (by decide) selected_cut_40906

theorem unmarked_context_11_83341_1116091 : frontier 10 ⟨1116091, by decide⟩
    (prefixCache 11 83341) (prefixPartial 11 83341) = false := by
  decide +kernel

theorem node_context_11_83341_1116091 : EJMOriginalGlobalDAGData.nodes 10 ⟨1116091, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1116012, by decide⟩,⟨1116051, by decide⟩,⟨1116090, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83341_1116091 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83341 ⟨1116091, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83341
    ⟨1116091, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1116012, by decide⟩,⟨1116051, by decide⟩,⟨1116090, by decide⟩]) unmarked_context_11_83341_1116091 node_context_11_83341_1116091
  intro a
  fin_cases a
  · exact context_12_333364_1108174
  · exact context_12_333365_1116012
  · exact context_12_333366_1116051
  · exact context_12_333367_1116090

theorem selected_cut_40907 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 333368) = some ⟨12, 1, 0, 1108174, 333368, 1, 65536⟩ := by
  decide +kernel

theorem context_12_333368_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333368 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 333368 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 333368, 1, 65536⟩
    (by decide) selected_cut_40907

theorem selected_cut_40908 : selected 9 ⟨1116118, by decide⟩
    (prefixPartial 12 333369) = some ⟨12, 2, 0, 1116118, 333369, 2053, 65536⟩ := by
  decide +kernel

theorem context_12_333369_1116118 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333369 ⟨1116118, by decide⟩ :=
  accepted_of_selected 12 333369 ⟨1116118, by decide⟩ ⟨12, 2, 0, 1116118, 333369, 2053, 65536⟩
    (by decide) selected_cut_40908

theorem selected_cut_40909 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 333370) = some ⟨12, 1, 0, 893903, 333370, 1, 65536⟩ := by
  decide +kernel

theorem context_12_333370_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333370 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 333370 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 333370, 1, 65536⟩
    (by decide) selected_cut_40909

theorem selected_cut_40910 : selected 9 ⟨1116184, by decide⟩
    (prefixPartial 12 333371) = some ⟨12, 2, 0, 1116184, 333371, 2913, 65536⟩ := by
  decide +kernel

theorem context_12_333371_1116184 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333371 ⟨1116184, by decide⟩ :=
  accepted_of_selected 12 333371 ⟨1116184, by decide⟩ ⟨12, 2, 0, 1116184, 333371, 2913, 65536⟩
    (by decide) selected_cut_40910

theorem unmarked_context_11_83342_1116185 : frontier 10 ⟨1116185, by decide⟩
    (prefixCache 11 83342) (prefixPartial 11 83342) = false := by
  decide +kernel

theorem node_context_11_83342_1116185 : EJMOriginalGlobalDAGData.nodes 10 ⟨1116185, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1116118, by decide⟩,⟨893903, by decide⟩,⟨1116184, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83342_1116185 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83342 ⟨1116185, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83342
    ⟨1116185, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1116118, by decide⟩,⟨893903, by decide⟩,⟨1116184, by decide⟩]) unmarked_context_11_83342_1116185 node_context_11_83342_1116185
  intro a
  fin_cases a
  · exact context_12_333368_1108174
  · exact context_12_333369_1116118
  · exact context_12_333370_893903
  · exact context_12_333371_1116184

theorem selected_cut_40911 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 333372) = some ⟨12, 1, 0, 1108174, 333372, 1, 65536⟩ := by
  decide +kernel

theorem context_12_333372_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333372 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 333372 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 333372, 1, 65536⟩
    (by decide) selected_cut_40911

theorem selected_cut_40912 : selected 9 ⟨1116206, by decide⟩
    (prefixPartial 12 333373) = some ⟨12, 2, 0, 1116206, 333373, 1901, 65536⟩ := by
  decide +kernel

theorem context_12_333373_1116206 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333373 ⟨1116206, by decide⟩ :=
  accepted_of_selected 12 333373 ⟨1116206, by decide⟩ ⟨12, 2, 0, 1116206, 333373, 1901, 65536⟩
    (by decide) selected_cut_40912

theorem selected_cut_40913 : selected 9 ⟨1116245, by decide⟩
    (prefixPartial 12 333374) = some ⟨12, 2, 0, 1116245, 333374, 2221, 65536⟩ := by
  decide +kernel

theorem context_12_333374_1116245 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333374 ⟨1116245, by decide⟩ :=
  accepted_of_selected 12 333374 ⟨1116245, by decide⟩ ⟨12, 2, 0, 1116245, 333374, 2221, 65536⟩
    (by decide) selected_cut_40913

theorem selected_cut_40914 : selected 9 ⟨1116246, by decide⟩
    (prefixPartial 12 333375) = some ⟨12, 1, 0, 1116246, 333375, 1, 65536⟩ := by
  decide +kernel

theorem context_12_333375_1116246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333375 ⟨1116246, by decide⟩ :=
  accepted_of_selected 12 333375 ⟨1116246, by decide⟩ ⟨12, 1, 0, 1116246, 333375, 1, 65536⟩
    (by decide) selected_cut_40914

theorem unmarked_context_11_83343_1116247 : frontier 10 ⟨1116247, by decide⟩
    (prefixCache 11 83343) (prefixPartial 11 83343) = false := by
  decide +kernel

theorem node_context_11_83343_1116247 : EJMOriginalGlobalDAGData.nodes 10 ⟨1116247, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1116206, by decide⟩,⟨1116245, by decide⟩,⟨1116246, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83343_1116247 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83343 ⟨1116247, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83343
    ⟨1116247, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1116206, by decide⟩,⟨1116245, by decide⟩,⟨1116246, by decide⟩]) unmarked_context_11_83343_1116247 node_context_11_83343_1116247
  intro a
  fin_cases a
  · exact context_12_333372_1108174
  · exact context_12_333373_1116206
  · exact context_12_333374_1116245
  · exact context_12_333375_1116246

theorem unmarked_context_10_20835_1116248 : frontier 11 ⟨1116248, by decide⟩
    (prefixCache 10 20835) (prefixPartial 10 20835) = false := by
  decide +kernel

theorem node_context_10_20835_1116248 : EJMOriginalGlobalDAGData.nodes 11 ⟨1116248, by decide⟩ =
    .split (coordinate 10) (![⟨1115973, by decide⟩,⟨1116091, by decide⟩,⟨1116185, by decide⟩,⟨1116247, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_20835_1116248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20835 ⟨1116248, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 20835
    ⟨1116248, by decide⟩ (by decide) (![⟨1115973, by decide⟩,⟨1116091, by decide⟩,⟨1116185, by decide⟩,⟨1116247, by decide⟩]) unmarked_context_10_20835_1116248 node_context_10_20835_1116248
  intro a
  fin_cases a
  · exact context_11_83340_1115973
  · exact context_11_83341_1116091
  · exact context_11_83342_1116185
  · exact context_11_83343_1116247

theorem unmarked_context_9_5208_1116249 : frontier 12 ⟨1116249, by decide⟩
    (prefixCache 9 5208) (prefixPartial 9 5208) = false := by
  decide +kernel

theorem node_context_9_5208_1116249 : EJMOriginalGlobalDAGData.nodes 12 ⟨1116249, by decide⟩ =
    .split (coordinate 9) (![⟨1114940, by decide⟩,⟨1115269, by decide⟩,⟨1115801, by decide⟩,⟨1116248, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5208_1116249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5208 ⟨1116249, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5208
    ⟨1116249, by decide⟩ (by decide) (![⟨1114940, by decide⟩,⟨1115269, by decide⟩,⟨1115801, by decide⟩,⟨1116248, by decide⟩]) unmarked_context_9_5208_1116249 node_context_9_5208_1116249
  intro a
  fin_cases a
  · exact context_10_20832_1114940
  · exact context_10_20833_1115269
  · exact context_10_20834_1115801
  · exact context_10_20835_1116248

theorem selected_cut_40915 : selected 9 ⟨1113480, by decide⟩
    (prefixPartial 12 333376) = some ⟨12, 1, 0, 1113480, 333376, 1, 65536⟩ := by
  decide +kernel

theorem context_12_333376_1113480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333376 ⟨1113480, by decide⟩ :=
  accepted_of_selected 12 333376 ⟨1113480, by decide⟩ ⟨12, 1, 0, 1113480, 333376, 1, 65536⟩
    (by decide) selected_cut_40915

theorem selected_cut_40916 : selected 9 ⟨1116280, by decide⟩
    (prefixPartial 12 333377) = some ⟨12, 2, 0, 1116280, 333377, 2033, 65536⟩ := by
  decide +kernel

theorem context_12_333377_1116280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333377 ⟨1116280, by decide⟩ :=
  accepted_of_selected 12 333377 ⟨1116280, by decide⟩ ⟨12, 2, 0, 1116280, 333377, 2033, 65536⟩
    (by decide) selected_cut_40916

theorem selected_cut_40917 : selected 9 ⟨1116330, by decide⟩
    (prefixPartial 12 333378) = some ⟨12, 2, 0, 1116330, 333378, 2481, 65536⟩ := by
  decide +kernel

theorem context_12_333378_1116330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333378 ⟨1116330, by decide⟩ :=
  accepted_of_selected 12 333378 ⟨1116330, by decide⟩ ⟨12, 2, 0, 1116330, 333378, 2481, 65536⟩
    (by decide) selected_cut_40917

theorem selected_cut_40918 : selected 9 ⟨1116378, by decide⟩
    (prefixPartial 12 333379) = some ⟨12, 2, 0, 1116378, 333379, 2505, 65536⟩ := by
  decide +kernel

theorem context_12_333379_1116378 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333379 ⟨1116378, by decide⟩ :=
  accepted_of_selected 12 333379 ⟨1116378, by decide⟩ ⟨12, 2, 0, 1116378, 333379, 2505, 65536⟩
    (by decide) selected_cut_40918

theorem unmarked_context_11_83344_1116379 : frontier 10 ⟨1116379, by decide⟩
    (prefixCache 11 83344) (prefixPartial 11 83344) = false := by
  decide +kernel

theorem node_context_11_83344_1116379 : EJMOriginalGlobalDAGData.nodes 10 ⟨1116379, by decide⟩ =
    .split (coordinate 11) (![⟨1113480, by decide⟩,⟨1116280, by decide⟩,⟨1116330, by decide⟩,⟨1116378, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83344_1116379 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83344 ⟨1116379, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83344
    ⟨1116379, by decide⟩ (by decide) (![⟨1113480, by decide⟩,⟨1116280, by decide⟩,⟨1116330, by decide⟩,⟨1116378, by decide⟩]) unmarked_context_11_83344_1116379 node_context_11_83344_1116379
  intro a
  fin_cases a
  · exact context_12_333376_1113480
  · exact context_12_333377_1116280
  · exact context_12_333378_1116330
  · exact context_12_333379_1116378

theorem selected_cut_40919 : selected 9 ⟨1116406, by decide⟩
    (prefixPartial 12 333380) = some ⟨12, 2, 0, 1116406, 333380, 1613, 65536⟩ := by
  decide +kernel

theorem context_12_333380_1116406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333380 ⟨1116406, by decide⟩ :=
  accepted_of_selected 12 333380 ⟨1116406, by decide⟩ ⟨12, 2, 0, 1116406, 333380, 1613, 65536⟩
    (by decide) selected_cut_40919

theorem selected_cut_40920 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 333381) = some ⟨12, 1, 0, 170504, 333381, 1, 65536⟩ := by
  decide +kernel

theorem context_12_333381_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333381 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 333381 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 333381, 1, 65536⟩
    (by decide) selected_cut_40920

theorem selected_cut_40921 : selected 9 ⟨1116451, by decide⟩
    (prefixPartial 12 333382) = some ⟨12, 2, 0, 1116451, 333382, 1953, 65536⟩ := by
  decide +kernel

theorem context_12_333382_1116451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333382 ⟨1116451, by decide⟩ :=
  accepted_of_selected 12 333382 ⟨1116451, by decide⟩ ⟨12, 2, 0, 1116451, 333382, 1953, 65536⟩
    (by decide) selected_cut_40921

theorem selected_cut_40922 : selected 9 ⟨1116484, by decide⟩
    (prefixPartial 12 333383) = some ⟨12, 2, 0, 1116484, 333383, 1913, 65536⟩ := by
  decide +kernel

theorem context_12_333383_1116484 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333383 ⟨1116484, by decide⟩ :=
  accepted_of_selected 12 333383 ⟨1116484, by decide⟩ ⟨12, 2, 0, 1116484, 333383, 1913, 65536⟩
    (by decide) selected_cut_40922

theorem unmarked_context_11_83345_1116485 : frontier 10 ⟨1116485, by decide⟩
    (prefixCache 11 83345) (prefixPartial 11 83345) = false := by
  decide +kernel

theorem node_context_11_83345_1116485 : EJMOriginalGlobalDAGData.nodes 10 ⟨1116485, by decide⟩ =
    .split (coordinate 11) (![⟨1116406, by decide⟩,⟨170504, by decide⟩,⟨1116451, by decide⟩,⟨1116484, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83345_1116485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83345 ⟨1116485, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83345
    ⟨1116485, by decide⟩ (by decide) (![⟨1116406, by decide⟩,⟨170504, by decide⟩,⟨1116451, by decide⟩,⟨1116484, by decide⟩]) unmarked_context_11_83345_1116485 node_context_11_83345_1116485
  intro a
  fin_cases a
  · exact context_12_333380_1116406
  · exact context_12_333381_170504
  · exact context_12_333382_1116451
  · exact context_12_333383_1116484

theorem selected_cut_40923 : selected 9 ⟨1116516, by decide⟩
    (prefixPartial 12 333384) = some ⟨12, 2, 0, 1116516, 333384, 1937, 65536⟩ := by
  decide +kernel

theorem context_12_333384_1116516 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333384 ⟨1116516, by decide⟩ :=
  accepted_of_selected 12 333384 ⟨1116516, by decide⟩ ⟨12, 2, 0, 1116516, 333384, 1937, 65536⟩
    (by decide) selected_cut_40923

theorem selected_cut_40924 : selected 9 ⟨1116538, by decide⟩
    (prefixPartial 12 333385) = some ⟨12, 2, 0, 1116538, 333385, 1837, 65536⟩ := by
  decide +kernel

theorem context_12_333385_1116538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333385 ⟨1116538, by decide⟩ :=
  accepted_of_selected 12 333385 ⟨1116538, by decide⟩ ⟨12, 2, 0, 1116538, 333385, 1837, 65536⟩
    (by decide) selected_cut_40924

theorem selected_cut_40925 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 333386) = some ⟨12, 1, 0, 893903, 333386, 1, 65536⟩ := by
  decide +kernel

theorem context_12_333386_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333386 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 333386 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 333386, 1, 65536⟩
    (by decide) selected_cut_40925

theorem selected_cut_40926 : selected 9 ⟨1116580, by decide⟩
    (prefixPartial 12 333387) = some ⟨12, 2, 0, 1116580, 333387, 2333, 65536⟩ := by
  decide +kernel

theorem context_12_333387_1116580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333387 ⟨1116580, by decide⟩ :=
  accepted_of_selected 12 333387 ⟨1116580, by decide⟩ ⟨12, 2, 0, 1116580, 333387, 2333, 65536⟩
    (by decide) selected_cut_40926

theorem unmarked_context_11_83346_1116581 : frontier 10 ⟨1116581, by decide⟩
    (prefixCache 11 83346) (prefixPartial 11 83346) = false := by
  decide +kernel

theorem node_context_11_83346_1116581 : EJMOriginalGlobalDAGData.nodes 10 ⟨1116581, by decide⟩ =
    .split (coordinate 11) (![⟨1116516, by decide⟩,⟨1116538, by decide⟩,⟨893903, by decide⟩,⟨1116580, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83346_1116581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83346 ⟨1116581, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83346
    ⟨1116581, by decide⟩ (by decide) (![⟨1116516, by decide⟩,⟨1116538, by decide⟩,⟨893903, by decide⟩,⟨1116580, by decide⟩]) unmarked_context_11_83346_1116581 node_context_11_83346_1116581
  intro a
  fin_cases a
  · exact context_12_333384_1116516
  · exact context_12_333385_1116538
  · exact context_12_333386_893903
  · exact context_12_333387_1116580

theorem selected_cut_40927 : selected 9 ⟨1116614, by decide⟩
    (prefixPartial 12 333388) = some ⟨12, 2, 0, 1116614, 333388, 2049, 65536⟩ := by
  decide +kernel

theorem context_12_333388_1116614 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333388 ⟨1116614, by decide⟩ :=
  accepted_of_selected 12 333388 ⟨1116614, by decide⟩ ⟨12, 2, 0, 1116614, 333388, 2049, 65536⟩
    (by decide) selected_cut_40927

theorem selected_cut_40928 : selected 9 ⟨1116645, by decide⟩
    (prefixPartial 12 333389) = some ⟨12, 2, 0, 1116645, 333389, 1957, 65536⟩ := by
  decide +kernel

theorem context_12_333389_1116645 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333389 ⟨1116645, by decide⟩ :=
  accepted_of_selected 12 333389 ⟨1116645, by decide⟩ ⟨12, 2, 0, 1116645, 333389, 1957, 65536⟩
    (by decide) selected_cut_40928

theorem selected_cut_40929 : selected 9 ⟨1116705, by decide⟩
    (prefixPartial 12 333390) = some ⟨12, 2, 0, 1116705, 333390, 2465, 65536⟩ := by
  decide +kernel

theorem context_12_333390_1116705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333390 ⟨1116705, by decide⟩ :=
  accepted_of_selected 12 333390 ⟨1116705, by decide⟩ ⟨12, 2, 0, 1116705, 333390, 2465, 65536⟩
    (by decide) selected_cut_40929

theorem selected_cut_40930 : selected 9 ⟨1116734, by decide⟩
    (prefixPartial 12 333391) = some ⟨12, 2, 0, 1116734, 333391, 2137, 65536⟩ := by
  decide +kernel

theorem context_12_333391_1116734 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333391 ⟨1116734, by decide⟩ :=
  accepted_of_selected 12 333391 ⟨1116734, by decide⟩ ⟨12, 2, 0, 1116734, 333391, 2137, 65536⟩
    (by decide) selected_cut_40930

theorem unmarked_context_11_83347_1116735 : frontier 10 ⟨1116735, by decide⟩
    (prefixCache 11 83347) (prefixPartial 11 83347) = false := by
  decide +kernel

theorem node_context_11_83347_1116735 : EJMOriginalGlobalDAGData.nodes 10 ⟨1116735, by decide⟩ =
    .split (coordinate 11) (![⟨1116614, by decide⟩,⟨1116645, by decide⟩,⟨1116705, by decide⟩,⟨1116734, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83347_1116735 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83347 ⟨1116735, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83347
    ⟨1116735, by decide⟩ (by decide) (![⟨1116614, by decide⟩,⟨1116645, by decide⟩,⟨1116705, by decide⟩,⟨1116734, by decide⟩]) unmarked_context_11_83347_1116735 node_context_11_83347_1116735
  intro a
  fin_cases a
  · exact context_12_333388_1116614
  · exact context_12_333389_1116645
  · exact context_12_333390_1116705
  · exact context_12_333391_1116734

theorem unmarked_context_10_20836_1116736 : frontier 11 ⟨1116736, by decide⟩
    (prefixCache 10 20836) (prefixPartial 10 20836) = false := by
  decide +kernel

theorem node_context_10_20836_1116736 : EJMOriginalGlobalDAGData.nodes 11 ⟨1116736, by decide⟩ =
    .split (coordinate 10) (![⟨1116379, by decide⟩,⟨1116485, by decide⟩,⟨1116581, by decide⟩,⟨1116735, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_20836_1116736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20836 ⟨1116736, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 20836
    ⟨1116736, by decide⟩ (by decide) (![⟨1116379, by decide⟩,⟨1116485, by decide⟩,⟨1116581, by decide⟩,⟨1116735, by decide⟩]) unmarked_context_10_20836_1116736 node_context_10_20836_1116736
  intro a
  fin_cases a
  · exact context_11_83344_1116379
  · exact context_11_83345_1116485
  · exact context_11_83346_1116581
  · exact context_11_83347_1116735

theorem selected_cut_40931 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 20837) = some ⟨10, 1, 0, 893098, 20837, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_20837_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20837 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 20837 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 20837, 1, 1048576⟩
    (by decide) selected_cut_40931

theorem selected_cut_40932 : selected 9 ⟨1116774, by decide⟩
    (prefixPartial 12 333408) = some ⟨12, 2, 0, 1116774, 333408, 1973, 65536⟩ := by
  decide +kernel

theorem context_12_333408_1116774 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333408 ⟨1116774, by decide⟩ :=
  accepted_of_selected 12 333408 ⟨1116774, by decide⟩ ⟨12, 2, 0, 1116774, 333408, 1973, 65536⟩
    (by decide) selected_cut_40932

theorem selected_cut_40933 : selected 9 ⟨1116804, by decide⟩
    (prefixPartial 12 333409) = some ⟨12, 2, 0, 1116804, 333409, 1985, 65536⟩ := by
  decide +kernel

theorem context_12_333409_1116804 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333409 ⟨1116804, by decide⟩ :=
  accepted_of_selected 12 333409 ⟨1116804, by decide⟩ ⟨12, 2, 0, 1116804, 333409, 1985, 65536⟩
    (by decide) selected_cut_40933

theorem selected_cut_40934 : selected 9 ⟨1116849, by decide⟩
    (prefixPartial 12 333410) = some ⟨12, 2, 0, 1116849, 333410, 2309, 65536⟩ := by
  decide +kernel

theorem context_12_333410_1116849 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333410 ⟨1116849, by decide⟩ :=
  accepted_of_selected 12 333410 ⟨1116849, by decide⟩ ⟨12, 2, 0, 1116849, 333410, 2309, 65536⟩
    (by decide) selected_cut_40934

theorem selected_cut_40935 : selected 9 ⟨1116897, by decide⟩
    (prefixPartial 12 333411) = some ⟨12, 2, 0, 1116897, 333411, 2465, 65536⟩ := by
  decide +kernel

theorem context_12_333411_1116897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333411 ⟨1116897, by decide⟩ :=
  accepted_of_selected 12 333411 ⟨1116897, by decide⟩ ⟨12, 2, 0, 1116897, 333411, 2465, 65536⟩
    (by decide) selected_cut_40935

theorem unmarked_context_11_83352_1116898 : frontier 10 ⟨1116898, by decide⟩
    (prefixCache 11 83352) (prefixPartial 11 83352) = false := by
  decide +kernel

theorem node_context_11_83352_1116898 : EJMOriginalGlobalDAGData.nodes 10 ⟨1116898, by decide⟩ =
    .split (coordinate 11) (![⟨1116774, by decide⟩,⟨1116804, by decide⟩,⟨1116849, by decide⟩,⟨1116897, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83352_1116898 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83352 ⟨1116898, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83352
    ⟨1116898, by decide⟩ (by decide) (![⟨1116774, by decide⟩,⟨1116804, by decide⟩,⟨1116849, by decide⟩,⟨1116897, by decide⟩]) unmarked_context_11_83352_1116898 node_context_11_83352_1116898
  intro a
  fin_cases a
  · exact context_12_333408_1116774
  · exact context_12_333409_1116804
  · exact context_12_333410_1116849
  · exact context_12_333411_1116897

theorem selected_cut_40936 : selected 9 ⟨1116920, by decide⟩
    (prefixPartial 12 333412) = some ⟨12, 2, 0, 1116920, 333412, 1605, 65536⟩ := by
  decide +kernel

theorem context_12_333412_1116920 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333412 ⟨1116920, by decide⟩ :=
  accepted_of_selected 12 333412 ⟨1116920, by decide⟩ ⟨12, 2, 0, 1116920, 333412, 1605, 65536⟩
    (by decide) selected_cut_40936

theorem selected_cut_40937 : selected 9 ⟨365907, by decide⟩
    (prefixPartial 12 333413) = some ⟨12, 1, 0, 365907, 333413, 1, 65536⟩ := by
  decide +kernel

theorem context_12_333413_365907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333413 ⟨365907, by decide⟩ :=
  accepted_of_selected 12 333413 ⟨365907, by decide⟩ ⟨12, 1, 0, 365907, 333413, 1, 65536⟩
    (by decide) selected_cut_40937

theorem selected_cut_40938 : selected 9 ⟨1116951, by decide⟩
    (prefixPartial 12 333414) = some ⟨12, 2, 0, 1116951, 333414, 1725, 65536⟩ := by
  decide +kernel

theorem context_12_333414_1116951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333414 ⟨1116951, by decide⟩ :=
  accepted_of_selected 12 333414 ⟨1116951, by decide⟩ ⟨12, 2, 0, 1116951, 333414, 1725, 65536⟩
    (by decide) selected_cut_40938

theorem selected_cut_40939 : selected 9 ⟨1116976, by decide⟩
    (prefixPartial 12 333415) = some ⟨12, 2, 0, 1116976, 333415, 1737, 65536⟩ := by
  decide +kernel

theorem context_12_333415_1116976 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333415 ⟨1116976, by decide⟩ :=
  accepted_of_selected 12 333415 ⟨1116976, by decide⟩ ⟨12, 2, 0, 1116976, 333415, 1737, 65536⟩
    (by decide) selected_cut_40939

theorem unmarked_context_11_83353_1116977 : frontier 10 ⟨1116977, by decide⟩
    (prefixCache 11 83353) (prefixPartial 11 83353) = false := by
  decide +kernel

theorem node_context_11_83353_1116977 : EJMOriginalGlobalDAGData.nodes 10 ⟨1116977, by decide⟩ =
    .split (coordinate 11) (![⟨1116920, by decide⟩,⟨365907, by decide⟩,⟨1116951, by decide⟩,⟨1116976, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83353_1116977 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83353 ⟨1116977, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83353
    ⟨1116977, by decide⟩ (by decide) (![⟨1116920, by decide⟩,⟨365907, by decide⟩,⟨1116951, by decide⟩,⟨1116976, by decide⟩]) unmarked_context_11_83353_1116977 node_context_11_83353_1116977
  intro a
  fin_cases a
  · exact context_12_333412_1116920
  · exact context_12_333413_365907
  · exact context_12_333414_1116951
  · exact context_12_333415_1116976

theorem selected_cut_40940 : selected 9 ⟨1117009, by decide⟩
    (prefixPartial 12 333416) = some ⟨12, 2, 0, 1117009, 333416, 1873, 65536⟩ := by
  decide +kernel

theorem context_12_333416_1117009 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333416 ⟨1117009, by decide⟩ :=
  accepted_of_selected 12 333416 ⟨1117009, by decide⟩ ⟨12, 2, 0, 1117009, 333416, 1873, 65536⟩
    (by decide) selected_cut_40940

theorem selected_cut_40941 : selected 9 ⟨1117057, by decide⟩
    (prefixPartial 12 333417) = some ⟨12, 2, 0, 1117057, 333417, 773, 65536⟩ := by
  decide +kernel

theorem context_12_333417_1117057 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333417 ⟨1117057, by decide⟩ :=
  accepted_of_selected 12 333417 ⟨1117057, by decide⟩ ⟨12, 2, 0, 1117057, 333417, 773, 65536⟩
    (by decide) selected_cut_40941

theorem selected_cut_40942 : selected 9 ⟨1113261, by decide⟩
    (prefixPartial 12 333418) = some ⟨12, 1, 0, 1113261, 333418, 1, 65536⟩ := by
  decide +kernel

theorem context_12_333418_1113261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333418 ⟨1113261, by decide⟩ :=
  accepted_of_selected 12 333418 ⟨1113261, by decide⟩ ⟨12, 1, 0, 1113261, 333418, 1, 65536⟩
    (by decide) selected_cut_40942

theorem selected_cut_40943 : selected 9 ⟨1117099, by decide⟩
    (prefixPartial 12 333419) = some ⟨12, 2, 0, 1117099, 333419, 2249, 65536⟩ := by
  decide +kernel

theorem context_12_333419_1117099 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333419 ⟨1117099, by decide⟩ :=
  accepted_of_selected 12 333419 ⟨1117099, by decide⟩ ⟨12, 2, 0, 1117099, 333419, 2249, 65536⟩
    (by decide) selected_cut_40943

theorem unmarked_context_11_83354_1117100 : frontier 10 ⟨1117100, by decide⟩
    (prefixCache 11 83354) (prefixPartial 11 83354) = false := by
  decide +kernel

theorem node_context_11_83354_1117100 : EJMOriginalGlobalDAGData.nodes 10 ⟨1117100, by decide⟩ =
    .split (coordinate 11) (![⟨1117009, by decide⟩,⟨1117057, by decide⟩,⟨1113261, by decide⟩,⟨1117099, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83354_1117100 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83354 ⟨1117100, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83354
    ⟨1117100, by decide⟩ (by decide) (![⟨1117009, by decide⟩,⟨1117057, by decide⟩,⟨1113261, by decide⟩,⟨1117099, by decide⟩]) unmarked_context_11_83354_1117100 node_context_11_83354_1117100
  intro a
  fin_cases a
  · exact context_12_333416_1117009
  · exact context_12_333417_1117057
  · exact context_12_333418_1113261
  · exact context_12_333419_1117099

theorem selected_cut_40944 : selected 9 ⟨1117134, by decide⟩
    (prefixPartial 12 333420) = some ⟨12, 2, 0, 1117134, 333420, 1993, 65536⟩ := by
  decide +kernel

theorem context_12_333420_1117134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333420 ⟨1117134, by decide⟩ :=
  accepted_of_selected 12 333420 ⟨1117134, by decide⟩ ⟨12, 2, 0, 1117134, 333420, 1993, 65536⟩
    (by decide) selected_cut_40944

theorem selected_cut_40945 : selected 9 ⟨1117157, by decide⟩
    (prefixPartial 12 333421) = some ⟨12, 2, 0, 1117157, 333421, 1721, 65536⟩ := by
  decide +kernel

theorem context_12_333421_1117157 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333421 ⟨1117157, by decide⟩ :=
  accepted_of_selected 12 333421 ⟨1117157, by decide⟩ ⟨12, 2, 0, 1117157, 333421, 1721, 65536⟩
    (by decide) selected_cut_40945

theorem selected_cut_40946 : selected 9 ⟨1117191, by decide⟩
    (prefixPartial 12 333422) = some ⟨12, 2, 0, 1117191, 333422, 2153, 65536⟩ := by
  decide +kernel

theorem context_12_333422_1117191 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333422 ⟨1117191, by decide⟩ :=
  accepted_of_selected 12 333422 ⟨1117191, by decide⟩ ⟨12, 2, 0, 1117191, 333422, 2153, 65536⟩
    (by decide) selected_cut_40946

theorem selected_cut_40947 : selected 9 ⟨1117223, by decide⟩
    (prefixPartial 12 333423) = some ⟨12, 2, 0, 1117223, 333423, 1909, 65536⟩ := by
  decide +kernel

theorem context_12_333423_1117223 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333423 ⟨1117223, by decide⟩ :=
  accepted_of_selected 12 333423 ⟨1117223, by decide⟩ ⟨12, 2, 0, 1117223, 333423, 1909, 65536⟩
    (by decide) selected_cut_40947

theorem unmarked_context_11_83355_1117224 : frontier 10 ⟨1117224, by decide⟩
    (prefixCache 11 83355) (prefixPartial 11 83355) = false := by
  decide +kernel

theorem node_context_11_83355_1117224 : EJMOriginalGlobalDAGData.nodes 10 ⟨1117224, by decide⟩ =
    .split (coordinate 11) (![⟨1117134, by decide⟩,⟨1117157, by decide⟩,⟨1117191, by decide⟩,⟨1117223, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83355_1117224 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83355 ⟨1117224, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83355
    ⟨1117224, by decide⟩ (by decide) (![⟨1117134, by decide⟩,⟨1117157, by decide⟩,⟨1117191, by decide⟩,⟨1117223, by decide⟩]) unmarked_context_11_83355_1117224 node_context_11_83355_1117224
  intro a
  fin_cases a
  · exact context_12_333420_1117134
  · exact context_12_333421_1117157
  · exact context_12_333422_1117191
  · exact context_12_333423_1117223

theorem unmarked_context_10_20838_1117225 : frontier 11 ⟨1117225, by decide⟩
    (prefixCache 10 20838) (prefixPartial 10 20838) = false := by
  decide +kernel

theorem node_context_10_20838_1117225 : EJMOriginalGlobalDAGData.nodes 11 ⟨1117225, by decide⟩ =
    .split (coordinate 10) (![⟨1116898, by decide⟩,⟨1116977, by decide⟩,⟨1117100, by decide⟩,⟨1117224, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_20838_1117225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20838 ⟨1117225, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 20838
    ⟨1117225, by decide⟩ (by decide) (![⟨1116898, by decide⟩,⟨1116977, by decide⟩,⟨1117100, by decide⟩,⟨1117224, by decide⟩]) unmarked_context_10_20838_1117225 node_context_10_20838_1117225
  intro a
  fin_cases a
  · exact context_11_83352_1116898
  · exact context_11_83353_1116977
  · exact context_11_83354_1117100
  · exact context_11_83355_1117224

theorem selected_cut_40948 : selected 9 ⟨1117246, by decide⟩
    (prefixPartial 12 333424) = some ⟨12, 2, 0, 1117246, 333424, 1449, 65536⟩ := by
  decide +kernel

theorem context_12_333424_1117246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333424 ⟨1117246, by decide⟩ :=
  accepted_of_selected 12 333424 ⟨1117246, by decide⟩ ⟨12, 2, 0, 1117246, 333424, 1449, 65536⟩
    (by decide) selected_cut_40948

theorem selected_cut_40949 : selected 9 ⟨1117259, by decide⟩
    (prefixPartial 12 333425) = some ⟨12, 2, 0, 1117259, 333425, 1485, 65536⟩ := by
  decide +kernel

theorem context_12_333425_1117259 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333425 ⟨1117259, by decide⟩ :=
  accepted_of_selected 12 333425 ⟨1117259, by decide⟩ ⟨12, 2, 0, 1117259, 333425, 1485, 65536⟩
    (by decide) selected_cut_40949

theorem selected_cut_40950 : selected 9 ⟨1117285, by decide⟩
    (prefixPartial 12 333426) = some ⟨12, 2, 0, 1117285, 333426, 1549, 65536⟩ := by
  decide +kernel

theorem context_12_333426_1117285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333426 ⟨1117285, by decide⟩ :=
  accepted_of_selected 12 333426 ⟨1117285, by decide⟩ ⟨12, 2, 0, 1117285, 333426, 1549, 65536⟩
    (by decide) selected_cut_40950

theorem selected_cut_40951 : selected 9 ⟨1117320, by decide⟩
    (prefixPartial 12 333427) = some ⟨12, 2, 0, 1117320, 333427, 1837, 65536⟩ := by
  decide +kernel

theorem context_12_333427_1117320 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333427 ⟨1117320, by decide⟩ :=
  accepted_of_selected 12 333427 ⟨1117320, by decide⟩ ⟨12, 2, 0, 1117320, 333427, 1837, 65536⟩
    (by decide) selected_cut_40951

theorem unmarked_context_11_83356_1117321 : frontier 10 ⟨1117321, by decide⟩
    (prefixCache 11 83356) (prefixPartial 11 83356) = false := by
  decide +kernel

theorem node_context_11_83356_1117321 : EJMOriginalGlobalDAGData.nodes 10 ⟨1117321, by decide⟩ =
    .split (coordinate 11) (![⟨1117246, by decide⟩,⟨1117259, by decide⟩,⟨1117285, by decide⟩,⟨1117320, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83356_1117321 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83356 ⟨1117321, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83356
    ⟨1117321, by decide⟩ (by decide) (![⟨1117246, by decide⟩,⟨1117259, by decide⟩,⟨1117285, by decide⟩,⟨1117320, by decide⟩]) unmarked_context_11_83356_1117321 node_context_11_83356_1117321
  intro a
  fin_cases a
  · exact context_12_333424_1117246
  · exact context_12_333425_1117259
  · exact context_12_333426_1117285
  · exact context_12_333427_1117320

theorem selected_cut_40952 : selected 10 ⟨1117372, by decide⟩
    (prefixPartial 11 83357) = some ⟨11, 2, 0, 1117372, 83357, 3765, 262144⟩ := by
  decide +kernel

theorem context_11_83357_1117372 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83357 ⟨1117372, by decide⟩ :=
  accepted_of_selected 11 83357 ⟨1117372, by decide⟩ ⟨11, 2, 0, 1117372, 83357, 3765, 262144⟩
    (by decide) selected_cut_40952

theorem selected_cut_40953 : selected 9 ⟨1117396, by decide⟩
    (prefixPartial 12 333432) = some ⟨12, 2, 0, 1117396, 333432, 1505, 65536⟩ := by
  decide +kernel

theorem context_12_333432_1117396 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333432 ⟨1117396, by decide⟩ :=
  accepted_of_selected 12 333432 ⟨1117396, by decide⟩ ⟨12, 2, 0, 1117396, 333432, 1505, 65536⟩
    (by decide) selected_cut_40953

theorem selected_cut_40954 : selected 9 ⟨1117414, by decide⟩
    (prefixPartial 12 333433) = some ⟨12, 2, 0, 1117414, 333433, 1337, 65536⟩ := by
  decide +kernel

theorem context_12_333433_1117414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333433 ⟨1117414, by decide⟩ :=
  accepted_of_selected 12 333433 ⟨1117414, by decide⟩ ⟨12, 2, 0, 1117414, 333433, 1337, 65536⟩
    (by decide) selected_cut_40954

theorem selected_cut_40955 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 333434) = some ⟨12, 1, 0, 893903, 333434, 1, 65536⟩ := by
  decide +kernel

theorem context_12_333434_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333434 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 333434 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 333434, 1, 65536⟩
    (by decide) selected_cut_40955

theorem selected_cut_40956 : selected 9 ⟨1117445, by decide⟩
    (prefixPartial 12 333435) = some ⟨12, 2, 0, 1117445, 333435, 1773, 65536⟩ := by
  decide +kernel

theorem context_12_333435_1117445 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333435 ⟨1117445, by decide⟩ :=
  accepted_of_selected 12 333435 ⟨1117445, by decide⟩ ⟨12, 2, 0, 1117445, 333435, 1773, 65536⟩
    (by decide) selected_cut_40956

theorem unmarked_context_11_83358_1117446 : frontier 10 ⟨1117446, by decide⟩
    (prefixCache 11 83358) (prefixPartial 11 83358) = false := by
  decide +kernel

theorem node_context_11_83358_1117446 : EJMOriginalGlobalDAGData.nodes 10 ⟨1117446, by decide⟩ =
    .split (coordinate 11) (![⟨1117396, by decide⟩,⟨1117414, by decide⟩,⟨893903, by decide⟩,⟨1117445, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83358_1117446 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83358 ⟨1117446, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83358
    ⟨1117446, by decide⟩ (by decide) (![⟨1117396, by decide⟩,⟨1117414, by decide⟩,⟨893903, by decide⟩,⟨1117445, by decide⟩]) unmarked_context_11_83358_1117446 node_context_11_83358_1117446
  intro a
  fin_cases a
  · exact context_12_333432_1117396
  · exact context_12_333433_1117414
  · exact context_12_333434_893903
  · exact context_12_333435_1117445

theorem selected_cut_40957 : selected 10 ⟨1117507, by decide⟩
    (prefixPartial 11 83359) = some ⟨11, 2, 0, 1117507, 83359, 3969, 262144⟩ := by
  decide +kernel

theorem context_11_83359_1117507 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83359 ⟨1117507, by decide⟩ :=
  accepted_of_selected 11 83359 ⟨1117507, by decide⟩ ⟨11, 2, 0, 1117507, 83359, 3969, 262144⟩
    (by decide) selected_cut_40957

theorem unmarked_context_10_20839_1117508 : frontier 11 ⟨1117508, by decide⟩
    (prefixCache 10 20839) (prefixPartial 10 20839) = false := by
  decide +kernel

theorem node_context_10_20839_1117508 : EJMOriginalGlobalDAGData.nodes 11 ⟨1117508, by decide⟩ =
    .split (coordinate 10) (![⟨1117321, by decide⟩,⟨1117372, by decide⟩,⟨1117446, by decide⟩,⟨1117507, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_20839_1117508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20839 ⟨1117508, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 20839
    ⟨1117508, by decide⟩ (by decide) (![⟨1117321, by decide⟩,⟨1117372, by decide⟩,⟨1117446, by decide⟩,⟨1117507, by decide⟩]) unmarked_context_10_20839_1117508 node_context_10_20839_1117508
  intro a
  fin_cases a
  · exact context_11_83356_1117321
  · exact context_11_83357_1117372
  · exact context_11_83358_1117446
  · exact context_11_83359_1117507

theorem unmarked_context_9_5209_1117509 : frontier 12 ⟨1117509, by decide⟩
    (prefixCache 9 5209) (prefixPartial 9 5209) = false := by
  decide +kernel

theorem node_context_9_5209_1117509 : EJMOriginalGlobalDAGData.nodes 12 ⟨1117509, by decide⟩ =
    .split (coordinate 9) (![⟨1116736, by decide⟩,⟨893098, by decide⟩,⟨1117225, by decide⟩,⟨1117508, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5209_1117509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5209 ⟨1117509, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5209
    ⟨1117509, by decide⟩ (by decide) (![⟨1116736, by decide⟩,⟨893098, by decide⟩,⟨1117225, by decide⟩,⟨1117508, by decide⟩]) unmarked_context_9_5209_1117509 node_context_9_5209_1117509
  intro a
  fin_cases a
  · exact context_10_20836_1116736
  · exact context_10_20837_893098
  · exact context_10_20838_1117225
  · exact context_10_20839_1117508

theorem selected_cut_40958 : selected 10 ⟨1117558, by decide⟩
    (prefixPartial 11 83360) = some ⟨11, 2, 0, 1117558, 83360, 3577, 262144⟩ := by
  decide +kernel

theorem context_11_83360_1117558 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83360 ⟨1117558, by decide⟩ :=
  accepted_of_selected 11 83360 ⟨1117558, by decide⟩ ⟨11, 2, 0, 1117558, 83360, 3577, 262144⟩
    (by decide) selected_cut_40958

theorem selected_cut_40959 : selected 9 ⟨1117576, by decide⟩
    (prefixPartial 12 333444) = some ⟨12, 2, 0, 1117576, 333444, 1061, 65536⟩ := by
  decide +kernel

theorem context_12_333444_1117576 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333444 ⟨1117576, by decide⟩ :=
  accepted_of_selected 12 333444 ⟨1117576, by decide⟩ ⟨12, 2, 0, 1117576, 333444, 1061, 65536⟩
    (by decide) selected_cut_40959

theorem selected_cut_40960 : selected 9 ⟨1117597, by decide⟩
    (prefixPartial 12 333445) = some ⟨12, 2, 0, 1117597, 333445, 1169, 65536⟩ := by
  decide +kernel

theorem context_12_333445_1117597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333445 ⟨1117597, by decide⟩ :=
  accepted_of_selected 12 333445 ⟨1117597, by decide⟩ ⟨12, 2, 0, 1117597, 333445, 1169, 65536⟩
    (by decide) selected_cut_40960

theorem selected_cut_40961 : selected 9 ⟨1117613, by decide⟩
    (prefixPartial 12 333446) = some ⟨12, 2, 0, 1117613, 333446, 1041, 65536⟩ := by
  decide +kernel

theorem context_12_333446_1117613 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333446 ⟨1117613, by decide⟩ :=
  accepted_of_selected 12 333446 ⟨1117613, by decide⟩ ⟨12, 2, 0, 1117613, 333446, 1041, 65536⟩
    (by decide) selected_cut_40961

theorem selected_cut_40962 : selected 9 ⟨1117629, by decide⟩
    (prefixPartial 12 333447) = some ⟨12, 2, 0, 1117629, 333447, 1065, 65536⟩ := by
  decide +kernel

theorem context_12_333447_1117629 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333447 ⟨1117629, by decide⟩ :=
  accepted_of_selected 12 333447 ⟨1117629, by decide⟩ ⟨12, 2, 0, 1117629, 333447, 1065, 65536⟩
    (by decide) selected_cut_40962

theorem unmarked_context_11_83361_1117630 : frontier 10 ⟨1117630, by decide⟩
    (prefixCache 11 83361) (prefixPartial 11 83361) = false := by
  decide +kernel

theorem node_context_11_83361_1117630 : EJMOriginalGlobalDAGData.nodes 10 ⟨1117630, by decide⟩ =
    .split (coordinate 11) (![⟨1117576, by decide⟩,⟨1117597, by decide⟩,⟨1117613, by decide⟩,⟨1117629, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83361_1117630 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83361 ⟨1117630, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83361
    ⟨1117630, by decide⟩ (by decide) (![⟨1117576, by decide⟩,⟨1117597, by decide⟩,⟨1117613, by decide⟩,⟨1117629, by decide⟩]) unmarked_context_11_83361_1117630 node_context_11_83361_1117630
  intro a
  fin_cases a
  · exact context_12_333444_1117576
  · exact context_12_333445_1117597
  · exact context_12_333446_1117613
  · exact context_12_333447_1117629

theorem selected_cut_40963 : selected 10 ⟨1117674, by decide⟩
    (prefixPartial 11 83362) = some ⟨11, 2, 0, 1117674, 83362, 3189, 262144⟩ := by
  decide +kernel

theorem context_11_83362_1117674 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83362 ⟨1117674, by decide⟩ :=
  accepted_of_selected 11 83362 ⟨1117674, by decide⟩ ⟨11, 2, 0, 1117674, 83362, 3189, 262144⟩
    (by decide) selected_cut_40963

theorem selected_cut_40964 : selected 9 ⟨1117688, by decide⟩
    (prefixPartial 12 333452) = some ⟨12, 2, 0, 1117688, 333452, 1065, 65536⟩ := by
  decide +kernel

theorem context_12_333452_1117688 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333452 ⟨1117688, by decide⟩ :=
  accepted_of_selected 12 333452 ⟨1117688, by decide⟩ ⟨12, 2, 0, 1117688, 333452, 1065, 65536⟩
    (by decide) selected_cut_40964

theorem selected_cut_40965 : selected 9 ⟨1117700, by decide⟩
    (prefixPartial 12 333453) = some ⟨12, 2, 0, 1117700, 333453, 973, 65536⟩ := by
  decide +kernel

theorem context_12_333453_1117700 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333453 ⟨1117700, by decide⟩ :=
  accepted_of_selected 12 333453 ⟨1117700, by decide⟩ ⟨12, 2, 0, 1117700, 333453, 973, 65536⟩
    (by decide) selected_cut_40965

theorem selected_cut_40966 : selected 9 ⟨1117718, by decide⟩
    (prefixPartial 12 333454) = some ⟨12, 2, 0, 1117718, 333454, 1121, 65536⟩ := by
  decide +kernel

theorem context_12_333454_1117718 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333454 ⟨1117718, by decide⟩ :=
  accepted_of_selected 12 333454 ⟨1117718, by decide⟩ ⟨12, 2, 0, 1117718, 333454, 1121, 65536⟩
    (by decide) selected_cut_40966

theorem selected_cut_40967 : selected 9 ⟨1117731, by decide⟩
    (prefixPartial 12 333455) = some ⟨12, 2, 0, 1117731, 333455, 1001, 65536⟩ := by
  decide +kernel

theorem context_12_333455_1117731 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333455 ⟨1117731, by decide⟩ :=
  accepted_of_selected 12 333455 ⟨1117731, by decide⟩ ⟨12, 2, 0, 1117731, 333455, 1001, 65536⟩
    (by decide) selected_cut_40967

theorem unmarked_context_11_83363_1117732 : frontier 10 ⟨1117732, by decide⟩
    (prefixCache 11 83363) (prefixPartial 11 83363) = false := by
  decide +kernel

theorem node_context_11_83363_1117732 : EJMOriginalGlobalDAGData.nodes 10 ⟨1117732, by decide⟩ =
    .split (coordinate 11) (![⟨1117688, by decide⟩,⟨1117700, by decide⟩,⟨1117718, by decide⟩,⟨1117731, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83363_1117732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83363 ⟨1117732, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83363
    ⟨1117732, by decide⟩ (by decide) (![⟨1117688, by decide⟩,⟨1117700, by decide⟩,⟨1117718, by decide⟩,⟨1117731, by decide⟩]) unmarked_context_11_83363_1117732 node_context_11_83363_1117732
  intro a
  fin_cases a
  · exact context_12_333452_1117688
  · exact context_12_333453_1117700
  · exact context_12_333454_1117718
  · exact context_12_333455_1117731

theorem unmarked_context_10_20840_1117733 : frontier 11 ⟨1117733, by decide⟩
    (prefixCache 10 20840) (prefixPartial 10 20840) = false := by
  decide +kernel

theorem node_context_10_20840_1117733 : EJMOriginalGlobalDAGData.nodes 11 ⟨1117733, by decide⟩ =
    .split (coordinate 10) (![⟨1117558, by decide⟩,⟨1117630, by decide⟩,⟨1117674, by decide⟩,⟨1117732, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_20840_1117733 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20840 ⟨1117733, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 20840
    ⟨1117733, by decide⟩ (by decide) (![⟨1117558, by decide⟩,⟨1117630, by decide⟩,⟨1117674, by decide⟩,⟨1117732, by decide⟩]) unmarked_context_10_20840_1117733 node_context_10_20840_1117733
  intro a
  fin_cases a
  · exact context_11_83360_1117558
  · exact context_11_83361_1117630
  · exact context_11_83362_1117674
  · exact context_11_83363_1117732

theorem selected_cut_40968 : selected 10 ⟨1117771, by decide⟩
    (prefixPartial 11 83364) = some ⟨11, 2, 0, 1117771, 83364, 3417, 262144⟩ := by
  decide +kernel

theorem context_11_83364_1117771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83364 ⟨1117771, by decide⟩ :=
  accepted_of_selected 11 83364 ⟨1117771, by decide⟩ ⟨11, 2, 0, 1117771, 83364, 3417, 262144⟩
    (by decide) selected_cut_40968

theorem selected_cut_40969 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 83365) = some ⟨11, 1, 0, 892405, 83365, 1, 262144⟩ := by
  decide +kernel

theorem context_11_83365_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83365 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 83365 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 83365, 1, 262144⟩
    (by decide) selected_cut_40969

theorem selected_cut_40970 : selected 10 ⟨1117805, by decide⟩
    (prefixPartial 11 83366) = some ⟨11, 2, 0, 1117805, 83366, 2637, 262144⟩ := by
  decide +kernel

theorem context_11_83366_1117805 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83366 ⟨1117805, by decide⟩ :=
  accepted_of_selected 11 83366 ⟨1117805, by decide⟩ ⟨11, 2, 0, 1117805, 83366, 2637, 262144⟩
    (by decide) selected_cut_40970

theorem selected_cut_40971 : selected 10 ⟨1117841, by decide⟩
    (prefixPartial 11 83367) = some ⟨11, 2, 0, 1117841, 83367, 3233, 262144⟩ := by
  decide +kernel

theorem context_11_83367_1117841 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83367 ⟨1117841, by decide⟩ :=
  accepted_of_selected 11 83367 ⟨1117841, by decide⟩ ⟨11, 2, 0, 1117841, 83367, 3233, 262144⟩
    (by decide) selected_cut_40971

theorem unmarked_context_10_20841_1117842 : frontier 11 ⟨1117842, by decide⟩
    (prefixCache 10 20841) (prefixPartial 10 20841) = false := by
  decide +kernel

theorem node_context_10_20841_1117842 : EJMOriginalGlobalDAGData.nodes 11 ⟨1117842, by decide⟩ =
    .split (coordinate 10) (![⟨1117771, by decide⟩,⟨892405, by decide⟩,⟨1117805, by decide⟩,⟨1117841, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_20841_1117842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20841 ⟨1117842, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 20841
    ⟨1117842, by decide⟩ (by decide) (![⟨1117771, by decide⟩,⟨892405, by decide⟩,⟨1117805, by decide⟩,⟨1117841, by decide⟩]) unmarked_context_10_20841_1117842 node_context_10_20841_1117842
  intro a
  fin_cases a
  · exact context_11_83364_1117771
  · exact context_11_83365_892405
  · exact context_11_83366_1117805
  · exact context_11_83367_1117841

theorem selected_cut_40972 : selected 10 ⟨1117878, by decide⟩
    (prefixPartial 11 83368) = some ⟨11, 2, 0, 1117878, 83368, 2593, 262144⟩ := by
  decide +kernel

theorem context_11_83368_1117878 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83368 ⟨1117878, by decide⟩ :=
  accepted_of_selected 11 83368 ⟨1117878, by decide⟩ ⟨11, 2, 0, 1117878, 83368, 2593, 262144⟩
    (by decide) selected_cut_40972

theorem selected_cut_40973 : selected 10 ⟨1117921, by decide⟩
    (prefixPartial 11 83369) = some ⟨11, 2, 0, 1117921, 83369, 2565, 262144⟩ := by
  decide +kernel

theorem context_11_83369_1117921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83369 ⟨1117921, by decide⟩ :=
  accepted_of_selected 11 83369 ⟨1117921, by decide⟩ ⟨11, 2, 0, 1117921, 83369, 2565, 262144⟩
    (by decide) selected_cut_40973

theorem selected_cut_40974 : selected 10 ⟨1109453, by decide⟩
    (prefixPartial 11 83370) = some ⟨11, 1, 0, 1109453, 83370, 1, 262144⟩ := by
  decide +kernel

theorem context_11_83370_1109453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83370 ⟨1109453, by decide⟩ :=
  accepted_of_selected 11 83370 ⟨1109453, by decide⟩ ⟨11, 1, 0, 1109453, 83370, 1, 262144⟩
    (by decide) selected_cut_40974

theorem selected_cut_40975 : selected 10 ⟨1117958, by decide⟩
    (prefixPartial 11 83371) = some ⟨11, 2, 0, 1117958, 83371, 2321, 262144⟩ := by
  decide +kernel

theorem context_11_83371_1117958 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83371 ⟨1117958, by decide⟩ :=
  accepted_of_selected 11 83371 ⟨1117958, by decide⟩ ⟨11, 2, 0, 1117958, 83371, 2321, 262144⟩
    (by decide) selected_cut_40975

theorem unmarked_context_10_20842_1117959 : frontier 11 ⟨1117959, by decide⟩
    (prefixCache 10 20842) (prefixPartial 10 20842) = false := by
  decide +kernel

theorem node_context_10_20842_1117959 : EJMOriginalGlobalDAGData.nodes 11 ⟨1117959, by decide⟩ =
    .split (coordinate 10) (![⟨1117878, by decide⟩,⟨1117921, by decide⟩,⟨1109453, by decide⟩,⟨1117958, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_20842_1117959 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20842 ⟨1117959, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 20842
    ⟨1117959, by decide⟩ (by decide) (![⟨1117878, by decide⟩,⟨1117921, by decide⟩,⟨1109453, by decide⟩,⟨1117958, by decide⟩]) unmarked_context_10_20842_1117959 node_context_10_20842_1117959
  intro a
  fin_cases a
  · exact context_11_83368_1117878
  · exact context_11_83369_1117921
  · exact context_11_83370_1109453
  · exact context_11_83371_1117958

theorem selected_cut_40976 : selected 10 ⟨1117994, by decide⟩
    (prefixPartial 11 83372) = some ⟨11, 2, 0, 1117994, 83372, 2801, 262144⟩ := by
  decide +kernel

theorem context_11_83372_1117994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83372 ⟨1117994, by decide⟩ :=
  accepted_of_selected 11 83372 ⟨1117994, by decide⟩ ⟨11, 2, 0, 1117994, 83372, 2801, 262144⟩
    (by decide) selected_cut_40976

theorem selected_cut_40977 : selected 10 ⟨1118027, by decide⟩
    (prefixPartial 11 83373) = some ⟨11, 2, 0, 1118027, 83373, 2505, 262144⟩ := by
  decide +kernel

theorem context_11_83373_1118027 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83373 ⟨1118027, by decide⟩ :=
  accepted_of_selected 11 83373 ⟨1118027, by decide⟩ ⟨11, 2, 0, 1118027, 83373, 2505, 262144⟩
    (by decide) selected_cut_40977

theorem selected_cut_40978 : selected 10 ⟨1118061, by decide⟩
    (prefixPartial 11 83374) = some ⟨11, 2, 0, 1118061, 83374, 1849, 262144⟩ := by
  decide +kernel

theorem context_11_83374_1118061 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83374 ⟨1118061, by decide⟩ :=
  accepted_of_selected 11 83374 ⟨1118061, by decide⟩ ⟨11, 2, 0, 1118061, 83374, 1849, 262144⟩
    (by decide) selected_cut_40978

theorem selected_cut_40979 : selected 10 ⟨1118081, by decide⟩
    (prefixPartial 11 83375) = some ⟨11, 2, 0, 1118081, 83375, 1517, 262144⟩ := by
  decide +kernel

theorem context_11_83375_1118081 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83375 ⟨1118081, by decide⟩ :=
  accepted_of_selected 11 83375 ⟨1118081, by decide⟩ ⟨11, 2, 0, 1118081, 83375, 1517, 262144⟩
    (by decide) selected_cut_40979

theorem unmarked_context_10_20843_1118082 : frontier 11 ⟨1118082, by decide⟩
    (prefixCache 10 20843) (prefixPartial 10 20843) = false := by
  decide +kernel

theorem node_context_10_20843_1118082 : EJMOriginalGlobalDAGData.nodes 11 ⟨1118082, by decide⟩ =
    .split (coordinate 10) (![⟨1117994, by decide⟩,⟨1118027, by decide⟩,⟨1118061, by decide⟩,⟨1118081, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_20843_1118082 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20843 ⟨1118082, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 20843
    ⟨1118082, by decide⟩ (by decide) (![⟨1117994, by decide⟩,⟨1118027, by decide⟩,⟨1118061, by decide⟩,⟨1118081, by decide⟩]) unmarked_context_10_20843_1118082 node_context_10_20843_1118082
  intro a
  fin_cases a
  · exact context_11_83372_1117994
  · exact context_11_83373_1118027
  · exact context_11_83374_1118061
  · exact context_11_83375_1118081

theorem unmarked_context_9_5210_1118083 : frontier 12 ⟨1118083, by decide⟩
    (prefixCache 9 5210) (prefixPartial 9 5210) = false := by
  decide +kernel

theorem node_context_9_5210_1118083 : EJMOriginalGlobalDAGData.nodes 12 ⟨1118083, by decide⟩ =
    .split (coordinate 9) (![⟨1117733, by decide⟩,⟨1117842, by decide⟩,⟨1117959, by decide⟩,⟨1118082, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5210_1118083 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5210 ⟨1118083, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5210
    ⟨1118083, by decide⟩ (by decide) (![⟨1117733, by decide⟩,⟨1117842, by decide⟩,⟨1117959, by decide⟩,⟨1118082, by decide⟩]) unmarked_context_9_5210_1118083 node_context_9_5210_1118083
  intro a
  fin_cases a
  · exact context_10_20840_1117733
  · exact context_10_20841_1117842
  · exact context_10_20842_1117959
  · exact context_10_20843_1118082

theorem selected_cut_40980 : selected 10 ⟨1118106, by decide⟩
    (prefixPartial 11 83376) = some ⟨11, 2, 0, 1118106, 83376, 1549, 262144⟩ := by
  decide +kernel

theorem context_11_83376_1118106 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83376 ⟨1118106, by decide⟩ :=
  accepted_of_selected 11 83376 ⟨1118106, by decide⟩ ⟨11, 2, 0, 1118106, 83376, 1549, 262144⟩
    (by decide) selected_cut_40980

theorem selected_cut_40981 : selected 10 ⟨1118131, by decide⟩
    (prefixPartial 11 83377) = some ⟨11, 2, 0, 1118131, 83377, 1769, 262144⟩ := by
  decide +kernel

theorem context_11_83377_1118131 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83377 ⟨1118131, by decide⟩ :=
  accepted_of_selected 11 83377 ⟨1118131, by decide⟩ ⟨11, 2, 0, 1118131, 83377, 1769, 262144⟩
    (by decide) selected_cut_40981

theorem selected_cut_40982 : selected 10 ⟨1118145, by decide⟩
    (prefixPartial 11 83378) = some ⟨11, 2, 0, 1118145, 83378, 1185, 262144⟩ := by
  decide +kernel

theorem context_11_83378_1118145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83378 ⟨1118145, by decide⟩ :=
  accepted_of_selected 11 83378 ⟨1118145, by decide⟩ ⟨11, 2, 0, 1118145, 83378, 1185, 262144⟩
    (by decide) selected_cut_40982

theorem selected_cut_40983 : selected 10 ⟨1118166, by decide⟩
    (prefixPartial 11 83379) = some ⟨11, 2, 0, 1118166, 83379, 1253, 262144⟩ := by
  decide +kernel

theorem context_11_83379_1118166 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83379 ⟨1118166, by decide⟩ :=
  accepted_of_selected 11 83379 ⟨1118166, by decide⟩ ⟨11, 2, 0, 1118166, 83379, 1253, 262144⟩
    (by decide) selected_cut_40983

theorem unmarked_context_10_20844_1118167 : frontier 11 ⟨1118167, by decide⟩
    (prefixCache 10 20844) (prefixPartial 10 20844) = false := by
  decide +kernel

theorem node_context_10_20844_1118167 : EJMOriginalGlobalDAGData.nodes 11 ⟨1118167, by decide⟩ =
    .split (coordinate 10) (![⟨1118106, by decide⟩,⟨1118131, by decide⟩,⟨1118145, by decide⟩,⟨1118166, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_20844_1118167 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20844 ⟨1118167, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 20844
    ⟨1118167, by decide⟩ (by decide) (![⟨1118106, by decide⟩,⟨1118131, by decide⟩,⟨1118145, by decide⟩,⟨1118166, by decide⟩]) unmarked_context_10_20844_1118167 node_context_10_20844_1118167
  intro a
  fin_cases a
  · exact context_11_83376_1118106
  · exact context_11_83377_1118131
  · exact context_11_83378_1118145
  · exact context_11_83379_1118166

theorem selected_cut_40984 : selected 11 ⟨1118207, by decide⟩
    (prefixPartial 10 20845) = some ⟨10, 2, 0, 1118207, 20845, 2761, 1048576⟩ := by
  decide +kernel

theorem context_10_20845_1118207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20845 ⟨1118207, by decide⟩ :=
  accepted_of_selected 10 20845 ⟨1118207, by decide⟩ ⟨10, 2, 0, 1118207, 20845, 2761, 1048576⟩
    (by decide) selected_cut_40984

theorem selected_cut_40985 : selected 11 ⟨1118261, by decide⟩
    (prefixPartial 10 20846) = some ⟨10, 2, 0, 1118261, 20846, 2425, 1048576⟩ := by
  decide +kernel

theorem context_10_20846_1118261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20846 ⟨1118261, by decide⟩ :=
  accepted_of_selected 10 20846 ⟨1118261, by decide⟩ ⟨10, 2, 0, 1118261, 20846, 2425, 1048576⟩
    (by decide) selected_cut_40985

theorem selected_cut_40986 : selected 11 ⟨1118286, by decide⟩
    (prefixPartial 10 20847) = some ⟨10, 2, 0, 1118286, 20847, 469, 1048576⟩ := by
  decide +kernel

theorem context_10_20847_1118286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20847 ⟨1118286, by decide⟩ :=
  accepted_of_selected 10 20847 ⟨1118286, by decide⟩ ⟨10, 2, 0, 1118286, 20847, 469, 1048576⟩
    (by decide) selected_cut_40986

theorem unmarked_context_9_5211_1118287 : frontier 12 ⟨1118287, by decide⟩
    (prefixCache 9 5211) (prefixPartial 9 5211) = false := by
  decide +kernel

theorem node_context_9_5211_1118287 : EJMOriginalGlobalDAGData.nodes 12 ⟨1118287, by decide⟩ =
    .split (coordinate 9) (![⟨1118167, by decide⟩,⟨1118207, by decide⟩,⟨1118261, by decide⟩,⟨1118286, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5211_1118287 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5211 ⟨1118287, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5211
    ⟨1118287, by decide⟩ (by decide) (![⟨1118167, by decide⟩,⟨1118207, by decide⟩,⟨1118261, by decide⟩,⟨1118286, by decide⟩]) unmarked_context_9_5211_1118287 node_context_9_5211_1118287
  intro a
  fin_cases a
  · exact context_10_20844_1118167
  · exact context_10_20845_1118207
  · exact context_10_20846_1118261
  · exact context_10_20847_1118286

theorem unmarked_context_8_1302_1118288 : frontier 13 ⟨1118288, by decide⟩
    (prefixCache 8 1302) (prefixPartial 8 1302) = false := by
  decide +kernel

theorem node_context_8_1302_1118288 : EJMOriginalGlobalDAGData.nodes 13 ⟨1118288, by decide⟩ =
    .split (coordinate 8) (![⟨1116249, by decide⟩,⟨1117509, by decide⟩,⟨1118083, by decide⟩,⟨1118287, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1302_1118288 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1302 ⟨1118288, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1302
    ⟨1118288, by decide⟩ (by decide) (![⟨1116249, by decide⟩,⟨1117509, by decide⟩,⟨1118083, by decide⟩,⟨1118287, by decide⟩]) unmarked_context_8_1302_1118288 node_context_8_1302_1118288
  intro a
  fin_cases a
  · exact context_9_5208_1116249
  · exact context_9_5209_1117509
  · exact context_9_5210_1118083
  · exact context_9_5211_1118287

theorem selected_cut_40987 : selected 13 ⟨14298, by decide⟩
    (prefixPartial 8 1303) = some ⟨8, 1, 0, 14298, 1303, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_1303_14298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1303 ⟨14298, by decide⟩ :=
  accepted_of_selected 8 1303 ⟨14298, by decide⟩ ⟨8, 1, 0, 14298, 1303, 1, 16777216⟩
    (by decide) selected_cut_40987

theorem unmarked_context_7_325_1118289 : frontier 14 ⟨1118289, by decide⟩
    (prefixCache 7 325) (prefixPartial 7 325) = false := by
  decide +kernel

theorem node_context_7_325_1118289 : EJMOriginalGlobalDAGData.nodes 14 ⟨1118289, by decide⟩ =
    .split (coordinate 7) (![⟨1114497, by decide⟩,⟨1109534, by decide⟩,⟨1118288, by decide⟩,⟨14298, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_325_1118289 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 325 ⟨1118289, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 325
    ⟨1118289, by decide⟩ (by decide) (![⟨1114497, by decide⟩,⟨1109534, by decide⟩,⟨1118288, by decide⟩,⟨14298, by decide⟩]) unmarked_context_7_325_1118289 node_context_7_325_1118289
  intro a
  fin_cases a
  · exact context_8_1300_1114497
  · exact context_8_1301_1109534
  · exact context_8_1302_1118288
  · exact context_8_1303_14298

theorem selected_cut_40988 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 83456) = some ⟨11, 1, 0, 434745, 83456, 1, 262144⟩ := by
  decide +kernel

theorem context_11_83456_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83456 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 83456 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 83456, 1, 262144⟩
    (by decide) selected_cut_40988

theorem selected_cut_40989 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 333828) = some ⟨12, 1, 0, 448748, 333828, 1, 65536⟩ := by
  decide +kernel

theorem context_12_333828_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333828 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 333828 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 333828, 1, 65536⟩
    (by decide) selected_cut_40989

theorem selected_cut_40990 : selected 9 ⟨1118392, by decide⟩
    (prefixPartial 12 333829) = some ⟨12, 2, 0, 1118392, 333829, 3445, 65536⟩ := by
  decide +kernel

theorem context_12_333829_1118392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333829 ⟨1118392, by decide⟩ :=
  accepted_of_selected 12 333829 ⟨1118392, by decide⟩ ⟨12, 2, 0, 1118392, 333829, 3445, 65536⟩
    (by decide) selected_cut_40990

theorem selected_cut_40991 : selected 9 ⟨1118451, by decide⟩
    (prefixPartial 12 333830) = some ⟨12, 2, 0, 1118451, 333830, 2965, 65536⟩ := by
  decide +kernel

theorem context_12_333830_1118451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333830 ⟨1118451, by decide⟩ :=
  accepted_of_selected 12 333830 ⟨1118451, by decide⟩ ⟨12, 2, 0, 1118451, 333830, 2965, 65536⟩
    (by decide) selected_cut_40991

theorem selected_cut_40992 : selected 9 ⟨1118507, by decide⟩
    (prefixPartial 12 333831) = some ⟨12, 2, 0, 1118507, 333831, 2957, 65536⟩ := by
  decide +kernel

theorem context_12_333831_1118507 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333831 ⟨1118507, by decide⟩ :=
  accepted_of_selected 12 333831 ⟨1118507, by decide⟩ ⟨12, 2, 0, 1118507, 333831, 2957, 65536⟩
    (by decide) selected_cut_40992

theorem unmarked_context_11_83457_1118508 : frontier 10 ⟨1118508, by decide⟩
    (prefixCache 11 83457) (prefixPartial 11 83457) = false := by
  decide +kernel

theorem node_context_11_83457_1118508 : EJMOriginalGlobalDAGData.nodes 10 ⟨1118508, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1118392, by decide⟩,⟨1118451, by decide⟩,⟨1118507, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83457_1118508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83457 ⟨1118508, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83457
    ⟨1118508, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1118392, by decide⟩,⟨1118451, by decide⟩,⟨1118507, by decide⟩]) unmarked_context_11_83457_1118508 node_context_11_83457_1118508
  intro a
  fin_cases a
  · exact context_12_333828_448748
  · exact context_12_333829_1118392
  · exact context_12_333830_1118451
  · exact context_12_333831_1118507

theorem selected_cut_40993 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 333832) = some ⟨12, 1, 0, 448748, 333832, 1, 65536⟩ := by
  decide +kernel

theorem context_12_333832_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333832 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 333832 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 333832, 1, 65536⟩
    (by decide) selected_cut_40993

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
