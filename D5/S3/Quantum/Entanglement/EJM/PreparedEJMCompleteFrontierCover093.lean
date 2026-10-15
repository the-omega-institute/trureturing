/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover092
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_08932 : selected 9 ⟨248017, by decide⟩
    (prefixPartial 12 23167) = some ⟨12, 2, 0, 248017, 23167, 3285, 65536⟩ := by
  decide +kernel

theorem context_12_23167_248017 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23167 ⟨248017, by decide⟩ :=
  accepted_of_selected 12 23167 ⟨248017, by decide⟩ ⟨12, 2, 0, 248017, 23167, 3285, 65536⟩
    (by decide) selected_cut_08932

theorem unmarked_context_11_5791_248018 : frontier 10 ⟨248018, by decide⟩
    (prefixCache 11 5791) (prefixPartial 11 5791) = false := by
  decide +kernel

theorem node_context_11_5791_248018 : EJMOriginalGlobalDAGData.nodes 10 ⟨248018, by decide⟩ =
    .split (coordinate 11) (![⟨247892, by decide⟩,⟨247953, by decide⟩,⟨247985, by decide⟩,⟨248017, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5791_248018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5791 ⟨248018, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5791
    ⟨248018, by decide⟩ (by decide) (![⟨247892, by decide⟩,⟨247953, by decide⟩,⟨247985, by decide⟩,⟨248017, by decide⟩]) unmarked_context_11_5791_248018 node_context_11_5791_248018
  intro a
  fin_cases a
  · exact context_12_23164_247892
  · exact context_12_23165_247953
  · exact context_12_23166_247985
  · exact context_12_23167_248017

theorem unmarked_context_10_1447_248019 : frontier 11 ⟨248019, by decide⟩
    (prefixCache 10 1447) (prefixPartial 10 1447) = false := by
  decide +kernel

theorem node_context_10_1447_248019 : EJMOriginalGlobalDAGData.nodes 11 ⟨248019, by decide⟩ =
    .split (coordinate 10) (![⟨247465, by decide⟩,⟨247635, by decide⟩,⟨247863, by decide⟩,⟨248018, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1447_248019 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1447 ⟨248019, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1447
    ⟨248019, by decide⟩ (by decide) (![⟨247465, by decide⟩,⟨247635, by decide⟩,⟨247863, by decide⟩,⟨248018, by decide⟩]) unmarked_context_10_1447_248019 node_context_10_1447_248019
  intro a
  fin_cases a
  · exact context_11_5788_247465
  · exact context_11_5789_247635
  · exact context_11_5790_247863
  · exact context_11_5791_248018

theorem unmarked_context_9_361_248020 : frontier 12 ⟨248020, by decide⟩
    (prefixCache 9 361) (prefixPartial 9 361) = false := by
  decide +kernel

theorem node_context_9_361_248020 : EJMOriginalGlobalDAGData.nodes 12 ⟨248020, by decide⟩ =
    .split (coordinate 9) (![⟨245514, by decide⟩,⟨246520, by decide⟩,⟨247282, by decide⟩,⟨248019, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_361_248020 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 361 ⟨248020, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 361
    ⟨248020, by decide⟩ (by decide) (![⟨245514, by decide⟩,⟨246520, by decide⟩,⟨247282, by decide⟩,⟨248019, by decide⟩]) unmarked_context_9_361_248020 node_context_9_361_248020
  intro a
  fin_cases a
  · exact context_10_1444_245514
  · exact context_10_1445_246520
  · exact context_10_1446_247282
  · exact context_10_1447_248019

theorem selected_cut_08933 : selected 9 ⟨248049, by decide⟩
    (prefixPartial 12 23168) = some ⟨12, 2, 0, 248049, 23168, 2305, 65536⟩ := by
  decide +kernel

theorem context_12_23168_248049 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23168 ⟨248049, by decide⟩ :=
  accepted_of_selected 12 23168 ⟨248049, by decide⟩ ⟨12, 2, 0, 248049, 23168, 2305, 65536⟩
    (by decide) selected_cut_08933

theorem selected_cut_08934 : selected 9 ⟨248079, by decide⟩
    (prefixPartial 12 23169) = some ⟨12, 2, 0, 248079, 23169, 2117, 65536⟩ := by
  decide +kernel

theorem context_12_23169_248079 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23169 ⟨248079, by decide⟩ :=
  accepted_of_selected 12 23169 ⟨248079, by decide⟩ ⟨12, 2, 0, 248079, 23169, 2117, 65536⟩
    (by decide) selected_cut_08934

theorem selected_cut_08935 : selected 9 ⟨248107, by decide⟩
    (prefixPartial 12 23170) = some ⟨12, 2, 0, 248107, 23170, 2201, 65536⟩ := by
  decide +kernel

theorem context_12_23170_248107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23170 ⟨248107, by decide⟩ :=
  accepted_of_selected 12 23170 ⟨248107, by decide⟩ ⟨12, 2, 0, 248107, 23170, 2201, 65536⟩
    (by decide) selected_cut_08935

theorem selected_cut_08936 : selected 9 ⟨248135, by decide⟩
    (prefixPartial 12 23171) = some ⟨12, 2, 0, 248135, 23171, 2205, 65536⟩ := by
  decide +kernel

theorem context_12_23171_248135 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23171 ⟨248135, by decide⟩ :=
  accepted_of_selected 12 23171 ⟨248135, by decide⟩ ⟨12, 2, 0, 248135, 23171, 2205, 65536⟩
    (by decide) selected_cut_08936

theorem unmarked_context_11_5792_248136 : frontier 10 ⟨248136, by decide⟩
    (prefixCache 11 5792) (prefixPartial 11 5792) = false := by
  decide +kernel

theorem node_context_11_5792_248136 : EJMOriginalGlobalDAGData.nodes 10 ⟨248136, by decide⟩ =
    .split (coordinate 11) (![⟨248049, by decide⟩,⟨248079, by decide⟩,⟨248107, by decide⟩,⟨248135, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5792_248136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5792 ⟨248136, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5792
    ⟨248136, by decide⟩ (by decide) (![⟨248049, by decide⟩,⟨248079, by decide⟩,⟨248107, by decide⟩,⟨248135, by decide⟩]) unmarked_context_11_5792_248136 node_context_11_5792_248136
  intro a
  fin_cases a
  · exact context_12_23168_248049
  · exact context_12_23169_248079
  · exact context_12_23170_248107
  · exact context_12_23171_248135

theorem selected_cut_08937 : selected 9 ⟨248171, by decide⟩
    (prefixPartial 12 23172) = some ⟨12, 2, 0, 248171, 23172, 2341, 65536⟩ := by
  decide +kernel

theorem context_12_23172_248171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23172 ⟨248171, by decide⟩ :=
  accepted_of_selected 12 23172 ⟨248171, by decide⟩ ⟨12, 2, 0, 248171, 23172, 2341, 65536⟩
    (by decide) selected_cut_08937

theorem selected_cut_08938 : selected 9 ⟨248200, by decide⟩
    (prefixPartial 12 23173) = some ⟨12, 2, 0, 248200, 23173, 2101, 65536⟩ := by
  decide +kernel

theorem context_12_23173_248200 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23173 ⟨248200, by decide⟩ :=
  accepted_of_selected 12 23173 ⟨248200, by decide⟩ ⟨12, 2, 0, 248200, 23173, 2101, 65536⟩
    (by decide) selected_cut_08938

theorem selected_cut_08939 : selected 9 ⟨248230, by decide⟩
    (prefixPartial 12 23174) = some ⟨12, 2, 0, 248230, 23174, 2157, 65536⟩ := by
  decide +kernel

theorem context_12_23174_248230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23174 ⟨248230, by decide⟩ :=
  accepted_of_selected 12 23174 ⟨248230, by decide⟩ ⟨12, 2, 0, 248230, 23174, 2157, 65536⟩
    (by decide) selected_cut_08939

theorem selected_cut_08940 : selected 9 ⟨248263, by decide⟩
    (prefixPartial 12 23175) = some ⟨12, 2, 0, 248263, 23175, 2193, 65536⟩ := by
  decide +kernel

theorem context_12_23175_248263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23175 ⟨248263, by decide⟩ :=
  accepted_of_selected 12 23175 ⟨248263, by decide⟩ ⟨12, 2, 0, 248263, 23175, 2193, 65536⟩
    (by decide) selected_cut_08940

theorem unmarked_context_11_5793_248264 : frontier 10 ⟨248264, by decide⟩
    (prefixCache 11 5793) (prefixPartial 11 5793) = false := by
  decide +kernel

theorem node_context_11_5793_248264 : EJMOriginalGlobalDAGData.nodes 10 ⟨248264, by decide⟩ =
    .split (coordinate 11) (![⟨248171, by decide⟩,⟨248200, by decide⟩,⟨248230, by decide⟩,⟨248263, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5793_248264 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5793 ⟨248264, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5793
    ⟨248264, by decide⟩ (by decide) (![⟨248171, by decide⟩,⟨248200, by decide⟩,⟨248230, by decide⟩,⟨248263, by decide⟩]) unmarked_context_11_5793_248264 node_context_11_5793_248264
  intro a
  fin_cases a
  · exact context_12_23172_248171
  · exact context_12_23173_248200
  · exact context_12_23174_248230
  · exact context_12_23175_248263

theorem selected_cut_08941 : selected 9 ⟨248289, by decide⟩
    (prefixPartial 12 23176) = some ⟨12, 2, 0, 248289, 23176, 1933, 65536⟩ := by
  decide +kernel

theorem context_12_23176_248289 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23176 ⟨248289, by decide⟩ :=
  accepted_of_selected 12 23176 ⟨248289, by decide⟩ ⟨12, 2, 0, 248289, 23176, 1933, 65536⟩
    (by decide) selected_cut_08941

theorem selected_cut_08942 : selected 9 ⟨248313, by decide⟩
    (prefixPartial 12 23177) = some ⟨12, 2, 0, 248313, 23177, 1853, 65536⟩ := by
  decide +kernel

theorem context_12_23177_248313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23177 ⟨248313, by decide⟩ :=
  accepted_of_selected 12 23177 ⟨248313, by decide⟩ ⟨12, 2, 0, 248313, 23177, 1853, 65536⟩
    (by decide) selected_cut_08942

theorem selected_cut_08943 : selected 9 ⟨248354, by decide⟩
    (prefixPartial 12 23178) = some ⟨12, 2, 0, 248354, 23178, 3041, 65536⟩ := by
  decide +kernel

theorem context_12_23178_248354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23178 ⟨248354, by decide⟩ :=
  accepted_of_selected 12 23178 ⟨248354, by decide⟩ ⟨12, 2, 0, 248354, 23178, 3041, 65536⟩
    (by decide) selected_cut_08943

theorem selected_cut_08944 : selected 9 ⟨248378, by decide⟩
    (prefixPartial 12 23179) = some ⟨12, 2, 0, 248378, 23179, 1821, 65536⟩ := by
  decide +kernel

theorem context_12_23179_248378 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23179 ⟨248378, by decide⟩ :=
  accepted_of_selected 12 23179 ⟨248378, by decide⟩ ⟨12, 2, 0, 248378, 23179, 1821, 65536⟩
    (by decide) selected_cut_08944

theorem unmarked_context_11_5794_248379 : frontier 10 ⟨248379, by decide⟩
    (prefixCache 11 5794) (prefixPartial 11 5794) = false := by
  decide +kernel

theorem node_context_11_5794_248379 : EJMOriginalGlobalDAGData.nodes 10 ⟨248379, by decide⟩ =
    .split (coordinate 11) (![⟨248289, by decide⟩,⟨248313, by decide⟩,⟨248354, by decide⟩,⟨248378, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5794_248379 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5794 ⟨248379, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5794
    ⟨248379, by decide⟩ (by decide) (![⟨248289, by decide⟩,⟨248313, by decide⟩,⟨248354, by decide⟩,⟨248378, by decide⟩]) unmarked_context_11_5794_248379 node_context_11_5794_248379
  intro a
  fin_cases a
  · exact context_12_23176_248289
  · exact context_12_23177_248313
  · exact context_12_23178_248354
  · exact context_12_23179_248378

theorem selected_cut_08945 : selected 9 ⟨248405, by decide⟩
    (prefixPartial 12 23180) = some ⟨12, 2, 0, 248405, 23180, 2369, 65536⟩ := by
  decide +kernel

theorem context_12_23180_248405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23180 ⟨248405, by decide⟩ :=
  accepted_of_selected 12 23180 ⟨248405, by decide⟩ ⟨12, 2, 0, 248405, 23180, 2369, 65536⟩
    (by decide) selected_cut_08945

theorem selected_cut_08946 : selected 9 ⟨248426, by decide⟩
    (prefixPartial 12 23181) = some ⟨12, 2, 0, 248426, 23181, 2113, 65536⟩ := by
  decide +kernel

theorem context_12_23181_248426 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23181 ⟨248426, by decide⟩ :=
  accepted_of_selected 12 23181 ⟨248426, by decide⟩ ⟨12, 2, 0, 248426, 23181, 2113, 65536⟩
    (by decide) selected_cut_08946

theorem selected_cut_08947 : selected 9 ⟨248458, by decide⟩
    (prefixPartial 12 23182) = some ⟨12, 2, 0, 248458, 23182, 2033, 65536⟩ := by
  decide +kernel

theorem context_12_23182_248458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23182 ⟨248458, by decide⟩ :=
  accepted_of_selected 12 23182 ⟨248458, by decide⟩ ⟨12, 2, 0, 248458, 23182, 2033, 65536⟩
    (by decide) selected_cut_08947

theorem selected_cut_08948 : selected 9 ⟨248479, by decide⟩
    (prefixPartial 12 23183) = some ⟨12, 2, 0, 248479, 23183, 2045, 65536⟩ := by
  decide +kernel

theorem context_12_23183_248479 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23183 ⟨248479, by decide⟩ :=
  accepted_of_selected 12 23183 ⟨248479, by decide⟩ ⟨12, 2, 0, 248479, 23183, 2045, 65536⟩
    (by decide) selected_cut_08948

theorem unmarked_context_11_5795_248480 : frontier 10 ⟨248480, by decide⟩
    (prefixCache 11 5795) (prefixPartial 11 5795) = false := by
  decide +kernel

theorem node_context_11_5795_248480 : EJMOriginalGlobalDAGData.nodes 10 ⟨248480, by decide⟩ =
    .split (coordinate 11) (![⟨248405, by decide⟩,⟨248426, by decide⟩,⟨248458, by decide⟩,⟨248479, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5795_248480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5795 ⟨248480, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5795
    ⟨248480, by decide⟩ (by decide) (![⟨248405, by decide⟩,⟨248426, by decide⟩,⟨248458, by decide⟩,⟨248479, by decide⟩]) unmarked_context_11_5795_248480 node_context_11_5795_248480
  intro a
  fin_cases a
  · exact context_12_23180_248405
  · exact context_12_23181_248426
  · exact context_12_23182_248458
  · exact context_12_23183_248479

theorem unmarked_context_10_1448_248481 : frontier 11 ⟨248481, by decide⟩
    (prefixCache 10 1448) (prefixPartial 10 1448) = false := by
  decide +kernel

theorem node_context_10_1448_248481 : EJMOriginalGlobalDAGData.nodes 11 ⟨248481, by decide⟩ =
    .split (coordinate 10) (![⟨248136, by decide⟩,⟨248264, by decide⟩,⟨248379, by decide⟩,⟨248480, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1448_248481 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1448 ⟨248481, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1448
    ⟨248481, by decide⟩ (by decide) (![⟨248136, by decide⟩,⟨248264, by decide⟩,⟨248379, by decide⟩,⟨248480, by decide⟩]) unmarked_context_10_1448_248481 node_context_10_1448_248481
  intro a
  fin_cases a
  · exact context_11_5792_248136
  · exact context_11_5793_248264
  · exact context_11_5794_248379
  · exact context_11_5795_248480

theorem selected_cut_08949 : selected 9 ⟨248505, by decide⟩
    (prefixPartial 12 23184) = some ⟨12, 2, 0, 248505, 23184, 2221, 65536⟩ := by
  decide +kernel

theorem context_12_23184_248505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23184 ⟨248505, by decide⟩ :=
  accepted_of_selected 12 23184 ⟨248505, by decide⟩ ⟨12, 2, 0, 248505, 23184, 2221, 65536⟩
    (by decide) selected_cut_08949

theorem selected_cut_08950 : selected 9 ⟨248534, by decide⟩
    (prefixPartial 12 23185) = some ⟨12, 2, 0, 248534, 23185, 2217, 65536⟩ := by
  decide +kernel

theorem context_12_23185_248534 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23185 ⟨248534, by decide⟩ :=
  accepted_of_selected 12 23185 ⟨248534, by decide⟩ ⟨12, 2, 0, 248534, 23185, 2217, 65536⟩
    (by decide) selected_cut_08950

theorem selected_cut_08951 : selected 9 ⟨248562, by decide⟩
    (prefixPartial 12 23186) = some ⟨12, 2, 0, 248562, 23186, 2281, 65536⟩ := by
  decide +kernel

theorem context_12_23186_248562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23186 ⟨248562, by decide⟩ :=
  accepted_of_selected 12 23186 ⟨248562, by decide⟩ ⟨12, 2, 0, 248562, 23186, 2281, 65536⟩
    (by decide) selected_cut_08951

theorem selected_cut_08952 : selected 9 ⟨248595, by decide⟩
    (prefixPartial 12 23187) = some ⟨12, 2, 0, 248595, 23187, 2309, 65536⟩ := by
  decide +kernel

theorem context_12_23187_248595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23187 ⟨248595, by decide⟩ :=
  accepted_of_selected 12 23187 ⟨248595, by decide⟩ ⟨12, 2, 0, 248595, 23187, 2309, 65536⟩
    (by decide) selected_cut_08952

theorem unmarked_context_11_5796_248596 : frontier 10 ⟨248596, by decide⟩
    (prefixCache 11 5796) (prefixPartial 11 5796) = false := by
  decide +kernel

theorem node_context_11_5796_248596 : EJMOriginalGlobalDAGData.nodes 10 ⟨248596, by decide⟩ =
    .split (coordinate 11) (![⟨248505, by decide⟩,⟨248534, by decide⟩,⟨248562, by decide⟩,⟨248595, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5796_248596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5796 ⟨248596, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5796
    ⟨248596, by decide⟩ (by decide) (![⟨248505, by decide⟩,⟨248534, by decide⟩,⟨248562, by decide⟩,⟨248595, by decide⟩]) unmarked_context_11_5796_248596 node_context_11_5796_248596
  intro a
  fin_cases a
  · exact context_12_23184_248505
  · exact context_12_23185_248534
  · exact context_12_23186_248562
  · exact context_12_23187_248595

theorem selected_cut_08953 : selected 9 ⟨248622, by decide⟩
    (prefixPartial 12 23188) = some ⟨12, 2, 0, 248622, 23188, 2121, 65536⟩ := by
  decide +kernel

theorem context_12_23188_248622 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23188 ⟨248622, by decide⟩ :=
  accepted_of_selected 12 23188 ⟨248622, by decide⟩ ⟨12, 2, 0, 248622, 23188, 2121, 65536⟩
    (by decide) selected_cut_08953

theorem selected_cut_08954 : selected 9 ⟨248657, by decide⟩
    (prefixPartial 12 23189) = some ⟨12, 2, 0, 248657, 23189, 2093, 65536⟩ := by
  decide +kernel

theorem context_12_23189_248657 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23189 ⟨248657, by decide⟩ :=
  accepted_of_selected 12 23189 ⟨248657, by decide⟩ ⟨12, 2, 0, 248657, 23189, 2093, 65536⟩
    (by decide) selected_cut_08954

theorem selected_cut_08955 : selected 9 ⟨248684, by decide⟩
    (prefixPartial 12 23190) = some ⟨12, 2, 0, 248684, 23190, 2097, 65536⟩ := by
  decide +kernel

theorem context_12_23190_248684 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23190 ⟨248684, by decide⟩ :=
  accepted_of_selected 12 23190 ⟨248684, by decide⟩ ⟨12, 2, 0, 248684, 23190, 2097, 65536⟩
    (by decide) selected_cut_08955

theorem selected_cut_08956 : selected 9 ⟨248717, by decide⟩
    (prefixPartial 12 23191) = some ⟨12, 2, 0, 248717, 23191, 2245, 65536⟩ := by
  decide +kernel

theorem context_12_23191_248717 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23191 ⟨248717, by decide⟩ :=
  accepted_of_selected 12 23191 ⟨248717, by decide⟩ ⟨12, 2, 0, 248717, 23191, 2245, 65536⟩
    (by decide) selected_cut_08956

theorem unmarked_context_11_5797_248718 : frontier 10 ⟨248718, by decide⟩
    (prefixCache 11 5797) (prefixPartial 11 5797) = false := by
  decide +kernel

theorem node_context_11_5797_248718 : EJMOriginalGlobalDAGData.nodes 10 ⟨248718, by decide⟩ =
    .split (coordinate 11) (![⟨248622, by decide⟩,⟨248657, by decide⟩,⟨248684, by decide⟩,⟨248717, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5797_248718 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5797 ⟨248718, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5797
    ⟨248718, by decide⟩ (by decide) (![⟨248622, by decide⟩,⟨248657, by decide⟩,⟨248684, by decide⟩,⟨248717, by decide⟩]) unmarked_context_11_5797_248718 node_context_11_5797_248718
  intro a
  fin_cases a
  · exact context_12_23188_248622
  · exact context_12_23189_248657
  · exact context_12_23190_248684
  · exact context_12_23191_248717

theorem selected_cut_08957 : selected 9 ⟨248739, by decide⟩
    (prefixPartial 12 23192) = some ⟨12, 2, 0, 248739, 23192, 1765, 65536⟩ := by
  decide +kernel

theorem context_12_23192_248739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23192 ⟨248739, by decide⟩ :=
  accepted_of_selected 12 23192 ⟨248739, by decide⟩ ⟨12, 2, 0, 248739, 23192, 1765, 65536⟩
    (by decide) selected_cut_08957

theorem selected_cut_08958 : selected 9 ⟨248764, by decide⟩
    (prefixPartial 12 23193) = some ⟨12, 2, 0, 248764, 23193, 1885, 65536⟩ := by
  decide +kernel

theorem context_12_23193_248764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23193 ⟨248764, by decide⟩ :=
  accepted_of_selected 12 23193 ⟨248764, by decide⟩ ⟨12, 2, 0, 248764, 23193, 1885, 65536⟩
    (by decide) selected_cut_08958

theorem selected_cut_08959 : selected 9 ⟨248765, by decide⟩
    (prefixPartial 12 23194) = some ⟨12, 1, 0, 248765, 23194, 1, 65536⟩ := by
  decide +kernel

theorem context_12_23194_248765 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23194 ⟨248765, by decide⟩ :=
  accepted_of_selected 12 23194 ⟨248765, by decide⟩ ⟨12, 1, 0, 248765, 23194, 1, 65536⟩
    (by decide) selected_cut_08959

theorem selected_cut_08960 : selected 9 ⟨248790, by decide⟩
    (prefixPartial 12 23195) = some ⟨12, 2, 0, 248790, 23195, 1921, 65536⟩ := by
  decide +kernel

theorem context_12_23195_248790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23195 ⟨248790, by decide⟩ :=
  accepted_of_selected 12 23195 ⟨248790, by decide⟩ ⟨12, 2, 0, 248790, 23195, 1921, 65536⟩
    (by decide) selected_cut_08960

theorem unmarked_context_11_5798_248791 : frontier 10 ⟨248791, by decide⟩
    (prefixCache 11 5798) (prefixPartial 11 5798) = false := by
  decide +kernel

theorem node_context_11_5798_248791 : EJMOriginalGlobalDAGData.nodes 10 ⟨248791, by decide⟩ =
    .split (coordinate 11) (![⟨248739, by decide⟩,⟨248764, by decide⟩,⟨248765, by decide⟩,⟨248790, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5798_248791 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5798 ⟨248791, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5798
    ⟨248791, by decide⟩ (by decide) (![⟨248739, by decide⟩,⟨248764, by decide⟩,⟨248765, by decide⟩,⟨248790, by decide⟩]) unmarked_context_11_5798_248791 node_context_11_5798_248791
  intro a
  fin_cases a
  · exact context_12_23192_248739
  · exact context_12_23193_248764
  · exact context_12_23194_248765
  · exact context_12_23195_248790

theorem selected_cut_08961 : selected 9 ⟨248815, by decide⟩
    (prefixPartial 12 23196) = some ⟨12, 2, 0, 248815, 23196, 1997, 65536⟩ := by
  decide +kernel

theorem context_12_23196_248815 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23196 ⟨248815, by decide⟩ :=
  accepted_of_selected 12 23196 ⟨248815, by decide⟩ ⟨12, 2, 0, 248815, 23196, 1997, 65536⟩
    (by decide) selected_cut_08961

theorem selected_cut_08962 : selected 9 ⟨248841, by decide⟩
    (prefixPartial 12 23197) = some ⟨12, 2, 0, 248841, 23197, 1969, 65536⟩ := by
  decide +kernel

theorem context_12_23197_248841 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23197 ⟨248841, by decide⟩ :=
  accepted_of_selected 12 23197 ⟨248841, by decide⟩ ⟨12, 2, 0, 248841, 23197, 1969, 65536⟩
    (by decide) selected_cut_08962

theorem selected_cut_08963 : selected 9 ⟨248861, by decide⟩
    (prefixPartial 12 23198) = some ⟨12, 2, 0, 248861, 23198, 1897, 65536⟩ := by
  decide +kernel

theorem context_12_23198_248861 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23198 ⟨248861, by decide⟩ :=
  accepted_of_selected 12 23198 ⟨248861, by decide⟩ ⟨12, 2, 0, 248861, 23198, 1897, 65536⟩
    (by decide) selected_cut_08963

theorem selected_cut_08964 : selected 9 ⟨248882, by decide⟩
    (prefixPartial 12 23199) = some ⟨12, 2, 0, 248882, 23199, 1973, 65536⟩ := by
  decide +kernel

theorem context_12_23199_248882 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23199 ⟨248882, by decide⟩ :=
  accepted_of_selected 12 23199 ⟨248882, by decide⟩ ⟨12, 2, 0, 248882, 23199, 1973, 65536⟩
    (by decide) selected_cut_08964

theorem unmarked_context_11_5799_248883 : frontier 10 ⟨248883, by decide⟩
    (prefixCache 11 5799) (prefixPartial 11 5799) = false := by
  decide +kernel

theorem node_context_11_5799_248883 : EJMOriginalGlobalDAGData.nodes 10 ⟨248883, by decide⟩ =
    .split (coordinate 11) (![⟨248815, by decide⟩,⟨248841, by decide⟩,⟨248861, by decide⟩,⟨248882, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5799_248883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5799 ⟨248883, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5799
    ⟨248883, by decide⟩ (by decide) (![⟨248815, by decide⟩,⟨248841, by decide⟩,⟨248861, by decide⟩,⟨248882, by decide⟩]) unmarked_context_11_5799_248883 node_context_11_5799_248883
  intro a
  fin_cases a
  · exact context_12_23196_248815
  · exact context_12_23197_248841
  · exact context_12_23198_248861
  · exact context_12_23199_248882

theorem unmarked_context_10_1449_248884 : frontier 11 ⟨248884, by decide⟩
    (prefixCache 10 1449) (prefixPartial 10 1449) = false := by
  decide +kernel

theorem node_context_10_1449_248884 : EJMOriginalGlobalDAGData.nodes 11 ⟨248884, by decide⟩ =
    .split (coordinate 10) (![⟨248596, by decide⟩,⟨248718, by decide⟩,⟨248791, by decide⟩,⟨248883, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1449_248884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1449 ⟨248884, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1449
    ⟨248884, by decide⟩ (by decide) (![⟨248596, by decide⟩,⟨248718, by decide⟩,⟨248791, by decide⟩,⟨248883, by decide⟩]) unmarked_context_10_1449_248884 node_context_10_1449_248884
  intro a
  fin_cases a
  · exact context_11_5796_248596
  · exact context_11_5797_248718
  · exact context_11_5798_248791
  · exact context_11_5799_248883

theorem selected_cut_08965 : selected 9 ⟨248901, by decide⟩
    (prefixPartial 12 23200) = some ⟨12, 2, 0, 248901, 23200, 1433, 65536⟩ := by
  decide +kernel

theorem context_12_23200_248901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23200 ⟨248901, by decide⟩ :=
  accepted_of_selected 12 23200 ⟨248901, by decide⟩ ⟨12, 2, 0, 248901, 23200, 1433, 65536⟩
    (by decide) selected_cut_08965

theorem selected_cut_08966 : selected 9 ⟨248919, by decide⟩
    (prefixPartial 12 23201) = some ⟨12, 2, 0, 248919, 23201, 1529, 65536⟩ := by
  decide +kernel

theorem context_12_23201_248919 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23201 ⟨248919, by decide⟩ :=
  accepted_of_selected 12 23201 ⟨248919, by decide⟩ ⟨12, 2, 0, 248919, 23201, 1529, 65536⟩
    (by decide) selected_cut_08966

theorem selected_cut_08967 : selected 9 ⟨248940, by decide⟩
    (prefixPartial 12 23202) = some ⟨12, 2, 0, 248940, 23202, 1477, 65536⟩ := by
  decide +kernel

theorem context_12_23202_248940 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23202 ⟨248940, by decide⟩ :=
  accepted_of_selected 12 23202 ⟨248940, by decide⟩ ⟨12, 2, 0, 248940, 23202, 1477, 65536⟩
    (by decide) selected_cut_08967

theorem selected_cut_08968 : selected 9 ⟨248957, by decide⟩
    (prefixPartial 12 23203) = some ⟨12, 2, 0, 248957, 23203, 1605, 65536⟩ := by
  decide +kernel

theorem context_12_23203_248957 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23203 ⟨248957, by decide⟩ :=
  accepted_of_selected 12 23203 ⟨248957, by decide⟩ ⟨12, 2, 0, 248957, 23203, 1605, 65536⟩
    (by decide) selected_cut_08968

theorem unmarked_context_11_5800_248958 : frontier 10 ⟨248958, by decide⟩
    (prefixCache 11 5800) (prefixPartial 11 5800) = false := by
  decide +kernel

theorem node_context_11_5800_248958 : EJMOriginalGlobalDAGData.nodes 10 ⟨248958, by decide⟩ =
    .split (coordinate 11) (![⟨248901, by decide⟩,⟨248919, by decide⟩,⟨248940, by decide⟩,⟨248957, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5800_248958 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5800 ⟨248958, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5800
    ⟨248958, by decide⟩ (by decide) (![⟨248901, by decide⟩,⟨248919, by decide⟩,⟨248940, by decide⟩,⟨248957, by decide⟩]) unmarked_context_11_5800_248958 node_context_11_5800_248958
  intro a
  fin_cases a
  · exact context_12_23200_248901
  · exact context_12_23201_248919
  · exact context_12_23202_248940
  · exact context_12_23203_248957

theorem selected_cut_08969 : selected 9 ⟨248976, by decide⟩
    (prefixPartial 12 23204) = some ⟨12, 2, 0, 248976, 23204, 1445, 65536⟩ := by
  decide +kernel

theorem context_12_23204_248976 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23204 ⟨248976, by decide⟩ :=
  accepted_of_selected 12 23204 ⟨248976, by decide⟩ ⟨12, 2, 0, 248976, 23204, 1445, 65536⟩
    (by decide) selected_cut_08969

theorem selected_cut_08970 : selected 9 ⟨248995, by decide⟩
    (prefixPartial 12 23205) = some ⟨12, 2, 0, 248995, 23205, 1405, 65536⟩ := by
  decide +kernel

theorem context_12_23205_248995 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23205 ⟨248995, by decide⟩ :=
  accepted_of_selected 12 23205 ⟨248995, by decide⟩ ⟨12, 2, 0, 248995, 23205, 1405, 65536⟩
    (by decide) selected_cut_08970

theorem selected_cut_08971 : selected 9 ⟨249015, by decide⟩
    (prefixPartial 12 23206) = some ⟨12, 2, 0, 249015, 23206, 1337, 65536⟩ := by
  decide +kernel

theorem context_12_23206_249015 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23206 ⟨249015, by decide⟩ :=
  accepted_of_selected 12 23206 ⟨249015, by decide⟩ ⟨12, 2, 0, 249015, 23206, 1337, 65536⟩
    (by decide) selected_cut_08971

theorem selected_cut_08972 : selected 9 ⟨249034, by decide⟩
    (prefixPartial 12 23207) = some ⟨12, 2, 0, 249034, 23207, 1489, 65536⟩ := by
  decide +kernel

theorem context_12_23207_249034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23207 ⟨249034, by decide⟩ :=
  accepted_of_selected 12 23207 ⟨249034, by decide⟩ ⟨12, 2, 0, 249034, 23207, 1489, 65536⟩
    (by decide) selected_cut_08972

theorem unmarked_context_11_5801_249035 : frontier 10 ⟨249035, by decide⟩
    (prefixCache 11 5801) (prefixPartial 11 5801) = false := by
  decide +kernel

theorem node_context_11_5801_249035 : EJMOriginalGlobalDAGData.nodes 10 ⟨249035, by decide⟩ =
    .split (coordinate 11) (![⟨248976, by decide⟩,⟨248995, by decide⟩,⟨249015, by decide⟩,⟨249034, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5801_249035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5801 ⟨249035, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5801
    ⟨249035, by decide⟩ (by decide) (![⟨248976, by decide⟩,⟨248995, by decide⟩,⟨249015, by decide⟩,⟨249034, by decide⟩]) unmarked_context_11_5801_249035 node_context_11_5801_249035
  intro a
  fin_cases a
  · exact context_12_23204_248976
  · exact context_12_23205_248995
  · exact context_12_23206_249015
  · exact context_12_23207_249034

theorem selected_cut_08973 : selected 10 ⟨249075, by decide⟩
    (prefixPartial 11 5802) = some ⟨11, 2, 0, 249075, 5802, 3369, 262144⟩ := by
  decide +kernel

theorem context_11_5802_249075 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5802 ⟨249075, by decide⟩ :=
  accepted_of_selected 11 5802 ⟨249075, by decide⟩ ⟨11, 2, 0, 249075, 5802, 3369, 262144⟩
    (by decide) selected_cut_08973

theorem selected_cut_08974 : selected 9 ⟨249087, by decide⟩
    (prefixPartial 12 23212) = some ⟨12, 2, 0, 249087, 23212, 1449, 65536⟩ := by
  decide +kernel

theorem context_12_23212_249087 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23212 ⟨249087, by decide⟩ :=
  accepted_of_selected 12 23212 ⟨249087, by decide⟩ ⟨12, 2, 0, 249087, 23212, 1449, 65536⟩
    (by decide) selected_cut_08974

theorem selected_cut_08975 : selected 9 ⟨249105, by decide⟩
    (prefixPartial 12 23213) = some ⟨12, 2, 0, 249105, 23213, 1429, 65536⟩ := by
  decide +kernel

theorem context_12_23213_249105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23213 ⟨249105, by decide⟩ :=
  accepted_of_selected 12 23213 ⟨249105, by decide⟩ ⟨12, 2, 0, 249105, 23213, 1429, 65536⟩
    (by decide) selected_cut_08975

theorem selected_cut_08976 : selected 9 ⟨249126, by decide⟩
    (prefixPartial 12 23214) = some ⟨12, 2, 0, 249126, 23214, 1261, 65536⟩ := by
  decide +kernel

theorem context_12_23214_249126 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23214 ⟨249126, by decide⟩ :=
  accepted_of_selected 12 23214 ⟨249126, by decide⟩ ⟨12, 2, 0, 249126, 23214, 1261, 65536⟩
    (by decide) selected_cut_08976

theorem selected_cut_08977 : selected 9 ⟨249140, by decide⟩
    (prefixPartial 12 23215) = some ⟨12, 2, 0, 249140, 23215, 1453, 65536⟩ := by
  decide +kernel

theorem context_12_23215_249140 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23215 ⟨249140, by decide⟩ :=
  accepted_of_selected 12 23215 ⟨249140, by decide⟩ ⟨12, 2, 0, 249140, 23215, 1453, 65536⟩
    (by decide) selected_cut_08977

theorem unmarked_context_11_5803_249141 : frontier 10 ⟨249141, by decide⟩
    (prefixCache 11 5803) (prefixPartial 11 5803) = false := by
  decide +kernel

theorem node_context_11_5803_249141 : EJMOriginalGlobalDAGData.nodes 10 ⟨249141, by decide⟩ =
    .split (coordinate 11) (![⟨249087, by decide⟩,⟨249105, by decide⟩,⟨249126, by decide⟩,⟨249140, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5803_249141 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5803 ⟨249141, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5803
    ⟨249141, by decide⟩ (by decide) (![⟨249087, by decide⟩,⟨249105, by decide⟩,⟨249126, by decide⟩,⟨249140, by decide⟩]) unmarked_context_11_5803_249141 node_context_11_5803_249141
  intro a
  fin_cases a
  · exact context_12_23212_249087
  · exact context_12_23213_249105
  · exact context_12_23214_249126
  · exact context_12_23215_249140

theorem unmarked_context_10_1450_249142 : frontier 11 ⟨249142, by decide⟩
    (prefixCache 10 1450) (prefixPartial 10 1450) = false := by
  decide +kernel

theorem node_context_10_1450_249142 : EJMOriginalGlobalDAGData.nodes 11 ⟨249142, by decide⟩ =
    .split (coordinate 10) (![⟨248958, by decide⟩,⟨249035, by decide⟩,⟨249075, by decide⟩,⟨249141, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1450_249142 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1450 ⟨249142, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1450
    ⟨249142, by decide⟩ (by decide) (![⟨248958, by decide⟩,⟨249035, by decide⟩,⟨249075, by decide⟩,⟨249141, by decide⟩]) unmarked_context_10_1450_249142 node_context_10_1450_249142
  intro a
  fin_cases a
  · exact context_11_5800_248958
  · exact context_11_5801_249035
  · exact context_11_5802_249075
  · exact context_11_5803_249141

theorem selected_cut_08978 : selected 9 ⟨249156, by decide⟩
    (prefixPartial 12 23216) = some ⟨12, 2, 0, 249156, 23216, 1297, 65536⟩ := by
  decide +kernel

theorem context_12_23216_249156 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23216 ⟨249156, by decide⟩ :=
  accepted_of_selected 12 23216 ⟨249156, by decide⟩ ⟨12, 2, 0, 249156, 23216, 1297, 65536⟩
    (by decide) selected_cut_08978

theorem selected_cut_08979 : selected 9 ⟨249172, by decide⟩
    (prefixPartial 12 23217) = some ⟨12, 2, 0, 249172, 23217, 1449, 65536⟩ := by
  decide +kernel

theorem context_12_23217_249172 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23217 ⟨249172, by decide⟩ :=
  accepted_of_selected 12 23217 ⟨249172, by decide⟩ ⟨12, 2, 0, 249172, 23217, 1449, 65536⟩
    (by decide) selected_cut_08979

theorem selected_cut_08980 : selected 9 ⟨249187, by decide⟩
    (prefixPartial 12 23218) = some ⟨12, 2, 0, 249187, 23218, 1277, 65536⟩ := by
  decide +kernel

theorem context_12_23218_249187 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23218 ⟨249187, by decide⟩ :=
  accepted_of_selected 12 23218 ⟨249187, by decide⟩ ⟨12, 2, 0, 249187, 23218, 1277, 65536⟩
    (by decide) selected_cut_08980

theorem selected_cut_08981 : selected 9 ⟨249204, by decide⟩
    (prefixPartial 12 23219) = some ⟨12, 2, 0, 249204, 23219, 1409, 65536⟩ := by
  decide +kernel

theorem context_12_23219_249204 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23219 ⟨249204, by decide⟩ :=
  accepted_of_selected 12 23219 ⟨249204, by decide⟩ ⟨12, 2, 0, 249204, 23219, 1409, 65536⟩
    (by decide) selected_cut_08981

theorem unmarked_context_11_5804_249205 : frontier 10 ⟨249205, by decide⟩
    (prefixCache 11 5804) (prefixPartial 11 5804) = false := by
  decide +kernel

theorem node_context_11_5804_249205 : EJMOriginalGlobalDAGData.nodes 10 ⟨249205, by decide⟩ =
    .split (coordinate 11) (![⟨249156, by decide⟩,⟨249172, by decide⟩,⟨249187, by decide⟩,⟨249204, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5804_249205 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5804 ⟨249205, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5804
    ⟨249205, by decide⟩ (by decide) (![⟨249156, by decide⟩,⟨249172, by decide⟩,⟨249187, by decide⟩,⟨249204, by decide⟩]) unmarked_context_11_5804_249205 node_context_11_5804_249205
  intro a
  fin_cases a
  · exact context_12_23216_249156
  · exact context_12_23217_249172
  · exact context_12_23218_249187
  · exact context_12_23219_249204

theorem selected_cut_08982 : selected 9 ⟨249221, by decide⟩
    (prefixPartial 12 23220) = some ⟨12, 2, 0, 249221, 23220, 1261, 65536⟩ := by
  decide +kernel

theorem context_12_23220_249221 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23220 ⟨249221, by decide⟩ :=
  accepted_of_selected 12 23220 ⟨249221, by decide⟩ ⟨12, 2, 0, 249221, 23220, 1261, 65536⟩
    (by decide) selected_cut_08982

theorem selected_cut_08983 : selected 9 ⟨249236, by decide⟩
    (prefixPartial 12 23221) = some ⟨12, 2, 0, 249236, 23221, 1257, 65536⟩ := by
  decide +kernel

theorem context_12_23221_249236 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23221 ⟨249236, by decide⟩ :=
  accepted_of_selected 12 23221 ⟨249236, by decide⟩ ⟨12, 2, 0, 249236, 23221, 1257, 65536⟩
    (by decide) selected_cut_08983

theorem selected_cut_08984 : selected 9 ⟨249253, by decide⟩
    (prefixPartial 12 23222) = some ⟨12, 2, 0, 249253, 23222, 1181, 65536⟩ := by
  decide +kernel

theorem context_12_23222_249253 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23222 ⟨249253, by decide⟩ :=
  accepted_of_selected 12 23222 ⟨249253, by decide⟩ ⟨12, 2, 0, 249253, 23222, 1181, 65536⟩
    (by decide) selected_cut_08984

theorem selected_cut_08985 : selected 9 ⟨249273, by decide⟩
    (prefixPartial 12 23223) = some ⟨12, 2, 0, 249273, 23223, 1301, 65536⟩ := by
  decide +kernel

theorem context_12_23223_249273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23223 ⟨249273, by decide⟩ :=
  accepted_of_selected 12 23223 ⟨249273, by decide⟩ ⟨12, 2, 0, 249273, 23223, 1301, 65536⟩
    (by decide) selected_cut_08985

theorem unmarked_context_11_5805_249274 : frontier 10 ⟨249274, by decide⟩
    (prefixCache 11 5805) (prefixPartial 11 5805) = false := by
  decide +kernel

theorem node_context_11_5805_249274 : EJMOriginalGlobalDAGData.nodes 10 ⟨249274, by decide⟩ =
    .split (coordinate 11) (![⟨249221, by decide⟩,⟨249236, by decide⟩,⟨249253, by decide⟩,⟨249273, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5805_249274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5805 ⟨249274, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5805
    ⟨249274, by decide⟩ (by decide) (![⟨249221, by decide⟩,⟨249236, by decide⟩,⟨249253, by decide⟩,⟨249273, by decide⟩]) unmarked_context_11_5805_249274 node_context_11_5805_249274
  intro a
  fin_cases a
  · exact context_12_23220_249221
  · exact context_12_23221_249236
  · exact context_12_23222_249253
  · exact context_12_23223_249273

theorem selected_cut_08986 : selected 9 ⟨249288, by decide⟩
    (prefixPartial 12 23224) = some ⟨12, 2, 0, 249288, 23224, 1117, 65536⟩ := by
  decide +kernel

theorem context_12_23224_249288 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23224 ⟨249288, by decide⟩ :=
  accepted_of_selected 12 23224 ⟨249288, by decide⟩ ⟨12, 2, 0, 249288, 23224, 1117, 65536⟩
    (by decide) selected_cut_08986

theorem selected_cut_08987 : selected 9 ⟨249305, by decide⟩
    (prefixPartial 12 23225) = some ⟨12, 2, 0, 249305, 23225, 1229, 65536⟩ := by
  decide +kernel

theorem context_12_23225_249305 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23225 ⟨249305, by decide⟩ :=
  accepted_of_selected 12 23225 ⟨249305, by decide⟩ ⟨12, 2, 0, 249305, 23225, 1229, 65536⟩
    (by decide) selected_cut_08987

theorem selected_cut_08988 : selected 9 ⟨249325, by decide⟩
    (prefixPartial 12 23226) = some ⟨12, 2, 0, 249325, 23226, 1473, 65536⟩ := by
  decide +kernel

theorem context_12_23226_249325 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23226 ⟨249325, by decide⟩ :=
  accepted_of_selected 12 23226 ⟨249325, by decide⟩ ⟨12, 2, 0, 249325, 23226, 1473, 65536⟩
    (by decide) selected_cut_08988

theorem selected_cut_08989 : selected 9 ⟨249340, by decide⟩
    (prefixPartial 12 23227) = some ⟨12, 2, 0, 249340, 23227, 1157, 65536⟩ := by
  decide +kernel

theorem context_12_23227_249340 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23227 ⟨249340, by decide⟩ :=
  accepted_of_selected 12 23227 ⟨249340, by decide⟩ ⟨12, 2, 0, 249340, 23227, 1157, 65536⟩
    (by decide) selected_cut_08989

theorem unmarked_context_11_5806_249341 : frontier 10 ⟨249341, by decide⟩
    (prefixCache 11 5806) (prefixPartial 11 5806) = false := by
  decide +kernel

theorem node_context_11_5806_249341 : EJMOriginalGlobalDAGData.nodes 10 ⟨249341, by decide⟩ =
    .split (coordinate 11) (![⟨249288, by decide⟩,⟨249305, by decide⟩,⟨249325, by decide⟩,⟨249340, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5806_249341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5806 ⟨249341, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5806
    ⟨249341, by decide⟩ (by decide) (![⟨249288, by decide⟩,⟨249305, by decide⟩,⟨249325, by decide⟩,⟨249340, by decide⟩]) unmarked_context_11_5806_249341 node_context_11_5806_249341
  intro a
  fin_cases a
  · exact context_12_23224_249288
  · exact context_12_23225_249305
  · exact context_12_23226_249325
  · exact context_12_23227_249340

theorem selected_cut_08990 : selected 9 ⟨249350, by decide⟩
    (prefixPartial 12 23228) = some ⟨12, 2, 0, 249350, 23228, 1137, 65536⟩ := by
  decide +kernel

theorem context_12_23228_249350 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23228 ⟨249350, by decide⟩ :=
  accepted_of_selected 12 23228 ⟨249350, by decide⟩ ⟨12, 2, 0, 249350, 23228, 1137, 65536⟩
    (by decide) selected_cut_08990

theorem selected_cut_08991 : selected 9 ⟨249362, by decide⟩
    (prefixPartial 12 23229) = some ⟨12, 2, 0, 249362, 23229, 1101, 65536⟩ := by
  decide +kernel

theorem context_12_23229_249362 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23229 ⟨249362, by decide⟩ :=
  accepted_of_selected 12 23229 ⟨249362, by decide⟩ ⟨12, 2, 0, 249362, 23229, 1101, 65536⟩
    (by decide) selected_cut_08991

theorem selected_cut_08992 : selected 9 ⟨249371, by decide⟩
    (prefixPartial 12 23230) = some ⟨12, 2, 0, 249371, 23230, 961, 65536⟩ := by
  decide +kernel

theorem context_12_23230_249371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23230 ⟨249371, by decide⟩ :=
  accepted_of_selected 12 23230 ⟨249371, by decide⟩ ⟨12, 2, 0, 249371, 23230, 961, 65536⟩
    (by decide) selected_cut_08992

theorem selected_cut_08993 : selected 9 ⟨249383, by decide⟩
    (prefixPartial 12 23231) = some ⟨12, 2, 0, 249383, 23231, 1133, 65536⟩ := by
  decide +kernel

theorem context_12_23231_249383 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23231 ⟨249383, by decide⟩ :=
  accepted_of_selected 12 23231 ⟨249383, by decide⟩ ⟨12, 2, 0, 249383, 23231, 1133, 65536⟩
    (by decide) selected_cut_08993

theorem unmarked_context_11_5807_249384 : frontier 10 ⟨249384, by decide⟩
    (prefixCache 11 5807) (prefixPartial 11 5807) = false := by
  decide +kernel

theorem node_context_11_5807_249384 : EJMOriginalGlobalDAGData.nodes 10 ⟨249384, by decide⟩ =
    .split (coordinate 11) (![⟨249350, by decide⟩,⟨249362, by decide⟩,⟨249371, by decide⟩,⟨249383, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5807_249384 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5807 ⟨249384, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5807
    ⟨249384, by decide⟩ (by decide) (![⟨249350, by decide⟩,⟨249362, by decide⟩,⟨249371, by decide⟩,⟨249383, by decide⟩]) unmarked_context_11_5807_249384 node_context_11_5807_249384
  intro a
  fin_cases a
  · exact context_12_23228_249350
  · exact context_12_23229_249362
  · exact context_12_23230_249371
  · exact context_12_23231_249383

theorem unmarked_context_10_1451_249385 : frontier 11 ⟨249385, by decide⟩
    (prefixCache 10 1451) (prefixPartial 10 1451) = false := by
  decide +kernel

theorem node_context_10_1451_249385 : EJMOriginalGlobalDAGData.nodes 11 ⟨249385, by decide⟩ =
    .split (coordinate 10) (![⟨249205, by decide⟩,⟨249274, by decide⟩,⟨249341, by decide⟩,⟨249384, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1451_249385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1451 ⟨249385, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1451
    ⟨249385, by decide⟩ (by decide) (![⟨249205, by decide⟩,⟨249274, by decide⟩,⟨249341, by decide⟩,⟨249384, by decide⟩]) unmarked_context_10_1451_249385 node_context_10_1451_249385
  intro a
  fin_cases a
  · exact context_11_5804_249205
  · exact context_11_5805_249274
  · exact context_11_5806_249341
  · exact context_11_5807_249384

theorem unmarked_context_9_362_249386 : frontier 12 ⟨249386, by decide⟩
    (prefixCache 9 362) (prefixPartial 9 362) = false := by
  decide +kernel

theorem node_context_9_362_249386 : EJMOriginalGlobalDAGData.nodes 12 ⟨249386, by decide⟩ =
    .split (coordinate 9) (![⟨248481, by decide⟩,⟨248884, by decide⟩,⟨249142, by decide⟩,⟨249385, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_362_249386 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 362 ⟨249386, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 362
    ⟨249386, by decide⟩ (by decide) (![⟨248481, by decide⟩,⟨248884, by decide⟩,⟨249142, by decide⟩,⟨249385, by decide⟩]) unmarked_context_9_362_249386 node_context_9_362_249386
  intro a
  fin_cases a
  · exact context_10_1448_248481
  · exact context_10_1449_248884
  · exact context_10_1450_249142
  · exact context_10_1451_249385

theorem selected_cut_08994 : selected 9 ⟨249399, by decide⟩
    (prefixPartial 12 23232) = some ⟨12, 2, 0, 249399, 23232, 1325, 65536⟩ := by
  decide +kernel

theorem context_12_23232_249399 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23232 ⟨249399, by decide⟩ :=
  accepted_of_selected 12 23232 ⟨249399, by decide⟩ ⟨12, 2, 0, 249399, 23232, 1325, 65536⟩
    (by decide) selected_cut_08994

theorem selected_cut_08995 : selected 9 ⟨249416, by decide⟩
    (prefixPartial 12 23233) = some ⟨12, 2, 0, 249416, 23233, 1297, 65536⟩ := by
  decide +kernel

theorem context_12_23233_249416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23233 ⟨249416, by decide⟩ :=
  accepted_of_selected 12 23233 ⟨249416, by decide⟩ ⟨12, 2, 0, 249416, 23233, 1297, 65536⟩
    (by decide) selected_cut_08995

theorem selected_cut_08996 : selected 9 ⟨249430, by decide⟩
    (prefixPartial 12 23234) = some ⟨12, 2, 0, 249430, 23234, 1269, 65536⟩ := by
  decide +kernel

theorem context_12_23234_249430 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23234 ⟨249430, by decide⟩ :=
  accepted_of_selected 12 23234 ⟨249430, by decide⟩ ⟨12, 2, 0, 249430, 23234, 1269, 65536⟩
    (by decide) selected_cut_08996

theorem selected_cut_08997 : selected 9 ⟨249448, by decide⟩
    (prefixPartial 12 23235) = some ⟨12, 2, 0, 249448, 23235, 1269, 65536⟩ := by
  decide +kernel

theorem context_12_23235_249448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23235 ⟨249448, by decide⟩ :=
  accepted_of_selected 12 23235 ⟨249448, by decide⟩ ⟨12, 2, 0, 249448, 23235, 1269, 65536⟩
    (by decide) selected_cut_08997

theorem unmarked_context_11_5808_249449 : frontier 10 ⟨249449, by decide⟩
    (prefixCache 11 5808) (prefixPartial 11 5808) = false := by
  decide +kernel

theorem node_context_11_5808_249449 : EJMOriginalGlobalDAGData.nodes 10 ⟨249449, by decide⟩ =
    .split (coordinate 11) (![⟨249399, by decide⟩,⟨249416, by decide⟩,⟨249430, by decide⟩,⟨249448, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5808_249449 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5808 ⟨249449, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5808
    ⟨249449, by decide⟩ (by decide) (![⟨249399, by decide⟩,⟨249416, by decide⟩,⟨249430, by decide⟩,⟨249448, by decide⟩]) unmarked_context_11_5808_249449 node_context_11_5808_249449
  intro a
  fin_cases a
  · exact context_12_23232_249399
  · exact context_12_23233_249416
  · exact context_12_23234_249430
  · exact context_12_23235_249448

theorem selected_cut_08998 : selected 9 ⟨249473, by decide⟩
    (prefixPartial 12 23236) = some ⟨12, 2, 0, 249473, 23236, 1169, 65536⟩ := by
  decide +kernel

theorem context_12_23236_249473 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23236 ⟨249473, by decide⟩ :=
  accepted_of_selected 12 23236 ⟨249473, by decide⟩ ⟨12, 2, 0, 249473, 23236, 1169, 65536⟩
    (by decide) selected_cut_08998

theorem selected_cut_08999 : selected 9 ⟨249483, by decide⟩
    (prefixPartial 12 23237) = some ⟨12, 2, 0, 249483, 23237, 1033, 65536⟩ := by
  decide +kernel

theorem context_12_23237_249483 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23237 ⟨249483, by decide⟩ :=
  accepted_of_selected 12 23237 ⟨249483, by decide⟩ ⟨12, 2, 0, 249483, 23237, 1033, 65536⟩
    (by decide) selected_cut_08999

theorem selected_cut_09000 : selected 9 ⟨249494, by decide⟩
    (prefixPartial 12 23238) = some ⟨12, 2, 0, 249494, 23238, 1077, 65536⟩ := by
  decide +kernel

theorem context_12_23238_249494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23238 ⟨249494, by decide⟩ :=
  accepted_of_selected 12 23238 ⟨249494, by decide⟩ ⟨12, 2, 0, 249494, 23238, 1077, 65536⟩
    (by decide) selected_cut_09000

theorem selected_cut_09001 : selected 9 ⟨249505, by decide⟩
    (prefixPartial 12 23239) = some ⟨12, 2, 0, 249505, 23239, 1061, 65536⟩ := by
  decide +kernel

theorem context_12_23239_249505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23239 ⟨249505, by decide⟩ :=
  accepted_of_selected 12 23239 ⟨249505, by decide⟩ ⟨12, 2, 0, 249505, 23239, 1061, 65536⟩
    (by decide) selected_cut_09001

theorem unmarked_context_11_5809_249506 : frontier 10 ⟨249506, by decide⟩
    (prefixCache 11 5809) (prefixPartial 11 5809) = false := by
  decide +kernel

theorem node_context_11_5809_249506 : EJMOriginalGlobalDAGData.nodes 10 ⟨249506, by decide⟩ =
    .split (coordinate 11) (![⟨249473, by decide⟩,⟨249483, by decide⟩,⟨249494, by decide⟩,⟨249505, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5809_249506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5809 ⟨249506, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5809
    ⟨249506, by decide⟩ (by decide) (![⟨249473, by decide⟩,⟨249483, by decide⟩,⟨249494, by decide⟩,⟨249505, by decide⟩]) unmarked_context_11_5809_249506 node_context_11_5809_249506
  intro a
  fin_cases a
  · exact context_12_23236_249473
  · exact context_12_23237_249483
  · exact context_12_23238_249494
  · exact context_12_23239_249505

theorem selected_cut_09002 : selected 10 ⟨249556, by decide⟩
    (prefixPartial 11 5810) = some ⟨11, 2, 0, 249556, 5810, 3905, 262144⟩ := by
  decide +kernel

theorem context_11_5810_249556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5810 ⟨249556, by decide⟩ :=
  accepted_of_selected 11 5810 ⟨249556, by decide⟩ ⟨11, 2, 0, 249556, 5810, 3905, 262144⟩
    (by decide) selected_cut_09002

theorem selected_cut_09003 : selected 10 ⟨249601, by decide⟩
    (prefixPartial 11 5811) = some ⟨11, 2, 0, 249601, 5811, 3841, 262144⟩ := by
  decide +kernel

theorem context_11_5811_249601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5811 ⟨249601, by decide⟩ :=
  accepted_of_selected 11 5811 ⟨249601, by decide⟩ ⟨11, 2, 0, 249601, 5811, 3841, 262144⟩
    (by decide) selected_cut_09003

theorem unmarked_context_10_1452_249602 : frontier 11 ⟨249602, by decide⟩
    (prefixCache 10 1452) (prefixPartial 10 1452) = false := by
  decide +kernel

theorem node_context_10_1452_249602 : EJMOriginalGlobalDAGData.nodes 11 ⟨249602, by decide⟩ =
    .split (coordinate 10) (![⟨249449, by decide⟩,⟨249506, by decide⟩,⟨249556, by decide⟩,⟨249601, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1452_249602 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1452 ⟨249602, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1452
    ⟨249602, by decide⟩ (by decide) (![⟨249449, by decide⟩,⟨249506, by decide⟩,⟨249556, by decide⟩,⟨249601, by decide⟩]) unmarked_context_10_1452_249602 node_context_10_1452_249602
  intro a
  fin_cases a
  · exact context_11_5808_249449
  · exact context_11_5809_249506
  · exact context_11_5810_249556
  · exact context_11_5811_249601

theorem selected_cut_09004 : selected 10 ⟨249644, by decide⟩
    (prefixPartial 11 5812) = some ⟨11, 2, 0, 249644, 5812, 3381, 262144⟩ := by
  decide +kernel

theorem context_11_5812_249644 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5812 ⟨249644, by decide⟩ :=
  accepted_of_selected 11 5812 ⟨249644, by decide⟩ ⟨11, 2, 0, 249644, 5812, 3381, 262144⟩
    (by decide) selected_cut_09004

theorem selected_cut_09005 : selected 10 ⟨249673, by decide⟩
    (prefixPartial 11 5813) = some ⟨11, 2, 0, 249673, 5813, 2617, 262144⟩ := by
  decide +kernel

theorem context_11_5813_249673 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5813 ⟨249673, by decide⟩ :=
  accepted_of_selected 11 5813 ⟨249673, by decide⟩ ⟨11, 2, 0, 249673, 5813, 2617, 262144⟩
    (by decide) selected_cut_09005

theorem selected_cut_09006 : selected 10 ⟨249698, by decide⟩
    (prefixPartial 11 5814) = some ⟨11, 2, 0, 249698, 5814, 2173, 262144⟩ := by
  decide +kernel

theorem context_11_5814_249698 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5814 ⟨249698, by decide⟩ :=
  accepted_of_selected 11 5814 ⟨249698, by decide⟩ ⟨11, 2, 0, 249698, 5814, 2173, 262144⟩
    (by decide) selected_cut_09006

theorem selected_cut_09007 : selected 10 ⟨249722, by decide⟩
    (prefixPartial 11 5815) = some ⟨11, 2, 0, 249722, 5815, 2001, 262144⟩ := by
  decide +kernel

theorem context_11_5815_249722 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5815 ⟨249722, by decide⟩ :=
  accepted_of_selected 11 5815 ⟨249722, by decide⟩ ⟨11, 2, 0, 249722, 5815, 2001, 262144⟩
    (by decide) selected_cut_09007

theorem unmarked_context_10_1453_249723 : frontier 11 ⟨249723, by decide⟩
    (prefixCache 10 1453) (prefixPartial 10 1453) = false := by
  decide +kernel

theorem node_context_10_1453_249723 : EJMOriginalGlobalDAGData.nodes 11 ⟨249723, by decide⟩ =
    .split (coordinate 10) (![⟨249644, by decide⟩,⟨249673, by decide⟩,⟨249698, by decide⟩,⟨249722, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1453_249723 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1453 ⟨249723, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1453
    ⟨249723, by decide⟩ (by decide) (![⟨249644, by decide⟩,⟨249673, by decide⟩,⟨249698, by decide⟩,⟨249722, by decide⟩]) unmarked_context_10_1453_249723 node_context_10_1453_249723
  intro a
  fin_cases a
  · exact context_11_5812_249644
  · exact context_11_5813_249673
  · exact context_11_5814_249698
  · exact context_11_5815_249722

theorem selected_cut_09008 : selected 10 ⟨249738, by decide⟩
    (prefixPartial 11 5816) = some ⟨11, 2, 0, 249738, 5816, 1561, 262144⟩ := by
  decide +kernel

theorem context_11_5816_249738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5816 ⟨249738, by decide⟩ :=
  accepted_of_selected 11 5816 ⟨249738, by decide⟩ ⟨11, 2, 0, 249738, 5816, 1561, 262144⟩
    (by decide) selected_cut_09008

theorem selected_cut_09009 : selected 10 ⟨249753, by decide⟩
    (prefixPartial 11 5817) = some ⟨11, 2, 0, 249753, 5817, 1201, 262144⟩ := by
  decide +kernel

theorem context_11_5817_249753 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5817 ⟨249753, by decide⟩ :=
  accepted_of_selected 11 5817 ⟨249753, by decide⟩ ⟨11, 2, 0, 249753, 5817, 1201, 262144⟩
    (by decide) selected_cut_09009

theorem selected_cut_09010 : selected 10 ⟨249767, by decide⟩
    (prefixPartial 11 5818) = some ⟨11, 2, 0, 249767, 5818, 849, 262144⟩ := by
  decide +kernel

theorem context_11_5818_249767 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5818 ⟨249767, by decide⟩ :=
  accepted_of_selected 11 5818 ⟨249767, by decide⟩ ⟨11, 2, 0, 249767, 5818, 849, 262144⟩
    (by decide) selected_cut_09010

theorem selected_cut_09011 : selected 10 ⟨249781, by decide⟩
    (prefixPartial 11 5819) = some ⟨11, 2, 0, 249781, 5819, 913, 262144⟩ := by
  decide +kernel

theorem context_11_5819_249781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5819 ⟨249781, by decide⟩ :=
  accepted_of_selected 11 5819 ⟨249781, by decide⟩ ⟨11, 2, 0, 249781, 5819, 913, 262144⟩
    (by decide) selected_cut_09011

theorem unmarked_context_10_1454_249782 : frontier 11 ⟨249782, by decide⟩
    (prefixCache 10 1454) (prefixPartial 10 1454) = false := by
  decide +kernel

theorem node_context_10_1454_249782 : EJMOriginalGlobalDAGData.nodes 11 ⟨249782, by decide⟩ =
    .split (coordinate 10) (![⟨249738, by decide⟩,⟨249753, by decide⟩,⟨249767, by decide⟩,⟨249781, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1454_249782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1454 ⟨249782, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1454
    ⟨249782, by decide⟩ (by decide) (![⟨249738, by decide⟩,⟨249753, by decide⟩,⟨249767, by decide⟩,⟨249781, by decide⟩]) unmarked_context_10_1454_249782 node_context_10_1454_249782
  intro a
  fin_cases a
  · exact context_11_5816_249738
  · exact context_11_5817_249753
  · exact context_11_5818_249767
  · exact context_11_5819_249781

theorem selected_cut_09012 : selected 11 ⟨249814, by decide⟩
    (prefixPartial 10 1455) = some ⟨10, 2, 0, 249814, 1455, 1701, 1048576⟩ := by
  decide +kernel

theorem context_10_1455_249814 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1455 ⟨249814, by decide⟩ :=
  accepted_of_selected 10 1455 ⟨249814, by decide⟩ ⟨10, 2, 0, 249814, 1455, 1701, 1048576⟩
    (by decide) selected_cut_09012

theorem unmarked_context_9_363_249815 : frontier 12 ⟨249815, by decide⟩
    (prefixCache 9 363) (prefixPartial 9 363) = false := by
  decide +kernel

theorem node_context_9_363_249815 : EJMOriginalGlobalDAGData.nodes 12 ⟨249815, by decide⟩ =
    .split (coordinate 9) (![⟨249602, by decide⟩,⟨249723, by decide⟩,⟨249782, by decide⟩,⟨249814, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_363_249815 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 363 ⟨249815, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 363
    ⟨249815, by decide⟩ (by decide) (![⟨249602, by decide⟩,⟨249723, by decide⟩,⟨249782, by decide⟩,⟨249814, by decide⟩]) unmarked_context_9_363_249815 node_context_9_363_249815
  intro a
  fin_cases a
  · exact context_10_1452_249602
  · exact context_10_1453_249723
  · exact context_10_1454_249782
  · exact context_10_1455_249814

theorem unmarked_context_8_90_249816 : frontier 13 ⟨249816, by decide⟩
    (prefixCache 8 90) (prefixPartial 8 90) = false := by
  decide +kernel

theorem node_context_8_90_249816 : EJMOriginalGlobalDAGData.nodes 13 ⟨249816, by decide⟩ =
    .split (coordinate 8) (![⟨243989, by decide⟩,⟨248020, by decide⟩,⟨249386, by decide⟩,⟨249815, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_90_249816 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 90 ⟨249816, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 90
    ⟨249816, by decide⟩ (by decide) (![⟨243989, by decide⟩,⟨248020, by decide⟩,⟨249386, by decide⟩,⟨249815, by decide⟩]) unmarked_context_8_90_249816 node_context_8_90_249816
  intro a
  fin_cases a
  · exact context_9_360_243989
  · exact context_9_361_248020
  · exact context_9_362_249386
  · exact context_9_363_249815

theorem selected_cut_09013 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 23296) = some ⟨12, 1, 0, 34034, 23296, 1, 65536⟩ := by
  decide +kernel

theorem context_12_23296_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23296 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 23296 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 23296, 1, 65536⟩
    (by decide) selected_cut_09013

theorem selected_cut_09014 : selected 7 ⟨249844, by decide⟩
    (prefixPartial 14 372752) = some ⟨14, 2, 0, 249844, 372752, 1229, 4096⟩ := by
  decide +kernel

theorem context_14_372752_249844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372752 ⟨249844, by decide⟩ :=
  accepted_of_selected 14 372752 ⟨249844, by decide⟩ ⟨14, 2, 0, 249844, 372752, 1229, 4096⟩
    (by decide) selected_cut_09014

theorem selected_cut_09015 : selected 7 ⟨249860, by decide⟩
    (prefixPartial 14 372753) = some ⟨14, 2, 0, 249860, 372753, 1101, 4096⟩ := by
  decide +kernel

theorem context_14_372753_249860 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372753 ⟨249860, by decide⟩ :=
  accepted_of_selected 14 372753 ⟨249860, by decide⟩ ⟨14, 2, 0, 249860, 372753, 1101, 4096⟩
    (by decide) selected_cut_09015

theorem selected_cut_09016 : selected 7 ⟨249876, by decide⟩
    (prefixPartial 14 372754) = some ⟨14, 2, 0, 249876, 372754, 1053, 4096⟩ := by
  decide +kernel

theorem context_14_372754_249876 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372754 ⟨249876, by decide⟩ :=
  accepted_of_selected 14 372754 ⟨249876, by decide⟩ ⟨14, 2, 0, 249876, 372754, 1053, 4096⟩
    (by decide) selected_cut_09016

theorem selected_cut_09017 : selected 7 ⟨249888, by decide⟩
    (prefixPartial 14 372755) = some ⟨14, 2, 0, 249888, 372755, 865, 4096⟩ := by
  decide +kernel

theorem context_14_372755_249888 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372755 ⟨249888, by decide⟩ :=
  accepted_of_selected 14 372755 ⟨249888, by decide⟩ ⟨14, 2, 0, 249888, 372755, 865, 4096⟩
    (by decide) selected_cut_09017

theorem unmarked_context_13_93188_249889 : frontier 8 ⟨249889, by decide⟩
    (prefixCache 13 93188) (prefixPartial 13 93188) = false := by
  decide +kernel

theorem node_context_13_93188_249889 : EJMOriginalGlobalDAGData.nodes 8 ⟨249889, by decide⟩ =
    .split (coordinate 13) (![⟨249844, by decide⟩,⟨249860, by decide⟩,⟨249876, by decide⟩,⟨249888, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_93188_249889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93188 ⟨249889, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 93188
    ⟨249889, by decide⟩ (by decide) (![⟨249844, by decide⟩,⟨249860, by decide⟩,⟨249876, by decide⟩,⟨249888, by decide⟩]) unmarked_context_13_93188_249889 node_context_13_93188_249889
  intro a
  fin_cases a
  · exact context_14_372752_249844
  · exact context_14_372753_249860
  · exact context_14_372754_249876
  · exact context_14_372755_249888

theorem selected_cut_09018 : selected 8 ⟨249958, by decide⟩
    (prefixPartial 13 93189) = some ⟨13, 2, 0, 249958, 93189, 3881, 16384⟩ := by
  decide +kernel

theorem context_13_93189_249958 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93189 ⟨249958, by decide⟩ :=
  accepted_of_selected 13 93189 ⟨249958, by decide⟩ ⟨13, 2, 0, 249958, 93189, 3881, 16384⟩
    (by decide) selected_cut_09018

theorem selected_cut_09019 : selected 8 ⟨249998, by decide⟩
    (prefixPartial 13 93190) = some ⟨13, 2, 0, 249998, 93190, 2281, 16384⟩ := by
  decide +kernel

theorem context_13_93190_249998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93190 ⟨249998, by decide⟩ :=
  accepted_of_selected 13 93190 ⟨249998, by decide⟩ ⟨13, 2, 0, 249998, 93190, 2281, 16384⟩
    (by decide) selected_cut_09019

theorem selected_cut_09020 : selected 8 ⟨250018, by decide⟩
    (prefixPartial 13 93191) = some ⟨13, 2, 0, 250018, 93191, 933, 16384⟩ := by
  decide +kernel

theorem context_13_93191_250018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93191 ⟨250018, by decide⟩ :=
  accepted_of_selected 13 93191 ⟨250018, by decide⟩ ⟨13, 2, 0, 250018, 93191, 933, 16384⟩
    (by decide) selected_cut_09020

theorem unmarked_context_12_23297_250019 : frontier 9 ⟨250019, by decide⟩
    (prefixCache 12 23297) (prefixPartial 12 23297) = false := by
  decide +kernel

theorem node_context_12_23297_250019 : EJMOriginalGlobalDAGData.nodes 9 ⟨250019, by decide⟩ =
    .split (coordinate 12) (![⟨249889, by decide⟩,⟨249958, by decide⟩,⟨249998, by decide⟩,⟨250018, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23297_250019 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23297 ⟨250019, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23297
    ⟨250019, by decide⟩ (by decide) (![⟨249889, by decide⟩,⟨249958, by decide⟩,⟨249998, by decide⟩,⟨250018, by decide⟩]) unmarked_context_12_23297_250019 node_context_12_23297_250019
  intro a
  fin_cases a
  · exact context_13_93188_249889
  · exact context_13_93189_249958
  · exact context_13_93190_249998
  · exact context_13_93191_250018

theorem selected_cut_09021 : selected 7 ⟨250048, by decide⟩
    (prefixPartial 14 372768) = some ⟨14, 2, 0, 250048, 372768, 929, 4096⟩ := by
  decide +kernel

theorem context_14_372768_250048 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372768 ⟨250048, by decide⟩ :=
  accepted_of_selected 14 372768 ⟨250048, by decide⟩ ⟨14, 2, 0, 250048, 372768, 929, 4096⟩
    (by decide) selected_cut_09021

theorem selected_cut_09022 : selected 7 ⟨250064, by decide⟩
    (prefixPartial 14 372769) = some ⟨14, 2, 0, 250064, 372769, 1205, 4096⟩ := by
  decide +kernel

theorem context_14_372769_250064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372769 ⟨250064, by decide⟩ :=
  accepted_of_selected 14 372769 ⟨250064, by decide⟩ ⟨14, 2, 0, 250064, 372769, 1205, 4096⟩
    (by decide) selected_cut_09022

theorem selected_cut_09023 : selected 7 ⟨250099, by decide⟩
    (prefixPartial 14 372770) = some ⟨14, 2, 0, 250099, 372770, 1313, 4096⟩ := by
  decide +kernel

theorem context_14_372770_250099 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372770 ⟨250099, by decide⟩ :=
  accepted_of_selected 14 372770 ⟨250099, by decide⟩ ⟨14, 2, 0, 250099, 372770, 1313, 4096⟩
    (by decide) selected_cut_09023

theorem selected_cut_09024 : selected 7 ⟨250123, by decide⟩
    (prefixPartial 14 372771) = some ⟨14, 2, 0, 250123, 372771, 965, 4096⟩ := by
  decide +kernel

theorem context_14_372771_250123 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 372771 ⟨250123, by decide⟩ :=
  accepted_of_selected 14 372771 ⟨250123, by decide⟩ ⟨14, 2, 0, 250123, 372771, 965, 4096⟩
    (by decide) selected_cut_09024

theorem unmarked_context_13_93192_250124 : frontier 8 ⟨250124, by decide⟩
    (prefixCache 13 93192) (prefixPartial 13 93192) = false := by
  decide +kernel

theorem node_context_13_93192_250124 : EJMOriginalGlobalDAGData.nodes 8 ⟨250124, by decide⟩ =
    .split (coordinate 13) (![⟨250048, by decide⟩,⟨250064, by decide⟩,⟨250099, by decide⟩,⟨250123, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_93192_250124 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93192 ⟨250124, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 93192
    ⟨250124, by decide⟩ (by decide) (![⟨250048, by decide⟩,⟨250064, by decide⟩,⟨250099, by decide⟩,⟨250123, by decide⟩]) unmarked_context_13_93192_250124 node_context_13_93192_250124
  intro a
  fin_cases a
  · exact context_14_372768_250048
  · exact context_14_372769_250064
  · exact context_14_372770_250099
  · exact context_14_372771_250123

theorem selected_cut_09025 : selected 8 ⟨250231, by decide⟩
    (prefixPartial 13 93193) = some ⟨13, 2, 0, 250231, 93193, 2577, 16384⟩ := by
  decide +kernel

theorem context_13_93193_250231 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93193 ⟨250231, by decide⟩ :=
  accepted_of_selected 13 93193 ⟨250231, by decide⟩ ⟨13, 2, 0, 250231, 93193, 2577, 16384⟩
    (by decide) selected_cut_09025

theorem selected_cut_09026 : selected 8 ⟨250283, by decide⟩
    (prefixPartial 13 93194) = some ⟨13, 2, 0, 250283, 93194, 765, 16384⟩ := by
  decide +kernel

theorem context_13_93194_250283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93194 ⟨250283, by decide⟩ :=
  accepted_of_selected 13 93194 ⟨250283, by decide⟩ ⟨13, 2, 0, 250283, 93194, 765, 16384⟩
    (by decide) selected_cut_09026

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
