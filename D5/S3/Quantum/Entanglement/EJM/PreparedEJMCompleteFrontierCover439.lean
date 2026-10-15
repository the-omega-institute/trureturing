/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover438
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_11_84356_1152027 : frontier 10 ⟨1152027, by decide⟩
    (prefixCache 11 84356) (prefixPartial 11 84356) = false := by
  decide +kernel

theorem node_context_11_84356_1152027 : EJMOriginalGlobalDAGData.nodes 10 ⟨1152027, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1151931, by decide⟩,⟨1151970, by decide⟩,⟨1152026, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84356_1152027 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84356 ⟨1152027, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84356
    ⟨1152027, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1151931, by decide⟩,⟨1151970, by decide⟩,⟨1152026, by decide⟩]) unmarked_context_11_84356_1152027 node_context_11_84356_1152027
  intro a
  fin_cases a
  · exact context_12_337424_1108174
  · exact context_12_337425_1151931
  · exact context_12_337426_1151970
  · exact context_12_337427_1152026

theorem selected_cut_42147 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 84357) = some ⟨11, 1, 0, 892405, 84357, 1, 262144⟩ := by
  decide +kernel

theorem context_11_84357_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84357 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 84357 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 84357, 1, 262144⟩
    (by decide) selected_cut_42147

theorem selected_cut_42148 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 337432) = some ⟨12, 1, 0, 1108174, 337432, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337432_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337432 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 337432 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 337432, 1, 65536⟩
    (by decide) selected_cut_42148

theorem selected_cut_42149 : selected 9 ⟨1152055, by decide⟩
    (prefixPartial 12 337433) = some ⟨12, 2, 0, 1152055, 337433, 2133, 65536⟩ := by
  decide +kernel

theorem context_12_337433_1152055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337433 ⟨1152055, by decide⟩ :=
  accepted_of_selected 12 337433 ⟨1152055, by decide⟩ ⟨12, 2, 0, 1152055, 337433, 2133, 65536⟩
    (by decide) selected_cut_42149

theorem selected_cut_42150 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 337434) = some ⟨12, 1, 0, 893903, 337434, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337434_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337434 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 337434 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 337434, 1, 65536⟩
    (by decide) selected_cut_42150

theorem selected_cut_42151 : selected 9 ⟨1152107, by decide⟩
    (prefixPartial 12 337435) = some ⟨12, 2, 0, 1152107, 337435, 2749, 65536⟩ := by
  decide +kernel

theorem context_12_337435_1152107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337435 ⟨1152107, by decide⟩ :=
  accepted_of_selected 12 337435 ⟨1152107, by decide⟩ ⟨12, 2, 0, 1152107, 337435, 2749, 65536⟩
    (by decide) selected_cut_42151

theorem unmarked_context_11_84358_1152108 : frontier 10 ⟨1152108, by decide⟩
    (prefixCache 11 84358) (prefixPartial 11 84358) = false := by
  decide +kernel

theorem node_context_11_84358_1152108 : EJMOriginalGlobalDAGData.nodes 10 ⟨1152108, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1152055, by decide⟩,⟨893903, by decide⟩,⟨1152107, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84358_1152108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84358 ⟨1152108, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84358
    ⟨1152108, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1152055, by decide⟩,⟨893903, by decide⟩,⟨1152107, by decide⟩]) unmarked_context_11_84358_1152108 node_context_11_84358_1152108
  intro a
  fin_cases a
  · exact context_12_337432_1108174
  · exact context_12_337433_1152055
  · exact context_12_337434_893903
  · exact context_12_337435_1152107

theorem selected_cut_42152 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 337436) = some ⟨12, 1, 0, 1108174, 337436, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337436_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337436 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 337436 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 337436, 1, 65536⟩
    (by decide) selected_cut_42152

theorem selected_cut_42153 : selected 9 ⟨1152137, by decide⟩
    (prefixPartial 12 337437) = some ⟨12, 2, 0, 1152137, 337437, 2197, 65536⟩ := by
  decide +kernel

theorem context_12_337437_1152137 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337437 ⟨1152137, by decide⟩ :=
  accepted_of_selected 12 337437 ⟨1152137, by decide⟩ ⟨12, 2, 0, 1152137, 337437, 2197, 65536⟩
    (by decide) selected_cut_42153

theorem selected_cut_42154 : selected 9 ⟨1152171, by decide⟩
    (prefixPartial 12 337438) = some ⟨12, 2, 0, 1152171, 337438, 2577, 65536⟩ := by
  decide +kernel

theorem context_12_337438_1152171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337438 ⟨1152171, by decide⟩ :=
  accepted_of_selected 12 337438 ⟨1152171, by decide⟩ ⟨12, 2, 0, 1152171, 337438, 2577, 65536⟩
    (by decide) selected_cut_42154

theorem selected_cut_42155 : selected 9 ⟨1152208, by decide⟩
    (prefixPartial 12 337439) = some ⟨12, 2, 0, 1152208, 337439, 2693, 65536⟩ := by
  decide +kernel

theorem context_12_337439_1152208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337439 ⟨1152208, by decide⟩ :=
  accepted_of_selected 12 337439 ⟨1152208, by decide⟩ ⟨12, 2, 0, 1152208, 337439, 2693, 65536⟩
    (by decide) selected_cut_42155

theorem unmarked_context_11_84359_1152209 : frontier 10 ⟨1152209, by decide⟩
    (prefixCache 11 84359) (prefixPartial 11 84359) = false := by
  decide +kernel

theorem node_context_11_84359_1152209 : EJMOriginalGlobalDAGData.nodes 10 ⟨1152209, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1152137, by decide⟩,⟨1152171, by decide⟩,⟨1152208, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84359_1152209 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84359 ⟨1152209, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84359
    ⟨1152209, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1152137, by decide⟩,⟨1152171, by decide⟩,⟨1152208, by decide⟩]) unmarked_context_11_84359_1152209 node_context_11_84359_1152209
  intro a
  fin_cases a
  · exact context_12_337436_1108174
  · exact context_12_337437_1152137
  · exact context_12_337438_1152171
  · exact context_12_337439_1152208

theorem unmarked_context_10_21089_1152210 : frontier 11 ⟨1152210, by decide⟩
    (prefixCache 10 21089) (prefixPartial 10 21089) = false := by
  decide +kernel

theorem node_context_10_21089_1152210 : EJMOriginalGlobalDAGData.nodes 11 ⟨1152210, by decide⟩ =
    .split (coordinate 10) (![⟨1152027, by decide⟩,⟨892405, by decide⟩,⟨1152108, by decide⟩,⟨1152209, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21089_1152210 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21089 ⟨1152210, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21089
    ⟨1152210, by decide⟩ (by decide) (![⟨1152027, by decide⟩,⟨892405, by decide⟩,⟨1152108, by decide⟩,⟨1152209, by decide⟩]) unmarked_context_10_21089_1152210 node_context_10_21089_1152210
  intro a
  fin_cases a
  · exact context_11_84356_1152027
  · exact context_11_84357_892405
  · exact context_11_84358_1152108
  · exact context_11_84359_1152209

theorem selected_cut_42156 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 337440) = some ⟨12, 1, 0, 1108174, 337440, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337440_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337440 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 337440 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 337440, 1, 65536⟩
    (by decide) selected_cut_42156

theorem selected_cut_42157 : selected 9 ⟨1152250, by decide⟩
    (prefixPartial 12 337441) = some ⟨12, 2, 0, 1152250, 337441, 2609, 65536⟩ := by
  decide +kernel

theorem context_12_337441_1152250 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337441 ⟨1152250, by decide⟩ :=
  accepted_of_selected 12 337441 ⟨1152250, by decide⟩ ⟨12, 2, 0, 1152250, 337441, 2609, 65536⟩
    (by decide) selected_cut_42157

theorem selected_cut_42158 : selected 9 ⟨1152292, by decide⟩
    (prefixPartial 12 337442) = some ⟨12, 2, 0, 1152292, 337442, 2825, 65536⟩ := by
  decide +kernel

theorem context_12_337442_1152292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337442 ⟨1152292, by decide⟩ :=
  accepted_of_selected 12 337442 ⟨1152292, by decide⟩ ⟨12, 2, 0, 1152292, 337442, 2825, 65536⟩
    (by decide) selected_cut_42158

theorem selected_cut_42159 : selected 9 ⟨1152356, by decide⟩
    (prefixPartial 12 337443) = some ⟨12, 2, 0, 1152356, 337443, 3401, 65536⟩ := by
  decide +kernel

theorem context_12_337443_1152356 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337443 ⟨1152356, by decide⟩ :=
  accepted_of_selected 12 337443 ⟨1152356, by decide⟩ ⟨12, 2, 0, 1152356, 337443, 3401, 65536⟩
    (by decide) selected_cut_42159

theorem unmarked_context_11_84360_1152357 : frontier 10 ⟨1152357, by decide⟩
    (prefixCache 11 84360) (prefixPartial 11 84360) = false := by
  decide +kernel

theorem node_context_11_84360_1152357 : EJMOriginalGlobalDAGData.nodes 10 ⟨1152357, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1152250, by decide⟩,⟨1152292, by decide⟩,⟨1152356, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84360_1152357 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84360 ⟨1152357, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84360
    ⟨1152357, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1152250, by decide⟩,⟨1152292, by decide⟩,⟨1152356, by decide⟩]) unmarked_context_11_84360_1152357 node_context_11_84360_1152357
  intro a
  fin_cases a
  · exact context_12_337440_1108174
  · exact context_12_337441_1152250
  · exact context_12_337442_1152292
  · exact context_12_337443_1152356

theorem selected_cut_42160 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 337444) = some ⟨12, 1, 0, 1108174, 337444, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337444_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337444 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 337444 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 337444, 1, 65536⟩
    (by decide) selected_cut_42160

theorem selected_cut_42161 : selected 9 ⟨1152383, by decide⟩
    (prefixPartial 12 337445) = some ⟨12, 2, 0, 1152383, 337445, 2369, 65536⟩ := by
  decide +kernel

theorem context_12_337445_1152383 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337445 ⟨1152383, by decide⟩ :=
  accepted_of_selected 12 337445 ⟨1152383, by decide⟩ ⟨12, 2, 0, 1152383, 337445, 2369, 65536⟩
    (by decide) selected_cut_42161

theorem selected_cut_42162 : selected 9 ⟨1152419, by decide⟩
    (prefixPartial 12 337446) = some ⟨12, 2, 0, 1152419, 337446, 2505, 65536⟩ := by
  decide +kernel

theorem context_12_337446_1152419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337446 ⟨1152419, by decide⟩ :=
  accepted_of_selected 12 337446 ⟨1152419, by decide⟩ ⟨12, 2, 0, 1152419, 337446, 2505, 65536⟩
    (by decide) selected_cut_42162

theorem selected_cut_42163 : selected 9 ⟨1152476, by decide⟩
    (prefixPartial 12 337447) = some ⟨12, 2, 0, 1152476, 337447, 3045, 65536⟩ := by
  decide +kernel

theorem context_12_337447_1152476 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337447 ⟨1152476, by decide⟩ :=
  accepted_of_selected 12 337447 ⟨1152476, by decide⟩ ⟨12, 2, 0, 1152476, 337447, 3045, 65536⟩
    (by decide) selected_cut_42163

theorem unmarked_context_11_84361_1152477 : frontier 10 ⟨1152477, by decide⟩
    (prefixCache 11 84361) (prefixPartial 11 84361) = false := by
  decide +kernel

theorem node_context_11_84361_1152477 : EJMOriginalGlobalDAGData.nodes 10 ⟨1152477, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1152383, by decide⟩,⟨1152419, by decide⟩,⟨1152476, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84361_1152477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84361 ⟨1152477, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84361
    ⟨1152477, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1152383, by decide⟩,⟨1152419, by decide⟩,⟨1152476, by decide⟩]) unmarked_context_11_84361_1152477 node_context_11_84361_1152477
  intro a
  fin_cases a
  · exact context_12_337444_1108174
  · exact context_12_337445_1152383
  · exact context_12_337446_1152419
  · exact context_12_337447_1152476

theorem selected_cut_42164 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 337448) = some ⟨12, 1, 0, 1108174, 337448, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337448_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337448 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 337448 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 337448, 1, 65536⟩
    (by decide) selected_cut_42164

theorem selected_cut_42165 : selected 9 ⟨1152539, by decide⟩
    (prefixPartial 12 337449) = some ⟨12, 2, 0, 1152539, 337449, 1317, 65536⟩ := by
  decide +kernel

theorem context_12_337449_1152539 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337449 ⟨1152539, by decide⟩ :=
  accepted_of_selected 12 337449 ⟨1152539, by decide⟩ ⟨12, 2, 0, 1152539, 337449, 1317, 65536⟩
    (by decide) selected_cut_42165

theorem selected_cut_42166 : selected 9 ⟨1113261, by decide⟩
    (prefixPartial 12 337450) = some ⟨12, 1, 0, 1113261, 337450, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337450_1113261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337450 ⟨1113261, by decide⟩ :=
  accepted_of_selected 12 337450 ⟨1113261, by decide⟩ ⟨12, 1, 0, 1113261, 337450, 1, 65536⟩
    (by decide) selected_cut_42166

theorem selected_cut_42167 : selected 9 ⟨1152589, by decide⟩
    (prefixPartial 12 337451) = some ⟨12, 2, 0, 1152589, 337451, 2817, 65536⟩ := by
  decide +kernel

theorem context_12_337451_1152589 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337451 ⟨1152589, by decide⟩ :=
  accepted_of_selected 12 337451 ⟨1152589, by decide⟩ ⟨12, 2, 0, 1152589, 337451, 2817, 65536⟩
    (by decide) selected_cut_42167

theorem unmarked_context_11_84362_1152590 : frontier 10 ⟨1152590, by decide⟩
    (prefixCache 11 84362) (prefixPartial 11 84362) = false := by
  decide +kernel

theorem node_context_11_84362_1152590 : EJMOriginalGlobalDAGData.nodes 10 ⟨1152590, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1152539, by decide⟩,⟨1113261, by decide⟩,⟨1152589, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84362_1152590 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84362 ⟨1152590, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84362
    ⟨1152590, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1152539, by decide⟩,⟨1113261, by decide⟩,⟨1152589, by decide⟩]) unmarked_context_11_84362_1152590 node_context_11_84362_1152590
  intro a
  fin_cases a
  · exact context_12_337448_1108174
  · exact context_12_337449_1152539
  · exact context_12_337450_1113261
  · exact context_12_337451_1152589

theorem selected_cut_42168 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 337452) = some ⟨12, 1, 0, 1108174, 337452, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337452_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337452 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 337452 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 337452, 1, 65536⟩
    (by decide) selected_cut_42168

theorem selected_cut_42169 : selected 9 ⟨1152620, by decide⟩
    (prefixPartial 12 337453) = some ⟨12, 2, 0, 1152620, 337453, 2337, 65536⟩ := by
  decide +kernel

theorem context_12_337453_1152620 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337453 ⟨1152620, by decide⟩ :=
  accepted_of_selected 12 337453 ⟨1152620, by decide⟩ ⟨12, 2, 0, 1152620, 337453, 2337, 65536⟩
    (by decide) selected_cut_42169

theorem selected_cut_42170 : selected 9 ⟨1152659, by decide⟩
    (prefixPartial 12 337454) = some ⟨12, 2, 0, 1152659, 337454, 2493, 65536⟩ := by
  decide +kernel

theorem context_12_337454_1152659 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337454 ⟨1152659, by decide⟩ :=
  accepted_of_selected 12 337454 ⟨1152659, by decide⟩ ⟨12, 2, 0, 1152659, 337454, 2493, 65536⟩
    (by decide) selected_cut_42170

theorem selected_cut_42171 : selected 9 ⟨1152708, by decide⟩
    (prefixPartial 12 337455) = some ⟨12, 2, 0, 1152708, 337455, 2885, 65536⟩ := by
  decide +kernel

theorem context_12_337455_1152708 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337455 ⟨1152708, by decide⟩ :=
  accepted_of_selected 12 337455 ⟨1152708, by decide⟩ ⟨12, 2, 0, 1152708, 337455, 2885, 65536⟩
    (by decide) selected_cut_42171

theorem unmarked_context_11_84363_1152709 : frontier 10 ⟨1152709, by decide⟩
    (prefixCache 11 84363) (prefixPartial 11 84363) = false := by
  decide +kernel

theorem node_context_11_84363_1152709 : EJMOriginalGlobalDAGData.nodes 10 ⟨1152709, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1152620, by decide⟩,⟨1152659, by decide⟩,⟨1152708, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84363_1152709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84363 ⟨1152709, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84363
    ⟨1152709, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1152620, by decide⟩,⟨1152659, by decide⟩,⟨1152708, by decide⟩]) unmarked_context_11_84363_1152709 node_context_11_84363_1152709
  intro a
  fin_cases a
  · exact context_12_337452_1108174
  · exact context_12_337453_1152620
  · exact context_12_337454_1152659
  · exact context_12_337455_1152708

theorem unmarked_context_10_21090_1152710 : frontier 11 ⟨1152710, by decide⟩
    (prefixCache 10 21090) (prefixPartial 10 21090) = false := by
  decide +kernel

theorem node_context_10_21090_1152710 : EJMOriginalGlobalDAGData.nodes 11 ⟨1152710, by decide⟩ =
    .split (coordinate 10) (![⟨1152357, by decide⟩,⟨1152477, by decide⟩,⟨1152590, by decide⟩,⟨1152709, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21090_1152710 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21090 ⟨1152710, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21090
    ⟨1152710, by decide⟩ (by decide) (![⟨1152357, by decide⟩,⟨1152477, by decide⟩,⟨1152590, by decide⟩,⟨1152709, by decide⟩]) unmarked_context_10_21090_1152710 node_context_10_21090_1152710
  intro a
  fin_cases a
  · exact context_11_84360_1152357
  · exact context_11_84361_1152477
  · exact context_11_84362_1152590
  · exact context_11_84363_1152709

theorem selected_cut_42172 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 337456) = some ⟨12, 1, 0, 1108174, 337456, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337456_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337456 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 337456 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 337456, 1, 65536⟩
    (by decide) selected_cut_42172

theorem selected_cut_42173 : selected 9 ⟨1152738, by decide⟩
    (prefixPartial 12 337457) = some ⟨12, 2, 0, 1152738, 337457, 2209, 65536⟩ := by
  decide +kernel

theorem context_12_337457_1152738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337457 ⟨1152738, by decide⟩ :=
  accepted_of_selected 12 337457 ⟨1152738, by decide⟩ ⟨12, 2, 0, 1152738, 337457, 2209, 65536⟩
    (by decide) selected_cut_42173

theorem selected_cut_42174 : selected 9 ⟨1152782, by decide⟩
    (prefixPartial 12 337458) = some ⟨12, 2, 0, 1152782, 337458, 2449, 65536⟩ := by
  decide +kernel

theorem context_12_337458_1152782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337458 ⟨1152782, by decide⟩ :=
  accepted_of_selected 12 337458 ⟨1152782, by decide⟩ ⟨12, 2, 0, 1152782, 337458, 2449, 65536⟩
    (by decide) selected_cut_42174

theorem selected_cut_42175 : selected 9 ⟨1152834, by decide⟩
    (prefixPartial 12 337459) = some ⟨12, 2, 0, 1152834, 337459, 3061, 65536⟩ := by
  decide +kernel

theorem context_12_337459_1152834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337459 ⟨1152834, by decide⟩ :=
  accepted_of_selected 12 337459 ⟨1152834, by decide⟩ ⟨12, 2, 0, 1152834, 337459, 3061, 65536⟩
    (by decide) selected_cut_42175

theorem unmarked_context_11_84364_1152835 : frontier 10 ⟨1152835, by decide⟩
    (prefixCache 11 84364) (prefixPartial 11 84364) = false := by
  decide +kernel

theorem node_context_11_84364_1152835 : EJMOriginalGlobalDAGData.nodes 10 ⟨1152835, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1152738, by decide⟩,⟨1152782, by decide⟩,⟨1152834, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84364_1152835 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84364 ⟨1152835, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84364
    ⟨1152835, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1152738, by decide⟩,⟨1152782, by decide⟩,⟨1152834, by decide⟩]) unmarked_context_11_84364_1152835 node_context_11_84364_1152835
  intro a
  fin_cases a
  · exact context_12_337456_1108174
  · exact context_12_337457_1152738
  · exact context_12_337458_1152782
  · exact context_12_337459_1152834

theorem selected_cut_42176 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 337460) = some ⟨12, 1, 0, 1108174, 337460, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337460_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337460 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 337460 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 337460, 1, 65536⟩
    (by decide) selected_cut_42176

theorem selected_cut_42177 : selected 9 ⟨1152856, by decide⟩
    (prefixPartial 12 337461) = some ⟨12, 2, 0, 1152856, 337461, 1957, 65536⟩ := by
  decide +kernel

theorem context_12_337461_1152856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337461 ⟨1152856, by decide⟩ :=
  accepted_of_selected 12 337461 ⟨1152856, by decide⟩ ⟨12, 2, 0, 1152856, 337461, 1957, 65536⟩
    (by decide) selected_cut_42177

theorem selected_cut_42178 : selected 9 ⟨1152885, by decide⟩
    (prefixPartial 12 337462) = some ⟨12, 2, 0, 1152885, 337462, 1993, 65536⟩ := by
  decide +kernel

theorem context_12_337462_1152885 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337462 ⟨1152885, by decide⟩ :=
  accepted_of_selected 12 337462 ⟨1152885, by decide⟩ ⟨12, 2, 0, 1152885, 337462, 1993, 65536⟩
    (by decide) selected_cut_42178

theorem selected_cut_42179 : selected 9 ⟨1152934, by decide⟩
    (prefixPartial 12 337463) = some ⟨12, 2, 0, 1152934, 337463, 2593, 65536⟩ := by
  decide +kernel

theorem context_12_337463_1152934 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337463 ⟨1152934, by decide⟩ :=
  accepted_of_selected 12 337463 ⟨1152934, by decide⟩ ⟨12, 2, 0, 1152934, 337463, 2593, 65536⟩
    (by decide) selected_cut_42179

theorem unmarked_context_11_84365_1152935 : frontier 10 ⟨1152935, by decide⟩
    (prefixCache 11 84365) (prefixPartial 11 84365) = false := by
  decide +kernel

theorem node_context_11_84365_1152935 : EJMOriginalGlobalDAGData.nodes 10 ⟨1152935, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1152856, by decide⟩,⟨1152885, by decide⟩,⟨1152934, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84365_1152935 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84365 ⟨1152935, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84365
    ⟨1152935, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1152856, by decide⟩,⟨1152885, by decide⟩,⟨1152934, by decide⟩]) unmarked_context_11_84365_1152935 node_context_11_84365_1152935
  intro a
  fin_cases a
  · exact context_12_337460_1108174
  · exact context_12_337461_1152856
  · exact context_12_337462_1152885
  · exact context_12_337463_1152934

theorem selected_cut_42180 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 337464) = some ⟨12, 1, 0, 1108174, 337464, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337464_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337464 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 337464 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 337464, 1, 65536⟩
    (by decide) selected_cut_42180

theorem selected_cut_42181 : selected 9 ⟨1152958, by decide⟩
    (prefixPartial 12 337465) = some ⟨12, 2, 0, 1152958, 337465, 1917, 65536⟩ := by
  decide +kernel

theorem context_12_337465_1152958 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337465 ⟨1152958, by decide⟩ :=
  accepted_of_selected 12 337465 ⟨1152958, by decide⟩ ⟨12, 2, 0, 1152958, 337465, 1917, 65536⟩
    (by decide) selected_cut_42181

theorem selected_cut_42182 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 337466) = some ⟨12, 1, 0, 893903, 337466, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337466_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337466 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 337466 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 337466, 1, 65536⟩
    (by decide) selected_cut_42182

theorem selected_cut_42183 : selected 9 ⟨1153009, by decide⟩
    (prefixPartial 12 337467) = some ⟨12, 2, 0, 1153009, 337467, 2681, 65536⟩ := by
  decide +kernel

theorem context_12_337467_1153009 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337467 ⟨1153009, by decide⟩ :=
  accepted_of_selected 12 337467 ⟨1153009, by decide⟩ ⟨12, 2, 0, 1153009, 337467, 2681, 65536⟩
    (by decide) selected_cut_42183

theorem unmarked_context_11_84366_1153010 : frontier 10 ⟨1153010, by decide⟩
    (prefixCache 11 84366) (prefixPartial 11 84366) = false := by
  decide +kernel

theorem node_context_11_84366_1153010 : EJMOriginalGlobalDAGData.nodes 10 ⟨1153010, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1152958, by decide⟩,⟨893903, by decide⟩,⟨1153009, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84366_1153010 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84366 ⟨1153010, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84366
    ⟨1153010, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1152958, by decide⟩,⟨893903, by decide⟩,⟨1153009, by decide⟩]) unmarked_context_11_84366_1153010 node_context_11_84366_1153010
  intro a
  fin_cases a
  · exact context_12_337464_1108174
  · exact context_12_337465_1152958
  · exact context_12_337466_893903
  · exact context_12_337467_1153009

theorem selected_cut_42184 : selected 10 ⟨1153059, by decide⟩
    (prefixPartial 11 84367) = some ⟨11, 2, 0, 1153059, 84367, 3837, 262144⟩ := by
  decide +kernel

theorem context_11_84367_1153059 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84367 ⟨1153059, by decide⟩ :=
  accepted_of_selected 11 84367 ⟨1153059, by decide⟩ ⟨11, 2, 0, 1153059, 84367, 3837, 262144⟩
    (by decide) selected_cut_42184

theorem unmarked_context_10_21091_1153060 : frontier 11 ⟨1153060, by decide⟩
    (prefixCache 10 21091) (prefixPartial 10 21091) = false := by
  decide +kernel

theorem node_context_10_21091_1153060 : EJMOriginalGlobalDAGData.nodes 11 ⟨1153060, by decide⟩ =
    .split (coordinate 10) (![⟨1152835, by decide⟩,⟨1152935, by decide⟩,⟨1153010, by decide⟩,⟨1153059, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21091_1153060 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21091 ⟨1153060, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21091
    ⟨1153060, by decide⟩ (by decide) (![⟨1152835, by decide⟩,⟨1152935, by decide⟩,⟨1153010, by decide⟩,⟨1153059, by decide⟩]) unmarked_context_10_21091_1153060 node_context_10_21091_1153060
  intro a
  fin_cases a
  · exact context_11_84364_1152835
  · exact context_11_84365_1152935
  · exact context_11_84366_1153010
  · exact context_11_84367_1153059

theorem unmarked_context_9_5272_1153061 : frontier 12 ⟨1153061, by decide⟩
    (prefixCache 9 5272) (prefixPartial 9 5272) = false := by
  decide +kernel

theorem node_context_9_5272_1153061 : EJMOriginalGlobalDAGData.nodes 12 ⟨1153061, by decide⟩ =
    .split (coordinate 9) (![⟨1151899, by decide⟩,⟨1152210, by decide⟩,⟨1152710, by decide⟩,⟨1153060, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5272_1153061 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5272 ⟨1153061, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5272
    ⟨1153061, by decide⟩ (by decide) (![⟨1151899, by decide⟩,⟨1152210, by decide⟩,⟨1152710, by decide⟩,⟨1153060, by decide⟩]) unmarked_context_9_5272_1153061 node_context_9_5272_1153061
  intro a
  fin_cases a
  · exact context_10_21088_1151899
  · exact context_10_21089_1152210
  · exact context_10_21090_1152710
  · exact context_10_21091_1153060

theorem selected_cut_42185 : selected 9 ⟨1113480, by decide⟩
    (prefixPartial 12 337472) = some ⟨12, 1, 0, 1113480, 337472, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337472_1113480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337472 ⟨1113480, by decide⟩ :=
  accepted_of_selected 12 337472 ⟨1113480, by decide⟩ ⟨12, 1, 0, 1113480, 337472, 1, 65536⟩
    (by decide) selected_cut_42185

theorem selected_cut_42186 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 337473) = some ⟨12, 1, 0, 170504, 337473, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337473_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337473 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 337473 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 337473, 1, 65536⟩
    (by decide) selected_cut_42186

theorem selected_cut_42187 : selected 9 ⟨1153122, by decide⟩
    (prefixPartial 12 337474) = some ⟨12, 2, 0, 1153122, 337474, 2873, 65536⟩ := by
  decide +kernel

theorem context_12_337474_1153122 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337474 ⟨1153122, by decide⟩ :=
  accepted_of_selected 12 337474 ⟨1153122, by decide⟩ ⟨12, 2, 0, 1153122, 337474, 2873, 65536⟩
    (by decide) selected_cut_42187

theorem selected_cut_42188 : selected 9 ⟨1153175, by decide⟩
    (prefixPartial 12 337475) = some ⟨12, 2, 0, 1153175, 337475, 2829, 65536⟩ := by
  decide +kernel

theorem context_12_337475_1153175 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337475 ⟨1153175, by decide⟩ :=
  accepted_of_selected 12 337475 ⟨1153175, by decide⟩ ⟨12, 2, 0, 1153175, 337475, 2829, 65536⟩
    (by decide) selected_cut_42188

theorem unmarked_context_11_84368_1153176 : frontier 10 ⟨1153176, by decide⟩
    (prefixCache 11 84368) (prefixPartial 11 84368) = false := by
  decide +kernel

theorem node_context_11_84368_1153176 : EJMOriginalGlobalDAGData.nodes 10 ⟨1153176, by decide⟩ =
    .split (coordinate 11) (![⟨1113480, by decide⟩,⟨170504, by decide⟩,⟨1153122, by decide⟩,⟨1153175, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84368_1153176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84368 ⟨1153176, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84368
    ⟨1153176, by decide⟩ (by decide) (![⟨1113480, by decide⟩,⟨170504, by decide⟩,⟨1153122, by decide⟩,⟨1153175, by decide⟩]) unmarked_context_11_84368_1153176 node_context_11_84368_1153176
  intro a
  fin_cases a
  · exact context_12_337472_1113480
  · exact context_12_337473_170504
  · exact context_12_337474_1153122
  · exact context_12_337475_1153175

theorem selected_cut_42189 : selected 9 ⟨1153198, by decide⟩
    (prefixPartial 12 337476) = some ⟨12, 2, 0, 1153198, 337476, 1841, 65536⟩ := by
  decide +kernel

theorem context_12_337476_1153198 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337476 ⟨1153198, by decide⟩ :=
  accepted_of_selected 12 337476 ⟨1153198, by decide⟩ ⟨12, 2, 0, 1153198, 337476, 1841, 65536⟩
    (by decide) selected_cut_42189

theorem selected_cut_42190 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 337477) = some ⟨12, 1, 0, 170504, 337477, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337477_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337477 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 337477 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 337477, 1, 65536⟩
    (by decide) selected_cut_42190

theorem selected_cut_42191 : selected 9 ⟨1153230, by decide⟩
    (prefixPartial 12 337478) = some ⟨12, 2, 0, 1153230, 337478, 2101, 65536⟩ := by
  decide +kernel

theorem context_12_337478_1153230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337478 ⟨1153230, by decide⟩ :=
  accepted_of_selected 12 337478 ⟨1153230, by decide⟩ ⟨12, 2, 0, 1153230, 337478, 2101, 65536⟩
    (by decide) selected_cut_42191

theorem selected_cut_42192 : selected 9 ⟨1153260, by decide⟩
    (prefixPartial 12 337479) = some ⟨12, 2, 0, 1153260, 337479, 2109, 65536⟩ := by
  decide +kernel

theorem context_12_337479_1153260 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337479 ⟨1153260, by decide⟩ :=
  accepted_of_selected 12 337479 ⟨1153260, by decide⟩ ⟨12, 2, 0, 1153260, 337479, 2109, 65536⟩
    (by decide) selected_cut_42192

theorem unmarked_context_11_84369_1153261 : frontier 10 ⟨1153261, by decide⟩
    (prefixCache 11 84369) (prefixPartial 11 84369) = false := by
  decide +kernel

theorem node_context_11_84369_1153261 : EJMOriginalGlobalDAGData.nodes 10 ⟨1153261, by decide⟩ =
    .split (coordinate 11) (![⟨1153198, by decide⟩,⟨170504, by decide⟩,⟨1153230, by decide⟩,⟨1153260, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84369_1153261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84369 ⟨1153261, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84369
    ⟨1153261, by decide⟩ (by decide) (![⟨1153198, by decide⟩,⟨170504, by decide⟩,⟨1153230, by decide⟩,⟨1153260, by decide⟩]) unmarked_context_11_84369_1153261 node_context_11_84369_1153261
  intro a
  fin_cases a
  · exact context_12_337476_1153198
  · exact context_12_337477_170504
  · exact context_12_337478_1153230
  · exact context_12_337479_1153260

theorem selected_cut_42193 : selected 9 ⟨1153292, by decide⟩
    (prefixPartial 12 337480) = some ⟨12, 2, 0, 1153292, 337480, 1981, 65536⟩ := by
  decide +kernel

theorem context_12_337480_1153292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337480 ⟨1153292, by decide⟩ :=
  accepted_of_selected 12 337480 ⟨1153292, by decide⟩ ⟨12, 2, 0, 1153292, 337480, 1981, 65536⟩
    (by decide) selected_cut_42193

theorem selected_cut_42194 : selected 9 ⟨1153320, by decide⟩
    (prefixPartial 12 337481) = some ⟨12, 2, 0, 1153320, 337481, 1833, 65536⟩ := by
  decide +kernel

theorem context_12_337481_1153320 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337481 ⟨1153320, by decide⟩ :=
  accepted_of_selected 12 337481 ⟨1153320, by decide⟩ ⟨12, 2, 0, 1153320, 337481, 1833, 65536⟩
    (by decide) selected_cut_42194

theorem selected_cut_42195 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 337482) = some ⟨12, 1, 0, 893903, 337482, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337482_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337482 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 337482 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 337482, 1, 65536⟩
    (by decide) selected_cut_42195

theorem selected_cut_42196 : selected 9 ⟨1153360, by decide⟩
    (prefixPartial 12 337483) = some ⟨12, 2, 0, 1153360, 337483, 2505, 65536⟩ := by
  decide +kernel

theorem context_12_337483_1153360 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337483 ⟨1153360, by decide⟩ :=
  accepted_of_selected 12 337483 ⟨1153360, by decide⟩ ⟨12, 2, 0, 1153360, 337483, 2505, 65536⟩
    (by decide) selected_cut_42196

theorem unmarked_context_11_84370_1153361 : frontier 10 ⟨1153361, by decide⟩
    (prefixCache 11 84370) (prefixPartial 11 84370) = false := by
  decide +kernel

theorem node_context_11_84370_1153361 : EJMOriginalGlobalDAGData.nodes 10 ⟨1153361, by decide⟩ =
    .split (coordinate 11) (![⟨1153292, by decide⟩,⟨1153320, by decide⟩,⟨893903, by decide⟩,⟨1153360, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84370_1153361 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84370 ⟨1153361, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84370
    ⟨1153361, by decide⟩ (by decide) (![⟨1153292, by decide⟩,⟨1153320, by decide⟩,⟨893903, by decide⟩,⟨1153360, by decide⟩]) unmarked_context_11_84370_1153361 node_context_11_84370_1153361
  intro a
  fin_cases a
  · exact context_12_337480_1153292
  · exact context_12_337481_1153320
  · exact context_12_337482_893903
  · exact context_12_337483_1153360

theorem selected_cut_42197 : selected 9 ⟨1153393, by decide⟩
    (prefixPartial 12 337484) = some ⟨12, 2, 0, 1153393, 337484, 2021, 65536⟩ := by
  decide +kernel

theorem context_12_337484_1153393 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337484 ⟨1153393, by decide⟩ :=
  accepted_of_selected 12 337484 ⟨1153393, by decide⟩ ⟨12, 2, 0, 1153393, 337484, 2021, 65536⟩
    (by decide) selected_cut_42197

theorem selected_cut_42198 : selected 9 ⟨1153417, by decide⟩
    (prefixPartial 12 337485) = some ⟨12, 2, 0, 1153417, 337485, 1817, 65536⟩ := by
  decide +kernel

theorem context_12_337485_1153417 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337485 ⟨1153417, by decide⟩ :=
  accepted_of_selected 12 337485 ⟨1153417, by decide⟩ ⟨12, 2, 0, 1153417, 337485, 1817, 65536⟩
    (by decide) selected_cut_42198

theorem selected_cut_42199 : selected 9 ⟨1153460, by decide⟩
    (prefixPartial 12 337486) = some ⟨12, 2, 0, 1153460, 337486, 2477, 65536⟩ := by
  decide +kernel

theorem context_12_337486_1153460 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337486 ⟨1153460, by decide⟩ :=
  accepted_of_selected 12 337486 ⟨1153460, by decide⟩ ⟨12, 2, 0, 1153460, 337486, 2477, 65536⟩
    (by decide) selected_cut_42199

theorem selected_cut_42200 : selected 9 ⟨1153496, by decide⟩
    (prefixPartial 12 337487) = some ⟨12, 2, 0, 1153496, 337487, 2269, 65536⟩ := by
  decide +kernel

theorem context_12_337487_1153496 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337487 ⟨1153496, by decide⟩ :=
  accepted_of_selected 12 337487 ⟨1153496, by decide⟩ ⟨12, 2, 0, 1153496, 337487, 2269, 65536⟩
    (by decide) selected_cut_42200

theorem unmarked_context_11_84371_1153497 : frontier 10 ⟨1153497, by decide⟩
    (prefixCache 11 84371) (prefixPartial 11 84371) = false := by
  decide +kernel

theorem node_context_11_84371_1153497 : EJMOriginalGlobalDAGData.nodes 10 ⟨1153497, by decide⟩ =
    .split (coordinate 11) (![⟨1153393, by decide⟩,⟨1153417, by decide⟩,⟨1153460, by decide⟩,⟨1153496, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84371_1153497 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84371 ⟨1153497, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84371
    ⟨1153497, by decide⟩ (by decide) (![⟨1153393, by decide⟩,⟨1153417, by decide⟩,⟨1153460, by decide⟩,⟨1153496, by decide⟩]) unmarked_context_11_84371_1153497 node_context_11_84371_1153497
  intro a
  fin_cases a
  · exact context_12_337484_1153393
  · exact context_12_337485_1153417
  · exact context_12_337486_1153460
  · exact context_12_337487_1153496

theorem unmarked_context_10_21092_1153498 : frontier 11 ⟨1153498, by decide⟩
    (prefixCache 10 21092) (prefixPartial 10 21092) = false := by
  decide +kernel

theorem node_context_10_21092_1153498 : EJMOriginalGlobalDAGData.nodes 11 ⟨1153498, by decide⟩ =
    .split (coordinate 10) (![⟨1153176, by decide⟩,⟨1153261, by decide⟩,⟨1153361, by decide⟩,⟨1153497, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21092_1153498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21092 ⟨1153498, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21092
    ⟨1153498, by decide⟩ (by decide) (![⟨1153176, by decide⟩,⟨1153261, by decide⟩,⟨1153361, by decide⟩,⟨1153497, by decide⟩]) unmarked_context_10_21092_1153498 node_context_10_21092_1153498
  intro a
  fin_cases a
  · exact context_11_84368_1153176
  · exact context_11_84369_1153261
  · exact context_11_84370_1153361
  · exact context_11_84371_1153497

theorem selected_cut_42201 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 21093) = some ⟨10, 1, 0, 893098, 21093, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_21093_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21093 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 21093 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 21093, 1, 1048576⟩
    (by decide) selected_cut_42201

theorem selected_cut_42202 : selected 9 ⟨1153532, by decide⟩
    (prefixPartial 12 337504) = some ⟨12, 2, 0, 1153532, 337504, 2153, 65536⟩ := by
  decide +kernel

theorem context_12_337504_1153532 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337504 ⟨1153532, by decide⟩ :=
  accepted_of_selected 12 337504 ⟨1153532, by decide⟩ ⟨12, 2, 0, 1153532, 337504, 2153, 65536⟩
    (by decide) selected_cut_42202

theorem selected_cut_42203 : selected 9 ⟨1153550, by decide⟩
    (prefixPartial 12 337505) = some ⟨12, 2, 0, 1153550, 337505, 1701, 65536⟩ := by
  decide +kernel

theorem context_12_337505_1153550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337505 ⟨1153550, by decide⟩ :=
  accepted_of_selected 12 337505 ⟨1153550, by decide⟩ ⟨12, 2, 0, 1153550, 337505, 1701, 65536⟩
    (by decide) selected_cut_42203

theorem selected_cut_42204 : selected 9 ⟨1153582, by decide⟩
    (prefixPartial 12 337506) = some ⟨12, 2, 0, 1153582, 337506, 2085, 65536⟩ := by
  decide +kernel

theorem context_12_337506_1153582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337506 ⟨1153582, by decide⟩ :=
  accepted_of_selected 12 337506 ⟨1153582, by decide⟩ ⟨12, 2, 0, 1153582, 337506, 2085, 65536⟩
    (by decide) selected_cut_42204

theorem selected_cut_42205 : selected 9 ⟨1153624, by decide⟩
    (prefixPartial 12 337507) = some ⟨12, 2, 0, 1153624, 337507, 2345, 65536⟩ := by
  decide +kernel

theorem context_12_337507_1153624 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337507 ⟨1153624, by decide⟩ :=
  accepted_of_selected 12 337507 ⟨1153624, by decide⟩ ⟨12, 2, 0, 1153624, 337507, 2345, 65536⟩
    (by decide) selected_cut_42205

theorem unmarked_context_11_84376_1153625 : frontier 10 ⟨1153625, by decide⟩
    (prefixCache 11 84376) (prefixPartial 11 84376) = false := by
  decide +kernel

theorem node_context_11_84376_1153625 : EJMOriginalGlobalDAGData.nodes 10 ⟨1153625, by decide⟩ =
    .split (coordinate 11) (![⟨1153532, by decide⟩,⟨1153550, by decide⟩,⟨1153582, by decide⟩,⟨1153624, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84376_1153625 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84376 ⟨1153625, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84376
    ⟨1153625, by decide⟩ (by decide) (![⟨1153532, by decide⟩,⟨1153550, by decide⟩,⟨1153582, by decide⟩,⟨1153624, by decide⟩]) unmarked_context_11_84376_1153625 node_context_11_84376_1153625
  intro a
  fin_cases a
  · exact context_12_337504_1153532
  · exact context_12_337505_1153550
  · exact context_12_337506_1153582
  · exact context_12_337507_1153624

theorem selected_cut_42206 : selected 9 ⟨1153653, by decide⟩
    (prefixPartial 12 337508) = some ⟨12, 2, 0, 1153653, 337508, 1765, 65536⟩ := by
  decide +kernel

theorem context_12_337508_1153653 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337508 ⟨1153653, by decide⟩ :=
  accepted_of_selected 12 337508 ⟨1153653, by decide⟩ ⟨12, 2, 0, 1153653, 337508, 1765, 65536⟩
    (by decide) selected_cut_42206

theorem selected_cut_42207 : selected 9 ⟨365907, by decide⟩
    (prefixPartial 12 337509) = some ⟨12, 1, 0, 365907, 337509, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337509_365907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337509 ⟨365907, by decide⟩ :=
  accepted_of_selected 12 337509 ⟨365907, by decide⟩ ⟨12, 1, 0, 365907, 337509, 1, 65536⟩
    (by decide) selected_cut_42207

theorem selected_cut_42208 : selected 9 ⟨1153678, by decide⟩
    (prefixPartial 12 337510) = some ⟨12, 2, 0, 1153678, 337510, 1657, 65536⟩ := by
  decide +kernel

theorem context_12_337510_1153678 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337510 ⟨1153678, by decide⟩ :=
  accepted_of_selected 12 337510 ⟨1153678, by decide⟩ ⟨12, 2, 0, 1153678, 337510, 1657, 65536⟩
    (by decide) selected_cut_42208

theorem selected_cut_42209 : selected 9 ⟨1153705, by decide⟩
    (prefixPartial 12 337511) = some ⟨12, 2, 0, 1153705, 337511, 1865, 65536⟩ := by
  decide +kernel

theorem context_12_337511_1153705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337511 ⟨1153705, by decide⟩ :=
  accepted_of_selected 12 337511 ⟨1153705, by decide⟩ ⟨12, 2, 0, 1153705, 337511, 1865, 65536⟩
    (by decide) selected_cut_42209

theorem unmarked_context_11_84377_1153706 : frontier 10 ⟨1153706, by decide⟩
    (prefixCache 11 84377) (prefixPartial 11 84377) = false := by
  decide +kernel

theorem node_context_11_84377_1153706 : EJMOriginalGlobalDAGData.nodes 10 ⟨1153706, by decide⟩ =
    .split (coordinate 11) (![⟨1153653, by decide⟩,⟨365907, by decide⟩,⟨1153678, by decide⟩,⟨1153705, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84377_1153706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84377 ⟨1153706, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84377
    ⟨1153706, by decide⟩ (by decide) (![⟨1153653, by decide⟩,⟨365907, by decide⟩,⟨1153678, by decide⟩,⟨1153705, by decide⟩]) unmarked_context_11_84377_1153706 node_context_11_84377_1153706
  intro a
  fin_cases a
  · exact context_12_337508_1153653
  · exact context_12_337509_365907
  · exact context_12_337510_1153678
  · exact context_12_337511_1153705

theorem selected_cut_42210 : selected 10 ⟨1153760, by decide⟩
    (prefixPartial 11 84378) = some ⟨11, 2, 0, 1153760, 84378, 3837, 262144⟩ := by
  decide +kernel

theorem context_11_84378_1153760 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84378 ⟨1153760, by decide⟩ :=
  accepted_of_selected 11 84378 ⟨1153760, by decide⟩ ⟨11, 2, 0, 1153760, 84378, 3837, 262144⟩
    (by decide) selected_cut_42210

theorem selected_cut_42211 : selected 9 ⟨1153789, by decide⟩
    (prefixPartial 12 337516) = some ⟨12, 2, 0, 1153789, 337516, 1817, 65536⟩ := by
  decide +kernel

theorem context_12_337516_1153789 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337516 ⟨1153789, by decide⟩ :=
  accepted_of_selected 12 337516 ⟨1153789, by decide⟩ ⟨12, 2, 0, 1153789, 337516, 1817, 65536⟩
    (by decide) selected_cut_42211

theorem selected_cut_42212 : selected 9 ⟨1153805, by decide⟩
    (prefixPartial 12 337517) = some ⟨12, 2, 0, 1153805, 337517, 1477, 65536⟩ := by
  decide +kernel

theorem context_12_337517_1153805 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337517 ⟨1153805, by decide⟩ :=
  accepted_of_selected 12 337517 ⟨1153805, by decide⟩ ⟨12, 2, 0, 1153805, 337517, 1477, 65536⟩
    (by decide) selected_cut_42212

theorem selected_cut_42213 : selected 9 ⟨1153837, by decide⟩
    (prefixPartial 12 337518) = some ⟨12, 2, 0, 1153837, 337518, 1789, 65536⟩ := by
  decide +kernel

theorem context_12_337518_1153837 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337518 ⟨1153837, by decide⟩ :=
  accepted_of_selected 12 337518 ⟨1153837, by decide⟩ ⟨12, 2, 0, 1153837, 337518, 1789, 65536⟩
    (by decide) selected_cut_42213

theorem selected_cut_42214 : selected 9 ⟨1153866, by decide⟩
    (prefixPartial 12 337519) = some ⟨12, 2, 0, 1153866, 337519, 1869, 65536⟩ := by
  decide +kernel

theorem context_12_337519_1153866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337519 ⟨1153866, by decide⟩ :=
  accepted_of_selected 12 337519 ⟨1153866, by decide⟩ ⟨12, 2, 0, 1153866, 337519, 1869, 65536⟩
    (by decide) selected_cut_42214

theorem unmarked_context_11_84379_1153867 : frontier 10 ⟨1153867, by decide⟩
    (prefixCache 11 84379) (prefixPartial 11 84379) = false := by
  decide +kernel

theorem node_context_11_84379_1153867 : EJMOriginalGlobalDAGData.nodes 10 ⟨1153867, by decide⟩ =
    .split (coordinate 11) (![⟨1153789, by decide⟩,⟨1153805, by decide⟩,⟨1153837, by decide⟩,⟨1153866, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84379_1153867 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84379 ⟨1153867, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84379
    ⟨1153867, by decide⟩ (by decide) (![⟨1153789, by decide⟩,⟨1153805, by decide⟩,⟨1153837, by decide⟩,⟨1153866, by decide⟩]) unmarked_context_11_84379_1153867 node_context_11_84379_1153867
  intro a
  fin_cases a
  · exact context_12_337516_1153789
  · exact context_12_337517_1153805
  · exact context_12_337518_1153837
  · exact context_12_337519_1153866

theorem unmarked_context_10_21094_1153868 : frontier 11 ⟨1153868, by decide⟩
    (prefixCache 10 21094) (prefixPartial 10 21094) = false := by
  decide +kernel

theorem node_context_10_21094_1153868 : EJMOriginalGlobalDAGData.nodes 11 ⟨1153868, by decide⟩ =
    .split (coordinate 10) (![⟨1153625, by decide⟩,⟨1153706, by decide⟩,⟨1153760, by decide⟩,⟨1153867, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21094_1153868 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21094 ⟨1153868, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21094
    ⟨1153868, by decide⟩ (by decide) (![⟨1153625, by decide⟩,⟨1153706, by decide⟩,⟨1153760, by decide⟩,⟨1153867, by decide⟩]) unmarked_context_10_21094_1153868 node_context_10_21094_1153868
  intro a
  fin_cases a
  · exact context_11_84376_1153625
  · exact context_11_84377_1153706
  · exact context_11_84378_1153760
  · exact context_11_84379_1153867

theorem selected_cut_42215 : selected 9 ⟨1153891, by decide⟩
    (prefixPartial 12 337520) = some ⟨12, 2, 0, 1153891, 337520, 1601, 65536⟩ := by
  decide +kernel

theorem context_12_337520_1153891 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337520 ⟨1153891, by decide⟩ :=
  accepted_of_selected 12 337520 ⟨1153891, by decide⟩ ⟨12, 2, 0, 1153891, 337520, 1601, 65536⟩
    (by decide) selected_cut_42215

theorem selected_cut_42216 : selected 9 ⟨1153905, by decide⟩
    (prefixPartial 12 337521) = some ⟨12, 2, 0, 1153905, 337521, 1305, 65536⟩ := by
  decide +kernel

theorem context_12_337521_1153905 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337521 ⟨1153905, by decide⟩ :=
  accepted_of_selected 12 337521 ⟨1153905, by decide⟩ ⟨12, 2, 0, 1153905, 337521, 1305, 65536⟩
    (by decide) selected_cut_42216

theorem selected_cut_42217 : selected 9 ⟨1153937, by decide⟩
    (prefixPartial 12 337522) = some ⟨12, 2, 0, 1153937, 337522, 1585, 65536⟩ := by
  decide +kernel

theorem context_12_337522_1153937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337522 ⟨1153937, by decide⟩ :=
  accepted_of_selected 12 337522 ⟨1153937, by decide⟩ ⟨12, 2, 0, 1153937, 337522, 1585, 65536⟩
    (by decide) selected_cut_42217

theorem selected_cut_42218 : selected 9 ⟨1153968, by decide⟩
    (prefixPartial 12 337523) = some ⟨12, 2, 0, 1153968, 337523, 1757, 65536⟩ := by
  decide +kernel

theorem context_12_337523_1153968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337523 ⟨1153968, by decide⟩ :=
  accepted_of_selected 12 337523 ⟨1153968, by decide⟩ ⟨12, 2, 0, 1153968, 337523, 1757, 65536⟩
    (by decide) selected_cut_42218

theorem unmarked_context_11_84380_1153969 : frontier 10 ⟨1153969, by decide⟩
    (prefixCache 11 84380) (prefixPartial 11 84380) = false := by
  decide +kernel

theorem node_context_11_84380_1153969 : EJMOriginalGlobalDAGData.nodes 10 ⟨1153969, by decide⟩ =
    .split (coordinate 11) (![⟨1153891, by decide⟩,⟨1153905, by decide⟩,⟨1153937, by decide⟩,⟨1153968, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84380_1153969 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84380 ⟨1153969, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84380
    ⟨1153969, by decide⟩ (by decide) (![⟨1153891, by decide⟩,⟨1153905, by decide⟩,⟨1153937, by decide⟩,⟨1153968, by decide⟩]) unmarked_context_11_84380_1153969 node_context_11_84380_1153969
  intro a
  fin_cases a
  · exact context_12_337520_1153891
  · exact context_12_337521_1153905
  · exact context_12_337522_1153937
  · exact context_12_337523_1153968

theorem selected_cut_42219 : selected 10 ⟨1154017, by decide⟩
    (prefixPartial 11 84381) = some ⟨11, 2, 0, 1154017, 84381, 3893, 262144⟩ := by
  decide +kernel

theorem context_11_84381_1154017 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84381 ⟨1154017, by decide⟩ :=
  accepted_of_selected 11 84381 ⟨1154017, by decide⟩ ⟨11, 2, 0, 1154017, 84381, 3893, 262144⟩
    (by decide) selected_cut_42219

theorem selected_cut_42220 : selected 10 ⟨1154060, by decide⟩
    (prefixPartial 11 84382) = some ⟨11, 2, 0, 1154060, 84382, 3877, 262144⟩ := by
  decide +kernel

theorem context_11_84382_1154060 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84382 ⟨1154060, by decide⟩ :=
  accepted_of_selected 11 84382 ⟨1154060, by decide⟩ ⟨11, 2, 0, 1154060, 84382, 3877, 262144⟩
    (by decide) selected_cut_42220

theorem selected_cut_42221 : selected 10 ⟨1154098, by decide⟩
    (prefixPartial 11 84383) = some ⟨11, 2, 0, 1154098, 84383, 3437, 262144⟩ := by
  decide +kernel

theorem context_11_84383_1154098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84383 ⟨1154098, by decide⟩ :=
  accepted_of_selected 11 84383 ⟨1154098, by decide⟩ ⟨11, 2, 0, 1154098, 84383, 3437, 262144⟩
    (by decide) selected_cut_42221

theorem unmarked_context_10_21095_1154099 : frontier 11 ⟨1154099, by decide⟩
    (prefixCache 10 21095) (prefixPartial 10 21095) = false := by
  decide +kernel

theorem node_context_10_21095_1154099 : EJMOriginalGlobalDAGData.nodes 11 ⟨1154099, by decide⟩ =
    .split (coordinate 10) (![⟨1153969, by decide⟩,⟨1154017, by decide⟩,⟨1154060, by decide⟩,⟨1154098, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21095_1154099 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21095 ⟨1154099, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21095
    ⟨1154099, by decide⟩ (by decide) (![⟨1153969, by decide⟩,⟨1154017, by decide⟩,⟨1154060, by decide⟩,⟨1154098, by decide⟩]) unmarked_context_10_21095_1154099 node_context_10_21095_1154099
  intro a
  fin_cases a
  · exact context_11_84380_1153969
  · exact context_11_84381_1154017
  · exact context_11_84382_1154060
  · exact context_11_84383_1154098

theorem unmarked_context_9_5273_1154100 : frontier 12 ⟨1154100, by decide⟩
    (prefixCache 9 5273) (prefixPartial 9 5273) = false := by
  decide +kernel

theorem node_context_9_5273_1154100 : EJMOriginalGlobalDAGData.nodes 12 ⟨1154100, by decide⟩ =
    .split (coordinate 9) (![⟨1153498, by decide⟩,⟨893098, by decide⟩,⟨1153868, by decide⟩,⟨1154099, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5273_1154100 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5273 ⟨1154100, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5273
    ⟨1154100, by decide⟩ (by decide) (![⟨1153498, by decide⟩,⟨893098, by decide⟩,⟨1153868, by decide⟩,⟨1154099, by decide⟩]) unmarked_context_9_5273_1154100 node_context_9_5273_1154100
  intro a
  fin_cases a
  · exact context_10_21092_1153498
  · exact context_10_21093_893098
  · exact context_10_21094_1153868
  · exact context_10_21095_1154099

theorem selected_cut_42222 : selected 10 ⟨1154132, by decide⟩
    (prefixPartial 11 84384) = some ⟨11, 2, 0, 1154132, 84384, 2453, 262144⟩ := by
  decide +kernel

theorem context_11_84384_1154132 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84384 ⟨1154132, by decide⟩ :=
  accepted_of_selected 11 84384 ⟨1154132, by decide⟩ ⟨11, 2, 0, 1154132, 84384, 2453, 262144⟩
    (by decide) selected_cut_42222

theorem selected_cut_42223 : selected 9 ⟨1154149, by decide⟩
    (prefixPartial 12 337540) = some ⟨12, 2, 0, 1154149, 337540, 1265, 65536⟩ := by
  decide +kernel

theorem context_12_337540_1154149 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337540 ⟨1154149, by decide⟩ :=
  accepted_of_selected 12 337540 ⟨1154149, by decide⟩ ⟨12, 2, 0, 1154149, 337540, 1265, 65536⟩
    (by decide) selected_cut_42223

theorem selected_cut_42224 : selected 9 ⟨1154161, by decide⟩
    (prefixPartial 12 337541) = some ⟨12, 2, 0, 1154161, 337541, 1061, 65536⟩ := by
  decide +kernel

theorem context_12_337541_1154161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337541 ⟨1154161, by decide⟩ :=
  accepted_of_selected 12 337541 ⟨1154161, by decide⟩ ⟨12, 2, 0, 1154161, 337541, 1061, 65536⟩
    (by decide) selected_cut_42224

theorem selected_cut_42225 : selected 9 ⟨1154180, by decide⟩
    (prefixPartial 12 337542) = some ⟨12, 2, 0, 1154180, 337542, 1145, 65536⟩ := by
  decide +kernel

theorem context_12_337542_1154180 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337542 ⟨1154180, by decide⟩ :=
  accepted_of_selected 12 337542 ⟨1154180, by decide⟩ ⟨12, 2, 0, 1154180, 337542, 1145, 65536⟩
    (by decide) selected_cut_42225

theorem selected_cut_42226 : selected 9 ⟨1154202, by decide⟩
    (prefixPartial 12 337543) = some ⟨12, 2, 0, 1154202, 337543, 1361, 65536⟩ := by
  decide +kernel

theorem context_12_337543_1154202 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337543 ⟨1154202, by decide⟩ :=
  accepted_of_selected 12 337543 ⟨1154202, by decide⟩ ⟨12, 2, 0, 1154202, 337543, 1361, 65536⟩
    (by decide) selected_cut_42226

theorem unmarked_context_11_84385_1154203 : frontier 10 ⟨1154203, by decide⟩
    (prefixCache 11 84385) (prefixPartial 11 84385) = false := by
  decide +kernel

theorem node_context_11_84385_1154203 : EJMOriginalGlobalDAGData.nodes 10 ⟨1154203, by decide⟩ =
    .split (coordinate 11) (![⟨1154149, by decide⟩,⟨1154161, by decide⟩,⟨1154180, by decide⟩,⟨1154202, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84385_1154203 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84385 ⟨1154203, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84385
    ⟨1154203, by decide⟩ (by decide) (![⟨1154149, by decide⟩,⟨1154161, by decide⟩,⟨1154180, by decide⟩,⟨1154202, by decide⟩]) unmarked_context_11_84385_1154203 node_context_11_84385_1154203
  intro a
  fin_cases a
  · exact context_12_337540_1154149
  · exact context_12_337541_1154161
  · exact context_12_337542_1154180
  · exact context_12_337543_1154202

theorem selected_cut_42227 : selected 10 ⟨1154258, by decide⟩
    (prefixPartial 11 84386) = some ⟨11, 2, 0, 1154258, 84386, 3725, 262144⟩ := by
  decide +kernel

theorem context_11_84386_1154258 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84386 ⟨1154258, by decide⟩ :=
  accepted_of_selected 11 84386 ⟨1154258, by decide⟩ ⟨11, 2, 0, 1154258, 84386, 3725, 262144⟩
    (by decide) selected_cut_42227

theorem selected_cut_42228 : selected 9 ⟨1154274, by decide⟩
    (prefixPartial 12 337548) = some ⟨12, 2, 0, 1154274, 337548, 1093, 65536⟩ := by
  decide +kernel

theorem context_12_337548_1154274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337548 ⟨1154274, by decide⟩ :=
  accepted_of_selected 12 337548 ⟨1154274, by decide⟩ ⟨12, 2, 0, 1154274, 337548, 1093, 65536⟩
    (by decide) selected_cut_42228

theorem selected_cut_42229 : selected 9 ⟨1154287, by decide⟩
    (prefixPartial 12 337549) = some ⟨12, 2, 0, 1154287, 337549, 1017, 65536⟩ := by
  decide +kernel

theorem context_12_337549_1154287 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337549 ⟨1154287, by decide⟩ :=
  accepted_of_selected 12 337549 ⟨1154287, by decide⟩ ⟨12, 2, 0, 1154287, 337549, 1017, 65536⟩
    (by decide) selected_cut_42229

theorem selected_cut_42230 : selected 9 ⟨1154305, by decide⟩
    (prefixPartial 12 337550) = some ⟨12, 2, 0, 1154305, 337550, 1109, 65536⟩ := by
  decide +kernel

theorem context_12_337550_1154305 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337550 ⟨1154305, by decide⟩ :=
  accepted_of_selected 12 337550 ⟨1154305, by decide⟩ ⟨12, 2, 0, 1154305, 337550, 1109, 65536⟩
    (by decide) selected_cut_42230

theorem selected_cut_42231 : selected 9 ⟨1154320, by decide⟩
    (prefixPartial 12 337551) = some ⟨12, 2, 0, 1154320, 337551, 1149, 65536⟩ := by
  decide +kernel

theorem context_12_337551_1154320 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337551 ⟨1154320, by decide⟩ :=
  accepted_of_selected 12 337551 ⟨1154320, by decide⟩ ⟨12, 2, 0, 1154320, 337551, 1149, 65536⟩
    (by decide) selected_cut_42231

theorem unmarked_context_11_84387_1154321 : frontier 10 ⟨1154321, by decide⟩
    (prefixCache 11 84387) (prefixPartial 11 84387) = false := by
  decide +kernel

theorem node_context_11_84387_1154321 : EJMOriginalGlobalDAGData.nodes 10 ⟨1154321, by decide⟩ =
    .split (coordinate 11) (![⟨1154274, by decide⟩,⟨1154287, by decide⟩,⟨1154305, by decide⟩,⟨1154320, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84387_1154321 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84387 ⟨1154321, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84387
    ⟨1154321, by decide⟩ (by decide) (![⟨1154274, by decide⟩,⟨1154287, by decide⟩,⟨1154305, by decide⟩,⟨1154320, by decide⟩]) unmarked_context_11_84387_1154321 node_context_11_84387_1154321
  intro a
  fin_cases a
  · exact context_12_337548_1154274
  · exact context_12_337549_1154287
  · exact context_12_337550_1154305
  · exact context_12_337551_1154320

theorem unmarked_context_10_21096_1154322 : frontier 11 ⟨1154322, by decide⟩
    (prefixCache 10 21096) (prefixPartial 10 21096) = false := by
  decide +kernel

theorem node_context_10_21096_1154322 : EJMOriginalGlobalDAGData.nodes 11 ⟨1154322, by decide⟩ =
    .split (coordinate 10) (![⟨1154132, by decide⟩,⟨1154203, by decide⟩,⟨1154258, by decide⟩,⟨1154321, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21096_1154322 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21096 ⟨1154322, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21096
    ⟨1154322, by decide⟩ (by decide) (![⟨1154132, by decide⟩,⟨1154203, by decide⟩,⟨1154258, by decide⟩,⟨1154321, by decide⟩]) unmarked_context_10_21096_1154322 node_context_10_21096_1154322
  intro a
  fin_cases a
  · exact context_11_84384_1154132
  · exact context_11_84385_1154203
  · exact context_11_84386_1154258
  · exact context_11_84387_1154321

theorem selected_cut_42232 : selected 10 ⟨1154361, by decide⟩
    (prefixPartial 11 84388) = some ⟨11, 2, 0, 1154361, 84388, 3517, 262144⟩ := by
  decide +kernel

theorem context_11_84388_1154361 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84388 ⟨1154361, by decide⟩ :=
  accepted_of_selected 11 84388 ⟨1154361, by decide⟩ ⟨11, 2, 0, 1154361, 84388, 3517, 262144⟩
    (by decide) selected_cut_42232

theorem selected_cut_42233 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 84389) = some ⟨11, 1, 0, 892405, 84389, 1, 262144⟩ := by
  decide +kernel

theorem context_11_84389_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84389 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 84389 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 84389, 1, 262144⟩
    (by decide) selected_cut_42233

theorem selected_cut_42234 : selected 10 ⟨1154396, by decide⟩
    (prefixPartial 11 84390) = some ⟨11, 2, 0, 1154396, 84390, 2737, 262144⟩ := by
  decide +kernel

theorem context_11_84390_1154396 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84390 ⟨1154396, by decide⟩ :=
  accepted_of_selected 11 84390 ⟨1154396, by decide⟩ ⟨11, 2, 0, 1154396, 84390, 2737, 262144⟩
    (by decide) selected_cut_42234

theorem selected_cut_42235 : selected 10 ⟨1154435, by decide⟩
    (prefixPartial 11 84391) = some ⟨11, 2, 0, 1154435, 84391, 3161, 262144⟩ := by
  decide +kernel

theorem context_11_84391_1154435 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84391 ⟨1154435, by decide⟩ :=
  accepted_of_selected 11 84391 ⟨1154435, by decide⟩ ⟨11, 2, 0, 1154435, 84391, 3161, 262144⟩
    (by decide) selected_cut_42235

theorem unmarked_context_10_21097_1154436 : frontier 11 ⟨1154436, by decide⟩
    (prefixCache 10 21097) (prefixPartial 10 21097) = false := by
  decide +kernel

theorem node_context_10_21097_1154436 : EJMOriginalGlobalDAGData.nodes 11 ⟨1154436, by decide⟩ =
    .split (coordinate 10) (![⟨1154361, by decide⟩,⟨892405, by decide⟩,⟨1154396, by decide⟩,⟨1154435, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21097_1154436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21097 ⟨1154436, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21097
    ⟨1154436, by decide⟩ (by decide) (![⟨1154361, by decide⟩,⟨892405, by decide⟩,⟨1154396, by decide⟩,⟨1154435, by decide⟩]) unmarked_context_10_21097_1154436 node_context_10_21097_1154436
  intro a
  fin_cases a
  · exact context_11_84388_1154361
  · exact context_11_84389_892405
  · exact context_11_84390_1154396
  · exact context_11_84391_1154435

theorem selected_cut_42236 : selected 10 ⟨1154451, by decide⟩
    (prefixPartial 11 84392) = some ⟨11, 2, 0, 1154451, 84392, 1681, 262144⟩ := by
  decide +kernel

theorem context_11_84392_1154451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84392 ⟨1154451, by decide⟩ :=
  accepted_of_selected 11 84392 ⟨1154451, by decide⟩ ⟨11, 2, 0, 1154451, 84392, 1681, 262144⟩
    (by decide) selected_cut_42236

theorem selected_cut_42237 : selected 10 ⟨1154483, by decide⟩
    (prefixPartial 11 84393) = some ⟨11, 2, 0, 1154483, 84393, 1945, 262144⟩ := by
  decide +kernel

theorem context_11_84393_1154483 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84393 ⟨1154483, by decide⟩ :=
  accepted_of_selected 11 84393 ⟨1154483, by decide⟩ ⟨11, 2, 0, 1154483, 84393, 1945, 262144⟩
    (by decide) selected_cut_42237

theorem selected_cut_42238 : selected 10 ⟨1109453, by decide⟩
    (prefixPartial 11 84394) = some ⟨11, 1, 0, 1109453, 84394, 1, 262144⟩ := by
  decide +kernel

theorem context_11_84394_1109453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84394 ⟨1109453, by decide⟩ :=
  accepted_of_selected 11 84394 ⟨1109453, by decide⟩ ⟨11, 1, 0, 1109453, 84394, 1, 262144⟩
    (by decide) selected_cut_42238

theorem selected_cut_42239 : selected 10 ⟨1154508, by decide⟩
    (prefixPartial 11 84395) = some ⟨11, 2, 0, 1154508, 84395, 2357, 262144⟩ := by
  decide +kernel

theorem context_11_84395_1154508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84395 ⟨1154508, by decide⟩ :=
  accepted_of_selected 11 84395 ⟨1154508, by decide⟩ ⟨11, 2, 0, 1154508, 84395, 2357, 262144⟩
    (by decide) selected_cut_42239

theorem unmarked_context_10_21098_1154509 : frontier 11 ⟨1154509, by decide⟩
    (prefixCache 10 21098) (prefixPartial 10 21098) = false := by
  decide +kernel

theorem node_context_10_21098_1154509 : EJMOriginalGlobalDAGData.nodes 11 ⟨1154509, by decide⟩ =
    .split (coordinate 10) (![⟨1154451, by decide⟩,⟨1154483, by decide⟩,⟨1109453, by decide⟩,⟨1154508, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21098_1154509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21098 ⟨1154509, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21098
    ⟨1154509, by decide⟩ (by decide) (![⟨1154451, by decide⟩,⟨1154483, by decide⟩,⟨1109453, by decide⟩,⟨1154508, by decide⟩]) unmarked_context_10_21098_1154509 node_context_10_21098_1154509
  intro a
  fin_cases a
  · exact context_11_84392_1154451
  · exact context_11_84393_1154483
  · exact context_11_84394_1109453
  · exact context_11_84395_1154508

theorem selected_cut_42240 : selected 10 ⟨1154545, by decide⟩
    (prefixPartial 11 84396) = some ⟨11, 2, 0, 1154545, 84396, 2705, 262144⟩ := by
  decide +kernel

theorem context_11_84396_1154545 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84396 ⟨1154545, by decide⟩ :=
  accepted_of_selected 11 84396 ⟨1154545, by decide⟩ ⟨11, 2, 0, 1154545, 84396, 2705, 262144⟩
    (by decide) selected_cut_42240

theorem selected_cut_42241 : selected 10 ⟨1154583, by decide⟩
    (prefixPartial 11 84397) = some ⟨11, 2, 0, 1154583, 84397, 2565, 262144⟩ := by
  decide +kernel

theorem context_11_84397_1154583 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84397 ⟨1154583, by decide⟩ :=
  accepted_of_selected 11 84397 ⟨1154583, by decide⟩ ⟨11, 2, 0, 1154583, 84397, 2565, 262144⟩
    (by decide) selected_cut_42241

theorem selected_cut_42242 : selected 10 ⟨1154604, by decide⟩
    (prefixPartial 11 84398) = some ⟨11, 2, 0, 1154604, 84398, 1733, 262144⟩ := by
  decide +kernel

theorem context_11_84398_1154604 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84398 ⟨1154604, by decide⟩ :=
  accepted_of_selected 11 84398 ⟨1154604, by decide⟩ ⟨11, 2, 0, 1154604, 84398, 1733, 262144⟩
    (by decide) selected_cut_42242

theorem selected_cut_42243 : selected 10 ⟨1154619, by decide⟩
    (prefixPartial 11 84399) = some ⟨11, 2, 0, 1154619, 84399, 1425, 262144⟩ := by
  decide +kernel

theorem context_11_84399_1154619 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84399 ⟨1154619, by decide⟩ :=
  accepted_of_selected 11 84399 ⟨1154619, by decide⟩ ⟨11, 2, 0, 1154619, 84399, 1425, 262144⟩
    (by decide) selected_cut_42243

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
