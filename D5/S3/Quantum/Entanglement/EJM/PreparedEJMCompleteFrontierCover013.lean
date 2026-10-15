/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover012
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_12_4457_46208 : frontier 9 ⟨46208, by decide⟩
    (prefixCache 12 4457) (prefixPartial 12 4457) = false := by
  decide +kernel

theorem node_context_12_4457_46208 : EJMOriginalGlobalDAGData.nodes 9 ⟨46208, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨46165, by decide⟩,⟨46191, by decide⟩,⟨46207, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4457_46208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4457 ⟨46208, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4457
    ⟨46208, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨46165, by decide⟩,⟨46191, by decide⟩,⟨46207, by decide⟩]) unmarked_context_12_4457_46208 node_context_12_4457_46208
  intro a
  fin_cases a
  · exact context_13_17828_3444
  · exact context_13_17829_46165
  · exact context_13_17830_46191
  · exact context_13_17831_46207

theorem selected_cut_01251 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 17832) = some ⟨13, 1, 0, 3444, 17832, 1, 16384⟩ := by
  decide +kernel

theorem context_13_17832_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17832 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 17832 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 17832, 1, 16384⟩
    (by decide) selected_cut_01251

theorem selected_cut_01252 : selected 8 ⟨46221, by decide⟩
    (prefixPartial 13 17833) = some ⟨13, 2, 0, 46221, 17833, 649, 16384⟩ := by
  decide +kernel

theorem context_13_17833_46221 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17833 ⟨46221, by decide⟩ :=
  accepted_of_selected 13 17833 ⟨46221, by decide⟩ ⟨13, 2, 0, 46221, 17833, 649, 16384⟩
    (by decide) selected_cut_01252

theorem selected_cut_01253 : selected 8 ⟨46247, by decide⟩
    (prefixPartial 13 17834) = some ⟨13, 2, 0, 46247, 17834, 2421, 16384⟩ := by
  decide +kernel

theorem context_13_17834_46247 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17834 ⟨46247, by decide⟩ :=
  accepted_of_selected 13 17834 ⟨46247, by decide⟩ ⟨13, 2, 0, 46247, 17834, 2421, 16384⟩
    (by decide) selected_cut_01253

theorem selected_cut_01254 : selected 8 ⟨46262, by decide⟩
    (prefixPartial 13 17835) = some ⟨13, 2, 0, 46262, 17835, 1397, 16384⟩ := by
  decide +kernel

theorem context_13_17835_46262 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17835 ⟨46262, by decide⟩ :=
  accepted_of_selected 13 17835 ⟨46262, by decide⟩ ⟨13, 2, 0, 46262, 17835, 1397, 16384⟩
    (by decide) selected_cut_01254

theorem unmarked_context_12_4458_46263 : frontier 9 ⟨46263, by decide⟩
    (prefixCache 12 4458) (prefixPartial 12 4458) = false := by
  decide +kernel

theorem node_context_12_4458_46263 : EJMOriginalGlobalDAGData.nodes 9 ⟨46263, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨46221, by decide⟩,⟨46247, by decide⟩,⟨46262, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4458_46263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4458 ⟨46263, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4458
    ⟨46263, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨46221, by decide⟩,⟨46247, by decide⟩,⟨46262, by decide⟩]) unmarked_context_12_4458_46263 node_context_12_4458_46263
  intro a
  fin_cases a
  · exact context_13_17832_3444
  · exact context_13_17833_46221
  · exact context_13_17834_46247
  · exact context_13_17835_46262

theorem selected_cut_01255 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 17836) = some ⟨13, 1, 0, 3444, 17836, 1, 16384⟩ := by
  decide +kernel

theorem context_13_17836_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17836 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 17836 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 17836, 1, 16384⟩
    (by decide) selected_cut_01255

theorem selected_cut_01256 : selected 8 ⟨46274, by decide⟩
    (prefixPartial 13 17837) = some ⟨13, 2, 0, 46274, 17837, 529, 16384⟩ := by
  decide +kernel

theorem context_13_17837_46274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17837 ⟨46274, by decide⟩ :=
  accepted_of_selected 13 17837 ⟨46274, by decide⟩ ⟨13, 2, 0, 46274, 17837, 529, 16384⟩
    (by decide) selected_cut_01256

theorem selected_cut_01257 : selected 8 ⟨46303, by decide⟩
    (prefixPartial 13 17838) = some ⟨13, 2, 0, 46303, 17838, 2373, 16384⟩ := by
  decide +kernel

theorem context_13_17838_46303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17838 ⟨46303, by decide⟩ :=
  accepted_of_selected 13 17838 ⟨46303, by decide⟩ ⟨13, 2, 0, 46303, 17838, 2373, 16384⟩
    (by decide) selected_cut_01257

theorem selected_cut_01258 : selected 8 ⟨46323, by decide⟩
    (prefixPartial 13 17839) = some ⟨13, 2, 0, 46323, 17839, 1493, 16384⟩ := by
  decide +kernel

theorem context_13_17839_46323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17839 ⟨46323, by decide⟩ :=
  accepted_of_selected 13 17839 ⟨46323, by decide⟩ ⟨13, 2, 0, 46323, 17839, 1493, 16384⟩
    (by decide) selected_cut_01258

theorem unmarked_context_12_4459_46324 : frontier 9 ⟨46324, by decide⟩
    (prefixCache 12 4459) (prefixPartial 12 4459) = false := by
  decide +kernel

theorem node_context_12_4459_46324 : EJMOriginalGlobalDAGData.nodes 9 ⟨46324, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨46274, by decide⟩,⟨46303, by decide⟩,⟨46323, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4459_46324 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4459 ⟨46324, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4459
    ⟨46324, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨46274, by decide⟩,⟨46303, by decide⟩,⟨46323, by decide⟩]) unmarked_context_12_4459_46324 node_context_12_4459_46324
  intro a
  fin_cases a
  · exact context_13_17836_3444
  · exact context_13_17837_46274
  · exact context_13_17838_46303
  · exact context_13_17839_46323

theorem unmarked_context_11_1114_46325 : frontier 10 ⟨46325, by decide⟩
    (prefixCache 11 1114) (prefixPartial 11 1114) = false := by
  decide +kernel

theorem node_context_11_1114_46325 : EJMOriginalGlobalDAGData.nodes 10 ⟨46325, by decide⟩ =
    .split (coordinate 11) (![⟨46152, by decide⟩,⟨46208, by decide⟩,⟨46263, by decide⟩,⟨46324, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1114_46325 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1114 ⟨46325, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1114
    ⟨46325, by decide⟩ (by decide) (![⟨46152, by decide⟩,⟨46208, by decide⟩,⟨46263, by decide⟩,⟨46324, by decide⟩]) unmarked_context_11_1114_46325 node_context_11_1114_46325
  intro a
  fin_cases a
  · exact context_12_4456_46152
  · exact context_12_4457_46208
  · exact context_12_4458_46263
  · exact context_12_4459_46324

theorem selected_cut_01259 : selected 9 ⟨46373, by decide⟩
    (prefixPartial 12 4460) = some ⟨12, 2, 0, 46373, 4460, 3417, 65536⟩ := by
  decide +kernel

theorem context_12_4460_46373 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4460 ⟨46373, by decide⟩ :=
  accepted_of_selected 12 4460 ⟨46373, by decide⟩ ⟨12, 2, 0, 46373, 4460, 3417, 65536⟩
    (by decide) selected_cut_01259

theorem selected_cut_01260 : selected 9 ⟨46428, by decide⟩
    (prefixPartial 12 4461) = some ⟨12, 2, 0, 46428, 4461, 3913, 65536⟩ := by
  decide +kernel

theorem context_12_4461_46428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4461 ⟨46428, by decide⟩ :=
  accepted_of_selected 12 4461 ⟨46428, by decide⟩ ⟨12, 2, 0, 46428, 4461, 3913, 65536⟩
    (by decide) selected_cut_01260

theorem selected_cut_01261 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 17848) = some ⟨13, 1, 0, 3444, 17848, 1, 16384⟩ := by
  decide +kernel

theorem context_13_17848_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17848 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 17848 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 17848, 1, 16384⟩
    (by decide) selected_cut_01261

theorem selected_cut_01262 : selected 8 ⟨46436, by decide⟩
    (prefixPartial 13 17849) = some ⟨13, 2, 0, 46436, 17849, 265, 16384⟩ := by
  decide +kernel

theorem context_13_17849_46436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17849 ⟨46436, by decide⟩ :=
  accepted_of_selected 13 17849 ⟨46436, by decide⟩ ⟨13, 2, 0, 46436, 17849, 265, 16384⟩
    (by decide) selected_cut_01262

theorem selected_cut_01263 : selected 8 ⟨46489, by decide⟩
    (prefixPartial 13 17850) = some ⟨13, 2, 0, 46489, 17850, 2765, 16384⟩ := by
  decide +kernel

theorem context_13_17850_46489 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17850 ⟨46489, by decide⟩ :=
  accepted_of_selected 13 17850 ⟨46489, by decide⟩ ⟨13, 2, 0, 46489, 17850, 2765, 16384⟩
    (by decide) selected_cut_01263

theorem selected_cut_01264 : selected 8 ⟨46514, by decide⟩
    (prefixPartial 13 17851) = some ⟨13, 2, 0, 46514, 17851, 1377, 16384⟩ := by
  decide +kernel

theorem context_13_17851_46514 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17851 ⟨46514, by decide⟩ :=
  accepted_of_selected 13 17851 ⟨46514, by decide⟩ ⟨13, 2, 0, 46514, 17851, 1377, 16384⟩
    (by decide) selected_cut_01264

theorem unmarked_context_12_4462_46515 : frontier 9 ⟨46515, by decide⟩
    (prefixCache 12 4462) (prefixPartial 12 4462) = false := by
  decide +kernel

theorem node_context_12_4462_46515 : EJMOriginalGlobalDAGData.nodes 9 ⟨46515, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨46436, by decide⟩,⟨46489, by decide⟩,⟨46514, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4462_46515 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4462 ⟨46515, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4462
    ⟨46515, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨46436, by decide⟩,⟨46489, by decide⟩,⟨46514, by decide⟩]) unmarked_context_12_4462_46515 node_context_12_4462_46515
  intro a
  fin_cases a
  · exact context_13_17848_3444
  · exact context_13_17849_46436
  · exact context_13_17850_46489
  · exact context_13_17851_46514

theorem selected_cut_01265 : selected 9 ⟨46565, by decide⟩
    (prefixPartial 12 4463) = some ⟨12, 2, 0, 46565, 4463, 3993, 65536⟩ := by
  decide +kernel

theorem context_12_4463_46565 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4463 ⟨46565, by decide⟩ :=
  accepted_of_selected 12 4463 ⟨46565, by decide⟩ ⟨12, 2, 0, 46565, 4463, 3993, 65536⟩
    (by decide) selected_cut_01265

theorem unmarked_context_11_1115_46566 : frontier 10 ⟨46566, by decide⟩
    (prefixCache 11 1115) (prefixPartial 11 1115) = false := by
  decide +kernel

theorem node_context_11_1115_46566 : EJMOriginalGlobalDAGData.nodes 10 ⟨46566, by decide⟩ =
    .split (coordinate 11) (![⟨46373, by decide⟩,⟨46428, by decide⟩,⟨46515, by decide⟩,⟨46565, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1115_46566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1115 ⟨46566, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1115
    ⟨46566, by decide⟩ (by decide) (![⟨46373, by decide⟩,⟨46428, by decide⟩,⟨46515, by decide⟩,⟨46565, by decide⟩]) unmarked_context_11_1115_46566 node_context_11_1115_46566
  intro a
  fin_cases a
  · exact context_12_4460_46373
  · exact context_12_4461_46428
  · exact context_12_4462_46515
  · exact context_12_4463_46565

theorem unmarked_context_10_278_46567 : frontier 11 ⟨46567, by decide⟩
    (prefixCache 10 278) (prefixPartial 10 278) = false := by
  decide +kernel

theorem node_context_10_278_46567 : EJMOriginalGlobalDAGData.nodes 11 ⟨46567, by decide⟩ =
    .split (coordinate 10) (![⟨45793, by decide⟩,⟨46101, by decide⟩,⟨46325, by decide⟩,⟨46566, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_278_46567 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 278 ⟨46567, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 278
    ⟨46567, by decide⟩ (by decide) (![⟨45793, by decide⟩,⟨46101, by decide⟩,⟨46325, by decide⟩,⟨46566, by decide⟩]) unmarked_context_10_278_46567 node_context_10_278_46567
  intro a
  fin_cases a
  · exact context_11_1112_45793
  · exact context_11_1113_46101
  · exact context_11_1114_46325
  · exact context_11_1115_46566

theorem selected_cut_01266 : selected 11 ⟨3440, by decide⟩
    (prefixPartial 10 279) = some ⟨10, 1, 0, 3440, 279, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_279_3440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 279 ⟨3440, by decide⟩ :=
  accepted_of_selected 10 279 ⟨3440, by decide⟩ ⟨10, 1, 0, 3440, 279, 1, 1048576⟩
    (by decide) selected_cut_01266

theorem unmarked_context_9_69_46568 : frontier 12 ⟨46568, by decide⟩
    (prefixCache 9 69) (prefixPartial 9 69) = false := by
  decide +kernel

theorem node_context_9_69_46568 : EJMOriginalGlobalDAGData.nodes 12 ⟨46568, by decide⟩ =
    .split (coordinate 9) (![⟨44895, by decide⟩,⟨45549, by decide⟩,⟨46567, by decide⟩,⟨3440, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_69_46568 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 69 ⟨46568, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 69
    ⟨46568, by decide⟩ (by decide) (![⟨44895, by decide⟩,⟨45549, by decide⟩,⟨46567, by decide⟩,⟨3440, by decide⟩]) unmarked_context_9_69_46568 node_context_9_69_46568
  intro a
  fin_cases a
  · exact context_10_276_44895
  · exact context_10_277_45549
  · exact context_10_278_46567
  · exact context_10_279_3440

theorem selected_cut_01267 : selected 9 ⟨46609, by decide⟩
    (prefixPartial 12 4480) = some ⟨12, 2, 0, 46609, 4480, 3485, 65536⟩ := by
  decide +kernel

theorem context_12_4480_46609 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4480 ⟨46609, by decide⟩ :=
  accepted_of_selected 12 4480 ⟨46609, by decide⟩ ⟨12, 2, 0, 46609, 4480, 3485, 65536⟩
    (by decide) selected_cut_01267

theorem selected_cut_01268 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 17924) = some ⟨13, 1, 0, 3444, 17924, 1, 16384⟩ := by
  decide +kernel

theorem context_13_17924_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17924 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 17924 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 17924, 1, 16384⟩
    (by decide) selected_cut_01268

theorem selected_cut_01269 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 17925) = some ⟨13, 1, 0, 3444, 17925, 1, 16384⟩ := by
  decide +kernel

theorem context_13_17925_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17925 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 17925 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 17925, 1, 16384⟩
    (by decide) selected_cut_01269

theorem selected_cut_01270 : selected 8 ⟨46671, by decide⟩
    (prefixPartial 13 17926) = some ⟨13, 2, 0, 46671, 17926, 3113, 16384⟩ := by
  decide +kernel

theorem context_13_17926_46671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17926 ⟨46671, by decide⟩ :=
  accepted_of_selected 13 17926 ⟨46671, by decide⟩ ⟨13, 2, 0, 46671, 17926, 3113, 16384⟩
    (by decide) selected_cut_01270

theorem selected_cut_01271 : selected 8 ⟨46697, by decide⟩
    (prefixPartial 13 17927) = some ⟨13, 2, 0, 46697, 17927, 1373, 16384⟩ := by
  decide +kernel

theorem context_13_17927_46697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17927 ⟨46697, by decide⟩ :=
  accepted_of_selected 13 17927 ⟨46697, by decide⟩ ⟨13, 2, 0, 46697, 17927, 1373, 16384⟩
    (by decide) selected_cut_01271

theorem unmarked_context_12_4481_46698 : frontier 9 ⟨46698, by decide⟩
    (prefixCache 12 4481) (prefixPartial 12 4481) = false := by
  decide +kernel

theorem node_context_12_4481_46698 : EJMOriginalGlobalDAGData.nodes 9 ⟨46698, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨3444, by decide⟩,⟨46671, by decide⟩,⟨46697, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4481_46698 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4481 ⟨46698, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4481
    ⟨46698, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨3444, by decide⟩,⟨46671, by decide⟩,⟨46697, by decide⟩]) unmarked_context_12_4481_46698 node_context_12_4481_46698
  intro a
  fin_cases a
  · exact context_13_17924_3444
  · exact context_13_17925_3444
  · exact context_13_17926_46671
  · exact context_13_17927_46697

theorem selected_cut_01272 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 17928) = some ⟨13, 1, 0, 3444, 17928, 1, 16384⟩ := by
  decide +kernel

theorem context_13_17928_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17928 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 17928 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 17928, 1, 16384⟩
    (by decide) selected_cut_01272

theorem selected_cut_01273 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 17929) = some ⟨13, 1, 0, 3444, 17929, 1, 16384⟩ := by
  decide +kernel

theorem context_13_17929_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17929 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 17929 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 17929, 1, 16384⟩
    (by decide) selected_cut_01273

theorem selected_cut_01274 : selected 8 ⟨46759, by decide⟩
    (prefixPartial 13 17930) = some ⟨13, 2, 0, 46759, 17930, 3289, 16384⟩ := by
  decide +kernel

theorem context_13_17930_46759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17930 ⟨46759, by decide⟩ :=
  accepted_of_selected 13 17930 ⟨46759, by decide⟩ ⟨13, 2, 0, 46759, 17930, 3289, 16384⟩
    (by decide) selected_cut_01274

theorem selected_cut_01275 : selected 8 ⟨46781, by decide⟩
    (prefixPartial 13 17931) = some ⟨13, 2, 0, 46781, 17931, 1305, 16384⟩ := by
  decide +kernel

theorem context_13_17931_46781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17931 ⟨46781, by decide⟩ :=
  accepted_of_selected 13 17931 ⟨46781, by decide⟩ ⟨13, 2, 0, 46781, 17931, 1305, 16384⟩
    (by decide) selected_cut_01275

theorem unmarked_context_12_4482_46782 : frontier 9 ⟨46782, by decide⟩
    (prefixCache 12 4482) (prefixPartial 12 4482) = false := by
  decide +kernel

theorem node_context_12_4482_46782 : EJMOriginalGlobalDAGData.nodes 9 ⟨46782, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨3444, by decide⟩,⟨46759, by decide⟩,⟨46781, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4482_46782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4482 ⟨46782, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4482
    ⟨46782, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨3444, by decide⟩,⟨46759, by decide⟩,⟨46781, by decide⟩]) unmarked_context_12_4482_46782 node_context_12_4482_46782
  intro a
  fin_cases a
  · exact context_13_17928_3444
  · exact context_13_17929_3444
  · exact context_13_17930_46759
  · exact context_13_17931_46781

theorem selected_cut_01276 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 17932) = some ⟨13, 1, 0, 3444, 17932, 1, 16384⟩ := by
  decide +kernel

theorem context_13_17932_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17932 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 17932 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 17932, 1, 16384⟩
    (by decide) selected_cut_01276

theorem selected_cut_01277 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 17933) = some ⟨13, 1, 0, 3444, 17933, 1, 16384⟩ := by
  decide +kernel

theorem context_13_17933_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17933 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 17933 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 17933, 1, 16384⟩
    (by decide) selected_cut_01277

theorem selected_cut_01278 : selected 8 ⟨46844, by decide⟩
    (prefixPartial 13 17934) = some ⟨13, 2, 0, 46844, 17934, 3261, 16384⟩ := by
  decide +kernel

theorem context_13_17934_46844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17934 ⟨46844, by decide⟩ :=
  accepted_of_selected 13 17934 ⟨46844, by decide⟩ ⟨13, 2, 0, 46844, 17934, 3261, 16384⟩
    (by decide) selected_cut_01278

theorem selected_cut_01279 : selected 8 ⟨46874, by decide⟩
    (prefixPartial 13 17935) = some ⟨13, 2, 0, 46874, 17935, 1521, 16384⟩ := by
  decide +kernel

theorem context_13_17935_46874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17935 ⟨46874, by decide⟩ :=
  accepted_of_selected 13 17935 ⟨46874, by decide⟩ ⟨13, 2, 0, 46874, 17935, 1521, 16384⟩
    (by decide) selected_cut_01279

theorem unmarked_context_12_4483_46875 : frontier 9 ⟨46875, by decide⟩
    (prefixCache 12 4483) (prefixPartial 12 4483) = false := by
  decide +kernel

theorem node_context_12_4483_46875 : EJMOriginalGlobalDAGData.nodes 9 ⟨46875, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨3444, by decide⟩,⟨46844, by decide⟩,⟨46874, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4483_46875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4483 ⟨46875, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4483
    ⟨46875, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨3444, by decide⟩,⟨46844, by decide⟩,⟨46874, by decide⟩]) unmarked_context_12_4483_46875 node_context_12_4483_46875
  intro a
  fin_cases a
  · exact context_13_17932_3444
  · exact context_13_17933_3444
  · exact context_13_17934_46844
  · exact context_13_17935_46874

theorem unmarked_context_11_1120_46876 : frontier 10 ⟨46876, by decide⟩
    (prefixCache 11 1120) (prefixPartial 11 1120) = false := by
  decide +kernel

theorem node_context_11_1120_46876 : EJMOriginalGlobalDAGData.nodes 10 ⟨46876, by decide⟩ =
    .split (coordinate 11) (![⟨46609, by decide⟩,⟨46698, by decide⟩,⟨46782, by decide⟩,⟨46875, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1120_46876 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1120 ⟨46876, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1120
    ⟨46876, by decide⟩ (by decide) (![⟨46609, by decide⟩,⟨46698, by decide⟩,⟨46782, by decide⟩,⟨46875, by decide⟩]) unmarked_context_11_1120_46876 node_context_11_1120_46876
  intro a
  fin_cases a
  · exact context_12_4480_46609
  · exact context_12_4481_46698
  · exact context_12_4482_46782
  · exact context_12_4483_46875

theorem selected_cut_01280 : selected 9 ⟨46922, by decide⟩
    (prefixPartial 12 4484) = some ⟨12, 2, 0, 46922, 4484, 2053, 65536⟩ := by
  decide +kernel

theorem context_12_4484_46922 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4484 ⟨46922, by decide⟩ :=
  accepted_of_selected 12 4484 ⟨46922, by decide⟩ ⟨12, 2, 0, 46922, 4484, 2053, 65536⟩
    (by decide) selected_cut_01280

theorem selected_cut_01281 : selected 9 ⟨46998, by decide⟩
    (prefixPartial 12 4485) = some ⟨12, 2, 0, 46998, 4485, 3753, 65536⟩ := by
  decide +kernel

theorem context_12_4485_46998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4485 ⟨46998, by decide⟩ :=
  accepted_of_selected 12 4485 ⟨46998, by decide⟩ ⟨12, 2, 0, 46998, 4485, 3753, 65536⟩
    (by decide) selected_cut_01281

theorem selected_cut_01282 : selected 9 ⟨47050, by decide⟩
    (prefixPartial 12 4486) = some ⟨12, 2, 0, 47050, 4486, 2613, 65536⟩ := by
  decide +kernel

theorem context_12_4486_47050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4486 ⟨47050, by decide⟩ :=
  accepted_of_selected 12 4486 ⟨47050, by decide⟩ ⟨12, 2, 0, 47050, 4486, 2613, 65536⟩
    (by decide) selected_cut_01282

theorem selected_cut_01283 : selected 9 ⟨47092, by decide⟩
    (prefixPartial 12 4487) = some ⟨12, 2, 0, 47092, 4487, 2693, 65536⟩ := by
  decide +kernel

theorem context_12_4487_47092 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4487 ⟨47092, by decide⟩ :=
  accepted_of_selected 12 4487 ⟨47092, by decide⟩ ⟨12, 2, 0, 47092, 4487, 2693, 65536⟩
    (by decide) selected_cut_01283

theorem unmarked_context_11_1121_47093 : frontier 10 ⟨47093, by decide⟩
    (prefixCache 11 1121) (prefixPartial 11 1121) = false := by
  decide +kernel

theorem node_context_11_1121_47093 : EJMOriginalGlobalDAGData.nodes 10 ⟨47093, by decide⟩ =
    .split (coordinate 11) (![⟨46922, by decide⟩,⟨46998, by decide⟩,⟨47050, by decide⟩,⟨47092, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1121_47093 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1121 ⟨47093, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1121
    ⟨47093, by decide⟩ (by decide) (![⟨46922, by decide⟩,⟨46998, by decide⟩,⟨47050, by decide⟩,⟨47092, by decide⟩]) unmarked_context_11_1121_47093 node_context_11_1121_47093
  intro a
  fin_cases a
  · exact context_12_4484_46922
  · exact context_12_4485_46998
  · exact context_12_4486_47050
  · exact context_12_4487_47092

theorem selected_cut_01284 : selected 9 ⟨47144, by decide⟩
    (prefixPartial 12 4488) = some ⟨12, 2, 0, 47144, 4488, 2201, 65536⟩ := by
  decide +kernel

theorem context_12_4488_47144 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4488 ⟨47144, by decide⟩ :=
  accepted_of_selected 12 4488 ⟨47144, by decide⟩ ⟨12, 2, 0, 47144, 4488, 2201, 65536⟩
    (by decide) selected_cut_01284

theorem selected_cut_01285 : selected 9 ⟨47205, by decide⟩
    (prefixPartial 12 4489) = some ⟨12, 2, 0, 47205, 4489, 2793, 65536⟩ := by
  decide +kernel

theorem context_12_4489_47205 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4489 ⟨47205, by decide⟩ :=
  accepted_of_selected 12 4489 ⟨47205, by decide⟩ ⟨12, 2, 0, 47205, 4489, 2793, 65536⟩
    (by decide) selected_cut_01285

theorem selected_cut_01286 : selected 9 ⟨47246, by decide⟩
    (prefixPartial 12 4490) = some ⟨12, 2, 0, 47246, 4490, 2401, 65536⟩ := by
  decide +kernel

theorem context_12_4490_47246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4490 ⟨47246, by decide⟩ :=
  accepted_of_selected 12 4490 ⟨47246, by decide⟩ ⟨12, 2, 0, 47246, 4490, 2401, 65536⟩
    (by decide) selected_cut_01286

theorem selected_cut_01287 : selected 9 ⟨47290, by decide⟩
    (prefixPartial 12 4491) = some ⟨12, 2, 0, 47290, 4491, 2657, 65536⟩ := by
  decide +kernel

theorem context_12_4491_47290 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4491 ⟨47290, by decide⟩ :=
  accepted_of_selected 12 4491 ⟨47290, by decide⟩ ⟨12, 2, 0, 47290, 4491, 2657, 65536⟩
    (by decide) selected_cut_01287

theorem unmarked_context_11_1122_47291 : frontier 10 ⟨47291, by decide⟩
    (prefixCache 11 1122) (prefixPartial 11 1122) = false := by
  decide +kernel

theorem node_context_11_1122_47291 : EJMOriginalGlobalDAGData.nodes 10 ⟨47291, by decide⟩ =
    .split (coordinate 11) (![⟨47144, by decide⟩,⟨47205, by decide⟩,⟨47246, by decide⟩,⟨47290, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1122_47291 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1122 ⟨47291, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1122
    ⟨47291, by decide⟩ (by decide) (![⟨47144, by decide⟩,⟨47205, by decide⟩,⟨47246, by decide⟩,⟨47290, by decide⟩]) unmarked_context_11_1122_47291 node_context_11_1122_47291
  intro a
  fin_cases a
  · exact context_12_4488_47144
  · exact context_12_4489_47205
  · exact context_12_4490_47246
  · exact context_12_4491_47290

theorem selected_cut_01288 : selected 9 ⟨47331, by decide⟩
    (prefixPartial 12 4492) = some ⟨12, 2, 0, 47331, 4492, 1849, 65536⟩ := by
  decide +kernel

theorem context_12_4492_47331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4492 ⟨47331, by decide⟩ :=
  accepted_of_selected 12 4492 ⟨47331, by decide⟩ ⟨12, 2, 0, 47331, 4492, 1849, 65536⟩
    (by decide) selected_cut_01288

theorem selected_cut_01289 : selected 9 ⟨47372, by decide⟩
    (prefixPartial 12 4493) = some ⟨12, 2, 0, 47372, 4493, 2389, 65536⟩ := by
  decide +kernel

theorem context_12_4493_47372 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4493 ⟨47372, by decide⟩ :=
  accepted_of_selected 12 4493 ⟨47372, by decide⟩ ⟨12, 2, 0, 47372, 4493, 2389, 65536⟩
    (by decide) selected_cut_01289

theorem selected_cut_01290 : selected 9 ⟨47417, by decide⟩
    (prefixPartial 12 4494) = some ⟨12, 2, 0, 47417, 4494, 2321, 65536⟩ := by
  decide +kernel

theorem context_12_4494_47417 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4494 ⟨47417, by decide⟩ :=
  accepted_of_selected 12 4494 ⟨47417, by decide⟩ ⟨12, 2, 0, 47417, 4494, 2321, 65536⟩
    (by decide) selected_cut_01290

theorem selected_cut_01291 : selected 9 ⟨47453, by decide⟩
    (prefixPartial 12 4495) = some ⟨12, 2, 0, 47453, 4495, 2217, 65536⟩ := by
  decide +kernel

theorem context_12_4495_47453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4495 ⟨47453, by decide⟩ :=
  accepted_of_selected 12 4495 ⟨47453, by decide⟩ ⟨12, 2, 0, 47453, 4495, 2217, 65536⟩
    (by decide) selected_cut_01291

theorem unmarked_context_11_1123_47454 : frontier 10 ⟨47454, by decide⟩
    (prefixCache 11 1123) (prefixPartial 11 1123) = false := by
  decide +kernel

theorem node_context_11_1123_47454 : EJMOriginalGlobalDAGData.nodes 10 ⟨47454, by decide⟩ =
    .split (coordinate 11) (![⟨47331, by decide⟩,⟨47372, by decide⟩,⟨47417, by decide⟩,⟨47453, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1123_47454 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1123 ⟨47454, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1123
    ⟨47454, by decide⟩ (by decide) (![⟨47331, by decide⟩,⟨47372, by decide⟩,⟨47417, by decide⟩,⟨47453, by decide⟩]) unmarked_context_11_1123_47454 node_context_11_1123_47454
  intro a
  fin_cases a
  · exact context_12_4492_47331
  · exact context_12_4493_47372
  · exact context_12_4494_47417
  · exact context_12_4495_47453

theorem unmarked_context_10_280_47455 : frontier 11 ⟨47455, by decide⟩
    (prefixCache 10 280) (prefixPartial 10 280) = false := by
  decide +kernel

theorem node_context_10_280_47455 : EJMOriginalGlobalDAGData.nodes 11 ⟨47455, by decide⟩ =
    .split (coordinate 10) (![⟨46876, by decide⟩,⟨47093, by decide⟩,⟨47291, by decide⟩,⟨47454, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_280_47455 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 280 ⟨47455, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 280
    ⟨47455, by decide⟩ (by decide) (![⟨46876, by decide⟩,⟨47093, by decide⟩,⟨47291, by decide⟩,⟨47454, by decide⟩]) unmarked_context_10_280_47455 node_context_10_280_47455
  intro a
  fin_cases a
  · exact context_11_1120_46876
  · exact context_11_1121_47093
  · exact context_11_1122_47291
  · exact context_11_1123_47454

theorem selected_cut_01292 : selected 9 ⟨47501, by decide⟩
    (prefixPartial 12 4496) = some ⟨12, 2, 0, 47501, 4496, 1369, 65536⟩ := by
  decide +kernel

theorem context_12_4496_47501 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4496 ⟨47501, by decide⟩ :=
  accepted_of_selected 12 4496 ⟨47501, by decide⟩ ⟨12, 2, 0, 47501, 4496, 1369, 65536⟩
    (by decide) selected_cut_01292

theorem selected_cut_01293 : selected 9 ⟨47538, by decide⟩
    (prefixPartial 12 4497) = some ⟨12, 2, 0, 47538, 4497, 1769, 65536⟩ := by
  decide +kernel

theorem context_12_4497_47538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4497 ⟨47538, by decide⟩ :=
  accepted_of_selected 12 4497 ⟨47538, by decide⟩ ⟨12, 2, 0, 47538, 4497, 1769, 65536⟩
    (by decide) selected_cut_01293

theorem selected_cut_01294 : selected 9 ⟨47573, by decide⟩
    (prefixPartial 12 4498) = some ⟨12, 2, 0, 47573, 4498, 1921, 65536⟩ := by
  decide +kernel

theorem context_12_4498_47573 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4498 ⟨47573, by decide⟩ :=
  accepted_of_selected 12 4498 ⟨47573, by decide⟩ ⟨12, 2, 0, 47573, 4498, 1921, 65536⟩
    (by decide) selected_cut_01294

theorem selected_cut_01295 : selected 9 ⟨47612, by decide⟩
    (prefixPartial 12 4499) = some ⟨12, 2, 0, 47612, 4499, 1921, 65536⟩ := by
  decide +kernel

theorem context_12_4499_47612 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4499 ⟨47612, by decide⟩ :=
  accepted_of_selected 12 4499 ⟨47612, by decide⟩ ⟨12, 2, 0, 47612, 4499, 1921, 65536⟩
    (by decide) selected_cut_01295

theorem unmarked_context_11_1124_47613 : frontier 10 ⟨47613, by decide⟩
    (prefixCache 11 1124) (prefixPartial 11 1124) = false := by
  decide +kernel

theorem node_context_11_1124_47613 : EJMOriginalGlobalDAGData.nodes 10 ⟨47613, by decide⟩ =
    .split (coordinate 11) (![⟨47501, by decide⟩,⟨47538, by decide⟩,⟨47573, by decide⟩,⟨47612, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1124_47613 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1124 ⟨47613, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1124
    ⟨47613, by decide⟩ (by decide) (![⟨47501, by decide⟩,⟨47538, by decide⟩,⟨47573, by decide⟩,⟨47612, by decide⟩]) unmarked_context_11_1124_47613 node_context_11_1124_47613
  intro a
  fin_cases a
  · exact context_12_4496_47501
  · exact context_12_4497_47538
  · exact context_12_4498_47573
  · exact context_12_4499_47612

theorem selected_cut_01296 : selected 9 ⟨47649, by decide⟩
    (prefixPartial 12 4500) = some ⟨12, 2, 0, 47649, 4500, 1325, 65536⟩ := by
  decide +kernel

theorem context_12_4500_47649 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4500 ⟨47649, by decide⟩ :=
  accepted_of_selected 12 4500 ⟨47649, by decide⟩ ⟨12, 2, 0, 47649, 4500, 1325, 65536⟩
    (by decide) selected_cut_01296

theorem selected_cut_01297 : selected 9 ⟨47729, by decide⟩
    (prefixPartial 12 4501) = some ⟨12, 2, 0, 47729, 4501, 2553, 65536⟩ := by
  decide +kernel

theorem context_12_4501_47729 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4501 ⟨47729, by decide⟩ :=
  accepted_of_selected 12 4501 ⟨47729, by decide⟩ ⟨12, 2, 0, 47729, 4501, 2553, 65536⟩
    (by decide) selected_cut_01297

theorem selected_cut_01298 : selected 9 ⟨47761, by decide⟩
    (prefixPartial 12 4502) = some ⟨12, 2, 0, 47761, 4502, 1745, 65536⟩ := by
  decide +kernel

theorem context_12_4502_47761 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4502 ⟨47761, by decide⟩ :=
  accepted_of_selected 12 4502 ⟨47761, by decide⟩ ⟨12, 2, 0, 47761, 4502, 1745, 65536⟩
    (by decide) selected_cut_01298

theorem selected_cut_01299 : selected 9 ⟨47788, by decide⟩
    (prefixPartial 12 4503) = some ⟨12, 2, 0, 47788, 4503, 1801, 65536⟩ := by
  decide +kernel

theorem context_12_4503_47788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4503 ⟨47788, by decide⟩ :=
  accepted_of_selected 12 4503 ⟨47788, by decide⟩ ⟨12, 2, 0, 47788, 4503, 1801, 65536⟩
    (by decide) selected_cut_01299

theorem unmarked_context_11_1125_47789 : frontier 10 ⟨47789, by decide⟩
    (prefixCache 11 1125) (prefixPartial 11 1125) = false := by
  decide +kernel

theorem node_context_11_1125_47789 : EJMOriginalGlobalDAGData.nodes 10 ⟨47789, by decide⟩ =
    .split (coordinate 11) (![⟨47649, by decide⟩,⟨47729, by decide⟩,⟨47761, by decide⟩,⟨47788, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1125_47789 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1125 ⟨47789, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1125
    ⟨47789, by decide⟩ (by decide) (![⟨47649, by decide⟩,⟨47729, by decide⟩,⟨47761, by decide⟩,⟨47788, by decide⟩]) unmarked_context_11_1125_47789 node_context_11_1125_47789
  intro a
  fin_cases a
  · exact context_12_4500_47649
  · exact context_12_4501_47729
  · exact context_12_4502_47761
  · exact context_12_4503_47788

theorem selected_cut_01300 : selected 9 ⟨47826, by decide⟩
    (prefixPartial 12 4504) = some ⟨12, 2, 0, 47826, 4504, 1497, 65536⟩ := by
  decide +kernel

theorem context_12_4504_47826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4504 ⟨47826, by decide⟩ :=
  accepted_of_selected 12 4504 ⟨47826, by decide⟩ ⟨12, 2, 0, 47826, 4504, 1497, 65536⟩
    (by decide) selected_cut_01300

theorem selected_cut_01301 : selected 9 ⟨47867, by decide⟩
    (prefixPartial 12 4505) = some ⟨12, 2, 0, 47867, 4505, 1837, 65536⟩ := by
  decide +kernel

theorem context_12_4505_47867 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4505 ⟨47867, by decide⟩ :=
  accepted_of_selected 12 4505 ⟨47867, by decide⟩ ⟨12, 2, 0, 47867, 4505, 1837, 65536⟩
    (by decide) selected_cut_01301

theorem selected_cut_01302 : selected 9 ⟨47892, by decide⟩
    (prefixPartial 12 4506) = some ⟨12, 2, 0, 47892, 4506, 1673, 65536⟩ := by
  decide +kernel

theorem context_12_4506_47892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4506 ⟨47892, by decide⟩ :=
  accepted_of_selected 12 4506 ⟨47892, by decide⟩ ⟨12, 2, 0, 47892, 4506, 1673, 65536⟩
    (by decide) selected_cut_01302

theorem selected_cut_01303 : selected 9 ⟨47926, by decide⟩
    (prefixPartial 12 4507) = some ⟨12, 2, 0, 47926, 4507, 1745, 65536⟩ := by
  decide +kernel

theorem context_12_4507_47926 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4507 ⟨47926, by decide⟩ :=
  accepted_of_selected 12 4507 ⟨47926, by decide⟩ ⟨12, 2, 0, 47926, 4507, 1745, 65536⟩
    (by decide) selected_cut_01303

theorem unmarked_context_11_1126_47927 : frontier 10 ⟨47927, by decide⟩
    (prefixCache 11 1126) (prefixPartial 11 1126) = false := by
  decide +kernel

theorem node_context_11_1126_47927 : EJMOriginalGlobalDAGData.nodes 10 ⟨47927, by decide⟩ =
    .split (coordinate 11) (![⟨47826, by decide⟩,⟨47867, by decide⟩,⟨47892, by decide⟩,⟨47926, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1126_47927 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1126 ⟨47927, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1126
    ⟨47927, by decide⟩ (by decide) (![⟨47826, by decide⟩,⟨47867, by decide⟩,⟨47892, by decide⟩,⟨47926, by decide⟩]) unmarked_context_11_1126_47927 node_context_11_1126_47927
  intro a
  fin_cases a
  · exact context_12_4504_47826
  · exact context_12_4505_47867
  · exact context_12_4506_47892
  · exact context_12_4507_47926

theorem selected_cut_01304 : selected 9 ⟨47953, by decide⟩
    (prefixPartial 12 4508) = some ⟨12, 2, 0, 47953, 4508, 1225, 65536⟩ := by
  decide +kernel

theorem context_12_4508_47953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4508 ⟨47953, by decide⟩ :=
  accepted_of_selected 12 4508 ⟨47953, by decide⟩ ⟨12, 2, 0, 47953, 4508, 1225, 65536⟩
    (by decide) selected_cut_01304

theorem selected_cut_01305 : selected 9 ⟨47980, by decide⟩
    (prefixPartial 12 4509) = some ⟨12, 2, 0, 47980, 4509, 1493, 65536⟩ := by
  decide +kernel

theorem context_12_4509_47980 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4509 ⟨47980, by decide⟩ :=
  accepted_of_selected 12 4509 ⟨47980, by decide⟩ ⟨12, 2, 0, 47980, 4509, 1493, 65536⟩
    (by decide) selected_cut_01305

theorem selected_cut_01306 : selected 9 ⟨48011, by decide⟩
    (prefixPartial 12 4510) = some ⟨12, 2, 0, 48011, 4510, 1533, 65536⟩ := by
  decide +kernel

theorem context_12_4510_48011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4510 ⟨48011, by decide⟩ :=
  accepted_of_selected 12 4510 ⟨48011, by decide⟩ ⟨12, 2, 0, 48011, 4510, 1533, 65536⟩
    (by decide) selected_cut_01306

theorem selected_cut_01307 : selected 9 ⟨48034, by decide⟩
    (prefixPartial 12 4511) = some ⟨12, 2, 0, 48034, 4511, 1413, 65536⟩ := by
  decide +kernel

theorem context_12_4511_48034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4511 ⟨48034, by decide⟩ :=
  accepted_of_selected 12 4511 ⟨48034, by decide⟩ ⟨12, 2, 0, 48034, 4511, 1413, 65536⟩
    (by decide) selected_cut_01307

theorem unmarked_context_11_1127_48035 : frontier 10 ⟨48035, by decide⟩
    (prefixCache 11 1127) (prefixPartial 11 1127) = false := by
  decide +kernel

theorem node_context_11_1127_48035 : EJMOriginalGlobalDAGData.nodes 10 ⟨48035, by decide⟩ =
    .split (coordinate 11) (![⟨47953, by decide⟩,⟨47980, by decide⟩,⟨48011, by decide⟩,⟨48034, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1127_48035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1127 ⟨48035, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1127
    ⟨48035, by decide⟩ (by decide) (![⟨47953, by decide⟩,⟨47980, by decide⟩,⟨48011, by decide⟩,⟨48034, by decide⟩]) unmarked_context_11_1127_48035 node_context_11_1127_48035
  intro a
  fin_cases a
  · exact context_12_4508_47953
  · exact context_12_4509_47980
  · exact context_12_4510_48011
  · exact context_12_4511_48034

theorem unmarked_context_10_281_48036 : frontier 11 ⟨48036, by decide⟩
    (prefixCache 10 281) (prefixPartial 10 281) = false := by
  decide +kernel

theorem node_context_10_281_48036 : EJMOriginalGlobalDAGData.nodes 11 ⟨48036, by decide⟩ =
    .split (coordinate 10) (![⟨47613, by decide⟩,⟨47789, by decide⟩,⟨47927, by decide⟩,⟨48035, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_281_48036 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 281 ⟨48036, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 281
    ⟨48036, by decide⟩ (by decide) (![⟨47613, by decide⟩,⟨47789, by decide⟩,⟨47927, by decide⟩,⟨48035, by decide⟩]) unmarked_context_10_281_48036 node_context_10_281_48036
  intro a
  fin_cases a
  · exact context_11_1124_47613
  · exact context_11_1125_47789
  · exact context_11_1126_47927
  · exact context_11_1127_48035

theorem selected_cut_01308 : selected 10 ⟨48113, by decide⟩
    (prefixPartial 11 1128) = some ⟨11, 2, 0, 48113, 1128, 3857, 262144⟩ := by
  decide +kernel

theorem context_11_1128_48113 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1128 ⟨48113, by decide⟩ :=
  accepted_of_selected 11 1128 ⟨48113, by decide⟩ ⟨11, 2, 0, 48113, 1128, 3857, 262144⟩
    (by decide) selected_cut_01308

theorem selected_cut_01309 : selected 9 ⟨48133, by decide⟩
    (prefixPartial 12 4516) = some ⟨12, 2, 0, 48133, 4516, 853, 65536⟩ := by
  decide +kernel

theorem context_12_4516_48133 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4516 ⟨48133, by decide⟩ :=
  accepted_of_selected 12 4516 ⟨48133, by decide⟩ ⟨12, 2, 0, 48133, 4516, 853, 65536⟩
    (by decide) selected_cut_01309

theorem selected_cut_01310 : selected 9 ⟨48194, by decide⟩
    (prefixPartial 12 4517) = some ⟨12, 2, 0, 48194, 4517, 1413, 65536⟩ := by
  decide +kernel

theorem context_12_4517_48194 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4517 ⟨48194, by decide⟩ :=
  accepted_of_selected 12 4517 ⟨48194, by decide⟩ ⟨12, 2, 0, 48194, 4517, 1413, 65536⟩
    (by decide) selected_cut_01310

theorem selected_cut_01311 : selected 9 ⟨48221, by decide⟩
    (prefixPartial 12 4518) = some ⟨12, 2, 0, 48221, 4518, 1033, 65536⟩ := by
  decide +kernel

theorem context_12_4518_48221 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4518 ⟨48221, by decide⟩ :=
  accepted_of_selected 12 4518 ⟨48221, by decide⟩ ⟨12, 2, 0, 48221, 4518, 1033, 65536⟩
    (by decide) selected_cut_01311

theorem selected_cut_01312 : selected 9 ⟨48237, by decide⟩
    (prefixPartial 12 4519) = some ⟨12, 2, 0, 48237, 4519, 933, 65536⟩ := by
  decide +kernel

theorem context_12_4519_48237 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4519 ⟨48237, by decide⟩ :=
  accepted_of_selected 12 4519 ⟨48237, by decide⟩ ⟨12, 2, 0, 48237, 4519, 933, 65536⟩
    (by decide) selected_cut_01312

theorem unmarked_context_11_1129_48238 : frontier 10 ⟨48238, by decide⟩
    (prefixCache 11 1129) (prefixPartial 11 1129) = false := by
  decide +kernel

theorem node_context_11_1129_48238 : EJMOriginalGlobalDAGData.nodes 10 ⟨48238, by decide⟩ =
    .split (coordinate 11) (![⟨48133, by decide⟩,⟨48194, by decide⟩,⟨48221, by decide⟩,⟨48237, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1129_48238 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1129 ⟨48238, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1129
    ⟨48238, by decide⟩ (by decide) (![⟨48133, by decide⟩,⟨48194, by decide⟩,⟨48221, by decide⟩,⟨48237, by decide⟩]) unmarked_context_11_1129_48238 node_context_11_1129_48238
  intro a
  fin_cases a
  · exact context_12_4516_48133
  · exact context_12_4517_48194
  · exact context_12_4518_48221
  · exact context_12_4519_48237

theorem selected_cut_01313 : selected 10 ⟨48303, by decide⟩
    (prefixPartial 11 1130) = some ⟨11, 2, 0, 48303, 1130, 3129, 262144⟩ := by
  decide +kernel

theorem context_11_1130_48303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1130 ⟨48303, by decide⟩ :=
  accepted_of_selected 11 1130 ⟨48303, by decide⟩ ⟨11, 2, 0, 48303, 1130, 3129, 262144⟩
    (by decide) selected_cut_01313

theorem selected_cut_01314 : selected 10 ⟨48380, by decide⟩
    (prefixPartial 11 1131) = some ⟨11, 2, 0, 48380, 1131, 2885, 262144⟩ := by
  decide +kernel

theorem context_11_1131_48380 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1131 ⟨48380, by decide⟩ :=
  accepted_of_selected 11 1131 ⟨48380, by decide⟩ ⟨11, 2, 0, 48380, 1131, 2885, 262144⟩
    (by decide) selected_cut_01314

theorem unmarked_context_10_282_48381 : frontier 11 ⟨48381, by decide⟩
    (prefixCache 10 282) (prefixPartial 10 282) = false := by
  decide +kernel

theorem node_context_10_282_48381 : EJMOriginalGlobalDAGData.nodes 11 ⟨48381, by decide⟩ =
    .split (coordinate 10) (![⟨48113, by decide⟩,⟨48238, by decide⟩,⟨48303, by decide⟩,⟨48380, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_282_48381 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 282 ⟨48381, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 282
    ⟨48381, by decide⟩ (by decide) (![⟨48113, by decide⟩,⟨48238, by decide⟩,⟨48303, by decide⟩,⟨48380, by decide⟩]) unmarked_context_10_282_48381 node_context_10_282_48381
  intro a
  fin_cases a
  · exact context_11_1128_48113
  · exact context_11_1129_48238
  · exact context_11_1130_48303
  · exact context_11_1131_48380

theorem selected_cut_01315 : selected 10 ⟨48429, by decide⟩
    (prefixPartial 11 1132) = some ⟨11, 2, 0, 48429, 1132, 1917, 262144⟩ := by
  decide +kernel

theorem context_11_1132_48429 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1132 ⟨48429, by decide⟩ :=
  accepted_of_selected 11 1132 ⟨48429, by decide⟩ ⟨11, 2, 0, 48429, 1132, 1917, 262144⟩
    (by decide) selected_cut_01315

theorem selected_cut_01316 : selected 10 ⟨48484, by decide⟩
    (prefixPartial 11 1133) = some ⟨11, 2, 0, 48484, 1133, 1541, 262144⟩ := by
  decide +kernel

theorem context_11_1133_48484 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1133 ⟨48484, by decide⟩ :=
  accepted_of_selected 11 1133 ⟨48484, by decide⟩ ⟨11, 2, 0, 48484, 1133, 1541, 262144⟩
    (by decide) selected_cut_01316

theorem selected_cut_01317 : selected 10 ⟨48518, by decide⟩
    (prefixPartial 11 1134) = some ⟨11, 2, 0, 48518, 1134, 893, 262144⟩ := by
  decide +kernel

theorem context_11_1134_48518 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1134 ⟨48518, by decide⟩ :=
  accepted_of_selected 11 1134 ⟨48518, by decide⟩ ⟨11, 2, 0, 48518, 1134, 893, 262144⟩
    (by decide) selected_cut_01317

theorem selected_cut_01318 : selected 10 ⟨48542, by decide⟩
    (prefixPartial 11 1135) = some ⟨11, 2, 0, 48542, 1135, 357, 262144⟩ := by
  decide +kernel

theorem context_11_1135_48542 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1135 ⟨48542, by decide⟩ :=
  accepted_of_selected 11 1135 ⟨48542, by decide⟩ ⟨11, 2, 0, 48542, 1135, 357, 262144⟩
    (by decide) selected_cut_01318

theorem unmarked_context_10_283_48543 : frontier 11 ⟨48543, by decide⟩
    (prefixCache 10 283) (prefixPartial 10 283) = false := by
  decide +kernel

theorem node_context_10_283_48543 : EJMOriginalGlobalDAGData.nodes 11 ⟨48543, by decide⟩ =
    .split (coordinate 10) (![⟨48429, by decide⟩,⟨48484, by decide⟩,⟨48518, by decide⟩,⟨48542, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_283_48543 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 283 ⟨48543, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 283
    ⟨48543, by decide⟩ (by decide) (![⟨48429, by decide⟩,⟨48484, by decide⟩,⟨48518, by decide⟩,⟨48542, by decide⟩]) unmarked_context_10_283_48543 node_context_10_283_48543
  intro a
  fin_cases a
  · exact context_11_1132_48429
  · exact context_11_1133_48484
  · exact context_11_1134_48518
  · exact context_11_1135_48542

theorem unmarked_context_9_70_48544 : frontier 12 ⟨48544, by decide⟩
    (prefixCache 9 70) (prefixPartial 9 70) = false := by
  decide +kernel

theorem node_context_9_70_48544 : EJMOriginalGlobalDAGData.nodes 12 ⟨48544, by decide⟩ =
    .split (coordinate 9) (![⟨47455, by decide⟩,⟨48036, by decide⟩,⟨48381, by decide⟩,⟨48543, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_70_48544 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 70 ⟨48544, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 70
    ⟨48544, by decide⟩ (by decide) (![⟨47455, by decide⟩,⟨48036, by decide⟩,⟨48381, by decide⟩,⟨48543, by decide⟩]) unmarked_context_9_70_48544 node_context_9_70_48544
  intro a
  fin_cases a
  · exact context_10_280_47455
  · exact context_10_281_48036
  · exact context_10_282_48381
  · exact context_10_283_48543

theorem selected_cut_01319 : selected 12 ⟨4601, by decide⟩
    (prefixPartial 9 71) = some ⟨9, 1, 0, 4601, 71, 1, 4194304⟩ := by
  decide +kernel

theorem context_9_71_4601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 71 ⟨4601, by decide⟩ :=
  accepted_of_selected 9 71 ⟨4601, by decide⟩ ⟨9, 1, 0, 4601, 71, 1, 4194304⟩
    (by decide) selected_cut_01319

theorem unmarked_context_8_17_48545 : frontier 13 ⟨48545, by decide⟩
    (prefixCache 8 17) (prefixPartial 8 17) = false := by
  decide +kernel

theorem node_context_8_17_48545 : EJMOriginalGlobalDAGData.nodes 13 ⟨48545, by decide⟩ =
    .split (coordinate 8) (![⟨44134, by decide⟩,⟨46568, by decide⟩,⟨48544, by decide⟩,⟨4601, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_17_48545 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 17 ⟨48545, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 17
    ⟨48545, by decide⟩ (by decide) (![⟨44134, by decide⟩,⟨46568, by decide⟩,⟨48544, by decide⟩,⟨4601, by decide⟩]) unmarked_context_8_17_48545 node_context_8_17_48545
  intro a
  fin_cases a
  · exact context_9_68_44134
  · exact context_9_69_46568
  · exact context_9_70_48544
  · exact context_9_71_4601

theorem selected_cut_01320 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 4608) = some ⟨12, 1, 0, 34034, 4608, 1, 65536⟩ := by
  decide +kernel

theorem context_12_4608_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4608 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 4608 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 4608, 1, 65536⟩
    (by decide) selected_cut_01320

theorem selected_cut_01321 : selected 7 ⟨48585, by decide⟩
    (prefixPartial 14 73744) = some ⟨14, 2, 0, 48585, 73744, 1005, 4096⟩ := by
  decide +kernel

theorem context_14_73744_48585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 73744 ⟨48585, by decide⟩ :=
  accepted_of_selected 14 73744 ⟨48585, by decide⟩ ⟨14, 2, 0, 48585, 73744, 1005, 4096⟩
    (by decide) selected_cut_01321

theorem selected_cut_01322 : selected 7 ⟨48617, by decide⟩
    (prefixPartial 14 73745) = some ⟨14, 2, 0, 48617, 73745, 1645, 4096⟩ := by
  decide +kernel

theorem context_14_73745_48617 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 73745 ⟨48617, by decide⟩ :=
  accepted_of_selected 14 73745 ⟨48617, by decide⟩ ⟨14, 2, 0, 48617, 73745, 1645, 4096⟩
    (by decide) selected_cut_01322

theorem selected_cut_01323 : selected 7 ⟨48653, by decide⟩
    (prefixPartial 14 73746) = some ⟨14, 2, 0, 48653, 73746, 1489, 4096⟩ := by
  decide +kernel

theorem context_14_73746_48653 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 73746 ⟨48653, by decide⟩ :=
  accepted_of_selected 14 73746 ⟨48653, by decide⟩ ⟨14, 2, 0, 48653, 73746, 1489, 4096⟩
    (by decide) selected_cut_01323

theorem selected_cut_01324 : selected 7 ⟨48686, by decide⟩
    (prefixPartial 14 73747) = some ⟨14, 2, 0, 48686, 73747, 1425, 4096⟩ := by
  decide +kernel

theorem context_14_73747_48686 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 73747 ⟨48686, by decide⟩ :=
  accepted_of_selected 14 73747 ⟨48686, by decide⟩ ⟨14, 2, 0, 48686, 73747, 1425, 4096⟩
    (by decide) selected_cut_01324

theorem unmarked_context_13_18436_48687 : frontier 8 ⟨48687, by decide⟩
    (prefixCache 13 18436) (prefixPartial 13 18436) = false := by
  decide +kernel

theorem node_context_13_18436_48687 : EJMOriginalGlobalDAGData.nodes 8 ⟨48687, by decide⟩ =
    .split (coordinate 13) (![⟨48585, by decide⟩,⟨48617, by decide⟩,⟨48653, by decide⟩,⟨48686, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_18436_48687 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18436 ⟨48687, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 18436
    ⟨48687, by decide⟩ (by decide) (![⟨48585, by decide⟩,⟨48617, by decide⟩,⟨48653, by decide⟩,⟨48686, by decide⟩]) unmarked_context_13_18436_48687 node_context_13_18436_48687
  intro a
  fin_cases a
  · exact context_14_73744_48585
  · exact context_14_73745_48617
  · exact context_14_73746_48653
  · exact context_14_73747_48686

theorem selected_cut_01325 : selected 8 ⟨48793, by decide⟩
    (prefixPartial 13 18437) = some ⟨13, 2, 0, 48793, 18437, 2897, 16384⟩ := by
  decide +kernel

theorem context_13_18437_48793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18437 ⟨48793, by decide⟩ :=
  accepted_of_selected 13 18437 ⟨48793, by decide⟩ ⟨13, 2, 0, 48793, 18437, 2897, 16384⟩
    (by decide) selected_cut_01325

theorem selected_cut_01326 : selected 8 ⟨48847, by decide⟩
    (prefixPartial 13 18438) = some ⟨13, 2, 0, 48847, 18438, 853, 16384⟩ := by
  decide +kernel

theorem context_13_18438_48847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18438 ⟨48847, by decide⟩ :=
  accepted_of_selected 13 18438 ⟨48847, by decide⟩ ⟨13, 2, 0, 48847, 18438, 853, 16384⟩
    (by decide) selected_cut_01326

theorem selected_cut_01327 : selected 8 ⟨48865, by decide⟩
    (prefixPartial 13 18439) = some ⟨13, 2, 0, 48865, 18439, 181, 16384⟩ := by
  decide +kernel

theorem context_13_18439_48865 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18439 ⟨48865, by decide⟩ :=
  accepted_of_selected 13 18439 ⟨48865, by decide⟩ ⟨13, 2, 0, 48865, 18439, 181, 16384⟩
    (by decide) selected_cut_01327

theorem unmarked_context_12_4609_48866 : frontier 9 ⟨48866, by decide⟩
    (prefixCache 12 4609) (prefixPartial 12 4609) = false := by
  decide +kernel

theorem node_context_12_4609_48866 : EJMOriginalGlobalDAGData.nodes 9 ⟨48866, by decide⟩ =
    .split (coordinate 12) (![⟨48687, by decide⟩,⟨48793, by decide⟩,⟨48847, by decide⟩,⟨48865, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4609_48866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4609 ⟨48866, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4609
    ⟨48866, by decide⟩ (by decide) (![⟨48687, by decide⟩,⟨48793, by decide⟩,⟨48847, by decide⟩,⟨48865, by decide⟩]) unmarked_context_12_4609_48866 node_context_12_4609_48866
  intro a
  fin_cases a
  · exact context_13_18436_48687
  · exact context_13_18437_48793
  · exact context_13_18438_48847
  · exact context_13_18439_48865

theorem selected_cut_01328 : selected 9 ⟨48867, by decide⟩
    (prefixPartial 12 4610) = some ⟨12, 1, 0, 48867, 4610, 1, 65536⟩ := by
  decide +kernel

theorem context_12_4610_48867 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4610 ⟨48867, by decide⟩ :=
  accepted_of_selected 12 4610 ⟨48867, by decide⟩ ⟨12, 1, 0, 48867, 4610, 1, 65536⟩
    (by decide) selected_cut_01328

theorem selected_cut_01329 : selected 7 ⟨48922, by decide⟩
    (prefixPartial 14 73776) = some ⟨14, 2, 0, 48922, 73776, 1125, 4096⟩ := by
  decide +kernel

theorem context_14_73776_48922 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 73776 ⟨48922, by decide⟩ :=
  accepted_of_selected 14 73776 ⟨48922, by decide⟩ ⟨14, 2, 0, 48922, 73776, 1125, 4096⟩
    (by decide) selected_cut_01329

theorem selected_cut_01330 : selected 7 ⟨48955, by decide⟩
    (prefixPartial 14 73777) = some ⟨14, 2, 0, 48955, 73777, 1713, 4096⟩ := by
  decide +kernel

theorem context_14_73777_48955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 73777 ⟨48955, by decide⟩ :=
  accepted_of_selected 14 73777 ⟨48955, by decide⟩ ⟨14, 2, 0, 48955, 73777, 1713, 4096⟩
    (by decide) selected_cut_01330

theorem selected_cut_01331 : selected 7 ⟨48995, by decide⟩
    (prefixPartial 14 73778) = some ⟨14, 2, 0, 48995, 73778, 1641, 4096⟩ := by
  decide +kernel

theorem context_14_73778_48995 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 73778 ⟨48995, by decide⟩ :=
  accepted_of_selected 14 73778 ⟨48995, by decide⟩ ⟨14, 2, 0, 48995, 73778, 1641, 4096⟩
    (by decide) selected_cut_01331

theorem selected_cut_01332 : selected 7 ⟨49033, by decide⟩
    (prefixPartial 14 73779) = some ⟨14, 2, 0, 49033, 73779, 1473, 4096⟩ := by
  decide +kernel

theorem context_14_73779_49033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 73779 ⟨49033, by decide⟩ :=
  accepted_of_selected 14 73779 ⟨49033, by decide⟩ ⟨14, 2, 0, 49033, 73779, 1473, 4096⟩
    (by decide) selected_cut_01332

theorem unmarked_context_13_18444_49034 : frontier 8 ⟨49034, by decide⟩
    (prefixCache 13 18444) (prefixPartial 13 18444) = false := by
  decide +kernel

theorem node_context_13_18444_49034 : EJMOriginalGlobalDAGData.nodes 8 ⟨49034, by decide⟩ =
    .split (coordinate 13) (![⟨48922, by decide⟩,⟨48955, by decide⟩,⟨48995, by decide⟩,⟨49033, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_18444_49034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18444 ⟨49034, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 18444
    ⟨49034, by decide⟩ (by decide) (![⟨48922, by decide⟩,⟨48955, by decide⟩,⟨48995, by decide⟩,⟨49033, by decide⟩]) unmarked_context_13_18444_49034 node_context_13_18444_49034
  intro a
  fin_cases a
  · exact context_14_73776_48922
  · exact context_14_73777_48955
  · exact context_14_73778_48995
  · exact context_14_73779_49033

theorem selected_cut_01333 : selected 8 ⟨49153, by decide⟩
    (prefixPartial 13 18445) = some ⟨13, 2, 0, 49153, 18445, 3017, 16384⟩ := by
  decide +kernel

theorem context_13_18445_49153 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18445 ⟨49153, by decide⟩ :=
  accepted_of_selected 13 18445 ⟨49153, by decide⟩ ⟨13, 2, 0, 49153, 18445, 3017, 16384⟩
    (by decide) selected_cut_01333

theorem selected_cut_01334 : selected 8 ⟨49225, by decide⟩
    (prefixPartial 13 18446) = some ⟨13, 2, 0, 49225, 18446, 977, 16384⟩ := by
  decide +kernel

theorem context_13_18446_49225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18446 ⟨49225, by decide⟩ :=
  accepted_of_selected 13 18446 ⟨49225, by decide⟩ ⟨13, 2, 0, 49225, 18446, 977, 16384⟩
    (by decide) selected_cut_01334

theorem selected_cut_01335 : selected 8 ⟨49252, by decide⟩
    (prefixPartial 13 18447) = some ⟨13, 2, 0, 49252, 18447, 193, 16384⟩ := by
  decide +kernel

theorem context_13_18447_49252 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18447 ⟨49252, by decide⟩ :=
  accepted_of_selected 13 18447 ⟨49252, by decide⟩ ⟨13, 2, 0, 49252, 18447, 193, 16384⟩
    (by decide) selected_cut_01335

theorem unmarked_context_12_4611_49253 : frontier 9 ⟨49253, by decide⟩
    (prefixCache 12 4611) (prefixPartial 12 4611) = false := by
  decide +kernel

theorem node_context_12_4611_49253 : EJMOriginalGlobalDAGData.nodes 9 ⟨49253, by decide⟩ =
    .split (coordinate 12) (![⟨49034, by decide⟩,⟨49153, by decide⟩,⟨49225, by decide⟩,⟨49252, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4611_49253 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4611 ⟨49253, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4611
    ⟨49253, by decide⟩ (by decide) (![⟨49034, by decide⟩,⟨49153, by decide⟩,⟨49225, by decide⟩,⟨49252, by decide⟩]) unmarked_context_12_4611_49253 node_context_12_4611_49253
  intro a
  fin_cases a
  · exact context_13_18444_49034
  · exact context_13_18445_49153
  · exact context_13_18446_49225
  · exact context_13_18447_49252

theorem unmarked_context_11_1152_49254 : frontier 10 ⟨49254, by decide⟩
    (prefixCache 11 1152) (prefixPartial 11 1152) = false := by
  decide +kernel

theorem node_context_11_1152_49254 : EJMOriginalGlobalDAGData.nodes 10 ⟨49254, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨48866, by decide⟩,⟨48867, by decide⟩,⟨49253, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1152_49254 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1152 ⟨49254, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1152
    ⟨49254, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨48866, by decide⟩,⟨48867, by decide⟩,⟨49253, by decide⟩]) unmarked_context_11_1152_49254 node_context_11_1152_49254
  intro a
  fin_cases a
  · exact context_12_4608_34034
  · exact context_12_4609_48866
  · exact context_12_4610_48867
  · exact context_12_4611_49253

theorem selected_cut_01336 : selected 7 ⟨49291, by decide⟩
    (prefixPartial 14 73792) = some ⟨14, 2, 0, 49291, 73792, 1713, 4096⟩ := by
  decide +kernel

theorem context_14_73792_49291 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 73792 ⟨49291, by decide⟩ :=
  accepted_of_selected 14 73792 ⟨49291, by decide⟩ ⟨14, 2, 0, 49291, 73792, 1713, 4096⟩
    (by decide) selected_cut_01336

theorem selected_cut_01337 : selected 7 ⟨49306, by decide⟩
    (prefixPartial 14 73793) = some ⟨14, 2, 0, 49306, 73793, 661, 4096⟩ := by
  decide +kernel

theorem context_14_73793_49306 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 73793 ⟨49306, by decide⟩ :=
  accepted_of_selected 14 73793 ⟨49306, by decide⟩ ⟨14, 2, 0, 49306, 73793, 661, 4096⟩
    (by decide) selected_cut_01337

theorem selected_cut_01338 : selected 7 ⟨49325, by decide⟩
    (prefixPartial 14 73794) = some ⟨14, 2, 0, 49325, 73794, 941, 4096⟩ := by
  decide +kernel

theorem context_14_73794_49325 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 73794 ⟨49325, by decide⟩ :=
  accepted_of_selected 14 73794 ⟨49325, by decide⟩ ⟨14, 2, 0, 49325, 73794, 941, 4096⟩
    (by decide) selected_cut_01338

theorem selected_cut_01339 : selected 7 ⟨49343, by decide⟩
    (prefixPartial 14 73795) = some ⟨14, 2, 0, 49343, 73795, 989, 4096⟩ := by
  decide +kernel

theorem context_14_73795_49343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 73795 ⟨49343, by decide⟩ :=
  accepted_of_selected 14 73795 ⟨49343, by decide⟩ ⟨14, 2, 0, 49343, 73795, 989, 4096⟩
    (by decide) selected_cut_01339

theorem unmarked_context_13_18448_49344 : frontier 8 ⟨49344, by decide⟩
    (prefixCache 13 18448) (prefixPartial 13 18448) = false := by
  decide +kernel

theorem node_context_13_18448_49344 : EJMOriginalGlobalDAGData.nodes 8 ⟨49344, by decide⟩ =
    .split (coordinate 13) (![⟨49291, by decide⟩,⟨49306, by decide⟩,⟨49325, by decide⟩,⟨49343, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_18448_49344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18448 ⟨49344, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 18448
    ⟨49344, by decide⟩ (by decide) (![⟨49291, by decide⟩,⟨49306, by decide⟩,⟨49325, by decide⟩,⟨49343, by decide⟩]) unmarked_context_13_18448_49344 node_context_13_18448_49344
  intro a
  fin_cases a
  · exact context_14_73792_49291
  · exact context_14_73793_49306
  · exact context_14_73794_49325
  · exact context_14_73795_49343

theorem selected_cut_01340 : selected 7 ⟨49388, by decide⟩
    (prefixPartial 14 73796) = some ⟨14, 2, 0, 49388, 73796, 2217, 4096⟩ := by
  decide +kernel

theorem context_14_73796_49388 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 73796 ⟨49388, by decide⟩ :=
  accepted_of_selected 14 73796 ⟨49388, by decide⟩ ⟨14, 2, 0, 49388, 73796, 2217, 4096⟩
    (by decide) selected_cut_01340

theorem selected_cut_01341 : selected 7 ⟨49416, by decide⟩
    (prefixPartial 14 73797) = some ⟨14, 2, 0, 49416, 73797, 1301, 4096⟩ := by
  decide +kernel

theorem context_14_73797_49416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 73797 ⟨49416, by decide⟩ :=
  accepted_of_selected 14 73797 ⟨49416, by decide⟩ ⟨14, 2, 0, 49416, 73797, 1301, 4096⟩
    (by decide) selected_cut_01341

theorem selected_cut_01342 : selected 7 ⟨49445, by decide⟩
    (prefixPartial 14 73798) = some ⟨14, 2, 0, 49445, 73798, 1241, 4096⟩ := by
  decide +kernel

theorem context_14_73798_49445 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 73798 ⟨49445, by decide⟩ :=
  accepted_of_selected 14 73798 ⟨49445, by decide⟩ ⟨14, 2, 0, 49445, 73798, 1241, 4096⟩
    (by decide) selected_cut_01342

theorem selected_cut_01343 : selected 7 ⟨49470, by decide⟩
    (prefixPartial 14 73799) = some ⟨14, 2, 0, 49470, 73799, 1281, 4096⟩ := by
  decide +kernel

theorem context_14_73799_49470 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 73799 ⟨49470, by decide⟩ :=
  accepted_of_selected 14 73799 ⟨49470, by decide⟩ ⟨14, 2, 0, 49470, 73799, 1281, 4096⟩
    (by decide) selected_cut_01343

theorem unmarked_context_13_18449_49471 : frontier 8 ⟨49471, by decide⟩
    (prefixCache 13 18449) (prefixPartial 13 18449) = false := by
  decide +kernel

theorem node_context_13_18449_49471 : EJMOriginalGlobalDAGData.nodes 8 ⟨49471, by decide⟩ =
    .split (coordinate 13) (![⟨49388, by decide⟩,⟨49416, by decide⟩,⟨49445, by decide⟩,⟨49470, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_18449_49471 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18449 ⟨49471, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 18449
    ⟨49471, by decide⟩ (by decide) (![⟨49388, by decide⟩,⟨49416, by decide⟩,⟨49445, by decide⟩,⟨49470, by decide⟩]) unmarked_context_13_18449_49471 node_context_13_18449_49471
  intro a
  fin_cases a
  · exact context_14_73796_49388
  · exact context_14_73797_49416
  · exact context_14_73798_49445
  · exact context_14_73799_49470

theorem selected_cut_01344 : selected 8 ⟨49556, by decide⟩
    (prefixPartial 13 18450) = some ⟨13, 2, 0, 49556, 18450, 3157, 16384⟩ := by
  decide +kernel

theorem context_13_18450_49556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18450 ⟨49556, by decide⟩ :=
  accepted_of_selected 13 18450 ⟨49556, by decide⟩ ⟨13, 2, 0, 49556, 18450, 3157, 16384⟩
    (by decide) selected_cut_01344

theorem selected_cut_01345 : selected 8 ⟨49587, by decide⟩
    (prefixPartial 13 18451) = some ⟨13, 2, 0, 49587, 18451, 1493, 16384⟩ := by
  decide +kernel

theorem context_13_18451_49587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 18451 ⟨49587, by decide⟩ :=
  accepted_of_selected 13 18451 ⟨49587, by decide⟩ ⟨13, 2, 0, 49587, 18451, 1493, 16384⟩
    (by decide) selected_cut_01345

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
