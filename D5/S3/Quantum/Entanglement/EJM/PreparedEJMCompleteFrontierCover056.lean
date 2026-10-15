/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover055
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_05378 : selected 11 ⟨145424, by decide⟩
    (prefixPartial 10 1208) = some ⟨10, 1, 0, 145424, 1208, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_1208_145424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1208 ⟨145424, by decide⟩ :=
  accepted_of_selected 10 1208 ⟨145424, by decide⟩ ⟨10, 1, 0, 145424, 1208, 1, 1048576⟩
    (by decide) selected_cut_05378

theorem selected_cut_05379 : selected 10 ⟨167105, by decide⟩
    (prefixPartial 11 4836) = some ⟨11, 2, 0, 167105, 4836, 3425, 262144⟩ := by
  decide +kernel

theorem context_11_4836_167105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4836 ⟨167105, by decide⟩ :=
  accepted_of_selected 11 4836 ⟨167105, by decide⟩ ⟨11, 2, 0, 167105, 4836, 3425, 262144⟩
    (by decide) selected_cut_05379

theorem selected_cut_05380 : selected 10 ⟨167168, by decide⟩
    (prefixPartial 11 4837) = some ⟨11, 2, 0, 167168, 4837, 2289, 262144⟩ := by
  decide +kernel

theorem context_11_4837_167168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4837 ⟨167168, by decide⟩ :=
  accepted_of_selected 11 4837 ⟨167168, by decide⟩ ⟨11, 2, 0, 167168, 4837, 2289, 262144⟩
    (by decide) selected_cut_05380

theorem selected_cut_05381 : selected 10 ⟨167201, by decide⟩
    (prefixPartial 11 4838) = some ⟨11, 2, 0, 167201, 4838, 1245, 262144⟩ := by
  decide +kernel

theorem context_11_4838_167201 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4838 ⟨167201, by decide⟩ :=
  accepted_of_selected 11 4838 ⟨167201, by decide⟩ ⟨11, 2, 0, 167201, 4838, 1245, 262144⟩
    (by decide) selected_cut_05381

theorem selected_cut_05382 : selected 10 ⟨167216, by decide⟩
    (prefixPartial 11 4839) = some ⟨11, 2, 0, 167216, 4839, 537, 262144⟩ := by
  decide +kernel

theorem context_11_4839_167216 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4839 ⟨167216, by decide⟩ :=
  accepted_of_selected 11 4839 ⟨167216, by decide⟩ ⟨11, 2, 0, 167216, 4839, 537, 262144⟩
    (by decide) selected_cut_05382

theorem unmarked_context_10_1209_167217 : frontier 11 ⟨167217, by decide⟩
    (prefixCache 10 1209) (prefixPartial 10 1209) = false := by
  decide +kernel

theorem node_context_10_1209_167217 : EJMOriginalGlobalDAGData.nodes 11 ⟨167217, by decide⟩ =
    .split (coordinate 10) (![⟨167105, by decide⟩,⟨167168, by decide⟩,⟨167201, by decide⟩,⟨167216, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1209_167217 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1209 ⟨167217, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1209
    ⟨167217, by decide⟩ (by decide) (![⟨167105, by decide⟩,⟨167168, by decide⟩,⟨167201, by decide⟩,⟨167216, by decide⟩]) unmarked_context_10_1209_167217 node_context_10_1209_167217
  intro a
  fin_cases a
  · exact context_11_4836_167105
  · exact context_11_4837_167168
  · exact context_11_4838_167201
  · exact context_11_4839_167216

theorem selected_cut_05383 : selected 11 ⟨145424, by decide⟩
    (prefixPartial 10 1210) = some ⟨10, 1, 0, 145424, 1210, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_1210_145424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1210 ⟨145424, by decide⟩ :=
  accepted_of_selected 10 1210 ⟨145424, by decide⟩ ⟨10, 1, 0, 145424, 1210, 1, 1048576⟩
    (by decide) selected_cut_05383

theorem selected_cut_05384 : selected 10 ⟨167271, by decide⟩
    (prefixPartial 11 4844) = some ⟨11, 2, 0, 167271, 4844, 2361, 262144⟩ := by
  decide +kernel

theorem context_11_4844_167271 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4844 ⟨167271, by decide⟩ :=
  accepted_of_selected 11 4844 ⟨167271, by decide⟩ ⟨11, 2, 0, 167271, 4844, 2361, 262144⟩
    (by decide) selected_cut_05384

theorem selected_cut_05385 : selected 10 ⟨167321, by decide⟩
    (prefixPartial 11 4845) = some ⟨11, 2, 0, 167321, 4845, 2093, 262144⟩ := by
  decide +kernel

theorem context_11_4845_167321 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4845 ⟨167321, by decide⟩ :=
  accepted_of_selected 11 4845 ⟨167321, by decide⟩ ⟨11, 2, 0, 167321, 4845, 2093, 262144⟩
    (by decide) selected_cut_05385

theorem selected_cut_05386 : selected 10 ⟨167363, by decide⟩
    (prefixPartial 11 4846) = some ⟨11, 2, 0, 167363, 4846, 1553, 262144⟩ := by
  decide +kernel

theorem context_11_4846_167363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4846 ⟨167363, by decide⟩ :=
  accepted_of_selected 11 4846 ⟨167363, by decide⟩ ⟨11, 2, 0, 167363, 4846, 1553, 262144⟩
    (by decide) selected_cut_05386

theorem selected_cut_05387 : selected 10 ⟨167399, by decide⟩
    (prefixPartial 11 4847) = some ⟨11, 2, 0, 167399, 4847, 1089, 262144⟩ := by
  decide +kernel

theorem context_11_4847_167399 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4847 ⟨167399, by decide⟩ :=
  accepted_of_selected 11 4847 ⟨167399, by decide⟩ ⟨11, 2, 0, 167399, 4847, 1089, 262144⟩
    (by decide) selected_cut_05387

theorem unmarked_context_10_1211_167400 : frontier 11 ⟨167400, by decide⟩
    (prefixCache 10 1211) (prefixPartial 10 1211) = false := by
  decide +kernel

theorem node_context_10_1211_167400 : EJMOriginalGlobalDAGData.nodes 11 ⟨167400, by decide⟩ =
    .split (coordinate 10) (![⟨167271, by decide⟩,⟨167321, by decide⟩,⟨167363, by decide⟩,⟨167399, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1211_167400 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1211 ⟨167400, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1211
    ⟨167400, by decide⟩ (by decide) (![⟨167271, by decide⟩,⟨167321, by decide⟩,⟨167363, by decide⟩,⟨167399, by decide⟩]) unmarked_context_10_1211_167400 node_context_10_1211_167400
  intro a
  fin_cases a
  · exact context_11_4844_167271
  · exact context_11_4845_167321
  · exact context_11_4846_167363
  · exact context_11_4847_167399

theorem unmarked_context_9_302_167401 : frontier 12 ⟨167401, by decide⟩
    (prefixCache 9 302) (prefixPartial 9 302) = false := by
  decide +kernel

theorem node_context_9_302_167401 : EJMOriginalGlobalDAGData.nodes 12 ⟨167401, by decide⟩ =
    .split (coordinate 9) (![⟨145424, by decide⟩,⟨167217, by decide⟩,⟨145424, by decide⟩,⟨167400, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_302_167401 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 302 ⟨167401, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 302
    ⟨167401, by decide⟩ (by decide) (![⟨145424, by decide⟩,⟨167217, by decide⟩,⟨145424, by decide⟩,⟨167400, by decide⟩]) unmarked_context_9_302_167401 node_context_9_302_167401
  intro a
  fin_cases a
  · exact context_10_1208_145424
  · exact context_10_1209_167217
  · exact context_10_1210_145424
  · exact context_10_1211_167400

theorem selected_cut_05388 : selected 12 ⟨167444, by decide⟩
    (prefixPartial 9 303) = some ⟨9, 2, 0, 167444, 303, 821, 4194304⟩ := by
  decide +kernel

theorem context_9_303_167444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 303 ⟨167444, by decide⟩ :=
  accepted_of_selected 9 303 ⟨167444, by decide⟩ ⟨9, 2, 0, 167444, 303, 821, 4194304⟩
    (by decide) selected_cut_05388

theorem unmarked_context_8_75_167445 : frontier 13 ⟨167445, by decide⟩
    (prefixCache 8 75) (prefixPartial 8 75) = false := by
  decide +kernel

theorem node_context_8_75_167445 : EJMOriginalGlobalDAGData.nodes 13 ⟨167445, by decide⟩ =
    .split (coordinate 8) (![⟨164475, by decide⟩,⟨167005, by decide⟩,⟨167401, by decide⟩,⟨167444, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_75_167445 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 75 ⟨167445, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 75
    ⟨167445, by decide⟩ (by decide) (![⟨164475, by decide⟩,⟨167005, by decide⟩,⟨167401, by decide⟩,⟨167444, by decide⟩]) unmarked_context_8_75_167445 node_context_8_75_167445
  intro a
  fin_cases a
  · exact context_9_300_164475
  · exact context_9_301_167005
  · exact context_9_302_167401
  · exact context_9_303_167444

theorem unmarked_context_7_18_167446 : frontier 14 ⟨167446, by decide⟩
    (prefixCache 7 18) (prefixPartial 7 18) = false := by
  decide +kernel

theorem node_context_7_18_167446 : EJMOriginalGlobalDAGData.nodes 14 ⟨167446, by decide⟩ =
    .split (coordinate 7) (![⟨146806, by decide⟩,⟨158378, by decide⟩,⟨158379, by decide⟩,⟨167445, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_18_167446 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 18 ⟨167446, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 18
    ⟨167446, by decide⟩ (by decide) (![⟨146806, by decide⟩,⟨158378, by decide⟩,⟨158379, by decide⟩,⟨167445, by decide⟩]) unmarked_context_7_18_167446 node_context_7_18_167446
  intro a
  fin_cases a
  · exact context_8_72_146806
  · exact context_8_73_158378
  · exact context_8_74_158379
  · exact context_8_75_167445

theorem selected_cut_05389 : selected 14 ⟨34032, by decide⟩
    (prefixPartial 7 19) = some ⟨7, 1, 0, 34032, 19, 1, 67108864⟩ := by
  decide +kernel

theorem context_7_19_34032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 19 ⟨34032, by decide⟩ :=
  accepted_of_selected 7 19 ⟨34032, by decide⟩ ⟨7, 1, 0, 34032, 19, 1, 67108864⟩
    (by decide) selected_cut_05389

theorem unmarked_context_6_4_167447 : frontier 15 ⟨167447, by decide⟩
    (prefixCache 6 4) (prefixPartial 6 4) = false := by
  decide +kernel

theorem node_context_6_4_167447 : EJMOriginalGlobalDAGData.nodes 15 ⟨167447, by decide⟩ =
    .split (coordinate 6) (![⟨116316, by decide⟩,⟨136006, by decide⟩,⟨167446, by decide⟩,⟨34032, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_6_4_167447 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 4 ⟨167447, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 6 4
    ⟨167447, by decide⟩ (by decide) (![⟨116316, by decide⟩,⟨136006, by decide⟩,⟨167446, by decide⟩,⟨34032, by decide⟩]) unmarked_context_6_4_167447 node_context_6_4_167447
  intro a
  fin_cases a
  · exact context_7_16_116316
  · exact context_7_17_136006
  · exact context_7_18_167446
  · exact context_7_19_34032

theorem selected_cut_05390 : selected 10 ⟨167448, by decide⟩
    (prefixPartial 11 5120) = some ⟨11, 1, 0, 167448, 5120, 1, 262144⟩ := by
  decide +kernel

theorem context_11_5120_167448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5120 ⟨167448, by decide⟩ :=
  accepted_of_selected 11 5120 ⟨167448, by decide⟩ ⟨11, 1, 0, 167448, 5120, 1, 262144⟩
    (by decide) selected_cut_05390

theorem selected_cut_05391 : selected 9 ⟨167528, by decide⟩
    (prefixPartial 12 20484) = some ⟨12, 2, 0, 167528, 20484, 3217, 65536⟩ := by
  decide +kernel

theorem context_12_20484_167528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20484 ⟨167528, by decide⟩ :=
  accepted_of_selected 12 20484 ⟨167528, by decide⟩ ⟨12, 2, 0, 167528, 20484, 3217, 65536⟩
    (by decide) selected_cut_05391

theorem selected_cut_05392 : selected 9 ⟨167598, by decide⟩
    (prefixPartial 12 20485) = some ⟨12, 2, 0, 167598, 20485, 3349, 65536⟩ := by
  decide +kernel

theorem context_12_20485_167598 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20485 ⟨167598, by decide⟩ :=
  accepted_of_selected 12 20485 ⟨167598, by decide⟩ ⟨12, 2, 0, 167598, 20485, 3349, 65536⟩
    (by decide) selected_cut_05392

theorem selected_cut_05393 : selected 8 ⟨167651, by decide⟩
    (prefixPartial 13 81944) = some ⟨13, 2, 0, 167651, 81944, 2085, 16384⟩ := by
  decide +kernel

theorem context_13_81944_167651 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 81944 ⟨167651, by decide⟩ :=
  accepted_of_selected 13 81944 ⟨167651, by decide⟩ ⟨13, 2, 0, 167651, 81944, 2085, 16384⟩
    (by decide) selected_cut_05393

theorem selected_cut_05394 : selected 8 ⟨167689, by decide⟩
    (prefixPartial 13 81945) = some ⟨13, 2, 0, 167689, 81945, 2933, 16384⟩ := by
  decide +kernel

theorem context_13_81945_167689 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 81945 ⟨167689, by decide⟩ :=
  accepted_of_selected 13 81945 ⟨167689, by decide⟩ ⟨13, 2, 0, 167689, 81945, 2933, 16384⟩
    (by decide) selected_cut_05394

theorem selected_cut_05395 : selected 8 ⟨167711, by decide⟩
    (prefixPartial 13 81946) = some ⟨13, 2, 0, 167711, 81946, 1761, 16384⟩ := by
  decide +kernel

theorem context_13_81946_167711 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 81946 ⟨167711, by decide⟩ :=
  accepted_of_selected 13 81946 ⟨167711, by decide⟩ ⟨13, 2, 0, 167711, 81946, 1761, 16384⟩
    (by decide) selected_cut_05395

theorem selected_cut_05396 : selected 8 ⟨167721, by decide⟩
    (prefixPartial 13 81947) = some ⟨13, 2, 0, 167721, 81947, 685, 16384⟩ := by
  decide +kernel

theorem context_13_81947_167721 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 81947 ⟨167721, by decide⟩ :=
  accepted_of_selected 13 81947 ⟨167721, by decide⟩ ⟨13, 2, 0, 167721, 81947, 685, 16384⟩
    (by decide) selected_cut_05396

theorem unmarked_context_12_20486_167722 : frontier 9 ⟨167722, by decide⟩
    (prefixCache 12 20486) (prefixPartial 12 20486) = false := by
  decide +kernel

theorem node_context_12_20486_167722 : EJMOriginalGlobalDAGData.nodes 9 ⟨167722, by decide⟩ =
    .split (coordinate 12) (![⟨167651, by decide⟩,⟨167689, by decide⟩,⟨167711, by decide⟩,⟨167721, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_20486_167722 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20486 ⟨167722, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 20486
    ⟨167722, by decide⟩ (by decide) (![⟨167651, by decide⟩,⟨167689, by decide⟩,⟨167711, by decide⟩,⟨167721, by decide⟩]) unmarked_context_12_20486_167722 node_context_12_20486_167722
  intro a
  fin_cases a
  · exact context_13_81944_167651
  · exact context_13_81945_167689
  · exact context_13_81946_167711
  · exact context_13_81947_167721

theorem selected_cut_05397 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 20487) = some ⟨12, 1, 0, 893, 20487, 1, 65536⟩ := by
  decide +kernel

theorem context_12_20487_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20487 ⟨893, by decide⟩ :=
  accepted_of_selected 12 20487 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 20487, 1, 65536⟩
    (by decide) selected_cut_05397

theorem unmarked_context_11_5121_167723 : frontier 10 ⟨167723, by decide⟩
    (prefixCache 11 5121) (prefixPartial 11 5121) = false := by
  decide +kernel

theorem node_context_11_5121_167723 : EJMOriginalGlobalDAGData.nodes 10 ⟨167723, by decide⟩ =
    .split (coordinate 11) (![⟨167528, by decide⟩,⟨167598, by decide⟩,⟨167722, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5121_167723 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5121 ⟨167723, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5121
    ⟨167723, by decide⟩ (by decide) (![⟨167528, by decide⟩,⟨167598, by decide⟩,⟨167722, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_5121_167723 node_context_11_5121_167723
  intro a
  fin_cases a
  · exact context_12_20484_167528
  · exact context_12_20485_167598
  · exact context_12_20486_167722
  · exact context_12_20487_893

theorem selected_cut_05398 : selected 8 ⟨167761, by decide⟩
    (prefixPartial 13 81952) = some ⟨13, 2, 0, 167761, 81952, 1529, 16384⟩ := by
  decide +kernel

theorem context_13_81952_167761 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 81952 ⟨167761, by decide⟩ :=
  accepted_of_selected 13 81952 ⟨167761, by decide⟩ ⟨13, 2, 0, 167761, 81952, 1529, 16384⟩
    (by decide) selected_cut_05398

theorem selected_cut_05399 : selected 8 ⟨167789, by decide⟩
    (prefixPartial 13 81953) = some ⟨13, 2, 0, 167789, 81953, 2417, 16384⟩ := by
  decide +kernel

theorem context_13_81953_167789 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 81953 ⟨167789, by decide⟩ :=
  accepted_of_selected 13 81953 ⟨167789, by decide⟩ ⟨13, 2, 0, 167789, 81953, 2417, 16384⟩
    (by decide) selected_cut_05399

theorem selected_cut_05400 : selected 8 ⟨167807, by decide⟩
    (prefixPartial 13 81954) = some ⟨13, 2, 0, 167807, 81954, 1449, 16384⟩ := by
  decide +kernel

theorem context_13_81954_167807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 81954 ⟨167807, by decide⟩ :=
  accepted_of_selected 13 81954 ⟨167807, by decide⟩ ⟨13, 2, 0, 167807, 81954, 1449, 16384⟩
    (by decide) selected_cut_05400

theorem selected_cut_05401 : selected 8 ⟨167817, by decide⟩
    (prefixPartial 13 81955) = some ⟨13, 2, 0, 167817, 81955, 661, 16384⟩ := by
  decide +kernel

theorem context_13_81955_167817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 81955 ⟨167817, by decide⟩ :=
  accepted_of_selected 13 81955 ⟨167817, by decide⟩ ⟨13, 2, 0, 167817, 81955, 661, 16384⟩
    (by decide) selected_cut_05401

theorem unmarked_context_12_20488_167818 : frontier 9 ⟨167818, by decide⟩
    (prefixCache 12 20488) (prefixPartial 12 20488) = false := by
  decide +kernel

theorem node_context_12_20488_167818 : EJMOriginalGlobalDAGData.nodes 9 ⟨167818, by decide⟩ =
    .split (coordinate 12) (![⟨167761, by decide⟩,⟨167789, by decide⟩,⟨167807, by decide⟩,⟨167817, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_20488_167818 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20488 ⟨167818, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 20488
    ⟨167818, by decide⟩ (by decide) (![⟨167761, by decide⟩,⟨167789, by decide⟩,⟨167807, by decide⟩,⟨167817, by decide⟩]) unmarked_context_12_20488_167818 node_context_12_20488_167818
  intro a
  fin_cases a
  · exact context_13_81952_167761
  · exact context_13_81953_167789
  · exact context_13_81954_167807
  · exact context_13_81955_167817

theorem selected_cut_05402 : selected 8 ⟨167858, by decide⟩
    (prefixPartial 13 81956) = some ⟨13, 2, 0, 167858, 81956, 1705, 16384⟩ := by
  decide +kernel

theorem context_13_81956_167858 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 81956 ⟨167858, by decide⟩ :=
  accepted_of_selected 13 81956 ⟨167858, by decide⟩ ⟨13, 2, 0, 167858, 81956, 1705, 16384⟩
    (by decide) selected_cut_05402

theorem selected_cut_05403 : selected 8 ⟨167903, by decide⟩
    (prefixPartial 13 81957) = some ⟨13, 2, 0, 167903, 81957, 3061, 16384⟩ := by
  decide +kernel

theorem context_13_81957_167903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 81957 ⟨167903, by decide⟩ :=
  accepted_of_selected 13 81957 ⟨167903, by decide⟩ ⟨13, 2, 0, 167903, 81957, 3061, 16384⟩
    (by decide) selected_cut_05403

theorem selected_cut_05404 : selected 8 ⟨167929, by decide⟩
    (prefixPartial 13 81958) = some ⟨13, 2, 0, 167929, 81958, 1829, 16384⟩ := by
  decide +kernel

theorem context_13_81958_167929 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 81958 ⟨167929, by decide⟩ :=
  accepted_of_selected 13 81958 ⟨167929, by decide⟩ ⟨13, 2, 0, 167929, 81958, 1829, 16384⟩
    (by decide) selected_cut_05404

theorem selected_cut_05405 : selected 8 ⟨167942, by decide⟩
    (prefixPartial 13 81959) = some ⟨13, 2, 0, 167942, 81959, 897, 16384⟩ := by
  decide +kernel

theorem context_13_81959_167942 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 81959 ⟨167942, by decide⟩ :=
  accepted_of_selected 13 81959 ⟨167942, by decide⟩ ⟨13, 2, 0, 167942, 81959, 897, 16384⟩
    (by decide) selected_cut_05405

theorem unmarked_context_12_20489_167943 : frontier 9 ⟨167943, by decide⟩
    (prefixCache 12 20489) (prefixPartial 12 20489) = false := by
  decide +kernel

theorem node_context_12_20489_167943 : EJMOriginalGlobalDAGData.nodes 9 ⟨167943, by decide⟩ =
    .split (coordinate 12) (![⟨167858, by decide⟩,⟨167903, by decide⟩,⟨167929, by decide⟩,⟨167942, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_20489_167943 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20489 ⟨167943, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 20489
    ⟨167943, by decide⟩ (by decide) (![⟨167858, by decide⟩,⟨167903, by decide⟩,⟨167929, by decide⟩,⟨167942, by decide⟩]) unmarked_context_12_20489_167943 node_context_12_20489_167943
  intro a
  fin_cases a
  · exact context_13_81956_167858
  · exact context_13_81957_167903
  · exact context_13_81958_167929
  · exact context_13_81959_167942

theorem selected_cut_05406 : selected 8 ⟨167982, by decide⟩
    (prefixPartial 13 81960) = some ⟨13, 2, 0, 167982, 81960, 1945, 16384⟩ := by
  decide +kernel

theorem context_13_81960_167982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 81960 ⟨167982, by decide⟩ :=
  accepted_of_selected 13 81960 ⟨167982, by decide⟩ ⟨13, 2, 0, 167982, 81960, 1945, 16384⟩
    (by decide) selected_cut_05406

theorem selected_cut_05407 : selected 8 ⟨168033, by decide⟩
    (prefixPartial 13 81961) = some ⟨13, 2, 0, 168033, 81961, 3385, 16384⟩ := by
  decide +kernel

theorem context_13_81961_168033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 81961 ⟨168033, by decide⟩ :=
  accepted_of_selected 13 81961 ⟨168033, by decide⟩ ⟨13, 2, 0, 168033, 81961, 3385, 16384⟩
    (by decide) selected_cut_05407

theorem selected_cut_05408 : selected 8 ⟨168058, by decide⟩
    (prefixPartial 13 81962) = some ⟨13, 2, 0, 168058, 81962, 1721, 16384⟩ := by
  decide +kernel

theorem context_13_81962_168058 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 81962 ⟨168058, by decide⟩ :=
  accepted_of_selected 13 81962 ⟨168058, by decide⟩ ⟨13, 2, 0, 168058, 81962, 1721, 16384⟩
    (by decide) selected_cut_05408

theorem selected_cut_05409 : selected 8 ⟨168067, by decide⟩
    (prefixPartial 13 81963) = some ⟨13, 2, 0, 168067, 81963, 829, 16384⟩ := by
  decide +kernel

theorem context_13_81963_168067 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 81963 ⟨168067, by decide⟩ :=
  accepted_of_selected 13 81963 ⟨168067, by decide⟩ ⟨13, 2, 0, 168067, 81963, 829, 16384⟩
    (by decide) selected_cut_05409

theorem unmarked_context_12_20490_168068 : frontier 9 ⟨168068, by decide⟩
    (prefixCache 12 20490) (prefixPartial 12 20490) = false := by
  decide +kernel

theorem node_context_12_20490_168068 : EJMOriginalGlobalDAGData.nodes 9 ⟨168068, by decide⟩ =
    .split (coordinate 12) (![⟨167982, by decide⟩,⟨168033, by decide⟩,⟨168058, by decide⟩,⟨168067, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_20490_168068 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20490 ⟨168068, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 20490
    ⟨168068, by decide⟩ (by decide) (![⟨167982, by decide⟩,⟨168033, by decide⟩,⟨168058, by decide⟩,⟨168067, by decide⟩]) unmarked_context_12_20490_168068 node_context_12_20490_168068
  intro a
  fin_cases a
  · exact context_13_81960_167982
  · exact context_13_81961_168033
  · exact context_13_81962_168058
  · exact context_13_81963_168067

theorem selected_cut_05410 : selected 8 ⟨168110, by decide⟩
    (prefixPartial 13 81964) = some ⟨13, 2, 0, 168110, 81964, 1929, 16384⟩ := by
  decide +kernel

theorem context_13_81964_168110 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 81964 ⟨168110, by decide⟩ :=
  accepted_of_selected 13 81964 ⟨168110, by decide⟩ ⟨13, 2, 0, 168110, 81964, 1929, 16384⟩
    (by decide) selected_cut_05410

theorem selected_cut_05411 : selected 8 ⟨168157, by decide⟩
    (prefixPartial 13 81965) = some ⟨13, 2, 0, 168157, 81965, 3457, 16384⟩ := by
  decide +kernel

theorem context_13_81965_168157 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 81965 ⟨168157, by decide⟩ :=
  accepted_of_selected 13 81965 ⟨168157, by decide⟩ ⟨13, 2, 0, 168157, 81965, 3457, 16384⟩
    (by decide) selected_cut_05411

theorem selected_cut_05412 : selected 8 ⟨168180, by decide⟩
    (prefixPartial 13 81966) = some ⟨13, 2, 0, 168180, 81966, 1761, 16384⟩ := by
  decide +kernel

theorem context_13_81966_168180 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 81966 ⟨168180, by decide⟩ :=
  accepted_of_selected 13 81966 ⟨168180, by decide⟩ ⟨13, 2, 0, 168180, 81966, 1761, 16384⟩
    (by decide) selected_cut_05412

theorem selected_cut_05413 : selected 8 ⟨168191, by decide⟩
    (prefixPartial 13 81967) = some ⟨13, 2, 0, 168191, 81967, 981, 16384⟩ := by
  decide +kernel

theorem context_13_81967_168191 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 81967 ⟨168191, by decide⟩ :=
  accepted_of_selected 13 81967 ⟨168191, by decide⟩ ⟨13, 2, 0, 168191, 81967, 981, 16384⟩
    (by decide) selected_cut_05413

theorem unmarked_context_12_20491_168192 : frontier 9 ⟨168192, by decide⟩
    (prefixCache 12 20491) (prefixPartial 12 20491) = false := by
  decide +kernel

theorem node_context_12_20491_168192 : EJMOriginalGlobalDAGData.nodes 9 ⟨168192, by decide⟩ =
    .split (coordinate 12) (![⟨168110, by decide⟩,⟨168157, by decide⟩,⟨168180, by decide⟩,⟨168191, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_20491_168192 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20491 ⟨168192, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 20491
    ⟨168192, by decide⟩ (by decide) (![⟨168110, by decide⟩,⟨168157, by decide⟩,⟨168180, by decide⟩,⟨168191, by decide⟩]) unmarked_context_12_20491_168192 node_context_12_20491_168192
  intro a
  fin_cases a
  · exact context_13_81964_168110
  · exact context_13_81965_168157
  · exact context_13_81966_168180
  · exact context_13_81967_168191

theorem unmarked_context_11_5122_168193 : frontier 10 ⟨168193, by decide⟩
    (prefixCache 11 5122) (prefixPartial 11 5122) = false := by
  decide +kernel

theorem node_context_11_5122_168193 : EJMOriginalGlobalDAGData.nodes 10 ⟨168193, by decide⟩ =
    .split (coordinate 11) (![⟨167818, by decide⟩,⟨167943, by decide⟩,⟨168068, by decide⟩,⟨168192, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5122_168193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5122 ⟨168193, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5122
    ⟨168193, by decide⟩ (by decide) (![⟨167818, by decide⟩,⟨167943, by decide⟩,⟨168068, by decide⟩,⟨168192, by decide⟩]) unmarked_context_11_5122_168193 node_context_11_5122_168193
  intro a
  fin_cases a
  · exact context_12_20488_167818
  · exact context_12_20489_167943
  · exact context_12_20490_168068
  · exact context_12_20491_168192

theorem selected_cut_05414 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 5123) = some ⟨11, 1, 0, 1736, 5123, 1, 262144⟩ := by
  decide +kernel

theorem context_11_5123_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5123 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 5123 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 5123, 1, 262144⟩
    (by decide) selected_cut_05414

theorem unmarked_context_10_1280_168194 : frontier 11 ⟨168194, by decide⟩
    (prefixCache 10 1280) (prefixPartial 10 1280) = false := by
  decide +kernel

theorem node_context_10_1280_168194 : EJMOriginalGlobalDAGData.nodes 11 ⟨168194, by decide⟩ =
    .split (coordinate 10) (![⟨167448, by decide⟩,⟨167723, by decide⟩,⟨168193, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1280_168194 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1280 ⟨168194, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1280
    ⟨168194, by decide⟩ (by decide) (![⟨167448, by decide⟩,⟨167723, by decide⟩,⟨168193, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_1280_168194 node_context_10_1280_168194
  intro a
  fin_cases a
  · exact context_11_5120_167448
  · exact context_11_5121_167723
  · exact context_11_5122_168193
  · exact context_11_5123_1736

theorem selected_cut_05415 : selected 9 ⟨168257, by decide⟩
    (prefixPartial 12 20496) = some ⟨12, 2, 0, 168257, 20496, 1817, 65536⟩ := by
  decide +kernel

theorem context_12_20496_168257 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20496 ⟨168257, by decide⟩ :=
  accepted_of_selected 12 20496 ⟨168257, by decide⟩ ⟨12, 2, 0, 168257, 20496, 1817, 65536⟩
    (by decide) selected_cut_05415

theorem selected_cut_05416 : selected 9 ⟨168299, by decide⟩
    (prefixPartial 12 20497) = some ⟨12, 2, 0, 168299, 20497, 1565, 65536⟩ := by
  decide +kernel

theorem context_12_20497_168299 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20497 ⟨168299, by decide⟩ :=
  accepted_of_selected 12 20497 ⟨168299, by decide⟩ ⟨12, 2, 0, 168299, 20497, 1565, 65536⟩
    (by decide) selected_cut_05416

theorem selected_cut_05417 : selected 9 ⟨168358, by decide⟩
    (prefixPartial 12 20498) = some ⟨12, 2, 0, 168358, 20498, 3313, 65536⟩ := by
  decide +kernel

theorem context_12_20498_168358 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20498 ⟨168358, by decide⟩ :=
  accepted_of_selected 12 20498 ⟨168358, by decide⟩ ⟨12, 2, 0, 168358, 20498, 3313, 65536⟩
    (by decide) selected_cut_05417

theorem selected_cut_05418 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 20499) = some ⟨12, 1, 0, 893, 20499, 1, 65536⟩ := by
  decide +kernel

theorem context_12_20499_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20499 ⟨893, by decide⟩ :=
  accepted_of_selected 12 20499 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 20499, 1, 65536⟩
    (by decide) selected_cut_05418

theorem unmarked_context_11_5124_168359 : frontier 10 ⟨168359, by decide⟩
    (prefixCache 11 5124) (prefixPartial 11 5124) = false := by
  decide +kernel

theorem node_context_11_5124_168359 : EJMOriginalGlobalDAGData.nodes 10 ⟨168359, by decide⟩ =
    .split (coordinate 11) (![⟨168257, by decide⟩,⟨168299, by decide⟩,⟨168358, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5124_168359 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5124 ⟨168359, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5124
    ⟨168359, by decide⟩ (by decide) (![⟨168257, by decide⟩,⟨168299, by decide⟩,⟨168358, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_5124_168359 node_context_11_5124_168359
  intro a
  fin_cases a
  · exact context_12_20496_168257
  · exact context_12_20497_168299
  · exact context_12_20498_168358
  · exact context_12_20499_893

theorem selected_cut_05419 : selected 9 ⟨168402, by decide⟩
    (prefixPartial 12 20500) = some ⟨12, 2, 0, 168402, 20500, 1933, 65536⟩ := by
  decide +kernel

theorem context_12_20500_168402 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20500 ⟨168402, by decide⟩ :=
  accepted_of_selected 12 20500 ⟨168402, by decide⟩ ⟨12, 2, 0, 168402, 20500, 1933, 65536⟩
    (by decide) selected_cut_05419

theorem selected_cut_05420 : selected 9 ⟨168451, by decide⟩
    (prefixPartial 12 20501) = some ⟨12, 2, 0, 168451, 20501, 1969, 65536⟩ := by
  decide +kernel

theorem context_12_20501_168451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20501 ⟨168451, by decide⟩ :=
  accepted_of_selected 12 20501 ⟨168451, by decide⟩ ⟨12, 2, 0, 168451, 20501, 1969, 65536⟩
    (by decide) selected_cut_05420

theorem selected_cut_05421 : selected 8 ⟨168468, by decide⟩
    (prefixPartial 13 82008) = some ⟨13, 2, 0, 168468, 82008, 873, 16384⟩ := by
  decide +kernel

theorem context_13_82008_168468 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82008 ⟨168468, by decide⟩ :=
  accepted_of_selected 13 82008 ⟨168468, by decide⟩ ⟨13, 2, 0, 168468, 82008, 873, 16384⟩
    (by decide) selected_cut_05421

theorem selected_cut_05422 : selected 8 ⟨168499, by decide⟩
    (prefixPartial 13 82009) = some ⟨13, 2, 0, 168499, 82009, 1649, 16384⟩ := by
  decide +kernel

theorem context_13_82009_168499 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82009 ⟨168499, by decide⟩ :=
  accepted_of_selected 13 82009 ⟨168499, by decide⟩ ⟨13, 2, 0, 168499, 82009, 1649, 16384⟩
    (by decide) selected_cut_05422

theorem selected_cut_05423 : selected 8 ⟨168518, by decide⟩
    (prefixPartial 13 82010) = some ⟨13, 2, 0, 168518, 82010, 1181, 16384⟩ := by
  decide +kernel

theorem context_13_82010_168518 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82010 ⟨168518, by decide⟩ :=
  accepted_of_selected 13 82010 ⟨168518, by decide⟩ ⟨13, 2, 0, 168518, 82010, 1181, 16384⟩
    (by decide) selected_cut_05423

theorem selected_cut_05424 : selected 8 ⟨168521, by decide⟩
    (prefixPartial 13 82011) = some ⟨13, 2, 0, 168521, 82011, 605, 16384⟩ := by
  decide +kernel

theorem context_13_82011_168521 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82011 ⟨168521, by decide⟩ :=
  accepted_of_selected 13 82011 ⟨168521, by decide⟩ ⟨13, 2, 0, 168521, 82011, 605, 16384⟩
    (by decide) selected_cut_05424

theorem unmarked_context_12_20502_168522 : frontier 9 ⟨168522, by decide⟩
    (prefixCache 12 20502) (prefixPartial 12 20502) = false := by
  decide +kernel

theorem node_context_12_20502_168522 : EJMOriginalGlobalDAGData.nodes 9 ⟨168522, by decide⟩ =
    .split (coordinate 12) (![⟨168468, by decide⟩,⟨168499, by decide⟩,⟨168518, by decide⟩,⟨168521, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_20502_168522 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20502 ⟨168522, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 20502
    ⟨168522, by decide⟩ (by decide) (![⟨168468, by decide⟩,⟨168499, by decide⟩,⟨168518, by decide⟩,⟨168521, by decide⟩]) unmarked_context_12_20502_168522 node_context_12_20502_168522
  intro a
  fin_cases a
  · exact context_13_82008_168468
  · exact context_13_82009_168499
  · exact context_13_82010_168518
  · exact context_13_82011_168521

theorem selected_cut_05425 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 20503) = some ⟨12, 1, 0, 893, 20503, 1, 65536⟩ := by
  decide +kernel

theorem context_12_20503_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20503 ⟨893, by decide⟩ :=
  accepted_of_selected 12 20503 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 20503, 1, 65536⟩
    (by decide) selected_cut_05425

theorem unmarked_context_11_5125_168523 : frontier 10 ⟨168523, by decide⟩
    (prefixCache 11 5125) (prefixPartial 11 5125) = false := by
  decide +kernel

theorem node_context_11_5125_168523 : EJMOriginalGlobalDAGData.nodes 10 ⟨168523, by decide⟩ =
    .split (coordinate 11) (![⟨168402, by decide⟩,⟨168451, by decide⟩,⟨168522, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5125_168523 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5125 ⟨168523, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5125
    ⟨168523, by decide⟩ (by decide) (![⟨168402, by decide⟩,⟨168451, by decide⟩,⟨168522, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_5125_168523 node_context_11_5125_168523
  intro a
  fin_cases a
  · exact context_12_20500_168402
  · exact context_12_20501_168451
  · exact context_12_20502_168522
  · exact context_12_20503_893

theorem selected_cut_05426 : selected 9 ⟨168592, by decide⟩
    (prefixPartial 12 20504) = some ⟨12, 2, 0, 168592, 20504, 3833, 65536⟩ := by
  decide +kernel

theorem context_12_20504_168592 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20504 ⟨168592, by decide⟩ :=
  accepted_of_selected 12 20504 ⟨168592, by decide⟩ ⟨12, 2, 0, 168592, 20504, 3833, 65536⟩
    (by decide) selected_cut_05426

theorem selected_cut_05427 : selected 8 ⟨168609, by decide⟩
    (prefixPartial 13 82020) = some ⟨13, 2, 0, 168609, 82020, 833, 16384⟩ := by
  decide +kernel

theorem context_13_82020_168609 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82020 ⟨168609, by decide⟩ :=
  accepted_of_selected 13 82020 ⟨168609, by decide⟩ ⟨13, 2, 0, 168609, 82020, 833, 16384⟩
    (by decide) selected_cut_05427

theorem selected_cut_05428 : selected 8 ⟨168634, by decide⟩
    (prefixPartial 13 82021) = some ⟨13, 2, 0, 168634, 82021, 1573, 16384⟩ := by
  decide +kernel

theorem context_13_82021_168634 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82021 ⟨168634, by decide⟩ :=
  accepted_of_selected 13 82021 ⟨168634, by decide⟩ ⟨13, 2, 0, 168634, 82021, 1573, 16384⟩
    (by decide) selected_cut_05428

theorem selected_cut_05429 : selected 8 ⟨168655, by decide⟩
    (prefixPartial 13 82022) = some ⟨13, 2, 0, 168655, 82022, 1317, 16384⟩ := by
  decide +kernel

theorem context_13_82022_168655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82022 ⟨168655, by decide⟩ :=
  accepted_of_selected 13 82022 ⟨168655, by decide⟩ ⟨13, 2, 0, 168655, 82022, 1317, 16384⟩
    (by decide) selected_cut_05429

theorem selected_cut_05430 : selected 8 ⟨168666, by decide⟩
    (prefixPartial 13 82023) = some ⟨13, 2, 0, 168666, 82023, 685, 16384⟩ := by
  decide +kernel

theorem context_13_82023_168666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82023 ⟨168666, by decide⟩ :=
  accepted_of_selected 13 82023 ⟨168666, by decide⟩ ⟨13, 2, 0, 168666, 82023, 685, 16384⟩
    (by decide) selected_cut_05430

theorem unmarked_context_12_20505_168667 : frontier 9 ⟨168667, by decide⟩
    (prefixCache 12 20505) (prefixPartial 12 20505) = false := by
  decide +kernel

theorem node_context_12_20505_168667 : EJMOriginalGlobalDAGData.nodes 9 ⟨168667, by decide⟩ =
    .split (coordinate 12) (![⟨168609, by decide⟩,⟨168634, by decide⟩,⟨168655, by decide⟩,⟨168666, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_20505_168667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20505 ⟨168667, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 20505
    ⟨168667, by decide⟩ (by decide) (![⟨168609, by decide⟩,⟨168634, by decide⟩,⟨168655, by decide⟩,⟨168666, by decide⟩]) unmarked_context_12_20505_168667 node_context_12_20505_168667
  intro a
  fin_cases a
  · exact context_13_82020_168609
  · exact context_13_82021_168634
  · exact context_13_82022_168655
  · exact context_13_82023_168666

theorem selected_cut_05431 : selected 8 ⟨168686, by decide⟩
    (prefixPartial 13 82024) = some ⟨13, 2, 0, 168686, 82024, 1005, 16384⟩ := by
  decide +kernel

theorem context_13_82024_168686 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82024 ⟨168686, by decide⟩ :=
  accepted_of_selected 13 82024 ⟨168686, by decide⟩ ⟨13, 2, 0, 168686, 82024, 1005, 16384⟩
    (by decide) selected_cut_05431

theorem selected_cut_05432 : selected 8 ⟨168724, by decide⟩
    (prefixPartial 13 82025) = some ⟨13, 2, 0, 168724, 82025, 1925, 16384⟩ := by
  decide +kernel

theorem context_13_82025_168724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82025 ⟨168724, by decide⟩ :=
  accepted_of_selected 13 82025 ⟨168724, by decide⟩ ⟨13, 2, 0, 168724, 82025, 1925, 16384⟩
    (by decide) selected_cut_05432

theorem selected_cut_05433 : selected 8 ⟨168742, by decide⟩
    (prefixPartial 13 82026) = some ⟨13, 2, 0, 168742, 82026, 1161, 16384⟩ := by
  decide +kernel

theorem context_13_82026_168742 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82026 ⟨168742, by decide⟩ :=
  accepted_of_selected 13 82026 ⟨168742, by decide⟩ ⟨13, 2, 0, 168742, 82026, 1161, 16384⟩
    (by decide) selected_cut_05433

theorem selected_cut_05434 : selected 8 ⟨168749, by decide⟩
    (prefixPartial 13 82027) = some ⟨13, 2, 0, 168749, 82027, 673, 16384⟩ := by
  decide +kernel

theorem context_13_82027_168749 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82027 ⟨168749, by decide⟩ :=
  accepted_of_selected 13 82027 ⟨168749, by decide⟩ ⟨13, 2, 0, 168749, 82027, 673, 16384⟩
    (by decide) selected_cut_05434

theorem unmarked_context_12_20506_168750 : frontier 9 ⟨168750, by decide⟩
    (prefixCache 12 20506) (prefixPartial 12 20506) = false := by
  decide +kernel

theorem node_context_12_20506_168750 : EJMOriginalGlobalDAGData.nodes 9 ⟨168750, by decide⟩ =
    .split (coordinate 12) (![⟨168686, by decide⟩,⟨168724, by decide⟩,⟨168742, by decide⟩,⟨168749, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_20506_168750 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20506 ⟨168750, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 20506
    ⟨168750, by decide⟩ (by decide) (![⟨168686, by decide⟩,⟨168724, by decide⟩,⟨168742, by decide⟩,⟨168749, by decide⟩]) unmarked_context_12_20506_168750 node_context_12_20506_168750
  intro a
  fin_cases a
  · exact context_13_82024_168686
  · exact context_13_82025_168724
  · exact context_13_82026_168742
  · exact context_13_82027_168749

theorem selected_cut_05435 : selected 8 ⟨168766, by decide⟩
    (prefixPartial 13 82028) = some ⟨13, 2, 0, 168766, 82028, 965, 16384⟩ := by
  decide +kernel

theorem context_13_82028_168766 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82028 ⟨168766, by decide⟩ :=
  accepted_of_selected 13 82028 ⟨168766, by decide⟩ ⟨13, 2, 0, 168766, 82028, 965, 16384⟩
    (by decide) selected_cut_05435

theorem selected_cut_05436 : selected 8 ⟨168799, by decide⟩
    (prefixPartial 13 82029) = some ⟨13, 2, 0, 168799, 82029, 1985, 16384⟩ := by
  decide +kernel

theorem context_13_82029_168799 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82029 ⟨168799, by decide⟩ :=
  accepted_of_selected 13 82029 ⟨168799, by decide⟩ ⟨13, 2, 0, 168799, 82029, 1985, 16384⟩
    (by decide) selected_cut_05436

theorem selected_cut_05437 : selected 8 ⟨168823, by decide⟩
    (prefixPartial 13 82030) = some ⟨13, 2, 0, 168823, 82030, 1313, 16384⟩ := by
  decide +kernel

theorem context_13_82030_168823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82030 ⟨168823, by decide⟩ :=
  accepted_of_selected 13 82030 ⟨168823, by decide⟩ ⟨13, 2, 0, 168823, 82030, 1313, 16384⟩
    (by decide) selected_cut_05437

theorem selected_cut_05438 : selected 8 ⟨168832, by decide⟩
    (prefixPartial 13 82031) = some ⟨13, 2, 0, 168832, 82031, 741, 16384⟩ := by
  decide +kernel

theorem context_13_82031_168832 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82031 ⟨168832, by decide⟩ :=
  accepted_of_selected 13 82031 ⟨168832, by decide⟩ ⟨13, 2, 0, 168832, 82031, 741, 16384⟩
    (by decide) selected_cut_05438

theorem unmarked_context_12_20507_168833 : frontier 9 ⟨168833, by decide⟩
    (prefixCache 12 20507) (prefixPartial 12 20507) = false := by
  decide +kernel

theorem node_context_12_20507_168833 : EJMOriginalGlobalDAGData.nodes 9 ⟨168833, by decide⟩ =
    .split (coordinate 12) (![⟨168766, by decide⟩,⟨168799, by decide⟩,⟨168823, by decide⟩,⟨168832, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_20507_168833 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20507 ⟨168833, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 20507
    ⟨168833, by decide⟩ (by decide) (![⟨168766, by decide⟩,⟨168799, by decide⟩,⟨168823, by decide⟩,⟨168832, by decide⟩]) unmarked_context_12_20507_168833 node_context_12_20507_168833
  intro a
  fin_cases a
  · exact context_13_82028_168766
  · exact context_13_82029_168799
  · exact context_13_82030_168823
  · exact context_13_82031_168832

theorem unmarked_context_11_5126_168834 : frontier 10 ⟨168834, by decide⟩
    (prefixCache 11 5126) (prefixPartial 11 5126) = false := by
  decide +kernel

theorem node_context_11_5126_168834 : EJMOriginalGlobalDAGData.nodes 10 ⟨168834, by decide⟩ =
    .split (coordinate 11) (![⟨168592, by decide⟩,⟨168667, by decide⟩,⟨168750, by decide⟩,⟨168833, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5126_168834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5126 ⟨168834, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5126
    ⟨168834, by decide⟩ (by decide) (![⟨168592, by decide⟩,⟨168667, by decide⟩,⟨168750, by decide⟩,⟨168833, by decide⟩]) unmarked_context_11_5126_168834 node_context_11_5126_168834
  intro a
  fin_cases a
  · exact context_12_20504_168592
  · exact context_12_20505_168667
  · exact context_12_20506_168750
  · exact context_12_20507_168833

theorem selected_cut_05439 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 5127) = some ⟨11, 1, 0, 1736, 5127, 1, 262144⟩ := by
  decide +kernel

theorem context_11_5127_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5127 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 5127 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 5127, 1, 262144⟩
    (by decide) selected_cut_05439

theorem unmarked_context_10_1281_168835 : frontier 11 ⟨168835, by decide⟩
    (prefixCache 10 1281) (prefixPartial 10 1281) = false := by
  decide +kernel

theorem node_context_10_1281_168835 : EJMOriginalGlobalDAGData.nodes 11 ⟨168835, by decide⟩ =
    .split (coordinate 10) (![⟨168359, by decide⟩,⟨168523, by decide⟩,⟨168834, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1281_168835 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1281 ⟨168835, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1281
    ⟨168835, by decide⟩ (by decide) (![⟨168359, by decide⟩,⟨168523, by decide⟩,⟨168834, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_1281_168835 node_context_10_1281_168835
  intro a
  fin_cases a
  · exact context_11_5124_168359
  · exact context_11_5125_168523
  · exact context_11_5126_168834
  · exact context_11_5127_1736

theorem selected_cut_05440 : selected 8 ⟨168850, by decide⟩
    (prefixPartial 13 82048) = some ⟨13, 2, 0, 168850, 82048, 849, 16384⟩ := by
  decide +kernel

theorem context_13_82048_168850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82048 ⟨168850, by decide⟩ :=
  accepted_of_selected 13 82048 ⟨168850, by decide⟩ ⟨13, 2, 0, 168850, 82048, 849, 16384⟩
    (by decide) selected_cut_05440

theorem selected_cut_05441 : selected 8 ⟨168877, by decide⟩
    (prefixPartial 13 82049) = some ⟨13, 2, 0, 168877, 82049, 2049, 16384⟩ := by
  decide +kernel

theorem context_13_82049_168877 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82049 ⟨168877, by decide⟩ :=
  accepted_of_selected 13 82049 ⟨168877, by decide⟩ ⟨13, 2, 0, 168877, 82049, 2049, 16384⟩
    (by decide) selected_cut_05441

theorem selected_cut_05442 : selected 8 ⟨168901, by decide⟩
    (prefixPartial 13 82050) = some ⟨13, 2, 0, 168901, 82050, 1301, 16384⟩ := by
  decide +kernel

theorem context_13_82050_168901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82050 ⟨168901, by decide⟩ :=
  accepted_of_selected 13 82050 ⟨168901, by decide⟩ ⟨13, 2, 0, 168901, 82050, 1301, 16384⟩
    (by decide) selected_cut_05442

theorem selected_cut_05443 : selected 8 ⟨168910, by decide⟩
    (prefixPartial 13 82051) = some ⟨13, 2, 0, 168910, 82051, 849, 16384⟩ := by
  decide +kernel

theorem context_13_82051_168910 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82051 ⟨168910, by decide⟩ :=
  accepted_of_selected 13 82051 ⟨168910, by decide⟩ ⟨13, 2, 0, 168910, 82051, 849, 16384⟩
    (by decide) selected_cut_05443

theorem unmarked_context_12_20512_168911 : frontier 9 ⟨168911, by decide⟩
    (prefixCache 12 20512) (prefixPartial 12 20512) = false := by
  decide +kernel

theorem node_context_12_20512_168911 : EJMOriginalGlobalDAGData.nodes 9 ⟨168911, by decide⟩ =
    .split (coordinate 12) (![⟨168850, by decide⟩,⟨168877, by decide⟩,⟨168901, by decide⟩,⟨168910, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_20512_168911 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20512 ⟨168911, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 20512
    ⟨168911, by decide⟩ (by decide) (![⟨168850, by decide⟩,⟨168877, by decide⟩,⟨168901, by decide⟩,⟨168910, by decide⟩]) unmarked_context_12_20512_168911 node_context_12_20512_168911
  intro a
  fin_cases a
  · exact context_13_82048_168850
  · exact context_13_82049_168877
  · exact context_13_82050_168901
  · exact context_13_82051_168910

theorem selected_cut_05444 : selected 9 ⟨168954, by decide⟩
    (prefixPartial 12 20513) = some ⟨12, 2, 0, 168954, 20513, 2613, 65536⟩ := by
  decide +kernel

theorem context_12_20513_168954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20513 ⟨168954, by decide⟩ :=
  accepted_of_selected 12 20513 ⟨168954, by decide⟩ ⟨12, 2, 0, 168954, 20513, 2613, 65536⟩
    (by decide) selected_cut_05444

theorem selected_cut_05445 : selected 9 ⟨169007, by decide⟩
    (prefixPartial 12 20514) = some ⟨12, 2, 0, 169007, 20514, 3249, 65536⟩ := by
  decide +kernel

theorem context_12_20514_169007 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20514 ⟨169007, by decide⟩ :=
  accepted_of_selected 12 20514 ⟨169007, by decide⟩ ⟨12, 2, 0, 169007, 20514, 3249, 65536⟩
    (by decide) selected_cut_05445

theorem selected_cut_05446 : selected 9 ⟨169053, by decide⟩
    (prefixPartial 12 20515) = some ⟨12, 2, 0, 169053, 20515, 2945, 65536⟩ := by
  decide +kernel

theorem context_12_20515_169053 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20515 ⟨169053, by decide⟩ :=
  accepted_of_selected 12 20515 ⟨169053, by decide⟩ ⟨12, 2, 0, 169053, 20515, 2945, 65536⟩
    (by decide) selected_cut_05446

theorem unmarked_context_11_5128_169054 : frontier 10 ⟨169054, by decide⟩
    (prefixCache 11 5128) (prefixPartial 11 5128) = false := by
  decide +kernel

theorem node_context_11_5128_169054 : EJMOriginalGlobalDAGData.nodes 10 ⟨169054, by decide⟩ =
    .split (coordinate 11) (![⟨168911, by decide⟩,⟨168954, by decide⟩,⟨169007, by decide⟩,⟨169053, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5128_169054 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5128 ⟨169054, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5128
    ⟨169054, by decide⟩ (by decide) (![⟨168911, by decide⟩,⟨168954, by decide⟩,⟨169007, by decide⟩,⟨169053, by decide⟩]) unmarked_context_11_5128_169054 node_context_11_5128_169054
  intro a
  fin_cases a
  · exact context_12_20512_168911
  · exact context_12_20513_168954
  · exact context_12_20514_169007
  · exact context_12_20515_169053

theorem selected_cut_05447 : selected 9 ⟨169115, by decide⟩
    (prefixPartial 12 20516) = some ⟨12, 2, 0, 169115, 20516, 3613, 65536⟩ := by
  decide +kernel

theorem context_12_20516_169115 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20516 ⟨169115, by decide⟩ :=
  accepted_of_selected 12 20516 ⟨169115, by decide⟩ ⟨12, 2, 0, 169115, 20516, 3613, 65536⟩
    (by decide) selected_cut_05447

theorem selected_cut_05448 : selected 9 ⟨169175, by decide⟩
    (prefixPartial 12 20517) = some ⟨12, 2, 0, 169175, 20517, 3473, 65536⟩ := by
  decide +kernel

theorem context_12_20517_169175 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20517 ⟨169175, by decide⟩ :=
  accepted_of_selected 12 20517 ⟨169175, by decide⟩ ⟨12, 2, 0, 169175, 20517, 3473, 65536⟩
    (by decide) selected_cut_05448

theorem selected_cut_05449 : selected 8 ⟨169186, by decide⟩
    (prefixPartial 13 82072) = some ⟨13, 2, 0, 169186, 82072, 521, 16384⟩ := by
  decide +kernel

theorem context_13_82072_169186 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82072 ⟨169186, by decide⟩ :=
  accepted_of_selected 13 82072 ⟨169186, by decide⟩ ⟨13, 2, 0, 169186, 82072, 521, 16384⟩
    (by decide) selected_cut_05449

theorem selected_cut_05450 : selected 8 ⟨169218, by decide⟩
    (prefixPartial 13 82073) = some ⟨13, 2, 0, 169218, 82073, 2121, 16384⟩ := by
  decide +kernel

theorem context_13_82073_169218 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82073 ⟨169218, by decide⟩ :=
  accepted_of_selected 13 82073 ⟨169218, by decide⟩ ⟨13, 2, 0, 169218, 82073, 2121, 16384⟩
    (by decide) selected_cut_05450

theorem selected_cut_05451 : selected 8 ⟨169235, by decide⟩
    (prefixPartial 13 82074) = some ⟨13, 2, 0, 169235, 82074, 1121, 16384⟩ := by
  decide +kernel

theorem context_13_82074_169235 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82074 ⟨169235, by decide⟩ :=
  accepted_of_selected 13 82074 ⟨169235, by decide⟩ ⟨13, 2, 0, 169235, 82074, 1121, 16384⟩
    (by decide) selected_cut_05451

theorem selected_cut_05452 : selected 8 ⟨169238, by decide⟩
    (prefixPartial 13 82075) = some ⟨13, 2, 0, 169238, 82075, 613, 16384⟩ := by
  decide +kernel

theorem context_13_82075_169238 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82075 ⟨169238, by decide⟩ :=
  accepted_of_selected 13 82075 ⟨169238, by decide⟩ ⟨13, 2, 0, 169238, 82075, 613, 16384⟩
    (by decide) selected_cut_05452

theorem unmarked_context_12_20518_169239 : frontier 9 ⟨169239, by decide⟩
    (prefixCache 12 20518) (prefixPartial 12 20518) = false := by
  decide +kernel

theorem node_context_12_20518_169239 : EJMOriginalGlobalDAGData.nodes 9 ⟨169239, by decide⟩ =
    .split (coordinate 12) (![⟨169186, by decide⟩,⟨169218, by decide⟩,⟨169235, by decide⟩,⟨169238, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_20518_169239 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20518 ⟨169239, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 20518
    ⟨169239, by decide⟩ (by decide) (![⟨169186, by decide⟩,⟨169218, by decide⟩,⟨169235, by decide⟩,⟨169238, by decide⟩]) unmarked_context_12_20518_169239 node_context_12_20518_169239
  intro a
  fin_cases a
  · exact context_13_82072_169186
  · exact context_13_82073_169218
  · exact context_13_82074_169235
  · exact context_13_82075_169238

theorem selected_cut_05453 : selected 9 ⟨169297, by decide⟩
    (prefixPartial 12 20519) = some ⟨12, 2, 0, 169297, 20519, 4085, 65536⟩ := by
  decide +kernel

theorem context_12_20519_169297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20519 ⟨169297, by decide⟩ :=
  accepted_of_selected 12 20519 ⟨169297, by decide⟩ ⟨12, 2, 0, 169297, 20519, 4085, 65536⟩
    (by decide) selected_cut_05453

theorem unmarked_context_11_5129_169298 : frontier 10 ⟨169298, by decide⟩
    (prefixCache 11 5129) (prefixPartial 11 5129) = false := by
  decide +kernel

theorem node_context_11_5129_169298 : EJMOriginalGlobalDAGData.nodes 10 ⟨169298, by decide⟩ =
    .split (coordinate 11) (![⟨169115, by decide⟩,⟨169175, by decide⟩,⟨169239, by decide⟩,⟨169297, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5129_169298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5129 ⟨169298, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5129
    ⟨169298, by decide⟩ (by decide) (![⟨169115, by decide⟩,⟨169175, by decide⟩,⟨169239, by decide⟩,⟨169297, by decide⟩]) unmarked_context_11_5129_169298 node_context_11_5129_169298
  intro a
  fin_cases a
  · exact context_12_20516_169115
  · exact context_12_20517_169175
  · exact context_12_20518_169239
  · exact context_12_20519_169297

theorem selected_cut_05454 : selected 9 ⟨169351, by decide⟩
    (prefixPartial 12 20520) = some ⟨12, 2, 0, 169351, 20520, 3349, 65536⟩ := by
  decide +kernel

theorem context_12_20520_169351 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20520 ⟨169351, by decide⟩ :=
  accepted_of_selected 12 20520 ⟨169351, by decide⟩ ⟨12, 2, 0, 169351, 20520, 3349, 65536⟩
    (by decide) selected_cut_05454

theorem selected_cut_05455 : selected 9 ⟨169416, by decide⟩
    (prefixPartial 12 20521) = some ⟨12, 2, 0, 169416, 20521, 3881, 65536⟩ := by
  decide +kernel

theorem context_12_20521_169416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20521 ⟨169416, by decide⟩ :=
  accepted_of_selected 12 20521 ⟨169416, by decide⟩ ⟨12, 2, 0, 169416, 20521, 3881, 65536⟩
    (by decide) selected_cut_05455

theorem selected_cut_05456 : selected 8 ⟨169424, by decide⟩
    (prefixPartial 13 82088) = some ⟨13, 2, 0, 169424, 82088, 353, 16384⟩ := by
  decide +kernel

theorem context_13_82088_169424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82088 ⟨169424, by decide⟩ :=
  accepted_of_selected 13 82088 ⟨169424, by decide⟩ ⟨13, 2, 0, 169424, 82088, 353, 16384⟩
    (by decide) selected_cut_05456

theorem selected_cut_05457 : selected 8 ⟨169456, by decide⟩
    (prefixPartial 13 82089) = some ⟨13, 2, 0, 169456, 82089, 2265, 16384⟩ := by
  decide +kernel

theorem context_13_82089_169456 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82089 ⟨169456, by decide⟩ :=
  accepted_of_selected 13 82089 ⟨169456, by decide⟩ ⟨13, 2, 0, 169456, 82089, 2265, 16384⟩
    (by decide) selected_cut_05457

theorem selected_cut_05458 : selected 8 ⟨169473, by decide⟩
    (prefixPartial 13 82090) = some ⟨13, 2, 0, 169473, 82090, 1061, 16384⟩ := by
  decide +kernel

theorem context_13_82090_169473 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82090 ⟨169473, by decide⟩ :=
  accepted_of_selected 13 82090 ⟨169473, by decide⟩ ⟨13, 2, 0, 169473, 82090, 1061, 16384⟩
    (by decide) selected_cut_05458

theorem selected_cut_05459 : selected 8 ⟨169479, by decide⟩
    (prefixPartial 13 82091) = some ⟨13, 2, 0, 169479, 82091, 673, 16384⟩ := by
  decide +kernel

theorem context_13_82091_169479 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82091 ⟨169479, by decide⟩ :=
  accepted_of_selected 13 82091 ⟨169479, by decide⟩ ⟨13, 2, 0, 169479, 82091, 673, 16384⟩
    (by decide) selected_cut_05459

theorem unmarked_context_12_20522_169480 : frontier 9 ⟨169480, by decide⟩
    (prefixCache 12 20522) (prefixPartial 12 20522) = false := by
  decide +kernel

theorem node_context_12_20522_169480 : EJMOriginalGlobalDAGData.nodes 9 ⟨169480, by decide⟩ =
    .split (coordinate 12) (![⟨169424, by decide⟩,⟨169456, by decide⟩,⟨169473, by decide⟩,⟨169479, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_20522_169480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20522 ⟨169480, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 20522
    ⟨169480, by decide⟩ (by decide) (![⟨169424, by decide⟩,⟨169456, by decide⟩,⟨169473, by decide⟩,⟨169479, by decide⟩]) unmarked_context_12_20522_169480 node_context_12_20522_169480
  intro a
  fin_cases a
  · exact context_13_82088_169424
  · exact context_13_82089_169456
  · exact context_13_82090_169473
  · exact context_13_82091_169479

theorem selected_cut_05460 : selected 8 ⟨169489, by decide⟩
    (prefixPartial 13 82092) = some ⟨13, 2, 0, 169489, 82092, 281, 16384⟩ := by
  decide +kernel

theorem context_13_82092_169489 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82092 ⟨169489, by decide⟩ :=
  accepted_of_selected 13 82092 ⟨169489, by decide⟩ ⟨13, 2, 0, 169489, 82092, 281, 16384⟩
    (by decide) selected_cut_05460

theorem selected_cut_05461 : selected 8 ⟨169528, by decide⟩
    (prefixPartial 13 82093) = some ⟨13, 2, 0, 169528, 82093, 2125, 16384⟩ := by
  decide +kernel

theorem context_13_82093_169528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82093 ⟨169528, by decide⟩ :=
  accepted_of_selected 13 82093 ⟨169528, by decide⟩ ⟨13, 2, 0, 169528, 82093, 2125, 16384⟩
    (by decide) selected_cut_05461

theorem selected_cut_05462 : selected 8 ⟨169542, by decide⟩
    (prefixPartial 13 82094) = some ⟨13, 2, 0, 169542, 82094, 1061, 16384⟩ := by
  decide +kernel

theorem context_13_82094_169542 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82094 ⟨169542, by decide⟩ :=
  accepted_of_selected 13 82094 ⟨169542, by decide⟩ ⟨13, 2, 0, 169542, 82094, 1061, 16384⟩
    (by decide) selected_cut_05462

theorem selected_cut_05463 : selected 8 ⟨169551, by decide⟩
    (prefixPartial 13 82095) = some ⟨13, 2, 0, 169551, 82095, 697, 16384⟩ := by
  decide +kernel

theorem context_13_82095_169551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82095 ⟨169551, by decide⟩ :=
  accepted_of_selected 13 82095 ⟨169551, by decide⟩ ⟨13, 2, 0, 169551, 82095, 697, 16384⟩
    (by decide) selected_cut_05463

theorem unmarked_context_12_20523_169552 : frontier 9 ⟨169552, by decide⟩
    (prefixCache 12 20523) (prefixPartial 12 20523) = false := by
  decide +kernel

theorem node_context_12_20523_169552 : EJMOriginalGlobalDAGData.nodes 9 ⟨169552, by decide⟩ =
    .split (coordinate 12) (![⟨169489, by decide⟩,⟨169528, by decide⟩,⟨169542, by decide⟩,⟨169551, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_20523_169552 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20523 ⟨169552, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 20523
    ⟨169552, by decide⟩ (by decide) (![⟨169489, by decide⟩,⟨169528, by decide⟩,⟨169542, by decide⟩,⟨169551, by decide⟩]) unmarked_context_12_20523_169552 node_context_12_20523_169552
  intro a
  fin_cases a
  · exact context_13_82092_169489
  · exact context_13_82093_169528
  · exact context_13_82094_169542
  · exact context_13_82095_169551

theorem unmarked_context_11_5130_169553 : frontier 10 ⟨169553, by decide⟩
    (prefixCache 11 5130) (prefixPartial 11 5130) = false := by
  decide +kernel

theorem node_context_11_5130_169553 : EJMOriginalGlobalDAGData.nodes 10 ⟨169553, by decide⟩ =
    .split (coordinate 11) (![⟨169351, by decide⟩,⟨169416, by decide⟩,⟨169480, by decide⟩,⟨169552, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5130_169553 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5130 ⟨169553, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5130
    ⟨169553, by decide⟩ (by decide) (![⟨169351, by decide⟩,⟨169416, by decide⟩,⟨169480, by decide⟩,⟨169552, by decide⟩]) unmarked_context_11_5130_169553 node_context_11_5130_169553
  intro a
  fin_cases a
  · exact context_12_20520_169351
  · exact context_12_20521_169416
  · exact context_12_20522_169480
  · exact context_12_20523_169552

theorem selected_cut_05464 : selected 9 ⟨169604, by decide⟩
    (prefixPartial 12 20524) = some ⟨12, 2, 0, 169604, 20524, 3269, 65536⟩ := by
  decide +kernel

theorem context_12_20524_169604 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20524 ⟨169604, by decide⟩ :=
  accepted_of_selected 12 20524 ⟨169604, by decide⟩ ⟨12, 2, 0, 169604, 20524, 3269, 65536⟩
    (by decide) selected_cut_05464

theorem selected_cut_05465 : selected 9 ⟨169659, by decide⟩
    (prefixPartial 12 20525) = some ⟨12, 2, 0, 169659, 20525, 3773, 65536⟩ := by
  decide +kernel

theorem context_12_20525_169659 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20525 ⟨169659, by decide⟩ :=
  accepted_of_selected 12 20525 ⟨169659, by decide⟩ ⟨12, 2, 0, 169659, 20525, 3773, 65536⟩
    (by decide) selected_cut_05465

theorem selected_cut_05466 : selected 8 ⟨169666, by decide⟩
    (prefixPartial 13 82104) = some ⟨13, 2, 0, 169666, 82104, 169, 16384⟩ := by
  decide +kernel

theorem context_13_82104_169666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82104 ⟨169666, by decide⟩ :=
  accepted_of_selected 13 82104 ⟨169666, by decide⟩ ⟨13, 2, 0, 169666, 82104, 169, 16384⟩
    (by decide) selected_cut_05466

theorem selected_cut_05467 : selected 8 ⟨169705, by decide⟩
    (prefixPartial 13 82105) = some ⟨13, 2, 0, 169705, 82105, 2333, 16384⟩ := by
  decide +kernel

theorem context_13_82105_169705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82105 ⟨169705, by decide⟩ :=
  accepted_of_selected 13 82105 ⟨169705, by decide⟩ ⟨13, 2, 0, 169705, 82105, 2333, 16384⟩
    (by decide) selected_cut_05467

theorem selected_cut_05468 : selected 8 ⟨169727, by decide⟩
    (prefixPartial 13 82106) = some ⟨13, 2, 0, 169727, 82106, 1301, 16384⟩ := by
  decide +kernel

theorem context_13_82106_169727 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82106 ⟨169727, by decide⟩ :=
  accepted_of_selected 13 82106 ⟨169727, by decide⟩ ⟨13, 2, 0, 169727, 82106, 1301, 16384⟩
    (by decide) selected_cut_05468

theorem selected_cut_05469 : selected 8 ⟨169732, by decide⟩
    (prefixPartial 13 82107) = some ⟨13, 2, 0, 169732, 82107, 693, 16384⟩ := by
  decide +kernel

theorem context_13_82107_169732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82107 ⟨169732, by decide⟩ :=
  accepted_of_selected 13 82107 ⟨169732, by decide⟩ ⟨13, 2, 0, 169732, 82107, 693, 16384⟩
    (by decide) selected_cut_05469

theorem unmarked_context_12_20526_169733 : frontier 9 ⟨169733, by decide⟩
    (prefixCache 12 20526) (prefixPartial 12 20526) = false := by
  decide +kernel

theorem node_context_12_20526_169733 : EJMOriginalGlobalDAGData.nodes 9 ⟨169733, by decide⟩ =
    .split (coordinate 12) (![⟨169666, by decide⟩,⟨169705, by decide⟩,⟨169727, by decide⟩,⟨169732, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_20526_169733 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20526 ⟨169733, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 20526
    ⟨169733, by decide⟩ (by decide) (![⟨169666, by decide⟩,⟨169705, by decide⟩,⟨169727, by decide⟩,⟨169732, by decide⟩]) unmarked_context_12_20526_169733 node_context_12_20526_169733
  intro a
  fin_cases a
  · exact context_13_82104_169666
  · exact context_13_82105_169705
  · exact context_13_82106_169727
  · exact context_13_82107_169732

theorem selected_cut_05470 : selected 9 ⟨169786, by decide⟩
    (prefixPartial 12 20527) = some ⟨12, 2, 0, 169786, 20527, 3857, 65536⟩ := by
  decide +kernel

theorem context_12_20527_169786 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20527 ⟨169786, by decide⟩ :=
  accepted_of_selected 12 20527 ⟨169786, by decide⟩ ⟨12, 2, 0, 169786, 20527, 3857, 65536⟩
    (by decide) selected_cut_05470

theorem unmarked_context_11_5131_169787 : frontier 10 ⟨169787, by decide⟩
    (prefixCache 11 5131) (prefixPartial 11 5131) = false := by
  decide +kernel

theorem node_context_11_5131_169787 : EJMOriginalGlobalDAGData.nodes 10 ⟨169787, by decide⟩ =
    .split (coordinate 11) (![⟨169604, by decide⟩,⟨169659, by decide⟩,⟨169733, by decide⟩,⟨169786, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5131_169787 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5131 ⟨169787, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5131
    ⟨169787, by decide⟩ (by decide) (![⟨169604, by decide⟩,⟨169659, by decide⟩,⟨169733, by decide⟩,⟨169786, by decide⟩]) unmarked_context_11_5131_169787 node_context_11_5131_169787
  intro a
  fin_cases a
  · exact context_12_20524_169604
  · exact context_12_20525_169659
  · exact context_12_20526_169733
  · exact context_12_20527_169786

theorem unmarked_context_10_1282_169788 : frontier 11 ⟨169788, by decide⟩
    (prefixCache 10 1282) (prefixPartial 10 1282) = false := by
  decide +kernel

theorem node_context_10_1282_169788 : EJMOriginalGlobalDAGData.nodes 11 ⟨169788, by decide⟩ =
    .split (coordinate 10) (![⟨169054, by decide⟩,⟨169298, by decide⟩,⟨169553, by decide⟩,⟨169787, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1282_169788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1282 ⟨169788, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1282
    ⟨169788, by decide⟩ (by decide) (![⟨169054, by decide⟩,⟨169298, by decide⟩,⟨169553, by decide⟩,⟨169787, by decide⟩]) unmarked_context_10_1282_169788 node_context_10_1282_169788
  intro a
  fin_cases a
  · exact context_11_5128_169054
  · exact context_11_5129_169298
  · exact context_11_5130_169553
  · exact context_11_5131_169787

theorem selected_cut_05471 : selected 11 ⟨3440, by decide⟩
    (prefixPartial 10 1283) = some ⟨10, 1, 0, 3440, 1283, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_1283_3440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1283 ⟨3440, by decide⟩ :=
  accepted_of_selected 10 1283 ⟨3440, by decide⟩ ⟨10, 1, 0, 3440, 1283, 1, 1048576⟩
    (by decide) selected_cut_05471

theorem unmarked_context_9_320_169789 : frontier 12 ⟨169789, by decide⟩
    (prefixCache 9 320) (prefixPartial 9 320) = false := by
  decide +kernel

theorem node_context_9_320_169789 : EJMOriginalGlobalDAGData.nodes 12 ⟨169789, by decide⟩ =
    .split (coordinate 9) (![⟨168194, by decide⟩,⟨168835, by decide⟩,⟨169788, by decide⟩,⟨3440, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_320_169789 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 320 ⟨169789, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 320
    ⟨169789, by decide⟩ (by decide) (![⟨168194, by decide⟩,⟨168835, by decide⟩,⟨169788, by decide⟩,⟨3440, by decide⟩]) unmarked_context_9_320_169789 node_context_9_320_169789
  intro a
  fin_cases a
  · exact context_10_1280_168194
  · exact context_10_1281_168835
  · exact context_10_1282_169788
  · exact context_10_1283_3440

theorem selected_cut_05472 : selected 9 ⟨169790, by decide⟩
    (prefixPartial 12 20544) = some ⟨12, 1, 0, 169790, 20544, 1, 65536⟩ := by
  decide +kernel

theorem context_12_20544_169790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20544 ⟨169790, by decide⟩ :=
  accepted_of_selected 12 20544 ⟨169790, by decide⟩ ⟨12, 1, 0, 169790, 20544, 1, 65536⟩
    (by decide) selected_cut_05472

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
