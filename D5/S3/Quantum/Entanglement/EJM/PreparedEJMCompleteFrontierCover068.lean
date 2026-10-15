/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover067
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_06530 : selected 9 ⟨194911, by decide⟩
    (prefixPartial 12 21650) = some ⟨12, 2, 0, 194911, 21650, 1961, 65536⟩ := by
  decide +kernel

theorem context_12_21650_194911 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21650 ⟨194911, by decide⟩ :=
  accepted_of_selected 12 21650 ⟨194911, by decide⟩ ⟨12, 2, 0, 194911, 21650, 1961, 65536⟩
    (by decide) selected_cut_06530

theorem selected_cut_06531 : selected 9 ⟨194945, by decide⟩
    (prefixPartial 12 21651) = some ⟨12, 2, 0, 194945, 21651, 1981, 65536⟩ := by
  decide +kernel

theorem context_12_21651_194945 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21651 ⟨194945, by decide⟩ :=
  accepted_of_selected 12 21651 ⟨194945, by decide⟩ ⟨12, 2, 0, 194945, 21651, 1981, 65536⟩
    (by decide) selected_cut_06531

theorem unmarked_context_11_5412_194946 : frontier 10 ⟨194946, by decide⟩
    (prefixCache 11 5412) (prefixPartial 11 5412) = false := by
  decide +kernel

theorem node_context_11_5412_194946 : EJMOriginalGlobalDAGData.nodes 10 ⟨194946, by decide⟩ =
    .split (coordinate 11) (![⟨194844, by decide⟩,⟨194875, by decide⟩,⟨194911, by decide⟩,⟨194945, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5412_194946 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5412 ⟨194946, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5412
    ⟨194946, by decide⟩ (by decide) (![⟨194844, by decide⟩,⟨194875, by decide⟩,⟨194911, by decide⟩,⟨194945, by decide⟩]) unmarked_context_11_5412_194946 node_context_11_5412_194946
  intro a
  fin_cases a
  · exact context_12_21648_194844
  · exact context_12_21649_194875
  · exact context_12_21650_194911
  · exact context_12_21651_194945

theorem selected_cut_06532 : selected 9 ⟨194989, by decide⟩
    (prefixPartial 12 21652) = some ⟨12, 2, 0, 194989, 21652, 1913, 65536⟩ := by
  decide +kernel

theorem context_12_21652_194989 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21652 ⟨194989, by decide⟩ :=
  accepted_of_selected 12 21652 ⟨194989, by decide⟩ ⟨12, 2, 0, 194989, 21652, 1913, 65536⟩
    (by decide) selected_cut_06532

theorem selected_cut_06533 : selected 9 ⟨195016, by decide⟩
    (prefixPartial 12 21653) = some ⟨12, 2, 0, 195016, 21653, 1873, 65536⟩ := by
  decide +kernel

theorem context_12_21653_195016 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21653 ⟨195016, by decide⟩ :=
  accepted_of_selected 12 21653 ⟨195016, by decide⟩ ⟨12, 2, 0, 195016, 21653, 1873, 65536⟩
    (by decide) selected_cut_06533

theorem selected_cut_06534 : selected 9 ⟨195041, by decide⟩
    (prefixPartial 12 21654) = some ⟨12, 2, 0, 195041, 21654, 1869, 65536⟩ := by
  decide +kernel

theorem context_12_21654_195041 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21654 ⟨195041, by decide⟩ :=
  accepted_of_selected 12 21654 ⟨195041, by decide⟩ ⟨12, 2, 0, 195041, 21654, 1869, 65536⟩
    (by decide) selected_cut_06534

theorem selected_cut_06535 : selected 9 ⟨195066, by decide⟩
    (prefixPartial 12 21655) = some ⟨12, 2, 0, 195066, 21655, 1853, 65536⟩ := by
  decide +kernel

theorem context_12_21655_195066 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21655 ⟨195066, by decide⟩ :=
  accepted_of_selected 12 21655 ⟨195066, by decide⟩ ⟨12, 2, 0, 195066, 21655, 1853, 65536⟩
    (by decide) selected_cut_06535

theorem unmarked_context_11_5413_195067 : frontier 10 ⟨195067, by decide⟩
    (prefixCache 11 5413) (prefixPartial 11 5413) = false := by
  decide +kernel

theorem node_context_11_5413_195067 : EJMOriginalGlobalDAGData.nodes 10 ⟨195067, by decide⟩ =
    .split (coordinate 11) (![⟨194989, by decide⟩,⟨195016, by decide⟩,⟨195041, by decide⟩,⟨195066, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5413_195067 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5413 ⟨195067, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5413
    ⟨195067, by decide⟩ (by decide) (![⟨194989, by decide⟩,⟨195016, by decide⟩,⟨195041, by decide⟩,⟨195066, by decide⟩]) unmarked_context_11_5413_195067 node_context_11_5413_195067
  intro a
  fin_cases a
  · exact context_12_21652_194989
  · exact context_12_21653_195016
  · exact context_12_21654_195041
  · exact context_12_21655_195066

theorem selected_cut_06536 : selected 9 ⟨195092, by decide⟩
    (prefixPartial 12 21656) = some ⟨12, 2, 0, 195092, 21656, 1473, 65536⟩ := by
  decide +kernel

theorem context_12_21656_195092 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21656 ⟨195092, by decide⟩ :=
  accepted_of_selected 12 21656 ⟨195092, by decide⟩ ⟨12, 2, 0, 195092, 21656, 1473, 65536⟩
    (by decide) selected_cut_06536

theorem selected_cut_06537 : selected 9 ⟨195110, by decide⟩
    (prefixPartial 12 21657) = some ⟨12, 2, 0, 195110, 21657, 1577, 65536⟩ := by
  decide +kernel

theorem context_12_21657_195110 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21657 ⟨195110, by decide⟩ :=
  accepted_of_selected 12 21657 ⟨195110, by decide⟩ ⟨12, 2, 0, 195110, 21657, 1577, 65536⟩
    (by decide) selected_cut_06537

theorem selected_cut_06538 : selected 9 ⟨195130, by decide⟩
    (prefixPartial 12 21658) = some ⟨12, 2, 0, 195130, 21658, 1473, 65536⟩ := by
  decide +kernel

theorem context_12_21658_195130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21658 ⟨195130, by decide⟩ :=
  accepted_of_selected 12 21658 ⟨195130, by decide⟩ ⟨12, 2, 0, 195130, 21658, 1473, 65536⟩
    (by decide) selected_cut_06538

theorem selected_cut_06539 : selected 9 ⟨195148, by decide⟩
    (prefixPartial 12 21659) = some ⟨12, 2, 0, 195148, 21659, 1477, 65536⟩ := by
  decide +kernel

theorem context_12_21659_195148 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21659 ⟨195148, by decide⟩ :=
  accepted_of_selected 12 21659 ⟨195148, by decide⟩ ⟨12, 2, 0, 195148, 21659, 1477, 65536⟩
    (by decide) selected_cut_06539

theorem unmarked_context_11_5414_195149 : frontier 10 ⟨195149, by decide⟩
    (prefixCache 11 5414) (prefixPartial 11 5414) = false := by
  decide +kernel

theorem node_context_11_5414_195149 : EJMOriginalGlobalDAGData.nodes 10 ⟨195149, by decide⟩ =
    .split (coordinate 11) (![⟨195092, by decide⟩,⟨195110, by decide⟩,⟨195130, by decide⟩,⟨195148, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5414_195149 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5414 ⟨195149, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5414
    ⟨195149, by decide⟩ (by decide) (![⟨195092, by decide⟩,⟨195110, by decide⟩,⟨195130, by decide⟩,⟨195148, by decide⟩]) unmarked_context_11_5414_195149 node_context_11_5414_195149
  intro a
  fin_cases a
  · exact context_12_21656_195092
  · exact context_12_21657_195110
  · exact context_12_21658_195130
  · exact context_12_21659_195148

theorem selected_cut_06540 : selected 9 ⟨195173, by decide⟩
    (prefixPartial 12 21660) = some ⟨12, 2, 0, 195173, 21660, 1141, 65536⟩ := by
  decide +kernel

theorem context_12_21660_195173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21660 ⟨195173, by decide⟩ :=
  accepted_of_selected 12 21660 ⟨195173, by decide⟩ ⟨12, 2, 0, 195173, 21660, 1141, 65536⟩
    (by decide) selected_cut_06540

theorem selected_cut_06541 : selected 9 ⟨195195, by decide⟩
    (prefixPartial 12 21661) = some ⟨12, 2, 0, 195195, 21661, 1257, 65536⟩ := by
  decide +kernel

theorem context_12_21661_195195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21661 ⟨195195, by decide⟩ :=
  accepted_of_selected 12 21661 ⟨195195, by decide⟩ ⟨12, 2, 0, 195195, 21661, 1257, 65536⟩
    (by decide) selected_cut_06541

theorem selected_cut_06542 : selected 9 ⟨195217, by decide⟩
    (prefixPartial 12 21662) = some ⟨12, 2, 0, 195217, 21662, 1217, 65536⟩ := by
  decide +kernel

theorem context_12_21662_195217 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21662 ⟨195217, by decide⟩ :=
  accepted_of_selected 12 21662 ⟨195217, by decide⟩ ⟨12, 2, 0, 195217, 21662, 1217, 65536⟩
    (by decide) selected_cut_06542

theorem selected_cut_06543 : selected 9 ⟨195238, by decide⟩
    (prefixPartial 12 21663) = some ⟨12, 2, 0, 195238, 21663, 1221, 65536⟩ := by
  decide +kernel

theorem context_12_21663_195238 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21663 ⟨195238, by decide⟩ :=
  accepted_of_selected 12 21663 ⟨195238, by decide⟩ ⟨12, 2, 0, 195238, 21663, 1221, 65536⟩
    (by decide) selected_cut_06543

theorem unmarked_context_11_5415_195239 : frontier 10 ⟨195239, by decide⟩
    (prefixCache 11 5415) (prefixPartial 11 5415) = false := by
  decide +kernel

theorem node_context_11_5415_195239 : EJMOriginalGlobalDAGData.nodes 10 ⟨195239, by decide⟩ =
    .split (coordinate 11) (![⟨195173, by decide⟩,⟨195195, by decide⟩,⟨195217, by decide⟩,⟨195238, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5415_195239 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5415 ⟨195239, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5415
    ⟨195239, by decide⟩ (by decide) (![⟨195173, by decide⟩,⟨195195, by decide⟩,⟨195217, by decide⟩,⟨195238, by decide⟩]) unmarked_context_11_5415_195239 node_context_11_5415_195239
  intro a
  fin_cases a
  · exact context_12_21660_195173
  · exact context_12_21661_195195
  · exact context_12_21662_195217
  · exact context_12_21663_195238

theorem unmarked_context_10_1353_195240 : frontier 11 ⟨195240, by decide⟩
    (prefixCache 10 1353) (prefixPartial 10 1353) = false := by
  decide +kernel

theorem node_context_10_1353_195240 : EJMOriginalGlobalDAGData.nodes 11 ⟨195240, by decide⟩ =
    .split (coordinate 10) (![⟨194946, by decide⟩,⟨195067, by decide⟩,⟨195149, by decide⟩,⟨195239, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1353_195240 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1353 ⟨195240, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1353
    ⟨195240, by decide⟩ (by decide) (![⟨194946, by decide⟩,⟨195067, by decide⟩,⟨195149, by decide⟩,⟨195239, by decide⟩]) unmarked_context_10_1353_195240 node_context_10_1353_195240
  intro a
  fin_cases a
  · exact context_11_5412_194946
  · exact context_11_5413_195067
  · exact context_11_5414_195149
  · exact context_11_5415_195239

theorem selected_cut_06544 : selected 10 ⟨195310, by decide⟩
    (prefixPartial 11 5416) = some ⟨11, 2, 0, 195310, 5416, 3769, 262144⟩ := by
  decide +kernel

theorem context_11_5416_195310 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5416 ⟨195310, by decide⟩ :=
  accepted_of_selected 11 5416 ⟨195310, by decide⟩ ⟨11, 2, 0, 195310, 5416, 3769, 262144⟩
    (by decide) selected_cut_06544

theorem selected_cut_06545 : selected 10 ⟨195356, by decide⟩
    (prefixPartial 11 5417) = some ⟨11, 2, 0, 195356, 5417, 2753, 262144⟩ := by
  decide +kernel

theorem context_11_5417_195356 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5417 ⟨195356, by decide⟩ :=
  accepted_of_selected 11 5417 ⟨195356, by decide⟩ ⟨11, 2, 0, 195356, 5417, 2753, 262144⟩
    (by decide) selected_cut_06545

theorem selected_cut_06546 : selected 10 ⟨195408, by decide⟩
    (prefixPartial 11 5418) = some ⟨11, 2, 0, 195408, 5418, 2545, 262144⟩ := by
  decide +kernel

theorem context_11_5418_195408 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5418 ⟨195408, by decide⟩ :=
  accepted_of_selected 11 5418 ⟨195408, by decide⟩ ⟨11, 2, 0, 195408, 5418, 2545, 262144⟩
    (by decide) selected_cut_06546

theorem selected_cut_06547 : selected 10 ⟨195447, by decide⟩
    (prefixPartial 11 5419) = some ⟨11, 2, 0, 195447, 5419, 2025, 262144⟩ := by
  decide +kernel

theorem context_11_5419_195447 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5419 ⟨195447, by decide⟩ :=
  accepted_of_selected 11 5419 ⟨195447, by decide⟩ ⟨11, 2, 0, 195447, 5419, 2025, 262144⟩
    (by decide) selected_cut_06547

theorem unmarked_context_10_1354_195448 : frontier 11 ⟨195448, by decide⟩
    (prefixCache 10 1354) (prefixPartial 10 1354) = false := by
  decide +kernel

theorem node_context_10_1354_195448 : EJMOriginalGlobalDAGData.nodes 11 ⟨195448, by decide⟩ =
    .split (coordinate 10) (![⟨195310, by decide⟩,⟨195356, by decide⟩,⟨195408, by decide⟩,⟨195447, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1354_195448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1354 ⟨195448, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1354
    ⟨195448, by decide⟩ (by decide) (![⟨195310, by decide⟩,⟨195356, by decide⟩,⟨195408, by decide⟩,⟨195447, by decide⟩]) unmarked_context_10_1354_195448 node_context_10_1354_195448
  intro a
  fin_cases a
  · exact context_11_5416_195310
  · exact context_11_5417_195356
  · exact context_11_5418_195408
  · exact context_11_5419_195447

theorem selected_cut_06548 : selected 10 ⟨195488, by decide⟩
    (prefixPartial 11 5420) = some ⟨11, 2, 0, 195488, 5420, 1885, 262144⟩ := by
  decide +kernel

theorem context_11_5420_195488 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5420 ⟨195488, by decide⟩ :=
  accepted_of_selected 11 5420 ⟨195488, by decide⟩ ⟨11, 2, 0, 195488, 5420, 1885, 262144⟩
    (by decide) selected_cut_06548

theorem selected_cut_06549 : selected 10 ⟨195515, by decide⟩
    (prefixPartial 11 5421) = some ⟨11, 2, 0, 195515, 5421, 1281, 262144⟩ := by
  decide +kernel

theorem context_11_5421_195515 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5421 ⟨195515, by decide⟩ :=
  accepted_of_selected 11 5421 ⟨195515, by decide⟩ ⟨11, 2, 0, 195515, 5421, 1281, 262144⟩
    (by decide) selected_cut_06549

theorem selected_cut_06550 : selected 10 ⟨195540, by decide⟩
    (prefixPartial 11 5422) = some ⟨11, 2, 0, 195540, 5422, 793, 262144⟩ := by
  decide +kernel

theorem context_11_5422_195540 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5422 ⟨195540, by decide⟩ :=
  accepted_of_selected 11 5422 ⟨195540, by decide⟩ ⟨11, 2, 0, 195540, 5422, 793, 262144⟩
    (by decide) selected_cut_06550

theorem selected_cut_06551 : selected 10 ⟨195562, by decide⟩
    (prefixPartial 11 5423) = some ⟨11, 2, 0, 195562, 5423, 329, 262144⟩ := by
  decide +kernel

theorem context_11_5423_195562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5423 ⟨195562, by decide⟩ :=
  accepted_of_selected 11 5423 ⟨195562, by decide⟩ ⟨11, 2, 0, 195562, 5423, 329, 262144⟩
    (by decide) selected_cut_06551

theorem unmarked_context_10_1355_195563 : frontier 11 ⟨195563, by decide⟩
    (prefixCache 10 1355) (prefixPartial 10 1355) = false := by
  decide +kernel

theorem node_context_10_1355_195563 : EJMOriginalGlobalDAGData.nodes 11 ⟨195563, by decide⟩ =
    .split (coordinate 10) (![⟨195488, by decide⟩,⟨195515, by decide⟩,⟨195540, by decide⟩,⟨195562, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1355_195563 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1355 ⟨195563, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1355
    ⟨195563, by decide⟩ (by decide) (![⟨195488, by decide⟩,⟨195515, by decide⟩,⟨195540, by decide⟩,⟨195562, by decide⟩]) unmarked_context_10_1355_195563 node_context_10_1355_195563
  intro a
  fin_cases a
  · exact context_11_5420_195488
  · exact context_11_5421_195515
  · exact context_11_5422_195540
  · exact context_11_5423_195562

theorem unmarked_context_9_338_195564 : frontier 12 ⟨195564, by decide⟩
    (prefixCache 9 338) (prefixPartial 9 338) = false := by
  decide +kernel

theorem node_context_9_338_195564 : EJMOriginalGlobalDAGData.nodes 12 ⟨195564, by decide⟩ =
    .split (coordinate 9) (![⟨194781, by decide⟩,⟨195240, by decide⟩,⟨195448, by decide⟩,⟨195563, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_338_195564 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 338 ⟨195564, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 338
    ⟨195564, by decide⟩ (by decide) (![⟨194781, by decide⟩,⟨195240, by decide⟩,⟨195448, by decide⟩,⟨195563, by decide⟩]) unmarked_context_9_338_195564 node_context_9_338_195564
  intro a
  fin_cases a
  · exact context_10_1352_194781
  · exact context_10_1353_195240
  · exact context_10_1354_195448
  · exact context_10_1355_195563

theorem selected_cut_06552 : selected 12 ⟨4601, by decide⟩
    (prefixPartial 9 339) = some ⟨9, 1, 0, 4601, 339, 1, 4194304⟩ := by
  decide +kernel

theorem context_9_339_4601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 339 ⟨4601, by decide⟩ :=
  accepted_of_selected 9 339 ⟨4601, by decide⟩ ⟨9, 1, 0, 4601, 339, 1, 4194304⟩
    (by decide) selected_cut_06552

theorem unmarked_context_8_84_195565 : frontier 13 ⟨195565, by decide⟩
    (prefixCache 8 84) (prefixPartial 8 84) = false := by
  decide +kernel

theorem node_context_8_84_195565 : EJMOriginalGlobalDAGData.nodes 13 ⟨195565, by decide⟩ =
    .split (coordinate 8) (![⟨192127, by decide⟩,⟨194251, by decide⟩,⟨195564, by decide⟩,⟨4601, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_84_195565 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 84 ⟨195565, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 84
    ⟨195565, by decide⟩ (by decide) (![⟨192127, by decide⟩,⟨194251, by decide⟩,⟨195564, by decide⟩,⟨4601, by decide⟩]) unmarked_context_8_84_195565 node_context_8_84_195565
  intro a
  fin_cases a
  · exact context_9_336_192127
  · exact context_9_337_194251
  · exact context_9_338_195564
  · exact context_9_339_4601

theorem selected_cut_06553 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 21760) = some ⟨12, 1, 0, 34034, 21760, 1, 65536⟩ := by
  decide +kernel

theorem context_12_21760_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21760 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 21760 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 21760, 1, 65536⟩
    (by decide) selected_cut_06553

theorem selected_cut_06554 : selected 9 ⟨195640, by decide⟩
    (prefixPartial 12 21761) = some ⟨12, 2, 0, 195640, 21761, 2861, 65536⟩ := by
  decide +kernel

theorem context_12_21761_195640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21761 ⟨195640, by decide⟩ :=
  accepted_of_selected 12 21761 ⟨195640, by decide⟩ ⟨12, 2, 0, 195640, 21761, 2861, 65536⟩
    (by decide) selected_cut_06554

theorem selected_cut_06555 : selected 7 ⟨195676, by decide⟩
    (prefixPartial 14 348192) = some ⟨14, 2, 0, 195676, 348192, 1577, 4096⟩ := by
  decide +kernel

theorem context_14_348192_195676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 348192 ⟨195676, by decide⟩ :=
  accepted_of_selected 14 348192 ⟨195676, by decide⟩ ⟨14, 2, 0, 195676, 348192, 1577, 4096⟩
    (by decide) selected_cut_06555

theorem selected_cut_06556 : selected 7 ⟨195688, by decide⟩
    (prefixPartial 14 348193) = some ⟨14, 2, 0, 195688, 348193, 961, 4096⟩ := by
  decide +kernel

theorem context_14_348193_195688 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 348193 ⟨195688, by decide⟩ :=
  accepted_of_selected 14 348193 ⟨195688, by decide⟩ ⟨14, 2, 0, 195688, 348193, 961, 4096⟩
    (by decide) selected_cut_06556

theorem selected_cut_06557 : selected 7 ⟨195707, by decide⟩
    (prefixPartial 14 348194) = some ⟨14, 2, 0, 195707, 348194, 1185, 4096⟩ := by
  decide +kernel

theorem context_14_348194_195707 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 348194 ⟨195707, by decide⟩ :=
  accepted_of_selected 14 348194 ⟨195707, by decide⟩ ⟨14, 2, 0, 195707, 348194, 1185, 4096⟩
    (by decide) selected_cut_06557

theorem selected_cut_06558 : selected 7 ⟨195717, by decide⟩
    (prefixPartial 14 348195) = some ⟨14, 2, 0, 195717, 348195, 1053, 4096⟩ := by
  decide +kernel

theorem context_14_348195_195717 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 348195 ⟨195717, by decide⟩ :=
  accepted_of_selected 14 348195 ⟨195717, by decide⟩ ⟨14, 2, 0, 195717, 348195, 1053, 4096⟩
    (by decide) selected_cut_06558

theorem unmarked_context_13_87048_195718 : frontier 8 ⟨195718, by decide⟩
    (prefixCache 13 87048) (prefixPartial 13 87048) = false := by
  decide +kernel

theorem node_context_13_87048_195718 : EJMOriginalGlobalDAGData.nodes 8 ⟨195718, by decide⟩ =
    .split (coordinate 13) (![⟨195676, by decide⟩,⟨195688, by decide⟩,⟨195707, by decide⟩,⟨195717, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_87048_195718 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87048 ⟨195718, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 87048
    ⟨195718, by decide⟩ (by decide) (![⟨195676, by decide⟩,⟨195688, by decide⟩,⟨195707, by decide⟩,⟨195717, by decide⟩]) unmarked_context_13_87048_195718 node_context_13_87048_195718
  intro a
  fin_cases a
  · exact context_14_348192_195676
  · exact context_14_348193_195688
  · exact context_14_348194_195707
  · exact context_14_348195_195717

theorem selected_cut_06559 : selected 8 ⟨195787, by decide⟩
    (prefixPartial 13 87049) = some ⟨13, 2, 0, 195787, 87049, 3785, 16384⟩ := by
  decide +kernel

theorem context_13_87049_195787 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87049 ⟨195787, by decide⟩ :=
  accepted_of_selected 13 87049 ⟨195787, by decide⟩ ⟨13, 2, 0, 195787, 87049, 3785, 16384⟩
    (by decide) selected_cut_06559

theorem selected_cut_06560 : selected 8 ⟨195814, by decide⟩
    (prefixPartial 13 87050) = some ⟨13, 2, 0, 195814, 87050, 2417, 16384⟩ := by
  decide +kernel

theorem context_13_87050_195814 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87050 ⟨195814, by decide⟩ :=
  accepted_of_selected 13 87050 ⟨195814, by decide⟩ ⟨13, 2, 0, 195814, 87050, 2417, 16384⟩
    (by decide) selected_cut_06560

theorem selected_cut_06561 : selected 8 ⟨195837, by decide⟩
    (prefixPartial 13 87051) = some ⟨13, 2, 0, 195837, 87051, 1401, 16384⟩ := by
  decide +kernel

theorem context_13_87051_195837 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87051 ⟨195837, by decide⟩ :=
  accepted_of_selected 13 87051 ⟨195837, by decide⟩ ⟨13, 2, 0, 195837, 87051, 1401, 16384⟩
    (by decide) selected_cut_06561

theorem unmarked_context_12_21762_195838 : frontier 9 ⟨195838, by decide⟩
    (prefixCache 12 21762) (prefixPartial 12 21762) = false := by
  decide +kernel

theorem node_context_12_21762_195838 : EJMOriginalGlobalDAGData.nodes 9 ⟨195838, by decide⟩ =
    .split (coordinate 12) (![⟨195718, by decide⟩,⟨195787, by decide⟩,⟨195814, by decide⟩,⟨195837, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21762_195838 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21762 ⟨195838, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21762
    ⟨195838, by decide⟩ (by decide) (![⟨195718, by decide⟩,⟨195787, by decide⟩,⟨195814, by decide⟩,⟨195837, by decide⟩]) unmarked_context_12_21762_195838 node_context_12_21762_195838
  intro a
  fin_cases a
  · exact context_13_87048_195718
  · exact context_13_87049_195787
  · exact context_13_87050_195814
  · exact context_13_87051_195837

theorem selected_cut_06562 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 21763) = some ⟨12, 1, 0, 893, 21763, 1, 65536⟩ := by
  decide +kernel

theorem context_12_21763_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21763 ⟨893, by decide⟩ :=
  accepted_of_selected 12 21763 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 21763, 1, 65536⟩
    (by decide) selected_cut_06562

theorem unmarked_context_11_5440_195839 : frontier 10 ⟨195839, by decide⟩
    (prefixCache 11 5440) (prefixPartial 11 5440) = false := by
  decide +kernel

theorem node_context_11_5440_195839 : EJMOriginalGlobalDAGData.nodes 10 ⟨195839, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨195640, by decide⟩,⟨195838, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5440_195839 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5440 ⟨195839, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5440
    ⟨195839, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨195640, by decide⟩,⟨195838, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_5440_195839 node_context_11_5440_195839
  intro a
  fin_cases a
  · exact context_12_21760_34034
  · exact context_12_21761_195640
  · exact context_12_21762_195838
  · exact context_12_21763_893

theorem selected_cut_06563 : selected 8 ⟨195876, by decide⟩
    (prefixPartial 13 87056) = some ⟨13, 2, 0, 195876, 87056, 1397, 16384⟩ := by
  decide +kernel

theorem context_13_87056_195876 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87056 ⟨195876, by decide⟩ :=
  accepted_of_selected 13 87056 ⟨195876, by decide⟩ ⟨13, 2, 0, 195876, 87056, 1397, 16384⟩
    (by decide) selected_cut_06563

theorem selected_cut_06564 : selected 8 ⟨195912, by decide⟩
    (prefixPartial 13 87057) = some ⟨13, 2, 0, 195912, 87057, 1681, 16384⟩ := by
  decide +kernel

theorem context_13_87057_195912 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87057 ⟨195912, by decide⟩ :=
  accepted_of_selected 13 87057 ⟨195912, by decide⟩ ⟨13, 2, 0, 195912, 87057, 1681, 16384⟩
    (by decide) selected_cut_06564

theorem selected_cut_06565 : selected 8 ⟨195948, by decide⟩
    (prefixPartial 13 87058) = some ⟨13, 2, 0, 195948, 87058, 1853, 16384⟩ := by
  decide +kernel

theorem context_13_87058_195948 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87058 ⟨195948, by decide⟩ :=
  accepted_of_selected 13 87058 ⟨195948, by decide⟩ ⟨13, 2, 0, 195948, 87058, 1853, 16384⟩
    (by decide) selected_cut_06565

theorem selected_cut_06566 : selected 8 ⟨414, by decide⟩
    (prefixPartial 13 87059) = some ⟨13, 1, 0, 414, 87059, 1, 16384⟩ := by
  decide +kernel

theorem context_13_87059_414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87059 ⟨414, by decide⟩ :=
  accepted_of_selected 13 87059 ⟨414, by decide⟩ ⟨13, 1, 0, 414, 87059, 1, 16384⟩
    (by decide) selected_cut_06566

theorem unmarked_context_12_21764_195949 : frontier 9 ⟨195949, by decide⟩
    (prefixCache 12 21764) (prefixPartial 12 21764) = false := by
  decide +kernel

theorem node_context_12_21764_195949 : EJMOriginalGlobalDAGData.nodes 9 ⟨195949, by decide⟩ =
    .split (coordinate 12) (![⟨195876, by decide⟩,⟨195912, by decide⟩,⟨195948, by decide⟩,⟨414, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21764_195949 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21764 ⟨195949, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21764
    ⟨195949, by decide⟩ (by decide) (![⟨195876, by decide⟩,⟨195912, by decide⟩,⟨195948, by decide⟩,⟨414, by decide⟩]) unmarked_context_12_21764_195949 node_context_12_21764_195949
  intro a
  fin_cases a
  · exact context_13_87056_195876
  · exact context_13_87057_195912
  · exact context_13_87058_195948
  · exact context_13_87059_414

theorem selected_cut_06567 : selected 8 ⟨195995, by decide⟩
    (prefixPartial 13 87060) = some ⟨13, 2, 0, 195995, 87060, 2509, 16384⟩ := by
  decide +kernel

theorem context_13_87060_195995 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87060 ⟨195995, by decide⟩ :=
  accepted_of_selected 13 87060 ⟨195995, by decide⟩ ⟨13, 2, 0, 195995, 87060, 2509, 16384⟩
    (by decide) selected_cut_06567

theorem selected_cut_06568 : selected 8 ⟨196048, by decide⟩
    (prefixPartial 13 87061) = some ⟨13, 2, 0, 196048, 87061, 2229, 16384⟩ := by
  decide +kernel

theorem context_13_87061_196048 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87061 ⟨196048, by decide⟩ :=
  accepted_of_selected 13 87061 ⟨196048, by decide⟩ ⟨13, 2, 0, 196048, 87061, 2229, 16384⟩
    (by decide) selected_cut_06568

theorem selected_cut_06569 : selected 8 ⟨196089, by decide⟩
    (prefixPartial 13 87062) = some ⟨13, 2, 0, 196089, 87062, 2325, 16384⟩ := by
  decide +kernel

theorem context_13_87062_196089 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87062 ⟨196089, by decide⟩ :=
  accepted_of_selected 13 87062 ⟨196089, by decide⟩ ⟨13, 2, 0, 196089, 87062, 2325, 16384⟩
    (by decide) selected_cut_06569

theorem selected_cut_06570 : selected 8 ⟨414, by decide⟩
    (prefixPartial 13 87063) = some ⟨13, 1, 0, 414, 87063, 1, 16384⟩ := by
  decide +kernel

theorem context_13_87063_414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87063 ⟨414, by decide⟩ :=
  accepted_of_selected 13 87063 ⟨414, by decide⟩ ⟨13, 1, 0, 414, 87063, 1, 16384⟩
    (by decide) selected_cut_06570

theorem unmarked_context_12_21765_196090 : frontier 9 ⟨196090, by decide⟩
    (prefixCache 12 21765) (prefixPartial 12 21765) = false := by
  decide +kernel

theorem node_context_12_21765_196090 : EJMOriginalGlobalDAGData.nodes 9 ⟨196090, by decide⟩ =
    .split (coordinate 12) (![⟨195995, by decide⟩,⟨196048, by decide⟩,⟨196089, by decide⟩,⟨414, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21765_196090 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21765 ⟨196090, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21765
    ⟨196090, by decide⟩ (by decide) (![⟨195995, by decide⟩,⟨196048, by decide⟩,⟨196089, by decide⟩,⟨414, by decide⟩]) unmarked_context_12_21765_196090 node_context_12_21765_196090
  intro a
  fin_cases a
  · exact context_13_87060_195995
  · exact context_13_87061_196048
  · exact context_13_87062_196089
  · exact context_13_87063_414

theorem selected_cut_06571 : selected 8 ⟨196159, by decide⟩
    (prefixPartial 13 87064) = some ⟨13, 2, 0, 196159, 87064, 3865, 16384⟩ := by
  decide +kernel

theorem context_13_87064_196159 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87064 ⟨196159, by decide⟩ :=
  accepted_of_selected 13 87064 ⟨196159, by decide⟩ ⟨13, 2, 0, 196159, 87064, 3865, 16384⟩
    (by decide) selected_cut_06571

theorem selected_cut_06572 : selected 8 ⟨196198, by decide⟩
    (prefixPartial 13 87065) = some ⟨13, 2, 0, 196198, 87065, 3365, 16384⟩ := by
  decide +kernel

theorem context_13_87065_196198 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87065 ⟨196198, by decide⟩ :=
  accepted_of_selected 13 87065 ⟨196198, by decide⟩ ⟨13, 2, 0, 196198, 87065, 3365, 16384⟩
    (by decide) selected_cut_06572

theorem selected_cut_06573 : selected 8 ⟨196222, by decide⟩
    (prefixPartial 13 87066) = some ⟨13, 2, 0, 196222, 87066, 2265, 16384⟩ := by
  decide +kernel

theorem context_13_87066_196222 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87066 ⟨196222, by decide⟩ :=
  accepted_of_selected 13 87066 ⟨196222, by decide⟩ ⟨13, 2, 0, 196222, 87066, 2265, 16384⟩
    (by decide) selected_cut_06573

theorem selected_cut_06574 : selected 8 ⟨196237, by decide⟩
    (prefixPartial 13 87067) = some ⟨13, 2, 0, 196237, 87067, 1321, 16384⟩ := by
  decide +kernel

theorem context_13_87067_196237 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87067 ⟨196237, by decide⟩ :=
  accepted_of_selected 13 87067 ⟨196237, by decide⟩ ⟨13, 2, 0, 196237, 87067, 1321, 16384⟩
    (by decide) selected_cut_06574

theorem unmarked_context_12_21766_196238 : frontier 9 ⟨196238, by decide⟩
    (prefixCache 12 21766) (prefixPartial 12 21766) = false := by
  decide +kernel

theorem node_context_12_21766_196238 : EJMOriginalGlobalDAGData.nodes 9 ⟨196238, by decide⟩ =
    .split (coordinate 12) (![⟨196159, by decide⟩,⟨196198, by decide⟩,⟨196222, by decide⟩,⟨196237, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21766_196238 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21766 ⟨196238, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21766
    ⟨196238, by decide⟩ (by decide) (![⟨196159, by decide⟩,⟨196198, by decide⟩,⟨196222, by decide⟩,⟨196237, by decide⟩]) unmarked_context_12_21766_196238 node_context_12_21766_196238
  intro a
  fin_cases a
  · exact context_13_87064_196159
  · exact context_13_87065_196198
  · exact context_13_87066_196222
  · exact context_13_87067_196237

theorem selected_cut_06575 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 21767) = some ⟨12, 1, 0, 893, 21767, 1, 65536⟩ := by
  decide +kernel

theorem context_12_21767_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21767 ⟨893, by decide⟩ :=
  accepted_of_selected 12 21767 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 21767, 1, 65536⟩
    (by decide) selected_cut_06575

theorem unmarked_context_11_5441_196239 : frontier 10 ⟨196239, by decide⟩
    (prefixCache 11 5441) (prefixPartial 11 5441) = false := by
  decide +kernel

theorem node_context_11_5441_196239 : EJMOriginalGlobalDAGData.nodes 10 ⟨196239, by decide⟩ =
    .split (coordinate 11) (![⟨195949, by decide⟩,⟨196090, by decide⟩,⟨196238, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5441_196239 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5441 ⟨196239, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5441
    ⟨196239, by decide⟩ (by decide) (![⟨195949, by decide⟩,⟨196090, by decide⟩,⟨196238, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_5441_196239 node_context_11_5441_196239
  intro a
  fin_cases a
  · exact context_12_21764_195949
  · exact context_12_21765_196090
  · exact context_12_21766_196238
  · exact context_12_21767_893

theorem selected_cut_06576 : selected 8 ⟨196277, by decide⟩
    (prefixPartial 13 87072) = some ⟨13, 2, 0, 196277, 87072, 2469, 16384⟩ := by
  decide +kernel

theorem context_13_87072_196277 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87072 ⟨196277, by decide⟩ :=
  accepted_of_selected 13 87072 ⟨196277, by decide⟩ ⟨13, 2, 0, 196277, 87072, 2469, 16384⟩
    (by decide) selected_cut_06576

theorem selected_cut_06577 : selected 8 ⟨196321, by decide⟩
    (prefixPartial 13 87073) = some ⟨13, 2, 0, 196321, 87073, 3489, 16384⟩ := by
  decide +kernel

theorem context_13_87073_196321 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87073 ⟨196321, by decide⟩ :=
  accepted_of_selected 13 87073 ⟨196321, by decide⟩ ⟨13, 2, 0, 196321, 87073, 3489, 16384⟩
    (by decide) selected_cut_06577

theorem selected_cut_06578 : selected 8 ⟨196355, by decide⟩
    (prefixPartial 13 87074) = some ⟨13, 2, 0, 196355, 87074, 2389, 16384⟩ := by
  decide +kernel

theorem context_13_87074_196355 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87074 ⟨196355, by decide⟩ :=
  accepted_of_selected 13 87074 ⟨196355, by decide⟩ ⟨13, 2, 0, 196355, 87074, 2389, 16384⟩
    (by decide) selected_cut_06578

theorem selected_cut_06579 : selected 8 ⟨196371, by decide⟩
    (prefixPartial 13 87075) = some ⟨13, 2, 0, 196371, 87075, 1189, 16384⟩ := by
  decide +kernel

theorem context_13_87075_196371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87075 ⟨196371, by decide⟩ :=
  accepted_of_selected 13 87075 ⟨196371, by decide⟩ ⟨13, 2, 0, 196371, 87075, 1189, 16384⟩
    (by decide) selected_cut_06579

theorem unmarked_context_12_21768_196372 : frontier 9 ⟨196372, by decide⟩
    (prefixCache 12 21768) (prefixPartial 12 21768) = false := by
  decide +kernel

theorem node_context_12_21768_196372 : EJMOriginalGlobalDAGData.nodes 9 ⟨196372, by decide⟩ =
    .split (coordinate 12) (![⟨196277, by decide⟩,⟨196321, by decide⟩,⟨196355, by decide⟩,⟨196371, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21768_196372 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21768 ⟨196372, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21768
    ⟨196372, by decide⟩ (by decide) (![⟨196277, by decide⟩,⟨196321, by decide⟩,⟨196355, by decide⟩,⟨196371, by decide⟩]) unmarked_context_12_21768_196372 node_context_12_21768_196372
  intro a
  fin_cases a
  · exact context_13_87072_196277
  · exact context_13_87073_196321
  · exact context_13_87074_196355
  · exact context_13_87075_196371

theorem selected_cut_06580 : selected 8 ⟨196412, by decide⟩
    (prefixPartial 13 87076) = some ⟨13, 2, 0, 196412, 87076, 2577, 16384⟩ := by
  decide +kernel

theorem context_13_87076_196412 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87076 ⟨196412, by decide⟩ :=
  accepted_of_selected 13 87076 ⟨196412, by decide⟩ ⟨13, 2, 0, 196412, 87076, 2577, 16384⟩
    (by decide) selected_cut_06580

theorem selected_cut_06581 : selected 8 ⟨196441, by decide⟩
    (prefixPartial 13 87077) = some ⟨13, 2, 0, 196441, 87077, 2633, 16384⟩ := by
  decide +kernel

theorem context_13_87077_196441 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87077 ⟨196441, by decide⟩ :=
  accepted_of_selected 13 87077 ⟨196441, by decide⟩ ⟨13, 2, 0, 196441, 87077, 2633, 16384⟩
    (by decide) selected_cut_06581

theorem selected_cut_06582 : selected 8 ⟨196460, by decide⟩
    (prefixPartial 13 87078) = some ⟨13, 2, 0, 196460, 87078, 2105, 16384⟩ := by
  decide +kernel

theorem context_13_87078_196460 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87078 ⟨196460, by decide⟩ :=
  accepted_of_selected 13 87078 ⟨196460, by decide⟩ ⟨13, 2, 0, 196460, 87078, 2105, 16384⟩
    (by decide) selected_cut_06582

theorem selected_cut_06583 : selected 8 ⟨196466, by decide⟩
    (prefixPartial 13 87079) = some ⟨13, 2, 0, 196466, 87079, 1137, 16384⟩ := by
  decide +kernel

theorem context_13_87079_196466 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87079 ⟨196466, by decide⟩ :=
  accepted_of_selected 13 87079 ⟨196466, by decide⟩ ⟨13, 2, 0, 196466, 87079, 1137, 16384⟩
    (by decide) selected_cut_06583

theorem unmarked_context_12_21769_196467 : frontier 9 ⟨196467, by decide⟩
    (prefixCache 12 21769) (prefixPartial 12 21769) = false := by
  decide +kernel

theorem node_context_12_21769_196467 : EJMOriginalGlobalDAGData.nodes 9 ⟨196467, by decide⟩ =
    .split (coordinate 12) (![⟨196412, by decide⟩,⟨196441, by decide⟩,⟨196460, by decide⟩,⟨196466, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21769_196467 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21769 ⟨196467, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21769
    ⟨196467, by decide⟩ (by decide) (![⟨196412, by decide⟩,⟨196441, by decide⟩,⟨196460, by decide⟩,⟨196466, by decide⟩]) unmarked_context_12_21769_196467 node_context_12_21769_196467
  intro a
  fin_cases a
  · exact context_13_87076_196412
  · exact context_13_87077_196441
  · exact context_13_87078_196460
  · exact context_13_87079_196466

theorem selected_cut_06584 : selected 8 ⟨196528, by decide⟩
    (prefixPartial 13 87080) = some ⟨13, 2, 0, 196528, 87080, 3741, 16384⟩ := by
  decide +kernel

theorem context_13_87080_196528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87080 ⟨196528, by decide⟩ :=
  accepted_of_selected 13 87080 ⟨196528, by decide⟩ ⟨13, 2, 0, 196528, 87080, 3741, 16384⟩
    (by decide) selected_cut_06584

theorem selected_cut_06585 : selected 8 ⟨196578, by decide⟩
    (prefixPartial 13 87081) = some ⟨13, 2, 0, 196578, 87081, 3621, 16384⟩ := by
  decide +kernel

theorem context_13_87081_196578 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87081 ⟨196578, by decide⟩ :=
  accepted_of_selected 13 87081 ⟨196578, by decide⟩ ⟨13, 2, 0, 196578, 87081, 3621, 16384⟩
    (by decide) selected_cut_06585

theorem selected_cut_06586 : selected 8 ⟨196604, by decide⟩
    (prefixPartial 13 87082) = some ⟨13, 2, 0, 196604, 87082, 2221, 16384⟩ := by
  decide +kernel

theorem context_13_87082_196604 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87082 ⟨196604, by decide⟩ :=
  accepted_of_selected 13 87082 ⟨196604, by decide⟩ ⟨13, 2, 0, 196604, 87082, 2221, 16384⟩
    (by decide) selected_cut_06586

theorem selected_cut_06587 : selected 8 ⟨196618, by decide⟩
    (prefixPartial 13 87083) = some ⟨13, 2, 0, 196618, 87083, 1293, 16384⟩ := by
  decide +kernel

theorem context_13_87083_196618 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87083 ⟨196618, by decide⟩ :=
  accepted_of_selected 13 87083 ⟨196618, by decide⟩ ⟨13, 2, 0, 196618, 87083, 1293, 16384⟩
    (by decide) selected_cut_06587

theorem unmarked_context_12_21770_196619 : frontier 9 ⟨196619, by decide⟩
    (prefixCache 12 21770) (prefixPartial 12 21770) = false := by
  decide +kernel

theorem node_context_12_21770_196619 : EJMOriginalGlobalDAGData.nodes 9 ⟨196619, by decide⟩ =
    .split (coordinate 12) (![⟨196528, by decide⟩,⟨196578, by decide⟩,⟨196604, by decide⟩,⟨196618, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21770_196619 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21770 ⟨196619, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21770
    ⟨196619, by decide⟩ (by decide) (![⟨196528, by decide⟩,⟨196578, by decide⟩,⟨196604, by decide⟩,⟨196618, by decide⟩]) unmarked_context_12_21770_196619 node_context_12_21770_196619
  intro a
  fin_cases a
  · exact context_13_87080_196528
  · exact context_13_87081_196578
  · exact context_13_87082_196604
  · exact context_13_87083_196618

theorem selected_cut_06588 : selected 8 ⟨196674, by decide⟩
    (prefixPartial 13 87084) = some ⟨13, 2, 0, 196674, 87084, 3509, 16384⟩ := by
  decide +kernel

theorem context_13_87084_196674 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87084 ⟨196674, by decide⟩ :=
  accepted_of_selected 13 87084 ⟨196674, by decide⟩ ⟨13, 2, 0, 196674, 87084, 3509, 16384⟩
    (by decide) selected_cut_06588

theorem selected_cut_06589 : selected 8 ⟨196734, by decide⟩
    (prefixPartial 13 87085) = some ⟨13, 2, 0, 196734, 87085, 3697, 16384⟩ := by
  decide +kernel

theorem context_13_87085_196734 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87085 ⟨196734, by decide⟩ :=
  accepted_of_selected 13 87085 ⟨196734, by decide⟩ ⟨13, 2, 0, 196734, 87085, 3697, 16384⟩
    (by decide) selected_cut_06589

theorem selected_cut_06590 : selected 8 ⟨196764, by decide⟩
    (prefixPartial 13 87086) = some ⟨13, 2, 0, 196764, 87086, 2357, 16384⟩ := by
  decide +kernel

theorem context_13_87086_196764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87086 ⟨196764, by decide⟩ :=
  accepted_of_selected 13 87086 ⟨196764, by decide⟩ ⟨13, 2, 0, 196764, 87086, 2357, 16384⟩
    (by decide) selected_cut_06590

theorem selected_cut_06591 : selected 8 ⟨196773, by decide⟩
    (prefixPartial 13 87087) = some ⟨13, 2, 0, 196773, 87087, 1185, 16384⟩ := by
  decide +kernel

theorem context_13_87087_196773 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87087 ⟨196773, by decide⟩ :=
  accepted_of_selected 13 87087 ⟨196773, by decide⟩ ⟨13, 2, 0, 196773, 87087, 1185, 16384⟩
    (by decide) selected_cut_06591

theorem unmarked_context_12_21771_196774 : frontier 9 ⟨196774, by decide⟩
    (prefixCache 12 21771) (prefixPartial 12 21771) = false := by
  decide +kernel

theorem node_context_12_21771_196774 : EJMOriginalGlobalDAGData.nodes 9 ⟨196774, by decide⟩ =
    .split (coordinate 12) (![⟨196674, by decide⟩,⟨196734, by decide⟩,⟨196764, by decide⟩,⟨196773, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21771_196774 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21771 ⟨196774, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21771
    ⟨196774, by decide⟩ (by decide) (![⟨196674, by decide⟩,⟨196734, by decide⟩,⟨196764, by decide⟩,⟨196773, by decide⟩]) unmarked_context_12_21771_196774 node_context_12_21771_196774
  intro a
  fin_cases a
  · exact context_13_87084_196674
  · exact context_13_87085_196734
  · exact context_13_87086_196764
  · exact context_13_87087_196773

theorem unmarked_context_11_5442_196775 : frontier 10 ⟨196775, by decide⟩
    (prefixCache 11 5442) (prefixPartial 11 5442) = false := by
  decide +kernel

theorem node_context_11_5442_196775 : EJMOriginalGlobalDAGData.nodes 10 ⟨196775, by decide⟩ =
    .split (coordinate 11) (![⟨196372, by decide⟩,⟨196467, by decide⟩,⟨196619, by decide⟩,⟨196774, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5442_196775 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5442 ⟨196775, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5442
    ⟨196775, by decide⟩ (by decide) (![⟨196372, by decide⟩,⟨196467, by decide⟩,⟨196619, by decide⟩,⟨196774, by decide⟩]) unmarked_context_11_5442_196775 node_context_11_5442_196775
  intro a
  fin_cases a
  · exact context_12_21768_196372
  · exact context_12_21769_196467
  · exact context_12_21770_196619
  · exact context_12_21771_196774

theorem selected_cut_06592 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 5443) = some ⟨11, 1, 0, 1736, 5443, 1, 262144⟩ := by
  decide +kernel

theorem context_11_5443_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5443 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 5443 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 5443, 1, 262144⟩
    (by decide) selected_cut_06592

theorem unmarked_context_10_1360_196776 : frontier 11 ⟨196776, by decide⟩
    (prefixCache 10 1360) (prefixPartial 10 1360) = false := by
  decide +kernel

theorem node_context_10_1360_196776 : EJMOriginalGlobalDAGData.nodes 11 ⟨196776, by decide⟩ =
    .split (coordinate 10) (![⟨195839, by decide⟩,⟨196239, by decide⟩,⟨196775, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1360_196776 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1360 ⟨196776, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1360
    ⟨196776, by decide⟩ (by decide) (![⟨195839, by decide⟩,⟨196239, by decide⟩,⟨196775, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_1360_196776 node_context_10_1360_196776
  intro a
  fin_cases a
  · exact context_11_5440_195839
  · exact context_11_5441_196239
  · exact context_11_5442_196775
  · exact context_11_5443_1736

theorem selected_cut_06593 : selected 9 ⟨196820, by decide⟩
    (prefixPartial 12 21776) = some ⟨12, 2, 0, 196820, 21776, 2481, 65536⟩ := by
  decide +kernel

theorem context_12_21776_196820 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21776 ⟨196820, by decide⟩ :=
  accepted_of_selected 12 21776 ⟨196820, by decide⟩ ⟨12, 2, 0, 196820, 21776, 2481, 65536⟩
    (by decide) selected_cut_06593

theorem selected_cut_06594 : selected 9 ⟨196856, by decide⟩
    (prefixPartial 12 21777) = some ⟨12, 2, 0, 196856, 21777, 1933, 65536⟩ := by
  decide +kernel

theorem context_12_21777_196856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21777 ⟨196856, by decide⟩ :=
  accepted_of_selected 12 21777 ⟨196856, by decide⟩ ⟨12, 2, 0, 196856, 21777, 1933, 65536⟩
    (by decide) selected_cut_06594

theorem selected_cut_06595 : selected 8 ⟨196881, by decide⟩
    (prefixPartial 13 87112) = some ⟨13, 2, 0, 196881, 87112, 1905, 16384⟩ := by
  decide +kernel

theorem context_13_87112_196881 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87112 ⟨196881, by decide⟩ :=
  accepted_of_selected 13 87112 ⟨196881, by decide⟩ ⟨13, 2, 0, 196881, 87112, 1905, 16384⟩
    (by decide) selected_cut_06595

theorem selected_cut_06596 : selected 8 ⟨196907, by decide⟩
    (prefixPartial 13 87113) = some ⟨13, 2, 0, 196907, 87113, 1753, 16384⟩ := by
  decide +kernel

theorem context_13_87113_196907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87113 ⟨196907, by decide⟩ :=
  accepted_of_selected 13 87113 ⟨196907, by decide⟩ ⟨13, 2, 0, 196907, 87113, 1753, 16384⟩
    (by decide) selected_cut_06596

theorem selected_cut_06597 : selected 8 ⟨196926, by decide⟩
    (prefixPartial 13 87114) = some ⟨13, 2, 0, 196926, 87114, 1581, 16384⟩ := by
  decide +kernel

theorem context_13_87114_196926 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87114 ⟨196926, by decide⟩ :=
  accepted_of_selected 13 87114 ⟨196926, by decide⟩ ⟨13, 2, 0, 196926, 87114, 1581, 16384⟩
    (by decide) selected_cut_06597

theorem selected_cut_06598 : selected 8 ⟨196933, by decide⟩
    (prefixPartial 13 87115) = some ⟨13, 2, 0, 196933, 87115, 837, 16384⟩ := by
  decide +kernel

theorem context_13_87115_196933 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87115 ⟨196933, by decide⟩ :=
  accepted_of_selected 13 87115 ⟨196933, by decide⟩ ⟨13, 2, 0, 196933, 87115, 837, 16384⟩
    (by decide) selected_cut_06598

theorem unmarked_context_12_21778_196934 : frontier 9 ⟨196934, by decide⟩
    (prefixCache 12 21778) (prefixPartial 12 21778) = false := by
  decide +kernel

theorem node_context_12_21778_196934 : EJMOriginalGlobalDAGData.nodes 9 ⟨196934, by decide⟩ =
    .split (coordinate 12) (![⟨196881, by decide⟩,⟨196907, by decide⟩,⟨196926, by decide⟩,⟨196933, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21778_196934 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21778 ⟨196934, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21778
    ⟨196934, by decide⟩ (by decide) (![⟨196881, by decide⟩,⟨196907, by decide⟩,⟨196926, by decide⟩,⟨196933, by decide⟩]) unmarked_context_12_21778_196934 node_context_12_21778_196934
  intro a
  fin_cases a
  · exact context_13_87112_196881
  · exact context_13_87113_196907
  · exact context_13_87114_196926
  · exact context_13_87115_196933

theorem selected_cut_06599 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 21779) = some ⟨12, 1, 0, 893, 21779, 1, 65536⟩ := by
  decide +kernel

theorem context_12_21779_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21779 ⟨893, by decide⟩ :=
  accepted_of_selected 12 21779 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 21779, 1, 65536⟩
    (by decide) selected_cut_06599

theorem unmarked_context_11_5444_196935 : frontier 10 ⟨196935, by decide⟩
    (prefixCache 11 5444) (prefixPartial 11 5444) = false := by
  decide +kernel

theorem node_context_11_5444_196935 : EJMOriginalGlobalDAGData.nodes 10 ⟨196935, by decide⟩ =
    .split (coordinate 11) (![⟨196820, by decide⟩,⟨196856, by decide⟩,⟨196934, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5444_196935 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5444 ⟨196935, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5444
    ⟨196935, by decide⟩ (by decide) (![⟨196820, by decide⟩,⟨196856, by decide⟩,⟨196934, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_5444_196935 node_context_11_5444_196935
  intro a
  fin_cases a
  · exact context_12_21776_196820
  · exact context_12_21777_196856
  · exact context_12_21778_196934
  · exact context_12_21779_893

theorem selected_cut_06600 : selected 9 ⟨197000, by decide⟩
    (prefixPartial 12 21780) = some ⟨12, 2, 0, 197000, 21780, 3261, 65536⟩ := by
  decide +kernel

theorem context_12_21780_197000 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21780 ⟨197000, by decide⟩ :=
  accepted_of_selected 12 21780 ⟨197000, by decide⟩ ⟨12, 2, 0, 197000, 21780, 3261, 65536⟩
    (by decide) selected_cut_06600

theorem selected_cut_06601 : selected 9 ⟨124308, by decide⟩
    (prefixPartial 12 21781) = some ⟨12, 1, 0, 124308, 21781, 1, 65536⟩ := by
  decide +kernel

theorem context_12_21781_124308 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21781 ⟨124308, by decide⟩ :=
  accepted_of_selected 12 21781 ⟨124308, by decide⟩ ⟨12, 1, 0, 124308, 21781, 1, 65536⟩
    (by decide) selected_cut_06601

theorem selected_cut_06602 : selected 8 ⟨197035, by decide⟩
    (prefixPartial 13 87128) = some ⟨13, 2, 0, 197035, 87128, 2065, 16384⟩ := by
  decide +kernel

theorem context_13_87128_197035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87128 ⟨197035, by decide⟩ :=
  accepted_of_selected 13 87128 ⟨197035, by decide⟩ ⟨13, 2, 0, 197035, 87128, 2065, 16384⟩
    (by decide) selected_cut_06602

theorem selected_cut_06603 : selected 8 ⟨197075, by decide⟩
    (prefixPartial 13 87129) = some ⟨13, 2, 0, 197075, 87129, 2833, 16384⟩ := by
  decide +kernel

theorem context_13_87129_197075 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87129 ⟨197075, by decide⟩ :=
  accepted_of_selected 13 87129 ⟨197075, by decide⟩ ⟨13, 2, 0, 197075, 87129, 2833, 16384⟩
    (by decide) selected_cut_06603

theorem selected_cut_06604 : selected 8 ⟨197095, by decide⟩
    (prefixPartial 13 87130) = some ⟨13, 2, 0, 197095, 87130, 1677, 16384⟩ := by
  decide +kernel

theorem context_13_87130_197095 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87130 ⟨197095, by decide⟩ :=
  accepted_of_selected 13 87130 ⟨197095, by decide⟩ ⟨13, 2, 0, 197095, 87130, 1677, 16384⟩
    (by decide) selected_cut_06604

theorem selected_cut_06605 : selected 8 ⟨197104, by decide⟩
    (prefixPartial 13 87131) = some ⟨13, 2, 0, 197104, 87131, 953, 16384⟩ := by
  decide +kernel

theorem context_13_87131_197104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87131 ⟨197104, by decide⟩ :=
  accepted_of_selected 13 87131 ⟨197104, by decide⟩ ⟨13, 2, 0, 197104, 87131, 953, 16384⟩
    (by decide) selected_cut_06605

theorem unmarked_context_12_21782_197105 : frontier 9 ⟨197105, by decide⟩
    (prefixCache 12 21782) (prefixPartial 12 21782) = false := by
  decide +kernel

theorem node_context_12_21782_197105 : EJMOriginalGlobalDAGData.nodes 9 ⟨197105, by decide⟩ =
    .split (coordinate 12) (![⟨197035, by decide⟩,⟨197075, by decide⟩,⟨197095, by decide⟩,⟨197104, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21782_197105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21782 ⟨197105, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21782
    ⟨197105, by decide⟩ (by decide) (![⟨197035, by decide⟩,⟨197075, by decide⟩,⟨197095, by decide⟩,⟨197104, by decide⟩]) unmarked_context_12_21782_197105 node_context_12_21782_197105
  intro a
  fin_cases a
  · exact context_13_87128_197035
  · exact context_13_87129_197075
  · exact context_13_87130_197095
  · exact context_13_87131_197104

theorem selected_cut_06606 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 21783) = some ⟨12, 1, 0, 893, 21783, 1, 65536⟩ := by
  decide +kernel

theorem context_12_21783_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21783 ⟨893, by decide⟩ :=
  accepted_of_selected 12 21783 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 21783, 1, 65536⟩
    (by decide) selected_cut_06606

theorem unmarked_context_11_5445_197106 : frontier 10 ⟨197106, by decide⟩
    (prefixCache 11 5445) (prefixPartial 11 5445) = false := by
  decide +kernel

theorem node_context_11_5445_197106 : EJMOriginalGlobalDAGData.nodes 10 ⟨197106, by decide⟩ =
    .split (coordinate 11) (![⟨197000, by decide⟩,⟨124308, by decide⟩,⟨197105, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5445_197106 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5445 ⟨197106, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5445
    ⟨197106, by decide⟩ (by decide) (![⟨197000, by decide⟩,⟨124308, by decide⟩,⟨197105, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_5445_197106 node_context_11_5445_197106
  intro a
  fin_cases a
  · exact context_12_21780_197000
  · exact context_12_21781_124308
  · exact context_12_21782_197105
  · exact context_12_21783_893

theorem selected_cut_06607 : selected 8 ⟨197118, by decide⟩
    (prefixPartial 13 87136) = some ⟨13, 2, 0, 197118, 87136, 989, 16384⟩ := by
  decide +kernel

theorem context_13_87136_197118 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87136 ⟨197118, by decide⟩ :=
  accepted_of_selected 13 87136 ⟨197118, by decide⟩ ⟨13, 2, 0, 197118, 87136, 989, 16384⟩
    (by decide) selected_cut_06607

theorem selected_cut_06608 : selected 8 ⟨197142, by decide⟩
    (prefixPartial 13 87137) = some ⟨13, 2, 0, 197142, 87137, 1565, 16384⟩ := by
  decide +kernel

theorem context_13_87137_197142 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87137 ⟨197142, by decide⟩ :=
  accepted_of_selected 13 87137 ⟨197142, by decide⟩ ⟨13, 2, 0, 197142, 87137, 1565, 16384⟩
    (by decide) selected_cut_06608

theorem selected_cut_06609 : selected 8 ⟨197162, by decide⟩
    (prefixPartial 13 87138) = some ⟨13, 2, 0, 197162, 87138, 1393, 16384⟩ := by
  decide +kernel

theorem context_13_87138_197162 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87138 ⟨197162, by decide⟩ :=
  accepted_of_selected 13 87138 ⟨197162, by decide⟩ ⟨13, 2, 0, 197162, 87138, 1393, 16384⟩
    (by decide) selected_cut_06609

theorem selected_cut_06610 : selected 8 ⟨197172, by decide⟩
    (prefixPartial 13 87139) = some ⟨13, 2, 0, 197172, 87139, 729, 16384⟩ := by
  decide +kernel

theorem context_13_87139_197172 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87139 ⟨197172, by decide⟩ :=
  accepted_of_selected 13 87139 ⟨197172, by decide⟩ ⟨13, 2, 0, 197172, 87139, 729, 16384⟩
    (by decide) selected_cut_06610

theorem unmarked_context_12_21784_197173 : frontier 9 ⟨197173, by decide⟩
    (prefixCache 12 21784) (prefixPartial 12 21784) = false := by
  decide +kernel

theorem node_context_12_21784_197173 : EJMOriginalGlobalDAGData.nodes 9 ⟨197173, by decide⟩ =
    .split (coordinate 12) (![⟨197118, by decide⟩,⟨197142, by decide⟩,⟨197162, by decide⟩,⟨197172, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21784_197173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21784 ⟨197173, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21784
    ⟨197173, by decide⟩ (by decide) (![⟨197118, by decide⟩,⟨197142, by decide⟩,⟨197162, by decide⟩,⟨197172, by decide⟩]) unmarked_context_12_21784_197173 node_context_12_21784_197173
  intro a
  fin_cases a
  · exact context_13_87136_197118
  · exact context_13_87137_197142
  · exact context_13_87138_197162
  · exact context_13_87139_197172

theorem selected_cut_06611 : selected 9 ⟨197232, by decide⟩
    (prefixPartial 12 21785) = some ⟨12, 2, 0, 197232, 21785, 3477, 65536⟩ := by
  decide +kernel

theorem context_12_21785_197232 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21785 ⟨197232, by decide⟩ :=
  accepted_of_selected 12 21785 ⟨197232, by decide⟩ ⟨12, 2, 0, 197232, 21785, 3477, 65536⟩
    (by decide) selected_cut_06611

theorem selected_cut_06612 : selected 8 ⟨197256, by decide⟩
    (prefixPartial 13 87144) = some ⟨13, 2, 0, 197256, 87144, 1425, 16384⟩ := by
  decide +kernel

theorem context_13_87144_197256 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87144 ⟨197256, by decide⟩ :=
  accepted_of_selected 13 87144 ⟨197256, by decide⟩ ⟨13, 2, 0, 197256, 87144, 1425, 16384⟩
    (by decide) selected_cut_06612

theorem selected_cut_06613 : selected 8 ⟨197282, by decide⟩
    (prefixPartial 13 87145) = some ⟨13, 2, 0, 197282, 87145, 1757, 16384⟩ := by
  decide +kernel

theorem context_13_87145_197282 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87145 ⟨197282, by decide⟩ :=
  accepted_of_selected 13 87145 ⟨197282, by decide⟩ ⟨13, 2, 0, 197282, 87145, 1757, 16384⟩
    (by decide) selected_cut_06613

theorem selected_cut_06614 : selected 8 ⟨197303, by decide⟩
    (prefixPartial 13 87146) = some ⟨13, 2, 0, 197303, 87146, 1221, 16384⟩ := by
  decide +kernel

theorem context_13_87146_197303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87146 ⟨197303, by decide⟩ :=
  accepted_of_selected 13 87146 ⟨197303, by decide⟩ ⟨13, 2, 0, 197303, 87146, 1221, 16384⟩
    (by decide) selected_cut_06614

theorem selected_cut_06615 : selected 8 ⟨197312, by decide⟩
    (prefixPartial 13 87147) = some ⟨13, 2, 0, 197312, 87147, 793, 16384⟩ := by
  decide +kernel

theorem context_13_87147_197312 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87147 ⟨197312, by decide⟩ :=
  accepted_of_selected 13 87147 ⟨197312, by decide⟩ ⟨13, 2, 0, 197312, 87147, 793, 16384⟩
    (by decide) selected_cut_06615

theorem unmarked_context_12_21786_197313 : frontier 9 ⟨197313, by decide⟩
    (prefixCache 12 21786) (prefixPartial 12 21786) = false := by
  decide +kernel

theorem node_context_12_21786_197313 : EJMOriginalGlobalDAGData.nodes 9 ⟨197313, by decide⟩ =
    .split (coordinate 12) (![⟨197256, by decide⟩,⟨197282, by decide⟩,⟨197303, by decide⟩,⟨197312, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21786_197313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21786 ⟨197313, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21786
    ⟨197313, by decide⟩ (by decide) (![⟨197256, by decide⟩,⟨197282, by decide⟩,⟨197303, by decide⟩,⟨197312, by decide⟩]) unmarked_context_12_21786_197313 node_context_12_21786_197313
  intro a
  fin_cases a
  · exact context_13_87144_197256
  · exact context_13_87145_197282
  · exact context_13_87146_197303
  · exact context_13_87147_197312

theorem selected_cut_06616 : selected 8 ⟨197335, by decide⟩
    (prefixPartial 13 87148) = some ⟨13, 2, 0, 197335, 87148, 1537, 16384⟩ := by
  decide +kernel

theorem context_13_87148_197335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87148 ⟨197335, by decide⟩ :=
  accepted_of_selected 13 87148 ⟨197335, by decide⟩ ⟨13, 2, 0, 197335, 87148, 1537, 16384⟩
    (by decide) selected_cut_06616

theorem selected_cut_06617 : selected 8 ⟨197362, by decide⟩
    (prefixPartial 13 87149) = some ⟨13, 2, 0, 197362, 87149, 1917, 16384⟩ := by
  decide +kernel

theorem context_13_87149_197362 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87149 ⟨197362, by decide⟩ :=
  accepted_of_selected 13 87149 ⟨197362, by decide⟩ ⟨13, 2, 0, 197362, 87149, 1917, 16384⟩
    (by decide) selected_cut_06617

theorem selected_cut_06618 : selected 8 ⟨197382, by decide⟩
    (prefixPartial 13 87150) = some ⟨13, 2, 0, 197382, 87150, 1361, 16384⟩ := by
  decide +kernel

theorem context_13_87150_197382 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87150 ⟨197382, by decide⟩ :=
  accepted_of_selected 13 87150 ⟨197382, by decide⟩ ⟨13, 2, 0, 197382, 87150, 1361, 16384⟩
    (by decide) selected_cut_06618

theorem selected_cut_06619 : selected 8 ⟨197390, by decide⟩
    (prefixPartial 13 87151) = some ⟨13, 2, 0, 197390, 87151, 769, 16384⟩ := by
  decide +kernel

theorem context_13_87151_197390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87151 ⟨197390, by decide⟩ :=
  accepted_of_selected 13 87151 ⟨197390, by decide⟩ ⟨13, 2, 0, 197390, 87151, 769, 16384⟩
    (by decide) selected_cut_06619

theorem unmarked_context_12_21787_197391 : frontier 9 ⟨197391, by decide⟩
    (prefixCache 12 21787) (prefixPartial 12 21787) = false := by
  decide +kernel

theorem node_context_12_21787_197391 : EJMOriginalGlobalDAGData.nodes 9 ⟨197391, by decide⟩ =
    .split (coordinate 12) (![⟨197335, by decide⟩,⟨197362, by decide⟩,⟨197382, by decide⟩,⟨197390, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21787_197391 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21787 ⟨197391, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21787
    ⟨197391, by decide⟩ (by decide) (![⟨197335, by decide⟩,⟨197362, by decide⟩,⟨197382, by decide⟩,⟨197390, by decide⟩]) unmarked_context_12_21787_197391 node_context_12_21787_197391
  intro a
  fin_cases a
  · exact context_13_87148_197335
  · exact context_13_87149_197362
  · exact context_13_87150_197382
  · exact context_13_87151_197390

theorem unmarked_context_11_5446_197392 : frontier 10 ⟨197392, by decide⟩
    (prefixCache 11 5446) (prefixPartial 11 5446) = false := by
  decide +kernel

theorem node_context_11_5446_197392 : EJMOriginalGlobalDAGData.nodes 10 ⟨197392, by decide⟩ =
    .split (coordinate 11) (![⟨197173, by decide⟩,⟨197232, by decide⟩,⟨197313, by decide⟩,⟨197391, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5446_197392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5446 ⟨197392, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5446
    ⟨197392, by decide⟩ (by decide) (![⟨197173, by decide⟩,⟨197232, by decide⟩,⟨197313, by decide⟩,⟨197391, by decide⟩]) unmarked_context_11_5446_197392 node_context_11_5446_197392
  intro a
  fin_cases a
  · exact context_12_21784_197173
  · exact context_12_21785_197232
  · exact context_12_21786_197313
  · exact context_12_21787_197391

theorem selected_cut_06620 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 5447) = some ⟨11, 1, 0, 1736, 5447, 1, 262144⟩ := by
  decide +kernel

theorem context_11_5447_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5447 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 5447 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 5447, 1, 262144⟩
    (by decide) selected_cut_06620

theorem unmarked_context_10_1361_197393 : frontier 11 ⟨197393, by decide⟩
    (prefixCache 10 1361) (prefixPartial 10 1361) = false := by
  decide +kernel

theorem node_context_10_1361_197393 : EJMOriginalGlobalDAGData.nodes 11 ⟨197393, by decide⟩ =
    .split (coordinate 10) (![⟨196935, by decide⟩,⟨197106, by decide⟩,⟨197392, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1361_197393 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1361 ⟨197393, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1361
    ⟨197393, by decide⟩ (by decide) (![⟨196935, by decide⟩,⟨197106, by decide⟩,⟨197392, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_1361_197393 node_context_10_1361_197393
  intro a
  fin_cases a
  · exact context_11_5444_196935
  · exact context_11_5445_197106
  · exact context_11_5446_197392
  · exact context_11_5447_1736

theorem selected_cut_06621 : selected 8 ⟨197408, by decide⟩
    (prefixPartial 13 87168) = some ⟨13, 2, 0, 197408, 87168, 1209, 16384⟩ := by
  decide +kernel

theorem context_13_87168_197408 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87168 ⟨197408, by decide⟩ :=
  accepted_of_selected 13 87168 ⟨197408, by decide⟩ ⟨13, 2, 0, 197408, 87168, 1209, 16384⟩
    (by decide) selected_cut_06621

theorem selected_cut_06622 : selected 8 ⟨197428, by decide⟩
    (prefixPartial 13 87169) = some ⟨13, 2, 0, 197428, 87169, 1613, 16384⟩ := by
  decide +kernel

theorem context_13_87169_197428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87169 ⟨197428, by decide⟩ :=
  accepted_of_selected 13 87169 ⟨197428, by decide⟩ ⟨13, 2, 0, 197428, 87169, 1613, 16384⟩
    (by decide) selected_cut_06622

theorem selected_cut_06623 : selected 8 ⟨197448, by decide⟩
    (prefixPartial 13 87170) = some ⟨13, 2, 0, 197448, 87170, 1393, 16384⟩ := by
  decide +kernel

theorem context_13_87170_197448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87170 ⟨197448, by decide⟩ :=
  accepted_of_selected 13 87170 ⟨197448, by decide⟩ ⟨13, 2, 0, 197448, 87170, 1393, 16384⟩
    (by decide) selected_cut_06623

theorem selected_cut_06624 : selected 8 ⟨197456, by decide⟩
    (prefixPartial 13 87171) = some ⟨13, 2, 0, 197456, 87171, 905, 16384⟩ := by
  decide +kernel

theorem context_13_87171_197456 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87171 ⟨197456, by decide⟩ :=
  accepted_of_selected 13 87171 ⟨197456, by decide⟩ ⟨13, 2, 0, 197456, 87171, 905, 16384⟩
    (by decide) selected_cut_06624

theorem unmarked_context_12_21792_197457 : frontier 9 ⟨197457, by decide⟩
    (prefixCache 12 21792) (prefixPartial 12 21792) = false := by
  decide +kernel

theorem node_context_12_21792_197457 : EJMOriginalGlobalDAGData.nodes 9 ⟨197457, by decide⟩ =
    .split (coordinate 12) (![⟨197408, by decide⟩,⟨197428, by decide⟩,⟨197448, by decide⟩,⟨197456, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21792_197457 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21792 ⟨197457, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21792
    ⟨197457, by decide⟩ (by decide) (![⟨197408, by decide⟩,⟨197428, by decide⟩,⟨197448, by decide⟩,⟨197456, by decide⟩]) unmarked_context_12_21792_197457 node_context_12_21792_197457
  intro a
  fin_cases a
  · exact context_13_87168_197408
  · exact context_13_87169_197428
  · exact context_13_87170_197448
  · exact context_13_87171_197456

theorem selected_cut_06625 : selected 8 ⟨197474, by decide⟩
    (prefixPartial 13 87172) = some ⟨13, 2, 0, 197474, 87172, 1181, 16384⟩ := by
  decide +kernel

theorem context_13_87172_197474 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87172 ⟨197474, by decide⟩ :=
  accepted_of_selected 13 87172 ⟨197474, by decide⟩ ⟨13, 2, 0, 197474, 87172, 1181, 16384⟩
    (by decide) selected_cut_06625

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
