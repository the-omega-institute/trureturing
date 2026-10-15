/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover208
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_20068 : selected 8 ⟨513269, by decide⟩
    (prefixPartial 13 290095) = some ⟨13, 2, 0, 513269, 290095, 865, 16384⟩ := by
  decide +kernel

theorem context_13_290095_513269 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290095 ⟨513269, by decide⟩ :=
  accepted_of_selected 13 290095 ⟨513269, by decide⟩ ⟨13, 2, 0, 513269, 290095, 865, 16384⟩
    (by decide) selected_cut_20068

theorem unmarked_context_12_72523_513270 : frontier 9 ⟨513270, by decide⟩
    (prefixCache 12 72523) (prefixPartial 12 72523) = false := by
  decide +kernel

theorem node_context_12_72523_513270 : EJMOriginalGlobalDAGData.nodes 9 ⟨513270, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨513236, by decide⟩,⟨513256, by decide⟩,⟨513269, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72523_513270 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72523 ⟨513270, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72523
    ⟨513270, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨513236, by decide⟩,⟨513256, by decide⟩,⟨513269, by decide⟩]) unmarked_context_12_72523_513270 node_context_12_72523_513270
  intro a
  fin_cases a
  · exact context_13_290092_3444
  · exact context_13_290093_513236
  · exact context_13_290094_513256
  · exact context_13_290095_513269

theorem unmarked_context_11_18130_513271 : frontier 10 ⟨513271, by decide⟩
    (prefixCache 11 18130) (prefixPartial 11 18130) = false := by
  decide +kernel

theorem node_context_11_18130_513271 : EJMOriginalGlobalDAGData.nodes 10 ⟨513271, by decide⟩ =
    .split (coordinate 11) (![⟨513110, by decide⟩,⟨513156, by decide⟩,⟨513214, by decide⟩,⟨513270, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18130_513271 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18130 ⟨513271, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18130
    ⟨513271, by decide⟩ (by decide) (![⟨513110, by decide⟩,⟨513156, by decide⟩,⟨513214, by decide⟩,⟨513270, by decide⟩]) unmarked_context_11_18130_513271 node_context_11_18130_513271
  intro a
  fin_cases a
  · exact context_12_72520_513110
  · exact context_12_72521_513156
  · exact context_12_72522_513214
  · exact context_12_72523_513270

theorem selected_cut_20069 : selected 9 ⟨513322, by decide⟩
    (prefixPartial 12 72524) = some ⟨12, 2, 0, 513322, 72524, 3785, 65536⟩ := by
  decide +kernel

theorem context_12_72524_513322 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72524 ⟨513322, by decide⟩ :=
  accepted_of_selected 12 72524 ⟨513322, by decide⟩ ⟨12, 2, 0, 513322, 72524, 3785, 65536⟩
    (by decide) selected_cut_20069

theorem selected_cut_20070 : selected 9 ⟨513366, by decide⟩
    (prefixPartial 12 72525) = some ⟨12, 2, 0, 513366, 72525, 3809, 65536⟩ := by
  decide +kernel

theorem context_12_72525_513366 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72525 ⟨513366, by decide⟩ :=
  accepted_of_selected 12 72525 ⟨513366, by decide⟩ ⟨12, 2, 0, 513366, 72525, 3809, 65536⟩
    (by decide) selected_cut_20070

theorem selected_cut_20071 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 290104) = some ⟨13, 1, 0, 3444, 290104, 1, 16384⟩ := by
  decide +kernel

theorem context_13_290104_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290104 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 290104 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 290104, 1, 16384⟩
    (by decide) selected_cut_20071

theorem selected_cut_20072 : selected 8 ⟨513404, by decide⟩
    (prefixPartial 13 290105) = some ⟨13, 2, 0, 513404, 290105, 2233, 16384⟩ := by
  decide +kernel

theorem context_13_290105_513404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290105 ⟨513404, by decide⟩ :=
  accepted_of_selected 13 290105 ⟨513404, by decide⟩ ⟨13, 2, 0, 513404, 290105, 2233, 16384⟩
    (by decide) selected_cut_20072

theorem selected_cut_20073 : selected 8 ⟨513423, by decide⟩
    (prefixPartial 13 290106) = some ⟨13, 2, 0, 513423, 290106, 1605, 16384⟩ := by
  decide +kernel

theorem context_13_290106_513423 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290106 ⟨513423, by decide⟩ :=
  accepted_of_selected 13 290106 ⟨513423, by decide⟩ ⟨13, 2, 0, 513423, 290106, 1605, 16384⟩
    (by decide) selected_cut_20073

theorem selected_cut_20074 : selected 8 ⟨513430, by decide⟩
    (prefixPartial 13 290107) = some ⟨13, 2, 0, 513430, 290107, 805, 16384⟩ := by
  decide +kernel

theorem context_13_290107_513430 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290107 ⟨513430, by decide⟩ :=
  accepted_of_selected 13 290107 ⟨513430, by decide⟩ ⟨13, 2, 0, 513430, 290107, 805, 16384⟩
    (by decide) selected_cut_20074

theorem unmarked_context_12_72526_513431 : frontier 9 ⟨513431, by decide⟩
    (prefixCache 12 72526) (prefixPartial 12 72526) = false := by
  decide +kernel

theorem node_context_12_72526_513431 : EJMOriginalGlobalDAGData.nodes 9 ⟨513431, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨513404, by decide⟩,⟨513423, by decide⟩,⟨513430, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72526_513431 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72526 ⟨513431, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72526
    ⟨513431, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨513404, by decide⟩,⟨513423, by decide⟩,⟨513430, by decide⟩]) unmarked_context_12_72526_513431 node_context_12_72526_513431
  intro a
  fin_cases a
  · exact context_13_290104_3444
  · exact context_13_290105_513404
  · exact context_13_290106_513423
  · exact context_13_290107_513430

theorem selected_cut_20075 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 290108) = some ⟨13, 1, 0, 3444, 290108, 1, 16384⟩ := by
  decide +kernel

theorem context_13_290108_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290108 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 290108 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 290108, 1, 16384⟩
    (by decide) selected_cut_20075

theorem selected_cut_20076 : selected 8 ⟨513492, by decide⟩
    (prefixPartial 13 290109) = some ⟨13, 2, 0, 513492, 290109, 3165, 16384⟩ := by
  decide +kernel

theorem context_13_290109_513492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290109 ⟨513492, by decide⟩ :=
  accepted_of_selected 13 290109 ⟨513492, by decide⟩ ⟨13, 2, 0, 513492, 290109, 3165, 16384⟩
    (by decide) selected_cut_20076

theorem selected_cut_20077 : selected 8 ⟨513545, by decide⟩
    (prefixPartial 13 290110) = some ⟨13, 2, 0, 513545, 290110, 2657, 16384⟩ := by
  decide +kernel

theorem context_13_290110_513545 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290110 ⟨513545, by decide⟩ :=
  accepted_of_selected 13 290110 ⟨513545, by decide⟩ ⟨13, 2, 0, 513545, 290110, 2657, 16384⟩
    (by decide) selected_cut_20077

theorem selected_cut_20078 : selected 8 ⟨513577, by decide⟩
    (prefixPartial 13 290111) = some ⟨13, 2, 0, 513577, 290111, 1253, 16384⟩ := by
  decide +kernel

theorem context_13_290111_513577 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290111 ⟨513577, by decide⟩ :=
  accepted_of_selected 13 290111 ⟨513577, by decide⟩ ⟨13, 2, 0, 513577, 290111, 1253, 16384⟩
    (by decide) selected_cut_20078

theorem unmarked_context_12_72527_513578 : frontier 9 ⟨513578, by decide⟩
    (prefixCache 12 72527) (prefixPartial 12 72527) = false := by
  decide +kernel

theorem node_context_12_72527_513578 : EJMOriginalGlobalDAGData.nodes 9 ⟨513578, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨513492, by decide⟩,⟨513545, by decide⟩,⟨513577, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72527_513578 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72527 ⟨513578, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72527
    ⟨513578, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨513492, by decide⟩,⟨513545, by decide⟩,⟨513577, by decide⟩]) unmarked_context_12_72527_513578 node_context_12_72527_513578
  intro a
  fin_cases a
  · exact context_13_290108_3444
  · exact context_13_290109_513492
  · exact context_13_290110_513545
  · exact context_13_290111_513577

theorem unmarked_context_11_18131_513579 : frontier 10 ⟨513579, by decide⟩
    (prefixCache 11 18131) (prefixPartial 11 18131) = false := by
  decide +kernel

theorem node_context_11_18131_513579 : EJMOriginalGlobalDAGData.nodes 10 ⟨513579, by decide⟩ =
    .split (coordinate 11) (![⟨513322, by decide⟩,⟨513366, by decide⟩,⟨513431, by decide⟩,⟨513578, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18131_513579 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18131 ⟨513579, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18131
    ⟨513579, by decide⟩ (by decide) (![⟨513322, by decide⟩,⟨513366, by decide⟩,⟨513431, by decide⟩,⟨513578, by decide⟩]) unmarked_context_11_18131_513579 node_context_11_18131_513579
  intro a
  fin_cases a
  · exact context_12_72524_513322
  · exact context_12_72525_513366
  · exact context_12_72526_513431
  · exact context_12_72527_513578

theorem unmarked_context_10_4532_513580 : frontier 11 ⟨513580, by decide⟩
    (prefixCache 10 4532) (prefixPartial 10 4532) = false := by
  decide +kernel

theorem node_context_10_4532_513580 : EJMOriginalGlobalDAGData.nodes 11 ⟨513580, by decide⟩ =
    .split (coordinate 10) (![⟨512800, by decide⟩,⟨513062, by decide⟩,⟨513271, by decide⟩,⟨513579, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4532_513580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4532 ⟨513580, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4532
    ⟨513580, by decide⟩ (by decide) (![⟨512800, by decide⟩,⟨513062, by decide⟩,⟨513271, by decide⟩,⟨513579, by decide⟩]) unmarked_context_10_4532_513580 node_context_10_4532_513580
  intro a
  fin_cases a
  · exact context_11_18128_512800
  · exact context_11_18129_513062
  · exact context_11_18130_513271
  · exact context_11_18131_513579

theorem selected_cut_20079 : selected 9 ⟨513625, by decide⟩
    (prefixPartial 12 72528) = some ⟨12, 2, 0, 513625, 72528, 3401, 65536⟩ := by
  decide +kernel

theorem context_12_72528_513625 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72528 ⟨513625, by decide⟩ :=
  accepted_of_selected 12 72528 ⟨513625, by decide⟩ ⟨12, 2, 0, 513625, 72528, 3401, 65536⟩
    (by decide) selected_cut_20079

theorem selected_cut_20080 : selected 9 ⟨513676, by decide⟩
    (prefixPartial 12 72529) = some ⟨12, 2, 0, 513676, 72529, 3745, 65536⟩ := by
  decide +kernel

theorem context_12_72529_513676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72529 ⟨513676, by decide⟩ :=
  accepted_of_selected 12 72529 ⟨513676, by decide⟩ ⟨12, 2, 0, 513676, 72529, 3745, 65536⟩
    (by decide) selected_cut_20080

theorem selected_cut_20081 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 290120) = some ⟨13, 1, 0, 3444, 290120, 1, 16384⟩ := by
  decide +kernel

theorem context_13_290120_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290120 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 290120 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 290120, 1, 16384⟩
    (by decide) selected_cut_20081

theorem selected_cut_20082 : selected 8 ⟨513713, by decide⟩
    (prefixPartial 13 290121) = some ⟨13, 2, 0, 513713, 290121, 2273, 16384⟩ := by
  decide +kernel

theorem context_13_290121_513713 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290121 ⟨513713, by decide⟩ :=
  accepted_of_selected 13 290121 ⟨513713, by decide⟩ ⟨13, 2, 0, 513713, 290121, 2273, 16384⟩
    (by decide) selected_cut_20082

theorem selected_cut_20083 : selected 8 ⟨513740, by decide⟩
    (prefixPartial 13 290122) = some ⟨13, 2, 0, 513740, 290122, 1629, 16384⟩ := by
  decide +kernel

theorem context_13_290122_513740 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290122 ⟨513740, by decide⟩ :=
  accepted_of_selected 13 290122 ⟨513740, by decide⟩ ⟨13, 2, 0, 513740, 290122, 1629, 16384⟩
    (by decide) selected_cut_20083

theorem selected_cut_20084 : selected 8 ⟨513746, by decide⟩
    (prefixPartial 13 290123) = some ⟨13, 2, 0, 513746, 290123, 717, 16384⟩ := by
  decide +kernel

theorem context_13_290123_513746 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290123 ⟨513746, by decide⟩ :=
  accepted_of_selected 13 290123 ⟨513746, by decide⟩ ⟨13, 2, 0, 513746, 290123, 717, 16384⟩
    (by decide) selected_cut_20084

theorem unmarked_context_12_72530_513747 : frontier 9 ⟨513747, by decide⟩
    (prefixCache 12 72530) (prefixPartial 12 72530) = false := by
  decide +kernel

theorem node_context_12_72530_513747 : EJMOriginalGlobalDAGData.nodes 9 ⟨513747, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨513713, by decide⟩,⟨513740, by decide⟩,⟨513746, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72530_513747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72530 ⟨513747, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72530
    ⟨513747, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨513713, by decide⟩,⟨513740, by decide⟩,⟨513746, by decide⟩]) unmarked_context_12_72530_513747 node_context_12_72530_513747
  intro a
  fin_cases a
  · exact context_13_290120_3444
  · exact context_13_290121_513713
  · exact context_13_290122_513740
  · exact context_13_290123_513746

theorem selected_cut_20085 : selected 9 ⟨513797, by decide⟩
    (prefixPartial 12 72531) = some ⟨12, 2, 0, 513797, 72531, 4021, 65536⟩ := by
  decide +kernel

theorem context_12_72531_513797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72531 ⟨513797, by decide⟩ :=
  accepted_of_selected 12 72531 ⟨513797, by decide⟩ ⟨12, 2, 0, 513797, 72531, 4021, 65536⟩
    (by decide) selected_cut_20085

theorem unmarked_context_11_18132_513798 : frontier 10 ⟨513798, by decide⟩
    (prefixCache 11 18132) (prefixPartial 11 18132) = false := by
  decide +kernel

theorem node_context_11_18132_513798 : EJMOriginalGlobalDAGData.nodes 10 ⟨513798, by decide⟩ =
    .split (coordinate 11) (![⟨513625, by decide⟩,⟨513676, by decide⟩,⟨513747, by decide⟩,⟨513797, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18132_513798 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18132 ⟨513798, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18132
    ⟨513798, by decide⟩ (by decide) (![⟨513625, by decide⟩,⟨513676, by decide⟩,⟨513747, by decide⟩,⟨513797, by decide⟩]) unmarked_context_11_18132_513798 node_context_11_18132_513798
  intro a
  fin_cases a
  · exact context_12_72528_513625
  · exact context_12_72529_513676
  · exact context_12_72530_513747
  · exact context_12_72531_513797

theorem selected_cut_20086 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 290128) = some ⟨13, 1, 0, 3444, 290128, 1, 16384⟩ := by
  decide +kernel

theorem context_13_290128_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290128 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 290128 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 290128, 1, 16384⟩
    (by decide) selected_cut_20086

theorem selected_cut_20087 : selected 8 ⟨513823, by decide⟩
    (prefixPartial 13 290129) = some ⟨13, 2, 0, 513823, 290129, 1781, 16384⟩ := by
  decide +kernel

theorem context_13_290129_513823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290129 ⟨513823, by decide⟩ :=
  accepted_of_selected 13 290129 ⟨513823, by decide⟩ ⟨13, 2, 0, 513823, 290129, 1781, 16384⟩
    (by decide) selected_cut_20087

theorem selected_cut_20088 : selected 8 ⟨513843, by decide⟩
    (prefixPartial 13 290130) = some ⟨13, 2, 0, 513843, 290130, 1585, 16384⟩ := by
  decide +kernel

theorem context_13_290130_513843 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290130 ⟨513843, by decide⟩ :=
  accepted_of_selected 13 290130 ⟨513843, by decide⟩ ⟨13, 2, 0, 513843, 290130, 1585, 16384⟩
    (by decide) selected_cut_20088

theorem selected_cut_20089 : selected 8 ⟨513849, by decide⟩
    (prefixPartial 13 290131) = some ⟨13, 2, 0, 513849, 290131, 845, 16384⟩ := by
  decide +kernel

theorem context_13_290131_513849 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290131 ⟨513849, by decide⟩ :=
  accepted_of_selected 13 290131 ⟨513849, by decide⟩ ⟨13, 2, 0, 513849, 290131, 845, 16384⟩
    (by decide) selected_cut_20089

theorem unmarked_context_12_72532_513850 : frontier 9 ⟨513850, by decide⟩
    (prefixCache 12 72532) (prefixPartial 12 72532) = false := by
  decide +kernel

theorem node_context_12_72532_513850 : EJMOriginalGlobalDAGData.nodes 9 ⟨513850, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨513823, by decide⟩,⟨513843, by decide⟩,⟨513849, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72532_513850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72532 ⟨513850, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72532
    ⟨513850, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨513823, by decide⟩,⟨513843, by decide⟩,⟨513849, by decide⟩]) unmarked_context_12_72532_513850 node_context_12_72532_513850
  intro a
  fin_cases a
  · exact context_13_290128_3444
  · exact context_13_290129_513823
  · exact context_13_290130_513843
  · exact context_13_290131_513849

theorem selected_cut_20090 : selected 9 ⟨513899, by decide⟩
    (prefixPartial 12 72533) = some ⟨12, 2, 0, 513899, 72533, 3773, 65536⟩ := by
  decide +kernel

theorem context_12_72533_513899 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72533 ⟨513899, by decide⟩ :=
  accepted_of_selected 12 72533 ⟨513899, by decide⟩ ⟨12, 2, 0, 513899, 72533, 3773, 65536⟩
    (by decide) selected_cut_20090

theorem selected_cut_20091 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 290136) = some ⟨13, 1, 0, 3444, 290136, 1, 16384⟩ := by
  decide +kernel

theorem context_13_290136_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290136 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 290136 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 290136, 1, 16384⟩
    (by decide) selected_cut_20091

theorem selected_cut_20092 : selected 8 ⟨513938, by decide⟩
    (prefixPartial 13 290137) = some ⟨13, 2, 0, 513938, 290137, 2205, 16384⟩ := by
  decide +kernel

theorem context_13_290137_513938 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290137 ⟨513938, by decide⟩ :=
  accepted_of_selected 13 290137 ⟨513938, by decide⟩ ⟨13, 2, 0, 513938, 290137, 2205, 16384⟩
    (by decide) selected_cut_20092

theorem selected_cut_20093 : selected 8 ⟨513968, by decide⟩
    (prefixPartial 13 290138) = some ⟨13, 2, 0, 513968, 290138, 1909, 16384⟩ := by
  decide +kernel

theorem context_13_290138_513968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290138 ⟨513968, by decide⟩ :=
  accepted_of_selected 13 290138 ⟨513968, by decide⟩ ⟨13, 2, 0, 513968, 290138, 1909, 16384⟩
    (by decide) selected_cut_20093

theorem selected_cut_20094 : selected 8 ⟨513979, by decide⟩
    (prefixPartial 13 290139) = some ⟨13, 2, 0, 513979, 290139, 865, 16384⟩ := by
  decide +kernel

theorem context_13_290139_513979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290139 ⟨513979, by decide⟩ :=
  accepted_of_selected 13 290139 ⟨513979, by decide⟩ ⟨13, 2, 0, 513979, 290139, 865, 16384⟩
    (by decide) selected_cut_20094

theorem unmarked_context_12_72534_513980 : frontier 9 ⟨513980, by decide⟩
    (prefixCache 12 72534) (prefixPartial 12 72534) = false := by
  decide +kernel

theorem node_context_12_72534_513980 : EJMOriginalGlobalDAGData.nodes 9 ⟨513980, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨513938, by decide⟩,⟨513968, by decide⟩,⟨513979, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72534_513980 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72534 ⟨513980, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72534
    ⟨513980, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨513938, by decide⟩,⟨513968, by decide⟩,⟨513979, by decide⟩]) unmarked_context_12_72534_513980 node_context_12_72534_513980
  intro a
  fin_cases a
  · exact context_13_290136_3444
  · exact context_13_290137_513938
  · exact context_13_290138_513968
  · exact context_13_290139_513979

theorem selected_cut_20095 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 290140) = some ⟨13, 1, 0, 3444, 290140, 1, 16384⟩ := by
  decide +kernel

theorem context_13_290140_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290140 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 290140 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 290140, 1, 16384⟩
    (by decide) selected_cut_20095

theorem selected_cut_20096 : selected 8 ⟨514006, by decide⟩
    (prefixPartial 13 290141) = some ⟨13, 2, 0, 514006, 290141, 1885, 16384⟩ := by
  decide +kernel

theorem context_13_290141_514006 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290141 ⟨514006, by decide⟩ :=
  accepted_of_selected 13 290141 ⟨514006, by decide⟩ ⟨13, 2, 0, 514006, 290141, 1885, 16384⟩
    (by decide) selected_cut_20096

theorem selected_cut_20097 : selected 8 ⟨514026, by decide⟩
    (prefixPartial 13 290142) = some ⟨13, 2, 0, 514026, 290142, 1793, 16384⟩ := by
  decide +kernel

theorem context_13_290142_514026 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290142 ⟨514026, by decide⟩ :=
  accepted_of_selected 13 290142 ⟨514026, by decide⟩ ⟨13, 2, 0, 514026, 290142, 1793, 16384⟩
    (by decide) selected_cut_20097

theorem selected_cut_20098 : selected 8 ⟨514031, by decide⟩
    (prefixPartial 13 290143) = some ⟨13, 2, 0, 514031, 290143, 725, 16384⟩ := by
  decide +kernel

theorem context_13_290143_514031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290143 ⟨514031, by decide⟩ :=
  accepted_of_selected 13 290143 ⟨514031, by decide⟩ ⟨13, 2, 0, 514031, 290143, 725, 16384⟩
    (by decide) selected_cut_20098

theorem unmarked_context_12_72535_514032 : frontier 9 ⟨514032, by decide⟩
    (prefixCache 12 72535) (prefixPartial 12 72535) = false := by
  decide +kernel

theorem node_context_12_72535_514032 : EJMOriginalGlobalDAGData.nodes 9 ⟨514032, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨514006, by decide⟩,⟨514026, by decide⟩,⟨514031, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72535_514032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72535 ⟨514032, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72535
    ⟨514032, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨514006, by decide⟩,⟨514026, by decide⟩,⟨514031, by decide⟩]) unmarked_context_12_72535_514032 node_context_12_72535_514032
  intro a
  fin_cases a
  · exact context_13_290140_3444
  · exact context_13_290141_514006
  · exact context_13_290142_514026
  · exact context_13_290143_514031

theorem unmarked_context_11_18133_514033 : frontier 10 ⟨514033, by decide⟩
    (prefixCache 11 18133) (prefixPartial 11 18133) = false := by
  decide +kernel

theorem node_context_11_18133_514033 : EJMOriginalGlobalDAGData.nodes 10 ⟨514033, by decide⟩ =
    .split (coordinate 11) (![⟨513850, by decide⟩,⟨513899, by decide⟩,⟨513980, by decide⟩,⟨514032, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18133_514033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18133 ⟨514033, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18133
    ⟨514033, by decide⟩ (by decide) (![⟨513850, by decide⟩,⟨513899, by decide⟩,⟨513980, by decide⟩,⟨514032, by decide⟩]) unmarked_context_11_18133_514033 node_context_11_18133_514033
  intro a
  fin_cases a
  · exact context_12_72532_513850
  · exact context_12_72533_513899
  · exact context_12_72534_513980
  · exact context_12_72535_514032

theorem selected_cut_20099 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 290144) = some ⟨13, 1, 0, 3444, 290144, 1, 16384⟩ := by
  decide +kernel

theorem context_13_290144_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290144 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 290144 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 290144, 1, 16384⟩
    (by decide) selected_cut_20099

theorem selected_cut_20100 : selected 8 ⟨514056, by decide⟩
    (prefixPartial 13 290145) = some ⟨13, 2, 0, 514056, 290145, 1633, 16384⟩ := by
  decide +kernel

theorem context_13_290145_514056 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290145 ⟨514056, by decide⟩ :=
  accepted_of_selected 13 290145 ⟨514056, by decide⟩ ⟨13, 2, 0, 514056, 290145, 1633, 16384⟩
    (by decide) selected_cut_20100

theorem selected_cut_20101 : selected 8 ⟨514077, by decide⟩
    (prefixPartial 13 290146) = some ⟨13, 2, 0, 514077, 290146, 1633, 16384⟩ := by
  decide +kernel

theorem context_13_290146_514077 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290146 ⟨514077, by decide⟩ :=
  accepted_of_selected 13 290146 ⟨514077, by decide⟩ ⟨13, 2, 0, 514077, 290146, 1633, 16384⟩
    (by decide) selected_cut_20101

theorem selected_cut_20102 : selected 8 ⟨514086, by decide⟩
    (prefixPartial 13 290147) = some ⟨13, 2, 0, 514086, 290147, 845, 16384⟩ := by
  decide +kernel

theorem context_13_290147_514086 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290147 ⟨514086, by decide⟩ :=
  accepted_of_selected 13 290147 ⟨514086, by decide⟩ ⟨13, 2, 0, 514086, 290147, 845, 16384⟩
    (by decide) selected_cut_20102

theorem unmarked_context_12_72536_514087 : frontier 9 ⟨514087, by decide⟩
    (prefixCache 12 72536) (prefixPartial 12 72536) = false := by
  decide +kernel

theorem node_context_12_72536_514087 : EJMOriginalGlobalDAGData.nodes 9 ⟨514087, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨514056, by decide⟩,⟨514077, by decide⟩,⟨514086, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72536_514087 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72536 ⟨514087, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72536
    ⟨514087, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨514056, by decide⟩,⟨514077, by decide⟩,⟨514086, by decide⟩]) unmarked_context_12_72536_514087 node_context_12_72536_514087
  intro a
  fin_cases a
  · exact context_13_290144_3444
  · exact context_13_290145_514056
  · exact context_13_290146_514077
  · exact context_13_290147_514086

theorem selected_cut_20103 : selected 9 ⟨514139, by decide⟩
    (prefixPartial 12 72537) = some ⟨12, 2, 0, 514139, 72537, 3921, 65536⟩ := by
  decide +kernel

theorem context_12_72537_514139 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72537 ⟨514139, by decide⟩ :=
  accepted_of_selected 12 72537 ⟨514139, by decide⟩ ⟨12, 2, 0, 514139, 72537, 3921, 65536⟩
    (by decide) selected_cut_20103

theorem selected_cut_20104 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 290152) = some ⟨13, 1, 0, 3444, 290152, 1, 16384⟩ := by
  decide +kernel

theorem context_13_290152_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290152 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 290152 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 290152, 1, 16384⟩
    (by decide) selected_cut_20104

theorem selected_cut_20105 : selected 8 ⟨514171, by decide⟩
    (prefixPartial 13 290153) = some ⟨13, 2, 0, 514171, 290153, 1901, 16384⟩ := by
  decide +kernel

theorem context_13_290153_514171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290153 ⟨514171, by decide⟩ :=
  accepted_of_selected 13 290153 ⟨514171, by decide⟩ ⟨13, 2, 0, 514171, 290153, 1901, 16384⟩
    (by decide) selected_cut_20105

theorem selected_cut_20106 : selected 8 ⟨514194, by decide⟩
    (prefixPartial 13 290154) = some ⟨13, 2, 0, 514194, 290154, 1921, 16384⟩ := by
  decide +kernel

theorem context_13_290154_514194 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290154 ⟨514194, by decide⟩ :=
  accepted_of_selected 13 290154 ⟨514194, by decide⟩ ⟨13, 2, 0, 514194, 290154, 1921, 16384⟩
    (by decide) selected_cut_20106

theorem selected_cut_20107 : selected 8 ⟨514201, by decide⟩
    (prefixPartial 13 290155) = some ⟨13, 2, 0, 514201, 290155, 865, 16384⟩ := by
  decide +kernel

theorem context_13_290155_514201 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290155 ⟨514201, by decide⟩ :=
  accepted_of_selected 13 290155 ⟨514201, by decide⟩ ⟨13, 2, 0, 514201, 290155, 865, 16384⟩
    (by decide) selected_cut_20107

theorem unmarked_context_12_72538_514202 : frontier 9 ⟨514202, by decide⟩
    (prefixCache 12 72538) (prefixPartial 12 72538) = false := by
  decide +kernel

theorem node_context_12_72538_514202 : EJMOriginalGlobalDAGData.nodes 9 ⟨514202, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨514171, by decide⟩,⟨514194, by decide⟩,⟨514201, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72538_514202 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72538 ⟨514202, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72538
    ⟨514202, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨514171, by decide⟩,⟨514194, by decide⟩,⟨514201, by decide⟩]) unmarked_context_12_72538_514202 node_context_12_72538_514202
  intro a
  fin_cases a
  · exact context_13_290152_3444
  · exact context_13_290153_514171
  · exact context_13_290154_514194
  · exact context_13_290155_514201

theorem selected_cut_20108 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 290156) = some ⟨13, 1, 0, 3444, 290156, 1, 16384⟩ := by
  decide +kernel

theorem context_13_290156_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290156 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 290156 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 290156, 1, 16384⟩
    (by decide) selected_cut_20108

theorem selected_cut_20109 : selected 8 ⟨514224, by decide⟩
    (prefixPartial 13 290157) = some ⟨13, 2, 0, 514224, 290157, 1749, 16384⟩ := by
  decide +kernel

theorem context_13_290157_514224 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290157 ⟨514224, by decide⟩ :=
  accepted_of_selected 13 290157 ⟨514224, by decide⟩ ⟨13, 2, 0, 514224, 290157, 1749, 16384⟩
    (by decide) selected_cut_20109

theorem selected_cut_20110 : selected 8 ⟨514245, by decide⟩
    (prefixPartial 13 290158) = some ⟨13, 2, 0, 514245, 290158, 1861, 16384⟩ := by
  decide +kernel

theorem context_13_290158_514245 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290158 ⟨514245, by decide⟩ :=
  accepted_of_selected 13 290158 ⟨514245, by decide⟩ ⟨13, 2, 0, 514245, 290158, 1861, 16384⟩
    (by decide) selected_cut_20110

theorem selected_cut_20111 : selected 8 ⟨514251, by decide⟩
    (prefixPartial 13 290159) = some ⟨13, 2, 0, 514251, 290159, 789, 16384⟩ := by
  decide +kernel

theorem context_13_290159_514251 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290159 ⟨514251, by decide⟩ :=
  accepted_of_selected 13 290159 ⟨514251, by decide⟩ ⟨13, 2, 0, 514251, 290159, 789, 16384⟩
    (by decide) selected_cut_20111

theorem unmarked_context_12_72539_514252 : frontier 9 ⟨514252, by decide⟩
    (prefixCache 12 72539) (prefixPartial 12 72539) = false := by
  decide +kernel

theorem node_context_12_72539_514252 : EJMOriginalGlobalDAGData.nodes 9 ⟨514252, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨514224, by decide⟩,⟨514245, by decide⟩,⟨514251, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72539_514252 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72539 ⟨514252, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72539
    ⟨514252, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨514224, by decide⟩,⟨514245, by decide⟩,⟨514251, by decide⟩]) unmarked_context_12_72539_514252 node_context_12_72539_514252
  intro a
  fin_cases a
  · exact context_13_290156_3444
  · exact context_13_290157_514224
  · exact context_13_290158_514245
  · exact context_13_290159_514251

theorem unmarked_context_11_18134_514253 : frontier 10 ⟨514253, by decide⟩
    (prefixCache 11 18134) (prefixPartial 11 18134) = false := by
  decide +kernel

theorem node_context_11_18134_514253 : EJMOriginalGlobalDAGData.nodes 10 ⟨514253, by decide⟩ =
    .split (coordinate 11) (![⟨514087, by decide⟩,⟨514139, by decide⟩,⟨514202, by decide⟩,⟨514252, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18134_514253 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18134 ⟨514253, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18134
    ⟨514253, by decide⟩ (by decide) (![⟨514087, by decide⟩,⟨514139, by decide⟩,⟨514202, by decide⟩,⟨514252, by decide⟩]) unmarked_context_11_18134_514253 node_context_11_18134_514253
  intro a
  fin_cases a
  · exact context_12_72536_514087
  · exact context_12_72537_514139
  · exact context_12_72538_514202
  · exact context_12_72539_514252

theorem selected_cut_20112 : selected 9 ⟨514300, by decide⟩
    (prefixPartial 12 72540) = some ⟨12, 2, 0, 514300, 72540, 3689, 65536⟩ := by
  decide +kernel

theorem context_12_72540_514300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72540 ⟨514300, by decide⟩ :=
  accepted_of_selected 12 72540 ⟨514300, by decide⟩ ⟨12, 2, 0, 514300, 72540, 3689, 65536⟩
    (by decide) selected_cut_20112

theorem selected_cut_20113 : selected 9 ⟨514342, by decide⟩
    (prefixPartial 12 72541) = some ⟨12, 2, 0, 514342, 72541, 3677, 65536⟩ := by
  decide +kernel

theorem context_12_72541_514342 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72541 ⟨514342, by decide⟩ :=
  accepted_of_selected 12 72541 ⟨514342, by decide⟩ ⟨12, 2, 0, 514342, 72541, 3677, 65536⟩
    (by decide) selected_cut_20113

theorem selected_cut_20114 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 290168) = some ⟨13, 1, 0, 3444, 290168, 1, 16384⟩ := by
  decide +kernel

theorem context_13_290168_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290168 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 290168 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 290168, 1, 16384⟩
    (by decide) selected_cut_20114

theorem selected_cut_20115 : selected 8 ⟨514369, by decide⟩
    (prefixPartial 13 290169) = some ⟨13, 2, 0, 514369, 290169, 1733, 16384⟩ := by
  decide +kernel

theorem context_13_290169_514369 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290169 ⟨514369, by decide⟩ :=
  accepted_of_selected 13 290169 ⟨514369, by decide⟩ ⟨13, 2, 0, 514369, 290169, 1733, 16384⟩
    (by decide) selected_cut_20115

theorem selected_cut_20116 : selected 8 ⟨514392, by decide⟩
    (prefixPartial 13 290170) = some ⟨13, 2, 0, 514392, 290170, 1869, 16384⟩ := by
  decide +kernel

theorem context_13_290170_514392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290170 ⟨514392, by decide⟩ :=
  accepted_of_selected 13 290170 ⟨514392, by decide⟩ ⟨13, 2, 0, 514392, 290170, 1869, 16384⟩
    (by decide) selected_cut_20116

theorem selected_cut_20117 : selected 8 ⟨514397, by decide⟩
    (prefixPartial 13 290171) = some ⟨13, 2, 0, 514397, 290171, 833, 16384⟩ := by
  decide +kernel

theorem context_13_290171_514397 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290171 ⟨514397, by decide⟩ :=
  accepted_of_selected 13 290171 ⟨514397, by decide⟩ ⟨13, 2, 0, 514397, 290171, 833, 16384⟩
    (by decide) selected_cut_20117

theorem unmarked_context_12_72542_514398 : frontier 9 ⟨514398, by decide⟩
    (prefixCache 12 72542) (prefixPartial 12 72542) = false := by
  decide +kernel

theorem node_context_12_72542_514398 : EJMOriginalGlobalDAGData.nodes 9 ⟨514398, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨514369, by decide⟩,⟨514392, by decide⟩,⟨514397, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72542_514398 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72542 ⟨514398, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72542
    ⟨514398, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨514369, by decide⟩,⟨514392, by decide⟩,⟨514397, by decide⟩]) unmarked_context_12_72542_514398 node_context_12_72542_514398
  intro a
  fin_cases a
  · exact context_13_290168_3444
  · exact context_13_290169_514369
  · exact context_13_290170_514392
  · exact context_13_290171_514397

theorem selected_cut_20118 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 290172) = some ⟨13, 1, 0, 3444, 290172, 1, 16384⟩ := by
  decide +kernel

theorem context_13_290172_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290172 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 290172 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 290172, 1, 16384⟩
    (by decide) selected_cut_20118

theorem selected_cut_20119 : selected 8 ⟨514447, by decide⟩
    (prefixPartial 13 290173) = some ⟨13, 2, 0, 514447, 290173, 2297, 16384⟩ := by
  decide +kernel

theorem context_13_290173_514447 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290173 ⟨514447, by decide⟩ :=
  accepted_of_selected 13 290173 ⟨514447, by decide⟩ ⟨13, 2, 0, 514447, 290173, 2297, 16384⟩
    (by decide) selected_cut_20119

theorem selected_cut_20120 : selected 8 ⟨514515, by decide⟩
    (prefixPartial 13 290174) = some ⟨13, 2, 0, 514515, 290174, 2957, 16384⟩ := by
  decide +kernel

theorem context_13_290174_514515 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290174 ⟨514515, by decide⟩ :=
  accepted_of_selected 13 290174 ⟨514515, by decide⟩ ⟨13, 2, 0, 514515, 290174, 2957, 16384⟩
    (by decide) selected_cut_20120

theorem selected_cut_20121 : selected 8 ⟨514529, by decide⟩
    (prefixPartial 13 290175) = some ⟨13, 2, 0, 514529, 290175, 1069, 16384⟩ := by
  decide +kernel

theorem context_13_290175_514529 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290175 ⟨514529, by decide⟩ :=
  accepted_of_selected 13 290175 ⟨514529, by decide⟩ ⟨13, 2, 0, 514529, 290175, 1069, 16384⟩
    (by decide) selected_cut_20121

theorem unmarked_context_12_72543_514530 : frontier 9 ⟨514530, by decide⟩
    (prefixCache 12 72543) (prefixPartial 12 72543) = false := by
  decide +kernel

theorem node_context_12_72543_514530 : EJMOriginalGlobalDAGData.nodes 9 ⟨514530, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨514447, by decide⟩,⟨514515, by decide⟩,⟨514529, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72543_514530 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72543 ⟨514530, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72543
    ⟨514530, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨514447, by decide⟩,⟨514515, by decide⟩,⟨514529, by decide⟩]) unmarked_context_12_72543_514530 node_context_12_72543_514530
  intro a
  fin_cases a
  · exact context_13_290172_3444
  · exact context_13_290173_514447
  · exact context_13_290174_514515
  · exact context_13_290175_514529

theorem unmarked_context_11_18135_514531 : frontier 10 ⟨514531, by decide⟩
    (prefixCache 11 18135) (prefixPartial 11 18135) = false := by
  decide +kernel

theorem node_context_11_18135_514531 : EJMOriginalGlobalDAGData.nodes 10 ⟨514531, by decide⟩ =
    .split (coordinate 11) (![⟨514300, by decide⟩,⟨514342, by decide⟩,⟨514398, by decide⟩,⟨514530, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18135_514531 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18135 ⟨514531, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18135
    ⟨514531, by decide⟩ (by decide) (![⟨514300, by decide⟩,⟨514342, by decide⟩,⟨514398, by decide⟩,⟨514530, by decide⟩]) unmarked_context_11_18135_514531 node_context_11_18135_514531
  intro a
  fin_cases a
  · exact context_12_72540_514300
  · exact context_12_72541_514342
  · exact context_12_72542_514398
  · exact context_12_72543_514530

theorem unmarked_context_10_4533_514532 : frontier 11 ⟨514532, by decide⟩
    (prefixCache 10 4533) (prefixPartial 10 4533) = false := by
  decide +kernel

theorem node_context_10_4533_514532 : EJMOriginalGlobalDAGData.nodes 11 ⟨514532, by decide⟩ =
    .split (coordinate 10) (![⟨513798, by decide⟩,⟨514033, by decide⟩,⟨514253, by decide⟩,⟨514531, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4533_514532 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4533 ⟨514532, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4533
    ⟨514532, by decide⟩ (by decide) (![⟨513798, by decide⟩,⟨514033, by decide⟩,⟨514253, by decide⟩,⟨514531, by decide⟩]) unmarked_context_10_4533_514532 node_context_10_4533_514532
  intro a
  fin_cases a
  · exact context_11_18132_513798
  · exact context_11_18133_514033
  · exact context_11_18134_514253
  · exact context_11_18135_514531

theorem selected_cut_20122 : selected 9 ⟨514577, by decide⟩
    (prefixPartial 12 72544) = some ⟨12, 2, 0, 514577, 72544, 3201, 65536⟩ := by
  decide +kernel

theorem context_12_72544_514577 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72544 ⟨514577, by decide⟩ :=
  accepted_of_selected 12 72544 ⟨514577, by decide⟩ ⟨12, 2, 0, 514577, 72544, 3201, 65536⟩
    (by decide) selected_cut_20122

theorem selected_cut_20123 : selected 9 ⟨514616, by decide⟩
    (prefixPartial 12 72545) = some ⟨12, 2, 0, 514616, 72545, 3465, 65536⟩ := by
  decide +kernel

theorem context_12_72545_514616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72545 ⟨514616, by decide⟩ :=
  accepted_of_selected 12 72545 ⟨514616, by decide⟩ ⟨12, 2, 0, 514616, 72545, 3465, 65536⟩
    (by decide) selected_cut_20123

theorem selected_cut_20124 : selected 9 ⟨514683, by decide⟩
    (prefixPartial 12 72546) = some ⟨12, 2, 0, 514683, 72546, 4081, 65536⟩ := by
  decide +kernel

theorem context_12_72546_514683 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72546 ⟨514683, by decide⟩ :=
  accepted_of_selected 12 72546 ⟨514683, by decide⟩ ⟨12, 2, 0, 514683, 72546, 4081, 65536⟩
    (by decide) selected_cut_20124

theorem selected_cut_20125 : selected 9 ⟨514720, by decide⟩
    (prefixPartial 12 72547) = some ⟨12, 2, 0, 514720, 72547, 3753, 65536⟩ := by
  decide +kernel

theorem context_12_72547_514720 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72547 ⟨514720, by decide⟩ :=
  accepted_of_selected 12 72547 ⟨514720, by decide⟩ ⟨12, 2, 0, 514720, 72547, 3753, 65536⟩
    (by decide) selected_cut_20125

theorem unmarked_context_11_18136_514721 : frontier 10 ⟨514721, by decide⟩
    (prefixCache 11 18136) (prefixPartial 11 18136) = false := by
  decide +kernel

theorem node_context_11_18136_514721 : EJMOriginalGlobalDAGData.nodes 10 ⟨514721, by decide⟩ =
    .split (coordinate 11) (![⟨514577, by decide⟩,⟨514616, by decide⟩,⟨514683, by decide⟩,⟨514720, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18136_514721 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18136 ⟨514721, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18136
    ⟨514721, by decide⟩ (by decide) (![⟨514577, by decide⟩,⟨514616, by decide⟩,⟨514683, by decide⟩,⟨514720, by decide⟩]) unmarked_context_11_18136_514721 node_context_11_18136_514721
  intro a
  fin_cases a
  · exact context_12_72544_514577
  · exact context_12_72545_514616
  · exact context_12_72546_514683
  · exact context_12_72547_514720

theorem selected_cut_20126 : selected 9 ⟨514786, by decide⟩
    (prefixPartial 12 72548) = some ⟨12, 2, 0, 514786, 72548, 3733, 65536⟩ := by
  decide +kernel

theorem context_12_72548_514786 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72548 ⟨514786, by decide⟩ :=
  accepted_of_selected 12 72548 ⟨514786, by decide⟩ ⟨12, 2, 0, 514786, 72548, 3733, 65536⟩
    (by decide) selected_cut_20126

theorem selected_cut_20127 : selected 9 ⟨514825, by decide⟩
    (prefixPartial 12 72549) = some ⟨12, 2, 0, 514825, 72549, 3301, 65536⟩ := by
  decide +kernel

theorem context_12_72549_514825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72549 ⟨514825, by decide⟩ :=
  accepted_of_selected 12 72549 ⟨514825, by decide⟩ ⟨12, 2, 0, 514825, 72549, 3301, 65536⟩
    (by decide) selected_cut_20127

theorem selected_cut_20128 : selected 9 ⟨514893, by decide⟩
    (prefixPartial 12 72550) = some ⟨12, 2, 0, 514893, 72550, 4017, 65536⟩ := by
  decide +kernel

theorem context_12_72550_514893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72550 ⟨514893, by decide⟩ :=
  accepted_of_selected 12 72550 ⟨514893, by decide⟩ ⟨12, 2, 0, 514893, 72550, 4017, 65536⟩
    (by decide) selected_cut_20128

theorem selected_cut_20129 : selected 9 ⟨514942, by decide⟩
    (prefixPartial 12 72551) = some ⟨12, 2, 0, 514942, 72551, 3809, 65536⟩ := by
  decide +kernel

theorem context_12_72551_514942 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72551 ⟨514942, by decide⟩ :=
  accepted_of_selected 12 72551 ⟨514942, by decide⟩ ⟨12, 2, 0, 514942, 72551, 3809, 65536⟩
    (by decide) selected_cut_20129

theorem unmarked_context_11_18137_514943 : frontier 10 ⟨514943, by decide⟩
    (prefixCache 11 18137) (prefixPartial 11 18137) = false := by
  decide +kernel

theorem node_context_11_18137_514943 : EJMOriginalGlobalDAGData.nodes 10 ⟨514943, by decide⟩ =
    .split (coordinate 11) (![⟨514786, by decide⟩,⟨514825, by decide⟩,⟨514893, by decide⟩,⟨514942, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18137_514943 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18137 ⟨514943, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18137
    ⟨514943, by decide⟩ (by decide) (![⟨514786, by decide⟩,⟨514825, by decide⟩,⟨514893, by decide⟩,⟨514942, by decide⟩]) unmarked_context_11_18137_514943 node_context_11_18137_514943
  intro a
  fin_cases a
  · exact context_12_72548_514786
  · exact context_12_72549_514825
  · exact context_12_72550_514893
  · exact context_12_72551_514942

theorem selected_cut_20130 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 290208) = some ⟨13, 1, 0, 3444, 290208, 1, 16384⟩ := by
  decide +kernel

theorem context_13_290208_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290208 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 290208 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 290208, 1, 16384⟩
    (by decide) selected_cut_20130

theorem selected_cut_20131 : selected 8 ⟨514967, by decide⟩
    (prefixPartial 13 290209) = some ⟨13, 2, 0, 514967, 290209, 1213, 16384⟩ := by
  decide +kernel

theorem context_13_290209_514967 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290209 ⟨514967, by decide⟩ :=
  accepted_of_selected 13 290209 ⟨514967, by decide⟩ ⟨13, 2, 0, 514967, 290209, 1213, 16384⟩
    (by decide) selected_cut_20131

theorem selected_cut_20132 : selected 8 ⟨514998, by decide⟩
    (prefixPartial 13 290210) = some ⟨13, 2, 0, 514998, 290210, 2201, 16384⟩ := by
  decide +kernel

theorem context_13_290210_514998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290210 ⟨514998, by decide⟩ :=
  accepted_of_selected 13 290210 ⟨514998, by decide⟩ ⟨13, 2, 0, 514998, 290210, 2201, 16384⟩
    (by decide) selected_cut_20132

theorem selected_cut_20133 : selected 8 ⟨515021, by decide⟩
    (prefixPartial 13 290211) = some ⟨13, 2, 0, 515021, 290211, 1249, 16384⟩ := by
  decide +kernel

theorem context_13_290211_515021 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290211 ⟨515021, by decide⟩ :=
  accepted_of_selected 13 290211 ⟨515021, by decide⟩ ⟨13, 2, 0, 515021, 290211, 1249, 16384⟩
    (by decide) selected_cut_20133

theorem unmarked_context_12_72552_515022 : frontier 9 ⟨515022, by decide⟩
    (prefixCache 12 72552) (prefixPartial 12 72552) = false := by
  decide +kernel

theorem node_context_12_72552_515022 : EJMOriginalGlobalDAGData.nodes 9 ⟨515022, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨514967, by decide⟩,⟨514998, by decide⟩,⟨515021, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72552_515022 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72552 ⟨515022, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72552
    ⟨515022, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨514967, by decide⟩,⟨514998, by decide⟩,⟨515021, by decide⟩]) unmarked_context_12_72552_515022 node_context_12_72552_515022
  intro a
  fin_cases a
  · exact context_13_290208_3444
  · exact context_13_290209_514967
  · exact context_13_290210_514998
  · exact context_13_290211_515021

theorem selected_cut_20134 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 290212) = some ⟨13, 1, 0, 3444, 290212, 1, 16384⟩ := by
  decide +kernel

theorem context_13_290212_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290212 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 290212 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 290212, 1, 16384⟩
    (by decide) selected_cut_20134

theorem selected_cut_20135 : selected 8 ⟨515038, by decide⟩
    (prefixPartial 13 290213) = some ⟨13, 2, 0, 515038, 290213, 1145, 16384⟩ := by
  decide +kernel

theorem context_13_290213_515038 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290213 ⟨515038, by decide⟩ :=
  accepted_of_selected 13 290213 ⟨515038, by decide⟩ ⟨13, 2, 0, 515038, 290213, 1145, 16384⟩
    (by decide) selected_cut_20135

theorem selected_cut_20136 : selected 8 ⟨515074, by decide⟩
    (prefixPartial 13 290214) = some ⟨13, 2, 0, 515074, 290214, 2173, 16384⟩ := by
  decide +kernel

theorem context_13_290214_515074 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290214 ⟨515074, by decide⟩ :=
  accepted_of_selected 13 290214 ⟨515074, by decide⟩ ⟨13, 2, 0, 515074, 290214, 2173, 16384⟩
    (by decide) selected_cut_20136

theorem selected_cut_20137 : selected 8 ⟨515116, by decide⟩
    (prefixPartial 13 290215) = some ⟨13, 2, 0, 515116, 290215, 1281, 16384⟩ := by
  decide +kernel

theorem context_13_290215_515116 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290215 ⟨515116, by decide⟩ :=
  accepted_of_selected 13 290215 ⟨515116, by decide⟩ ⟨13, 2, 0, 515116, 290215, 1281, 16384⟩
    (by decide) selected_cut_20137

theorem unmarked_context_12_72553_515117 : frontier 9 ⟨515117, by decide⟩
    (prefixCache 12 72553) (prefixPartial 12 72553) = false := by
  decide +kernel

theorem node_context_12_72553_515117 : EJMOriginalGlobalDAGData.nodes 9 ⟨515117, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨515038, by decide⟩,⟨515074, by decide⟩,⟨515116, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72553_515117 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72553 ⟨515117, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72553
    ⟨515117, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨515038, by decide⟩,⟨515074, by decide⟩,⟨515116, by decide⟩]) unmarked_context_12_72553_515117 node_context_12_72553_515117
  intro a
  fin_cases a
  · exact context_13_290212_3444
  · exact context_13_290213_515038
  · exact context_13_290214_515074
  · exact context_13_290215_515116

theorem selected_cut_20138 : selected 9 ⟨474208, by decide⟩
    (prefixPartial 12 72554) = some ⟨12, 1, 0, 474208, 72554, 1, 65536⟩ := by
  decide +kernel

theorem context_12_72554_474208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72554 ⟨474208, by decide⟩ :=
  accepted_of_selected 12 72554 ⟨474208, by decide⟩ ⟨12, 1, 0, 474208, 72554, 1, 65536⟩
    (by decide) selected_cut_20138

theorem selected_cut_20139 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 290220) = some ⟨13, 1, 0, 3444, 290220, 1, 16384⟩ := by
  decide +kernel

theorem context_13_290220_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290220 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 290220 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 290220, 1, 16384⟩
    (by decide) selected_cut_20139

theorem selected_cut_20140 : selected 8 ⟨515140, by decide⟩
    (prefixPartial 13 290221) = some ⟨13, 2, 0, 515140, 290221, 1201, 16384⟩ := by
  decide +kernel

theorem context_13_290221_515140 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290221 ⟨515140, by decide⟩ :=
  accepted_of_selected 13 290221 ⟨515140, by decide⟩ ⟨13, 2, 0, 515140, 290221, 1201, 16384⟩
    (by decide) selected_cut_20140

theorem selected_cut_20141 : selected 8 ⟨515185, by decide⟩
    (prefixPartial 13 290222) = some ⟨13, 2, 0, 515185, 290222, 2633, 16384⟩ := by
  decide +kernel

theorem context_13_290222_515185 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290222 ⟨515185, by decide⟩ :=
  accepted_of_selected 13 290222 ⟨515185, by decide⟩ ⟨13, 2, 0, 515185, 290222, 2633, 16384⟩
    (by decide) selected_cut_20141

theorem selected_cut_20142 : selected 8 ⟨515213, by decide⟩
    (prefixPartial 13 290223) = some ⟨13, 2, 0, 515213, 290223, 1249, 16384⟩ := by
  decide +kernel

theorem context_13_290223_515213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290223 ⟨515213, by decide⟩ :=
  accepted_of_selected 13 290223 ⟨515213, by decide⟩ ⟨13, 2, 0, 515213, 290223, 1249, 16384⟩
    (by decide) selected_cut_20142

theorem unmarked_context_12_72555_515214 : frontier 9 ⟨515214, by decide⟩
    (prefixCache 12 72555) (prefixPartial 12 72555) = false := by
  decide +kernel

theorem node_context_12_72555_515214 : EJMOriginalGlobalDAGData.nodes 9 ⟨515214, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨515140, by decide⟩,⟨515185, by decide⟩,⟨515213, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72555_515214 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72555 ⟨515214, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72555
    ⟨515214, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨515140, by decide⟩,⟨515185, by decide⟩,⟨515213, by decide⟩]) unmarked_context_12_72555_515214 node_context_12_72555_515214
  intro a
  fin_cases a
  · exact context_13_290220_3444
  · exact context_13_290221_515140
  · exact context_13_290222_515185
  · exact context_13_290223_515213

theorem unmarked_context_11_18138_515215 : frontier 10 ⟨515215, by decide⟩
    (prefixCache 11 18138) (prefixPartial 11 18138) = false := by
  decide +kernel

theorem node_context_11_18138_515215 : EJMOriginalGlobalDAGData.nodes 10 ⟨515215, by decide⟩ =
    .split (coordinate 11) (![⟨515022, by decide⟩,⟨515117, by decide⟩,⟨474208, by decide⟩,⟨515214, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18138_515215 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18138 ⟨515215, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18138
    ⟨515215, by decide⟩ (by decide) (![⟨515022, by decide⟩,⟨515117, by decide⟩,⟨474208, by decide⟩,⟨515214, by decide⟩]) unmarked_context_11_18138_515215 node_context_11_18138_515215
  intro a
  fin_cases a
  · exact context_12_72552_515022
  · exact context_12_72553_515117
  · exact context_12_72554_474208
  · exact context_12_72555_515214

theorem selected_cut_20143 : selected 9 ⟨515260, by decide⟩
    (prefixPartial 12 72556) = some ⟨12, 2, 0, 515260, 72556, 3301, 65536⟩ := by
  decide +kernel

theorem context_12_72556_515260 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72556 ⟨515260, by decide⟩ :=
  accepted_of_selected 12 72556 ⟨515260, by decide⟩ ⟨12, 2, 0, 515260, 72556, 3301, 65536⟩
    (by decide) selected_cut_20143

theorem selected_cut_20144 : selected 9 ⟨515296, by decide⟩
    (prefixPartial 12 72557) = some ⟨12, 2, 0, 515296, 72557, 3177, 65536⟩ := by
  decide +kernel

theorem context_12_72557_515296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72557 ⟨515296, by decide⟩ :=
  accepted_of_selected 12 72557 ⟨515296, by decide⟩ ⟨12, 2, 0, 515296, 72557, 3177, 65536⟩
    (by decide) selected_cut_20144

theorem selected_cut_20145 : selected 9 ⟨515343, by decide⟩
    (prefixPartial 12 72558) = some ⟨12, 2, 0, 515343, 72558, 3537, 65536⟩ := by
  decide +kernel

theorem context_12_72558_515343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72558 ⟨515343, by decide⟩ :=
  accepted_of_selected 12 72558 ⟨515343, by decide⟩ ⟨12, 2, 0, 515343, 72558, 3537, 65536⟩
    (by decide) selected_cut_20145

theorem selected_cut_20146 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 290236) = some ⟨13, 1, 0, 3444, 290236, 1, 16384⟩ := by
  decide +kernel

theorem context_13_290236_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290236 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 290236 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 290236, 1, 16384⟩
    (by decide) selected_cut_20146

theorem selected_cut_20147 : selected 8 ⟨515367, by decide⟩
    (prefixPartial 13 290237) = some ⟨13, 2, 0, 515367, 290237, 1121, 16384⟩ := by
  decide +kernel

theorem context_13_290237_515367 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290237 ⟨515367, by decide⟩ :=
  accepted_of_selected 13 290237 ⟨515367, by decide⟩ ⟨13, 2, 0, 515367, 290237, 1121, 16384⟩
    (by decide) selected_cut_20147

theorem selected_cut_20148 : selected 8 ⟨515431, by decide⟩
    (prefixPartial 13 290238) = some ⟨13, 2, 0, 515431, 290238, 3077, 16384⟩ := by
  decide +kernel

theorem context_13_290238_515431 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290238 ⟨515431, by decide⟩ :=
  accepted_of_selected 13 290238 ⟨515431, by decide⟩ ⟨13, 2, 0, 515431, 290238, 3077, 16384⟩
    (by decide) selected_cut_20148

theorem selected_cut_20149 : selected 8 ⟨515460, by decide⟩
    (prefixPartial 13 290239) = some ⟨13, 2, 0, 515460, 290239, 1285, 16384⟩ := by
  decide +kernel

theorem context_13_290239_515460 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290239 ⟨515460, by decide⟩ :=
  accepted_of_selected 13 290239 ⟨515460, by decide⟩ ⟨13, 2, 0, 515460, 290239, 1285, 16384⟩
    (by decide) selected_cut_20149

theorem unmarked_context_12_72559_515461 : frontier 9 ⟨515461, by decide⟩
    (prefixCache 12 72559) (prefixPartial 12 72559) = false := by
  decide +kernel

theorem node_context_12_72559_515461 : EJMOriginalGlobalDAGData.nodes 9 ⟨515461, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨515367, by decide⟩,⟨515431, by decide⟩,⟨515460, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72559_515461 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72559 ⟨515461, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72559
    ⟨515461, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨515367, by decide⟩,⟨515431, by decide⟩,⟨515460, by decide⟩]) unmarked_context_12_72559_515461 node_context_12_72559_515461
  intro a
  fin_cases a
  · exact context_13_290236_3444
  · exact context_13_290237_515367
  · exact context_13_290238_515431
  · exact context_13_290239_515460

theorem unmarked_context_11_18139_515462 : frontier 10 ⟨515462, by decide⟩
    (prefixCache 11 18139) (prefixPartial 11 18139) = false := by
  decide +kernel

theorem node_context_11_18139_515462 : EJMOriginalGlobalDAGData.nodes 10 ⟨515462, by decide⟩ =
    .split (coordinate 11) (![⟨515260, by decide⟩,⟨515296, by decide⟩,⟨515343, by decide⟩,⟨515461, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18139_515462 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18139 ⟨515462, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18139
    ⟨515462, by decide⟩ (by decide) (![⟨515260, by decide⟩,⟨515296, by decide⟩,⟨515343, by decide⟩,⟨515461, by decide⟩]) unmarked_context_11_18139_515462 node_context_11_18139_515462
  intro a
  fin_cases a
  · exact context_12_72556_515260
  · exact context_12_72557_515296
  · exact context_12_72558_515343
  · exact context_12_72559_515461

theorem unmarked_context_10_4534_515463 : frontier 11 ⟨515463, by decide⟩
    (prefixCache 10 4534) (prefixPartial 10 4534) = false := by
  decide +kernel

theorem node_context_10_4534_515463 : EJMOriginalGlobalDAGData.nodes 11 ⟨515463, by decide⟩ =
    .split (coordinate 10) (![⟨514721, by decide⟩,⟨514943, by decide⟩,⟨515215, by decide⟩,⟨515462, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4534_515463 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4534 ⟨515463, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4534
    ⟨515463, by decide⟩ (by decide) (![⟨514721, by decide⟩,⟨514943, by decide⟩,⟨515215, by decide⟩,⟨515462, by decide⟩]) unmarked_context_10_4534_515463 node_context_10_4534_515463
  intro a
  fin_cases a
  · exact context_11_18136_514721
  · exact context_11_18137_514943
  · exact context_11_18138_515215
  · exact context_11_18139_515462

theorem selected_cut_20150 : selected 9 ⟨515500, by decide⟩
    (prefixPartial 12 72560) = some ⟨12, 2, 0, 515500, 72560, 2889, 65536⟩ := by
  decide +kernel

theorem context_12_72560_515500 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72560 ⟨515500, by decide⟩ :=
  accepted_of_selected 12 72560 ⟨515500, by decide⟩ ⟨12, 2, 0, 515500, 72560, 2889, 65536⟩
    (by decide) selected_cut_20150

theorem selected_cut_20151 : selected 9 ⟨515543, by decide⟩
    (prefixPartial 12 72561) = some ⟨12, 2, 0, 515543, 72561, 3101, 65536⟩ := by
  decide +kernel

theorem context_12_72561_515543 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72561 ⟨515543, by decide⟩ :=
  accepted_of_selected 12 72561 ⟨515543, by decide⟩ ⟨12, 2, 0, 515543, 72561, 3101, 65536⟩
    (by decide) selected_cut_20151

theorem selected_cut_20152 : selected 9 ⟨515591, by decide⟩
    (prefixPartial 12 72562) = some ⟨12, 2, 0, 515591, 72562, 3685, 65536⟩ := by
  decide +kernel

theorem context_12_72562_515591 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72562 ⟨515591, by decide⟩ :=
  accepted_of_selected 12 72562 ⟨515591, by decide⟩ ⟨12, 2, 0, 515591, 72562, 3685, 65536⟩
    (by decide) selected_cut_20152

theorem selected_cut_20153 : selected 9 ⟨515629, by decide⟩
    (prefixPartial 12 72563) = some ⟨12, 2, 0, 515629, 72563, 3241, 65536⟩ := by
  decide +kernel

theorem context_12_72563_515629 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72563 ⟨515629, by decide⟩ :=
  accepted_of_selected 12 72563 ⟨515629, by decide⟩ ⟨12, 2, 0, 515629, 72563, 3241, 65536⟩
    (by decide) selected_cut_20153

theorem unmarked_context_11_18140_515630 : frontier 10 ⟨515630, by decide⟩
    (prefixCache 11 18140) (prefixPartial 11 18140) = false := by
  decide +kernel

theorem node_context_11_18140_515630 : EJMOriginalGlobalDAGData.nodes 10 ⟨515630, by decide⟩ =
    .split (coordinate 11) (![⟨515500, by decide⟩,⟨515543, by decide⟩,⟨515591, by decide⟩,⟨515629, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18140_515630 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18140 ⟨515630, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18140
    ⟨515630, by decide⟩ (by decide) (![⟨515500, by decide⟩,⟨515543, by decide⟩,⟨515591, by decide⟩,⟨515629, by decide⟩]) unmarked_context_11_18140_515630 node_context_11_18140_515630
  intro a
  fin_cases a
  · exact context_12_72560_515500
  · exact context_12_72561_515543
  · exact context_12_72562_515591
  · exact context_12_72563_515629

theorem selected_cut_20154 : selected 9 ⟨515685, by decide⟩
    (prefixPartial 12 72564) = some ⟨12, 2, 0, 515685, 72564, 3341, 65536⟩ := by
  decide +kernel

theorem context_12_72564_515685 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72564 ⟨515685, by decide⟩ :=
  accepted_of_selected 12 72564 ⟨515685, by decide⟩ ⟨12, 2, 0, 515685, 72564, 3341, 65536⟩
    (by decide) selected_cut_20154

theorem selected_cut_20155 : selected 9 ⟨515724, by decide⟩
    (prefixPartial 12 72565) = some ⟨12, 2, 0, 515724, 72565, 3113, 65536⟩ := by
  decide +kernel

theorem context_12_72565_515724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72565 ⟨515724, by decide⟩ :=
  accepted_of_selected 12 72565 ⟨515724, by decide⟩ ⟨12, 2, 0, 515724, 72565, 3113, 65536⟩
    (by decide) selected_cut_20155

theorem selected_cut_20156 : selected 9 ⟨515791, by decide⟩
    (prefixPartial 12 72566) = some ⟨12, 2, 0, 515791, 72566, 3857, 65536⟩ := by
  decide +kernel

theorem context_12_72566_515791 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72566 ⟨515791, by decide⟩ :=
  accepted_of_selected 12 72566 ⟨515791, by decide⟩ ⟨12, 2, 0, 515791, 72566, 3857, 65536⟩
    (by decide) selected_cut_20156

theorem selected_cut_20157 : selected 9 ⟨515835, by decide⟩
    (prefixPartial 12 72567) = some ⟨12, 2, 0, 515835, 72567, 3373, 65536⟩ := by
  decide +kernel

theorem context_12_72567_515835 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72567 ⟨515835, by decide⟩ :=
  accepted_of_selected 12 72567 ⟨515835, by decide⟩ ⟨12, 2, 0, 515835, 72567, 3373, 65536⟩
    (by decide) selected_cut_20157

theorem unmarked_context_11_18141_515836 : frontier 10 ⟨515836, by decide⟩
    (prefixCache 11 18141) (prefixPartial 11 18141) = false := by
  decide +kernel

theorem node_context_11_18141_515836 : EJMOriginalGlobalDAGData.nodes 10 ⟨515836, by decide⟩ =
    .split (coordinate 11) (![⟨515685, by decide⟩,⟨515724, by decide⟩,⟨515791, by decide⟩,⟨515835, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18141_515836 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18141 ⟨515836, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18141
    ⟨515836, by decide⟩ (by decide) (![⟨515685, by decide⟩,⟨515724, by decide⟩,⟨515791, by decide⟩,⟨515835, by decide⟩]) unmarked_context_11_18141_515836 node_context_11_18141_515836
  intro a
  fin_cases a
  · exact context_12_72564_515685
  · exact context_12_72565_515724
  · exact context_12_72566_515791
  · exact context_12_72567_515835

theorem selected_cut_20158 : selected 9 ⟨515880, by decide⟩
    (prefixPartial 12 72568) = some ⟨12, 2, 0, 515880, 72568, 3389, 65536⟩ := by
  decide +kernel

theorem context_12_72568_515880 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72568 ⟨515880, by decide⟩ :=
  accepted_of_selected 12 72568 ⟨515880, by decide⟩ ⟨12, 2, 0, 515880, 72568, 3389, 65536⟩
    (by decide) selected_cut_20158

theorem selected_cut_20159 : selected 9 ⟨515927, by decide⟩
    (prefixPartial 12 72569) = some ⟨12, 2, 0, 515927, 72569, 3373, 65536⟩ := by
  decide +kernel

theorem context_12_72569_515927 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72569 ⟨515927, by decide⟩ :=
  accepted_of_selected 12 72569 ⟨515927, by decide⟩ ⟨12, 2, 0, 515927, 72569, 3373, 65536⟩
    (by decide) selected_cut_20159

theorem selected_cut_20160 : selected 9 ⟨515977, by decide⟩
    (prefixPartial 12 72570) = some ⟨12, 2, 0, 515977, 72570, 3669, 65536⟩ := by
  decide +kernel

theorem context_12_72570_515977 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72570 ⟨515977, by decide⟩ :=
  accepted_of_selected 12 72570 ⟨515977, by decide⟩ ⟨12, 2, 0, 515977, 72570, 3669, 65536⟩
    (by decide) selected_cut_20160

theorem selected_cut_20161 : selected 9 ⟨516019, by decide⟩
    (prefixPartial 12 72571) = some ⟨12, 2, 0, 516019, 72571, 3441, 65536⟩ := by
  decide +kernel

theorem context_12_72571_516019 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72571 ⟨516019, by decide⟩ :=
  accepted_of_selected 12 72571 ⟨516019, by decide⟩ ⟨12, 2, 0, 516019, 72571, 3441, 65536⟩
    (by decide) selected_cut_20161

theorem unmarked_context_11_18142_516020 : frontier 10 ⟨516020, by decide⟩
    (prefixCache 11 18142) (prefixPartial 11 18142) = false := by
  decide +kernel

theorem node_context_11_18142_516020 : EJMOriginalGlobalDAGData.nodes 10 ⟨516020, by decide⟩ =
    .split (coordinate 11) (![⟨515880, by decide⟩,⟨515927, by decide⟩,⟨515977, by decide⟩,⟨516019, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18142_516020 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18142 ⟨516020, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18142
    ⟨516020, by decide⟩ (by decide) (![⟨515880, by decide⟩,⟨515927, by decide⟩,⟨515977, by decide⟩,⟨516019, by decide⟩]) unmarked_context_11_18142_516020 node_context_11_18142_516020
  intro a
  fin_cases a
  · exact context_12_72568_515880
  · exact context_12_72569_515927
  · exact context_12_72570_515977
  · exact context_12_72571_516019

theorem selected_cut_20162 : selected 9 ⟨516051, by decide⟩
    (prefixPartial 12 72572) = some ⟨12, 2, 0, 516051, 72572, 2805, 65536⟩ := by
  decide +kernel

theorem context_12_72572_516051 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72572 ⟨516051, by decide⟩ :=
  accepted_of_selected 12 72572 ⟨516051, by decide⟩ ⟨12, 2, 0, 516051, 72572, 2805, 65536⟩
    (by decide) selected_cut_20162

theorem selected_cut_20163 : selected 9 ⟨516084, by decide⟩
    (prefixPartial 12 72573) = some ⟨12, 2, 0, 516084, 72573, 2801, 65536⟩ := by
  decide +kernel

theorem context_12_72573_516084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72573 ⟨516084, by decide⟩ :=
  accepted_of_selected 12 72573 ⟨516084, by decide⟩ ⟨12, 2, 0, 516084, 72573, 2801, 65536⟩
    (by decide) selected_cut_20163

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
