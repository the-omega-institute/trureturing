/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover020
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_02019 : selected 8 ⟨67180, by decide⟩
    (prefixPartial 13 21675) = some ⟨13, 2, 0, 67180, 21675, 913, 16384⟩ := by
  decide +kernel

theorem context_13_21675_67180 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21675 ⟨67180, by decide⟩ :=
  accepted_of_selected 13 21675 ⟨67180, by decide⟩ ⟨13, 2, 0, 67180, 21675, 913, 16384⟩
    (by decide) selected_cut_02019

theorem unmarked_context_12_5418_67181 : frontier 9 ⟨67181, by decide⟩
    (prefixCache 12 5418) (prefixPartial 12 5418) = false := by
  decide +kernel

theorem node_context_12_5418_67181 : EJMOriginalGlobalDAGData.nodes 9 ⟨67181, by decide⟩ =
    .split (coordinate 12) (![⟨67116, by decide⟩,⟨67144, by decide⟩,⟨67167, by decide⟩,⟨67180, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5418_67181 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5418 ⟨67181, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5418
    ⟨67181, by decide⟩ (by decide) (![⟨67116, by decide⟩,⟨67144, by decide⟩,⟨67167, by decide⟩,⟨67180, by decide⟩]) unmarked_context_12_5418_67181 node_context_12_5418_67181
  intro a
  fin_cases a
  · exact context_13_21672_67116
  · exact context_13_21673_67144
  · exact context_13_21674_67167
  · exact context_13_21675_67180

theorem selected_cut_02020 : selected 8 ⟨67205, by decide⟩
    (prefixPartial 13 21676) = some ⟨13, 2, 0, 67205, 21676, 541, 16384⟩ := by
  decide +kernel

theorem context_13_21676_67205 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21676 ⟨67205, by decide⟩ :=
  accepted_of_selected 13 21676 ⟨67205, by decide⟩ ⟨13, 2, 0, 67205, 21676, 541, 16384⟩
    (by decide) selected_cut_02020

theorem selected_cut_02021 : selected 8 ⟨67245, by decide⟩
    (prefixPartial 13 21677) = some ⟨13, 2, 0, 67245, 21677, 2781, 16384⟩ := by
  decide +kernel

theorem context_13_21677_67245 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21677 ⟨67245, by decide⟩ :=
  accepted_of_selected 13 21677 ⟨67245, by decide⟩ ⟨13, 2, 0, 67245, 21677, 2781, 16384⟩
    (by decide) selected_cut_02021

theorem selected_cut_02022 : selected 8 ⟨67276, by decide⟩
    (prefixPartial 13 21678) = some ⟨13, 2, 0, 67276, 21678, 2269, 16384⟩ := by
  decide +kernel

theorem context_13_21678_67276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21678 ⟨67276, by decide⟩ :=
  accepted_of_selected 13 21678 ⟨67276, by decide⟩ ⟨13, 2, 0, 67276, 21678, 2269, 16384⟩
    (by decide) selected_cut_02022

theorem selected_cut_02023 : selected 8 ⟨67286, by decide⟩
    (prefixPartial 13 21679) = some ⟨13, 2, 0, 67286, 21679, 1277, 16384⟩ := by
  decide +kernel

theorem context_13_21679_67286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21679 ⟨67286, by decide⟩ :=
  accepted_of_selected 13 21679 ⟨67286, by decide⟩ ⟨13, 2, 0, 67286, 21679, 1277, 16384⟩
    (by decide) selected_cut_02023

theorem unmarked_context_12_5419_67287 : frontier 9 ⟨67287, by decide⟩
    (prefixCache 12 5419) (prefixPartial 12 5419) = false := by
  decide +kernel

theorem node_context_12_5419_67287 : EJMOriginalGlobalDAGData.nodes 9 ⟨67287, by decide⟩ =
    .split (coordinate 12) (![⟨67205, by decide⟩,⟨67245, by decide⟩,⟨67276, by decide⟩,⟨67286, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5419_67287 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5419 ⟨67287, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5419
    ⟨67287, by decide⟩ (by decide) (![⟨67205, by decide⟩,⟨67245, by decide⟩,⟨67276, by decide⟩,⟨67286, by decide⟩]) unmarked_context_12_5419_67287 node_context_12_5419_67287
  intro a
  fin_cases a
  · exact context_13_21676_67205
  · exact context_13_21677_67245
  · exact context_13_21678_67276
  · exact context_13_21679_67286

theorem unmarked_context_11_1354_67288 : frontier 10 ⟨67288, by decide⟩
    (prefixCache 11 1354) (prefixPartial 11 1354) = false := by
  decide +kernel

theorem node_context_11_1354_67288 : EJMOriginalGlobalDAGData.nodes 10 ⟨67288, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨67181, by decide⟩,⟨67287, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1354_67288 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1354 ⟨67288, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1354
    ⟨67288, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨67181, by decide⟩,⟨67287, by decide⟩]) unmarked_context_11_1354_67288 node_context_11_1354_67288
  intro a
  fin_cases a
  · exact context_12_5416_1738
  · exact context_12_5417_1738
  · exact context_12_5418_67181
  · exact context_12_5419_67287

theorem selected_cut_02024 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 5420) = some ⟨12, 1, 0, 1738, 5420, 1, 65536⟩ := by
  decide +kernel

theorem context_12_5420_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5420 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 5420 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 5420, 1, 65536⟩
    (by decide) selected_cut_02024

theorem selected_cut_02025 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 5421) = some ⟨12, 1, 0, 1738, 5421, 1, 65536⟩ := by
  decide +kernel

theorem context_12_5421_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5421 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 5421 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 5421, 1, 65536⟩
    (by decide) selected_cut_02025

theorem selected_cut_02026 : selected 8 ⟨67299, by decide⟩
    (prefixPartial 13 21688) = some ⟨13, 2, 0, 67299, 21688, 233, 16384⟩ := by
  decide +kernel

theorem context_13_21688_67299 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21688 ⟨67299, by decide⟩ :=
  accepted_of_selected 13 21688 ⟨67299, by decide⟩ ⟨13, 2, 0, 67299, 21688, 233, 16384⟩
    (by decide) selected_cut_02026

theorem selected_cut_02027 : selected 8 ⟨67337, by decide⟩
    (prefixPartial 13 21689) = some ⟨13, 2, 0, 67337, 21689, 2037, 16384⟩ := by
  decide +kernel

theorem context_13_21689_67337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21689 ⟨67337, by decide⟩ :=
  accepted_of_selected 13 21689 ⟨67337, by decide⟩ ⟨13, 2, 0, 67337, 21689, 2037, 16384⟩
    (by decide) selected_cut_02027

theorem selected_cut_02028 : selected 8 ⟨67376, by decide⟩
    (prefixPartial 13 21690) = some ⟨13, 2, 0, 67376, 21690, 1841, 16384⟩ := by
  decide +kernel

theorem context_13_21690_67376 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21690 ⟨67376, by decide⟩ :=
  accepted_of_selected 13 21690 ⟨67376, by decide⟩ ⟨13, 2, 0, 67376, 21690, 1841, 16384⟩
    (by decide) selected_cut_02028

theorem selected_cut_02029 : selected 8 ⟨67390, by decide⟩
    (prefixPartial 13 21691) = some ⟨13, 2, 0, 67390, 21691, 837, 16384⟩ := by
  decide +kernel

theorem context_13_21691_67390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21691 ⟨67390, by decide⟩ :=
  accepted_of_selected 13 21691 ⟨67390, by decide⟩ ⟨13, 2, 0, 67390, 21691, 837, 16384⟩
    (by decide) selected_cut_02029

theorem unmarked_context_12_5422_67391 : frontier 9 ⟨67391, by decide⟩
    (prefixCache 12 5422) (prefixPartial 12 5422) = false := by
  decide +kernel

theorem node_context_12_5422_67391 : EJMOriginalGlobalDAGData.nodes 9 ⟨67391, by decide⟩ =
    .split (coordinate 12) (![⟨67299, by decide⟩,⟨67337, by decide⟩,⟨67376, by decide⟩,⟨67390, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5422_67391 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5422 ⟨67391, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5422
    ⟨67391, by decide⟩ (by decide) (![⟨67299, by decide⟩,⟨67337, by decide⟩,⟨67376, by decide⟩,⟨67390, by decide⟩]) unmarked_context_12_5422_67391 node_context_12_5422_67391
  intro a
  fin_cases a
  · exact context_13_21688_67299
  · exact context_13_21689_67337
  · exact context_13_21690_67376
  · exact context_13_21691_67390

theorem selected_cut_02030 : selected 9 ⟨4596, by decide⟩
    (prefixPartial 12 5423) = some ⟨12, 1, 0, 4596, 5423, 1, 65536⟩ := by
  decide +kernel

theorem context_12_5423_4596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5423 ⟨4596, by decide⟩ :=
  accepted_of_selected 12 5423 ⟨4596, by decide⟩ ⟨12, 1, 0, 4596, 5423, 1, 65536⟩
    (by decide) selected_cut_02030

theorem unmarked_context_11_1355_67392 : frontier 10 ⟨67392, by decide⟩
    (prefixCache 11 1355) (prefixPartial 11 1355) = false := by
  decide +kernel

theorem node_context_11_1355_67392 : EJMOriginalGlobalDAGData.nodes 10 ⟨67392, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨67391, by decide⟩,⟨4596, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1355_67392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1355 ⟨67392, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1355
    ⟨67392, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨67391, by decide⟩,⟨4596, by decide⟩]) unmarked_context_11_1355_67392 node_context_11_1355_67392
  intro a
  fin_cases a
  · exact context_12_5420_1738
  · exact context_12_5421_1738
  · exact context_12_5422_67391
  · exact context_12_5423_4596

theorem unmarked_context_10_338_67393 : frontier 11 ⟨67393, by decide⟩
    (prefixCache 10 338) (prefixPartial 10 338) = false := by
  decide +kernel

theorem node_context_10_338_67393 : EJMOriginalGlobalDAGData.nodes 11 ⟨67393, by decide⟩ =
    .split (coordinate 10) (![⟨66882, by decide⟩,⟨67092, by decide⟩,⟨67288, by decide⟩,⟨67392, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_338_67393 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 338 ⟨67393, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 338
    ⟨67393, by decide⟩ (by decide) (![⟨66882, by decide⟩,⟨67092, by decide⟩,⟨67288, by decide⟩,⟨67392, by decide⟩]) unmarked_context_10_338_67393 node_context_10_338_67393
  intro a
  fin_cases a
  · exact context_11_1352_66882
  · exact context_11_1353_67092
  · exact context_11_1354_67288
  · exact context_11_1355_67392

theorem selected_cut_02031 : selected 11 ⟨3440, by decide⟩
    (prefixPartial 10 339) = some ⟨10, 1, 0, 3440, 339, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_339_3440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 339 ⟨3440, by decide⟩ :=
  accepted_of_selected 10 339 ⟨3440, by decide⟩ ⟨10, 1, 0, 3440, 339, 1, 1048576⟩
    (by decide) selected_cut_02031

theorem unmarked_context_9_84_67394 : frontier 12 ⟨67394, by decide⟩
    (prefixCache 9 84) (prefixPartial 9 84) = false := by
  decide +kernel

theorem node_context_9_84_67394 : EJMOriginalGlobalDAGData.nodes 12 ⟨67394, by decide⟩ =
    .split (coordinate 9) (![⟨65686, by decide⟩,⟨66614, by decide⟩,⟨67393, by decide⟩,⟨3440, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_84_67394 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 84 ⟨67394, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 84
    ⟨67394, by decide⟩ (by decide) (![⟨65686, by decide⟩,⟨66614, by decide⟩,⟨67393, by decide⟩,⟨3440, by decide⟩]) unmarked_context_9_84_67394 node_context_9_84_67394
  intro a
  fin_cases a
  · exact context_10_336_65686
  · exact context_10_337_66614
  · exact context_10_338_67393
  · exact context_10_339_3440

theorem selected_cut_02032 : selected 9 ⟨67437, by decide⟩
    (prefixPartial 12 5440) = some ⟨12, 2, 0, 67437, 5440, 1713, 65536⟩ := by
  decide +kernel

theorem context_12_5440_67437 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5440 ⟨67437, by decide⟩ :=
  accepted_of_selected 12 5440 ⟨67437, by decide⟩ ⟨12, 2, 0, 67437, 5440, 1713, 65536⟩
    (by decide) selected_cut_02032

theorem selected_cut_02033 : selected 9 ⟨67480, by decide⟩
    (prefixPartial 12 5441) = some ⟨12, 2, 0, 67480, 5441, 2465, 65536⟩ := by
  decide +kernel

theorem context_12_5441_67480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5441 ⟨67480, by decide⟩ :=
  accepted_of_selected 12 5441 ⟨67480, by decide⟩ ⟨12, 2, 0, 67480, 5441, 2465, 65536⟩
    (by decide) selected_cut_02033

theorem selected_cut_02034 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 21768) = some ⟨13, 1, 0, 3444, 21768, 1, 16384⟩ := by
  decide +kernel

theorem context_13_21768_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21768 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 21768 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 21768, 1, 16384⟩
    (by decide) selected_cut_02034

theorem selected_cut_02035 : selected 8 ⟨67514, by decide⟩
    (prefixPartial 13 21769) = some ⟨13, 2, 0, 67514, 21769, 2105, 16384⟩ := by
  decide +kernel

theorem context_13_21769_67514 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21769 ⟨67514, by decide⟩ :=
  accepted_of_selected 13 21769 ⟨67514, by decide⟩ ⟨13, 2, 0, 67514, 21769, 2105, 16384⟩
    (by decide) selected_cut_02035

theorem selected_cut_02036 : selected 8 ⟨67543, by decide⟩
    (prefixPartial 13 21770) = some ⟨13, 2, 0, 67543, 21770, 2229, 16384⟩ := by
  decide +kernel

theorem context_13_21770_67543 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21770 ⟨67543, by decide⟩ :=
  accepted_of_selected 13 21770 ⟨67543, by decide⟩ ⟨13, 2, 0, 67543, 21770, 2229, 16384⟩
    (by decide) selected_cut_02036

theorem selected_cut_02037 : selected 8 ⟨67556, by decide⟩
    (prefixPartial 13 21771) = some ⟨13, 2, 0, 67556, 21771, 1109, 16384⟩ := by
  decide +kernel

theorem context_13_21771_67556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21771 ⟨67556, by decide⟩ :=
  accepted_of_selected 13 21771 ⟨67556, by decide⟩ ⟨13, 2, 0, 67556, 21771, 1109, 16384⟩
    (by decide) selected_cut_02037

theorem unmarked_context_12_5442_67557 : frontier 9 ⟨67557, by decide⟩
    (prefixCache 12 5442) (prefixPartial 12 5442) = false := by
  decide +kernel

theorem node_context_12_5442_67557 : EJMOriginalGlobalDAGData.nodes 9 ⟨67557, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨67514, by decide⟩,⟨67543, by decide⟩,⟨67556, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5442_67557 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5442 ⟨67557, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5442
    ⟨67557, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨67514, by decide⟩,⟨67543, by decide⟩,⟨67556, by decide⟩]) unmarked_context_12_5442_67557 node_context_12_5442_67557
  intro a
  fin_cases a
  · exact context_13_21768_3444
  · exact context_13_21769_67514
  · exact context_13_21770_67543
  · exact context_13_21771_67556

theorem selected_cut_02038 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 5443) = some ⟨12, 1, 0, 893, 5443, 1, 65536⟩ := by
  decide +kernel

theorem context_12_5443_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5443 ⟨893, by decide⟩ :=
  accepted_of_selected 12 5443 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 5443, 1, 65536⟩
    (by decide) selected_cut_02038

theorem unmarked_context_11_1360_67558 : frontier 10 ⟨67558, by decide⟩
    (prefixCache 11 1360) (prefixPartial 11 1360) = false := by
  decide +kernel

theorem node_context_11_1360_67558 : EJMOriginalGlobalDAGData.nodes 10 ⟨67558, by decide⟩ =
    .split (coordinate 11) (![⟨67437, by decide⟩,⟨67480, by decide⟩,⟨67557, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1360_67558 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1360 ⟨67558, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1360
    ⟨67558, by decide⟩ (by decide) (![⟨67437, by decide⟩,⟨67480, by decide⟩,⟨67557, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_1360_67558 node_context_11_1360_67558
  intro a
  fin_cases a
  · exact context_12_5440_67437
  · exact context_12_5441_67480
  · exact context_12_5442_67557
  · exact context_12_5443_893

theorem selected_cut_02039 : selected 9 ⟨67594, by decide⟩
    (prefixPartial 12 5444) = some ⟨12, 2, 0, 67594, 5444, 1513, 65536⟩ := by
  decide +kernel

theorem context_12_5444_67594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5444 ⟨67594, by decide⟩ :=
  accepted_of_selected 12 5444 ⟨67594, by decide⟩ ⟨12, 2, 0, 67594, 5444, 1513, 65536⟩
    (by decide) selected_cut_02039

theorem selected_cut_02040 : selected 9 ⟨67657, by decide⟩
    (prefixPartial 12 5445) = some ⟨12, 2, 0, 67657, 5445, 3677, 65536⟩ := by
  decide +kernel

theorem context_12_5445_67657 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5445 ⟨67657, by decide⟩ :=
  accepted_of_selected 12 5445 ⟨67657, by decide⟩ ⟨12, 2, 0, 67657, 5445, 3677, 65536⟩
    (by decide) selected_cut_02040

theorem selected_cut_02041 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 21784) = some ⟨13, 1, 0, 3444, 21784, 1, 16384⟩ := by
  decide +kernel

theorem context_13_21784_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21784 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 21784 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 21784, 1, 16384⟩
    (by decide) selected_cut_02041

theorem selected_cut_02042 : selected 8 ⟨67685, by decide⟩
    (prefixPartial 13 21785) = some ⟨13, 2, 0, 67685, 21785, 1693, 16384⟩ := by
  decide +kernel

theorem context_13_21785_67685 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21785 ⟨67685, by decide⟩ :=
  accepted_of_selected 13 21785 ⟨67685, by decide⟩ ⟨13, 2, 0, 67685, 21785, 1693, 16384⟩
    (by decide) selected_cut_02042

theorem selected_cut_02043 : selected 8 ⟨67713, by decide⟩
    (prefixPartial 13 21786) = some ⟨13, 2, 0, 67713, 21786, 1761, 16384⟩ := by
  decide +kernel

theorem context_13_21786_67713 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21786 ⟨67713, by decide⟩ :=
  accepted_of_selected 13 21786 ⟨67713, by decide⟩ ⟨13, 2, 0, 67713, 21786, 1761, 16384⟩
    (by decide) selected_cut_02043

theorem selected_cut_02044 : selected 8 ⟨67729, by decide⟩
    (prefixPartial 13 21787) = some ⟨13, 2, 0, 67729, 21787, 1093, 16384⟩ := by
  decide +kernel

theorem context_13_21787_67729 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21787 ⟨67729, by decide⟩ :=
  accepted_of_selected 13 21787 ⟨67729, by decide⟩ ⟨13, 2, 0, 67729, 21787, 1093, 16384⟩
    (by decide) selected_cut_02044

theorem unmarked_context_12_5446_67730 : frontier 9 ⟨67730, by decide⟩
    (prefixCache 12 5446) (prefixPartial 12 5446) = false := by
  decide +kernel

theorem node_context_12_5446_67730 : EJMOriginalGlobalDAGData.nodes 9 ⟨67730, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨67685, by decide⟩,⟨67713, by decide⟩,⟨67729, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5446_67730 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5446 ⟨67730, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5446
    ⟨67730, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨67685, by decide⟩,⟨67713, by decide⟩,⟨67729, by decide⟩]) unmarked_context_12_5446_67730 node_context_12_5446_67730
  intro a
  fin_cases a
  · exact context_13_21784_3444
  · exact context_13_21785_67685
  · exact context_13_21786_67713
  · exact context_13_21787_67729

theorem selected_cut_02045 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 5447) = some ⟨12, 1, 0, 893, 5447, 1, 65536⟩ := by
  decide +kernel

theorem context_12_5447_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5447 ⟨893, by decide⟩ :=
  accepted_of_selected 12 5447 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 5447, 1, 65536⟩
    (by decide) selected_cut_02045

theorem unmarked_context_11_1361_67731 : frontier 10 ⟨67731, by decide⟩
    (prefixCache 11 1361) (prefixPartial 11 1361) = false := by
  decide +kernel

theorem node_context_11_1361_67731 : EJMOriginalGlobalDAGData.nodes 10 ⟨67731, by decide⟩ =
    .split (coordinate 11) (![⟨67594, by decide⟩,⟨67657, by decide⟩,⟨67730, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1361_67731 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1361 ⟨67731, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1361
    ⟨67731, by decide⟩ (by decide) (![⟨67594, by decide⟩,⟨67657, by decide⟩,⟨67730, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_1361_67731 node_context_11_1361_67731
  intro a
  fin_cases a
  · exact context_12_5444_67594
  · exact context_12_5445_67657
  · exact context_12_5446_67730
  · exact context_12_5447_893

theorem selected_cut_02046 : selected 9 ⟨67804, by decide⟩
    (prefixPartial 12 5448) = some ⟨12, 2, 0, 67804, 5448, 3501, 65536⟩ := by
  decide +kernel

theorem context_12_5448_67804 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5448 ⟨67804, by decide⟩ :=
  accepted_of_selected 12 5448 ⟨67804, by decide⟩ ⟨12, 2, 0, 67804, 5448, 3501, 65536⟩
    (by decide) selected_cut_02046

theorem selected_cut_02047 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 21796) = some ⟨13, 1, 0, 3444, 21796, 1, 16384⟩ := by
  decide +kernel

theorem context_13_21796_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21796 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 21796 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 21796, 1, 16384⟩
    (by decide) selected_cut_02047

theorem selected_cut_02048 : selected 8 ⟨67836, by decide⟩
    (prefixPartial 13 21797) = some ⟨13, 2, 0, 67836, 21797, 1733, 16384⟩ := by
  decide +kernel

theorem context_13_21797_67836 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21797 ⟨67836, by decide⟩ :=
  accepted_of_selected 13 21797 ⟨67836, by decide⟩ ⟨13, 2, 0, 67836, 21797, 1733, 16384⟩
    (by decide) selected_cut_02048

theorem selected_cut_02049 : selected 8 ⟨67866, by decide⟩
    (prefixPartial 13 21798) = some ⟨13, 2, 0, 67866, 21798, 2137, 16384⟩ := by
  decide +kernel

theorem context_13_21798_67866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21798 ⟨67866, by decide⟩ :=
  accepted_of_selected 13 21798 ⟨67866, by decide⟩ ⟨13, 2, 0, 67866, 21798, 2137, 16384⟩
    (by decide) selected_cut_02049

theorem selected_cut_02050 : selected 8 ⟨67880, by decide⟩
    (prefixPartial 13 21799) = some ⟨13, 2, 0, 67880, 21799, 1093, 16384⟩ := by
  decide +kernel

theorem context_13_21799_67880 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21799 ⟨67880, by decide⟩ :=
  accepted_of_selected 13 21799 ⟨67880, by decide⟩ ⟨13, 2, 0, 67880, 21799, 1093, 16384⟩
    (by decide) selected_cut_02050

theorem unmarked_context_12_5449_67881 : frontier 9 ⟨67881, by decide⟩
    (prefixCache 12 5449) (prefixPartial 12 5449) = false := by
  decide +kernel

theorem node_context_12_5449_67881 : EJMOriginalGlobalDAGData.nodes 9 ⟨67881, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨67836, by decide⟩,⟨67866, by decide⟩,⟨67880, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5449_67881 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5449 ⟨67881, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5449
    ⟨67881, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨67836, by decide⟩,⟨67866, by decide⟩,⟨67880, by decide⟩]) unmarked_context_12_5449_67881 node_context_12_5449_67881
  intro a
  fin_cases a
  · exact context_13_21796_3444
  · exact context_13_21797_67836
  · exact context_13_21798_67866
  · exact context_13_21799_67880

theorem selected_cut_02051 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 21800) = some ⟨13, 1, 0, 3444, 21800, 1, 16384⟩ := by
  decide +kernel

theorem context_13_21800_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21800 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 21800 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 21800, 1, 16384⟩
    (by decide) selected_cut_02051

theorem selected_cut_02052 : selected 8 ⟨67916, by decide⟩
    (prefixPartial 13 21801) = some ⟨13, 2, 0, 67916, 21801, 1877, 16384⟩ := by
  decide +kernel

theorem context_13_21801_67916 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21801 ⟨67916, by decide⟩ :=
  accepted_of_selected 13 21801 ⟨67916, by decide⟩ ⟨13, 2, 0, 67916, 21801, 1877, 16384⟩
    (by decide) selected_cut_02052

theorem selected_cut_02053 : selected 8 ⟨67947, by decide⟩
    (prefixPartial 13 21802) = some ⟨13, 2, 0, 67947, 21802, 2201, 16384⟩ := by
  decide +kernel

theorem context_13_21802_67947 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21802 ⟨67947, by decide⟩ :=
  accepted_of_selected 13 21802 ⟨67947, by decide⟩ ⟨13, 2, 0, 67947, 21802, 2201, 16384⟩
    (by decide) selected_cut_02053

theorem selected_cut_02054 : selected 8 ⟨67969, by decide⟩
    (prefixPartial 13 21803) = some ⟨13, 2, 0, 67969, 21803, 1189, 16384⟩ := by
  decide +kernel

theorem context_13_21803_67969 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21803 ⟨67969, by decide⟩ :=
  accepted_of_selected 13 21803 ⟨67969, by decide⟩ ⟨13, 2, 0, 67969, 21803, 1189, 16384⟩
    (by decide) selected_cut_02054

theorem unmarked_context_12_5450_67970 : frontier 9 ⟨67970, by decide⟩
    (prefixCache 12 5450) (prefixPartial 12 5450) = false := by
  decide +kernel

theorem node_context_12_5450_67970 : EJMOriginalGlobalDAGData.nodes 9 ⟨67970, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨67916, by decide⟩,⟨67947, by decide⟩,⟨67969, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5450_67970 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5450 ⟨67970, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5450
    ⟨67970, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨67916, by decide⟩,⟨67947, by decide⟩,⟨67969, by decide⟩]) unmarked_context_12_5450_67970 node_context_12_5450_67970
  intro a
  fin_cases a
  · exact context_13_21800_3444
  · exact context_13_21801_67916
  · exact context_13_21802_67947
  · exact context_13_21803_67969

theorem selected_cut_02055 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 21804) = some ⟨13, 1, 0, 3444, 21804, 1, 16384⟩ := by
  decide +kernel

theorem context_13_21804_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21804 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 21804 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 21804, 1, 16384⟩
    (by decide) selected_cut_02055

theorem selected_cut_02056 : selected 8 ⟨68006, by decide⟩
    (prefixPartial 13 21805) = some ⟨13, 2, 0, 68006, 21805, 1757, 16384⟩ := by
  decide +kernel

theorem context_13_21805_68006 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21805 ⟨68006, by decide⟩ :=
  accepted_of_selected 13 21805 ⟨68006, by decide⟩ ⟨13, 2, 0, 68006, 21805, 1757, 16384⟩
    (by decide) selected_cut_02056

theorem selected_cut_02057 : selected 8 ⟨68044, by decide⟩
    (prefixPartial 13 21806) = some ⟨13, 2, 0, 68044, 21806, 2509, 16384⟩ := by
  decide +kernel

theorem context_13_21806_68044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21806 ⟨68044, by decide⟩ :=
  accepted_of_selected 13 21806 ⟨68044, by decide⟩ ⟨13, 2, 0, 68044, 21806, 2509, 16384⟩
    (by decide) selected_cut_02057

theorem selected_cut_02058 : selected 8 ⟨68062, by decide⟩
    (prefixPartial 13 21807) = some ⟨13, 2, 0, 68062, 21807, 1081, 16384⟩ := by
  decide +kernel

theorem context_13_21807_68062 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21807 ⟨68062, by decide⟩ :=
  accepted_of_selected 13 21807 ⟨68062, by decide⟩ ⟨13, 2, 0, 68062, 21807, 1081, 16384⟩
    (by decide) selected_cut_02058

theorem unmarked_context_12_5451_68063 : frontier 9 ⟨68063, by decide⟩
    (prefixCache 12 5451) (prefixPartial 12 5451) = false := by
  decide +kernel

theorem node_context_12_5451_68063 : EJMOriginalGlobalDAGData.nodes 9 ⟨68063, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨68006, by decide⟩,⟨68044, by decide⟩,⟨68062, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5451_68063 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5451 ⟨68063, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5451
    ⟨68063, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨68006, by decide⟩,⟨68044, by decide⟩,⟨68062, by decide⟩]) unmarked_context_12_5451_68063 node_context_12_5451_68063
  intro a
  fin_cases a
  · exact context_13_21804_3444
  · exact context_13_21805_68006
  · exact context_13_21806_68044
  · exact context_13_21807_68062

theorem unmarked_context_11_1362_68064 : frontier 10 ⟨68064, by decide⟩
    (prefixCache 11 1362) (prefixPartial 11 1362) = false := by
  decide +kernel

theorem node_context_11_1362_68064 : EJMOriginalGlobalDAGData.nodes 10 ⟨68064, by decide⟩ =
    .split (coordinate 11) (![⟨67804, by decide⟩,⟨67881, by decide⟩,⟨67970, by decide⟩,⟨68063, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1362_68064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1362 ⟨68064, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1362
    ⟨68064, by decide⟩ (by decide) (![⟨67804, by decide⟩,⟨67881, by decide⟩,⟨67970, by decide⟩,⟨68063, by decide⟩]) unmarked_context_11_1362_68064 node_context_11_1362_68064
  intro a
  fin_cases a
  · exact context_12_5448_67804
  · exact context_12_5449_67881
  · exact context_12_5450_67970
  · exact context_12_5451_68063

theorem selected_cut_02059 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 1363) = some ⟨11, 1, 0, 1736, 1363, 1, 262144⟩ := by
  decide +kernel

theorem context_11_1363_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1363 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 1363 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 1363, 1, 262144⟩
    (by decide) selected_cut_02059

theorem unmarked_context_10_340_68065 : frontier 11 ⟨68065, by decide⟩
    (prefixCache 10 340) (prefixPartial 10 340) = false := by
  decide +kernel

theorem node_context_10_340_68065 : EJMOriginalGlobalDAGData.nodes 11 ⟨68065, by decide⟩ =
    .split (coordinate 10) (![⟨67558, by decide⟩,⟨67731, by decide⟩,⟨68064, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_340_68065 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 340 ⟨68065, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 340
    ⟨68065, by decide⟩ (by decide) (![⟨67558, by decide⟩,⟨67731, by decide⟩,⟨68064, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_340_68065 node_context_10_340_68065
  intro a
  fin_cases a
  · exact context_11_1360_67558
  · exact context_11_1361_67731
  · exact context_11_1362_68064
  · exact context_11_1363_1736

theorem selected_cut_02060 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 5456) = some ⟨12, 1, 0, 1738, 5456, 1, 65536⟩ := by
  decide +kernel

theorem context_12_5456_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5456 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 5456 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 5456, 1, 65536⟩
    (by decide) selected_cut_02060

theorem selected_cut_02061 : selected 9 ⟨68105, by decide⟩
    (prefixPartial 12 5457) = some ⟨12, 2, 0, 68105, 5457, 1617, 65536⟩ := by
  decide +kernel

theorem context_12_5457_68105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5457 ⟨68105, by decide⟩ :=
  accepted_of_selected 12 5457 ⟨68105, by decide⟩ ⟨12, 2, 0, 68105, 5457, 1617, 65536⟩
    (by decide) selected_cut_02061

theorem selected_cut_02062 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 21832) = some ⟨13, 1, 0, 3444, 21832, 1, 16384⟩ := by
  decide +kernel

theorem context_13_21832_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21832 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 21832 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 21832, 1, 16384⟩
    (by decide) selected_cut_02062

theorem selected_cut_02063 : selected 8 ⟨68132, by decide⟩
    (prefixPartial 13 21833) = some ⟨13, 2, 0, 68132, 21833, 1377, 16384⟩ := by
  decide +kernel

theorem context_13_21833_68132 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21833 ⟨68132, by decide⟩ :=
  accepted_of_selected 13 21833 ⟨68132, by decide⟩ ⟨13, 2, 0, 68132, 21833, 1377, 16384⟩
    (by decide) selected_cut_02063

theorem selected_cut_02064 : selected 8 ⟨68160, by decide⟩
    (prefixPartial 13 21834) = some ⟨13, 2, 0, 68160, 21834, 2617, 16384⟩ := by
  decide +kernel

theorem context_13_21834_68160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21834 ⟨68160, by decide⟩ :=
  accepted_of_selected 13 21834 ⟨68160, by decide⟩ ⟨13, 2, 0, 68160, 21834, 2617, 16384⟩
    (by decide) selected_cut_02064

theorem selected_cut_02065 : selected 8 ⟨68177, by decide⟩
    (prefixPartial 13 21835) = some ⟨13, 2, 0, 68177, 21835, 1261, 16384⟩ := by
  decide +kernel

theorem context_13_21835_68177 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21835 ⟨68177, by decide⟩ :=
  accepted_of_selected 13 21835 ⟨68177, by decide⟩ ⟨13, 2, 0, 68177, 21835, 1261, 16384⟩
    (by decide) selected_cut_02065

theorem unmarked_context_12_5458_68178 : frontier 9 ⟨68178, by decide⟩
    (prefixCache 12 5458) (prefixPartial 12 5458) = false := by
  decide +kernel

theorem node_context_12_5458_68178 : EJMOriginalGlobalDAGData.nodes 9 ⟨68178, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨68132, by decide⟩,⟨68160, by decide⟩,⟨68177, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5458_68178 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5458 ⟨68178, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5458
    ⟨68178, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨68132, by decide⟩,⟨68160, by decide⟩,⟨68177, by decide⟩]) unmarked_context_12_5458_68178 node_context_12_5458_68178
  intro a
  fin_cases a
  · exact context_13_21832_3444
  · exact context_13_21833_68132
  · exact context_13_21834_68160
  · exact context_13_21835_68177

theorem selected_cut_02066 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 5459) = some ⟨12, 1, 0, 893, 5459, 1, 65536⟩ := by
  decide +kernel

theorem context_12_5459_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5459 ⟨893, by decide⟩ :=
  accepted_of_selected 12 5459 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 5459, 1, 65536⟩
    (by decide) selected_cut_02066

theorem unmarked_context_11_1364_68179 : frontier 10 ⟨68179, by decide⟩
    (prefixCache 11 1364) (prefixPartial 11 1364) = false := by
  decide +kernel

theorem node_context_11_1364_68179 : EJMOriginalGlobalDAGData.nodes 10 ⟨68179, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨68105, by decide⟩,⟨68178, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1364_68179 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1364 ⟨68179, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1364
    ⟨68179, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨68105, by decide⟩,⟨68178, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_1364_68179 node_context_11_1364_68179
  intro a
  fin_cases a
  · exact context_12_5456_1738
  · exact context_12_5457_68105
  · exact context_12_5458_68178
  · exact context_12_5459_893

theorem selected_cut_02067 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 5460) = some ⟨12, 1, 0, 1738, 5460, 1, 65536⟩ := by
  decide +kernel

theorem context_12_5460_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5460 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 5460 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 5460, 1, 65536⟩
    (by decide) selected_cut_02067

theorem selected_cut_02068 : selected 9 ⟨68180, by decide⟩
    (prefixPartial 12 5461) = some ⟨12, 1, 0, 68180, 5461, 1, 65536⟩ := by
  decide +kernel

theorem context_12_5461_68180 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5461 ⟨68180, by decide⟩ :=
  accepted_of_selected 12 5461 ⟨68180, by decide⟩ ⟨12, 1, 0, 68180, 5461, 1, 65536⟩
    (by decide) selected_cut_02068

theorem selected_cut_02069 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 21848) = some ⟨13, 1, 0, 3444, 21848, 1, 16384⟩ := by
  decide +kernel

theorem context_13_21848_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21848 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 21848 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 21848, 1, 16384⟩
    (by decide) selected_cut_02069

theorem selected_cut_02070 : selected 8 ⟨68220, by decide⟩
    (prefixPartial 13 21849) = some ⟨13, 2, 0, 68220, 21849, 2157, 16384⟩ := by
  decide +kernel

theorem context_13_21849_68220 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21849 ⟨68220, by decide⟩ :=
  accepted_of_selected 13 21849 ⟨68220, by decide⟩ ⟨13, 2, 0, 68220, 21849, 2157, 16384⟩
    (by decide) selected_cut_02070

theorem selected_cut_02071 : selected 8 ⟨68278, by decide⟩
    (prefixPartial 13 21850) = some ⟨13, 2, 0, 68278, 21850, 3265, 16384⟩ := by
  decide +kernel

theorem context_13_21850_68278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21850 ⟨68278, by decide⟩ :=
  accepted_of_selected 13 21850 ⟨68278, by decide⟩ ⟨13, 2, 0, 68278, 21850, 3265, 16384⟩
    (by decide) selected_cut_02071

theorem selected_cut_02072 : selected 8 ⟨68313, by decide⟩
    (prefixPartial 13 21851) = some ⟨13, 2, 0, 68313, 21851, 1709, 16384⟩ := by
  decide +kernel

theorem context_13_21851_68313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21851 ⟨68313, by decide⟩ :=
  accepted_of_selected 13 21851 ⟨68313, by decide⟩ ⟨13, 2, 0, 68313, 21851, 1709, 16384⟩
    (by decide) selected_cut_02072

theorem unmarked_context_12_5462_68314 : frontier 9 ⟨68314, by decide⟩
    (prefixCache 12 5462) (prefixPartial 12 5462) = false := by
  decide +kernel

theorem node_context_12_5462_68314 : EJMOriginalGlobalDAGData.nodes 9 ⟨68314, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨68220, by decide⟩,⟨68278, by decide⟩,⟨68313, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5462_68314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5462 ⟨68314, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5462
    ⟨68314, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨68220, by decide⟩,⟨68278, by decide⟩,⟨68313, by decide⟩]) unmarked_context_12_5462_68314 node_context_12_5462_68314
  intro a
  fin_cases a
  · exact context_13_21848_3444
  · exact context_13_21849_68220
  · exact context_13_21850_68278
  · exact context_13_21851_68313

theorem selected_cut_02073 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 5463) = some ⟨12, 1, 0, 893, 5463, 1, 65536⟩ := by
  decide +kernel

theorem context_12_5463_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5463 ⟨893, by decide⟩ :=
  accepted_of_selected 12 5463 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 5463, 1, 65536⟩
    (by decide) selected_cut_02073

theorem unmarked_context_11_1365_68315 : frontier 10 ⟨68315, by decide⟩
    (prefixCache 11 1365) (prefixPartial 11 1365) = false := by
  decide +kernel

theorem node_context_11_1365_68315 : EJMOriginalGlobalDAGData.nodes 10 ⟨68315, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨68180, by decide⟩,⟨68314, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1365_68315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1365 ⟨68315, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1365
    ⟨68315, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨68180, by decide⟩,⟨68314, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_1365_68315 node_context_11_1365_68315
  intro a
  fin_cases a
  · exact context_12_5460_1738
  · exact context_12_5461_68180
  · exact context_12_5462_68314
  · exact context_12_5463_893

theorem selected_cut_02074 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 5464) = some ⟨12, 1, 0, 1738, 5464, 1, 65536⟩ := by
  decide +kernel

theorem context_12_5464_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5464 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 5464 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 5464, 1, 65536⟩
    (by decide) selected_cut_02074

theorem selected_cut_02075 : selected 9 ⟨68368, by decide⟩
    (prefixPartial 12 5465) = some ⟨12, 2, 0, 68368, 5465, 3165, 65536⟩ := by
  decide +kernel

theorem context_12_5465_68368 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5465 ⟨68368, by decide⟩ :=
  accepted_of_selected 12 5465 ⟨68368, by decide⟩ ⟨12, 2, 0, 68368, 5465, 3165, 65536⟩
    (by decide) selected_cut_02075

theorem selected_cut_02076 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 21864) = some ⟨13, 1, 0, 3444, 21864, 1, 16384⟩ := by
  decide +kernel

theorem context_13_21864_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21864 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 21864 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 21864, 1, 16384⟩
    (by decide) selected_cut_02076

theorem selected_cut_02077 : selected 8 ⟨68386, by decide⟩
    (prefixPartial 13 21865) = some ⟨13, 2, 0, 68386, 21865, 1161, 16384⟩ := by
  decide +kernel

theorem context_13_21865_68386 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21865 ⟨68386, by decide⟩ :=
  accepted_of_selected 13 21865 ⟨68386, by decide⟩ ⟨13, 2, 0, 68386, 21865, 1161, 16384⟩
    (by decide) selected_cut_02077

theorem selected_cut_02078 : selected 8 ⟨68412, by decide⟩
    (prefixPartial 13 21866) = some ⟨13, 2, 0, 68412, 21866, 2581, 16384⟩ := by
  decide +kernel

theorem context_13_21866_68412 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21866 ⟨68412, by decide⟩ :=
  accepted_of_selected 13 21866 ⟨68412, by decide⟩ ⟨13, 2, 0, 68412, 21866, 2581, 16384⟩
    (by decide) selected_cut_02078

theorem selected_cut_02079 : selected 8 ⟨68425, by decide⟩
    (prefixPartial 13 21867) = some ⟨13, 2, 0, 68425, 21867, 1341, 16384⟩ := by
  decide +kernel

theorem context_13_21867_68425 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21867 ⟨68425, by decide⟩ :=
  accepted_of_selected 13 21867 ⟨68425, by decide⟩ ⟨13, 2, 0, 68425, 21867, 1341, 16384⟩
    (by decide) selected_cut_02079

theorem unmarked_context_12_5466_68426 : frontier 9 ⟨68426, by decide⟩
    (prefixCache 12 5466) (prefixPartial 12 5466) = false := by
  decide +kernel

theorem node_context_12_5466_68426 : EJMOriginalGlobalDAGData.nodes 9 ⟨68426, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨68386, by decide⟩,⟨68412, by decide⟩,⟨68425, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5466_68426 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5466 ⟨68426, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5466
    ⟨68426, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨68386, by decide⟩,⟨68412, by decide⟩,⟨68425, by decide⟩]) unmarked_context_12_5466_68426 node_context_12_5466_68426
  intro a
  fin_cases a
  · exact context_13_21864_3444
  · exact context_13_21865_68386
  · exact context_13_21866_68412
  · exact context_13_21867_68425

theorem selected_cut_02080 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 21868) = some ⟨13, 1, 0, 3444, 21868, 1, 16384⟩ := by
  decide +kernel

theorem context_13_21868_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21868 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 21868 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 21868, 1, 16384⟩
    (by decide) selected_cut_02080

theorem selected_cut_02081 : selected 8 ⟨68448, by decide⟩
    (prefixPartial 13 21869) = some ⟨13, 2, 0, 68448, 21869, 1045, 16384⟩ := by
  decide +kernel

theorem context_13_21869_68448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21869 ⟨68448, by decide⟩ :=
  accepted_of_selected 13 21869 ⟨68448, by decide⟩ ⟨13, 2, 0, 68448, 21869, 1045, 16384⟩
    (by decide) selected_cut_02081

theorem selected_cut_02082 : selected 8 ⟨68481, by decide⟩
    (prefixPartial 13 21870) = some ⟨13, 2, 0, 68481, 21870, 2721, 16384⟩ := by
  decide +kernel

theorem context_13_21870_68481 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21870 ⟨68481, by decide⟩ :=
  accepted_of_selected 13 21870 ⟨68481, by decide⟩ ⟨13, 2, 0, 68481, 21870, 2721, 16384⟩
    (by decide) selected_cut_02082

theorem selected_cut_02083 : selected 8 ⟨68495, by decide⟩
    (prefixPartial 13 21871) = some ⟨13, 2, 0, 68495, 21871, 1317, 16384⟩ := by
  decide +kernel

theorem context_13_21871_68495 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21871 ⟨68495, by decide⟩ :=
  accepted_of_selected 13 21871 ⟨68495, by decide⟩ ⟨13, 2, 0, 68495, 21871, 1317, 16384⟩
    (by decide) selected_cut_02083

theorem unmarked_context_12_5467_68496 : frontier 9 ⟨68496, by decide⟩
    (prefixCache 12 5467) (prefixPartial 12 5467) = false := by
  decide +kernel

theorem node_context_12_5467_68496 : EJMOriginalGlobalDAGData.nodes 9 ⟨68496, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨68448, by decide⟩,⟨68481, by decide⟩,⟨68495, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5467_68496 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5467 ⟨68496, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5467
    ⟨68496, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨68448, by decide⟩,⟨68481, by decide⟩,⟨68495, by decide⟩]) unmarked_context_12_5467_68496 node_context_12_5467_68496
  intro a
  fin_cases a
  · exact context_13_21868_3444
  · exact context_13_21869_68448
  · exact context_13_21870_68481
  · exact context_13_21871_68495

theorem unmarked_context_11_1366_68497 : frontier 10 ⟨68497, by decide⟩
    (prefixCache 11 1366) (prefixPartial 11 1366) = false := by
  decide +kernel

theorem node_context_11_1366_68497 : EJMOriginalGlobalDAGData.nodes 10 ⟨68497, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨68368, by decide⟩,⟨68426, by decide⟩,⟨68496, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1366_68497 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1366 ⟨68497, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1366
    ⟨68497, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨68368, by decide⟩,⟨68426, by decide⟩,⟨68496, by decide⟩]) unmarked_context_11_1366_68497 node_context_11_1366_68497
  intro a
  fin_cases a
  · exact context_12_5464_1738
  · exact context_12_5465_68368
  · exact context_12_5466_68426
  · exact context_12_5467_68496

theorem selected_cut_02084 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 1367) = some ⟨11, 1, 0, 1736, 1367, 1, 262144⟩ := by
  decide +kernel

theorem context_11_1367_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1367 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 1367 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 1367, 1, 262144⟩
    (by decide) selected_cut_02084

theorem unmarked_context_10_341_68498 : frontier 11 ⟨68498, by decide⟩
    (prefixCache 10 341) (prefixPartial 10 341) = false := by
  decide +kernel

theorem node_context_10_341_68498 : EJMOriginalGlobalDAGData.nodes 11 ⟨68498, by decide⟩ =
    .split (coordinate 10) (![⟨68179, by decide⟩,⟨68315, by decide⟩,⟨68497, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_341_68498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 341 ⟨68498, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 341
    ⟨68498, by decide⟩ (by decide) (![⟨68179, by decide⟩,⟨68315, by decide⟩,⟨68497, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_341_68498 node_context_10_341_68498
  intro a
  fin_cases a
  · exact context_11_1364_68179
  · exact context_11_1365_68315
  · exact context_11_1366_68497
  · exact context_11_1367_1736

theorem selected_cut_02085 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 5472) = some ⟨12, 1, 0, 1738, 5472, 1, 65536⟩ := by
  decide +kernel

theorem context_12_5472_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5472 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 5472 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 5472, 1, 65536⟩
    (by decide) selected_cut_02085

theorem selected_cut_02086 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 5473) = some ⟨12, 1, 0, 1738, 5473, 1, 65536⟩ := by
  decide +kernel

theorem context_12_5473_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5473 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 5473 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 5473, 1, 65536⟩
    (by decide) selected_cut_02086

theorem selected_cut_02087 : selected 9 ⟨68569, by decide⟩
    (prefixPartial 12 5474) = some ⟨12, 2, 0, 68569, 5474, 3609, 65536⟩ := by
  decide +kernel

theorem context_12_5474_68569 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5474 ⟨68569, by decide⟩ :=
  accepted_of_selected 12 5474 ⟨68569, by decide⟩ ⟨12, 2, 0, 68569, 5474, 3609, 65536⟩
    (by decide) selected_cut_02087

theorem selected_cut_02088 : selected 9 ⟨68655, by decide⟩
    (prefixPartial 12 5475) = some ⟨12, 2, 0, 68655, 5475, 3493, 65536⟩ := by
  decide +kernel

theorem context_12_5475_68655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5475 ⟨68655, by decide⟩ :=
  accepted_of_selected 12 5475 ⟨68655, by decide⟩ ⟨12, 2, 0, 68655, 5475, 3493, 65536⟩
    (by decide) selected_cut_02088

theorem unmarked_context_11_1368_68656 : frontier 10 ⟨68656, by decide⟩
    (prefixCache 11 1368) (prefixPartial 11 1368) = false := by
  decide +kernel

theorem node_context_11_1368_68656 : EJMOriginalGlobalDAGData.nodes 10 ⟨68656, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨68569, by decide⟩,⟨68655, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1368_68656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1368 ⟨68656, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1368
    ⟨68656, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨68569, by decide⟩,⟨68655, by decide⟩]) unmarked_context_11_1368_68656 node_context_11_1368_68656
  intro a
  fin_cases a
  · exact context_12_5472_1738
  · exact context_12_5473_1738
  · exact context_12_5474_68569
  · exact context_12_5475_68655

theorem selected_cut_02089 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 5476) = some ⟨12, 1, 0, 1738, 5476, 1, 65536⟩ := by
  decide +kernel

theorem context_12_5476_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5476 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 5476 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 5476, 1, 65536⟩
    (by decide) selected_cut_02089

theorem selected_cut_02090 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 5477) = some ⟨12, 1, 0, 1738, 5477, 1, 65536⟩ := by
  decide +kernel

theorem context_12_5477_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5477 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 5477 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 5477, 1, 65536⟩
    (by decide) selected_cut_02090

theorem selected_cut_02091 : selected 9 ⟨68730, by decide⟩
    (prefixPartial 12 5478) = some ⟨12, 2, 0, 68730, 5478, 2965, 65536⟩ := by
  decide +kernel

theorem context_12_5478_68730 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5478 ⟨68730, by decide⟩ :=
  accepted_of_selected 12 5478 ⟨68730, by decide⟩ ⟨12, 2, 0, 68730, 5478, 2965, 65536⟩
    (by decide) selected_cut_02091

theorem selected_cut_02092 : selected 9 ⟨68793, by decide⟩
    (prefixPartial 12 5479) = some ⟨12, 2, 0, 68793, 5479, 2801, 65536⟩ := by
  decide +kernel

theorem context_12_5479_68793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5479 ⟨68793, by decide⟩ :=
  accepted_of_selected 12 5479 ⟨68793, by decide⟩ ⟨12, 2, 0, 68793, 5479, 2801, 65536⟩
    (by decide) selected_cut_02092

theorem unmarked_context_11_1369_68794 : frontier 10 ⟨68794, by decide⟩
    (prefixCache 11 1369) (prefixPartial 11 1369) = false := by
  decide +kernel

theorem node_context_11_1369_68794 : EJMOriginalGlobalDAGData.nodes 10 ⟨68794, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨68730, by decide⟩,⟨68793, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1369_68794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1369 ⟨68794, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1369
    ⟨68794, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨68730, by decide⟩,⟨68793, by decide⟩]) unmarked_context_11_1369_68794 node_context_11_1369_68794
  intro a
  fin_cases a
  · exact context_12_5476_1738
  · exact context_12_5477_1738
  · exact context_12_5478_68730
  · exact context_12_5479_68793

theorem selected_cut_02093 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 5480) = some ⟨12, 1, 0, 1738, 5480, 1, 65536⟩ := by
  decide +kernel

theorem context_12_5480_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5480 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 5480 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 5480, 1, 65536⟩
    (by decide) selected_cut_02093

theorem selected_cut_02094 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 5481) = some ⟨12, 1, 0, 1738, 5481, 1, 65536⟩ := by
  decide +kernel

theorem context_12_5481_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5481 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 5481 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 5481, 1, 65536⟩
    (by decide) selected_cut_02094

theorem selected_cut_02095 : selected 9 ⟨68847, by decide⟩
    (prefixPartial 12 5482) = some ⟨12, 2, 0, 68847, 5482, 3049, 65536⟩ := by
  decide +kernel

theorem context_12_5482_68847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5482 ⟨68847, by decide⟩ :=
  accepted_of_selected 12 5482 ⟨68847, by decide⟩ ⟨12, 2, 0, 68847, 5482, 3049, 65536⟩
    (by decide) selected_cut_02095

theorem selected_cut_02096 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 21932) = some ⟨13, 1, 0, 3444, 21932, 1, 16384⟩ := by
  decide +kernel

theorem context_13_21932_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21932 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 21932 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 21932, 1, 16384⟩
    (by decide) selected_cut_02096

theorem selected_cut_02097 : selected 8 ⟨68856, by decide⟩
    (prefixPartial 13 21933) = some ⟨13, 2, 0, 68856, 21933, 317, 16384⟩ := by
  decide +kernel

theorem context_13_21933_68856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21933 ⟨68856, by decide⟩ :=
  accepted_of_selected 13 21933 ⟨68856, by decide⟩ ⟨13, 2, 0, 68856, 21933, 317, 16384⟩
    (by decide) selected_cut_02097

theorem selected_cut_02098 : selected 8 ⟨68898, by decide⟩
    (prefixPartial 13 21934) = some ⟨13, 2, 0, 68898, 21934, 2793, 16384⟩ := by
  decide +kernel

theorem context_13_21934_68898 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21934 ⟨68898, by decide⟩ :=
  accepted_of_selected 13 21934 ⟨68898, by decide⟩ ⟨13, 2, 0, 68898, 21934, 2793, 16384⟩
    (by decide) selected_cut_02098

theorem selected_cut_02099 : selected 8 ⟨68915, by decide⟩
    (prefixPartial 13 21935) = some ⟨13, 2, 0, 68915, 21935, 1349, 16384⟩ := by
  decide +kernel

theorem context_13_21935_68915 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 21935 ⟨68915, by decide⟩ :=
  accepted_of_selected 13 21935 ⟨68915, by decide⟩ ⟨13, 2, 0, 68915, 21935, 1349, 16384⟩
    (by decide) selected_cut_02099

theorem unmarked_context_12_5483_68916 : frontier 9 ⟨68916, by decide⟩
    (prefixCache 12 5483) (prefixPartial 12 5483) = false := by
  decide +kernel

theorem node_context_12_5483_68916 : EJMOriginalGlobalDAGData.nodes 9 ⟨68916, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨68856, by decide⟩,⟨68898, by decide⟩,⟨68915, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5483_68916 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5483 ⟨68916, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5483
    ⟨68916, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨68856, by decide⟩,⟨68898, by decide⟩,⟨68915, by decide⟩]) unmarked_context_12_5483_68916 node_context_12_5483_68916
  intro a
  fin_cases a
  · exact context_13_21932_3444
  · exact context_13_21933_68856
  · exact context_13_21934_68898
  · exact context_13_21935_68915

theorem unmarked_context_11_1370_68917 : frontier 10 ⟨68917, by decide⟩
    (prefixCache 11 1370) (prefixPartial 11 1370) = false := by
  decide +kernel

theorem node_context_11_1370_68917 : EJMOriginalGlobalDAGData.nodes 10 ⟨68917, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨68847, by decide⟩,⟨68916, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1370_68917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1370 ⟨68917, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1370
    ⟨68917, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨68847, by decide⟩,⟨68916, by decide⟩]) unmarked_context_11_1370_68917 node_context_11_1370_68917
  intro a
  fin_cases a
  · exact context_12_5480_1738
  · exact context_12_5481_1738
  · exact context_12_5482_68847
  · exact context_12_5483_68916

theorem selected_cut_02100 : selected 10 ⟨68982, by decide⟩
    (prefixPartial 11 1371) = some ⟨11, 2, 0, 68982, 1371, 3057, 262144⟩ := by
  decide +kernel

theorem context_11_1371_68982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1371 ⟨68982, by decide⟩ :=
  accepted_of_selected 11 1371 ⟨68982, by decide⟩ ⟨11, 2, 0, 68982, 1371, 3057, 262144⟩
    (by decide) selected_cut_02100

theorem unmarked_context_10_342_68983 : frontier 11 ⟨68983, by decide⟩
    (prefixCache 10 342) (prefixPartial 10 342) = false := by
  decide +kernel

theorem node_context_10_342_68983 : EJMOriginalGlobalDAGData.nodes 11 ⟨68983, by decide⟩ =
    .split (coordinate 10) (![⟨68656, by decide⟩,⟨68794, by decide⟩,⟨68917, by decide⟩,⟨68982, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_342_68983 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 342 ⟨68983, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 342
    ⟨68983, by decide⟩ (by decide) (![⟨68656, by decide⟩,⟨68794, by decide⟩,⟨68917, by decide⟩,⟨68982, by decide⟩]) unmarked_context_10_342_68983 node_context_10_342_68983
  intro a
  fin_cases a
  · exact context_11_1368_68656
  · exact context_11_1369_68794
  · exact context_11_1370_68917
  · exact context_11_1371_68982

theorem selected_cut_02101 : selected 11 ⟨3440, by decide⟩
    (prefixPartial 10 343) = some ⟨10, 1, 0, 3440, 343, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_343_3440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 343 ⟨3440, by decide⟩ :=
  accepted_of_selected 10 343 ⟨3440, by decide⟩ ⟨10, 1, 0, 3440, 343, 1, 1048576⟩
    (by decide) selected_cut_02101

theorem unmarked_context_9_85_68984 : frontier 12 ⟨68984, by decide⟩
    (prefixCache 9 85) (prefixPartial 9 85) = false := by
  decide +kernel

theorem node_context_9_85_68984 : EJMOriginalGlobalDAGData.nodes 12 ⟨68984, by decide⟩ =
    .split (coordinate 9) (![⟨68065, by decide⟩,⟨68498, by decide⟩,⟨68983, by decide⟩,⟨3440, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_85_68984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 85 ⟨68984, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 85
    ⟨68984, by decide⟩ (by decide) (![⟨68065, by decide⟩,⟨68498, by decide⟩,⟨68983, by decide⟩,⟨3440, by decide⟩]) unmarked_context_9_85_68984 node_context_9_85_68984
  intro a
  fin_cases a
  · exact context_10_340_68065
  · exact context_10_341_68498
  · exact context_10_342_68983
  · exact context_10_343_3440

theorem selected_cut_02102 : selected 9 ⟨69014, by decide⟩
    (prefixPartial 12 5504) = some ⟨12, 2, 0, 69014, 5504, 2029, 65536⟩ := by
  decide +kernel

theorem context_12_5504_69014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5504 ⟨69014, by decide⟩ :=
  accepted_of_selected 12 5504 ⟨69014, by decide⟩ ⟨12, 2, 0, 69014, 5504, 2029, 65536⟩
    (by decide) selected_cut_02102

theorem selected_cut_02103 : selected 9 ⟨69054, by decide⟩
    (prefixPartial 12 5505) = some ⟨12, 2, 0, 69054, 5505, 3217, 65536⟩ := by
  decide +kernel

theorem context_12_5505_69054 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5505 ⟨69054, by decide⟩ :=
  accepted_of_selected 12 5505 ⟨69054, by decide⟩ ⟨12, 2, 0, 69054, 5505, 3217, 65536⟩
    (by decide) selected_cut_02103

theorem selected_cut_02104 : selected 9 ⟨69097, by decide⟩
    (prefixPartial 12 5506) = some ⟨12, 2, 0, 69097, 5506, 3333, 65536⟩ := by
  decide +kernel

theorem context_12_5506_69097 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5506 ⟨69097, by decide⟩ :=
  accepted_of_selected 12 5506 ⟨69097, by decide⟩ ⟨12, 2, 0, 69097, 5506, 3333, 65536⟩
    (by decide) selected_cut_02104

theorem selected_cut_02105 : selected 9 ⟨69142, by decide⟩
    (prefixPartial 12 5507) = some ⟨12, 2, 0, 69142, 5507, 3553, 65536⟩ := by
  decide +kernel

theorem context_12_5507_69142 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5507 ⟨69142, by decide⟩ :=
  accepted_of_selected 12 5507 ⟨69142, by decide⟩ ⟨12, 2, 0, 69142, 5507, 3553, 65536⟩
    (by decide) selected_cut_02105

theorem unmarked_context_11_1376_69143 : frontier 10 ⟨69143, by decide⟩
    (prefixCache 11 1376) (prefixPartial 11 1376) = false := by
  decide +kernel

theorem node_context_11_1376_69143 : EJMOriginalGlobalDAGData.nodes 10 ⟨69143, by decide⟩ =
    .split (coordinate 11) (![⟨69014, by decide⟩,⟨69054, by decide⟩,⟨69097, by decide⟩,⟨69142, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1376_69143 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1376 ⟨69143, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1376
    ⟨69143, by decide⟩ (by decide) (![⟨69014, by decide⟩,⟨69054, by decide⟩,⟨69097, by decide⟩,⟨69142, by decide⟩]) unmarked_context_11_1376_69143 node_context_11_1376_69143
  intro a
  fin_cases a
  · exact context_12_5504_69014
  · exact context_12_5505_69054
  · exact context_12_5506_69097
  · exact context_12_5507_69142

theorem selected_cut_02106 : selected 9 ⟨69178, by decide⟩
    (prefixPartial 12 5508) = some ⟨12, 2, 0, 69178, 5508, 1789, 65536⟩ := by
  decide +kernel

theorem context_12_5508_69178 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5508 ⟨69178, by decide⟩ :=
  accepted_of_selected 12 5508 ⟨69178, by decide⟩ ⟨12, 2, 0, 69178, 5508, 1789, 65536⟩
    (by decide) selected_cut_02106

theorem selected_cut_02107 : selected 9 ⟨69278, by decide⟩
    (prefixPartial 12 5509) = some ⟨12, 2, 0, 69278, 5509, 3921, 65536⟩ := by
  decide +kernel

theorem context_12_5509_69278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5509 ⟨69278, by decide⟩ :=
  accepted_of_selected 12 5509 ⟨69278, by decide⟩ ⟨12, 2, 0, 69278, 5509, 3921, 65536⟩
    (by decide) selected_cut_02107

theorem selected_cut_02108 : selected 9 ⟨69321, by decide⟩
    (prefixPartial 12 5510) = some ⟨12, 2, 0, 69321, 5510, 2805, 65536⟩ := by
  decide +kernel

theorem context_12_5510_69321 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5510 ⟨69321, by decide⟩ :=
  accepted_of_selected 12 5510 ⟨69321, by decide⟩ ⟨12, 2, 0, 69321, 5510, 2805, 65536⟩
    (by decide) selected_cut_02108

theorem selected_cut_02109 : selected 9 ⟨69366, by decide⟩
    (prefixPartial 12 5511) = some ⟨12, 2, 0, 69366, 5511, 2849, 65536⟩ := by
  decide +kernel

theorem context_12_5511_69366 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5511 ⟨69366, by decide⟩ :=
  accepted_of_selected 12 5511 ⟨69366, by decide⟩ ⟨12, 2, 0, 69366, 5511, 2849, 65536⟩
    (by decide) selected_cut_02109

theorem unmarked_context_11_1377_69367 : frontier 10 ⟨69367, by decide⟩
    (prefixCache 11 1377) (prefixPartial 11 1377) = false := by
  decide +kernel

theorem node_context_11_1377_69367 : EJMOriginalGlobalDAGData.nodes 10 ⟨69367, by decide⟩ =
    .split (coordinate 11) (![⟨69178, by decide⟩,⟨69278, by decide⟩,⟨69321, by decide⟩,⟨69366, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1377_69367 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1377 ⟨69367, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1377
    ⟨69367, by decide⟩ (by decide) (![⟨69178, by decide⟩,⟨69278, by decide⟩,⟨69321, by decide⟩,⟨69366, by decide⟩]) unmarked_context_11_1377_69367 node_context_11_1377_69367
  intro a
  fin_cases a
  · exact context_12_5508_69178
  · exact context_12_5509_69278
  · exact context_12_5510_69321
  · exact context_12_5511_69366

theorem selected_cut_02110 : selected 9 ⟨69420, by decide⟩
    (prefixPartial 12 5512) = some ⟨12, 2, 0, 69420, 5512, 2021, 65536⟩ := by
  decide +kernel

theorem context_12_5512_69420 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5512 ⟨69420, by decide⟩ :=
  accepted_of_selected 12 5512 ⟨69420, by decide⟩ ⟨12, 2, 0, 69420, 5512, 2021, 65536⟩
    (by decide) selected_cut_02110

theorem selected_cut_02111 : selected 9 ⟨69485, by decide⟩
    (prefixPartial 12 5513) = some ⟨12, 2, 0, 69485, 5513, 2913, 65536⟩ := by
  decide +kernel

theorem context_12_5513_69485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5513 ⟨69485, by decide⟩ :=
  accepted_of_selected 12 5513 ⟨69485, by decide⟩ ⟨12, 2, 0, 69485, 5513, 2913, 65536⟩
    (by decide) selected_cut_02111

theorem selected_cut_02112 : selected 9 ⟨69547, by decide⟩
    (prefixPartial 12 5514) = some ⟨12, 2, 0, 69547, 5514, 2701, 65536⟩ := by
  decide +kernel

theorem context_12_5514_69547 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5514 ⟨69547, by decide⟩ :=
  accepted_of_selected 12 5514 ⟨69547, by decide⟩ ⟨12, 2, 0, 69547, 5514, 2701, 65536⟩
    (by decide) selected_cut_02112

theorem selected_cut_02113 : selected 9 ⟨69620, by decide⟩
    (prefixPartial 12 5515) = some ⟨12, 2, 0, 69620, 5515, 2877, 65536⟩ := by
  decide +kernel

theorem context_12_5515_69620 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5515 ⟨69620, by decide⟩ :=
  accepted_of_selected 12 5515 ⟨69620, by decide⟩ ⟨12, 2, 0, 69620, 5515, 2877, 65536⟩
    (by decide) selected_cut_02113

theorem unmarked_context_11_1378_69621 : frontier 10 ⟨69621, by decide⟩
    (prefixCache 11 1378) (prefixPartial 11 1378) = false := by
  decide +kernel

theorem node_context_11_1378_69621 : EJMOriginalGlobalDAGData.nodes 10 ⟨69621, by decide⟩ =
    .split (coordinate 11) (![⟨69420, by decide⟩,⟨69485, by decide⟩,⟨69547, by decide⟩,⟨69620, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1378_69621 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1378 ⟨69621, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1378
    ⟨69621, by decide⟩ (by decide) (![⟨69420, by decide⟩,⟨69485, by decide⟩,⟨69547, by decide⟩,⟨69620, by decide⟩]) unmarked_context_11_1378_69621 node_context_11_1378_69621
  intro a
  fin_cases a
  · exact context_12_5512_69420
  · exact context_12_5513_69485
  · exact context_12_5514_69547
  · exact context_12_5515_69620

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
