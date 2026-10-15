/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover063
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_06147 : selected 8 ⟨185398, by decide⟩
    (prefixPartial 13 84327) = some ⟨13, 2, 0, 185398, 84327, 1145, 16384⟩ := by
  decide +kernel

theorem context_13_84327_185398 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84327 ⟨185398, by decide⟩ :=
  accepted_of_selected 13 84327 ⟨185398, by decide⟩ ⟨13, 2, 0, 185398, 84327, 1145, 16384⟩
    (by decide) selected_cut_06147

theorem unmarked_context_12_21081_185399 : frontier 9 ⟨185399, by decide⟩
    (prefixCache 12 21081) (prefixPartial 12 21081) = false := by
  decide +kernel

theorem node_context_12_21081_185399 : EJMOriginalGlobalDAGData.nodes 9 ⟨185399, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨185358, by decide⟩,⟨185386, by decide⟩,⟨185398, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21081_185399 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21081 ⟨185399, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21081
    ⟨185399, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨185358, by decide⟩,⟨185386, by decide⟩,⟨185398, by decide⟩]) unmarked_context_12_21081_185399 node_context_12_21081_185399
  intro a
  fin_cases a
  · exact context_13_84324_3444
  · exact context_13_84325_185358
  · exact context_13_84326_185386
  · exact context_13_84327_185398

theorem selected_cut_06148 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 84328) = some ⟨13, 1, 0, 3444, 84328, 1, 16384⟩ := by
  decide +kernel

theorem context_13_84328_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84328 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 84328 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 84328, 1, 16384⟩
    (by decide) selected_cut_06148

theorem selected_cut_06149 : selected 8 ⟨185424, by decide⟩
    (prefixPartial 13 84329) = some ⟨13, 2, 0, 185424, 84329, 2133, 16384⟩ := by
  decide +kernel

theorem context_13_84329_185424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84329 ⟨185424, by decide⟩ :=
  accepted_of_selected 13 84329 ⟨185424, by decide⟩ ⟨13, 2, 0, 185424, 84329, 2133, 16384⟩
    (by decide) selected_cut_06149

theorem selected_cut_06150 : selected 8 ⟨185460, by decide⟩
    (prefixPartial 13 84330) = some ⟨13, 2, 0, 185460, 84330, 2789, 16384⟩ := by
  decide +kernel

theorem context_13_84330_185460 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84330 ⟨185460, by decide⟩ :=
  accepted_of_selected 13 84330 ⟨185460, by decide⟩ ⟨13, 2, 0, 185460, 84330, 2789, 16384⟩
    (by decide) selected_cut_06150

theorem selected_cut_06151 : selected 8 ⟨185471, by decide⟩
    (prefixPartial 13 84331) = some ⟨13, 2, 0, 185471, 84331, 1261, 16384⟩ := by
  decide +kernel

theorem context_13_84331_185471 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84331 ⟨185471, by decide⟩ :=
  accepted_of_selected 13 84331 ⟨185471, by decide⟩ ⟨13, 2, 0, 185471, 84331, 1261, 16384⟩
    (by decide) selected_cut_06151

theorem unmarked_context_12_21082_185472 : frontier 9 ⟨185472, by decide⟩
    (prefixCache 12 21082) (prefixPartial 12 21082) = false := by
  decide +kernel

theorem node_context_12_21082_185472 : EJMOriginalGlobalDAGData.nodes 9 ⟨185472, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨185424, by decide⟩,⟨185460, by decide⟩,⟨185471, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21082_185472 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21082 ⟨185472, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21082
    ⟨185472, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨185424, by decide⟩,⟨185460, by decide⟩,⟨185471, by decide⟩]) unmarked_context_12_21082_185472 node_context_12_21082_185472
  intro a
  fin_cases a
  · exact context_13_84328_3444
  · exact context_13_84329_185424
  · exact context_13_84330_185460
  · exact context_13_84331_185471

theorem selected_cut_06152 : selected 9 ⟨185516, by decide⟩
    (prefixPartial 12 21083) = some ⟨12, 2, 0, 185516, 21083, 3897, 65536⟩ := by
  decide +kernel

theorem context_12_21083_185516 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21083 ⟨185516, by decide⟩ :=
  accepted_of_selected 12 21083 ⟨185516, by decide⟩ ⟨12, 2, 0, 185516, 21083, 3897, 65536⟩
    (by decide) selected_cut_06152

theorem unmarked_context_11_5270_185517 : frontier 10 ⟨185517, by decide⟩
    (prefixCache 11 5270) (prefixPartial 11 5270) = false := by
  decide +kernel

theorem node_context_11_5270_185517 : EJMOriginalGlobalDAGData.nodes 10 ⟨185517, by decide⟩ =
    .split (coordinate 11) (![⟨185335, by decide⟩,⟨185399, by decide⟩,⟨185472, by decide⟩,⟨185516, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5270_185517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5270 ⟨185517, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5270
    ⟨185517, by decide⟩ (by decide) (![⟨185335, by decide⟩,⟨185399, by decide⟩,⟨185472, by decide⟩,⟨185516, by decide⟩]) unmarked_context_11_5270_185517 node_context_11_5270_185517
  intro a
  fin_cases a
  · exact context_12_21080_185335
  · exact context_12_21081_185399
  · exact context_12_21082_185472
  · exact context_12_21083_185516

theorem selected_cut_06153 : selected 9 ⟨185565, by decide⟩
    (prefixPartial 12 21084) = some ⟨12, 2, 0, 185565, 21084, 3181, 65536⟩ := by
  decide +kernel

theorem context_12_21084_185565 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21084 ⟨185565, by decide⟩ :=
  accepted_of_selected 12 21084 ⟨185565, by decide⟩ ⟨12, 2, 0, 185565, 21084, 3181, 65536⟩
    (by decide) selected_cut_06153

theorem selected_cut_06154 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 84340) = some ⟨13, 1, 0, 3444, 84340, 1, 16384⟩ := by
  decide +kernel

theorem context_13_84340_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84340 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 84340 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 84340, 1, 16384⟩
    (by decide) selected_cut_06154

theorem selected_cut_06155 : selected 8 ⟨185589, by decide⟩
    (prefixPartial 13 84341) = some ⟨13, 2, 0, 185589, 84341, 1657, 16384⟩ := by
  decide +kernel

theorem context_13_84341_185589 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84341 ⟨185589, by decide⟩ :=
  accepted_of_selected 13 84341 ⟨185589, by decide⟩ ⟨13, 2, 0, 185589, 84341, 1657, 16384⟩
    (by decide) selected_cut_06155

theorem selected_cut_06156 : selected 8 ⟨185634, by decide⟩
    (prefixPartial 13 84342) = some ⟨13, 2, 0, 185634, 84342, 2721, 16384⟩ := by
  decide +kernel

theorem context_13_84342_185634 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84342 ⟨185634, by decide⟩ :=
  accepted_of_selected 13 84342 ⟨185634, by decide⟩ ⟨13, 2, 0, 185634, 84342, 2721, 16384⟩
    (by decide) selected_cut_06156

theorem selected_cut_06157 : selected 8 ⟨185652, by decide⟩
    (prefixPartial 13 84343) = some ⟨13, 2, 0, 185652, 84343, 1201, 16384⟩ := by
  decide +kernel

theorem context_13_84343_185652 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84343 ⟨185652, by decide⟩ :=
  accepted_of_selected 13 84343 ⟨185652, by decide⟩ ⟨13, 2, 0, 185652, 84343, 1201, 16384⟩
    (by decide) selected_cut_06157

theorem unmarked_context_12_21085_185653 : frontier 9 ⟨185653, by decide⟩
    (prefixCache 12 21085) (prefixPartial 12 21085) = false := by
  decide +kernel

theorem node_context_12_21085_185653 : EJMOriginalGlobalDAGData.nodes 9 ⟨185653, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨185589, by decide⟩,⟨185634, by decide⟩,⟨185652, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21085_185653 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21085 ⟨185653, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21085
    ⟨185653, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨185589, by decide⟩,⟨185634, by decide⟩,⟨185652, by decide⟩]) unmarked_context_12_21085_185653 node_context_12_21085_185653
  intro a
  fin_cases a
  · exact context_13_84340_3444
  · exact context_13_84341_185589
  · exact context_13_84342_185634
  · exact context_13_84343_185652

theorem selected_cut_06158 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 84344) = some ⟨13, 1, 0, 3444, 84344, 1, 16384⟩ := by
  decide +kernel

theorem context_13_84344_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84344 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 84344 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 84344, 1, 16384⟩
    (by decide) selected_cut_06158

theorem selected_cut_06159 : selected 8 ⟨185666, by decide⟩
    (prefixPartial 13 84345) = some ⟨13, 2, 0, 185666, 84345, 1273, 16384⟩ := by
  decide +kernel

theorem context_13_84345_185666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84345 ⟨185666, by decide⟩ :=
  accepted_of_selected 13 84345 ⟨185666, by decide⟩ ⟨13, 2, 0, 185666, 84345, 1273, 16384⟩
    (by decide) selected_cut_06159

theorem selected_cut_06160 : selected 8 ⟨185691, by decide⟩
    (prefixPartial 13 84346) = some ⟨13, 2, 0, 185691, 84346, 1997, 16384⟩ := by
  decide +kernel

theorem context_13_84346_185691 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84346 ⟨185691, by decide⟩ :=
  accepted_of_selected 13 84346 ⟨185691, by decide⟩ ⟨13, 2, 0, 185691, 84346, 1997, 16384⟩
    (by decide) selected_cut_06160

theorem selected_cut_06161 : selected 8 ⟨185700, by decide⟩
    (prefixPartial 13 84347) = some ⟨13, 2, 0, 185700, 84347, 889, 16384⟩ := by
  decide +kernel

theorem context_13_84347_185700 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84347 ⟨185700, by decide⟩ :=
  accepted_of_selected 13 84347 ⟨185700, by decide⟩ ⟨13, 2, 0, 185700, 84347, 889, 16384⟩
    (by decide) selected_cut_06161

theorem unmarked_context_12_21086_185701 : frontier 9 ⟨185701, by decide⟩
    (prefixCache 12 21086) (prefixPartial 12 21086) = false := by
  decide +kernel

theorem node_context_12_21086_185701 : EJMOriginalGlobalDAGData.nodes 9 ⟨185701, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨185666, by decide⟩,⟨185691, by decide⟩,⟨185700, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21086_185701 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21086 ⟨185701, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21086
    ⟨185701, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨185666, by decide⟩,⟨185691, by decide⟩,⟨185700, by decide⟩]) unmarked_context_12_21086_185701 node_context_12_21086_185701
  intro a
  fin_cases a
  · exact context_13_84344_3444
  · exact context_13_84345_185666
  · exact context_13_84346_185691
  · exact context_13_84347_185700

theorem selected_cut_06162 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 84348) = some ⟨13, 1, 0, 3444, 84348, 1, 16384⟩ := by
  decide +kernel

theorem context_13_84348_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84348 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 84348 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 84348, 1, 16384⟩
    (by decide) selected_cut_06162

theorem selected_cut_06163 : selected 8 ⟨185717, by decide⟩
    (prefixPartial 13 84349) = some ⟨13, 2, 0, 185717, 84349, 1173, 16384⟩ := by
  decide +kernel

theorem context_13_84349_185717 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84349 ⟨185717, by decide⟩ :=
  accepted_of_selected 13 84349 ⟨185717, by decide⟩ ⟨13, 2, 0, 185717, 84349, 1173, 16384⟩
    (by decide) selected_cut_06163

theorem selected_cut_06164 : selected 8 ⟨185740, by decide⟩
    (prefixPartial 13 84350) = some ⟨13, 2, 0, 185740, 84350, 1961, 16384⟩ := by
  decide +kernel

theorem context_13_84350_185740 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84350 ⟨185740, by decide⟩ :=
  accepted_of_selected 13 84350 ⟨185740, by decide⟩ ⟨13, 2, 0, 185740, 84350, 1961, 16384⟩
    (by decide) selected_cut_06164

theorem selected_cut_06165 : selected 8 ⟨185751, by decide⟩
    (prefixPartial 13 84351) = some ⟨13, 2, 0, 185751, 84351, 977, 16384⟩ := by
  decide +kernel

theorem context_13_84351_185751 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84351 ⟨185751, by decide⟩ :=
  accepted_of_selected 13 84351 ⟨185751, by decide⟩ ⟨13, 2, 0, 185751, 84351, 977, 16384⟩
    (by decide) selected_cut_06165

theorem unmarked_context_12_21087_185752 : frontier 9 ⟨185752, by decide⟩
    (prefixCache 12 21087) (prefixPartial 12 21087) = false := by
  decide +kernel

theorem node_context_12_21087_185752 : EJMOriginalGlobalDAGData.nodes 9 ⟨185752, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨185717, by decide⟩,⟨185740, by decide⟩,⟨185751, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21087_185752 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21087 ⟨185752, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21087
    ⟨185752, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨185717, by decide⟩,⟨185740, by decide⟩,⟨185751, by decide⟩]) unmarked_context_12_21087_185752 node_context_12_21087_185752
  intro a
  fin_cases a
  · exact context_13_84348_3444
  · exact context_13_84349_185717
  · exact context_13_84350_185740
  · exact context_13_84351_185751

theorem unmarked_context_11_5271_185753 : frontier 10 ⟨185753, by decide⟩
    (prefixCache 11 5271) (prefixPartial 11 5271) = false := by
  decide +kernel

theorem node_context_11_5271_185753 : EJMOriginalGlobalDAGData.nodes 10 ⟨185753, by decide⟩ =
    .split (coordinate 11) (![⟨185565, by decide⟩,⟨185653, by decide⟩,⟨185701, by decide⟩,⟨185752, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5271_185753 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5271 ⟨185753, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5271
    ⟨185753, by decide⟩ (by decide) (![⟨185565, by decide⟩,⟨185653, by decide⟩,⟨185701, by decide⟩,⟨185752, by decide⟩]) unmarked_context_11_5271_185753 node_context_11_5271_185753
  intro a
  fin_cases a
  · exact context_12_21084_185565
  · exact context_12_21085_185653
  · exact context_12_21086_185701
  · exact context_12_21087_185752

theorem unmarked_context_10_1317_185754 : frontier 11 ⟨185754, by decide⟩
    (prefixCache 10 1317) (prefixPartial 10 1317) = false := by
  decide +kernel

theorem node_context_10_1317_185754 : EJMOriginalGlobalDAGData.nodes 11 ⟨185754, by decide⟩ =
    .split (coordinate 10) (![⟨185166, by decide⟩,⟨185301, by decide⟩,⟨185517, by decide⟩,⟨185753, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1317_185754 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1317 ⟨185754, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1317
    ⟨185754, by decide⟩ (by decide) (![⟨185166, by decide⟩,⟨185301, by decide⟩,⟨185517, by decide⟩,⟨185753, by decide⟩]) unmarked_context_10_1317_185754 node_context_10_1317_185754
  intro a
  fin_cases a
  · exact context_11_5268_185166
  · exact context_11_5269_185301
  · exact context_11_5270_185517
  · exact context_11_5271_185753

theorem selected_cut_06166 : selected 9 ⟨185786, by decide⟩
    (prefixPartial 12 21088) = some ⟨12, 2, 0, 185786, 21088, 2733, 65536⟩ := by
  decide +kernel

theorem context_12_21088_185786 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21088 ⟨185786, by decide⟩ :=
  accepted_of_selected 12 21088 ⟨185786, by decide⟩ ⟨12, 2, 0, 185786, 21088, 2733, 65536⟩
    (by decide) selected_cut_06166

theorem selected_cut_06167 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 84356) = some ⟨13, 1, 0, 3444, 84356, 1, 16384⟩ := by
  decide +kernel

theorem context_13_84356_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84356 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 84356 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 84356, 1, 16384⟩
    (by decide) selected_cut_06167

theorem selected_cut_06168 : selected 8 ⟨185805, by decide⟩
    (prefixPartial 13 84357) = some ⟨13, 2, 0, 185805, 84357, 1621, 16384⟩ := by
  decide +kernel

theorem context_13_84357_185805 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84357 ⟨185805, by decide⟩ :=
  accepted_of_selected 13 84357 ⟨185805, by decide⟩ ⟨13, 2, 0, 185805, 84357, 1621, 16384⟩
    (by decide) selected_cut_06168

theorem selected_cut_06169 : selected 8 ⟨185829, by decide⟩
    (prefixPartial 13 84358) = some ⟨13, 2, 0, 185829, 84358, 2009, 16384⟩ := by
  decide +kernel

theorem context_13_84358_185829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84358 ⟨185829, by decide⟩ :=
  accepted_of_selected 13 84358 ⟨185829, by decide⟩ ⟨13, 2, 0, 185829, 84358, 2009, 16384⟩
    (by decide) selected_cut_06169

theorem selected_cut_06170 : selected 8 ⟨185839, by decide⟩
    (prefixPartial 13 84359) = some ⟨13, 2, 0, 185839, 84359, 1025, 16384⟩ := by
  decide +kernel

theorem context_13_84359_185839 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84359 ⟨185839, by decide⟩ :=
  accepted_of_selected 13 84359 ⟨185839, by decide⟩ ⟨13, 2, 0, 185839, 84359, 1025, 16384⟩
    (by decide) selected_cut_06170

theorem unmarked_context_12_21089_185840 : frontier 9 ⟨185840, by decide⟩
    (prefixCache 12 21089) (prefixPartial 12 21089) = false := by
  decide +kernel

theorem node_context_12_21089_185840 : EJMOriginalGlobalDAGData.nodes 9 ⟨185840, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨185805, by decide⟩,⟨185829, by decide⟩,⟨185839, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21089_185840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21089 ⟨185840, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21089
    ⟨185840, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨185805, by decide⟩,⟨185829, by decide⟩,⟨185839, by decide⟩]) unmarked_context_12_21089_185840 node_context_12_21089_185840
  intro a
  fin_cases a
  · exact context_13_84356_3444
  · exact context_13_84357_185805
  · exact context_13_84358_185829
  · exact context_13_84359_185839

theorem selected_cut_06171 : selected 9 ⟨185880, by decide⟩
    (prefixPartial 12 21090) = some ⟨12, 2, 0, 185880, 21090, 3405, 65536⟩ := by
  decide +kernel

theorem context_12_21090_185880 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21090 ⟨185880, by decide⟩ :=
  accepted_of_selected 12 21090 ⟨185880, by decide⟩ ⟨12, 2, 0, 185880, 21090, 3405, 65536⟩
    (by decide) selected_cut_06171

theorem selected_cut_06172 : selected 9 ⟨185925, by decide⟩
    (prefixPartial 12 21091) = some ⟨12, 2, 0, 185925, 21091, 3589, 65536⟩ := by
  decide +kernel

theorem context_12_21091_185925 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21091 ⟨185925, by decide⟩ :=
  accepted_of_selected 12 21091 ⟨185925, by decide⟩ ⟨12, 2, 0, 185925, 21091, 3589, 65536⟩
    (by decide) selected_cut_06172

theorem unmarked_context_11_5272_185926 : frontier 10 ⟨185926, by decide⟩
    (prefixCache 11 5272) (prefixPartial 11 5272) = false := by
  decide +kernel

theorem node_context_11_5272_185926 : EJMOriginalGlobalDAGData.nodes 10 ⟨185926, by decide⟩ =
    .split (coordinate 11) (![⟨185786, by decide⟩,⟨185840, by decide⟩,⟨185880, by decide⟩,⟨185925, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5272_185926 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5272 ⟨185926, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5272
    ⟨185926, by decide⟩ (by decide) (![⟨185786, by decide⟩,⟨185840, by decide⟩,⟨185880, by decide⟩,⟨185925, by decide⟩]) unmarked_context_11_5272_185926 node_context_11_5272_185926
  intro a
  fin_cases a
  · exact context_12_21088_185786
  · exact context_12_21089_185840
  · exact context_12_21090_185880
  · exact context_12_21091_185925

theorem selected_cut_06173 : selected 9 ⟨185965, by decide⟩
    (prefixPartial 12 21092) = some ⟨12, 2, 0, 185965, 21092, 2953, 65536⟩ := by
  decide +kernel

theorem context_12_21092_185965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21092 ⟨185965, by decide⟩ :=
  accepted_of_selected 12 21092 ⟨185965, by decide⟩ ⟨12, 2, 0, 185965, 21092, 2953, 65536⟩
    (by decide) selected_cut_06173

theorem selected_cut_06174 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 84372) = some ⟨13, 1, 0, 3444, 84372, 1, 16384⟩ := by
  decide +kernel

theorem context_13_84372_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84372 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 84372 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 84372, 1, 16384⟩
    (by decide) selected_cut_06174

theorem selected_cut_06175 : selected 8 ⟨185987, by decide⟩
    (prefixPartial 13 84373) = some ⟨13, 2, 0, 185987, 84373, 1457, 16384⟩ := by
  decide +kernel

theorem context_13_84373_185987 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84373 ⟨185987, by decide⟩ :=
  accepted_of_selected 13 84373 ⟨185987, by decide⟩ ⟨13, 2, 0, 185987, 84373, 1457, 16384⟩
    (by decide) selected_cut_06175

theorem selected_cut_06176 : selected 8 ⟨186015, by decide⟩
    (prefixPartial 13 84374) = some ⟨13, 2, 0, 186015, 84374, 2165, 16384⟩ := by
  decide +kernel

theorem context_13_84374_186015 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84374 ⟨186015, by decide⟩ :=
  accepted_of_selected 13 84374 ⟨186015, by decide⟩ ⟨13, 2, 0, 186015, 84374, 2165, 16384⟩
    (by decide) selected_cut_06176

theorem selected_cut_06177 : selected 8 ⟨186027, by decide⟩
    (prefixPartial 13 84375) = some ⟨13, 2, 0, 186027, 84375, 925, 16384⟩ := by
  decide +kernel

theorem context_13_84375_186027 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84375 ⟨186027, by decide⟩ :=
  accepted_of_selected 13 84375 ⟨186027, by decide⟩ ⟨13, 2, 0, 186027, 84375, 925, 16384⟩
    (by decide) selected_cut_06177

theorem unmarked_context_12_21093_186028 : frontier 9 ⟨186028, by decide⟩
    (prefixCache 12 21093) (prefixPartial 12 21093) = false := by
  decide +kernel

theorem node_context_12_21093_186028 : EJMOriginalGlobalDAGData.nodes 9 ⟨186028, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨185987, by decide⟩,⟨186015, by decide⟩,⟨186027, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21093_186028 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21093 ⟨186028, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21093
    ⟨186028, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨185987, by decide⟩,⟨186015, by decide⟩,⟨186027, by decide⟩]) unmarked_context_12_21093_186028 node_context_12_21093_186028
  intro a
  fin_cases a
  · exact context_13_84372_3444
  · exact context_13_84373_185987
  · exact context_13_84374_186015
  · exact context_13_84375_186027

theorem selected_cut_06178 : selected 9 ⟨186067, by decide⟩
    (prefixPartial 12 21094) = some ⟨12, 2, 0, 186067, 21094, 3333, 65536⟩ := by
  decide +kernel

theorem context_12_21094_186067 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21094 ⟨186067, by decide⟩ :=
  accepted_of_selected 12 21094 ⟨186067, by decide⟩ ⟨12, 2, 0, 186067, 21094, 3333, 65536⟩
    (by decide) selected_cut_06178

theorem selected_cut_06179 : selected 9 ⟨186115, by decide⟩
    (prefixPartial 12 21095) = some ⟨12, 2, 0, 186115, 21095, 3593, 65536⟩ := by
  decide +kernel

theorem context_12_21095_186115 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21095 ⟨186115, by decide⟩ :=
  accepted_of_selected 12 21095 ⟨186115, by decide⟩ ⟨12, 2, 0, 186115, 21095, 3593, 65536⟩
    (by decide) selected_cut_06179

theorem unmarked_context_11_5273_186116 : frontier 10 ⟨186116, by decide⟩
    (prefixCache 11 5273) (prefixPartial 11 5273) = false := by
  decide +kernel

theorem node_context_11_5273_186116 : EJMOriginalGlobalDAGData.nodes 10 ⟨186116, by decide⟩ =
    .split (coordinate 11) (![⟨185965, by decide⟩,⟨186028, by decide⟩,⟨186067, by decide⟩,⟨186115, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5273_186116 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5273 ⟨186116, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5273
    ⟨186116, by decide⟩ (by decide) (![⟨185965, by decide⟩,⟨186028, by decide⟩,⟨186067, by decide⟩,⟨186115, by decide⟩]) unmarked_context_11_5273_186116 node_context_11_5273_186116
  intro a
  fin_cases a
  · exact context_12_21092_185965
  · exact context_12_21093_186028
  · exact context_12_21094_186067
  · exact context_12_21095_186115

theorem selected_cut_06180 : selected 9 ⟨186145, by decide⟩
    (prefixPartial 12 21096) = some ⟨12, 2, 0, 186145, 21096, 2637, 65536⟩ := by
  decide +kernel

theorem context_12_21096_186145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21096 ⟨186145, by decide⟩ :=
  accepted_of_selected 12 21096 ⟨186145, by decide⟩ ⟨12, 2, 0, 186145, 21096, 2637, 65536⟩
    (by decide) selected_cut_06180

theorem selected_cut_06181 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 84388) = some ⟨13, 1, 0, 3444, 84388, 1, 16384⟩ := by
  decide +kernel

theorem context_13_84388_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84388 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 84388 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 84388, 1, 16384⟩
    (by decide) selected_cut_06181

theorem selected_cut_06182 : selected 8 ⟨186159, by decide⟩
    (prefixPartial 13 84389) = some ⟨13, 2, 0, 186159, 84389, 1145, 16384⟩ := by
  decide +kernel

theorem context_13_84389_186159 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84389 ⟨186159, by decide⟩ :=
  accepted_of_selected 13 84389 ⟨186159, by decide⟩ ⟨13, 2, 0, 186159, 84389, 1145, 16384⟩
    (by decide) selected_cut_06182

theorem selected_cut_06183 : selected 8 ⟨186183, by decide⟩
    (prefixPartial 13 84390) = some ⟨13, 2, 0, 186183, 84390, 2245, 16384⟩ := by
  decide +kernel

theorem context_13_84390_186183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84390 ⟨186183, by decide⟩ :=
  accepted_of_selected 13 84390 ⟨186183, by decide⟩ ⟨13, 2, 0, 186183, 84390, 2245, 16384⟩
    (by decide) selected_cut_06183

theorem selected_cut_06184 : selected 8 ⟨186193, by decide⟩
    (prefixPartial 13 84391) = some ⟨13, 2, 0, 186193, 84391, 1009, 16384⟩ := by
  decide +kernel

theorem context_13_84391_186193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84391 ⟨186193, by decide⟩ :=
  accepted_of_selected 13 84391 ⟨186193, by decide⟩ ⟨13, 2, 0, 186193, 84391, 1009, 16384⟩
    (by decide) selected_cut_06184

theorem unmarked_context_12_21097_186194 : frontier 9 ⟨186194, by decide⟩
    (prefixCache 12 21097) (prefixPartial 12 21097) = false := by
  decide +kernel

theorem node_context_12_21097_186194 : EJMOriginalGlobalDAGData.nodes 9 ⟨186194, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨186159, by decide⟩,⟨186183, by decide⟩,⟨186193, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21097_186194 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21097 ⟨186194, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21097
    ⟨186194, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨186159, by decide⟩,⟨186183, by decide⟩,⟨186193, by decide⟩]) unmarked_context_12_21097_186194 node_context_12_21097_186194
  intro a
  fin_cases a
  · exact context_13_84388_3444
  · exact context_13_84389_186159
  · exact context_13_84390_186183
  · exact context_13_84391_186193

theorem selected_cut_06185 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 84392) = some ⟨13, 1, 0, 3444, 84392, 1, 16384⟩ := by
  decide +kernel

theorem context_13_84392_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84392 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 84392 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 84392, 1, 16384⟩
    (by decide) selected_cut_06185

theorem selected_cut_06186 : selected 8 ⟨186212, by decide⟩
    (prefixPartial 13 84393) = some ⟨13, 2, 0, 186212, 84393, 1385, 16384⟩ := by
  decide +kernel

theorem context_13_84393_186212 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84393 ⟨186212, by decide⟩ :=
  accepted_of_selected 13 84393 ⟨186212, by decide⟩ ⟨13, 2, 0, 186212, 84393, 1385, 16384⟩
    (by decide) selected_cut_06186

theorem selected_cut_06187 : selected 8 ⟨186246, by decide⟩
    (prefixPartial 13 84394) = some ⟨13, 2, 0, 186246, 84394, 2573, 16384⟩ := by
  decide +kernel

theorem context_13_84394_186246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84394 ⟨186246, by decide⟩ :=
  accepted_of_selected 13 84394 ⟨186246, by decide⟩ ⟨13, 2, 0, 186246, 84394, 2573, 16384⟩
    (by decide) selected_cut_06187

theorem selected_cut_06188 : selected 8 ⟨186253, by decide⟩
    (prefixPartial 13 84395) = some ⟨13, 2, 0, 186253, 84395, 1009, 16384⟩ := by
  decide +kernel

theorem context_13_84395_186253 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84395 ⟨186253, by decide⟩ :=
  accepted_of_selected 13 84395 ⟨186253, by decide⟩ ⟨13, 2, 0, 186253, 84395, 1009, 16384⟩
    (by decide) selected_cut_06188

theorem unmarked_context_12_21098_186254 : frontier 9 ⟨186254, by decide⟩
    (prefixCache 12 21098) (prefixPartial 12 21098) = false := by
  decide +kernel

theorem node_context_12_21098_186254 : EJMOriginalGlobalDAGData.nodes 9 ⟨186254, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨186212, by decide⟩,⟨186246, by decide⟩,⟨186253, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21098_186254 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21098 ⟨186254, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21098
    ⟨186254, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨186212, by decide⟩,⟨186246, by decide⟩,⟨186253, by decide⟩]) unmarked_context_12_21098_186254 node_context_12_21098_186254
  intro a
  fin_cases a
  · exact context_13_84392_3444
  · exact context_13_84393_186212
  · exact context_13_84394_186246
  · exact context_13_84395_186253

theorem selected_cut_06189 : selected 9 ⟨186297, by decide⟩
    (prefixPartial 12 21099) = some ⟨12, 2, 0, 186297, 21099, 3393, 65536⟩ := by
  decide +kernel

theorem context_12_21099_186297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21099 ⟨186297, by decide⟩ :=
  accepted_of_selected 12 21099 ⟨186297, by decide⟩ ⟨12, 2, 0, 186297, 21099, 3393, 65536⟩
    (by decide) selected_cut_06189

theorem unmarked_context_11_5274_186298 : frontier 10 ⟨186298, by decide⟩
    (prefixCache 11 5274) (prefixPartial 11 5274) = false := by
  decide +kernel

theorem node_context_11_5274_186298 : EJMOriginalGlobalDAGData.nodes 10 ⟨186298, by decide⟩ =
    .split (coordinate 11) (![⟨186145, by decide⟩,⟨186194, by decide⟩,⟨186254, by decide⟩,⟨186297, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5274_186298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5274 ⟨186298, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5274
    ⟨186298, by decide⟩ (by decide) (![⟨186145, by decide⟩,⟨186194, by decide⟩,⟨186254, by decide⟩,⟨186297, by decide⟩]) unmarked_context_11_5274_186298 node_context_11_5274_186298
  intro a
  fin_cases a
  · exact context_12_21096_186145
  · exact context_12_21097_186194
  · exact context_12_21098_186254
  · exact context_12_21099_186297

theorem selected_cut_06190 : selected 9 ⟨186342, by decide⟩
    (prefixPartial 12 21100) = some ⟨12, 2, 0, 186342, 21100, 3201, 65536⟩ := by
  decide +kernel

theorem context_12_21100_186342 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21100 ⟨186342, by decide⟩ :=
  accepted_of_selected 12 21100 ⟨186342, by decide⟩ ⟨12, 2, 0, 186342, 21100, 3201, 65536⟩
    (by decide) selected_cut_06190

theorem selected_cut_06191 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 84404) = some ⟨13, 1, 0, 3444, 84404, 1, 16384⟩ := by
  decide +kernel

theorem context_13_84404_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84404 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 84404 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 84404, 1, 16384⟩
    (by decide) selected_cut_06191

theorem selected_cut_06192 : selected 8 ⟨186354, by decide⟩
    (prefixPartial 13 84405) = some ⟨13, 2, 0, 186354, 84405, 1013, 16384⟩ := by
  decide +kernel

theorem context_13_84405_186354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84405 ⟨186354, by decide⟩ :=
  accepted_of_selected 13 84405 ⟨186354, by decide⟩ ⟨13, 2, 0, 186354, 84405, 1013, 16384⟩
    (by decide) selected_cut_06192

theorem selected_cut_06193 : selected 8 ⟨186387, by decide⟩
    (prefixPartial 13 84406) = some ⟨13, 2, 0, 186387, 84406, 2813, 16384⟩ := by
  decide +kernel

theorem context_13_84406_186387 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84406 ⟨186387, by decide⟩ :=
  accepted_of_selected 13 84406 ⟨186387, by decide⟩ ⟨13, 2, 0, 186387, 84406, 2813, 16384⟩
    (by decide) selected_cut_06193

theorem selected_cut_06194 : selected 8 ⟨186403, by decide⟩
    (prefixPartial 13 84407) = some ⟨13, 2, 0, 186403, 84407, 1185, 16384⟩ := by
  decide +kernel

theorem context_13_84407_186403 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84407 ⟨186403, by decide⟩ :=
  accepted_of_selected 13 84407 ⟨186403, by decide⟩ ⟨13, 2, 0, 186403, 84407, 1185, 16384⟩
    (by decide) selected_cut_06194

theorem unmarked_context_12_21101_186404 : frontier 9 ⟨186404, by decide⟩
    (prefixCache 12 21101) (prefixPartial 12 21101) = false := by
  decide +kernel

theorem node_context_12_21101_186404 : EJMOriginalGlobalDAGData.nodes 9 ⟨186404, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨186354, by decide⟩,⟨186387, by decide⟩,⟨186403, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21101_186404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21101 ⟨186404, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21101
    ⟨186404, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨186354, by decide⟩,⟨186387, by decide⟩,⟨186403, by decide⟩]) unmarked_context_12_21101_186404 node_context_12_21101_186404
  intro a
  fin_cases a
  · exact context_13_84404_3444
  · exact context_13_84405_186354
  · exact context_13_84406_186387
  · exact context_13_84407_186403

theorem selected_cut_06195 : selected 9 ⟨186445, by decide⟩
    (prefixPartial 12 21102) = some ⟨12, 2, 0, 186445, 21102, 3777, 65536⟩ := by
  decide +kernel

theorem context_12_21102_186445 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21102 ⟨186445, by decide⟩ :=
  accepted_of_selected 12 21102 ⟨186445, by decide⟩ ⟨12, 2, 0, 186445, 21102, 3777, 65536⟩
    (by decide) selected_cut_06195

theorem selected_cut_06196 : selected 9 ⟨186483, by decide⟩
    (prefixPartial 12 21103) = some ⟨12, 2, 0, 186483, 21103, 3701, 65536⟩ := by
  decide +kernel

theorem context_12_21103_186483 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21103 ⟨186483, by decide⟩ :=
  accepted_of_selected 12 21103 ⟨186483, by decide⟩ ⟨12, 2, 0, 186483, 21103, 3701, 65536⟩
    (by decide) selected_cut_06196

theorem unmarked_context_11_5275_186484 : frontier 10 ⟨186484, by decide⟩
    (prefixCache 11 5275) (prefixPartial 11 5275) = false := by
  decide +kernel

theorem node_context_11_5275_186484 : EJMOriginalGlobalDAGData.nodes 10 ⟨186484, by decide⟩ =
    .split (coordinate 11) (![⟨186342, by decide⟩,⟨186404, by decide⟩,⟨186445, by decide⟩,⟨186483, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5275_186484 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5275 ⟨186484, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5275
    ⟨186484, by decide⟩ (by decide) (![⟨186342, by decide⟩,⟨186404, by decide⟩,⟨186445, by decide⟩,⟨186483, by decide⟩]) unmarked_context_11_5275_186484 node_context_11_5275_186484
  intro a
  fin_cases a
  · exact context_12_21100_186342
  · exact context_12_21101_186404
  · exact context_12_21102_186445
  · exact context_12_21103_186483

theorem unmarked_context_10_1318_186485 : frontier 11 ⟨186485, by decide⟩
    (prefixCache 10 1318) (prefixPartial 10 1318) = false := by
  decide +kernel

theorem node_context_10_1318_186485 : EJMOriginalGlobalDAGData.nodes 11 ⟨186485, by decide⟩ =
    .split (coordinate 10) (![⟨185926, by decide⟩,⟨186116, by decide⟩,⟨186298, by decide⟩,⟨186484, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1318_186485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1318 ⟨186485, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1318
    ⟨186485, by decide⟩ (by decide) (![⟨185926, by decide⟩,⟨186116, by decide⟩,⟨186298, by decide⟩,⟨186484, by decide⟩]) unmarked_context_10_1318_186485 node_context_10_1318_186485
  intro a
  fin_cases a
  · exact context_11_5272_185926
  · exact context_11_5273_186116
  · exact context_11_5274_186298
  · exact context_11_5275_186484

theorem selected_cut_06197 : selected 9 ⟨186509, by decide⟩
    (prefixPartial 12 21104) = some ⟨12, 2, 0, 186509, 21104, 2109, 65536⟩ := by
  decide +kernel

theorem context_12_21104_186509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21104 ⟨186509, by decide⟩ :=
  accepted_of_selected 12 21104 ⟨186509, by decide⟩ ⟨12, 2, 0, 186509, 21104, 2109, 65536⟩
    (by decide) selected_cut_06197

theorem selected_cut_06198 : selected 9 ⟨186554, by decide⟩
    (prefixPartial 12 21105) = some ⟨12, 2, 0, 186554, 21105, 3621, 65536⟩ := by
  decide +kernel

theorem context_12_21105_186554 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21105 ⟨186554, by decide⟩ :=
  accepted_of_selected 12 21105 ⟨186554, by decide⟩ ⟨12, 2, 0, 186554, 21105, 3621, 65536⟩
    (by decide) selected_cut_06198

theorem selected_cut_06199 : selected 9 ⟨186589, by decide⟩
    (prefixPartial 12 21106) = some ⟨12, 2, 0, 186589, 21106, 2609, 65536⟩ := by
  decide +kernel

theorem context_12_21106_186589 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21106 ⟨186589, by decide⟩ :=
  accepted_of_selected 12 21106 ⟨186589, by decide⟩ ⟨12, 2, 0, 186589, 21106, 2609, 65536⟩
    (by decide) selected_cut_06199

theorem selected_cut_06200 : selected 9 ⟨186626, by decide⟩
    (prefixPartial 12 21107) = some ⟨12, 2, 0, 186626, 21107, 2889, 65536⟩ := by
  decide +kernel

theorem context_12_21107_186626 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21107 ⟨186626, by decide⟩ :=
  accepted_of_selected 12 21107 ⟨186626, by decide⟩ ⟨12, 2, 0, 186626, 21107, 2889, 65536⟩
    (by decide) selected_cut_06200

theorem unmarked_context_11_5276_186627 : frontier 10 ⟨186627, by decide⟩
    (prefixCache 11 5276) (prefixPartial 11 5276) = false := by
  decide +kernel

theorem node_context_11_5276_186627 : EJMOriginalGlobalDAGData.nodes 10 ⟨186627, by decide⟩ =
    .split (coordinate 11) (![⟨186509, by decide⟩,⟨186554, by decide⟩,⟨186589, by decide⟩,⟨186626, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5276_186627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5276 ⟨186627, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5276
    ⟨186627, by decide⟩ (by decide) (![⟨186509, by decide⟩,⟨186554, by decide⟩,⟨186589, by decide⟩,⟨186626, by decide⟩]) unmarked_context_11_5276_186627 node_context_11_5276_186627
  intro a
  fin_cases a
  · exact context_12_21104_186509
  · exact context_12_21105_186554
  · exact context_12_21106_186589
  · exact context_12_21107_186626

theorem selected_cut_06201 : selected 9 ⟨186652, by decide⟩
    (prefixPartial 12 21108) = some ⟨12, 2, 0, 186652, 21108, 2229, 65536⟩ := by
  decide +kernel

theorem context_12_21108_186652 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21108 ⟨186652, by decide⟩ :=
  accepted_of_selected 12 21108 ⟨186652, by decide⟩ ⟨12, 2, 0, 186652, 21108, 2229, 65536⟩
    (by decide) selected_cut_06201

theorem selected_cut_06202 : selected 9 ⟨186698, by decide⟩
    (prefixPartial 12 21109) = some ⟨12, 2, 0, 186698, 21109, 3613, 65536⟩ := by
  decide +kernel

theorem context_12_21109_186698 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21109 ⟨186698, by decide⟩ :=
  accepted_of_selected 12 21109 ⟨186698, by decide⟩ ⟨12, 2, 0, 186698, 21109, 3613, 65536⟩
    (by decide) selected_cut_06202

theorem selected_cut_06203 : selected 9 ⟨186734, by decide⟩
    (prefixPartial 12 21110) = some ⟨12, 2, 0, 186734, 21110, 2433, 65536⟩ := by
  decide +kernel

theorem context_12_21110_186734 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21110 ⟨186734, by decide⟩ :=
  accepted_of_selected 12 21110 ⟨186734, by decide⟩ ⟨12, 2, 0, 186734, 21110, 2433, 65536⟩
    (by decide) selected_cut_06203

theorem selected_cut_06204 : selected 9 ⟨186771, by decide⟩
    (prefixPartial 12 21111) = some ⟨12, 2, 0, 186771, 21111, 2981, 65536⟩ := by
  decide +kernel

theorem context_12_21111_186771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21111 ⟨186771, by decide⟩ :=
  accepted_of_selected 12 21111 ⟨186771, by decide⟩ ⟨12, 2, 0, 186771, 21111, 2981, 65536⟩
    (by decide) selected_cut_06204

theorem unmarked_context_11_5277_186772 : frontier 10 ⟨186772, by decide⟩
    (prefixCache 11 5277) (prefixPartial 11 5277) = false := by
  decide +kernel

theorem node_context_11_5277_186772 : EJMOriginalGlobalDAGData.nodes 10 ⟨186772, by decide⟩ =
    .split (coordinate 11) (![⟨186652, by decide⟩,⟨186698, by decide⟩,⟨186734, by decide⟩,⟨186771, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5277_186772 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5277 ⟨186772, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5277
    ⟨186772, by decide⟩ (by decide) (![⟨186652, by decide⟩,⟨186698, by decide⟩,⟨186734, by decide⟩,⟨186771, by decide⟩]) unmarked_context_11_5277_186772 node_context_11_5277_186772
  intro a
  fin_cases a
  · exact context_12_21108_186652
  · exact context_12_21109_186698
  · exact context_12_21110_186734
  · exact context_12_21111_186771

theorem selected_cut_06205 : selected 9 ⟨186800, by decide⟩
    (prefixPartial 12 21112) = some ⟨12, 2, 0, 186800, 21112, 2177, 65536⟩ := by
  decide +kernel

theorem context_12_21112_186800 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21112 ⟨186800, by decide⟩ :=
  accepted_of_selected 12 21112 ⟨186800, by decide⟩ ⟨12, 2, 0, 186800, 21112, 2177, 65536⟩
    (by decide) selected_cut_06205

theorem selected_cut_06206 : selected 9 ⟨186843, by decide⟩
    (prefixPartial 12 21113) = some ⟨12, 2, 0, 186843, 21113, 3905, 65536⟩ := by
  decide +kernel

theorem context_12_21113_186843 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21113 ⟨186843, by decide⟩ :=
  accepted_of_selected 12 21113 ⟨186843, by decide⟩ ⟨12, 2, 0, 186843, 21113, 3905, 65536⟩
    (by decide) selected_cut_06206

theorem selected_cut_06207 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 84456) = some ⟨13, 1, 0, 3444, 84456, 1, 16384⟩ := by
  decide +kernel

theorem context_13_84456_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84456 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 84456 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 84456, 1, 16384⟩
    (by decide) selected_cut_06207

theorem selected_cut_06208 : selected 8 ⟨186848, by decide⟩
    (prefixPartial 13 84457) = some ⟨13, 2, 0, 186848, 84457, 381, 16384⟩ := by
  decide +kernel

theorem context_13_84457_186848 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84457 ⟨186848, by decide⟩ :=
  accepted_of_selected 13 84457 ⟨186848, by decide⟩ ⟨13, 2, 0, 186848, 84457, 381, 16384⟩
    (by decide) selected_cut_06208

theorem selected_cut_06209 : selected 8 ⟨186892, by decide⟩
    (prefixPartial 13 84458) = some ⟨13, 2, 0, 186892, 84458, 2889, 16384⟩ := by
  decide +kernel

theorem context_13_84458_186892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84458 ⟨186892, by decide⟩ :=
  accepted_of_selected 13 84458 ⟨186892, by decide⟩ ⟨13, 2, 0, 186892, 84458, 2889, 16384⟩
    (by decide) selected_cut_06209

theorem selected_cut_06210 : selected 8 ⟨186905, by decide⟩
    (prefixPartial 13 84459) = some ⟨13, 2, 0, 186905, 84459, 1141, 16384⟩ := by
  decide +kernel

theorem context_13_84459_186905 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 84459 ⟨186905, by decide⟩ :=
  accepted_of_selected 13 84459 ⟨186905, by decide⟩ ⟨13, 2, 0, 186905, 84459, 1141, 16384⟩
    (by decide) selected_cut_06210

theorem unmarked_context_12_21114_186906 : frontier 9 ⟨186906, by decide⟩
    (prefixCache 12 21114) (prefixPartial 12 21114) = false := by
  decide +kernel

theorem node_context_12_21114_186906 : EJMOriginalGlobalDAGData.nodes 9 ⟨186906, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨186848, by decide⟩,⟨186892, by decide⟩,⟨186905, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21114_186906 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21114 ⟨186906, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21114
    ⟨186906, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨186848, by decide⟩,⟨186892, by decide⟩,⟨186905, by decide⟩]) unmarked_context_12_21114_186906 node_context_12_21114_186906
  intro a
  fin_cases a
  · exact context_13_84456_3444
  · exact context_13_84457_186848
  · exact context_13_84458_186892
  · exact context_13_84459_186905

theorem selected_cut_06211 : selected 9 ⟨186940, by decide⟩
    (prefixPartial 12 21115) = some ⟨12, 2, 0, 186940, 21115, 2977, 65536⟩ := by
  decide +kernel

theorem context_12_21115_186940 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21115 ⟨186940, by decide⟩ :=
  accepted_of_selected 12 21115 ⟨186940, by decide⟩ ⟨12, 2, 0, 186940, 21115, 2977, 65536⟩
    (by decide) selected_cut_06211

theorem unmarked_context_11_5278_186941 : frontier 10 ⟨186941, by decide⟩
    (prefixCache 11 5278) (prefixPartial 11 5278) = false := by
  decide +kernel

theorem node_context_11_5278_186941 : EJMOriginalGlobalDAGData.nodes 10 ⟨186941, by decide⟩ =
    .split (coordinate 11) (![⟨186800, by decide⟩,⟨186843, by decide⟩,⟨186906, by decide⟩,⟨186940, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5278_186941 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5278 ⟨186941, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5278
    ⟨186941, by decide⟩ (by decide) (![⟨186800, by decide⟩,⟨186843, by decide⟩,⟨186906, by decide⟩,⟨186940, by decide⟩]) unmarked_context_11_5278_186941 node_context_11_5278_186941
  intro a
  fin_cases a
  · exact context_12_21112_186800
  · exact context_12_21113_186843
  · exact context_12_21114_186906
  · exact context_12_21115_186940

theorem selected_cut_06212 : selected 9 ⟨186972, by decide⟩
    (prefixPartial 12 21116) = some ⟨12, 2, 0, 186972, 21116, 2261, 65536⟩ := by
  decide +kernel

theorem context_12_21116_186972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21116 ⟨186972, by decide⟩ :=
  accepted_of_selected 12 21116 ⟨186972, by decide⟩ ⟨12, 2, 0, 186972, 21116, 2261, 65536⟩
    (by decide) selected_cut_06212

theorem selected_cut_06213 : selected 9 ⟨187029, by decide⟩
    (prefixPartial 12 21117) = some ⟨12, 2, 0, 187029, 21117, 3885, 65536⟩ := by
  decide +kernel

theorem context_12_21117_187029 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21117 ⟨187029, by decide⟩ :=
  accepted_of_selected 12 21117 ⟨187029, by decide⟩ ⟨12, 2, 0, 187029, 21117, 3885, 65536⟩
    (by decide) selected_cut_06213

theorem selected_cut_06214 : selected 9 ⟨187064, by decide⟩
    (prefixPartial 12 21118) = some ⟨12, 2, 0, 187064, 21118, 2697, 65536⟩ := by
  decide +kernel

theorem context_12_21118_187064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21118 ⟨187064, by decide⟩ :=
  accepted_of_selected 12 21118 ⟨187064, by decide⟩ ⟨12, 2, 0, 187064, 21118, 2697, 65536⟩
    (by decide) selected_cut_06214

theorem selected_cut_06215 : selected 9 ⟨187102, by decide⟩
    (prefixPartial 12 21119) = some ⟨12, 2, 0, 187102, 21119, 2953, 65536⟩ := by
  decide +kernel

theorem context_12_21119_187102 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21119 ⟨187102, by decide⟩ :=
  accepted_of_selected 12 21119 ⟨187102, by decide⟩ ⟨12, 2, 0, 187102, 21119, 2953, 65536⟩
    (by decide) selected_cut_06215

theorem unmarked_context_11_5279_187103 : frontier 10 ⟨187103, by decide⟩
    (prefixCache 11 5279) (prefixPartial 11 5279) = false := by
  decide +kernel

theorem node_context_11_5279_187103 : EJMOriginalGlobalDAGData.nodes 10 ⟨187103, by decide⟩ =
    .split (coordinate 11) (![⟨186972, by decide⟩,⟨187029, by decide⟩,⟨187064, by decide⟩,⟨187102, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5279_187103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5279 ⟨187103, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5279
    ⟨187103, by decide⟩ (by decide) (![⟨186972, by decide⟩,⟨187029, by decide⟩,⟨187064, by decide⟩,⟨187102, by decide⟩]) unmarked_context_11_5279_187103 node_context_11_5279_187103
  intro a
  fin_cases a
  · exact context_12_21116_186972
  · exact context_12_21117_187029
  · exact context_12_21118_187064
  · exact context_12_21119_187102

theorem unmarked_context_10_1319_187104 : frontier 11 ⟨187104, by decide⟩
    (prefixCache 10 1319) (prefixPartial 10 1319) = false := by
  decide +kernel

theorem node_context_10_1319_187104 : EJMOriginalGlobalDAGData.nodes 11 ⟨187104, by decide⟩ =
    .split (coordinate 10) (![⟨186627, by decide⟩,⟨186772, by decide⟩,⟨186941, by decide⟩,⟨187103, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1319_187104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1319 ⟨187104, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1319
    ⟨187104, by decide⟩ (by decide) (![⟨186627, by decide⟩,⟨186772, by decide⟩,⟨186941, by decide⟩,⟨187103, by decide⟩]) unmarked_context_10_1319_187104 node_context_10_1319_187104
  intro a
  fin_cases a
  · exact context_11_5276_186627
  · exact context_11_5277_186772
  · exact context_11_5278_186941
  · exact context_11_5279_187103

theorem unmarked_context_9_329_187105 : frontier 12 ⟨187105, by decide⟩
    (prefixCache 9 329) (prefixPartial 9 329) = false := by
  decide +kernel

theorem node_context_9_329_187105 : EJMOriginalGlobalDAGData.nodes 12 ⟨187105, by decide⟩ =
    .split (coordinate 9) (![⟨184981, by decide⟩,⟨185754, by decide⟩,⟨186485, by decide⟩,⟨187104, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_329_187105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 329 ⟨187105, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 329
    ⟨187105, by decide⟩ (by decide) (![⟨184981, by decide⟩,⟨185754, by decide⟩,⟨186485, by decide⟩,⟨187104, by decide⟩]) unmarked_context_9_329_187105 node_context_9_329_187105
  intro a
  fin_cases a
  · exact context_10_1316_184981
  · exact context_10_1317_185754
  · exact context_10_1318_186485
  · exact context_10_1319_187104

theorem selected_cut_06216 : selected 9 ⟨187168, by decide⟩
    (prefixPartial 12 21120) = some ⟨12, 2, 0, 187168, 21120, 869, 65536⟩ := by
  decide +kernel

theorem context_12_21120_187168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21120 ⟨187168, by decide⟩ :=
  accepted_of_selected 12 21120 ⟨187168, by decide⟩ ⟨12, 2, 0, 187168, 21120, 869, 65536⟩
    (by decide) selected_cut_06216

theorem selected_cut_06217 : selected 9 ⟨187201, by decide⟩
    (prefixPartial 12 21121) = some ⟨12, 2, 0, 187201, 21121, 2953, 65536⟩ := by
  decide +kernel

theorem context_12_21121_187201 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21121 ⟨187201, by decide⟩ :=
  accepted_of_selected 12 21121 ⟨187201, by decide⟩ ⟨12, 2, 0, 187201, 21121, 2953, 65536⟩
    (by decide) selected_cut_06217

theorem selected_cut_06218 : selected 9 ⟨187232, by decide⟩
    (prefixPartial 12 21122) = some ⟨12, 2, 0, 187232, 21122, 2909, 65536⟩ := by
  decide +kernel

theorem context_12_21122_187232 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21122 ⟨187232, by decide⟩ :=
  accepted_of_selected 12 21122 ⟨187232, by decide⟩ ⟨12, 2, 0, 187232, 21122, 2909, 65536⟩
    (by decide) selected_cut_06218

theorem selected_cut_06219 : selected 9 ⟨187270, by decide⟩
    (prefixPartial 12 21123) = some ⟨12, 2, 0, 187270, 21123, 3137, 65536⟩ := by
  decide +kernel

theorem context_12_21123_187270 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21123 ⟨187270, by decide⟩ :=
  accepted_of_selected 12 21123 ⟨187270, by decide⟩ ⟨12, 2, 0, 187270, 21123, 3137, 65536⟩
    (by decide) selected_cut_06219

theorem unmarked_context_11_5280_187271 : frontier 10 ⟨187271, by decide⟩
    (prefixCache 11 5280) (prefixPartial 11 5280) = false := by
  decide +kernel

theorem node_context_11_5280_187271 : EJMOriginalGlobalDAGData.nodes 10 ⟨187271, by decide⟩ =
    .split (coordinate 11) (![⟨187168, by decide⟩,⟨187201, by decide⟩,⟨187232, by decide⟩,⟨187270, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5280_187271 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5280 ⟨187271, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5280
    ⟨187271, by decide⟩ (by decide) (![⟨187168, by decide⟩,⟨187201, by decide⟩,⟨187232, by decide⟩,⟨187270, by decide⟩]) unmarked_context_11_5280_187271 node_context_11_5280_187271
  intro a
  fin_cases a
  · exact context_12_21120_187168
  · exact context_12_21121_187201
  · exact context_12_21122_187232
  · exact context_12_21123_187270

theorem selected_cut_06220 : selected 9 ⟨187292, by decide⟩
    (prefixPartial 12 21124) = some ⟨12, 2, 0, 187292, 21124, 1849, 65536⟩ := by
  decide +kernel

theorem context_12_21124_187292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21124 ⟨187292, by decide⟩ :=
  accepted_of_selected 12 21124 ⟨187292, by decide⟩ ⟨12, 2, 0, 187292, 21124, 1849, 65536⟩
    (by decide) selected_cut_06220

theorem selected_cut_06221 : selected 9 ⟨187320, by decide⟩
    (prefixPartial 12 21125) = some ⟨12, 2, 0, 187320, 21125, 2077, 65536⟩ := by
  decide +kernel

theorem context_12_21125_187320 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21125 ⟨187320, by decide⟩ :=
  accepted_of_selected 12 21125 ⟨187320, by decide⟩ ⟨12, 2, 0, 187320, 21125, 2077, 65536⟩
    (by decide) selected_cut_06221

theorem selected_cut_06222 : selected 9 ⟨187344, by decide⟩
    (prefixPartial 12 21126) = some ⟨12, 2, 0, 187344, 21126, 1985, 65536⟩ := by
  decide +kernel

theorem context_12_21126_187344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21126 ⟨187344, by decide⟩ :=
  accepted_of_selected 12 21126 ⟨187344, by decide⟩ ⟨12, 2, 0, 187344, 21126, 1985, 65536⟩
    (by decide) selected_cut_06222

theorem selected_cut_06223 : selected 9 ⟨187373, by decide⟩
    (prefixPartial 12 21127) = some ⟨12, 2, 0, 187373, 21127, 2313, 65536⟩ := by
  decide +kernel

theorem context_12_21127_187373 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21127 ⟨187373, by decide⟩ :=
  accepted_of_selected 12 21127 ⟨187373, by decide⟩ ⟨12, 2, 0, 187373, 21127, 2313, 65536⟩
    (by decide) selected_cut_06223

theorem unmarked_context_11_5281_187374 : frontier 10 ⟨187374, by decide⟩
    (prefixCache 11 5281) (prefixPartial 11 5281) = false := by
  decide +kernel

theorem node_context_11_5281_187374 : EJMOriginalGlobalDAGData.nodes 10 ⟨187374, by decide⟩ =
    .split (coordinate 11) (![⟨187292, by decide⟩,⟨187320, by decide⟩,⟨187344, by decide⟩,⟨187373, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5281_187374 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5281 ⟨187374, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5281
    ⟨187374, by decide⟩ (by decide) (![⟨187292, by decide⟩,⟨187320, by decide⟩,⟨187344, by decide⟩,⟨187373, by decide⟩]) unmarked_context_11_5281_187374 node_context_11_5281_187374
  intro a
  fin_cases a
  · exact context_12_21124_187292
  · exact context_12_21125_187320
  · exact context_12_21126_187344
  · exact context_12_21127_187373

theorem selected_cut_06224 : selected 9 ⟨187396, by decide⟩
    (prefixPartial 12 21128) = some ⟨12, 2, 0, 187396, 21128, 1761, 65536⟩ := by
  decide +kernel

theorem context_12_21128_187396 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21128 ⟨187396, by decide⟩ :=
  accepted_of_selected 12 21128 ⟨187396, by decide⟩ ⟨12, 2, 0, 187396, 21128, 1761, 65536⟩
    (by decide) selected_cut_06224

theorem selected_cut_06225 : selected 9 ⟨187422, by decide⟩
    (prefixPartial 12 21129) = some ⟨12, 2, 0, 187422, 21129, 2189, 65536⟩ := by
  decide +kernel

theorem context_12_21129_187422 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21129 ⟨187422, by decide⟩ :=
  accepted_of_selected 12 21129 ⟨187422, by decide⟩ ⟨12, 2, 0, 187422, 21129, 2189, 65536⟩
    (by decide) selected_cut_06225

theorem selected_cut_06226 : selected 9 ⟨187459, by decide⟩
    (prefixPartial 12 21130) = some ⟨12, 2, 0, 187459, 21130, 3285, 65536⟩ := by
  decide +kernel

theorem context_12_21130_187459 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21130 ⟨187459, by decide⟩ :=
  accepted_of_selected 12 21130 ⟨187459, by decide⟩ ⟨12, 2, 0, 187459, 21130, 3285, 65536⟩
    (by decide) selected_cut_06226

theorem selected_cut_06227 : selected 9 ⟨187486, by decide⟩
    (prefixPartial 12 21131) = some ⟨12, 2, 0, 187486, 21131, 2229, 65536⟩ := by
  decide +kernel

theorem context_12_21131_187486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21131 ⟨187486, by decide⟩ :=
  accepted_of_selected 12 21131 ⟨187486, by decide⟩ ⟨12, 2, 0, 187486, 21131, 2229, 65536⟩
    (by decide) selected_cut_06227

theorem unmarked_context_11_5282_187487 : frontier 10 ⟨187487, by decide⟩
    (prefixCache 11 5282) (prefixPartial 11 5282) = false := by
  decide +kernel

theorem node_context_11_5282_187487 : EJMOriginalGlobalDAGData.nodes 10 ⟨187487, by decide⟩ =
    .split (coordinate 11) (![⟨187396, by decide⟩,⟨187422, by decide⟩,⟨187459, by decide⟩,⟨187486, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5282_187487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5282 ⟨187487, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5282
    ⟨187487, by decide⟩ (by decide) (![⟨187396, by decide⟩,⟨187422, by decide⟩,⟨187459, by decide⟩,⟨187486, by decide⟩]) unmarked_context_11_5282_187487 node_context_11_5282_187487
  intro a
  fin_cases a
  · exact context_12_21128_187396
  · exact context_12_21129_187422
  · exact context_12_21130_187459
  · exact context_12_21131_187486

theorem selected_cut_06228 : selected 9 ⟨187510, by decide⟩
    (prefixPartial 12 21132) = some ⟨12, 2, 0, 187510, 21132, 2001, 65536⟩ := by
  decide +kernel

theorem context_12_21132_187510 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21132 ⟨187510, by decide⟩ :=
  accepted_of_selected 12 21132 ⟨187510, by decide⟩ ⟨12, 2, 0, 187510, 21132, 2001, 65536⟩
    (by decide) selected_cut_06228

theorem selected_cut_06229 : selected 9 ⟨187537, by decide⟩
    (prefixPartial 12 21133) = some ⟨12, 2, 0, 187537, 21133, 2361, 65536⟩ := by
  decide +kernel

theorem context_12_21133_187537 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21133 ⟨187537, by decide⟩ :=
  accepted_of_selected 12 21133 ⟨187537, by decide⟩ ⟨12, 2, 0, 187537, 21133, 2361, 65536⟩
    (by decide) selected_cut_06229

theorem selected_cut_06230 : selected 9 ⟨187564, by decide⟩
    (prefixPartial 12 21134) = some ⟨12, 2, 0, 187564, 21134, 2101, 65536⟩ := by
  decide +kernel

theorem context_12_21134_187564 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21134 ⟨187564, by decide⟩ :=
  accepted_of_selected 12 21134 ⟨187564, by decide⟩ ⟨12, 2, 0, 187564, 21134, 2101, 65536⟩
    (by decide) selected_cut_06230

theorem selected_cut_06231 : selected 9 ⟨187587, by decide⟩
    (prefixPartial 12 21135) = some ⟨12, 2, 0, 187587, 21135, 2377, 65536⟩ := by
  decide +kernel

theorem context_12_21135_187587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21135 ⟨187587, by decide⟩ :=
  accepted_of_selected 12 21135 ⟨187587, by decide⟩ ⟨12, 2, 0, 187587, 21135, 2377, 65536⟩
    (by decide) selected_cut_06231

theorem unmarked_context_11_5283_187588 : frontier 10 ⟨187588, by decide⟩
    (prefixCache 11 5283) (prefixPartial 11 5283) = false := by
  decide +kernel

theorem node_context_11_5283_187588 : EJMOriginalGlobalDAGData.nodes 10 ⟨187588, by decide⟩ =
    .split (coordinate 11) (![⟨187510, by decide⟩,⟨187537, by decide⟩,⟨187564, by decide⟩,⟨187587, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5283_187588 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5283 ⟨187588, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5283
    ⟨187588, by decide⟩ (by decide) (![⟨187510, by decide⟩,⟨187537, by decide⟩,⟨187564, by decide⟩,⟨187587, by decide⟩]) unmarked_context_11_5283_187588 node_context_11_5283_187588
  intro a
  fin_cases a
  · exact context_12_21132_187510
  · exact context_12_21133_187537
  · exact context_12_21134_187564
  · exact context_12_21135_187587

theorem unmarked_context_10_1320_187589 : frontier 11 ⟨187589, by decide⟩
    (prefixCache 10 1320) (prefixPartial 10 1320) = false := by
  decide +kernel

theorem node_context_10_1320_187589 : EJMOriginalGlobalDAGData.nodes 11 ⟨187589, by decide⟩ =
    .split (coordinate 10) (![⟨187271, by decide⟩,⟨187374, by decide⟩,⟨187487, by decide⟩,⟨187588, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1320_187589 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1320 ⟨187589, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1320
    ⟨187589, by decide⟩ (by decide) (![⟨187271, by decide⟩,⟨187374, by decide⟩,⟨187487, by decide⟩,⟨187588, by decide⟩]) unmarked_context_10_1320_187589 node_context_10_1320_187589
  intro a
  fin_cases a
  · exact context_11_5280_187271
  · exact context_11_5281_187374
  · exact context_11_5282_187487
  · exact context_11_5283_187588

theorem selected_cut_06232 : selected 9 ⟨187607, by decide⟩
    (prefixPartial 12 21136) = some ⟨12, 2, 0, 187607, 21136, 1889, 65536⟩ := by
  decide +kernel

theorem context_12_21136_187607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21136 ⟨187607, by decide⟩ :=
  accepted_of_selected 12 21136 ⟨187607, by decide⟩ ⟨12, 2, 0, 187607, 21136, 1889, 65536⟩
    (by decide) selected_cut_06232

theorem selected_cut_06233 : selected 9 ⟨187633, by decide⟩
    (prefixPartial 12 21137) = some ⟨12, 2, 0, 187633, 21137, 2373, 65536⟩ := by
  decide +kernel

theorem context_12_21137_187633 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21137 ⟨187633, by decide⟩ :=
  accepted_of_selected 12 21137 ⟨187633, by decide⟩ ⟨12, 2, 0, 187633, 21137, 2373, 65536⟩
    (by decide) selected_cut_06233

theorem selected_cut_06234 : selected 9 ⟨187658, by decide⟩
    (prefixPartial 12 21138) = some ⟨12, 2, 0, 187658, 21138, 2289, 65536⟩ := by
  decide +kernel

theorem context_12_21138_187658 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21138 ⟨187658, by decide⟩ :=
  accepted_of_selected 12 21138 ⟨187658, by decide⟩ ⟨12, 2, 0, 187658, 21138, 2289, 65536⟩
    (by decide) selected_cut_06234

theorem selected_cut_06235 : selected 9 ⟨187689, by decide⟩
    (prefixPartial 12 21139) = some ⟨12, 2, 0, 187689, 21139, 2469, 65536⟩ := by
  decide +kernel

theorem context_12_21139_187689 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21139 ⟨187689, by decide⟩ :=
  accepted_of_selected 12 21139 ⟨187689, by decide⟩ ⟨12, 2, 0, 187689, 21139, 2469, 65536⟩
    (by decide) selected_cut_06235

theorem unmarked_context_11_5284_187690 : frontier 10 ⟨187690, by decide⟩
    (prefixCache 11 5284) (prefixPartial 11 5284) = false := by
  decide +kernel

theorem node_context_11_5284_187690 : EJMOriginalGlobalDAGData.nodes 10 ⟨187690, by decide⟩ =
    .split (coordinate 11) (![⟨187607, by decide⟩,⟨187633, by decide⟩,⟨187658, by decide⟩,⟨187689, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5284_187690 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5284 ⟨187690, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5284
    ⟨187690, by decide⟩ (by decide) (![⟨187607, by decide⟩,⟨187633, by decide⟩,⟨187658, by decide⟩,⟨187689, by decide⟩]) unmarked_context_11_5284_187690 node_context_11_5284_187690
  intro a
  fin_cases a
  · exact context_12_21136_187607
  · exact context_12_21137_187633
  · exact context_12_21138_187658
  · exact context_12_21139_187689

theorem selected_cut_06236 : selected 9 ⟨187713, by decide⟩
    (prefixPartial 12 21140) = some ⟨12, 2, 0, 187713, 21140, 1845, 65536⟩ := by
  decide +kernel

theorem context_12_21140_187713 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21140 ⟨187713, by decide⟩ :=
  accepted_of_selected 12 21140 ⟨187713, by decide⟩ ⟨12, 2, 0, 187713, 21140, 1845, 65536⟩
    (by decide) selected_cut_06236

theorem selected_cut_06237 : selected 9 ⟨187736, by decide⟩
    (prefixPartial 12 21141) = some ⟨12, 2, 0, 187736, 21141, 2301, 65536⟩ := by
  decide +kernel

theorem context_12_21141_187736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21141 ⟨187736, by decide⟩ :=
  accepted_of_selected 12 21141 ⟨187736, by decide⟩ ⟨12, 2, 0, 187736, 21141, 2301, 65536⟩
    (by decide) selected_cut_06237

theorem selected_cut_06238 : selected 9 ⟨187759, by decide⟩
    (prefixPartial 12 21142) = some ⟨12, 2, 0, 187759, 21142, 2141, 65536⟩ := by
  decide +kernel

theorem context_12_21142_187759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21142 ⟨187759, by decide⟩ :=
  accepted_of_selected 12 21142 ⟨187759, by decide⟩ ⟨12, 2, 0, 187759, 21142, 2141, 65536⟩
    (by decide) selected_cut_06238

theorem selected_cut_06239 : selected 9 ⟨187785, by decide⟩
    (prefixPartial 12 21143) = some ⟨12, 2, 0, 187785, 21143, 2381, 65536⟩ := by
  decide +kernel

theorem context_12_21143_187785 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21143 ⟨187785, by decide⟩ :=
  accepted_of_selected 12 21143 ⟨187785, by decide⟩ ⟨12, 2, 0, 187785, 21143, 2381, 65536⟩
    (by decide) selected_cut_06239

theorem unmarked_context_11_5285_187786 : frontier 10 ⟨187786, by decide⟩
    (prefixCache 11 5285) (prefixPartial 11 5285) = false := by
  decide +kernel

theorem node_context_11_5285_187786 : EJMOriginalGlobalDAGData.nodes 10 ⟨187786, by decide⟩ =
    .split (coordinate 11) (![⟨187713, by decide⟩,⟨187736, by decide⟩,⟨187759, by decide⟩,⟨187785, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5285_187786 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5285 ⟨187786, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5285
    ⟨187786, by decide⟩ (by decide) (![⟨187713, by decide⟩,⟨187736, by decide⟩,⟨187759, by decide⟩,⟨187785, by decide⟩]) unmarked_context_11_5285_187786 node_context_11_5285_187786
  intro a
  fin_cases a
  · exact context_12_21140_187713
  · exact context_12_21141_187736
  · exact context_12_21142_187759
  · exact context_12_21143_187785

theorem selected_cut_06240 : selected 9 ⟨187807, by decide⟩
    (prefixPartial 12 21144) = some ⟨12, 2, 0, 187807, 21144, 1821, 65536⟩ := by
  decide +kernel

theorem context_12_21144_187807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21144 ⟨187807, by decide⟩ :=
  accepted_of_selected 12 21144 ⟨187807, by decide⟩ ⟨12, 2, 0, 187807, 21144, 1821, 65536⟩
    (by decide) selected_cut_06240

theorem selected_cut_06241 : selected 9 ⟨187829, by decide⟩
    (prefixPartial 12 21145) = some ⟨12, 2, 0, 187829, 21145, 2469, 65536⟩ := by
  decide +kernel

theorem context_12_21145_187829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21145 ⟨187829, by decide⟩ :=
  accepted_of_selected 12 21145 ⟨187829, by decide⟩ ⟨12, 2, 0, 187829, 21145, 2469, 65536⟩
    (by decide) selected_cut_06241

theorem selected_cut_06242 : selected 9 ⟨187877, by decide⟩
    (prefixPartial 12 21146) = some ⟨12, 2, 0, 187877, 21146, 3265, 65536⟩ := by
  decide +kernel

theorem context_12_21146_187877 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21146 ⟨187877, by decide⟩ :=
  accepted_of_selected 12 21146 ⟨187877, by decide⟩ ⟨12, 2, 0, 187877, 21146, 3265, 65536⟩
    (by decide) selected_cut_06242

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
