/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover089
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_12_23079_241909 : frontier 9 ⟨241909, by decide⟩
    (prefixCache 12 23079) (prefixPartial 12 23079) = false := by
  decide +kernel

theorem node_context_12_23079_241909 : EJMOriginalGlobalDAGData.nodes 9 ⟨241909, by decide⟩ =
    .split (coordinate 12) (![⟨241834, by decide⟩,⟨241879, by decide⟩,⟨241900, by decide⟩,⟨241908, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23079_241909 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23079 ⟨241909, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23079
    ⟨241909, by decide⟩ (by decide) (![⟨241834, by decide⟩,⟨241879, by decide⟩,⟨241900, by decide⟩,⟨241908, by decide⟩]) unmarked_context_12_23079_241909 node_context_12_23079_241909
  intro a
  fin_cases a
  · exact context_13_92316_241834
  · exact context_13_92317_241879
  · exact context_13_92318_241900
  · exact context_13_92319_241908

theorem unmarked_context_11_5769_241910 : frontier 10 ⟨241910, by decide⟩
    (prefixCache 11 5769) (prefixPartial 11 5769) = false := by
  decide +kernel

theorem node_context_11_5769_241910 : EJMOriginalGlobalDAGData.nodes 10 ⟨241910, by decide⟩ =
    .split (coordinate 11) (![⟨241657, by decide⟩,⟨241740, by decide⟩,⟨241816, by decide⟩,⟨241909, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5769_241910 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5769 ⟨241910, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5769
    ⟨241910, by decide⟩ (by decide) (![⟨241657, by decide⟩,⟨241740, by decide⟩,⟨241816, by decide⟩,⟨241909, by decide⟩]) unmarked_context_11_5769_241910 node_context_11_5769_241910
  intro a
  fin_cases a
  · exact context_12_23076_241657
  · exact context_12_23077_241740
  · exact context_12_23078_241816
  · exact context_12_23079_241909

theorem selected_cut_08644 : selected 8 ⟨241926, by decide⟩
    (prefixPartial 13 92320) = some ⟨13, 2, 0, 241926, 92320, 1281, 16384⟩ := by
  decide +kernel

theorem context_13_92320_241926 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92320 ⟨241926, by decide⟩ :=
  accepted_of_selected 13 92320 ⟨241926, by decide⟩ ⟨13, 2, 0, 241926, 92320, 1281, 16384⟩
    (by decide) selected_cut_08644

theorem selected_cut_08645 : selected 8 ⟨241993, by decide⟩
    (prefixPartial 13 92321) = some ⟨13, 2, 0, 241993, 92321, 3657, 16384⟩ := by
  decide +kernel

theorem context_13_92321_241993 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92321 ⟨241993, by decide⟩ :=
  accepted_of_selected 13 92321 ⟨241993, by decide⟩ ⟨13, 2, 0, 241993, 92321, 3657, 16384⟩
    (by decide) selected_cut_08645

theorem selected_cut_08646 : selected 8 ⟨242020, by decide⟩
    (prefixPartial 13 92322) = some ⟨13, 2, 0, 242020, 92322, 1957, 16384⟩ := by
  decide +kernel

theorem context_13_92322_242020 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92322 ⟨242020, by decide⟩ :=
  accepted_of_selected 13 92322 ⟨242020, by decide⟩ ⟨13, 2, 0, 242020, 92322, 1957, 16384⟩
    (by decide) selected_cut_08646

theorem selected_cut_08647 : selected 8 ⟨242030, by decide⟩
    (prefixPartial 13 92323) = some ⟨13, 2, 0, 242030, 92323, 1005, 16384⟩ := by
  decide +kernel

theorem context_13_92323_242030 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92323 ⟨242030, by decide⟩ :=
  accepted_of_selected 13 92323 ⟨242030, by decide⟩ ⟨13, 2, 0, 242030, 92323, 1005, 16384⟩
    (by decide) selected_cut_08647

theorem unmarked_context_12_23080_242031 : frontier 9 ⟨242031, by decide⟩
    (prefixCache 12 23080) (prefixPartial 12 23080) = false := by
  decide +kernel

theorem node_context_12_23080_242031 : EJMOriginalGlobalDAGData.nodes 9 ⟨242031, by decide⟩ =
    .split (coordinate 12) (![⟨241926, by decide⟩,⟨241993, by decide⟩,⟨242020, by decide⟩,⟨242030, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23080_242031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23080 ⟨242031, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23080
    ⟨242031, by decide⟩ (by decide) (![⟨241926, by decide⟩,⟨241993, by decide⟩,⟨242020, by decide⟩,⟨242030, by decide⟩]) unmarked_context_12_23080_242031 node_context_12_23080_242031
  intro a
  fin_cases a
  · exact context_13_92320_241926
  · exact context_13_92321_241993
  · exact context_13_92322_242020
  · exact context_13_92323_242030

theorem selected_cut_08648 : selected 8 ⟨242053, by decide⟩
    (prefixPartial 13 92324) = some ⟨13, 2, 0, 242053, 92324, 1465, 16384⟩ := by
  decide +kernel

theorem context_13_92324_242053 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92324 ⟨242053, by decide⟩ :=
  accepted_of_selected 13 92324 ⟨242053, by decide⟩ ⟨13, 2, 0, 242053, 92324, 1465, 16384⟩
    (by decide) selected_cut_08648

theorem selected_cut_08649 : selected 8 ⟨242111, by decide⟩
    (prefixPartial 13 92325) = some ⟨13, 2, 0, 242111, 92325, 3381, 16384⟩ := by
  decide +kernel

theorem context_13_92325_242111 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92325 ⟨242111, by decide⟩ :=
  accepted_of_selected 13 92325 ⟨242111, by decide⟩ ⟨13, 2, 0, 242111, 92325, 3381, 16384⟩
    (by decide) selected_cut_08649

theorem selected_cut_08650 : selected 8 ⟨242141, by decide⟩
    (prefixPartial 13 92326) = some ⟨13, 2, 0, 242141, 92326, 1921, 16384⟩ := by
  decide +kernel

theorem context_13_92326_242141 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92326 ⟨242141, by decide⟩ :=
  accepted_of_selected 13 92326 ⟨242141, by decide⟩ ⟨13, 2, 0, 242141, 92326, 1921, 16384⟩
    (by decide) selected_cut_08650

theorem selected_cut_08651 : selected 8 ⟨242155, by decide⟩
    (prefixPartial 13 92327) = some ⟨13, 2, 0, 242155, 92327, 1041, 16384⟩ := by
  decide +kernel

theorem context_13_92327_242155 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92327 ⟨242155, by decide⟩ :=
  accepted_of_selected 13 92327 ⟨242155, by decide⟩ ⟨13, 2, 0, 242155, 92327, 1041, 16384⟩
    (by decide) selected_cut_08651

theorem unmarked_context_12_23081_242156 : frontier 9 ⟨242156, by decide⟩
    (prefixCache 12 23081) (prefixPartial 12 23081) = false := by
  decide +kernel

theorem node_context_12_23081_242156 : EJMOriginalGlobalDAGData.nodes 9 ⟨242156, by decide⟩ =
    .split (coordinate 12) (![⟨242053, by decide⟩,⟨242111, by decide⟩,⟨242141, by decide⟩,⟨242155, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23081_242156 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23081 ⟨242156, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23081
    ⟨242156, by decide⟩ (by decide) (![⟨242053, by decide⟩,⟨242111, by decide⟩,⟨242141, by decide⟩,⟨242155, by decide⟩]) unmarked_context_12_23081_242156 node_context_12_23081_242156
  intro a
  fin_cases a
  · exact context_13_92324_242053
  · exact context_13_92325_242111
  · exact context_13_92326_242141
  · exact context_13_92327_242155

theorem selected_cut_08652 : selected 9 ⟨242157, by decide⟩
    (prefixPartial 12 23082) = some ⟨12, 1, 0, 242157, 23082, 1, 65536⟩ := by
  decide +kernel

theorem context_12_23082_242157 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23082 ⟨242157, by decide⟩ :=
  accepted_of_selected 12 23082 ⟨242157, by decide⟩ ⟨12, 1, 0, 242157, 23082, 1, 65536⟩
    (by decide) selected_cut_08652

theorem selected_cut_08653 : selected 8 ⟨242184, by decide⟩
    (prefixPartial 13 92332) = some ⟨13, 2, 0, 242184, 92332, 1677, 16384⟩ := by
  decide +kernel

theorem context_13_92332_242184 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92332 ⟨242184, by decide⟩ :=
  accepted_of_selected 13 92332 ⟨242184, by decide⟩ ⟨13, 2, 0, 242184, 92332, 1677, 16384⟩
    (by decide) selected_cut_08653

theorem selected_cut_08654 : selected 7 ⟨242204, by decide⟩
    (prefixPartial 14 369332) = some ⟨14, 2, 0, 242204, 369332, 1121, 4096⟩ := by
  decide +kernel

theorem context_14_369332_242204 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 369332 ⟨242204, by decide⟩ :=
  accepted_of_selected 14 369332 ⟨242204, by decide⟩ ⟨14, 2, 0, 242204, 369332, 1121, 4096⟩
    (by decide) selected_cut_08654

theorem selected_cut_08655 : selected 7 ⟨242229, by decide⟩
    (prefixPartial 14 369333) = some ⟨14, 2, 0, 242229, 369333, 1249, 4096⟩ := by
  decide +kernel

theorem context_14_369333_242229 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 369333 ⟨242229, by decide⟩ :=
  accepted_of_selected 14 369333 ⟨242229, by decide⟩ ⟨14, 2, 0, 242229, 369333, 1249, 4096⟩
    (by decide) selected_cut_08655

theorem selected_cut_08656 : selected 7 ⟨242240, by decide⟩
    (prefixPartial 14 369334) = some ⟨14, 2, 0, 242240, 369334, 801, 4096⟩ := by
  decide +kernel

theorem context_14_369334_242240 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 369334 ⟨242240, by decide⟩ :=
  accepted_of_selected 14 369334 ⟨242240, by decide⟩ ⟨14, 2, 0, 242240, 369334, 801, 4096⟩
    (by decide) selected_cut_08656

theorem selected_cut_08657 : selected 7 ⟨242257, by decide⟩
    (prefixPartial 14 369335) = some ⟨14, 2, 0, 242257, 369335, 945, 4096⟩ := by
  decide +kernel

theorem context_14_369335_242257 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 369335 ⟨242257, by decide⟩ :=
  accepted_of_selected 14 369335 ⟨242257, by decide⟩ ⟨14, 2, 0, 242257, 369335, 945, 4096⟩
    (by decide) selected_cut_08657

theorem unmarked_context_13_92333_242258 : frontier 8 ⟨242258, by decide⟩
    (prefixCache 13 92333) (prefixPartial 13 92333) = false := by
  decide +kernel

theorem node_context_13_92333_242258 : EJMOriginalGlobalDAGData.nodes 8 ⟨242258, by decide⟩ =
    .split (coordinate 13) (![⟨242204, by decide⟩,⟨242229, by decide⟩,⟨242240, by decide⟩,⟨242257, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_92333_242258 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92333 ⟨242258, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 92333
    ⟨242258, by decide⟩ (by decide) (![⟨242204, by decide⟩,⟨242229, by decide⟩,⟨242240, by decide⟩,⟨242257, by decide⟩]) unmarked_context_13_92333_242258 node_context_13_92333_242258
  intro a
  fin_cases a
  · exact context_14_369332_242204
  · exact context_14_369333_242229
  · exact context_14_369334_242240
  · exact context_14_369335_242257

theorem selected_cut_08658 : selected 8 ⟨242279, by decide⟩
    (prefixPartial 13 92334) = some ⟨13, 2, 0, 242279, 92334, 2049, 16384⟩ := by
  decide +kernel

theorem context_13_92334_242279 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92334 ⟨242279, by decide⟩ :=
  accepted_of_selected 13 92334 ⟨242279, by decide⟩ ⟨13, 2, 0, 242279, 92334, 2049, 16384⟩
    (by decide) selected_cut_08658

theorem selected_cut_08659 : selected 8 ⟨242288, by decide⟩
    (prefixPartial 13 92335) = some ⟨13, 2, 0, 242288, 92335, 1145, 16384⟩ := by
  decide +kernel

theorem context_13_92335_242288 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92335 ⟨242288, by decide⟩ :=
  accepted_of_selected 13 92335 ⟨242288, by decide⟩ ⟨13, 2, 0, 242288, 92335, 1145, 16384⟩
    (by decide) selected_cut_08659

theorem unmarked_context_12_23083_242289 : frontier 9 ⟨242289, by decide⟩
    (prefixCache 12 23083) (prefixPartial 12 23083) = false := by
  decide +kernel

theorem node_context_12_23083_242289 : EJMOriginalGlobalDAGData.nodes 9 ⟨242289, by decide⟩ =
    .split (coordinate 12) (![⟨242184, by decide⟩,⟨242258, by decide⟩,⟨242279, by decide⟩,⟨242288, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23083_242289 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23083 ⟨242289, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23083
    ⟨242289, by decide⟩ (by decide) (![⟨242184, by decide⟩,⟨242258, by decide⟩,⟨242279, by decide⟩,⟨242288, by decide⟩]) unmarked_context_12_23083_242289 node_context_12_23083_242289
  intro a
  fin_cases a
  · exact context_13_92332_242184
  · exact context_13_92333_242258
  · exact context_13_92334_242279
  · exact context_13_92335_242288

theorem unmarked_context_11_5770_242290 : frontier 10 ⟨242290, by decide⟩
    (prefixCache 11 5770) (prefixPartial 11 5770) = false := by
  decide +kernel

theorem node_context_11_5770_242290 : EJMOriginalGlobalDAGData.nodes 10 ⟨242290, by decide⟩ =
    .split (coordinate 11) (![⟨242031, by decide⟩,⟨242156, by decide⟩,⟨242157, by decide⟩,⟨242289, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5770_242290 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5770 ⟨242290, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5770
    ⟨242290, by decide⟩ (by decide) (![⟨242031, by decide⟩,⟨242156, by decide⟩,⟨242157, by decide⟩,⟨242289, by decide⟩]) unmarked_context_11_5770_242290 node_context_11_5770_242290
  intro a
  fin_cases a
  · exact context_12_23080_242031
  · exact context_12_23081_242156
  · exact context_12_23082_242157
  · exact context_12_23083_242289

theorem selected_cut_08660 : selected 8 ⟨242298, by decide⟩
    (prefixPartial 13 92336) = some ⟨13, 2, 0, 242298, 92336, 701, 16384⟩ := by
  decide +kernel

theorem context_13_92336_242298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92336 ⟨242298, by decide⟩ :=
  accepted_of_selected 13 92336 ⟨242298, by decide⟩ ⟨13, 2, 0, 242298, 92336, 701, 16384⟩
    (by decide) selected_cut_08660

theorem selected_cut_08661 : selected 8 ⟨242339, by decide⟩
    (prefixPartial 13 92337) = some ⟨13, 2, 0, 242339, 92337, 3021, 16384⟩ := by
  decide +kernel

theorem context_13_92337_242339 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92337 ⟨242339, by decide⟩ :=
  accepted_of_selected 13 92337 ⟨242339, by decide⟩ ⟨13, 2, 0, 242339, 92337, 3021, 16384⟩
    (by decide) selected_cut_08661

theorem selected_cut_08662 : selected 8 ⟨242361, by decide⟩
    (prefixPartial 13 92338) = some ⟨13, 2, 0, 242361, 92338, 1729, 16384⟩ := by
  decide +kernel

theorem context_13_92338_242361 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92338 ⟨242361, by decide⟩ :=
  accepted_of_selected 13 92338 ⟨242361, by decide⟩ ⟨13, 2, 0, 242361, 92338, 1729, 16384⟩
    (by decide) selected_cut_08662

theorem selected_cut_08663 : selected 8 ⟨242368, by decide⟩
    (prefixPartial 13 92339) = some ⟨13, 2, 0, 242368, 92339, 905, 16384⟩ := by
  decide +kernel

theorem context_13_92339_242368 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92339 ⟨242368, by decide⟩ :=
  accepted_of_selected 13 92339 ⟨242368, by decide⟩ ⟨13, 2, 0, 242368, 92339, 905, 16384⟩
    (by decide) selected_cut_08663

theorem unmarked_context_12_23084_242369 : frontier 9 ⟨242369, by decide⟩
    (prefixCache 12 23084) (prefixPartial 12 23084) = false := by
  decide +kernel

theorem node_context_12_23084_242369 : EJMOriginalGlobalDAGData.nodes 9 ⟨242369, by decide⟩ =
    .split (coordinate 12) (![⟨242298, by decide⟩,⟨242339, by decide⟩,⟨242361, by decide⟩,⟨242368, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23084_242369 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23084 ⟨242369, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23084
    ⟨242369, by decide⟩ (by decide) (![⟨242298, by decide⟩,⟨242339, by decide⟩,⟨242361, by decide⟩,⟨242368, by decide⟩]) unmarked_context_12_23084_242369 node_context_12_23084_242369
  intro a
  fin_cases a
  · exact context_13_92336_242298
  · exact context_13_92337_242339
  · exact context_13_92338_242361
  · exact context_13_92339_242368

theorem selected_cut_08664 : selected 8 ⟨242381, by decide⟩
    (prefixPartial 13 92340) = some ⟨13, 2, 0, 242381, 92340, 777, 16384⟩ := by
  decide +kernel

theorem context_13_92340_242381 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92340 ⟨242381, by decide⟩ :=
  accepted_of_selected 13 92340 ⟨242381, by decide⟩ ⟨13, 2, 0, 242381, 92340, 777, 16384⟩
    (by decide) selected_cut_08664

theorem selected_cut_08665 : selected 8 ⟨242422, by decide⟩
    (prefixPartial 13 92341) = some ⟨13, 2, 0, 242422, 92341, 2653, 16384⟩ := by
  decide +kernel

theorem context_13_92341_242422 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92341 ⟨242422, by decide⟩ :=
  accepted_of_selected 13 92341 ⟨242422, by decide⟩ ⟨13, 2, 0, 242422, 92341, 2653, 16384⟩
    (by decide) selected_cut_08665

theorem selected_cut_08666 : selected 8 ⟨242446, by decide⟩
    (prefixPartial 13 92342) = some ⟨13, 2, 0, 242446, 92342, 1637, 16384⟩ := by
  decide +kernel

theorem context_13_92342_242446 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92342 ⟨242446, by decide⟩ :=
  accepted_of_selected 13 92342 ⟨242446, by decide⟩ ⟨13, 2, 0, 242446, 92342, 1637, 16384⟩
    (by decide) selected_cut_08666

theorem selected_cut_08667 : selected 8 ⟨242455, by decide⟩
    (prefixPartial 13 92343) = some ⟨13, 2, 0, 242455, 92343, 841, 16384⟩ := by
  decide +kernel

theorem context_13_92343_242455 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92343 ⟨242455, by decide⟩ :=
  accepted_of_selected 13 92343 ⟨242455, by decide⟩ ⟨13, 2, 0, 242455, 92343, 841, 16384⟩
    (by decide) selected_cut_08667

theorem unmarked_context_12_23085_242456 : frontier 9 ⟨242456, by decide⟩
    (prefixCache 12 23085) (prefixPartial 12 23085) = false := by
  decide +kernel

theorem node_context_12_23085_242456 : EJMOriginalGlobalDAGData.nodes 9 ⟨242456, by decide⟩ =
    .split (coordinate 12) (![⟨242381, by decide⟩,⟨242422, by decide⟩,⟨242446, by decide⟩,⟨242455, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23085_242456 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23085 ⟨242456, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23085
    ⟨242456, by decide⟩ (by decide) (![⟨242381, by decide⟩,⟨242422, by decide⟩,⟨242446, by decide⟩,⟨242455, by decide⟩]) unmarked_context_12_23085_242456 node_context_12_23085_242456
  intro a
  fin_cases a
  · exact context_13_92340_242381
  · exact context_13_92341_242422
  · exact context_13_92342_242446
  · exact context_13_92343_242455

theorem selected_cut_08668 : selected 8 ⟨242467, by decide⟩
    (prefixPartial 13 92344) = some ⟨13, 2, 0, 242467, 92344, 841, 16384⟩ := by
  decide +kernel

theorem context_13_92344_242467 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92344 ⟨242467, by decide⟩ :=
  accepted_of_selected 13 92344 ⟨242467, by decide⟩ ⟨13, 2, 0, 242467, 92344, 841, 16384⟩
    (by decide) selected_cut_08668

theorem selected_cut_08669 : selected 8 ⟨242501, by decide⟩
    (prefixPartial 13 92345) = some ⟨13, 2, 0, 242501, 92345, 2901, 16384⟩ := by
  decide +kernel

theorem context_13_92345_242501 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92345 ⟨242501, by decide⟩ :=
  accepted_of_selected 13 92345 ⟨242501, by decide⟩ ⟨13, 2, 0, 242501, 92345, 2901, 16384⟩
    (by decide) selected_cut_08669

theorem selected_cut_08670 : selected 8 ⟨242520, by decide⟩
    (prefixPartial 13 92346) = some ⟨13, 2, 0, 242520, 92346, 1469, 16384⟩ := by
  decide +kernel

theorem context_13_92346_242520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92346 ⟨242520, by decide⟩ :=
  accepted_of_selected 13 92346 ⟨242520, by decide⟩ ⟨13, 2, 0, 242520, 92346, 1469, 16384⟩
    (by decide) selected_cut_08670

theorem selected_cut_08671 : selected 8 ⟨242531, by decide⟩
    (prefixPartial 13 92347) = some ⟨13, 2, 0, 242531, 92347, 813, 16384⟩ := by
  decide +kernel

theorem context_13_92347_242531 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92347 ⟨242531, by decide⟩ :=
  accepted_of_selected 13 92347 ⟨242531, by decide⟩ ⟨13, 2, 0, 242531, 92347, 813, 16384⟩
    (by decide) selected_cut_08671

theorem unmarked_context_12_23086_242532 : frontier 9 ⟨242532, by decide⟩
    (prefixCache 12 23086) (prefixPartial 12 23086) = false := by
  decide +kernel

theorem node_context_12_23086_242532 : EJMOriginalGlobalDAGData.nodes 9 ⟨242532, by decide⟩ =
    .split (coordinate 12) (![⟨242467, by decide⟩,⟨242501, by decide⟩,⟨242520, by decide⟩,⟨242531, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23086_242532 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23086 ⟨242532, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23086
    ⟨242532, by decide⟩ (by decide) (![⟨242467, by decide⟩,⟨242501, by decide⟩,⟨242520, by decide⟩,⟨242531, by decide⟩]) unmarked_context_12_23086_242532 node_context_12_23086_242532
  intro a
  fin_cases a
  · exact context_13_92344_242467
  · exact context_13_92345_242501
  · exact context_13_92346_242520
  · exact context_13_92347_242531

theorem selected_cut_08672 : selected 8 ⟨242544, by decide⟩
    (prefixPartial 13 92348) = some ⟨13, 2, 0, 242544, 92348, 857, 16384⟩ := by
  decide +kernel

theorem context_13_92348_242544 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92348 ⟨242544, by decide⟩ :=
  accepted_of_selected 13 92348 ⟨242544, by decide⟩ ⟨13, 2, 0, 242544, 92348, 857, 16384⟩
    (by decide) selected_cut_08672

theorem selected_cut_08673 : selected 8 ⟨242582, by decide⟩
    (prefixPartial 13 92349) = some ⟨13, 2, 0, 242582, 92349, 3033, 16384⟩ := by
  decide +kernel

theorem context_13_92349_242582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92349 ⟨242582, by decide⟩ :=
  accepted_of_selected 13 92349 ⟨242582, by decide⟩ ⟨13, 2, 0, 242582, 92349, 3033, 16384⟩
    (by decide) selected_cut_08673

theorem selected_cut_08674 : selected 8 ⟨242601, by decide⟩
    (prefixPartial 13 92350) = some ⟨13, 2, 0, 242601, 92350, 1697, 16384⟩ := by
  decide +kernel

theorem context_13_92350_242601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92350 ⟨242601, by decide⟩ :=
  accepted_of_selected 13 92350 ⟨242601, by decide⟩ ⟨13, 2, 0, 242601, 92350, 1697, 16384⟩
    (by decide) selected_cut_08674

theorem selected_cut_08675 : selected 8 ⟨242608, by decide⟩
    (prefixPartial 13 92351) = some ⟨13, 2, 0, 242608, 92351, 929, 16384⟩ := by
  decide +kernel

theorem context_13_92351_242608 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92351 ⟨242608, by decide⟩ :=
  accepted_of_selected 13 92351 ⟨242608, by decide⟩ ⟨13, 2, 0, 242608, 92351, 929, 16384⟩
    (by decide) selected_cut_08675

theorem unmarked_context_12_23087_242609 : frontier 9 ⟨242609, by decide⟩
    (prefixCache 12 23087) (prefixPartial 12 23087) = false := by
  decide +kernel

theorem node_context_12_23087_242609 : EJMOriginalGlobalDAGData.nodes 9 ⟨242609, by decide⟩ =
    .split (coordinate 12) (![⟨242544, by decide⟩,⟨242582, by decide⟩,⟨242601, by decide⟩,⟨242608, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23087_242609 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23087 ⟨242609, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23087
    ⟨242609, by decide⟩ (by decide) (![⟨242544, by decide⟩,⟨242582, by decide⟩,⟨242601, by decide⟩,⟨242608, by decide⟩]) unmarked_context_12_23087_242609 node_context_12_23087_242609
  intro a
  fin_cases a
  · exact context_13_92348_242544
  · exact context_13_92349_242582
  · exact context_13_92350_242601
  · exact context_13_92351_242608

theorem unmarked_context_11_5771_242610 : frontier 10 ⟨242610, by decide⟩
    (prefixCache 11 5771) (prefixPartial 11 5771) = false := by
  decide +kernel

theorem node_context_11_5771_242610 : EJMOriginalGlobalDAGData.nodes 10 ⟨242610, by decide⟩ =
    .split (coordinate 11) (![⟨242369, by decide⟩,⟨242456, by decide⟩,⟨242532, by decide⟩,⟨242609, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5771_242610 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5771 ⟨242610, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5771
    ⟨242610, by decide⟩ (by decide) (![⟨242369, by decide⟩,⟨242456, by decide⟩,⟨242532, by decide⟩,⟨242609, by decide⟩]) unmarked_context_11_5771_242610 node_context_11_5771_242610
  intro a
  fin_cases a
  · exact context_12_23084_242369
  · exact context_12_23085_242456
  · exact context_12_23086_242532
  · exact context_12_23087_242609

theorem unmarked_context_10_1442_242611 : frontier 11 ⟨242611, by decide⟩
    (prefixCache 10 1442) (prefixPartial 10 1442) = false := by
  decide +kernel

theorem node_context_10_1442_242611 : EJMOriginalGlobalDAGData.nodes 11 ⟨242611, by decide⟩ =
    .split (coordinate 10) (![⟨241564, by decide⟩,⟨241910, by decide⟩,⟨242290, by decide⟩,⟨242610, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1442_242611 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1442 ⟨242611, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1442
    ⟨242611, by decide⟩ (by decide) (![⟨241564, by decide⟩,⟨241910, by decide⟩,⟨242290, by decide⟩,⟨242610, by decide⟩]) unmarked_context_10_1442_242611 node_context_10_1442_242611
  intro a
  fin_cases a
  · exact context_11_5768_241564
  · exact context_11_5769_241910
  · exact context_11_5770_242290
  · exact context_11_5771_242610

theorem selected_cut_08676 : selected 8 ⟨242619, by decide⟩
    (prefixPartial 13 92352) = some ⟨13, 2, 0, 242619, 92352, 897, 16384⟩ := by
  decide +kernel

theorem context_13_92352_242619 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92352 ⟨242619, by decide⟩ :=
  accepted_of_selected 13 92352 ⟨242619, by decide⟩ ⟨13, 2, 0, 242619, 92352, 897, 16384⟩
    (by decide) selected_cut_08676

theorem selected_cut_08677 : selected 8 ⟨242654, by decide⟩
    (prefixPartial 13 92353) = some ⟨13, 2, 0, 242654, 92353, 2605, 16384⟩ := by
  decide +kernel

theorem context_13_92353_242654 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92353 ⟨242654, by decide⟩ :=
  accepted_of_selected 13 92353 ⟨242654, by decide⟩ ⟨13, 2, 0, 242654, 92353, 2605, 16384⟩
    (by decide) selected_cut_08677

theorem selected_cut_08678 : selected 8 ⟨242671, by decide⟩
    (prefixPartial 13 92354) = some ⟨13, 2, 0, 242671, 92354, 1521, 16384⟩ := by
  decide +kernel

theorem context_13_92354_242671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92354 ⟨242671, by decide⟩ :=
  accepted_of_selected 13 92354 ⟨242671, by decide⟩ ⟨13, 2, 0, 242671, 92354, 1521, 16384⟩
    (by decide) selected_cut_08678

theorem selected_cut_08679 : selected 8 ⟨242676, by decide⟩
    (prefixPartial 13 92355) = some ⟨13, 2, 0, 242676, 92355, 841, 16384⟩ := by
  decide +kernel

theorem context_13_92355_242676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92355 ⟨242676, by decide⟩ :=
  accepted_of_selected 13 92355 ⟨242676, by decide⟩ ⟨13, 2, 0, 242676, 92355, 841, 16384⟩
    (by decide) selected_cut_08679

theorem unmarked_context_12_23088_242677 : frontier 9 ⟨242677, by decide⟩
    (prefixCache 12 23088) (prefixPartial 12 23088) = false := by
  decide +kernel

theorem node_context_12_23088_242677 : EJMOriginalGlobalDAGData.nodes 9 ⟨242677, by decide⟩ =
    .split (coordinate 12) (![⟨242619, by decide⟩,⟨242654, by decide⟩,⟨242671, by decide⟩,⟨242676, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23088_242677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23088 ⟨242677, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23088
    ⟨242677, by decide⟩ (by decide) (![⟨242619, by decide⟩,⟨242654, by decide⟩,⟨242671, by decide⟩,⟨242676, by decide⟩]) unmarked_context_12_23088_242677 node_context_12_23088_242677
  intro a
  fin_cases a
  · exact context_13_92352_242619
  · exact context_13_92353_242654
  · exact context_13_92354_242671
  · exact context_13_92355_242676

theorem selected_cut_08680 : selected 8 ⟨242691, by decide⟩
    (prefixPartial 13 92356) = some ⟨13, 2, 0, 242691, 92356, 877, 16384⟩ := by
  decide +kernel

theorem context_13_92356_242691 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92356 ⟨242691, by decide⟩ :=
  accepted_of_selected 13 92356 ⟨242691, by decide⟩ ⟨13, 2, 0, 242691, 92356, 877, 16384⟩
    (by decide) selected_cut_08680

theorem selected_cut_08681 : selected 8 ⟨242726, by decide⟩
    (prefixPartial 13 92357) = some ⟨13, 2, 0, 242726, 92357, 2401, 16384⟩ := by
  decide +kernel

theorem context_13_92357_242726 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92357 ⟨242726, by decide⟩ :=
  accepted_of_selected 13 92357 ⟨242726, by decide⟩ ⟨13, 2, 0, 242726, 92357, 2401, 16384⟩
    (by decide) selected_cut_08681

theorem selected_cut_08682 : selected 8 ⟨242746, by decide⟩
    (prefixPartial 13 92358) = some ⟨13, 2, 0, 242746, 92358, 1469, 16384⟩ := by
  decide +kernel

theorem context_13_92358_242746 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92358 ⟨242746, by decide⟩ :=
  accepted_of_selected 13 92358 ⟨242746, by decide⟩ ⟨13, 2, 0, 242746, 92358, 1469, 16384⟩
    (by decide) selected_cut_08682

theorem selected_cut_08683 : selected 8 ⟨242755, by decide⟩
    (prefixPartial 13 92359) = some ⟨13, 2, 0, 242755, 92359, 969, 16384⟩ := by
  decide +kernel

theorem context_13_92359_242755 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92359 ⟨242755, by decide⟩ :=
  accepted_of_selected 13 92359 ⟨242755, by decide⟩ ⟨13, 2, 0, 242755, 92359, 969, 16384⟩
    (by decide) selected_cut_08683

theorem unmarked_context_12_23089_242756 : frontier 9 ⟨242756, by decide⟩
    (prefixCache 12 23089) (prefixPartial 12 23089) = false := by
  decide +kernel

theorem node_context_12_23089_242756 : EJMOriginalGlobalDAGData.nodes 9 ⟨242756, by decide⟩ =
    .split (coordinate 12) (![⟨242691, by decide⟩,⟨242726, by decide⟩,⟨242746, by decide⟩,⟨242755, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23089_242756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23089 ⟨242756, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23089
    ⟨242756, by decide⟩ (by decide) (![⟨242691, by decide⟩,⟨242726, by decide⟩,⟨242746, by decide⟩,⟨242755, by decide⟩]) unmarked_context_12_23089_242756 node_context_12_23089_242756
  intro a
  fin_cases a
  · exact context_13_92356_242691
  · exact context_13_92357_242726
  · exact context_13_92358_242746
  · exact context_13_92359_242755

theorem selected_cut_08684 : selected 8 ⟨242764, by decide⟩
    (prefixPartial 13 92360) = some ⟨13, 2, 0, 242764, 92360, 821, 16384⟩ := by
  decide +kernel

theorem context_13_92360_242764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92360 ⟨242764, by decide⟩ :=
  accepted_of_selected 13 92360 ⟨242764, by decide⟩ ⟨13, 2, 0, 242764, 92360, 821, 16384⟩
    (by decide) selected_cut_08684

theorem selected_cut_08685 : selected 8 ⟨242804, by decide⟩
    (prefixPartial 13 92361) = some ⟨13, 2, 0, 242804, 92361, 2889, 16384⟩ := by
  decide +kernel

theorem context_13_92361_242804 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92361 ⟨242804, by decide⟩ :=
  accepted_of_selected 13 92361 ⟨242804, by decide⟩ ⟨13, 2, 0, 242804, 92361, 2889, 16384⟩
    (by decide) selected_cut_08685

theorem selected_cut_08686 : selected 8 ⟨242822, by decide⟩
    (prefixPartial 13 92362) = some ⟨13, 2, 0, 242822, 92362, 1733, 16384⟩ := by
  decide +kernel

theorem context_13_92362_242822 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92362 ⟨242822, by decide⟩ :=
  accepted_of_selected 13 92362 ⟨242822, by decide⟩ ⟨13, 2, 0, 242822, 92362, 1733, 16384⟩
    (by decide) selected_cut_08686

theorem selected_cut_08687 : selected 8 ⟨242830, by decide⟩
    (prefixPartial 13 92363) = some ⟨13, 2, 0, 242830, 92363, 965, 16384⟩ := by
  decide +kernel

theorem context_13_92363_242830 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92363 ⟨242830, by decide⟩ :=
  accepted_of_selected 13 92363 ⟨242830, by decide⟩ ⟨13, 2, 0, 242830, 92363, 965, 16384⟩
    (by decide) selected_cut_08687

theorem unmarked_context_12_23090_242831 : frontier 9 ⟨242831, by decide⟩
    (prefixCache 12 23090) (prefixPartial 12 23090) = false := by
  decide +kernel

theorem node_context_12_23090_242831 : EJMOriginalGlobalDAGData.nodes 9 ⟨242831, by decide⟩ =
    .split (coordinate 12) (![⟨242764, by decide⟩,⟨242804, by decide⟩,⟨242822, by decide⟩,⟨242830, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23090_242831 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23090 ⟨242831, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23090
    ⟨242831, by decide⟩ (by decide) (![⟨242764, by decide⟩,⟨242804, by decide⟩,⟨242822, by decide⟩,⟨242830, by decide⟩]) unmarked_context_12_23090_242831 node_context_12_23090_242831
  intro a
  fin_cases a
  · exact context_13_92360_242764
  · exact context_13_92361_242804
  · exact context_13_92362_242822
  · exact context_13_92363_242830

theorem selected_cut_08688 : selected 8 ⟨242852, by decide⟩
    (prefixPartial 13 92364) = some ⟨13, 2, 0, 242852, 92364, 1129, 16384⟩ := by
  decide +kernel

theorem context_13_92364_242852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92364 ⟨242852, by decide⟩ :=
  accepted_of_selected 13 92364 ⟨242852, by decide⟩ ⟨13, 2, 0, 242852, 92364, 1129, 16384⟩
    (by decide) selected_cut_08688

theorem selected_cut_08689 : selected 8 ⟨242904, by decide⟩
    (prefixPartial 13 92365) = some ⟨13, 2, 0, 242904, 92365, 3237, 16384⟩ := by
  decide +kernel

theorem context_13_92365_242904 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92365 ⟨242904, by decide⟩ :=
  accepted_of_selected 13 92365 ⟨242904, by decide⟩ ⟨13, 2, 0, 242904, 92365, 3237, 16384⟩
    (by decide) selected_cut_08689

theorem selected_cut_08690 : selected 8 ⟨242925, by decide⟩
    (prefixPartial 13 92366) = some ⟨13, 2, 0, 242925, 92366, 1765, 16384⟩ := by
  decide +kernel

theorem context_13_92366_242925 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92366 ⟨242925, by decide⟩ :=
  accepted_of_selected 13 92366 ⟨242925, by decide⟩ ⟨13, 2, 0, 242925, 92366, 1765, 16384⟩
    (by decide) selected_cut_08690

theorem selected_cut_08691 : selected 8 ⟨242933, by decide⟩
    (prefixPartial 13 92367) = some ⟨13, 2, 0, 242933, 92367, 1013, 16384⟩ := by
  decide +kernel

theorem context_13_92367_242933 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92367 ⟨242933, by decide⟩ :=
  accepted_of_selected 13 92367 ⟨242933, by decide⟩ ⟨13, 2, 0, 242933, 92367, 1013, 16384⟩
    (by decide) selected_cut_08691

theorem unmarked_context_12_23091_242934 : frontier 9 ⟨242934, by decide⟩
    (prefixCache 12 23091) (prefixPartial 12 23091) = false := by
  decide +kernel

theorem node_context_12_23091_242934 : EJMOriginalGlobalDAGData.nodes 9 ⟨242934, by decide⟩ =
    .split (coordinate 12) (![⟨242852, by decide⟩,⟨242904, by decide⟩,⟨242925, by decide⟩,⟨242933, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23091_242934 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23091 ⟨242934, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23091
    ⟨242934, by decide⟩ (by decide) (![⟨242852, by decide⟩,⟨242904, by decide⟩,⟨242925, by decide⟩,⟨242933, by decide⟩]) unmarked_context_12_23091_242934 node_context_12_23091_242934
  intro a
  fin_cases a
  · exact context_13_92364_242852
  · exact context_13_92365_242904
  · exact context_13_92366_242925
  · exact context_13_92367_242933

theorem unmarked_context_11_5772_242935 : frontier 10 ⟨242935, by decide⟩
    (prefixCache 11 5772) (prefixPartial 11 5772) = false := by
  decide +kernel

theorem node_context_11_5772_242935 : EJMOriginalGlobalDAGData.nodes 10 ⟨242935, by decide⟩ =
    .split (coordinate 11) (![⟨242677, by decide⟩,⟨242756, by decide⟩,⟨242831, by decide⟩,⟨242934, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5772_242935 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5772 ⟨242935, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5772
    ⟨242935, by decide⟩ (by decide) (![⟨242677, by decide⟩,⟨242756, by decide⟩,⟨242831, by decide⟩,⟨242934, by decide⟩]) unmarked_context_11_5772_242935 node_context_11_5772_242935
  intro a
  fin_cases a
  · exact context_12_23088_242677
  · exact context_12_23089_242756
  · exact context_12_23090_242831
  · exact context_12_23091_242934

theorem selected_cut_08692 : selected 8 ⟨242947, by decide⟩
    (prefixPartial 13 92368) = some ⟨13, 2, 0, 242947, 92368, 645, 16384⟩ := by
  decide +kernel

theorem context_13_92368_242947 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92368 ⟨242947, by decide⟩ :=
  accepted_of_selected 13 92368 ⟨242947, by decide⟩ ⟨13, 2, 0, 242947, 92368, 645, 16384⟩
    (by decide) selected_cut_08692

theorem selected_cut_08693 : selected 8 ⟨243011, by decide⟩
    (prefixPartial 13 92369) = some ⟨13, 2, 0, 243011, 92369, 3001, 16384⟩ := by
  decide +kernel

theorem context_13_92369_243011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92369 ⟨243011, by decide⟩ :=
  accepted_of_selected 13 92369 ⟨243011, by decide⟩ ⟨13, 2, 0, 243011, 92369, 3001, 16384⟩
    (by decide) selected_cut_08693

theorem selected_cut_08694 : selected 8 ⟨243032, by decide⟩
    (prefixPartial 13 92370) = some ⟨13, 2, 0, 243032, 92370, 1325, 16384⟩ := by
  decide +kernel

theorem context_13_92370_243032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92370 ⟨243032, by decide⟩ :=
  accepted_of_selected 13 92370 ⟨243032, by decide⟩ ⟨13, 2, 0, 243032, 92370, 1325, 16384⟩
    (by decide) selected_cut_08694

theorem selected_cut_08695 : selected 8 ⟨243042, by decide⟩
    (prefixPartial 13 92371) = some ⟨13, 2, 0, 243042, 92371, 957, 16384⟩ := by
  decide +kernel

theorem context_13_92371_243042 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92371 ⟨243042, by decide⟩ :=
  accepted_of_selected 13 92371 ⟨243042, by decide⟩ ⟨13, 2, 0, 243042, 92371, 957, 16384⟩
    (by decide) selected_cut_08695

theorem unmarked_context_12_23092_243043 : frontier 9 ⟨243043, by decide⟩
    (prefixCache 12 23092) (prefixPartial 12 23092) = false := by
  decide +kernel

theorem node_context_12_23092_243043 : EJMOriginalGlobalDAGData.nodes 9 ⟨243043, by decide⟩ =
    .split (coordinate 12) (![⟨242947, by decide⟩,⟨243011, by decide⟩,⟨243032, by decide⟩,⟨243042, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23092_243043 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23092 ⟨243043, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23092
    ⟨243043, by decide⟩ (by decide) (![⟨242947, by decide⟩,⟨243011, by decide⟩,⟨243032, by decide⟩,⟨243042, by decide⟩]) unmarked_context_12_23092_243043 node_context_12_23092_243043
  intro a
  fin_cases a
  · exact context_13_92368_242947
  · exact context_13_92369_243011
  · exact context_13_92370_243032
  · exact context_13_92371_243042

theorem selected_cut_08696 : selected 8 ⟨243053, by decide⟩
    (prefixPartial 13 92372) = some ⟨13, 2, 0, 243053, 92372, 633, 16384⟩ := by
  decide +kernel

theorem context_13_92372_243053 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92372 ⟨243053, by decide⟩ :=
  accepted_of_selected 13 92372 ⟨243053, by decide⟩ ⟨13, 2, 0, 243053, 92372, 633, 16384⟩
    (by decide) selected_cut_08696

theorem selected_cut_08697 : selected 8 ⟨243086, by decide⟩
    (prefixPartial 13 92373) = some ⟨13, 2, 0, 243086, 92373, 2321, 16384⟩ := by
  decide +kernel

theorem context_13_92373_243086 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92373 ⟨243086, by decide⟩ :=
  accepted_of_selected 13 92373 ⟨243086, by decide⟩ ⟨13, 2, 0, 243086, 92373, 2321, 16384⟩
    (by decide) selected_cut_08697

theorem selected_cut_08698 : selected 8 ⟨243103, by decide⟩
    (prefixPartial 13 92374) = some ⟨13, 2, 0, 243103, 92374, 1313, 16384⟩ := by
  decide +kernel

theorem context_13_92374_243103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92374 ⟨243103, by decide⟩ :=
  accepted_of_selected 13 92374 ⟨243103, by decide⟩ ⟨13, 2, 0, 243103, 92374, 1313, 16384⟩
    (by decide) selected_cut_08698

theorem selected_cut_08699 : selected 8 ⟨243111, by decide⟩
    (prefixPartial 13 92375) = some ⟨13, 2, 0, 243111, 92375, 921, 16384⟩ := by
  decide +kernel

theorem context_13_92375_243111 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92375 ⟨243111, by decide⟩ :=
  accepted_of_selected 13 92375 ⟨243111, by decide⟩ ⟨13, 2, 0, 243111, 92375, 921, 16384⟩
    (by decide) selected_cut_08699

theorem unmarked_context_12_23093_243112 : frontier 9 ⟨243112, by decide⟩
    (prefixCache 12 23093) (prefixPartial 12 23093) = false := by
  decide +kernel

theorem node_context_12_23093_243112 : EJMOriginalGlobalDAGData.nodes 9 ⟨243112, by decide⟩ =
    .split (coordinate 12) (![⟨243053, by decide⟩,⟨243086, by decide⟩,⟨243103, by decide⟩,⟨243111, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23093_243112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23093 ⟨243112, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23093
    ⟨243112, by decide⟩ (by decide) (![⟨243053, by decide⟩,⟨243086, by decide⟩,⟨243103, by decide⟩,⟨243111, by decide⟩]) unmarked_context_12_23093_243112 node_context_12_23093_243112
  intro a
  fin_cases a
  · exact context_13_92372_243053
  · exact context_13_92373_243086
  · exact context_13_92374_243103
  · exact context_13_92375_243111

theorem selected_cut_08700 : selected 8 ⟨243123, by decide⟩
    (prefixPartial 13 92376) = some ⟨13, 2, 0, 243123, 92376, 589, 16384⟩ := by
  decide +kernel

theorem context_13_92376_243123 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92376 ⟨243123, by decide⟩ :=
  accepted_of_selected 13 92376 ⟨243123, by decide⟩ ⟨13, 2, 0, 243123, 92376, 589, 16384⟩
    (by decide) selected_cut_08700

theorem selected_cut_08701 : selected 8 ⟨243163, by decide⟩
    (prefixPartial 13 92377) = some ⟨13, 2, 0, 243163, 92377, 2637, 16384⟩ := by
  decide +kernel

theorem context_13_92377_243163 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92377 ⟨243163, by decide⟩ :=
  accepted_of_selected 13 92377 ⟨243163, by decide⟩ ⟨13, 2, 0, 243163, 92377, 2637, 16384⟩
    (by decide) selected_cut_08701

theorem selected_cut_08702 : selected 8 ⟨243182, by decide⟩
    (prefixPartial 13 92378) = some ⟨13, 2, 0, 243182, 92378, 1433, 16384⟩ := by
  decide +kernel

theorem context_13_92378_243182 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92378 ⟨243182, by decide⟩ :=
  accepted_of_selected 13 92378 ⟨243182, by decide⟩ ⟨13, 2, 0, 243182, 92378, 1433, 16384⟩
    (by decide) selected_cut_08702

theorem selected_cut_08703 : selected 8 ⟨243187, by decide⟩
    (prefixPartial 13 92379) = some ⟨13, 2, 0, 243187, 92379, 961, 16384⟩ := by
  decide +kernel

theorem context_13_92379_243187 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92379 ⟨243187, by decide⟩ :=
  accepted_of_selected 13 92379 ⟨243187, by decide⟩ ⟨13, 2, 0, 243187, 92379, 961, 16384⟩
    (by decide) selected_cut_08703

theorem unmarked_context_12_23094_243188 : frontier 9 ⟨243188, by decide⟩
    (prefixCache 12 23094) (prefixPartial 12 23094) = false := by
  decide +kernel

theorem node_context_12_23094_243188 : EJMOriginalGlobalDAGData.nodes 9 ⟨243188, by decide⟩ =
    .split (coordinate 12) (![⟨243123, by decide⟩,⟨243163, by decide⟩,⟨243182, by decide⟩,⟨243187, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23094_243188 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23094 ⟨243188, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23094
    ⟨243188, by decide⟩ (by decide) (![⟨243123, by decide⟩,⟨243163, by decide⟩,⟨243182, by decide⟩,⟨243187, by decide⟩]) unmarked_context_12_23094_243188 node_context_12_23094_243188
  intro a
  fin_cases a
  · exact context_13_92376_243123
  · exact context_13_92377_243163
  · exact context_13_92378_243182
  · exact context_13_92379_243187

theorem selected_cut_08704 : selected 8 ⟨243202, by decide⟩
    (prefixPartial 13 92380) = some ⟨13, 2, 0, 243202, 92380, 737, 16384⟩ := by
  decide +kernel

theorem context_13_92380_243202 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92380 ⟨243202, by decide⟩ :=
  accepted_of_selected 13 92380 ⟨243202, by decide⟩ ⟨13, 2, 0, 243202, 92380, 737, 16384⟩
    (by decide) selected_cut_08704

theorem selected_cut_08705 : selected 8 ⟨243246, by decide⟩
    (prefixPartial 13 92381) = some ⟨13, 2, 0, 243246, 92381, 2893, 16384⟩ := by
  decide +kernel

theorem context_13_92381_243246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92381 ⟨243246, by decide⟩ :=
  accepted_of_selected 13 92381 ⟨243246, by decide⟩ ⟨13, 2, 0, 243246, 92381, 2893, 16384⟩
    (by decide) selected_cut_08705

theorem selected_cut_08706 : selected 8 ⟨243269, by decide⟩
    (prefixPartial 13 92382) = some ⟨13, 2, 0, 243269, 92382, 1653, 16384⟩ := by
  decide +kernel

theorem context_13_92382_243269 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92382 ⟨243269, by decide⟩ :=
  accepted_of_selected 13 92382 ⟨243269, by decide⟩ ⟨13, 2, 0, 243269, 92382, 1653, 16384⟩
    (by decide) selected_cut_08706

theorem selected_cut_08707 : selected 8 ⟨243277, by decide⟩
    (prefixPartial 13 92383) = some ⟨13, 2, 0, 243277, 92383, 1021, 16384⟩ := by
  decide +kernel

theorem context_13_92383_243277 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92383 ⟨243277, by decide⟩ :=
  accepted_of_selected 13 92383 ⟨243277, by decide⟩ ⟨13, 2, 0, 243277, 92383, 1021, 16384⟩
    (by decide) selected_cut_08707

theorem unmarked_context_12_23095_243278 : frontier 9 ⟨243278, by decide⟩
    (prefixCache 12 23095) (prefixPartial 12 23095) = false := by
  decide +kernel

theorem node_context_12_23095_243278 : EJMOriginalGlobalDAGData.nodes 9 ⟨243278, by decide⟩ =
    .split (coordinate 12) (![⟨243202, by decide⟩,⟨243246, by decide⟩,⟨243269, by decide⟩,⟨243277, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23095_243278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23095 ⟨243278, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23095
    ⟨243278, by decide⟩ (by decide) (![⟨243202, by decide⟩,⟨243246, by decide⟩,⟨243269, by decide⟩,⟨243277, by decide⟩]) unmarked_context_12_23095_243278 node_context_12_23095_243278
  intro a
  fin_cases a
  · exact context_13_92380_243202
  · exact context_13_92381_243246
  · exact context_13_92382_243269
  · exact context_13_92383_243277

theorem unmarked_context_11_5773_243279 : frontier 10 ⟨243279, by decide⟩
    (prefixCache 11 5773) (prefixPartial 11 5773) = false := by
  decide +kernel

theorem node_context_11_5773_243279 : EJMOriginalGlobalDAGData.nodes 10 ⟨243279, by decide⟩ =
    .split (coordinate 11) (![⟨243043, by decide⟩,⟨243112, by decide⟩,⟨243188, by decide⟩,⟨243278, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5773_243279 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5773 ⟨243279, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5773
    ⟨243279, by decide⟩ (by decide) (![⟨243043, by decide⟩,⟨243112, by decide⟩,⟨243188, by decide⟩,⟨243278, by decide⟩]) unmarked_context_11_5773_243279 node_context_11_5773_243279
  intro a
  fin_cases a
  · exact context_12_23092_243043
  · exact context_12_23093_243112
  · exact context_12_23094_243188
  · exact context_12_23095_243278

theorem selected_cut_08708 : selected 8 ⟨243285, by decide⟩
    (prefixPartial 13 92384) = some ⟨13, 2, 0, 243285, 92384, 377, 16384⟩ := by
  decide +kernel

theorem context_13_92384_243285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92384 ⟨243285, by decide⟩ :=
  accepted_of_selected 13 92384 ⟨243285, by decide⟩ ⟨13, 2, 0, 243285, 92384, 377, 16384⟩
    (by decide) selected_cut_08708

theorem selected_cut_08709 : selected 8 ⟨243316, by decide⟩
    (prefixPartial 13 92385) = some ⟨13, 2, 0, 243316, 92385, 2717, 16384⟩ := by
  decide +kernel

theorem context_13_92385_243316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92385 ⟨243316, by decide⟩ :=
  accepted_of_selected 13 92385 ⟨243316, by decide⟩ ⟨13, 2, 0, 243316, 92385, 2717, 16384⟩
    (by decide) selected_cut_08709

theorem selected_cut_08710 : selected 8 ⟨243334, by decide⟩
    (prefixPartial 13 92386) = some ⟨13, 2, 0, 243334, 92386, 1537, 16384⟩ := by
  decide +kernel

theorem context_13_92386_243334 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92386 ⟨243334, by decide⟩ :=
  accepted_of_selected 13 92386 ⟨243334, by decide⟩ ⟨13, 2, 0, 243334, 92386, 1537, 16384⟩
    (by decide) selected_cut_08710

theorem selected_cut_08711 : selected 8 ⟨243339, by decide⟩
    (prefixPartial 13 92387) = some ⟨13, 2, 0, 243339, 92387, 945, 16384⟩ := by
  decide +kernel

theorem context_13_92387_243339 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92387 ⟨243339, by decide⟩ :=
  accepted_of_selected 13 92387 ⟨243339, by decide⟩ ⟨13, 2, 0, 243339, 92387, 945, 16384⟩
    (by decide) selected_cut_08711

theorem unmarked_context_12_23096_243340 : frontier 9 ⟨243340, by decide⟩
    (prefixCache 12 23096) (prefixPartial 12 23096) = false := by
  decide +kernel

theorem node_context_12_23096_243340 : EJMOriginalGlobalDAGData.nodes 9 ⟨243340, by decide⟩ =
    .split (coordinate 12) (![⟨243285, by decide⟩,⟨243316, by decide⟩,⟨243334, by decide⟩,⟨243339, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23096_243340 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23096 ⟨243340, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23096
    ⟨243340, by decide⟩ (by decide) (![⟨243285, by decide⟩,⟨243316, by decide⟩,⟨243334, by decide⟩,⟨243339, by decide⟩]) unmarked_context_12_23096_243340 node_context_12_23096_243340
  intro a
  fin_cases a
  · exact context_13_92384_243285
  · exact context_13_92385_243316
  · exact context_13_92386_243334
  · exact context_13_92387_243339

theorem selected_cut_08712 : selected 8 ⟨243346, by decide⟩
    (prefixPartial 13 92388) = some ⟨13, 2, 0, 243346, 92388, 417, 16384⟩ := by
  decide +kernel

theorem context_13_92388_243346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92388 ⟨243346, by decide⟩ :=
  accepted_of_selected 13 92388 ⟨243346, by decide⟩ ⟨13, 2, 0, 243346, 92388, 417, 16384⟩
    (by decide) selected_cut_08712

theorem selected_cut_08713 : selected 8 ⟨243373, by decide⟩
    (prefixPartial 13 92389) = some ⟨13, 2, 0, 243373, 92389, 2293, 16384⟩ := by
  decide +kernel

theorem context_13_92389_243373 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92389 ⟨243373, by decide⟩ :=
  accepted_of_selected 13 92389 ⟨243373, by decide⟩ ⟨13, 2, 0, 243373, 92389, 2293, 16384⟩
    (by decide) selected_cut_08713

theorem selected_cut_08714 : selected 8 ⟨243393, by decide⟩
    (prefixPartial 13 92390) = some ⟨13, 2, 0, 243393, 92390, 1569, 16384⟩ := by
  decide +kernel

theorem context_13_92390_243393 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92390 ⟨243393, by decide⟩ :=
  accepted_of_selected 13 92390 ⟨243393, by decide⟩ ⟨13, 2, 0, 243393, 92390, 1569, 16384⟩
    (by decide) selected_cut_08714

theorem selected_cut_08715 : selected 8 ⟨243397, by decide⟩
    (prefixPartial 13 92391) = some ⟨13, 2, 0, 243397, 92391, 957, 16384⟩ := by
  decide +kernel

theorem context_13_92391_243397 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92391 ⟨243397, by decide⟩ :=
  accepted_of_selected 13 92391 ⟨243397, by decide⟩ ⟨13, 2, 0, 243397, 92391, 957, 16384⟩
    (by decide) selected_cut_08715

theorem unmarked_context_12_23097_243398 : frontier 9 ⟨243398, by decide⟩
    (prefixCache 12 23097) (prefixPartial 12 23097) = false := by
  decide +kernel

theorem node_context_12_23097_243398 : EJMOriginalGlobalDAGData.nodes 9 ⟨243398, by decide⟩ =
    .split (coordinate 12) (![⟨243346, by decide⟩,⟨243373, by decide⟩,⟨243393, by decide⟩,⟨243397, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23097_243398 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23097 ⟨243398, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23097
    ⟨243398, by decide⟩ (by decide) (![⟨243346, by decide⟩,⟨243373, by decide⟩,⟨243393, by decide⟩,⟨243397, by decide⟩]) unmarked_context_12_23097_243398 node_context_12_23097_243398
  intro a
  fin_cases a
  · exact context_13_92388_243346
  · exact context_13_92389_243373
  · exact context_13_92390_243393
  · exact context_13_92391_243397

theorem selected_cut_08716 : selected 8 ⟨243411, by decide⟩
    (prefixPartial 13 92392) = some ⟨13, 2, 0, 243411, 92392, 525, 16384⟩ := by
  decide +kernel

theorem context_13_92392_243411 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92392 ⟨243411, by decide⟩ :=
  accepted_of_selected 13 92392 ⟨243411, by decide⟩ ⟨13, 2, 0, 243411, 92392, 525, 16384⟩
    (by decide) selected_cut_08716

theorem selected_cut_08717 : selected 7 ⟨243435, by decide⟩
    (prefixPartial 14 369572) = some ⟨14, 2, 0, 243435, 369572, 1245, 4096⟩ := by
  decide +kernel

theorem context_14_369572_243435 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 369572 ⟨243435, by decide⟩ :=
  accepted_of_selected 14 369572 ⟨243435, by decide⟩ ⟨14, 2, 0, 243435, 369572, 1245, 4096⟩
    (by decide) selected_cut_08717

theorem selected_cut_08718 : selected 7 ⟨243467, by decide⟩
    (prefixPartial 14 369573) = some ⟨14, 2, 0, 243467, 369573, 1349, 4096⟩ := by
  decide +kernel

theorem context_14_369573_243467 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 369573 ⟨243467, by decide⟩ :=
  accepted_of_selected 14 369573 ⟨243467, by decide⟩ ⟨14, 2, 0, 243467, 369573, 1349, 4096⟩
    (by decide) selected_cut_08718

theorem selected_cut_08719 : selected 7 ⟨243484, by decide⟩
    (prefixPartial 14 369574) = some ⟨14, 2, 0, 243484, 369574, 1037, 4096⟩ := by
  decide +kernel

theorem context_14_369574_243484 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 369574 ⟨243484, by decide⟩ :=
  accepted_of_selected 14 369574 ⟨243484, by decide⟩ ⟨14, 2, 0, 243484, 369574, 1037, 4096⟩
    (by decide) selected_cut_08719

theorem selected_cut_08720 : selected 7 ⟨243500, by decide⟩
    (prefixPartial 14 369575) = some ⟨14, 2, 0, 243500, 369575, 1093, 4096⟩ := by
  decide +kernel

theorem context_14_369575_243500 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 369575 ⟨243500, by decide⟩ :=
  accepted_of_selected 14 369575 ⟨243500, by decide⟩ ⟨14, 2, 0, 243500, 369575, 1093, 4096⟩
    (by decide) selected_cut_08720

theorem unmarked_context_13_92393_243501 : frontier 8 ⟨243501, by decide⟩
    (prefixCache 13 92393) (prefixPartial 13 92393) = false := by
  decide +kernel

theorem node_context_13_92393_243501 : EJMOriginalGlobalDAGData.nodes 8 ⟨243501, by decide⟩ =
    .split (coordinate 13) (![⟨243435, by decide⟩,⟨243467, by decide⟩,⟨243484, by decide⟩,⟨243500, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_92393_243501 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92393 ⟨243501, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 92393
    ⟨243501, by decide⟩ (by decide) (![⟨243435, by decide⟩,⟨243467, by decide⟩,⟨243484, by decide⟩,⟨243500, by decide⟩]) unmarked_context_13_92393_243501 node_context_13_92393_243501
  intro a
  fin_cases a
  · exact context_14_369572_243435
  · exact context_14_369573_243467
  · exact context_14_369574_243484
  · exact context_14_369575_243500

theorem selected_cut_08721 : selected 8 ⟨243570, by decide⟩
    (prefixPartial 13 92394) = some ⟨13, 2, 0, 243570, 92394, 3053, 16384⟩ := by
  decide +kernel

theorem context_13_92394_243570 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92394 ⟨243570, by decide⟩ :=
  accepted_of_selected 13 92394 ⟨243570, by decide⟩ ⟨13, 2, 0, 243570, 92394, 3053, 16384⟩
    (by decide) selected_cut_08721

theorem selected_cut_08722 : selected 8 ⟨243592, by decide⟩
    (prefixPartial 13 92395) = some ⟨13, 2, 0, 243592, 92395, 1321, 16384⟩ := by
  decide +kernel

theorem context_13_92395_243592 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92395 ⟨243592, by decide⟩ :=
  accepted_of_selected 13 92395 ⟨243592, by decide⟩ ⟨13, 2, 0, 243592, 92395, 1321, 16384⟩
    (by decide) selected_cut_08722

theorem unmarked_context_12_23098_243593 : frontier 9 ⟨243593, by decide⟩
    (prefixCache 12 23098) (prefixPartial 12 23098) = false := by
  decide +kernel

theorem node_context_12_23098_243593 : EJMOriginalGlobalDAGData.nodes 9 ⟨243593, by decide⟩ =
    .split (coordinate 12) (![⟨243411, by decide⟩,⟨243501, by decide⟩,⟨243570, by decide⟩,⟨243592, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23098_243593 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23098 ⟨243593, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23098
    ⟨243593, by decide⟩ (by decide) (![⟨243411, by decide⟩,⟨243501, by decide⟩,⟨243570, by decide⟩,⟨243592, by decide⟩]) unmarked_context_12_23098_243593 node_context_12_23098_243593
  intro a
  fin_cases a
  · exact context_13_92392_243411
  · exact context_13_92393_243501
  · exact context_13_92394_243570
  · exact context_13_92395_243592

theorem selected_cut_08723 : selected 8 ⟨243600, by decide⟩
    (prefixPartial 13 92396) = some ⟨13, 2, 0, 243600, 92396, 325, 16384⟩ := by
  decide +kernel

theorem context_13_92396_243600 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92396 ⟨243600, by decide⟩ :=
  accepted_of_selected 13 92396 ⟨243600, by decide⟩ ⟨13, 2, 0, 243600, 92396, 325, 16384⟩
    (by decide) selected_cut_08723

theorem selected_cut_08724 : selected 8 ⟨243646, by decide⟩
    (prefixPartial 13 92397) = some ⟨13, 2, 0, 243646, 92397, 3105, 16384⟩ := by
  decide +kernel

theorem context_13_92397_243646 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92397 ⟨243646, by decide⟩ :=
  accepted_of_selected 13 92397 ⟨243646, by decide⟩ ⟨13, 2, 0, 243646, 92397, 3105, 16384⟩
    (by decide) selected_cut_08724

theorem selected_cut_08725 : selected 8 ⟨243671, by decide⟩
    (prefixPartial 13 92398) = some ⟨13, 2, 0, 243671, 92398, 1813, 16384⟩ := by
  decide +kernel

theorem context_13_92398_243671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92398 ⟨243671, by decide⟩ :=
  accepted_of_selected 13 92398 ⟨243671, by decide⟩ ⟨13, 2, 0, 243671, 92398, 1813, 16384⟩
    (by decide) selected_cut_08725

theorem selected_cut_08726 : selected 8 ⟨243679, by decide⟩
    (prefixPartial 13 92399) = some ⟨13, 2, 0, 243679, 92399, 985, 16384⟩ := by
  decide +kernel

theorem context_13_92399_243679 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92399 ⟨243679, by decide⟩ :=
  accepted_of_selected 13 92399 ⟨243679, by decide⟩ ⟨13, 2, 0, 243679, 92399, 985, 16384⟩
    (by decide) selected_cut_08726

theorem unmarked_context_12_23099_243680 : frontier 9 ⟨243680, by decide⟩
    (prefixCache 12 23099) (prefixPartial 12 23099) = false := by
  decide +kernel

theorem node_context_12_23099_243680 : EJMOriginalGlobalDAGData.nodes 9 ⟨243680, by decide⟩ =
    .split (coordinate 12) (![⟨243600, by decide⟩,⟨243646, by decide⟩,⟨243671, by decide⟩,⟨243679, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23099_243680 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23099 ⟨243680, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23099
    ⟨243680, by decide⟩ (by decide) (![⟨243600, by decide⟩,⟨243646, by decide⟩,⟨243671, by decide⟩,⟨243679, by decide⟩]) unmarked_context_12_23099_243680 node_context_12_23099_243680
  intro a
  fin_cases a
  · exact context_13_92396_243600
  · exact context_13_92397_243646
  · exact context_13_92398_243671
  · exact context_13_92399_243679

theorem unmarked_context_11_5774_243681 : frontier 10 ⟨243681, by decide⟩
    (prefixCache 11 5774) (prefixPartial 11 5774) = false := by
  decide +kernel

theorem node_context_11_5774_243681 : EJMOriginalGlobalDAGData.nodes 10 ⟨243681, by decide⟩ =
    .split (coordinate 11) (![⟨243340, by decide⟩,⟨243398, by decide⟩,⟨243593, by decide⟩,⟨243680, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5774_243681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5774 ⟨243681, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5774
    ⟨243681, by decide⟩ (by decide) (![⟨243340, by decide⟩,⟨243398, by decide⟩,⟨243593, by decide⟩,⟨243680, by decide⟩]) unmarked_context_11_5774_243681 node_context_11_5774_243681
  intro a
  fin_cases a
  · exact context_12_23096_243340
  · exact context_12_23097_243398
  · exact context_12_23098_243593
  · exact context_12_23099_243680

theorem selected_cut_08727 : selected 8 ⟨243684, by decide⟩
    (prefixPartial 13 92400) = some ⟨13, 2, 0, 243684, 92400, 145, 16384⟩ := by
  decide +kernel

theorem context_13_92400_243684 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92400 ⟨243684, by decide⟩ :=
  accepted_of_selected 13 92400 ⟨243684, by decide⟩ ⟨13, 2, 0, 243684, 92400, 145, 16384⟩
    (by decide) selected_cut_08727

theorem selected_cut_08728 : selected 8 ⟨243728, by decide⟩
    (prefixPartial 13 92401) = some ⟨13, 2, 0, 243728, 92401, 2877, 16384⟩ := by
  decide +kernel

theorem context_13_92401_243728 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92401 ⟨243728, by decide⟩ :=
  accepted_of_selected 13 92401 ⟨243728, by decide⟩ ⟨13, 2, 0, 243728, 92401, 2877, 16384⟩
    (by decide) selected_cut_08728

theorem selected_cut_08729 : selected 8 ⟨243745, by decide⟩
    (prefixPartial 13 92402) = some ⟨13, 2, 0, 243745, 92402, 1437, 16384⟩ := by
  decide +kernel

theorem context_13_92402_243745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92402 ⟨243745, by decide⟩ :=
  accepted_of_selected 13 92402 ⟨243745, by decide⟩ ⟨13, 2, 0, 243745, 92402, 1437, 16384⟩
    (by decide) selected_cut_08729

theorem selected_cut_08730 : selected 8 ⟨243752, by decide⟩
    (prefixPartial 13 92403) = some ⟨13, 2, 0, 243752, 92403, 901, 16384⟩ := by
  decide +kernel

theorem context_13_92403_243752 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92403 ⟨243752, by decide⟩ :=
  accepted_of_selected 13 92403 ⟨243752, by decide⟩ ⟨13, 2, 0, 243752, 92403, 901, 16384⟩
    (by decide) selected_cut_08730

theorem unmarked_context_12_23100_243753 : frontier 9 ⟨243753, by decide⟩
    (prefixCache 12 23100) (prefixPartial 12 23100) = false := by
  decide +kernel

theorem node_context_12_23100_243753 : EJMOriginalGlobalDAGData.nodes 9 ⟨243753, by decide⟩ =
    .split (coordinate 12) (![⟨243684, by decide⟩,⟨243728, by decide⟩,⟨243745, by decide⟩,⟨243752, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23100_243753 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23100 ⟨243753, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23100
    ⟨243753, by decide⟩ (by decide) (![⟨243684, by decide⟩,⟨243728, by decide⟩,⟨243745, by decide⟩,⟨243752, by decide⟩]) unmarked_context_12_23100_243753 node_context_12_23100_243753
  intro a
  fin_cases a
  · exact context_13_92400_243684
  · exact context_13_92401_243728
  · exact context_13_92402_243745
  · exact context_13_92403_243752

theorem selected_cut_08731 : selected 8 ⟨243756, by decide⟩
    (prefixPartial 13 92404) = some ⟨13, 2, 0, 243756, 92404, 137, 16384⟩ := by
  decide +kernel

theorem context_13_92404_243756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92404 ⟨243756, by decide⟩ :=
  accepted_of_selected 13 92404 ⟨243756, by decide⟩ ⟨13, 2, 0, 243756, 92404, 137, 16384⟩
    (by decide) selected_cut_08731

theorem selected_cut_08732 : selected 8 ⟨243790, by decide⟩
    (prefixPartial 13 92405) = some ⟨13, 2, 0, 243790, 92405, 2473, 16384⟩ := by
  decide +kernel

theorem context_13_92405_243790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92405 ⟨243790, by decide⟩ :=
  accepted_of_selected 13 92405 ⟨243790, by decide⟩ ⟨13, 2, 0, 243790, 92405, 2473, 16384⟩
    (by decide) selected_cut_08732

theorem selected_cut_08733 : selected 8 ⟨243813, by decide⟩
    (prefixPartial 13 92406) = some ⟨13, 2, 0, 243813, 92406, 1449, 16384⟩ := by
  decide +kernel

theorem context_13_92406_243813 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92406 ⟨243813, by decide⟩ :=
  accepted_of_selected 13 92406 ⟨243813, by decide⟩ ⟨13, 2, 0, 243813, 92406, 1449, 16384⟩
    (by decide) selected_cut_08733

theorem selected_cut_08734 : selected 8 ⟨243823, by decide⟩
    (prefixPartial 13 92407) = some ⟨13, 2, 0, 243823, 92407, 837, 16384⟩ := by
  decide +kernel

theorem context_13_92407_243823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92407 ⟨243823, by decide⟩ :=
  accepted_of_selected 13 92407 ⟨243823, by decide⟩ ⟨13, 2, 0, 243823, 92407, 837, 16384⟩
    (by decide) selected_cut_08734

theorem unmarked_context_12_23101_243824 : frontier 9 ⟨243824, by decide⟩
    (prefixCache 12 23101) (prefixPartial 12 23101) = false := by
  decide +kernel

theorem node_context_12_23101_243824 : EJMOriginalGlobalDAGData.nodes 9 ⟨243824, by decide⟩ =
    .split (coordinate 12) (![⟨243756, by decide⟩,⟨243790, by decide⟩,⟨243813, by decide⟩,⟨243823, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23101_243824 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23101 ⟨243824, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23101
    ⟨243824, by decide⟩ (by decide) (![⟨243756, by decide⟩,⟨243790, by decide⟩,⟨243813, by decide⟩,⟨243823, by decide⟩]) unmarked_context_12_23101_243824 node_context_12_23101_243824
  intro a
  fin_cases a
  · exact context_13_92404_243756
  · exact context_13_92405_243790
  · exact context_13_92406_243813
  · exact context_13_92407_243823

theorem selected_cut_08735 : selected 8 ⟨243827, by decide⟩
    (prefixPartial 13 92408) = some ⟨13, 2, 0, 243827, 92408, 85, 16384⟩ := by
  decide +kernel

theorem context_13_92408_243827 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92408 ⟨243827, by decide⟩ :=
  accepted_of_selected 13 92408 ⟨243827, by decide⟩ ⟨13, 2, 0, 243827, 92408, 85, 16384⟩
    (by decide) selected_cut_08735

theorem selected_cut_08736 : selected 8 ⟨243876, by decide⟩
    (prefixPartial 13 92409) = some ⟨13, 2, 0, 243876, 92409, 2961, 16384⟩ := by
  decide +kernel

theorem context_13_92409_243876 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92409 ⟨243876, by decide⟩ :=
  accepted_of_selected 13 92409 ⟨243876, by decide⟩ ⟨13, 2, 0, 243876, 92409, 2961, 16384⟩
    (by decide) selected_cut_08736

theorem selected_cut_08737 : selected 8 ⟨243899, by decide⟩
    (prefixPartial 13 92410) = some ⟨13, 2, 0, 243899, 92410, 1597, 16384⟩ := by
  decide +kernel

theorem context_13_92410_243899 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92410 ⟨243899, by decide⟩ :=
  accepted_of_selected 13 92410 ⟨243899, by decide⟩ ⟨13, 2, 0, 243899, 92410, 1597, 16384⟩
    (by decide) selected_cut_08737

theorem selected_cut_08738 : selected 8 ⟨243906, by decide⟩
    (prefixPartial 13 92411) = some ⟨13, 2, 0, 243906, 92411, 781, 16384⟩ := by
  decide +kernel

theorem context_13_92411_243906 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92411 ⟨243906, by decide⟩ :=
  accepted_of_selected 13 92411 ⟨243906, by decide⟩ ⟨13, 2, 0, 243906, 92411, 781, 16384⟩
    (by decide) selected_cut_08738

theorem unmarked_context_12_23102_243907 : frontier 9 ⟨243907, by decide⟩
    (prefixCache 12 23102) (prefixPartial 12 23102) = false := by
  decide +kernel

theorem node_context_12_23102_243907 : EJMOriginalGlobalDAGData.nodes 9 ⟨243907, by decide⟩ =
    .split (coordinate 12) (![⟨243827, by decide⟩,⟨243876, by decide⟩,⟨243899, by decide⟩,⟨243906, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23102_243907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23102 ⟨243907, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23102
    ⟨243907, by decide⟩ (by decide) (![⟨243827, by decide⟩,⟨243876, by decide⟩,⟨243899, by decide⟩,⟨243906, by decide⟩]) unmarked_context_12_23102_243907 node_context_12_23102_243907
  intro a
  fin_cases a
  · exact context_13_92408_243827
  · exact context_13_92409_243876
  · exact context_13_92410_243899
  · exact context_13_92411_243906

theorem selected_cut_08739 : selected 8 ⟨243912, by decide⟩
    (prefixPartial 13 92412) = some ⟨13, 2, 0, 243912, 92412, 81, 16384⟩ := by
  decide +kernel

theorem context_13_92412_243912 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92412 ⟨243912, by decide⟩ :=
  accepted_of_selected 13 92412 ⟨243912, by decide⟩ ⟨13, 2, 0, 243912, 92412, 81, 16384⟩
    (by decide) selected_cut_08739

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
