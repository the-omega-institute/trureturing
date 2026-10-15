/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover521
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_10_26451_1427501 : frontier 11 ⟨1427501, by decide⟩
    (prefixCache 10 26451) (prefixPartial 10 26451) = false := by
  decide +kernel

theorem node_context_10_26451_1427501 : EJMOriginalGlobalDAGData.nodes 11 ⟨1427501, by decide⟩ =
    .split (coordinate 10) (![⟨1427186, by decide⟩,⟨1427279, by decide⟩,⟨1427463, by decide⟩,⟨1427500, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26451_1427501 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26451 ⟨1427501, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26451
    ⟨1427501, by decide⟩ (by decide) (![⟨1427186, by decide⟩,⟨1427279, by decide⟩,⟨1427463, by decide⟩,⟨1427500, by decide⟩]) unmarked_context_10_26451_1427501 node_context_10_26451_1427501
  intro a
  fin_cases a
  · exact context_11_105804_1427186
  · exact context_11_105805_1427279
  · exact context_11_105806_1427463
  · exact context_11_105807_1427500

theorem unmarked_context_9_6612_1427502 : frontier 12 ⟨1427502, by decide⟩
    (prefixCache 9 6612) (prefixPartial 9 6612) = false := by
  decide +kernel

theorem node_context_9_6612_1427502 : EJMOriginalGlobalDAGData.nodes 12 ⟨1427502, by decide⟩ =
    .split (coordinate 9) (![⟨1425895, by decide⟩,⟨1426269, by decide⟩,⟨1427018, by decide⟩,⟨1427501, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6612_1427502 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6612 ⟨1427502, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6612
    ⟨1427502, by decide⟩ (by decide) (![⟨1425895, by decide⟩,⟨1426269, by decide⟩,⟨1427018, by decide⟩,⟨1427501, by decide⟩]) unmarked_context_9_6612_1427502 node_context_9_6612_1427502
  intro a
  fin_cases a
  · exact context_10_26448_1425895
  · exact context_10_26449_1426269
  · exact context_10_26450_1427018
  · exact context_10_26451_1427501

theorem selected_cut_50116 : selected 11 ⟨793297, by decide⟩
    (prefixPartial 10 26452) = some ⟨10, 1, 0, 793297, 26452, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_26452_793297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26452 ⟨793297, by decide⟩ :=
  accepted_of_selected 10 26452 ⟨793297, by decide⟩ ⟨10, 1, 0, 793297, 26452, 1, 1048576⟩
    (by decide) selected_cut_50116

theorem selected_cut_50117 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 26453) = some ⟨10, 1, 0, 893098, 26453, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_26453_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26453 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 26453 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 26453, 1, 1048576⟩
    (by decide) selected_cut_50117

theorem selected_cut_50118 : selected 10 ⟨1427573, by decide⟩
    (prefixPartial 11 105816) = some ⟨11, 2, 0, 1427573, 105816, 1593, 262144⟩ := by
  decide +kernel

theorem context_11_105816_1427573 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105816 ⟨1427573, by decide⟩ :=
  accepted_of_selected 11 105816 ⟨1427573, by decide⟩ ⟨11, 2, 0, 1427573, 105816, 1593, 262144⟩
    (by decide) selected_cut_50118

theorem selected_cut_50119 : selected 10 ⟨1427641, by decide⟩
    (prefixPartial 11 105817) = some ⟨11, 2, 0, 1427641, 105817, 1749, 262144⟩ := by
  decide +kernel

theorem context_11_105817_1427641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105817 ⟨1427641, by decide⟩ :=
  accepted_of_selected 11 105817 ⟨1427641, by decide⟩ ⟨11, 2, 0, 1427641, 105817, 1749, 262144⟩
    (by decide) selected_cut_50119

theorem selected_cut_50120 : selected 10 ⟨1369759, by decide⟩
    (prefixPartial 11 105818) = some ⟨11, 1, 0, 1369759, 105818, 1, 262144⟩ := by
  decide +kernel

theorem context_11_105818_1369759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105818 ⟨1369759, by decide⟩ :=
  accepted_of_selected 11 105818 ⟨1369759, by decide⟩ ⟨11, 1, 0, 1369759, 105818, 1, 262144⟩
    (by decide) selected_cut_50120

theorem selected_cut_50121 : selected 10 ⟨1427689, by decide⟩
    (prefixPartial 11 105819) = some ⟨11, 2, 0, 1427689, 105819, 1289, 262144⟩ := by
  decide +kernel

theorem context_11_105819_1427689 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105819 ⟨1427689, by decide⟩ :=
  accepted_of_selected 11 105819 ⟨1427689, by decide⟩ ⟨11, 2, 0, 1427689, 105819, 1289, 262144⟩
    (by decide) selected_cut_50121

theorem unmarked_context_10_26454_1427690 : frontier 11 ⟨1427690, by decide⟩
    (prefixCache 10 26454) (prefixPartial 10 26454) = false := by
  decide +kernel

theorem node_context_10_26454_1427690 : EJMOriginalGlobalDAGData.nodes 11 ⟨1427690, by decide⟩ =
    .split (coordinate 10) (![⟨1427573, by decide⟩,⟨1427641, by decide⟩,⟨1369759, by decide⟩,⟨1427689, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26454_1427690 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26454 ⟨1427690, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26454
    ⟨1427690, by decide⟩ (by decide) (![⟨1427573, by decide⟩,⟨1427641, by decide⟩,⟨1369759, by decide⟩,⟨1427689, by decide⟩]) unmarked_context_10_26454_1427690 node_context_10_26454_1427690
  intro a
  fin_cases a
  · exact context_11_105816_1427573
  · exact context_11_105817_1427641
  · exact context_11_105818_1369759
  · exact context_11_105819_1427689

theorem selected_cut_50122 : selected 11 ⟨1427817, by decide⟩
    (prefixPartial 10 26455) = some ⟨10, 2, 0, 1427817, 26455, 2793, 1048576⟩ := by
  decide +kernel

theorem context_10_26455_1427817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26455 ⟨1427817, by decide⟩ :=
  accepted_of_selected 10 26455 ⟨1427817, by decide⟩ ⟨10, 2, 0, 1427817, 26455, 2793, 1048576⟩
    (by decide) selected_cut_50122

theorem unmarked_context_9_6613_1427818 : frontier 12 ⟨1427818, by decide⟩
    (prefixCache 9 6613) (prefixPartial 9 6613) = false := by
  decide +kernel

theorem node_context_9_6613_1427818 : EJMOriginalGlobalDAGData.nodes 12 ⟨1427818, by decide⟩ =
    .split (coordinate 9) (![⟨793297, by decide⟩,⟨893098, by decide⟩,⟨1427690, by decide⟩,⟨1427817, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6613_1427818 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6613 ⟨1427818, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6613
    ⟨1427818, by decide⟩ (by decide) (![⟨793297, by decide⟩,⟨893098, by decide⟩,⟨1427690, by decide⟩,⟨1427817, by decide⟩]) unmarked_context_9_6613_1427818 node_context_9_6613_1427818
  intro a
  fin_cases a
  · exact context_10_26452_793297
  · exact context_10_26453_893098
  · exact context_10_26454_1427690
  · exact context_10_26455_1427817

theorem selected_cut_50123 : selected 12 ⟨1427879, by decide⟩
    (prefixPartial 9 6614) = some ⟨9, 2, 0, 1427879, 6614, 777, 4194304⟩ := by
  decide +kernel

theorem context_9_6614_1427879 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6614 ⟨1427879, by decide⟩ :=
  accepted_of_selected 9 6614 ⟨1427879, by decide⟩ ⟨9, 2, 0, 1427879, 6614, 777, 4194304⟩
    (by decide) selected_cut_50123

theorem selected_cut_50124 : selected 12 ⟨1427906, by decide⟩
    (prefixPartial 9 6615) = some ⟨9, 2, 0, 1427906, 6615, 341, 4194304⟩ := by
  decide +kernel

theorem context_9_6615_1427906 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6615 ⟨1427906, by decide⟩ :=
  accepted_of_selected 9 6615 ⟨1427906, by decide⟩ ⟨9, 2, 0, 1427906, 6615, 341, 4194304⟩
    (by decide) selected_cut_50124

theorem unmarked_context_8_1653_1427907 : frontier 13 ⟨1427907, by decide⟩
    (prefixCache 8 1653) (prefixPartial 8 1653) = false := by
  decide +kernel

theorem node_context_8_1653_1427907 : EJMOriginalGlobalDAGData.nodes 13 ⟨1427907, by decide⟩ =
    .split (coordinate 8) (![⟨1427502, by decide⟩,⟨1427818, by decide⟩,⟨1427879, by decide⟩,⟨1427906, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1653_1427907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1653 ⟨1427907, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1653
    ⟨1427907, by decide⟩ (by decide) (![⟨1427502, by decide⟩,⟨1427818, by decide⟩,⟨1427879, by decide⟩,⟨1427906, by decide⟩]) unmarked_context_8_1653_1427907 node_context_8_1653_1427907
  intro a
  fin_cases a
  · exact context_9_6612_1427502
  · exact context_9_6613_1427818
  · exact context_9_6614_1427879
  · exact context_9_6615_1427906

theorem selected_cut_50125 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 105856) = some ⟨11, 1, 0, 434745, 105856, 1, 262144⟩ := by
  decide +kernel

theorem context_11_105856_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105856 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 105856 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 105856, 1, 262144⟩
    (by decide) selected_cut_50125

theorem selected_cut_50126 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 105857) = some ⟨11, 1, 0, 434745, 105857, 1, 262144⟩ := by
  decide +kernel

theorem context_11_105857_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105857 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 105857 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 105857, 1, 262144⟩
    (by decide) selected_cut_50126

theorem selected_cut_50127 : selected 10 ⟨1427969, by decide⟩
    (prefixPartial 11 105858) = some ⟨11, 2, 0, 1427969, 105858, 1369, 262144⟩ := by
  decide +kernel

theorem context_11_105858_1427969 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105858 ⟨1427969, by decide⟩ :=
  accepted_of_selected 11 105858 ⟨1427969, by decide⟩ ⟨11, 2, 0, 1427969, 105858, 1369, 262144⟩
    (by decide) selected_cut_50127

theorem selected_cut_50128 : selected 10 ⟨1428095, by decide⟩
    (prefixPartial 11 105859) = some ⟨11, 2, 0, 1428095, 105859, 3309, 262144⟩ := by
  decide +kernel

theorem context_11_105859_1428095 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105859 ⟨1428095, by decide⟩ :=
  accepted_of_selected 11 105859 ⟨1428095, by decide⟩ ⟨11, 2, 0, 1428095, 105859, 3309, 262144⟩
    (by decide) selected_cut_50128

theorem unmarked_context_10_26464_1428096 : frontier 11 ⟨1428096, by decide⟩
    (prefixCache 10 26464) (prefixPartial 10 26464) = false := by
  decide +kernel

theorem node_context_10_26464_1428096 : EJMOriginalGlobalDAGData.nodes 11 ⟨1428096, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨434745, by decide⟩,⟨1427969, by decide⟩,⟨1428095, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26464_1428096 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26464 ⟨1428096, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26464
    ⟨1428096, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨434745, by decide⟩,⟨1427969, by decide⟩,⟨1428095, by decide⟩]) unmarked_context_10_26464_1428096 node_context_10_26464_1428096
  intro a
  fin_cases a
  · exact context_11_105856_434745
  · exact context_11_105857_434745
  · exact context_11_105858_1427969
  · exact context_11_105859_1428095

theorem selected_cut_50129 : selected 9 ⟨1415033, by decide⟩
    (prefixPartial 12 423440) = some ⟨12, 1, 0, 1415033, 423440, 1, 65536⟩ := by
  decide +kernel

theorem context_12_423440_1415033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 423440 ⟨1415033, by decide⟩ :=
  accepted_of_selected 12 423440 ⟨1415033, by decide⟩ ⟨12, 1, 0, 1415033, 423440, 1, 65536⟩
    (by decide) selected_cut_50129

theorem selected_cut_50130 : selected 9 ⟨1428141, by decide⟩
    (prefixPartial 12 423441) = some ⟨12, 2, 0, 1428141, 423441, 1761, 65536⟩ := by
  decide +kernel

theorem context_12_423441_1428141 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 423441 ⟨1428141, by decide⟩ :=
  accepted_of_selected 12 423441 ⟨1428141, by decide⟩ ⟨12, 2, 0, 1428141, 423441, 1761, 65536⟩
    (by decide) selected_cut_50130

theorem selected_cut_50131 : selected 9 ⟨1428200, by decide⟩
    (prefixPartial 12 423442) = some ⟨12, 2, 0, 1428200, 423442, 2361, 65536⟩ := by
  decide +kernel

theorem context_12_423442_1428200 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 423442 ⟨1428200, by decide⟩ :=
  accepted_of_selected 12 423442 ⟨1428200, by decide⟩ ⟨12, 2, 0, 1428200, 423442, 2361, 65536⟩
    (by decide) selected_cut_50131

theorem selected_cut_50132 : selected 9 ⟨1428249, by decide⟩
    (prefixPartial 12 423443) = some ⟨12, 2, 0, 1428249, 423443, 2153, 65536⟩ := by
  decide +kernel

theorem context_12_423443_1428249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 423443 ⟨1428249, by decide⟩ :=
  accepted_of_selected 12 423443 ⟨1428249, by decide⟩ ⟨12, 2, 0, 1428249, 423443, 2153, 65536⟩
    (by decide) selected_cut_50132

theorem unmarked_context_11_105860_1428250 : frontier 10 ⟨1428250, by decide⟩
    (prefixCache 11 105860) (prefixPartial 11 105860) = false := by
  decide +kernel

theorem node_context_11_105860_1428250 : EJMOriginalGlobalDAGData.nodes 10 ⟨1428250, by decide⟩ =
    .split (coordinate 11) (![⟨1415033, by decide⟩,⟨1428141, by decide⟩,⟨1428200, by decide⟩,⟨1428249, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_105860_1428250 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105860 ⟨1428250, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 105860
    ⟨1428250, by decide⟩ (by decide) (![⟨1415033, by decide⟩,⟨1428141, by decide⟩,⟨1428200, by decide⟩,⟨1428249, by decide⟩]) unmarked_context_11_105860_1428250 node_context_11_105860_1428250
  intro a
  fin_cases a
  · exact context_12_423440_1415033
  · exact context_12_423441_1428141
  · exact context_12_423442_1428200
  · exact context_12_423443_1428249

theorem selected_cut_50133 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 105861) = some ⟨11, 1, 0, 892405, 105861, 1, 262144⟩ := by
  decide +kernel

theorem context_11_105861_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105861 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 105861 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 105861, 1, 262144⟩
    (by decide) selected_cut_50133

theorem selected_cut_50134 : selected 10 ⟨1428328, by decide⟩
    (prefixPartial 11 105862) = some ⟨11, 2, 0, 1428328, 105862, 3581, 262144⟩ := by
  decide +kernel

theorem context_11_105862_1428328 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105862 ⟨1428328, by decide⟩ :=
  accepted_of_selected 11 105862 ⟨1428328, by decide⟩ ⟨11, 2, 0, 1428328, 105862, 3581, 262144⟩
    (by decide) selected_cut_50134

theorem selected_cut_50135 : selected 9 ⟨1415033, by decide⟩
    (prefixPartial 12 423452) = some ⟨12, 1, 0, 1415033, 423452, 1, 65536⟩ := by
  decide +kernel

theorem context_12_423452_1415033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 423452 ⟨1415033, by decide⟩ :=
  accepted_of_selected 12 423452 ⟨1415033, by decide⟩ ⟨12, 1, 0, 1415033, 423452, 1, 65536⟩
    (by decide) selected_cut_50135

theorem selected_cut_50136 : selected 9 ⟨1428374, by decide⟩
    (prefixPartial 12 423453) = some ⟨12, 2, 0, 1428374, 423453, 1857, 65536⟩ := by
  decide +kernel

theorem context_12_423453_1428374 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 423453 ⟨1428374, by decide⟩ :=
  accepted_of_selected 12 423453 ⟨1428374, by decide⟩ ⟨12, 2, 0, 1428374, 423453, 1857, 65536⟩
    (by decide) selected_cut_50136

theorem selected_cut_50137 : selected 9 ⟨1428432, by decide⟩
    (prefixPartial 12 423454) = some ⟨12, 2, 0, 1428432, 423454, 2493, 65536⟩ := by
  decide +kernel

theorem context_12_423454_1428432 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 423454 ⟨1428432, by decide⟩ :=
  accepted_of_selected 12 423454 ⟨1428432, by decide⟩ ⟨12, 2, 0, 1428432, 423454, 2493, 65536⟩
    (by decide) selected_cut_50137

theorem selected_cut_50138 : selected 9 ⟨1428482, by decide⟩
    (prefixPartial 12 423455) = some ⟨12, 2, 0, 1428482, 423455, 2053, 65536⟩ := by
  decide +kernel

theorem context_12_423455_1428482 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 423455 ⟨1428482, by decide⟩ :=
  accepted_of_selected 12 423455 ⟨1428482, by decide⟩ ⟨12, 2, 0, 1428482, 423455, 2053, 65536⟩
    (by decide) selected_cut_50138

theorem unmarked_context_11_105863_1428483 : frontier 10 ⟨1428483, by decide⟩
    (prefixCache 11 105863) (prefixPartial 11 105863) = false := by
  decide +kernel

theorem node_context_11_105863_1428483 : EJMOriginalGlobalDAGData.nodes 10 ⟨1428483, by decide⟩ =
    .split (coordinate 11) (![⟨1415033, by decide⟩,⟨1428374, by decide⟩,⟨1428432, by decide⟩,⟨1428482, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_105863_1428483 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105863 ⟨1428483, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 105863
    ⟨1428483, by decide⟩ (by decide) (![⟨1415033, by decide⟩,⟨1428374, by decide⟩,⟨1428432, by decide⟩,⟨1428482, by decide⟩]) unmarked_context_11_105863_1428483 node_context_11_105863_1428483
  intro a
  fin_cases a
  · exact context_12_423452_1415033
  · exact context_12_423453_1428374
  · exact context_12_423454_1428432
  · exact context_12_423455_1428482

theorem unmarked_context_10_26465_1428484 : frontier 11 ⟨1428484, by decide⟩
    (prefixCache 10 26465) (prefixPartial 10 26465) = false := by
  decide +kernel

theorem node_context_10_26465_1428484 : EJMOriginalGlobalDAGData.nodes 11 ⟨1428484, by decide⟩ =
    .split (coordinate 10) (![⟨1428250, by decide⟩,⟨892405, by decide⟩,⟨1428328, by decide⟩,⟨1428483, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26465_1428484 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26465 ⟨1428484, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26465
    ⟨1428484, by decide⟩ (by decide) (![⟨1428250, by decide⟩,⟨892405, by decide⟩,⟨1428328, by decide⟩,⟨1428483, by decide⟩]) unmarked_context_10_26465_1428484 node_context_10_26465_1428484
  intro a
  fin_cases a
  · exact context_11_105860_1428250
  · exact context_11_105861_892405
  · exact context_11_105862_1428328
  · exact context_11_105863_1428483

theorem selected_cut_50139 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 423456) = some ⟨12, 1, 0, 435160, 423456, 1, 65536⟩ := by
  decide +kernel

theorem context_12_423456_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 423456 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 423456 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 423456, 1, 65536⟩
    (by decide) selected_cut_50139

theorem selected_cut_50140 : selected 9 ⟨1428541, by decide⟩
    (prefixPartial 12 423457) = some ⟨12, 2, 0, 1428541, 423457, 2105, 65536⟩ := by
  decide +kernel

theorem context_12_423457_1428541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 423457 ⟨1428541, by decide⟩ :=
  accepted_of_selected 12 423457 ⟨1428541, by decide⟩ ⟨12, 2, 0, 1428541, 423457, 2105, 65536⟩
    (by decide) selected_cut_50140

theorem selected_cut_50141 : selected 9 ⟨1428595, by decide⟩
    (prefixPartial 12 423458) = some ⟨12, 2, 0, 1428595, 423458, 2569, 65536⟩ := by
  decide +kernel

theorem context_12_423458_1428595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 423458 ⟨1428595, by decide⟩ :=
  accepted_of_selected 12 423458 ⟨1428595, by decide⟩ ⟨12, 2, 0, 1428595, 423458, 2569, 65536⟩
    (by decide) selected_cut_50141

theorem selected_cut_50142 : selected 9 ⟨1428652, by decide⟩
    (prefixPartial 12 423459) = some ⟨12, 2, 0, 1428652, 423459, 2205, 65536⟩ := by
  decide +kernel

theorem context_12_423459_1428652 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 423459 ⟨1428652, by decide⟩ :=
  accepted_of_selected 12 423459 ⟨1428652, by decide⟩ ⟨12, 2, 0, 1428652, 423459, 2205, 65536⟩
    (by decide) selected_cut_50142

theorem unmarked_context_11_105864_1428653 : frontier 10 ⟨1428653, by decide⟩
    (prefixCache 11 105864) (prefixPartial 11 105864) = false := by
  decide +kernel

theorem node_context_11_105864_1428653 : EJMOriginalGlobalDAGData.nodes 10 ⟨1428653, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨1428541, by decide⟩,⟨1428595, by decide⟩,⟨1428652, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_105864_1428653 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105864 ⟨1428653, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 105864
    ⟨1428653, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨1428541, by decide⟩,⟨1428595, by decide⟩,⟨1428652, by decide⟩]) unmarked_context_11_105864_1428653 node_context_11_105864_1428653
  intro a
  fin_cases a
  · exact context_12_423456_435160
  · exact context_12_423457_1428541
  · exact context_12_423458_1428595
  · exact context_12_423459_1428652

theorem selected_cut_50143 : selected 10 ⟨1428738, by decide⟩
    (prefixPartial 11 105865) = some ⟨11, 2, 0, 1428738, 105865, 3681, 262144⟩ := by
  decide +kernel

theorem context_11_105865_1428738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105865 ⟨1428738, by decide⟩ :=
  accepted_of_selected 11 105865 ⟨1428738, by decide⟩ ⟨11, 2, 0, 1428738, 105865, 3681, 262144⟩
    (by decide) selected_cut_50143

theorem selected_cut_50144 : selected 10 ⟨1428739, by decide⟩
    (prefixPartial 11 105866) = some ⟨11, 2, 0, 1428739, 105866, 5, 262144⟩ := by
  decide +kernel

theorem context_11_105866_1428739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105866 ⟨1428739, by decide⟩ :=
  accepted_of_selected 11 105866 ⟨1428739, by decide⟩ ⟨11, 2, 0, 1428739, 105866, 5, 262144⟩
    (by decide) selected_cut_50144

theorem selected_cut_50145 : selected 9 ⟨1428804, by decide⟩
    (prefixPartial 12 423468) = some ⟨12, 2, 0, 1428804, 423468, 2185, 65536⟩ := by
  decide +kernel

theorem context_12_423468_1428804 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 423468 ⟨1428804, by decide⟩ :=
  accepted_of_selected 12 423468 ⟨1428804, by decide⟩ ⟨12, 2, 0, 1428804, 423468, 2185, 65536⟩
    (by decide) selected_cut_50145

theorem selected_cut_50146 : selected 9 ⟨1428860, by decide⟩
    (prefixPartial 12 423469) = some ⟨12, 2, 0, 1428860, 423469, 2017, 65536⟩ := by
  decide +kernel

theorem context_12_423469_1428860 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 423469 ⟨1428860, by decide⟩ :=
  accepted_of_selected 12 423469 ⟨1428860, by decide⟩ ⟨12, 2, 0, 1428860, 423469, 2017, 65536⟩
    (by decide) selected_cut_50146

theorem selected_cut_50147 : selected 9 ⟨1428913, by decide⟩
    (prefixPartial 12 423470) = some ⟨12, 2, 0, 1428913, 423470, 2381, 65536⟩ := by
  decide +kernel

theorem context_12_423470_1428913 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 423470 ⟨1428913, by decide⟩ :=
  accepted_of_selected 12 423470 ⟨1428913, by decide⟩ ⟨12, 2, 0, 1428913, 423470, 2381, 65536⟩
    (by decide) selected_cut_50147

theorem selected_cut_50148 : selected 9 ⟨1387722, by decide⟩
    (prefixPartial 12 423471) = some ⟨12, 1, 0, 1387722, 423471, 1, 65536⟩ := by
  decide +kernel

theorem context_12_423471_1387722 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 423471 ⟨1387722, by decide⟩ :=
  accepted_of_selected 12 423471 ⟨1387722, by decide⟩ ⟨12, 1, 0, 1387722, 423471, 1, 65536⟩
    (by decide) selected_cut_50148

theorem unmarked_context_11_105867_1428914 : frontier 10 ⟨1428914, by decide⟩
    (prefixCache 11 105867) (prefixPartial 11 105867) = false := by
  decide +kernel

theorem node_context_11_105867_1428914 : EJMOriginalGlobalDAGData.nodes 10 ⟨1428914, by decide⟩ =
    .split (coordinate 11) (![⟨1428804, by decide⟩,⟨1428860, by decide⟩,⟨1428913, by decide⟩,⟨1387722, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_105867_1428914 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105867 ⟨1428914, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 105867
    ⟨1428914, by decide⟩ (by decide) (![⟨1428804, by decide⟩,⟨1428860, by decide⟩,⟨1428913, by decide⟩,⟨1387722, by decide⟩]) unmarked_context_11_105867_1428914 node_context_11_105867_1428914
  intro a
  fin_cases a
  · exact context_12_423468_1428804
  · exact context_12_423469_1428860
  · exact context_12_423470_1428913
  · exact context_12_423471_1387722

theorem unmarked_context_10_26466_1428915 : frontier 11 ⟨1428915, by decide⟩
    (prefixCache 10 26466) (prefixPartial 10 26466) = false := by
  decide +kernel

theorem node_context_10_26466_1428915 : EJMOriginalGlobalDAGData.nodes 11 ⟨1428915, by decide⟩ =
    .split (coordinate 10) (![⟨1428653, by decide⟩,⟨1428738, by decide⟩,⟨1428739, by decide⟩,⟨1428914, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26466_1428915 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26466 ⟨1428915, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26466
    ⟨1428915, by decide⟩ (by decide) (![⟨1428653, by decide⟩,⟨1428738, by decide⟩,⟨1428739, by decide⟩,⟨1428914, by decide⟩]) unmarked_context_10_26466_1428915 node_context_10_26466_1428915
  intro a
  fin_cases a
  · exact context_11_105864_1428653
  · exact context_11_105865_1428738
  · exact context_11_105866_1428739
  · exact context_11_105867_1428914

theorem selected_cut_50149 : selected 9 ⟨1416143, by decide⟩
    (prefixPartial 12 423472) = some ⟨12, 1, 0, 1416143, 423472, 1, 65536⟩ := by
  decide +kernel

theorem context_12_423472_1416143 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 423472 ⟨1416143, by decide⟩ :=
  accepted_of_selected 12 423472 ⟨1416143, by decide⟩ ⟨12, 1, 0, 1416143, 423472, 1, 65536⟩
    (by decide) selected_cut_50149

theorem selected_cut_50150 : selected 9 ⟨1428950, by decide⟩
    (prefixPartial 12 423473) = some ⟨12, 2, 0, 1428950, 423473, 1529, 65536⟩ := by
  decide +kernel

theorem context_12_423473_1428950 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 423473 ⟨1428950, by decide⟩ :=
  accepted_of_selected 12 423473 ⟨1428950, by decide⟩ ⟨12, 2, 0, 1428950, 423473, 1529, 65536⟩
    (by decide) selected_cut_50150

theorem selected_cut_50151 : selected 9 ⟨1428989, by decide⟩
    (prefixPartial 12 423474) = some ⟨12, 2, 0, 1428989, 423474, 1853, 65536⟩ := by
  decide +kernel

theorem context_12_423474_1428989 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 423474 ⟨1428989, by decide⟩ :=
  accepted_of_selected 12 423474 ⟨1428989, by decide⟩ ⟨12, 2, 0, 1428989, 423474, 1853, 65536⟩
    (by decide) selected_cut_50151

theorem selected_cut_50152 : selected 9 ⟨1429034, by decide⟩
    (prefixPartial 12 423475) = some ⟨12, 2, 0, 1429034, 423475, 1677, 65536⟩ := by
  decide +kernel

theorem context_12_423475_1429034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 423475 ⟨1429034, by decide⟩ :=
  accepted_of_selected 12 423475 ⟨1429034, by decide⟩ ⟨12, 2, 0, 1429034, 423475, 1677, 65536⟩
    (by decide) selected_cut_50152

theorem unmarked_context_11_105868_1429035 : frontier 10 ⟨1429035, by decide⟩
    (prefixCache 11 105868) (prefixPartial 11 105868) = false := by
  decide +kernel

theorem node_context_11_105868_1429035 : EJMOriginalGlobalDAGData.nodes 10 ⟨1429035, by decide⟩ =
    .split (coordinate 11) (![⟨1416143, by decide⟩,⟨1428950, by decide⟩,⟨1428989, by decide⟩,⟨1429034, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_105868_1429035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105868 ⟨1429035, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 105868
    ⟨1429035, by decide⟩ (by decide) (![⟨1416143, by decide⟩,⟨1428950, by decide⟩,⟨1428989, by decide⟩,⟨1429034, by decide⟩]) unmarked_context_11_105868_1429035 node_context_11_105868_1429035
  intro a
  fin_cases a
  · exact context_12_423472_1416143
  · exact context_12_423473_1428950
  · exact context_12_423474_1428989
  · exact context_12_423475_1429034

theorem selected_cut_50153 : selected 10 ⟨1429089, by decide⟩
    (prefixPartial 11 105869) = some ⟨11, 2, 0, 1429089, 105869, 2889, 262144⟩ := by
  decide +kernel

theorem context_11_105869_1429089 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105869 ⟨1429089, by decide⟩ :=
  accepted_of_selected 11 105869 ⟨1429089, by decide⟩ ⟨11, 2, 0, 1429089, 105869, 2889, 262144⟩
    (by decide) selected_cut_50153

theorem selected_cut_50154 : selected 9 ⟨1429131, by decide⟩
    (prefixPartial 12 423480) = some ⟨12, 2, 0, 1429131, 423480, 1581, 65536⟩ := by
  decide +kernel

theorem context_12_423480_1429131 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 423480 ⟨1429131, by decide⟩ :=
  accepted_of_selected 12 423480 ⟨1429131, by decide⟩ ⟨12, 2, 0, 1429131, 423480, 1581, 65536⟩
    (by decide) selected_cut_50154

theorem selected_cut_50155 : selected 9 ⟨1429160, by decide⟩
    (prefixPartial 12 423481) = some ⟨12, 2, 0, 1429160, 423481, 1341, 65536⟩ := by
  decide +kernel

theorem context_12_423481_1429160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 423481 ⟨1429160, by decide⟩ :=
  accepted_of_selected 12 423481 ⟨1429160, by decide⟩ ⟨12, 2, 0, 1429160, 423481, 1341, 65536⟩
    (by decide) selected_cut_50155

theorem selected_cut_50156 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 423482) = some ⟨12, 1, 0, 893903, 423482, 1, 65536⟩ := by
  decide +kernel

theorem context_12_423482_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 423482 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 423482 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 423482, 1, 65536⟩
    (by decide) selected_cut_50156

theorem selected_cut_50157 : selected 9 ⟨1429190, by decide⟩
    (prefixPartial 12 423483) = some ⟨12, 2, 0, 1429190, 423483, 1497, 65536⟩ := by
  decide +kernel

theorem context_12_423483_1429190 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 423483 ⟨1429190, by decide⟩ :=
  accepted_of_selected 12 423483 ⟨1429190, by decide⟩ ⟨12, 2, 0, 1429190, 423483, 1497, 65536⟩
    (by decide) selected_cut_50157

theorem unmarked_context_11_105870_1429191 : frontier 10 ⟨1429191, by decide⟩
    (prefixCache 11 105870) (prefixPartial 11 105870) = false := by
  decide +kernel

theorem node_context_11_105870_1429191 : EJMOriginalGlobalDAGData.nodes 10 ⟨1429191, by decide⟩ =
    .split (coordinate 11) (![⟨1429131, by decide⟩,⟨1429160, by decide⟩,⟨893903, by decide⟩,⟨1429190, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_105870_1429191 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105870 ⟨1429191, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 105870
    ⟨1429191, by decide⟩ (by decide) (![⟨1429131, by decide⟩,⟨1429160, by decide⟩,⟨893903, by decide⟩,⟨1429190, by decide⟩]) unmarked_context_11_105870_1429191 node_context_11_105870_1429191
  intro a
  fin_cases a
  · exact context_12_423480_1429131
  · exact context_12_423481_1429160
  · exact context_12_423482_893903
  · exact context_12_423483_1429190

theorem selected_cut_50158 : selected 10 ⟨1429229, by decide⟩
    (prefixPartial 11 105871) = some ⟨11, 2, 0, 1429229, 105871, 1709, 262144⟩ := by
  decide +kernel

theorem context_11_105871_1429229 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105871 ⟨1429229, by decide⟩ :=
  accepted_of_selected 11 105871 ⟨1429229, by decide⟩ ⟨11, 2, 0, 1429229, 105871, 1709, 262144⟩
    (by decide) selected_cut_50158

theorem unmarked_context_10_26467_1429230 : frontier 11 ⟨1429230, by decide⟩
    (prefixCache 10 26467) (prefixPartial 10 26467) = false := by
  decide +kernel

theorem node_context_10_26467_1429230 : EJMOriginalGlobalDAGData.nodes 11 ⟨1429230, by decide⟩ =
    .split (coordinate 10) (![⟨1429035, by decide⟩,⟨1429089, by decide⟩,⟨1429191, by decide⟩,⟨1429229, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26467_1429230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26467 ⟨1429230, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26467
    ⟨1429230, by decide⟩ (by decide) (![⟨1429035, by decide⟩,⟨1429089, by decide⟩,⟨1429191, by decide⟩,⟨1429229, by decide⟩]) unmarked_context_10_26467_1429230 node_context_10_26467_1429230
  intro a
  fin_cases a
  · exact context_11_105868_1429035
  · exact context_11_105869_1429089
  · exact context_11_105870_1429191
  · exact context_11_105871_1429229

theorem unmarked_context_9_6616_1429231 : frontier 12 ⟨1429231, by decide⟩
    (prefixCache 9 6616) (prefixPartial 9 6616) = false := by
  decide +kernel

theorem node_context_9_6616_1429231 : EJMOriginalGlobalDAGData.nodes 12 ⟨1429231, by decide⟩ =
    .split (coordinate 9) (![⟨1428096, by decide⟩,⟨1428484, by decide⟩,⟨1428915, by decide⟩,⟨1429230, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6616_1429231 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6616 ⟨1429231, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6616
    ⟨1429231, by decide⟩ (by decide) (![⟨1428096, by decide⟩,⟨1428484, by decide⟩,⟨1428915, by decide⟩,⟨1429230, by decide⟩]) unmarked_context_9_6616_1429231 node_context_9_6616_1429231
  intro a
  fin_cases a
  · exact context_10_26464_1428096
  · exact context_10_26465_1428484
  · exact context_10_26466_1428915
  · exact context_10_26467_1429230

theorem selected_cut_50159 : selected 10 ⟨1369428, by decide⟩
    (prefixPartial 11 105872) = some ⟨11, 1, 0, 1369428, 105872, 1, 262144⟩ := by
  decide +kernel

theorem context_11_105872_1369428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105872 ⟨1369428, by decide⟩ :=
  accepted_of_selected 11 105872 ⟨1369428, by decide⟩ ⟨11, 1, 0, 1369428, 105872, 1, 262144⟩
    (by decide) selected_cut_50159

theorem selected_cut_50160 : selected 10 ⟨1429309, by decide⟩
    (prefixPartial 11 105873) = some ⟨11, 2, 0, 1429309, 105873, 3577, 262144⟩ := by
  decide +kernel

theorem context_11_105873_1429309 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105873 ⟨1429309, by decide⟩ :=
  accepted_of_selected 11 105873 ⟨1429309, by decide⟩ ⟨11, 2, 0, 1429309, 105873, 3577, 262144⟩
    (by decide) selected_cut_50160

theorem selected_cut_50161 : selected 10 ⟨1429366, by decide⟩
    (prefixPartial 11 105874) = some ⟨11, 2, 0, 1429366, 105874, 2657, 262144⟩ := by
  decide +kernel

theorem context_11_105874_1429366 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105874 ⟨1429366, by decide⟩ :=
  accepted_of_selected 11 105874 ⟨1429366, by decide⟩ ⟨11, 2, 0, 1429366, 105874, 2657, 262144⟩
    (by decide) selected_cut_50161

theorem selected_cut_50162 : selected 9 ⟨1429409, by decide⟩
    (prefixPartial 12 423500) = some ⟨12, 2, 0, 1429409, 423500, 1593, 65536⟩ := by
  decide +kernel

theorem context_12_423500_1429409 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 423500 ⟨1429409, by decide⟩ :=
  accepted_of_selected 12 423500 ⟨1429409, by decide⟩ ⟨12, 2, 0, 1429409, 423500, 1593, 65536⟩
    (by decide) selected_cut_50162

theorem selected_cut_50163 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 423501) = some ⟨12, 1, 0, 896706, 423501, 1, 65536⟩ := by
  decide +kernel

theorem context_12_423501_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 423501 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 423501 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 423501, 1, 65536⟩
    (by decide) selected_cut_50163

theorem selected_cut_50164 : selected 9 ⟨1429445, by decide⟩
    (prefixPartial 12 423502) = some ⟨12, 2, 0, 1429445, 423502, 1433, 65536⟩ := by
  decide +kernel

theorem context_12_423502_1429445 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 423502 ⟨1429445, by decide⟩ :=
  accepted_of_selected 12 423502 ⟨1429445, by decide⟩ ⟨12, 2, 0, 1429445, 423502, 1433, 65536⟩
    (by decide) selected_cut_50164

theorem selected_cut_50165 : selected 9 ⟨1429477, by decide⟩
    (prefixPartial 12 423503) = some ⟨12, 2, 0, 1429477, 423503, 1377, 65536⟩ := by
  decide +kernel

theorem context_12_423503_1429477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 423503 ⟨1429477, by decide⟩ :=
  accepted_of_selected 12 423503 ⟨1429477, by decide⟩ ⟨12, 2, 0, 1429477, 423503, 1377, 65536⟩
    (by decide) selected_cut_50165

theorem unmarked_context_11_105875_1429478 : frontier 10 ⟨1429478, by decide⟩
    (prefixCache 11 105875) (prefixPartial 11 105875) = false := by
  decide +kernel

theorem node_context_11_105875_1429478 : EJMOriginalGlobalDAGData.nodes 10 ⟨1429478, by decide⟩ =
    .split (coordinate 11) (![⟨1429409, by decide⟩,⟨896706, by decide⟩,⟨1429445, by decide⟩,⟨1429477, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_105875_1429478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105875 ⟨1429478, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 105875
    ⟨1429478, by decide⟩ (by decide) (![⟨1429409, by decide⟩,⟨896706, by decide⟩,⟨1429445, by decide⟩,⟨1429477, by decide⟩]) unmarked_context_11_105875_1429478 node_context_11_105875_1429478
  intro a
  fin_cases a
  · exact context_12_423500_1429409
  · exact context_12_423501_896706
  · exact context_12_423502_1429445
  · exact context_12_423503_1429477

theorem unmarked_context_10_26468_1429479 : frontier 11 ⟨1429479, by decide⟩
    (prefixCache 10 26468) (prefixPartial 10 26468) = false := by
  decide +kernel

theorem node_context_10_26468_1429479 : EJMOriginalGlobalDAGData.nodes 11 ⟨1429479, by decide⟩ =
    .split (coordinate 10) (![⟨1369428, by decide⟩,⟨1429309, by decide⟩,⟨1429366, by decide⟩,⟨1429478, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26468_1429479 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26468 ⟨1429479, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26468
    ⟨1429479, by decide⟩ (by decide) (![⟨1369428, by decide⟩,⟨1429309, by decide⟩,⟨1429366, by decide⟩,⟨1429478, by decide⟩]) unmarked_context_10_26468_1429479 node_context_10_26468_1429479
  intro a
  fin_cases a
  · exact context_11_105872_1369428
  · exact context_11_105873_1429309
  · exact context_11_105874_1429366
  · exact context_11_105875_1429478

theorem selected_cut_50166 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 26469) = some ⟨10, 1, 0, 893098, 26469, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_26469_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26469 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 26469 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 26469, 1, 1048576⟩
    (by decide) selected_cut_50166

theorem selected_cut_50167 : selected 10 ⟨1429530, by decide⟩
    (prefixPartial 11 105880) = some ⟨11, 2, 0, 1429530, 105880, 2409, 262144⟩ := by
  decide +kernel

theorem context_11_105880_1429530 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105880 ⟨1429530, by decide⟩ :=
  accepted_of_selected 11 105880 ⟨1429530, by decide⟩ ⟨11, 2, 0, 1429530, 105880, 2409, 262144⟩
    (by decide) selected_cut_50167

theorem selected_cut_50168 : selected 10 ⟨1429587, by decide⟩
    (prefixPartial 11 105881) = some ⟨11, 2, 0, 1429587, 105881, 2837, 262144⟩ := by
  decide +kernel

theorem context_11_105881_1429587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105881 ⟨1429587, by decide⟩ :=
  accepted_of_selected 11 105881 ⟨1429587, by decide⟩ ⟨11, 2, 0, 1429587, 105881, 2837, 262144⟩
    (by decide) selected_cut_50168

theorem selected_cut_50169 : selected 10 ⟨1369759, by decide⟩
    (prefixPartial 11 105882) = some ⟨11, 1, 0, 1369759, 105882, 1, 262144⟩ := by
  decide +kernel

theorem context_11_105882_1369759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105882 ⟨1369759, by decide⟩ :=
  accepted_of_selected 11 105882 ⟨1369759, by decide⟩ ⟨11, 1, 0, 1369759, 105882, 1, 262144⟩
    (by decide) selected_cut_50169

theorem selected_cut_50170 : selected 10 ⟨1429641, by decide⟩
    (prefixPartial 11 105883) = some ⟨11, 2, 0, 1429641, 105883, 2253, 262144⟩ := by
  decide +kernel

theorem context_11_105883_1429641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105883 ⟨1429641, by decide⟩ :=
  accepted_of_selected 11 105883 ⟨1429641, by decide⟩ ⟨11, 2, 0, 1429641, 105883, 2253, 262144⟩
    (by decide) selected_cut_50170

theorem unmarked_context_10_26470_1429642 : frontier 11 ⟨1429642, by decide⟩
    (prefixCache 10 26470) (prefixPartial 10 26470) = false := by
  decide +kernel

theorem node_context_10_26470_1429642 : EJMOriginalGlobalDAGData.nodes 11 ⟨1429642, by decide⟩ =
    .split (coordinate 10) (![⟨1429530, by decide⟩,⟨1429587, by decide⟩,⟨1369759, by decide⟩,⟨1429641, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26470_1429642 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26470 ⟨1429642, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26470
    ⟨1429642, by decide⟩ (by decide) (![⟨1429530, by decide⟩,⟨1429587, by decide⟩,⟨1369759, by decide⟩,⟨1429641, by decide⟩]) unmarked_context_10_26470_1429642 node_context_10_26470_1429642
  intro a
  fin_cases a
  · exact context_11_105880_1429530
  · exact context_11_105881_1429587
  · exact context_11_105882_1369759
  · exact context_11_105883_1429641

theorem selected_cut_50171 : selected 10 ⟨1429702, by decide⟩
    (prefixPartial 11 105884) = some ⟨11, 2, 0, 1429702, 105884, 2469, 262144⟩ := by
  decide +kernel

theorem context_11_105884_1429702 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105884 ⟨1429702, by decide⟩ :=
  accepted_of_selected 11 105884 ⟨1429702, by decide⟩ ⟨11, 2, 0, 1429702, 105884, 2469, 262144⟩
    (by decide) selected_cut_50171

theorem selected_cut_50172 : selected 10 ⟨1429744, by decide⟩
    (prefixPartial 11 105885) = some ⟨11, 2, 0, 1429744, 105885, 1917, 262144⟩ := by
  decide +kernel

theorem context_11_105885_1429744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105885 ⟨1429744, by decide⟩ :=
  accepted_of_selected 11 105885 ⟨1429744, by decide⟩ ⟨11, 2, 0, 1429744, 105885, 1917, 262144⟩
    (by decide) selected_cut_50172

theorem selected_cut_50173 : selected 10 ⟨1429773, by decide⟩
    (prefixPartial 11 105886) = some ⟨11, 2, 0, 1429773, 105886, 1401, 262144⟩ := by
  decide +kernel

theorem context_11_105886_1429773 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105886 ⟨1429773, by decide⟩ :=
  accepted_of_selected 11 105886 ⟨1429773, by decide⟩ ⟨11, 2, 0, 1429773, 105886, 1401, 262144⟩
    (by decide) selected_cut_50173

theorem selected_cut_50174 : selected 10 ⟨1370051, by decide⟩
    (prefixPartial 11 105887) = some ⟨11, 1, 0, 1370051, 105887, 1, 262144⟩ := by
  decide +kernel

theorem context_11_105887_1370051 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105887 ⟨1370051, by decide⟩ :=
  accepted_of_selected 11 105887 ⟨1370051, by decide⟩ ⟨11, 1, 0, 1370051, 105887, 1, 262144⟩
    (by decide) selected_cut_50174

theorem unmarked_context_10_26471_1429774 : frontier 11 ⟨1429774, by decide⟩
    (prefixCache 10 26471) (prefixPartial 10 26471) = false := by
  decide +kernel

theorem node_context_10_26471_1429774 : EJMOriginalGlobalDAGData.nodes 11 ⟨1429774, by decide⟩ =
    .split (coordinate 10) (![⟨1429702, by decide⟩,⟨1429744, by decide⟩,⟨1429773, by decide⟩,⟨1370051, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26471_1429774 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26471 ⟨1429774, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26471
    ⟨1429774, by decide⟩ (by decide) (![⟨1429702, by decide⟩,⟨1429744, by decide⟩,⟨1429773, by decide⟩,⟨1370051, by decide⟩]) unmarked_context_10_26471_1429774 node_context_10_26471_1429774
  intro a
  fin_cases a
  · exact context_11_105884_1429702
  · exact context_11_105885_1429744
  · exact context_11_105886_1429773
  · exact context_11_105887_1370051

theorem unmarked_context_9_6617_1429775 : frontier 12 ⟨1429775, by decide⟩
    (prefixCache 9 6617) (prefixPartial 9 6617) = false := by
  decide +kernel

theorem node_context_9_6617_1429775 : EJMOriginalGlobalDAGData.nodes 12 ⟨1429775, by decide⟩ =
    .split (coordinate 9) (![⟨1429479, by decide⟩,⟨893098, by decide⟩,⟨1429642, by decide⟩,⟨1429774, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6617_1429775 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6617 ⟨1429775, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6617
    ⟨1429775, by decide⟩ (by decide) (![⟨1429479, by decide⟩,⟨893098, by decide⟩,⟨1429642, by decide⟩,⟨1429774, by decide⟩]) unmarked_context_9_6617_1429775 node_context_9_6617_1429775
  intro a
  fin_cases a
  · exact context_10_26468_1429479
  · exact context_10_26469_893098
  · exact context_10_26470_1429642
  · exact context_10_26471_1429774

theorem selected_cut_50175 : selected 10 ⟨1429794, by decide⟩
    (prefixPartial 11 105888) = some ⟨11, 2, 0, 1429794, 105888, 757, 262144⟩ := by
  decide +kernel

theorem context_11_105888_1429794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105888 ⟨1429794, by decide⟩ :=
  accepted_of_selected 11 105888 ⟨1429794, by decide⟩ ⟨11, 2, 0, 1429794, 105888, 757, 262144⟩
    (by decide) selected_cut_50175

theorem selected_cut_50176 : selected 10 ⟨1429834, by decide⟩
    (prefixPartial 11 105889) = some ⟨11, 2, 0, 1429834, 105889, 1633, 262144⟩ := by
  decide +kernel

theorem context_11_105889_1429834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105889 ⟨1429834, by decide⟩ :=
  accepted_of_selected 11 105889 ⟨1429834, by decide⟩ ⟨11, 2, 0, 1429834, 105889, 1633, 262144⟩
    (by decide) selected_cut_50176

theorem selected_cut_50177 : selected 10 ⟨1429883, by decide⟩
    (prefixPartial 11 105890) = some ⟨11, 2, 0, 1429883, 105890, 2157, 262144⟩ := by
  decide +kernel

theorem context_11_105890_1429883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105890 ⟨1429883, by decide⟩ :=
  accepted_of_selected 11 105890 ⟨1429883, by decide⟩ ⟨11, 2, 0, 1429883, 105890, 2157, 262144⟩
    (by decide) selected_cut_50177

theorem selected_cut_50178 : selected 10 ⟨1429927, by decide⟩
    (prefixPartial 11 105891) = some ⟨11, 2, 0, 1429927, 105891, 1673, 262144⟩ := by
  decide +kernel

theorem context_11_105891_1429927 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105891 ⟨1429927, by decide⟩ :=
  accepted_of_selected 11 105891 ⟨1429927, by decide⟩ ⟨11, 2, 0, 1429927, 105891, 1673, 262144⟩
    (by decide) selected_cut_50178

theorem unmarked_context_10_26472_1429928 : frontier 11 ⟨1429928, by decide⟩
    (prefixCache 10 26472) (prefixPartial 10 26472) = false := by
  decide +kernel

theorem node_context_10_26472_1429928 : EJMOriginalGlobalDAGData.nodes 11 ⟨1429928, by decide⟩ =
    .split (coordinate 10) (![⟨1429794, by decide⟩,⟨1429834, by decide⟩,⟨1429883, by decide⟩,⟨1429927, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26472_1429928 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26472 ⟨1429928, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26472
    ⟨1429928, by decide⟩ (by decide) (![⟨1429794, by decide⟩,⟨1429834, by decide⟩,⟨1429883, by decide⟩,⟨1429927, by decide⟩]) unmarked_context_10_26472_1429928 node_context_10_26472_1429928
  intro a
  fin_cases a
  · exact context_11_105888_1429794
  · exact context_11_105889_1429834
  · exact context_11_105890_1429883
  · exact context_11_105891_1429927

theorem selected_cut_50179 : selected 11 ⟨1430034, by decide⟩
    (prefixPartial 10 26473) = some ⟨10, 2, 0, 1430034, 26473, 4013, 1048576⟩ := by
  decide +kernel

theorem context_10_26473_1430034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26473 ⟨1430034, by decide⟩ :=
  accepted_of_selected 10 26473 ⟨1430034, by decide⟩ ⟨10, 2, 0, 1430034, 26473, 4013, 1048576⟩
    (by decide) selected_cut_50179

theorem selected_cut_50180 : selected 11 ⟨1430037, by decide⟩
    (prefixPartial 10 26474) = some ⟨10, 2, 0, 1430037, 26474, 13, 1048576⟩ := by
  decide +kernel

theorem context_10_26474_1430037 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26474 ⟨1430037, by decide⟩ :=
  accepted_of_selected 10 26474 ⟨1430037, by decide⟩ ⟨10, 2, 0, 1430037, 26474, 13, 1048576⟩
    (by decide) selected_cut_50180

theorem selected_cut_50181 : selected 11 ⟨1430107, by decide⟩
    (prefixPartial 10 26475) = some ⟨10, 2, 0, 1430107, 26475, 3497, 1048576⟩ := by
  decide +kernel

theorem context_10_26475_1430107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26475 ⟨1430107, by decide⟩ :=
  accepted_of_selected 10 26475 ⟨1430107, by decide⟩ ⟨10, 2, 0, 1430107, 26475, 3497, 1048576⟩
    (by decide) selected_cut_50181

theorem unmarked_context_9_6618_1430108 : frontier 12 ⟨1430108, by decide⟩
    (prefixCache 9 6618) (prefixPartial 9 6618) = false := by
  decide +kernel

theorem node_context_9_6618_1430108 : EJMOriginalGlobalDAGData.nodes 12 ⟨1430108, by decide⟩ =
    .split (coordinate 9) (![⟨1429928, by decide⟩,⟨1430034, by decide⟩,⟨1430037, by decide⟩,⟨1430107, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6618_1430108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6618 ⟨1430108, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6618
    ⟨1430108, by decide⟩ (by decide) (![⟨1429928, by decide⟩,⟨1430034, by decide⟩,⟨1430037, by decide⟩,⟨1430107, by decide⟩]) unmarked_context_9_6618_1430108 node_context_9_6618_1430108
  intro a
  fin_cases a
  · exact context_10_26472_1429928
  · exact context_10_26473_1430034
  · exact context_10_26474_1430037
  · exact context_10_26475_1430107

theorem selected_cut_50182 : selected 11 ⟨1430234, by decide⟩
    (prefixPartial 10 26476) = some ⟨10, 2, 0, 1430234, 26476, 3317, 1048576⟩ := by
  decide +kernel

theorem context_10_26476_1430234 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26476 ⟨1430234, by decide⟩ :=
  accepted_of_selected 10 26476 ⟨1430234, by decide⟩ ⟨10, 2, 0, 1430234, 26476, 3317, 1048576⟩
    (by decide) selected_cut_50182

theorem selected_cut_50183 : selected 11 ⟨1430286, by decide⟩
    (prefixPartial 10 26477) = some ⟨10, 2, 0, 1430286, 26477, 1601, 1048576⟩ := by
  decide +kernel

theorem context_10_26477_1430286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26477 ⟨1430286, by decide⟩ :=
  accepted_of_selected 10 26477 ⟨1430286, by decide⟩ ⟨10, 2, 0, 1430286, 26477, 1601, 1048576⟩
    (by decide) selected_cut_50183

theorem selected_cut_50184 : selected 11 ⟨1430324, by decide⟩
    (prefixPartial 10 26478) = some ⟨10, 2, 0, 1430324, 26478, 769, 1048576⟩ := by
  decide +kernel

theorem context_10_26478_1430324 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26478 ⟨1430324, by decide⟩ :=
  accepted_of_selected 10 26478 ⟨1430324, by decide⟩ ⟨10, 2, 0, 1430324, 26478, 769, 1048576⟩
    (by decide) selected_cut_50184

theorem selected_cut_50185 : selected 11 ⟨1430327, by decide⟩
    (prefixPartial 10 26479) = some ⟨10, 2, 0, 1430327, 26479, 25, 1048576⟩ := by
  decide +kernel

theorem context_10_26479_1430327 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26479 ⟨1430327, by decide⟩ :=
  accepted_of_selected 10 26479 ⟨1430327, by decide⟩ ⟨10, 2, 0, 1430327, 26479, 25, 1048576⟩
    (by decide) selected_cut_50185

theorem unmarked_context_9_6619_1430328 : frontier 12 ⟨1430328, by decide⟩
    (prefixCache 9 6619) (prefixPartial 9 6619) = false := by
  decide +kernel

theorem node_context_9_6619_1430328 : EJMOriginalGlobalDAGData.nodes 12 ⟨1430328, by decide⟩ =
    .split (coordinate 9) (![⟨1430234, by decide⟩,⟨1430286, by decide⟩,⟨1430324, by decide⟩,⟨1430327, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6619_1430328 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6619 ⟨1430328, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6619
    ⟨1430328, by decide⟩ (by decide) (![⟨1430234, by decide⟩,⟨1430286, by decide⟩,⟨1430324, by decide⟩,⟨1430327, by decide⟩]) unmarked_context_9_6619_1430328 node_context_9_6619_1430328
  intro a
  fin_cases a
  · exact context_10_26476_1430234
  · exact context_10_26477_1430286
  · exact context_10_26478_1430324
  · exact context_10_26479_1430327

theorem unmarked_context_8_1654_1430329 : frontier 13 ⟨1430329, by decide⟩
    (prefixCache 8 1654) (prefixPartial 8 1654) = false := by
  decide +kernel

theorem node_context_8_1654_1430329 : EJMOriginalGlobalDAGData.nodes 13 ⟨1430329, by decide⟩ =
    .split (coordinate 8) (![⟨1429231, by decide⟩,⟨1429775, by decide⟩,⟨1430108, by decide⟩,⟨1430328, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1654_1430329 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1654 ⟨1430329, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1654
    ⟨1430329, by decide⟩ (by decide) (![⟨1429231, by decide⟩,⟨1429775, by decide⟩,⟨1430108, by decide⟩,⟨1430328, by decide⟩]) unmarked_context_8_1654_1430329 node_context_8_1654_1430329
  intro a
  fin_cases a
  · exact context_9_6616_1429231
  · exact context_9_6617_1429775
  · exact context_9_6618_1430108
  · exact context_9_6619_1430328

theorem selected_cut_50186 : selected 13 ⟨814757, by decide⟩
    (prefixPartial 8 1655) = some ⟨8, 1, 0, 814757, 1655, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_1655_814757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1655 ⟨814757, by decide⟩ :=
  accepted_of_selected 8 1655 ⟨814757, by decide⟩ ⟨8, 1, 0, 814757, 1655, 1, 16777216⟩
    (by decide) selected_cut_50186

theorem unmarked_context_7_413_1430330 : frontier 14 ⟨1430330, by decide⟩
    (prefixCache 7 413) (prefixPartial 7 413) = false := by
  decide +kernel

theorem node_context_7_413_1430330 : EJMOriginalGlobalDAGData.nodes 14 ⟨1430330, by decide⟩ =
    .split (coordinate 7) (![⟨1425764, by decide⟩,⟨1427907, by decide⟩,⟨1430329, by decide⟩,⟨814757, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_413_1430330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 413 ⟨1430330, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 413
    ⟨1430330, by decide⟩ (by decide) (![⟨1425764, by decide⟩,⟨1427907, by decide⟩,⟨1430329, by decide⟩,⟨814757, by decide⟩]) unmarked_context_7_413_1430330 node_context_7_413_1430330
  intro a
  fin_cases a
  · exact context_8_1652_1425764
  · exact context_8_1653_1427907
  · exact context_8_1654_1430329
  · exact context_8_1655_814757

theorem selected_cut_50187 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 105984) = some ⟨11, 1, 0, 434745, 105984, 1, 262144⟩ := by
  decide +kernel

theorem context_11_105984_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105984 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 105984 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 105984, 1, 262144⟩
    (by decide) selected_cut_50187

theorem selected_cut_50188 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 105985) = some ⟨11, 1, 0, 434745, 105985, 1, 262144⟩ := by
  decide +kernel

theorem context_11_105985_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105985 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 105985 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 105985, 1, 262144⟩
    (by decide) selected_cut_50188

theorem selected_cut_50189 : selected 10 ⟨1430467, by decide⟩
    (prefixPartial 11 105986) = some ⟨11, 2, 0, 1430467, 105986, 2749, 262144⟩ := by
  decide +kernel

theorem context_11_105986_1430467 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105986 ⟨1430467, by decide⟩ :=
  accepted_of_selected 11 105986 ⟨1430467, by decide⟩ ⟨11, 2, 0, 1430467, 105986, 2749, 262144⟩
    (by decide) selected_cut_50189

theorem selected_cut_50190 : selected 10 ⟨1430630, by decide⟩
    (prefixPartial 11 105987) = some ⟨11, 2, 0, 1430630, 105987, 3353, 262144⟩ := by
  decide +kernel

theorem context_11_105987_1430630 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105987 ⟨1430630, by decide⟩ :=
  accepted_of_selected 11 105987 ⟨1430630, by decide⟩ ⟨11, 2, 0, 1430630, 105987, 3353, 262144⟩
    (by decide) selected_cut_50190

theorem unmarked_context_10_26496_1430631 : frontier 11 ⟨1430631, by decide⟩
    (prefixCache 10 26496) (prefixPartial 10 26496) = false := by
  decide +kernel

theorem node_context_10_26496_1430631 : EJMOriginalGlobalDAGData.nodes 11 ⟨1430631, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨434745, by decide⟩,⟨1430467, by decide⟩,⟨1430630, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26496_1430631 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26496 ⟨1430631, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26496
    ⟨1430631, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨434745, by decide⟩,⟨1430467, by decide⟩,⟨1430630, by decide⟩]) unmarked_context_10_26496_1430631 node_context_10_26496_1430631
  intro a
  fin_cases a
  · exact context_11_105984_434745
  · exact context_11_105985_434745
  · exact context_11_105986_1430467
  · exact context_11_105987_1430630

theorem selected_cut_50191 : selected 9 ⟨1415033, by decide⟩
    (prefixPartial 12 423952) = some ⟨12, 1, 0, 1415033, 423952, 1, 65536⟩ := by
  decide +kernel

theorem context_12_423952_1415033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 423952 ⟨1415033, by decide⟩ :=
  accepted_of_selected 12 423952 ⟨1415033, by decide⟩ ⟨12, 1, 0, 1415033, 423952, 1, 65536⟩
    (by decide) selected_cut_50191

theorem selected_cut_50192 : selected 9 ⟨1430705, by decide⟩
    (prefixPartial 12 423953) = some ⟨12, 2, 0, 1430705, 423953, 2277, 65536⟩ := by
  decide +kernel

theorem context_12_423953_1430705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 423953 ⟨1430705, by decide⟩ :=
  accepted_of_selected 12 423953 ⟨1430705, by decide⟩ ⟨12, 2, 0, 1430705, 423953, 2277, 65536⟩
    (by decide) selected_cut_50192

theorem selected_cut_50193 : selected 9 ⟨1430787, by decide⟩
    (prefixPartial 12 423954) = some ⟨12, 2, 0, 1430787, 423954, 2429, 65536⟩ := by
  decide +kernel

theorem context_12_423954_1430787 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 423954 ⟨1430787, by decide⟩ :=
  accepted_of_selected 12 423954 ⟨1430787, by decide⟩ ⟨12, 2, 0, 1430787, 423954, 2429, 65536⟩
    (by decide) selected_cut_50193

theorem selected_cut_50194 : selected 9 ⟨1430866, by decide⟩
    (prefixPartial 12 423955) = some ⟨12, 2, 0, 1430866, 423955, 2449, 65536⟩ := by
  decide +kernel

theorem context_12_423955_1430866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 423955 ⟨1430866, by decide⟩ :=
  accepted_of_selected 12 423955 ⟨1430866, by decide⟩ ⟨12, 2, 0, 1430866, 423955, 2449, 65536⟩
    (by decide) selected_cut_50194

theorem unmarked_context_11_105988_1430867 : frontier 10 ⟨1430867, by decide⟩
    (prefixCache 11 105988) (prefixPartial 11 105988) = false := by
  decide +kernel

theorem node_context_11_105988_1430867 : EJMOriginalGlobalDAGData.nodes 10 ⟨1430867, by decide⟩ =
    .split (coordinate 11) (![⟨1415033, by decide⟩,⟨1430705, by decide⟩,⟨1430787, by decide⟩,⟨1430866, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_105988_1430867 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105988 ⟨1430867, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 105988
    ⟨1430867, by decide⟩ (by decide) (![⟨1415033, by decide⟩,⟨1430705, by decide⟩,⟨1430787, by decide⟩,⟨1430866, by decide⟩]) unmarked_context_11_105988_1430867 node_context_11_105988_1430867
  intro a
  fin_cases a
  · exact context_12_423952_1415033
  · exact context_12_423953_1430705
  · exact context_12_423954_1430787
  · exact context_12_423955_1430866

theorem selected_cut_50195 : selected 10 ⟨1192826, by decide⟩
    (prefixPartial 11 105989) = some ⟨11, 1, 0, 1192826, 105989, 1, 262144⟩ := by
  decide +kernel

theorem context_11_105989_1192826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105989 ⟨1192826, by decide⟩ :=
  accepted_of_selected 11 105989 ⟨1192826, by decide⟩ ⟨11, 1, 0, 1192826, 105989, 1, 262144⟩
    (by decide) selected_cut_50195

theorem selected_cut_50196 : selected 9 ⟨1415033, by decide⟩
    (prefixPartial 12 423960) = some ⟨12, 1, 0, 1415033, 423960, 1, 65536⟩ := by
  decide +kernel

theorem context_12_423960_1415033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 423960 ⟨1415033, by decide⟩ :=
  accepted_of_selected 12 423960 ⟨1415033, by decide⟩ ⟨12, 1, 0, 1415033, 423960, 1, 65536⟩
    (by decide) selected_cut_50196

theorem selected_cut_50197 : selected 9 ⟨1430922, by decide⟩
    (prefixPartial 12 423961) = some ⟨12, 2, 0, 1430922, 423961, 2121, 65536⟩ := by
  decide +kernel

theorem context_12_423961_1430922 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 423961 ⟨1430922, by decide⟩ :=
  accepted_of_selected 12 423961 ⟨1430922, by decide⟩ ⟨12, 2, 0, 1430922, 423961, 2121, 65536⟩
    (by decide) selected_cut_50197

theorem selected_cut_50198 : selected 9 ⟨663554, by decide⟩
    (prefixPartial 12 423962) = some ⟨12, 1, 0, 663554, 423962, 1, 65536⟩ := by
  decide +kernel

theorem context_12_423962_663554 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 423962 ⟨663554, by decide⟩ :=
  accepted_of_selected 12 423962 ⟨663554, by decide⟩ ⟨12, 1, 0, 663554, 423962, 1, 65536⟩
    (by decide) selected_cut_50198

theorem selected_cut_50199 : selected 9 ⟨1430995, by decide⟩
    (prefixPartial 12 423963) = some ⟨12, 2, 0, 1430995, 423963, 2501, 65536⟩ := by
  decide +kernel

theorem context_12_423963_1430995 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 423963 ⟨1430995, by decide⟩ :=
  accepted_of_selected 12 423963 ⟨1430995, by decide⟩ ⟨12, 2, 0, 1430995, 423963, 2501, 65536⟩
    (by decide) selected_cut_50199

theorem unmarked_context_11_105990_1430996 : frontier 10 ⟨1430996, by decide⟩
    (prefixCache 11 105990) (prefixPartial 11 105990) = false := by
  decide +kernel

theorem node_context_11_105990_1430996 : EJMOriginalGlobalDAGData.nodes 10 ⟨1430996, by decide⟩ =
    .split (coordinate 11) (![⟨1415033, by decide⟩,⟨1430922, by decide⟩,⟨663554, by decide⟩,⟨1430995, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_105990_1430996 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105990 ⟨1430996, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 105990
    ⟨1430996, by decide⟩ (by decide) (![⟨1415033, by decide⟩,⟨1430922, by decide⟩,⟨663554, by decide⟩,⟨1430995, by decide⟩]) unmarked_context_11_105990_1430996 node_context_11_105990_1430996
  intro a
  fin_cases a
  · exact context_12_423960_1415033
  · exact context_12_423961_1430922
  · exact context_12_423962_663554
  · exact context_12_423963_1430995

theorem selected_cut_50200 : selected 9 ⟨1415033, by decide⟩
    (prefixPartial 12 423964) = some ⟨12, 1, 0, 1415033, 423964, 1, 65536⟩ := by
  decide +kernel

theorem context_12_423964_1415033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 423964 ⟨1415033, by decide⟩ :=
  accepted_of_selected 12 423964 ⟨1415033, by decide⟩ ⟨12, 1, 0, 1415033, 423964, 1, 65536⟩
    (by decide) selected_cut_50200

theorem selected_cut_50201 : selected 9 ⟨1431058, by decide⟩
    (prefixPartial 12 423965) = some ⟨12, 2, 0, 1431058, 423965, 2249, 65536⟩ := by
  decide +kernel

theorem context_12_423965_1431058 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 423965 ⟨1431058, by decide⟩ :=
  accepted_of_selected 12 423965 ⟨1431058, by decide⟩ ⟨12, 2, 0, 1431058, 423965, 2249, 65536⟩
    (by decide) selected_cut_50201

theorem selected_cut_50202 : selected 9 ⟨1431118, by decide⟩
    (prefixPartial 12 423966) = some ⟨12, 2, 0, 1431118, 423966, 2593, 65536⟩ := by
  decide +kernel

theorem context_12_423966_1431118 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 423966 ⟨1431118, by decide⟩ :=
  accepted_of_selected 12 423966 ⟨1431118, by decide⟩ ⟨12, 2, 0, 1431118, 423966, 2593, 65536⟩
    (by decide) selected_cut_50202

theorem selected_cut_50203 : selected 9 ⟨517541, by decide⟩
    (prefixPartial 12 423967) = some ⟨12, 1, 0, 517541, 423967, 1, 65536⟩ := by
  decide +kernel

theorem context_12_423967_517541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 423967 ⟨517541, by decide⟩ :=
  accepted_of_selected 12 423967 ⟨517541, by decide⟩ ⟨12, 1, 0, 517541, 423967, 1, 65536⟩
    (by decide) selected_cut_50203

theorem unmarked_context_11_105991_1431119 : frontier 10 ⟨1431119, by decide⟩
    (prefixCache 11 105991) (prefixPartial 11 105991) = false := by
  decide +kernel

theorem node_context_11_105991_1431119 : EJMOriginalGlobalDAGData.nodes 10 ⟨1431119, by decide⟩ =
    .split (coordinate 11) (![⟨1415033, by decide⟩,⟨1431058, by decide⟩,⟨1431118, by decide⟩,⟨517541, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_105991_1431119 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105991 ⟨1431119, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 105991
    ⟨1431119, by decide⟩ (by decide) (![⟨1415033, by decide⟩,⟨1431058, by decide⟩,⟨1431118, by decide⟩,⟨517541, by decide⟩]) unmarked_context_11_105991_1431119 node_context_11_105991_1431119
  intro a
  fin_cases a
  · exact context_12_423964_1415033
  · exact context_12_423965_1431058
  · exact context_12_423966_1431118
  · exact context_12_423967_517541

theorem unmarked_context_10_26497_1431120 : frontier 11 ⟨1431120, by decide⟩
    (prefixCache 10 26497) (prefixPartial 10 26497) = false := by
  decide +kernel

theorem node_context_10_26497_1431120 : EJMOriginalGlobalDAGData.nodes 11 ⟨1431120, by decide⟩ =
    .split (coordinate 10) (![⟨1430867, by decide⟩,⟨1192826, by decide⟩,⟨1430996, by decide⟩,⟨1431119, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26497_1431120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26497 ⟨1431120, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26497
    ⟨1431120, by decide⟩ (by decide) (![⟨1430867, by decide⟩,⟨1192826, by decide⟩,⟨1430996, by decide⟩,⟨1431119, by decide⟩]) unmarked_context_10_26497_1431120 node_context_10_26497_1431120
  intro a
  fin_cases a
  · exact context_11_105988_1430867
  · exact context_11_105989_1192826
  · exact context_11_105990_1430996
  · exact context_11_105991_1431119

theorem selected_cut_50204 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 423968) = some ⟨12, 1, 0, 435160, 423968, 1, 65536⟩ := by
  decide +kernel

theorem context_12_423968_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 423968 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 423968 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 423968, 1, 65536⟩
    (by decide) selected_cut_50204

theorem selected_cut_50205 : selected 9 ⟨1431183, by decide⟩
    (prefixPartial 12 423969) = some ⟨12, 2, 0, 1431183, 423969, 2181, 65536⟩ := by
  decide +kernel

theorem context_12_423969_1431183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 423969 ⟨1431183, by decide⟩ :=
  accepted_of_selected 12 423969 ⟨1431183, by decide⟩ ⟨12, 2, 0, 1431183, 423969, 2181, 65536⟩
    (by decide) selected_cut_50205

theorem selected_cut_50206 : selected 9 ⟨1431242, by decide⟩
    (prefixPartial 12 423970) = some ⟨12, 2, 0, 1431242, 423970, 2189, 65536⟩ := by
  decide +kernel

theorem context_12_423970_1431242 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 423970 ⟨1431242, by decide⟩ :=
  accepted_of_selected 12 423970 ⟨1431242, by decide⟩ ⟨12, 2, 0, 1431242, 423970, 2189, 65536⟩
    (by decide) selected_cut_50206

theorem selected_cut_50207 : selected 9 ⟨1431306, by decide⟩
    (prefixPartial 12 423971) = some ⟨12, 2, 0, 1431306, 423971, 2069, 65536⟩ := by
  decide +kernel

theorem context_12_423971_1431306 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 423971 ⟨1431306, by decide⟩ :=
  accepted_of_selected 12 423971 ⟨1431306, by decide⟩ ⟨12, 2, 0, 1431306, 423971, 2069, 65536⟩
    (by decide) selected_cut_50207

theorem unmarked_context_11_105992_1431307 : frontier 10 ⟨1431307, by decide⟩
    (prefixCache 11 105992) (prefixPartial 11 105992) = false := by
  decide +kernel

theorem node_context_11_105992_1431307 : EJMOriginalGlobalDAGData.nodes 10 ⟨1431307, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨1431183, by decide⟩,⟨1431242, by decide⟩,⟨1431306, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_105992_1431307 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105992 ⟨1431307, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 105992
    ⟨1431307, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨1431183, by decide⟩,⟨1431242, by decide⟩,⟨1431306, by decide⟩]) unmarked_context_11_105992_1431307 node_context_11_105992_1431307
  intro a
  fin_cases a
  · exact context_12_423968_435160
  · exact context_12_423969_1431183
  · exact context_12_423970_1431242
  · exact context_12_423971_1431306

theorem selected_cut_50208 : selected 10 ⟨1431416, by decide⟩
    (prefixPartial 11 105993) = some ⟨11, 2, 0, 1431416, 105993, 3881, 262144⟩ := by
  decide +kernel

theorem context_11_105993_1431416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105993 ⟨1431416, by decide⟩ :=
  accepted_of_selected 11 105993 ⟨1431416, by decide⟩ ⟨11, 2, 0, 1431416, 105993, 3881, 262144⟩
    (by decide) selected_cut_50208

theorem selected_cut_50209 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 105994) = some ⟨11, 1, 0, 900587, 105994, 1, 262144⟩ := by
  decide +kernel

theorem context_11_105994_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105994 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 105994 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 105994, 1, 262144⟩
    (by decide) selected_cut_50209

theorem selected_cut_50210 : selected 9 ⟨449505, by decide⟩
    (prefixPartial 12 423980) = some ⟨12, 1, 0, 449505, 423980, 1, 65536⟩ := by
  decide +kernel

theorem context_12_423980_449505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 423980 ⟨449505, by decide⟩ :=
  accepted_of_selected 12 423980 ⟨449505, by decide⟩ ⟨12, 1, 0, 449505, 423980, 1, 65536⟩
    (by decide) selected_cut_50210

theorem selected_cut_50211 : selected 9 ⟨1431472, by decide⟩
    (prefixPartial 12 423981) = some ⟨12, 2, 0, 1431472, 423981, 1969, 65536⟩ := by
  decide +kernel

theorem context_12_423981_1431472 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 423981 ⟨1431472, by decide⟩ :=
  accepted_of_selected 12 423981 ⟨1431472, by decide⟩ ⟨12, 2, 0, 1431472, 423981, 1969, 65536⟩
    (by decide) selected_cut_50211

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
