/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover069
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_06723 : selected 8 ⟨199234, by decide⟩
    (prefixPartial 13 87387) = some ⟨13, 2, 0, 199234, 87387, 977, 16384⟩ := by
  decide +kernel

theorem context_13_87387_199234 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87387 ⟨199234, by decide⟩ :=
  accepted_of_selected 13 87387 ⟨199234, by decide⟩ ⟨13, 2, 0, 199234, 87387, 977, 16384⟩
    (by decide) selected_cut_06723

theorem unmarked_context_12_21846_199235 : frontier 9 ⟨199235, by decide⟩
    (prefixCache 12 21846) (prefixPartial 12 21846) = false := by
  decide +kernel

theorem node_context_12_21846_199235 : EJMOriginalGlobalDAGData.nodes 9 ⟨199235, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨199205, by decide⟩,⟨199225, by decide⟩,⟨199234, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21846_199235 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21846 ⟨199235, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21846
    ⟨199235, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨199205, by decide⟩,⟨199225, by decide⟩,⟨199234, by decide⟩]) unmarked_context_12_21846_199235 node_context_12_21846_199235
  intro a
  fin_cases a
  · exact context_13_87384_3444
  · exact context_13_87385_199205
  · exact context_13_87386_199225
  · exact context_13_87387_199234

theorem selected_cut_06724 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 21847) = some ⟨12, 1, 0, 893, 21847, 1, 65536⟩ := by
  decide +kernel

theorem context_12_21847_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21847 ⟨893, by decide⟩ :=
  accepted_of_selected 12 21847 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 21847, 1, 65536⟩
    (by decide) selected_cut_06724

theorem unmarked_context_11_5461_199236 : frontier 10 ⟨199236, by decide⟩
    (prefixCache 11 5461) (prefixPartial 11 5461) = false := by
  decide +kernel

theorem node_context_11_5461_199236 : EJMOriginalGlobalDAGData.nodes 10 ⟨199236, by decide⟩ =
    .split (coordinate 11) (![⟨199180, by decide⟩,⟨170504, by decide⟩,⟨199235, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5461_199236 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5461 ⟨199236, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5461
    ⟨199236, by decide⟩ (by decide) (![⟨199180, by decide⟩,⟨170504, by decide⟩,⟨199235, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_5461_199236 node_context_11_5461_199236
  intro a
  fin_cases a
  · exact context_12_21844_199180
  · exact context_12_21845_170504
  · exact context_12_21846_199235
  · exact context_12_21847_893

theorem selected_cut_06725 : selected 9 ⟨199289, by decide⟩
    (prefixPartial 12 21848) = some ⟨12, 2, 0, 199289, 21848, 3809, 65536⟩ := by
  decide +kernel

theorem context_12_21848_199289 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21848 ⟨199289, by decide⟩ :=
  accepted_of_selected 12 21848 ⟨199289, by decide⟩ ⟨12, 2, 0, 199289, 21848, 3809, 65536⟩
    (by decide) selected_cut_06725

theorem selected_cut_06726 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 87396) = some ⟨13, 1, 0, 3444, 87396, 1, 16384⟩ := by
  decide +kernel

theorem context_13_87396_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87396 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 87396 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 87396, 1, 16384⟩
    (by decide) selected_cut_06726

theorem selected_cut_06727 : selected 8 ⟨199306, by decide⟩
    (prefixPartial 13 87397) = some ⟨13, 2, 0, 199306, 87397, 1081, 16384⟩ := by
  decide +kernel

theorem context_13_87397_199306 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87397 ⟨199306, by decide⟩ :=
  accepted_of_selected 13 87397 ⟨199306, by decide⟩ ⟨13, 2, 0, 199306, 87397, 1081, 16384⟩
    (by decide) selected_cut_06727

theorem selected_cut_06728 : selected 8 ⟨199330, by decide⟩
    (prefixPartial 13 87398) = some ⟨13, 2, 0, 199330, 87398, 2173, 16384⟩ := by
  decide +kernel

theorem context_13_87398_199330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87398 ⟨199330, by decide⟩ :=
  accepted_of_selected 13 87398 ⟨199330, by decide⟩ ⟨13, 2, 0, 199330, 87398, 2173, 16384⟩
    (by decide) selected_cut_06728

theorem selected_cut_06729 : selected 8 ⟨199343, by decide⟩
    (prefixPartial 13 87399) = some ⟨13, 2, 0, 199343, 87399, 1073, 16384⟩ := by
  decide +kernel

theorem context_13_87399_199343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87399 ⟨199343, by decide⟩ :=
  accepted_of_selected 13 87399 ⟨199343, by decide⟩ ⟨13, 2, 0, 199343, 87399, 1073, 16384⟩
    (by decide) selected_cut_06729

theorem unmarked_context_12_21849_199344 : frontier 9 ⟨199344, by decide⟩
    (prefixCache 12 21849) (prefixPartial 12 21849) = false := by
  decide +kernel

theorem node_context_12_21849_199344 : EJMOriginalGlobalDAGData.nodes 9 ⟨199344, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨199306, by decide⟩,⟨199330, by decide⟩,⟨199343, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21849_199344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21849 ⟨199344, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21849
    ⟨199344, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨199306, by decide⟩,⟨199330, by decide⟩,⟨199343, by decide⟩]) unmarked_context_12_21849_199344 node_context_12_21849_199344
  intro a
  fin_cases a
  · exact context_13_87396_3444
  · exact context_13_87397_199306
  · exact context_13_87398_199330
  · exact context_13_87399_199343

theorem selected_cut_06730 : selected 9 ⟨199405, by decide⟩
    (prefixPartial 12 21850) = some ⟨12, 2, 0, 199405, 21850, 3901, 65536⟩ := by
  decide +kernel

theorem context_12_21850_199405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21850 ⟨199405, by decide⟩ :=
  accepted_of_selected 12 21850 ⟨199405, by decide⟩ ⟨12, 2, 0, 199405, 21850, 3901, 65536⟩
    (by decide) selected_cut_06730

theorem selected_cut_06731 : selected 9 ⟨199457, by decide⟩
    (prefixPartial 12 21851) = some ⟨12, 2, 0, 199457, 21851, 4093, 65536⟩ := by
  decide +kernel

theorem context_12_21851_199457 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21851 ⟨199457, by decide⟩ :=
  accepted_of_selected 12 21851 ⟨199457, by decide⟩ ⟨12, 2, 0, 199457, 21851, 4093, 65536⟩
    (by decide) selected_cut_06731

theorem unmarked_context_11_5462_199458 : frontier 10 ⟨199458, by decide⟩
    (prefixCache 11 5462) (prefixPartial 11 5462) = false := by
  decide +kernel

theorem node_context_11_5462_199458 : EJMOriginalGlobalDAGData.nodes 10 ⟨199458, by decide⟩ =
    .split (coordinate 11) (![⟨199289, by decide⟩,⟨199344, by decide⟩,⟨199405, by decide⟩,⟨199457, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5462_199458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5462 ⟨199458, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5462
    ⟨199458, by decide⟩ (by decide) (![⟨199289, by decide⟩,⟨199344, by decide⟩,⟨199405, by decide⟩,⟨199457, by decide⟩]) unmarked_context_11_5462_199458 node_context_11_5462_199458
  intro a
  fin_cases a
  · exact context_12_21848_199289
  · exact context_12_21849_199344
  · exact context_12_21850_199405
  · exact context_12_21851_199457

theorem selected_cut_06732 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 5463) = some ⟨11, 1, 0, 1736, 5463, 1, 262144⟩ := by
  decide +kernel

theorem context_11_5463_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5463 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 5463 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 5463, 1, 262144⟩
    (by decide) selected_cut_06732

theorem unmarked_context_10_1365_199459 : frontier 11 ⟨199459, by decide⟩
    (prefixCache 10 1365) (prefixPartial 10 1365) = false := by
  decide +kernel

theorem node_context_10_1365_199459 : EJMOriginalGlobalDAGData.nodes 11 ⟨199459, by decide⟩ =
    .split (coordinate 10) (![⟨199179, by decide⟩,⟨199236, by decide⟩,⟨199458, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1365_199459 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1365 ⟨199459, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1365
    ⟨199459, by decide⟩ (by decide) (![⟨199179, by decide⟩,⟨199236, by decide⟩,⟨199458, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_1365_199459 node_context_10_1365_199459
  intro a
  fin_cases a
  · exact context_11_5460_199179
  · exact context_11_5461_199236
  · exact context_11_5462_199458
  · exact context_11_5463_1736

theorem selected_cut_06733 : selected 9 ⟨199503, by decide⟩
    (prefixPartial 12 21856) = some ⟨12, 2, 0, 199503, 21856, 3641, 65536⟩ := by
  decide +kernel

theorem context_12_21856_199503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21856 ⟨199503, by decide⟩ :=
  accepted_of_selected 12 21856 ⟨199503, by decide⟩ ⟨12, 2, 0, 199503, 21856, 3641, 65536⟩
    (by decide) selected_cut_06733

theorem selected_cut_06734 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 87428) = some ⟨13, 1, 0, 3444, 87428, 1, 16384⟩ := by
  decide +kernel

theorem context_13_87428_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87428 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 87428 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 87428, 1, 16384⟩
    (by decide) selected_cut_06734

theorem selected_cut_06735 : selected 8 ⟨199517, by decide⟩
    (prefixPartial 13 87429) = some ⟨13, 2, 0, 199517, 87429, 1349, 16384⟩ := by
  decide +kernel

theorem context_13_87429_199517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87429 ⟨199517, by decide⟩ :=
  accepted_of_selected 13 87429 ⟨199517, by decide⟩ ⟨13, 2, 0, 199517, 87429, 1349, 16384⟩
    (by decide) selected_cut_06735

theorem selected_cut_06736 : selected 8 ⟨199535, by decide⟩
    (prefixPartial 13 87430) = some ⟨13, 2, 0, 199535, 87430, 2033, 16384⟩ := by
  decide +kernel

theorem context_13_87430_199535 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87430 ⟨199535, by decide⟩ :=
  accepted_of_selected 13 87430 ⟨199535, by decide⟩ ⟨13, 2, 0, 199535, 87430, 2033, 16384⟩
    (by decide) selected_cut_06736

theorem selected_cut_06737 : selected 8 ⟨199547, by decide⟩
    (prefixPartial 13 87431) = some ⟨13, 2, 0, 199547, 87431, 1193, 16384⟩ := by
  decide +kernel

theorem context_13_87431_199547 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87431 ⟨199547, by decide⟩ :=
  accepted_of_selected 13 87431 ⟨199547, by decide⟩ ⟨13, 2, 0, 199547, 87431, 1193, 16384⟩
    (by decide) selected_cut_06737

theorem unmarked_context_12_21857_199548 : frontier 9 ⟨199548, by decide⟩
    (prefixCache 12 21857) (prefixPartial 12 21857) = false := by
  decide +kernel

theorem node_context_12_21857_199548 : EJMOriginalGlobalDAGData.nodes 9 ⟨199548, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨199517, by decide⟩,⟨199535, by decide⟩,⟨199547, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21857_199548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21857 ⟨199548, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21857
    ⟨199548, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨199517, by decide⟩,⟨199535, by decide⟩,⟨199547, by decide⟩]) unmarked_context_12_21857_199548 node_context_12_21857_199548
  intro a
  fin_cases a
  · exact context_13_87428_3444
  · exact context_13_87429_199517
  · exact context_13_87430_199535
  · exact context_13_87431_199547

theorem selected_cut_06738 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 87432) = some ⟨13, 1, 0, 3444, 87432, 1, 16384⟩ := by
  decide +kernel

theorem context_13_87432_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87432 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 87432 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 87432, 1, 16384⟩
    (by decide) selected_cut_06738

theorem selected_cut_06739 : selected 8 ⟨199565, by decide⟩
    (prefixPartial 13 87433) = some ⟨13, 2, 0, 199565, 87433, 1409, 16384⟩ := by
  decide +kernel

theorem context_13_87433_199565 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87433 ⟨199565, by decide⟩ :=
  accepted_of_selected 13 87433 ⟨199565, by decide⟩ ⟨13, 2, 0, 199565, 87433, 1409, 16384⟩
    (by decide) selected_cut_06739

theorem selected_cut_06740 : selected 8 ⟨199587, by decide⟩
    (prefixPartial 13 87434) = some ⟨13, 2, 0, 199587, 87434, 1729, 16384⟩ := by
  decide +kernel

theorem context_13_87434_199587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87434 ⟨199587, by decide⟩ :=
  accepted_of_selected 13 87434 ⟨199587, by decide⟩ ⟨13, 2, 0, 199587, 87434, 1729, 16384⟩
    (by decide) selected_cut_06740

theorem selected_cut_06741 : selected 8 ⟨199597, by decide⟩
    (prefixPartial 13 87435) = some ⟨13, 2, 0, 199597, 87435, 1093, 16384⟩ := by
  decide +kernel

theorem context_13_87435_199597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87435 ⟨199597, by decide⟩ :=
  accepted_of_selected 13 87435 ⟨199597, by decide⟩ ⟨13, 2, 0, 199597, 87435, 1093, 16384⟩
    (by decide) selected_cut_06741

theorem unmarked_context_12_21858_199598 : frontier 9 ⟨199598, by decide⟩
    (prefixCache 12 21858) (prefixPartial 12 21858) = false := by
  decide +kernel

theorem node_context_12_21858_199598 : EJMOriginalGlobalDAGData.nodes 9 ⟨199598, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨199565, by decide⟩,⟨199587, by decide⟩,⟨199597, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21858_199598 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21858 ⟨199598, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21858
    ⟨199598, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨199565, by decide⟩,⟨199587, by decide⟩,⟨199597, by decide⟩]) unmarked_context_12_21858_199598 node_context_12_21858_199598
  intro a
  fin_cases a
  · exact context_13_87432_3444
  · exact context_13_87433_199565
  · exact context_13_87434_199587
  · exact context_13_87435_199597

theorem selected_cut_06742 : selected 9 ⟨199642, by decide⟩
    (prefixPartial 12 21859) = some ⟨12, 2, 0, 199642, 21859, 4061, 65536⟩ := by
  decide +kernel

theorem context_12_21859_199642 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21859 ⟨199642, by decide⟩ :=
  accepted_of_selected 12 21859 ⟨199642, by decide⟩ ⟨12, 2, 0, 199642, 21859, 4061, 65536⟩
    (by decide) selected_cut_06742

theorem unmarked_context_11_5464_199643 : frontier 10 ⟨199643, by decide⟩
    (prefixCache 11 5464) (prefixPartial 11 5464) = false := by
  decide +kernel

theorem node_context_11_5464_199643 : EJMOriginalGlobalDAGData.nodes 10 ⟨199643, by decide⟩ =
    .split (coordinate 11) (![⟨199503, by decide⟩,⟨199548, by decide⟩,⟨199598, by decide⟩,⟨199642, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5464_199643 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5464 ⟨199643, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5464
    ⟨199643, by decide⟩ (by decide) (![⟨199503, by decide⟩,⟨199548, by decide⟩,⟨199598, by decide⟩,⟨199642, by decide⟩]) unmarked_context_11_5464_199643 node_context_11_5464_199643
  intro a
  fin_cases a
  · exact context_12_21856_199503
  · exact context_12_21857_199548
  · exact context_12_21858_199598
  · exact context_12_21859_199642

theorem selected_cut_06743 : selected 9 ⟨199686, by decide⟩
    (prefixPartial 12 21860) = some ⟨12, 2, 0, 199686, 21860, 2725, 65536⟩ := by
  decide +kernel

theorem context_12_21860_199686 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21860 ⟨199686, by decide⟩ :=
  accepted_of_selected 12 21860 ⟨199686, by decide⟩ ⟨12, 2, 0, 199686, 21860, 2725, 65536⟩
    (by decide) selected_cut_06743

theorem selected_cut_06744 : selected 9 ⟨126884, by decide⟩
    (prefixPartial 12 21861) = some ⟨12, 1, 0, 126884, 21861, 1, 65536⟩ := by
  decide +kernel

theorem context_12_21861_126884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21861 ⟨126884, by decide⟩ :=
  accepted_of_selected 12 21861 ⟨126884, by decide⟩ ⟨12, 1, 0, 126884, 21861, 1, 65536⟩
    (by decide) selected_cut_06744

theorem selected_cut_06745 : selected 9 ⟨199731, by decide⟩
    (prefixPartial 12 21862) = some ⟨12, 2, 0, 199731, 21862, 2897, 65536⟩ := by
  decide +kernel

theorem context_12_21862_199731 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21862 ⟨199731, by decide⟩ :=
  accepted_of_selected 12 21862 ⟨199731, by decide⟩ ⟨12, 2, 0, 199731, 21862, 2897, 65536⟩
    (by decide) selected_cut_06745

theorem selected_cut_06746 : selected 9 ⟨199775, by decide⟩
    (prefixPartial 12 21863) = some ⟨12, 2, 0, 199775, 21863, 2805, 65536⟩ := by
  decide +kernel

theorem context_12_21863_199775 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21863 ⟨199775, by decide⟩ :=
  accepted_of_selected 12 21863 ⟨199775, by decide⟩ ⟨12, 2, 0, 199775, 21863, 2805, 65536⟩
    (by decide) selected_cut_06746

theorem unmarked_context_11_5465_199776 : frontier 10 ⟨199776, by decide⟩
    (prefixCache 11 5465) (prefixPartial 11 5465) = false := by
  decide +kernel

theorem node_context_11_5465_199776 : EJMOriginalGlobalDAGData.nodes 10 ⟨199776, by decide⟩ =
    .split (coordinate 11) (![⟨199686, by decide⟩,⟨126884, by decide⟩,⟨199731, by decide⟩,⟨199775, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5465_199776 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5465 ⟨199776, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5465
    ⟨199776, by decide⟩ (by decide) (![⟨199686, by decide⟩,⟨126884, by decide⟩,⟨199731, by decide⟩,⟨199775, by decide⟩]) unmarked_context_11_5465_199776 node_context_11_5465_199776
  intro a
  fin_cases a
  · exact context_12_21860_199686
  · exact context_12_21861_126884
  · exact context_12_21862_199731
  · exact context_12_21863_199775

theorem selected_cut_06747 : selected 9 ⟨199819, by decide⟩
    (prefixPartial 12 21864) = some ⟨12, 2, 0, 199819, 21864, 3413, 65536⟩ := by
  decide +kernel

theorem context_12_21864_199819 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21864 ⟨199819, by decide⟩ :=
  accepted_of_selected 12 21864 ⟨199819, by decide⟩ ⟨12, 2, 0, 199819, 21864, 3413, 65536⟩
    (by decide) selected_cut_06747

theorem selected_cut_06748 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 87460) = some ⟨13, 1, 0, 3444, 87460, 1, 16384⟩ := by
  decide +kernel

theorem context_13_87460_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87460 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 87460 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 87460, 1, 16384⟩
    (by decide) selected_cut_06748

theorem selected_cut_06749 : selected 8 ⟨199833, by decide⟩
    (prefixPartial 13 87461) = some ⟨13, 2, 0, 199833, 87461, 749, 16384⟩ := by
  decide +kernel

theorem context_13_87461_199833 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87461 ⟨199833, by decide⟩ :=
  accepted_of_selected 13 87461 ⟨199833, by decide⟩ ⟨13, 2, 0, 199833, 87461, 749, 16384⟩
    (by decide) selected_cut_06749

theorem selected_cut_06750 : selected 8 ⟨199855, by decide⟩
    (prefixPartial 13 87462) = some ⟨13, 2, 0, 199855, 87462, 2249, 16384⟩ := by
  decide +kernel

theorem context_13_87462_199855 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87462 ⟨199855, by decide⟩ :=
  accepted_of_selected 13 87462 ⟨199855, by decide⟩ ⟨13, 2, 0, 199855, 87462, 2249, 16384⟩
    (by decide) selected_cut_06750

theorem selected_cut_06751 : selected 8 ⟨199868, by decide⟩
    (prefixPartial 13 87463) = some ⟨13, 2, 0, 199868, 87463, 1233, 16384⟩ := by
  decide +kernel

theorem context_13_87463_199868 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 87463 ⟨199868, by decide⟩ :=
  accepted_of_selected 13 87463 ⟨199868, by decide⟩ ⟨13, 2, 0, 199868, 87463, 1233, 16384⟩
    (by decide) selected_cut_06751

theorem unmarked_context_12_21865_199869 : frontier 9 ⟨199869, by decide⟩
    (prefixCache 12 21865) (prefixPartial 12 21865) = false := by
  decide +kernel

theorem node_context_12_21865_199869 : EJMOriginalGlobalDAGData.nodes 9 ⟨199869, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨199833, by decide⟩,⟨199855, by decide⟩,⟨199868, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21865_199869 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21865 ⟨199869, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21865
    ⟨199869, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨199833, by decide⟩,⟨199855, by decide⟩,⟨199868, by decide⟩]) unmarked_context_12_21865_199869 node_context_12_21865_199869
  intro a
  fin_cases a
  · exact context_13_87460_3444
  · exact context_13_87461_199833
  · exact context_13_87462_199855
  · exact context_13_87463_199868

theorem selected_cut_06752 : selected 9 ⟨199915, by decide⟩
    (prefixPartial 12 21866) = some ⟨12, 2, 0, 199915, 21866, 3401, 65536⟩ := by
  decide +kernel

theorem context_12_21866_199915 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21866 ⟨199915, by decide⟩ :=
  accepted_of_selected 12 21866 ⟨199915, by decide⟩ ⟨12, 2, 0, 199915, 21866, 3401, 65536⟩
    (by decide) selected_cut_06752

theorem selected_cut_06753 : selected 9 ⟨199961, by decide⟩
    (prefixPartial 12 21867) = some ⟨12, 2, 0, 199961, 21867, 3405, 65536⟩ := by
  decide +kernel

theorem context_12_21867_199961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21867 ⟨199961, by decide⟩ :=
  accepted_of_selected 12 21867 ⟨199961, by decide⟩ ⟨12, 2, 0, 199961, 21867, 3405, 65536⟩
    (by decide) selected_cut_06753

theorem unmarked_context_11_5466_199962 : frontier 10 ⟨199962, by decide⟩
    (prefixCache 11 5466) (prefixPartial 11 5466) = false := by
  decide +kernel

theorem node_context_11_5466_199962 : EJMOriginalGlobalDAGData.nodes 10 ⟨199962, by decide⟩ =
    .split (coordinate 11) (![⟨199819, by decide⟩,⟨199869, by decide⟩,⟨199915, by decide⟩,⟨199961, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5466_199962 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5466 ⟨199962, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5466
    ⟨199962, by decide⟩ (by decide) (![⟨199819, by decide⟩,⟨199869, by decide⟩,⟨199915, by decide⟩,⟨199961, by decide⟩]) unmarked_context_11_5466_199962 node_context_11_5466_199962
  intro a
  fin_cases a
  · exact context_12_21864_199819
  · exact context_12_21865_199869
  · exact context_12_21866_199915
  · exact context_12_21867_199961

theorem selected_cut_06754 : selected 9 ⟨199999, by decide⟩
    (prefixPartial 12 21868) = some ⟨12, 2, 0, 199999, 21868, 2977, 65536⟩ := by
  decide +kernel

theorem context_12_21868_199999 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21868 ⟨199999, by decide⟩ :=
  accepted_of_selected 12 21868 ⟨199999, by decide⟩ ⟨12, 2, 0, 199999, 21868, 2977, 65536⟩
    (by decide) selected_cut_06754

theorem selected_cut_06755 : selected 9 ⟨200045, by decide⟩
    (prefixPartial 12 21869) = some ⟨12, 2, 0, 200045, 21869, 3669, 65536⟩ := by
  decide +kernel

theorem context_12_21869_200045 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21869 ⟨200045, by decide⟩ :=
  accepted_of_selected 12 21869 ⟨200045, by decide⟩ ⟨12, 2, 0, 200045, 21869, 3669, 65536⟩
    (by decide) selected_cut_06755

theorem selected_cut_06756 : selected 9 ⟨200082, by decide⟩
    (prefixPartial 12 21870) = some ⟨12, 2, 0, 200082, 21870, 3013, 65536⟩ := by
  decide +kernel

theorem context_12_21870_200082 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21870 ⟨200082, by decide⟩ :=
  accepted_of_selected 12 21870 ⟨200082, by decide⟩ ⟨12, 2, 0, 200082, 21870, 3013, 65536⟩
    (by decide) selected_cut_06756

theorem selected_cut_06757 : selected 9 ⟨200116, by decide⟩
    (prefixPartial 12 21871) = some ⟨12, 2, 0, 200116, 21871, 2797, 65536⟩ := by
  decide +kernel

theorem context_12_21871_200116 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21871 ⟨200116, by decide⟩ :=
  accepted_of_selected 12 21871 ⟨200116, by decide⟩ ⟨12, 2, 0, 200116, 21871, 2797, 65536⟩
    (by decide) selected_cut_06757

theorem unmarked_context_11_5467_200117 : frontier 10 ⟨200117, by decide⟩
    (prefixCache 11 5467) (prefixPartial 11 5467) = false := by
  decide +kernel

theorem node_context_11_5467_200117 : EJMOriginalGlobalDAGData.nodes 10 ⟨200117, by decide⟩ =
    .split (coordinate 11) (![⟨199999, by decide⟩,⟨200045, by decide⟩,⟨200082, by decide⟩,⟨200116, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5467_200117 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5467 ⟨200117, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5467
    ⟨200117, by decide⟩ (by decide) (![⟨199999, by decide⟩,⟨200045, by decide⟩,⟨200082, by decide⟩,⟨200116, by decide⟩]) unmarked_context_11_5467_200117 node_context_11_5467_200117
  intro a
  fin_cases a
  · exact context_12_21868_199999
  · exact context_12_21869_200045
  · exact context_12_21870_200082
  · exact context_12_21871_200116

theorem unmarked_context_10_1366_200118 : frontier 11 ⟨200118, by decide⟩
    (prefixCache 10 1366) (prefixPartial 10 1366) = false := by
  decide +kernel

theorem node_context_10_1366_200118 : EJMOriginalGlobalDAGData.nodes 11 ⟨200118, by decide⟩ =
    .split (coordinate 10) (![⟨199643, by decide⟩,⟨199776, by decide⟩,⟨199962, by decide⟩,⟨200117, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1366_200118 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1366 ⟨200118, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1366
    ⟨200118, by decide⟩ (by decide) (![⟨199643, by decide⟩,⟨199776, by decide⟩,⟨199962, by decide⟩,⟨200117, by decide⟩]) unmarked_context_10_1366_200118 node_context_10_1366_200118
  intro a
  fin_cases a
  · exact context_11_5464_199643
  · exact context_11_5465_199776
  · exact context_11_5466_199962
  · exact context_11_5467_200117

theorem selected_cut_06758 : selected 11 ⟨3440, by decide⟩
    (prefixPartial 10 1367) = some ⟨10, 1, 0, 3440, 1367, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_1367_3440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1367 ⟨3440, by decide⟩ :=
  accepted_of_selected 10 1367 ⟨3440, by decide⟩ ⟨10, 1, 0, 3440, 1367, 1, 1048576⟩
    (by decide) selected_cut_06758

theorem unmarked_context_9_341_200119 : frontier 12 ⟨200119, by decide⟩
    (prefixCache 9 341) (prefixPartial 9 341) = false := by
  decide +kernel

theorem node_context_9_341_200119 : EJMOriginalGlobalDAGData.nodes 12 ⟨200119, by decide⟩ =
    .split (coordinate 9) (![⟨199081, by decide⟩,⟨199459, by decide⟩,⟨200118, by decide⟩,⟨3440, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_341_200119 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 341 ⟨200119, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 341
    ⟨200119, by decide⟩ (by decide) (![⟨199081, by decide⟩,⟨199459, by decide⟩,⟨200118, by decide⟩,⟨3440, by decide⟩]) unmarked_context_9_341_200119 node_context_9_341_200119
  intro a
  fin_cases a
  · exact context_10_1364_199081
  · exact context_10_1365_199459
  · exact context_10_1366_200118
  · exact context_10_1367_3440

theorem selected_cut_06759 : selected 9 ⟨200155, by decide⟩
    (prefixPartial 12 21888) = some ⟨12, 2, 0, 200155, 21888, 2897, 65536⟩ := by
  decide +kernel

theorem context_12_21888_200155 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21888 ⟨200155, by decide⟩ :=
  accepted_of_selected 12 21888 ⟨200155, by decide⟩ ⟨12, 2, 0, 200155, 21888, 2897, 65536⟩
    (by decide) selected_cut_06759

theorem selected_cut_06760 : selected 9 ⟨200187, by decide⟩
    (prefixPartial 12 21889) = some ⟨12, 2, 0, 200187, 21889, 2581, 65536⟩ := by
  decide +kernel

theorem context_12_21889_200187 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21889 ⟨200187, by decide⟩ :=
  accepted_of_selected 12 21889 ⟨200187, by decide⟩ ⟨12, 2, 0, 200187, 21889, 2581, 65536⟩
    (by decide) selected_cut_06760

theorem selected_cut_06761 : selected 9 ⟨200219, by decide⟩
    (prefixPartial 12 21890) = some ⟨12, 2, 0, 200219, 21890, 2965, 65536⟩ := by
  decide +kernel

theorem context_12_21890_200219 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21890 ⟨200219, by decide⟩ :=
  accepted_of_selected 12 21890 ⟨200219, by decide⟩ ⟨12, 2, 0, 200219, 21890, 2965, 65536⟩
    (by decide) selected_cut_06761

theorem selected_cut_06762 : selected 9 ⟨200263, by decide⟩
    (prefixPartial 12 21891) = some ⟨12, 2, 0, 200263, 21891, 3241, 65536⟩ := by
  decide +kernel

theorem context_12_21891_200263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21891 ⟨200263, by decide⟩ :=
  accepted_of_selected 12 21891 ⟨200263, by decide⟩ ⟨12, 2, 0, 200263, 21891, 3241, 65536⟩
    (by decide) selected_cut_06762

theorem unmarked_context_11_5472_200264 : frontier 10 ⟨200264, by decide⟩
    (prefixCache 11 5472) (prefixPartial 11 5472) = false := by
  decide +kernel

theorem node_context_11_5472_200264 : EJMOriginalGlobalDAGData.nodes 10 ⟨200264, by decide⟩ =
    .split (coordinate 11) (![⟨200155, by decide⟩,⟨200187, by decide⟩,⟨200219, by decide⟩,⟨200263, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5472_200264 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5472 ⟨200264, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5472
    ⟨200264, by decide⟩ (by decide) (![⟨200155, by decide⟩,⟨200187, by decide⟩,⟨200219, by decide⟩,⟨200263, by decide⟩]) unmarked_context_11_5472_200264 node_context_11_5472_200264
  intro a
  fin_cases a
  · exact context_12_21888_200155
  · exact context_12_21889_200187
  · exact context_12_21890_200219
  · exact context_12_21891_200263

theorem selected_cut_06763 : selected 9 ⟨200318, by decide⟩
    (prefixPartial 12 21892) = some ⟨12, 2, 0, 200318, 21892, 2197, 65536⟩ := by
  decide +kernel

theorem context_12_21892_200318 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21892 ⟨200318, by decide⟩ :=
  accepted_of_selected 12 21892 ⟨200318, by decide⟩ ⟨12, 2, 0, 200318, 21892, 2197, 65536⟩
    (by decide) selected_cut_06763

theorem selected_cut_06764 : selected 9 ⟨200363, by decide⟩
    (prefixPartial 12 21893) = some ⟨12, 2, 0, 200363, 21893, 3105, 65536⟩ := by
  decide +kernel

theorem context_12_21893_200363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21893 ⟨200363, by decide⟩ :=
  accepted_of_selected 12 21893 ⟨200363, by decide⟩ ⟨12, 2, 0, 200363, 21893, 3105, 65536⟩
    (by decide) selected_cut_06764

theorem selected_cut_06765 : selected 9 ⟨200401, by decide⟩
    (prefixPartial 12 21894) = some ⟨12, 2, 0, 200401, 21894, 2093, 65536⟩ := by
  decide +kernel

theorem context_12_21894_200401 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21894 ⟨200401, by decide⟩ :=
  accepted_of_selected 12 21894 ⟨200401, by decide⟩ ⟨12, 2, 0, 200401, 21894, 2093, 65536⟩
    (by decide) selected_cut_06765

theorem selected_cut_06766 : selected 9 ⟨200438, by decide⟩
    (prefixPartial 12 21895) = some ⟨12, 2, 0, 200438, 21895, 2309, 65536⟩ := by
  decide +kernel

theorem context_12_21895_200438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21895 ⟨200438, by decide⟩ :=
  accepted_of_selected 12 21895 ⟨200438, by decide⟩ ⟨12, 2, 0, 200438, 21895, 2309, 65536⟩
    (by decide) selected_cut_06766

theorem unmarked_context_11_5473_200439 : frontier 10 ⟨200439, by decide⟩
    (prefixCache 11 5473) (prefixPartial 11 5473) = false := by
  decide +kernel

theorem node_context_11_5473_200439 : EJMOriginalGlobalDAGData.nodes 10 ⟨200439, by decide⟩ =
    .split (coordinate 11) (![⟨200318, by decide⟩,⟨200363, by decide⟩,⟨200401, by decide⟩,⟨200438, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5473_200439 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5473 ⟨200439, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5473
    ⟨200439, by decide⟩ (by decide) (![⟨200318, by decide⟩,⟨200363, by decide⟩,⟨200401, by decide⟩,⟨200438, by decide⟩]) unmarked_context_11_5473_200439 node_context_11_5473_200439
  intro a
  fin_cases a
  · exact context_12_21892_200318
  · exact context_12_21893_200363
  · exact context_12_21894_200401
  · exact context_12_21895_200438

theorem selected_cut_06767 : selected 9 ⟨200487, by decide⟩
    (prefixPartial 12 21896) = some ⟨12, 2, 0, 200487, 21896, 2297, 65536⟩ := by
  decide +kernel

theorem context_12_21896_200487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21896 ⟨200487, by decide⟩ :=
  accepted_of_selected 12 21896 ⟨200487, by decide⟩ ⟨12, 2, 0, 200487, 21896, 2297, 65536⟩
    (by decide) selected_cut_06767

theorem selected_cut_06768 : selected 9 ⟨200521, by decide⟩
    (prefixPartial 12 21897) = some ⟨12, 2, 0, 200521, 21897, 1909, 65536⟩ := by
  decide +kernel

theorem context_12_21897_200521 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21897 ⟨200521, by decide⟩ :=
  accepted_of_selected 12 21897 ⟨200521, by decide⟩ ⟨12, 2, 0, 200521, 21897, 1909, 65536⟩
    (by decide) selected_cut_06768

theorem selected_cut_06769 : selected 9 ⟨200556, by decide⟩
    (prefixPartial 12 21898) = some ⟨12, 2, 0, 200556, 21898, 2033, 65536⟩ := by
  decide +kernel

theorem context_12_21898_200556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21898 ⟨200556, by decide⟩ :=
  accepted_of_selected 12 21898 ⟨200556, by decide⟩ ⟨12, 2, 0, 200556, 21898, 2033, 65536⟩
    (by decide) selected_cut_06769

theorem selected_cut_06770 : selected 9 ⟨200596, by decide⟩
    (prefixPartial 12 21899) = some ⟨12, 2, 0, 200596, 21899, 2333, 65536⟩ := by
  decide +kernel

theorem context_12_21899_200596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21899 ⟨200596, by decide⟩ :=
  accepted_of_selected 12 21899 ⟨200596, by decide⟩ ⟨12, 2, 0, 200596, 21899, 2333, 65536⟩
    (by decide) selected_cut_06770

theorem unmarked_context_11_5474_200597 : frontier 10 ⟨200597, by decide⟩
    (prefixCache 11 5474) (prefixPartial 11 5474) = false := by
  decide +kernel

theorem node_context_11_5474_200597 : EJMOriginalGlobalDAGData.nodes 10 ⟨200597, by decide⟩ =
    .split (coordinate 11) (![⟨200487, by decide⟩,⟨200521, by decide⟩,⟨200556, by decide⟩,⟨200596, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5474_200597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5474 ⟨200597, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5474
    ⟨200597, by decide⟩ (by decide) (![⟨200487, by decide⟩,⟨200521, by decide⟩,⟨200556, by decide⟩,⟨200596, by decide⟩]) unmarked_context_11_5474_200597 node_context_11_5474_200597
  intro a
  fin_cases a
  · exact context_12_21896_200487
  · exact context_12_21897_200521
  · exact context_12_21898_200556
  · exact context_12_21899_200596

theorem selected_cut_06771 : selected 9 ⟨200631, by decide⟩
    (prefixPartial 12 21900) = some ⟨12, 2, 0, 200631, 21900, 1937, 65536⟩ := by
  decide +kernel

theorem context_12_21900_200631 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21900 ⟨200631, by decide⟩ :=
  accepted_of_selected 12 21900 ⟨200631, by decide⟩ ⟨12, 2, 0, 200631, 21900, 1937, 65536⟩
    (by decide) selected_cut_06771

theorem selected_cut_06772 : selected 9 ⟨200657, by decide⟩
    (prefixPartial 12 21901) = some ⟨12, 2, 0, 200657, 21901, 1681, 65536⟩ := by
  decide +kernel

theorem context_12_21901_200657 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21901 ⟨200657, by decide⟩ :=
  accepted_of_selected 12 21901 ⟨200657, by decide⟩ ⟨12, 2, 0, 200657, 21901, 1681, 65536⟩
    (by decide) selected_cut_06772

theorem selected_cut_06773 : selected 9 ⟨200689, by decide⟩
    (prefixPartial 12 21902) = some ⟨12, 2, 0, 200689, 21902, 1961, 65536⟩ := by
  decide +kernel

theorem context_12_21902_200689 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21902 ⟨200689, by decide⟩ :=
  accepted_of_selected 12 21902 ⟨200689, by decide⟩ ⟨12, 2, 0, 200689, 21902, 1961, 65536⟩
    (by decide) selected_cut_06773

theorem selected_cut_06774 : selected 9 ⟨200717, by decide⟩
    (prefixPartial 12 21903) = some ⟨12, 2, 0, 200717, 21903, 1889, 65536⟩ := by
  decide +kernel

theorem context_12_21903_200717 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21903 ⟨200717, by decide⟩ :=
  accepted_of_selected 12 21903 ⟨200717, by decide⟩ ⟨12, 2, 0, 200717, 21903, 1889, 65536⟩
    (by decide) selected_cut_06774

theorem unmarked_context_11_5475_200718 : frontier 10 ⟨200718, by decide⟩
    (prefixCache 11 5475) (prefixPartial 11 5475) = false := by
  decide +kernel

theorem node_context_11_5475_200718 : EJMOriginalGlobalDAGData.nodes 10 ⟨200718, by decide⟩ =
    .split (coordinate 11) (![⟨200631, by decide⟩,⟨200657, by decide⟩,⟨200689, by decide⟩,⟨200717, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5475_200718 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5475 ⟨200718, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5475
    ⟨200718, by decide⟩ (by decide) (![⟨200631, by decide⟩,⟨200657, by decide⟩,⟨200689, by decide⟩,⟨200717, by decide⟩]) unmarked_context_11_5475_200718 node_context_11_5475_200718
  intro a
  fin_cases a
  · exact context_12_21900_200631
  · exact context_12_21901_200657
  · exact context_12_21902_200689
  · exact context_12_21903_200717

theorem unmarked_context_10_1368_200719 : frontier 11 ⟨200719, by decide⟩
    (prefixCache 10 1368) (prefixPartial 10 1368) = false := by
  decide +kernel

theorem node_context_10_1368_200719 : EJMOriginalGlobalDAGData.nodes 11 ⟨200719, by decide⟩ =
    .split (coordinate 10) (![⟨200264, by decide⟩,⟨200439, by decide⟩,⟨200597, by decide⟩,⟨200718, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1368_200719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1368 ⟨200719, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1368
    ⟨200719, by decide⟩ (by decide) (![⟨200264, by decide⟩,⟨200439, by decide⟩,⟨200597, by decide⟩,⟨200718, by decide⟩]) unmarked_context_10_1368_200719 node_context_10_1368_200719
  intro a
  fin_cases a
  · exact context_11_5472_200264
  · exact context_11_5473_200439
  · exact context_11_5474_200597
  · exact context_11_5475_200718

theorem selected_cut_06775 : selected 9 ⟨200743, by decide⟩
    (prefixPartial 12 21904) = some ⟨12, 2, 0, 200743, 21904, 1641, 65536⟩ := by
  decide +kernel

theorem context_12_21904_200743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21904 ⟨200743, by decide⟩ :=
  accepted_of_selected 12 21904 ⟨200743, by decide⟩ ⟨12, 2, 0, 200743, 21904, 1641, 65536⟩
    (by decide) selected_cut_06775

theorem selected_cut_06776 : selected 9 ⟨200766, by decide⟩
    (prefixPartial 12 21905) = some ⟨12, 2, 0, 200766, 21905, 1445, 65536⟩ := by
  decide +kernel

theorem context_12_21905_200766 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21905 ⟨200766, by decide⟩ :=
  accepted_of_selected 12 21905 ⟨200766, by decide⟩ ⟨12, 2, 0, 200766, 21905, 1445, 65536⟩
    (by decide) selected_cut_06776

theorem selected_cut_06777 : selected 9 ⟨200796, by decide⟩
    (prefixPartial 12 21906) = some ⟨12, 2, 0, 200796, 21906, 1753, 65536⟩ := by
  decide +kernel

theorem context_12_21906_200796 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21906 ⟨200796, by decide⟩ :=
  accepted_of_selected 12 21906 ⟨200796, by decide⟩ ⟨12, 2, 0, 200796, 21906, 1753, 65536⟩
    (by decide) selected_cut_06777

theorem selected_cut_06778 : selected 9 ⟨200831, by decide⟩
    (prefixPartial 12 21907) = some ⟨12, 2, 0, 200831, 21907, 1905, 65536⟩ := by
  decide +kernel

theorem context_12_21907_200831 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21907 ⟨200831, by decide⟩ :=
  accepted_of_selected 12 21907 ⟨200831, by decide⟩ ⟨12, 2, 0, 200831, 21907, 1905, 65536⟩
    (by decide) selected_cut_06778

theorem unmarked_context_11_5476_200832 : frontier 10 ⟨200832, by decide⟩
    (prefixCache 11 5476) (prefixPartial 11 5476) = false := by
  decide +kernel

theorem node_context_11_5476_200832 : EJMOriginalGlobalDAGData.nodes 10 ⟨200832, by decide⟩ =
    .split (coordinate 11) (![⟨200743, by decide⟩,⟨200766, by decide⟩,⟨200796, by decide⟩,⟨200831, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5476_200832 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5476 ⟨200832, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5476
    ⟨200832, by decide⟩ (by decide) (![⟨200743, by decide⟩,⟨200766, by decide⟩,⟨200796, by decide⟩,⟨200831, by decide⟩]) unmarked_context_11_5476_200832 node_context_11_5476_200832
  intro a
  fin_cases a
  · exact context_12_21904_200743
  · exact context_12_21905_200766
  · exact context_12_21906_200796
  · exact context_12_21907_200831

theorem selected_cut_06779 : selected 9 ⟨200857, by decide⟩
    (prefixPartial 12 21908) = some ⟨12, 2, 0, 200857, 21908, 1501, 65536⟩ := by
  decide +kernel

theorem context_12_21908_200857 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21908 ⟨200857, by decide⟩ :=
  accepted_of_selected 12 21908 ⟨200857, by decide⟩ ⟨12, 2, 0, 200857, 21908, 1501, 65536⟩
    (by decide) selected_cut_06779

theorem selected_cut_06780 : selected 9 ⟨124308, by decide⟩
    (prefixPartial 12 21909) = some ⟨12, 1, 0, 124308, 21909, 1, 65536⟩ := by
  decide +kernel

theorem context_12_21909_124308 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21909 ⟨124308, by decide⟩ :=
  accepted_of_selected 12 21909 ⟨124308, by decide⟩ ⟨12, 1, 0, 124308, 21909, 1, 65536⟩
    (by decide) selected_cut_06780

theorem selected_cut_06781 : selected 9 ⟨200881, by decide⟩
    (prefixPartial 12 21910) = some ⟨12, 2, 0, 200881, 21910, 1553, 65536⟩ := by
  decide +kernel

theorem context_12_21910_200881 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21910 ⟨200881, by decide⟩ :=
  accepted_of_selected 12 21910 ⟨200881, by decide⟩ ⟨12, 2, 0, 200881, 21910, 1553, 65536⟩
    (by decide) selected_cut_06781

theorem selected_cut_06782 : selected 9 ⟨200909, by decide⟩
    (prefixPartial 12 21911) = some ⟨12, 2, 0, 200909, 21911, 1653, 65536⟩ := by
  decide +kernel

theorem context_12_21911_200909 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21911 ⟨200909, by decide⟩ :=
  accepted_of_selected 12 21911 ⟨200909, by decide⟩ ⟨12, 2, 0, 200909, 21911, 1653, 65536⟩
    (by decide) selected_cut_06782

theorem unmarked_context_11_5477_200910 : frontier 10 ⟨200910, by decide⟩
    (prefixCache 11 5477) (prefixPartial 11 5477) = false := by
  decide +kernel

theorem node_context_11_5477_200910 : EJMOriginalGlobalDAGData.nodes 10 ⟨200910, by decide⟩ =
    .split (coordinate 11) (![⟨200857, by decide⟩,⟨124308, by decide⟩,⟨200881, by decide⟩,⟨200909, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5477_200910 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5477 ⟨200910, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5477
    ⟨200910, by decide⟩ (by decide) (![⟨200857, by decide⟩,⟨124308, by decide⟩,⟨200881, by decide⟩,⟨200909, by decide⟩]) unmarked_context_11_5477_200910 node_context_11_5477_200910
  intro a
  fin_cases a
  · exact context_12_21908_200857
  · exact context_12_21909_124308
  · exact context_12_21910_200881
  · exact context_12_21911_200909

theorem selected_cut_06783 : selected 9 ⟨200931, by decide⟩
    (prefixPartial 12 21912) = some ⟨12, 2, 0, 200931, 21912, 1229, 65536⟩ := by
  decide +kernel

theorem context_12_21912_200931 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21912 ⟨200931, by decide⟩ :=
  accepted_of_selected 12 21912 ⟨200931, by decide⟩ ⟨12, 2, 0, 200931, 21912, 1229, 65536⟩
    (by decide) selected_cut_06783

theorem selected_cut_06784 : selected 9 ⟨200950, by decide⟩
    (prefixPartial 12 21913) = some ⟨12, 2, 0, 200950, 21913, 1113, 65536⟩ := by
  decide +kernel

theorem context_12_21913_200950 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21913 ⟨200950, by decide⟩ :=
  accepted_of_selected 12 21913 ⟨200950, by decide⟩ ⟨12, 2, 0, 200950, 21913, 1113, 65536⟩
    (by decide) selected_cut_06784

theorem selected_cut_06785 : selected 9 ⟨200968, by decide⟩
    (prefixPartial 12 21914) = some ⟨12, 2, 0, 200968, 21914, 1133, 65536⟩ := by
  decide +kernel

theorem context_12_21914_200968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21914 ⟨200968, by decide⟩ :=
  accepted_of_selected 12 21914 ⟨200968, by decide⟩ ⟨12, 2, 0, 200968, 21914, 1133, 65536⟩
    (by decide) selected_cut_06785

theorem selected_cut_06786 : selected 9 ⟨200987, by decide⟩
    (prefixPartial 12 21915) = some ⟨12, 2, 0, 200987, 21915, 1217, 65536⟩ := by
  decide +kernel

theorem context_12_21915_200987 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21915 ⟨200987, by decide⟩ :=
  accepted_of_selected 12 21915 ⟨200987, by decide⟩ ⟨12, 2, 0, 200987, 21915, 1217, 65536⟩
    (by decide) selected_cut_06786

theorem unmarked_context_11_5478_200988 : frontier 10 ⟨200988, by decide⟩
    (prefixCache 11 5478) (prefixPartial 11 5478) = false := by
  decide +kernel

theorem node_context_11_5478_200988 : EJMOriginalGlobalDAGData.nodes 10 ⟨200988, by decide⟩ =
    .split (coordinate 11) (![⟨200931, by decide⟩,⟨200950, by decide⟩,⟨200968, by decide⟩,⟨200987, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5478_200988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5478 ⟨200988, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5478
    ⟨200988, by decide⟩ (by decide) (![⟨200931, by decide⟩,⟨200950, by decide⟩,⟨200968, by decide⟩,⟨200987, by decide⟩]) unmarked_context_11_5478_200988 node_context_11_5478_200988
  intro a
  fin_cases a
  · exact context_12_21912_200931
  · exact context_12_21913_200950
  · exact context_12_21914_200968
  · exact context_12_21915_200987

theorem selected_cut_06787 : selected 9 ⟨201007, by decide⟩
    (prefixPartial 12 21916) = some ⟨12, 2, 0, 201007, 21916, 1077, 65536⟩ := by
  decide +kernel

theorem context_12_21916_201007 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21916 ⟨201007, by decide⟩ :=
  accepted_of_selected 12 21916 ⟨201007, by decide⟩ ⟨12, 2, 0, 201007, 21916, 1077, 65536⟩
    (by decide) selected_cut_06787

theorem selected_cut_06788 : selected 9 ⟨201024, by decide⟩
    (prefixPartial 12 21917) = some ⟨12, 2, 0, 201024, 21917, 997, 65536⟩ := by
  decide +kernel

theorem context_12_21917_201024 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21917 ⟨201024, by decide⟩ :=
  accepted_of_selected 12 21917 ⟨201024, by decide⟩ ⟨12, 2, 0, 201024, 21917, 997, 65536⟩
    (by decide) selected_cut_06788

theorem selected_cut_06789 : selected 9 ⟨201041, by decide⟩
    (prefixPartial 12 21918) = some ⟨12, 2, 0, 201041, 21918, 1073, 65536⟩ := by
  decide +kernel

theorem context_12_21918_201041 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21918 ⟨201041, by decide⟩ :=
  accepted_of_selected 12 21918 ⟨201041, by decide⟩ ⟨12, 2, 0, 201041, 21918, 1073, 65536⟩
    (by decide) selected_cut_06789

theorem selected_cut_06790 : selected 9 ⟨201058, by decide⟩
    (prefixPartial 12 21919) = some ⟨12, 2, 0, 201058, 21919, 1069, 65536⟩ := by
  decide +kernel

theorem context_12_21919_201058 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21919 ⟨201058, by decide⟩ :=
  accepted_of_selected 12 21919 ⟨201058, by decide⟩ ⟨12, 2, 0, 201058, 21919, 1069, 65536⟩
    (by decide) selected_cut_06790

theorem unmarked_context_11_5479_201059 : frontier 10 ⟨201059, by decide⟩
    (prefixCache 11 5479) (prefixPartial 11 5479) = false := by
  decide +kernel

theorem node_context_11_5479_201059 : EJMOriginalGlobalDAGData.nodes 10 ⟨201059, by decide⟩ =
    .split (coordinate 11) (![⟨201007, by decide⟩,⟨201024, by decide⟩,⟨201041, by decide⟩,⟨201058, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5479_201059 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5479 ⟨201059, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5479
    ⟨201059, by decide⟩ (by decide) (![⟨201007, by decide⟩,⟨201024, by decide⟩,⟨201041, by decide⟩,⟨201058, by decide⟩]) unmarked_context_11_5479_201059 node_context_11_5479_201059
  intro a
  fin_cases a
  · exact context_12_21916_201007
  · exact context_12_21917_201024
  · exact context_12_21918_201041
  · exact context_12_21919_201058

theorem unmarked_context_10_1369_201060 : frontier 11 ⟨201060, by decide⟩
    (prefixCache 10 1369) (prefixPartial 10 1369) = false := by
  decide +kernel

theorem node_context_10_1369_201060 : EJMOriginalGlobalDAGData.nodes 11 ⟨201060, by decide⟩ =
    .split (coordinate 10) (![⟨200832, by decide⟩,⟨200910, by decide⟩,⟨200988, by decide⟩,⟨201059, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1369_201060 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1369 ⟨201060, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1369
    ⟨201060, by decide⟩ (by decide) (![⟨200832, by decide⟩,⟨200910, by decide⟩,⟨200988, by decide⟩,⟨201059, by decide⟩]) unmarked_context_10_1369_201060 node_context_10_1369_201060
  intro a
  fin_cases a
  · exact context_11_5476_200832
  · exact context_11_5477_200910
  · exact context_11_5478_200988
  · exact context_11_5479_201059

theorem selected_cut_06791 : selected 10 ⟨201121, by decide⟩
    (prefixPartial 11 5480) = some ⟨11, 2, 0, 201121, 5480, 4089, 262144⟩ := by
  decide +kernel

theorem context_11_5480_201121 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5480 ⟨201121, by decide⟩ :=
  accepted_of_selected 11 5480 ⟨201121, by decide⟩ ⟨11, 2, 0, 201121, 5480, 4089, 262144⟩
    (by decide) selected_cut_06791

theorem selected_cut_06792 : selected 10 ⟨201172, by decide⟩
    (prefixPartial 11 5481) = some ⟨11, 2, 0, 201172, 5481, 3209, 262144⟩ := by
  decide +kernel

theorem context_11_5481_201172 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5481 ⟨201172, by decide⟩ :=
  accepted_of_selected 11 5481 ⟨201172, by decide⟩ ⟨11, 2, 0, 201172, 5481, 3209, 262144⟩
    (by decide) selected_cut_06792

theorem selected_cut_06793 : selected 10 ⟨201221, by decide⟩
    (prefixPartial 11 5482) = some ⟨11, 2, 0, 201221, 5482, 2569, 262144⟩ := by
  decide +kernel

theorem context_11_5482_201221 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5482 ⟨201221, by decide⟩ :=
  accepted_of_selected 11 5482 ⟨201221, by decide⟩ ⟨11, 2, 0, 201221, 5482, 2569, 262144⟩
    (by decide) selected_cut_06793

theorem selected_cut_06794 : selected 10 ⟨201263, by decide⟩
    (prefixPartial 11 5483) = some ⟨11, 2, 0, 201263, 5483, 2133, 262144⟩ := by
  decide +kernel

theorem context_11_5483_201263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5483 ⟨201263, by decide⟩ :=
  accepted_of_selected 11 5483 ⟨201263, by decide⟩ ⟨11, 2, 0, 201263, 5483, 2133, 262144⟩
    (by decide) selected_cut_06794

theorem unmarked_context_10_1370_201264 : frontier 11 ⟨201264, by decide⟩
    (prefixCache 10 1370) (prefixPartial 10 1370) = false := by
  decide +kernel

theorem node_context_10_1370_201264 : EJMOriginalGlobalDAGData.nodes 11 ⟨201264, by decide⟩ =
    .split (coordinate 10) (![⟨201121, by decide⟩,⟨201172, by decide⟩,⟨201221, by decide⟩,⟨201263, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1370_201264 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1370 ⟨201264, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1370
    ⟨201264, by decide⟩ (by decide) (![⟨201121, by decide⟩,⟨201172, by decide⟩,⟨201221, by decide⟩,⟨201263, by decide⟩]) unmarked_context_10_1370_201264 node_context_10_1370_201264
  intro a
  fin_cases a
  · exact context_11_5480_201121
  · exact context_11_5481_201172
  · exact context_11_5482_201221
  · exact context_11_5483_201263

theorem selected_cut_06795 : selected 10 ⟨201296, by decide⟩
    (prefixPartial 11 5484) = some ⟨11, 2, 0, 201296, 5484, 1889, 262144⟩ := by
  decide +kernel

theorem context_11_5484_201296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5484 ⟨201296, by decide⟩ :=
  accepted_of_selected 11 5484 ⟨201296, by decide⟩ ⟨11, 2, 0, 201296, 5484, 1889, 262144⟩
    (by decide) selected_cut_06795

theorem selected_cut_06796 : selected 10 ⟨201321, by decide⟩
    (prefixPartial 11 5485) = some ⟨11, 2, 0, 201321, 5485, 1257, 262144⟩ := by
  decide +kernel

theorem context_11_5485_201321 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5485 ⟨201321, by decide⟩ :=
  accepted_of_selected 11 5485 ⟨201321, by decide⟩ ⟨11, 2, 0, 201321, 5485, 1257, 262144⟩
    (by decide) selected_cut_06796

theorem selected_cut_06797 : selected 10 ⟨201346, by decide⟩
    (prefixPartial 11 5486) = some ⟨11, 2, 0, 201346, 5486, 769, 262144⟩ := by
  decide +kernel

theorem context_11_5486_201346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5486 ⟨201346, by decide⟩ :=
  accepted_of_selected 11 5486 ⟨201346, by decide⟩ ⟨11, 2, 0, 201346, 5486, 769, 262144⟩
    (by decide) selected_cut_06797

theorem selected_cut_06798 : selected 10 ⟨201355, by decide⟩
    (prefixPartial 11 5487) = some ⟨11, 2, 0, 201355, 5487, 341, 262144⟩ := by
  decide +kernel

theorem context_11_5487_201355 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5487 ⟨201355, by decide⟩ :=
  accepted_of_selected 11 5487 ⟨201355, by decide⟩ ⟨11, 2, 0, 201355, 5487, 341, 262144⟩
    (by decide) selected_cut_06798

theorem unmarked_context_10_1371_201356 : frontier 11 ⟨201356, by decide⟩
    (prefixCache 10 1371) (prefixPartial 10 1371) = false := by
  decide +kernel

theorem node_context_10_1371_201356 : EJMOriginalGlobalDAGData.nodes 11 ⟨201356, by decide⟩ =
    .split (coordinate 10) (![⟨201296, by decide⟩,⟨201321, by decide⟩,⟨201346, by decide⟩,⟨201355, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1371_201356 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1371 ⟨201356, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1371
    ⟨201356, by decide⟩ (by decide) (![⟨201296, by decide⟩,⟨201321, by decide⟩,⟨201346, by decide⟩,⟨201355, by decide⟩]) unmarked_context_10_1371_201356 node_context_10_1371_201356
  intro a
  fin_cases a
  · exact context_11_5484_201296
  · exact context_11_5485_201321
  · exact context_11_5486_201346
  · exact context_11_5487_201355

theorem unmarked_context_9_342_201357 : frontier 12 ⟨201357, by decide⟩
    (prefixCache 9 342) (prefixPartial 9 342) = false := by
  decide +kernel

theorem node_context_9_342_201357 : EJMOriginalGlobalDAGData.nodes 12 ⟨201357, by decide⟩ =
    .split (coordinate 9) (![⟨200719, by decide⟩,⟨201060, by decide⟩,⟨201264, by decide⟩,⟨201356, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_342_201357 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 342 ⟨201357, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 342
    ⟨201357, by decide⟩ (by decide) (![⟨200719, by decide⟩,⟨201060, by decide⟩,⟨201264, by decide⟩,⟨201356, by decide⟩]) unmarked_context_9_342_201357 node_context_9_342_201357
  intro a
  fin_cases a
  · exact context_10_1368_200719
  · exact context_10_1369_201060
  · exact context_10_1370_201264
  · exact context_10_1371_201356

theorem selected_cut_06799 : selected 12 ⟨4601, by decide⟩
    (prefixPartial 9 343) = some ⟨9, 1, 0, 4601, 343, 1, 4194304⟩ := by
  decide +kernel

theorem context_9_343_4601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 343 ⟨4601, by decide⟩ :=
  accepted_of_selected 9 343 ⟨4601, by decide⟩ ⟨9, 1, 0, 4601, 343, 1, 4194304⟩
    (by decide) selected_cut_06799

theorem unmarked_context_8_85_201358 : frontier 13 ⟨201358, by decide⟩
    (prefixCache 8 85) (prefixPartial 8 85) = false := by
  decide +kernel

theorem node_context_8_85_201358 : EJMOriginalGlobalDAGData.nodes 13 ⟨201358, by decide⟩ =
    .split (coordinate 8) (![⟨198565, by decide⟩,⟨200119, by decide⟩,⟨201357, by decide⟩,⟨4601, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_85_201358 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 85 ⟨201358, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 85
    ⟨201358, by decide⟩ (by decide) (![⟨198565, by decide⟩,⟨200119, by decide⟩,⟨201357, by decide⟩,⟨4601, by decide⟩]) unmarked_context_8_85_201358 node_context_8_85_201358
  intro a
  fin_cases a
  · exact context_9_340_198565
  · exact context_9_341_200119
  · exact context_9_342_201357
  · exact context_9_343_4601

theorem selected_cut_06800 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 22016) = some ⟨12, 1, 0, 34034, 22016, 1, 65536⟩ := by
  decide +kernel

theorem context_12_22016_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22016 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 22016 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 22016, 1, 65536⟩
    (by decide) selected_cut_06800

theorem selected_cut_06801 : selected 8 ⟨201438, by decide⟩
    (prefixPartial 13 88068) = some ⟨13, 2, 0, 201438, 88068, 3065, 16384⟩ := by
  decide +kernel

theorem context_13_88068_201438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88068 ⟨201438, by decide⟩ :=
  accepted_of_selected 13 88068 ⟨201438, by decide⟩ ⟨13, 2, 0, 201438, 88068, 3065, 16384⟩
    (by decide) selected_cut_06801

theorem selected_cut_06802 : selected 8 ⟨201496, by decide⟩
    (prefixPartial 13 88069) = some ⟨13, 2, 0, 201496, 88069, 1737, 16384⟩ := by
  decide +kernel

theorem context_13_88069_201496 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88069 ⟨201496, by decide⟩ :=
  accepted_of_selected 13 88069 ⟨201496, by decide⟩ ⟨13, 2, 0, 201496, 88069, 1737, 16384⟩
    (by decide) selected_cut_06802

theorem selected_cut_06803 : selected 8 ⟨201521, by decide⟩
    (prefixPartial 13 88070) = some ⟨13, 2, 0, 201521, 88070, 593, 16384⟩ := by
  decide +kernel

theorem context_13_88070_201521 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88070 ⟨201521, by decide⟩ :=
  accepted_of_selected 13 88070 ⟨201521, by decide⟩ ⟨13, 2, 0, 201521, 88070, 593, 16384⟩
    (by decide) selected_cut_06803

theorem selected_cut_06804 : selected 8 ⟨201525, by decide⟩
    (prefixPartial 13 88071) = some ⟨13, 2, 0, 201525, 88071, 149, 16384⟩ := by
  decide +kernel

theorem context_13_88071_201525 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88071 ⟨201525, by decide⟩ :=
  accepted_of_selected 13 88071 ⟨201525, by decide⟩ ⟨13, 2, 0, 201525, 88071, 149, 16384⟩
    (by decide) selected_cut_06804

theorem unmarked_context_12_22017_201526 : frontier 9 ⟨201526, by decide⟩
    (prefixCache 12 22017) (prefixPartial 12 22017) = false := by
  decide +kernel

theorem node_context_12_22017_201526 : EJMOriginalGlobalDAGData.nodes 9 ⟨201526, by decide⟩ =
    .split (coordinate 12) (![⟨201438, by decide⟩,⟨201496, by decide⟩,⟨201521, by decide⟩,⟨201525, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22017_201526 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22017 ⟨201526, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22017
    ⟨201526, by decide⟩ (by decide) (![⟨201438, by decide⟩,⟨201496, by decide⟩,⟨201521, by decide⟩,⟨201525, by decide⟩]) unmarked_context_12_22017_201526 node_context_12_22017_201526
  intro a
  fin_cases a
  · exact context_13_88068_201438
  · exact context_13_88069_201496
  · exact context_13_88070_201521
  · exact context_13_88071_201525

theorem selected_cut_06805 : selected 8 ⟨201585, by decide⟩
    (prefixPartial 13 88072) = some ⟨13, 2, 0, 201585, 88072, 3989, 16384⟩ := by
  decide +kernel

theorem context_13_88072_201585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88072 ⟨201585, by decide⟩ :=
  accepted_of_selected 13 88072 ⟨201585, by decide⟩ ⟨13, 2, 0, 201585, 88072, 3989, 16384⟩
    (by decide) selected_cut_06805

theorem selected_cut_06806 : selected 8 ⟨201629, by decide⟩
    (prefixPartial 13 88073) = some ⟨13, 2, 0, 201629, 88073, 3733, 16384⟩ := by
  decide +kernel

theorem context_13_88073_201629 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88073 ⟨201629, by decide⟩ :=
  accepted_of_selected 13 88073 ⟨201629, by decide⟩ ⟨13, 2, 0, 201629, 88073, 3733, 16384⟩
    (by decide) selected_cut_06806

theorem selected_cut_06807 : selected 8 ⟨201647, by decide⟩
    (prefixPartial 13 88074) = some ⟨13, 2, 0, 201647, 88074, 1857, 16384⟩ := by
  decide +kernel

theorem context_13_88074_201647 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88074 ⟨201647, by decide⟩ :=
  accepted_of_selected 13 88074 ⟨201647, by decide⟩ ⟨13, 2, 0, 201647, 88074, 1857, 16384⟩
    (by decide) selected_cut_06807

theorem selected_cut_06808 : selected 8 ⟨201660, by decide⟩
    (prefixPartial 13 88075) = some ⟨13, 2, 0, 201660, 88075, 1261, 16384⟩ := by
  decide +kernel

theorem context_13_88075_201660 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88075 ⟨201660, by decide⟩ :=
  accepted_of_selected 13 88075 ⟨201660, by decide⟩ ⟨13, 2, 0, 201660, 88075, 1261, 16384⟩
    (by decide) selected_cut_06808

theorem unmarked_context_12_22018_201661 : frontier 9 ⟨201661, by decide⟩
    (prefixCache 12 22018) (prefixPartial 12 22018) = false := by
  decide +kernel

theorem node_context_12_22018_201661 : EJMOriginalGlobalDAGData.nodes 9 ⟨201661, by decide⟩ =
    .split (coordinate 12) (![⟨201585, by decide⟩,⟨201629, by decide⟩,⟨201647, by decide⟩,⟨201660, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22018_201661 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22018 ⟨201661, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22018
    ⟨201661, by decide⟩ (by decide) (![⟨201585, by decide⟩,⟨201629, by decide⟩,⟨201647, by decide⟩,⟨201660, by decide⟩]) unmarked_context_12_22018_201661 node_context_12_22018_201661
  intro a
  fin_cases a
  · exact context_13_88072_201585
  · exact context_13_88073_201629
  · exact context_13_88074_201647
  · exact context_13_88075_201660

theorem selected_cut_06809 : selected 7 ⟨201686, by decide⟩
    (prefixPartial 14 352304) = some ⟨14, 2, 0, 201686, 352304, 1393, 4096⟩ := by
  decide +kernel

theorem context_14_352304_201686 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 352304 ⟨201686, by decide⟩ :=
  accepted_of_selected 14 352304 ⟨201686, by decide⟩ ⟨14, 2, 0, 201686, 352304, 1393, 4096⟩
    (by decide) selected_cut_06809

theorem selected_cut_06810 : selected 7 ⟨201697, by decide⟩
    (prefixPartial 14 352305) = some ⟨14, 2, 0, 201697, 352305, 949, 4096⟩ := by
  decide +kernel

theorem context_14_352305_201697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 352305 ⟨201697, by decide⟩ :=
  accepted_of_selected 14 352305 ⟨201697, by decide⟩ ⟨14, 2, 0, 201697, 352305, 949, 4096⟩
    (by decide) selected_cut_06810

theorem selected_cut_06811 : selected 7 ⟨201706, by decide⟩
    (prefixPartial 14 352306) = some ⟨14, 2, 0, 201706, 352306, 917, 4096⟩ := by
  decide +kernel

theorem context_14_352306_201706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 352306 ⟨201706, by decide⟩ :=
  accepted_of_selected 14 352306 ⟨201706, by decide⟩ ⟨14, 2, 0, 201706, 352306, 917, 4096⟩
    (by decide) selected_cut_06811

theorem selected_cut_06812 : selected 7 ⟨201719, by decide⟩
    (prefixPartial 14 352307) = some ⟨14, 2, 0, 201719, 352307, 1053, 4096⟩ := by
  decide +kernel

theorem context_14_352307_201719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 352307 ⟨201719, by decide⟩ :=
  accepted_of_selected 14 352307 ⟨201719, by decide⟩ ⟨14, 2, 0, 201719, 352307, 1053, 4096⟩
    (by decide) selected_cut_06812

theorem unmarked_context_13_88076_201720 : frontier 8 ⟨201720, by decide⟩
    (prefixCache 13 88076) (prefixPartial 13 88076) = false := by
  decide +kernel

theorem node_context_13_88076_201720 : EJMOriginalGlobalDAGData.nodes 8 ⟨201720, by decide⟩ =
    .split (coordinate 13) (![⟨201686, by decide⟩,⟨201697, by decide⟩,⟨201706, by decide⟩,⟨201719, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_88076_201720 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88076 ⟨201720, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 88076
    ⟨201720, by decide⟩ (by decide) (![⟨201686, by decide⟩,⟨201697, by decide⟩,⟨201706, by decide⟩,⟨201719, by decide⟩]) unmarked_context_13_88076_201720 node_context_13_88076_201720
  intro a
  fin_cases a
  · exact context_14_352304_201686
  · exact context_14_352305_201697
  · exact context_14_352306_201706
  · exact context_14_352307_201719

theorem selected_cut_06813 : selected 7 ⟨201736, by decide⟩
    (prefixPartial 14 352308) = some ⟨14, 2, 0, 201736, 352308, 1065, 4096⟩ := by
  decide +kernel

theorem context_14_352308_201736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 352308 ⟨201736, by decide⟩ :=
  accepted_of_selected 14 352308 ⟨201736, by decide⟩ ⟨14, 2, 0, 201736, 352308, 1065, 4096⟩
    (by decide) selected_cut_06813

theorem selected_cut_06814 : selected 7 ⟨201756, by decide⟩
    (prefixPartial 14 352309) = some ⟨14, 2, 0, 201756, 352309, 1085, 4096⟩ := by
  decide +kernel

theorem context_14_352309_201756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 352309 ⟨201756, by decide⟩ :=
  accepted_of_selected 14 352309 ⟨201756, by decide⟩ ⟨14, 2, 0, 201756, 352309, 1085, 4096⟩
    (by decide) selected_cut_06814

theorem selected_cut_06815 : selected 7 ⟨201770, by decide⟩
    (prefixPartial 14 352310) = some ⟨14, 2, 0, 201770, 352310, 1037, 4096⟩ := by
  decide +kernel

theorem context_14_352310_201770 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 352310 ⟨201770, by decide⟩ :=
  accepted_of_selected 14 352310 ⟨201770, by decide⟩ ⟨14, 2, 0, 201770, 352310, 1037, 4096⟩
    (by decide) selected_cut_06815

theorem selected_cut_06816 : selected 7 ⟨201782, by decide⟩
    (prefixPartial 14 352311) = some ⟨14, 2, 0, 201782, 352311, 965, 4096⟩ := by
  decide +kernel

theorem context_14_352311_201782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 352311 ⟨201782, by decide⟩ :=
  accepted_of_selected 14 352311 ⟨201782, by decide⟩ ⟨14, 2, 0, 201782, 352311, 965, 4096⟩
    (by decide) selected_cut_06816

theorem unmarked_context_13_88077_201783 : frontier 8 ⟨201783, by decide⟩
    (prefixCache 13 88077) (prefixPartial 13 88077) = false := by
  decide +kernel

theorem node_context_13_88077_201783 : EJMOriginalGlobalDAGData.nodes 8 ⟨201783, by decide⟩ =
    .split (coordinate 13) (![⟨201736, by decide⟩,⟨201756, by decide⟩,⟨201770, by decide⟩,⟨201782, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_88077_201783 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88077 ⟨201783, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 88077
    ⟨201783, by decide⟩ (by decide) (![⟨201736, by decide⟩,⟨201756, by decide⟩,⟨201770, by decide⟩,⟨201782, by decide⟩]) unmarked_context_13_88077_201783 node_context_13_88077_201783
  intro a
  fin_cases a
  · exact context_14_352308_201736
  · exact context_14_352309_201756
  · exact context_14_352310_201770
  · exact context_14_352311_201782

theorem selected_cut_06817 : selected 8 ⟨201810, by decide⟩
    (prefixPartial 13 88078) = some ⟨13, 2, 0, 201810, 88078, 2109, 16384⟩ := by
  decide +kernel

theorem context_13_88078_201810 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88078 ⟨201810, by decide⟩ :=
  accepted_of_selected 13 88078 ⟨201810, by decide⟩ ⟨13, 2, 0, 201810, 88078, 2109, 16384⟩
    (by decide) selected_cut_06817

theorem selected_cut_06818 : selected 8 ⟨201819, by decide⟩
    (prefixPartial 13 88079) = some ⟨13, 2, 0, 201819, 88079, 1125, 16384⟩ := by
  decide +kernel

theorem context_13_88079_201819 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 88079 ⟨201819, by decide⟩ :=
  accepted_of_selected 13 88079 ⟨201819, by decide⟩ ⟨13, 2, 0, 201819, 88079, 1125, 16384⟩
    (by decide) selected_cut_06818

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
