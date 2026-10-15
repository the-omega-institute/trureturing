/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover028
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_11_1455_86071 : frontier 10 ⟨86071, by decide⟩
    (prefixCache 11 1455) (prefixPartial 11 1455) = false := by
  decide +kernel

theorem node_context_11_1455_86071 : EJMOriginalGlobalDAGData.nodes 10 ⟨86071, by decide⟩ =
    .split (coordinate 11) (![⟨86033, by decide⟩,⟨86049, by decide⟩,⟨86058, by decide⟩,⟨86070, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1455_86071 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1455 ⟨86071, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1455
    ⟨86071, by decide⟩ (by decide) (![⟨86033, by decide⟩,⟨86049, by decide⟩,⟨86058, by decide⟩,⟨86070, by decide⟩]) unmarked_context_11_1455_86071 node_context_11_1455_86071
  intro a
  fin_cases a
  · exact context_12_5820_86033
  · exact context_12_5821_86049
  · exact context_12_5822_86058
  · exact context_12_5823_86070

theorem unmarked_context_10_363_86072 : frontier 11 ⟨86072, by decide⟩
    (prefixCache 10 363) (prefixPartial 10 363) = false := by
  decide +kernel

theorem node_context_10_363_86072 : EJMOriginalGlobalDAGData.nodes 11 ⟨86072, by decide⟩ =
    .split (coordinate 10) (![⟨85845, by decide⟩,⟨85921, by decide⟩,⟨86019, by decide⟩,⟨86071, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_363_86072 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 363 ⟨86072, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 363
    ⟨86072, by decide⟩ (by decide) (![⟨85845, by decide⟩,⟨85921, by decide⟩,⟨86019, by decide⟩,⟨86071, by decide⟩]) unmarked_context_10_363_86072 node_context_10_363_86072
  intro a
  fin_cases a
  · exact context_11_1452_85845
  · exact context_11_1453_85921
  · exact context_11_1454_86019
  · exact context_11_1455_86071

theorem unmarked_context_9_90_86073 : frontier 12 ⟨86073, by decide⟩
    (prefixCache 9 90) (prefixPartial 9 90) = false := by
  decide +kernel

theorem node_context_9_90_86073 : EJMOriginalGlobalDAGData.nodes 12 ⟨86073, by decide⟩ =
    .split (coordinate 9) (![⟨84710, by decide⟩,⟨85389, by decide⟩,⟨85757, by decide⟩,⟨86072, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_90_86073 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 90 ⟨86073, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 90
    ⟨86073, by decide⟩ (by decide) (![⟨84710, by decide⟩,⟨85389, by decide⟩,⟨85757, by decide⟩,⟨86072, by decide⟩]) unmarked_context_9_90_86073 node_context_9_90_86073
  intro a
  fin_cases a
  · exact context_10_360_84710
  · exact context_10_361_85389
  · exact context_10_362_85757
  · exact context_10_363_86072

theorem selected_cut_02788 : selected 9 ⟨86085, by decide⟩
    (prefixPartial 12 5824) = some ⟨12, 2, 0, 86085, 5824, 1073, 65536⟩ := by
  decide +kernel

theorem context_12_5824_86085 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5824 ⟨86085, by decide⟩ :=
  accepted_of_selected 12 5824 ⟨86085, by decide⟩ ⟨12, 2, 0, 86085, 5824, 1073, 65536⟩
    (by decide) selected_cut_02788

theorem selected_cut_02789 : selected 9 ⟨86098, by decide⟩
    (prefixPartial 12 5825) = some ⟨12, 2, 0, 86098, 5825, 1273, 65536⟩ := by
  decide +kernel

theorem context_12_5825_86098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5825 ⟨86098, by decide⟩ :=
  accepted_of_selected 12 5825 ⟨86098, by decide⟩ ⟨12, 2, 0, 86098, 5825, 1273, 65536⟩
    (by decide) selected_cut_02789

theorem selected_cut_02790 : selected 9 ⟨86114, by decide⟩
    (prefixPartial 12 5826) = some ⟨12, 2, 0, 86114, 5826, 1233, 65536⟩ := by
  decide +kernel

theorem context_12_5826_86114 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5826 ⟨86114, by decide⟩ :=
  accepted_of_selected 12 5826 ⟨86114, by decide⟩ ⟨12, 2, 0, 86114, 5826, 1233, 65536⟩
    (by decide) selected_cut_02790

theorem selected_cut_02791 : selected 9 ⟨86126, by decide⟩
    (prefixPartial 12 5827) = some ⟨12, 2, 0, 86126, 5827, 1165, 65536⟩ := by
  decide +kernel

theorem context_12_5827_86126 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5827 ⟨86126, by decide⟩ :=
  accepted_of_selected 12 5827 ⟨86126, by decide⟩ ⟨12, 2, 0, 86126, 5827, 1165, 65536⟩
    (by decide) selected_cut_02791

theorem unmarked_context_11_1456_86127 : frontier 10 ⟨86127, by decide⟩
    (prefixCache 11 1456) (prefixPartial 11 1456) = false := by
  decide +kernel

theorem node_context_11_1456_86127 : EJMOriginalGlobalDAGData.nodes 10 ⟨86127, by decide⟩ =
    .split (coordinate 11) (![⟨86085, by decide⟩,⟨86098, by decide⟩,⟨86114, by decide⟩,⟨86126, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1456_86127 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1456 ⟨86127, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1456
    ⟨86127, by decide⟩ (by decide) (![⟨86085, by decide⟩,⟨86098, by decide⟩,⟨86114, by decide⟩,⟨86126, by decide⟩]) unmarked_context_11_1456_86127 node_context_11_1456_86127
  intro a
  fin_cases a
  · exact context_12_5824_86085
  · exact context_12_5825_86098
  · exact context_12_5826_86114
  · exact context_12_5827_86126

theorem selected_cut_02792 : selected 9 ⟨86138, by decide⟩
    (prefixPartial 12 5828) = some ⟨12, 2, 0, 86138, 5828, 941, 65536⟩ := by
  decide +kernel

theorem context_12_5828_86138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5828 ⟨86138, by decide⟩ :=
  accepted_of_selected 12 5828 ⟨86138, by decide⟩ ⟨12, 2, 0, 86138, 5828, 941, 65536⟩
    (by decide) selected_cut_02792

theorem selected_cut_02793 : selected 9 ⟨86146, by decide⟩
    (prefixPartial 12 5829) = some ⟨12, 2, 0, 86146, 5829, 1065, 65536⟩ := by
  decide +kernel

theorem context_12_5829_86146 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5829 ⟨86146, by decide⟩ :=
  accepted_of_selected 12 5829 ⟨86146, by decide⟩ ⟨12, 2, 0, 86146, 5829, 1065, 65536⟩
    (by decide) selected_cut_02793

theorem selected_cut_02794 : selected 9 ⟨86161, by decide⟩
    (prefixPartial 12 5830) = some ⟨12, 2, 0, 86161, 5830, 1097, 65536⟩ := by
  decide +kernel

theorem context_12_5830_86161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5830 ⟨86161, by decide⟩ :=
  accepted_of_selected 12 5830 ⟨86161, by decide⟩ ⟨12, 2, 0, 86161, 5830, 1097, 65536⟩
    (by decide) selected_cut_02794

theorem selected_cut_02795 : selected 9 ⟨86174, by decide⟩
    (prefixPartial 12 5831) = some ⟨12, 2, 0, 86174, 5831, 1029, 65536⟩ := by
  decide +kernel

theorem context_12_5831_86174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5831 ⟨86174, by decide⟩ :=
  accepted_of_selected 12 5831 ⟨86174, by decide⟩ ⟨12, 2, 0, 86174, 5831, 1029, 65536⟩
    (by decide) selected_cut_02795

theorem unmarked_context_11_1457_86175 : frontier 10 ⟨86175, by decide⟩
    (prefixCache 11 1457) (prefixPartial 11 1457) = false := by
  decide +kernel

theorem node_context_11_1457_86175 : EJMOriginalGlobalDAGData.nodes 10 ⟨86175, by decide⟩ =
    .split (coordinate 11) (![⟨86138, by decide⟩,⟨86146, by decide⟩,⟨86161, by decide⟩,⟨86174, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1457_86175 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1457 ⟨86175, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1457
    ⟨86175, by decide⟩ (by decide) (![⟨86138, by decide⟩,⟨86146, by decide⟩,⟨86161, by decide⟩,⟨86174, by decide⟩]) unmarked_context_11_1457_86175 node_context_11_1457_86175
  intro a
  fin_cases a
  · exact context_12_5828_86138
  · exact context_12_5829_86146
  · exact context_12_5830_86161
  · exact context_12_5831_86174

theorem selected_cut_02796 : selected 9 ⟨86183, by decide⟩
    (prefixPartial 12 5832) = some ⟨12, 2, 0, 86183, 5832, 797, 65536⟩ := by
  decide +kernel

theorem context_12_5832_86183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5832 ⟨86183, by decide⟩ :=
  accepted_of_selected 12 5832 ⟨86183, by decide⟩ ⟨12, 2, 0, 86183, 5832, 797, 65536⟩
    (by decide) selected_cut_02796

theorem selected_cut_02797 : selected 9 ⟨86192, by decide⟩
    (prefixPartial 12 5833) = some ⟨12, 2, 0, 86192, 5833, 1041, 65536⟩ := by
  decide +kernel

theorem context_12_5833_86192 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5833 ⟨86192, by decide⟩ :=
  accepted_of_selected 12 5833 ⟨86192, by decide⟩ ⟨12, 2, 0, 86192, 5833, 1041, 65536⟩
    (by decide) selected_cut_02797

theorem selected_cut_02798 : selected 9 ⟨86213, by decide⟩
    (prefixPartial 12 5834) = some ⟨12, 2, 0, 86213, 5834, 1333, 65536⟩ := by
  decide +kernel

theorem context_12_5834_86213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5834 ⟨86213, by decide⟩ :=
  accepted_of_selected 12 5834 ⟨86213, by decide⟩ ⟨12, 2, 0, 86213, 5834, 1333, 65536⟩
    (by decide) selected_cut_02798

theorem selected_cut_02799 : selected 9 ⟨86220, by decide⟩
    (prefixPartial 12 5835) = some ⟨12, 2, 0, 86220, 5835, 953, 65536⟩ := by
  decide +kernel

theorem context_12_5835_86220 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5835 ⟨86220, by decide⟩ :=
  accepted_of_selected 12 5835 ⟨86220, by decide⟩ ⟨12, 2, 0, 86220, 5835, 953, 65536⟩
    (by decide) selected_cut_02799

theorem unmarked_context_11_1458_86221 : frontier 10 ⟨86221, by decide⟩
    (prefixCache 11 1458) (prefixPartial 11 1458) = false := by
  decide +kernel

theorem node_context_11_1458_86221 : EJMOriginalGlobalDAGData.nodes 10 ⟨86221, by decide⟩ =
    .split (coordinate 11) (![⟨86183, by decide⟩,⟨86192, by decide⟩,⟨86213, by decide⟩,⟨86220, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1458_86221 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1458 ⟨86221, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1458
    ⟨86221, by decide⟩ (by decide) (![⟨86183, by decide⟩,⟨86192, by decide⟩,⟨86213, by decide⟩,⟨86220, by decide⟩]) unmarked_context_11_1458_86221 node_context_11_1458_86221
  intro a
  fin_cases a
  · exact context_12_5832_86183
  · exact context_12_5833_86192
  · exact context_12_5834_86213
  · exact context_12_5835_86220

theorem selected_cut_02800 : selected 10 ⟨86291, by decide⟩
    (prefixPartial 11 1459) = some ⟨11, 2, 0, 86291, 1459, 4085, 262144⟩ := by
  decide +kernel

theorem context_11_1459_86291 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1459 ⟨86291, by decide⟩ :=
  accepted_of_selected 11 1459 ⟨86291, by decide⟩ ⟨11, 2, 0, 86291, 1459, 4085, 262144⟩
    (by decide) selected_cut_02800

theorem unmarked_context_10_364_86292 : frontier 11 ⟨86292, by decide⟩
    (prefixCache 10 364) (prefixPartial 10 364) = false := by
  decide +kernel

theorem node_context_10_364_86292 : EJMOriginalGlobalDAGData.nodes 11 ⟨86292, by decide⟩ =
    .split (coordinate 10) (![⟨86127, by decide⟩,⟨86175, by decide⟩,⟨86221, by decide⟩,⟨86291, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_364_86292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 364 ⟨86292, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 364
    ⟨86292, by decide⟩ (by decide) (![⟨86127, by decide⟩,⟨86175, by decide⟩,⟨86221, by decide⟩,⟨86291, by decide⟩]) unmarked_context_10_364_86292 node_context_10_364_86292
  intro a
  fin_cases a
  · exact context_11_1456_86127
  · exact context_11_1457_86175
  · exact context_11_1458_86221
  · exact context_11_1459_86291

theorem selected_cut_02801 : selected 10 ⟨86334, by decide⟩
    (prefixPartial 11 1460) = some ⟨11, 2, 0, 86334, 1460, 3513, 262144⟩ := by
  decide +kernel

theorem context_11_1460_86334 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1460 ⟨86334, by decide⟩ :=
  accepted_of_selected 11 1460 ⟨86334, by decide⟩ ⟨11, 2, 0, 86334, 1460, 3513, 262144⟩
    (by decide) selected_cut_02801

theorem selected_cut_02802 : selected 10 ⟨86396, by decide⟩
    (prefixPartial 11 1461) = some ⟨11, 2, 0, 86396, 1461, 3997, 262144⟩ := by
  decide +kernel

theorem context_11_1461_86396 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1461 ⟨86396, by decide⟩ :=
  accepted_of_selected 11 1461 ⟨86396, by decide⟩ ⟨11, 2, 0, 86396, 1461, 3997, 262144⟩
    (by decide) selected_cut_02802

theorem selected_cut_02803 : selected 10 ⟨86421, by decide⟩
    (prefixPartial 11 1462) = some ⟨11, 2, 0, 86421, 1462, 2681, 262144⟩ := by
  decide +kernel

theorem context_11_1462_86421 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1462 ⟨86421, by decide⟩ :=
  accepted_of_selected 11 1462 ⟨86421, by decide⟩ ⟨11, 2, 0, 86421, 1462, 2681, 262144⟩
    (by decide) selected_cut_02803

theorem selected_cut_02804 : selected 10 ⟨86446, by decide⟩
    (prefixPartial 11 1463) = some ⟨11, 2, 0, 86446, 1463, 2217, 262144⟩ := by
  decide +kernel

theorem context_11_1463_86446 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1463 ⟨86446, by decide⟩ :=
  accepted_of_selected 11 1463 ⟨86446, by decide⟩ ⟨11, 2, 0, 86446, 1463, 2217, 262144⟩
    (by decide) selected_cut_02804

theorem unmarked_context_10_365_86447 : frontier 11 ⟨86447, by decide⟩
    (prefixCache 10 365) (prefixPartial 10 365) = false := by
  decide +kernel

theorem node_context_10_365_86447 : EJMOriginalGlobalDAGData.nodes 11 ⟨86447, by decide⟩ =
    .split (coordinate 10) (![⟨86334, by decide⟩,⟨86396, by decide⟩,⟨86421, by decide⟩,⟨86446, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_365_86447 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 365 ⟨86447, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 365
    ⟨86447, by decide⟩ (by decide) (![⟨86334, by decide⟩,⟨86396, by decide⟩,⟨86421, by decide⟩,⟨86446, by decide⟩]) unmarked_context_10_365_86447 node_context_10_365_86447
  intro a
  fin_cases a
  · exact context_11_1460_86334
  · exact context_11_1461_86396
  · exact context_11_1462_86421
  · exact context_11_1463_86446

theorem selected_cut_02805 : selected 10 ⟨86470, by decide⟩
    (prefixPartial 11 1464) = some ⟨11, 2, 0, 86470, 1464, 1777, 262144⟩ := by
  decide +kernel

theorem context_11_1464_86470 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1464 ⟨86470, by decide⟩ :=
  accepted_of_selected 11 1464 ⟨86470, by decide⟩ ⟨11, 2, 0, 86470, 1464, 1777, 262144⟩
    (by decide) selected_cut_02805

theorem selected_cut_02806 : selected 10 ⟨86491, by decide⟩
    (prefixPartial 11 1465) = some ⟨11, 2, 0, 86491, 1465, 1601, 262144⟩ := by
  decide +kernel

theorem context_11_1465_86491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1465 ⟨86491, by decide⟩ :=
  accepted_of_selected 11 1465 ⟨86491, by decide⟩ ⟨11, 2, 0, 86491, 1465, 1601, 262144⟩
    (by decide) selected_cut_02806

theorem selected_cut_02807 : selected 10 ⟨86510, by decide⟩
    (prefixPartial 11 1466) = some ⟨11, 2, 0, 86510, 1466, 1329, 262144⟩ := by
  decide +kernel

theorem context_11_1466_86510 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1466 ⟨86510, by decide⟩ :=
  accepted_of_selected 11 1466 ⟨86510, by decide⟩ ⟨11, 2, 0, 86510, 1466, 1329, 262144⟩
    (by decide) selected_cut_02807

theorem selected_cut_02808 : selected 10 ⟨86526, by decide⟩
    (prefixPartial 11 1467) = some ⟨11, 2, 0, 86526, 1467, 1021, 262144⟩ := by
  decide +kernel

theorem context_11_1467_86526 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1467 ⟨86526, by decide⟩ :=
  accepted_of_selected 11 1467 ⟨86526, by decide⟩ ⟨11, 2, 0, 86526, 1467, 1021, 262144⟩
    (by decide) selected_cut_02808

theorem unmarked_context_10_366_86527 : frontier 11 ⟨86527, by decide⟩
    (prefixCache 10 366) (prefixPartial 10 366) = false := by
  decide +kernel

theorem node_context_10_366_86527 : EJMOriginalGlobalDAGData.nodes 11 ⟨86527, by decide⟩ =
    .split (coordinate 10) (![⟨86470, by decide⟩,⟨86491, by decide⟩,⟨86510, by decide⟩,⟨86526, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_366_86527 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 366 ⟨86527, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 366
    ⟨86527, by decide⟩ (by decide) (![⟨86470, by decide⟩,⟨86491, by decide⟩,⟨86510, by decide⟩,⟨86526, by decide⟩]) unmarked_context_10_366_86527 node_context_10_366_86527
  intro a
  fin_cases a
  · exact context_11_1464_86470
  · exact context_11_1465_86491
  · exact context_11_1466_86510
  · exact context_11_1467_86526

theorem selected_cut_02809 : selected 11 ⟨86583, by decide⟩
    (prefixPartial 10 367) = some ⟨10, 2, 0, 86583, 367, 1957, 1048576⟩ := by
  decide +kernel

theorem context_10_367_86583 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 367 ⟨86583, by decide⟩ :=
  accepted_of_selected 10 367 ⟨86583, by decide⟩ ⟨10, 2, 0, 86583, 367, 1957, 1048576⟩
    (by decide) selected_cut_02809

theorem unmarked_context_9_91_86584 : frontier 12 ⟨86584, by decide⟩
    (prefixCache 9 91) (prefixPartial 9 91) = false := by
  decide +kernel

theorem node_context_9_91_86584 : EJMOriginalGlobalDAGData.nodes 12 ⟨86584, by decide⟩ =
    .split (coordinate 9) (![⟨86292, by decide⟩,⟨86447, by decide⟩,⟨86527, by decide⟩,⟨86583, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_91_86584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 91 ⟨86584, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 91
    ⟨86584, by decide⟩ (by decide) (![⟨86292, by decide⟩,⟨86447, by decide⟩,⟨86527, by decide⟩,⟨86583, by decide⟩]) unmarked_context_9_91_86584 node_context_9_91_86584
  intro a
  fin_cases a
  · exact context_10_364_86292
  · exact context_10_365_86447
  · exact context_10_366_86527
  · exact context_10_367_86583

theorem unmarked_context_8_22_86585 : frontier 13 ⟨86585, by decide⟩
    (prefixCache 8 22) (prefixPartial 8 22) = false := by
  decide +kernel

theorem node_context_8_22_86585 : EJMOriginalGlobalDAGData.nodes 13 ⟨86585, by decide⟩ =
    .split (coordinate 8) (![⟨79543, by decide⟩,⟨84171, by decide⟩,⟨86073, by decide⟩,⟨86584, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_22_86585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 22 ⟨86585, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 22
    ⟨86585, by decide⟩ (by decide) (![⟨79543, by decide⟩,⟨84171, by decide⟩,⟨86073, by decide⟩,⟨86584, by decide⟩]) unmarked_context_8_22_86585 node_context_8_22_86585
  intro a
  fin_cases a
  · exact context_9_88_79543
  · exact context_9_89_84171
  · exact context_9_90_86073
  · exact context_9_91_86584

theorem selected_cut_02810 : selected 13 ⟨14298, by decide⟩
    (prefixPartial 8 23) = some ⟨8, 1, 0, 14298, 23, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_23_14298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 23 ⟨14298, by decide⟩ :=
  accepted_of_selected 8 23 ⟨14298, by decide⟩ ⟨8, 1, 0, 14298, 23, 1, 16777216⟩
    (by decide) selected_cut_02810

theorem unmarked_context_7_5_86586 : frontier 14 ⟨86586, by decide⟩
    (prefixCache 7 5) (prefixPartial 7 5) = false := by
  decide +kernel

theorem node_context_7_5_86586 : EJMOriginalGlobalDAGData.nodes 14 ⟨86586, by decide⟩ =
    .split (coordinate 7) (![⟨14300, by decide⟩,⟨70598, by decide⟩,⟨86585, by decide⟩,⟨14298, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_5_86586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 5 ⟨86586, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 5
    ⟨86586, by decide⟩ (by decide) (![⟨14300, by decide⟩,⟨70598, by decide⟩,⟨86585, by decide⟩,⟨14298, by decide⟩]) unmarked_context_7_5_86586 node_context_7_5_86586
  intro a
  fin_cases a
  · exact context_8_20_14300
  · exact context_8_21_70598
  · exact context_8_22_86585
  · exact context_8_23_14298

theorem selected_cut_02811 : selected 13 ⟨14300, by decide⟩
    (prefixPartial 8 24) = some ⟨8, 1, 0, 14300, 24, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_24_14300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 24 ⟨14300, by decide⟩ :=
  accepted_of_selected 8 24 ⟨14300, by decide⟩ ⟨8, 1, 0, 14300, 24, 1, 16777216⟩
    (by decide) selected_cut_02811

theorem selected_cut_02812 : selected 13 ⟨14300, by decide⟩
    (prefixPartial 8 25) = some ⟨8, 1, 0, 14300, 25, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_25_14300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 25 ⟨14300, by decide⟩ :=
  accepted_of_selected 8 25 ⟨14300, by decide⟩ ⟨8, 1, 0, 14300, 25, 1, 16777216⟩
    (by decide) selected_cut_02812

theorem selected_cut_02813 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 6656) = some ⟨12, 1, 0, 34034, 6656, 1, 65536⟩ := by
  decide +kernel

theorem context_12_6656_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6656 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 6656 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 6656, 1, 65536⟩
    (by decide) selected_cut_02813

theorem selected_cut_02814 : selected 7 ⟨86643, by decide⟩
    (prefixPartial 14 106512) = some ⟨14, 2, 0, 86643, 106512, 1913, 4096⟩ := by
  decide +kernel

theorem context_14_106512_86643 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106512 ⟨86643, by decide⟩ :=
  accepted_of_selected 14 106512 ⟨86643, by decide⟩ ⟨14, 2, 0, 86643, 106512, 1913, 4096⟩
    (by decide) selected_cut_02814

theorem selected_cut_02815 : selected 7 ⟨86698, by decide⟩
    (prefixPartial 14 106513) = some ⟨14, 2, 0, 86698, 106513, 1753, 4096⟩ := by
  decide +kernel

theorem context_14_106513_86698 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106513 ⟨86698, by decide⟩ :=
  accepted_of_selected 14 106513 ⟨86698, by decide⟩ ⟨14, 2, 0, 86698, 106513, 1753, 4096⟩
    (by decide) selected_cut_02815

theorem selected_cut_02816 : selected 7 ⟨86727, by decide⟩
    (prefixPartial 14 106514) = some ⟨14, 2, 0, 86727, 106514, 1341, 4096⟩ := by
  decide +kernel

theorem context_14_106514_86727 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106514 ⟨86727, by decide⟩ :=
  accepted_of_selected 14 106514 ⟨86727, by decide⟩ ⟨14, 2, 0, 86727, 106514, 1341, 4096⟩
    (by decide) selected_cut_02816

theorem selected_cut_02817 : selected 7 ⟨86750, by decide⟩
    (prefixPartial 14 106515) = some ⟨14, 2, 0, 86750, 106515, 1345, 4096⟩ := by
  decide +kernel

theorem context_14_106515_86750 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106515 ⟨86750, by decide⟩ :=
  accepted_of_selected 14 106515 ⟨86750, by decide⟩ ⟨14, 2, 0, 86750, 106515, 1345, 4096⟩
    (by decide) selected_cut_02817

theorem unmarked_context_13_26628_86751 : frontier 8 ⟨86751, by decide⟩
    (prefixCache 13 26628) (prefixPartial 13 26628) = false := by
  decide +kernel

theorem node_context_13_26628_86751 : EJMOriginalGlobalDAGData.nodes 8 ⟨86751, by decide⟩ =
    .split (coordinate 13) (![⟨86643, by decide⟩,⟨86698, by decide⟩,⟨86727, by decide⟩,⟨86750, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_26628_86751 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26628 ⟨86751, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 26628
    ⟨86751, by decide⟩ (by decide) (![⟨86643, by decide⟩,⟨86698, by decide⟩,⟨86727, by decide⟩,⟨86750, by decide⟩]) unmarked_context_13_26628_86751 node_context_13_26628_86751
  intro a
  fin_cases a
  · exact context_14_106512_86643
  · exact context_14_106513_86698
  · exact context_14_106514_86727
  · exact context_14_106515_86750

theorem selected_cut_02818 : selected 7 ⟨86766, by decide⟩
    (prefixPartial 14 106516) = some ⟨14, 2, 0, 86766, 106516, 965, 4096⟩ := by
  decide +kernel

theorem context_14_106516_86766 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106516 ⟨86766, by decide⟩ :=
  accepted_of_selected 14 106516 ⟨86766, by decide⟩ ⟨14, 2, 0, 86766, 106516, 965, 4096⟩
    (by decide) selected_cut_02818

theorem selected_cut_02819 : selected 7 ⟨86788, by decide⟩
    (prefixPartial 14 106517) = some ⟨14, 2, 0, 86788, 106517, 1229, 4096⟩ := by
  decide +kernel

theorem context_14_106517_86788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106517 ⟨86788, by decide⟩ :=
  accepted_of_selected 14 106517 ⟨86788, by decide⟩ ⟨14, 2, 0, 86788, 106517, 1229, 4096⟩
    (by decide) selected_cut_02819

theorem selected_cut_02820 : selected 7 ⟨86809, by decide⟩
    (prefixPartial 14 106518) = some ⟨14, 2, 0, 86809, 106518, 1089, 4096⟩ := by
  decide +kernel

theorem context_14_106518_86809 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106518 ⟨86809, by decide⟩ :=
  accepted_of_selected 14 106518 ⟨86809, by decide⟩ ⟨14, 2, 0, 86809, 106518, 1089, 4096⟩
    (by decide) selected_cut_02820

theorem selected_cut_02821 : selected 7 ⟨86828, by decide⟩
    (prefixPartial 14 106519) = some ⟨14, 2, 0, 86828, 106519, 921, 4096⟩ := by
  decide +kernel

theorem context_14_106519_86828 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106519 ⟨86828, by decide⟩ :=
  accepted_of_selected 14 106519 ⟨86828, by decide⟩ ⟨14, 2, 0, 86828, 106519, 921, 4096⟩
    (by decide) selected_cut_02821

theorem unmarked_context_13_26629_86829 : frontier 8 ⟨86829, by decide⟩
    (prefixCache 13 26629) (prefixPartial 13 26629) = false := by
  decide +kernel

theorem node_context_13_26629_86829 : EJMOriginalGlobalDAGData.nodes 8 ⟨86829, by decide⟩ =
    .split (coordinate 13) (![⟨86766, by decide⟩,⟨86788, by decide⟩,⟨86809, by decide⟩,⟨86828, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_26629_86829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26629 ⟨86829, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 26629
    ⟨86829, by decide⟩ (by decide) (![⟨86766, by decide⟩,⟨86788, by decide⟩,⟨86809, by decide⟩,⟨86828, by decide⟩]) unmarked_context_13_26629_86829 node_context_13_26629_86829
  intro a
  fin_cases a
  · exact context_14_106516_86766
  · exact context_14_106517_86788
  · exact context_14_106518_86809
  · exact context_14_106519_86828

theorem selected_cut_02822 : selected 8 ⟨86867, by decide⟩
    (prefixPartial 13 26630) = some ⟨13, 2, 0, 86867, 26630, 2385, 16384⟩ := by
  decide +kernel

theorem context_13_26630_86867 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26630 ⟨86867, by decide⟩ :=
  accepted_of_selected 13 26630 ⟨86867, by decide⟩ ⟨13, 2, 0, 86867, 26630, 2385, 16384⟩
    (by decide) selected_cut_02822

theorem selected_cut_02823 : selected 8 ⟨86885, by decide⟩
    (prefixPartial 13 26631) = some ⟨13, 2, 0, 86885, 26631, 1441, 16384⟩ := by
  decide +kernel

theorem context_13_26631_86885 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26631 ⟨86885, by decide⟩ :=
  accepted_of_selected 13 26631 ⟨86885, by decide⟩ ⟨13, 2, 0, 86885, 26631, 1441, 16384⟩
    (by decide) selected_cut_02823

theorem unmarked_context_12_6657_86886 : frontier 9 ⟨86886, by decide⟩
    (prefixCache 12 6657) (prefixPartial 12 6657) = false := by
  decide +kernel

theorem node_context_12_6657_86886 : EJMOriginalGlobalDAGData.nodes 9 ⟨86886, by decide⟩ =
    .split (coordinate 12) (![⟨86751, by decide⟩,⟨86829, by decide⟩,⟨86867, by decide⟩,⟨86885, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6657_86886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6657 ⟨86886, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6657
    ⟨86886, by decide⟩ (by decide) (![⟨86751, by decide⟩,⟨86829, by decide⟩,⟨86867, by decide⟩,⟨86885, by decide⟩]) unmarked_context_12_6657_86886 node_context_12_6657_86886
  intro a
  fin_cases a
  · exact context_13_26628_86751
  · exact context_13_26629_86829
  · exact context_13_26630_86867
  · exact context_13_26631_86885

theorem selected_cut_02824 : selected 7 ⟨86921, by decide⟩
    (prefixPartial 14 106528) = some ⟨14, 2, 0, 86921, 106528, 1593, 4096⟩ := by
  decide +kernel

theorem context_14_106528_86921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106528 ⟨86921, by decide⟩ :=
  accepted_of_selected 14 106528 ⟨86921, by decide⟩ ⟨14, 2, 0, 86921, 106528, 1593, 4096⟩
    (by decide) selected_cut_02824

theorem selected_cut_02825 : selected 7 ⟨86949, by decide⟩
    (prefixPartial 14 106529) = some ⟨14, 2, 0, 86949, 106529, 1317, 4096⟩ := by
  decide +kernel

theorem context_14_106529_86949 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106529 ⟨86949, by decide⟩ :=
  accepted_of_selected 14 106529 ⟨86949, by decide⟩ ⟨14, 2, 0, 86949, 106529, 1317, 4096⟩
    (by decide) selected_cut_02825

theorem selected_cut_02826 : selected 7 ⟨86977, by decide⟩
    (prefixPartial 14 106530) = some ⟨14, 2, 0, 86977, 106530, 1285, 4096⟩ := by
  decide +kernel

theorem context_14_106530_86977 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106530 ⟨86977, by decide⟩ :=
  accepted_of_selected 14 106530 ⟨86977, by decide⟩ ⟨14, 2, 0, 86977, 106530, 1285, 4096⟩
    (by decide) selected_cut_02826

theorem selected_cut_02827 : selected 7 ⟨86998, by decide⟩
    (prefixPartial 14 106531) = some ⟨14, 2, 0, 86998, 106531, 1181, 4096⟩ := by
  decide +kernel

theorem context_14_106531_86998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106531 ⟨86998, by decide⟩ :=
  accepted_of_selected 14 106531 ⟨86998, by decide⟩ ⟨14, 2, 0, 86998, 106531, 1181, 4096⟩
    (by decide) selected_cut_02827

theorem unmarked_context_13_26632_86999 : frontier 8 ⟨86999, by decide⟩
    (prefixCache 13 26632) (prefixPartial 13 26632) = false := by
  decide +kernel

theorem node_context_13_26632_86999 : EJMOriginalGlobalDAGData.nodes 8 ⟨86999, by decide⟩ =
    .split (coordinate 13) (![⟨86921, by decide⟩,⟨86949, by decide⟩,⟨86977, by decide⟩,⟨86998, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_26632_86999 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26632 ⟨86999, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 26632
    ⟨86999, by decide⟩ (by decide) (![⟨86921, by decide⟩,⟨86949, by decide⟩,⟨86977, by decide⟩,⟨86998, by decide⟩]) unmarked_context_13_26632_86999 node_context_13_26632_86999
  intro a
  fin_cases a
  · exact context_14_106528_86921
  · exact context_14_106529_86949
  · exact context_14_106530_86977
  · exact context_14_106531_86998

theorem selected_cut_02828 : selected 8 ⟨87071, by decide⟩
    (prefixPartial 13 26633) = some ⟨13, 2, 0, 87071, 26633, 4065, 16384⟩ := by
  decide +kernel

theorem context_13_26633_87071 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26633 ⟨87071, by decide⟩ :=
  accepted_of_selected 13 26633 ⟨87071, by decide⟩ ⟨13, 2, 0, 87071, 26633, 4065, 16384⟩
    (by decide) selected_cut_02828

theorem selected_cut_02829 : selected 8 ⟨87112, by decide⟩
    (prefixPartial 13 26634) = some ⟨13, 2, 0, 87112, 26634, 2449, 16384⟩ := by
  decide +kernel

theorem context_13_26634_87112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26634 ⟨87112, by decide⟩ :=
  accepted_of_selected 13 26634 ⟨87112, by decide⟩ ⟨13, 2, 0, 87112, 26634, 2449, 16384⟩
    (by decide) selected_cut_02829

theorem selected_cut_02830 : selected 8 ⟨87122, by decide⟩
    (prefixPartial 13 26635) = some ⟨13, 2, 0, 87122, 26635, 1313, 16384⟩ := by
  decide +kernel

theorem context_13_26635_87122 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26635 ⟨87122, by decide⟩ :=
  accepted_of_selected 13 26635 ⟨87122, by decide⟩ ⟨13, 2, 0, 87122, 26635, 1313, 16384⟩
    (by decide) selected_cut_02830

theorem unmarked_context_12_6658_87123 : frontier 9 ⟨87123, by decide⟩
    (prefixCache 12 6658) (prefixPartial 12 6658) = false := by
  decide +kernel

theorem node_context_12_6658_87123 : EJMOriginalGlobalDAGData.nodes 9 ⟨87123, by decide⟩ =
    .split (coordinate 12) (![⟨86999, by decide⟩,⟨87071, by decide⟩,⟨87112, by decide⟩,⟨87122, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6658_87123 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6658 ⟨87123, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6658
    ⟨87123, by decide⟩ (by decide) (![⟨86999, by decide⟩,⟨87071, by decide⟩,⟨87112, by decide⟩,⟨87122, by decide⟩]) unmarked_context_12_6658_87123 node_context_12_6658_87123
  intro a
  fin_cases a
  · exact context_13_26632_86999
  · exact context_13_26633_87071
  · exact context_13_26634_87112
  · exact context_13_26635_87122

theorem selected_cut_02831 : selected 7 ⟨87166, by decide⟩
    (prefixPartial 14 106544) = some ⟨14, 2, 0, 87166, 106544, 1893, 4096⟩ := by
  decide +kernel

theorem context_14_106544_87166 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106544 ⟨87166, by decide⟩ :=
  accepted_of_selected 14 106544 ⟨87166, by decide⟩ ⟨14, 2, 0, 87166, 106544, 1893, 4096⟩
    (by decide) selected_cut_02831

theorem selected_cut_02832 : selected 7 ⟨87195, by decide⟩
    (prefixPartial 14 106545) = some ⟨14, 2, 0, 87195, 106545, 1545, 4096⟩ := by
  decide +kernel

theorem context_14_106545_87195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106545 ⟨87195, by decide⟩ :=
  accepted_of_selected 14 106545 ⟨87195, by decide⟩ ⟨14, 2, 0, 87195, 106545, 1545, 4096⟩
    (by decide) selected_cut_02832

theorem selected_cut_02833 : selected 7 ⟨87221, by decide⟩
    (prefixPartial 14 106546) = some ⟨14, 2, 0, 87221, 106546, 1437, 4096⟩ := by
  decide +kernel

theorem context_14_106546_87221 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106546 ⟨87221, by decide⟩ :=
  accepted_of_selected 14 106546 ⟨87221, by decide⟩ ⟨14, 2, 0, 87221, 106546, 1437, 4096⟩
    (by decide) selected_cut_02833

theorem selected_cut_02834 : selected 7 ⟨87245, by decide⟩
    (prefixPartial 14 106547) = some ⟨14, 2, 0, 87245, 106547, 1589, 4096⟩ := by
  decide +kernel

theorem context_14_106547_87245 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106547 ⟨87245, by decide⟩ :=
  accepted_of_selected 14 106547 ⟨87245, by decide⟩ ⟨14, 2, 0, 87245, 106547, 1589, 4096⟩
    (by decide) selected_cut_02834

theorem unmarked_context_13_26636_87246 : frontier 8 ⟨87246, by decide⟩
    (prefixCache 13 26636) (prefixPartial 13 26636) = false := by
  decide +kernel

theorem node_context_13_26636_87246 : EJMOriginalGlobalDAGData.nodes 8 ⟨87246, by decide⟩ =
    .split (coordinate 13) (![⟨87166, by decide⟩,⟨87195, by decide⟩,⟨87221, by decide⟩,⟨87245, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_26636_87246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26636 ⟨87246, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 26636
    ⟨87246, by decide⟩ (by decide) (![⟨87166, by decide⟩,⟨87195, by decide⟩,⟨87221, by decide⟩,⟨87245, by decide⟩]) unmarked_context_13_26636_87246 node_context_13_26636_87246
  intro a
  fin_cases a
  · exact context_14_106544_87166
  · exact context_14_106545_87195
  · exact context_14_106546_87221
  · exact context_14_106547_87245

theorem selected_cut_02835 : selected 7 ⟨87262, by decide⟩
    (prefixPartial 14 106548) = some ⟨14, 2, 0, 87262, 106548, 1137, 4096⟩ := by
  decide +kernel

theorem context_14_106548_87262 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106548 ⟨87262, by decide⟩ :=
  accepted_of_selected 14 106548 ⟨87262, by decide⟩ ⟨14, 2, 0, 87262, 106548, 1137, 4096⟩
    (by decide) selected_cut_02835

theorem selected_cut_02836 : selected 7 ⟨87285, by decide⟩
    (prefixPartial 14 106549) = some ⟨14, 2, 0, 87285, 106549, 1289, 4096⟩ := by
  decide +kernel

theorem context_14_106549_87285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106549 ⟨87285, by decide⟩ :=
  accepted_of_selected 14 106549 ⟨87285, by decide⟩ ⟨14, 2, 0, 87285, 106549, 1289, 4096⟩
    (by decide) selected_cut_02836

theorem selected_cut_02837 : selected 7 ⟨87310, by decide⟩
    (prefixPartial 14 106550) = some ⟨14, 2, 0, 87310, 106550, 1345, 4096⟩ := by
  decide +kernel

theorem context_14_106550_87310 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106550 ⟨87310, by decide⟩ :=
  accepted_of_selected 14 106550 ⟨87310, by decide⟩ ⟨14, 2, 0, 87310, 106550, 1345, 4096⟩
    (by decide) selected_cut_02837

theorem selected_cut_02838 : selected 7 ⟨87326, by decide⟩
    (prefixPartial 14 106551) = some ⟨14, 2, 0, 87326, 106551, 1001, 4096⟩ := by
  decide +kernel

theorem context_14_106551_87326 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106551 ⟨87326, by decide⟩ :=
  accepted_of_selected 14 106551 ⟨87326, by decide⟩ ⟨14, 2, 0, 87326, 106551, 1001, 4096⟩
    (by decide) selected_cut_02838

theorem unmarked_context_13_26637_87327 : frontier 8 ⟨87327, by decide⟩
    (prefixCache 13 26637) (prefixPartial 13 26637) = false := by
  decide +kernel

theorem node_context_13_26637_87327 : EJMOriginalGlobalDAGData.nodes 8 ⟨87327, by decide⟩ =
    .split (coordinate 13) (![⟨87262, by decide⟩,⟨87285, by decide⟩,⟨87310, by decide⟩,⟨87326, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_26637_87327 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26637 ⟨87327, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 26637
    ⟨87327, by decide⟩ (by decide) (![⟨87262, by decide⟩,⟨87285, by decide⟩,⟨87310, by decide⟩,⟨87326, by decide⟩]) unmarked_context_13_26637_87327 node_context_13_26637_87327
  intro a
  fin_cases a
  · exact context_14_106548_87262
  · exact context_14_106549_87285
  · exact context_14_106550_87310
  · exact context_14_106551_87326

theorem selected_cut_02839 : selected 8 ⟨87359, by decide⟩
    (prefixPartial 13 26638) = some ⟨13, 2, 0, 87359, 26638, 2457, 16384⟩ := by
  decide +kernel

theorem context_13_26638_87359 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26638 ⟨87359, by decide⟩ :=
  accepted_of_selected 13 26638 ⟨87359, by decide⟩ ⟨13, 2, 0, 87359, 26638, 2457, 16384⟩
    (by decide) selected_cut_02839

theorem selected_cut_02840 : selected 8 ⟨87381, by decide⟩
    (prefixPartial 13 26639) = some ⟨13, 2, 0, 87381, 26639, 1409, 16384⟩ := by
  decide +kernel

theorem context_13_26639_87381 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26639 ⟨87381, by decide⟩ :=
  accepted_of_selected 13 26639 ⟨87381, by decide⟩ ⟨13, 2, 0, 87381, 26639, 1409, 16384⟩
    (by decide) selected_cut_02840

theorem unmarked_context_12_6659_87382 : frontier 9 ⟨87382, by decide⟩
    (prefixCache 12 6659) (prefixPartial 12 6659) = false := by
  decide +kernel

theorem node_context_12_6659_87382 : EJMOriginalGlobalDAGData.nodes 9 ⟨87382, by decide⟩ =
    .split (coordinate 12) (![⟨87246, by decide⟩,⟨87327, by decide⟩,⟨87359, by decide⟩,⟨87381, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6659_87382 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6659 ⟨87382, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6659
    ⟨87382, by decide⟩ (by decide) (![⟨87246, by decide⟩,⟨87327, by decide⟩,⟨87359, by decide⟩,⟨87381, by decide⟩]) unmarked_context_12_6659_87382 node_context_12_6659_87382
  intro a
  fin_cases a
  · exact context_13_26636_87246
  · exact context_13_26637_87327
  · exact context_13_26638_87359
  · exact context_13_26639_87381

theorem unmarked_context_11_1664_87383 : frontier 10 ⟨87383, by decide⟩
    (prefixCache 11 1664) (prefixPartial 11 1664) = false := by
  decide +kernel

theorem node_context_11_1664_87383 : EJMOriginalGlobalDAGData.nodes 10 ⟨87383, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨86886, by decide⟩,⟨87123, by decide⟩,⟨87382, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1664_87383 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1664 ⟨87383, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1664
    ⟨87383, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨86886, by decide⟩,⟨87123, by decide⟩,⟨87382, by decide⟩]) unmarked_context_11_1664_87383 node_context_11_1664_87383
  intro a
  fin_cases a
  · exact context_12_6656_34034
  · exact context_12_6657_86886
  · exact context_12_6658_87123
  · exact context_12_6659_87382

theorem selected_cut_02841 : selected 7 ⟨87439, by decide⟩
    (prefixPartial 14 106560) = some ⟨14, 2, 0, 87439, 106560, 2785, 4096⟩ := by
  decide +kernel

theorem context_14_106560_87439 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106560 ⟨87439, by decide⟩ :=
  accepted_of_selected 14 106560 ⟨87439, by decide⟩ ⟨14, 2, 0, 87439, 106560, 2785, 4096⟩
    (by decide) selected_cut_02841

theorem selected_cut_02842 : selected 7 ⟨87479, by decide⟩
    (prefixPartial 14 106561) = some ⟨14, 2, 0, 87479, 106561, 1189, 4096⟩ := by
  decide +kernel

theorem context_14_106561_87479 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106561 ⟨87479, by decide⟩ :=
  accepted_of_selected 14 106561 ⟨87479, by decide⟩ ⟨14, 2, 0, 87479, 106561, 1189, 4096⟩
    (by decide) selected_cut_02842

theorem selected_cut_02843 : selected 7 ⟨87505, by decide⟩
    (prefixPartial 14 106562) = some ⟨14, 2, 0, 87505, 106562, 857, 4096⟩ := by
  decide +kernel

theorem context_14_106562_87505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106562 ⟨87505, by decide⟩ :=
  accepted_of_selected 14 106562 ⟨87505, by decide⟩ ⟨14, 2, 0, 87505, 106562, 857, 4096⟩
    (by decide) selected_cut_02843

theorem selected_cut_02844 : selected 7 ⟨87523, by decide⟩
    (prefixPartial 14 106563) = some ⟨14, 2, 0, 87523, 106563, 561, 4096⟩ := by
  decide +kernel

theorem context_14_106563_87523 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106563 ⟨87523, by decide⟩ :=
  accepted_of_selected 14 106563 ⟨87523, by decide⟩ ⟨14, 2, 0, 87523, 106563, 561, 4096⟩
    (by decide) selected_cut_02844

theorem unmarked_context_13_26640_87524 : frontier 8 ⟨87524, by decide⟩
    (prefixCache 13 26640) (prefixPartial 13 26640) = false := by
  decide +kernel

theorem node_context_13_26640_87524 : EJMOriginalGlobalDAGData.nodes 8 ⟨87524, by decide⟩ =
    .split (coordinate 13) (![⟨87439, by decide⟩,⟨87479, by decide⟩,⟨87505, by decide⟩,⟨87523, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_26640_87524 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26640 ⟨87524, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 26640
    ⟨87524, by decide⟩ (by decide) (![⟨87439, by decide⟩,⟨87479, by decide⟩,⟨87505, by decide⟩,⟨87523, by decide⟩]) unmarked_context_13_26640_87524 node_context_13_26640_87524
  intro a
  fin_cases a
  · exact context_14_106560_87439
  · exact context_14_106561_87479
  · exact context_14_106562_87505
  · exact context_14_106563_87523

theorem selected_cut_02845 : selected 7 ⟨87588, by decide⟩
    (prefixPartial 14 106564) = some ⟨14, 2, 0, 87588, 106564, 2437, 4096⟩ := by
  decide +kernel

theorem context_14_106564_87588 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106564 ⟨87588, by decide⟩ :=
  accepted_of_selected 14 106564 ⟨87588, by decide⟩ ⟨14, 2, 0, 87588, 106564, 2437, 4096⟩
    (by decide) selected_cut_02845

theorem selected_cut_02846 : selected 7 ⟨87643, by decide⟩
    (prefixPartial 14 106565) = some ⟨14, 2, 0, 87643, 106565, 1905, 4096⟩ := by
  decide +kernel

theorem context_14_106565_87643 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106565 ⟨87643, by decide⟩ :=
  accepted_of_selected 14 106565 ⟨87643, by decide⟩ ⟨14, 2, 0, 87643, 106565, 1905, 4096⟩
    (by decide) selected_cut_02846

theorem selected_cut_02847 : selected 7 ⟨87680, by decide⟩
    (prefixPartial 14 106566) = some ⟨14, 2, 0, 87680, 106566, 1045, 4096⟩ := by
  decide +kernel

theorem context_14_106566_87680 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106566 ⟨87680, by decide⟩ :=
  accepted_of_selected 14 106566 ⟨87680, by decide⟩ ⟨14, 2, 0, 87680, 106566, 1045, 4096⟩
    (by decide) selected_cut_02847

theorem selected_cut_02848 : selected 7 ⟨87695, by decide⟩
    (prefixPartial 14 106567) = some ⟨14, 2, 0, 87695, 106567, 593, 4096⟩ := by
  decide +kernel

theorem context_14_106567_87695 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106567 ⟨87695, by decide⟩ :=
  accepted_of_selected 14 106567 ⟨87695, by decide⟩ ⟨14, 2, 0, 87695, 106567, 593, 4096⟩
    (by decide) selected_cut_02848

theorem unmarked_context_13_26641_87696 : frontier 8 ⟨87696, by decide⟩
    (prefixCache 13 26641) (prefixPartial 13 26641) = false := by
  decide +kernel

theorem node_context_13_26641_87696 : EJMOriginalGlobalDAGData.nodes 8 ⟨87696, by decide⟩ =
    .split (coordinate 13) (![⟨87588, by decide⟩,⟨87643, by decide⟩,⟨87680, by decide⟩,⟨87695, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_26641_87696 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26641 ⟨87696, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 26641
    ⟨87696, by decide⟩ (by decide) (![⟨87588, by decide⟩,⟨87643, by decide⟩,⟨87680, by decide⟩,⟨87695, by decide⟩]) unmarked_context_13_26641_87696 node_context_13_26641_87696
  intro a
  fin_cases a
  · exact context_14_106564_87588
  · exact context_14_106565_87643
  · exact context_14_106566_87680
  · exact context_14_106567_87695

theorem selected_cut_02849 : selected 8 ⟨87822, by decide⟩
    (prefixPartial 13 26642) = some ⟨13, 2, 0, 87822, 26642, 3217, 16384⟩ := by
  decide +kernel

theorem context_13_26642_87822 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26642 ⟨87822, by decide⟩ :=
  accepted_of_selected 13 26642 ⟨87822, by decide⟩ ⟨13, 2, 0, 87822, 26642, 3217, 16384⟩
    (by decide) selected_cut_02849

theorem selected_cut_02850 : selected 8 ⟨87912, by decide⟩
    (prefixPartial 13 26643) = some ⟨13, 2, 0, 87912, 26643, 1701, 16384⟩ := by
  decide +kernel

theorem context_13_26643_87912 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26643 ⟨87912, by decide⟩ :=
  accepted_of_selected 13 26643 ⟨87912, by decide⟩ ⟨13, 2, 0, 87912, 26643, 1701, 16384⟩
    (by decide) selected_cut_02850

theorem unmarked_context_12_6660_87913 : frontier 9 ⟨87913, by decide⟩
    (prefixCache 12 6660) (prefixPartial 12 6660) = false := by
  decide +kernel

theorem node_context_12_6660_87913 : EJMOriginalGlobalDAGData.nodes 9 ⟨87913, by decide⟩ =
    .split (coordinate 12) (![⟨87524, by decide⟩,⟨87696, by decide⟩,⟨87822, by decide⟩,⟨87912, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6660_87913 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6660 ⟨87913, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6660
    ⟨87913, by decide⟩ (by decide) (![⟨87524, by decide⟩,⟨87696, by decide⟩,⟨87822, by decide⟩,⟨87912, by decide⟩]) unmarked_context_12_6660_87913 node_context_12_6660_87913
  intro a
  fin_cases a
  · exact context_13_26640_87524
  · exact context_13_26641_87696
  · exact context_13_26642_87822
  · exact context_13_26643_87912

theorem selected_cut_02851 : selected 7 ⟨87951, by decide⟩
    (prefixPartial 14 106576) = some ⟨14, 2, 0, 87951, 106576, 1697, 4096⟩ := by
  decide +kernel

theorem context_14_106576_87951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106576 ⟨87951, by decide⟩ :=
  accepted_of_selected 14 106576 ⟨87951, by decide⟩ ⟨14, 2, 0, 87951, 106576, 1697, 4096⟩
    (by decide) selected_cut_02851

theorem selected_cut_02852 : selected 7 ⟨87993, by decide⟩
    (prefixPartial 14 106577) = some ⟨14, 2, 0, 87993, 106577, 1721, 4096⟩ := by
  decide +kernel

theorem context_14_106577_87993 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106577 ⟨87993, by decide⟩ :=
  accepted_of_selected 14 106577 ⟨87993, by decide⟩ ⟨14, 2, 0, 87993, 106577, 1721, 4096⟩
    (by decide) selected_cut_02852

theorem selected_cut_02853 : selected 7 ⟨88019, by decide⟩
    (prefixPartial 14 106578) = some ⟨14, 2, 0, 88019, 106578, 1573, 4096⟩ := by
  decide +kernel

theorem context_14_106578_88019 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106578 ⟨88019, by decide⟩ :=
  accepted_of_selected 14 106578 ⟨88019, by decide⟩ ⟨14, 2, 0, 88019, 106578, 1573, 4096⟩
    (by decide) selected_cut_02853

theorem selected_cut_02854 : selected 7 ⟨88046, by decide⟩
    (prefixPartial 14 106579) = some ⟨14, 2, 0, 88046, 106579, 1717, 4096⟩ := by
  decide +kernel

theorem context_14_106579_88046 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106579 ⟨88046, by decide⟩ :=
  accepted_of_selected 14 106579 ⟨88046, by decide⟩ ⟨14, 2, 0, 88046, 106579, 1717, 4096⟩
    (by decide) selected_cut_02854

theorem unmarked_context_13_26644_88047 : frontier 8 ⟨88047, by decide⟩
    (prefixCache 13 26644) (prefixPartial 13 26644) = false := by
  decide +kernel

theorem node_context_13_26644_88047 : EJMOriginalGlobalDAGData.nodes 8 ⟨88047, by decide⟩ =
    .split (coordinate 13) (![⟨87951, by decide⟩,⟨87993, by decide⟩,⟨88019, by decide⟩,⟨88046, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_26644_88047 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26644 ⟨88047, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 26644
    ⟨88047, by decide⟩ (by decide) (![⟨87951, by decide⟩,⟨87993, by decide⟩,⟨88019, by decide⟩,⟨88046, by decide⟩]) unmarked_context_13_26644_88047 node_context_13_26644_88047
  intro a
  fin_cases a
  · exact context_14_106576_87951
  · exact context_14_106577_87993
  · exact context_14_106578_88019
  · exact context_14_106579_88046

theorem selected_cut_02855 : selected 7 ⟨88065, by decide⟩
    (prefixPartial 14 106580) = some ⟨14, 2, 0, 88065, 106580, 1169, 4096⟩ := by
  decide +kernel

theorem context_14_106580_88065 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106580 ⟨88065, by decide⟩ :=
  accepted_of_selected 14 106580 ⟨88065, by decide⟩ ⟨14, 2, 0, 88065, 106580, 1169, 4096⟩
    (by decide) selected_cut_02855

theorem selected_cut_02856 : selected 7 ⟨88092, by decide⟩
    (prefixPartial 14 106581) = some ⟨14, 2, 0, 88092, 106581, 1501, 4096⟩ := by
  decide +kernel

theorem context_14_106581_88092 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106581 ⟨88092, by decide⟩ :=
  accepted_of_selected 14 106581 ⟨88092, by decide⟩ ⟨14, 2, 0, 88092, 106581, 1501, 4096⟩
    (by decide) selected_cut_02856

theorem selected_cut_02857 : selected 7 ⟨88119, by decide⟩
    (prefixPartial 14 106582) = some ⟨14, 2, 0, 88119, 106582, 1457, 4096⟩ := by
  decide +kernel

theorem context_14_106582_88119 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106582 ⟨88119, by decide⟩ :=
  accepted_of_selected 14 106582 ⟨88119, by decide⟩ ⟨14, 2, 0, 88119, 106582, 1457, 4096⟩
    (by decide) selected_cut_02857

theorem selected_cut_02858 : selected 7 ⟨88138, by decide⟩
    (prefixPartial 14 106583) = some ⟨14, 2, 0, 88138, 106583, 1241, 4096⟩ := by
  decide +kernel

theorem context_14_106583_88138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106583 ⟨88138, by decide⟩ :=
  accepted_of_selected 14 106583 ⟨88138, by decide⟩ ⟨14, 2, 0, 88138, 106583, 1241, 4096⟩
    (by decide) selected_cut_02858

theorem unmarked_context_13_26645_88139 : frontier 8 ⟨88139, by decide⟩
    (prefixCache 13 26645) (prefixPartial 13 26645) = false := by
  decide +kernel

theorem node_context_13_26645_88139 : EJMOriginalGlobalDAGData.nodes 8 ⟨88139, by decide⟩ =
    .split (coordinate 13) (![⟨88065, by decide⟩,⟨88092, by decide⟩,⟨88119, by decide⟩,⟨88138, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_26645_88139 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26645 ⟨88139, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 26645
    ⟨88139, by decide⟩ (by decide) (![⟨88065, by decide⟩,⟨88092, by decide⟩,⟨88119, by decide⟩,⟨88138, by decide⟩]) unmarked_context_13_26645_88139 node_context_13_26645_88139
  intro a
  fin_cases a
  · exact context_14_106580_88065
  · exact context_14_106581_88092
  · exact context_14_106582_88119
  · exact context_14_106583_88138

theorem selected_cut_02859 : selected 8 ⟨88205, by decide⟩
    (prefixPartial 13 26646) = some ⟨13, 2, 0, 88205, 26646, 2877, 16384⟩ := by
  decide +kernel

theorem context_13_26646_88205 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26646 ⟨88205, by decide⟩ :=
  accepted_of_selected 13 26646 ⟨88205, by decide⟩ ⟨13, 2, 0, 88205, 26646, 2877, 16384⟩
    (by decide) selected_cut_02859

theorem selected_cut_02860 : selected 8 ⟨88247, by decide⟩
    (prefixPartial 13 26647) = some ⟨13, 2, 0, 88247, 26647, 1753, 16384⟩ := by
  decide +kernel

theorem context_13_26647_88247 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26647 ⟨88247, by decide⟩ :=
  accepted_of_selected 13 26647 ⟨88247, by decide⟩ ⟨13, 2, 0, 88247, 26647, 1753, 16384⟩
    (by decide) selected_cut_02860

theorem unmarked_context_12_6661_88248 : frontier 9 ⟨88248, by decide⟩
    (prefixCache 12 6661) (prefixPartial 12 6661) = false := by
  decide +kernel

theorem node_context_12_6661_88248 : EJMOriginalGlobalDAGData.nodes 9 ⟨88248, by decide⟩ =
    .split (coordinate 12) (![⟨88047, by decide⟩,⟨88139, by decide⟩,⟨88205, by decide⟩,⟨88247, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6661_88248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6661 ⟨88248, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6661
    ⟨88248, by decide⟩ (by decide) (![⟨88047, by decide⟩,⟨88139, by decide⟩,⟨88205, by decide⟩,⟨88247, by decide⟩]) unmarked_context_12_6661_88248 node_context_12_6661_88248
  intro a
  fin_cases a
  · exact context_13_26644_88047
  · exact context_13_26645_88139
  · exact context_13_26646_88205
  · exact context_13_26647_88247

theorem selected_cut_02861 : selected 7 ⟨88276, by decide⟩
    (prefixPartial 14 106592) = some ⟨14, 2, 0, 88276, 106592, 1389, 4096⟩ := by
  decide +kernel

theorem context_14_106592_88276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106592 ⟨88276, by decide⟩ :=
  accepted_of_selected 14 106592 ⟨88276, by decide⟩ ⟨14, 2, 0, 88276, 106592, 1389, 4096⟩
    (by decide) selected_cut_02861

theorem selected_cut_02862 : selected 7 ⟨88297, by decide⟩
    (prefixPartial 14 106593) = some ⟨14, 2, 0, 88297, 106593, 1217, 4096⟩ := by
  decide +kernel

theorem context_14_106593_88297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106593 ⟨88297, by decide⟩ :=
  accepted_of_selected 14 106593 ⟨88297, by decide⟩ ⟨14, 2, 0, 88297, 106593, 1217, 4096⟩
    (by decide) selected_cut_02862

theorem selected_cut_02863 : selected 7 ⟨88326, by decide⟩
    (prefixPartial 14 106594) = some ⟨14, 2, 0, 88326, 106594, 1473, 4096⟩ := by
  decide +kernel

theorem context_14_106594_88326 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106594 ⟨88326, by decide⟩ :=
  accepted_of_selected 14 106594 ⟨88326, by decide⟩ ⟨14, 2, 0, 88326, 106594, 1473, 4096⟩
    (by decide) selected_cut_02863

theorem selected_cut_02864 : selected 7 ⟨88348, by decide⟩
    (prefixPartial 14 106595) = some ⟨14, 2, 0, 88348, 106595, 1557, 4096⟩ := by
  decide +kernel

theorem context_14_106595_88348 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106595 ⟨88348, by decide⟩ :=
  accepted_of_selected 14 106595 ⟨88348, by decide⟩ ⟨14, 2, 0, 88348, 106595, 1557, 4096⟩
    (by decide) selected_cut_02864

theorem unmarked_context_13_26648_88349 : frontier 8 ⟨88349, by decide⟩
    (prefixCache 13 26648) (prefixPartial 13 26648) = false := by
  decide +kernel

theorem node_context_13_26648_88349 : EJMOriginalGlobalDAGData.nodes 8 ⟨88349, by decide⟩ =
    .split (coordinate 13) (![⟨88276, by decide⟩,⟨88297, by decide⟩,⟨88326, by decide⟩,⟨88348, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_26648_88349 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26648 ⟨88349, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 26648
    ⟨88349, by decide⟩ (by decide) (![⟨88276, by decide⟩,⟨88297, by decide⟩,⟨88326, by decide⟩,⟨88348, by decide⟩]) unmarked_context_13_26648_88349 node_context_13_26648_88349
  intro a
  fin_cases a
  · exact context_14_106592_88276
  · exact context_14_106593_88297
  · exact context_14_106594_88326
  · exact context_14_106595_88348

theorem selected_cut_02865 : selected 7 ⟨88366, by decide⟩
    (prefixPartial 14 106596) = some ⟨14, 2, 0, 88366, 106596, 1077, 4096⟩ := by
  decide +kernel

theorem context_14_106596_88366 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106596 ⟨88366, by decide⟩ :=
  accepted_of_selected 14 106596 ⟨88366, by decide⟩ ⟨14, 2, 0, 88366, 106596, 1077, 4096⟩
    (by decide) selected_cut_02865

theorem selected_cut_02866 : selected 7 ⟨88397, by decide⟩
    (prefixPartial 14 106597) = some ⟨14, 2, 0, 88397, 106597, 1281, 4096⟩ := by
  decide +kernel

theorem context_14_106597_88397 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106597 ⟨88397, by decide⟩ :=
  accepted_of_selected 14 106597 ⟨88397, by decide⟩ ⟨14, 2, 0, 88397, 106597, 1281, 4096⟩
    (by decide) selected_cut_02866

theorem selected_cut_02867 : selected 7 ⟨88428, by decide⟩
    (prefixPartial 14 106598) = some ⟨14, 2, 0, 88428, 106598, 1373, 4096⟩ := by
  decide +kernel

theorem context_14_106598_88428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106598 ⟨88428, by decide⟩ :=
  accepted_of_selected 14 106598 ⟨88428, by decide⟩ ⟨14, 2, 0, 88428, 106598, 1373, 4096⟩
    (by decide) selected_cut_02867

theorem selected_cut_02868 : selected 7 ⟨88451, by decide⟩
    (prefixPartial 14 106599) = some ⟨14, 2, 0, 88451, 106599, 1193, 4096⟩ := by
  decide +kernel

theorem context_14_106599_88451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106599 ⟨88451, by decide⟩ :=
  accepted_of_selected 14 106599 ⟨88451, by decide⟩ ⟨14, 2, 0, 88451, 106599, 1193, 4096⟩
    (by decide) selected_cut_02868

theorem unmarked_context_13_26649_88452 : frontier 8 ⟨88452, by decide⟩
    (prefixCache 13 26649) (prefixPartial 13 26649) = false := by
  decide +kernel

theorem node_context_13_26649_88452 : EJMOriginalGlobalDAGData.nodes 8 ⟨88452, by decide⟩ =
    .split (coordinate 13) (![⟨88366, by decide⟩,⟨88397, by decide⟩,⟨88428, by decide⟩,⟨88451, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_26649_88452 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26649 ⟨88452, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 26649
    ⟨88452, by decide⟩ (by decide) (![⟨88366, by decide⟩,⟨88397, by decide⟩,⟨88428, by decide⟩,⟨88451, by decide⟩]) unmarked_context_13_26649_88452 node_context_13_26649_88452
  intro a
  fin_cases a
  · exact context_14_106596_88366
  · exact context_14_106597_88397
  · exact context_14_106598_88428
  · exact context_14_106599_88451

theorem selected_cut_02869 : selected 8 ⟨88528, by decide⟩
    (prefixPartial 13 26650) = some ⟨13, 2, 0, 88528, 26650, 3165, 16384⟩ := by
  decide +kernel

theorem context_13_26650_88528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26650 ⟨88528, by decide⟩ :=
  accepted_of_selected 13 26650 ⟨88528, by decide⟩ ⟨13, 2, 0, 88528, 26650, 3165, 16384⟩
    (by decide) selected_cut_02869

theorem selected_cut_02870 : selected 8 ⟨88559, by decide⟩
    (prefixPartial 13 26651) = some ⟨13, 2, 0, 88559, 26651, 1697, 16384⟩ := by
  decide +kernel

theorem context_13_26651_88559 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26651 ⟨88559, by decide⟩ :=
  accepted_of_selected 13 26651 ⟨88559, by decide⟩ ⟨13, 2, 0, 88559, 26651, 1697, 16384⟩
    (by decide) selected_cut_02870

theorem unmarked_context_12_6662_88560 : frontier 9 ⟨88560, by decide⟩
    (prefixCache 12 6662) (prefixPartial 12 6662) = false := by
  decide +kernel

theorem node_context_12_6662_88560 : EJMOriginalGlobalDAGData.nodes 9 ⟨88560, by decide⟩ =
    .split (coordinate 12) (![⟨88349, by decide⟩,⟨88452, by decide⟩,⟨88528, by decide⟩,⟨88559, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6662_88560 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6662 ⟨88560, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6662
    ⟨88560, by decide⟩ (by decide) (![⟨88349, by decide⟩,⟨88452, by decide⟩,⟨88528, by decide⟩,⟨88559, by decide⟩]) unmarked_context_12_6662_88560 node_context_12_6662_88560
  intro a
  fin_cases a
  · exact context_13_26648_88349
  · exact context_13_26649_88452
  · exact context_13_26650_88528
  · exact context_13_26651_88559

theorem selected_cut_02871 : selected 7 ⟨88598, by decide⟩
    (prefixPartial 14 106608) = some ⟨14, 2, 0, 88598, 106608, 1601, 4096⟩ := by
  decide +kernel

theorem context_14_106608_88598 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106608 ⟨88598, by decide⟩ :=
  accepted_of_selected 14 106608 ⟨88598, by decide⟩ ⟨14, 2, 0, 88598, 106608, 1601, 4096⟩
    (by decide) selected_cut_02871

theorem selected_cut_02872 : selected 7 ⟨88631, by decide⟩
    (prefixPartial 14 106609) = some ⟨14, 2, 0, 88631, 106609, 1705, 4096⟩ := by
  decide +kernel

theorem context_14_106609_88631 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106609 ⟨88631, by decide⟩ :=
  accepted_of_selected 14 106609 ⟨88631, by decide⟩ ⟨14, 2, 0, 88631, 106609, 1705, 4096⟩
    (by decide) selected_cut_02872

theorem selected_cut_02873 : selected 7 ⟨88655, by decide⟩
    (prefixPartial 14 106610) = some ⟨14, 2, 0, 88655, 106610, 1589, 4096⟩ := by
  decide +kernel

theorem context_14_106610_88655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106610 ⟨88655, by decide⟩ :=
  accepted_of_selected 14 106610 ⟨88655, by decide⟩ ⟨14, 2, 0, 88655, 106610, 1589, 4096⟩
    (by decide) selected_cut_02873

theorem selected_cut_02874 : selected 7 ⟨88689, by decide⟩
    (prefixPartial 14 106611) = some ⟨14, 2, 0, 88689, 106611, 1993, 4096⟩ := by
  decide +kernel

theorem context_14_106611_88689 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106611 ⟨88689, by decide⟩ :=
  accepted_of_selected 14 106611 ⟨88689, by decide⟩ ⟨14, 2, 0, 88689, 106611, 1993, 4096⟩
    (by decide) selected_cut_02874

theorem unmarked_context_13_26652_88690 : frontier 8 ⟨88690, by decide⟩
    (prefixCache 13 26652) (prefixPartial 13 26652) = false := by
  decide +kernel

theorem node_context_13_26652_88690 : EJMOriginalGlobalDAGData.nodes 8 ⟨88690, by decide⟩ =
    .split (coordinate 13) (![⟨88598, by decide⟩,⟨88631, by decide⟩,⟨88655, by decide⟩,⟨88689, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_26652_88690 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26652 ⟨88690, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 26652
    ⟨88690, by decide⟩ (by decide) (![⟨88598, by decide⟩,⟨88631, by decide⟩,⟨88655, by decide⟩,⟨88689, by decide⟩]) unmarked_context_13_26652_88690 node_context_13_26652_88690
  intro a
  fin_cases a
  · exact context_14_106608_88598
  · exact context_14_106609_88631
  · exact context_14_106610_88655
  · exact context_14_106611_88689

theorem selected_cut_02875 : selected 7 ⟨88713, by decide⟩
    (prefixPartial 14 106612) = some ⟨14, 2, 0, 88713, 106612, 1385, 4096⟩ := by
  decide +kernel

theorem context_14_106612_88713 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106612 ⟨88713, by decide⟩ :=
  accepted_of_selected 14 106612 ⟨88713, by decide⟩ ⟨14, 2, 0, 88713, 106612, 1385, 4096⟩
    (by decide) selected_cut_02875

theorem selected_cut_02876 : selected 7 ⟨88748, by decide⟩
    (prefixPartial 14 106613) = some ⟨14, 2, 0, 88748, 106613, 1553, 4096⟩ := by
  decide +kernel

theorem context_14_106613_88748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106613 ⟨88748, by decide⟩ :=
  accepted_of_selected 14 106613 ⟨88748, by decide⟩ ⟨14, 2, 0, 88748, 106613, 1553, 4096⟩
    (by decide) selected_cut_02876

theorem selected_cut_02877 : selected 7 ⟨88775, by decide⟩
    (prefixPartial 14 106614) = some ⟨14, 2, 0, 88775, 106614, 1505, 4096⟩ := by
  decide +kernel

theorem context_14_106614_88775 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106614 ⟨88775, by decide⟩ :=
  accepted_of_selected 14 106614 ⟨88775, by decide⟩ ⟨14, 2, 0, 88775, 106614, 1505, 4096⟩
    (by decide) selected_cut_02877

theorem selected_cut_02878 : selected 7 ⟨88798, by decide⟩
    (prefixPartial 14 106615) = some ⟨14, 2, 0, 88798, 106615, 1377, 4096⟩ := by
  decide +kernel

theorem context_14_106615_88798 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 106615 ⟨88798, by decide⟩ :=
  accepted_of_selected 14 106615 ⟨88798, by decide⟩ ⟨14, 2, 0, 88798, 106615, 1377, 4096⟩
    (by decide) selected_cut_02878

theorem unmarked_context_13_26653_88799 : frontier 8 ⟨88799, by decide⟩
    (prefixCache 13 26653) (prefixPartial 13 26653) = false := by
  decide +kernel

theorem node_context_13_26653_88799 : EJMOriginalGlobalDAGData.nodes 8 ⟨88799, by decide⟩ =
    .split (coordinate 13) (![⟨88713, by decide⟩,⟨88748, by decide⟩,⟨88775, by decide⟩,⟨88798, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_26653_88799 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26653 ⟨88799, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 26653
    ⟨88799, by decide⟩ (by decide) (![⟨88713, by decide⟩,⟨88748, by decide⟩,⟨88775, by decide⟩,⟨88798, by decide⟩]) unmarked_context_13_26653_88799 node_context_13_26653_88799
  intro a
  fin_cases a
  · exact context_14_106612_88713
  · exact context_14_106613_88748
  · exact context_14_106614_88775
  · exact context_14_106615_88798

theorem selected_cut_02879 : selected 8 ⟨88867, by decide⟩
    (prefixPartial 13 26654) = some ⟨13, 2, 0, 88867, 26654, 3421, 16384⟩ := by
  decide +kernel

theorem context_13_26654_88867 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26654 ⟨88867, by decide⟩ :=
  accepted_of_selected 13 26654 ⟨88867, by decide⟩ ⟨13, 2, 0, 88867, 26654, 3421, 16384⟩
    (by decide) selected_cut_02879

theorem selected_cut_02880 : selected 8 ⟨88906, by decide⟩
    (prefixPartial 13 26655) = some ⟨13, 2, 0, 88906, 26655, 1757, 16384⟩ := by
  decide +kernel

theorem context_13_26655_88906 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 26655 ⟨88906, by decide⟩ :=
  accepted_of_selected 13 26655 ⟨88906, by decide⟩ ⟨13, 2, 0, 88906, 26655, 1757, 16384⟩
    (by decide) selected_cut_02880

theorem unmarked_context_12_6663_88907 : frontier 9 ⟨88907, by decide⟩
    (prefixCache 12 6663) (prefixPartial 12 6663) = false := by
  decide +kernel

theorem node_context_12_6663_88907 : EJMOriginalGlobalDAGData.nodes 9 ⟨88907, by decide⟩ =
    .split (coordinate 12) (![⟨88690, by decide⟩,⟨88799, by decide⟩,⟨88867, by decide⟩,⟨88906, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_6663_88907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6663 ⟨88907, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 6663
    ⟨88907, by decide⟩ (by decide) (![⟨88690, by decide⟩,⟨88799, by decide⟩,⟨88867, by decide⟩,⟨88906, by decide⟩]) unmarked_context_12_6663_88907 node_context_12_6663_88907
  intro a
  fin_cases a
  · exact context_13_26652_88690
  · exact context_13_26653_88799
  · exact context_13_26654_88867
  · exact context_13_26655_88906

theorem unmarked_context_11_1665_88908 : frontier 10 ⟨88908, by decide⟩
    (prefixCache 11 1665) (prefixPartial 11 1665) = false := by
  decide +kernel

theorem node_context_11_1665_88908 : EJMOriginalGlobalDAGData.nodes 10 ⟨88908, by decide⟩ =
    .split (coordinate 11) (![⟨87913, by decide⟩,⟨88248, by decide⟩,⟨88560, by decide⟩,⟨88907, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1665_88908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1665 ⟨88908, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1665
    ⟨88908, by decide⟩ (by decide) (![⟨87913, by decide⟩,⟨88248, by decide⟩,⟨88560, by decide⟩,⟨88907, by decide⟩]) unmarked_context_11_1665_88908 node_context_11_1665_88908
  intro a
  fin_cases a
  · exact context_12_6660_87913
  · exact context_12_6661_88248
  · exact context_12_6662_88560
  · exact context_12_6663_88907

theorem selected_cut_02881 : selected 9 ⟨88909, by decide⟩
    (prefixPartial 12 6664) = some ⟨12, 1, 0, 88909, 6664, 1, 65536⟩ := by
  decide +kernel

theorem context_12_6664_88909 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 6664 ⟨88909, by decide⟩ :=
  accepted_of_selected 12 6664 ⟨88909, by decide⟩ ⟨12, 1, 0, 88909, 6664, 1, 65536⟩
    (by decide) selected_cut_02881

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
