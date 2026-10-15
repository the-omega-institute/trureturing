/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover327
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_31492 : selected 8 ⟨808495, by decide⟩
    (prefixPartial 13 424102) = some ⟨13, 2, 0, 808495, 424102, 1513, 16384⟩ := by
  decide +kernel

theorem context_13_424102_808495 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424102 ⟨808495, by decide⟩ :=
  accepted_of_selected 13 424102 ⟨808495, by decide⟩ ⟨13, 2, 0, 808495, 424102, 1513, 16384⟩
    (by decide) selected_cut_31492

theorem selected_cut_31493 : selected 8 ⟨808504, by decide⟩
    (prefixPartial 13 424103) = some ⟨13, 2, 0, 808504, 424103, 821, 16384⟩ := by
  decide +kernel

theorem context_13_424103_808504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424103 ⟨808504, by decide⟩ :=
  accepted_of_selected 13 424103 ⟨808504, by decide⟩ ⟨13, 2, 0, 808504, 424103, 821, 16384⟩
    (by decide) selected_cut_31493

theorem unmarked_context_12_106025_808505 : frontier 9 ⟨808505, by decide⟩
    (prefixCache 12 106025) (prefixPartial 12 106025) = false := by
  decide +kernel

theorem node_context_12_106025_808505 : EJMOriginalGlobalDAGData.nodes 9 ⟨808505, by decide⟩ =
    .split (coordinate 12) (![⟨808426, by decide⟩,⟨808471, by decide⟩,⟨808495, by decide⟩,⟨808504, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_106025_808505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106025 ⟨808505, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 106025
    ⟨808505, by decide⟩ (by decide) (![⟨808426, by decide⟩,⟨808471, by decide⟩,⟨808495, by decide⟩,⟨808504, by decide⟩]) unmarked_context_12_106025_808505 node_context_12_106025_808505
  intro a
  fin_cases a
  · exact context_13_424100_808426
  · exact context_13_424101_808471
  · exact context_13_424102_808495
  · exact context_13_424103_808504

theorem selected_cut_31494 : selected 9 ⟨445248, by decide⟩
    (prefixPartial 12 106026) = some ⟨12, 1, 0, 445248, 106026, 1, 65536⟩ := by
  decide +kernel

theorem context_12_106026_445248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106026 ⟨445248, by decide⟩ :=
  accepted_of_selected 12 106026 ⟨445248, by decide⟩ ⟨12, 1, 0, 445248, 106026, 1, 65536⟩
    (by decide) selected_cut_31494

theorem selected_cut_31495 : selected 8 ⟨808520, by decide⟩
    (prefixPartial 13 424108) = some ⟨13, 2, 0, 808520, 424108, 881, 16384⟩ := by
  decide +kernel

theorem context_13_424108_808520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424108 ⟨808520, by decide⟩ :=
  accepted_of_selected 13 424108 ⟨808520, by decide⟩ ⟨13, 2, 0, 808520, 424108, 881, 16384⟩
    (by decide) selected_cut_31495

theorem selected_cut_31496 : selected 8 ⟨808564, by decide⟩
    (prefixPartial 13 424109) = some ⟨13, 2, 0, 808564, 424109, 2765, 16384⟩ := by
  decide +kernel

theorem context_13_424109_808564 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424109 ⟨808564, by decide⟩ :=
  accepted_of_selected 13 424109 ⟨808564, by decide⟩ ⟨13, 2, 0, 808564, 424109, 2765, 16384⟩
    (by decide) selected_cut_31496

theorem selected_cut_31497 : selected 8 ⟨808587, by decide⟩
    (prefixPartial 13 424110) = some ⟨13, 2, 0, 808587, 424110, 1629, 16384⟩ := by
  decide +kernel

theorem context_13_424110_808587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424110 ⟨808587, by decide⟩ :=
  accepted_of_selected 13 424110 ⟨808587, by decide⟩ ⟨13, 2, 0, 808587, 424110, 1629, 16384⟩
    (by decide) selected_cut_31497

theorem selected_cut_31498 : selected 8 ⟨808594, by decide⟩
    (prefixPartial 13 424111) = some ⟨13, 2, 0, 808594, 424111, 917, 16384⟩ := by
  decide +kernel

theorem context_13_424111_808594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424111 ⟨808594, by decide⟩ :=
  accepted_of_selected 13 424111 ⟨808594, by decide⟩ ⟨13, 2, 0, 808594, 424111, 917, 16384⟩
    (by decide) selected_cut_31498

theorem unmarked_context_12_106027_808595 : frontier 9 ⟨808595, by decide⟩
    (prefixCache 12 106027) (prefixPartial 12 106027) = false := by
  decide +kernel

theorem node_context_12_106027_808595 : EJMOriginalGlobalDAGData.nodes 9 ⟨808595, by decide⟩ =
    .split (coordinate 12) (![⟨808520, by decide⟩,⟨808564, by decide⟩,⟨808587, by decide⟩,⟨808594, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_106027_808595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106027 ⟨808595, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 106027
    ⟨808595, by decide⟩ (by decide) (![⟨808520, by decide⟩,⟨808564, by decide⟩,⟨808587, by decide⟩,⟨808594, by decide⟩]) unmarked_context_12_106027_808595 node_context_12_106027_808595
  intro a
  fin_cases a
  · exact context_13_424108_808520
  · exact context_13_424109_808564
  · exact context_13_424110_808587
  · exact context_13_424111_808594

theorem unmarked_context_11_26506_808596 : frontier 10 ⟨808596, by decide⟩
    (prefixCache 11 26506) (prefixPartial 11 26506) = false := by
  decide +kernel

theorem node_context_11_26506_808596 : EJMOriginalGlobalDAGData.nodes 10 ⟨808596, by decide⟩ =
    .split (coordinate 11) (![⟨808407, by decide⟩,⟨808505, by decide⟩,⟨445248, by decide⟩,⟨808595, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26506_808596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26506 ⟨808596, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26506
    ⟨808596, by decide⟩ (by decide) (![⟨808407, by decide⟩,⟨808505, by decide⟩,⟨445248, by decide⟩,⟨808595, by decide⟩]) unmarked_context_11_26506_808596 node_context_11_26506_808596
  intro a
  fin_cases a
  · exact context_12_106024_808407
  · exact context_12_106025_808505
  · exact context_12_106026_445248
  · exact context_12_106027_808595

theorem selected_cut_31499 : selected 8 ⟨808607, by decide⟩
    (prefixPartial 13 424112) = some ⟨13, 2, 0, 808607, 424112, 573, 16384⟩ := by
  decide +kernel

theorem context_13_424112_808607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424112 ⟨808607, by decide⟩ :=
  accepted_of_selected 13 424112 ⟨808607, by decide⟩ ⟨13, 2, 0, 808607, 424112, 573, 16384⟩
    (by decide) selected_cut_31499

theorem selected_cut_31500 : selected 8 ⟨808636, by decide⟩
    (prefixPartial 13 424113) = some ⟨13, 2, 0, 808636, 424113, 2125, 16384⟩ := by
  decide +kernel

theorem context_13_424113_808636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424113 ⟨808636, by decide⟩ :=
  accepted_of_selected 13 424113 ⟨808636, by decide⟩ ⟨13, 2, 0, 808636, 424113, 2125, 16384⟩
    (by decide) selected_cut_31500

theorem selected_cut_31501 : selected 8 ⟨808658, by decide⟩
    (prefixPartial 13 424114) = some ⟨13, 2, 0, 808658, 424114, 1517, 16384⟩ := by
  decide +kernel

theorem context_13_424114_808658 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424114 ⟨808658, by decide⟩ :=
  accepted_of_selected 13 424114 ⟨808658, by decide⟩ ⟨13, 2, 0, 808658, 424114, 1517, 16384⟩
    (by decide) selected_cut_31501

theorem selected_cut_31502 : selected 8 ⟨808669, by decide⟩
    (prefixPartial 13 424115) = some ⟨13, 2, 0, 808669, 424115, 901, 16384⟩ := by
  decide +kernel

theorem context_13_424115_808669 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424115 ⟨808669, by decide⟩ :=
  accepted_of_selected 13 424115 ⟨808669, by decide⟩ ⟨13, 2, 0, 808669, 424115, 901, 16384⟩
    (by decide) selected_cut_31502

theorem unmarked_context_12_106028_808670 : frontier 9 ⟨808670, by decide⟩
    (prefixCache 12 106028) (prefixPartial 12 106028) = false := by
  decide +kernel

theorem node_context_12_106028_808670 : EJMOriginalGlobalDAGData.nodes 9 ⟨808670, by decide⟩ =
    .split (coordinate 12) (![⟨808607, by decide⟩,⟨808636, by decide⟩,⟨808658, by decide⟩,⟨808669, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_106028_808670 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106028 ⟨808670, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 106028
    ⟨808670, by decide⟩ (by decide) (![⟨808607, by decide⟩,⟨808636, by decide⟩,⟨808658, by decide⟩,⟨808669, by decide⟩]) unmarked_context_12_106028_808670 node_context_12_106028_808670
  intro a
  fin_cases a
  · exact context_13_424112_808607
  · exact context_13_424113_808636
  · exact context_13_424114_808658
  · exact context_13_424115_808669

theorem selected_cut_31503 : selected 8 ⟨808682, by decide⟩
    (prefixPartial 13 424116) = some ⟨13, 2, 0, 808682, 424116, 689, 16384⟩ := by
  decide +kernel

theorem context_13_424116_808682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424116 ⟨808682, by decide⟩ :=
  accepted_of_selected 13 424116 ⟨808682, by decide⟩ ⟨13, 2, 0, 808682, 424116, 689, 16384⟩
    (by decide) selected_cut_31503

theorem selected_cut_31504 : selected 8 ⟨808725, by decide⟩
    (prefixPartial 13 424117) = some ⟨13, 2, 0, 808725, 424117, 2389, 16384⟩ := by
  decide +kernel

theorem context_13_424117_808725 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424117 ⟨808725, by decide⟩ :=
  accepted_of_selected 13 424117 ⟨808725, by decide⟩ ⟨13, 2, 0, 808725, 424117, 2389, 16384⟩
    (by decide) selected_cut_31504

theorem selected_cut_31505 : selected 8 ⟨808749, by decide⟩
    (prefixPartial 13 424118) = some ⟨13, 2, 0, 808749, 424118, 1413, 16384⟩ := by
  decide +kernel

theorem context_13_424118_808749 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424118 ⟨808749, by decide⟩ :=
  accepted_of_selected 13 424118 ⟨808749, by decide⟩ ⟨13, 2, 0, 808749, 424118, 1413, 16384⟩
    (by decide) selected_cut_31505

theorem selected_cut_31506 : selected 8 ⟨808765, by decide⟩
    (prefixPartial 13 424119) = some ⟨13, 2, 0, 808765, 424119, 849, 16384⟩ := by
  decide +kernel

theorem context_13_424119_808765 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424119 ⟨808765, by decide⟩ :=
  accepted_of_selected 13 424119 ⟨808765, by decide⟩ ⟨13, 2, 0, 808765, 424119, 849, 16384⟩
    (by decide) selected_cut_31506

theorem unmarked_context_12_106029_808766 : frontier 9 ⟨808766, by decide⟩
    (prefixCache 12 106029) (prefixPartial 12 106029) = false := by
  decide +kernel

theorem node_context_12_106029_808766 : EJMOriginalGlobalDAGData.nodes 9 ⟨808766, by decide⟩ =
    .split (coordinate 12) (![⟨808682, by decide⟩,⟨808725, by decide⟩,⟨808749, by decide⟩,⟨808765, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_106029_808766 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106029 ⟨808766, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 106029
    ⟨808766, by decide⟩ (by decide) (![⟨808682, by decide⟩,⟨808725, by decide⟩,⟨808749, by decide⟩,⟨808765, by decide⟩]) unmarked_context_12_106029_808766 node_context_12_106029_808766
  intro a
  fin_cases a
  · exact context_13_424116_808682
  · exact context_13_424117_808725
  · exact context_13_424118_808749
  · exact context_13_424119_808765

theorem selected_cut_31507 : selected 8 ⟨808779, by decide⟩
    (prefixPartial 13 424120) = some ⟨13, 2, 0, 808779, 424120, 505, 16384⟩ := by
  decide +kernel

theorem context_13_424120_808779 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424120 ⟨808779, by decide⟩ :=
  accepted_of_selected 13 424120 ⟨808779, by decide⟩ ⟨13, 2, 0, 808779, 424120, 505, 16384⟩
    (by decide) selected_cut_31507

theorem selected_cut_31508 : selected 8 ⟨808805, by decide⟩
    (prefixPartial 13 424121) = some ⟨13, 2, 0, 808805, 424121, 2297, 16384⟩ := by
  decide +kernel

theorem context_13_424121_808805 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424121 ⟨808805, by decide⟩ :=
  accepted_of_selected 13 424121 ⟨808805, by decide⟩ ⟨13, 2, 0, 808805, 424121, 2297, 16384⟩
    (by decide) selected_cut_31508

theorem selected_cut_31509 : selected 8 ⟨808826, by decide⟩
    (prefixPartial 13 424122) = some ⟨13, 2, 0, 808826, 424122, 1353, 16384⟩ := by
  decide +kernel

theorem context_13_424122_808826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424122 ⟨808826, by decide⟩ :=
  accepted_of_selected 13 424122 ⟨808826, by decide⟩ ⟨13, 2, 0, 808826, 424122, 1353, 16384⟩
    (by decide) selected_cut_31509

theorem selected_cut_31510 : selected 8 ⟨808831, by decide⟩
    (prefixPartial 13 424123) = some ⟨13, 2, 0, 808831, 424123, 905, 16384⟩ := by
  decide +kernel

theorem context_13_424123_808831 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424123 ⟨808831, by decide⟩ :=
  accepted_of_selected 13 424123 ⟨808831, by decide⟩ ⟨13, 2, 0, 808831, 424123, 905, 16384⟩
    (by decide) selected_cut_31510

theorem unmarked_context_12_106030_808832 : frontier 9 ⟨808832, by decide⟩
    (prefixCache 12 106030) (prefixPartial 12 106030) = false := by
  decide +kernel

theorem node_context_12_106030_808832 : EJMOriginalGlobalDAGData.nodes 9 ⟨808832, by decide⟩ =
    .split (coordinate 12) (![⟨808779, by decide⟩,⟨808805, by decide⟩,⟨808826, by decide⟩,⟨808831, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_106030_808832 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106030 ⟨808832, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 106030
    ⟨808832, by decide⟩ (by decide) (![⟨808779, by decide⟩,⟨808805, by decide⟩,⟨808826, by decide⟩,⟨808831, by decide⟩]) unmarked_context_12_106030_808832 node_context_12_106030_808832
  intro a
  fin_cases a
  · exact context_13_424120_808779
  · exact context_13_424121_808805
  · exact context_13_424122_808826
  · exact context_13_424123_808831

theorem selected_cut_31511 : selected 8 ⟨808845, by decide⟩
    (prefixPartial 13 424124) = some ⟨13, 2, 0, 808845, 424124, 669, 16384⟩ := by
  decide +kernel

theorem context_13_424124_808845 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424124 ⟨808845, by decide⟩ :=
  accepted_of_selected 13 424124 ⟨808845, by decide⟩ ⟨13, 2, 0, 808845, 424124, 669, 16384⟩
    (by decide) selected_cut_31511

theorem selected_cut_31512 : selected 8 ⟨808881, by decide⟩
    (prefixPartial 13 424125) = some ⟨13, 2, 0, 808881, 424125, 2677, 16384⟩ := by
  decide +kernel

theorem context_13_424125_808881 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424125 ⟨808881, by decide⟩ :=
  accepted_of_selected 13 424125 ⟨808881, by decide⟩ ⟨13, 2, 0, 808881, 424125, 2677, 16384⟩
    (by decide) selected_cut_31512

theorem selected_cut_31513 : selected 8 ⟨808900, by decide⟩
    (prefixPartial 13 424126) = some ⟨13, 2, 0, 808900, 424126, 1653, 16384⟩ := by
  decide +kernel

theorem context_13_424126_808900 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424126 ⟨808900, by decide⟩ :=
  accepted_of_selected 13 424126 ⟨808900, by decide⟩ ⟨13, 2, 0, 808900, 424126, 1653, 16384⟩
    (by decide) selected_cut_31513

theorem selected_cut_31514 : selected 8 ⟨808909, by decide⟩
    (prefixPartial 13 424127) = some ⟨13, 2, 0, 808909, 424127, 1005, 16384⟩ := by
  decide +kernel

theorem context_13_424127_808909 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424127 ⟨808909, by decide⟩ :=
  accepted_of_selected 13 424127 ⟨808909, by decide⟩ ⟨13, 2, 0, 808909, 424127, 1005, 16384⟩
    (by decide) selected_cut_31514

theorem unmarked_context_12_106031_808910 : frontier 9 ⟨808910, by decide⟩
    (prefixCache 12 106031) (prefixPartial 12 106031) = false := by
  decide +kernel

theorem node_context_12_106031_808910 : EJMOriginalGlobalDAGData.nodes 9 ⟨808910, by decide⟩ =
    .split (coordinate 12) (![⟨808845, by decide⟩,⟨808881, by decide⟩,⟨808900, by decide⟩,⟨808909, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_106031_808910 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106031 ⟨808910, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 106031
    ⟨808910, by decide⟩ (by decide) (![⟨808845, by decide⟩,⟨808881, by decide⟩,⟨808900, by decide⟩,⟨808909, by decide⟩]) unmarked_context_12_106031_808910 node_context_12_106031_808910
  intro a
  fin_cases a
  · exact context_13_424124_808845
  · exact context_13_424125_808881
  · exact context_13_424126_808900
  · exact context_13_424127_808909

theorem unmarked_context_11_26507_808911 : frontier 10 ⟨808911, by decide⟩
    (prefixCache 11 26507) (prefixPartial 11 26507) = false := by
  decide +kernel

theorem node_context_11_26507_808911 : EJMOriginalGlobalDAGData.nodes 10 ⟨808911, by decide⟩ =
    .split (coordinate 11) (![⟨808670, by decide⟩,⟨808766, by decide⟩,⟨808832, by decide⟩,⟨808910, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26507_808911 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26507 ⟨808911, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26507
    ⟨808911, by decide⟩ (by decide) (![⟨808670, by decide⟩,⟨808766, by decide⟩,⟨808832, by decide⟩,⟨808910, by decide⟩]) unmarked_context_11_26507_808911 node_context_11_26507_808911
  intro a
  fin_cases a
  · exact context_12_106028_808670
  · exact context_12_106029_808766
  · exact context_12_106030_808832
  · exact context_12_106031_808910

theorem unmarked_context_10_6626_808912 : frontier 11 ⟨808912, by decide⟩
    (prefixCache 10 6626) (prefixPartial 10 6626) = false := by
  decide +kernel

theorem node_context_10_6626_808912 : EJMOriginalGlobalDAGData.nodes 11 ⟨808912, by decide⟩ =
    .split (coordinate 10) (![⟨807881, by decide⟩,⟨808327, by decide⟩,⟨808596, by decide⟩,⟨808911, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6626_808912 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6626 ⟨808912, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6626
    ⟨808912, by decide⟩ (by decide) (![⟨807881, by decide⟩,⟨808327, by decide⟩,⟨808596, by decide⟩,⟨808911, by decide⟩]) unmarked_context_10_6626_808912 node_context_10_6626_808912
  intro a
  fin_cases a
  · exact context_11_26504_807881
  · exact context_11_26505_808327
  · exact context_11_26506_808596
  · exact context_11_26507_808911

theorem selected_cut_31515 : selected 8 ⟨808925, by decide⟩
    (prefixPartial 13 424128) = some ⟨13, 2, 0, 808925, 424128, 773, 16384⟩ := by
  decide +kernel

theorem context_13_424128_808925 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424128 ⟨808925, by decide⟩ :=
  accepted_of_selected 13 424128 ⟨808925, by decide⟩ ⟨13, 2, 0, 808925, 424128, 773, 16384⟩
    (by decide) selected_cut_31515

theorem selected_cut_31516 : selected 8 ⟨808968, by decide⟩
    (prefixPartial 13 424129) = some ⟨13, 2, 0, 808968, 424129, 2633, 16384⟩ := by
  decide +kernel

theorem context_13_424129_808968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424129 ⟨808968, by decide⟩ :=
  accepted_of_selected 13 424129 ⟨808968, by decide⟩ ⟨13, 2, 0, 808968, 424129, 2633, 16384⟩
    (by decide) selected_cut_31516

theorem selected_cut_31517 : selected 8 ⟨808992, by decide⟩
    (prefixPartial 13 424130) = some ⟨13, 2, 0, 808992, 424130, 1497, 16384⟩ := by
  decide +kernel

theorem context_13_424130_808992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424130 ⟨808992, by decide⟩ :=
  accepted_of_selected 13 424130 ⟨808992, by decide⟩ ⟨13, 2, 0, 808992, 424130, 1497, 16384⟩
    (by decide) selected_cut_31517

theorem selected_cut_31518 : selected 8 ⟨809003, by decide⟩
    (prefixPartial 13 424131) = some ⟨13, 2, 0, 809003, 424131, 753, 16384⟩ := by
  decide +kernel

theorem context_13_424131_809003 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424131 ⟨809003, by decide⟩ :=
  accepted_of_selected 13 424131 ⟨809003, by decide⟩ ⟨13, 2, 0, 809003, 424131, 753, 16384⟩
    (by decide) selected_cut_31518

theorem unmarked_context_12_106032_809004 : frontier 9 ⟨809004, by decide⟩
    (prefixCache 12 106032) (prefixPartial 12 106032) = false := by
  decide +kernel

theorem node_context_12_106032_809004 : EJMOriginalGlobalDAGData.nodes 9 ⟨809004, by decide⟩ =
    .split (coordinate 12) (![⟨808925, by decide⟩,⟨808968, by decide⟩,⟨808992, by decide⟩,⟨809003, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_106032_809004 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106032 ⟨809004, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 106032
    ⟨809004, by decide⟩ (by decide) (![⟨808925, by decide⟩,⟨808968, by decide⟩,⟨808992, by decide⟩,⟨809003, by decide⟩]) unmarked_context_12_106032_809004 node_context_12_106032_809004
  intro a
  fin_cases a
  · exact context_13_424128_808925
  · exact context_13_424129_808968
  · exact context_13_424130_808992
  · exact context_13_424131_809003

theorem selected_cut_31519 : selected 8 ⟨809015, by decide⟩
    (prefixPartial 13 424132) = some ⟨13, 2, 0, 809015, 424132, 665, 16384⟩ := by
  decide +kernel

theorem context_13_424132_809015 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424132 ⟨809015, by decide⟩ :=
  accepted_of_selected 13 424132 ⟨809015, by decide⟩ ⟨13, 2, 0, 809015, 424132, 665, 16384⟩
    (by decide) selected_cut_31519

theorem selected_cut_31520 : selected 8 ⟨809051, by decide⟩
    (prefixPartial 13 424133) = some ⟨13, 2, 0, 809051, 424133, 2733, 16384⟩ := by
  decide +kernel

theorem context_13_424133_809051 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424133 ⟨809051, by decide⟩ :=
  accepted_of_selected 13 424133 ⟨809051, by decide⟩ ⟨13, 2, 0, 809051, 424133, 2733, 16384⟩
    (by decide) selected_cut_31520

theorem selected_cut_31521 : selected 8 ⟨809078, by decide⟩
    (prefixPartial 13 424134) = some ⟨13, 2, 0, 809078, 424134, 1517, 16384⟩ := by
  decide +kernel

theorem context_13_424134_809078 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424134 ⟨809078, by decide⟩ :=
  accepted_of_selected 13 424134 ⟨809078, by decide⟩ ⟨13, 2, 0, 809078, 424134, 1517, 16384⟩
    (by decide) selected_cut_31521

theorem selected_cut_31522 : selected 8 ⟨809088, by decide⟩
    (prefixPartial 13 424135) = some ⟨13, 2, 0, 809088, 424135, 953, 16384⟩ := by
  decide +kernel

theorem context_13_424135_809088 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424135 ⟨809088, by decide⟩ :=
  accepted_of_selected 13 424135 ⟨809088, by decide⟩ ⟨13, 2, 0, 809088, 424135, 953, 16384⟩
    (by decide) selected_cut_31522

theorem unmarked_context_12_106033_809089 : frontier 9 ⟨809089, by decide⟩
    (prefixCache 12 106033) (prefixPartial 12 106033) = false := by
  decide +kernel

theorem node_context_12_106033_809089 : EJMOriginalGlobalDAGData.nodes 9 ⟨809089, by decide⟩ =
    .split (coordinate 12) (![⟨809015, by decide⟩,⟨809051, by decide⟩,⟨809078, by decide⟩,⟨809088, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_106033_809089 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106033 ⟨809089, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 106033
    ⟨809089, by decide⟩ (by decide) (![⟨809015, by decide⟩,⟨809051, by decide⟩,⟨809078, by decide⟩,⟨809088, by decide⟩]) unmarked_context_12_106033_809089 node_context_12_106033_809089
  intro a
  fin_cases a
  · exact context_13_424132_809015
  · exact context_13_424133_809051
  · exact context_13_424134_809078
  · exact context_13_424135_809088

theorem selected_cut_31523 : selected 8 ⟨809099, by decide⟩
    (prefixPartial 13 424136) = some ⟨13, 2, 0, 809099, 424136, 489, 16384⟩ := by
  decide +kernel

theorem context_13_424136_809099 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424136 ⟨809099, by decide⟩ :=
  accepted_of_selected 13 424136 ⟨809099, by decide⟩ ⟨13, 2, 0, 809099, 424136, 489, 16384⟩
    (by decide) selected_cut_31523

theorem selected_cut_31524 : selected 8 ⟨809130, by decide⟩
    (prefixPartial 13 424137) = some ⟨13, 2, 0, 809130, 424137, 2649, 16384⟩ := by
  decide +kernel

theorem context_13_424137_809130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424137 ⟨809130, by decide⟩ :=
  accepted_of_selected 13 424137 ⟨809130, by decide⟩ ⟨13, 2, 0, 809130, 424137, 2649, 16384⟩
    (by decide) selected_cut_31524

theorem selected_cut_31525 : selected 8 ⟨809149, by decide⟩
    (prefixPartial 13 424138) = some ⟨13, 2, 0, 809149, 424138, 1197, 16384⟩ := by
  decide +kernel

theorem context_13_424138_809149 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424138 ⟨809149, by decide⟩ :=
  accepted_of_selected 13 424138 ⟨809149, by decide⟩ ⟨13, 2, 0, 809149, 424138, 1197, 16384⟩
    (by decide) selected_cut_31525

theorem selected_cut_31526 : selected 8 ⟨809154, by decide⟩
    (prefixPartial 13 424139) = some ⟨13, 2, 0, 809154, 424139, 917, 16384⟩ := by
  decide +kernel

theorem context_13_424139_809154 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424139 ⟨809154, by decide⟩ :=
  accepted_of_selected 13 424139 ⟨809154, by decide⟩ ⟨13, 2, 0, 809154, 424139, 917, 16384⟩
    (by decide) selected_cut_31526

theorem unmarked_context_12_106034_809155 : frontier 9 ⟨809155, by decide⟩
    (prefixCache 12 106034) (prefixPartial 12 106034) = false := by
  decide +kernel

theorem node_context_12_106034_809155 : EJMOriginalGlobalDAGData.nodes 9 ⟨809155, by decide⟩ =
    .split (coordinate 12) (![⟨809099, by decide⟩,⟨809130, by decide⟩,⟨809149, by decide⟩,⟨809154, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_106034_809155 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106034 ⟨809155, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 106034
    ⟨809155, by decide⟩ (by decide) (![⟨809099, by decide⟩,⟨809130, by decide⟩,⟨809149, by decide⟩,⟨809154, by decide⟩]) unmarked_context_12_106034_809155 node_context_12_106034_809155
  intro a
  fin_cases a
  · exact context_13_424136_809099
  · exact context_13_424137_809130
  · exact context_13_424138_809149
  · exact context_13_424139_809154

theorem selected_cut_31527 : selected 8 ⟨809171, by decide⟩
    (prefixPartial 13 424140) = some ⟨13, 2, 0, 809171, 424140, 669, 16384⟩ := by
  decide +kernel

theorem context_13_424140_809171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424140 ⟨809171, by decide⟩ :=
  accepted_of_selected 13 424140 ⟨809171, by decide⟩ ⟨13, 2, 0, 809171, 424140, 669, 16384⟩
    (by decide) selected_cut_31527

theorem selected_cut_31528 : selected 8 ⟨809228, by decide⟩
    (prefixPartial 13 424141) = some ⟨13, 2, 0, 809228, 424141, 3393, 16384⟩ := by
  decide +kernel

theorem context_13_424141_809228 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424141 ⟨809228, by decide⟩ :=
  accepted_of_selected 13 424141 ⟨809228, by decide⟩ ⟨13, 2, 0, 809228, 424141, 3393, 16384⟩
    (by decide) selected_cut_31528

theorem selected_cut_31529 : selected 8 ⟨809252, by decide⟩
    (prefixPartial 13 424142) = some ⟨13, 2, 0, 809252, 424142, 1713, 16384⟩ := by
  decide +kernel

theorem context_13_424142_809252 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424142 ⟨809252, by decide⟩ :=
  accepted_of_selected 13 424142 ⟨809252, by decide⟩ ⟨13, 2, 0, 809252, 424142, 1713, 16384⟩
    (by decide) selected_cut_31529

theorem selected_cut_31530 : selected 8 ⟨809267, by decide⟩
    (prefixPartial 13 424143) = some ⟨13, 2, 0, 809267, 424143, 1021, 16384⟩ := by
  decide +kernel

theorem context_13_424143_809267 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424143 ⟨809267, by decide⟩ :=
  accepted_of_selected 13 424143 ⟨809267, by decide⟩ ⟨13, 2, 0, 809267, 424143, 1021, 16384⟩
    (by decide) selected_cut_31530

theorem unmarked_context_12_106035_809268 : frontier 9 ⟨809268, by decide⟩
    (prefixCache 12 106035) (prefixPartial 12 106035) = false := by
  decide +kernel

theorem node_context_12_106035_809268 : EJMOriginalGlobalDAGData.nodes 9 ⟨809268, by decide⟩ =
    .split (coordinate 12) (![⟨809171, by decide⟩,⟨809228, by decide⟩,⟨809252, by decide⟩,⟨809267, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_106035_809268 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106035 ⟨809268, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 106035
    ⟨809268, by decide⟩ (by decide) (![⟨809171, by decide⟩,⟨809228, by decide⟩,⟨809252, by decide⟩,⟨809267, by decide⟩]) unmarked_context_12_106035_809268 node_context_12_106035_809268
  intro a
  fin_cases a
  · exact context_13_424140_809171
  · exact context_13_424141_809228
  · exact context_13_424142_809252
  · exact context_13_424143_809267

theorem unmarked_context_11_26508_809269 : frontier 10 ⟨809269, by decide⟩
    (prefixCache 11 26508) (prefixPartial 11 26508) = false := by
  decide +kernel

theorem node_context_11_26508_809269 : EJMOriginalGlobalDAGData.nodes 10 ⟨809269, by decide⟩ =
    .split (coordinate 11) (![⟨809004, by decide⟩,⟨809089, by decide⟩,⟨809155, by decide⟩,⟨809268, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26508_809269 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26508 ⟨809269, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26508
    ⟨809269, by decide⟩ (by decide) (![⟨809004, by decide⟩,⟨809089, by decide⟩,⟨809155, by decide⟩,⟨809268, by decide⟩]) unmarked_context_11_26508_809269 node_context_11_26508_809269
  intro a
  fin_cases a
  · exact context_12_106032_809004
  · exact context_12_106033_809089
  · exact context_12_106034_809155
  · exact context_12_106035_809268

theorem selected_cut_31531 : selected 8 ⟨809278, by decide⟩
    (prefixPartial 13 424144) = some ⟨13, 2, 0, 809278, 424144, 533, 16384⟩ := by
  decide +kernel

theorem context_13_424144_809278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424144 ⟨809278, by decide⟩ :=
  accepted_of_selected 13 424144 ⟨809278, by decide⟩ ⟨13, 2, 0, 809278, 424144, 533, 16384⟩
    (by decide) selected_cut_31531

theorem selected_cut_31532 : selected 8 ⟨809343, by decide⟩
    (prefixPartial 13 424145) = some ⟨13, 2, 0, 809343, 424145, 3185, 16384⟩ := by
  decide +kernel

theorem context_13_424145_809343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424145 ⟨809343, by decide⟩ :=
  accepted_of_selected 13 424145 ⟨809343, by decide⟩ ⟨13, 2, 0, 809343, 424145, 3185, 16384⟩
    (by decide) selected_cut_31532

theorem selected_cut_31533 : selected 8 ⟨809376, by decide⟩
    (prefixPartial 13 424146) = some ⟨13, 2, 0, 809376, 424146, 1737, 16384⟩ := by
  decide +kernel

theorem context_13_424146_809376 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424146 ⟨809376, by decide⟩ :=
  accepted_of_selected 13 424146 ⟨809376, by decide⟩ ⟨13, 2, 0, 809376, 424146, 1737, 16384⟩
    (by decide) selected_cut_31533

theorem selected_cut_31534 : selected 8 ⟨809385, by decide⟩
    (prefixPartial 13 424147) = some ⟨13, 2, 0, 809385, 424147, 709, 16384⟩ := by
  decide +kernel

theorem context_13_424147_809385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424147 ⟨809385, by decide⟩ :=
  accepted_of_selected 13 424147 ⟨809385, by decide⟩ ⟨13, 2, 0, 809385, 424147, 709, 16384⟩
    (by decide) selected_cut_31534

theorem unmarked_context_12_106036_809386 : frontier 9 ⟨809386, by decide⟩
    (prefixCache 12 106036) (prefixPartial 12 106036) = false := by
  decide +kernel

theorem node_context_12_106036_809386 : EJMOriginalGlobalDAGData.nodes 9 ⟨809386, by decide⟩ =
    .split (coordinate 12) (![⟨809278, by decide⟩,⟨809343, by decide⟩,⟨809376, by decide⟩,⟨809385, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_106036_809386 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106036 ⟨809386, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 106036
    ⟨809386, by decide⟩ (by decide) (![⟨809278, by decide⟩,⟨809343, by decide⟩,⟨809376, by decide⟩,⟨809385, by decide⟩]) unmarked_context_12_106036_809386 node_context_12_106036_809386
  intro a
  fin_cases a
  · exact context_13_424144_809278
  · exact context_13_424145_809343
  · exact context_13_424146_809376
  · exact context_13_424147_809385

theorem selected_cut_31535 : selected 8 ⟨809395, by decide⟩
    (prefixPartial 13 424148) = some ⟨13, 2, 0, 809395, 424148, 405, 16384⟩ := by
  decide +kernel

theorem context_13_424148_809395 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424148 ⟨809395, by decide⟩ :=
  accepted_of_selected 13 424148 ⟨809395, by decide⟩ ⟨13, 2, 0, 809395, 424148, 405, 16384⟩
    (by decide) selected_cut_31535

theorem selected_cut_31536 : selected 8 ⟨809436, by decide⟩
    (prefixPartial 13 424149) = some ⟨13, 2, 0, 809436, 424149, 2753, 16384⟩ := by
  decide +kernel

theorem context_13_424149_809436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424149 ⟨809436, by decide⟩ :=
  accepted_of_selected 13 424149 ⟨809436, by decide⟩ ⟨13, 2, 0, 809436, 424149, 2753, 16384⟩
    (by decide) selected_cut_31536

theorem selected_cut_31537 : selected 8 ⟨809462, by decide⟩
    (prefixPartial 13 424150) = some ⟨13, 2, 0, 809462, 424150, 1521, 16384⟩ := by
  decide +kernel

theorem context_13_424150_809462 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424150 ⟨809462, by decide⟩ :=
  accepted_of_selected 13 424150 ⟨809462, by decide⟩ ⟨13, 2, 0, 809462, 424150, 1521, 16384⟩
    (by decide) selected_cut_31537

theorem selected_cut_31538 : selected 8 ⟨809472, by decide⟩
    (prefixPartial 13 424151) = some ⟨13, 2, 0, 809472, 424151, 769, 16384⟩ := by
  decide +kernel

theorem context_13_424151_809472 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424151 ⟨809472, by decide⟩ :=
  accepted_of_selected 13 424151 ⟨809472, by decide⟩ ⟨13, 2, 0, 809472, 424151, 769, 16384⟩
    (by decide) selected_cut_31538

theorem unmarked_context_12_106037_809473 : frontier 9 ⟨809473, by decide⟩
    (prefixCache 12 106037) (prefixPartial 12 106037) = false := by
  decide +kernel

theorem node_context_12_106037_809473 : EJMOriginalGlobalDAGData.nodes 9 ⟨809473, by decide⟩ =
    .split (coordinate 12) (![⟨809395, by decide⟩,⟨809436, by decide⟩,⟨809462, by decide⟩,⟨809472, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_106037_809473 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106037 ⟨809473, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 106037
    ⟨809473, by decide⟩ (by decide) (![⟨809395, by decide⟩,⟨809436, by decide⟩,⟨809462, by decide⟩,⟨809472, by decide⟩]) unmarked_context_12_106037_809473 node_context_12_106037_809473
  intro a
  fin_cases a
  · exact context_13_424148_809395
  · exact context_13_424149_809436
  · exact context_13_424150_809462
  · exact context_13_424151_809472

theorem selected_cut_31539 : selected 8 ⟨809480, by decide⟩
    (prefixPartial 13 424152) = some ⟨13, 2, 0, 809480, 424152, 317, 16384⟩ := by
  decide +kernel

theorem context_13_424152_809480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424152 ⟨809480, by decide⟩ :=
  accepted_of_selected 13 424152 ⟨809480, by decide⟩ ⟨13, 2, 0, 809480, 424152, 317, 16384⟩
    (by decide) selected_cut_31539

theorem selected_cut_31540 : selected 8 ⟨809515, by decide⟩
    (prefixPartial 13 424153) = some ⟨13, 2, 0, 809515, 424153, 2733, 16384⟩ := by
  decide +kernel

theorem context_13_424153_809515 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424153 ⟨809515, by decide⟩ :=
  accepted_of_selected 13 424153 ⟨809515, by decide⟩ ⟨13, 2, 0, 809515, 424153, 2733, 16384⟩
    (by decide) selected_cut_31540

theorem selected_cut_31541 : selected 8 ⟨809533, by decide⟩
    (prefixPartial 13 424154) = some ⟨13, 2, 0, 809533, 424154, 1341, 16384⟩ := by
  decide +kernel

theorem context_13_424154_809533 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424154 ⟨809533, by decide⟩ :=
  accepted_of_selected 13 424154 ⟨809533, by decide⟩ ⟨13, 2, 0, 809533, 424154, 1341, 16384⟩
    (by decide) selected_cut_31541

theorem selected_cut_31542 : selected 8 ⟨809539, by decide⟩
    (prefixPartial 13 424155) = some ⟨13, 2, 0, 809539, 424155, 797, 16384⟩ := by
  decide +kernel

theorem context_13_424155_809539 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424155 ⟨809539, by decide⟩ :=
  accepted_of_selected 13 424155 ⟨809539, by decide⟩ ⟨13, 2, 0, 809539, 424155, 797, 16384⟩
    (by decide) selected_cut_31542

theorem unmarked_context_12_106038_809540 : frontier 9 ⟨809540, by decide⟩
    (prefixCache 12 106038) (prefixPartial 12 106038) = false := by
  decide +kernel

theorem node_context_12_106038_809540 : EJMOriginalGlobalDAGData.nodes 9 ⟨809540, by decide⟩ =
    .split (coordinate 12) (![⟨809480, by decide⟩,⟨809515, by decide⟩,⟨809533, by decide⟩,⟨809539, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_106038_809540 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106038 ⟨809540, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 106038
    ⟨809540, by decide⟩ (by decide) (![⟨809480, by decide⟩,⟨809515, by decide⟩,⟨809533, by decide⟩,⟨809539, by decide⟩]) unmarked_context_12_106038_809540 node_context_12_106038_809540
  intro a
  fin_cases a
  · exact context_13_424152_809480
  · exact context_13_424153_809515
  · exact context_13_424154_809533
  · exact context_13_424155_809539

theorem selected_cut_31543 : selected 8 ⟨809548, by decide⟩
    (prefixPartial 13 424156) = some ⟨13, 2, 0, 809548, 424156, 365, 16384⟩ := by
  decide +kernel

theorem context_13_424156_809548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424156 ⟨809548, by decide⟩ :=
  accepted_of_selected 13 424156 ⟨809548, by decide⟩ ⟨13, 2, 0, 809548, 424156, 365, 16384⟩
    (by decide) selected_cut_31543

theorem selected_cut_31544 : selected 8 ⟨809614, by decide⟩
    (prefixPartial 13 424157) = some ⟨13, 2, 0, 809614, 424157, 3637, 16384⟩ := by
  decide +kernel

theorem context_13_424157_809614 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424157 ⟨809614, by decide⟩ :=
  accepted_of_selected 13 424157 ⟨809614, by decide⟩ ⟨13, 2, 0, 809614, 424157, 3637, 16384⟩
    (by decide) selected_cut_31544

theorem selected_cut_31545 : selected 8 ⟨809661, by decide⟩
    (prefixPartial 13 424158) = some ⟨13, 2, 0, 809661, 424158, 1981, 16384⟩ := by
  decide +kernel

theorem context_13_424158_809661 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424158 ⟨809661, by decide⟩ :=
  accepted_of_selected 13 424158 ⟨809661, by decide⟩ ⟨13, 2, 0, 809661, 424158, 1981, 16384⟩
    (by decide) selected_cut_31545

theorem selected_cut_31546 : selected 8 ⟨809676, by decide⟩
    (prefixPartial 13 424159) = some ⟨13, 2, 0, 809676, 424159, 905, 16384⟩ := by
  decide +kernel

theorem context_13_424159_809676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424159 ⟨809676, by decide⟩ :=
  accepted_of_selected 13 424159 ⟨809676, by decide⟩ ⟨13, 2, 0, 809676, 424159, 905, 16384⟩
    (by decide) selected_cut_31546

theorem unmarked_context_12_106039_809677 : frontier 9 ⟨809677, by decide⟩
    (prefixCache 12 106039) (prefixPartial 12 106039) = false := by
  decide +kernel

theorem node_context_12_106039_809677 : EJMOriginalGlobalDAGData.nodes 9 ⟨809677, by decide⟩ =
    .split (coordinate 12) (![⟨809548, by decide⟩,⟨809614, by decide⟩,⟨809661, by decide⟩,⟨809676, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_106039_809677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106039 ⟨809677, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 106039
    ⟨809677, by decide⟩ (by decide) (![⟨809548, by decide⟩,⟨809614, by decide⟩,⟨809661, by decide⟩,⟨809676, by decide⟩]) unmarked_context_12_106039_809677 node_context_12_106039_809677
  intro a
  fin_cases a
  · exact context_13_424156_809548
  · exact context_13_424157_809614
  · exact context_13_424158_809661
  · exact context_13_424159_809676

theorem unmarked_context_11_26509_809678 : frontier 10 ⟨809678, by decide⟩
    (prefixCache 11 26509) (prefixPartial 11 26509) = false := by
  decide +kernel

theorem node_context_11_26509_809678 : EJMOriginalGlobalDAGData.nodes 10 ⟨809678, by decide⟩ =
    .split (coordinate 11) (![⟨809386, by decide⟩,⟨809473, by decide⟩,⟨809540, by decide⟩,⟨809677, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26509_809678 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26509 ⟨809678, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26509
    ⟨809678, by decide⟩ (by decide) (![⟨809386, by decide⟩,⟨809473, by decide⟩,⟨809540, by decide⟩,⟨809677, by decide⟩]) unmarked_context_11_26509_809678 node_context_11_26509_809678
  intro a
  fin_cases a
  · exact context_12_106036_809386
  · exact context_12_106037_809473
  · exact context_12_106038_809540
  · exact context_12_106039_809677

theorem selected_cut_31547 : selected 8 ⟨809682, by decide⟩
    (prefixPartial 13 424160) = some ⟨13, 2, 0, 809682, 424160, 213, 16384⟩ := by
  decide +kernel

theorem context_13_424160_809682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424160 ⟨809682, by decide⟩ :=
  accepted_of_selected 13 424160 ⟨809682, by decide⟩ ⟨13, 2, 0, 809682, 424160, 213, 16384⟩
    (by decide) selected_cut_31547

theorem selected_cut_31548 : selected 8 ⟨809718, by decide⟩
    (prefixPartial 13 424161) = some ⟨13, 2, 0, 809718, 424161, 2469, 16384⟩ := by
  decide +kernel

theorem context_13_424161_809718 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424161 ⟨809718, by decide⟩ :=
  accepted_of_selected 13 424161 ⟨809718, by decide⟩ ⟨13, 2, 0, 809718, 424161, 2469, 16384⟩
    (by decide) selected_cut_31548

theorem selected_cut_31549 : selected 8 ⟨809740, by decide⟩
    (prefixPartial 13 424162) = some ⟨13, 2, 0, 809740, 424162, 1641, 16384⟩ := by
  decide +kernel

theorem context_13_424162_809740 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424162 ⟨809740, by decide⟩ :=
  accepted_of_selected 13 424162 ⟨809740, by decide⟩ ⟨13, 2, 0, 809740, 424162, 1641, 16384⟩
    (by decide) selected_cut_31549

theorem selected_cut_31550 : selected 8 ⟨809751, by decide⟩
    (prefixPartial 13 424163) = some ⟨13, 2, 0, 809751, 424163, 777, 16384⟩ := by
  decide +kernel

theorem context_13_424163_809751 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424163 ⟨809751, by decide⟩ :=
  accepted_of_selected 13 424163 ⟨809751, by decide⟩ ⟨13, 2, 0, 809751, 424163, 777, 16384⟩
    (by decide) selected_cut_31550

theorem unmarked_context_12_106040_809752 : frontier 9 ⟨809752, by decide⟩
    (prefixCache 12 106040) (prefixPartial 12 106040) = false := by
  decide +kernel

theorem node_context_12_106040_809752 : EJMOriginalGlobalDAGData.nodes 9 ⟨809752, by decide⟩ =
    .split (coordinate 12) (![⟨809682, by decide⟩,⟨809718, by decide⟩,⟨809740, by decide⟩,⟨809751, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_106040_809752 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106040 ⟨809752, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 106040
    ⟨809752, by decide⟩ (by decide) (![⟨809682, by decide⟩,⟨809718, by decide⟩,⟨809740, by decide⟩,⟨809751, by decide⟩]) unmarked_context_12_106040_809752 node_context_12_106040_809752
  intro a
  fin_cases a
  · exact context_13_424160_809682
  · exact context_13_424161_809718
  · exact context_13_424162_809740
  · exact context_13_424163_809751

theorem selected_cut_31551 : selected 8 ⟨809756, by decide⟩
    (prefixPartial 13 424164) = some ⟨13, 2, 0, 809756, 424164, 133, 16384⟩ := by
  decide +kernel

theorem context_13_424164_809756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424164 ⟨809756, by decide⟩ :=
  accepted_of_selected 13 424164 ⟨809756, by decide⟩ ⟨13, 2, 0, 809756, 424164, 133, 16384⟩
    (by decide) selected_cut_31551

theorem selected_cut_31552 : selected 8 ⟨809783, by decide⟩
    (prefixPartial 13 424165) = some ⟨13, 2, 0, 809783, 424165, 2193, 16384⟩ := by
  decide +kernel

theorem context_13_424165_809783 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424165 ⟨809783, by decide⟩ :=
  accepted_of_selected 13 424165 ⟨809783, by decide⟩ ⟨13, 2, 0, 809783, 424165, 2193, 16384⟩
    (by decide) selected_cut_31552

theorem selected_cut_31553 : selected 8 ⟨809805, by decide⟩
    (prefixPartial 13 424166) = some ⟨13, 2, 0, 809805, 424166, 1505, 16384⟩ := by
  decide +kernel

theorem context_13_424166_809805 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424166 ⟨809805, by decide⟩ :=
  accepted_of_selected 13 424166 ⟨809805, by decide⟩ ⟨13, 2, 0, 809805, 424166, 1505, 16384⟩
    (by decide) selected_cut_31553

theorem selected_cut_31554 : selected 8 ⟨809810, by decide⟩
    (prefixPartial 13 424167) = some ⟨13, 2, 0, 809810, 424167, 901, 16384⟩ := by
  decide +kernel

theorem context_13_424167_809810 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424167 ⟨809810, by decide⟩ :=
  accepted_of_selected 13 424167 ⟨809810, by decide⟩ ⟨13, 2, 0, 809810, 424167, 901, 16384⟩
    (by decide) selected_cut_31554

theorem unmarked_context_12_106041_809811 : frontier 9 ⟨809811, by decide⟩
    (prefixCache 12 106041) (prefixPartial 12 106041) = false := by
  decide +kernel

theorem node_context_12_106041_809811 : EJMOriginalGlobalDAGData.nodes 9 ⟨809811, by decide⟩ =
    .split (coordinate 12) (![⟨809756, by decide⟩,⟨809783, by decide⟩,⟨809805, by decide⟩,⟨809810, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_106041_809811 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106041 ⟨809811, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 106041
    ⟨809811, by decide⟩ (by decide) (![⟨809756, by decide⟩,⟨809783, by decide⟩,⟨809805, by decide⟩,⟨809810, by decide⟩]) unmarked_context_12_106041_809811 node_context_12_106041_809811
  intro a
  fin_cases a
  · exact context_13_424164_809756
  · exact context_13_424165_809783
  · exact context_13_424166_809805
  · exact context_13_424167_809810

theorem selected_cut_31555 : selected 9 ⟨662655, by decide⟩
    (prefixPartial 12 106042) = some ⟨12, 1, 0, 662655, 106042, 1, 65536⟩ := by
  decide +kernel

theorem context_12_106042_662655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106042 ⟨662655, by decide⟩ :=
  accepted_of_selected 12 106042 ⟨662655, by decide⟩ ⟨12, 1, 0, 662655, 106042, 1, 65536⟩
    (by decide) selected_cut_31555

theorem selected_cut_31556 : selected 8 ⟨809814, by decide⟩
    (prefixPartial 13 424172) = some ⟨13, 2, 0, 809814, 424172, 85, 16384⟩ := by
  decide +kernel

theorem context_13_424172_809814 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424172 ⟨809814, by decide⟩ :=
  accepted_of_selected 13 424172 ⟨809814, by decide⟩ ⟨13, 2, 0, 809814, 424172, 85, 16384⟩
    (by decide) selected_cut_31556

theorem selected_cut_31557 : selected 8 ⟨809856, by decide⟩
    (prefixPartial 13 424173) = some ⟨13, 2, 0, 809856, 424173, 3273, 16384⟩ := by
  decide +kernel

theorem context_13_424173_809856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424173 ⟨809856, by decide⟩ :=
  accepted_of_selected 13 424173 ⟨809856, by decide⟩ ⟨13, 2, 0, 809856, 424173, 3273, 16384⟩
    (by decide) selected_cut_31557

theorem selected_cut_31558 : selected 8 ⟨809873, by decide⟩
    (prefixPartial 13 424174) = some ⟨13, 2, 0, 809873, 424174, 1709, 16384⟩ := by
  decide +kernel

theorem context_13_424174_809873 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424174 ⟨809873, by decide⟩ :=
  accepted_of_selected 13 424174 ⟨809873, by decide⟩ ⟨13, 2, 0, 809873, 424174, 1709, 16384⟩
    (by decide) selected_cut_31558

theorem selected_cut_31559 : selected 8 ⟨809883, by decide⟩
    (prefixPartial 13 424175) = some ⟨13, 2, 0, 809883, 424175, 965, 16384⟩ := by
  decide +kernel

theorem context_13_424175_809883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424175 ⟨809883, by decide⟩ :=
  accepted_of_selected 13 424175 ⟨809883, by decide⟩ ⟨13, 2, 0, 809883, 424175, 965, 16384⟩
    (by decide) selected_cut_31559

theorem unmarked_context_12_106043_809884 : frontier 9 ⟨809884, by decide⟩
    (prefixCache 12 106043) (prefixPartial 12 106043) = false := by
  decide +kernel

theorem node_context_12_106043_809884 : EJMOriginalGlobalDAGData.nodes 9 ⟨809884, by decide⟩ =
    .split (coordinate 12) (![⟨809814, by decide⟩,⟨809856, by decide⟩,⟨809873, by decide⟩,⟨809883, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_106043_809884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106043 ⟨809884, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 106043
    ⟨809884, by decide⟩ (by decide) (![⟨809814, by decide⟩,⟨809856, by decide⟩,⟨809873, by decide⟩,⟨809883, by decide⟩]) unmarked_context_12_106043_809884 node_context_12_106043_809884
  intro a
  fin_cases a
  · exact context_13_424172_809814
  · exact context_13_424173_809856
  · exact context_13_424174_809873
  · exact context_13_424175_809883

theorem unmarked_context_11_26510_809885 : frontier 10 ⟨809885, by decide⟩
    (prefixCache 11 26510) (prefixPartial 11 26510) = false := by
  decide +kernel

theorem node_context_11_26510_809885 : EJMOriginalGlobalDAGData.nodes 10 ⟨809885, by decide⟩ =
    .split (coordinate 11) (![⟨809752, by decide⟩,⟨809811, by decide⟩,⟨662655, by decide⟩,⟨809884, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26510_809885 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26510 ⟨809885, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26510
    ⟨809885, by decide⟩ (by decide) (![⟨809752, by decide⟩,⟨809811, by decide⟩,⟨662655, by decide⟩,⟨809884, by decide⟩]) unmarked_context_11_26510_809885 node_context_11_26510_809885
  intro a
  fin_cases a
  · exact context_12_106040_809752
  · exact context_12_106041_809811
  · exact context_12_106042_662655
  · exact context_12_106043_809884

theorem selected_cut_31560 : selected 10 ⟨793294, by decide⟩
    (prefixPartial 11 26511) = some ⟨11, 1, 0, 793294, 26511, 1, 262144⟩ := by
  decide +kernel

theorem context_11_26511_793294 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26511 ⟨793294, by decide⟩ :=
  accepted_of_selected 11 26511 ⟨793294, by decide⟩ ⟨11, 1, 0, 793294, 26511, 1, 262144⟩
    (by decide) selected_cut_31560

theorem unmarked_context_10_6627_809886 : frontier 11 ⟨809886, by decide⟩
    (prefixCache 10 6627) (prefixPartial 10 6627) = false := by
  decide +kernel

theorem node_context_10_6627_809886 : EJMOriginalGlobalDAGData.nodes 11 ⟨809886, by decide⟩ =
    .split (coordinate 10) (![⟨809269, by decide⟩,⟨809678, by decide⟩,⟨809885, by decide⟩,⟨793294, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6627_809886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6627 ⟨809886, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6627
    ⟨809886, by decide⟩ (by decide) (![⟨809269, by decide⟩,⟨809678, by decide⟩,⟨809885, by decide⟩,⟨793294, by decide⟩]) unmarked_context_10_6627_809886 node_context_10_6627_809886
  intro a
  fin_cases a
  · exact context_11_26508_809269
  · exact context_11_26509_809678
  · exact context_11_26510_809885
  · exact context_11_26511_793294

theorem unmarked_context_9_1656_809887 : frontier 12 ⟨809887, by decide⟩
    (prefixCache 9 1656) (prefixPartial 9 1656) = false := by
  decide +kernel

theorem node_context_9_1656_809887 : EJMOriginalGlobalDAGData.nodes 12 ⟨809887, by decide⟩ =
    .split (coordinate 9) (![⟨805818, by decide⟩,⟨807499, by decide⟩,⟨808912, by decide⟩,⟨809886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1656_809887 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1656 ⟨809887, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1656
    ⟨809887, by decide⟩ (by decide) (![⟨805818, by decide⟩,⟨807499, by decide⟩,⟨808912, by decide⟩,⟨809886, by decide⟩]) unmarked_context_9_1656_809887 node_context_9_1656_809887
  intro a
  fin_cases a
  · exact context_10_6624_805818
  · exact context_10_6625_807499
  · exact context_10_6626_808912
  · exact context_10_6627_809886

theorem selected_cut_31561 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 424192) = some ⟨13, 1, 0, 3444, 424192, 1, 16384⟩ := by
  decide +kernel

theorem context_13_424192_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424192 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 424192 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 424192, 1, 16384⟩
    (by decide) selected_cut_31561

theorem selected_cut_31562 : selected 8 ⟨809940, by decide⟩
    (prefixPartial 13 424193) = some ⟨13, 2, 0, 809940, 424193, 2873, 16384⟩ := by
  decide +kernel

theorem context_13_424193_809940 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424193 ⟨809940, by decide⟩ :=
  accepted_of_selected 13 424193 ⟨809940, by decide⟩ ⟨13, 2, 0, 809940, 424193, 2873, 16384⟩
    (by decide) selected_cut_31562

theorem selected_cut_31563 : selected 8 ⟨809964, by decide⟩
    (prefixPartial 13 424194) = some ⟨13, 2, 0, 809964, 424194, 1365, 16384⟩ := by
  decide +kernel

theorem context_13_424194_809964 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424194 ⟨809964, by decide⟩ :=
  accepted_of_selected 13 424194 ⟨809964, by decide⟩ ⟨13, 2, 0, 809964, 424194, 1365, 16384⟩
    (by decide) selected_cut_31563

theorem selected_cut_31564 : selected 8 ⟨809972, by decide⟩
    (prefixPartial 13 424195) = some ⟨13, 2, 0, 809972, 424195, 701, 16384⟩ := by
  decide +kernel

theorem context_13_424195_809972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424195 ⟨809972, by decide⟩ :=
  accepted_of_selected 13 424195 ⟨809972, by decide⟩ ⟨13, 2, 0, 809972, 424195, 701, 16384⟩
    (by decide) selected_cut_31564

theorem unmarked_context_12_106048_809973 : frontier 9 ⟨809973, by decide⟩
    (prefixCache 12 106048) (prefixPartial 12 106048) = false := by
  decide +kernel

theorem node_context_12_106048_809973 : EJMOriginalGlobalDAGData.nodes 9 ⟨809973, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨809940, by decide⟩,⟨809964, by decide⟩,⟨809972, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_106048_809973 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106048 ⟨809973, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 106048
    ⟨809973, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨809940, by decide⟩,⟨809964, by decide⟩,⟨809972, by decide⟩]) unmarked_context_12_106048_809973 node_context_12_106048_809973
  intro a
  fin_cases a
  · exact context_13_424192_3444
  · exact context_13_424193_809940
  · exact context_13_424194_809964
  · exact context_13_424195_809972

theorem selected_cut_31565 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 424196) = some ⟨13, 1, 0, 3444, 424196, 1, 16384⟩ := by
  decide +kernel

theorem context_13_424196_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424196 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 424196 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 424196, 1, 16384⟩
    (by decide) selected_cut_31565

theorem selected_cut_31566 : selected 8 ⟨810013, by decide⟩
    (prefixPartial 13 424197) = some ⟨13, 2, 0, 810013, 424197, 2977, 16384⟩ := by
  decide +kernel

theorem context_13_424197_810013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424197 ⟨810013, by decide⟩ :=
  accepted_of_selected 13 424197 ⟨810013, by decide⟩ ⟨13, 2, 0, 810013, 424197, 2977, 16384⟩
    (by decide) selected_cut_31566

theorem selected_cut_31567 : selected 8 ⟨810031, by decide⟩
    (prefixPartial 13 424198) = some ⟨13, 2, 0, 810031, 424198, 1213, 16384⟩ := by
  decide +kernel

theorem context_13_424198_810031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424198 ⟨810031, by decide⟩ :=
  accepted_of_selected 13 424198 ⟨810031, by decide⟩ ⟨13, 2, 0, 810031, 424198, 1213, 16384⟩
    (by decide) selected_cut_31567

theorem selected_cut_31568 : selected 8 ⟨810037, by decide⟩
    (prefixPartial 13 424199) = some ⟨13, 2, 0, 810037, 424199, 717, 16384⟩ := by
  decide +kernel

theorem context_13_424199_810037 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424199 ⟨810037, by decide⟩ :=
  accepted_of_selected 13 424199 ⟨810037, by decide⟩ ⟨13, 2, 0, 810037, 424199, 717, 16384⟩
    (by decide) selected_cut_31568

theorem unmarked_context_12_106049_810038 : frontier 9 ⟨810038, by decide⟩
    (prefixCache 12 106049) (prefixPartial 12 106049) = false := by
  decide +kernel

theorem node_context_12_106049_810038 : EJMOriginalGlobalDAGData.nodes 9 ⟨810038, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨810013, by decide⟩,⟨810031, by decide⟩,⟨810037, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_106049_810038 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106049 ⟨810038, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 106049
    ⟨810038, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨810013, by decide⟩,⟨810031, by decide⟩,⟨810037, by decide⟩]) unmarked_context_12_106049_810038 node_context_12_106049_810038
  intro a
  fin_cases a
  · exact context_13_424196_3444
  · exact context_13_424197_810013
  · exact context_13_424198_810031
  · exact context_13_424199_810037

theorem selected_cut_31569 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 424200) = some ⟨13, 1, 0, 3444, 424200, 1, 16384⟩ := by
  decide +kernel

theorem context_13_424200_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424200 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 424200 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 424200, 1, 16384⟩
    (by decide) selected_cut_31569

theorem selected_cut_31570 : selected 8 ⟨810073, by decide⟩
    (prefixPartial 13 424201) = some ⟨13, 2, 0, 810073, 424201, 2697, 16384⟩ := by
  decide +kernel

theorem context_13_424201_810073 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424201 ⟨810073, by decide⟩ :=
  accepted_of_selected 13 424201 ⟨810073, by decide⟩ ⟨13, 2, 0, 810073, 424201, 2697, 16384⟩
    (by decide) selected_cut_31570

theorem selected_cut_31571 : selected 8 ⟨810093, by decide⟩
    (prefixPartial 13 424202) = some ⟨13, 2, 0, 810093, 424202, 1169, 16384⟩ := by
  decide +kernel

theorem context_13_424202_810093 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424202 ⟨810093, by decide⟩ :=
  accepted_of_selected 13 424202 ⟨810093, by decide⟩ ⟨13, 2, 0, 810093, 424202, 1169, 16384⟩
    (by decide) selected_cut_31571

theorem selected_cut_31572 : selected 8 ⟨810098, by decide⟩
    (prefixPartial 13 424203) = some ⟨13, 2, 0, 810098, 424203, 685, 16384⟩ := by
  decide +kernel

theorem context_13_424203_810098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424203 ⟨810098, by decide⟩ :=
  accepted_of_selected 13 424203 ⟨810098, by decide⟩ ⟨13, 2, 0, 810098, 424203, 685, 16384⟩
    (by decide) selected_cut_31572

theorem unmarked_context_12_106050_810099 : frontier 9 ⟨810099, by decide⟩
    (prefixCache 12 106050) (prefixPartial 12 106050) = false := by
  decide +kernel

theorem node_context_12_106050_810099 : EJMOriginalGlobalDAGData.nodes 9 ⟨810099, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨810073, by decide⟩,⟨810093, by decide⟩,⟨810098, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_106050_810099 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106050 ⟨810099, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 106050
    ⟨810099, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨810073, by decide⟩,⟨810093, by decide⟩,⟨810098, by decide⟩]) unmarked_context_12_106050_810099 node_context_12_106050_810099
  intro a
  fin_cases a
  · exact context_13_424200_3444
  · exact context_13_424201_810073
  · exact context_13_424202_810093
  · exact context_13_424203_810098

theorem selected_cut_31573 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 424204) = some ⟨13, 1, 0, 3444, 424204, 1, 16384⟩ := by
  decide +kernel

theorem context_13_424204_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424204 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 424204 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 424204, 1, 16384⟩
    (by decide) selected_cut_31573

theorem selected_cut_31574 : selected 8 ⟨810150, by decide⟩
    (prefixPartial 13 424205) = some ⟨13, 2, 0, 810150, 424205, 3001, 16384⟩ := by
  decide +kernel

theorem context_13_424205_810150 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424205 ⟨810150, by decide⟩ :=
  accepted_of_selected 13 424205 ⟨810150, by decide⟩ ⟨13, 2, 0, 810150, 424205, 3001, 16384⟩
    (by decide) selected_cut_31574

theorem selected_cut_31575 : selected 8 ⟨810169, by decide⟩
    (prefixPartial 13 424206) = some ⟨13, 2, 0, 810169, 424206, 1381, 16384⟩ := by
  decide +kernel

theorem context_13_424206_810169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424206 ⟨810169, by decide⟩ :=
  accepted_of_selected 13 424206 ⟨810169, by decide⟩ ⟨13, 2, 0, 810169, 424206, 1381, 16384⟩
    (by decide) selected_cut_31575

theorem selected_cut_31576 : selected 8 ⟨810182, by decide⟩
    (prefixPartial 13 424207) = some ⟨13, 2, 0, 810182, 424207, 841, 16384⟩ := by
  decide +kernel

theorem context_13_424207_810182 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424207 ⟨810182, by decide⟩ :=
  accepted_of_selected 13 424207 ⟨810182, by decide⟩ ⟨13, 2, 0, 810182, 424207, 841, 16384⟩
    (by decide) selected_cut_31576

theorem unmarked_context_12_106051_810183 : frontier 9 ⟨810183, by decide⟩
    (prefixCache 12 106051) (prefixPartial 12 106051) = false := by
  decide +kernel

theorem node_context_12_106051_810183 : EJMOriginalGlobalDAGData.nodes 9 ⟨810183, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨810150, by decide⟩,⟨810169, by decide⟩,⟨810182, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_106051_810183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106051 ⟨810183, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 106051
    ⟨810183, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨810150, by decide⟩,⟨810169, by decide⟩,⟨810182, by decide⟩]) unmarked_context_12_106051_810183 node_context_12_106051_810183
  intro a
  fin_cases a
  · exact context_13_424204_3444
  · exact context_13_424205_810150
  · exact context_13_424206_810169
  · exact context_13_424207_810182

theorem unmarked_context_11_26512_810184 : frontier 10 ⟨810184, by decide⟩
    (prefixCache 11 26512) (prefixPartial 11 26512) = false := by
  decide +kernel

theorem node_context_11_26512_810184 : EJMOriginalGlobalDAGData.nodes 10 ⟨810184, by decide⟩ =
    .split (coordinate 11) (![⟨809973, by decide⟩,⟨810038, by decide⟩,⟨810099, by decide⟩,⟨810183, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26512_810184 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26512 ⟨810184, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26512
    ⟨810184, by decide⟩ (by decide) (![⟨809973, by decide⟩,⟨810038, by decide⟩,⟨810099, by decide⟩,⟨810183, by decide⟩]) unmarked_context_11_26512_810184 node_context_11_26512_810184
  intro a
  fin_cases a
  · exact context_12_106048_809973
  · exact context_12_106049_810038
  · exact context_12_106050_810099
  · exact context_12_106051_810183

theorem selected_cut_31577 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 424208) = some ⟨13, 1, 0, 3444, 424208, 1, 16384⟩ := by
  decide +kernel

theorem context_13_424208_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424208 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 424208 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 424208, 1, 16384⟩
    (by decide) selected_cut_31577

theorem selected_cut_31578 : selected 8 ⟨810244, by decide⟩
    (prefixPartial 13 424209) = some ⟨13, 2, 0, 810244, 424209, 3193, 16384⟩ := by
  decide +kernel

theorem context_13_424209_810244 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424209 ⟨810244, by decide⟩ :=
  accepted_of_selected 13 424209 ⟨810244, by decide⟩ ⟨13, 2, 0, 810244, 424209, 3193, 16384⟩
    (by decide) selected_cut_31578

theorem selected_cut_31579 : selected 8 ⟨810281, by decide⟩
    (prefixPartial 13 424210) = some ⟨13, 2, 0, 810281, 424210, 1749, 16384⟩ := by
  decide +kernel

theorem context_13_424210_810281 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424210 ⟨810281, by decide⟩ :=
  accepted_of_selected 13 424210 ⟨810281, by decide⟩ ⟨13, 2, 0, 810281, 424210, 1749, 16384⟩
    (by decide) selected_cut_31579

theorem selected_cut_31580 : selected 8 ⟨810291, by decide⟩
    (prefixPartial 13 424211) = some ⟨13, 2, 0, 810291, 424211, 893, 16384⟩ := by
  decide +kernel

theorem context_13_424211_810291 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424211 ⟨810291, by decide⟩ :=
  accepted_of_selected 13 424211 ⟨810291, by decide⟩ ⟨13, 2, 0, 810291, 424211, 893, 16384⟩
    (by decide) selected_cut_31580

theorem unmarked_context_12_106052_810292 : frontier 9 ⟨810292, by decide⟩
    (prefixCache 12 106052) (prefixPartial 12 106052) = false := by
  decide +kernel

theorem node_context_12_106052_810292 : EJMOriginalGlobalDAGData.nodes 9 ⟨810292, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨810244, by decide⟩,⟨810281, by decide⟩,⟨810291, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_106052_810292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106052 ⟨810292, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 106052
    ⟨810292, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨810244, by decide⟩,⟨810281, by decide⟩,⟨810291, by decide⟩]) unmarked_context_12_106052_810292 node_context_12_106052_810292
  intro a
  fin_cases a
  · exact context_13_424208_3444
  · exact context_13_424209_810244
  · exact context_13_424210_810281
  · exact context_13_424211_810291

theorem selected_cut_31581 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 424212) = some ⟨13, 1, 0, 3444, 424212, 1, 16384⟩ := by
  decide +kernel

theorem context_13_424212_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424212 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 424212 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 424212, 1, 16384⟩
    (by decide) selected_cut_31581

theorem selected_cut_31582 : selected 8 ⟨810337, by decide⟩
    (prefixPartial 13 424213) = some ⟨13, 2, 0, 810337, 424213, 2645, 16384⟩ := by
  decide +kernel

theorem context_13_424213_810337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424213 ⟨810337, by decide⟩ :=
  accepted_of_selected 13 424213 ⟨810337, by decide⟩ ⟨13, 2, 0, 810337, 424213, 2645, 16384⟩
    (by decide) selected_cut_31582

theorem selected_cut_31583 : selected 8 ⟨810357, by decide⟩
    (prefixPartial 13 424214) = some ⟨13, 2, 0, 810357, 424214, 1329, 16384⟩ := by
  decide +kernel

theorem context_13_424214_810357 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424214 ⟨810357, by decide⟩ :=
  accepted_of_selected 13 424214 ⟨810357, by decide⟩ ⟨13, 2, 0, 810357, 424214, 1329, 16384⟩
    (by decide) selected_cut_31583

theorem selected_cut_31584 : selected 8 ⟨810363, by decide⟩
    (prefixPartial 13 424215) = some ⟨13, 2, 0, 810363, 424215, 721, 16384⟩ := by
  decide +kernel

theorem context_13_424215_810363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424215 ⟨810363, by decide⟩ :=
  accepted_of_selected 13 424215 ⟨810363, by decide⟩ ⟨13, 2, 0, 810363, 424215, 721, 16384⟩
    (by decide) selected_cut_31584

theorem unmarked_context_12_106053_810364 : frontier 9 ⟨810364, by decide⟩
    (prefixCache 12 106053) (prefixPartial 12 106053) = false := by
  decide +kernel

theorem node_context_12_106053_810364 : EJMOriginalGlobalDAGData.nodes 9 ⟨810364, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨810337, by decide⟩,⟨810357, by decide⟩,⟨810363, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_106053_810364 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106053 ⟨810364, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 106053
    ⟨810364, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨810337, by decide⟩,⟨810357, by decide⟩,⟨810363, by decide⟩]) unmarked_context_12_106053_810364 node_context_12_106053_810364
  intro a
  fin_cases a
  · exact context_13_424212_3444
  · exact context_13_424213_810337
  · exact context_13_424214_810357
  · exact context_13_424215_810363

theorem selected_cut_31585 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 424216) = some ⟨13, 1, 0, 3444, 424216, 1, 16384⟩ := by
  decide +kernel

theorem context_13_424216_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424216 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 424216 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 424216, 1, 16384⟩
    (by decide) selected_cut_31585

theorem selected_cut_31586 : selected 8 ⟨810400, by decide⟩
    (prefixPartial 13 424217) = some ⟨13, 2, 0, 810400, 424217, 2601, 16384⟩ := by
  decide +kernel

theorem context_13_424217_810400 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424217 ⟨810400, by decide⟩ :=
  accepted_of_selected 13 424217 ⟨810400, by decide⟩ ⟨13, 2, 0, 810400, 424217, 2601, 16384⟩
    (by decide) selected_cut_31586

theorem selected_cut_31587 : selected 8 ⟨810423, by decide⟩
    (prefixPartial 13 424218) = some ⟨13, 2, 0, 810423, 424218, 1421, 16384⟩ := by
  decide +kernel

theorem context_13_424218_810423 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424218 ⟨810423, by decide⟩ :=
  accepted_of_selected 13 424218 ⟨810423, by decide⟩ ⟨13, 2, 0, 810423, 424218, 1421, 16384⟩
    (by decide) selected_cut_31587

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
