/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover512
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_49252 : selected 9 ⟨1392372, by decide⟩
    (prefixPartial 12 406831) = some ⟨12, 2, 0, 1392372, 406831, 1753, 65536⟩ := by
  decide +kernel

theorem context_12_406831_1392372 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406831 ⟨1392372, by decide⟩ :=
  accepted_of_selected 12 406831 ⟨1392372, by decide⟩ ⟨12, 2, 0, 1392372, 406831, 1753, 65536⟩
    (by decide) selected_cut_49252

theorem unmarked_context_11_101707_1392373 : frontier 10 ⟨1392373, by decide⟩
    (prefixCache 11 101707) (prefixPartial 11 101707) = false := by
  decide +kernel

theorem node_context_11_101707_1392373 : EJMOriginalGlobalDAGData.nodes 10 ⟨1392373, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1392282, by decide⟩,⟨1392335, by decide⟩,⟨1392372, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_101707_1392373 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101707 ⟨1392373, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 101707
    ⟨1392373, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1392282, by decide⟩,⟨1392335, by decide⟩,⟨1392372, by decide⟩]) unmarked_context_11_101707_1392373 node_context_11_101707_1392373
  intro a
  fin_cases a
  · exact context_12_406828_1108174
  · exact context_12_406829_1392282
  · exact context_12_406830_1392335
  · exact context_12_406831_1392372

theorem unmarked_context_10_25426_1392374 : frontier 11 ⟨1392374, by decide⟩
    (prefixCache 10 25426) (prefixPartial 10 25426) = false := by
  decide +kernel

theorem node_context_10_25426_1392374 : EJMOriginalGlobalDAGData.nodes 11 ⟨1392374, by decide⟩ =
    .split (coordinate 10) (![⟨1392128, by decide⟩,⟨1392209, by decide⟩,⟨1392252, by decide⟩,⟨1392373, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25426_1392374 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25426 ⟨1392374, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25426
    ⟨1392374, by decide⟩ (by decide) (![⟨1392128, by decide⟩,⟨1392209, by decide⟩,⟨1392252, by decide⟩,⟨1392373, by decide⟩]) unmarked_context_10_25426_1392374 node_context_10_25426_1392374
  intro a
  fin_cases a
  · exact context_11_101704_1392128
  · exact context_11_101705_1392209
  · exact context_11_101706_1392252
  · exact context_11_101707_1392373

theorem selected_cut_49253 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 406832) = some ⟨12, 1, 0, 1108174, 406832, 1, 65536⟩ := by
  decide +kernel

theorem context_12_406832_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406832 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 406832 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 406832, 1, 65536⟩
    (by decide) selected_cut_49253

theorem selected_cut_49254 : selected 9 ⟨1392409, by decide⟩
    (prefixPartial 12 406833) = some ⟨12, 2, 0, 1392409, 406833, 1853, 65536⟩ := by
  decide +kernel

theorem context_12_406833_1392409 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406833 ⟨1392409, by decide⟩ :=
  accepted_of_selected 12 406833 ⟨1392409, by decide⟩ ⟨12, 2, 0, 1392409, 406833, 1853, 65536⟩
    (by decide) selected_cut_49254

theorem selected_cut_49255 : selected 9 ⟨1392449, by decide⟩
    (prefixPartial 12 406834) = some ⟨12, 2, 0, 1392449, 406834, 2181, 65536⟩ := by
  decide +kernel

theorem context_12_406834_1392449 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406834 ⟨1392449, by decide⟩ :=
  accepted_of_selected 12 406834 ⟨1392449, by decide⟩ ⟨12, 2, 0, 1392449, 406834, 2181, 65536⟩
    (by decide) selected_cut_49255

theorem selected_cut_49256 : selected 9 ⟨1392483, by decide⟩
    (prefixPartial 12 406835) = some ⟨12, 2, 0, 1392483, 406835, 1749, 65536⟩ := by
  decide +kernel

theorem context_12_406835_1392483 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406835 ⟨1392483, by decide⟩ :=
  accepted_of_selected 12 406835 ⟨1392483, by decide⟩ ⟨12, 2, 0, 1392483, 406835, 1749, 65536⟩
    (by decide) selected_cut_49256

theorem unmarked_context_11_101708_1392484 : frontier 10 ⟨1392484, by decide⟩
    (prefixCache 11 101708) (prefixPartial 11 101708) = false := by
  decide +kernel

theorem node_context_11_101708_1392484 : EJMOriginalGlobalDAGData.nodes 10 ⟨1392484, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1392409, by decide⟩,⟨1392449, by decide⟩,⟨1392483, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_101708_1392484 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101708 ⟨1392484, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 101708
    ⟨1392484, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1392409, by decide⟩,⟨1392449, by decide⟩,⟨1392483, by decide⟩]) unmarked_context_11_101708_1392484 node_context_11_101708_1392484
  intro a
  fin_cases a
  · exact context_12_406832_1108174
  · exact context_12_406833_1392409
  · exact context_12_406834_1392449
  · exact context_12_406835_1392483

theorem selected_cut_49257 : selected 10 ⟨1392548, by decide⟩
    (prefixPartial 11 101709) = some ⟨11, 2, 0, 1392548, 101709, 3281, 262144⟩ := by
  decide +kernel

theorem context_11_101709_1392548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101709 ⟨1392548, by decide⟩ :=
  accepted_of_selected 11 101709 ⟨1392548, by decide⟩ ⟨11, 2, 0, 1392548, 101709, 3281, 262144⟩
    (by decide) selected_cut_49257

theorem selected_cut_49258 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 406840) = some ⟨12, 1, 0, 1108174, 406840, 1, 65536⟩ := by
  decide +kernel

theorem context_12_406840_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406840 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 406840 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 406840, 1, 65536⟩
    (by decide) selected_cut_49258

theorem selected_cut_49259 : selected 9 ⟨1392577, by decide⟩
    (prefixPartial 12 406841) = some ⟨12, 2, 0, 1392577, 406841, 1553, 65536⟩ := by
  decide +kernel

theorem context_12_406841_1392577 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406841 ⟨1392577, by decide⟩ :=
  accepted_of_selected 12 406841 ⟨1392577, by decide⟩ ⟨12, 2, 0, 1392577, 406841, 1553, 65536⟩
    (by decide) selected_cut_49259

theorem selected_cut_49260 : selected 9 ⟨1392605, by decide⟩
    (prefixPartial 12 406842) = some ⟨12, 2, 0, 1392605, 406842, 1761, 65536⟩ := by
  decide +kernel

theorem context_12_406842_1392605 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406842 ⟨1392605, by decide⟩ :=
  accepted_of_selected 12 406842 ⟨1392605, by decide⟩ ⟨12, 2, 0, 1392605, 406842, 1761, 65536⟩
    (by decide) selected_cut_49260

theorem selected_cut_49261 : selected 9 ⟨1392633, by decide⟩
    (prefixPartial 12 406843) = some ⟨12, 2, 0, 1392633, 406843, 1517, 65536⟩ := by
  decide +kernel

theorem context_12_406843_1392633 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406843 ⟨1392633, by decide⟩ :=
  accepted_of_selected 12 406843 ⟨1392633, by decide⟩ ⟨12, 2, 0, 1392633, 406843, 1517, 65536⟩
    (by decide) selected_cut_49261

theorem unmarked_context_11_101710_1392634 : frontier 10 ⟨1392634, by decide⟩
    (prefixCache 11 101710) (prefixPartial 11 101710) = false := by
  decide +kernel

theorem node_context_11_101710_1392634 : EJMOriginalGlobalDAGData.nodes 10 ⟨1392634, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1392577, by decide⟩,⟨1392605, by decide⟩,⟨1392633, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_101710_1392634 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101710 ⟨1392634, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 101710
    ⟨1392634, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1392577, by decide⟩,⟨1392605, by decide⟩,⟨1392633, by decide⟩]) unmarked_context_11_101710_1392634 node_context_11_101710_1392634
  intro a
  fin_cases a
  · exact context_12_406840_1108174
  · exact context_12_406841_1392577
  · exact context_12_406842_1392605
  · exact context_12_406843_1392633

theorem selected_cut_49262 : selected 10 ⟨1392667, by decide⟩
    (prefixPartial 11 101711) = some ⟨11, 2, 0, 1392667, 101711, 1833, 262144⟩ := by
  decide +kernel

theorem context_11_101711_1392667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101711 ⟨1392667, by decide⟩ :=
  accepted_of_selected 11 101711 ⟨1392667, by decide⟩ ⟨11, 2, 0, 1392667, 101711, 1833, 262144⟩
    (by decide) selected_cut_49262

theorem unmarked_context_10_25427_1392668 : frontier 11 ⟨1392668, by decide⟩
    (prefixCache 10 25427) (prefixPartial 10 25427) = false := by
  decide +kernel

theorem node_context_10_25427_1392668 : EJMOriginalGlobalDAGData.nodes 11 ⟨1392668, by decide⟩ =
    .split (coordinate 10) (![⟨1392484, by decide⟩,⟨1392548, by decide⟩,⟨1392634, by decide⟩,⟨1392667, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25427_1392668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25427 ⟨1392668, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25427
    ⟨1392668, by decide⟩ (by decide) (![⟨1392484, by decide⟩,⟨1392548, by decide⟩,⟨1392634, by decide⟩,⟨1392667, by decide⟩]) unmarked_context_10_25427_1392668 node_context_10_25427_1392668
  intro a
  fin_cases a
  · exact context_11_101708_1392484
  · exact context_11_101709_1392548
  · exact context_11_101710_1392634
  · exact context_11_101711_1392667

theorem unmarked_context_9_6356_1392669 : frontier 12 ⟨1392669, by decide⟩
    (prefixCache 9 6356) (prefixPartial 9 6356) = false := by
  decide +kernel

theorem node_context_9_6356_1392669 : EJMOriginalGlobalDAGData.nodes 12 ⟨1392669, by decide⟩ =
    .split (coordinate 9) (![⟨1391639, by decide⟩,⟨1391977, by decide⟩,⟨1392374, by decide⟩,⟨1392668, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6356_1392669 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6356 ⟨1392669, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6356
    ⟨1392669, by decide⟩ (by decide) (![⟨1391639, by decide⟩,⟨1391977, by decide⟩,⟨1392374, by decide⟩,⟨1392668, by decide⟩]) unmarked_context_9_6356_1392669 node_context_9_6356_1392669
  intro a
  fin_cases a
  · exact context_10_25424_1391639
  · exact context_10_25425_1391977
  · exact context_10_25426_1392374
  · exact context_10_25427_1392668

theorem selected_cut_49263 : selected 10 ⟨1369428, by decide⟩
    (prefixPartial 11 101712) = some ⟨11, 1, 0, 1369428, 101712, 1, 262144⟩ := by
  decide +kernel

theorem context_11_101712_1369428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101712 ⟨1369428, by decide⟩ :=
  accepted_of_selected 11 101712 ⟨1369428, by decide⟩ ⟨11, 1, 0, 1369428, 101712, 1, 262144⟩
    (by decide) selected_cut_49263

theorem selected_cut_49264 : selected 10 ⟨1392724, by decide⟩
    (prefixPartial 11 101713) = some ⟨11, 2, 0, 1392724, 101713, 3513, 262144⟩ := by
  decide +kernel

theorem context_11_101713_1392724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101713 ⟨1392724, by decide⟩ :=
  accepted_of_selected 11 101713 ⟨1392724, by decide⟩ ⟨11, 2, 0, 1392724, 101713, 3513, 262144⟩
    (by decide) selected_cut_49264

theorem selected_cut_49265 : selected 10 ⟨1392771, by decide⟩
    (prefixPartial 11 101714) = some ⟨11, 2, 0, 1392771, 101714, 2605, 262144⟩ := by
  decide +kernel

theorem context_11_101714_1392771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101714 ⟨1392771, by decide⟩ :=
  accepted_of_selected 11 101714 ⟨1392771, by decide⟩ ⟨11, 2, 0, 1392771, 101714, 2605, 262144⟩
    (by decide) selected_cut_49265

theorem selected_cut_49266 : selected 10 ⟨1392823, by decide⟩
    (prefixPartial 11 101715) = some ⟨11, 2, 0, 1392823, 101715, 2665, 262144⟩ := by
  decide +kernel

theorem context_11_101715_1392823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101715 ⟨1392823, by decide⟩ :=
  accepted_of_selected 11 101715 ⟨1392823, by decide⟩ ⟨11, 2, 0, 1392823, 101715, 2665, 262144⟩
    (by decide) selected_cut_49266

theorem unmarked_context_10_25428_1392824 : frontier 11 ⟨1392824, by decide⟩
    (prefixCache 10 25428) (prefixPartial 10 25428) = false := by
  decide +kernel

theorem node_context_10_25428_1392824 : EJMOriginalGlobalDAGData.nodes 11 ⟨1392824, by decide⟩ =
    .split (coordinate 10) (![⟨1369428, by decide⟩,⟨1392724, by decide⟩,⟨1392771, by decide⟩,⟨1392823, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25428_1392824 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25428 ⟨1392824, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25428
    ⟨1392824, by decide⟩ (by decide) (![⟨1369428, by decide⟩,⟨1392724, by decide⟩,⟨1392771, by decide⟩,⟨1392823, by decide⟩]) unmarked_context_10_25428_1392824 node_context_10_25428_1392824
  intro a
  fin_cases a
  · exact context_11_101712_1369428
  · exact context_11_101713_1392724
  · exact context_11_101714_1392771
  · exact context_11_101715_1392823

theorem selected_cut_49267 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 25429) = some ⟨10, 1, 0, 893098, 25429, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_25429_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25429 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 25429 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 25429, 1, 1048576⟩
    (by decide) selected_cut_49267

theorem selected_cut_49268 : selected 10 ⟨1392879, by decide⟩
    (prefixPartial 11 101720) = some ⟨11, 2, 0, 1392879, 101720, 2857, 262144⟩ := by
  decide +kernel

theorem context_11_101720_1392879 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101720 ⟨1392879, by decide⟩ :=
  accepted_of_selected 11 101720 ⟨1392879, by decide⟩ ⟨11, 2, 0, 1392879, 101720, 2857, 262144⟩
    (by decide) selected_cut_49268

theorem selected_cut_49269 : selected 10 ⟨1392929, by decide⟩
    (prefixPartial 11 101721) = some ⟨11, 2, 0, 1392929, 101721, 3233, 262144⟩ := by
  decide +kernel

theorem context_11_101721_1392929 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101721 ⟨1392929, by decide⟩ :=
  accepted_of_selected 11 101721 ⟨1392929, by decide⟩ ⟨11, 2, 0, 1392929, 101721, 3233, 262144⟩
    (by decide) selected_cut_49269

theorem selected_cut_49270 : selected 10 ⟨1369759, by decide⟩
    (prefixPartial 11 101722) = some ⟨11, 1, 0, 1369759, 101722, 1, 262144⟩ := by
  decide +kernel

theorem context_11_101722_1369759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101722 ⟨1369759, by decide⟩ :=
  accepted_of_selected 11 101722 ⟨1369759, by decide⟩ ⟨11, 1, 0, 1369759, 101722, 1, 262144⟩
    (by decide) selected_cut_49270

theorem selected_cut_49271 : selected 10 ⟨1392969, by decide⟩
    (prefixPartial 11 101723) = some ⟨11, 2, 0, 1392969, 101723, 2397, 262144⟩ := by
  decide +kernel

theorem context_11_101723_1392969 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101723 ⟨1392969, by decide⟩ :=
  accepted_of_selected 11 101723 ⟨1392969, by decide⟩ ⟨11, 2, 0, 1392969, 101723, 2397, 262144⟩
    (by decide) selected_cut_49271

theorem unmarked_context_10_25430_1392970 : frontier 11 ⟨1392970, by decide⟩
    (prefixCache 10 25430) (prefixPartial 10 25430) = false := by
  decide +kernel

theorem node_context_10_25430_1392970 : EJMOriginalGlobalDAGData.nodes 11 ⟨1392970, by decide⟩ =
    .split (coordinate 10) (![⟨1392879, by decide⟩,⟨1392929, by decide⟩,⟨1369759, by decide⟩,⟨1392969, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25430_1392970 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25430 ⟨1392970, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25430
    ⟨1392970, by decide⟩ (by decide) (![⟨1392879, by decide⟩,⟨1392929, by decide⟩,⟨1369759, by decide⟩,⟨1392969, by decide⟩]) unmarked_context_10_25430_1392970 node_context_10_25430_1392970
  intro a
  fin_cases a
  · exact context_11_101720_1392879
  · exact context_11_101721_1392929
  · exact context_11_101722_1369759
  · exact context_11_101723_1392969

theorem selected_cut_49272 : selected 10 ⟨1393017, by decide⟩
    (prefixPartial 11 101724) = some ⟨11, 2, 0, 1393017, 101724, 2597, 262144⟩ := by
  decide +kernel

theorem context_11_101724_1393017 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101724 ⟨1393017, by decide⟩ :=
  accepted_of_selected 11 101724 ⟨1393017, by decide⟩ ⟨11, 2, 0, 1393017, 101724, 2597, 262144⟩
    (by decide) selected_cut_49272

theorem selected_cut_49273 : selected 10 ⟨1393069, by decide⟩
    (prefixPartial 11 101725) = some ⟨11, 2, 0, 1393069, 101725, 3017, 262144⟩ := by
  decide +kernel

theorem context_11_101725_1393069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101725 ⟨1393069, by decide⟩ :=
  accepted_of_selected 11 101725 ⟨1393069, by decide⟩ ⟨11, 2, 0, 1393069, 101725, 3017, 262144⟩
    (by decide) selected_cut_49273

theorem selected_cut_49274 : selected 10 ⟨1393107, by decide⟩
    (prefixPartial 11 101726) = some ⟨11, 2, 0, 1393107, 101726, 2157, 262144⟩ := by
  decide +kernel

theorem context_11_101726_1393107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101726 ⟨1393107, by decide⟩ :=
  accepted_of_selected 11 101726 ⟨1393107, by decide⟩ ⟨11, 2, 0, 1393107, 101726, 2157, 262144⟩
    (by decide) selected_cut_49274

theorem selected_cut_49275 : selected 10 ⟨1370051, by decide⟩
    (prefixPartial 11 101727) = some ⟨11, 1, 0, 1370051, 101727, 1, 262144⟩ := by
  decide +kernel

theorem context_11_101727_1370051 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101727 ⟨1370051, by decide⟩ :=
  accepted_of_selected 11 101727 ⟨1370051, by decide⟩ ⟨11, 1, 0, 1370051, 101727, 1, 262144⟩
    (by decide) selected_cut_49275

theorem unmarked_context_10_25431_1393108 : frontier 11 ⟨1393108, by decide⟩
    (prefixCache 10 25431) (prefixPartial 10 25431) = false := by
  decide +kernel

theorem node_context_10_25431_1393108 : EJMOriginalGlobalDAGData.nodes 11 ⟨1393108, by decide⟩ =
    .split (coordinate 10) (![⟨1393017, by decide⟩,⟨1393069, by decide⟩,⟨1393107, by decide⟩,⟨1370051, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25431_1393108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25431 ⟨1393108, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25431
    ⟨1393108, by decide⟩ (by decide) (![⟨1393017, by decide⟩,⟨1393069, by decide⟩,⟨1393107, by decide⟩,⟨1370051, by decide⟩]) unmarked_context_10_25431_1393108 node_context_10_25431_1393108
  intro a
  fin_cases a
  · exact context_11_101724_1393017
  · exact context_11_101725_1393069
  · exact context_11_101726_1393107
  · exact context_11_101727_1370051

theorem unmarked_context_9_6357_1393109 : frontier 12 ⟨1393109, by decide⟩
    (prefixCache 9 6357) (prefixPartial 9 6357) = false := by
  decide +kernel

theorem node_context_9_6357_1393109 : EJMOriginalGlobalDAGData.nodes 12 ⟨1393109, by decide⟩ =
    .split (coordinate 9) (![⟨1392824, by decide⟩,⟨893098, by decide⟩,⟨1392970, by decide⟩,⟨1393108, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6357_1393109 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6357 ⟨1393109, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6357
    ⟨1393109, by decide⟩ (by decide) (![⟨1392824, by decide⟩,⟨893098, by decide⟩,⟨1392970, by decide⟩,⟨1393108, by decide⟩]) unmarked_context_9_6357_1393109 node_context_9_6357_1393109
  intro a
  fin_cases a
  · exact context_10_25428_1392824
  · exact context_10_25429_893098
  · exact context_10_25430_1392970
  · exact context_10_25431_1393108

theorem selected_cut_49276 : selected 10 ⟨1393133, by decide⟩
    (prefixPartial 11 101728) = some ⟨11, 2, 0, 1393133, 101728, 1117, 262144⟩ := by
  decide +kernel

theorem context_11_101728_1393133 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101728 ⟨1393133, by decide⟩ :=
  accepted_of_selected 11 101728 ⟨1393133, by decide⟩ ⟨11, 2, 0, 1393133, 101728, 1117, 262144⟩
    (by decide) selected_cut_49276

theorem selected_cut_49277 : selected 10 ⟨1393160, by decide⟩
    (prefixPartial 11 101729) = some ⟨11, 2, 0, 1393160, 101729, 1729, 262144⟩ := by
  decide +kernel

theorem context_11_101729_1393160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101729 ⟨1393160, by decide⟩ :=
  accepted_of_selected 11 101729 ⟨1393160, by decide⟩ ⟨11, 2, 0, 1393160, 101729, 1729, 262144⟩
    (by decide) selected_cut_49277

theorem selected_cut_49278 : selected 10 ⟨1393198, by decide⟩
    (prefixPartial 11 101730) = some ⟨11, 2, 0, 1393198, 101730, 2633, 262144⟩ := by
  decide +kernel

theorem context_11_101730_1393198 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101730 ⟨1393198, by decide⟩ :=
  accepted_of_selected 11 101730 ⟨1393198, by decide⟩ ⟨11, 2, 0, 1393198, 101730, 2633, 262144⟩
    (by decide) selected_cut_49278

theorem selected_cut_49279 : selected 10 ⟨1393253, by decide⟩
    (prefixPartial 11 101731) = some ⟨11, 2, 0, 1393253, 101731, 2781, 262144⟩ := by
  decide +kernel

theorem context_11_101731_1393253 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101731 ⟨1393253, by decide⟩ :=
  accepted_of_selected 11 101731 ⟨1393253, by decide⟩ ⟨11, 2, 0, 1393253, 101731, 2781, 262144⟩
    (by decide) selected_cut_49279

theorem unmarked_context_10_25432_1393254 : frontier 11 ⟨1393254, by decide⟩
    (prefixCache 10 25432) (prefixPartial 10 25432) = false := by
  decide +kernel

theorem node_context_10_25432_1393254 : EJMOriginalGlobalDAGData.nodes 11 ⟨1393254, by decide⟩ =
    .split (coordinate 10) (![⟨1393133, by decide⟩,⟨1393160, by decide⟩,⟨1393198, by decide⟩,⟨1393253, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25432_1393254 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25432 ⟨1393254, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25432
    ⟨1393254, by decide⟩ (by decide) (![⟨1393133, by decide⟩,⟨1393160, by decide⟩,⟨1393198, by decide⟩,⟨1393253, by decide⟩]) unmarked_context_10_25432_1393254 node_context_10_25432_1393254
  intro a
  fin_cases a
  · exact context_11_101728_1393133
  · exact context_11_101729_1393160
  · exact context_11_101730_1393198
  · exact context_11_101731_1393253

theorem selected_cut_49280 : selected 10 ⟨1393279, by decide⟩
    (prefixPartial 11 101732) = some ⟨11, 2, 0, 1393279, 101732, 1709, 262144⟩ := by
  decide +kernel

theorem context_11_101732_1393279 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101732 ⟨1393279, by decide⟩ :=
  accepted_of_selected 11 101732 ⟨1393279, by decide⟩ ⟨11, 2, 0, 1393279, 101732, 1709, 262144⟩
    (by decide) selected_cut_49280

theorem selected_cut_49281 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 101733) = some ⟨11, 1, 0, 892405, 101733, 1, 262144⟩ := by
  decide +kernel

theorem context_11_101733_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101733 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 101733 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 101733, 1, 262144⟩
    (by decide) selected_cut_49281

theorem selected_cut_49282 : selected 10 ⟨1393319, by decide⟩
    (prefixPartial 11 101734) = some ⟨11, 2, 0, 1393319, 101734, 2289, 262144⟩ := by
  decide +kernel

theorem context_11_101734_1393319 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101734 ⟨1393319, by decide⟩ :=
  accepted_of_selected 11 101734 ⟨1393319, by decide⟩ ⟨11, 2, 0, 1393319, 101734, 2289, 262144⟩
    (by decide) selected_cut_49282

theorem selected_cut_49283 : selected 10 ⟨1393356, by decide⟩
    (prefixPartial 11 101735) = some ⟨11, 2, 0, 1393356, 101735, 2109, 262144⟩ := by
  decide +kernel

theorem context_11_101735_1393356 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101735 ⟨1393356, by decide⟩ :=
  accepted_of_selected 11 101735 ⟨1393356, by decide⟩ ⟨11, 2, 0, 1393356, 101735, 2109, 262144⟩
    (by decide) selected_cut_49283

theorem unmarked_context_10_25433_1393357 : frontier 11 ⟨1393357, by decide⟩
    (prefixCache 10 25433) (prefixPartial 10 25433) = false := by
  decide +kernel

theorem node_context_10_25433_1393357 : EJMOriginalGlobalDAGData.nodes 11 ⟨1393357, by decide⟩ =
    .split (coordinate 10) (![⟨1393279, by decide⟩,⟨892405, by decide⟩,⟨1393319, by decide⟩,⟨1393356, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25433_1393357 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25433 ⟨1393357, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25433
    ⟨1393357, by decide⟩ (by decide) (![⟨1393279, by decide⟩,⟨892405, by decide⟩,⟨1393319, by decide⟩,⟨1393356, by decide⟩]) unmarked_context_10_25433_1393357 node_context_10_25433_1393357
  intro a
  fin_cases a
  · exact context_11_101732_1393279
  · exact context_11_101733_892405
  · exact context_11_101734_1393319
  · exact context_11_101735_1393356

theorem selected_cut_49284 : selected 11 ⟨1393383, by decide⟩
    (prefixPartial 10 25434) = some ⟨10, 2, 0, 1393383, 25434, 1897, 1048576⟩ := by
  decide +kernel

theorem context_10_25434_1393383 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25434 ⟨1393383, by decide⟩ :=
  accepted_of_selected 10 25434 ⟨1393383, by decide⟩ ⟨10, 2, 0, 1393383, 25434, 1897, 1048576⟩
    (by decide) selected_cut_49284

theorem selected_cut_49285 : selected 10 ⟨1393404, by decide⟩
    (prefixPartial 11 101740) = some ⟨11, 2, 0, 1393404, 101740, 1237, 262144⟩ := by
  decide +kernel

theorem context_11_101740_1393404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101740 ⟨1393404, by decide⟩ :=
  accepted_of_selected 11 101740 ⟨1393404, by decide⟩ ⟨11, 2, 0, 1393404, 101740, 1237, 262144⟩
    (by decide) selected_cut_49285

theorem selected_cut_49286 : selected 10 ⟨1393430, by decide⟩
    (prefixPartial 11 101741) = some ⟨11, 2, 0, 1393430, 101741, 1433, 262144⟩ := by
  decide +kernel

theorem context_11_101741_1393430 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101741 ⟨1393430, by decide⟩ :=
  accepted_of_selected 11 101741 ⟨1393430, by decide⟩ ⟨11, 2, 0, 1393430, 101741, 1433, 262144⟩
    (by decide) selected_cut_49286

theorem selected_cut_49287 : selected 10 ⟨1393462, by decide⟩
    (prefixPartial 11 101742) = some ⟨11, 2, 0, 1393462, 101742, 1473, 262144⟩ := by
  decide +kernel

theorem context_11_101742_1393462 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101742 ⟨1393462, by decide⟩ :=
  accepted_of_selected 11 101742 ⟨1393462, by decide⟩ ⟨11, 2, 0, 1393462, 101742, 1473, 262144⟩
    (by decide) selected_cut_49287

theorem selected_cut_49288 : selected 10 ⟨1393480, by decide⟩
    (prefixPartial 11 101743) = some ⟨11, 2, 0, 1393480, 101743, 993, 262144⟩ := by
  decide +kernel

theorem context_11_101743_1393480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101743 ⟨1393480, by decide⟩ :=
  accepted_of_selected 11 101743 ⟨1393480, by decide⟩ ⟨11, 2, 0, 1393480, 101743, 993, 262144⟩
    (by decide) selected_cut_49288

theorem unmarked_context_10_25435_1393481 : frontier 11 ⟨1393481, by decide⟩
    (prefixCache 10 25435) (prefixPartial 10 25435) = false := by
  decide +kernel

theorem node_context_10_25435_1393481 : EJMOriginalGlobalDAGData.nodes 11 ⟨1393481, by decide⟩ =
    .split (coordinate 10) (![⟨1393404, by decide⟩,⟨1393430, by decide⟩,⟨1393462, by decide⟩,⟨1393480, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25435_1393481 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25435 ⟨1393481, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25435
    ⟨1393481, by decide⟩ (by decide) (![⟨1393404, by decide⟩,⟨1393430, by decide⟩,⟨1393462, by decide⟩,⟨1393480, by decide⟩]) unmarked_context_10_25435_1393481 node_context_10_25435_1393481
  intro a
  fin_cases a
  · exact context_11_101740_1393404
  · exact context_11_101741_1393430
  · exact context_11_101742_1393462
  · exact context_11_101743_1393480

theorem unmarked_context_9_6358_1393482 : frontier 12 ⟨1393482, by decide⟩
    (prefixCache 9 6358) (prefixPartial 9 6358) = false := by
  decide +kernel

theorem node_context_9_6358_1393482 : EJMOriginalGlobalDAGData.nodes 12 ⟨1393482, by decide⟩ =
    .split (coordinate 9) (![⟨1393254, by decide⟩,⟨1393357, by decide⟩,⟨1393383, by decide⟩,⟨1393481, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6358_1393482 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6358 ⟨1393482, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6358
    ⟨1393482, by decide⟩ (by decide) (![⟨1393254, by decide⟩,⟨1393357, by decide⟩,⟨1393383, by decide⟩,⟨1393481, by decide⟩]) unmarked_context_9_6358_1393482 node_context_9_6358_1393482
  intro a
  fin_cases a
  · exact context_10_25432_1393254
  · exact context_10_25433_1393357
  · exact context_10_25434_1393383
  · exact context_10_25435_1393481

theorem selected_cut_49289 : selected 11 ⟨1393559, by decide⟩
    (prefixPartial 10 25436) = some ⟨10, 2, 0, 1393559, 25436, 3749, 1048576⟩ := by
  decide +kernel

theorem context_10_25436_1393559 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25436 ⟨1393559, by decide⟩ :=
  accepted_of_selected 10 25436 ⟨1393559, by decide⟩ ⟨10, 2, 0, 1393559, 25436, 3749, 1048576⟩
    (by decide) selected_cut_49289

theorem selected_cut_49290 : selected 11 ⟨1393606, by decide⟩
    (prefixPartial 10 25437) = some ⟨10, 2, 0, 1393606, 25437, 2145, 1048576⟩ := by
  decide +kernel

theorem context_10_25437_1393606 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25437 ⟨1393606, by decide⟩ :=
  accepted_of_selected 10 25437 ⟨1393606, by decide⟩ ⟨10, 2, 0, 1393606, 25437, 2145, 1048576⟩
    (by decide) selected_cut_49290

theorem selected_cut_49291 : selected 11 ⟨1393646, by decide⟩
    (prefixPartial 10 25438) = some ⟨10, 2, 0, 1393646, 25438, 1417, 1048576⟩ := by
  decide +kernel

theorem context_10_25438_1393646 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25438 ⟨1393646, by decide⟩ :=
  accepted_of_selected 10 25438 ⟨1393646, by decide⟩ ⟨10, 2, 0, 1393646, 25438, 1417, 1048576⟩
    (by decide) selected_cut_49291

theorem selected_cut_49292 : selected 11 ⟨1393649, by decide⟩
    (prefixPartial 10 25439) = some ⟨10, 2, 0, 1393649, 25439, 113, 1048576⟩ := by
  decide +kernel

theorem context_10_25439_1393649 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25439 ⟨1393649, by decide⟩ :=
  accepted_of_selected 10 25439 ⟨1393649, by decide⟩ ⟨10, 2, 0, 1393649, 25439, 113, 1048576⟩
    (by decide) selected_cut_49292

theorem unmarked_context_9_6359_1393650 : frontier 12 ⟨1393650, by decide⟩
    (prefixCache 9 6359) (prefixPartial 9 6359) = false := by
  decide +kernel

theorem node_context_9_6359_1393650 : EJMOriginalGlobalDAGData.nodes 12 ⟨1393650, by decide⟩ =
    .split (coordinate 9) (![⟨1393559, by decide⟩,⟨1393606, by decide⟩,⟨1393646, by decide⟩,⟨1393649, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6359_1393650 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6359 ⟨1393650, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6359
    ⟨1393650, by decide⟩ (by decide) (![⟨1393559, by decide⟩,⟨1393606, by decide⟩,⟨1393646, by decide⟩,⟨1393649, by decide⟩]) unmarked_context_9_6359_1393650 node_context_9_6359_1393650
  intro a
  fin_cases a
  · exact context_10_25436_1393559
  · exact context_10_25437_1393606
  · exact context_10_25438_1393646
  · exact context_10_25439_1393649

theorem unmarked_context_8_1589_1393651 : frontier 13 ⟨1393651, by decide⟩
    (prefixCache 8 1589) (prefixPartial 8 1589) = false := by
  decide +kernel

theorem node_context_8_1589_1393651 : EJMOriginalGlobalDAGData.nodes 13 ⟨1393651, by decide⟩ =
    .split (coordinate 8) (![⟨1392669, by decide⟩,⟨1393109, by decide⟩,⟨1393482, by decide⟩,⟨1393650, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1589_1393651 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1589 ⟨1393651, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1589
    ⟨1393651, by decide⟩ (by decide) (![⟨1392669, by decide⟩,⟨1393109, by decide⟩,⟨1393482, by decide⟩,⟨1393650, by decide⟩]) unmarked_context_8_1589_1393651 node_context_8_1589_1393651
  intro a
  fin_cases a
  · exact context_9_6356_1392669
  · exact context_9_6357_1393109
  · exact context_9_6358_1393482
  · exact context_9_6359_1393650

theorem selected_cut_49293 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 101760) = some ⟨11, 1, 0, 434745, 101760, 1, 262144⟩ := by
  decide +kernel

theorem context_11_101760_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101760 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 101760 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 101760, 1, 262144⟩
    (by decide) selected_cut_49293

theorem selected_cut_49294 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 101761) = some ⟨11, 1, 0, 434745, 101761, 1, 262144⟩ := by
  decide +kernel

theorem context_11_101761_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101761 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 101761 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 101761, 1, 262144⟩
    (by decide) selected_cut_49294

theorem selected_cut_49295 : selected 10 ⟨1393714, by decide⟩
    (prefixPartial 11 101762) = some ⟨11, 2, 0, 1393714, 101762, 2049, 262144⟩ := by
  decide +kernel

theorem context_11_101762_1393714 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101762 ⟨1393714, by decide⟩ :=
  accepted_of_selected 11 101762 ⟨1393714, by decide⟩ ⟨11, 2, 0, 1393714, 101762, 2049, 262144⟩
    (by decide) selected_cut_49295

theorem selected_cut_49296 : selected 10 ⟨1393799, by decide⟩
    (prefixPartial 11 101763) = some ⟨11, 2, 0, 1393799, 101763, 3077, 262144⟩ := by
  decide +kernel

theorem context_11_101763_1393799 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101763 ⟨1393799, by decide⟩ :=
  accepted_of_selected 11 101763 ⟨1393799, by decide⟩ ⟨11, 2, 0, 1393799, 101763, 3077, 262144⟩
    (by decide) selected_cut_49296

theorem unmarked_context_10_25440_1393800 : frontier 11 ⟨1393800, by decide⟩
    (prefixCache 10 25440) (prefixPartial 10 25440) = false := by
  decide +kernel

theorem node_context_10_25440_1393800 : EJMOriginalGlobalDAGData.nodes 11 ⟨1393800, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨434745, by decide⟩,⟨1393714, by decide⟩,⟨1393799, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25440_1393800 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25440 ⟨1393800, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25440
    ⟨1393800, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨434745, by decide⟩,⟨1393714, by decide⟩,⟨1393799, by decide⟩]) unmarked_context_10_25440_1393800 node_context_10_25440_1393800
  intro a
  fin_cases a
  · exact context_11_101760_434745
  · exact context_11_101761_434745
  · exact context_11_101762_1393714
  · exact context_11_101763_1393799

theorem selected_cut_49297 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 407056) = some ⟨12, 1, 0, 1108174, 407056, 1, 65536⟩ := by
  decide +kernel

theorem context_12_407056_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407056 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 407056 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 407056, 1, 65536⟩
    (by decide) selected_cut_49297

theorem selected_cut_49298 : selected 9 ⟨1393853, by decide⟩
    (prefixPartial 12 407057) = some ⟨12, 2, 0, 1393853, 407057, 2417, 65536⟩ := by
  decide +kernel

theorem context_12_407057_1393853 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407057 ⟨1393853, by decide⟩ :=
  accepted_of_selected 12 407057 ⟨1393853, by decide⟩ ⟨12, 2, 0, 1393853, 407057, 2417, 65536⟩
    (by decide) selected_cut_49298

theorem selected_cut_49299 : selected 9 ⟨1393922, by decide⟩
    (prefixPartial 12 407058) = some ⟨12, 2, 0, 1393922, 407058, 2753, 65536⟩ := by
  decide +kernel

theorem context_12_407058_1393922 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407058 ⟨1393922, by decide⟩ :=
  accepted_of_selected 12 407058 ⟨1393922, by decide⟩ ⟨12, 2, 0, 1393922, 407058, 2753, 65536⟩
    (by decide) selected_cut_49299

theorem selected_cut_49300 : selected 9 ⟨1393980, by decide⟩
    (prefixPartial 12 407059) = some ⟨12, 2, 0, 1393980, 407059, 2401, 65536⟩ := by
  decide +kernel

theorem context_12_407059_1393980 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407059 ⟨1393980, by decide⟩ :=
  accepted_of_selected 12 407059 ⟨1393980, by decide⟩ ⟨12, 2, 0, 1393980, 407059, 2401, 65536⟩
    (by decide) selected_cut_49300

theorem unmarked_context_11_101764_1393981 : frontier 10 ⟨1393981, by decide⟩
    (prefixCache 11 101764) (prefixPartial 11 101764) = false := by
  decide +kernel

theorem node_context_11_101764_1393981 : EJMOriginalGlobalDAGData.nodes 10 ⟨1393981, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1393853, by decide⟩,⟨1393922, by decide⟩,⟨1393980, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_101764_1393981 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101764 ⟨1393981, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 101764
    ⟨1393981, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1393853, by decide⟩,⟨1393922, by decide⟩,⟨1393980, by decide⟩]) unmarked_context_11_101764_1393981 node_context_11_101764_1393981
  intro a
  fin_cases a
  · exact context_12_407056_1108174
  · exact context_12_407057_1393853
  · exact context_12_407058_1393922
  · exact context_12_407059_1393980

theorem selected_cut_49301 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 101765) = some ⟨11, 1, 0, 892405, 101765, 1, 262144⟩ := by
  decide +kernel

theorem context_11_101765_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101765 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 101765 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 101765, 1, 262144⟩
    (by decide) selected_cut_49301

theorem selected_cut_49302 : selected 10 ⟨1394062, by decide⟩
    (prefixPartial 11 101766) = some ⟨11, 2, 0, 1394062, 101766, 3865, 262144⟩ := by
  decide +kernel

theorem context_11_101766_1394062 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101766 ⟨1394062, by decide⟩ :=
  accepted_of_selected 11 101766 ⟨1394062, by decide⟩ ⟨11, 2, 0, 1394062, 101766, 3865, 262144⟩
    (by decide) selected_cut_49302

theorem selected_cut_49303 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 407068) = some ⟨12, 1, 0, 1108174, 407068, 1, 65536⟩ := by
  decide +kernel

theorem context_12_407068_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407068 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 407068 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 407068, 1, 65536⟩
    (by decide) selected_cut_49303

theorem selected_cut_49304 : selected 9 ⟨1394099, by decide⟩
    (prefixPartial 12 407069) = some ⟨12, 2, 0, 1394099, 407069, 1973, 65536⟩ := by
  decide +kernel

theorem context_12_407069_1394099 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407069 ⟨1394099, by decide⟩ :=
  accepted_of_selected 12 407069 ⟨1394099, by decide⟩ ⟨12, 2, 0, 1394099, 407069, 1973, 65536⟩
    (by decide) selected_cut_49304

theorem selected_cut_49305 : selected 9 ⟨1394154, by decide⟩
    (prefixPartial 12 407070) = some ⟨12, 2, 0, 1394154, 407070, 2317, 65536⟩ := by
  decide +kernel

theorem context_12_407070_1394154 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407070 ⟨1394154, by decide⟩ :=
  accepted_of_selected 12 407070 ⟨1394154, by decide⟩ ⟨12, 2, 0, 1394154, 407070, 2317, 65536⟩
    (by decide) selected_cut_49305

theorem selected_cut_49306 : selected 9 ⟨1394195, by decide⟩
    (prefixPartial 12 407071) = some ⟨12, 2, 0, 1394195, 407071, 1901, 65536⟩ := by
  decide +kernel

theorem context_12_407071_1394195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407071 ⟨1394195, by decide⟩ :=
  accepted_of_selected 12 407071 ⟨1394195, by decide⟩ ⟨12, 2, 0, 1394195, 407071, 1901, 65536⟩
    (by decide) selected_cut_49306

theorem unmarked_context_11_101767_1394196 : frontier 10 ⟨1394196, by decide⟩
    (prefixCache 11 101767) (prefixPartial 11 101767) = false := by
  decide +kernel

theorem node_context_11_101767_1394196 : EJMOriginalGlobalDAGData.nodes 10 ⟨1394196, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1394099, by decide⟩,⟨1394154, by decide⟩,⟨1394195, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_101767_1394196 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101767 ⟨1394196, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 101767
    ⟨1394196, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1394099, by decide⟩,⟨1394154, by decide⟩,⟨1394195, by decide⟩]) unmarked_context_11_101767_1394196 node_context_11_101767_1394196
  intro a
  fin_cases a
  · exact context_12_407068_1108174
  · exact context_12_407069_1394099
  · exact context_12_407070_1394154
  · exact context_12_407071_1394195

theorem unmarked_context_10_25441_1394197 : frontier 11 ⟨1394197, by decide⟩
    (prefixCache 10 25441) (prefixPartial 10 25441) = false := by
  decide +kernel

theorem node_context_10_25441_1394197 : EJMOriginalGlobalDAGData.nodes 11 ⟨1394197, by decide⟩ =
    .split (coordinate 10) (![⟨1393981, by decide⟩,⟨892405, by decide⟩,⟨1394062, by decide⟩,⟨1394196, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25441_1394197 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25441 ⟨1394197, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25441
    ⟨1394197, by decide⟩ (by decide) (![⟨1393981, by decide⟩,⟨892405, by decide⟩,⟨1394062, by decide⟩,⟨1394196, by decide⟩]) unmarked_context_10_25441_1394197 node_context_10_25441_1394197
  intro a
  fin_cases a
  · exact context_11_101764_1393981
  · exact context_11_101765_892405
  · exact context_11_101766_1394062
  · exact context_11_101767_1394196

theorem selected_cut_49307 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 407072) = some ⟨12, 1, 0, 1108174, 407072, 1, 65536⟩ := by
  decide +kernel

theorem context_12_407072_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407072 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 407072 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 407072, 1, 65536⟩
    (by decide) selected_cut_49307

theorem selected_cut_49308 : selected 9 ⟨1394253, by decide⟩
    (prefixPartial 12 407073) = some ⟨12, 2, 0, 1394253, 407073, 2349, 65536⟩ := by
  decide +kernel

theorem context_12_407073_1394253 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407073 ⟨1394253, by decide⟩ :=
  accepted_of_selected 12 407073 ⟨1394253, by decide⟩ ⟨12, 2, 0, 1394253, 407073, 2349, 65536⟩
    (by decide) selected_cut_49308

theorem selected_cut_49309 : selected 9 ⟨1394321, by decide⟩
    (prefixPartial 12 407074) = some ⟨12, 2, 0, 1394321, 407074, 2765, 65536⟩ := by
  decide +kernel

theorem context_12_407074_1394321 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407074 ⟨1394321, by decide⟩ :=
  accepted_of_selected 12 407074 ⟨1394321, by decide⟩ ⟨12, 2, 0, 1394321, 407074, 2765, 65536⟩
    (by decide) selected_cut_49309

theorem selected_cut_49310 : selected 9 ⟨1394373, by decide⟩
    (prefixPartial 12 407075) = some ⟨12, 2, 0, 1394373, 407075, 2357, 65536⟩ := by
  decide +kernel

theorem context_12_407075_1394373 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407075 ⟨1394373, by decide⟩ :=
  accepted_of_selected 12 407075 ⟨1394373, by decide⟩ ⟨12, 2, 0, 1394373, 407075, 2357, 65536⟩
    (by decide) selected_cut_49310

theorem unmarked_context_11_101768_1394374 : frontier 10 ⟨1394374, by decide⟩
    (prefixCache 11 101768) (prefixPartial 11 101768) = false := by
  decide +kernel

theorem node_context_11_101768_1394374 : EJMOriginalGlobalDAGData.nodes 10 ⟨1394374, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1394253, by decide⟩,⟨1394321, by decide⟩,⟨1394373, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_101768_1394374 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101768 ⟨1394374, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 101768
    ⟨1394374, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1394253, by decide⟩,⟨1394321, by decide⟩,⟨1394373, by decide⟩]) unmarked_context_11_101768_1394374 node_context_11_101768_1394374
  intro a
  fin_cases a
  · exact context_12_407072_1108174
  · exact context_12_407073_1394253
  · exact context_12_407074_1394321
  · exact context_12_407075_1394373

theorem selected_cut_49311 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 407076) = some ⟨12, 1, 0, 1108174, 407076, 1, 65536⟩ := by
  decide +kernel

theorem context_12_407076_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407076 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 407076 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 407076, 1, 65536⟩
    (by decide) selected_cut_49311

theorem selected_cut_49312 : selected 9 ⟨1387565, by decide⟩
    (prefixPartial 12 407077) = some ⟨12, 1, 0, 1387565, 407077, 1, 65536⟩ := by
  decide +kernel

theorem context_12_407077_1387565 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407077 ⟨1387565, by decide⟩ :=
  accepted_of_selected 12 407077 ⟨1387565, by decide⟩ ⟨12, 1, 0, 1387565, 407077, 1, 65536⟩
    (by decide) selected_cut_49312

theorem selected_cut_49313 : selected 9 ⟨1394427, by decide⟩
    (prefixPartial 12 407078) = some ⟨12, 2, 0, 1394427, 407078, 2245, 65536⟩ := by
  decide +kernel

theorem context_12_407078_1394427 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407078 ⟨1394427, by decide⟩ :=
  accepted_of_selected 12 407078 ⟨1394427, by decide⟩ ⟨12, 2, 0, 1394427, 407078, 2245, 65536⟩
    (by decide) selected_cut_49313

theorem selected_cut_49314 : selected 9 ⟨1394465, by decide⟩
    (prefixPartial 12 407079) = some ⟨12, 2, 0, 1394465, 407079, 1945, 65536⟩ := by
  decide +kernel

theorem context_12_407079_1394465 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407079 ⟨1394465, by decide⟩ :=
  accepted_of_selected 12 407079 ⟨1394465, by decide⟩ ⟨12, 2, 0, 1394465, 407079, 1945, 65536⟩
    (by decide) selected_cut_49314

theorem unmarked_context_11_101769_1394466 : frontier 10 ⟨1394466, by decide⟩
    (prefixCache 11 101769) (prefixPartial 11 101769) = false := by
  decide +kernel

theorem node_context_11_101769_1394466 : EJMOriginalGlobalDAGData.nodes 10 ⟨1394466, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1387565, by decide⟩,⟨1394427, by decide⟩,⟨1394465, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_101769_1394466 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101769 ⟨1394466, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 101769
    ⟨1394466, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1387565, by decide⟩,⟨1394427, by decide⟩,⟨1394465, by decide⟩]) unmarked_context_11_101769_1394466 node_context_11_101769_1394466
  intro a
  fin_cases a
  · exact context_12_407076_1108174
  · exact context_12_407077_1387565
  · exact context_12_407078_1394427
  · exact context_12_407079_1394465

theorem selected_cut_49315 : selected 10 ⟨1394510, by decide⟩
    (prefixPartial 11 101770) = some ⟨11, 2, 0, 1394510, 101770, 1917, 262144⟩ := by
  decide +kernel

theorem context_11_101770_1394510 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101770 ⟨1394510, by decide⟩ :=
  accepted_of_selected 11 101770 ⟨1394510, by decide⟩ ⟨11, 2, 0, 1394510, 101770, 1917, 262144⟩
    (by decide) selected_cut_49315

theorem selected_cut_49316 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 407084) = some ⟨12, 1, 0, 1108174, 407084, 1, 65536⟩ := by
  decide +kernel

theorem context_12_407084_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407084 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 407084 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 407084, 1, 65536⟩
    (by decide) selected_cut_49316

theorem selected_cut_49317 : selected 9 ⟨1394552, by decide⟩
    (prefixPartial 12 407085) = some ⟨12, 2, 0, 1394552, 407085, 1933, 65536⟩ := by
  decide +kernel

theorem context_12_407085_1394552 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407085 ⟨1394552, by decide⟩ :=
  accepted_of_selected 12 407085 ⟨1394552, by decide⟩ ⟨12, 2, 0, 1394552, 407085, 1933, 65536⟩
    (by decide) selected_cut_49317

theorem selected_cut_49318 : selected 9 ⟨1394603, by decide⟩
    (prefixPartial 12 407086) = some ⟨12, 2, 0, 1394603, 407086, 2353, 65536⟩ := by
  decide +kernel

theorem context_12_407086_1394603 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407086 ⟨1394603, by decide⟩ :=
  accepted_of_selected 12 407086 ⟨1394603, by decide⟩ ⟨12, 2, 0, 1394603, 407086, 2353, 65536⟩
    (by decide) selected_cut_49318

theorem selected_cut_49319 : selected 9 ⟨1387722, by decide⟩
    (prefixPartial 12 407087) = some ⟨12, 1, 0, 1387722, 407087, 1, 65536⟩ := by
  decide +kernel

theorem context_12_407087_1387722 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407087 ⟨1387722, by decide⟩ :=
  accepted_of_selected 12 407087 ⟨1387722, by decide⟩ ⟨12, 1, 0, 1387722, 407087, 1, 65536⟩
    (by decide) selected_cut_49319

theorem unmarked_context_11_101771_1394604 : frontier 10 ⟨1394604, by decide⟩
    (prefixCache 11 101771) (prefixPartial 11 101771) = false := by
  decide +kernel

theorem node_context_11_101771_1394604 : EJMOriginalGlobalDAGData.nodes 10 ⟨1394604, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1394552, by decide⟩,⟨1394603, by decide⟩,⟨1387722, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_101771_1394604 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101771 ⟨1394604, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 101771
    ⟨1394604, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1394552, by decide⟩,⟨1394603, by decide⟩,⟨1387722, by decide⟩]) unmarked_context_11_101771_1394604 node_context_11_101771_1394604
  intro a
  fin_cases a
  · exact context_12_407084_1108174
  · exact context_12_407085_1394552
  · exact context_12_407086_1394603
  · exact context_12_407087_1387722

theorem unmarked_context_10_25442_1394605 : frontier 11 ⟨1394605, by decide⟩
    (prefixCache 10 25442) (prefixPartial 10 25442) = false := by
  decide +kernel

theorem node_context_10_25442_1394605 : EJMOriginalGlobalDAGData.nodes 11 ⟨1394605, by decide⟩ =
    .split (coordinate 10) (![⟨1394374, by decide⟩,⟨1394466, by decide⟩,⟨1394510, by decide⟩,⟨1394604, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25442_1394605 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25442 ⟨1394605, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25442
    ⟨1394605, by decide⟩ (by decide) (![⟨1394374, by decide⟩,⟨1394466, by decide⟩,⟨1394510, by decide⟩,⟨1394604, by decide⟩]) unmarked_context_10_25442_1394605 node_context_10_25442_1394605
  intro a
  fin_cases a
  · exact context_11_101768_1394374
  · exact context_11_101769_1394466
  · exact context_11_101770_1394510
  · exact context_11_101771_1394604

theorem selected_cut_49320 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 407088) = some ⟨12, 1, 0, 1108174, 407088, 1, 65536⟩ := by
  decide +kernel

theorem context_12_407088_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407088 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 407088 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 407088, 1, 65536⟩
    (by decide) selected_cut_49320

theorem selected_cut_49321 : selected 9 ⟨1394647, by decide⟩
    (prefixPartial 12 407089) = some ⟨12, 2, 0, 1394647, 407089, 1821, 65536⟩ := by
  decide +kernel

theorem context_12_407089_1394647 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407089 ⟨1394647, by decide⟩ :=
  accepted_of_selected 12 407089 ⟨1394647, by decide⟩ ⟨12, 2, 0, 1394647, 407089, 1821, 65536⟩
    (by decide) selected_cut_49321

theorem selected_cut_49322 : selected 9 ⟨1394690, by decide⟩
    (prefixPartial 12 407090) = some ⟨12, 2, 0, 1394690, 407090, 2029, 65536⟩ := by
  decide +kernel

theorem context_12_407090_1394690 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407090 ⟨1394690, by decide⟩ :=
  accepted_of_selected 12 407090 ⟨1394690, by decide⟩ ⟨12, 2, 0, 1394690, 407090, 2029, 65536⟩
    (by decide) selected_cut_49322

theorem selected_cut_49323 : selected 9 ⟨1394733, by decide⟩
    (prefixPartial 12 407091) = some ⟨12, 2, 0, 1394733, 407091, 1829, 65536⟩ := by
  decide +kernel

theorem context_12_407091_1394733 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407091 ⟨1394733, by decide⟩ :=
  accepted_of_selected 12 407091 ⟨1394733, by decide⟩ ⟨12, 2, 0, 1394733, 407091, 1829, 65536⟩
    (by decide) selected_cut_49323

theorem unmarked_context_11_101772_1394734 : frontier 10 ⟨1394734, by decide⟩
    (prefixCache 11 101772) (prefixPartial 11 101772) = false := by
  decide +kernel

theorem node_context_11_101772_1394734 : EJMOriginalGlobalDAGData.nodes 10 ⟨1394734, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1394647, by decide⟩,⟨1394690, by decide⟩,⟨1394733, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_101772_1394734 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101772 ⟨1394734, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 101772
    ⟨1394734, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1394647, by decide⟩,⟨1394690, by decide⟩,⟨1394733, by decide⟩]) unmarked_context_11_101772_1394734 node_context_11_101772_1394734
  intro a
  fin_cases a
  · exact context_12_407088_1108174
  · exact context_12_407089_1394647
  · exact context_12_407090_1394690
  · exact context_12_407091_1394733

theorem selected_cut_49324 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 407092) = some ⟨12, 1, 0, 1108174, 407092, 1, 65536⟩ := by
  decide +kernel

theorem context_12_407092_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407092 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 407092 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 407092, 1, 65536⟩
    (by decide) selected_cut_49324

theorem selected_cut_49325 : selected 9 ⟨1394765, by decide⟩
    (prefixPartial 12 407093) = some ⟨12, 2, 0, 1394765, 407093, 1469, 65536⟩ := by
  decide +kernel

theorem context_12_407093_1394765 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407093 ⟨1394765, by decide⟩ :=
  accepted_of_selected 12 407093 ⟨1394765, by decide⟩ ⟨12, 2, 0, 1394765, 407093, 1469, 65536⟩
    (by decide) selected_cut_49325

theorem selected_cut_49326 : selected 9 ⟨1394797, by decide⟩
    (prefixPartial 12 407094) = some ⟨12, 2, 0, 1394797, 407094, 1637, 65536⟩ := by
  decide +kernel

theorem context_12_407094_1394797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407094 ⟨1394797, by decide⟩ :=
  accepted_of_selected 12 407094 ⟨1394797, by decide⟩ ⟨12, 2, 0, 1394797, 407094, 1637, 65536⟩
    (by decide) selected_cut_49326

theorem selected_cut_49327 : selected 9 ⟨1394821, by decide⟩
    (prefixPartial 12 407095) = some ⟨12, 2, 0, 1394821, 407095, 1385, 65536⟩ := by
  decide +kernel

theorem context_12_407095_1394821 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407095 ⟨1394821, by decide⟩ :=
  accepted_of_selected 12 407095 ⟨1394821, by decide⟩ ⟨12, 2, 0, 1394821, 407095, 1385, 65536⟩
    (by decide) selected_cut_49327

theorem unmarked_context_11_101773_1394822 : frontier 10 ⟨1394822, by decide⟩
    (prefixCache 11 101773) (prefixPartial 11 101773) = false := by
  decide +kernel

theorem node_context_11_101773_1394822 : EJMOriginalGlobalDAGData.nodes 10 ⟨1394822, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1394765, by decide⟩,⟨1394797, by decide⟩,⟨1394821, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_101773_1394822 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101773 ⟨1394822, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 101773
    ⟨1394822, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1394765, by decide⟩,⟨1394797, by decide⟩,⟨1394821, by decide⟩]) unmarked_context_11_101773_1394822 node_context_11_101773_1394822
  intro a
  fin_cases a
  · exact context_12_407092_1108174
  · exact context_12_407093_1394765
  · exact context_12_407094_1394797
  · exact context_12_407095_1394821

theorem selected_cut_49328 : selected 10 ⟨1394883, by decide⟩
    (prefixPartial 11 101774) = some ⟨11, 2, 0, 1394883, 101774, 2953, 262144⟩ := by
  decide +kernel

theorem context_11_101774_1394883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101774 ⟨1394883, by decide⟩ :=
  accepted_of_selected 11 101774 ⟨1394883, by decide⟩ ⟨11, 2, 0, 1394883, 101774, 2953, 262144⟩
    (by decide) selected_cut_49328

theorem selected_cut_49329 : selected 10 ⟨1394916, by decide⟩
    (prefixPartial 11 101775) = some ⟨11, 2, 0, 1394916, 101775, 1649, 262144⟩ := by
  decide +kernel

theorem context_11_101775_1394916 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101775 ⟨1394916, by decide⟩ :=
  accepted_of_selected 11 101775 ⟨1394916, by decide⟩ ⟨11, 2, 0, 1394916, 101775, 1649, 262144⟩
    (by decide) selected_cut_49329

theorem unmarked_context_10_25443_1394917 : frontier 11 ⟨1394917, by decide⟩
    (prefixCache 10 25443) (prefixPartial 10 25443) = false := by
  decide +kernel

theorem node_context_10_25443_1394917 : EJMOriginalGlobalDAGData.nodes 11 ⟨1394917, by decide⟩ =
    .split (coordinate 10) (![⟨1394734, by decide⟩,⟨1394822, by decide⟩,⟨1394883, by decide⟩,⟨1394916, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25443_1394917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25443 ⟨1394917, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25443
    ⟨1394917, by decide⟩ (by decide) (![⟨1394734, by decide⟩,⟨1394822, by decide⟩,⟨1394883, by decide⟩,⟨1394916, by decide⟩]) unmarked_context_10_25443_1394917 node_context_10_25443_1394917
  intro a
  fin_cases a
  · exact context_11_101772_1394734
  · exact context_11_101773_1394822
  · exact context_11_101774_1394883
  · exact context_11_101775_1394916

theorem unmarked_context_9_6360_1394918 : frontier 12 ⟨1394918, by decide⟩
    (prefixCache 9 6360) (prefixPartial 9 6360) = false := by
  decide +kernel

theorem node_context_9_6360_1394918 : EJMOriginalGlobalDAGData.nodes 12 ⟨1394918, by decide⟩ =
    .split (coordinate 9) (![⟨1393800, by decide⟩,⟨1394197, by decide⟩,⟨1394605, by decide⟩,⟨1394917, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6360_1394918 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6360 ⟨1394918, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6360
    ⟨1394918, by decide⟩ (by decide) (![⟨1393800, by decide⟩,⟨1394197, by decide⟩,⟨1394605, by decide⟩,⟨1394917, by decide⟩]) unmarked_context_9_6360_1394918 node_context_9_6360_1394918
  intro a
  fin_cases a
  · exact context_10_25440_1393800
  · exact context_10_25441_1394197
  · exact context_10_25442_1394605
  · exact context_10_25443_1394917

theorem selected_cut_49330 : selected 10 ⟨1369428, by decide⟩
    (prefixPartial 11 101776) = some ⟨11, 1, 0, 1369428, 101776, 1, 262144⟩ := by
  decide +kernel

theorem context_11_101776_1369428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101776 ⟨1369428, by decide⟩ :=
  accepted_of_selected 11 101776 ⟨1369428, by decide⟩ ⟨11, 1, 0, 1369428, 101776, 1, 262144⟩
    (by decide) selected_cut_49330

theorem selected_cut_49331 : selected 9 ⟨1394949, by decide⟩
    (prefixPartial 12 407108) = some ⟨12, 2, 0, 1394949, 407108, 1417, 65536⟩ := by
  decide +kernel

theorem context_12_407108_1394949 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407108 ⟨1394949, by decide⟩ :=
  accepted_of_selected 12 407108 ⟨1394949, by decide⟩ ⟨12, 2, 0, 1394949, 407108, 1417, 65536⟩
    (by decide) selected_cut_49331

theorem selected_cut_49332 : selected 9 ⟨642341, by decide⟩
    (prefixPartial 12 407109) = some ⟨12, 1, 0, 642341, 407109, 1, 65536⟩ := by
  decide +kernel

theorem context_12_407109_642341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407109 ⟨642341, by decide⟩ :=
  accepted_of_selected 12 407109 ⟨642341, by decide⟩ ⟨12, 1, 0, 642341, 407109, 1, 65536⟩
    (by decide) selected_cut_49332

theorem selected_cut_49333 : selected 9 ⟨1394973, by decide⟩
    (prefixPartial 12 407110) = some ⟨12, 2, 0, 1394973, 407110, 1501, 65536⟩ := by
  decide +kernel

theorem context_12_407110_1394973 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407110 ⟨1394973, by decide⟩ :=
  accepted_of_selected 12 407110 ⟨1394973, by decide⟩ ⟨12, 2, 0, 1394973, 407110, 1501, 65536⟩
    (by decide) selected_cut_49333

theorem selected_cut_49334 : selected 9 ⟨1395001, by decide⟩
    (prefixPartial 12 407111) = some ⟨12, 2, 0, 1395001, 407111, 1493, 65536⟩ := by
  decide +kernel

theorem context_12_407111_1395001 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407111 ⟨1395001, by decide⟩ :=
  accepted_of_selected 12 407111 ⟨1395001, by decide⟩ ⟨12, 2, 0, 1395001, 407111, 1493, 65536⟩
    (by decide) selected_cut_49334

theorem unmarked_context_11_101777_1395002 : frontier 10 ⟨1395002, by decide⟩
    (prefixCache 11 101777) (prefixPartial 11 101777) = false := by
  decide +kernel

theorem node_context_11_101777_1395002 : EJMOriginalGlobalDAGData.nodes 10 ⟨1395002, by decide⟩ =
    .split (coordinate 11) (![⟨1394949, by decide⟩,⟨642341, by decide⟩,⟨1394973, by decide⟩,⟨1395001, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_101777_1395002 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101777 ⟨1395002, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 101777
    ⟨1395002, by decide⟩ (by decide) (![⟨1394949, by decide⟩,⟨642341, by decide⟩,⟨1394973, by decide⟩,⟨1395001, by decide⟩]) unmarked_context_11_101777_1395002 node_context_11_101777_1395002
  intro a
  fin_cases a
  · exact context_12_407108_1394949
  · exact context_12_407109_642341
  · exact context_12_407110_1394973
  · exact context_12_407111_1395001

theorem selected_cut_49335 : selected 10 ⟨1395059, by decide⟩
    (prefixPartial 11 101778) = some ⟨11, 2, 0, 1395059, 101778, 2929, 262144⟩ := by
  decide +kernel

theorem context_11_101778_1395059 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101778 ⟨1395059, by decide⟩ :=
  accepted_of_selected 11 101778 ⟨1395059, by decide⟩ ⟨11, 2, 0, 1395059, 101778, 2929, 262144⟩
    (by decide) selected_cut_49335

theorem selected_cut_49336 : selected 9 ⟨1395097, by decide⟩
    (prefixPartial 12 407116) = some ⟨12, 2, 0, 1395097, 407116, 1613, 65536⟩ := by
  decide +kernel

theorem context_12_407116_1395097 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407116 ⟨1395097, by decide⟩ :=
  accepted_of_selected 12 407116 ⟨1395097, by decide⟩ ⟨12, 2, 0, 1395097, 407116, 1613, 65536⟩
    (by decide) selected_cut_49336

theorem selected_cut_49337 : selected 9 ⟨642341, by decide⟩
    (prefixPartial 12 407117) = some ⟨12, 1, 0, 642341, 407117, 1, 65536⟩ := by
  decide +kernel

theorem context_12_407117_642341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407117 ⟨642341, by decide⟩ :=
  accepted_of_selected 12 407117 ⟨642341, by decide⟩ ⟨12, 1, 0, 642341, 407117, 1, 65536⟩
    (by decide) selected_cut_49337

theorem selected_cut_49338 : selected 9 ⟨1395134, by decide⟩
    (prefixPartial 12 407118) = some ⟨12, 2, 0, 1395134, 407118, 1609, 65536⟩ := by
  decide +kernel

theorem context_12_407118_1395134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407118 ⟨1395134, by decide⟩ :=
  accepted_of_selected 12 407118 ⟨1395134, by decide⟩ ⟨12, 2, 0, 1395134, 407118, 1609, 65536⟩
    (by decide) selected_cut_49338

theorem selected_cut_49339 : selected 9 ⟨1395165, by decide⟩
    (prefixPartial 12 407119) = some ⟨12, 2, 0, 1395165, 407119, 1521, 65536⟩ := by
  decide +kernel

theorem context_12_407119_1395165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407119 ⟨1395165, by decide⟩ :=
  accepted_of_selected 12 407119 ⟨1395165, by decide⟩ ⟨12, 2, 0, 1395165, 407119, 1521, 65536⟩
    (by decide) selected_cut_49339

theorem unmarked_context_11_101779_1395166 : frontier 10 ⟨1395166, by decide⟩
    (prefixCache 11 101779) (prefixPartial 11 101779) = false := by
  decide +kernel

theorem node_context_11_101779_1395166 : EJMOriginalGlobalDAGData.nodes 10 ⟨1395166, by decide⟩ =
    .split (coordinate 11) (![⟨1395097, by decide⟩,⟨642341, by decide⟩,⟨1395134, by decide⟩,⟨1395165, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_101779_1395166 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101779 ⟨1395166, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 101779
    ⟨1395166, by decide⟩ (by decide) (![⟨1395097, by decide⟩,⟨642341, by decide⟩,⟨1395134, by decide⟩,⟨1395165, by decide⟩]) unmarked_context_11_101779_1395166 node_context_11_101779_1395166
  intro a
  fin_cases a
  · exact context_12_407116_1395097
  · exact context_12_407117_642341
  · exact context_12_407118_1395134
  · exact context_12_407119_1395165

theorem unmarked_context_10_25444_1395167 : frontier 11 ⟨1395167, by decide⟩
    (prefixCache 10 25444) (prefixPartial 10 25444) = false := by
  decide +kernel

theorem node_context_10_25444_1395167 : EJMOriginalGlobalDAGData.nodes 11 ⟨1395167, by decide⟩ =
    .split (coordinate 10) (![⟨1369428, by decide⟩,⟨1395002, by decide⟩,⟨1395059, by decide⟩,⟨1395166, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25444_1395167 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25444 ⟨1395167, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25444
    ⟨1395167, by decide⟩ (by decide) (![⟨1369428, by decide⟩,⟨1395002, by decide⟩,⟨1395059, by decide⟩,⟨1395166, by decide⟩]) unmarked_context_10_25444_1395167 node_context_10_25444_1395167
  intro a
  fin_cases a
  · exact context_11_101776_1369428
  · exact context_11_101777_1395002
  · exact context_11_101778_1395059
  · exact context_11_101779_1395166

theorem selected_cut_49340 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 25445) = some ⟨10, 1, 0, 893098, 25445, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_25445_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25445 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 25445 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 25445, 1, 1048576⟩
    (by decide) selected_cut_49340

theorem selected_cut_49341 : selected 10 ⟨1395233, by decide⟩
    (prefixPartial 11 101784) = some ⟨11, 2, 0, 1395233, 101784, 3149, 262144⟩ := by
  decide +kernel

theorem context_11_101784_1395233 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101784 ⟨1395233, by decide⟩ :=
  accepted_of_selected 11 101784 ⟨1395233, by decide⟩ ⟨11, 2, 0, 1395233, 101784, 3149, 262144⟩
    (by decide) selected_cut_49341

theorem selected_cut_49342 : selected 10 ⟨1395303, by decide⟩
    (prefixPartial 11 101785) = some ⟨11, 2, 0, 1395303, 101785, 3977, 262144⟩ := by
  decide +kernel

theorem context_11_101785_1395303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101785 ⟨1395303, by decide⟩ :=
  accepted_of_selected 11 101785 ⟨1395303, by decide⟩ ⟨11, 2, 0, 1395303, 101785, 3977, 262144⟩
    (by decide) selected_cut_49342

theorem selected_cut_49343 : selected 10 ⟨1369759, by decide⟩
    (prefixPartial 11 101786) = some ⟨11, 1, 0, 1369759, 101786, 1, 262144⟩ := by
  decide +kernel

theorem context_11_101786_1369759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101786 ⟨1369759, by decide⟩ :=
  accepted_of_selected 11 101786 ⟨1369759, by decide⟩ ⟨11, 1, 0, 1369759, 101786, 1, 262144⟩
    (by decide) selected_cut_49343

theorem selected_cut_49344 : selected 10 ⟨1395371, by decide⟩
    (prefixPartial 11 101787) = some ⟨11, 2, 0, 1395371, 101787, 3709, 262144⟩ := by
  decide +kernel

theorem context_11_101787_1395371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101787 ⟨1395371, by decide⟩ :=
  accepted_of_selected 11 101787 ⟨1395371, by decide⟩ ⟨11, 2, 0, 1395371, 101787, 3709, 262144⟩
    (by decide) selected_cut_49344

theorem unmarked_context_10_25446_1395372 : frontier 11 ⟨1395372, by decide⟩
    (prefixCache 10 25446) (prefixPartial 10 25446) = false := by
  decide +kernel

theorem node_context_10_25446_1395372 : EJMOriginalGlobalDAGData.nodes 11 ⟨1395372, by decide⟩ =
    .split (coordinate 10) (![⟨1395233, by decide⟩,⟨1395303, by decide⟩,⟨1369759, by decide⟩,⟨1395371, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25446_1395372 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25446 ⟨1395372, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25446
    ⟨1395372, by decide⟩ (by decide) (![⟨1395233, by decide⟩,⟨1395303, by decide⟩,⟨1369759, by decide⟩,⟨1395371, by decide⟩]) unmarked_context_10_25446_1395372 node_context_10_25446_1395372
  intro a
  fin_cases a
  · exact context_11_101784_1395233
  · exact context_11_101785_1395303
  · exact context_11_101786_1369759
  · exact context_11_101787_1395371

theorem selected_cut_49345 : selected 10 ⟨1395437, by decide⟩
    (prefixPartial 11 101788) = some ⟨11, 2, 0, 1395437, 101788, 3393, 262144⟩ := by
  decide +kernel

theorem context_11_101788_1395437 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101788 ⟨1395437, by decide⟩ :=
  accepted_of_selected 11 101788 ⟨1395437, by decide⟩ ⟨11, 2, 0, 1395437, 101788, 3393, 262144⟩
    (by decide) selected_cut_49345

theorem selected_cut_49346 : selected 10 ⟨1395492, by decide⟩
    (prefixPartial 11 101789) = some ⟨11, 2, 0, 1395492, 101789, 2829, 262144⟩ := by
  decide +kernel

theorem context_11_101789_1395492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101789 ⟨1395492, by decide⟩ :=
  accepted_of_selected 11 101789 ⟨1395492, by decide⟩ ⟨11, 2, 0, 1395492, 101789, 2829, 262144⟩
    (by decide) selected_cut_49346

theorem selected_cut_49347 : selected 10 ⟨1395534, by decide⟩
    (prefixPartial 11 101790) = some ⟨11, 2, 0, 1395534, 101790, 2465, 262144⟩ := by
  decide +kernel

theorem context_11_101790_1395534 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101790 ⟨1395534, by decide⟩ :=
  accepted_of_selected 11 101790 ⟨1395534, by decide⟩ ⟨11, 2, 0, 1395534, 101790, 2465, 262144⟩
    (by decide) selected_cut_49347

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
