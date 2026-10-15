/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover329
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_31684 : selected 9 ⟨812859, by decide⟩
    (prefixPartial 12 106099) = some ⟨12, 2, 0, 812859, 106099, 3417, 65536⟩ := by
  decide +kernel

theorem context_12_106099_812859 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106099 ⟨812859, by decide⟩ :=
  accepted_of_selected 12 106099 ⟨812859, by decide⟩ ⟨12, 2, 0, 812859, 106099, 3417, 65536⟩
    (by decide) selected_cut_31684

theorem unmarked_context_11_26524_812860 : frontier 10 ⟨812860, by decide⟩
    (prefixCache 11 26524) (prefixPartial 11 26524) = false := by
  decide +kernel

theorem node_context_11_26524_812860 : EJMOriginalGlobalDAGData.nodes 10 ⟨812860, by decide⟩ =
    .split (coordinate 11) (![⟨812728, by decide⟩,⟨812768, by decide⟩,⟨812807, by decide⟩,⟨812859, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26524_812860 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26524 ⟨812860, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26524
    ⟨812860, by decide⟩ (by decide) (![⟨812728, by decide⟩,⟨812768, by decide⟩,⟨812807, by decide⟩,⟨812859, by decide⟩]) unmarked_context_11_26524_812860 node_context_11_26524_812860
  intro a
  fin_cases a
  · exact context_12_106096_812728
  · exact context_12_106097_812768
  · exact context_12_106098_812807
  · exact context_12_106099_812859

theorem selected_cut_31685 : selected 9 ⟨812926, by decide⟩
    (prefixPartial 12 106100) = some ⟨12, 2, 0, 812926, 106100, 3129, 65536⟩ := by
  decide +kernel

theorem context_12_106100_812926 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106100 ⟨812926, by decide⟩ :=
  accepted_of_selected 12 106100 ⟨812926, by decide⟩ ⟨12, 2, 0, 812926, 106100, 3129, 65536⟩
    (by decide) selected_cut_31685

theorem selected_cut_31686 : selected 9 ⟨812966, by decide⟩
    (prefixPartial 12 106101) = some ⟨12, 2, 0, 812966, 106101, 2457, 65536⟩ := by
  decide +kernel

theorem context_12_106101_812966 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106101 ⟨812966, by decide⟩ :=
  accepted_of_selected 12 106101 ⟨812966, by decide⟩ ⟨12, 2, 0, 812966, 106101, 2457, 65536⟩
    (by decide) selected_cut_31686

theorem selected_cut_31687 : selected 9 ⟨813007, by decide⟩
    (prefixPartial 12 106102) = some ⟨12, 2, 0, 813007, 106102, 2453, 65536⟩ := by
  decide +kernel

theorem context_12_106102_813007 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106102 ⟨813007, by decide⟩ :=
  accepted_of_selected 12 106102 ⟨813007, by decide⟩ ⟨12, 2, 0, 813007, 106102, 2453, 65536⟩
    (by decide) selected_cut_31687

theorem selected_cut_31688 : selected 9 ⟨813077, by decide⟩
    (prefixPartial 12 106103) = some ⟨12, 2, 0, 813077, 106103, 3277, 65536⟩ := by
  decide +kernel

theorem context_12_106103_813077 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106103 ⟨813077, by decide⟩ :=
  accepted_of_selected 12 106103 ⟨813077, by decide⟩ ⟨12, 2, 0, 813077, 106103, 3277, 65536⟩
    (by decide) selected_cut_31688

theorem unmarked_context_11_26525_813078 : frontier 10 ⟨813078, by decide⟩
    (prefixCache 11 26525) (prefixPartial 11 26525) = false := by
  decide +kernel

theorem node_context_11_26525_813078 : EJMOriginalGlobalDAGData.nodes 10 ⟨813078, by decide⟩ =
    .split (coordinate 11) (![⟨812926, by decide⟩,⟨812966, by decide⟩,⟨813007, by decide⟩,⟨813077, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26525_813078 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26525 ⟨813078, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26525
    ⟨813078, by decide⟩ (by decide) (![⟨812926, by decide⟩,⟨812966, by decide⟩,⟨813007, by decide⟩,⟨813077, by decide⟩]) unmarked_context_11_26525_813078 node_context_11_26525_813078
  intro a
  fin_cases a
  · exact context_12_106100_812926
  · exact context_12_106101_812966
  · exact context_12_106102_813007
  · exact context_12_106103_813077

theorem selected_cut_31689 : selected 9 ⟨813116, by decide⟩
    (prefixPartial 12 106104) = some ⟨12, 2, 0, 813116, 106104, 2893, 65536⟩ := by
  decide +kernel

theorem context_12_106104_813116 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106104 ⟨813116, by decide⟩ :=
  accepted_of_selected 12 106104 ⟨813116, by decide⟩ ⟨12, 2, 0, 813116, 106104, 2893, 65536⟩
    (by decide) selected_cut_31689

theorem selected_cut_31690 : selected 9 ⟨813149, by decide⟩
    (prefixPartial 12 106105) = some ⟨12, 2, 0, 813149, 106105, 2413, 65536⟩ := by
  decide +kernel

theorem context_12_106105_813149 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106105 ⟨813149, by decide⟩ :=
  accepted_of_selected 12 106105 ⟨813149, by decide⟩ ⟨12, 2, 0, 813149, 106105, 2413, 65536⟩
    (by decide) selected_cut_31690

theorem selected_cut_31691 : selected 9 ⟨662655, by decide⟩
    (prefixPartial 12 106106) = some ⟨12, 1, 0, 662655, 106106, 1, 65536⟩ := by
  decide +kernel

theorem context_12_106106_662655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106106 ⟨662655, by decide⟩ :=
  accepted_of_selected 12 106106 ⟨662655, by decide⟩ ⟨12, 1, 0, 662655, 106106, 1, 65536⟩
    (by decide) selected_cut_31691

theorem selected_cut_31692 : selected 9 ⟨813194, by decide⟩
    (prefixPartial 12 106107) = some ⟨12, 2, 0, 813194, 106107, 2893, 65536⟩ := by
  decide +kernel

theorem context_12_106107_813194 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106107 ⟨813194, by decide⟩ :=
  accepted_of_selected 12 106107 ⟨813194, by decide⟩ ⟨12, 2, 0, 813194, 106107, 2893, 65536⟩
    (by decide) selected_cut_31692

theorem unmarked_context_11_26526_813195 : frontier 10 ⟨813195, by decide⟩
    (prefixCache 11 26526) (prefixPartial 11 26526) = false := by
  decide +kernel

theorem node_context_11_26526_813195 : EJMOriginalGlobalDAGData.nodes 10 ⟨813195, by decide⟩ =
    .split (coordinate 11) (![⟨813116, by decide⟩,⟨813149, by decide⟩,⟨662655, by decide⟩,⟨813194, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26526_813195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26526 ⟨813195, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26526
    ⟨813195, by decide⟩ (by decide) (![⟨813116, by decide⟩,⟨813149, by decide⟩,⟨662655, by decide⟩,⟨813194, by decide⟩]) unmarked_context_11_26526_813195 node_context_11_26526_813195
  intro a
  fin_cases a
  · exact context_12_106104_813116
  · exact context_12_106105_813149
  · exact context_12_106106_662655
  · exact context_12_106107_813194

theorem selected_cut_31693 : selected 9 ⟨813296, by decide⟩
    (prefixPartial 12 106108) = some ⟨12, 2, 0, 813296, 106108, 3757, 65536⟩ := by
  decide +kernel

theorem context_12_106108_813296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106108 ⟨813296, by decide⟩ :=
  accepted_of_selected 12 106108 ⟨813296, by decide⟩ ⟨12, 2, 0, 813296, 106108, 3757, 65536⟩
    (by decide) selected_cut_31693

theorem selected_cut_31694 : selected 9 ⟨813379, by decide⟩
    (prefixPartial 12 106109) = some ⟨12, 2, 0, 813379, 106109, 1033, 65536⟩ := by
  decide +kernel

theorem context_12_106109_813379 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106109 ⟨813379, by decide⟩ :=
  accepted_of_selected 12 106109 ⟨813379, by decide⟩ ⟨12, 2, 0, 813379, 106109, 1033, 65536⟩
    (by decide) selected_cut_31694

theorem selected_cut_31695 : selected 9 ⟨762109, by decide⟩
    (prefixPartial 12 106110) = some ⟨12, 1, 0, 762109, 106110, 1, 65536⟩ := by
  decide +kernel

theorem context_12_106110_762109 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106110 ⟨762109, by decide⟩ :=
  accepted_of_selected 12 106110 ⟨762109, by decide⟩ ⟨12, 1, 0, 762109, 106110, 1, 65536⟩
    (by decide) selected_cut_31695

theorem selected_cut_31696 : selected 9 ⟨795414, by decide⟩
    (prefixPartial 12 106111) = some ⟨12, 1, 0, 795414, 106111, 1, 65536⟩ := by
  decide +kernel

theorem context_12_106111_795414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106111 ⟨795414, by decide⟩ :=
  accepted_of_selected 12 106111 ⟨795414, by decide⟩ ⟨12, 1, 0, 795414, 106111, 1, 65536⟩
    (by decide) selected_cut_31696

theorem unmarked_context_11_26527_813380 : frontier 10 ⟨813380, by decide⟩
    (prefixCache 11 26527) (prefixPartial 11 26527) = false := by
  decide +kernel

theorem node_context_11_26527_813380 : EJMOriginalGlobalDAGData.nodes 10 ⟨813380, by decide⟩ =
    .split (coordinate 11) (![⟨813296, by decide⟩,⟨813379, by decide⟩,⟨762109, by decide⟩,⟨795414, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26527_813380 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26527 ⟨813380, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26527
    ⟨813380, by decide⟩ (by decide) (![⟨813296, by decide⟩,⟨813379, by decide⟩,⟨762109, by decide⟩,⟨795414, by decide⟩]) unmarked_context_11_26527_813380 node_context_11_26527_813380
  intro a
  fin_cases a
  · exact context_12_106108_813296
  · exact context_12_106109_813379
  · exact context_12_106110_762109
  · exact context_12_106111_795414

theorem unmarked_context_10_6631_813381 : frontier 11 ⟨813381, by decide⟩
    (prefixCache 10 6631) (prefixPartial 10 6631) = false := by
  decide +kernel

theorem node_context_10_6631_813381 : EJMOriginalGlobalDAGData.nodes 11 ⟨813381, by decide⟩ =
    .split (coordinate 10) (![⟨812860, by decide⟩,⟨813078, by decide⟩,⟨813195, by decide⟩,⟨813380, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6631_813381 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6631 ⟨813381, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6631
    ⟨813381, by decide⟩ (by decide) (![⟨812860, by decide⟩,⟨813078, by decide⟩,⟨813195, by decide⟩,⟨813380, by decide⟩]) unmarked_context_10_6631_813381 node_context_10_6631_813381
  intro a
  fin_cases a
  · exact context_11_26524_812860
  · exact context_11_26525_813078
  · exact context_11_26526_813195
  · exact context_11_26527_813380

theorem unmarked_context_9_1657_813382 : frontier 12 ⟨813382, by decide⟩
    (prefixCache 9 1657) (prefixPartial 9 1657) = false := by
  decide +kernel

theorem node_context_9_1657_813382 : EJMOriginalGlobalDAGData.nodes 12 ⟨813382, by decide⟩ =
    .split (coordinate 9) (![⟨811015, by decide⟩,⟨811910, by decide⟩,⟨812673, by decide⟩,⟨813381, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1657_813382 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1657 ⟨813382, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1657
    ⟨813382, by decide⟩ (by decide) (![⟨811015, by decide⟩,⟨811910, by decide⟩,⟨812673, by decide⟩,⟨813381, by decide⟩]) unmarked_context_9_1657_813382 node_context_9_1657_813382
  intro a
  fin_cases a
  · exact context_10_6628_811015
  · exact context_10_6629_811910
  · exact context_10_6630_812673
  · exact context_10_6631_813381

theorem selected_cut_31697 : selected 9 ⟨813414, by decide⟩
    (prefixPartial 12 106112) = some ⟨12, 2, 0, 813414, 106112, 2133, 65536⟩ := by
  decide +kernel

theorem context_12_106112_813414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106112 ⟨813414, by decide⟩ :=
  accepted_of_selected 12 106112 ⟨813414, by decide⟩ ⟨12, 2, 0, 813414, 106112, 2133, 65536⟩
    (by decide) selected_cut_31697

theorem selected_cut_31698 : selected 9 ⟨813439, by decide⟩
    (prefixPartial 12 106113) = some ⟨12, 2, 0, 813439, 106113, 2165, 65536⟩ := by
  decide +kernel

theorem context_12_106113_813439 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106113 ⟨813439, by decide⟩ :=
  accepted_of_selected 12 106113 ⟨813439, by decide⟩ ⟨12, 2, 0, 813439, 106113, 2165, 65536⟩
    (by decide) selected_cut_31698

theorem selected_cut_31699 : selected 9 ⟨813440, by decide⟩
    (prefixPartial 12 106114) = some ⟨12, 1, 0, 813440, 106114, 1, 65536⟩ := by
  decide +kernel

theorem context_12_106114_813440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106114 ⟨813440, by decide⟩ :=
  accepted_of_selected 12 106114 ⟨813440, by decide⟩ ⟨12, 1, 0, 813440, 106114, 1, 65536⟩
    (by decide) selected_cut_31699

theorem selected_cut_31700 : selected 9 ⟨813474, by decide⟩
    (prefixPartial 12 106115) = some ⟨12, 2, 0, 813474, 106115, 2301, 65536⟩ := by
  decide +kernel

theorem context_12_106115_813474 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106115 ⟨813474, by decide⟩ :=
  accepted_of_selected 12 106115 ⟨813474, by decide⟩ ⟨12, 2, 0, 813474, 106115, 2301, 65536⟩
    (by decide) selected_cut_31700

theorem unmarked_context_11_26528_813475 : frontier 10 ⟨813475, by decide⟩
    (prefixCache 11 26528) (prefixPartial 11 26528) = false := by
  decide +kernel

theorem node_context_11_26528_813475 : EJMOriginalGlobalDAGData.nodes 10 ⟨813475, by decide⟩ =
    .split (coordinate 11) (![⟨813414, by decide⟩,⟨813439, by decide⟩,⟨813440, by decide⟩,⟨813474, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26528_813475 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26528 ⟨813475, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26528
    ⟨813475, by decide⟩ (by decide) (![⟨813414, by decide⟩,⟨813439, by decide⟩,⟨813440, by decide⟩,⟨813474, by decide⟩]) unmarked_context_11_26528_813475 node_context_11_26528_813475
  intro a
  fin_cases a
  · exact context_12_106112_813414
  · exact context_12_106113_813439
  · exact context_12_106114_813440
  · exact context_12_106115_813474

theorem selected_cut_31701 : selected 9 ⟨813505, by decide⟩
    (prefixPartial 12 106116) = some ⟨12, 2, 0, 813505, 106116, 2201, 65536⟩ := by
  decide +kernel

theorem context_12_106116_813505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106116 ⟨813505, by decide⟩ :=
  accepted_of_selected 12 106116 ⟨813505, by decide⟩ ⟨12, 2, 0, 813505, 106116, 2201, 65536⟩
    (by decide) selected_cut_31701

theorem selected_cut_31702 : selected 9 ⟨813532, by decide⟩
    (prefixPartial 12 106117) = some ⟨12, 2, 0, 813532, 106117, 1913, 65536⟩ := by
  decide +kernel

theorem context_12_106117_813532 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106117 ⟨813532, by decide⟩ :=
  accepted_of_selected 12 106117 ⟨813532, by decide⟩ ⟨12, 2, 0, 813532, 106117, 1913, 65536⟩
    (by decide) selected_cut_31702

theorem selected_cut_31703 : selected 9 ⟨813440, by decide⟩
    (prefixPartial 12 106118) = some ⟨12, 1, 0, 813440, 106118, 1, 65536⟩ := by
  decide +kernel

theorem context_12_106118_813440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106118 ⟨813440, by decide⟩ :=
  accepted_of_selected 12 106118 ⟨813440, by decide⟩ ⟨12, 1, 0, 813440, 106118, 1, 65536⟩
    (by decide) selected_cut_31703

theorem selected_cut_31704 : selected 9 ⟨813555, by decide⟩
    (prefixPartial 12 106119) = some ⟨12, 2, 0, 813555, 106119, 2197, 65536⟩ := by
  decide +kernel

theorem context_12_106119_813555 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106119 ⟨813555, by decide⟩ :=
  accepted_of_selected 12 106119 ⟨813555, by decide⟩ ⟨12, 2, 0, 813555, 106119, 2197, 65536⟩
    (by decide) selected_cut_31704

theorem unmarked_context_11_26529_813556 : frontier 10 ⟨813556, by decide⟩
    (prefixCache 11 26529) (prefixPartial 11 26529) = false := by
  decide +kernel

theorem node_context_11_26529_813556 : EJMOriginalGlobalDAGData.nodes 10 ⟨813556, by decide⟩ =
    .split (coordinate 11) (![⟨813505, by decide⟩,⟨813532, by decide⟩,⟨813440, by decide⟩,⟨813555, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26529_813556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26529 ⟨813556, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26529
    ⟨813556, by decide⟩ (by decide) (![⟨813505, by decide⟩,⟨813532, by decide⟩,⟨813440, by decide⟩,⟨813555, by decide⟩]) unmarked_context_11_26529_813556 node_context_11_26529_813556
  intro a
  fin_cases a
  · exact context_12_106116_813505
  · exact context_12_106117_813532
  · exact context_12_106118_813440
  · exact context_12_106119_813555

theorem selected_cut_31705 : selected 9 ⟨813584, by decide⟩
    (prefixPartial 12 106120) = some ⟨12, 2, 0, 813584, 106120, 1925, 65536⟩ := by
  decide +kernel

theorem context_12_106120_813584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106120 ⟨813584, by decide⟩ :=
  accepted_of_selected 12 106120 ⟨813584, by decide⟩ ⟨12, 2, 0, 813584, 106120, 1925, 65536⟩
    (by decide) selected_cut_31705

theorem selected_cut_31706 : selected 9 ⟨813608, by decide⟩
    (prefixPartial 12 106121) = some ⟨12, 2, 0, 813608, 106121, 1821, 65536⟩ := by
  decide +kernel

theorem context_12_106121_813608 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106121 ⟨813608, by decide⟩ :=
  accepted_of_selected 12 106121 ⟨813608, by decide⟩ ⟨12, 2, 0, 813608, 106121, 1821, 65536⟩
    (by decide) selected_cut_31706

theorem selected_cut_31707 : selected 9 ⟨813440, by decide⟩
    (prefixPartial 12 106122) = some ⟨12, 1, 0, 813440, 106122, 1, 65536⟩ := by
  decide +kernel

theorem context_12_106122_813440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106122 ⟨813440, by decide⟩ :=
  accepted_of_selected 12 106122 ⟨813440, by decide⟩ ⟨12, 1, 0, 813440, 106122, 1, 65536⟩
    (by decide) selected_cut_31707

theorem selected_cut_31708 : selected 9 ⟨813640, by decide⟩
    (prefixPartial 12 106123) = some ⟨12, 2, 0, 813640, 106123, 1989, 65536⟩ := by
  decide +kernel

theorem context_12_106123_813640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106123 ⟨813640, by decide⟩ :=
  accepted_of_selected 12 106123 ⟨813640, by decide⟩ ⟨12, 2, 0, 813640, 106123, 1989, 65536⟩
    (by decide) selected_cut_31708

theorem unmarked_context_11_26530_813641 : frontier 10 ⟨813641, by decide⟩
    (prefixCache 11 26530) (prefixPartial 11 26530) = false := by
  decide +kernel

theorem node_context_11_26530_813641 : EJMOriginalGlobalDAGData.nodes 10 ⟨813641, by decide⟩ =
    .split (coordinate 11) (![⟨813584, by decide⟩,⟨813608, by decide⟩,⟨813440, by decide⟩,⟨813640, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26530_813641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26530 ⟨813641, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26530
    ⟨813641, by decide⟩ (by decide) (![⟨813584, by decide⟩,⟨813608, by decide⟩,⟨813440, by decide⟩,⟨813640, by decide⟩]) unmarked_context_11_26530_813641 node_context_11_26530_813641
  intro a
  fin_cases a
  · exact context_12_106120_813584
  · exact context_12_106121_813608
  · exact context_12_106122_813440
  · exact context_12_106123_813640

theorem selected_cut_31709 : selected 9 ⟨813666, by decide⟩
    (prefixPartial 12 106124) = some ⟨12, 2, 0, 813666, 106124, 2013, 65536⟩ := by
  decide +kernel

theorem context_12_106124_813666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106124 ⟨813666, by decide⟩ :=
  accepted_of_selected 12 106124 ⟨813666, by decide⟩ ⟨12, 2, 0, 813666, 106124, 2013, 65536⟩
    (by decide) selected_cut_31709

theorem selected_cut_31710 : selected 9 ⟨813684, by decide⟩
    (prefixPartial 12 106125) = some ⟨12, 2, 0, 813684, 106125, 1857, 65536⟩ := by
  decide +kernel

theorem context_12_106125_813684 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106125 ⟨813684, by decide⟩ :=
  accepted_of_selected 12 106125 ⟨813684, by decide⟩ ⟨12, 2, 0, 813684, 106125, 1857, 65536⟩
    (by decide) selected_cut_31710

theorem selected_cut_31711 : selected 9 ⟨813440, by decide⟩
    (prefixPartial 12 106126) = some ⟨12, 1, 0, 813440, 106126, 1, 65536⟩ := by
  decide +kernel

theorem context_12_106126_813440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106126 ⟨813440, by decide⟩ :=
  accepted_of_selected 12 106126 ⟨813440, by decide⟩ ⟨12, 1, 0, 813440, 106126, 1, 65536⟩
    (by decide) selected_cut_31711

theorem selected_cut_31712 : selected 9 ⟨813706, by decide⟩
    (prefixPartial 12 106127) = some ⟨12, 2, 0, 813706, 106127, 2109, 65536⟩ := by
  decide +kernel

theorem context_12_106127_813706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106127 ⟨813706, by decide⟩ :=
  accepted_of_selected 12 106127 ⟨813706, by decide⟩ ⟨12, 2, 0, 813706, 106127, 2109, 65536⟩
    (by decide) selected_cut_31712

theorem unmarked_context_11_26531_813707 : frontier 10 ⟨813707, by decide⟩
    (prefixCache 11 26531) (prefixPartial 11 26531) = false := by
  decide +kernel

theorem node_context_11_26531_813707 : EJMOriginalGlobalDAGData.nodes 10 ⟨813707, by decide⟩ =
    .split (coordinate 11) (![⟨813666, by decide⟩,⟨813684, by decide⟩,⟨813440, by decide⟩,⟨813706, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26531_813707 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26531 ⟨813707, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26531
    ⟨813707, by decide⟩ (by decide) (![⟨813666, by decide⟩,⟨813684, by decide⟩,⟨813440, by decide⟩,⟨813706, by decide⟩]) unmarked_context_11_26531_813707 node_context_11_26531_813707
  intro a
  fin_cases a
  · exact context_12_106124_813666
  · exact context_12_106125_813684
  · exact context_12_106126_813440
  · exact context_12_106127_813706

theorem unmarked_context_10_6632_813708 : frontier 11 ⟨813708, by decide⟩
    (prefixCache 10 6632) (prefixPartial 10 6632) = false := by
  decide +kernel

theorem node_context_10_6632_813708 : EJMOriginalGlobalDAGData.nodes 11 ⟨813708, by decide⟩ =
    .split (coordinate 10) (![⟨813475, by decide⟩,⟨813556, by decide⟩,⟨813641, by decide⟩,⟨813707, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6632_813708 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6632 ⟨813708, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6632
    ⟨813708, by decide⟩ (by decide) (![⟨813475, by decide⟩,⟨813556, by decide⟩,⟨813641, by decide⟩,⟨813707, by decide⟩]) unmarked_context_10_6632_813708 node_context_10_6632_813708
  intro a
  fin_cases a
  · exact context_11_26528_813475
  · exact context_11_26529_813556
  · exact context_11_26530_813641
  · exact context_11_26531_813707

theorem selected_cut_31713 : selected 9 ⟨813744, by decide⟩
    (prefixPartial 12 106128) = some ⟨12, 2, 0, 813744, 106128, 2337, 65536⟩ := by
  decide +kernel

theorem context_12_106128_813744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106128 ⟨813744, by decide⟩ :=
  accepted_of_selected 12 106128 ⟨813744, by decide⟩ ⟨12, 2, 0, 813744, 106128, 2337, 65536⟩
    (by decide) selected_cut_31713

theorem selected_cut_31714 : selected 9 ⟨813777, by decide⟩
    (prefixPartial 12 106129) = some ⟨12, 2, 0, 813777, 106129, 2425, 65536⟩ := by
  decide +kernel

theorem context_12_106129_813777 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106129 ⟨813777, by decide⟩ :=
  accepted_of_selected 12 106129 ⟨813777, by decide⟩ ⟨12, 2, 0, 813777, 106129, 2425, 65536⟩
    (by decide) selected_cut_31714

theorem selected_cut_31715 : selected 9 ⟨770014, by decide⟩
    (prefixPartial 12 106130) = some ⟨12, 1, 0, 770014, 106130, 1, 65536⟩ := by
  decide +kernel

theorem context_12_106130_770014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106130 ⟨770014, by decide⟩ :=
  accepted_of_selected 12 106130 ⟨770014, by decide⟩ ⟨12, 1, 0, 770014, 106130, 1, 65536⟩
    (by decide) selected_cut_31715

theorem selected_cut_31716 : selected 9 ⟨813835, by decide⟩
    (prefixPartial 12 106131) = some ⟨12, 2, 0, 813835, 106131, 2593, 65536⟩ := by
  decide +kernel

theorem context_12_106131_813835 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106131 ⟨813835, by decide⟩ :=
  accepted_of_selected 12 106131 ⟨813835, by decide⟩ ⟨12, 2, 0, 813835, 106131, 2593, 65536⟩
    (by decide) selected_cut_31716

theorem unmarked_context_11_26532_813836 : frontier 10 ⟨813836, by decide⟩
    (prefixCache 11 26532) (prefixPartial 11 26532) = false := by
  decide +kernel

theorem node_context_11_26532_813836 : EJMOriginalGlobalDAGData.nodes 10 ⟨813836, by decide⟩ =
    .split (coordinate 11) (![⟨813744, by decide⟩,⟨813777, by decide⟩,⟨770014, by decide⟩,⟨813835, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26532_813836 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26532 ⟨813836, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26532
    ⟨813836, by decide⟩ (by decide) (![⟨813744, by decide⟩,⟨813777, by decide⟩,⟨770014, by decide⟩,⟨813835, by decide⟩]) unmarked_context_11_26532_813836 node_context_11_26532_813836
  intro a
  fin_cases a
  · exact context_12_106128_813744
  · exact context_12_106129_813777
  · exact context_12_106130_770014
  · exact context_12_106131_813835

theorem selected_cut_31717 : selected 9 ⟨813865, by decide⟩
    (prefixPartial 12 106132) = some ⟨12, 2, 0, 813865, 106132, 2093, 65536⟩ := by
  decide +kernel

theorem context_12_106132_813865 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106132 ⟨813865, by decide⟩ :=
  accepted_of_selected 12 106132 ⟨813865, by decide⟩ ⟨12, 2, 0, 813865, 106132, 2093, 65536⟩
    (by decide) selected_cut_31717

theorem selected_cut_31718 : selected 9 ⟨813888, by decide⟩
    (prefixPartial 12 106133) = some ⟨12, 2, 0, 813888, 106133, 1901, 65536⟩ := by
  decide +kernel

theorem context_12_106133_813888 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106133 ⟨813888, by decide⟩ :=
  accepted_of_selected 12 106133 ⟨813888, by decide⟩ ⟨12, 2, 0, 813888, 106133, 1901, 65536⟩
    (by decide) selected_cut_31718

theorem selected_cut_31719 : selected 9 ⟨813889, by decide⟩
    (prefixPartial 12 106134) = some ⟨12, 1, 0, 813889, 106134, 1, 65536⟩ := by
  decide +kernel

theorem context_12_106134_813889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106134 ⟨813889, by decide⟩ :=
  accepted_of_selected 12 106134 ⟨813889, by decide⟩ ⟨12, 1, 0, 813889, 106134, 1, 65536⟩
    (by decide) selected_cut_31719

theorem selected_cut_31720 : selected 9 ⟨813923, by decide⟩
    (prefixPartial 12 106135) = some ⟨12, 2, 0, 813923, 106135, 2173, 65536⟩ := by
  decide +kernel

theorem context_12_106135_813923 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106135 ⟨813923, by decide⟩ :=
  accepted_of_selected 12 106135 ⟨813923, by decide⟩ ⟨12, 2, 0, 813923, 106135, 2173, 65536⟩
    (by decide) selected_cut_31720

theorem unmarked_context_11_26533_813924 : frontier 10 ⟨813924, by decide⟩
    (prefixCache 11 26533) (prefixPartial 11 26533) = false := by
  decide +kernel

theorem node_context_11_26533_813924 : EJMOriginalGlobalDAGData.nodes 10 ⟨813924, by decide⟩ =
    .split (coordinate 11) (![⟨813865, by decide⟩,⟨813888, by decide⟩,⟨813889, by decide⟩,⟨813923, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26533_813924 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26533 ⟨813924, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26533
    ⟨813924, by decide⟩ (by decide) (![⟨813865, by decide⟩,⟨813888, by decide⟩,⟨813889, by decide⟩,⟨813923, by decide⟩]) unmarked_context_11_26533_813924 node_context_11_26533_813924
  intro a
  fin_cases a
  · exact context_12_106132_813865
  · exact context_12_106133_813888
  · exact context_12_106134_813889
  · exact context_12_106135_813923

theorem selected_cut_31721 : selected 9 ⟨813957, by decide⟩
    (prefixPartial 12 106136) = some ⟨12, 2, 0, 813957, 106136, 1849, 65536⟩ := by
  decide +kernel

theorem context_12_106136_813957 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106136 ⟨813957, by decide⟩ :=
  accepted_of_selected 12 106136 ⟨813957, by decide⟩ ⟨12, 2, 0, 813957, 106136, 1849, 65536⟩
    (by decide) selected_cut_31721

theorem selected_cut_31722 : selected 9 ⟨813978, by decide⟩
    (prefixPartial 12 106137) = some ⟨12, 2, 0, 813978, 106137, 1857, 65536⟩ := by
  decide +kernel

theorem context_12_106137_813978 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106137 ⟨813978, by decide⟩ :=
  accepted_of_selected 12 106137 ⟨813978, by decide⟩ ⟨12, 2, 0, 813978, 106137, 1857, 65536⟩
    (by decide) selected_cut_31722

theorem selected_cut_31723 : selected 9 ⟨813979, by decide⟩
    (prefixPartial 12 106138) = some ⟨12, 1, 0, 813979, 106138, 1, 65536⟩ := by
  decide +kernel

theorem context_12_106138_813979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106138 ⟨813979, by decide⟩ :=
  accepted_of_selected 12 106138 ⟨813979, by decide⟩ ⟨12, 1, 0, 813979, 106138, 1, 65536⟩
    (by decide) selected_cut_31723

theorem selected_cut_31724 : selected 9 ⟨814004, by decide⟩
    (prefixPartial 12 106139) = some ⟨12, 2, 0, 814004, 106139, 1933, 65536⟩ := by
  decide +kernel

theorem context_12_106139_814004 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106139 ⟨814004, by decide⟩ :=
  accepted_of_selected 12 106139 ⟨814004, by decide⟩ ⟨12, 2, 0, 814004, 106139, 1933, 65536⟩
    (by decide) selected_cut_31724

theorem unmarked_context_11_26534_814005 : frontier 10 ⟨814005, by decide⟩
    (prefixCache 11 26534) (prefixPartial 11 26534) = false := by
  decide +kernel

theorem node_context_11_26534_814005 : EJMOriginalGlobalDAGData.nodes 10 ⟨814005, by decide⟩ =
    .split (coordinate 11) (![⟨813957, by decide⟩,⟨813978, by decide⟩,⟨813979, by decide⟩,⟨814004, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26534_814005 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26534 ⟨814005, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26534
    ⟨814005, by decide⟩ (by decide) (![⟨813957, by decide⟩,⟨813978, by decide⟩,⟨813979, by decide⟩,⟨814004, by decide⟩]) unmarked_context_11_26534_814005 node_context_11_26534_814005
  intro a
  fin_cases a
  · exact context_12_106136_813957
  · exact context_12_106137_813978
  · exact context_12_106138_813979
  · exact context_12_106139_814004

theorem selected_cut_31725 : selected 9 ⟨814033, by decide⟩
    (prefixPartial 12 106140) = some ⟨12, 2, 0, 814033, 106140, 1821, 65536⟩ := by
  decide +kernel

theorem context_12_106140_814033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106140 ⟨814033, by decide⟩ :=
  accepted_of_selected 12 106140 ⟨814033, by decide⟩ ⟨12, 2, 0, 814033, 106140, 1821, 65536⟩
    (by decide) selected_cut_31725

theorem selected_cut_31726 : selected 9 ⟨814047, by decide⟩
    (prefixPartial 12 106141) = some ⟨12, 2, 0, 814047, 106141, 1777, 65536⟩ := by
  decide +kernel

theorem context_12_106141_814047 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106141 ⟨814047, by decide⟩ :=
  accepted_of_selected 12 106141 ⟨814047, by decide⟩ ⟨12, 2, 0, 814047, 106141, 1777, 65536⟩
    (by decide) selected_cut_31726

theorem selected_cut_31727 : selected 9 ⟨814048, by decide⟩
    (prefixPartial 12 106142) = some ⟨12, 1, 0, 814048, 106142, 1, 65536⟩ := by
  decide +kernel

theorem context_12_106142_814048 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106142 ⟨814048, by decide⟩ :=
  accepted_of_selected 12 106142 ⟨814048, by decide⟩ ⟨12, 1, 0, 814048, 106142, 1, 65536⟩
    (by decide) selected_cut_31727

theorem selected_cut_31728 : selected 9 ⟨814073, by decide⟩
    (prefixPartial 12 106143) = some ⟨12, 2, 0, 814073, 106143, 1925, 65536⟩ := by
  decide +kernel

theorem context_12_106143_814073 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106143 ⟨814073, by decide⟩ :=
  accepted_of_selected 12 106143 ⟨814073, by decide⟩ ⟨12, 2, 0, 814073, 106143, 1925, 65536⟩
    (by decide) selected_cut_31728

theorem unmarked_context_11_26535_814074 : frontier 10 ⟨814074, by decide⟩
    (prefixCache 11 26535) (prefixPartial 11 26535) = false := by
  decide +kernel

theorem node_context_11_26535_814074 : EJMOriginalGlobalDAGData.nodes 10 ⟨814074, by decide⟩ =
    .split (coordinate 11) (![⟨814033, by decide⟩,⟨814047, by decide⟩,⟨814048, by decide⟩,⟨814073, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26535_814074 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26535 ⟨814074, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26535
    ⟨814074, by decide⟩ (by decide) (![⟨814033, by decide⟩,⟨814047, by decide⟩,⟨814048, by decide⟩,⟨814073, by decide⟩]) unmarked_context_11_26535_814074 node_context_11_26535_814074
  intro a
  fin_cases a
  · exact context_12_106140_814033
  · exact context_12_106141_814047
  · exact context_12_106142_814048
  · exact context_12_106143_814073

theorem unmarked_context_10_6633_814075 : frontier 11 ⟨814075, by decide⟩
    (prefixCache 10 6633) (prefixPartial 10 6633) = false := by
  decide +kernel

theorem node_context_10_6633_814075 : EJMOriginalGlobalDAGData.nodes 11 ⟨814075, by decide⟩ =
    .split (coordinate 10) (![⟨813836, by decide⟩,⟨813924, by decide⟩,⟨814005, by decide⟩,⟨814074, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6633_814075 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6633 ⟨814075, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6633
    ⟨814075, by decide⟩ (by decide) (![⟨813836, by decide⟩,⟨813924, by decide⟩,⟨814005, by decide⟩,⟨814074, by decide⟩]) unmarked_context_10_6633_814075 node_context_10_6633_814075
  intro a
  fin_cases a
  · exact context_11_26532_813836
  · exact context_11_26533_813924
  · exact context_11_26534_814005
  · exact context_11_26535_814074

theorem selected_cut_31729 : selected 9 ⟨814094, by decide⟩
    (prefixPartial 12 106144) = some ⟨12, 2, 0, 814094, 106144, 1501, 65536⟩ := by
  decide +kernel

theorem context_12_106144_814094 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106144 ⟨814094, by decide⟩ :=
  accepted_of_selected 12 106144 ⟨814094, by decide⟩ ⟨12, 2, 0, 814094, 106144, 1501, 65536⟩
    (by decide) selected_cut_31729

theorem selected_cut_31730 : selected 9 ⟨814108, by decide⟩
    (prefixPartial 12 106145) = some ⟨12, 2, 0, 814108, 106145, 1585, 65536⟩ := by
  decide +kernel

theorem context_12_106145_814108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106145 ⟨814108, by decide⟩ :=
  accepted_of_selected 12 106145 ⟨814108, by decide⟩ ⟨12, 2, 0, 814108, 106145, 1585, 65536⟩
    (by decide) selected_cut_31730

theorem selected_cut_31731 : selected 9 ⟨769937, by decide⟩
    (prefixPartial 12 106146) = some ⟨12, 1, 0, 769937, 106146, 1, 65536⟩ := by
  decide +kernel

theorem context_12_106146_769937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106146 ⟨769937, by decide⟩ :=
  accepted_of_selected 12 106146 ⟨769937, by decide⟩ ⟨12, 1, 0, 769937, 106146, 1, 65536⟩
    (by decide) selected_cut_31731

theorem selected_cut_31732 : selected 9 ⟨814129, by decide⟩
    (prefixPartial 12 106147) = some ⟨12, 2, 0, 814129, 106147, 1693, 65536⟩ := by
  decide +kernel

theorem context_12_106147_814129 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106147 ⟨814129, by decide⟩ :=
  accepted_of_selected 12 106147 ⟨814129, by decide⟩ ⟨12, 2, 0, 814129, 106147, 1693, 65536⟩
    (by decide) selected_cut_31732

theorem unmarked_context_11_26536_814130 : frontier 10 ⟨814130, by decide⟩
    (prefixCache 11 26536) (prefixPartial 11 26536) = false := by
  decide +kernel

theorem node_context_11_26536_814130 : EJMOriginalGlobalDAGData.nodes 10 ⟨814130, by decide⟩ =
    .split (coordinate 11) (![⟨814094, by decide⟩,⟨814108, by decide⟩,⟨769937, by decide⟩,⟨814129, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26536_814130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26536 ⟨814130, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26536
    ⟨814130, by decide⟩ (by decide) (![⟨814094, by decide⟩,⟨814108, by decide⟩,⟨769937, by decide⟩,⟨814129, by decide⟩]) unmarked_context_11_26536_814130 node_context_11_26536_814130
  intro a
  fin_cases a
  · exact context_12_106144_814094
  · exact context_12_106145_814108
  · exact context_12_106146_769937
  · exact context_12_106147_814129

theorem selected_cut_31733 : selected 9 ⟨814151, by decide⟩
    (prefixPartial 12 106148) = some ⟨12, 2, 0, 814151, 106148, 1433, 65536⟩ := by
  decide +kernel

theorem context_12_106148_814151 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106148 ⟨814151, by decide⟩ :=
  accepted_of_selected 12 106148 ⟨814151, by decide⟩ ⟨12, 2, 0, 814151, 106148, 1433, 65536⟩
    (by decide) selected_cut_31733

theorem selected_cut_31734 : selected 9 ⟨814172, by decide⟩
    (prefixPartial 12 106149) = some ⟨12, 2, 0, 814172, 106149, 1229, 65536⟩ := by
  decide +kernel

theorem context_12_106149_814172 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106149 ⟨814172, by decide⟩ :=
  accepted_of_selected 12 106149 ⟨814172, by decide⟩ ⟨12, 2, 0, 814172, 106149, 1229, 65536⟩
    (by decide) selected_cut_31734

theorem selected_cut_31735 : selected 9 ⟨769937, by decide⟩
    (prefixPartial 12 106150) = some ⟨12, 1, 0, 769937, 106150, 1, 65536⟩ := by
  decide +kernel

theorem context_12_106150_769937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106150 ⟨769937, by decide⟩ :=
  accepted_of_selected 12 106150 ⟨769937, by decide⟩ ⟨12, 1, 0, 769937, 106150, 1, 65536⟩
    (by decide) selected_cut_31735

theorem selected_cut_31736 : selected 9 ⟨814192, by decide⟩
    (prefixPartial 12 106151) = some ⟨12, 2, 0, 814192, 106151, 1541, 65536⟩ := by
  decide +kernel

theorem context_12_106151_814192 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106151 ⟨814192, by decide⟩ :=
  accepted_of_selected 12 106151 ⟨814192, by decide⟩ ⟨12, 2, 0, 814192, 106151, 1541, 65536⟩
    (by decide) selected_cut_31736

theorem unmarked_context_11_26537_814193 : frontier 10 ⟨814193, by decide⟩
    (prefixCache 11 26537) (prefixPartial 11 26537) = false := by
  decide +kernel

theorem node_context_11_26537_814193 : EJMOriginalGlobalDAGData.nodes 10 ⟨814193, by decide⟩ =
    .split (coordinate 11) (![⟨814151, by decide⟩,⟨814172, by decide⟩,⟨769937, by decide⟩,⟨814192, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26537_814193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26537 ⟨814193, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26537
    ⟨814193, by decide⟩ (by decide) (![⟨814151, by decide⟩,⟨814172, by decide⟩,⟨769937, by decide⟩,⟨814192, by decide⟩]) unmarked_context_11_26537_814193 node_context_11_26537_814193
  intro a
  fin_cases a
  · exact context_12_106148_814151
  · exact context_12_106149_814172
  · exact context_12_106150_769937
  · exact context_12_106151_814192

theorem selected_cut_31737 : selected 10 ⟨814242, by decide⟩
    (prefixPartial 11 26538) = some ⟨11, 2, 0, 814242, 26538, 3917, 262144⟩ := by
  decide +kernel

theorem context_11_26538_814242 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26538 ⟨814242, by decide⟩ :=
  accepted_of_selected 11 26538 ⟨814242, by decide⟩ ⟨11, 2, 0, 814242, 26538, 3917, 262144⟩
    (by decide) selected_cut_31737

theorem selected_cut_31738 : selected 10 ⟨814287, by decide⟩
    (prefixPartial 11 26539) = some ⟨11, 2, 0, 814287, 26539, 4001, 262144⟩ := by
  decide +kernel

theorem context_11_26539_814287 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26539 ⟨814287, by decide⟩ :=
  accepted_of_selected 11 26539 ⟨814287, by decide⟩ ⟨11, 2, 0, 814287, 26539, 4001, 262144⟩
    (by decide) selected_cut_31738

theorem unmarked_context_10_6634_814288 : frontier 11 ⟨814288, by decide⟩
    (prefixCache 10 6634) (prefixPartial 10 6634) = false := by
  decide +kernel

theorem node_context_10_6634_814288 : EJMOriginalGlobalDAGData.nodes 11 ⟨814288, by decide⟩ =
    .split (coordinate 10) (![⟨814130, by decide⟩,⟨814193, by decide⟩,⟨814242, by decide⟩,⟨814287, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6634_814288 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6634 ⟨814288, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6634
    ⟨814288, by decide⟩ (by decide) (![⟨814130, by decide⟩,⟨814193, by decide⟩,⟨814242, by decide⟩,⟨814287, by decide⟩]) unmarked_context_10_6634_814288 node_context_10_6634_814288
  intro a
  fin_cases a
  · exact context_11_26536_814130
  · exact context_11_26537_814193
  · exact context_11_26538_814242
  · exact context_11_26539_814287

theorem selected_cut_31739 : selected 10 ⟨814333, by decide⟩
    (prefixPartial 11 26540) = some ⟨11, 2, 0, 814333, 26540, 3937, 262144⟩ := by
  decide +kernel

theorem context_11_26540_814333 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26540 ⟨814333, by decide⟩ :=
  accepted_of_selected 11 26540 ⟨814333, by decide⟩ ⟨11, 2, 0, 814333, 26540, 3937, 262144⟩
    (by decide) selected_cut_31739

theorem selected_cut_31740 : selected 10 ⟨814371, by decide⟩
    (prefixPartial 11 26541) = some ⟨11, 2, 0, 814371, 26541, 2929, 262144⟩ := by
  decide +kernel

theorem context_11_26541_814371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26541 ⟨814371, by decide⟩ :=
  accepted_of_selected 11 26541 ⟨814371, by decide⟩ ⟨11, 2, 0, 814371, 26541, 2929, 262144⟩
    (by decide) selected_cut_31740

theorem selected_cut_31741 : selected 10 ⟨814408, by decide⟩
    (prefixPartial 11 26542) = some ⟨11, 2, 0, 814408, 26542, 2857, 262144⟩ := by
  decide +kernel

theorem context_11_26542_814408 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26542 ⟨814408, by decide⟩ :=
  accepted_of_selected 11 26542 ⟨814408, by decide⟩ ⟨11, 2, 0, 814408, 26542, 2857, 262144⟩
    (by decide) selected_cut_31741

theorem selected_cut_31742 : selected 10 ⟨814436, by decide⟩
    (prefixPartial 11 26543) = some ⟨11, 2, 0, 814436, 26543, 2357, 262144⟩ := by
  decide +kernel

theorem context_11_26543_814436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26543 ⟨814436, by decide⟩ :=
  accepted_of_selected 11 26543 ⟨814436, by decide⟩ ⟨11, 2, 0, 814436, 26543, 2357, 262144⟩
    (by decide) selected_cut_31742

theorem unmarked_context_10_6635_814437 : frontier 11 ⟨814437, by decide⟩
    (prefixCache 10 6635) (prefixPartial 10 6635) = false := by
  decide +kernel

theorem node_context_10_6635_814437 : EJMOriginalGlobalDAGData.nodes 11 ⟨814437, by decide⟩ =
    .split (coordinate 10) (![⟨814333, by decide⟩,⟨814371, by decide⟩,⟨814408, by decide⟩,⟨814436, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6635_814437 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6635 ⟨814437, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6635
    ⟨814437, by decide⟩ (by decide) (![⟨814333, by decide⟩,⟨814371, by decide⟩,⟨814408, by decide⟩,⟨814436, by decide⟩]) unmarked_context_10_6635_814437 node_context_10_6635_814437
  intro a
  fin_cases a
  · exact context_11_26540_814333
  · exact context_11_26541_814371
  · exact context_11_26542_814408
  · exact context_11_26543_814436

theorem unmarked_context_9_1658_814438 : frontier 12 ⟨814438, by decide⟩
    (prefixCache 9 1658) (prefixPartial 9 1658) = false := by
  decide +kernel

theorem node_context_9_1658_814438 : EJMOriginalGlobalDAGData.nodes 12 ⟨814438, by decide⟩ =
    .split (coordinate 9) (![⟨813708, by decide⟩,⟨814075, by decide⟩,⟨814288, by decide⟩,⟨814437, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1658_814438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1658 ⟨814438, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1658
    ⟨814438, by decide⟩ (by decide) (![⟨813708, by decide⟩,⟨814075, by decide⟩,⟨814288, by decide⟩,⟨814437, by decide⟩]) unmarked_context_9_1658_814438 node_context_9_1658_814438
  intro a
  fin_cases a
  · exact context_10_6632_813708
  · exact context_10_6633_814075
  · exact context_10_6634_814288
  · exact context_10_6635_814437

theorem selected_cut_31743 : selected 10 ⟨814480, by decide⟩
    (prefixPartial 11 26544) = some ⟨11, 2, 0, 814480, 26544, 3805, 262144⟩ := by
  decide +kernel

theorem context_11_26544_814480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26544 ⟨814480, by decide⟩ :=
  accepted_of_selected 11 26544 ⟨814480, by decide⟩ ⟨11, 2, 0, 814480, 26544, 3805, 262144⟩
    (by decide) selected_cut_31743

theorem selected_cut_31744 : selected 10 ⟨814526, by decide⟩
    (prefixPartial 11 26545) = some ⟨11, 2, 0, 814526, 26545, 3561, 262144⟩ := by
  decide +kernel

theorem context_11_26545_814526 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26545 ⟨814526, by decide⟩ :=
  accepted_of_selected 11 26545 ⟨814526, by decide⟩ ⟨11, 2, 0, 814526, 26545, 3561, 262144⟩
    (by decide) selected_cut_31744

theorem selected_cut_31745 : selected 10 ⟨814548, by decide⟩
    (prefixPartial 11 26546) = some ⟨11, 2, 0, 814548, 26546, 2277, 262144⟩ := by
  decide +kernel

theorem context_11_26546_814548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26546 ⟨814548, by decide⟩ :=
  accepted_of_selected 11 26546 ⟨814548, by decide⟩ ⟨11, 2, 0, 814548, 26546, 2277, 262144⟩
    (by decide) selected_cut_31745

theorem selected_cut_31746 : selected 10 ⟨814573, by decide⟩
    (prefixPartial 11 26547) = some ⟨11, 2, 0, 814573, 26547, 3097, 262144⟩ := by
  decide +kernel

theorem context_11_26547_814573 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26547 ⟨814573, by decide⟩ :=
  accepted_of_selected 11 26547 ⟨814573, by decide⟩ ⟨11, 2, 0, 814573, 26547, 3097, 262144⟩
    (by decide) selected_cut_31746

theorem unmarked_context_10_6636_814574 : frontier 11 ⟨814574, by decide⟩
    (prefixCache 10 6636) (prefixPartial 10 6636) = false := by
  decide +kernel

theorem node_context_10_6636_814574 : EJMOriginalGlobalDAGData.nodes 11 ⟨814574, by decide⟩ =
    .split (coordinate 10) (![⟨814480, by decide⟩,⟨814526, by decide⟩,⟨814548, by decide⟩,⟨814573, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6636_814574 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6636 ⟨814574, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6636
    ⟨814574, by decide⟩ (by decide) (![⟨814480, by decide⟩,⟨814526, by decide⟩,⟨814548, by decide⟩,⟨814573, by decide⟩]) unmarked_context_10_6636_814574 node_context_10_6636_814574
  intro a
  fin_cases a
  · exact context_11_26544_814480
  · exact context_11_26545_814526
  · exact context_11_26546_814548
  · exact context_11_26547_814573

theorem selected_cut_31747 : selected 10 ⟨814605, by decide⟩
    (prefixPartial 11 26548) = some ⟨11, 2, 0, 814605, 26548, 2909, 262144⟩ := by
  decide +kernel

theorem context_11_26548_814605 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26548 ⟨814605, by decide⟩ :=
  accepted_of_selected 11 26548 ⟨814605, by decide⟩ ⟨11, 2, 0, 814605, 26548, 2909, 262144⟩
    (by decide) selected_cut_31747

theorem selected_cut_31748 : selected 10 ⟨814626, by decide⟩
    (prefixPartial 11 26549) = some ⟨11, 2, 0, 814626, 26549, 2261, 262144⟩ := by
  decide +kernel

theorem context_11_26549_814626 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26549 ⟨814626, by decide⟩ :=
  accepted_of_selected 11 26549 ⟨814626, by decide⟩ ⟨11, 2, 0, 814626, 26549, 2261, 262144⟩
    (by decide) selected_cut_31748

theorem selected_cut_31749 : selected 10 ⟨814643, by decide⟩
    (prefixPartial 11 26550) = some ⟨11, 2, 0, 814643, 26550, 1537, 262144⟩ := by
  decide +kernel

theorem context_11_26550_814643 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26550 ⟨814643, by decide⟩ :=
  accepted_of_selected 11 26550 ⟨814643, by decide⟩ ⟨11, 2, 0, 814643, 26550, 1537, 262144⟩
    (by decide) selected_cut_31749

theorem selected_cut_31750 : selected 10 ⟨814661, by decide⟩
    (prefixPartial 11 26551) = some ⟨11, 2, 0, 814661, 26551, 1877, 262144⟩ := by
  decide +kernel

theorem context_11_26551_814661 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26551 ⟨814661, by decide⟩ :=
  accepted_of_selected 11 26551 ⟨814661, by decide⟩ ⟨11, 2, 0, 814661, 26551, 1877, 262144⟩
    (by decide) selected_cut_31750

theorem unmarked_context_10_6637_814662 : frontier 11 ⟨814662, by decide⟩
    (prefixCache 10 6637) (prefixPartial 10 6637) = false := by
  decide +kernel

theorem node_context_10_6637_814662 : EJMOriginalGlobalDAGData.nodes 11 ⟨814662, by decide⟩ =
    .split (coordinate 10) (![⟨814605, by decide⟩,⟨814626, by decide⟩,⟨814643, by decide⟩,⟨814661, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6637_814662 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6637 ⟨814662, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6637
    ⟨814662, by decide⟩ (by decide) (![⟨814605, by decide⟩,⟨814626, by decide⟩,⟨814643, by decide⟩,⟨814661, by decide⟩]) unmarked_context_10_6637_814662 node_context_10_6637_814662
  intro a
  fin_cases a
  · exact context_11_26548_814605
  · exact context_11_26549_814626
  · exact context_11_26550_814643
  · exact context_11_26551_814661

theorem selected_cut_31751 : selected 11 ⟨814715, by decide⟩
    (prefixPartial 10 6638) = some ⟨10, 2, 0, 814715, 6638, 3901, 1048576⟩ := by
  decide +kernel

theorem context_10_6638_814715 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6638 ⟨814715, by decide⟩ :=
  accepted_of_selected 10 6638 ⟨814715, by decide⟩ ⟨10, 2, 0, 814715, 6638, 3901, 1048576⟩
    (by decide) selected_cut_31751

theorem selected_cut_31752 : selected 11 ⟨814754, by decide⟩
    (prefixPartial 10 6639) = some ⟨10, 2, 0, 814754, 6639, 997, 1048576⟩ := by
  decide +kernel

theorem context_10_6639_814754 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6639 ⟨814754, by decide⟩ :=
  accepted_of_selected 10 6639 ⟨814754, by decide⟩ ⟨10, 2, 0, 814754, 6639, 997, 1048576⟩
    (by decide) selected_cut_31752

theorem unmarked_context_9_1659_814755 : frontier 12 ⟨814755, by decide⟩
    (prefixCache 9 1659) (prefixPartial 9 1659) = false := by
  decide +kernel

theorem node_context_9_1659_814755 : EJMOriginalGlobalDAGData.nodes 12 ⟨814755, by decide⟩ =
    .split (coordinate 9) (![⟨814574, by decide⟩,⟨814662, by decide⟩,⟨814715, by decide⟩,⟨814754, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1659_814755 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1659 ⟨814755, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1659
    ⟨814755, by decide⟩ (by decide) (![⟨814574, by decide⟩,⟨814662, by decide⟩,⟨814715, by decide⟩,⟨814754, by decide⟩]) unmarked_context_9_1659_814755 node_context_9_1659_814755
  intro a
  fin_cases a
  · exact context_10_6636_814574
  · exact context_10_6637_814662
  · exact context_10_6638_814715
  · exact context_10_6639_814754

theorem unmarked_context_8_414_814756 : frontier 13 ⟨814756, by decide⟩
    (prefixCache 8 414) (prefixPartial 8 414) = false := by
  decide +kernel

theorem node_context_8_414_814756 : EJMOriginalGlobalDAGData.nodes 13 ⟨814756, by decide⟩ =
    .split (coordinate 8) (![⟨809887, by decide⟩,⟨813382, by decide⟩,⟨814438, by decide⟩,⟨814755, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_414_814756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 414 ⟨814756, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 414
    ⟨814756, by decide⟩ (by decide) (![⟨809887, by decide⟩,⟨813382, by decide⟩,⟨814438, by decide⟩,⟨814755, by decide⟩]) unmarked_context_8_414_814756 node_context_8_414_814756
  intro a
  fin_cases a
  · exact context_9_1656_809887
  · exact context_9_1657_813382
  · exact context_9_1658_814438
  · exact context_9_1659_814755

theorem selected_cut_31753 : selected 13 ⟨814757, by decide⟩
    (prefixPartial 8 415) = some ⟨8, 1, 0, 814757, 415, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_415_814757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 415 ⟨814757, by decide⟩ :=
  accepted_of_selected 8 415 ⟨814757, by decide⟩ ⟨8, 1, 0, 814757, 415, 1, 16777216⟩
    (by decide) selected_cut_31753

theorem unmarked_context_7_103_814758 : frontier 14 ⟨814758, by decide⟩
    (prefixCache 7 103) (prefixPartial 7 103) = false := by
  decide +kernel

theorem node_context_7_103_814758 : EJMOriginalGlobalDAGData.nodes 14 ⟨814758, by decide⟩ =
    .split (coordinate 7) (![⟨795816, by decide⟩,⟨804631, by decide⟩,⟨814756, by decide⟩,⟨814757, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_103_814758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 103 ⟨814758, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 103
    ⟨814758, by decide⟩ (by decide) (![⟨795816, by decide⟩,⟨804631, by decide⟩,⟨814756, by decide⟩,⟨814757, by decide⟩]) unmarked_context_7_103_814758 node_context_7_103_814758
  intro a
  fin_cases a
  · exact context_8_412_795816
  · exact context_8_413_804631
  · exact context_8_414_814756
  · exact context_8_415_814757

theorem unmarked_context_6_25_814759 : frontier 15 ⟨814759, by decide⟩
    (prefixCache 6 25) (prefixPartial 6 25) = false := by
  decide +kernel

theorem node_context_6_25_814759 : EJMOriginalGlobalDAGData.nodes 15 ⟨814759, by decide⟩ =
    .split (coordinate 6) (![⟨116316, by decide⟩,⟨116316, by decide⟩,⟨788404, by decide⟩,⟨814758, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_6_25_814759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 25 ⟨814759, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 6 25
    ⟨814759, by decide⟩ (by decide) (![⟨116316, by decide⟩,⟨116316, by decide⟩,⟨788404, by decide⟩,⟨814758, by decide⟩]) unmarked_context_6_25_814759 node_context_6_25_814759
  intro a
  fin_cases a
  · exact context_7_100_116316
  · exact context_7_101_116316
  · exact context_7_102_788404
  · exact context_7_103_814758

theorem selected_cut_31754 : selected 14 ⟨676732, by decide⟩
    (prefixPartial 7 104) = some ⟨7, 1, 0, 676732, 104, 1, 67108864⟩ := by
  decide +kernel

theorem context_7_104_676732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 104 ⟨676732, by decide⟩ :=
  accepted_of_selected 7 104 ⟨676732, by decide⟩ ⟨7, 1, 0, 676732, 104, 1, 67108864⟩
    (by decide) selected_cut_31754

theorem selected_cut_31755 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 26880) = some ⟨11, 1, 0, 434745, 26880, 1, 262144⟩ := by
  decide +kernel

theorem context_11_26880_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26880 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 26880 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 26880, 1, 262144⟩
    (by decide) selected_cut_31755

theorem selected_cut_31756 : selected 10 ⟨167448, by decide⟩
    (prefixPartial 11 26881) = some ⟨11, 1, 0, 167448, 26881, 1, 262144⟩ := by
  decide +kernel

theorem context_11_26881_167448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26881 ⟨167448, by decide⟩ :=
  accepted_of_selected 11 26881 ⟨167448, by decide⟩ ⟨11, 1, 0, 167448, 26881, 1, 262144⟩
    (by decide) selected_cut_31756

theorem selected_cut_31757 : selected 9 ⟨4595, by decide⟩
    (prefixPartial 12 107528) = some ⟨12, 1, 0, 4595, 107528, 1, 65536⟩ := by
  decide +kernel

theorem context_12_107528_4595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107528 ⟨4595, by decide⟩ :=
  accepted_of_selected 12 107528 ⟨4595, by decide⟩ ⟨12, 1, 0, 4595, 107528, 1, 65536⟩
    (by decide) selected_cut_31757

theorem selected_cut_31758 : selected 8 ⟨814903, by decide⟩
    (prefixPartial 13 430116) = some ⟨13, 2, 0, 814903, 430116, 3581, 16384⟩ := by
  decide +kernel

theorem context_13_430116_814903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430116 ⟨814903, by decide⟩ :=
  accepted_of_selected 13 430116 ⟨814903, by decide⟩ ⟨13, 2, 0, 814903, 430116, 3581, 16384⟩
    (by decide) selected_cut_31758

theorem selected_cut_31759 : selected 8 ⟨814968, by decide⟩
    (prefixPartial 13 430117) = some ⟨13, 2, 0, 814968, 430117, 1817, 16384⟩ := by
  decide +kernel

theorem context_13_430117_814968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430117 ⟨814968, by decide⟩ :=
  accepted_of_selected 13 430117 ⟨814968, by decide⟩ ⟨13, 2, 0, 814968, 430117, 1817, 16384⟩
    (by decide) selected_cut_31759

theorem selected_cut_31760 : selected 8 ⟨814989, by decide⟩
    (prefixPartial 13 430118) = some ⟨13, 2, 0, 814989, 430118, 537, 16384⟩ := by
  decide +kernel

theorem context_13_430118_814989 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430118 ⟨814989, by decide⟩ :=
  accepted_of_selected 13 430118 ⟨814989, by decide⟩ ⟨13, 2, 0, 814989, 430118, 537, 16384⟩
    (by decide) selected_cut_31760

theorem selected_cut_31761 : selected 8 ⟨814991, by decide⟩
    (prefixPartial 13 430119) = some ⟨13, 2, 0, 814991, 430119, 101, 16384⟩ := by
  decide +kernel

theorem context_13_430119_814991 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430119 ⟨814991, by decide⟩ :=
  accepted_of_selected 13 430119 ⟨814991, by decide⟩ ⟨13, 2, 0, 814991, 430119, 101, 16384⟩
    (by decide) selected_cut_31761

theorem unmarked_context_12_107529_814992 : frontier 9 ⟨814992, by decide⟩
    (prefixCache 12 107529) (prefixPartial 12 107529) = false := by
  decide +kernel

theorem node_context_12_107529_814992 : EJMOriginalGlobalDAGData.nodes 9 ⟨814992, by decide⟩ =
    .split (coordinate 12) (![⟨814903, by decide⟩,⟨814968, by decide⟩,⟨814989, by decide⟩,⟨814991, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107529_814992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107529 ⟨814992, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107529
    ⟨814992, by decide⟩ (by decide) (![⟨814903, by decide⟩,⟨814968, by decide⟩,⟨814989, by decide⟩,⟨814991, by decide⟩]) unmarked_context_12_107529_814992 node_context_12_107529_814992
  intro a
  fin_cases a
  · exact context_13_430116_814903
  · exact context_13_430117_814968
  · exact context_13_430118_814989
  · exact context_13_430119_814991

theorem selected_cut_31762 : selected 9 ⟨4595, by decide⟩
    (prefixPartial 12 107530) = some ⟨12, 1, 0, 4595, 107530, 1, 65536⟩ := by
  decide +kernel

theorem context_12_107530_4595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107530 ⟨4595, by decide⟩ :=
  accepted_of_selected 12 107530 ⟨4595, by decide⟩ ⟨12, 1, 0, 4595, 107530, 1, 65536⟩
    (by decide) selected_cut_31762

theorem selected_cut_31763 : selected 7 ⟨815008, by decide⟩
    (prefixPartial 14 1720496) = some ⟨14, 2, 0, 815008, 1720496, 369, 4096⟩ := by
  decide +kernel

theorem context_14_1720496_815008 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1720496 ⟨815008, by decide⟩ :=
  accepted_of_selected 14 1720496 ⟨815008, by decide⟩ ⟨14, 2, 0, 815008, 1720496, 369, 4096⟩
    (by decide) selected_cut_31763

theorem selected_cut_31764 : selected 7 ⟨815036, by decide⟩
    (prefixPartial 14 1720497) = some ⟨14, 2, 0, 815036, 1720497, 1045, 4096⟩ := by
  decide +kernel

theorem context_14_1720497_815036 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1720497 ⟨815036, by decide⟩ :=
  accepted_of_selected 14 1720497 ⟨815036, by decide⟩ ⟨14, 2, 0, 815036, 1720497, 1045, 4096⟩
    (by decide) selected_cut_31764

theorem selected_cut_31765 : selected 7 ⟨815069, by decide⟩
    (prefixPartial 14 1720498) = some ⟨14, 2, 0, 815069, 1720498, 1345, 4096⟩ := by
  decide +kernel

theorem context_14_1720498_815069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1720498 ⟨815069, by decide⟩ :=
  accepted_of_selected 14 1720498 ⟨815069, by decide⟩ ⟨14, 2, 0, 815069, 1720498, 1345, 4096⟩
    (by decide) selected_cut_31765

theorem selected_cut_31766 : selected 7 ⟨815103, by decide⟩
    (prefixPartial 14 1720499) = some ⟨14, 2, 0, 815103, 1720499, 1425, 4096⟩ := by
  decide +kernel

theorem context_14_1720499_815103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1720499 ⟨815103, by decide⟩ :=
  accepted_of_selected 14 1720499 ⟨815103, by decide⟩ ⟨14, 2, 0, 815103, 1720499, 1425, 4096⟩
    (by decide) selected_cut_31766

theorem unmarked_context_13_430124_815104 : frontier 8 ⟨815104, by decide⟩
    (prefixCache 13 430124) (prefixPartial 13 430124) = false := by
  decide +kernel

theorem node_context_13_430124_815104 : EJMOriginalGlobalDAGData.nodes 8 ⟨815104, by decide⟩ =
    .split (coordinate 13) (![⟨815008, by decide⟩,⟨815036, by decide⟩,⟨815069, by decide⟩,⟨815103, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_430124_815104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430124 ⟨815104, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 430124
    ⟨815104, by decide⟩ (by decide) (![⟨815008, by decide⟩,⟨815036, by decide⟩,⟨815069, by decide⟩,⟨815103, by decide⟩]) unmarked_context_13_430124_815104 node_context_13_430124_815104
  intro a
  fin_cases a
  · exact context_14_1720496_815008
  · exact context_14_1720497_815036
  · exact context_14_1720498_815069
  · exact context_14_1720499_815103

theorem selected_cut_31767 : selected 7 ⟨815133, by decide⟩
    (prefixPartial 14 1720500) = some ⟨14, 2, 0, 815133, 1720500, 1065, 4096⟩ := by
  decide +kernel

theorem context_14_1720500_815133 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1720500 ⟨815133, by decide⟩ :=
  accepted_of_selected 14 1720500 ⟨815133, by decide⟩ ⟨14, 2, 0, 815133, 1720500, 1065, 4096⟩
    (by decide) selected_cut_31767

theorem selected_cut_31768 : selected 7 ⟨815155, by decide⟩
    (prefixPartial 14 1720501) = some ⟨14, 2, 0, 815155, 1720501, 789, 4096⟩ := by
  decide +kernel

theorem context_14_1720501_815155 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1720501 ⟨815155, by decide⟩ :=
  accepted_of_selected 14 1720501 ⟨815155, by decide⟩ ⟨14, 2, 0, 815155, 1720501, 789, 4096⟩
    (by decide) selected_cut_31768

theorem selected_cut_31769 : selected 7 ⟨815196, by decide⟩
    (prefixPartial 14 1720502) = some ⟨14, 2, 0, 815196, 1720502, 1273, 4096⟩ := by
  decide +kernel

theorem context_14_1720502_815196 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1720502 ⟨815196, by decide⟩ :=
  accepted_of_selected 14 1720502 ⟨815196, by decide⟩ ⟨14, 2, 0, 815196, 1720502, 1273, 4096⟩
    (by decide) selected_cut_31769

theorem selected_cut_31770 : selected 7 ⟨815230, by decide⟩
    (prefixPartial 14 1720503) = some ⟨14, 2, 0, 815230, 1720503, 1117, 4096⟩ := by
  decide +kernel

theorem context_14_1720503_815230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1720503 ⟨815230, by decide⟩ :=
  accepted_of_selected 14 1720503 ⟨815230, by decide⟩ ⟨14, 2, 0, 815230, 1720503, 1117, 4096⟩
    (by decide) selected_cut_31770

theorem unmarked_context_13_430125_815231 : frontier 8 ⟨815231, by decide⟩
    (prefixCache 13 430125) (prefixPartial 13 430125) = false := by
  decide +kernel

theorem node_context_13_430125_815231 : EJMOriginalGlobalDAGData.nodes 8 ⟨815231, by decide⟩ =
    .split (coordinate 13) (![⟨815133, by decide⟩,⟨815155, by decide⟩,⟨815196, by decide⟩,⟨815230, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_430125_815231 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430125 ⟨815231, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 430125
    ⟨815231, by decide⟩ (by decide) (![⟨815133, by decide⟩,⟨815155, by decide⟩,⟨815196, by decide⟩,⟨815230, by decide⟩]) unmarked_context_13_430125_815231 node_context_13_430125_815231
  intro a
  fin_cases a
  · exact context_14_1720500_815133
  · exact context_14_1720501_815155
  · exact context_14_1720502_815196
  · exact context_14_1720503_815230

theorem selected_cut_31771 : selected 8 ⟨815316, by decide⟩
    (prefixPartial 13 430126) = some ⟨13, 2, 0, 815316, 430126, 2293, 16384⟩ := by
  decide +kernel

theorem context_13_430126_815316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430126 ⟨815316, by decide⟩ :=
  accepted_of_selected 13 430126 ⟨815316, by decide⟩ ⟨13, 2, 0, 815316, 430126, 2293, 16384⟩
    (by decide) selected_cut_31771

theorem selected_cut_31772 : selected 8 ⟨815331, by decide⟩
    (prefixPartial 13 430127) = some ⟨13, 2, 0, 815331, 430127, 973, 16384⟩ := by
  decide +kernel

theorem context_13_430127_815331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430127 ⟨815331, by decide⟩ :=
  accepted_of_selected 13 430127 ⟨815331, by decide⟩ ⟨13, 2, 0, 815331, 430127, 973, 16384⟩
    (by decide) selected_cut_31772

theorem unmarked_context_12_107531_815332 : frontier 9 ⟨815332, by decide⟩
    (prefixCache 12 107531) (prefixPartial 12 107531) = false := by
  decide +kernel

theorem node_context_12_107531_815332 : EJMOriginalGlobalDAGData.nodes 9 ⟨815332, by decide⟩ =
    .split (coordinate 12) (![⟨815104, by decide⟩,⟨815231, by decide⟩,⟨815316, by decide⟩,⟨815331, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107531_815332 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107531 ⟨815332, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107531
    ⟨815332, by decide⟩ (by decide) (![⟨815104, by decide⟩,⟨815231, by decide⟩,⟨815316, by decide⟩,⟨815331, by decide⟩]) unmarked_context_12_107531_815332 node_context_12_107531_815332
  intro a
  fin_cases a
  · exact context_13_430124_815104
  · exact context_13_430125_815231
  · exact context_13_430126_815316
  · exact context_13_430127_815331

theorem unmarked_context_11_26882_815333 : frontier 10 ⟨815333, by decide⟩
    (prefixCache 11 26882) (prefixPartial 11 26882) = false := by
  decide +kernel

theorem node_context_11_26882_815333 : EJMOriginalGlobalDAGData.nodes 10 ⟨815333, by decide⟩ =
    .split (coordinate 11) (![⟨4595, by decide⟩,⟨814992, by decide⟩,⟨4595, by decide⟩,⟨815332, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26882_815333 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26882 ⟨815333, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26882
    ⟨815333, by decide⟩ (by decide) (![⟨4595, by decide⟩,⟨814992, by decide⟩,⟨4595, by decide⟩,⟨815332, by decide⟩]) unmarked_context_11_26882_815333 node_context_11_26882_815333
  intro a
  fin_cases a
  · exact context_12_107528_4595
  · exact context_12_107529_814992
  · exact context_12_107530_4595
  · exact context_12_107531_815332

theorem selected_cut_31773 : selected 10 ⟨815335, by decide⟩
    (prefixPartial 11 26883) = some ⟨11, 2, 0, 815335, 26883, 5, 262144⟩ := by
  decide +kernel

theorem context_11_26883_815335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26883 ⟨815335, by decide⟩ :=
  accepted_of_selected 11 26883 ⟨815335, by decide⟩ ⟨11, 2, 0, 815335, 26883, 5, 262144⟩
    (by decide) selected_cut_31773

theorem unmarked_context_10_6720_815336 : frontier 11 ⟨815336, by decide⟩
    (prefixCache 10 6720) (prefixPartial 10 6720) = false := by
  decide +kernel

theorem node_context_10_6720_815336 : EJMOriginalGlobalDAGData.nodes 11 ⟨815336, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨167448, by decide⟩,⟨815333, by decide⟩,⟨815335, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6720_815336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6720 ⟨815336, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6720
    ⟨815336, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨167448, by decide⟩,⟨815333, by decide⟩,⟨815335, by decide⟩]) unmarked_context_10_6720_815336 node_context_10_6720_815336
  intro a
  fin_cases a
  · exact context_11_26880_434745
  · exact context_11_26881_167448
  · exact context_11_26882_815333
  · exact context_11_26883_815335

theorem selected_cut_31774 : selected 9 ⟨815337, by decide⟩
    (prefixPartial 12 107536) = some ⟨12, 1, 0, 815337, 107536, 1, 65536⟩ := by
  decide +kernel

theorem context_12_107536_815337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107536 ⟨815337, by decide⟩ :=
  accepted_of_selected 12 107536 ⟨815337, by decide⟩ ⟨12, 1, 0, 815337, 107536, 1, 65536⟩
    (by decide) selected_cut_31774

theorem selected_cut_31775 : selected 8 ⟨815370, by decide⟩
    (prefixPartial 13 430148) = some ⟨13, 2, 0, 815370, 430148, 1725, 16384⟩ := by
  decide +kernel

theorem context_13_430148_815370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430148 ⟨815370, by decide⟩ :=
  accepted_of_selected 13 430148 ⟨815370, by decide⟩ ⟨13, 2, 0, 815370, 430148, 1725, 16384⟩
    (by decide) selected_cut_31775

theorem selected_cut_31776 : selected 8 ⟨815400, by decide⟩
    (prefixPartial 13 430149) = some ⟨13, 2, 0, 815400, 430149, 2185, 16384⟩ := by
  decide +kernel

theorem context_13_430149_815400 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430149 ⟨815400, by decide⟩ :=
  accepted_of_selected 13 430149 ⟨815400, by decide⟩ ⟨13, 2, 0, 815400, 430149, 2185, 16384⟩
    (by decide) selected_cut_31776

theorem selected_cut_31777 : selected 8 ⟨815420, by decide⟩
    (prefixPartial 13 430150) = some ⟨13, 2, 0, 815420, 430150, 1033, 16384⟩ := by
  decide +kernel

theorem context_13_430150_815420 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430150 ⟨815420, by decide⟩ :=
  accepted_of_selected 13 430150 ⟨815420, by decide⟩ ⟨13, 2, 0, 815420, 430150, 1033, 16384⟩
    (by decide) selected_cut_31777

theorem selected_cut_31778 : selected 8 ⟨815428, by decide⟩
    (prefixPartial 13 430151) = some ⟨13, 2, 0, 815428, 430151, 757, 16384⟩ := by
  decide +kernel

theorem context_13_430151_815428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430151 ⟨815428, by decide⟩ :=
  accepted_of_selected 13 430151 ⟨815428, by decide⟩ ⟨13, 2, 0, 815428, 430151, 757, 16384⟩
    (by decide) selected_cut_31778

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
