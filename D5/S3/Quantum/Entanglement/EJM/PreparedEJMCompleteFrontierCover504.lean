/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover503
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_48388 : selected 9 ⟨1357642, by decide⟩
    (prefixPartial 12 376102) = some ⟨12, 2, 0, 1357642, 376102, 2533, 65536⟩ := by
  decide +kernel

theorem context_12_376102_1357642 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376102 ⟨1357642, by decide⟩ :=
  accepted_of_selected 12 376102 ⟨1357642, by decide⟩ ⟨12, 2, 0, 1357642, 376102, 2533, 65536⟩
    (by decide) selected_cut_48388

theorem selected_cut_48389 : selected 9 ⟨1357684, by decide⟩
    (prefixPartial 12 376103) = some ⟨12, 2, 0, 1357684, 376103, 2389, 65536⟩ := by
  decide +kernel

theorem context_12_376103_1357684 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376103 ⟨1357684, by decide⟩ :=
  accepted_of_selected 12 376103 ⟨1357684, by decide⟩ ⟨12, 2, 0, 1357684, 376103, 2389, 65536⟩
    (by decide) selected_cut_48389

theorem unmarked_context_11_94025_1357685 : frontier 10 ⟨1357685, by decide⟩
    (prefixCache 11 94025) (prefixPartial 11 94025) = false := by
  decide +kernel

theorem node_context_11_94025_1357685 : EJMOriginalGlobalDAGData.nodes 10 ⟨1357685, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨891951, by decide⟩,⟨1357642, by decide⟩,⟨1357684, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_94025_1357685 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94025 ⟨1357685, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 94025
    ⟨1357685, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨891951, by decide⟩,⟨1357642, by decide⟩,⟨1357684, by decide⟩]) unmarked_context_11_94025_1357685 node_context_11_94025_1357685
  intro a
  fin_cases a
  · exact context_12_376100_435790
  · exact context_12_376101_891951
  · exact context_12_376102_1357642
  · exact context_12_376103_1357684

theorem selected_cut_48390 : selected 10 ⟨1357724, by decide⟩
    (prefixPartial 11 94026) = some ⟨11, 2, 0, 1357724, 94026, 2057, 262144⟩ := by
  decide +kernel

theorem context_11_94026_1357724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94026 ⟨1357724, by decide⟩ :=
  accepted_of_selected 11 94026 ⟨1357724, by decide⟩ ⟨11, 2, 0, 1357724, 94026, 2057, 262144⟩
    (by decide) selected_cut_48390

theorem selected_cut_48391 : selected 9 ⟨450498, by decide⟩
    (prefixPartial 12 376108) = some ⟨12, 1, 0, 450498, 376108, 1, 65536⟩ := by
  decide +kernel

theorem context_12_376108_450498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376108 ⟨450498, by decide⟩ :=
  accepted_of_selected 12 376108 ⟨450498, by decide⟩ ⟨12, 1, 0, 450498, 376108, 1, 65536⟩
    (by decide) selected_cut_48391

theorem selected_cut_48392 : selected 9 ⟨1357759, by decide⟩
    (prefixPartial 12 376109) = some ⟨12, 2, 0, 1357759, 376109, 2197, 65536⟩ := by
  decide +kernel

theorem context_12_376109_1357759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376109 ⟨1357759, by decide⟩ :=
  accepted_of_selected 12 376109 ⟨1357759, by decide⟩ ⟨12, 2, 0, 1357759, 376109, 2197, 65536⟩
    (by decide) selected_cut_48392

theorem selected_cut_48393 : selected 9 ⟨1357800, by decide⟩
    (prefixPartial 12 376110) = some ⟨12, 2, 0, 1357800, 376110, 2069, 65536⟩ := by
  decide +kernel

theorem context_12_376110_1357800 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376110 ⟨1357800, by decide⟩ :=
  accepted_of_selected 12 376110 ⟨1357800, by decide⟩ ⟨12, 2, 0, 1357800, 376110, 2069, 65536⟩
    (by decide) selected_cut_48393

theorem selected_cut_48394 : selected 9 ⟨1357839, by decide⟩
    (prefixPartial 12 376111) = some ⟨12, 2, 0, 1357839, 376111, 2097, 65536⟩ := by
  decide +kernel

theorem context_12_376111_1357839 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376111 ⟨1357839, by decide⟩ :=
  accepted_of_selected 12 376111 ⟨1357839, by decide⟩ ⟨12, 2, 0, 1357839, 376111, 2097, 65536⟩
    (by decide) selected_cut_48394

theorem unmarked_context_11_94027_1357840 : frontier 10 ⟨1357840, by decide⟩
    (prefixCache 11 94027) (prefixPartial 11 94027) = false := by
  decide +kernel

theorem node_context_11_94027_1357840 : EJMOriginalGlobalDAGData.nodes 10 ⟨1357840, by decide⟩ =
    .split (coordinate 11) (![⟨450498, by decide⟩,⟨1357759, by decide⟩,⟨1357800, by decide⟩,⟨1357839, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_94027_1357840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94027 ⟨1357840, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 94027
    ⟨1357840, by decide⟩ (by decide) (![⟨450498, by decide⟩,⟨1357759, by decide⟩,⟨1357800, by decide⟩,⟨1357839, by decide⟩]) unmarked_context_11_94027_1357840 node_context_11_94027_1357840
  intro a
  fin_cases a
  · exact context_12_376108_450498
  · exact context_12_376109_1357759
  · exact context_12_376110_1357800
  · exact context_12_376111_1357839

theorem unmarked_context_10_23506_1357841 : frontier 11 ⟨1357841, by decide⟩
    (prefixCache 10 23506) (prefixPartial 10 23506) = false := by
  decide +kernel

theorem node_context_10_23506_1357841 : EJMOriginalGlobalDAGData.nodes 11 ⟨1357841, by decide⟩ =
    .split (coordinate 10) (![⟨1357591, by decide⟩,⟨1357685, by decide⟩,⟨1357724, by decide⟩,⟨1357840, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23506_1357841 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23506 ⟨1357841, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23506
    ⟨1357841, by decide⟩ (by decide) (![⟨1357591, by decide⟩,⟨1357685, by decide⟩,⟨1357724, by decide⟩,⟨1357840, by decide⟩]) unmarked_context_10_23506_1357841 node_context_10_23506_1357841
  intro a
  fin_cases a
  · exact context_11_94024_1357591
  · exact context_11_94025_1357685
  · exact context_11_94026_1357724
  · exact context_11_94027_1357840

theorem selected_cut_48395 : selected 9 ⟨1255011, by decide⟩
    (prefixPartial 12 376112) = some ⟨12, 1, 0, 1255011, 376112, 1, 65536⟩ := by
  decide +kernel

theorem context_12_376112_1255011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376112 ⟨1255011, by decide⟩ :=
  accepted_of_selected 12 376112 ⟨1255011, by decide⟩ ⟨12, 1, 0, 1255011, 376112, 1, 65536⟩
    (by decide) selected_cut_48395

theorem selected_cut_48396 : selected 9 ⟨1357869, by decide⟩
    (prefixPartial 12 376113) = some ⟨12, 2, 0, 1357869, 376113, 1649, 65536⟩ := by
  decide +kernel

theorem context_12_376113_1357869 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376113 ⟨1357869, by decide⟩ :=
  accepted_of_selected 12 376113 ⟨1357869, by decide⟩ ⟨12, 2, 0, 1357869, 376113, 1649, 65536⟩
    (by decide) selected_cut_48396

theorem selected_cut_48397 : selected 9 ⟨1357898, by decide⟩
    (prefixPartial 12 376114) = some ⟨12, 2, 0, 1357898, 376114, 1545, 65536⟩ := by
  decide +kernel

theorem context_12_376114_1357898 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376114 ⟨1357898, by decide⟩ :=
  accepted_of_selected 12 376114 ⟨1357898, by decide⟩ ⟨12, 2, 0, 1357898, 376114, 1545, 65536⟩
    (by decide) selected_cut_48397

theorem selected_cut_48398 : selected 9 ⟨1357925, by decide⟩
    (prefixPartial 12 376115) = some ⟨12, 2, 0, 1357925, 376115, 1509, 65536⟩ := by
  decide +kernel

theorem context_12_376115_1357925 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376115 ⟨1357925, by decide⟩ :=
  accepted_of_selected 12 376115 ⟨1357925, by decide⟩ ⟨12, 2, 0, 1357925, 376115, 1509, 65536⟩
    (by decide) selected_cut_48398

theorem unmarked_context_11_94028_1357926 : frontier 10 ⟨1357926, by decide⟩
    (prefixCache 11 94028) (prefixPartial 11 94028) = false := by
  decide +kernel

theorem node_context_11_94028_1357926 : EJMOriginalGlobalDAGData.nodes 10 ⟨1357926, by decide⟩ =
    .split (coordinate 11) (![⟨1255011, by decide⟩,⟨1357869, by decide⟩,⟨1357898, by decide⟩,⟨1357925, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_94028_1357926 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94028 ⟨1357926, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 94028
    ⟨1357926, by decide⟩ (by decide) (![⟨1255011, by decide⟩,⟨1357869, by decide⟩,⟨1357898, by decide⟩,⟨1357925, by decide⟩]) unmarked_context_11_94028_1357926 node_context_11_94028_1357926
  intro a
  fin_cases a
  · exact context_12_376112_1255011
  · exact context_12_376113_1357869
  · exact context_12_376114_1357898
  · exact context_12_376115_1357925

theorem selected_cut_48399 : selected 9 ⟨1357962, by decide⟩
    (prefixPartial 12 376116) = some ⟨12, 2, 0, 1357962, 376116, 1781, 65536⟩ := by
  decide +kernel

theorem context_12_376116_1357962 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376116 ⟨1357962, by decide⟩ :=
  accepted_of_selected 12 376116 ⟨1357962, by decide⟩ ⟨12, 2, 0, 1357962, 376116, 1781, 65536⟩
    (by decide) selected_cut_48399

theorem selected_cut_48400 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 376117) = some ⟨12, 1, 0, 891951, 376117, 1, 65536⟩ := by
  decide +kernel

theorem context_12_376117_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376117 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 376117 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 376117, 1, 65536⟩
    (by decide) selected_cut_48400

theorem selected_cut_48401 : selected 9 ⟨1357987, by decide⟩
    (prefixPartial 12 376118) = some ⟨12, 2, 0, 1357987, 376118, 1581, 65536⟩ := by
  decide +kernel

theorem context_12_376118_1357987 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376118 ⟨1357987, by decide⟩ :=
  accepted_of_selected 12 376118 ⟨1357987, by decide⟩ ⟨12, 2, 0, 1357987, 376118, 1581, 65536⟩
    (by decide) selected_cut_48401

theorem selected_cut_48402 : selected 9 ⟨1358011, by decide⟩
    (prefixPartial 12 376119) = some ⟨12, 2, 0, 1358011, 376119, 1573, 65536⟩ := by
  decide +kernel

theorem context_12_376119_1358011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376119 ⟨1358011, by decide⟩ :=
  accepted_of_selected 12 376119 ⟨1358011, by decide⟩ ⟨12, 2, 0, 1358011, 376119, 1573, 65536⟩
    (by decide) selected_cut_48402

theorem unmarked_context_11_94029_1358012 : frontier 10 ⟨1358012, by decide⟩
    (prefixCache 11 94029) (prefixPartial 11 94029) = false := by
  decide +kernel

theorem node_context_11_94029_1358012 : EJMOriginalGlobalDAGData.nodes 10 ⟨1358012, by decide⟩ =
    .split (coordinate 11) (![⟨1357962, by decide⟩,⟨891951, by decide⟩,⟨1357987, by decide⟩,⟨1358011, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_94029_1358012 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94029 ⟨1358012, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 94029
    ⟨1358012, by decide⟩ (by decide) (![⟨1357962, by decide⟩,⟨891951, by decide⟩,⟨1357987, by decide⟩,⟨1358011, by decide⟩]) unmarked_context_11_94029_1358012 node_context_11_94029_1358012
  intro a
  fin_cases a
  · exact context_12_376116_1357962
  · exact context_12_376117_891951
  · exact context_12_376118_1357987
  · exact context_12_376119_1358011

theorem selected_cut_48403 : selected 9 ⟨1055595, by decide⟩
    (prefixPartial 12 376120) = some ⟨12, 1, 0, 1055595, 376120, 1, 65536⟩ := by
  decide +kernel

theorem context_12_376120_1055595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376120 ⟨1055595, by decide⟩ :=
  accepted_of_selected 12 376120 ⟨1055595, by decide⟩ ⟨12, 1, 0, 1055595, 376120, 1, 65536⟩
    (by decide) selected_cut_48403

theorem selected_cut_48404 : selected 9 ⟨1358033, by decide⟩
    (prefixPartial 12 376121) = some ⟨12, 2, 0, 1358033, 376121, 1425, 65536⟩ := by
  decide +kernel

theorem context_12_376121_1358033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376121 ⟨1358033, by decide⟩ :=
  accepted_of_selected 12 376121 ⟨1358033, by decide⟩ ⟨12, 2, 0, 1358033, 376121, 1425, 65536⟩
    (by decide) selected_cut_48404

theorem selected_cut_48405 : selected 9 ⟨1358055, by decide⟩
    (prefixPartial 12 376122) = some ⟨12, 2, 0, 1358055, 376122, 1517, 65536⟩ := by
  decide +kernel

theorem context_12_376122_1358055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376122 ⟨1358055, by decide⟩ :=
  accepted_of_selected 12 376122 ⟨1358055, by decide⟩ ⟨12, 2, 0, 1358055, 376122, 1517, 65536⟩
    (by decide) selected_cut_48405

theorem selected_cut_48406 : selected 9 ⟨1358078, by decide⟩
    (prefixPartial 12 376123) = some ⟨12, 2, 0, 1358078, 376123, 1405, 65536⟩ := by
  decide +kernel

theorem context_12_376123_1358078 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376123 ⟨1358078, by decide⟩ :=
  accepted_of_selected 12 376123 ⟨1358078, by decide⟩ ⟨12, 2, 0, 1358078, 376123, 1405, 65536⟩
    (by decide) selected_cut_48406

theorem unmarked_context_11_94030_1358079 : frontier 10 ⟨1358079, by decide⟩
    (prefixCache 11 94030) (prefixPartial 11 94030) = false := by
  decide +kernel

theorem node_context_11_94030_1358079 : EJMOriginalGlobalDAGData.nodes 10 ⟨1358079, by decide⟩ =
    .split (coordinate 11) (![⟨1055595, by decide⟩,⟨1358033, by decide⟩,⟨1358055, by decide⟩,⟨1358078, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_94030_1358079 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94030 ⟨1358079, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 94030
    ⟨1358079, by decide⟩ (by decide) (![⟨1055595, by decide⟩,⟨1358033, by decide⟩,⟨1358055, by decide⟩,⟨1358078, by decide⟩]) unmarked_context_11_94030_1358079 node_context_11_94030_1358079
  intro a
  fin_cases a
  · exact context_12_376120_1055595
  · exact context_12_376121_1358033
  · exact context_12_376122_1358055
  · exact context_12_376123_1358078

theorem selected_cut_48407 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 94031) = some ⟨11, 1, 0, 977886, 94031, 1, 262144⟩ := by
  decide +kernel

theorem context_11_94031_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94031 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 94031 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 94031, 1, 262144⟩
    (by decide) selected_cut_48407

theorem unmarked_context_10_23507_1358080 : frontier 11 ⟨1358080, by decide⟩
    (prefixCache 10 23507) (prefixPartial 10 23507) = false := by
  decide +kernel

theorem node_context_10_23507_1358080 : EJMOriginalGlobalDAGData.nodes 11 ⟨1358080, by decide⟩ =
    .split (coordinate 10) (![⟨1357926, by decide⟩,⟨1358012, by decide⟩,⟨1358079, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23507_1358080 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23507 ⟨1358080, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23507
    ⟨1358080, by decide⟩ (by decide) (![⟨1357926, by decide⟩,⟨1358012, by decide⟩,⟨1358079, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_23507_1358080 node_context_10_23507_1358080
  intro a
  fin_cases a
  · exact context_11_94028_1357926
  · exact context_11_94029_1358012
  · exact context_11_94030_1358079
  · exact context_11_94031_977886

theorem unmarked_context_9_5876_1358081 : frontier 12 ⟨1358081, by decide⟩
    (prefixCache 9 5876) (prefixPartial 9 5876) = false := by
  decide +kernel

theorem node_context_9_5876_1358081 : EJMOriginalGlobalDAGData.nodes 12 ⟨1358081, by decide⟩ =
    .split (coordinate 9) (![⟨1357064, by decide⟩,⟨1357469, by decide⟩,⟨1357841, by decide⟩,⟨1358080, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5876_1358081 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5876 ⟨1358081, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5876
    ⟨1358081, by decide⟩ (by decide) (![⟨1357064, by decide⟩,⟨1357469, by decide⟩,⟨1357841, by decide⟩,⟨1358080, by decide⟩]) unmarked_context_9_5876_1358081 node_context_9_5876_1358081
  intro a
  fin_cases a
  · exact context_10_23504_1357064
  · exact context_10_23505_1357469
  · exact context_10_23506_1357841
  · exact context_10_23507_1358080

theorem selected_cut_48408 : selected 10 ⟨1358133, by decide⟩
    (prefixPartial 11 94032) = some ⟨11, 2, 0, 1358133, 94032, 2785, 262144⟩ := by
  decide +kernel

theorem context_11_94032_1358133 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94032 ⟨1358133, by decide⟩ :=
  accepted_of_selected 11 94032 ⟨1358133, by decide⟩ ⟨11, 2, 0, 1358133, 94032, 2785, 262144⟩
    (by decide) selected_cut_48408

theorem selected_cut_48409 : selected 9 ⟨1358165, by decide⟩
    (prefixPartial 12 376132) = some ⟨12, 2, 0, 1358165, 376132, 1685, 65536⟩ := by
  decide +kernel

theorem context_12_376132_1358165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376132 ⟨1358165, by decide⟩ :=
  accepted_of_selected 12 376132 ⟨1358165, by decide⟩ ⟨12, 2, 0, 1358165, 376132, 1685, 65536⟩
    (by decide) selected_cut_48409

theorem selected_cut_48410 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 376133) = some ⟨12, 1, 0, 891951, 376133, 1, 65536⟩ := by
  decide +kernel

theorem context_12_376133_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376133 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 376133 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 376133, 1, 65536⟩
    (by decide) selected_cut_48410

theorem selected_cut_48411 : selected 9 ⟨1358194, by decide⟩
    (prefixPartial 12 376134) = some ⟨12, 2, 0, 1358194, 376134, 1529, 65536⟩ := by
  decide +kernel

theorem context_12_376134_1358194 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376134 ⟨1358194, by decide⟩ :=
  accepted_of_selected 12 376134 ⟨1358194, by decide⟩ ⟨12, 2, 0, 1358194, 376134, 1529, 65536⟩
    (by decide) selected_cut_48411

theorem selected_cut_48412 : selected 9 ⟨1358223, by decide⟩
    (prefixPartial 12 376135) = some ⟨12, 2, 0, 1358223, 376135, 1601, 65536⟩ := by
  decide +kernel

theorem context_12_376135_1358223 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376135 ⟨1358223, by decide⟩ :=
  accepted_of_selected 12 376135 ⟨1358223, by decide⟩ ⟨12, 2, 0, 1358223, 376135, 1601, 65536⟩
    (by decide) selected_cut_48412

theorem unmarked_context_11_94033_1358224 : frontier 10 ⟨1358224, by decide⟩
    (prefixCache 11 94033) (prefixPartial 11 94033) = false := by
  decide +kernel

theorem node_context_11_94033_1358224 : EJMOriginalGlobalDAGData.nodes 10 ⟨1358224, by decide⟩ =
    .split (coordinate 11) (![⟨1358165, by decide⟩,⟨891951, by decide⟩,⟨1358194, by decide⟩,⟨1358223, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_94033_1358224 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94033 ⟨1358224, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 94033
    ⟨1358224, by decide⟩ (by decide) (![⟨1358165, by decide⟩,⟨891951, by decide⟩,⟨1358194, by decide⟩,⟨1358223, by decide⟩]) unmarked_context_11_94033_1358224 node_context_11_94033_1358224
  intro a
  fin_cases a
  · exact context_12_376132_1358165
  · exact context_12_376133_891951
  · exact context_12_376134_1358194
  · exact context_12_376135_1358223

theorem selected_cut_48413 : selected 10 ⟨1358279, by decide⟩
    (prefixPartial 11 94034) = some ⟨11, 2, 0, 1358279, 94034, 2725, 262144⟩ := by
  decide +kernel

theorem context_11_94034_1358279 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94034 ⟨1358279, by decide⟩ :=
  accepted_of_selected 11 94034 ⟨1358279, by decide⟩ ⟨11, 2, 0, 1358279, 94034, 2725, 262144⟩
    (by decide) selected_cut_48413

theorem selected_cut_48414 : selected 9 ⟨1358302, by decide⟩
    (prefixPartial 12 376140) = some ⟨12, 2, 0, 1358302, 376140, 1341, 65536⟩ := by
  decide +kernel

theorem context_12_376140_1358302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376140 ⟨1358302, by decide⟩ :=
  accepted_of_selected 12 376140 ⟨1358302, by decide⟩ ⟨12, 2, 0, 1358302, 376140, 1341, 65536⟩
    (by decide) selected_cut_48414

theorem selected_cut_48415 : selected 9 ⟨1358326, by decide⟩
    (prefixPartial 12 376141) = some ⟨12, 2, 0, 1358326, 376141, 1393, 65536⟩ := by
  decide +kernel

theorem context_12_376141_1358326 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376141 ⟨1358326, by decide⟩ :=
  accepted_of_selected 12 376141 ⟨1358326, by decide⟩ ⟨12, 2, 0, 1358326, 376141, 1393, 65536⟩
    (by decide) selected_cut_48415

theorem selected_cut_48416 : selected 9 ⟨1358349, by decide⟩
    (prefixPartial 12 376142) = some ⟨12, 2, 0, 1358349, 376142, 1369, 65536⟩ := by
  decide +kernel

theorem context_12_376142_1358349 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376142 ⟨1358349, by decide⟩ :=
  accepted_of_selected 12 376142 ⟨1358349, by decide⟩ ⟨12, 2, 0, 1358349, 376142, 1369, 65536⟩
    (by decide) selected_cut_48416

theorem selected_cut_48417 : selected 9 ⟨434704, by decide⟩
    (prefixPartial 12 376143) = some ⟨12, 1, 0, 434704, 376143, 1, 65536⟩ := by
  decide +kernel

theorem context_12_376143_434704 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376143 ⟨434704, by decide⟩ :=
  accepted_of_selected 12 376143 ⟨434704, by decide⟩ ⟨12, 1, 0, 434704, 376143, 1, 65536⟩
    (by decide) selected_cut_48417

theorem unmarked_context_11_94035_1358350 : frontier 10 ⟨1358350, by decide⟩
    (prefixCache 11 94035) (prefixPartial 11 94035) = false := by
  decide +kernel

theorem node_context_11_94035_1358350 : EJMOriginalGlobalDAGData.nodes 10 ⟨1358350, by decide⟩ =
    .split (coordinate 11) (![⟨1358302, by decide⟩,⟨1358326, by decide⟩,⟨1358349, by decide⟩,⟨434704, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_94035_1358350 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94035 ⟨1358350, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 94035
    ⟨1358350, by decide⟩ (by decide) (![⟨1358302, by decide⟩,⟨1358326, by decide⟩,⟨1358349, by decide⟩,⟨434704, by decide⟩]) unmarked_context_11_94035_1358350 node_context_11_94035_1358350
  intro a
  fin_cases a
  · exact context_12_376140_1358302
  · exact context_12_376141_1358326
  · exact context_12_376142_1358349
  · exact context_12_376143_434704

theorem unmarked_context_10_23508_1358351 : frontier 11 ⟨1358351, by decide⟩
    (prefixCache 10 23508) (prefixPartial 10 23508) = false := by
  decide +kernel

theorem node_context_10_23508_1358351 : EJMOriginalGlobalDAGData.nodes 11 ⟨1358351, by decide⟩ =
    .split (coordinate 10) (![⟨1358133, by decide⟩,⟨1358224, by decide⟩,⟨1358279, by decide⟩,⟨1358350, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23508_1358351 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23508 ⟨1358351, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23508
    ⟨1358351, by decide⟩ (by decide) (![⟨1358133, by decide⟩,⟨1358224, by decide⟩,⟨1358279, by decide⟩,⟨1358350, by decide⟩]) unmarked_context_10_23508_1358351 node_context_10_23508_1358351
  intro a
  fin_cases a
  · exact context_11_94032_1358133
  · exact context_11_94033_1358224
  · exact context_11_94034_1358279
  · exact context_11_94035_1358350

theorem selected_cut_48418 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 23509) = some ⟨10, 1, 0, 893098, 23509, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_23509_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23509 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 23509 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 23509, 1, 1048576⟩
    (by decide) selected_cut_48418

theorem selected_cut_48419 : selected 10 ⟨1358384, by decide⟩
    (prefixPartial 11 94040) = some ⟨11, 2, 0, 1358384, 94040, 2401, 262144⟩ := by
  decide +kernel

theorem context_11_94040_1358384 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94040 ⟨1358384, by decide⟩ :=
  accepted_of_selected 11 94040 ⟨1358384, by decide⟩ ⟨11, 2, 0, 1358384, 94040, 2401, 262144⟩
    (by decide) selected_cut_48419

theorem selected_cut_48420 : selected 10 ⟨1358450, by decide⟩
    (prefixPartial 11 94041) = some ⟨11, 2, 0, 1358450, 94041, 3845, 262144⟩ := by
  decide +kernel

theorem context_11_94041_1358450 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94041 ⟨1358450, by decide⟩ :=
  accepted_of_selected 11 94041 ⟨1358450, by decide⟩ ⟨11, 2, 0, 1358450, 94041, 3845, 262144⟩
    (by decide) selected_cut_48420

theorem selected_cut_48421 : selected 10 ⟨1358470, by decide⟩
    (prefixPartial 11 94042) = some ⟨11, 2, 0, 1358470, 94042, 1009, 262144⟩ := by
  decide +kernel

theorem context_11_94042_1358470 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94042 ⟨1358470, by decide⟩ :=
  accepted_of_selected 11 94042 ⟨1358470, by decide⟩ ⟨11, 2, 0, 1358470, 94042, 1009, 262144⟩
    (by decide) selected_cut_48421

theorem selected_cut_48422 : selected 10 ⟨1358509, by decide⟩
    (prefixPartial 11 94043) = some ⟨11, 2, 0, 1358509, 94043, 2185, 262144⟩ := by
  decide +kernel

theorem context_11_94043_1358509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94043 ⟨1358509, by decide⟩ :=
  accepted_of_selected 11 94043 ⟨1358509, by decide⟩ ⟨11, 2, 0, 1358509, 94043, 2185, 262144⟩
    (by decide) selected_cut_48422

theorem unmarked_context_10_23510_1358510 : frontier 11 ⟨1358510, by decide⟩
    (prefixCache 10 23510) (prefixPartial 10 23510) = false := by
  decide +kernel

theorem node_context_10_23510_1358510 : EJMOriginalGlobalDAGData.nodes 11 ⟨1358510, by decide⟩ =
    .split (coordinate 10) (![⟨1358384, by decide⟩,⟨1358450, by decide⟩,⟨1358470, by decide⟩,⟨1358509, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23510_1358510 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23510 ⟨1358510, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23510
    ⟨1358510, by decide⟩ (by decide) (![⟨1358384, by decide⟩,⟨1358450, by decide⟩,⟨1358470, by decide⟩,⟨1358509, by decide⟩]) unmarked_context_10_23510_1358510 node_context_10_23510_1358510
  intro a
  fin_cases a
  · exact context_11_94040_1358384
  · exact context_11_94041_1358450
  · exact context_11_94042_1358470
  · exact context_11_94043_1358509

theorem selected_cut_48423 : selected 10 ⟨1358578, by decide⟩
    (prefixPartial 11 94044) = some ⟨11, 2, 0, 1358578, 94044, 2909, 262144⟩ := by
  decide +kernel

theorem context_11_94044_1358578 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94044 ⟨1358578, by decide⟩ :=
  accepted_of_selected 11 94044 ⟨1358578, by decide⟩ ⟨11, 2, 0, 1358578, 94044, 2909, 262144⟩
    (by decide) selected_cut_48423

theorem selected_cut_48424 : selected 10 ⟨1358629, by decide⟩
    (prefixPartial 11 94045) = some ⟨11, 2, 0, 1358629, 94045, 2613, 262144⟩ := by
  decide +kernel

theorem context_11_94045_1358629 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94045 ⟨1358629, by decide⟩ :=
  accepted_of_selected 11 94045 ⟨1358629, by decide⟩ ⟨11, 2, 0, 1358629, 94045, 2613, 262144⟩
    (by decide) selected_cut_48424

theorem selected_cut_48425 : selected 10 ⟨1358652, by decide⟩
    (prefixPartial 11 94046) = some ⟨11, 2, 0, 1358652, 94046, 1569, 262144⟩ := by
  decide +kernel

theorem context_11_94046_1358652 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94046 ⟨1358652, by decide⟩ :=
  accepted_of_selected 11 94046 ⟨1358652, by decide⟩ ⟨11, 2, 0, 1358652, 94046, 1569, 262144⟩
    (by decide) selected_cut_48425

theorem selected_cut_48426 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 94047) = some ⟨11, 1, 0, 977886, 94047, 1, 262144⟩ := by
  decide +kernel

theorem context_11_94047_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94047 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 94047 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 94047, 1, 262144⟩
    (by decide) selected_cut_48426

theorem unmarked_context_10_23511_1358653 : frontier 11 ⟨1358653, by decide⟩
    (prefixCache 10 23511) (prefixPartial 10 23511) = false := by
  decide +kernel

theorem node_context_10_23511_1358653 : EJMOriginalGlobalDAGData.nodes 11 ⟨1358653, by decide⟩ =
    .split (coordinate 10) (![⟨1358578, by decide⟩,⟨1358629, by decide⟩,⟨1358652, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23511_1358653 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23511 ⟨1358653, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23511
    ⟨1358653, by decide⟩ (by decide) (![⟨1358578, by decide⟩,⟨1358629, by decide⟩,⟨1358652, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_23511_1358653 node_context_10_23511_1358653
  intro a
  fin_cases a
  · exact context_11_94044_1358578
  · exact context_11_94045_1358629
  · exact context_11_94046_1358652
  · exact context_11_94047_977886

theorem unmarked_context_9_5877_1358654 : frontier 12 ⟨1358654, by decide⟩
    (prefixCache 9 5877) (prefixPartial 9 5877) = false := by
  decide +kernel

theorem node_context_9_5877_1358654 : EJMOriginalGlobalDAGData.nodes 12 ⟨1358654, by decide⟩ =
    .split (coordinate 9) (![⟨1358351, by decide⟩,⟨893098, by decide⟩,⟨1358510, by decide⟩,⟨1358653, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5877_1358654 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5877 ⟨1358654, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5877
    ⟨1358654, by decide⟩ (by decide) (![⟨1358351, by decide⟩,⟨893098, by decide⟩,⟨1358510, by decide⟩,⟨1358653, by decide⟩]) unmarked_context_9_5877_1358654 node_context_9_5877_1358654
  intro a
  fin_cases a
  · exact context_10_23508_1358351
  · exact context_10_23509_893098
  · exact context_10_23510_1358510
  · exact context_10_23511_1358653

theorem selected_cut_48427 : selected 10 ⟨1358674, by decide⟩
    (prefixPartial 11 94048) = some ⟨11, 2, 0, 1358674, 94048, 1101, 262144⟩ := by
  decide +kernel

theorem context_11_94048_1358674 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94048 ⟨1358674, by decide⟩ :=
  accepted_of_selected 11 94048 ⟨1358674, by decide⟩ ⟨11, 2, 0, 1358674, 94048, 1101, 262144⟩
    (by decide) selected_cut_48427

theorem selected_cut_48428 : selected 10 ⟨1358714, by decide⟩
    (prefixPartial 11 94049) = some ⟨11, 2, 0, 1358714, 94049, 2377, 262144⟩ := by
  decide +kernel

theorem context_11_94049_1358714 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94049 ⟨1358714, by decide⟩ :=
  accepted_of_selected 11 94049 ⟨1358714, by decide⟩ ⟨11, 2, 0, 1358714, 94049, 2377, 262144⟩
    (by decide) selected_cut_48428

theorem selected_cut_48429 : selected 10 ⟨1358775, by decide⟩
    (prefixPartial 11 94050) = some ⟨11, 2, 0, 1358775, 94050, 3077, 262144⟩ := by
  decide +kernel

theorem context_11_94050_1358775 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94050 ⟨1358775, by decide⟩ :=
  accepted_of_selected 11 94050 ⟨1358775, by decide⟩ ⟨11, 2, 0, 1358775, 94050, 3077, 262144⟩
    (by decide) selected_cut_48429

theorem selected_cut_48430 : selected 10 ⟨1358817, by decide⟩
    (prefixPartial 11 94051) = some ⟨11, 2, 0, 1358817, 94051, 2649, 262144⟩ := by
  decide +kernel

theorem context_11_94051_1358817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94051 ⟨1358817, by decide⟩ :=
  accepted_of_selected 11 94051 ⟨1358817, by decide⟩ ⟨11, 2, 0, 1358817, 94051, 2649, 262144⟩
    (by decide) selected_cut_48430

theorem unmarked_context_10_23512_1358818 : frontier 11 ⟨1358818, by decide⟩
    (prefixCache 10 23512) (prefixPartial 10 23512) = false := by
  decide +kernel

theorem node_context_10_23512_1358818 : EJMOriginalGlobalDAGData.nodes 11 ⟨1358818, by decide⟩ =
    .split (coordinate 10) (![⟨1358674, by decide⟩,⟨1358714, by decide⟩,⟨1358775, by decide⟩,⟨1358817, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23512_1358818 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23512 ⟨1358818, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23512
    ⟨1358818, by decide⟩ (by decide) (![⟨1358674, by decide⟩,⟨1358714, by decide⟩,⟨1358775, by decide⟩,⟨1358817, by decide⟩]) unmarked_context_10_23512_1358818 node_context_10_23512_1358818
  intro a
  fin_cases a
  · exact context_11_94048_1358674
  · exact context_11_94049_1358714
  · exact context_11_94050_1358775
  · exact context_11_94051_1358817

theorem selected_cut_48431 : selected 10 ⟨1358876, by decide⟩
    (prefixPartial 11 94052) = some ⟨11, 2, 0, 1358876, 94052, 2009, 262144⟩ := by
  decide +kernel

theorem context_11_94052_1358876 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94052 ⟨1358876, by decide⟩ :=
  accepted_of_selected 11 94052 ⟨1358876, by decide⟩ ⟨11, 2, 0, 1358876, 94052, 2009, 262144⟩
    (by decide) selected_cut_48431

theorem selected_cut_48432 : selected 10 ⟨1358888, by decide⟩
    (prefixPartial 11 94053) = some ⟨11, 2, 0, 1358888, 94053, 781, 262144⟩ := by
  decide +kernel

theorem context_11_94053_1358888 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94053 ⟨1358888, by decide⟩ :=
  accepted_of_selected 11 94053 ⟨1358888, by decide⟩ ⟨11, 2, 0, 1358888, 94053, 781, 262144⟩
    (by decide) selected_cut_48432

theorem selected_cut_48433 : selected 10 ⟨1358919, by decide⟩
    (prefixPartial 11 94054) = some ⟨11, 2, 0, 1358919, 94054, 2105, 262144⟩ := by
  decide +kernel

theorem context_11_94054_1358919 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94054 ⟨1358919, by decide⟩ :=
  accepted_of_selected 11 94054 ⟨1358919, by decide⟩ ⟨11, 2, 0, 1358919, 94054, 2105, 262144⟩
    (by decide) selected_cut_48433

theorem selected_cut_48434 : selected 10 ⟨1358935, by decide⟩
    (prefixPartial 11 94055) = some ⟨11, 2, 0, 1358935, 94055, 1093, 262144⟩ := by
  decide +kernel

theorem context_11_94055_1358935 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94055 ⟨1358935, by decide⟩ :=
  accepted_of_selected 11 94055 ⟨1358935, by decide⟩ ⟨11, 2, 0, 1358935, 94055, 1093, 262144⟩
    (by decide) selected_cut_48434

theorem unmarked_context_10_23513_1358936 : frontier 11 ⟨1358936, by decide⟩
    (prefixCache 10 23513) (prefixPartial 10 23513) = false := by
  decide +kernel

theorem node_context_10_23513_1358936 : EJMOriginalGlobalDAGData.nodes 11 ⟨1358936, by decide⟩ =
    .split (coordinate 10) (![⟨1358876, by decide⟩,⟨1358888, by decide⟩,⟨1358919, by decide⟩,⟨1358935, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23513_1358936 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23513 ⟨1358936, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23513
    ⟨1358936, by decide⟩ (by decide) (![⟨1358876, by decide⟩,⟨1358888, by decide⟩,⟨1358919, by decide⟩,⟨1358935, by decide⟩]) unmarked_context_10_23513_1358936 node_context_10_23513_1358936
  intro a
  fin_cases a
  · exact context_11_94052_1358876
  · exact context_11_94053_1358888
  · exact context_11_94054_1358919
  · exact context_11_94055_1358935

theorem selected_cut_48435 : selected 11 ⟨1358976, by decide⟩
    (prefixPartial 10 23514) = some ⟨10, 2, 0, 1358976, 23514, 2197, 1048576⟩ := by
  decide +kernel

theorem context_10_23514_1358976 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23514 ⟨1358976, by decide⟩ :=
  accepted_of_selected 10 23514 ⟨1358976, by decide⟩ ⟨10, 2, 0, 1358976, 23514, 2197, 1048576⟩
    (by decide) selected_cut_48435

theorem selected_cut_48436 : selected 11 ⟨1359028, by decide⟩
    (prefixPartial 10 23515) = some ⟨10, 2, 0, 1359028, 23515, 2913, 1048576⟩ := by
  decide +kernel

theorem context_10_23515_1359028 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23515 ⟨1359028, by decide⟩ :=
  accepted_of_selected 10 23515 ⟨1359028, by decide⟩ ⟨10, 2, 0, 1359028, 23515, 2913, 1048576⟩
    (by decide) selected_cut_48436

theorem unmarked_context_9_5878_1359029 : frontier 12 ⟨1359029, by decide⟩
    (prefixCache 9 5878) (prefixPartial 9 5878) = false := by
  decide +kernel

theorem node_context_9_5878_1359029 : EJMOriginalGlobalDAGData.nodes 12 ⟨1359029, by decide⟩ =
    .split (coordinate 9) (![⟨1358818, by decide⟩,⟨1358936, by decide⟩,⟨1358976, by decide⟩,⟨1359028, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5878_1359029 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5878 ⟨1359029, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5878
    ⟨1359029, by decide⟩ (by decide) (![⟨1358818, by decide⟩,⟨1358936, by decide⟩,⟨1358976, by decide⟩,⟨1359028, by decide⟩]) unmarked_context_9_5878_1359029 node_context_9_5878_1359029
  intro a
  fin_cases a
  · exact context_10_23512_1358818
  · exact context_10_23513_1358936
  · exact context_10_23514_1358976
  · exact context_10_23515_1359028

theorem selected_cut_48437 : selected 11 ⟨1359083, by decide⟩
    (prefixPartial 10 23516) = some ⟨10, 2, 0, 1359083, 23516, 2793, 1048576⟩ := by
  decide +kernel

theorem context_10_23516_1359083 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23516 ⟨1359083, by decide⟩ :=
  accepted_of_selected 10 23516 ⟨1359083, by decide⟩ ⟨10, 2, 0, 1359083, 23516, 2793, 1048576⟩
    (by decide) selected_cut_48437

theorem selected_cut_48438 : selected 11 ⟨1359113, by decide⟩
    (prefixPartial 10 23517) = some ⟨10, 2, 0, 1359113, 23517, 1453, 1048576⟩ := by
  decide +kernel

theorem context_10_23517_1359113 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23517 ⟨1359113, by decide⟩ :=
  accepted_of_selected 10 23517 ⟨1359113, by decide⟩ ⟨10, 2, 0, 1359113, 23517, 1453, 1048576⟩
    (by decide) selected_cut_48438

theorem selected_cut_48439 : selected 11 ⟨1359141, by decide⟩
    (prefixPartial 10 23518) = some ⟨10, 2, 0, 1359141, 23518, 901, 1048576⟩ := by
  decide +kernel

theorem context_10_23518_1359141 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23518 ⟨1359141, by decide⟩ :=
  accepted_of_selected 10 23518 ⟨1359141, by decide⟩ ⟨10, 2, 0, 1359141, 23518, 901, 1048576⟩
    (by decide) selected_cut_48439

theorem selected_cut_48440 : selected 11 ⟨1359145, by decide⟩
    (prefixPartial 10 23519) = some ⟨10, 2, 0, 1359145, 23519, 141, 1048576⟩ := by
  decide +kernel

theorem context_10_23519_1359145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23519 ⟨1359145, by decide⟩ :=
  accepted_of_selected 10 23519 ⟨1359145, by decide⟩ ⟨10, 2, 0, 1359145, 23519, 141, 1048576⟩
    (by decide) selected_cut_48440

theorem unmarked_context_9_5879_1359146 : frontier 12 ⟨1359146, by decide⟩
    (prefixCache 9 5879) (prefixPartial 9 5879) = false := by
  decide +kernel

theorem node_context_9_5879_1359146 : EJMOriginalGlobalDAGData.nodes 12 ⟨1359146, by decide⟩ =
    .split (coordinate 9) (![⟨1359083, by decide⟩,⟨1359113, by decide⟩,⟨1359141, by decide⟩,⟨1359145, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5879_1359146 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5879 ⟨1359146, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5879
    ⟨1359146, by decide⟩ (by decide) (![⟨1359083, by decide⟩,⟨1359113, by decide⟩,⟨1359141, by decide⟩,⟨1359145, by decide⟩]) unmarked_context_9_5879_1359146 node_context_9_5879_1359146
  intro a
  fin_cases a
  · exact context_10_23516_1359083
  · exact context_10_23517_1359113
  · exact context_10_23518_1359141
  · exact context_10_23519_1359145

theorem unmarked_context_8_1469_1359147 : frontier 13 ⟨1359147, by decide⟩
    (prefixCache 8 1469) (prefixPartial 8 1469) = false := by
  decide +kernel

theorem node_context_8_1469_1359147 : EJMOriginalGlobalDAGData.nodes 13 ⟨1359147, by decide⟩ =
    .split (coordinate 8) (![⟨1358081, by decide⟩,⟨1358654, by decide⟩,⟨1359029, by decide⟩,⟨1359146, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1469_1359147 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1469 ⟨1359147, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1469
    ⟨1359147, by decide⟩ (by decide) (![⟨1358081, by decide⟩,⟨1358654, by decide⟩,⟨1359029, by decide⟩,⟨1359146, by decide⟩]) unmarked_context_8_1469_1359147 node_context_8_1469_1359147
  intro a
  fin_cases a
  · exact context_9_5876_1358081
  · exact context_9_5877_1358654
  · exact context_9_5878_1359029
  · exact context_9_5879_1359146

theorem selected_cut_48441 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 94080) = some ⟨11, 1, 0, 434745, 94080, 1, 262144⟩ := by
  decide +kernel

theorem context_11_94080_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94080 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 94080 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 94080, 1, 262144⟩
    (by decide) selected_cut_48441

theorem selected_cut_48442 : selected 10 ⟨1359216, by decide⟩
    (prefixPartial 11 94081) = some ⟨11, 2, 0, 1359216, 94081, 3685, 262144⟩ := by
  decide +kernel

theorem context_11_94081_1359216 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94081 ⟨1359216, by decide⟩ :=
  accepted_of_selected 11 94081 ⟨1359216, by decide⟩ ⟨11, 2, 0, 1359216, 94081, 3685, 262144⟩
    (by decide) selected_cut_48442

theorem selected_cut_48443 : selected 10 ⟨1359282, by decide⟩
    (prefixPartial 11 94082) = some ⟨11, 2, 0, 1359282, 94082, 3297, 262144⟩ := by
  decide +kernel

theorem context_11_94082_1359282 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94082 ⟨1359282, by decide⟩ :=
  accepted_of_selected 11 94082 ⟨1359282, by decide⟩ ⟨11, 2, 0, 1359282, 94082, 3297, 262144⟩
    (by decide) selected_cut_48443

theorem selected_cut_48444 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 376332) = some ⟨12, 1, 0, 448748, 376332, 1, 65536⟩ := by
  decide +kernel

theorem context_12_376332_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376332 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 376332 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 376332, 1, 65536⟩
    (by decide) selected_cut_48444

theorem selected_cut_48445 : selected 9 ⟨1359353, by decide⟩
    (prefixPartial 12 376333) = some ⟨12, 2, 0, 1359353, 376333, 3357, 65536⟩ := by
  decide +kernel

theorem context_12_376333_1359353 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376333 ⟨1359353, by decide⟩ :=
  accepted_of_selected 12 376333 ⟨1359353, by decide⟩ ⟨12, 2, 0, 1359353, 376333, 3357, 65536⟩
    (by decide) selected_cut_48445

theorem selected_cut_48446 : selected 9 ⟨1359409, by decide⟩
    (prefixPartial 12 376334) = some ⟨12, 2, 0, 1359409, 376334, 3085, 65536⟩ := by
  decide +kernel

theorem context_12_376334_1359409 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376334 ⟨1359409, by decide⟩ :=
  accepted_of_selected 12 376334 ⟨1359409, by decide⟩ ⟨12, 2, 0, 1359409, 376334, 3085, 65536⟩
    (by decide) selected_cut_48446

theorem selected_cut_48447 : selected 9 ⟨1359461, by decide⟩
    (prefixPartial 12 376335) = some ⟨12, 2, 0, 1359461, 376335, 2977, 65536⟩ := by
  decide +kernel

theorem context_12_376335_1359461 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376335 ⟨1359461, by decide⟩ :=
  accepted_of_selected 12 376335 ⟨1359461, by decide⟩ ⟨12, 2, 0, 1359461, 376335, 2977, 65536⟩
    (by decide) selected_cut_48447

theorem unmarked_context_11_94083_1359462 : frontier 10 ⟨1359462, by decide⟩
    (prefixCache 11 94083) (prefixPartial 11 94083) = false := by
  decide +kernel

theorem node_context_11_94083_1359462 : EJMOriginalGlobalDAGData.nodes 10 ⟨1359462, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1359353, by decide⟩,⟨1359409, by decide⟩,⟨1359461, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_94083_1359462 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94083 ⟨1359462, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 94083
    ⟨1359462, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1359353, by decide⟩,⟨1359409, by decide⟩,⟨1359461, by decide⟩]) unmarked_context_11_94083_1359462 node_context_11_94083_1359462
  intro a
  fin_cases a
  · exact context_12_376332_448748
  · exact context_12_376333_1359353
  · exact context_12_376334_1359409
  · exact context_12_376335_1359461

theorem unmarked_context_10_23520_1359463 : frontier 11 ⟨1359463, by decide⟩
    (prefixCache 10 23520) (prefixPartial 10 23520) = false := by
  decide +kernel

theorem node_context_10_23520_1359463 : EJMOriginalGlobalDAGData.nodes 11 ⟨1359463, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨1359216, by decide⟩,⟨1359282, by decide⟩,⟨1359462, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23520_1359463 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23520 ⟨1359463, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23520
    ⟨1359463, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨1359216, by decide⟩,⟨1359282, by decide⟩,⟨1359462, by decide⟩]) unmarked_context_10_23520_1359463 node_context_10_23520_1359463
  intro a
  fin_cases a
  · exact context_11_94080_434745
  · exact context_11_94081_1359216
  · exact context_11_94082_1359282
  · exact context_11_94083_1359462

theorem selected_cut_48448 : selected 9 ⟨1255011, by decide⟩
    (prefixPartial 12 376336) = some ⟨12, 1, 0, 1255011, 376336, 1, 65536⟩ := by
  decide +kernel

theorem context_12_376336_1255011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376336 ⟨1255011, by decide⟩ :=
  accepted_of_selected 12 376336 ⟨1255011, by decide⟩ ⟨12, 1, 0, 1255011, 376336, 1, 65536⟩
    (by decide) selected_cut_48448

theorem selected_cut_48449 : selected 9 ⟨1359515, by decide⟩
    (prefixPartial 12 376337) = some ⟨12, 2, 0, 1359515, 376337, 3221, 65536⟩ := by
  decide +kernel

theorem context_12_376337_1359515 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376337 ⟨1359515, by decide⟩ :=
  accepted_of_selected 12 376337 ⟨1359515, by decide⟩ ⟨12, 2, 0, 1359515, 376337, 3221, 65536⟩
    (by decide) selected_cut_48449

theorem selected_cut_48450 : selected 9 ⟨1359577, by decide⟩
    (prefixPartial 12 376338) = some ⟨12, 2, 0, 1359577, 376338, 3009, 65536⟩ := by
  decide +kernel

theorem context_12_376338_1359577 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376338 ⟨1359577, by decide⟩ :=
  accepted_of_selected 12 376338 ⟨1359577, by decide⟩ ⟨12, 2, 0, 1359577, 376338, 3009, 65536⟩
    (by decide) selected_cut_48450

theorem selected_cut_48451 : selected 9 ⟨1359628, by decide⟩
    (prefixPartial 12 376339) = some ⟨12, 2, 0, 1359628, 376339, 3253, 65536⟩ := by
  decide +kernel

theorem context_12_376339_1359628 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376339 ⟨1359628, by decide⟩ :=
  accepted_of_selected 12 376339 ⟨1359628, by decide⟩ ⟨12, 2, 0, 1359628, 376339, 3253, 65536⟩
    (by decide) selected_cut_48451

theorem unmarked_context_11_94084_1359629 : frontier 10 ⟨1359629, by decide⟩
    (prefixCache 11 94084) (prefixPartial 11 94084) = false := by
  decide +kernel

theorem node_context_11_94084_1359629 : EJMOriginalGlobalDAGData.nodes 10 ⟨1359629, by decide⟩ =
    .split (coordinate 11) (![⟨1255011, by decide⟩,⟨1359515, by decide⟩,⟨1359577, by decide⟩,⟨1359628, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_94084_1359629 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94084 ⟨1359629, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 94084
    ⟨1359629, by decide⟩ (by decide) (![⟨1255011, by decide⟩,⟨1359515, by decide⟩,⟨1359577, by decide⟩,⟨1359628, by decide⟩]) unmarked_context_11_94084_1359629 node_context_11_94084_1359629
  intro a
  fin_cases a
  · exact context_12_376336_1255011
  · exact context_12_376337_1359515
  · exact context_12_376338_1359577
  · exact context_12_376339_1359628

theorem selected_cut_48452 : selected 9 ⟨1359682, by decide⟩
    (prefixPartial 12 376340) = some ⟨12, 2, 0, 1359682, 376340, 3305, 65536⟩ := by
  decide +kernel

theorem context_12_376340_1359682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376340 ⟨1359682, by decide⟩ :=
  accepted_of_selected 12 376340 ⟨1359682, by decide⟩ ⟨12, 2, 0, 1359682, 376340, 3305, 65536⟩
    (by decide) selected_cut_48452

theorem selected_cut_48453 : selected 9 ⟨1172003, by decide⟩
    (prefixPartial 12 376341) = some ⟨12, 1, 0, 1172003, 376341, 1, 65536⟩ := by
  decide +kernel

theorem context_12_376341_1172003 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376341 ⟨1172003, by decide⟩ :=
  accepted_of_selected 12 376341 ⟨1172003, by decide⟩ ⟨12, 1, 0, 1172003, 376341, 1, 65536⟩
    (by decide) selected_cut_48453

theorem selected_cut_48454 : selected 9 ⟨1359738, by decide⟩
    (prefixPartial 12 376342) = some ⟨12, 2, 0, 1359738, 376342, 3241, 65536⟩ := by
  decide +kernel

theorem context_12_376342_1359738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376342 ⟨1359738, by decide⟩ :=
  accepted_of_selected 12 376342 ⟨1359738, by decide⟩ ⟨12, 2, 0, 1359738, 376342, 3241, 65536⟩
    (by decide) selected_cut_48454

theorem selected_cut_48455 : selected 9 ⟨979367, by decide⟩
    (prefixPartial 12 376343) = some ⟨12, 1, 0, 979367, 376343, 1, 65536⟩ := by
  decide +kernel

theorem context_12_376343_979367 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376343 ⟨979367, by decide⟩ :=
  accepted_of_selected 12 376343 ⟨979367, by decide⟩ ⟨12, 1, 0, 979367, 376343, 1, 65536⟩
    (by decide) selected_cut_48455

theorem unmarked_context_11_94085_1359739 : frontier 10 ⟨1359739, by decide⟩
    (prefixCache 11 94085) (prefixPartial 11 94085) = false := by
  decide +kernel

theorem node_context_11_94085_1359739 : EJMOriginalGlobalDAGData.nodes 10 ⟨1359739, by decide⟩ =
    .split (coordinate 11) (![⟨1359682, by decide⟩,⟨1172003, by decide⟩,⟨1359738, by decide⟩,⟨979367, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_94085_1359739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94085 ⟨1359739, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 94085
    ⟨1359739, by decide⟩ (by decide) (![⟨1359682, by decide⟩,⟨1172003, by decide⟩,⟨1359738, by decide⟩,⟨979367, by decide⟩]) unmarked_context_11_94085_1359739 node_context_11_94085_1359739
  intro a
  fin_cases a
  · exact context_12_376340_1359682
  · exact context_12_376341_1172003
  · exact context_12_376342_1359738
  · exact context_12_376343_979367

theorem selected_cut_48456 : selected 9 ⟨994572, by decide⟩
    (prefixPartial 12 376344) = some ⟨12, 1, 0, 994572, 376344, 1, 65536⟩ := by
  decide +kernel

theorem context_12_376344_994572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376344 ⟨994572, by decide⟩ :=
  accepted_of_selected 12 376344 ⟨994572, by decide⟩ ⟨12, 1, 0, 994572, 376344, 1, 65536⟩
    (by decide) selected_cut_48456

theorem selected_cut_48457 : selected 9 ⟨1359781, by decide⟩
    (prefixPartial 12 376345) = some ⟨12, 2, 0, 1359781, 376345, 2809, 65536⟩ := by
  decide +kernel

theorem context_12_376345_1359781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376345 ⟨1359781, by decide⟩ :=
  accepted_of_selected 12 376345 ⟨1359781, by decide⟩ ⟨12, 2, 0, 1359781, 376345, 2809, 65536⟩
    (by decide) selected_cut_48457

theorem selected_cut_48458 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 376346) = some ⟨12, 1, 0, 893903, 376346, 1, 65536⟩ := by
  decide +kernel

theorem context_12_376346_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376346 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 376346 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 376346, 1, 65536⟩
    (by decide) selected_cut_48458

theorem selected_cut_48459 : selected 9 ⟨1359827, by decide⟩
    (prefixPartial 12 376347) = some ⟨12, 2, 0, 1359827, 376347, 3033, 65536⟩ := by
  decide +kernel

theorem context_12_376347_1359827 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376347 ⟨1359827, by decide⟩ :=
  accepted_of_selected 12 376347 ⟨1359827, by decide⟩ ⟨12, 2, 0, 1359827, 376347, 3033, 65536⟩
    (by decide) selected_cut_48459

theorem unmarked_context_11_94086_1359828 : frontier 10 ⟨1359828, by decide⟩
    (prefixCache 11 94086) (prefixPartial 11 94086) = false := by
  decide +kernel

theorem node_context_11_94086_1359828 : EJMOriginalGlobalDAGData.nodes 10 ⟨1359828, by decide⟩ =
    .split (coordinate 11) (![⟨994572, by decide⟩,⟨1359781, by decide⟩,⟨893903, by decide⟩,⟨1359827, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_94086_1359828 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94086 ⟨1359828, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 94086
    ⟨1359828, by decide⟩ (by decide) (![⟨994572, by decide⟩,⟨1359781, by decide⟩,⟨893903, by decide⟩,⟨1359827, by decide⟩]) unmarked_context_11_94086_1359828 node_context_11_94086_1359828
  intro a
  fin_cases a
  · exact context_12_376344_994572
  · exact context_12_376345_1359781
  · exact context_12_376346_893903
  · exact context_12_376347_1359827

theorem selected_cut_48460 : selected 9 ⟨1359877, by decide⟩
    (prefixPartial 12 376348) = some ⟨12, 2, 0, 1359877, 376348, 2789, 65536⟩ := by
  decide +kernel

theorem context_12_376348_1359877 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376348 ⟨1359877, by decide⟩ :=
  accepted_of_selected 12 376348 ⟨1359877, by decide⟩ ⟨12, 2, 0, 1359877, 376348, 2789, 65536⟩
    (by decide) selected_cut_48460

theorem selected_cut_48461 : selected 9 ⟨1359925, by decide⟩
    (prefixPartial 12 376349) = some ⟨12, 2, 0, 1359925, 376349, 2833, 65536⟩ := by
  decide +kernel

theorem context_12_376349_1359925 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376349 ⟨1359925, by decide⟩ :=
  accepted_of_selected 12 376349 ⟨1359925, by decide⟩ ⟨12, 2, 0, 1359925, 376349, 2833, 65536⟩
    (by decide) selected_cut_48461

theorem selected_cut_48462 : selected 9 ⟨1359970, by decide⟩
    (prefixPartial 12 376350) = some ⟨12, 2, 0, 1359970, 376350, 2453, 65536⟩ := by
  decide +kernel

theorem context_12_376350_1359970 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376350 ⟨1359970, by decide⟩ :=
  accepted_of_selected 12 376350 ⟨1359970, by decide⟩ ⟨12, 2, 0, 1359970, 376350, 2453, 65536⟩
    (by decide) selected_cut_48462

theorem selected_cut_48463 : selected 9 ⟨1360023, by decide⟩
    (prefixPartial 12 376351) = some ⟨12, 2, 0, 1360023, 376351, 2601, 65536⟩ := by
  decide +kernel

theorem context_12_376351_1360023 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376351 ⟨1360023, by decide⟩ :=
  accepted_of_selected 12 376351 ⟨1360023, by decide⟩ ⟨12, 2, 0, 1360023, 376351, 2601, 65536⟩
    (by decide) selected_cut_48463

theorem unmarked_context_11_94087_1360024 : frontier 10 ⟨1360024, by decide⟩
    (prefixCache 11 94087) (prefixPartial 11 94087) = false := by
  decide +kernel

theorem node_context_11_94087_1360024 : EJMOriginalGlobalDAGData.nodes 10 ⟨1360024, by decide⟩ =
    .split (coordinate 11) (![⟨1359877, by decide⟩,⟨1359925, by decide⟩,⟨1359970, by decide⟩,⟨1360023, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_94087_1360024 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94087 ⟨1360024, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 94087
    ⟨1360024, by decide⟩ (by decide) (![⟨1359877, by decide⟩,⟨1359925, by decide⟩,⟨1359970, by decide⟩,⟨1360023, by decide⟩]) unmarked_context_11_94087_1360024 node_context_11_94087_1360024
  intro a
  fin_cases a
  · exact context_12_376348_1359877
  · exact context_12_376349_1359925
  · exact context_12_376350_1359970
  · exact context_12_376351_1360023

theorem unmarked_context_10_23521_1360025 : frontier 11 ⟨1360025, by decide⟩
    (prefixCache 10 23521) (prefixPartial 10 23521) = false := by
  decide +kernel

theorem node_context_10_23521_1360025 : EJMOriginalGlobalDAGData.nodes 11 ⟨1360025, by decide⟩ =
    .split (coordinate 10) (![⟨1359629, by decide⟩,⟨1359739, by decide⟩,⟨1359828, by decide⟩,⟨1360024, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23521_1360025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23521 ⟨1360025, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23521
    ⟨1360025, by decide⟩ (by decide) (![⟨1359629, by decide⟩,⟨1359739, by decide⟩,⟨1359828, by decide⟩,⟨1360024, by decide⟩]) unmarked_context_10_23521_1360025 node_context_10_23521_1360025
  intro a
  fin_cases a
  · exact context_11_94084_1359629
  · exact context_11_94085_1359739
  · exact context_11_94086_1359828
  · exact context_11_94087_1360024

theorem selected_cut_48464 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 376352) = some ⟨12, 1, 0, 435790, 376352, 1, 65536⟩ := by
  decide +kernel

theorem context_12_376352_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376352 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 376352 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 376352, 1, 65536⟩
    (by decide) selected_cut_48464

theorem selected_cut_48465 : selected 9 ⟨1360069, by decide⟩
    (prefixPartial 12 376353) = some ⟨12, 2, 0, 1360069, 376353, 2629, 65536⟩ := by
  decide +kernel

theorem context_12_376353_1360069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376353 ⟨1360069, by decide⟩ :=
  accepted_of_selected 12 376353 ⟨1360069, by decide⟩ ⟨12, 2, 0, 1360069, 376353, 2629, 65536⟩
    (by decide) selected_cut_48465

theorem selected_cut_48466 : selected 9 ⟨1360113, by decide⟩
    (prefixPartial 12 376354) = some ⟨12, 2, 0, 1360113, 376354, 2533, 65536⟩ := by
  decide +kernel

theorem context_12_376354_1360113 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376354 ⟨1360113, by decide⟩ :=
  accepted_of_selected 12 376354 ⟨1360113, by decide⟩ ⟨12, 2, 0, 1360113, 376354, 2533, 65536⟩
    (by decide) selected_cut_48466

theorem selected_cut_48467 : selected 9 ⟨1360160, by decide⟩
    (prefixPartial 12 376355) = some ⟨12, 2, 0, 1360160, 376355, 2605, 65536⟩ := by
  decide +kernel

theorem context_12_376355_1360160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376355 ⟨1360160, by decide⟩ :=
  accepted_of_selected 12 376355 ⟨1360160, by decide⟩ ⟨12, 2, 0, 1360160, 376355, 2605, 65536⟩
    (by decide) selected_cut_48467

theorem unmarked_context_11_94088_1360161 : frontier 10 ⟨1360161, by decide⟩
    (prefixCache 11 94088) (prefixPartial 11 94088) = false := by
  decide +kernel

theorem node_context_11_94088_1360161 : EJMOriginalGlobalDAGData.nodes 10 ⟨1360161, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨1360069, by decide⟩,⟨1360113, by decide⟩,⟨1360160, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_94088_1360161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94088 ⟨1360161, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 94088
    ⟨1360161, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨1360069, by decide⟩,⟨1360113, by decide⟩,⟨1360160, by decide⟩]) unmarked_context_11_94088_1360161 node_context_11_94088_1360161
  intro a
  fin_cases a
  · exact context_12_376352_435790
  · exact context_12_376353_1360069
  · exact context_12_376354_1360113
  · exact context_12_376355_1360160

theorem selected_cut_48468 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 376356) = some ⟨12, 1, 0, 435790, 376356, 1, 65536⟩ := by
  decide +kernel

theorem context_12_376356_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376356 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 376356 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 376356, 1, 65536⟩
    (by decide) selected_cut_48468

theorem selected_cut_48469 : selected 9 ⟨366744, by decide⟩
    (prefixPartial 12 376357) = some ⟨12, 1, 0, 366744, 376357, 1, 65536⟩ := by
  decide +kernel

theorem context_12_376357_366744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376357 ⟨366744, by decide⟩ :=
  accepted_of_selected 12 376357 ⟨366744, by decide⟩ ⟨12, 1, 0, 366744, 376357, 1, 65536⟩
    (by decide) selected_cut_48469

theorem selected_cut_48470 : selected 9 ⟨1360205, by decide⟩
    (prefixPartial 12 376358) = some ⟨12, 2, 0, 1360205, 376358, 2761, 65536⟩ := by
  decide +kernel

theorem context_12_376358_1360205 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376358 ⟨1360205, by decide⟩ :=
  accepted_of_selected 12 376358 ⟨1360205, by decide⟩ ⟨12, 2, 0, 1360205, 376358, 2761, 65536⟩
    (by decide) selected_cut_48470

theorem selected_cut_48471 : selected 9 ⟨1360265, by decide⟩
    (prefixPartial 12 376359) = some ⟨12, 2, 0, 1360265, 376359, 2765, 65536⟩ := by
  decide +kernel

theorem context_12_376359_1360265 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376359 ⟨1360265, by decide⟩ :=
  accepted_of_selected 12 376359 ⟨1360265, by decide⟩ ⟨12, 2, 0, 1360265, 376359, 2765, 65536⟩
    (by decide) selected_cut_48471

theorem unmarked_context_11_94089_1360266 : frontier 10 ⟨1360266, by decide⟩
    (prefixCache 11 94089) (prefixPartial 11 94089) = false := by
  decide +kernel

theorem node_context_11_94089_1360266 : EJMOriginalGlobalDAGData.nodes 10 ⟨1360266, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨366744, by decide⟩,⟨1360205, by decide⟩,⟨1360265, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_94089_1360266 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94089 ⟨1360266, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 94089
    ⟨1360266, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨366744, by decide⟩,⟨1360205, by decide⟩,⟨1360265, by decide⟩]) unmarked_context_11_94089_1360266 node_context_11_94089_1360266
  intro a
  fin_cases a
  · exact context_12_376356_435790
  · exact context_12_376357_366744
  · exact context_12_376358_1360205
  · exact context_12_376359_1360265

theorem selected_cut_48472 : selected 10 ⟨1360305, by decide⟩
    (prefixPartial 11 94090) = some ⟨11, 2, 0, 1360305, 94090, 2377, 262144⟩ := by
  decide +kernel

theorem context_11_94090_1360305 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94090 ⟨1360305, by decide⟩ :=
  accepted_of_selected 11 94090 ⟨1360305, by decide⟩ ⟨11, 2, 0, 1360305, 94090, 2377, 262144⟩
    (by decide) selected_cut_48472

theorem selected_cut_48473 : selected 9 ⟨450498, by decide⟩
    (prefixPartial 12 376364) = some ⟨12, 1, 0, 450498, 376364, 1, 65536⟩ := by
  decide +kernel

theorem context_12_376364_450498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376364 ⟨450498, by decide⟩ :=
  accepted_of_selected 12 376364 ⟨450498, by decide⟩ ⟨12, 1, 0, 450498, 376364, 1, 65536⟩
    (by decide) selected_cut_48473

theorem selected_cut_48474 : selected 9 ⟨1360339, by decide⟩
    (prefixPartial 12 376365) = some ⟨12, 2, 0, 1360339, 376365, 2537, 65536⟩ := by
  decide +kernel

theorem context_12_376365_1360339 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376365 ⟨1360339, by decide⟩ :=
  accepted_of_selected 12 376365 ⟨1360339, by decide⟩ ⟨12, 2, 0, 1360339, 376365, 2537, 65536⟩
    (by decide) selected_cut_48474

theorem selected_cut_48475 : selected 9 ⟨1360377, by decide⟩
    (prefixPartial 12 376366) = some ⟨12, 2, 0, 1360377, 376366, 2269, 65536⟩ := by
  decide +kernel

theorem context_12_376366_1360377 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376366 ⟨1360377, by decide⟩ :=
  accepted_of_selected 12 376366 ⟨1360377, by decide⟩ ⟨12, 2, 0, 1360377, 376366, 2269, 65536⟩
    (by decide) selected_cut_48475

theorem selected_cut_48476 : selected 9 ⟨758968, by decide⟩
    (prefixPartial 12 376367) = some ⟨12, 1, 0, 758968, 376367, 1, 65536⟩ := by
  decide +kernel

theorem context_12_376367_758968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376367 ⟨758968, by decide⟩ :=
  accepted_of_selected 12 376367 ⟨758968, by decide⟩ ⟨12, 1, 0, 758968, 376367, 1, 65536⟩
    (by decide) selected_cut_48476

theorem unmarked_context_11_94091_1360378 : frontier 10 ⟨1360378, by decide⟩
    (prefixCache 11 94091) (prefixPartial 11 94091) = false := by
  decide +kernel

theorem node_context_11_94091_1360378 : EJMOriginalGlobalDAGData.nodes 10 ⟨1360378, by decide⟩ =
    .split (coordinate 11) (![⟨450498, by decide⟩,⟨1360339, by decide⟩,⟨1360377, by decide⟩,⟨758968, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_94091_1360378 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94091 ⟨1360378, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 94091
    ⟨1360378, by decide⟩ (by decide) (![⟨450498, by decide⟩,⟨1360339, by decide⟩,⟨1360377, by decide⟩,⟨758968, by decide⟩]) unmarked_context_11_94091_1360378 node_context_11_94091_1360378
  intro a
  fin_cases a
  · exact context_12_376364_450498
  · exact context_12_376365_1360339
  · exact context_12_376366_1360377
  · exact context_12_376367_758968

theorem unmarked_context_10_23522_1360379 : frontier 11 ⟨1360379, by decide⟩
    (prefixCache 10 23522) (prefixPartial 10 23522) = false := by
  decide +kernel

theorem node_context_10_23522_1360379 : EJMOriginalGlobalDAGData.nodes 11 ⟨1360379, by decide⟩ =
    .split (coordinate 10) (![⟨1360161, by decide⟩,⟨1360266, by decide⟩,⟨1360305, by decide⟩,⟨1360378, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23522_1360379 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23522 ⟨1360379, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23522
    ⟨1360379, by decide⟩ (by decide) (![⟨1360161, by decide⟩,⟨1360266, by decide⟩,⟨1360305, by decide⟩,⟨1360378, by decide⟩]) unmarked_context_10_23522_1360379 node_context_10_23522_1360379
  intro a
  fin_cases a
  · exact context_11_94088_1360161
  · exact context_11_94089_1360266
  · exact context_11_94090_1360305
  · exact context_11_94091_1360378

theorem selected_cut_48477 : selected 9 ⟨1255011, by decide⟩
    (prefixPartial 12 376368) = some ⟨12, 1, 0, 1255011, 376368, 1, 65536⟩ := by
  decide +kernel

theorem context_12_376368_1255011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376368 ⟨1255011, by decide⟩ :=
  accepted_of_selected 12 376368 ⟨1255011, by decide⟩ ⟨12, 1, 0, 1255011, 376368, 1, 65536⟩
    (by decide) selected_cut_48477

theorem selected_cut_48478 : selected 9 ⟨1360410, by decide⟩
    (prefixPartial 12 376369) = some ⟨12, 2, 0, 1360410, 376369, 2081, 65536⟩ := by
  decide +kernel

theorem context_12_376369_1360410 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376369 ⟨1360410, by decide⟩ :=
  accepted_of_selected 12 376369 ⟨1360410, by decide⟩ ⟨12, 2, 0, 1360410, 376369, 2081, 65536⟩
    (by decide) selected_cut_48478

theorem selected_cut_48479 : selected 9 ⟨1360445, by decide⟩
    (prefixPartial 12 376370) = some ⟨12, 2, 0, 1360445, 376370, 2129, 65536⟩ := by
  decide +kernel

theorem context_12_376370_1360445 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376370 ⟨1360445, by decide⟩ :=
  accepted_of_selected 12 376370 ⟨1360445, by decide⟩ ⟨12, 2, 0, 1360445, 376370, 2129, 65536⟩
    (by decide) selected_cut_48479

theorem selected_cut_48480 : selected 9 ⟨1360478, by decide⟩
    (prefixPartial 12 376371) = some ⟨12, 2, 0, 1360478, 376371, 2065, 65536⟩ := by
  decide +kernel

theorem context_12_376371_1360478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376371 ⟨1360478, by decide⟩ :=
  accepted_of_selected 12 376371 ⟨1360478, by decide⟩ ⟨12, 2, 0, 1360478, 376371, 2065, 65536⟩
    (by decide) selected_cut_48480

theorem unmarked_context_11_94092_1360479 : frontier 10 ⟨1360479, by decide⟩
    (prefixCache 11 94092) (prefixPartial 11 94092) = false := by
  decide +kernel

theorem node_context_11_94092_1360479 : EJMOriginalGlobalDAGData.nodes 10 ⟨1360479, by decide⟩ =
    .split (coordinate 11) (![⟨1255011, by decide⟩,⟨1360410, by decide⟩,⟨1360445, by decide⟩,⟨1360478, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_94092_1360479 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94092 ⟨1360479, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 94092
    ⟨1360479, by decide⟩ (by decide) (![⟨1255011, by decide⟩,⟨1360410, by decide⟩,⟨1360445, by decide⟩,⟨1360478, by decide⟩]) unmarked_context_11_94092_1360479 node_context_11_94092_1360479
  intro a
  fin_cases a
  · exact context_12_376368_1255011
  · exact context_12_376369_1360410
  · exact context_12_376370_1360445
  · exact context_12_376371_1360478

theorem selected_cut_48481 : selected 9 ⟨1360528, by decide⟩
    (prefixPartial 12 376372) = some ⟨12, 2, 0, 1360528, 376372, 2441, 65536⟩ := by
  decide +kernel

theorem context_12_376372_1360528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376372 ⟨1360528, by decide⟩ :=
  accepted_of_selected 12 376372 ⟨1360528, by decide⟩ ⟨12, 2, 0, 1360528, 376372, 2441, 65536⟩
    (by decide) selected_cut_48481

theorem selected_cut_48482 : selected 9 ⟨1360565, by decide⟩
    (prefixPartial 12 376373) = some ⟨12, 2, 0, 1360565, 376373, 2245, 65536⟩ := by
  decide +kernel

theorem context_12_376373_1360565 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376373 ⟨1360565, by decide⟩ :=
  accepted_of_selected 12 376373 ⟨1360565, by decide⟩ ⟨12, 2, 0, 1360565, 376373, 2245, 65536⟩
    (by decide) selected_cut_48482

theorem selected_cut_48483 : selected 9 ⟨1360606, by decide⟩
    (prefixPartial 12 376374) = some ⟨12, 2, 0, 1360606, 376374, 2249, 65536⟩ := by
  decide +kernel

theorem context_12_376374_1360606 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376374 ⟨1360606, by decide⟩ :=
  accepted_of_selected 12 376374 ⟨1360606, by decide⟩ ⟨12, 2, 0, 1360606, 376374, 2249, 65536⟩
    (by decide) selected_cut_48483

theorem selected_cut_48484 : selected 9 ⟨1360646, by decide⟩
    (prefixPartial 12 376375) = some ⟨12, 2, 0, 1360646, 376375, 2065, 65536⟩ := by
  decide +kernel

theorem context_12_376375_1360646 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376375 ⟨1360646, by decide⟩ :=
  accepted_of_selected 12 376375 ⟨1360646, by decide⟩ ⟨12, 2, 0, 1360646, 376375, 2065, 65536⟩
    (by decide) selected_cut_48484

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
