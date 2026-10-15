/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover511
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_49155 : selected 11 ⟨1388740, by decide⟩
    (prefixPartial 10 25386) = some ⟨10, 2, 0, 1388740, 25386, 973, 1048576⟩ := by
  decide +kernel

theorem context_10_25386_1388740 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25386 ⟨1388740, by decide⟩ :=
  accepted_of_selected 10 25386 ⟨1388740, by decide⟩ ⟨10, 2, 0, 1388740, 25386, 973, 1048576⟩
    (by decide) selected_cut_49155

theorem selected_cut_49156 : selected 11 ⟨1388839, by decide⟩
    (prefixPartial 10 25387) = some ⟨10, 2, 0, 1388839, 25387, 3961, 1048576⟩ := by
  decide +kernel

theorem context_10_25387_1388839 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25387 ⟨1388839, by decide⟩ :=
  accepted_of_selected 10 25387 ⟨1388839, by decide⟩ ⟨10, 2, 0, 1388839, 25387, 3961, 1048576⟩
    (by decide) selected_cut_49156

theorem unmarked_context_9_6346_1388840 : frontier 12 ⟨1388840, by decide⟩
    (prefixCache 9 6346) (prefixPartial 9 6346) = false := by
  decide +kernel

theorem node_context_9_6346_1388840 : EJMOriginalGlobalDAGData.nodes 12 ⟨1388840, by decide⟩ =
    .split (coordinate 9) (![⟨1388601, by decide⟩,⟨1388720, by decide⟩,⟨1388740, by decide⟩,⟨1388839, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6346_1388840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6346 ⟨1388840, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6346
    ⟨1388840, by decide⟩ (by decide) (![⟨1388601, by decide⟩,⟨1388720, by decide⟩,⟨1388740, by decide⟩,⟨1388839, by decide⟩]) unmarked_context_9_6346_1388840 node_context_9_6346_1388840
  intro a
  fin_cases a
  · exact context_10_25384_1388601
  · exact context_10_25385_1388720
  · exact context_10_25386_1388740
  · exact context_10_25387_1388839

theorem selected_cut_49157 : selected 11 ⟨1388897, by decide⟩
    (prefixPartial 10 25388) = some ⟨10, 2, 0, 1388897, 25388, 2413, 1048576⟩ := by
  decide +kernel

theorem context_10_25388_1388897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25388 ⟨1388897, by decide⟩ :=
  accepted_of_selected 10 25388 ⟨1388897, by decide⟩ ⟨10, 2, 0, 1388897, 25388, 2413, 1048576⟩
    (by decide) selected_cut_49157

theorem selected_cut_49158 : selected 11 ⟨1388940, by decide⟩
    (prefixPartial 10 25389) = some ⟨10, 2, 0, 1388940, 25389, 1737, 1048576⟩ := by
  decide +kernel

theorem context_10_25389_1388940 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25389 ⟨1388940, by decide⟩ :=
  accepted_of_selected 10 25389 ⟨1388940, by decide⟩ ⟨10, 2, 0, 1388940, 25389, 1737, 1048576⟩
    (by decide) selected_cut_49158

theorem selected_cut_49159 : selected 11 ⟨1388978, by decide⟩
    (prefixPartial 10 25390) = some ⟨10, 2, 0, 1388978, 25390, 877, 1048576⟩ := by
  decide +kernel

theorem context_10_25390_1388978 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25390 ⟨1388978, by decide⟩ :=
  accepted_of_selected 10 25390 ⟨1388978, by decide⟩ ⟨10, 2, 0, 1388978, 25390, 877, 1048576⟩
    (by decide) selected_cut_49159

theorem selected_cut_49160 : selected 11 ⟨1388987, by decide⟩
    (prefixPartial 10 25391) = some ⟨10, 2, 0, 1388987, 25391, 69, 1048576⟩ := by
  decide +kernel

theorem context_10_25391_1388987 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25391 ⟨1388987, by decide⟩ :=
  accepted_of_selected 10 25391 ⟨1388987, by decide⟩ ⟨10, 2, 0, 1388987, 25391, 69, 1048576⟩
    (by decide) selected_cut_49160

theorem unmarked_context_9_6347_1388988 : frontier 12 ⟨1388988, by decide⟩
    (prefixCache 9 6347) (prefixPartial 9 6347) = false := by
  decide +kernel

theorem node_context_9_6347_1388988 : EJMOriginalGlobalDAGData.nodes 12 ⟨1388988, by decide⟩ =
    .split (coordinate 9) (![⟨1388897, by decide⟩,⟨1388940, by decide⟩,⟨1388978, by decide⟩,⟨1388987, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6347_1388988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6347 ⟨1388988, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6347
    ⟨1388988, by decide⟩ (by decide) (![⟨1388897, by decide⟩,⟨1388940, by decide⟩,⟨1388978, by decide⟩,⟨1388987, by decide⟩]) unmarked_context_9_6347_1388988 node_context_9_6347_1388988
  intro a
  fin_cases a
  · exact context_10_25388_1388897
  · exact context_10_25389_1388940
  · exact context_10_25390_1388978
  · exact context_10_25391_1388987

theorem unmarked_context_8_1586_1388989 : frontier 13 ⟨1388989, by decide⟩
    (prefixCache 8 1586) (prefixPartial 8 1586) = false := by
  decide +kernel

theorem node_context_8_1586_1388989 : EJMOriginalGlobalDAGData.nodes 13 ⟨1388989, by decide⟩ =
    .split (coordinate 8) (![⟨1387937, by decide⟩,⟨1388494, by decide⟩,⟨1388840, by decide⟩,⟨1388988, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1586_1388989 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1586 ⟨1388989, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1586
    ⟨1388989, by decide⟩ (by decide) (![⟨1387937, by decide⟩,⟨1388494, by decide⟩,⟨1388840, by decide⟩,⟨1388988, by decide⟩]) unmarked_context_8_1586_1388989 node_context_8_1586_1388989
  intro a
  fin_cases a
  · exact context_9_6344_1387937
  · exact context_9_6345_1388494
  · exact context_9_6346_1388840
  · exact context_9_6347_1388988

theorem selected_cut_49161 : selected 13 ⟨814757, by decide⟩
    (prefixPartial 8 1587) = some ⟨8, 1, 0, 814757, 1587, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_1587_814757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1587 ⟨814757, by decide⟩ :=
  accepted_of_selected 8 1587 ⟨814757, by decide⟩ ⟨8, 1, 0, 814757, 1587, 1, 16777216⟩
    (by decide) selected_cut_49161

theorem unmarked_context_7_396_1388990 : frontier 14 ⟨1388990, by decide⟩
    (prefixCache 7 396) (prefixPartial 7 396) = false := by
  decide +kernel

theorem node_context_7_396_1388990 : EJMOriginalGlobalDAGData.nodes 14 ⟨1388990, by decide⟩ =
    .split (coordinate 7) (![⟨1385583, by decide⟩,⟨1386969, by decide⟩,⟨1388989, by decide⟩,⟨814757, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_396_1388990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 396 ⟨1388990, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 396
    ⟨1388990, by decide⟩ (by decide) (![⟨1385583, by decide⟩,⟨1386969, by decide⟩,⟨1388989, by decide⟩,⟨814757, by decide⟩]) unmarked_context_7_396_1388990 node_context_7_396_1388990
  intro a
  fin_cases a
  · exact context_8_1584_1385583
  · exact context_8_1585_1386969
  · exact context_8_1586_1388989
  · exact context_8_1587_814757

theorem selected_cut_49162 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 101632) = some ⟨11, 1, 0, 434745, 101632, 1, 262144⟩ := by
  decide +kernel

theorem context_11_101632_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101632 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 101632 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 101632, 1, 262144⟩
    (by decide) selected_cut_49162

theorem selected_cut_49163 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 101633) = some ⟨11, 1, 0, 434745, 101633, 1, 262144⟩ := by
  decide +kernel

theorem context_11_101633_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101633 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 101633 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 101633, 1, 262144⟩
    (by decide) selected_cut_49163

theorem selected_cut_49164 : selected 10 ⟨1389042, by decide⟩
    (prefixPartial 11 101634) = some ⟨11, 2, 0, 1389042, 101634, 1213, 262144⟩ := by
  decide +kernel

theorem context_11_101634_1389042 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101634 ⟨1389042, by decide⟩ :=
  accepted_of_selected 11 101634 ⟨1389042, by decide⟩ ⟨11, 2, 0, 1389042, 101634, 1213, 262144⟩
    (by decide) selected_cut_49164

theorem selected_cut_49165 : selected 10 ⟨1389148, by decide⟩
    (prefixPartial 11 101635) = some ⟨11, 2, 0, 1389148, 101635, 2901, 262144⟩ := by
  decide +kernel

theorem context_11_101635_1389148 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101635 ⟨1389148, by decide⟩ :=
  accepted_of_selected 11 101635 ⟨1389148, by decide⟩ ⟨11, 2, 0, 1389148, 101635, 2901, 262144⟩
    (by decide) selected_cut_49165

theorem unmarked_context_10_25408_1389149 : frontier 11 ⟨1389149, by decide⟩
    (prefixCache 10 25408) (prefixPartial 10 25408) = false := by
  decide +kernel

theorem node_context_10_25408_1389149 : EJMOriginalGlobalDAGData.nodes 11 ⟨1389149, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨434745, by decide⟩,⟨1389042, by decide⟩,⟨1389148, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25408_1389149 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25408 ⟨1389149, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25408
    ⟨1389149, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨434745, by decide⟩,⟨1389042, by decide⟩,⟨1389148, by decide⟩]) unmarked_context_10_25408_1389149 node_context_10_25408_1389149
  intro a
  fin_cases a
  · exact context_11_101632_434745
  · exact context_11_101633_434745
  · exact context_11_101634_1389042
  · exact context_11_101635_1389148

theorem selected_cut_49166 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 406544) = some ⟨12, 1, 0, 1108174, 406544, 1, 65536⟩ := by
  decide +kernel

theorem context_12_406544_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406544 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 406544 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 406544, 1, 65536⟩
    (by decide) selected_cut_49166

theorem selected_cut_49167 : selected 9 ⟨1389200, by decide⟩
    (prefixPartial 12 406545) = some ⟨12, 2, 0, 1389200, 406545, 2109, 65536⟩ := by
  decide +kernel

theorem context_12_406545_1389200 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406545 ⟨1389200, by decide⟩ :=
  accepted_of_selected 12 406545 ⟨1389200, by decide⟩ ⟨12, 2, 0, 1389200, 406545, 2109, 65536⟩
    (by decide) selected_cut_49167

theorem selected_cut_49168 : selected 9 ⟨1389259, by decide⟩
    (prefixPartial 12 406546) = some ⟨12, 2, 0, 1389259, 406546, 2377, 65536⟩ := by
  decide +kernel

theorem context_12_406546_1389259 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406546 ⟨1389259, by decide⟩ :=
  accepted_of_selected 12 406546 ⟨1389259, by decide⟩ ⟨12, 2, 0, 1389259, 406546, 2377, 65536⟩
    (by decide) selected_cut_49168

theorem selected_cut_49169 : selected 9 ⟨1389311, by decide⟩
    (prefixPartial 12 406547) = some ⟨12, 2, 0, 1389311, 406547, 2089, 65536⟩ := by
  decide +kernel

theorem context_12_406547_1389311 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406547 ⟨1389311, by decide⟩ :=
  accepted_of_selected 12 406547 ⟨1389311, by decide⟩ ⟨12, 2, 0, 1389311, 406547, 2089, 65536⟩
    (by decide) selected_cut_49169

theorem unmarked_context_11_101636_1389312 : frontier 10 ⟨1389312, by decide⟩
    (prefixCache 11 101636) (prefixPartial 11 101636) = false := by
  decide +kernel

theorem node_context_11_101636_1389312 : EJMOriginalGlobalDAGData.nodes 10 ⟨1389312, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1389200, by decide⟩,⟨1389259, by decide⟩,⟨1389311, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_101636_1389312 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101636 ⟨1389312, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 101636
    ⟨1389312, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1389200, by decide⟩,⟨1389259, by decide⟩,⟨1389311, by decide⟩]) unmarked_context_11_101636_1389312 node_context_11_101636_1389312
  intro a
  fin_cases a
  · exact context_12_406544_1108174
  · exact context_12_406545_1389200
  · exact context_12_406546_1389259
  · exact context_12_406547_1389311

theorem selected_cut_49170 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 101637) = some ⟨11, 1, 0, 892405, 101637, 1, 262144⟩ := by
  decide +kernel

theorem context_11_101637_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101637 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 101637 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 101637, 1, 262144⟩
    (by decide) selected_cut_49170

theorem selected_cut_49171 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 406552) = some ⟨12, 1, 0, 1108174, 406552, 1, 65536⟩ := by
  decide +kernel

theorem context_12_406552_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406552 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 406552 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 406552, 1, 65536⟩
    (by decide) selected_cut_49171

theorem selected_cut_49172 : selected 9 ⟨1389363, by decide⟩
    (prefixPartial 12 406553) = some ⟨12, 2, 0, 1389363, 406553, 2101, 65536⟩ := by
  decide +kernel

theorem context_12_406553_1389363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406553 ⟨1389363, by decide⟩ :=
  accepted_of_selected 12 406553 ⟨1389363, by decide⟩ ⟨12, 2, 0, 1389363, 406553, 2101, 65536⟩
    (by decide) selected_cut_49172

theorem selected_cut_49173 : selected 9 ⟨448662, by decide⟩
    (prefixPartial 12 406554) = some ⟨12, 1, 0, 448662, 406554, 1, 65536⟩ := by
  decide +kernel

theorem context_12_406554_448662 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406554 ⟨448662, by decide⟩ :=
  accepted_of_selected 12 406554 ⟨448662, by decide⟩ ⟨12, 1, 0, 448662, 406554, 1, 65536⟩
    (by decide) selected_cut_49173

theorem selected_cut_49174 : selected 9 ⟨1389427, by decide⟩
    (prefixPartial 12 406555) = some ⟨12, 2, 0, 1389427, 406555, 2337, 65536⟩ := by
  decide +kernel

theorem context_12_406555_1389427 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406555 ⟨1389427, by decide⟩ :=
  accepted_of_selected 12 406555 ⟨1389427, by decide⟩ ⟨12, 2, 0, 1389427, 406555, 2337, 65536⟩
    (by decide) selected_cut_49174

theorem unmarked_context_11_101638_1389428 : frontier 10 ⟨1389428, by decide⟩
    (prefixCache 11 101638) (prefixPartial 11 101638) = false := by
  decide +kernel

theorem node_context_11_101638_1389428 : EJMOriginalGlobalDAGData.nodes 10 ⟨1389428, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1389363, by decide⟩,⟨448662, by decide⟩,⟨1389427, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_101638_1389428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101638 ⟨1389428, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 101638
    ⟨1389428, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1389363, by decide⟩,⟨448662, by decide⟩,⟨1389427, by decide⟩]) unmarked_context_11_101638_1389428 node_context_11_101638_1389428
  intro a
  fin_cases a
  · exact context_12_406552_1108174
  · exact context_12_406553_1389363
  · exact context_12_406554_448662
  · exact context_12_406555_1389427

theorem selected_cut_49175 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 406556) = some ⟨12, 1, 0, 1108174, 406556, 1, 65536⟩ := by
  decide +kernel

theorem context_12_406556_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406556 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 406556 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 406556, 1, 65536⟩
    (by decide) selected_cut_49175

theorem selected_cut_49176 : selected 9 ⟨1389470, by decide⟩
    (prefixPartial 12 406557) = some ⟨12, 2, 0, 1389470, 406557, 1989, 65536⟩ := by
  decide +kernel

theorem context_12_406557_1389470 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406557 ⟨1389470, by decide⟩ :=
  accepted_of_selected 12 406557 ⟨1389470, by decide⟩ ⟨12, 2, 0, 1389470, 406557, 1989, 65536⟩
    (by decide) selected_cut_49176

theorem selected_cut_49177 : selected 9 ⟨1389527, by decide⟩
    (prefixPartial 12 406558) = some ⟨12, 2, 0, 1389527, 406558, 2465, 65536⟩ := by
  decide +kernel

theorem context_12_406558_1389527 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406558 ⟨1389527, by decide⟩ :=
  accepted_of_selected 12 406558 ⟨1389527, by decide⟩ ⟨12, 2, 0, 1389527, 406558, 2465, 65536⟩
    (by decide) selected_cut_49177

theorem selected_cut_49178 : selected 9 ⟨517541, by decide⟩
    (prefixPartial 12 406559) = some ⟨12, 1, 0, 517541, 406559, 1, 65536⟩ := by
  decide +kernel

theorem context_12_406559_517541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406559 ⟨517541, by decide⟩ :=
  accepted_of_selected 12 406559 ⟨517541, by decide⟩ ⟨12, 1, 0, 517541, 406559, 1, 65536⟩
    (by decide) selected_cut_49178

theorem unmarked_context_11_101639_1389528 : frontier 10 ⟨1389528, by decide⟩
    (prefixCache 11 101639) (prefixPartial 11 101639) = false := by
  decide +kernel

theorem node_context_11_101639_1389528 : EJMOriginalGlobalDAGData.nodes 10 ⟨1389528, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1389470, by decide⟩,⟨1389527, by decide⟩,⟨517541, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_101639_1389528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101639 ⟨1389528, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 101639
    ⟨1389528, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1389470, by decide⟩,⟨1389527, by decide⟩,⟨517541, by decide⟩]) unmarked_context_11_101639_1389528 node_context_11_101639_1389528
  intro a
  fin_cases a
  · exact context_12_406556_1108174
  · exact context_12_406557_1389470
  · exact context_12_406558_1389527
  · exact context_12_406559_517541

theorem unmarked_context_10_25409_1389529 : frontier 11 ⟨1389529, by decide⟩
    (prefixCache 10 25409) (prefixPartial 10 25409) = false := by
  decide +kernel

theorem node_context_10_25409_1389529 : EJMOriginalGlobalDAGData.nodes 11 ⟨1389529, by decide⟩ =
    .split (coordinate 10) (![⟨1389312, by decide⟩,⟨892405, by decide⟩,⟨1389428, by decide⟩,⟨1389528, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25409_1389529 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25409 ⟨1389529, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25409
    ⟨1389529, by decide⟩ (by decide) (![⟨1389312, by decide⟩,⟨892405, by decide⟩,⟨1389428, by decide⟩,⟨1389528, by decide⟩]) unmarked_context_10_25409_1389529 node_context_10_25409_1389529
  intro a
  fin_cases a
  · exact context_11_101636_1389312
  · exact context_11_101637_892405
  · exact context_11_101638_1389428
  · exact context_11_101639_1389528

theorem selected_cut_49179 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 406560) = some ⟨12, 1, 0, 1108174, 406560, 1, 65536⟩ := by
  decide +kernel

theorem context_12_406560_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406560 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 406560 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 406560, 1, 65536⟩
    (by decide) selected_cut_49179

theorem selected_cut_49180 : selected 9 ⟨1389570, by decide⟩
    (prefixPartial 12 406561) = some ⟨12, 2, 0, 1389570, 406561, 2069, 65536⟩ := by
  decide +kernel

theorem context_12_406561_1389570 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406561 ⟨1389570, by decide⟩ :=
  accepted_of_selected 12 406561 ⟨1389570, by decide⟩ ⟨12, 2, 0, 1389570, 406561, 2069, 65536⟩
    (by decide) selected_cut_49180

theorem selected_cut_49181 : selected 9 ⟨1389633, by decide⟩
    (prefixPartial 12 406562) = some ⟨12, 2, 0, 1389633, 406562, 2457, 65536⟩ := by
  decide +kernel

theorem context_12_406562_1389633 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406562 ⟨1389633, by decide⟩ :=
  accepted_of_selected 12 406562 ⟨1389633, by decide⟩ ⟨12, 2, 0, 1389633, 406562, 2457, 65536⟩
    (by decide) selected_cut_49181

theorem selected_cut_49182 : selected 9 ⟨1389678, by decide⟩
    (prefixPartial 12 406563) = some ⟨12, 2, 0, 1389678, 406563, 1973, 65536⟩ := by
  decide +kernel

theorem context_12_406563_1389678 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406563 ⟨1389678, by decide⟩ :=
  accepted_of_selected 12 406563 ⟨1389678, by decide⟩ ⟨12, 2, 0, 1389678, 406563, 1973, 65536⟩
    (by decide) selected_cut_49182

theorem unmarked_context_11_101640_1389679 : frontier 10 ⟨1389679, by decide⟩
    (prefixCache 11 101640) (prefixPartial 11 101640) = false := by
  decide +kernel

theorem node_context_11_101640_1389679 : EJMOriginalGlobalDAGData.nodes 10 ⟨1389679, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1389570, by decide⟩,⟨1389633, by decide⟩,⟨1389678, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_101640_1389679 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101640 ⟨1389679, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 101640
    ⟨1389679, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1389570, by decide⟩,⟨1389633, by decide⟩,⟨1389678, by decide⟩]) unmarked_context_11_101640_1389679 node_context_11_101640_1389679
  intro a
  fin_cases a
  · exact context_12_406560_1108174
  · exact context_12_406561_1389570
  · exact context_12_406562_1389633
  · exact context_12_406563_1389678

theorem selected_cut_49183 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 406564) = some ⟨12, 1, 0, 1108174, 406564, 1, 65536⟩ := by
  decide +kernel

theorem context_12_406564_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406564 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 406564 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 406564, 1, 65536⟩
    (by decide) selected_cut_49183

theorem selected_cut_49184 : selected 9 ⟨275013, by decide⟩
    (prefixPartial 12 406565) = some ⟨12, 1, 0, 275013, 406565, 1, 65536⟩ := by
  decide +kernel

theorem context_12_406565_275013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406565 ⟨275013, by decide⟩ :=
  accepted_of_selected 12 406565 ⟨275013, by decide⟩ ⟨12, 1, 0, 275013, 406565, 1, 65536⟩
    (by decide) selected_cut_49184

theorem selected_cut_49185 : selected 9 ⟨1389740, by decide⟩
    (prefixPartial 12 406566) = some ⟨12, 2, 0, 1389740, 406566, 2349, 65536⟩ := by
  decide +kernel

theorem context_12_406566_1389740 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406566 ⟨1389740, by decide⟩ :=
  accepted_of_selected 12 406566 ⟨1389740, by decide⟩ ⟨12, 2, 0, 1389740, 406566, 2349, 65536⟩
    (by decide) selected_cut_49185

theorem selected_cut_49186 : selected 9 ⟨1389784, by decide⟩
    (prefixPartial 12 406567) = some ⟨12, 2, 0, 1389784, 406567, 1833, 65536⟩ := by
  decide +kernel

theorem context_12_406567_1389784 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406567 ⟨1389784, by decide⟩ :=
  accepted_of_selected 12 406567 ⟨1389784, by decide⟩ ⟨12, 2, 0, 1389784, 406567, 1833, 65536⟩
    (by decide) selected_cut_49186

theorem unmarked_context_11_101641_1389785 : frontier 10 ⟨1389785, by decide⟩
    (prefixCache 11 101641) (prefixPartial 11 101641) = false := by
  decide +kernel

theorem node_context_11_101641_1389785 : EJMOriginalGlobalDAGData.nodes 10 ⟨1389785, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨275013, by decide⟩,⟨1389740, by decide⟩,⟨1389784, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_101641_1389785 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101641 ⟨1389785, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 101641
    ⟨1389785, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨275013, by decide⟩,⟨1389740, by decide⟩,⟨1389784, by decide⟩]) unmarked_context_11_101641_1389785 node_context_11_101641_1389785
  intro a
  fin_cases a
  · exact context_12_406564_1108174
  · exact context_12_406565_275013
  · exact context_12_406566_1389740
  · exact context_12_406567_1389784

theorem selected_cut_49187 : selected 10 ⟨1389846, by decide⟩
    (prefixPartial 11 101642) = some ⟨11, 2, 0, 1389846, 101642, 2229, 262144⟩ := by
  decide +kernel

theorem context_11_101642_1389846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101642 ⟨1389846, by decide⟩ :=
  accepted_of_selected 11 101642 ⟨1389846, by decide⟩ ⟨11, 2, 0, 1389846, 101642, 2229, 262144⟩
    (by decide) selected_cut_49187

theorem selected_cut_49188 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 406572) = some ⟨12, 1, 0, 1108174, 406572, 1, 65536⟩ := by
  decide +kernel

theorem context_12_406572_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406572 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 406572 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 406572, 1, 65536⟩
    (by decide) selected_cut_49188

theorem selected_cut_49189 : selected 9 ⟨1389881, by decide⟩
    (prefixPartial 12 406573) = some ⟨12, 2, 0, 1389881, 406573, 1841, 65536⟩ := by
  decide +kernel

theorem context_12_406573_1389881 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406573 ⟨1389881, by decide⟩ :=
  accepted_of_selected 12 406573 ⟨1389881, by decide⟩ ⟨12, 2, 0, 1389881, 406573, 1841, 65536⟩
    (by decide) selected_cut_49189

theorem selected_cut_49190 : selected 9 ⟨1389947, by decide⟩
    (prefixPartial 12 406574) = some ⟨12, 2, 0, 1389947, 406574, 2417, 65536⟩ := by
  decide +kernel

theorem context_12_406574_1389947 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406574 ⟨1389947, by decide⟩ :=
  accepted_of_selected 12 406574 ⟨1389947, by decide⟩ ⟨12, 2, 0, 1389947, 406574, 2417, 65536⟩
    (by decide) selected_cut_49190

theorem selected_cut_49191 : selected 9 ⟨517541, by decide⟩
    (prefixPartial 12 406575) = some ⟨12, 1, 0, 517541, 406575, 1, 65536⟩ := by
  decide +kernel

theorem context_12_406575_517541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406575 ⟨517541, by decide⟩ :=
  accepted_of_selected 12 406575 ⟨517541, by decide⟩ ⟨12, 1, 0, 517541, 406575, 1, 65536⟩
    (by decide) selected_cut_49191

theorem unmarked_context_11_101643_1389948 : frontier 10 ⟨1389948, by decide⟩
    (prefixCache 11 101643) (prefixPartial 11 101643) = false := by
  decide +kernel

theorem node_context_11_101643_1389948 : EJMOriginalGlobalDAGData.nodes 10 ⟨1389948, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1389881, by decide⟩,⟨1389947, by decide⟩,⟨517541, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_101643_1389948 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101643 ⟨1389948, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 101643
    ⟨1389948, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1389881, by decide⟩,⟨1389947, by decide⟩,⟨517541, by decide⟩]) unmarked_context_11_101643_1389948 node_context_11_101643_1389948
  intro a
  fin_cases a
  · exact context_12_406572_1108174
  · exact context_12_406573_1389881
  · exact context_12_406574_1389947
  · exact context_12_406575_517541

theorem unmarked_context_10_25410_1389949 : frontier 11 ⟨1389949, by decide⟩
    (prefixCache 10 25410) (prefixPartial 10 25410) = false := by
  decide +kernel

theorem node_context_10_25410_1389949 : EJMOriginalGlobalDAGData.nodes 11 ⟨1389949, by decide⟩ =
    .split (coordinate 10) (![⟨1389679, by decide⟩,⟨1389785, by decide⟩,⟨1389846, by decide⟩,⟨1389948, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25410_1389949 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25410 ⟨1389949, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25410
    ⟨1389949, by decide⟩ (by decide) (![⟨1389679, by decide⟩,⟨1389785, by decide⟩,⟨1389846, by decide⟩,⟨1389948, by decide⟩]) unmarked_context_10_25410_1389949 node_context_10_25410_1389949
  intro a
  fin_cases a
  · exact context_11_101640_1389679
  · exact context_11_101641_1389785
  · exact context_11_101642_1389846
  · exact context_11_101643_1389948

theorem selected_cut_49192 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 406576) = some ⟨12, 1, 0, 1108174, 406576, 1, 65536⟩ := by
  decide +kernel

theorem context_12_406576_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406576 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 406576 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 406576, 1, 65536⟩
    (by decide) selected_cut_49192

theorem selected_cut_49193 : selected 9 ⟨1389981, by decide⟩
    (prefixPartial 12 406577) = some ⟨12, 2, 0, 1389981, 406577, 1793, 65536⟩ := by
  decide +kernel

theorem context_12_406577_1389981 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406577 ⟨1389981, by decide⟩ :=
  accepted_of_selected 12 406577 ⟨1389981, by decide⟩ ⟨12, 2, 0, 1389981, 406577, 1793, 65536⟩
    (by decide) selected_cut_49193

theorem selected_cut_49194 : selected 9 ⟨1390024, by decide⟩
    (prefixPartial 12 406578) = some ⟨12, 2, 0, 1390024, 406578, 2013, 65536⟩ := by
  decide +kernel

theorem context_12_406578_1390024 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406578 ⟨1390024, by decide⟩ :=
  accepted_of_selected 12 406578 ⟨1390024, by decide⟩ ⟨12, 2, 0, 1390024, 406578, 2013, 65536⟩
    (by decide) selected_cut_49194

theorem selected_cut_49195 : selected 9 ⟨1390062, by decide⟩
    (prefixPartial 12 406579) = some ⟨12, 2, 0, 1390062, 406579, 1741, 65536⟩ := by
  decide +kernel

theorem context_12_406579_1390062 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406579 ⟨1390062, by decide⟩ :=
  accepted_of_selected 12 406579 ⟨1390062, by decide⟩ ⟨12, 2, 0, 1390062, 406579, 1741, 65536⟩
    (by decide) selected_cut_49195

theorem unmarked_context_11_101644_1390063 : frontier 10 ⟨1390063, by decide⟩
    (prefixCache 11 101644) (prefixPartial 11 101644) = false := by
  decide +kernel

theorem node_context_11_101644_1390063 : EJMOriginalGlobalDAGData.nodes 10 ⟨1390063, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1389981, by decide⟩,⟨1390024, by decide⟩,⟨1390062, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_101644_1390063 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101644 ⟨1390063, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 101644
    ⟨1390063, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1389981, by decide⟩,⟨1390024, by decide⟩,⟨1390062, by decide⟩]) unmarked_context_11_101644_1390063 node_context_11_101644_1390063
  intro a
  fin_cases a
  · exact context_12_406576_1108174
  · exact context_12_406577_1389981
  · exact context_12_406578_1390024
  · exact context_12_406579_1390062

theorem selected_cut_49196 : selected 10 ⟨1390146, by decide⟩
    (prefixPartial 11 101645) = some ⟨11, 2, 0, 1390146, 101645, 3641, 262144⟩ := by
  decide +kernel

theorem context_11_101645_1390146 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101645 ⟨1390146, by decide⟩ :=
  accepted_of_selected 11 101645 ⟨1390146, by decide⟩ ⟨11, 2, 0, 1390146, 101645, 3641, 262144⟩
    (by decide) selected_cut_49196

theorem selected_cut_49197 : selected 10 ⟨1390237, by decide⟩
    (prefixPartial 11 101646) = some ⟨11, 2, 0, 1390237, 101646, 3653, 262144⟩ := by
  decide +kernel

theorem context_11_101646_1390237 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101646 ⟨1390237, by decide⟩ :=
  accepted_of_selected 11 101646 ⟨1390237, by decide⟩ ⟨11, 2, 0, 1390237, 101646, 3653, 262144⟩
    (by decide) selected_cut_49197

theorem selected_cut_49198 : selected 10 ⟨1390281, by decide⟩
    (prefixPartial 11 101647) = some ⟨11, 2, 0, 1390281, 101647, 1921, 262144⟩ := by
  decide +kernel

theorem context_11_101647_1390281 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101647 ⟨1390281, by decide⟩ :=
  accepted_of_selected 11 101647 ⟨1390281, by decide⟩ ⟨11, 2, 0, 1390281, 101647, 1921, 262144⟩
    (by decide) selected_cut_49198

theorem unmarked_context_10_25411_1390282 : frontier 11 ⟨1390282, by decide⟩
    (prefixCache 10 25411) (prefixPartial 10 25411) = false := by
  decide +kernel

theorem node_context_10_25411_1390282 : EJMOriginalGlobalDAGData.nodes 11 ⟨1390282, by decide⟩ =
    .split (coordinate 10) (![⟨1390063, by decide⟩,⟨1390146, by decide⟩,⟨1390237, by decide⟩,⟨1390281, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25411_1390282 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25411 ⟨1390282, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25411
    ⟨1390282, by decide⟩ (by decide) (![⟨1390063, by decide⟩,⟨1390146, by decide⟩,⟨1390237, by decide⟩,⟨1390281, by decide⟩]) unmarked_context_10_25411_1390282 node_context_10_25411_1390282
  intro a
  fin_cases a
  · exact context_11_101644_1390063
  · exact context_11_101645_1390146
  · exact context_11_101646_1390237
  · exact context_11_101647_1390281

theorem unmarked_context_9_6352_1390283 : frontier 12 ⟨1390283, by decide⟩
    (prefixCache 9 6352) (prefixPartial 9 6352) = false := by
  decide +kernel

theorem node_context_9_6352_1390283 : EJMOriginalGlobalDAGData.nodes 12 ⟨1390283, by decide⟩ =
    .split (coordinate 9) (![⟨1389149, by decide⟩,⟨1389529, by decide⟩,⟨1389949, by decide⟩,⟨1390282, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6352_1390283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6352 ⟨1390283, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6352
    ⟨1390283, by decide⟩ (by decide) (![⟨1389149, by decide⟩,⟨1389529, by decide⟩,⟨1389949, by decide⟩,⟨1390282, by decide⟩]) unmarked_context_9_6352_1390283 node_context_9_6352_1390283
  intro a
  fin_cases a
  · exact context_10_25408_1389149
  · exact context_10_25409_1389529
  · exact context_10_25410_1389949
  · exact context_10_25411_1390282

theorem selected_cut_49199 : selected 10 ⟨1369428, by decide⟩
    (prefixPartial 11 101648) = some ⟨11, 1, 0, 1369428, 101648, 1, 262144⟩ := by
  decide +kernel

theorem context_11_101648_1369428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101648 ⟨1369428, by decide⟩ :=
  accepted_of_selected 11 101648 ⟨1369428, by decide⟩ ⟨11, 1, 0, 1369428, 101648, 1, 262144⟩
    (by decide) selected_cut_49199

theorem selected_cut_49200 : selected 10 ⟨1390368, by decide⟩
    (prefixPartial 11 101649) = some ⟨11, 2, 0, 1390368, 101649, 3985, 262144⟩ := by
  decide +kernel

theorem context_11_101649_1390368 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101649 ⟨1390368, by decide⟩ :=
  accepted_of_selected 11 101649 ⟨1390368, by decide⟩ ⟨11, 2, 0, 1390368, 101649, 3985, 262144⟩
    (by decide) selected_cut_49200

theorem selected_cut_49201 : selected 10 ⟨1390427, by decide⟩
    (prefixPartial 11 101650) = some ⟨11, 2, 0, 1390427, 101650, 2897, 262144⟩ := by
  decide +kernel

theorem context_11_101650_1390427 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101650 ⟨1390427, by decide⟩ :=
  accepted_of_selected 11 101650 ⟨1390427, by decide⟩ ⟨11, 2, 0, 1390427, 101650, 2897, 262144⟩
    (by decide) selected_cut_49201

theorem selected_cut_49202 : selected 10 ⟨1390486, by decide⟩
    (prefixPartial 11 101651) = some ⟨11, 2, 0, 1390486, 101651, 2749, 262144⟩ := by
  decide +kernel

theorem context_11_101651_1390486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101651 ⟨1390486, by decide⟩ :=
  accepted_of_selected 11 101651 ⟨1390486, by decide⟩ ⟨11, 2, 0, 1390486, 101651, 2749, 262144⟩
    (by decide) selected_cut_49202

theorem unmarked_context_10_25412_1390487 : frontier 11 ⟨1390487, by decide⟩
    (prefixCache 10 25412) (prefixPartial 10 25412) = false := by
  decide +kernel

theorem node_context_10_25412_1390487 : EJMOriginalGlobalDAGData.nodes 11 ⟨1390487, by decide⟩ =
    .split (coordinate 10) (![⟨1369428, by decide⟩,⟨1390368, by decide⟩,⟨1390427, by decide⟩,⟨1390486, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25412_1390487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25412 ⟨1390487, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25412
    ⟨1390487, by decide⟩ (by decide) (![⟨1369428, by decide⟩,⟨1390368, by decide⟩,⟨1390427, by decide⟩,⟨1390486, by decide⟩]) unmarked_context_10_25412_1390487 node_context_10_25412_1390487
  intro a
  fin_cases a
  · exact context_11_101648_1369428
  · exact context_11_101649_1390368
  · exact context_11_101650_1390427
  · exact context_11_101651_1390486

theorem selected_cut_49203 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 25413) = some ⟨10, 1, 0, 893098, 25413, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_25413_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25413 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 25413 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 25413, 1, 1048576⟩
    (by decide) selected_cut_49203

theorem selected_cut_49204 : selected 10 ⟨1390560, by decide⟩
    (prefixPartial 11 101656) = some ⟨11, 2, 0, 1390560, 101656, 3117, 262144⟩ := by
  decide +kernel

theorem context_11_101656_1390560 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101656 ⟨1390560, by decide⟩ :=
  accepted_of_selected 11 101656 ⟨1390560, by decide⟩ ⟨11, 2, 0, 1390560, 101656, 3117, 262144⟩
    (by decide) selected_cut_49204

theorem selected_cut_49205 : selected 10 ⟨1390647, by decide⟩
    (prefixPartial 11 101657) = some ⟨11, 2, 0, 1390647, 101657, 3857, 262144⟩ := by
  decide +kernel

theorem context_11_101657_1390647 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101657 ⟨1390647, by decide⟩ :=
  accepted_of_selected 11 101657 ⟨1390647, by decide⟩ ⟨11, 2, 0, 1390647, 101657, 3857, 262144⟩
    (by decide) selected_cut_49205

theorem selected_cut_49206 : selected 10 ⟨1369759, by decide⟩
    (prefixPartial 11 101658) = some ⟨11, 1, 0, 1369759, 101658, 1, 262144⟩ := by
  decide +kernel

theorem context_11_101658_1369759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101658 ⟨1369759, by decide⟩ :=
  accepted_of_selected 11 101658 ⟨1369759, by decide⟩ ⟨11, 1, 0, 1369759, 101658, 1, 262144⟩
    (by decide) selected_cut_49206

theorem selected_cut_49207 : selected 9 ⟨1390675, by decide⟩
    (prefixPartial 12 406636) = some ⟨12, 2, 0, 1390675, 406636, 1213, 65536⟩ := by
  decide +kernel

theorem context_12_406636_1390675 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406636 ⟨1390675, by decide⟩ :=
  accepted_of_selected 12 406636 ⟨1390675, by decide⟩ ⟨12, 2, 0, 1390675, 406636, 1213, 65536⟩
    (by decide) selected_cut_49207

theorem selected_cut_49208 : selected 9 ⟨1390697, by decide⟩
    (prefixPartial 12 406637) = some ⟨12, 2, 0, 1390697, 406637, 597, 65536⟩ := by
  decide +kernel

theorem context_12_406637_1390697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406637 ⟨1390697, by decide⟩ :=
  accepted_of_selected 12 406637 ⟨1390697, by decide⟩ ⟨12, 2, 0, 1390697, 406637, 597, 65536⟩
    (by decide) selected_cut_49208

theorem selected_cut_49209 : selected 9 ⟨1390732, by decide⟩
    (prefixPartial 12 406638) = some ⟨12, 2, 0, 1390732, 406638, 1449, 65536⟩ := by
  decide +kernel

theorem context_12_406638_1390732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406638 ⟨1390732, by decide⟩ :=
  accepted_of_selected 12 406638 ⟨1390732, by decide⟩ ⟨12, 2, 0, 1390732, 406638, 1449, 65536⟩
    (by decide) selected_cut_49209

theorem selected_cut_49210 : selected 9 ⟨1390758, by decide⟩
    (prefixPartial 12 406639) = some ⟨12, 2, 0, 1390758, 406639, 1225, 65536⟩ := by
  decide +kernel

theorem context_12_406639_1390758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406639 ⟨1390758, by decide⟩ :=
  accepted_of_selected 12 406639 ⟨1390758, by decide⟩ ⟨12, 2, 0, 1390758, 406639, 1225, 65536⟩
    (by decide) selected_cut_49210

theorem unmarked_context_11_101659_1390759 : frontier 10 ⟨1390759, by decide⟩
    (prefixCache 11 101659) (prefixPartial 11 101659) = false := by
  decide +kernel

theorem node_context_11_101659_1390759 : EJMOriginalGlobalDAGData.nodes 10 ⟨1390759, by decide⟩ =
    .split (coordinate 11) (![⟨1390675, by decide⟩,⟨1390697, by decide⟩,⟨1390732, by decide⟩,⟨1390758, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_101659_1390759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101659 ⟨1390759, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 101659
    ⟨1390759, by decide⟩ (by decide) (![⟨1390675, by decide⟩,⟨1390697, by decide⟩,⟨1390732, by decide⟩,⟨1390758, by decide⟩]) unmarked_context_11_101659_1390759 node_context_11_101659_1390759
  intro a
  fin_cases a
  · exact context_12_406636_1390675
  · exact context_12_406637_1390697
  · exact context_12_406638_1390732
  · exact context_12_406639_1390758

theorem unmarked_context_10_25414_1390760 : frontier 11 ⟨1390760, by decide⟩
    (prefixCache 10 25414) (prefixPartial 10 25414) = false := by
  decide +kernel

theorem node_context_10_25414_1390760 : EJMOriginalGlobalDAGData.nodes 11 ⟨1390760, by decide⟩ =
    .split (coordinate 10) (![⟨1390560, by decide⟩,⟨1390647, by decide⟩,⟨1369759, by decide⟩,⟨1390759, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25414_1390760 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25414 ⟨1390760, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25414
    ⟨1390760, by decide⟩ (by decide) (![⟨1390560, by decide⟩,⟨1390647, by decide⟩,⟨1369759, by decide⟩,⟨1390759, by decide⟩]) unmarked_context_10_25414_1390760 node_context_10_25414_1390760
  intro a
  fin_cases a
  · exact context_11_101656_1390560
  · exact context_11_101657_1390647
  · exact context_11_101658_1369759
  · exact context_11_101659_1390759

theorem selected_cut_49211 : selected 10 ⟨1390811, by decide⟩
    (prefixPartial 11 101660) = some ⟨11, 2, 0, 1390811, 101660, 2409, 262144⟩ := by
  decide +kernel

theorem context_11_101660_1390811 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101660 ⟨1390811, by decide⟩ :=
  accepted_of_selected 11 101660 ⟨1390811, by decide⟩ ⟨11, 2, 0, 1390811, 101660, 2409, 262144⟩
    (by decide) selected_cut_49211

theorem selected_cut_49212 : selected 10 ⟨1390874, by decide⟩
    (prefixPartial 11 101661) = some ⟨11, 2, 0, 1390874, 101661, 2917, 262144⟩ := by
  decide +kernel

theorem context_11_101661_1390874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101661 ⟨1390874, by decide⟩ :=
  accepted_of_selected 11 101661 ⟨1390874, by decide⟩ ⟨11, 2, 0, 1390874, 101661, 2917, 262144⟩
    (by decide) selected_cut_49212

theorem selected_cut_49213 : selected 10 ⟨1390955, by decide⟩
    (prefixPartial 11 101662) = some ⟨11, 2, 0, 1390955, 101662, 3669, 262144⟩ := by
  decide +kernel

theorem context_11_101662_1390955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101662 ⟨1390955, by decide⟩ :=
  accepted_of_selected 11 101662 ⟨1390955, by decide⟩ ⟨11, 2, 0, 1390955, 101662, 3669, 262144⟩
    (by decide) selected_cut_49213

theorem selected_cut_49214 : selected 10 ⟨1370051, by decide⟩
    (prefixPartial 11 101663) = some ⟨11, 1, 0, 1370051, 101663, 1, 262144⟩ := by
  decide +kernel

theorem context_11_101663_1370051 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101663 ⟨1370051, by decide⟩ :=
  accepted_of_selected 11 101663 ⟨1370051, by decide⟩ ⟨11, 1, 0, 1370051, 101663, 1, 262144⟩
    (by decide) selected_cut_49214

theorem unmarked_context_10_25415_1390956 : frontier 11 ⟨1390956, by decide⟩
    (prefixCache 10 25415) (prefixPartial 10 25415) = false := by
  decide +kernel

theorem node_context_10_25415_1390956 : EJMOriginalGlobalDAGData.nodes 11 ⟨1390956, by decide⟩ =
    .split (coordinate 10) (![⟨1390811, by decide⟩,⟨1390874, by decide⟩,⟨1390955, by decide⟩,⟨1370051, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25415_1390956 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25415 ⟨1390956, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25415
    ⟨1390956, by decide⟩ (by decide) (![⟨1390811, by decide⟩,⟨1390874, by decide⟩,⟨1390955, by decide⟩,⟨1370051, by decide⟩]) unmarked_context_10_25415_1390956 node_context_10_25415_1390956
  intro a
  fin_cases a
  · exact context_11_101660_1390811
  · exact context_11_101661_1390874
  · exact context_11_101662_1390955
  · exact context_11_101663_1370051

theorem unmarked_context_9_6353_1390957 : frontier 12 ⟨1390957, by decide⟩
    (prefixCache 9 6353) (prefixPartial 9 6353) = false := by
  decide +kernel

theorem node_context_9_6353_1390957 : EJMOriginalGlobalDAGData.nodes 12 ⟨1390957, by decide⟩ =
    .split (coordinate 9) (![⟨1390487, by decide⟩,⟨893098, by decide⟩,⟨1390760, by decide⟩,⟨1390956, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6353_1390957 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6353 ⟨1390957, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6353
    ⟨1390957, by decide⟩ (by decide) (![⟨1390487, by decide⟩,⟨893098, by decide⟩,⟨1390760, by decide⟩,⟨1390956, by decide⟩]) unmarked_context_9_6353_1390957 node_context_9_6353_1390957
  intro a
  fin_cases a
  · exact context_10_25412_1390487
  · exact context_10_25413_893098
  · exact context_10_25414_1390760
  · exact context_10_25415_1390956

theorem selected_cut_49215 : selected 10 ⟨1390997, by decide⟩
    (prefixPartial 11 101664) = some ⟨11, 2, 0, 1390997, 101664, 465, 262144⟩ := by
  decide +kernel

theorem context_11_101664_1390997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101664 ⟨1390997, by decide⟩ :=
  accepted_of_selected 11 101664 ⟨1390997, by decide⟩ ⟨11, 2, 0, 1390997, 101664, 465, 262144⟩
    (by decide) selected_cut_49215

theorem selected_cut_49216 : selected 10 ⟨1391021, by decide⟩
    (prefixPartial 11 101665) = some ⟨11, 2, 0, 1391021, 101665, 1613, 262144⟩ := by
  decide +kernel

theorem context_11_101665_1391021 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101665 ⟨1391021, by decide⟩ :=
  accepted_of_selected 11 101665 ⟨1391021, by decide⟩ ⟨11, 2, 0, 1391021, 101665, 1613, 262144⟩
    (by decide) selected_cut_49216

theorem selected_cut_49217 : selected 10 ⟨1391071, by decide⟩
    (prefixPartial 11 101666) = some ⟨11, 2, 0, 1391071, 101666, 2645, 262144⟩ := by
  decide +kernel

theorem context_11_101666_1391071 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101666 ⟨1391071, by decide⟩ :=
  accepted_of_selected 11 101666 ⟨1391071, by decide⟩ ⟨11, 2, 0, 1391071, 101666, 2645, 262144⟩
    (by decide) selected_cut_49217

theorem selected_cut_49218 : selected 10 ⟨1391101, by decide⟩
    (prefixPartial 11 101667) = some ⟨11, 2, 0, 1391101, 101667, 1753, 262144⟩ := by
  decide +kernel

theorem context_11_101667_1391101 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101667 ⟨1391101, by decide⟩ :=
  accepted_of_selected 11 101667 ⟨1391101, by decide⟩ ⟨11, 2, 0, 1391101, 101667, 1753, 262144⟩
    (by decide) selected_cut_49218

theorem unmarked_context_10_25416_1391102 : frontier 11 ⟨1391102, by decide⟩
    (prefixCache 10 25416) (prefixPartial 10 25416) = false := by
  decide +kernel

theorem node_context_10_25416_1391102 : EJMOriginalGlobalDAGData.nodes 11 ⟨1391102, by decide⟩ =
    .split (coordinate 10) (![⟨1390997, by decide⟩,⟨1391021, by decide⟩,⟨1391071, by decide⟩,⟨1391101, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25416_1391102 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25416 ⟨1391102, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25416
    ⟨1391102, by decide⟩ (by decide) (![⟨1390997, by decide⟩,⟨1391021, by decide⟩,⟨1391071, by decide⟩,⟨1391101, by decide⟩]) unmarked_context_10_25416_1391102 node_context_10_25416_1391102
  intro a
  fin_cases a
  · exact context_11_101664_1390997
  · exact context_11_101665_1391021
  · exact context_11_101666_1391071
  · exact context_11_101667_1391101

theorem selected_cut_49219 : selected 10 ⟨1391133, by decide⟩
    (prefixPartial 11 101668) = some ⟨11, 2, 0, 1391133, 101668, 1605, 262144⟩ := by
  decide +kernel

theorem context_11_101668_1391133 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101668 ⟨1391133, by decide⟩ :=
  accepted_of_selected 11 101668 ⟨1391133, by decide⟩ ⟨11, 2, 0, 1391133, 101668, 1605, 262144⟩
    (by decide) selected_cut_49219

theorem selected_cut_49220 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 101669) = some ⟨11, 1, 0, 892405, 101669, 1, 262144⟩ := by
  decide +kernel

theorem context_11_101669_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101669 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 101669 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 101669, 1, 262144⟩
    (by decide) selected_cut_49220

theorem selected_cut_49221 : selected 10 ⟨1391177, by decide⟩
    (prefixPartial 11 101670) = some ⟨11, 2, 0, 1391177, 101670, 2369, 262144⟩ := by
  decide +kernel

theorem context_11_101670_1391177 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101670 ⟨1391177, by decide⟩ :=
  accepted_of_selected 11 101670 ⟨1391177, by decide⟩ ⟨11, 2, 0, 1391177, 101670, 2369, 262144⟩
    (by decide) selected_cut_49221

theorem selected_cut_49222 : selected 10 ⟨1391234, by decide⟩
    (prefixPartial 11 101671) = some ⟨11, 2, 0, 1391234, 101671, 2809, 262144⟩ := by
  decide +kernel

theorem context_11_101671_1391234 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101671 ⟨1391234, by decide⟩ :=
  accepted_of_selected 11 101671 ⟨1391234, by decide⟩ ⟨11, 2, 0, 1391234, 101671, 2809, 262144⟩
    (by decide) selected_cut_49222

theorem unmarked_context_10_25417_1391235 : frontier 11 ⟨1391235, by decide⟩
    (prefixCache 10 25417) (prefixPartial 10 25417) = false := by
  decide +kernel

theorem node_context_10_25417_1391235 : EJMOriginalGlobalDAGData.nodes 11 ⟨1391235, by decide⟩ =
    .split (coordinate 10) (![⟨1391133, by decide⟩,⟨892405, by decide⟩,⟨1391177, by decide⟩,⟨1391234, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25417_1391235 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25417 ⟨1391235, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25417
    ⟨1391235, by decide⟩ (by decide) (![⟨1391133, by decide⟩,⟨892405, by decide⟩,⟨1391177, by decide⟩,⟨1391234, by decide⟩]) unmarked_context_10_25417_1391235 node_context_10_25417_1391235
  intro a
  fin_cases a
  · exact context_11_101668_1391133
  · exact context_11_101669_892405
  · exact context_11_101670_1391177
  · exact context_11_101671_1391234

theorem selected_cut_49223 : selected 11 ⟨1391271, by decide⟩
    (prefixPartial 10 25418) = some ⟨10, 2, 0, 1391271, 25418, 1849, 1048576⟩ := by
  decide +kernel

theorem context_10_25418_1391271 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25418 ⟨1391271, by decide⟩ :=
  accepted_of_selected 10 25418 ⟨1391271, by decide⟩ ⟨10, 2, 0, 1391271, 25418, 1849, 1048576⟩
    (by decide) selected_cut_49223

theorem selected_cut_49224 : selected 10 ⟨1391286, by decide⟩
    (prefixPartial 11 101676) = some ⟨11, 2, 0, 1391286, 101676, 961, 262144⟩ := by
  decide +kernel

theorem context_11_101676_1391286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101676 ⟨1391286, by decide⟩ :=
  accepted_of_selected 11 101676 ⟨1391286, by decide⟩ ⟨11, 2, 0, 1391286, 101676, 961, 262144⟩
    (by decide) selected_cut_49224

theorem selected_cut_49225 : selected 10 ⟨1391319, by decide⟩
    (prefixPartial 11 101677) = some ⟨11, 2, 0, 1391319, 101677, 1533, 262144⟩ := by
  decide +kernel

theorem context_11_101677_1391319 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101677 ⟨1391319, by decide⟩ :=
  accepted_of_selected 11 101677 ⟨1391319, by decide⟩ ⟨11, 2, 0, 1391319, 101677, 1533, 262144⟩
    (by decide) selected_cut_49225

theorem selected_cut_49226 : selected 10 ⟨1391349, by decide⟩
    (prefixPartial 11 101678) = some ⟨11, 2, 0, 1391349, 101678, 1457, 262144⟩ := by
  decide +kernel

theorem context_11_101678_1391349 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101678 ⟨1391349, by decide⟩ :=
  accepted_of_selected 11 101678 ⟨1391349, by decide⟩ ⟨11, 2, 0, 1391349, 101678, 1457, 262144⟩
    (by decide) selected_cut_49226

theorem selected_cut_49227 : selected 10 ⟨1391368, by decide⟩
    (prefixPartial 11 101679) = some ⟨11, 2, 0, 1391368, 101679, 961, 262144⟩ := by
  decide +kernel

theorem context_11_101679_1391368 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101679 ⟨1391368, by decide⟩ :=
  accepted_of_selected 11 101679 ⟨1391368, by decide⟩ ⟨11, 2, 0, 1391368, 101679, 961, 262144⟩
    (by decide) selected_cut_49227

theorem unmarked_context_10_25419_1391369 : frontier 11 ⟨1391369, by decide⟩
    (prefixCache 10 25419) (prefixPartial 10 25419) = false := by
  decide +kernel

theorem node_context_10_25419_1391369 : EJMOriginalGlobalDAGData.nodes 11 ⟨1391369, by decide⟩ =
    .split (coordinate 10) (![⟨1391286, by decide⟩,⟨1391319, by decide⟩,⟨1391349, by decide⟩,⟨1391368, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25419_1391369 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25419 ⟨1391369, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25419
    ⟨1391369, by decide⟩ (by decide) (![⟨1391286, by decide⟩,⟨1391319, by decide⟩,⟨1391349, by decide⟩,⟨1391368, by decide⟩]) unmarked_context_10_25419_1391369 node_context_10_25419_1391369
  intro a
  fin_cases a
  · exact context_11_101676_1391286
  · exact context_11_101677_1391319
  · exact context_11_101678_1391349
  · exact context_11_101679_1391368

theorem unmarked_context_9_6354_1391370 : frontier 12 ⟨1391370, by decide⟩
    (prefixCache 9 6354) (prefixPartial 9 6354) = false := by
  decide +kernel

theorem node_context_9_6354_1391370 : EJMOriginalGlobalDAGData.nodes 12 ⟨1391370, by decide⟩ =
    .split (coordinate 9) (![⟨1391102, by decide⟩,⟨1391235, by decide⟩,⟨1391271, by decide⟩,⟨1391369, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6354_1391370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6354 ⟨1391370, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6354
    ⟨1391370, by decide⟩ (by decide) (![⟨1391102, by decide⟩,⟨1391235, by decide⟩,⟨1391271, by decide⟩,⟨1391369, by decide⟩]) unmarked_context_9_6354_1391370 node_context_9_6354_1391370
  intro a
  fin_cases a
  · exact context_10_25416_1391102
  · exact context_10_25417_1391235
  · exact context_10_25418_1391271
  · exact context_10_25419_1391369

theorem selected_cut_49228 : selected 11 ⟨1391430, by decide⟩
    (prefixPartial 10 25420) = some ⟨10, 2, 0, 1391430, 25420, 2789, 1048576⟩ := by
  decide +kernel

theorem context_10_25420_1391430 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25420 ⟨1391430, by decide⟩ :=
  accepted_of_selected 10 25420 ⟨1391430, by decide⟩ ⟨10, 2, 0, 1391430, 25420, 2789, 1048576⟩
    (by decide) selected_cut_49228

theorem selected_cut_49229 : selected 11 ⟨1391477, by decide⟩
    (prefixPartial 10 25421) = some ⟨10, 2, 0, 1391477, 25421, 2209, 1048576⟩ := by
  decide +kernel

theorem context_10_25421_1391477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25421 ⟨1391477, by decide⟩ :=
  accepted_of_selected 10 25421 ⟨1391477, by decide⟩ ⟨10, 2, 0, 1391477, 25421, 2209, 1048576⟩
    (by decide) selected_cut_49229

theorem selected_cut_49230 : selected 11 ⟨1391516, by decide⟩
    (prefixPartial 10 25422) = some ⟨10, 2, 0, 1391516, 25422, 1233, 1048576⟩ := by
  decide +kernel

theorem context_10_25422_1391516 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25422 ⟨1391516, by decide⟩ :=
  accepted_of_selected 10 25422 ⟨1391516, by decide⟩ ⟨10, 2, 0, 1391516, 25422, 1233, 1048576⟩
    (by decide) selected_cut_49230

theorem selected_cut_49231 : selected 11 ⟨1391518, by decide⟩
    (prefixPartial 10 25423) = some ⟨10, 2, 0, 1391518, 25423, 113, 1048576⟩ := by
  decide +kernel

theorem context_10_25423_1391518 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25423 ⟨1391518, by decide⟩ :=
  accepted_of_selected 10 25423 ⟨1391518, by decide⟩ ⟨10, 2, 0, 1391518, 25423, 113, 1048576⟩
    (by decide) selected_cut_49231

theorem unmarked_context_9_6355_1391519 : frontier 12 ⟨1391519, by decide⟩
    (prefixCache 9 6355) (prefixPartial 9 6355) = false := by
  decide +kernel

theorem node_context_9_6355_1391519 : EJMOriginalGlobalDAGData.nodes 12 ⟨1391519, by decide⟩ =
    .split (coordinate 9) (![⟨1391430, by decide⟩,⟨1391477, by decide⟩,⟨1391516, by decide⟩,⟨1391518, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6355_1391519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6355 ⟨1391519, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6355
    ⟨1391519, by decide⟩ (by decide) (![⟨1391430, by decide⟩,⟨1391477, by decide⟩,⟨1391516, by decide⟩,⟨1391518, by decide⟩]) unmarked_context_9_6355_1391519 node_context_9_6355_1391519
  intro a
  fin_cases a
  · exact context_10_25420_1391430
  · exact context_10_25421_1391477
  · exact context_10_25422_1391516
  · exact context_10_25423_1391518

theorem unmarked_context_8_1588_1391520 : frontier 13 ⟨1391520, by decide⟩
    (prefixCache 8 1588) (prefixPartial 8 1588) = false := by
  decide +kernel

theorem node_context_8_1588_1391520 : EJMOriginalGlobalDAGData.nodes 13 ⟨1391520, by decide⟩ =
    .split (coordinate 8) (![⟨1390283, by decide⟩,⟨1390957, by decide⟩,⟨1391370, by decide⟩,⟨1391519, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1588_1391520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1588 ⟨1391520, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1588
    ⟨1391520, by decide⟩ (by decide) (![⟨1390283, by decide⟩,⟨1390957, by decide⟩,⟨1391370, by decide⟩,⟨1391519, by decide⟩]) unmarked_context_8_1588_1391520 node_context_8_1588_1391520
  intro a
  fin_cases a
  · exact context_9_6352_1390283
  · exact context_9_6353_1390957
  · exact context_9_6354_1391370
  · exact context_9_6355_1391519

theorem selected_cut_49232 : selected 11 ⟨1391639, by decide⟩
    (prefixPartial 10 25424) = some ⟨10, 2, 0, 1391639, 25424, 4033, 1048576⟩ := by
  decide +kernel

theorem context_10_25424_1391639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25424 ⟨1391639, by decide⟩ :=
  accepted_of_selected 10 25424 ⟨1391639, by decide⟩ ⟨10, 2, 0, 1391639, 25424, 4033, 1048576⟩
    (by decide) selected_cut_49232

theorem selected_cut_49233 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 406800) = some ⟨12, 1, 0, 1108174, 406800, 1, 65536⟩ := by
  decide +kernel

theorem context_12_406800_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406800 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 406800 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 406800, 1, 65536⟩
    (by decide) selected_cut_49233

theorem selected_cut_49234 : selected 9 ⟨1391683, by decide⟩
    (prefixPartial 12 406801) = some ⟨12, 2, 0, 1391683, 406801, 2057, 65536⟩ := by
  decide +kernel

theorem context_12_406801_1391683 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406801 ⟨1391683, by decide⟩ :=
  accepted_of_selected 12 406801 ⟨1391683, by decide⟩ ⟨12, 2, 0, 1391683, 406801, 2057, 65536⟩
    (by decide) selected_cut_49234

theorem selected_cut_49235 : selected 9 ⟨1391748, by decide⟩
    (prefixPartial 12 406802) = some ⟨12, 2, 0, 1391748, 406802, 2609, 65536⟩ := by
  decide +kernel

theorem context_12_406802_1391748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406802 ⟨1391748, by decide⟩ :=
  accepted_of_selected 12 406802 ⟨1391748, by decide⟩ ⟨12, 2, 0, 1391748, 406802, 2609, 65536⟩
    (by decide) selected_cut_49235

theorem selected_cut_49236 : selected 9 ⟨1391802, by decide⟩
    (prefixPartial 12 406803) = some ⟨12, 2, 0, 1391802, 406803, 2269, 65536⟩ := by
  decide +kernel

theorem context_12_406803_1391802 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406803 ⟨1391802, by decide⟩ :=
  accepted_of_selected 12 406803 ⟨1391802, by decide⟩ ⟨12, 2, 0, 1391802, 406803, 2269, 65536⟩
    (by decide) selected_cut_49236

theorem unmarked_context_11_101700_1391803 : frontier 10 ⟨1391803, by decide⟩
    (prefixCache 11 101700) (prefixPartial 11 101700) = false := by
  decide +kernel

theorem node_context_11_101700_1391803 : EJMOriginalGlobalDAGData.nodes 10 ⟨1391803, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1391683, by decide⟩,⟨1391748, by decide⟩,⟨1391802, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_101700_1391803 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101700 ⟨1391803, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 101700
    ⟨1391803, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1391683, by decide⟩,⟨1391748, by decide⟩,⟨1391802, by decide⟩]) unmarked_context_11_101700_1391803 node_context_11_101700_1391803
  intro a
  fin_cases a
  · exact context_12_406800_1108174
  · exact context_12_406801_1391683
  · exact context_12_406802_1391748
  · exact context_12_406803_1391802

theorem selected_cut_49237 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 101701) = some ⟨11, 1, 0, 892405, 101701, 1, 262144⟩ := by
  decide +kernel

theorem context_11_101701_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101701 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 101701 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 101701, 1, 262144⟩
    (by decide) selected_cut_49237

theorem selected_cut_49238 : selected 10 ⟨1391886, by decide⟩
    (prefixPartial 11 101702) = some ⟨11, 2, 0, 1391886, 101702, 3725, 262144⟩ := by
  decide +kernel

theorem context_11_101702_1391886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101702 ⟨1391886, by decide⟩ :=
  accepted_of_selected 11 101702 ⟨1391886, by decide⟩ ⟨11, 2, 0, 1391886, 101702, 3725, 262144⟩
    (by decide) selected_cut_49238

theorem selected_cut_49239 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 406812) = some ⟨12, 1, 0, 1108174, 406812, 1, 65536⟩ := by
  decide +kernel

theorem context_12_406812_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406812 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 406812 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 406812, 1, 65536⟩
    (by decide) selected_cut_49239

theorem selected_cut_49240 : selected 9 ⟨1391920, by decide⟩
    (prefixPartial 12 406813) = some ⟨12, 2, 0, 1391920, 406813, 1757, 65536⟩ := by
  decide +kernel

theorem context_12_406813_1391920 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406813 ⟨1391920, by decide⟩ :=
  accepted_of_selected 12 406813 ⟨1391920, by decide⟩ ⟨12, 2, 0, 1391920, 406813, 1757, 65536⟩
    (by decide) selected_cut_49240

theorem selected_cut_49241 : selected 9 ⟨1391975, by decide⟩
    (prefixPartial 12 406814) = some ⟨12, 2, 0, 1391975, 406814, 2365, 65536⟩ := by
  decide +kernel

theorem context_12_406814_1391975 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406814 ⟨1391975, by decide⟩ :=
  accepted_of_selected 12 406814 ⟨1391975, by decide⟩ ⟨12, 2, 0, 1391975, 406814, 2365, 65536⟩
    (by decide) selected_cut_49241

theorem selected_cut_49242 : selected 9 ⟨1365011, by decide⟩
    (prefixPartial 12 406815) = some ⟨12, 1, 0, 1365011, 406815, 1, 65536⟩ := by
  decide +kernel

theorem context_12_406815_1365011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406815 ⟨1365011, by decide⟩ :=
  accepted_of_selected 12 406815 ⟨1365011, by decide⟩ ⟨12, 1, 0, 1365011, 406815, 1, 65536⟩
    (by decide) selected_cut_49242

theorem unmarked_context_11_101703_1391976 : frontier 10 ⟨1391976, by decide⟩
    (prefixCache 11 101703) (prefixPartial 11 101703) = false := by
  decide +kernel

theorem node_context_11_101703_1391976 : EJMOriginalGlobalDAGData.nodes 10 ⟨1391976, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1391920, by decide⟩,⟨1391975, by decide⟩,⟨1365011, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_101703_1391976 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101703 ⟨1391976, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 101703
    ⟨1391976, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1391920, by decide⟩,⟨1391975, by decide⟩,⟨1365011, by decide⟩]) unmarked_context_11_101703_1391976 node_context_11_101703_1391976
  intro a
  fin_cases a
  · exact context_12_406812_1108174
  · exact context_12_406813_1391920
  · exact context_12_406814_1391975
  · exact context_12_406815_1365011

theorem unmarked_context_10_25425_1391977 : frontier 11 ⟨1391977, by decide⟩
    (prefixCache 10 25425) (prefixPartial 10 25425) = false := by
  decide +kernel

theorem node_context_10_25425_1391977 : EJMOriginalGlobalDAGData.nodes 11 ⟨1391977, by decide⟩ =
    .split (coordinate 10) (![⟨1391803, by decide⟩,⟨892405, by decide⟩,⟨1391886, by decide⟩,⟨1391976, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25425_1391977 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25425 ⟨1391977, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25425
    ⟨1391977, by decide⟩ (by decide) (![⟨1391803, by decide⟩,⟨892405, by decide⟩,⟨1391886, by decide⟩,⟨1391976, by decide⟩]) unmarked_context_10_25425_1391977 node_context_10_25425_1391977
  intro a
  fin_cases a
  · exact context_11_101700_1391803
  · exact context_11_101701_892405
  · exact context_11_101702_1391886
  · exact context_11_101703_1391976

theorem selected_cut_49243 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 406816) = some ⟨12, 1, 0, 1108174, 406816, 1, 65536⟩ := by
  decide +kernel

theorem context_12_406816_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406816 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 406816 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 406816, 1, 65536⟩
    (by decide) selected_cut_49243

theorem selected_cut_49244 : selected 9 ⟨1392019, by decide⟩
    (prefixPartial 12 406817) = some ⟨12, 2, 0, 1392019, 406817, 2097, 65536⟩ := by
  decide +kernel

theorem context_12_406817_1392019 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406817 ⟨1392019, by decide⟩ :=
  accepted_of_selected 12 406817 ⟨1392019, by decide⟩ ⟨12, 2, 0, 1392019, 406817, 2097, 65536⟩
    (by decide) selected_cut_49244

theorem selected_cut_49245 : selected 9 ⟨1392085, by decide⟩
    (prefixPartial 12 406818) = some ⟨12, 2, 0, 1392085, 406818, 2617, 65536⟩ := by
  decide +kernel

theorem context_12_406818_1392085 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406818 ⟨1392085, by decide⟩ :=
  accepted_of_selected 12 406818 ⟨1392085, by decide⟩ ⟨12, 2, 0, 1392085, 406818, 2617, 65536⟩
    (by decide) selected_cut_49245

theorem selected_cut_49246 : selected 9 ⟨1392127, by decide⟩
    (prefixPartial 12 406819) = some ⟨12, 2, 0, 1392127, 406819, 2049, 65536⟩ := by
  decide +kernel

theorem context_12_406819_1392127 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406819 ⟨1392127, by decide⟩ :=
  accepted_of_selected 12 406819 ⟨1392127, by decide⟩ ⟨12, 2, 0, 1392127, 406819, 2049, 65536⟩
    (by decide) selected_cut_49246

theorem unmarked_context_11_101704_1392128 : frontier 10 ⟨1392128, by decide⟩
    (prefixCache 11 101704) (prefixPartial 11 101704) = false := by
  decide +kernel

theorem node_context_11_101704_1392128 : EJMOriginalGlobalDAGData.nodes 10 ⟨1392128, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1392019, by decide⟩,⟨1392085, by decide⟩,⟨1392127, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_101704_1392128 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101704 ⟨1392128, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 101704
    ⟨1392128, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1392019, by decide⟩,⟨1392085, by decide⟩,⟨1392127, by decide⟩]) unmarked_context_11_101704_1392128 node_context_11_101704_1392128
  intro a
  fin_cases a
  · exact context_12_406816_1108174
  · exact context_12_406817_1392019
  · exact context_12_406818_1392085
  · exact context_12_406819_1392127

theorem selected_cut_49247 : selected 10 ⟨1392209, by decide⟩
    (prefixPartial 11 101705) = some ⟨11, 2, 0, 1392209, 101705, 3773, 262144⟩ := by
  decide +kernel

theorem context_11_101705_1392209 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101705 ⟨1392209, by decide⟩ :=
  accepted_of_selected 11 101705 ⟨1392209, by decide⟩ ⟨11, 2, 0, 1392209, 101705, 3773, 262144⟩
    (by decide) selected_cut_49247

theorem selected_cut_49248 : selected 10 ⟨1392252, by decide⟩
    (prefixPartial 11 101706) = some ⟨11, 2, 0, 1392252, 101706, 1873, 262144⟩ := by
  decide +kernel

theorem context_11_101706_1392252 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101706 ⟨1392252, by decide⟩ :=
  accepted_of_selected 11 101706 ⟨1392252, by decide⟩ ⟨11, 2, 0, 1392252, 101706, 1873, 262144⟩
    (by decide) selected_cut_49248

theorem selected_cut_49249 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 406828) = some ⟨12, 1, 0, 1108174, 406828, 1, 65536⟩ := by
  decide +kernel

theorem context_12_406828_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406828 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 406828 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 406828, 1, 65536⟩
    (by decide) selected_cut_49249

theorem selected_cut_49250 : selected 9 ⟨1392282, by decide⟩
    (prefixPartial 12 406829) = some ⟨12, 2, 0, 1392282, 406829, 1749, 65536⟩ := by
  decide +kernel

theorem context_12_406829_1392282 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406829 ⟨1392282, by decide⟩ :=
  accepted_of_selected 12 406829 ⟨1392282, by decide⟩ ⟨12, 2, 0, 1392282, 406829, 1749, 65536⟩
    (by decide) selected_cut_49250

theorem selected_cut_49251 : selected 9 ⟨1392335, by decide⟩
    (prefixPartial 12 406830) = some ⟨12, 2, 0, 1392335, 406830, 2209, 65536⟩ := by
  decide +kernel

theorem context_12_406830_1392335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406830 ⟨1392335, by decide⟩ :=
  accepted_of_selected 12 406830 ⟨1392335, by decide⟩ ⟨12, 2, 0, 1392335, 406830, 2209, 65536⟩
    (by decide) selected_cut_49251

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
