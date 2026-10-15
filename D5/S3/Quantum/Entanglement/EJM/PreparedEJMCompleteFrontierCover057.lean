/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover056
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_05473 : selected 9 ⟨169870, by decide⟩
    (prefixPartial 12 20545) = some ⟨12, 2, 0, 169870, 20545, 3909, 65536⟩ := by
  decide +kernel

theorem context_12_20545_169870 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20545 ⟨169870, by decide⟩ :=
  accepted_of_selected 12 20545 ⟨169870, by decide⟩ ⟨12, 2, 0, 169870, 20545, 3909, 65536⟩
    (by decide) selected_cut_05473

theorem selected_cut_05474 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 82184) = some ⟨13, 1, 0, 3444, 82184, 1, 16384⟩ := by
  decide +kernel

theorem context_13_82184_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82184 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 82184 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 82184, 1, 16384⟩
    (by decide) selected_cut_05474

theorem selected_cut_05475 : selected 8 ⟨169917, by decide⟩
    (prefixPartial 13 82185) = some ⟨13, 2, 0, 169917, 82185, 2929, 16384⟩ := by
  decide +kernel

theorem context_13_82185_169917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82185 ⟨169917, by decide⟩ :=
  accepted_of_selected 13 82185 ⟨169917, by decide⟩ ⟨13, 2, 0, 169917, 82185, 2929, 16384⟩
    (by decide) selected_cut_05475

theorem selected_cut_05476 : selected 8 ⟨169945, by decide⟩
    (prefixPartial 13 82186) = some ⟨13, 2, 0, 169945, 82186, 1785, 16384⟩ := by
  decide +kernel

theorem context_13_82186_169945 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82186 ⟨169945, by decide⟩ :=
  accepted_of_selected 13 82186 ⟨169945, by decide⟩ ⟨13, 2, 0, 169945, 82186, 1785, 16384⟩
    (by decide) selected_cut_05476

theorem selected_cut_05477 : selected 8 ⟨169957, by decide⟩
    (prefixPartial 13 82187) = some ⟨13, 2, 0, 169957, 82187, 873, 16384⟩ := by
  decide +kernel

theorem context_13_82187_169957 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82187 ⟨169957, by decide⟩ :=
  accepted_of_selected 13 82187 ⟨169957, by decide⟩ ⟨13, 2, 0, 169957, 82187, 873, 16384⟩
    (by decide) selected_cut_05477

theorem unmarked_context_12_20546_169958 : frontier 9 ⟨169958, by decide⟩
    (prefixCache 12 20546) (prefixPartial 12 20546) = false := by
  decide +kernel

theorem node_context_12_20546_169958 : EJMOriginalGlobalDAGData.nodes 9 ⟨169958, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨169917, by decide⟩,⟨169945, by decide⟩,⟨169957, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_20546_169958 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20546 ⟨169958, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 20546
    ⟨169958, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨169917, by decide⟩,⟨169945, by decide⟩,⟨169957, by decide⟩]) unmarked_context_12_20546_169958 node_context_12_20546_169958
  intro a
  fin_cases a
  · exact context_13_82184_3444
  · exact context_13_82185_169917
  · exact context_13_82186_169945
  · exact context_13_82187_169957

theorem selected_cut_05478 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 20547) = some ⟨12, 1, 0, 893, 20547, 1, 65536⟩ := by
  decide +kernel

theorem context_12_20547_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20547 ⟨893, by decide⟩ :=
  accepted_of_selected 12 20547 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 20547, 1, 65536⟩
    (by decide) selected_cut_05478

theorem unmarked_context_11_5136_169959 : frontier 10 ⟨169959, by decide⟩
    (prefixCache 11 5136) (prefixPartial 11 5136) = false := by
  decide +kernel

theorem node_context_11_5136_169959 : EJMOriginalGlobalDAGData.nodes 10 ⟨169959, by decide⟩ =
    .split (coordinate 11) (![⟨169790, by decide⟩,⟨169870, by decide⟩,⟨169958, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5136_169959 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5136 ⟨169959, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5136
    ⟨169959, by decide⟩ (by decide) (![⟨169790, by decide⟩,⟨169870, by decide⟩,⟨169958, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_5136_169959 node_context_11_5136_169959
  intro a
  fin_cases a
  · exact context_12_20544_169790
  · exact context_12_20545_169870
  · exact context_12_20546_169958
  · exact context_12_20547_893

theorem selected_cut_05479 : selected 9 ⟨169987, by decide⟩
    (prefixPartial 12 20548) = some ⟨12, 2, 0, 169987, 20548, 1485, 65536⟩ := by
  decide +kernel

theorem context_12_20548_169987 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20548 ⟨169987, by decide⟩ :=
  accepted_of_selected 12 20548 ⟨169987, by decide⟩ ⟨12, 2, 0, 169987, 20548, 1485, 65536⟩
    (by decide) selected_cut_05479

theorem selected_cut_05480 : selected 9 ⟨170030, by decide⟩
    (prefixPartial 12 20549) = some ⟨12, 2, 0, 170030, 20549, 2609, 65536⟩ := by
  decide +kernel

theorem context_12_20549_170030 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20549 ⟨170030, by decide⟩ :=
  accepted_of_selected 12 20549 ⟨170030, by decide⟩ ⟨12, 2, 0, 170030, 20549, 2609, 65536⟩
    (by decide) selected_cut_05480

theorem selected_cut_05481 : selected 9 ⟨170092, by decide⟩
    (prefixPartial 12 20550) = some ⟨12, 2, 0, 170092, 20550, 4001, 65536⟩ := by
  decide +kernel

theorem context_12_20550_170092 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20550 ⟨170092, by decide⟩ :=
  accepted_of_selected 12 20550 ⟨170092, by decide⟩ ⟨12, 2, 0, 170092, 20550, 4001, 65536⟩
    (by decide) selected_cut_05481

theorem selected_cut_05482 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 20551) = some ⟨12, 1, 0, 893, 20551, 1, 65536⟩ := by
  decide +kernel

theorem context_12_20551_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20551 ⟨893, by decide⟩ :=
  accepted_of_selected 12 20551 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 20551, 1, 65536⟩
    (by decide) selected_cut_05482

theorem unmarked_context_11_5137_170093 : frontier 10 ⟨170093, by decide⟩
    (prefixCache 11 5137) (prefixPartial 11 5137) = false := by
  decide +kernel

theorem node_context_11_5137_170093 : EJMOriginalGlobalDAGData.nodes 10 ⟨170093, by decide⟩ =
    .split (coordinate 11) (![⟨169987, by decide⟩,⟨170030, by decide⟩,⟨170092, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5137_170093 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5137 ⟨170093, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5137
    ⟨170093, by decide⟩ (by decide) (![⟨169987, by decide⟩,⟨170030, by decide⟩,⟨170092, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_5137_170093 node_context_11_5137_170093
  intro a
  fin_cases a
  · exact context_12_20548_169987
  · exact context_12_20549_170030
  · exact context_12_20550_170092
  · exact context_12_20551_893

theorem selected_cut_05483 : selected 9 ⟨170131, by decide⟩
    (prefixPartial 12 20552) = some ⟨12, 2, 0, 170131, 20552, 2685, 65536⟩ := by
  decide +kernel

theorem context_12_20552_170131 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20552 ⟨170131, by decide⟩ :=
  accepted_of_selected 12 20552 ⟨170131, by decide⟩ ⟨12, 2, 0, 170131, 20552, 2685, 65536⟩
    (by decide) selected_cut_05483

theorem selected_cut_05484 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 82212) = some ⟨13, 1, 0, 3444, 82212, 1, 16384⟩ := by
  decide +kernel

theorem context_13_82212_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82212 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 82212 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 82212, 1, 16384⟩
    (by decide) selected_cut_05484

theorem selected_cut_05485 : selected 8 ⟨170165, by decide⟩
    (prefixPartial 13 82213) = some ⟨13, 2, 0, 170165, 82213, 2513, 16384⟩ := by
  decide +kernel

theorem context_13_82213_170165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82213 ⟨170165, by decide⟩ :=
  accepted_of_selected 13 82213 ⟨170165, by decide⟩ ⟨13, 2, 0, 170165, 82213, 2513, 16384⟩
    (by decide) selected_cut_05485

theorem selected_cut_05486 : selected 8 ⟨170187, by decide⟩
    (prefixPartial 13 82214) = some ⟨13, 2, 0, 170187, 82214, 2117, 16384⟩ := by
  decide +kernel

theorem context_13_82214_170187 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82214 ⟨170187, by decide⟩ :=
  accepted_of_selected 13 82214 ⟨170187, by decide⟩ ⟨13, 2, 0, 170187, 82214, 2117, 16384⟩
    (by decide) selected_cut_05486

theorem selected_cut_05487 : selected 8 ⟨170196, by decide⟩
    (prefixPartial 13 82215) = some ⟨13, 2, 0, 170196, 82215, 1037, 16384⟩ := by
  decide +kernel

theorem context_13_82215_170196 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82215 ⟨170196, by decide⟩ :=
  accepted_of_selected 13 82215 ⟨170196, by decide⟩ ⟨13, 2, 0, 170196, 82215, 1037, 16384⟩
    (by decide) selected_cut_05487

theorem unmarked_context_12_20553_170197 : frontier 9 ⟨170197, by decide⟩
    (prefixCache 12 20553) (prefixPartial 12 20553) = false := by
  decide +kernel

theorem node_context_12_20553_170197 : EJMOriginalGlobalDAGData.nodes 9 ⟨170197, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨170165, by decide⟩,⟨170187, by decide⟩,⟨170196, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_20553_170197 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20553 ⟨170197, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 20553
    ⟨170197, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨170165, by decide⟩,⟨170187, by decide⟩,⟨170196, by decide⟩]) unmarked_context_12_20553_170197 node_context_12_20553_170197
  intro a
  fin_cases a
  · exact context_13_82212_3444
  · exact context_13_82213_170165
  · exact context_13_82214_170187
  · exact context_13_82215_170196

theorem selected_cut_05488 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 82216) = some ⟨13, 1, 0, 3444, 82216, 1, 16384⟩ := by
  decide +kernel

theorem context_13_82216_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82216 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 82216 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 82216, 1, 16384⟩
    (by decide) selected_cut_05488

theorem selected_cut_05489 : selected 8 ⟨170226, by decide⟩
    (prefixPartial 13 82217) = some ⟨13, 2, 0, 170226, 82217, 1985, 16384⟩ := by
  decide +kernel

theorem context_13_82217_170226 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82217 ⟨170226, by decide⟩ :=
  accepted_of_selected 13 82217 ⟨170226, by decide⟩ ⟨13, 2, 0, 170226, 82217, 1985, 16384⟩
    (by decide) selected_cut_05489

theorem selected_cut_05490 : selected 8 ⟨170251, by decide⟩
    (prefixPartial 13 82218) = some ⟨13, 2, 0, 170251, 82218, 1505, 16384⟩ := by
  decide +kernel

theorem context_13_82218_170251 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82218 ⟨170251, by decide⟩ :=
  accepted_of_selected 13 82218 ⟨170251, by decide⟩ ⟨13, 2, 0, 170251, 82218, 1505, 16384⟩
    (by decide) selected_cut_05490

theorem selected_cut_05491 : selected 8 ⟨170259, by decide⟩
    (prefixPartial 13 82219) = some ⟨13, 2, 0, 170259, 82219, 769, 16384⟩ := by
  decide +kernel

theorem context_13_82219_170259 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82219 ⟨170259, by decide⟩ :=
  accepted_of_selected 13 82219 ⟨170259, by decide⟩ ⟨13, 2, 0, 170259, 82219, 769, 16384⟩
    (by decide) selected_cut_05491

theorem unmarked_context_12_20554_170260 : frontier 9 ⟨170260, by decide⟩
    (prefixCache 12 20554) (prefixPartial 12 20554) = false := by
  decide +kernel

theorem node_context_12_20554_170260 : EJMOriginalGlobalDAGData.nodes 9 ⟨170260, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨170226, by decide⟩,⟨170251, by decide⟩,⟨170259, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_20554_170260 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20554 ⟨170260, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 20554
    ⟨170260, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨170226, by decide⟩,⟨170251, by decide⟩,⟨170259, by decide⟩]) unmarked_context_12_20554_170260 node_context_12_20554_170260
  intro a
  fin_cases a
  · exact context_13_82216_3444
  · exact context_13_82217_170226
  · exact context_13_82218_170251
  · exact context_13_82219_170259

theorem selected_cut_05492 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 82220) = some ⟨13, 1, 0, 3444, 82220, 1, 16384⟩ := by
  decide +kernel

theorem context_13_82220_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82220 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 82220 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 82220, 1, 16384⟩
    (by decide) selected_cut_05492

theorem selected_cut_05493 : selected 8 ⟨170291, by decide⟩
    (prefixPartial 13 82221) = some ⟨13, 2, 0, 170291, 82221, 1849, 16384⟩ := by
  decide +kernel

theorem context_13_82221_170291 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82221 ⟨170291, by decide⟩ :=
  accepted_of_selected 13 82221 ⟨170291, by decide⟩ ⟨13, 2, 0, 170291, 82221, 1849, 16384⟩
    (by decide) selected_cut_05493

theorem selected_cut_05494 : selected 8 ⟨170312, by decide⟩
    (prefixPartial 13 82222) = some ⟨13, 2, 0, 170312, 82222, 1609, 16384⟩ := by
  decide +kernel

theorem context_13_82222_170312 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82222 ⟨170312, by decide⟩ :=
  accepted_of_selected 13 82222 ⟨170312, by decide⟩ ⟨13, 2, 0, 170312, 82222, 1609, 16384⟩
    (by decide) selected_cut_05494

theorem selected_cut_05495 : selected 8 ⟨170325, by decide⟩
    (prefixPartial 13 82223) = some ⟨13, 2, 0, 170325, 82223, 893, 16384⟩ := by
  decide +kernel

theorem context_13_82223_170325 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82223 ⟨170325, by decide⟩ :=
  accepted_of_selected 13 82223 ⟨170325, by decide⟩ ⟨13, 2, 0, 170325, 82223, 893, 16384⟩
    (by decide) selected_cut_05495

theorem unmarked_context_12_20555_170326 : frontier 9 ⟨170326, by decide⟩
    (prefixCache 12 20555) (prefixPartial 12 20555) = false := by
  decide +kernel

theorem node_context_12_20555_170326 : EJMOriginalGlobalDAGData.nodes 9 ⟨170326, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨170291, by decide⟩,⟨170312, by decide⟩,⟨170325, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_20555_170326 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20555 ⟨170326, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 20555
    ⟨170326, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨170291, by decide⟩,⟨170312, by decide⟩,⟨170325, by decide⟩]) unmarked_context_12_20555_170326 node_context_12_20555_170326
  intro a
  fin_cases a
  · exact context_13_82220_3444
  · exact context_13_82221_170291
  · exact context_13_82222_170312
  · exact context_13_82223_170325

theorem unmarked_context_11_5138_170327 : frontier 10 ⟨170327, by decide⟩
    (prefixCache 11 5138) (prefixPartial 11 5138) = false := by
  decide +kernel

theorem node_context_11_5138_170327 : EJMOriginalGlobalDAGData.nodes 10 ⟨170327, by decide⟩ =
    .split (coordinate 11) (![⟨170131, by decide⟩,⟨170197, by decide⟩,⟨170260, by decide⟩,⟨170326, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5138_170327 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5138 ⟨170327, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5138
    ⟨170327, by decide⟩ (by decide) (![⟨170131, by decide⟩,⟨170197, by decide⟩,⟨170260, by decide⟩,⟨170326, by decide⟩]) unmarked_context_11_5138_170327 node_context_11_5138_170327
  intro a
  fin_cases a
  · exact context_12_20552_170131
  · exact context_12_20553_170197
  · exact context_12_20554_170260
  · exact context_12_20555_170326

theorem selected_cut_05496 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 5139) = some ⟨11, 1, 0, 1736, 5139, 1, 262144⟩ := by
  decide +kernel

theorem context_11_5139_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5139 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 5139 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 5139, 1, 262144⟩
    (by decide) selected_cut_05496

theorem unmarked_context_10_1284_170328 : frontier 11 ⟨170328, by decide⟩
    (prefixCache 10 1284) (prefixPartial 10 1284) = false := by
  decide +kernel

theorem node_context_10_1284_170328 : EJMOriginalGlobalDAGData.nodes 11 ⟨170328, by decide⟩ =
    .split (coordinate 10) (![⟨169959, by decide⟩,⟨170093, by decide⟩,⟨170327, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1284_170328 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1284 ⟨170328, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1284
    ⟨170328, by decide⟩ (by decide) (![⟨169959, by decide⟩,⟨170093, by decide⟩,⟨170327, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_1284_170328 node_context_10_1284_170328
  intro a
  fin_cases a
  · exact context_11_5136_169959
  · exact context_11_5137_170093
  · exact context_11_5138_170327
  · exact context_11_5139_1736

theorem selected_cut_05497 : selected 9 ⟨170375, by decide⟩
    (prefixPartial 12 20560) = some ⟨12, 2, 0, 170375, 20560, 2885, 65536⟩ := by
  decide +kernel

theorem context_12_20560_170375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20560 ⟨170375, by decide⟩ :=
  accepted_of_selected 12 20560 ⟨170375, by decide⟩ ⟨12, 2, 0, 170375, 20560, 2885, 65536⟩
    (by decide) selected_cut_05497

theorem selected_cut_05498 : selected 9 ⟨170414, by decide⟩
    (prefixPartial 12 20561) = some ⟨12, 2, 0, 170414, 20561, 3041, 65536⟩ := by
  decide +kernel

theorem context_12_20561_170414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20561 ⟨170414, by decide⟩ :=
  accepted_of_selected 12 20561 ⟨170414, by decide⟩ ⟨12, 2, 0, 170414, 20561, 3041, 65536⟩
    (by decide) selected_cut_05498

theorem selected_cut_05499 : selected 9 ⟨170467, by decide⟩
    (prefixPartial 12 20562) = some ⟨12, 2, 0, 170467, 20562, 4017, 65536⟩ := by
  decide +kernel

theorem context_12_20562_170467 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20562 ⟨170467, by decide⟩ :=
  accepted_of_selected 12 20562 ⟨170467, by decide⟩ ⟨12, 2, 0, 170467, 20562, 4017, 65536⟩
    (by decide) selected_cut_05499

theorem selected_cut_05500 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 20563) = some ⟨12, 1, 0, 893, 20563, 1, 65536⟩ := by
  decide +kernel

theorem context_12_20563_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20563 ⟨893, by decide⟩ :=
  accepted_of_selected 12 20563 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 20563, 1, 65536⟩
    (by decide) selected_cut_05500

theorem unmarked_context_11_5140_170468 : frontier 10 ⟨170468, by decide⟩
    (prefixCache 11 5140) (prefixPartial 11 5140) = false := by
  decide +kernel

theorem node_context_11_5140_170468 : EJMOriginalGlobalDAGData.nodes 10 ⟨170468, by decide⟩ =
    .split (coordinate 11) (![⟨170375, by decide⟩,⟨170414, by decide⟩,⟨170467, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5140_170468 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5140 ⟨170468, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5140
    ⟨170468, by decide⟩ (by decide) (![⟨170375, by decide⟩,⟨170414, by decide⟩,⟨170467, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_5140_170468 node_context_11_5140_170468
  intro a
  fin_cases a
  · exact context_12_20560_170375
  · exact context_12_20561_170414
  · exact context_12_20562_170467
  · exact context_12_20563_893

theorem selected_cut_05501 : selected 9 ⟨170503, by decide⟩
    (prefixPartial 12 20564) = some ⟨12, 2, 0, 170503, 20564, 1749, 65536⟩ := by
  decide +kernel

theorem context_12_20564_170503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20564 ⟨170503, by decide⟩ :=
  accepted_of_selected 12 20564 ⟨170503, by decide⟩ ⟨12, 2, 0, 170503, 20564, 1749, 65536⟩
    (by decide) selected_cut_05501

theorem selected_cut_05502 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 20565) = some ⟨12, 1, 0, 170504, 20565, 1, 65536⟩ := by
  decide +kernel

theorem context_12_20565_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20565 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 20565 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 20565, 1, 65536⟩
    (by decide) selected_cut_05502

theorem selected_cut_05503 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 82264) = some ⟨13, 1, 0, 3444, 82264, 1, 16384⟩ := by
  decide +kernel

theorem context_13_82264_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82264 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 82264 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 82264, 1, 16384⟩
    (by decide) selected_cut_05503

theorem selected_cut_05504 : selected 8 ⟨170522, by decide⟩
    (prefixPartial 13 82265) = some ⟨13, 2, 0, 170522, 82265, 1777, 16384⟩ := by
  decide +kernel

theorem context_13_82265_170522 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82265 ⟨170522, by decide⟩ :=
  accepted_of_selected 13 82265 ⟨170522, by decide⟩ ⟨13, 2, 0, 170522, 82265, 1777, 16384⟩
    (by decide) selected_cut_05504

theorem selected_cut_05505 : selected 8 ⟨170543, by decide⟩
    (prefixPartial 13 82266) = some ⟨13, 2, 0, 170543, 82266, 1801, 16384⟩ := by
  decide +kernel

theorem context_13_82266_170543 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82266 ⟨170543, by decide⟩ :=
  accepted_of_selected 13 82266 ⟨170543, by decide⟩ ⟨13, 2, 0, 170543, 82266, 1801, 16384⟩
    (by decide) selected_cut_05505

theorem selected_cut_05506 : selected 8 ⟨170552, by decide⟩
    (prefixPartial 13 82267) = some ⟨13, 2, 0, 170552, 82267, 809, 16384⟩ := by
  decide +kernel

theorem context_13_82267_170552 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82267 ⟨170552, by decide⟩ :=
  accepted_of_selected 13 82267 ⟨170552, by decide⟩ ⟨13, 2, 0, 170552, 82267, 809, 16384⟩
    (by decide) selected_cut_05506

theorem unmarked_context_12_20566_170553 : frontier 9 ⟨170553, by decide⟩
    (prefixCache 12 20566) (prefixPartial 12 20566) = false := by
  decide +kernel

theorem node_context_12_20566_170553 : EJMOriginalGlobalDAGData.nodes 9 ⟨170553, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨170522, by decide⟩,⟨170543, by decide⟩,⟨170552, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_20566_170553 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20566 ⟨170553, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 20566
    ⟨170553, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨170522, by decide⟩,⟨170543, by decide⟩,⟨170552, by decide⟩]) unmarked_context_12_20566_170553 node_context_12_20566_170553
  intro a
  fin_cases a
  · exact context_13_82264_3444
  · exact context_13_82265_170522
  · exact context_13_82266_170543
  · exact context_13_82267_170552

theorem selected_cut_05507 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 20567) = some ⟨12, 1, 0, 893, 20567, 1, 65536⟩ := by
  decide +kernel

theorem context_12_20567_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20567 ⟨893, by decide⟩ :=
  accepted_of_selected 12 20567 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 20567, 1, 65536⟩
    (by decide) selected_cut_05507

theorem unmarked_context_11_5141_170554 : frontier 10 ⟨170554, by decide⟩
    (prefixCache 11 5141) (prefixPartial 11 5141) = false := by
  decide +kernel

theorem node_context_11_5141_170554 : EJMOriginalGlobalDAGData.nodes 10 ⟨170554, by decide⟩ =
    .split (coordinate 11) (![⟨170503, by decide⟩,⟨170504, by decide⟩,⟨170553, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5141_170554 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5141 ⟨170554, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5141
    ⟨170554, by decide⟩ (by decide) (![⟨170503, by decide⟩,⟨170504, by decide⟩,⟨170553, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_5141_170554 node_context_11_5141_170554
  intro a
  fin_cases a
  · exact context_12_20564_170503
  · exact context_12_20565_170504
  · exact context_12_20566_170553
  · exact context_12_20567_893

theorem selected_cut_05508 : selected 9 ⟨170603, by decide⟩
    (prefixPartial 12 20568) = some ⟨12, 2, 0, 170603, 20568, 3229, 65536⟩ := by
  decide +kernel

theorem context_12_20568_170603 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20568 ⟨170603, by decide⟩ :=
  accepted_of_selected 12 20568 ⟨170603, by decide⟩ ⟨12, 2, 0, 170603, 20568, 3229, 65536⟩
    (by decide) selected_cut_05508

theorem selected_cut_05509 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 82276) = some ⟨13, 1, 0, 3444, 82276, 1, 16384⟩ := by
  decide +kernel

theorem context_13_82276_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82276 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 82276 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 82276, 1, 16384⟩
    (by decide) selected_cut_05509

theorem selected_cut_05510 : selected 8 ⟨170643, by decide⟩
    (prefixPartial 13 82277) = some ⟨13, 2, 0, 170643, 82277, 2085, 16384⟩ := by
  decide +kernel

theorem context_13_82277_170643 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82277 ⟨170643, by decide⟩ :=
  accepted_of_selected 13 82277 ⟨170643, by decide⟩ ⟨13, 2, 0, 170643, 82277, 2085, 16384⟩
    (by decide) selected_cut_05510

theorem selected_cut_05511 : selected 8 ⟨170700, by decide⟩
    (prefixPartial 13 82278) = some ⟨13, 2, 0, 170700, 82278, 2645, 16384⟩ := by
  decide +kernel

theorem context_13_82278_170700 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82278 ⟨170700, by decide⟩ :=
  accepted_of_selected 13 82278 ⟨170700, by decide⟩ ⟨13, 2, 0, 170700, 82278, 2645, 16384⟩
    (by decide) selected_cut_05511

theorem selected_cut_05512 : selected 8 ⟨170710, by decide⟩
    (prefixPartial 13 82279) = some ⟨13, 2, 0, 170710, 82279, 1181, 16384⟩ := by
  decide +kernel

theorem context_13_82279_170710 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82279 ⟨170710, by decide⟩ :=
  accepted_of_selected 13 82279 ⟨170710, by decide⟩ ⟨13, 2, 0, 170710, 82279, 1181, 16384⟩
    (by decide) selected_cut_05512

theorem unmarked_context_12_20569_170711 : frontier 9 ⟨170711, by decide⟩
    (prefixCache 12 20569) (prefixPartial 12 20569) = false := by
  decide +kernel

theorem node_context_12_20569_170711 : EJMOriginalGlobalDAGData.nodes 9 ⟨170711, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨170643, by decide⟩,⟨170700, by decide⟩,⟨170710, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_20569_170711 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20569 ⟨170711, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 20569
    ⟨170711, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨170643, by decide⟩,⟨170700, by decide⟩,⟨170710, by decide⟩]) unmarked_context_12_20569_170711 node_context_12_20569_170711
  intro a
  fin_cases a
  · exact context_13_82276_3444
  · exact context_13_82277_170643
  · exact context_13_82278_170700
  · exact context_13_82279_170710

theorem selected_cut_05513 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 82280) = some ⟨13, 1, 0, 3444, 82280, 1, 16384⟩ := by
  decide +kernel

theorem context_13_82280_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82280 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 82280 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 82280, 1, 16384⟩
    (by decide) selected_cut_05513

theorem selected_cut_05514 : selected 8 ⟨170728, by decide⟩
    (prefixPartial 13 82281) = some ⟨13, 2, 0, 170728, 82281, 1601, 16384⟩ := by
  decide +kernel

theorem context_13_82281_170728 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82281 ⟨170728, by decide⟩ :=
  accepted_of_selected 13 82281 ⟨170728, by decide⟩ ⟨13, 2, 0, 170728, 82281, 1601, 16384⟩
    (by decide) selected_cut_05514

theorem selected_cut_05515 : selected 8 ⟨170749, by decide⟩
    (prefixPartial 13 82282) = some ⟨13, 2, 0, 170749, 82282, 1905, 16384⟩ := by
  decide +kernel

theorem context_13_82282_170749 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82282 ⟨170749, by decide⟩ :=
  accepted_of_selected 13 82282 ⟨170749, by decide⟩ ⟨13, 2, 0, 170749, 82282, 1905, 16384⟩
    (by decide) selected_cut_05515

theorem selected_cut_05516 : selected 8 ⟨170759, by decide⟩
    (prefixPartial 13 82283) = some ⟨13, 2, 0, 170759, 82283, 989, 16384⟩ := by
  decide +kernel

theorem context_13_82283_170759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82283 ⟨170759, by decide⟩ :=
  accepted_of_selected 13 82283 ⟨170759, by decide⟩ ⟨13, 2, 0, 170759, 82283, 989, 16384⟩
    (by decide) selected_cut_05516

theorem unmarked_context_12_20570_170760 : frontier 9 ⟨170760, by decide⟩
    (prefixCache 12 20570) (prefixPartial 12 20570) = false := by
  decide +kernel

theorem node_context_12_20570_170760 : EJMOriginalGlobalDAGData.nodes 9 ⟨170760, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨170728, by decide⟩,⟨170749, by decide⟩,⟨170759, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_20570_170760 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20570 ⟨170760, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 20570
    ⟨170760, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨170728, by decide⟩,⟨170749, by decide⟩,⟨170759, by decide⟩]) unmarked_context_12_20570_170760 node_context_12_20570_170760
  intro a
  fin_cases a
  · exact context_13_82280_3444
  · exact context_13_82281_170728
  · exact context_13_82282_170749
  · exact context_13_82283_170759

theorem selected_cut_05517 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 82284) = some ⟨13, 1, 0, 3444, 82284, 1, 16384⟩ := by
  decide +kernel

theorem context_13_82284_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82284 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 82284 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 82284, 1, 16384⟩
    (by decide) selected_cut_05517

theorem selected_cut_05518 : selected 8 ⟨170782, by decide⟩
    (prefixPartial 13 82285) = some ⟨13, 2, 0, 170782, 82285, 1457, 16384⟩ := by
  decide +kernel

theorem context_13_82285_170782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82285 ⟨170782, by decide⟩ :=
  accepted_of_selected 13 82285 ⟨170782, by decide⟩ ⟨13, 2, 0, 170782, 82285, 1457, 16384⟩
    (by decide) selected_cut_05518

theorem selected_cut_05519 : selected 8 ⟨170804, by decide⟩
    (prefixPartial 13 82286) = some ⟨13, 2, 0, 170804, 82286, 2105, 16384⟩ := by
  decide +kernel

theorem context_13_82286_170804 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82286 ⟨170804, by decide⟩ :=
  accepted_of_selected 13 82286 ⟨170804, by decide⟩ ⟨13, 2, 0, 170804, 82286, 2105, 16384⟩
    (by decide) selected_cut_05519

theorem selected_cut_05520 : selected 8 ⟨170813, by decide⟩
    (prefixPartial 13 82287) = some ⟨13, 2, 0, 170813, 82287, 1101, 16384⟩ := by
  decide +kernel

theorem context_13_82287_170813 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82287 ⟨170813, by decide⟩ :=
  accepted_of_selected 13 82287 ⟨170813, by decide⟩ ⟨13, 2, 0, 170813, 82287, 1101, 16384⟩
    (by decide) selected_cut_05520

theorem unmarked_context_12_20571_170814 : frontier 9 ⟨170814, by decide⟩
    (prefixCache 12 20571) (prefixPartial 12 20571) = false := by
  decide +kernel

theorem node_context_12_20571_170814 : EJMOriginalGlobalDAGData.nodes 9 ⟨170814, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨170782, by decide⟩,⟨170804, by decide⟩,⟨170813, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_20571_170814 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20571 ⟨170814, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 20571
    ⟨170814, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨170782, by decide⟩,⟨170804, by decide⟩,⟨170813, by decide⟩]) unmarked_context_12_20571_170814 node_context_12_20571_170814
  intro a
  fin_cases a
  · exact context_13_82284_3444
  · exact context_13_82285_170782
  · exact context_13_82286_170804
  · exact context_13_82287_170813

theorem unmarked_context_11_5142_170815 : frontier 10 ⟨170815, by decide⟩
    (prefixCache 11 5142) (prefixPartial 11 5142) = false := by
  decide +kernel

theorem node_context_11_5142_170815 : EJMOriginalGlobalDAGData.nodes 10 ⟨170815, by decide⟩ =
    .split (coordinate 11) (![⟨170603, by decide⟩,⟨170711, by decide⟩,⟨170760, by decide⟩,⟨170814, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5142_170815 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5142 ⟨170815, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5142
    ⟨170815, by decide⟩ (by decide) (![⟨170603, by decide⟩,⟨170711, by decide⟩,⟨170760, by decide⟩,⟨170814, by decide⟩]) unmarked_context_11_5142_170815 node_context_11_5142_170815
  intro a
  fin_cases a
  · exact context_12_20568_170603
  · exact context_12_20569_170711
  · exact context_12_20570_170760
  · exact context_12_20571_170814

theorem selected_cut_05521 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 5143) = some ⟨11, 1, 0, 1736, 5143, 1, 262144⟩ := by
  decide +kernel

theorem context_11_5143_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5143 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 5143 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 5143, 1, 262144⟩
    (by decide) selected_cut_05521

theorem unmarked_context_10_1285_170816 : frontier 11 ⟨170816, by decide⟩
    (prefixCache 10 1285) (prefixPartial 10 1285) = false := by
  decide +kernel

theorem node_context_10_1285_170816 : EJMOriginalGlobalDAGData.nodes 11 ⟨170816, by decide⟩ =
    .split (coordinate 10) (![⟨170468, by decide⟩,⟨170554, by decide⟩,⟨170815, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1285_170816 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1285 ⟨170816, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1285
    ⟨170816, by decide⟩ (by decide) (![⟨170468, by decide⟩,⟨170554, by decide⟩,⟨170815, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_1285_170816 node_context_10_1285_170816
  intro a
  fin_cases a
  · exact context_11_5140_170468
  · exact context_11_5141_170554
  · exact context_11_5142_170815
  · exact context_11_5143_1736

theorem selected_cut_05522 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 82304) = some ⟨13, 1, 0, 3444, 82304, 1, 16384⟩ := by
  decide +kernel

theorem context_13_82304_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82304 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 82304 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 82304, 1, 16384⟩
    (by decide) selected_cut_05522

theorem selected_cut_05523 : selected 8 ⟨170833, by decide⟩
    (prefixPartial 13 82305) = some ⟨13, 2, 0, 170833, 82305, 1549, 16384⟩ := by
  decide +kernel

theorem context_13_82305_170833 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82305 ⟨170833, by decide⟩ :=
  accepted_of_selected 13 82305 ⟨170833, by decide⟩ ⟨13, 2, 0, 170833, 82305, 1549, 16384⟩
    (by decide) selected_cut_05523

theorem selected_cut_05524 : selected 8 ⟨170868, by decide⟩
    (prefixPartial 13 82306) = some ⟨13, 2, 0, 170868, 82306, 1953, 16384⟩ := by
  decide +kernel

theorem context_13_82306_170868 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82306 ⟨170868, by decide⟩ :=
  accepted_of_selected 13 82306 ⟨170868, by decide⟩ ⟨13, 2, 0, 170868, 82306, 1953, 16384⟩
    (by decide) selected_cut_05524

theorem selected_cut_05525 : selected 8 ⟨170882, by decide⟩
    (prefixPartial 13 82307) = some ⟨13, 2, 0, 170882, 82307, 1037, 16384⟩ := by
  decide +kernel

theorem context_13_82307_170882 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82307 ⟨170882, by decide⟩ :=
  accepted_of_selected 13 82307 ⟨170882, by decide⟩ ⟨13, 2, 0, 170882, 82307, 1037, 16384⟩
    (by decide) selected_cut_05525

theorem unmarked_context_12_20576_170883 : frontier 9 ⟨170883, by decide⟩
    (prefixCache 12 20576) (prefixPartial 12 20576) = false := by
  decide +kernel

theorem node_context_12_20576_170883 : EJMOriginalGlobalDAGData.nodes 9 ⟨170883, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨170833, by decide⟩,⟨170868, by decide⟩,⟨170882, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_20576_170883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20576 ⟨170883, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 20576
    ⟨170883, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨170833, by decide⟩,⟨170868, by decide⟩,⟨170882, by decide⟩]) unmarked_context_12_20576_170883 node_context_12_20576_170883
  intro a
  fin_cases a
  · exact context_13_82304_3444
  · exact context_13_82305_170833
  · exact context_13_82306_170868
  · exact context_13_82307_170882

theorem selected_cut_05526 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 82308) = some ⟨13, 1, 0, 3444, 82308, 1, 16384⟩ := by
  decide +kernel

theorem context_13_82308_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82308 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 82308 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 82308, 1, 16384⟩
    (by decide) selected_cut_05526

theorem selected_cut_05527 : selected 8 ⟨170904, by decide⟩
    (prefixPartial 13 82309) = some ⟨13, 2, 0, 170904, 82309, 1437, 16384⟩ := by
  decide +kernel

theorem context_13_82309_170904 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82309 ⟨170904, by decide⟩ :=
  accepted_of_selected 13 82309 ⟨170904, by decide⟩ ⟨13, 2, 0, 170904, 82309, 1437, 16384⟩
    (by decide) selected_cut_05527

theorem selected_cut_05528 : selected 8 ⟨170926, by decide⟩
    (prefixPartial 13 82310) = some ⟨13, 2, 0, 170926, 82310, 1925, 16384⟩ := by
  decide +kernel

theorem context_13_82310_170926 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82310 ⟨170926, by decide⟩ :=
  accepted_of_selected 13 82310 ⟨170926, by decide⟩ ⟨13, 2, 0, 170926, 82310, 1925, 16384⟩
    (by decide) selected_cut_05528

theorem selected_cut_05529 : selected 8 ⟨170935, by decide⟩
    (prefixPartial 13 82311) = some ⟨13, 2, 0, 170935, 82311, 1097, 16384⟩ := by
  decide +kernel

theorem context_13_82311_170935 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82311 ⟨170935, by decide⟩ :=
  accepted_of_selected 13 82311 ⟨170935, by decide⟩ ⟨13, 2, 0, 170935, 82311, 1097, 16384⟩
    (by decide) selected_cut_05529

theorem unmarked_context_12_20577_170936 : frontier 9 ⟨170936, by decide⟩
    (prefixCache 12 20577) (prefixPartial 12 20577) = false := by
  decide +kernel

theorem node_context_12_20577_170936 : EJMOriginalGlobalDAGData.nodes 9 ⟨170936, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨170904, by decide⟩,⟨170926, by decide⟩,⟨170935, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_20577_170936 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20577 ⟨170936, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 20577
    ⟨170936, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨170904, by decide⟩,⟨170926, by decide⟩,⟨170935, by decide⟩]) unmarked_context_12_20577_170936 node_context_12_20577_170936
  intro a
  fin_cases a
  · exact context_13_82308_3444
  · exact context_13_82309_170904
  · exact context_13_82310_170926
  · exact context_13_82311_170935

theorem selected_cut_05530 : selected 9 ⟨170992, by decide⟩
    (prefixPartial 12 20578) = some ⟨12, 2, 0, 170992, 20578, 3509, 65536⟩ := by
  decide +kernel

theorem context_12_20578_170992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20578 ⟨170992, by decide⟩ :=
  accepted_of_selected 12 20578 ⟨170992, by decide⟩ ⟨12, 2, 0, 170992, 20578, 3509, 65536⟩
    (by decide) selected_cut_05530

theorem selected_cut_05531 : selected 9 ⟨171035, by decide⟩
    (prefixPartial 12 20579) = some ⟨12, 2, 0, 171035, 20579, 3077, 65536⟩ := by
  decide +kernel

theorem context_12_20579_171035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20579 ⟨171035, by decide⟩ :=
  accepted_of_selected 12 20579 ⟨171035, by decide⟩ ⟨12, 2, 0, 171035, 20579, 3077, 65536⟩
    (by decide) selected_cut_05531

theorem unmarked_context_11_5144_171036 : frontier 10 ⟨171036, by decide⟩
    (prefixCache 11 5144) (prefixPartial 11 5144) = false := by
  decide +kernel

theorem node_context_11_5144_171036 : EJMOriginalGlobalDAGData.nodes 10 ⟨171036, by decide⟩ =
    .split (coordinate 11) (![⟨170883, by decide⟩,⟨170936, by decide⟩,⟨170992, by decide⟩,⟨171035, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5144_171036 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5144 ⟨171036, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5144
    ⟨171036, by decide⟩ (by decide) (![⟨170883, by decide⟩,⟨170936, by decide⟩,⟨170992, by decide⟩,⟨171035, by decide⟩]) unmarked_context_11_5144_171036 node_context_11_5144_171036
  intro a
  fin_cases a
  · exact context_12_20576_170883
  · exact context_12_20577_170936
  · exact context_12_20578_170992
  · exact context_12_20579_171035

theorem selected_cut_05532 : selected 9 ⟨171084, by decide⟩
    (prefixPartial 12 20580) = some ⟨12, 2, 0, 171084, 20580, 2653, 65536⟩ := by
  decide +kernel

theorem context_12_20580_171084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20580 ⟨171084, by decide⟩ :=
  accepted_of_selected 12 20580 ⟨171084, by decide⟩ ⟨12, 2, 0, 171084, 20580, 2653, 65536⟩
    (by decide) selected_cut_05532

theorem selected_cut_05533 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 82324) = some ⟨13, 1, 0, 3444, 82324, 1, 16384⟩ := by
  decide +kernel

theorem context_13_82324_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82324 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 82324 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 82324, 1, 16384⟩
    (by decide) selected_cut_05533

theorem selected_cut_05534 : selected 8 ⟨171101, by decide⟩
    (prefixPartial 13 82325) = some ⟨13, 2, 0, 171101, 82325, 1077, 16384⟩ := by
  decide +kernel

theorem context_13_82325_171101 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82325 ⟨171101, by decide⟩ :=
  accepted_of_selected 13 82325 ⟨171101, by decide⟩ ⟨13, 2, 0, 171101, 82325, 1077, 16384⟩
    (by decide) selected_cut_05534

theorem selected_cut_05535 : selected 8 ⟨171130, by decide⟩
    (prefixPartial 13 82326) = some ⟨13, 2, 0, 171130, 82326, 2045, 16384⟩ := by
  decide +kernel

theorem context_13_82326_171130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82326 ⟨171130, by decide⟩ :=
  accepted_of_selected 13 82326 ⟨171130, by decide⟩ ⟨13, 2, 0, 171130, 82326, 2045, 16384⟩
    (by decide) selected_cut_05535

theorem selected_cut_05536 : selected 8 ⟨171142, by decide⟩
    (prefixPartial 13 82327) = some ⟨13, 2, 0, 171142, 82327, 1089, 16384⟩ := by
  decide +kernel

theorem context_13_82327_171142 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82327 ⟨171142, by decide⟩ :=
  accepted_of_selected 13 82327 ⟨171142, by decide⟩ ⟨13, 2, 0, 171142, 82327, 1089, 16384⟩
    (by decide) selected_cut_05536

theorem unmarked_context_12_20581_171143 : frontier 9 ⟨171143, by decide⟩
    (prefixCache 12 20581) (prefixPartial 12 20581) = false := by
  decide +kernel

theorem node_context_12_20581_171143 : EJMOriginalGlobalDAGData.nodes 9 ⟨171143, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨171101, by decide⟩,⟨171130, by decide⟩,⟨171142, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_20581_171143 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20581 ⟨171143, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 20581
    ⟨171143, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨171101, by decide⟩,⟨171130, by decide⟩,⟨171142, by decide⟩]) unmarked_context_12_20581_171143 node_context_12_20581_171143
  intro a
  fin_cases a
  · exact context_13_82324_3444
  · exact context_13_82325_171101
  · exact context_13_82326_171130
  · exact context_13_82327_171142

theorem selected_cut_05537 : selected 9 ⟨171193, by decide⟩
    (prefixPartial 12 20582) = some ⟨12, 2, 0, 171193, 20582, 3625, 65536⟩ := by
  decide +kernel

theorem context_12_20582_171193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20582 ⟨171193, by decide⟩ :=
  accepted_of_selected 12 20582 ⟨171193, by decide⟩ ⟨12, 2, 0, 171193, 20582, 3625, 65536⟩
    (by decide) selected_cut_05537

theorem selected_cut_05538 : selected 9 ⟨171246, by decide⟩
    (prefixPartial 12 20583) = some ⟨12, 2, 0, 171246, 20583, 3065, 65536⟩ := by
  decide +kernel

theorem context_12_20583_171246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20583 ⟨171246, by decide⟩ :=
  accepted_of_selected 12 20583 ⟨171246, by decide⟩ ⟨12, 2, 0, 171246, 20583, 3065, 65536⟩
    (by decide) selected_cut_05538

theorem unmarked_context_11_5145_171247 : frontier 10 ⟨171247, by decide⟩
    (prefixCache 11 5145) (prefixPartial 11 5145) = false := by
  decide +kernel

theorem node_context_11_5145_171247 : EJMOriginalGlobalDAGData.nodes 10 ⟨171247, by decide⟩ =
    .split (coordinate 11) (![⟨171084, by decide⟩,⟨171143, by decide⟩,⟨171193, by decide⟩,⟨171246, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5145_171247 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5145 ⟨171247, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5145
    ⟨171247, by decide⟩ (by decide) (![⟨171084, by decide⟩,⟨171143, by decide⟩,⟨171193, by decide⟩,⟨171246, by decide⟩]) unmarked_context_11_5145_171247 node_context_11_5145_171247
  intro a
  fin_cases a
  · exact context_12_20580_171084
  · exact context_12_20581_171143
  · exact context_12_20582_171193
  · exact context_12_20583_171246

theorem selected_cut_05539 : selected 9 ⟨171284, by decide⟩
    (prefixPartial 12 20584) = some ⟨12, 2, 0, 171284, 20584, 2641, 65536⟩ := by
  decide +kernel

theorem context_12_20584_171284 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20584 ⟨171284, by decide⟩ :=
  accepted_of_selected 12 20584 ⟨171284, by decide⟩ ⟨12, 2, 0, 171284, 20584, 2641, 65536⟩
    (by decide) selected_cut_05539

theorem selected_cut_05540 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 82340) = some ⟨13, 1, 0, 3444, 82340, 1, 16384⟩ := by
  decide +kernel

theorem context_13_82340_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82340 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 82340 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 82340, 1, 16384⟩
    (by decide) selected_cut_05540

theorem selected_cut_05541 : selected 8 ⟨171301, by decide⟩
    (prefixPartial 13 82341) = some ⟨13, 2, 0, 171301, 82341, 793, 16384⟩ := by
  decide +kernel

theorem context_13_82341_171301 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82341 ⟨171301, by decide⟩ :=
  accepted_of_selected 13 82341 ⟨171301, by decide⟩ ⟨13, 2, 0, 171301, 82341, 793, 16384⟩
    (by decide) selected_cut_05541

theorem selected_cut_05542 : selected 8 ⟨171327, by decide⟩
    (prefixPartial 13 82342) = some ⟨13, 2, 0, 171327, 82342, 2441, 16384⟩ := by
  decide +kernel

theorem context_13_82342_171327 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82342 ⟨171327, by decide⟩ :=
  accepted_of_selected 13 82342 ⟨171327, by decide⟩ ⟨13, 2, 0, 171327, 82342, 2441, 16384⟩
    (by decide) selected_cut_05542

theorem selected_cut_05543 : selected 8 ⟨171337, by decide⟩
    (prefixPartial 13 82343) = some ⟨13, 2, 0, 171337, 82343, 1149, 16384⟩ := by
  decide +kernel

theorem context_13_82343_171337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 82343 ⟨171337, by decide⟩ :=
  accepted_of_selected 13 82343 ⟨171337, by decide⟩ ⟨13, 2, 0, 171337, 82343, 1149, 16384⟩
    (by decide) selected_cut_05543

theorem unmarked_context_12_20585_171338 : frontier 9 ⟨171338, by decide⟩
    (prefixCache 12 20585) (prefixPartial 12 20585) = false := by
  decide +kernel

theorem node_context_12_20585_171338 : EJMOriginalGlobalDAGData.nodes 9 ⟨171338, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨171301, by decide⟩,⟨171327, by decide⟩,⟨171337, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_20585_171338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20585 ⟨171338, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 20585
    ⟨171338, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨171301, by decide⟩,⟨171327, by decide⟩,⟨171337, by decide⟩]) unmarked_context_12_20585_171338 node_context_12_20585_171338
  intro a
  fin_cases a
  · exact context_13_82340_3444
  · exact context_13_82341_171301
  · exact context_13_82342_171327
  · exact context_13_82343_171337

theorem selected_cut_05544 : selected 9 ⟨171382, by decide⟩
    (prefixPartial 12 20586) = some ⟨12, 2, 0, 171382, 20586, 3425, 65536⟩ := by
  decide +kernel

theorem context_12_20586_171382 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20586 ⟨171382, by decide⟩ :=
  accepted_of_selected 12 20586 ⟨171382, by decide⟩ ⟨12, 2, 0, 171382, 20586, 3425, 65536⟩
    (by decide) selected_cut_05544

theorem selected_cut_05545 : selected 9 ⟨171423, by decide⟩
    (prefixPartial 12 20587) = some ⟨12, 2, 0, 171423, 20587, 3397, 65536⟩ := by
  decide +kernel

theorem context_12_20587_171423 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20587 ⟨171423, by decide⟩ :=
  accepted_of_selected 12 20587 ⟨171423, by decide⟩ ⟨12, 2, 0, 171423, 20587, 3397, 65536⟩
    (by decide) selected_cut_05545

theorem unmarked_context_11_5146_171424 : frontier 10 ⟨171424, by decide⟩
    (prefixCache 11 5146) (prefixPartial 11 5146) = false := by
  decide +kernel

theorem node_context_11_5146_171424 : EJMOriginalGlobalDAGData.nodes 10 ⟨171424, by decide⟩ =
    .split (coordinate 11) (![⟨171284, by decide⟩,⟨171338, by decide⟩,⟨171382, by decide⟩,⟨171423, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5146_171424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5146 ⟨171424, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5146
    ⟨171424, by decide⟩ (by decide) (![⟨171284, by decide⟩,⟨171338, by decide⟩,⟨171382, by decide⟩,⟨171423, by decide⟩]) unmarked_context_11_5146_171424 node_context_11_5146_171424
  intro a
  fin_cases a
  · exact context_12_20584_171284
  · exact context_12_20585_171338
  · exact context_12_20586_171382
  · exact context_12_20587_171423

theorem selected_cut_05546 : selected 9 ⟨171465, by decide⟩
    (prefixPartial 12 20588) = some ⟨12, 2, 0, 171465, 20588, 2393, 65536⟩ := by
  decide +kernel

theorem context_12_20588_171465 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20588 ⟨171465, by decide⟩ :=
  accepted_of_selected 12 20588 ⟨171465, by decide⟩ ⟨12, 2, 0, 171465, 20588, 2393, 65536⟩
    (by decide) selected_cut_05546

theorem selected_cut_05547 : selected 9 ⟨171514, by decide⟩
    (prefixPartial 12 20589) = some ⟨12, 2, 0, 171514, 20589, 4001, 65536⟩ := by
  decide +kernel

theorem context_12_20589_171514 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20589 ⟨171514, by decide⟩ :=
  accepted_of_selected 12 20589 ⟨171514, by decide⟩ ⟨12, 2, 0, 171514, 20589, 4001, 65536⟩
    (by decide) selected_cut_05547

theorem selected_cut_05548 : selected 9 ⟨171554, by decide⟩
    (prefixPartial 12 20590) = some ⟨12, 2, 0, 171554, 20590, 3469, 65536⟩ := by
  decide +kernel

theorem context_12_20590_171554 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20590 ⟨171554, by decide⟩ :=
  accepted_of_selected 12 20590 ⟨171554, by decide⟩ ⟨12, 2, 0, 171554, 20590, 3469, 65536⟩
    (by decide) selected_cut_05548

theorem selected_cut_05549 : selected 9 ⟨171600, by decide⟩
    (prefixPartial 12 20591) = some ⟨12, 2, 0, 171600, 20591, 2809, 65536⟩ := by
  decide +kernel

theorem context_12_20591_171600 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20591 ⟨171600, by decide⟩ :=
  accepted_of_selected 12 20591 ⟨171600, by decide⟩ ⟨12, 2, 0, 171600, 20591, 2809, 65536⟩
    (by decide) selected_cut_05549

theorem unmarked_context_11_5147_171601 : frontier 10 ⟨171601, by decide⟩
    (prefixCache 11 5147) (prefixPartial 11 5147) = false := by
  decide +kernel

theorem node_context_11_5147_171601 : EJMOriginalGlobalDAGData.nodes 10 ⟨171601, by decide⟩ =
    .split (coordinate 11) (![⟨171465, by decide⟩,⟨171514, by decide⟩,⟨171554, by decide⟩,⟨171600, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5147_171601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5147 ⟨171601, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5147
    ⟨171601, by decide⟩ (by decide) (![⟨171465, by decide⟩,⟨171514, by decide⟩,⟨171554, by decide⟩,⟨171600, by decide⟩]) unmarked_context_11_5147_171601 node_context_11_5147_171601
  intro a
  fin_cases a
  · exact context_12_20588_171465
  · exact context_12_20589_171514
  · exact context_12_20590_171554
  · exact context_12_20591_171600

theorem unmarked_context_10_1286_171602 : frontier 11 ⟨171602, by decide⟩
    (prefixCache 10 1286) (prefixPartial 10 1286) = false := by
  decide +kernel

theorem node_context_10_1286_171602 : EJMOriginalGlobalDAGData.nodes 11 ⟨171602, by decide⟩ =
    .split (coordinate 10) (![⟨171036, by decide⟩,⟨171247, by decide⟩,⟨171424, by decide⟩,⟨171601, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1286_171602 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1286 ⟨171602, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1286
    ⟨171602, by decide⟩ (by decide) (![⟨171036, by decide⟩,⟨171247, by decide⟩,⟨171424, by decide⟩,⟨171601, by decide⟩]) unmarked_context_10_1286_171602 node_context_10_1286_171602
  intro a
  fin_cases a
  · exact context_11_5144_171036
  · exact context_11_5145_171247
  · exact context_11_5146_171424
  · exact context_11_5147_171601

theorem selected_cut_05550 : selected 11 ⟨3440, by decide⟩
    (prefixPartial 10 1287) = some ⟨10, 1, 0, 3440, 1287, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_1287_3440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1287 ⟨3440, by decide⟩ :=
  accepted_of_selected 10 1287 ⟨3440, by decide⟩ ⟨10, 1, 0, 3440, 1287, 1, 1048576⟩
    (by decide) selected_cut_05550

theorem unmarked_context_9_321_171603 : frontier 12 ⟨171603, by decide⟩
    (prefixCache 9 321) (prefixPartial 9 321) = false := by
  decide +kernel

theorem node_context_9_321_171603 : EJMOriginalGlobalDAGData.nodes 12 ⟨171603, by decide⟩ =
    .split (coordinate 9) (![⟨170328, by decide⟩,⟨170816, by decide⟩,⟨171602, by decide⟩,⟨3440, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_321_171603 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 321 ⟨171603, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 321
    ⟨171603, by decide⟩ (by decide) (![⟨170328, by decide⟩,⟨170816, by decide⟩,⟨171602, by decide⟩,⟨3440, by decide⟩]) unmarked_context_9_321_171603 node_context_9_321_171603
  intro a
  fin_cases a
  · exact context_10_1284_170328
  · exact context_10_1285_170816
  · exact context_10_1286_171602
  · exact context_10_1287_3440

theorem selected_cut_05551 : selected 9 ⟨169790, by decide⟩
    (prefixPartial 12 20608) = some ⟨12, 1, 0, 169790, 20608, 1, 65536⟩ := by
  decide +kernel

theorem context_12_20608_169790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20608 ⟨169790, by decide⟩ :=
  accepted_of_selected 12 20608 ⟨169790, by decide⟩ ⟨12, 1, 0, 169790, 20608, 1, 65536⟩
    (by decide) selected_cut_05551

theorem selected_cut_05552 : selected 9 ⟨171637, by decide⟩
    (prefixPartial 12 20609) = some ⟨12, 2, 0, 171637, 20609, 2857, 65536⟩ := by
  decide +kernel

theorem context_12_20609_171637 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20609 ⟨171637, by decide⟩ :=
  accepted_of_selected 12 20609 ⟨171637, by decide⟩ ⟨12, 2, 0, 171637, 20609, 2857, 65536⟩
    (by decide) selected_cut_05552

theorem selected_cut_05553 : selected 9 ⟨171666, by decide⟩
    (prefixPartial 12 20610) = some ⟨12, 2, 0, 171666, 20610, 2625, 65536⟩ := by
  decide +kernel

theorem context_12_20610_171666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20610 ⟨171666, by decide⟩ :=
  accepted_of_selected 12 20610 ⟨171666, by decide⟩ ⟨12, 2, 0, 171666, 20610, 2625, 65536⟩
    (by decide) selected_cut_05553

theorem selected_cut_05554 : selected 9 ⟨171702, by decide⟩
    (prefixPartial 12 20611) = some ⟨12, 2, 0, 171702, 20611, 2793, 65536⟩ := by
  decide +kernel

theorem context_12_20611_171702 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20611 ⟨171702, by decide⟩ :=
  accepted_of_selected 12 20611 ⟨171702, by decide⟩ ⟨12, 2, 0, 171702, 20611, 2793, 65536⟩
    (by decide) selected_cut_05554

theorem unmarked_context_11_5152_171703 : frontier 10 ⟨171703, by decide⟩
    (prefixCache 11 5152) (prefixPartial 11 5152) = false := by
  decide +kernel

theorem node_context_11_5152_171703 : EJMOriginalGlobalDAGData.nodes 10 ⟨171703, by decide⟩ =
    .split (coordinate 11) (![⟨169790, by decide⟩,⟨171637, by decide⟩,⟨171666, by decide⟩,⟨171702, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5152_171703 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5152 ⟨171703, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5152
    ⟨171703, by decide⟩ (by decide) (![⟨169790, by decide⟩,⟨171637, by decide⟩,⟨171666, by decide⟩,⟨171702, by decide⟩]) unmarked_context_11_5152_171703 node_context_11_5152_171703
  intro a
  fin_cases a
  · exact context_12_20608_169790
  · exact context_12_20609_171637
  · exact context_12_20610_171666
  · exact context_12_20611_171702

theorem selected_cut_05555 : selected 9 ⟨171731, by decide⟩
    (prefixPartial 12 20612) = some ⟨12, 2, 0, 171731, 20612, 1521, 65536⟩ := by
  decide +kernel

theorem context_12_20612_171731 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20612 ⟨171731, by decide⟩ :=
  accepted_of_selected 12 20612 ⟨171731, by decide⟩ ⟨12, 2, 0, 171731, 20612, 1521, 65536⟩
    (by decide) selected_cut_05555

theorem selected_cut_05556 : selected 9 ⟨171766, by decide⟩
    (prefixPartial 12 20613) = some ⟨12, 2, 0, 171766, 20613, 1945, 65536⟩ := by
  decide +kernel

theorem context_12_20613_171766 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20613 ⟨171766, by decide⟩ :=
  accepted_of_selected 12 20613 ⟨171766, by decide⟩ ⟨12, 2, 0, 171766, 20613, 1945, 65536⟩
    (by decide) selected_cut_05556

theorem selected_cut_05557 : selected 9 ⟨171793, by decide⟩
    (prefixPartial 12 20614) = some ⟨12, 2, 0, 171793, 20614, 1845, 65536⟩ := by
  decide +kernel

theorem context_12_20614_171793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20614 ⟨171793, by decide⟩ :=
  accepted_of_selected 12 20614 ⟨171793, by decide⟩ ⟨12, 2, 0, 171793, 20614, 1845, 65536⟩
    (by decide) selected_cut_05557

theorem selected_cut_05558 : selected 9 ⟨171825, by decide⟩
    (prefixPartial 12 20615) = some ⟨12, 2, 0, 171825, 20615, 2021, 65536⟩ := by
  decide +kernel

theorem context_12_20615_171825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20615 ⟨171825, by decide⟩ :=
  accepted_of_selected 12 20615 ⟨171825, by decide⟩ ⟨12, 2, 0, 171825, 20615, 2021, 65536⟩
    (by decide) selected_cut_05558

theorem unmarked_context_11_5153_171826 : frontier 10 ⟨171826, by decide⟩
    (prefixCache 11 5153) (prefixPartial 11 5153) = false := by
  decide +kernel

theorem node_context_11_5153_171826 : EJMOriginalGlobalDAGData.nodes 10 ⟨171826, by decide⟩ =
    .split (coordinate 11) (![⟨171731, by decide⟩,⟨171766, by decide⟩,⟨171793, by decide⟩,⟨171825, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5153_171826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5153 ⟨171826, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5153
    ⟨171826, by decide⟩ (by decide) (![⟨171731, by decide⟩,⟨171766, by decide⟩,⟨171793, by decide⟩,⟨171825, by decide⟩]) unmarked_context_11_5153_171826 node_context_11_5153_171826
  intro a
  fin_cases a
  · exact context_12_20612_171731
  · exact context_12_20613_171766
  · exact context_12_20614_171793
  · exact context_12_20615_171825

theorem selected_cut_05559 : selected 9 ⟨171857, by decide⟩
    (prefixPartial 12 20616) = some ⟨12, 2, 0, 171857, 20616, 1649, 65536⟩ := by
  decide +kernel

theorem context_12_20616_171857 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20616 ⟨171857, by decide⟩ :=
  accepted_of_selected 12 20616 ⟨171857, by decide⟩ ⟨12, 2, 0, 171857, 20616, 1649, 65536⟩
    (by decide) selected_cut_05559

theorem selected_cut_05560 : selected 9 ⟨171896, by decide⟩
    (prefixPartial 12 20617) = some ⟨12, 2, 0, 171896, 20617, 2277, 65536⟩ := by
  decide +kernel

theorem context_12_20617_171896 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20617 ⟨171896, by decide⟩ :=
  accepted_of_selected 12 20617 ⟨171896, by decide⟩ ⟨12, 2, 0, 171896, 20617, 2277, 65536⟩
    (by decide) selected_cut_05560

theorem selected_cut_05561 : selected 9 ⟨171922, by decide⟩
    (prefixPartial 12 20618) = some ⟨12, 2, 0, 171922, 20618, 2001, 65536⟩ := by
  decide +kernel

theorem context_12_20618_171922 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20618 ⟨171922, by decide⟩ :=
  accepted_of_selected 12 20618 ⟨171922, by decide⟩ ⟨12, 2, 0, 171922, 20618, 2001, 65536⟩
    (by decide) selected_cut_05561

theorem selected_cut_05562 : selected 9 ⟨171956, by decide⟩
    (prefixPartial 12 20619) = some ⟨12, 2, 0, 171956, 20619, 2269, 65536⟩ := by
  decide +kernel

theorem context_12_20619_171956 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20619 ⟨171956, by decide⟩ :=
  accepted_of_selected 12 20619 ⟨171956, by decide⟩ ⟨12, 2, 0, 171956, 20619, 2269, 65536⟩
    (by decide) selected_cut_05562

theorem unmarked_context_11_5154_171957 : frontier 10 ⟨171957, by decide⟩
    (prefixCache 11 5154) (prefixPartial 11 5154) = false := by
  decide +kernel

theorem node_context_11_5154_171957 : EJMOriginalGlobalDAGData.nodes 10 ⟨171957, by decide⟩ =
    .split (coordinate 11) (![⟨171857, by decide⟩,⟨171896, by decide⟩,⟨171922, by decide⟩,⟨171956, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5154_171957 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5154 ⟨171957, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5154
    ⟨171957, by decide⟩ (by decide) (![⟨171857, by decide⟩,⟨171896, by decide⟩,⟨171922, by decide⟩,⟨171956, by decide⟩]) unmarked_context_11_5154_171957 node_context_11_5154_171957
  intro a
  fin_cases a
  · exact context_12_20616_171857
  · exact context_12_20617_171896
  · exact context_12_20618_171922
  · exact context_12_20619_171956

theorem selected_cut_05563 : selected 9 ⟨171979, by decide⟩
    (prefixPartial 12 20620) = some ⟨12, 2, 0, 171979, 20620, 1389, 65536⟩ := by
  decide +kernel

theorem context_12_20620_171979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20620 ⟨171979, by decide⟩ :=
  accepted_of_selected 12 20620 ⟨171979, by decide⟩ ⟨12, 2, 0, 171979, 20620, 1389, 65536⟩
    (by decide) selected_cut_05563

theorem selected_cut_05564 : selected 9 ⟨172016, by decide⟩
    (prefixPartial 12 20621) = some ⟨12, 2, 0, 172016, 20621, 1829, 65536⟩ := by
  decide +kernel

theorem context_12_20621_172016 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20621 ⟨172016, by decide⟩ :=
  accepted_of_selected 12 20621 ⟨172016, by decide⟩ ⟨12, 2, 0, 172016, 20621, 1829, 65536⟩
    (by decide) selected_cut_05564

theorem selected_cut_05565 : selected 9 ⟨172046, by decide⟩
    (prefixPartial 12 20622) = some ⟨12, 2, 0, 172046, 20622, 1729, 65536⟩ := by
  decide +kernel

theorem context_12_20622_172046 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20622 ⟨172046, by decide⟩ :=
  accepted_of_selected 12 20622 ⟨172046, by decide⟩ ⟨12, 2, 0, 172046, 20622, 1729, 65536⟩
    (by decide) selected_cut_05565

theorem selected_cut_05566 : selected 9 ⟨172071, by decide⟩
    (prefixPartial 12 20623) = some ⟨12, 2, 0, 172071, 20623, 1969, 65536⟩ := by
  decide +kernel

theorem context_12_20623_172071 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20623 ⟨172071, by decide⟩ :=
  accepted_of_selected 12 20623 ⟨172071, by decide⟩ ⟨12, 2, 0, 172071, 20623, 1969, 65536⟩
    (by decide) selected_cut_05566

theorem unmarked_context_11_5155_172072 : frontier 10 ⟨172072, by decide⟩
    (prefixCache 11 5155) (prefixPartial 11 5155) = false := by
  decide +kernel

theorem node_context_11_5155_172072 : EJMOriginalGlobalDAGData.nodes 10 ⟨172072, by decide⟩ =
    .split (coordinate 11) (![⟨171979, by decide⟩,⟨172016, by decide⟩,⟨172046, by decide⟩,⟨172071, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5155_172072 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5155 ⟨172072, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5155
    ⟨172072, by decide⟩ (by decide) (![⟨171979, by decide⟩,⟨172016, by decide⟩,⟨172046, by decide⟩,⟨172071, by decide⟩]) unmarked_context_11_5155_172072 node_context_11_5155_172072
  intro a
  fin_cases a
  · exact context_12_20620_171979
  · exact context_12_20621_172016
  · exact context_12_20622_172046
  · exact context_12_20623_172071

theorem unmarked_context_10_1288_172073 : frontier 11 ⟨172073, by decide⟩
    (prefixCache 10 1288) (prefixPartial 10 1288) = false := by
  decide +kernel

theorem node_context_10_1288_172073 : EJMOriginalGlobalDAGData.nodes 11 ⟨172073, by decide⟩ =
    .split (coordinate 10) (![⟨171703, by decide⟩,⟨171826, by decide⟩,⟨171957, by decide⟩,⟨172072, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1288_172073 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1288 ⟨172073, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1288
    ⟨172073, by decide⟩ (by decide) (![⟨171703, by decide⟩,⟨171826, by decide⟩,⟨171957, by decide⟩,⟨172072, by decide⟩]) unmarked_context_10_1288_172073 node_context_10_1288_172073
  intro a
  fin_cases a
  · exact context_11_5152_171703
  · exact context_11_5153_171826
  · exact context_11_5154_171957
  · exact context_11_5155_172072

theorem selected_cut_05567 : selected 9 ⟨172121, by decide⟩
    (prefixPartial 12 20624) = some ⟨12, 2, 0, 172121, 20624, 2389, 65536⟩ := by
  decide +kernel

theorem context_12_20624_172121 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20624 ⟨172121, by decide⟩ :=
  accepted_of_selected 12 20624 ⟨172121, by decide⟩ ⟨12, 2, 0, 172121, 20624, 2389, 65536⟩
    (by decide) selected_cut_05567

theorem selected_cut_05568 : selected 9 ⟨172153, by decide⟩
    (prefixPartial 12 20625) = some ⟨12, 2, 0, 172153, 20625, 1965, 65536⟩ := by
  decide +kernel

theorem context_12_20625_172153 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20625 ⟨172153, by decide⟩ :=
  accepted_of_selected 12 20625 ⟨172153, by decide⟩ ⟨12, 2, 0, 172153, 20625, 1965, 65536⟩
    (by decide) selected_cut_05568

theorem selected_cut_05569 : selected 9 ⟨172174, by decide⟩
    (prefixPartial 12 20626) = some ⟨12, 2, 0, 172174, 20626, 1753, 65536⟩ := by
  decide +kernel

theorem context_12_20626_172174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 20626 ⟨172174, by decide⟩ :=
  accepted_of_selected 12 20626 ⟨172174, by decide⟩ ⟨12, 2, 0, 172174, 20626, 1753, 65536⟩
    (by decide) selected_cut_05569

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
