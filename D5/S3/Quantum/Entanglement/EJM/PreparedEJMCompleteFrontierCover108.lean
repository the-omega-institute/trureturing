/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover107
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_10_1562_282333 : frontier 11 ⟨282333, by decide⟩
    (prefixCache 10 1562) (prefixPartial 10 1562) = false := by
  decide +kernel

theorem node_context_10_1562_282333 : EJMOriginalGlobalDAGData.nodes 11 ⟨282333, by decide⟩ =
    .split (coordinate 10) (![⟨282116, by decide⟩,⟨282191, by decide⟩,⟨282260, by decide⟩,⟨282332, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1562_282333 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1562 ⟨282333, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1562
    ⟨282333, by decide⟩ (by decide) (![⟨282116, by decide⟩,⟨282191, by decide⟩,⟨282260, by decide⟩,⟨282332, by decide⟩]) unmarked_context_10_1562_282333 node_context_10_1562_282333
  intro a
  fin_cases a
  · exact context_11_6248_282116
  · exact context_11_6249_282191
  · exact context_11_6250_282260
  · exact context_11_6251_282332

theorem selected_cut_10371 : selected 9 ⟨282346, by decide⟩
    (prefixPartial 12 25008) = some ⟨12, 2, 0, 282346, 25008, 1101, 65536⟩ := by
  decide +kernel

theorem context_12_25008_282346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25008 ⟨282346, by decide⟩ :=
  accepted_of_selected 12 25008 ⟨282346, by decide⟩ ⟨12, 2, 0, 282346, 25008, 1101, 65536⟩
    (by decide) selected_cut_10371

theorem selected_cut_10372 : selected 9 ⟨282360, by decide⟩
    (prefixPartial 12 25009) = some ⟨12, 2, 0, 282360, 25009, 1205, 65536⟩ := by
  decide +kernel

theorem context_12_25009_282360 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25009 ⟨282360, by decide⟩ :=
  accepted_of_selected 12 25009 ⟨282360, by decide⟩ ⟨12, 2, 0, 282360, 25009, 1205, 65536⟩
    (by decide) selected_cut_10372

theorem selected_cut_10373 : selected 9 ⟨282375, by decide⟩
    (prefixPartial 12 25010) = some ⟨12, 2, 0, 282375, 25010, 1225, 65536⟩ := by
  decide +kernel

theorem context_12_25010_282375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25010 ⟨282375, by decide⟩ :=
  accepted_of_selected 12 25010 ⟨282375, by decide⟩ ⟨12, 2, 0, 282375, 25010, 1225, 65536⟩
    (by decide) selected_cut_10373

theorem selected_cut_10374 : selected 9 ⟨282393, by decide⟩
    (prefixPartial 12 25011) = some ⟨12, 2, 0, 282393, 25011, 1349, 65536⟩ := by
  decide +kernel

theorem context_12_25011_282393 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25011 ⟨282393, by decide⟩ :=
  accepted_of_selected 12 25011 ⟨282393, by decide⟩ ⟨12, 2, 0, 282393, 25011, 1349, 65536⟩
    (by decide) selected_cut_10374

theorem unmarked_context_11_6252_282394 : frontier 10 ⟨282394, by decide⟩
    (prefixCache 11 6252) (prefixPartial 11 6252) = false := by
  decide +kernel

theorem node_context_11_6252_282394 : EJMOriginalGlobalDAGData.nodes 10 ⟨282394, by decide⟩ =
    .split (coordinate 11) (![⟨282346, by decide⟩,⟨282360, by decide⟩,⟨282375, by decide⟩,⟨282393, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6252_282394 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6252 ⟨282394, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6252
    ⟨282394, by decide⟩ (by decide) (![⟨282346, by decide⟩,⟨282360, by decide⟩,⟨282375, by decide⟩,⟨282393, by decide⟩]) unmarked_context_11_6252_282394 node_context_11_6252_282394
  intro a
  fin_cases a
  · exact context_12_25008_282346
  · exact context_12_25009_282360
  · exact context_12_25010_282375
  · exact context_12_25011_282393

theorem selected_cut_10375 : selected 9 ⟨282409, by decide⟩
    (prefixPartial 12 25012) = some ⟨12, 2, 0, 282409, 25012, 1161, 65536⟩ := by
  decide +kernel

theorem context_12_25012_282409 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25012 ⟨282409, by decide⟩ :=
  accepted_of_selected 12 25012 ⟨282409, by decide⟩ ⟨12, 2, 0, 282409, 25012, 1161, 65536⟩
    (by decide) selected_cut_10375

theorem selected_cut_10376 : selected 9 ⟨282425, by decide⟩
    (prefixPartial 12 25013) = some ⟨12, 2, 0, 282425, 25013, 1617, 65536⟩ := by
  decide +kernel

theorem context_12_25013_282425 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25013 ⟨282425, by decide⟩ :=
  accepted_of_selected 12 25013 ⟨282425, by decide⟩ ⟨12, 2, 0, 282425, 25013, 1617, 65536⟩
    (by decide) selected_cut_10376

theorem selected_cut_10377 : selected 9 ⟨282439, by decide⟩
    (prefixPartial 12 25014) = some ⟨12, 2, 0, 282439, 25014, 1245, 65536⟩ := by
  decide +kernel

theorem context_12_25014_282439 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25014 ⟨282439, by decide⟩ :=
  accepted_of_selected 12 25014 ⟨282439, by decide⟩ ⟨12, 2, 0, 282439, 25014, 1245, 65536⟩
    (by decide) selected_cut_10377

theorem selected_cut_10378 : selected 9 ⟨282450, by decide⟩
    (prefixPartial 12 25015) = some ⟨12, 2, 0, 282450, 25015, 1313, 65536⟩ := by
  decide +kernel

theorem context_12_25015_282450 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25015 ⟨282450, by decide⟩ :=
  accepted_of_selected 12 25015 ⟨282450, by decide⟩ ⟨12, 2, 0, 282450, 25015, 1313, 65536⟩
    (by decide) selected_cut_10378

theorem unmarked_context_11_6253_282451 : frontier 10 ⟨282451, by decide⟩
    (prefixCache 11 6253) (prefixPartial 11 6253) = false := by
  decide +kernel

theorem node_context_11_6253_282451 : EJMOriginalGlobalDAGData.nodes 10 ⟨282451, by decide⟩ =
    .split (coordinate 11) (![⟨282409, by decide⟩,⟨282425, by decide⟩,⟨282439, by decide⟩,⟨282450, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6253_282451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6253 ⟨282451, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6253
    ⟨282451, by decide⟩ (by decide) (![⟨282409, by decide⟩,⟨282425, by decide⟩,⟨282439, by decide⟩,⟨282450, by decide⟩]) unmarked_context_11_6253_282451 node_context_11_6253_282451
  intro a
  fin_cases a
  · exact context_12_25012_282409
  · exact context_12_25013_282425
  · exact context_12_25014_282439
  · exact context_12_25015_282450

theorem selected_cut_10379 : selected 9 ⟨282466, by decide⟩
    (prefixPartial 12 25016) = some ⟨12, 2, 0, 282466, 25016, 1089, 65536⟩ := by
  decide +kernel

theorem context_12_25016_282466 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25016 ⟨282466, by decide⟩ :=
  accepted_of_selected 12 25016 ⟨282466, by decide⟩ ⟨12, 2, 0, 282466, 25016, 1089, 65536⟩
    (by decide) selected_cut_10379

theorem selected_cut_10380 : selected 9 ⟨282484, by decide⟩
    (prefixPartial 12 25017) = some ⟨12, 2, 0, 282484, 25017, 1117, 65536⟩ := by
  decide +kernel

theorem context_12_25017_282484 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25017 ⟨282484, by decide⟩ :=
  accepted_of_selected 12 25017 ⟨282484, by decide⟩ ⟨12, 2, 0, 282484, 25017, 1117, 65536⟩
    (by decide) selected_cut_10380

theorem selected_cut_10381 : selected 9 ⟨282502, by decide⟩
    (prefixPartial 12 25018) = some ⟨12, 2, 0, 282502, 25018, 1089, 65536⟩ := by
  decide +kernel

theorem context_12_25018_282502 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25018 ⟨282502, by decide⟩ :=
  accepted_of_selected 12 25018 ⟨282502, by decide⟩ ⟨12, 2, 0, 282502, 25018, 1089, 65536⟩
    (by decide) selected_cut_10381

theorem selected_cut_10382 : selected 9 ⟨282519, by decide⟩
    (prefixPartial 12 25019) = some ⟨12, 2, 0, 282519, 25019, 1133, 65536⟩ := by
  decide +kernel

theorem context_12_25019_282519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25019 ⟨282519, by decide⟩ :=
  accepted_of_selected 12 25019 ⟨282519, by decide⟩ ⟨12, 2, 0, 282519, 25019, 1133, 65536⟩
    (by decide) selected_cut_10382

theorem unmarked_context_11_6254_282520 : frontier 10 ⟨282520, by decide⟩
    (prefixCache 11 6254) (prefixPartial 11 6254) = false := by
  decide +kernel

theorem node_context_11_6254_282520 : EJMOriginalGlobalDAGData.nodes 10 ⟨282520, by decide⟩ =
    .split (coordinate 11) (![⟨282466, by decide⟩,⟨282484, by decide⟩,⟨282502, by decide⟩,⟨282519, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6254_282520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6254 ⟨282520, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6254
    ⟨282520, by decide⟩ (by decide) (![⟨282466, by decide⟩,⟨282484, by decide⟩,⟨282502, by decide⟩,⟨282519, by decide⟩]) unmarked_context_11_6254_282520 node_context_11_6254_282520
  intro a
  fin_cases a
  · exact context_12_25016_282466
  · exact context_12_25017_282484
  · exact context_12_25018_282502
  · exact context_12_25019_282519

theorem selected_cut_10383 : selected 10 ⟨282566, by decide⟩
    (prefixPartial 11 6255) = some ⟨11, 2, 0, 282566, 6255, 3977, 262144⟩ := by
  decide +kernel

theorem context_11_6255_282566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6255 ⟨282566, by decide⟩ :=
  accepted_of_selected 11 6255 ⟨282566, by decide⟩ ⟨11, 2, 0, 282566, 6255, 3977, 262144⟩
    (by decide) selected_cut_10383

theorem unmarked_context_10_1563_282567 : frontier 11 ⟨282567, by decide⟩
    (prefixCache 10 1563) (prefixPartial 10 1563) = false := by
  decide +kernel

theorem node_context_10_1563_282567 : EJMOriginalGlobalDAGData.nodes 11 ⟨282567, by decide⟩ =
    .split (coordinate 10) (![⟨282394, by decide⟩,⟨282451, by decide⟩,⟨282520, by decide⟩,⟨282566, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1563_282567 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1563 ⟨282567, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1563
    ⟨282567, by decide⟩ (by decide) (![⟨282394, by decide⟩,⟨282451, by decide⟩,⟨282520, by decide⟩,⟨282566, by decide⟩]) unmarked_context_10_1563_282567 node_context_10_1563_282567
  intro a
  fin_cases a
  · exact context_11_6252_282394
  · exact context_11_6253_282451
  · exact context_11_6254_282520
  · exact context_11_6255_282566

theorem unmarked_context_9_390_282568 : frontier 12 ⟨282568, by decide⟩
    (prefixCache 9 390) (prefixPartial 9 390) = false := by
  decide +kernel

theorem node_context_9_390_282568 : EJMOriginalGlobalDAGData.nodes 12 ⟨282568, by decide⟩ =
    .split (coordinate 9) (![⟨281662, by decide⟩,⟨282043, by decide⟩,⟨282333, by decide⟩,⟨282567, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_390_282568 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 390 ⟨282568, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 390
    ⟨282568, by decide⟩ (by decide) (![⟨281662, by decide⟩,⟨282043, by decide⟩,⟨282333, by decide⟩,⟨282567, by decide⟩]) unmarked_context_9_390_282568 node_context_9_390_282568
  intro a
  fin_cases a
  · exact context_10_1560_281662
  · exact context_10_1561_282043
  · exact context_10_1562_282333
  · exact context_10_1563_282567

theorem selected_cut_10384 : selected 10 ⟨282636, by decide⟩
    (prefixPartial 11 6256) = some ⟨11, 2, 0, 282636, 6256, 3597, 262144⟩ := by
  decide +kernel

theorem context_11_6256_282636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6256 ⟨282636, by decide⟩ :=
  accepted_of_selected 11 6256 ⟨282636, by decide⟩ ⟨11, 2, 0, 282636, 6256, 3597, 262144⟩
    (by decide) selected_cut_10384

theorem selected_cut_10385 : selected 10 ⟨282665, by decide⟩
    (prefixPartial 11 6257) = some ⟨11, 2, 0, 282665, 6257, 3017, 262144⟩ := by
  decide +kernel

theorem context_11_6257_282665 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6257 ⟨282665, by decide⟩ :=
  accepted_of_selected 11 6257 ⟨282665, by decide⟩ ⟨11, 2, 0, 282665, 6257, 3017, 262144⟩
    (by decide) selected_cut_10385

theorem selected_cut_10386 : selected 10 ⟨282705, by decide⟩
    (prefixPartial 11 6258) = some ⟨11, 2, 0, 282705, 6258, 2729, 262144⟩ := by
  decide +kernel

theorem context_11_6258_282705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6258 ⟨282705, by decide⟩ :=
  accepted_of_selected 11 6258 ⟨282705, by decide⟩ ⟨11, 2, 0, 282705, 6258, 2729, 262144⟩
    (by decide) selected_cut_10386

theorem selected_cut_10387 : selected 10 ⟨282736, by decide⟩
    (prefixPartial 11 6259) = some ⟨11, 2, 0, 282736, 6259, 2765, 262144⟩ := by
  decide +kernel

theorem context_11_6259_282736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6259 ⟨282736, by decide⟩ :=
  accepted_of_selected 11 6259 ⟨282736, by decide⟩ ⟨11, 2, 0, 282736, 6259, 2765, 262144⟩
    (by decide) selected_cut_10387

theorem unmarked_context_10_1564_282737 : frontier 11 ⟨282737, by decide⟩
    (prefixCache 10 1564) (prefixPartial 10 1564) = false := by
  decide +kernel

theorem node_context_10_1564_282737 : EJMOriginalGlobalDAGData.nodes 11 ⟨282737, by decide⟩ =
    .split (coordinate 10) (![⟨282636, by decide⟩,⟨282665, by decide⟩,⟨282705, by decide⟩,⟨282736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1564_282737 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1564 ⟨282737, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1564
    ⟨282737, by decide⟩ (by decide) (![⟨282636, by decide⟩,⟨282665, by decide⟩,⟨282705, by decide⟩,⟨282736, by decide⟩]) unmarked_context_10_1564_282737 node_context_10_1564_282737
  intro a
  fin_cases a
  · exact context_11_6256_282636
  · exact context_11_6257_282665
  · exact context_11_6258_282705
  · exact context_11_6259_282736

theorem selected_cut_10388 : selected 10 ⟨282757, by decide⟩
    (prefixPartial 11 6260) = some ⟨11, 2, 0, 282757, 6260, 2101, 262144⟩ := by
  decide +kernel

theorem context_11_6260_282757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6260 ⟨282757, by decide⟩ :=
  accepted_of_selected 11 6260 ⟨282757, by decide⟩ ⟨11, 2, 0, 282757, 6260, 2101, 262144⟩
    (by decide) selected_cut_10388

theorem selected_cut_10389 : selected 10 ⟨282791, by decide⟩
    (prefixPartial 11 6261) = some ⟨11, 2, 0, 282791, 6261, 1589, 262144⟩ := by
  decide +kernel

theorem context_11_6261_282791 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6261 ⟨282791, by decide⟩ :=
  accepted_of_selected 11 6261 ⟨282791, by decide⟩ ⟨11, 2, 0, 282791, 6261, 1589, 262144⟩
    (by decide) selected_cut_10389

theorem selected_cut_10390 : selected 10 ⟨282812, by decide⟩
    (prefixPartial 11 6262) = some ⟨11, 2, 0, 282812, 6262, 1885, 262144⟩ := by
  decide +kernel

theorem context_11_6262_282812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6262 ⟨282812, by decide⟩ :=
  accepted_of_selected 11 6262 ⟨282812, by decide⟩ ⟨11, 2, 0, 282812, 6262, 1885, 262144⟩
    (by decide) selected_cut_10390

theorem selected_cut_10391 : selected 10 ⟨282835, by decide⟩
    (prefixPartial 11 6263) = some ⟨11, 2, 0, 282835, 6263, 1745, 262144⟩ := by
  decide +kernel

theorem context_11_6263_282835 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6263 ⟨282835, by decide⟩ :=
  accepted_of_selected 11 6263 ⟨282835, by decide⟩ ⟨11, 2, 0, 282835, 6263, 1745, 262144⟩
    (by decide) selected_cut_10391

theorem unmarked_context_10_1565_282836 : frontier 11 ⟨282836, by decide⟩
    (prefixCache 10 1565) (prefixPartial 10 1565) = false := by
  decide +kernel

theorem node_context_10_1565_282836 : EJMOriginalGlobalDAGData.nodes 11 ⟨282836, by decide⟩ =
    .split (coordinate 10) (![⟨282757, by decide⟩,⟨282791, by decide⟩,⟨282812, by decide⟩,⟨282835, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1565_282836 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1565 ⟨282836, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1565
    ⟨282836, by decide⟩ (by decide) (![⟨282757, by decide⟩,⟨282791, by decide⟩,⟨282812, by decide⟩,⟨282835, by decide⟩]) unmarked_context_10_1565_282836 node_context_10_1565_282836
  intro a
  fin_cases a
  · exact context_11_6260_282757
  · exact context_11_6261_282791
  · exact context_11_6262_282812
  · exact context_11_6263_282835

theorem selected_cut_10392 : selected 10 ⟨282854, by decide⟩
    (prefixPartial 11 6264) = some ⟨11, 2, 0, 282854, 6264, 1553, 262144⟩ := by
  decide +kernel

theorem context_11_6264_282854 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6264 ⟨282854, by decide⟩ :=
  accepted_of_selected 11 6264 ⟨282854, by decide⟩ ⟨11, 2, 0, 282854, 6264, 1553, 262144⟩
    (by decide) selected_cut_10392

theorem selected_cut_10393 : selected 10 ⟨282872, by decide⟩
    (prefixPartial 11 6265) = some ⟨11, 2, 0, 282872, 6265, 1361, 262144⟩ := by
  decide +kernel

theorem context_11_6265_282872 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6265 ⟨282872, by decide⟩ :=
  accepted_of_selected 11 6265 ⟨282872, by decide⟩ ⟨11, 2, 0, 282872, 6265, 1361, 262144⟩
    (by decide) selected_cut_10393

theorem selected_cut_10394 : selected 10 ⟨282887, by decide⟩
    (prefixPartial 11 6266) = some ⟨11, 2, 0, 282887, 6266, 1093, 262144⟩ := by
  decide +kernel

theorem context_11_6266_282887 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6266 ⟨282887, by decide⟩ :=
  accepted_of_selected 11 6266 ⟨282887, by decide⟩ ⟨11, 2, 0, 282887, 6266, 1093, 262144⟩
    (by decide) selected_cut_10394

theorem selected_cut_10395 : selected 10 ⟨282899, by decide⟩
    (prefixPartial 11 6267) = some ⟨11, 2, 0, 282899, 6267, 921, 262144⟩ := by
  decide +kernel

theorem context_11_6267_282899 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6267 ⟨282899, by decide⟩ :=
  accepted_of_selected 11 6267 ⟨282899, by decide⟩ ⟨11, 2, 0, 282899, 6267, 921, 262144⟩
    (by decide) selected_cut_10395

theorem unmarked_context_10_1566_282900 : frontier 11 ⟨282900, by decide⟩
    (prefixCache 10 1566) (prefixPartial 10 1566) = false := by
  decide +kernel

theorem node_context_10_1566_282900 : EJMOriginalGlobalDAGData.nodes 11 ⟨282900, by decide⟩ =
    .split (coordinate 10) (![⟨282854, by decide⟩,⟨282872, by decide⟩,⟨282887, by decide⟩,⟨282899, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1566_282900 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1566 ⟨282900, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1566
    ⟨282900, by decide⟩ (by decide) (![⟨282854, by decide⟩,⟨282872, by decide⟩,⟨282887, by decide⟩,⟨282899, by decide⟩]) unmarked_context_10_1566_282900 node_context_10_1566_282900
  intro a
  fin_cases a
  · exact context_11_6264_282854
  · exact context_11_6265_282872
  · exact context_11_6266_282887
  · exact context_11_6267_282899

theorem selected_cut_10396 : selected 11 ⟨282937, by decide⟩
    (prefixPartial 10 1567) = some ⟨10, 2, 0, 282937, 1567, 1633, 1048576⟩ := by
  decide +kernel

theorem context_10_1567_282937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1567 ⟨282937, by decide⟩ :=
  accepted_of_selected 10 1567 ⟨282937, by decide⟩ ⟨10, 2, 0, 282937, 1567, 1633, 1048576⟩
    (by decide) selected_cut_10396

theorem unmarked_context_9_391_282938 : frontier 12 ⟨282938, by decide⟩
    (prefixCache 9 391) (prefixPartial 9 391) = false := by
  decide +kernel

theorem node_context_9_391_282938 : EJMOriginalGlobalDAGData.nodes 12 ⟨282938, by decide⟩ =
    .split (coordinate 9) (![⟨282737, by decide⟩,⟨282836, by decide⟩,⟨282900, by decide⟩,⟨282937, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_391_282938 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 391 ⟨282938, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 391
    ⟨282938, by decide⟩ (by decide) (![⟨282737, by decide⟩,⟨282836, by decide⟩,⟨282900, by decide⟩,⟨282937, by decide⟩]) unmarked_context_9_391_282938 node_context_9_391_282938
  intro a
  fin_cases a
  · exact context_10_1564_282737
  · exact context_10_1565_282836
  · exact context_10_1566_282900
  · exact context_10_1567_282937

theorem unmarked_context_8_97_282939 : frontier 13 ⟨282939, by decide⟩
    (prefixCache 8 97) (prefixPartial 8 97) = false := by
  decide +kernel

theorem node_context_8_97_282939 : EJMOriginalGlobalDAGData.nodes 13 ⟨282939, by decide⟩ =
    .split (coordinate 8) (![⟨277903, by decide⟩,⟨281036, by decide⟩,⟨282568, by decide⟩,⟨282938, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_97_282939 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 97 ⟨282939, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 97
    ⟨282939, by decide⟩ (by decide) (![⟨277903, by decide⟩,⟨281036, by decide⟩,⟨282568, by decide⟩,⟨282938, by decide⟩]) unmarked_context_8_97_282939 node_context_8_97_282939
  intro a
  fin_cases a
  · exact context_9_388_277903
  · exact context_9_389_281036
  · exact context_9_390_282568
  · exact context_9_391_282938

theorem selected_cut_10397 : selected 10 ⟨167448, by decide⟩
    (prefixPartial 11 6272) = some ⟨11, 1, 0, 167448, 6272, 1, 262144⟩ := by
  decide +kernel

theorem context_11_6272_167448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6272 ⟨167448, by decide⟩ :=
  accepted_of_selected 11 6272 ⟨167448, by decide⟩ ⟨11, 1, 0, 167448, 6272, 1, 262144⟩
    (by decide) selected_cut_10397

theorem selected_cut_10398 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 25092) = some ⟨12, 1, 0, 34034, 25092, 1, 65536⟩ := by
  decide +kernel

theorem context_12_25092_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25092 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 25092 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 25092, 1, 65536⟩
    (by decide) selected_cut_10398

theorem selected_cut_10399 : selected 8 ⟨283005, by decide⟩
    (prefixPartial 13 100372) = some ⟨13, 2, 0, 283005, 100372, 3677, 16384⟩ := by
  decide +kernel

theorem context_13_100372_283005 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100372 ⟨283005, by decide⟩ :=
  accepted_of_selected 13 100372 ⟨283005, by decide⟩ ⟨13, 2, 0, 283005, 100372, 3677, 16384⟩
    (by decide) selected_cut_10399

theorem selected_cut_10400 : selected 8 ⟨283046, by decide⟩
    (prefixPartial 13 100373) = some ⟨13, 2, 0, 283046, 100373, 3101, 16384⟩ := by
  decide +kernel

theorem context_13_100373_283046 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100373 ⟨283046, by decide⟩ :=
  accepted_of_selected 13 100373 ⟨283046, by decide⟩ ⟨13, 2, 0, 283046, 100373, 3101, 16384⟩
    (by decide) selected_cut_10400

theorem selected_cut_10401 : selected 8 ⟨283064, by decide⟩
    (prefixPartial 13 100374) = some ⟨13, 2, 0, 283064, 100374, 1969, 16384⟩ := by
  decide +kernel

theorem context_13_100374_283064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100374 ⟨283064, by decide⟩ :=
  accepted_of_selected 13 100374 ⟨283064, by decide⟩ ⟨13, 2, 0, 283064, 100374, 1969, 16384⟩
    (by decide) selected_cut_10401

theorem selected_cut_10402 : selected 8 ⟨283072, by decide⟩
    (prefixPartial 13 100375) = some ⟨13, 2, 0, 283072, 100375, 1049, 16384⟩ := by
  decide +kernel

theorem context_13_100375_283072 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100375 ⟨283072, by decide⟩ :=
  accepted_of_selected 13 100375 ⟨283072, by decide⟩ ⟨13, 2, 0, 283072, 100375, 1049, 16384⟩
    (by decide) selected_cut_10402

theorem unmarked_context_12_25093_283073 : frontier 9 ⟨283073, by decide⟩
    (prefixCache 12 25093) (prefixPartial 12 25093) = false := by
  decide +kernel

theorem node_context_12_25093_283073 : EJMOriginalGlobalDAGData.nodes 9 ⟨283073, by decide⟩ =
    .split (coordinate 12) (![⟨283005, by decide⟩,⟨283046, by decide⟩,⟨283064, by decide⟩,⟨283072, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25093_283073 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25093 ⟨283073, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25093
    ⟨283073, by decide⟩ (by decide) (![⟨283005, by decide⟩,⟨283046, by decide⟩,⟨283064, by decide⟩,⟨283072, by decide⟩]) unmarked_context_12_25093_283073 node_context_12_25093_283073
  intro a
  fin_cases a
  · exact context_13_100372_283005
  · exact context_13_100373_283046
  · exact context_13_100374_283064
  · exact context_13_100375_283072

theorem selected_cut_10403 : selected 8 ⟨283115, by decide⟩
    (prefixPartial 13 100376) = some ⟨13, 2, 0, 283115, 100376, 3209, 16384⟩ := by
  decide +kernel

theorem context_13_100376_283115 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100376 ⟨283115, by decide⟩ :=
  accepted_of_selected 13 100376 ⟨283115, by decide⟩ ⟨13, 2, 0, 283115, 100376, 3209, 16384⟩
    (by decide) selected_cut_10403

theorem selected_cut_10404 : selected 8 ⟨283138, by decide⟩
    (prefixPartial 13 100377) = some ⟨13, 2, 0, 283138, 100377, 2821, 16384⟩ := by
  decide +kernel

theorem context_13_100377_283138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100377 ⟨283138, by decide⟩ :=
  accepted_of_selected 13 100377 ⟨283138, by decide⟩ ⟨13, 2, 0, 283138, 100377, 2821, 16384⟩
    (by decide) selected_cut_10404

theorem selected_cut_10405 : selected 8 ⟨283153, by decide⟩
    (prefixPartial 13 100378) = some ⟨13, 2, 0, 283153, 100378, 1881, 16384⟩ := by
  decide +kernel

theorem context_13_100378_283153 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100378 ⟨283153, by decide⟩ :=
  accepted_of_selected 13 100378 ⟨283153, by decide⟩ ⟨13, 2, 0, 283153, 100378, 1881, 16384⟩
    (by decide) selected_cut_10405

theorem selected_cut_10406 : selected 8 ⟨283158, by decide⟩
    (prefixPartial 13 100379) = some ⟨13, 2, 0, 283158, 100379, 1081, 16384⟩ := by
  decide +kernel

theorem context_13_100379_283158 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100379 ⟨283158, by decide⟩ :=
  accepted_of_selected 13 100379 ⟨283158, by decide⟩ ⟨13, 2, 0, 283158, 100379, 1081, 16384⟩
    (by decide) selected_cut_10406

theorem unmarked_context_12_25094_283159 : frontier 9 ⟨283159, by decide⟩
    (prefixCache 12 25094) (prefixPartial 12 25094) = false := by
  decide +kernel

theorem node_context_12_25094_283159 : EJMOriginalGlobalDAGData.nodes 9 ⟨283159, by decide⟩ =
    .split (coordinate 12) (![⟨283115, by decide⟩,⟨283138, by decide⟩,⟨283153, by decide⟩,⟨283158, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25094_283159 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25094 ⟨283159, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25094
    ⟨283159, by decide⟩ (by decide) (![⟨283115, by decide⟩,⟨283138, by decide⟩,⟨283153, by decide⟩,⟨283158, by decide⟩]) unmarked_context_12_25094_283159 node_context_12_25094_283159
  intro a
  fin_cases a
  · exact context_13_100376_283115
  · exact context_13_100377_283138
  · exact context_13_100378_283153
  · exact context_13_100379_283158

theorem selected_cut_10407 : selected 7 ⟨283183, by decide⟩
    (prefixPartial 14 401520) = some ⟨14, 2, 0, 283183, 401520, 1169, 4096⟩ := by
  decide +kernel

theorem context_14_401520_283183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 401520 ⟨283183, by decide⟩ :=
  accepted_of_selected 14 401520 ⟨283183, by decide⟩ ⟨14, 2, 0, 283183, 401520, 1169, 4096⟩
    (by decide) selected_cut_10407

theorem selected_cut_10408 : selected 7 ⟨283198, by decide⟩
    (prefixPartial 14 401521) = some ⟨14, 2, 0, 283198, 401521, 1213, 4096⟩ := by
  decide +kernel

theorem context_14_401521_283198 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 401521 ⟨283198, by decide⟩ :=
  accepted_of_selected 14 401521 ⟨283198, by decide⟩ ⟨14, 2, 0, 283198, 401521, 1213, 4096⟩
    (by decide) selected_cut_10408

theorem selected_cut_10409 : selected 7 ⟨283209, by decide⟩
    (prefixPartial 14 401522) = some ⟨14, 2, 0, 283209, 401522, 837, 4096⟩ := by
  decide +kernel

theorem context_14_401522_283209 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 401522 ⟨283209, by decide⟩ :=
  accepted_of_selected 14 401522 ⟨283209, by decide⟩ ⟨14, 2, 0, 283209, 401522, 837, 4096⟩
    (by decide) selected_cut_10409

theorem selected_cut_10410 : selected 7 ⟨283225, by decide⟩
    (prefixPartial 14 401523) = some ⟨14, 2, 0, 283225, 401523, 1057, 4096⟩ := by
  decide +kernel

theorem context_14_401523_283225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 401523 ⟨283225, by decide⟩ :=
  accepted_of_selected 14 401523 ⟨283225, by decide⟩ ⟨14, 2, 0, 283225, 401523, 1057, 4096⟩
    (by decide) selected_cut_10410

theorem unmarked_context_13_100380_283226 : frontier 8 ⟨283226, by decide⟩
    (prefixCache 13 100380) (prefixPartial 13 100380) = false := by
  decide +kernel

theorem node_context_13_100380_283226 : EJMOriginalGlobalDAGData.nodes 8 ⟨283226, by decide⟩ =
    .split (coordinate 13) (![⟨283183, by decide⟩,⟨283198, by decide⟩,⟨283209, by decide⟩,⟨283225, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_100380_283226 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100380 ⟨283226, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 100380
    ⟨283226, by decide⟩ (by decide) (![⟨283183, by decide⟩,⟨283198, by decide⟩,⟨283209, by decide⟩,⟨283225, by decide⟩]) unmarked_context_13_100380_283226 node_context_13_100380_283226
  intro a
  fin_cases a
  · exact context_14_401520_283183
  · exact context_14_401521_283198
  · exact context_14_401522_283209
  · exact context_14_401523_283225

theorem selected_cut_10411 : selected 8 ⟨283257, by decide⟩
    (prefixPartial 13 100381) = some ⟨13, 2, 0, 283257, 100381, 3201, 16384⟩ := by
  decide +kernel

theorem context_13_100381_283257 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100381 ⟨283257, by decide⟩ :=
  accepted_of_selected 13 100381 ⟨283257, by decide⟩ ⟨13, 2, 0, 283257, 100381, 3201, 16384⟩
    (by decide) selected_cut_10411

theorem selected_cut_10412 : selected 8 ⟨283279, by decide⟩
    (prefixPartial 13 100382) = some ⟨13, 2, 0, 283279, 100382, 2081, 16384⟩ := by
  decide +kernel

theorem context_13_100382_283279 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100382 ⟨283279, by decide⟩ :=
  accepted_of_selected 13 100382 ⟨283279, by decide⟩ ⟨13, 2, 0, 283279, 100382, 2081, 16384⟩
    (by decide) selected_cut_10412

theorem selected_cut_10413 : selected 8 ⟨283288, by decide⟩
    (prefixPartial 13 100383) = some ⟨13, 2, 0, 283288, 100383, 1197, 16384⟩ := by
  decide +kernel

theorem context_13_100383_283288 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100383 ⟨283288, by decide⟩ :=
  accepted_of_selected 13 100383 ⟨283288, by decide⟩ ⟨13, 2, 0, 283288, 100383, 1197, 16384⟩
    (by decide) selected_cut_10413

theorem unmarked_context_12_25095_283289 : frontier 9 ⟨283289, by decide⟩
    (prefixCache 12 25095) (prefixPartial 12 25095) = false := by
  decide +kernel

theorem node_context_12_25095_283289 : EJMOriginalGlobalDAGData.nodes 9 ⟨283289, by decide⟩ =
    .split (coordinate 12) (![⟨283226, by decide⟩,⟨283257, by decide⟩,⟨283279, by decide⟩,⟨283288, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25095_283289 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25095 ⟨283289, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25095
    ⟨283289, by decide⟩ (by decide) (![⟨283226, by decide⟩,⟨283257, by decide⟩,⟨283279, by decide⟩,⟨283288, by decide⟩]) unmarked_context_12_25095_283289 node_context_12_25095_283289
  intro a
  fin_cases a
  · exact context_13_100380_283226
  · exact context_13_100381_283257
  · exact context_13_100382_283279
  · exact context_13_100383_283288

theorem unmarked_context_11_6273_283290 : frontier 10 ⟨283290, by decide⟩
    (prefixCache 11 6273) (prefixPartial 11 6273) = false := by
  decide +kernel

theorem node_context_11_6273_283290 : EJMOriginalGlobalDAGData.nodes 10 ⟨283290, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨283073, by decide⟩,⟨283159, by decide⟩,⟨283289, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6273_283290 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6273 ⟨283290, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6273
    ⟨283290, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨283073, by decide⟩,⟨283159, by decide⟩,⟨283289, by decide⟩]) unmarked_context_11_6273_283290 node_context_11_6273_283290
  intro a
  fin_cases a
  · exact context_12_25092_34034
  · exact context_12_25093_283073
  · exact context_12_25094_283159
  · exact context_12_25095_283289

theorem selected_cut_10414 : selected 8 ⟨283343, by decide⟩
    (prefixPartial 13 100384) = some ⟨13, 2, 0, 283343, 100384, 2785, 16384⟩ := by
  decide +kernel

theorem context_13_100384_283343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100384 ⟨283343, by decide⟩ :=
  accepted_of_selected 13 100384 ⟨283343, by decide⟩ ⟨13, 2, 0, 283343, 100384, 2785, 16384⟩
    (by decide) selected_cut_10414

theorem selected_cut_10415 : selected 8 ⟨283374, by decide⟩
    (prefixPartial 13 100385) = some ⟨13, 2, 0, 283374, 100385, 2569, 16384⟩ := by
  decide +kernel

theorem context_13_100385_283374 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100385 ⟨283374, by decide⟩ :=
  accepted_of_selected 13 100385 ⟨283374, by decide⟩ ⟨13, 2, 0, 283374, 100385, 2569, 16384⟩
    (by decide) selected_cut_10415

theorem selected_cut_10416 : selected 8 ⟨283395, by decide⟩
    (prefixPartial 13 100386) = some ⟨13, 2, 0, 283395, 100386, 1741, 16384⟩ := by
  decide +kernel

theorem context_13_100386_283395 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100386 ⟨283395, by decide⟩ :=
  accepted_of_selected 13 100386 ⟨283395, by decide⟩ ⟨13, 2, 0, 283395, 100386, 1741, 16384⟩
    (by decide) selected_cut_10416

theorem selected_cut_10417 : selected 8 ⟨283405, by decide⟩
    (prefixPartial 13 100387) = some ⟨13, 2, 0, 283405, 100387, 953, 16384⟩ := by
  decide +kernel

theorem context_13_100387_283405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100387 ⟨283405, by decide⟩ :=
  accepted_of_selected 13 100387 ⟨283405, by decide⟩ ⟨13, 2, 0, 283405, 100387, 953, 16384⟩
    (by decide) selected_cut_10417

theorem unmarked_context_12_25096_283406 : frontier 9 ⟨283406, by decide⟩
    (prefixCache 12 25096) (prefixPartial 12 25096) = false := by
  decide +kernel

theorem node_context_12_25096_283406 : EJMOriginalGlobalDAGData.nodes 9 ⟨283406, by decide⟩ =
    .split (coordinate 12) (![⟨283343, by decide⟩,⟨283374, by decide⟩,⟨283395, by decide⟩,⟨283405, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25096_283406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25096 ⟨283406, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25096
    ⟨283406, by decide⟩ (by decide) (![⟨283343, by decide⟩,⟨283374, by decide⟩,⟨283395, by decide⟩,⟨283405, by decide⟩]) unmarked_context_12_25096_283406 node_context_12_25096_283406
  intro a
  fin_cases a
  · exact context_13_100384_283343
  · exact context_13_100385_283374
  · exact context_13_100386_283395
  · exact context_13_100387_283405

theorem selected_cut_10418 : selected 8 ⟨283459, by decide⟩
    (prefixPartial 13 100388) = some ⟨13, 2, 0, 283459, 100388, 2785, 16384⟩ := by
  decide +kernel

theorem context_13_100388_283459 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100388 ⟨283459, by decide⟩ :=
  accepted_of_selected 13 100388 ⟨283459, by decide⟩ ⟨13, 2, 0, 283459, 100388, 2785, 16384⟩
    (by decide) selected_cut_10418

theorem selected_cut_10419 : selected 8 ⟨283497, by decide⟩
    (prefixPartial 13 100389) = some ⟨13, 2, 0, 283497, 100389, 2993, 16384⟩ := by
  decide +kernel

theorem context_13_100389_283497 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100389 ⟨283497, by decide⟩ :=
  accepted_of_selected 13 100389 ⟨283497, by decide⟩ ⟨13, 2, 0, 283497, 100389, 2993, 16384⟩
    (by decide) selected_cut_10419

theorem selected_cut_10420 : selected 8 ⟨283518, by decide⟩
    (prefixPartial 13 100390) = some ⟨13, 2, 0, 283518, 100390, 1981, 16384⟩ := by
  decide +kernel

theorem context_13_100390_283518 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100390 ⟨283518, by decide⟩ :=
  accepted_of_selected 13 100390 ⟨283518, by decide⟩ ⟨13, 2, 0, 283518, 100390, 1981, 16384⟩
    (by decide) selected_cut_10420

theorem selected_cut_10421 : selected 8 ⟨283527, by decide⟩
    (prefixPartial 13 100391) = some ⟨13, 2, 0, 283527, 100391, 965, 16384⟩ := by
  decide +kernel

theorem context_13_100391_283527 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100391 ⟨283527, by decide⟩ :=
  accepted_of_selected 13 100391 ⟨283527, by decide⟩ ⟨13, 2, 0, 283527, 100391, 965, 16384⟩
    (by decide) selected_cut_10421

theorem unmarked_context_12_25097_283528 : frontier 9 ⟨283528, by decide⟩
    (prefixCache 12 25097) (prefixPartial 12 25097) = false := by
  decide +kernel

theorem node_context_12_25097_283528 : EJMOriginalGlobalDAGData.nodes 9 ⟨283528, by decide⟩ =
    .split (coordinate 12) (![⟨283459, by decide⟩,⟨283497, by decide⟩,⟨283518, by decide⟩,⟨283527, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25097_283528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25097 ⟨283528, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25097
    ⟨283528, by decide⟩ (by decide) (![⟨283459, by decide⟩,⟨283497, by decide⟩,⟨283518, by decide⟩,⟨283527, by decide⟩]) unmarked_context_12_25097_283528 node_context_12_25097_283528
  intro a
  fin_cases a
  · exact context_13_100388_283459
  · exact context_13_100389_283497
  · exact context_13_100390_283518
  · exact context_13_100391_283527

theorem selected_cut_10422 : selected 7 ⟨283546, by decide⟩
    (prefixPartial 14 401568) = some ⟨14, 2, 0, 283546, 401568, 969, 4096⟩ := by
  decide +kernel

theorem context_14_401568_283546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 401568 ⟨283546, by decide⟩ :=
  accepted_of_selected 14 401568 ⟨283546, by decide⟩ ⟨14, 2, 0, 283546, 401568, 969, 4096⟩
    (by decide) selected_cut_10422

theorem selected_cut_10423 : selected 7 ⟨283565, by decide⟩
    (prefixPartial 14 401569) = some ⟨14, 2, 0, 283565, 401569, 1229, 4096⟩ := by
  decide +kernel

theorem context_14_401569_283565 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 401569 ⟨283565, by decide⟩ :=
  accepted_of_selected 14 401569 ⟨283565, by decide⟩ ⟨14, 2, 0, 283565, 401569, 1229, 4096⟩
    (by decide) selected_cut_10423

theorem selected_cut_10424 : selected 7 ⟨283571, by decide⟩
    (prefixPartial 14 401570) = some ⟨14, 2, 0, 283571, 401570, 869, 4096⟩ := by
  decide +kernel

theorem context_14_401570_283571 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 401570 ⟨283571, by decide⟩ :=
  accepted_of_selected 14 401570 ⟨283571, by decide⟩ ⟨14, 2, 0, 283571, 401570, 869, 4096⟩
    (by decide) selected_cut_10424

theorem selected_cut_10425 : selected 7 ⟨283587, by decide⟩
    (prefixPartial 14 401571) = some ⟨14, 2, 0, 283587, 401571, 1161, 4096⟩ := by
  decide +kernel

theorem context_14_401571_283587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 401571 ⟨283587, by decide⟩ :=
  accepted_of_selected 14 401571 ⟨283587, by decide⟩ ⟨14, 2, 0, 283587, 401571, 1161, 4096⟩
    (by decide) selected_cut_10425

theorem unmarked_context_13_100392_283588 : frontier 8 ⟨283588, by decide⟩
    (prefixCache 13 100392) (prefixPartial 13 100392) = false := by
  decide +kernel

theorem node_context_13_100392_283588 : EJMOriginalGlobalDAGData.nodes 8 ⟨283588, by decide⟩ =
    .split (coordinate 13) (![⟨283546, by decide⟩,⟨283565, by decide⟩,⟨283571, by decide⟩,⟨283587, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_100392_283588 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100392 ⟨283588, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 100392
    ⟨283588, by decide⟩ (by decide) (![⟨283546, by decide⟩,⟨283565, by decide⟩,⟨283571, by decide⟩,⟨283587, by decide⟩]) unmarked_context_13_100392_283588 node_context_13_100392_283588
  intro a
  fin_cases a
  · exact context_14_401568_283546
  · exact context_14_401569_283565
  · exact context_14_401570_283571
  · exact context_14_401571_283587

theorem selected_cut_10426 : selected 7 ⟨283618, by decide⟩
    (prefixPartial 14 401572) = some ⟨14, 2, 0, 283618, 401572, 1325, 4096⟩ := by
  decide +kernel

theorem context_14_401572_283618 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 401572 ⟨283618, by decide⟩ :=
  accepted_of_selected 14 401572 ⟨283618, by decide⟩ ⟨14, 2, 0, 283618, 401572, 1325, 4096⟩
    (by decide) selected_cut_10426

theorem selected_cut_10427 : selected 7 ⟨283637, by decide⟩
    (prefixPartial 14 401573) = some ⟨14, 2, 0, 283637, 401573, 1049, 4096⟩ := by
  decide +kernel

theorem context_14_401573_283637 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 401573 ⟨283637, by decide⟩ :=
  accepted_of_selected 14 401573 ⟨283637, by decide⟩ ⟨14, 2, 0, 283637, 401573, 1049, 4096⟩
    (by decide) selected_cut_10427

theorem selected_cut_10428 : selected 7 ⟨283650, by decide⟩
    (prefixPartial 14 401574) = some ⟨14, 2, 0, 283650, 401574, 957, 4096⟩ := by
  decide +kernel

theorem context_14_401574_283650 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 401574 ⟨283650, by decide⟩ :=
  accepted_of_selected 14 401574 ⟨283650, by decide⟩ ⟨14, 2, 0, 283650, 401574, 957, 4096⟩
    (by decide) selected_cut_10428

theorem selected_cut_10429 : selected 7 ⟨283668, by decide⟩
    (prefixPartial 14 401575) = some ⟨14, 2, 0, 283668, 401575, 1073, 4096⟩ := by
  decide +kernel

theorem context_14_401575_283668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 401575 ⟨283668, by decide⟩ :=
  accepted_of_selected 14 401575 ⟨283668, by decide⟩ ⟨14, 2, 0, 283668, 401575, 1073, 4096⟩
    (by decide) selected_cut_10429

theorem unmarked_context_13_100393_283669 : frontier 8 ⟨283669, by decide⟩
    (prefixCache 13 100393) (prefixPartial 13 100393) = false := by
  decide +kernel

theorem node_context_13_100393_283669 : EJMOriginalGlobalDAGData.nodes 8 ⟨283669, by decide⟩ =
    .split (coordinate 13) (![⟨283618, by decide⟩,⟨283637, by decide⟩,⟨283650, by decide⟩,⟨283668, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_100393_283669 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100393 ⟨283669, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 100393
    ⟨283669, by decide⟩ (by decide) (![⟨283618, by decide⟩,⟨283637, by decide⟩,⟨283650, by decide⟩,⟨283668, by decide⟩]) unmarked_context_13_100393_283669 node_context_13_100393_283669
  intro a
  fin_cases a
  · exact context_14_401572_283618
  · exact context_14_401573_283637
  · exact context_14_401574_283650
  · exact context_14_401575_283668

theorem selected_cut_10430 : selected 8 ⟨283724, by decide⟩
    (prefixPartial 13 100394) = some ⟨13, 2, 0, 283724, 100394, 2809, 16384⟩ := by
  decide +kernel

theorem context_13_100394_283724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100394 ⟨283724, by decide⟩ :=
  accepted_of_selected 13 100394 ⟨283724, by decide⟩ ⟨13, 2, 0, 283724, 100394, 2809, 16384⟩
    (by decide) selected_cut_10430

theorem selected_cut_10431 : selected 8 ⟨283741, by decide⟩
    (prefixPartial 13 100395) = some ⟨13, 2, 0, 283741, 100395, 1289, 16384⟩ := by
  decide +kernel

theorem context_13_100395_283741 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100395 ⟨283741, by decide⟩ :=
  accepted_of_selected 13 100395 ⟨283741, by decide⟩ ⟨13, 2, 0, 283741, 100395, 1289, 16384⟩
    (by decide) selected_cut_10431

theorem unmarked_context_12_25098_283742 : frontier 9 ⟨283742, by decide⟩
    (prefixCache 12 25098) (prefixPartial 12 25098) = false := by
  decide +kernel

theorem node_context_12_25098_283742 : EJMOriginalGlobalDAGData.nodes 9 ⟨283742, by decide⟩ =
    .split (coordinate 12) (![⟨283588, by decide⟩,⟨283669, by decide⟩,⟨283724, by decide⟩,⟨283741, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25098_283742 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25098 ⟨283742, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25098
    ⟨283742, by decide⟩ (by decide) (![⟨283588, by decide⟩,⟨283669, by decide⟩,⟨283724, by decide⟩,⟨283741, by decide⟩]) unmarked_context_12_25098_283742 node_context_12_25098_283742
  intro a
  fin_cases a
  · exact context_13_100392_283588
  · exact context_13_100393_283669
  · exact context_13_100394_283724
  · exact context_13_100395_283741

theorem selected_cut_10432 : selected 8 ⟨283789, by decide⟩
    (prefixPartial 13 100396) = some ⟨13, 2, 0, 283789, 100396, 3153, 16384⟩ := by
  decide +kernel

theorem context_13_100396_283789 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100396 ⟨283789, by decide⟩ :=
  accepted_of_selected 13 100396 ⟨283789, by decide⟩ ⟨13, 2, 0, 283789, 100396, 3153, 16384⟩
    (by decide) selected_cut_10432

theorem selected_cut_10433 : selected 8 ⟨283829, by decide⟩
    (prefixPartial 13 100397) = some ⟨13, 2, 0, 283829, 100397, 3205, 16384⟩ := by
  decide +kernel

theorem context_13_100397_283829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100397 ⟨283829, by decide⟩ :=
  accepted_of_selected 13 100397 ⟨283829, by decide⟩ ⟨13, 2, 0, 283829, 100397, 3205, 16384⟩
    (by decide) selected_cut_10433

theorem selected_cut_10434 : selected 8 ⟨283848, by decide⟩
    (prefixPartial 13 100398) = some ⟨13, 2, 0, 283848, 100398, 1957, 16384⟩ := by
  decide +kernel

theorem context_13_100398_283848 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100398 ⟨283848, by decide⟩ :=
  accepted_of_selected 13 100398 ⟨283848, by decide⟩ ⟨13, 2, 0, 283848, 100398, 1957, 16384⟩
    (by decide) selected_cut_10434

theorem selected_cut_10435 : selected 8 ⟨283855, by decide⟩
    (prefixPartial 13 100399) = some ⟨13, 2, 0, 283855, 100399, 1049, 16384⟩ := by
  decide +kernel

theorem context_13_100399_283855 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100399 ⟨283855, by decide⟩ :=
  accepted_of_selected 13 100399 ⟨283855, by decide⟩ ⟨13, 2, 0, 283855, 100399, 1049, 16384⟩
    (by decide) selected_cut_10435

theorem unmarked_context_12_25099_283856 : frontier 9 ⟨283856, by decide⟩
    (prefixCache 12 25099) (prefixPartial 12 25099) = false := by
  decide +kernel

theorem node_context_12_25099_283856 : EJMOriginalGlobalDAGData.nodes 9 ⟨283856, by decide⟩ =
    .split (coordinate 12) (![⟨283789, by decide⟩,⟨283829, by decide⟩,⟨283848, by decide⟩,⟨283855, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25099_283856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25099 ⟨283856, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25099
    ⟨283856, by decide⟩ (by decide) (![⟨283789, by decide⟩,⟨283829, by decide⟩,⟨283848, by decide⟩,⟨283855, by decide⟩]) unmarked_context_12_25099_283856 node_context_12_25099_283856
  intro a
  fin_cases a
  · exact context_13_100396_283789
  · exact context_13_100397_283829
  · exact context_13_100398_283848
  · exact context_13_100399_283855

theorem unmarked_context_11_6274_283857 : frontier 10 ⟨283857, by decide⟩
    (prefixCache 11 6274) (prefixPartial 11 6274) = false := by
  decide +kernel

theorem node_context_11_6274_283857 : EJMOriginalGlobalDAGData.nodes 10 ⟨283857, by decide⟩ =
    .split (coordinate 11) (![⟨283406, by decide⟩,⟨283528, by decide⟩,⟨283742, by decide⟩,⟨283856, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6274_283857 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6274 ⟨283857, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6274
    ⟨283857, by decide⟩ (by decide) (![⟨283406, by decide⟩,⟨283528, by decide⟩,⟨283742, by decide⟩,⟨283856, by decide⟩]) unmarked_context_11_6274_283857 node_context_11_6274_283857
  intro a
  fin_cases a
  · exact context_12_25096_283406
  · exact context_12_25097_283528
  · exact context_12_25098_283742
  · exact context_12_25099_283856

theorem selected_cut_10436 : selected 8 ⟨283889, by decide⟩
    (prefixPartial 13 100400) = some ⟨13, 2, 0, 283889, 100400, 2565, 16384⟩ := by
  decide +kernel

theorem context_13_100400_283889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100400 ⟨283889, by decide⟩ :=
  accepted_of_selected 13 100400 ⟨283889, by decide⟩ ⟨13, 2, 0, 283889, 100400, 2565, 16384⟩
    (by decide) selected_cut_10436

theorem selected_cut_10437 : selected 8 ⟨283917, by decide⟩
    (prefixPartial 13 100401) = some ⟨13, 2, 0, 283917, 100401, 2893, 16384⟩ := by
  decide +kernel

theorem context_13_100401_283917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100401 ⟨283917, by decide⟩ :=
  accepted_of_selected 13 100401 ⟨283917, by decide⟩ ⟨13, 2, 0, 283917, 100401, 2893, 16384⟩
    (by decide) selected_cut_10437

theorem selected_cut_10438 : selected 8 ⟨283942, by decide⟩
    (prefixPartial 13 100402) = some ⟨13, 2, 0, 283942, 100402, 1937, 16384⟩ := by
  decide +kernel

theorem context_13_100402_283942 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100402 ⟨283942, by decide⟩ :=
  accepted_of_selected 13 100402 ⟨283942, by decide⟩ ⟨13, 2, 0, 283942, 100402, 1937, 16384⟩
    (by decide) selected_cut_10438

theorem selected_cut_10439 : selected 8 ⟨283951, by decide⟩
    (prefixPartial 13 100403) = some ⟨13, 2, 0, 283951, 100403, 1065, 16384⟩ := by
  decide +kernel

theorem context_13_100403_283951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100403 ⟨283951, by decide⟩ :=
  accepted_of_selected 13 100403 ⟨283951, by decide⟩ ⟨13, 2, 0, 283951, 100403, 1065, 16384⟩
    (by decide) selected_cut_10439

theorem unmarked_context_12_25100_283952 : frontier 9 ⟨283952, by decide⟩
    (prefixCache 12 25100) (prefixPartial 12 25100) = false := by
  decide +kernel

theorem node_context_12_25100_283952 : EJMOriginalGlobalDAGData.nodes 9 ⟨283952, by decide⟩ =
    .split (coordinate 12) (![⟨283889, by decide⟩,⟨283917, by decide⟩,⟨283942, by decide⟩,⟨283951, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25100_283952 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25100 ⟨283952, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25100
    ⟨283952, by decide⟩ (by decide) (![⟨283889, by decide⟩,⟨283917, by decide⟩,⟨283942, by decide⟩,⟨283951, by decide⟩]) unmarked_context_12_25100_283952 node_context_12_25100_283952
  intro a
  fin_cases a
  · exact context_13_100400_283889
  · exact context_13_100401_283917
  · exact context_13_100402_283942
  · exact context_13_100403_283951

theorem selected_cut_10440 : selected 8 ⟨283992, by decide⟩
    (prefixPartial 13 100404) = some ⟨13, 2, 0, 283992, 100404, 2901, 16384⟩ := by
  decide +kernel

theorem context_13_100404_283992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100404 ⟨283992, by decide⟩ :=
  accepted_of_selected 13 100404 ⟨283992, by decide⟩ ⟨13, 2, 0, 283992, 100404, 2901, 16384⟩
    (by decide) selected_cut_10440

theorem selected_cut_10441 : selected 8 ⟨284033, by decide⟩
    (prefixPartial 13 100405) = some ⟨13, 2, 0, 284033, 100405, 3333, 16384⟩ := by
  decide +kernel

theorem context_13_100405_284033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100405 ⟨284033, by decide⟩ :=
  accepted_of_selected 13 100405 ⟨284033, by decide⟩ ⟨13, 2, 0, 284033, 100405, 3333, 16384⟩
    (by decide) selected_cut_10441

theorem selected_cut_10442 : selected 8 ⟨284061, by decide⟩
    (prefixPartial 13 100406) = some ⟨13, 2, 0, 284061, 100406, 2041, 16384⟩ := by
  decide +kernel

theorem context_13_100406_284061 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100406 ⟨284061, by decide⟩ :=
  accepted_of_selected 13 100406 ⟨284061, by decide⟩ ⟨13, 2, 0, 284061, 100406, 2041, 16384⟩
    (by decide) selected_cut_10442

theorem selected_cut_10443 : selected 8 ⟨284068, by decide⟩
    (prefixPartial 13 100407) = some ⟨13, 2, 0, 284068, 100407, 981, 16384⟩ := by
  decide +kernel

theorem context_13_100407_284068 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100407 ⟨284068, by decide⟩ :=
  accepted_of_selected 13 100407 ⟨284068, by decide⟩ ⟨13, 2, 0, 284068, 100407, 981, 16384⟩
    (by decide) selected_cut_10443

theorem unmarked_context_12_25101_284069 : frontier 9 ⟨284069, by decide⟩
    (prefixCache 12 25101) (prefixPartial 12 25101) = false := by
  decide +kernel

theorem node_context_12_25101_284069 : EJMOriginalGlobalDAGData.nodes 9 ⟨284069, by decide⟩ =
    .split (coordinate 12) (![⟨283992, by decide⟩,⟨284033, by decide⟩,⟨284061, by decide⟩,⟨284068, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25101_284069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25101 ⟨284069, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25101
    ⟨284069, by decide⟩ (by decide) (![⟨283992, by decide⟩,⟨284033, by decide⟩,⟨284061, by decide⟩,⟨284068, by decide⟩]) unmarked_context_12_25101_284069 node_context_12_25101_284069
  intro a
  fin_cases a
  · exact context_13_100404_283992
  · exact context_13_100405_284033
  · exact context_13_100406_284061
  · exact context_13_100407_284068

theorem selected_cut_10444 : selected 8 ⟨284104, by decide⟩
    (prefixPartial 13 100408) = some ⟨13, 2, 0, 284104, 100408, 2517, 16384⟩ := by
  decide +kernel

theorem context_13_100408_284104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100408 ⟨284104, by decide⟩ :=
  accepted_of_selected 13 100408 ⟨284104, by decide⟩ ⟨13, 2, 0, 284104, 100408, 2517, 16384⟩
    (by decide) selected_cut_10444

theorem selected_cut_10445 : selected 8 ⟨284135, by decide⟩
    (prefixPartial 13 100409) = some ⟨13, 2, 0, 284135, 100409, 3021, 16384⟩ := by
  decide +kernel

theorem context_13_100409_284135 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100409 ⟨284135, by decide⟩ :=
  accepted_of_selected 13 100409 ⟨284135, by decide⟩ ⟨13, 2, 0, 284135, 100409, 3021, 16384⟩
    (by decide) selected_cut_10445

theorem selected_cut_10446 : selected 8 ⟨284153, by decide⟩
    (prefixPartial 13 100410) = some ⟨13, 2, 0, 284153, 100410, 1849, 16384⟩ := by
  decide +kernel

theorem context_13_100410_284153 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100410 ⟨284153, by decide⟩ :=
  accepted_of_selected 13 100410 ⟨284153, by decide⟩ ⟨13, 2, 0, 284153, 100410, 1849, 16384⟩
    (by decide) selected_cut_10446

theorem selected_cut_10447 : selected 8 ⟨284159, by decide⟩
    (prefixPartial 13 100411) = some ⟨13, 2, 0, 284159, 100411, 941, 16384⟩ := by
  decide +kernel

theorem context_13_100411_284159 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100411 ⟨284159, by decide⟩ :=
  accepted_of_selected 13 100411 ⟨284159, by decide⟩ ⟨13, 2, 0, 284159, 100411, 941, 16384⟩
    (by decide) selected_cut_10447

theorem unmarked_context_12_25102_284160 : frontier 9 ⟨284160, by decide⟩
    (prefixCache 12 25102) (prefixPartial 12 25102) = false := by
  decide +kernel

theorem node_context_12_25102_284160 : EJMOriginalGlobalDAGData.nodes 9 ⟨284160, by decide⟩ =
    .split (coordinate 12) (![⟨284104, by decide⟩,⟨284135, by decide⟩,⟨284153, by decide⟩,⟨284159, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25102_284160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25102 ⟨284160, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25102
    ⟨284160, by decide⟩ (by decide) (![⟨284104, by decide⟩,⟨284135, by decide⟩,⟨284153, by decide⟩,⟨284159, by decide⟩]) unmarked_context_12_25102_284160 node_context_12_25102_284160
  intro a
  fin_cases a
  · exact context_13_100408_284104
  · exact context_13_100409_284135
  · exact context_13_100410_284153
  · exact context_13_100411_284159

theorem selected_cut_10448 : selected 8 ⟨284197, by decide⟩
    (prefixPartial 13 100412) = some ⟨13, 2, 0, 284197, 100412, 3121, 16384⟩ := by
  decide +kernel

theorem context_13_100412_284197 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100412 ⟨284197, by decide⟩ :=
  accepted_of_selected 13 100412 ⟨284197, by decide⟩ ⟨13, 2, 0, 284197, 100412, 3121, 16384⟩
    (by decide) selected_cut_10448

theorem selected_cut_10449 : selected 8 ⟨284232, by decide⟩
    (prefixPartial 13 100413) = some ⟨13, 2, 0, 284232, 100413, 3233, 16384⟩ := by
  decide +kernel

theorem context_13_100413_284232 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100413 ⟨284232, by decide⟩ :=
  accepted_of_selected 13 100413 ⟨284232, by decide⟩ ⟨13, 2, 0, 284232, 100413, 3233, 16384⟩
    (by decide) selected_cut_10449

theorem selected_cut_10450 : selected 8 ⟨284254, by decide⟩
    (prefixPartial 13 100414) = some ⟨13, 2, 0, 284254, 100414, 2053, 16384⟩ := by
  decide +kernel

theorem context_13_100414_284254 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100414 ⟨284254, by decide⟩ :=
  accepted_of_selected 13 100414 ⟨284254, by decide⟩ ⟨13, 2, 0, 284254, 100414, 2053, 16384⟩
    (by decide) selected_cut_10450

theorem selected_cut_10451 : selected 8 ⟨284263, by decide⟩
    (prefixPartial 13 100415) = some ⟨13, 2, 0, 284263, 100415, 1133, 16384⟩ := by
  decide +kernel

theorem context_13_100415_284263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100415 ⟨284263, by decide⟩ :=
  accepted_of_selected 13 100415 ⟨284263, by decide⟩ ⟨13, 2, 0, 284263, 100415, 1133, 16384⟩
    (by decide) selected_cut_10451

theorem unmarked_context_12_25103_284264 : frontier 9 ⟨284264, by decide⟩
    (prefixCache 12 25103) (prefixPartial 12 25103) = false := by
  decide +kernel

theorem node_context_12_25103_284264 : EJMOriginalGlobalDAGData.nodes 9 ⟨284264, by decide⟩ =
    .split (coordinate 12) (![⟨284197, by decide⟩,⟨284232, by decide⟩,⟨284254, by decide⟩,⟨284263, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25103_284264 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25103 ⟨284264, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25103
    ⟨284264, by decide⟩ (by decide) (![⟨284197, by decide⟩,⟨284232, by decide⟩,⟨284254, by decide⟩,⟨284263, by decide⟩]) unmarked_context_12_25103_284264 node_context_12_25103_284264
  intro a
  fin_cases a
  · exact context_13_100412_284197
  · exact context_13_100413_284232
  · exact context_13_100414_284254
  · exact context_13_100415_284263

theorem unmarked_context_11_6275_284265 : frontier 10 ⟨284265, by decide⟩
    (prefixCache 11 6275) (prefixPartial 11 6275) = false := by
  decide +kernel

theorem node_context_11_6275_284265 : EJMOriginalGlobalDAGData.nodes 10 ⟨284265, by decide⟩ =
    .split (coordinate 11) (![⟨283952, by decide⟩,⟨284069, by decide⟩,⟨284160, by decide⟩,⟨284264, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6275_284265 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6275 ⟨284265, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6275
    ⟨284265, by decide⟩ (by decide) (![⟨283952, by decide⟩,⟨284069, by decide⟩,⟨284160, by decide⟩,⟨284264, by decide⟩]) unmarked_context_11_6275_284265 node_context_11_6275_284265
  intro a
  fin_cases a
  · exact context_12_25100_283952
  · exact context_12_25101_284069
  · exact context_12_25102_284160
  · exact context_12_25103_284264

theorem unmarked_context_10_1568_284266 : frontier 11 ⟨284266, by decide⟩
    (prefixCache 10 1568) (prefixPartial 10 1568) = false := by
  decide +kernel

theorem node_context_10_1568_284266 : EJMOriginalGlobalDAGData.nodes 11 ⟨284266, by decide⟩ =
    .split (coordinate 10) (![⟨167448, by decide⟩,⟨283290, by decide⟩,⟨283857, by decide⟩,⟨284265, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1568_284266 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1568 ⟨284266, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1568
    ⟨284266, by decide⟩ (by decide) (![⟨167448, by decide⟩,⟨283290, by decide⟩,⟨283857, by decide⟩,⟨284265, by decide⟩]) unmarked_context_10_1568_284266 node_context_10_1568_284266
  intro a
  fin_cases a
  · exact context_11_6272_167448
  · exact context_11_6273_283290
  · exact context_11_6274_283857
  · exact context_11_6275_284265

theorem selected_cut_10452 : selected 8 ⟨284287, by decide⟩
    (prefixPartial 13 100416) = some ⟨13, 2, 0, 284287, 100416, 1449, 16384⟩ := by
  decide +kernel

theorem context_13_100416_284287 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100416 ⟨284287, by decide⟩ :=
  accepted_of_selected 13 100416 ⟨284287, by decide⟩ ⟨13, 2, 0, 284287, 100416, 1449, 16384⟩
    (by decide) selected_cut_10452

theorem selected_cut_10453 : selected 8 ⟨284305, by decide⟩
    (prefixPartial 13 100417) = some ⟨13, 2, 0, 284305, 100417, 1229, 16384⟩ := by
  decide +kernel

theorem context_13_100417_284305 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100417 ⟨284305, by decide⟩ :=
  accepted_of_selected 13 100417 ⟨284305, by decide⟩ ⟨13, 2, 0, 284305, 100417, 1229, 16384⟩
    (by decide) selected_cut_10453

theorem selected_cut_10454 : selected 8 ⟨284321, by decide⟩
    (prefixPartial 13 100418) = some ⟨13, 2, 0, 284321, 100418, 909, 16384⟩ := by
  decide +kernel

theorem context_13_100418_284321 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100418 ⟨284321, by decide⟩ :=
  accepted_of_selected 13 100418 ⟨284321, by decide⟩ ⟨13, 2, 0, 284321, 100418, 909, 16384⟩
    (by decide) selected_cut_10454

theorem selected_cut_10455 : selected 8 ⟨284325, by decide⟩
    (prefixPartial 13 100419) = some ⟨13, 2, 0, 284325, 100419, 625, 16384⟩ := by
  decide +kernel

theorem context_13_100419_284325 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100419 ⟨284325, by decide⟩ :=
  accepted_of_selected 13 100419 ⟨284325, by decide⟩ ⟨13, 2, 0, 284325, 100419, 625, 16384⟩
    (by decide) selected_cut_10455

theorem unmarked_context_12_25104_284326 : frontier 9 ⟨284326, by decide⟩
    (prefixCache 12 25104) (prefixPartial 12 25104) = false := by
  decide +kernel

theorem node_context_12_25104_284326 : EJMOriginalGlobalDAGData.nodes 9 ⟨284326, by decide⟩ =
    .split (coordinate 12) (![⟨284287, by decide⟩,⟨284305, by decide⟩,⟨284321, by decide⟩,⟨284325, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25104_284326 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25104 ⟨284326, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25104
    ⟨284326, by decide⟩ (by decide) (![⟨284287, by decide⟩,⟨284305, by decide⟩,⟨284321, by decide⟩,⟨284325, by decide⟩]) unmarked_context_12_25104_284326 node_context_12_25104_284326
  intro a
  fin_cases a
  · exact context_13_100416_284287
  · exact context_13_100417_284305
  · exact context_13_100418_284321
  · exact context_13_100419_284325

theorem selected_cut_10456 : selected 8 ⟨284346, by decide⟩
    (prefixPartial 13 100420) = some ⟨13, 2, 0, 284346, 100420, 1373, 16384⟩ := by
  decide +kernel

theorem context_13_100420_284346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100420 ⟨284346, by decide⟩ :=
  accepted_of_selected 13 100420 ⟨284346, by decide⟩ ⟨13, 2, 0, 284346, 100420, 1373, 16384⟩
    (by decide) selected_cut_10456

theorem selected_cut_10457 : selected 8 ⟨284373, by decide⟩
    (prefixPartial 13 100421) = some ⟨13, 2, 0, 284373, 100421, 1765, 16384⟩ := by
  decide +kernel

theorem context_13_100421_284373 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100421 ⟨284373, by decide⟩ :=
  accepted_of_selected 13 100421 ⟨284373, by decide⟩ ⟨13, 2, 0, 284373, 100421, 1765, 16384⟩
    (by decide) selected_cut_10457

theorem selected_cut_10458 : selected 8 ⟨284395, by decide⟩
    (prefixPartial 13 100422) = some ⟨13, 2, 0, 284395, 100422, 1285, 16384⟩ := by
  decide +kernel

theorem context_13_100422_284395 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100422 ⟨284395, by decide⟩ :=
  accepted_of_selected 13 100422 ⟨284395, by decide⟩ ⟨13, 2, 0, 284395, 100422, 1285, 16384⟩
    (by decide) selected_cut_10458

theorem selected_cut_10459 : selected 8 ⟨284402, by decide⟩
    (prefixPartial 13 100423) = some ⟨13, 2, 0, 284402, 100423, 749, 16384⟩ := by
  decide +kernel

theorem context_13_100423_284402 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100423 ⟨284402, by decide⟩ :=
  accepted_of_selected 13 100423 ⟨284402, by decide⟩ ⟨13, 2, 0, 284402, 100423, 749, 16384⟩
    (by decide) selected_cut_10459

theorem unmarked_context_12_25105_284403 : frontier 9 ⟨284403, by decide⟩
    (prefixCache 12 25105) (prefixPartial 12 25105) = false := by
  decide +kernel

theorem node_context_12_25105_284403 : EJMOriginalGlobalDAGData.nodes 9 ⟨284403, by decide⟩ =
    .split (coordinate 12) (![⟨284346, by decide⟩,⟨284373, by decide⟩,⟨284395, by decide⟩,⟨284402, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25105_284403 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25105 ⟨284403, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25105
    ⟨284403, by decide⟩ (by decide) (![⟨284346, by decide⟩,⟨284373, by decide⟩,⟨284395, by decide⟩,⟨284402, by decide⟩]) unmarked_context_12_25105_284403 node_context_12_25105_284403
  intro a
  fin_cases a
  · exact context_13_100420_284346
  · exact context_13_100421_284373
  · exact context_13_100422_284395
  · exact context_13_100423_284402

theorem selected_cut_10460 : selected 8 ⟨284424, by decide⟩
    (prefixPartial 13 100424) = some ⟨13, 2, 0, 284424, 100424, 1357, 16384⟩ := by
  decide +kernel

theorem context_13_100424_284424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100424 ⟨284424, by decide⟩ :=
  accepted_of_selected 13 100424 ⟨284424, by decide⟩ ⟨13, 2, 0, 284424, 100424, 1357, 16384⟩
    (by decide) selected_cut_10460

theorem selected_cut_10461 : selected 8 ⟨284445, by decide⟩
    (prefixPartial 13 100425) = some ⟨13, 2, 0, 284445, 100425, 1533, 16384⟩ := by
  decide +kernel

theorem context_13_100425_284445 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100425 ⟨284445, by decide⟩ :=
  accepted_of_selected 13 100425 ⟨284445, by decide⟩ ⟨13, 2, 0, 284445, 100425, 1533, 16384⟩
    (by decide) selected_cut_10461

theorem selected_cut_10462 : selected 8 ⟨284460, by decide⟩
    (prefixPartial 13 100426) = some ⟨13, 2, 0, 284460, 100426, 1025, 16384⟩ := by
  decide +kernel

theorem context_13_100426_284460 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100426 ⟨284460, by decide⟩ :=
  accepted_of_selected 13 100426 ⟨284460, by decide⟩ ⟨13, 2, 0, 284460, 100426, 1025, 16384⟩
    (by decide) selected_cut_10462

theorem selected_cut_10463 : selected 8 ⟨284468, by decide⟩
    (prefixPartial 13 100427) = some ⟨13, 2, 0, 284468, 100427, 717, 16384⟩ := by
  decide +kernel

theorem context_13_100427_284468 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100427 ⟨284468, by decide⟩ :=
  accepted_of_selected 13 100427 ⟨284468, by decide⟩ ⟨13, 2, 0, 284468, 100427, 717, 16384⟩
    (by decide) selected_cut_10463

theorem unmarked_context_12_25106_284469 : frontier 9 ⟨284469, by decide⟩
    (prefixCache 12 25106) (prefixPartial 12 25106) = false := by
  decide +kernel

theorem node_context_12_25106_284469 : EJMOriginalGlobalDAGData.nodes 9 ⟨284469, by decide⟩ =
    .split (coordinate 12) (![⟨284424, by decide⟩,⟨284445, by decide⟩,⟨284460, by decide⟩,⟨284468, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25106_284469 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25106 ⟨284469, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25106
    ⟨284469, by decide⟩ (by decide) (![⟨284424, by decide⟩,⟨284445, by decide⟩,⟨284460, by decide⟩,⟨284468, by decide⟩]) unmarked_context_12_25106_284469 node_context_12_25106_284469
  intro a
  fin_cases a
  · exact context_13_100424_284424
  · exact context_13_100425_284445
  · exact context_13_100426_284460
  · exact context_13_100427_284468

theorem selected_cut_10464 : selected 8 ⟨284501, by decide⟩
    (prefixPartial 13 100428) = some ⟨13, 2, 0, 284501, 100428, 1913, 16384⟩ := by
  decide +kernel

theorem context_13_100428_284501 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100428 ⟨284501, by decide⟩ :=
  accepted_of_selected 13 100428 ⟨284501, by decide⟩ ⟨13, 2, 0, 284501, 100428, 1913, 16384⟩
    (by decide) selected_cut_10464

theorem selected_cut_10465 : selected 8 ⟨284528, by decide⟩
    (prefixPartial 13 100429) = some ⟨13, 2, 0, 284528, 100429, 1889, 16384⟩ := by
  decide +kernel

theorem context_13_100429_284528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100429 ⟨284528, by decide⟩ :=
  accepted_of_selected 13 100429 ⟨284528, by decide⟩ ⟨13, 2, 0, 284528, 100429, 1889, 16384⟩
    (by decide) selected_cut_10465

theorem selected_cut_10466 : selected 8 ⟨284545, by decide⟩
    (prefixPartial 13 100430) = some ⟨13, 2, 0, 284545, 100430, 1309, 16384⟩ := by
  decide +kernel

theorem context_13_100430_284545 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 100430 ⟨284545, by decide⟩ :=
  accepted_of_selected 13 100430 ⟨284545, by decide⟩ ⟨13, 2, 0, 284545, 100430, 1309, 16384⟩
    (by decide) selected_cut_10466

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
