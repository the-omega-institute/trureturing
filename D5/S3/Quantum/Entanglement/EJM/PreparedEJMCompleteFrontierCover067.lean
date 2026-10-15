/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover066
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_06434 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 21575) = some ⟨12, 1, 0, 893, 21575, 1, 65536⟩ := by
  decide +kernel

theorem context_12_21575_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21575 ⟨893, by decide⟩ :=
  accepted_of_selected 12 21575 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 21575, 1, 65536⟩
    (by decide) selected_cut_06434

theorem unmarked_context_11_5393_192613 : frontier 10 ⟨192613, by decide⟩
    (prefixCache 11 5393) (prefixPartial 11 5393) = false := by
  decide +kernel

theorem node_context_11_5393_192613 : EJMOriginalGlobalDAGData.nodes 10 ⟨192613, by decide⟩ =
    .split (coordinate 11) (![⟨192456, by decide⟩,⟨192544, by decide⟩,⟨192612, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5393_192613 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5393 ⟨192613, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5393
    ⟨192613, by decide⟩ (by decide) (![⟨192456, by decide⟩,⟨192544, by decide⟩,⟨192612, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_5393_192613 node_context_11_5393_192613
  intro a
  fin_cases a
  · exact context_12_21572_192456
  · exact context_12_21573_192544
  · exact context_12_21574_192612
  · exact context_12_21575_893

theorem selected_cut_06435 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 86304) = some ⟨13, 1, 0, 3444, 86304, 1, 16384⟩ := by
  decide +kernel

theorem context_13_86304_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86304 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 86304 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 86304, 1, 16384⟩
    (by decide) selected_cut_06435

theorem selected_cut_06436 : selected 8 ⟨192649, by decide⟩
    (prefixPartial 13 86305) = some ⟨13, 2, 0, 192649, 86305, 2213, 16384⟩ := by
  decide +kernel

theorem context_13_86305_192649 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86305 ⟨192649, by decide⟩ :=
  accepted_of_selected 13 86305 ⟨192649, by decide⟩ ⟨13, 2, 0, 192649, 86305, 2213, 16384⟩
    (by decide) selected_cut_06436

theorem selected_cut_06437 : selected 8 ⟨192670, by decide⟩
    (prefixPartial 13 86306) = some ⟨13, 2, 0, 192670, 86306, 1569, 16384⟩ := by
  decide +kernel

theorem context_13_86306_192670 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86306 ⟨192670, by decide⟩ :=
  accepted_of_selected 13 86306 ⟨192670, by decide⟩ ⟨13, 2, 0, 192670, 86306, 1569, 16384⟩
    (by decide) selected_cut_06437

theorem selected_cut_06438 : selected 8 ⟨192681, by decide⟩
    (prefixPartial 13 86307) = some ⟨13, 2, 0, 192681, 86307, 733, 16384⟩ := by
  decide +kernel

theorem context_13_86307_192681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86307 ⟨192681, by decide⟩ :=
  accepted_of_selected 13 86307 ⟨192681, by decide⟩ ⟨13, 2, 0, 192681, 86307, 733, 16384⟩
    (by decide) selected_cut_06438

theorem unmarked_context_12_21576_192682 : frontier 9 ⟨192682, by decide⟩
    (prefixCache 12 21576) (prefixPartial 12 21576) = false := by
  decide +kernel

theorem node_context_12_21576_192682 : EJMOriginalGlobalDAGData.nodes 9 ⟨192682, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨192649, by decide⟩,⟨192670, by decide⟩,⟨192681, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21576_192682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21576 ⟨192682, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21576
    ⟨192682, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨192649, by decide⟩,⟨192670, by decide⟩,⟨192681, by decide⟩]) unmarked_context_12_21576_192682 node_context_12_21576_192682
  intro a
  fin_cases a
  · exact context_13_86304_3444
  · exact context_13_86305_192649
  · exact context_13_86306_192670
  · exact context_13_86307_192681

theorem selected_cut_06439 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 86308) = some ⟨13, 1, 0, 3444, 86308, 1, 16384⟩ := by
  decide +kernel

theorem context_13_86308_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86308 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 86308 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 86308, 1, 16384⟩
    (by decide) selected_cut_06439

theorem selected_cut_06440 : selected 8 ⟨192733, by decide⟩
    (prefixPartial 13 86309) = some ⟨13, 2, 0, 192733, 86309, 2665, 16384⟩ := by
  decide +kernel

theorem context_13_86309_192733 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86309 ⟨192733, by decide⟩ :=
  accepted_of_selected 13 86309 ⟨192733, by decide⟩ ⟨13, 2, 0, 192733, 86309, 2665, 16384⟩
    (by decide) selected_cut_06440

theorem selected_cut_06441 : selected 8 ⟨192764, by decide⟩
    (prefixPartial 13 86310) = some ⟨13, 2, 0, 192764, 86310, 2101, 16384⟩ := by
  decide +kernel

theorem context_13_86310_192764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86310 ⟨192764, by decide⟩ :=
  accepted_of_selected 13 86310 ⟨192764, by decide⟩ ⟨13, 2, 0, 192764, 86310, 2101, 16384⟩
    (by decide) selected_cut_06441

theorem selected_cut_06442 : selected 8 ⟨192775, by decide⟩
    (prefixPartial 13 86311) = some ⟨13, 2, 0, 192775, 86311, 1077, 16384⟩ := by
  decide +kernel

theorem context_13_86311_192775 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86311 ⟨192775, by decide⟩ :=
  accepted_of_selected 13 86311 ⟨192775, by decide⟩ ⟨13, 2, 0, 192775, 86311, 1077, 16384⟩
    (by decide) selected_cut_06442

theorem unmarked_context_12_21577_192776 : frontier 9 ⟨192776, by decide⟩
    (prefixCache 12 21577) (prefixPartial 12 21577) = false := by
  decide +kernel

theorem node_context_12_21577_192776 : EJMOriginalGlobalDAGData.nodes 9 ⟨192776, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨192733, by decide⟩,⟨192764, by decide⟩,⟨192775, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21577_192776 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21577 ⟨192776, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21577
    ⟨192776, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨192733, by decide⟩,⟨192764, by decide⟩,⟨192775, by decide⟩]) unmarked_context_12_21577_192776 node_context_12_21577_192776
  intro a
  fin_cases a
  · exact context_13_86308_3444
  · exact context_13_86309_192733
  · exact context_13_86310_192764
  · exact context_13_86311_192775

theorem selected_cut_06443 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 86312) = some ⟨13, 1, 0, 3444, 86312, 1, 16384⟩ := by
  decide +kernel

theorem context_13_86312_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86312 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 86312 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 86312, 1, 16384⟩
    (by decide) selected_cut_06443

theorem selected_cut_06444 : selected 8 ⟨192805, by decide⟩
    (prefixPartial 13 86313) = some ⟨13, 2, 0, 192805, 86313, 2045, 16384⟩ := by
  decide +kernel

theorem context_13_86313_192805 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86313 ⟨192805, by decide⟩ :=
  accepted_of_selected 13 86313 ⟨192805, by decide⟩ ⟨13, 2, 0, 192805, 86313, 2045, 16384⟩
    (by decide) selected_cut_06444

theorem selected_cut_06445 : selected 8 ⟨192828, by decide⟩
    (prefixPartial 13 86314) = some ⟨13, 2, 0, 192828, 86314, 1321, 16384⟩ := by
  decide +kernel

theorem context_13_86314_192828 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86314 ⟨192828, by decide⟩ :=
  accepted_of_selected 13 86314 ⟨192828, by decide⟩ ⟨13, 2, 0, 192828, 86314, 1321, 16384⟩
    (by decide) selected_cut_06445

theorem selected_cut_06446 : selected 8 ⟨192837, by decide⟩
    (prefixPartial 13 86315) = some ⟨13, 2, 0, 192837, 86315, 797, 16384⟩ := by
  decide +kernel

theorem context_13_86315_192837 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86315 ⟨192837, by decide⟩ :=
  accepted_of_selected 13 86315 ⟨192837, by decide⟩ ⟨13, 2, 0, 192837, 86315, 797, 16384⟩
    (by decide) selected_cut_06446

theorem unmarked_context_12_21578_192838 : frontier 9 ⟨192838, by decide⟩
    (prefixCache 12 21578) (prefixPartial 12 21578) = false := by
  decide +kernel

theorem node_context_12_21578_192838 : EJMOriginalGlobalDAGData.nodes 9 ⟨192838, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨192805, by decide⟩,⟨192828, by decide⟩,⟨192837, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21578_192838 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21578 ⟨192838, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21578
    ⟨192838, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨192805, by decide⟩,⟨192828, by decide⟩,⟨192837, by decide⟩]) unmarked_context_12_21578_192838 node_context_12_21578_192838
  intro a
  fin_cases a
  · exact context_13_86312_3444
  · exact context_13_86313_192805
  · exact context_13_86314_192828
  · exact context_13_86315_192837

theorem selected_cut_06447 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 86316) = some ⟨13, 1, 0, 3444, 86316, 1, 16384⟩ := by
  decide +kernel

theorem context_13_86316_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86316 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 86316 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 86316, 1, 16384⟩
    (by decide) selected_cut_06447

theorem selected_cut_06448 : selected 8 ⟨192863, by decide⟩
    (prefixPartial 13 86317) = some ⟨13, 2, 0, 192863, 86317, 1881, 16384⟩ := by
  decide +kernel

theorem context_13_86317_192863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86317 ⟨192863, by decide⟩ :=
  accepted_of_selected 13 86317 ⟨192863, by decide⟩ ⟨13, 2, 0, 192863, 86317, 1881, 16384⟩
    (by decide) selected_cut_06448

theorem selected_cut_06449 : selected 8 ⟨192887, by decide⟩
    (prefixPartial 13 86318) = some ⟨13, 2, 0, 192887, 86318, 1513, 16384⟩ := by
  decide +kernel

theorem context_13_86318_192887 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86318 ⟨192887, by decide⟩ :=
  accepted_of_selected 13 86318 ⟨192887, by decide⟩ ⟨13, 2, 0, 192887, 86318, 1513, 16384⟩
    (by decide) selected_cut_06449

theorem selected_cut_06450 : selected 8 ⟨192900, by decide⟩
    (prefixPartial 13 86319) = some ⟨13, 2, 0, 192900, 86319, 841, 16384⟩ := by
  decide +kernel

theorem context_13_86319_192900 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86319 ⟨192900, by decide⟩ :=
  accepted_of_selected 13 86319 ⟨192900, by decide⟩ ⟨13, 2, 0, 192900, 86319, 841, 16384⟩
    (by decide) selected_cut_06450

theorem unmarked_context_12_21579_192901 : frontier 9 ⟨192901, by decide⟩
    (prefixCache 12 21579) (prefixPartial 12 21579) = false := by
  decide +kernel

theorem node_context_12_21579_192901 : EJMOriginalGlobalDAGData.nodes 9 ⟨192901, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨192863, by decide⟩,⟨192887, by decide⟩,⟨192900, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21579_192901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21579 ⟨192901, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21579
    ⟨192901, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨192863, by decide⟩,⟨192887, by decide⟩,⟨192900, by decide⟩]) unmarked_context_12_21579_192901 node_context_12_21579_192901
  intro a
  fin_cases a
  · exact context_13_86316_3444
  · exact context_13_86317_192863
  · exact context_13_86318_192887
  · exact context_13_86319_192900

theorem unmarked_context_11_5394_192902 : frontier 10 ⟨192902, by decide⟩
    (prefixCache 11 5394) (prefixPartial 11 5394) = false := by
  decide +kernel

theorem node_context_11_5394_192902 : EJMOriginalGlobalDAGData.nodes 10 ⟨192902, by decide⟩ =
    .split (coordinate 11) (![⟨192682, by decide⟩,⟨192776, by decide⟩,⟨192838, by decide⟩,⟨192901, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5394_192902 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5394 ⟨192902, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5394
    ⟨192902, by decide⟩ (by decide) (![⟨192682, by decide⟩,⟨192776, by decide⟩,⟨192838, by decide⟩,⟨192901, by decide⟩]) unmarked_context_11_5394_192902 node_context_11_5394_192902
  intro a
  fin_cases a
  · exact context_12_21576_192682
  · exact context_12_21577_192776
  · exact context_12_21578_192838
  · exact context_12_21579_192901

theorem selected_cut_06451 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 5395) = some ⟨11, 1, 0, 1736, 5395, 1, 262144⟩ := by
  decide +kernel

theorem context_11_5395_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5395 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 5395 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 5395, 1, 262144⟩
    (by decide) selected_cut_06451

theorem unmarked_context_10_1348_192903 : frontier 11 ⟨192903, by decide⟩
    (prefixCache 10 1348) (prefixPartial 10 1348) = false := by
  decide +kernel

theorem node_context_10_1348_192903 : EJMOriginalGlobalDAGData.nodes 11 ⟨192903, by decide⟩ =
    .split (coordinate 10) (![⟨192393, by decide⟩,⟨192613, by decide⟩,⟨192902, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1348_192903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1348 ⟨192903, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1348
    ⟨192903, by decide⟩ (by decide) (![⟨192393, by decide⟩,⟨192613, by decide⟩,⟨192902, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_1348_192903 node_context_10_1348_192903
  intro a
  fin_cases a
  · exact context_11_5392_192393
  · exact context_11_5393_192613
  · exact context_11_5394_192902
  · exact context_11_5395_1736

theorem selected_cut_06452 : selected 9 ⟨192986, by decide⟩
    (prefixPartial 12 21584) = some ⟨12, 2, 0, 192986, 21584, 3681, 65536⟩ := by
  decide +kernel

theorem context_12_21584_192986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21584 ⟨192986, by decide⟩ :=
  accepted_of_selected 12 21584 ⟨192986, by decide⟩ ⟨12, 2, 0, 192986, 21584, 3681, 65536⟩
    (by decide) selected_cut_06452

theorem selected_cut_06453 : selected 9 ⟨193043, by decide⟩
    (prefixPartial 12 21585) = some ⟨12, 2, 0, 193043, 21585, 1305, 65536⟩ := by
  decide +kernel

theorem context_12_21585_193043 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21585 ⟨193043, by decide⟩ :=
  accepted_of_selected 12 21585 ⟨193043, by decide⟩ ⟨12, 2, 0, 193043, 21585, 1305, 65536⟩
    (by decide) selected_cut_06453

theorem selected_cut_06454 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 86344) = some ⟨13, 1, 0, 3444, 86344, 1, 16384⟩ := by
  decide +kernel

theorem context_13_86344_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86344 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 86344 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 86344, 1, 16384⟩
    (by decide) selected_cut_06454

theorem selected_cut_06455 : selected 8 ⟨193064, by decide⟩
    (prefixPartial 13 86345) = some ⟨13, 2, 0, 193064, 86345, 1749, 16384⟩ := by
  decide +kernel

theorem context_13_86345_193064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86345 ⟨193064, by decide⟩ :=
  accepted_of_selected 13 86345 ⟨193064, by decide⟩ ⟨13, 2, 0, 193064, 86345, 1749, 16384⟩
    (by decide) selected_cut_06455

theorem selected_cut_06456 : selected 8 ⟨193090, by decide⟩
    (prefixPartial 13 86346) = some ⟨13, 2, 0, 193090, 86346, 1697, 16384⟩ := by
  decide +kernel

theorem context_13_86346_193090 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86346 ⟨193090, by decide⟩ :=
  accepted_of_selected 13 86346 ⟨193090, by decide⟩ ⟨13, 2, 0, 193090, 86346, 1697, 16384⟩
    (by decide) selected_cut_06456

theorem selected_cut_06457 : selected 8 ⟨193102, by decide⟩
    (prefixPartial 13 86347) = some ⟨13, 2, 0, 193102, 86347, 1025, 16384⟩ := by
  decide +kernel

theorem context_13_86347_193102 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86347 ⟨193102, by decide⟩ :=
  accepted_of_selected 13 86347 ⟨193102, by decide⟩ ⟨13, 2, 0, 193102, 86347, 1025, 16384⟩
    (by decide) selected_cut_06457

theorem unmarked_context_12_21586_193103 : frontier 9 ⟨193103, by decide⟩
    (prefixCache 12 21586) (prefixPartial 12 21586) = false := by
  decide +kernel

theorem node_context_12_21586_193103 : EJMOriginalGlobalDAGData.nodes 9 ⟨193103, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨193064, by decide⟩,⟨193090, by decide⟩,⟨193102, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21586_193103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21586 ⟨193103, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21586
    ⟨193103, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨193064, by decide⟩,⟨193090, by decide⟩,⟨193102, by decide⟩]) unmarked_context_12_21586_193103 node_context_12_21586_193103
  intro a
  fin_cases a
  · exact context_13_86344_3444
  · exact context_13_86345_193064
  · exact context_13_86346_193090
  · exact context_13_86347_193102

theorem selected_cut_06458 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 21587) = some ⟨12, 1, 0, 893, 21587, 1, 65536⟩ := by
  decide +kernel

theorem context_12_21587_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21587 ⟨893, by decide⟩ :=
  accepted_of_selected 12 21587 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 21587, 1, 65536⟩
    (by decide) selected_cut_06458

theorem unmarked_context_11_5396_193104 : frontier 10 ⟨193104, by decide⟩
    (prefixCache 11 5396) (prefixPartial 11 5396) = false := by
  decide +kernel

theorem node_context_11_5396_193104 : EJMOriginalGlobalDAGData.nodes 10 ⟨193104, by decide⟩ =
    .split (coordinate 11) (![⟨192986, by decide⟩,⟨193043, by decide⟩,⟨193103, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5396_193104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5396 ⟨193104, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5396
    ⟨193104, by decide⟩ (by decide) (![⟨192986, by decide⟩,⟨193043, by decide⟩,⟨193103, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_5396_193104 node_context_11_5396_193104
  intro a
  fin_cases a
  · exact context_12_21584_192986
  · exact context_12_21585_193043
  · exact context_12_21586_193103
  · exact context_12_21587_893

theorem selected_cut_06459 : selected 9 ⟨193105, by decide⟩
    (prefixPartial 12 21588) = some ⟨12, 1, 0, 193105, 21588, 1, 65536⟩ := by
  decide +kernel

theorem context_12_21588_193105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21588 ⟨193105, by decide⟩ :=
  accepted_of_selected 12 21588 ⟨193105, by decide⟩ ⟨12, 1, 0, 193105, 21588, 1, 65536⟩
    (by decide) selected_cut_06459

theorem selected_cut_06460 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 21589) = some ⟨12, 1, 0, 170504, 21589, 1, 65536⟩ := by
  decide +kernel

theorem context_12_21589_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21589 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 21589 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 21589, 1, 65536⟩
    (by decide) selected_cut_06460

theorem selected_cut_06461 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 86360) = some ⟨13, 1, 0, 3444, 86360, 1, 16384⟩ := by
  decide +kernel

theorem context_13_86360_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86360 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 86360 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 86360, 1, 16384⟩
    (by decide) selected_cut_06461

theorem selected_cut_06462 : selected 8 ⟨193146, by decide⟩
    (prefixPartial 13 86361) = some ⟨13, 2, 0, 193146, 86361, 2637, 16384⟩ := by
  decide +kernel

theorem context_13_86361_193146 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86361 ⟨193146, by decide⟩ :=
  accepted_of_selected 13 86361 ⟨193146, by decide⟩ ⟨13, 2, 0, 193146, 86361, 2637, 16384⟩
    (by decide) selected_cut_06462

theorem selected_cut_06463 : selected 8 ⟨193173, by decide⟩
    (prefixPartial 13 86362) = some ⟨13, 2, 0, 193173, 86362, 2357, 16384⟩ := by
  decide +kernel

theorem context_13_86362_193173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86362 ⟨193173, by decide⟩ :=
  accepted_of_selected 13 86362 ⟨193173, by decide⟩ ⟨13, 2, 0, 193173, 86362, 2357, 16384⟩
    (by decide) selected_cut_06463

theorem selected_cut_06464 : selected 8 ⟨193188, by decide⟩
    (prefixPartial 13 86363) = some ⟨13, 2, 0, 193188, 86363, 1205, 16384⟩ := by
  decide +kernel

theorem context_13_86363_193188 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86363 ⟨193188, by decide⟩ :=
  accepted_of_selected 13 86363 ⟨193188, by decide⟩ ⟨13, 2, 0, 193188, 86363, 1205, 16384⟩
    (by decide) selected_cut_06464

theorem unmarked_context_12_21590_193189 : frontier 9 ⟨193189, by decide⟩
    (prefixCache 12 21590) (prefixPartial 12 21590) = false := by
  decide +kernel

theorem node_context_12_21590_193189 : EJMOriginalGlobalDAGData.nodes 9 ⟨193189, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨193146, by decide⟩,⟨193173, by decide⟩,⟨193188, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21590_193189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21590 ⟨193189, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21590
    ⟨193189, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨193146, by decide⟩,⟨193173, by decide⟩,⟨193188, by decide⟩]) unmarked_context_12_21590_193189 node_context_12_21590_193189
  intro a
  fin_cases a
  · exact context_13_86360_3444
  · exact context_13_86361_193146
  · exact context_13_86362_193173
  · exact context_13_86363_193188

theorem selected_cut_06465 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 21591) = some ⟨12, 1, 0, 893, 21591, 1, 65536⟩ := by
  decide +kernel

theorem context_12_21591_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21591 ⟨893, by decide⟩ :=
  accepted_of_selected 12 21591 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 21591, 1, 65536⟩
    (by decide) selected_cut_06465

theorem unmarked_context_11_5397_193190 : frontier 10 ⟨193190, by decide⟩
    (prefixCache 11 5397) (prefixPartial 11 5397) = false := by
  decide +kernel

theorem node_context_11_5397_193190 : EJMOriginalGlobalDAGData.nodes 10 ⟨193190, by decide⟩ =
    .split (coordinate 11) (![⟨193105, by decide⟩,⟨170504, by decide⟩,⟨193189, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5397_193190 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5397 ⟨193190, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5397
    ⟨193190, by decide⟩ (by decide) (![⟨193105, by decide⟩,⟨170504, by decide⟩,⟨193189, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_5397_193190 node_context_11_5397_193190
  intro a
  fin_cases a
  · exact context_12_21588_193105
  · exact context_12_21589_170504
  · exact context_12_21590_193189
  · exact context_12_21591_893

theorem selected_cut_06466 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 86368) = some ⟨13, 1, 0, 3444, 86368, 1, 16384⟩ := by
  decide +kernel

theorem context_13_86368_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86368 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 86368 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 86368, 1, 16384⟩
    (by decide) selected_cut_06466

theorem selected_cut_06467 : selected 8 ⟨193206, by decide⟩
    (prefixPartial 13 86369) = some ⟨13, 2, 0, 193206, 86369, 1721, 16384⟩ := by
  decide +kernel

theorem context_13_86369_193206 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86369 ⟨193206, by decide⟩ :=
  accepted_of_selected 13 86369 ⟨193206, by decide⟩ ⟨13, 2, 0, 193206, 86369, 1721, 16384⟩
    (by decide) selected_cut_06467

theorem selected_cut_06468 : selected 8 ⟨193225, by decide⟩
    (prefixPartial 13 86370) = some ⟨13, 2, 0, 193225, 86370, 1785, 16384⟩ := by
  decide +kernel

theorem context_13_86370_193225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86370 ⟨193225, by decide⟩ :=
  accepted_of_selected 13 86370 ⟨193225, by decide⟩ ⟨13, 2, 0, 193225, 86370, 1785, 16384⟩
    (by decide) selected_cut_06468

theorem selected_cut_06469 : selected 8 ⟨193236, by decide⟩
    (prefixPartial 13 86371) = some ⟨13, 2, 0, 193236, 86371, 909, 16384⟩ := by
  decide +kernel

theorem context_13_86371_193236 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86371 ⟨193236, by decide⟩ :=
  accepted_of_selected 13 86371 ⟨193236, by decide⟩ ⟨13, 2, 0, 193236, 86371, 909, 16384⟩
    (by decide) selected_cut_06469

theorem unmarked_context_12_21592_193237 : frontier 9 ⟨193237, by decide⟩
    (prefixCache 12 21592) (prefixPartial 12 21592) = false := by
  decide +kernel

theorem node_context_12_21592_193237 : EJMOriginalGlobalDAGData.nodes 9 ⟨193237, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨193206, by decide⟩,⟨193225, by decide⟩,⟨193236, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21592_193237 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21592 ⟨193237, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21592
    ⟨193237, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨193206, by decide⟩,⟨193225, by decide⟩,⟨193236, by decide⟩]) unmarked_context_12_21592_193237 node_context_12_21592_193237
  intro a
  fin_cases a
  · exact context_13_86368_3444
  · exact context_13_86369_193206
  · exact context_13_86370_193225
  · exact context_13_86371_193236

theorem selected_cut_06470 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 86372) = some ⟨13, 1, 0, 3444, 86372, 1, 16384⟩ := by
  decide +kernel

theorem context_13_86372_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86372 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 86372 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 86372, 1, 16384⟩
    (by decide) selected_cut_06470

theorem selected_cut_06471 : selected 8 ⟨193263, by decide⟩
    (prefixPartial 13 86373) = some ⟨13, 2, 0, 193263, 86373, 1841, 16384⟩ := by
  decide +kernel

theorem context_13_86373_193263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86373 ⟨193263, by decide⟩ :=
  accepted_of_selected 13 86373 ⟨193263, by decide⟩ ⟨13, 2, 0, 193263, 86373, 1841, 16384⟩
    (by decide) selected_cut_06471

theorem selected_cut_06472 : selected 8 ⟨193286, by decide⟩
    (prefixPartial 13 86374) = some ⟨13, 2, 0, 193286, 86374, 2413, 16384⟩ := by
  decide +kernel

theorem context_13_86374_193286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86374 ⟨193286, by decide⟩ :=
  accepted_of_selected 13 86374 ⟨193286, by decide⟩ ⟨13, 2, 0, 193286, 86374, 2413, 16384⟩
    (by decide) selected_cut_06472

theorem selected_cut_06473 : selected 8 ⟨193297, by decide⟩
    (prefixPartial 13 86375) = some ⟨13, 2, 0, 193297, 86375, 1249, 16384⟩ := by
  decide +kernel

theorem context_13_86375_193297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86375 ⟨193297, by decide⟩ :=
  accepted_of_selected 13 86375 ⟨193297, by decide⟩ ⟨13, 2, 0, 193297, 86375, 1249, 16384⟩
    (by decide) selected_cut_06473

theorem unmarked_context_12_21593_193298 : frontier 9 ⟨193298, by decide⟩
    (prefixCache 12 21593) (prefixPartial 12 21593) = false := by
  decide +kernel

theorem node_context_12_21593_193298 : EJMOriginalGlobalDAGData.nodes 9 ⟨193298, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨193263, by decide⟩,⟨193286, by decide⟩,⟨193297, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21593_193298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21593 ⟨193298, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21593
    ⟨193298, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨193263, by decide⟩,⟨193286, by decide⟩,⟨193297, by decide⟩]) unmarked_context_12_21593_193298 node_context_12_21593_193298
  intro a
  fin_cases a
  · exact context_13_86372_3444
  · exact context_13_86373_193263
  · exact context_13_86374_193286
  · exact context_13_86375_193297

theorem selected_cut_06474 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 86376) = some ⟨13, 1, 0, 3444, 86376, 1, 16384⟩ := by
  decide +kernel

theorem context_13_86376_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86376 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 86376 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 86376, 1, 16384⟩
    (by decide) selected_cut_06474

theorem selected_cut_06475 : selected 8 ⟨193315, by decide⟩
    (prefixPartial 13 86377) = some ⟨13, 2, 0, 193315, 86377, 1677, 16384⟩ := by
  decide +kernel

theorem context_13_86377_193315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86377 ⟨193315, by decide⟩ :=
  accepted_of_selected 13 86377 ⟨193315, by decide⟩ ⟨13, 2, 0, 193315, 86377, 1677, 16384⟩
    (by decide) selected_cut_06475

theorem selected_cut_06476 : selected 8 ⟨193341, by decide⟩
    (prefixPartial 13 86378) = some ⟨13, 2, 0, 193341, 86378, 1753, 16384⟩ := by
  decide +kernel

theorem context_13_86378_193341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86378 ⟨193341, by decide⟩ :=
  accepted_of_selected 13 86378 ⟨193341, by decide⟩ ⟨13, 2, 0, 193341, 86378, 1753, 16384⟩
    (by decide) selected_cut_06476

theorem selected_cut_06477 : selected 8 ⟨193356, by decide⟩
    (prefixPartial 13 86379) = some ⟨13, 2, 0, 193356, 86379, 1145, 16384⟩ := by
  decide +kernel

theorem context_13_86379_193356 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86379 ⟨193356, by decide⟩ :=
  accepted_of_selected 13 86379 ⟨193356, by decide⟩ ⟨13, 2, 0, 193356, 86379, 1145, 16384⟩
    (by decide) selected_cut_06477

theorem unmarked_context_12_21594_193357 : frontier 9 ⟨193357, by decide⟩
    (prefixCache 12 21594) (prefixPartial 12 21594) = false := by
  decide +kernel

theorem node_context_12_21594_193357 : EJMOriginalGlobalDAGData.nodes 9 ⟨193357, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨193315, by decide⟩,⟨193341, by decide⟩,⟨193356, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21594_193357 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21594 ⟨193357, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21594
    ⟨193357, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨193315, by decide⟩,⟨193341, by decide⟩,⟨193356, by decide⟩]) unmarked_context_12_21594_193357 node_context_12_21594_193357
  intro a
  fin_cases a
  · exact context_13_86376_3444
  · exact context_13_86377_193315
  · exact context_13_86378_193341
  · exact context_13_86379_193356

theorem selected_cut_06478 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 86380) = some ⟨13, 1, 0, 3444, 86380, 1, 16384⟩ := by
  decide +kernel

theorem context_13_86380_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86380 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 86380 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 86380, 1, 16384⟩
    (by decide) selected_cut_06478

theorem selected_cut_06479 : selected 8 ⟨193374, by decide⟩
    (prefixPartial 13 86381) = some ⟨13, 2, 0, 193374, 86381, 1513, 16384⟩ := by
  decide +kernel

theorem context_13_86381_193374 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86381 ⟨193374, by decide⟩ :=
  accepted_of_selected 13 86381 ⟨193374, by decide⟩ ⟨13, 2, 0, 193374, 86381, 1513, 16384⟩
    (by decide) selected_cut_06479

theorem selected_cut_06480 : selected 8 ⟨193400, by decide⟩
    (prefixPartial 13 86382) = some ⟨13, 2, 0, 193400, 86382, 2033, 16384⟩ := by
  decide +kernel

theorem context_13_86382_193400 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86382 ⟨193400, by decide⟩ :=
  accepted_of_selected 13 86382 ⟨193400, by decide⟩ ⟨13, 2, 0, 193400, 86382, 2033, 16384⟩
    (by decide) selected_cut_06480

theorem selected_cut_06481 : selected 8 ⟨193409, by decide⟩
    (prefixPartial 13 86383) = some ⟨13, 2, 0, 193409, 86383, 1069, 16384⟩ := by
  decide +kernel

theorem context_13_86383_193409 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86383 ⟨193409, by decide⟩ :=
  accepted_of_selected 13 86383 ⟨193409, by decide⟩ ⟨13, 2, 0, 193409, 86383, 1069, 16384⟩
    (by decide) selected_cut_06481

theorem unmarked_context_12_21595_193410 : frontier 9 ⟨193410, by decide⟩
    (prefixCache 12 21595) (prefixPartial 12 21595) = false := by
  decide +kernel

theorem node_context_12_21595_193410 : EJMOriginalGlobalDAGData.nodes 9 ⟨193410, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨193374, by decide⟩,⟨193400, by decide⟩,⟨193409, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21595_193410 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21595 ⟨193410, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21595
    ⟨193410, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨193374, by decide⟩,⟨193400, by decide⟩,⟨193409, by decide⟩]) unmarked_context_12_21595_193410 node_context_12_21595_193410
  intro a
  fin_cases a
  · exact context_13_86380_3444
  · exact context_13_86381_193374
  · exact context_13_86382_193400
  · exact context_13_86383_193409

theorem unmarked_context_11_5398_193411 : frontier 10 ⟨193411, by decide⟩
    (prefixCache 11 5398) (prefixPartial 11 5398) = false := by
  decide +kernel

theorem node_context_11_5398_193411 : EJMOriginalGlobalDAGData.nodes 10 ⟨193411, by decide⟩ =
    .split (coordinate 11) (![⟨193237, by decide⟩,⟨193298, by decide⟩,⟨193357, by decide⟩,⟨193410, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5398_193411 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5398 ⟨193411, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5398
    ⟨193411, by decide⟩ (by decide) (![⟨193237, by decide⟩,⟨193298, by decide⟩,⟨193357, by decide⟩,⟨193410, by decide⟩]) unmarked_context_11_5398_193411 node_context_11_5398_193411
  intro a
  fin_cases a
  · exact context_12_21592_193237
  · exact context_12_21593_193298
  · exact context_12_21594_193357
  · exact context_12_21595_193410

theorem selected_cut_06482 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 5399) = some ⟨11, 1, 0, 1736, 5399, 1, 262144⟩ := by
  decide +kernel

theorem context_11_5399_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5399 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 5399 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 5399, 1, 262144⟩
    (by decide) selected_cut_06482

theorem unmarked_context_10_1349_193412 : frontier 11 ⟨193412, by decide⟩
    (prefixCache 10 1349) (prefixPartial 10 1349) = false := by
  decide +kernel

theorem node_context_10_1349_193412 : EJMOriginalGlobalDAGData.nodes 11 ⟨193412, by decide⟩ =
    .split (coordinate 10) (![⟨193104, by decide⟩,⟨193190, by decide⟩,⟨193411, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1349_193412 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1349 ⟨193412, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1349
    ⟨193412, by decide⟩ (by decide) (![⟨193104, by decide⟩,⟨193190, by decide⟩,⟨193411, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_1349_193412 node_context_10_1349_193412
  intro a
  fin_cases a
  · exact context_11_5396_193104
  · exact context_11_5397_193190
  · exact context_11_5398_193411
  · exact context_11_5399_1736

theorem selected_cut_06483 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 86400) = some ⟨13, 1, 0, 3444, 86400, 1, 16384⟩ := by
  decide +kernel

theorem context_13_86400_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86400 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 86400 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 86400, 1, 16384⟩
    (by decide) selected_cut_06483

theorem selected_cut_06484 : selected 8 ⟨193458, by decide⟩
    (prefixPartial 13 86401) = some ⟨13, 2, 0, 193458, 86401, 2261, 16384⟩ := by
  decide +kernel

theorem context_13_86401_193458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86401 ⟨193458, by decide⟩ :=
  accepted_of_selected 13 86401 ⟨193458, by decide⟩ ⟨13, 2, 0, 193458, 86401, 2261, 16384⟩
    (by decide) selected_cut_06484

theorem selected_cut_06485 : selected 8 ⟨193507, by decide⟩
    (prefixPartial 13 86402) = some ⟨13, 2, 0, 193507, 86402, 2577, 16384⟩ := by
  decide +kernel

theorem context_13_86402_193507 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86402 ⟨193507, by decide⟩ :=
  accepted_of_selected 13 86402 ⟨193507, by decide⟩ ⟨13, 2, 0, 193507, 86402, 2577, 16384⟩
    (by decide) selected_cut_06485

theorem selected_cut_06486 : selected 8 ⟨193539, by decide⟩
    (prefixPartial 13 86403) = some ⟨13, 2, 0, 193539, 86403, 1409, 16384⟩ := by
  decide +kernel

theorem context_13_86403_193539 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86403 ⟨193539, by decide⟩ :=
  accepted_of_selected 13 86403 ⟨193539, by decide⟩ ⟨13, 2, 0, 193539, 86403, 1409, 16384⟩
    (by decide) selected_cut_06486

theorem unmarked_context_12_21600_193540 : frontier 9 ⟨193540, by decide⟩
    (prefixCache 12 21600) (prefixPartial 12 21600) = false := by
  decide +kernel

theorem node_context_12_21600_193540 : EJMOriginalGlobalDAGData.nodes 9 ⟨193540, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨193458, by decide⟩,⟨193507, by decide⟩,⟨193539, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21600_193540 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21600 ⟨193540, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21600
    ⟨193540, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨193458, by decide⟩,⟨193507, by decide⟩,⟨193539, by decide⟩]) unmarked_context_12_21600_193540 node_context_12_21600_193540
  intro a
  fin_cases a
  · exact context_13_86400_3444
  · exact context_13_86401_193458
  · exact context_13_86402_193507
  · exact context_13_86403_193539

theorem selected_cut_06487 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 86404) = some ⟨13, 1, 0, 3444, 86404, 1, 16384⟩ := by
  decide +kernel

theorem context_13_86404_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86404 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 86404 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 86404, 1, 16384⟩
    (by decide) selected_cut_06487

theorem selected_cut_06488 : selected 8 ⟨193571, by decide⟩
    (prefixPartial 13 86405) = some ⟨13, 2, 0, 193571, 86405, 1541, 16384⟩ := by
  decide +kernel

theorem context_13_86405_193571 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86405 ⟨193571, by decide⟩ :=
  accepted_of_selected 13 86405 ⟨193571, by decide⟩ ⟨13, 2, 0, 193571, 86405, 1541, 16384⟩
    (by decide) selected_cut_06488

theorem selected_cut_06489 : selected 8 ⟨193593, by decide⟩
    (prefixPartial 13 86406) = some ⟨13, 2, 0, 193593, 86406, 1881, 16384⟩ := by
  decide +kernel

theorem context_13_86406_193593 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86406 ⟨193593, by decide⟩ :=
  accepted_of_selected 13 86406 ⟨193593, by decide⟩ ⟨13, 2, 0, 193593, 86406, 1881, 16384⟩
    (by decide) selected_cut_06489

theorem selected_cut_06490 : selected 8 ⟨193606, by decide⟩
    (prefixPartial 13 86407) = some ⟨13, 2, 0, 193606, 86407, 1305, 16384⟩ := by
  decide +kernel

theorem context_13_86407_193606 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86407 ⟨193606, by decide⟩ :=
  accepted_of_selected 13 86407 ⟨193606, by decide⟩ ⟨13, 2, 0, 193606, 86407, 1305, 16384⟩
    (by decide) selected_cut_06490

theorem unmarked_context_12_21601_193607 : frontier 9 ⟨193607, by decide⟩
    (prefixCache 12 21601) (prefixPartial 12 21601) = false := by
  decide +kernel

theorem node_context_12_21601_193607 : EJMOriginalGlobalDAGData.nodes 9 ⟨193607, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨193571, by decide⟩,⟨193593, by decide⟩,⟨193606, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21601_193607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21601 ⟨193607, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21601
    ⟨193607, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨193571, by decide⟩,⟨193593, by decide⟩,⟨193606, by decide⟩]) unmarked_context_12_21601_193607 node_context_12_21601_193607
  intro a
  fin_cases a
  · exact context_13_86404_3444
  · exact context_13_86405_193571
  · exact context_13_86406_193593
  · exact context_13_86407_193606

theorem selected_cut_06491 : selected 9 ⟨193658, by decide⟩
    (prefixPartial 12 21602) = some ⟨12, 2, 0, 193658, 21602, 3745, 65536⟩ := by
  decide +kernel

theorem context_12_21602_193658 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21602 ⟨193658, by decide⟩ :=
  accepted_of_selected 12 21602 ⟨193658, by decide⟩ ⟨12, 2, 0, 193658, 21602, 3745, 65536⟩
    (by decide) selected_cut_06491

theorem selected_cut_06492 : selected 9 ⟨193703, by decide⟩
    (prefixPartial 12 21603) = some ⟨12, 2, 0, 193703, 21603, 3401, 65536⟩ := by
  decide +kernel

theorem context_12_21603_193703 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21603 ⟨193703, by decide⟩ :=
  accepted_of_selected 12 21603 ⟨193703, by decide⟩ ⟨12, 2, 0, 193703, 21603, 3401, 65536⟩
    (by decide) selected_cut_06492

theorem unmarked_context_11_5400_193704 : frontier 10 ⟨193704, by decide⟩
    (prefixCache 11 5400) (prefixPartial 11 5400) = false := by
  decide +kernel

theorem node_context_11_5400_193704 : EJMOriginalGlobalDAGData.nodes 10 ⟨193704, by decide⟩ =
    .split (coordinate 11) (![⟨193540, by decide⟩,⟨193607, by decide⟩,⟨193658, by decide⟩,⟨193703, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5400_193704 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5400 ⟨193704, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5400
    ⟨193704, by decide⟩ (by decide) (![⟨193540, by decide⟩,⟨193607, by decide⟩,⟨193658, by decide⟩,⟨193703, by decide⟩]) unmarked_context_11_5400_193704 node_context_11_5400_193704
  intro a
  fin_cases a
  · exact context_12_21600_193540
  · exact context_12_21601_193607
  · exact context_12_21602_193658
  · exact context_12_21603_193703

theorem selected_cut_06493 : selected 9 ⟨193758, by decide⟩
    (prefixPartial 12 21604) = some ⟨12, 2, 0, 193758, 21604, 3537, 65536⟩ := by
  decide +kernel

theorem context_12_21604_193758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21604 ⟨193758, by decide⟩ :=
  accepted_of_selected 12 21604 ⟨193758, by decide⟩ ⟨12, 2, 0, 193758, 21604, 3537, 65536⟩
    (by decide) selected_cut_06493

theorem selected_cut_06494 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 86420) = some ⟨13, 1, 0, 3444, 86420, 1, 16384⟩ := by
  decide +kernel

theorem context_13_86420_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86420 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 86420 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 86420, 1, 16384⟩
    (by decide) selected_cut_06494

theorem selected_cut_06495 : selected 8 ⟨193779, by decide⟩
    (prefixPartial 13 86421) = some ⟨13, 2, 0, 193779, 86421, 1089, 16384⟩ := by
  decide +kernel

theorem context_13_86421_193779 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86421 ⟨193779, by decide⟩ :=
  accepted_of_selected 13 86421 ⟨193779, by decide⟩ ⟨13, 2, 0, 193779, 86421, 1089, 16384⟩
    (by decide) selected_cut_06495

theorem selected_cut_06496 : selected 8 ⟨193805, by decide⟩
    (prefixPartial 13 86422) = some ⟨13, 2, 0, 193805, 86422, 2001, 16384⟩ := by
  decide +kernel

theorem context_13_86422_193805 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86422 ⟨193805, by decide⟩ :=
  accepted_of_selected 13 86422 ⟨193805, by decide⟩ ⟨13, 2, 0, 193805, 86422, 2001, 16384⟩
    (by decide) selected_cut_06496

theorem selected_cut_06497 : selected 8 ⟨193821, by decide⟩
    (prefixPartial 13 86423) = some ⟨13, 2, 0, 193821, 86423, 1193, 16384⟩ := by
  decide +kernel

theorem context_13_86423_193821 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86423 ⟨193821, by decide⟩ :=
  accepted_of_selected 13 86423 ⟨193821, by decide⟩ ⟨13, 2, 0, 193821, 86423, 1193, 16384⟩
    (by decide) selected_cut_06497

theorem unmarked_context_12_21605_193822 : frontier 9 ⟨193822, by decide⟩
    (prefixCache 12 21605) (prefixPartial 12 21605) = false := by
  decide +kernel

theorem node_context_12_21605_193822 : EJMOriginalGlobalDAGData.nodes 9 ⟨193822, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨193779, by decide⟩,⟨193805, by decide⟩,⟨193821, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21605_193822 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21605 ⟨193822, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21605
    ⟨193822, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨193779, by decide⟩,⟨193805, by decide⟩,⟨193821, by decide⟩]) unmarked_context_12_21605_193822 node_context_12_21605_193822
  intro a
  fin_cases a
  · exact context_13_86420_3444
  · exact context_13_86421_193779
  · exact context_13_86422_193805
  · exact context_13_86423_193821

theorem selected_cut_06498 : selected 9 ⟨193869, by decide⟩
    (prefixPartial 12 21606) = some ⟨12, 2, 0, 193869, 21606, 3573, 65536⟩ := by
  decide +kernel

theorem context_12_21606_193869 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21606 ⟨193869, by decide⟩ :=
  accepted_of_selected 12 21606 ⟨193869, by decide⟩ ⟨12, 2, 0, 193869, 21606, 3573, 65536⟩
    (by decide) selected_cut_06498

theorem selected_cut_06499 : selected 9 ⟨193908, by decide⟩
    (prefixPartial 12 21607) = some ⟨12, 2, 0, 193908, 21607, 3193, 65536⟩ := by
  decide +kernel

theorem context_12_21607_193908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21607 ⟨193908, by decide⟩ :=
  accepted_of_selected 12 21607 ⟨193908, by decide⟩ ⟨12, 2, 0, 193908, 21607, 3193, 65536⟩
    (by decide) selected_cut_06499

theorem unmarked_context_11_5401_193909 : frontier 10 ⟨193909, by decide⟩
    (prefixCache 11 5401) (prefixPartial 11 5401) = false := by
  decide +kernel

theorem node_context_11_5401_193909 : EJMOriginalGlobalDAGData.nodes 10 ⟨193909, by decide⟩ =
    .split (coordinate 11) (![⟨193758, by decide⟩,⟨193822, by decide⟩,⟨193869, by decide⟩,⟨193908, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5401_193909 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5401 ⟨193909, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5401
    ⟨193909, by decide⟩ (by decide) (![⟨193758, by decide⟩,⟨193822, by decide⟩,⟨193869, by decide⟩,⟨193908, by decide⟩]) unmarked_context_11_5401_193909 node_context_11_5401_193909
  intro a
  fin_cases a
  · exact context_12_21604_193758
  · exact context_12_21605_193822
  · exact context_12_21606_193869
  · exact context_12_21607_193908

theorem selected_cut_06500 : selected 9 ⟨193953, by decide⟩
    (prefixPartial 12 21608) = some ⟨12, 2, 0, 193953, 21608, 3509, 65536⟩ := by
  decide +kernel

theorem context_12_21608_193953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21608 ⟨193953, by decide⟩ :=
  accepted_of_selected 12 21608 ⟨193953, by decide⟩ ⟨12, 2, 0, 193953, 21608, 3509, 65536⟩
    (by decide) selected_cut_06500

theorem selected_cut_06501 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 86436) = some ⟨13, 1, 0, 3444, 86436, 1, 16384⟩ := by
  decide +kernel

theorem context_13_86436_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86436 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 86436 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 86436, 1, 16384⟩
    (by decide) selected_cut_06501

theorem selected_cut_06502 : selected 8 ⟨193966, by decide⟩
    (prefixPartial 13 86437) = some ⟨13, 2, 0, 193966, 86437, 809, 16384⟩ := by
  decide +kernel

theorem context_13_86437_193966 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86437 ⟨193966, by decide⟩ :=
  accepted_of_selected 13 86437 ⟨193966, by decide⟩ ⟨13, 2, 0, 193966, 86437, 809, 16384⟩
    (by decide) selected_cut_06502

theorem selected_cut_06503 : selected 8 ⟨193988, by decide⟩
    (prefixPartial 13 86438) = some ⟨13, 2, 0, 193988, 86438, 2277, 16384⟩ := by
  decide +kernel

theorem context_13_86438_193988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86438 ⟨193988, by decide⟩ :=
  accepted_of_selected 13 86438 ⟨193988, by decide⟩ ⟨13, 2, 0, 193988, 86438, 2277, 16384⟩
    (by decide) selected_cut_06503

theorem selected_cut_06504 : selected 8 ⟨194000, by decide⟩
    (prefixPartial 13 86439) = some ⟨13, 2, 0, 194000, 86439, 1333, 16384⟩ := by
  decide +kernel

theorem context_13_86439_194000 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 86439 ⟨194000, by decide⟩ :=
  accepted_of_selected 13 86439 ⟨194000, by decide⟩ ⟨13, 2, 0, 194000, 86439, 1333, 16384⟩
    (by decide) selected_cut_06504

theorem unmarked_context_12_21609_194001 : frontier 9 ⟨194001, by decide⟩
    (prefixCache 12 21609) (prefixPartial 12 21609) = false := by
  decide +kernel

theorem node_context_12_21609_194001 : EJMOriginalGlobalDAGData.nodes 9 ⟨194001, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨193966, by decide⟩,⟨193988, by decide⟩,⟨194000, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_21609_194001 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21609 ⟨194001, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 21609
    ⟨194001, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨193966, by decide⟩,⟨193988, by decide⟩,⟨194000, by decide⟩]) unmarked_context_12_21609_194001 node_context_12_21609_194001
  intro a
  fin_cases a
  · exact context_13_86436_3444
  · exact context_13_86437_193966
  · exact context_13_86438_193988
  · exact context_13_86439_194000

theorem selected_cut_06505 : selected 9 ⟨194039, by decide⟩
    (prefixPartial 12 21610) = some ⟨12, 2, 0, 194039, 21610, 3289, 65536⟩ := by
  decide +kernel

theorem context_12_21610_194039 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21610 ⟨194039, by decide⟩ :=
  accepted_of_selected 12 21610 ⟨194039, by decide⟩ ⟨12, 2, 0, 194039, 21610, 3289, 65536⟩
    (by decide) selected_cut_06505

theorem selected_cut_06506 : selected 9 ⟨194078, by decide⟩
    (prefixPartial 12 21611) = some ⟨12, 2, 0, 194078, 21611, 3321, 65536⟩ := by
  decide +kernel

theorem context_12_21611_194078 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21611 ⟨194078, by decide⟩ :=
  accepted_of_selected 12 21611 ⟨194078, by decide⟩ ⟨12, 2, 0, 194078, 21611, 3321, 65536⟩
    (by decide) selected_cut_06506

theorem unmarked_context_11_5402_194079 : frontier 10 ⟨194079, by decide⟩
    (prefixCache 11 5402) (prefixPartial 11 5402) = false := by
  decide +kernel

theorem node_context_11_5402_194079 : EJMOriginalGlobalDAGData.nodes 10 ⟨194079, by decide⟩ =
    .split (coordinate 11) (![⟨193953, by decide⟩,⟨194001, by decide⟩,⟨194039, by decide⟩,⟨194078, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5402_194079 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5402 ⟨194079, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5402
    ⟨194079, by decide⟩ (by decide) (![⟨193953, by decide⟩,⟨194001, by decide⟩,⟨194039, by decide⟩,⟨194078, by decide⟩]) unmarked_context_11_5402_194079 node_context_11_5402_194079
  intro a
  fin_cases a
  · exact context_12_21608_193953
  · exact context_12_21609_194001
  · exact context_12_21610_194039
  · exact context_12_21611_194078

theorem selected_cut_06507 : selected 9 ⟨194118, by decide⟩
    (prefixPartial 12 21612) = some ⟨12, 2, 0, 194118, 21612, 2901, 65536⟩ := by
  decide +kernel

theorem context_12_21612_194118 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21612 ⟨194118, by decide⟩ :=
  accepted_of_selected 12 21612 ⟨194118, by decide⟩ ⟨12, 2, 0, 194118, 21612, 2901, 65536⟩
    (by decide) selected_cut_06507

theorem selected_cut_06508 : selected 9 ⟨194169, by decide⟩
    (prefixPartial 12 21613) = some ⟨12, 2, 0, 194169, 21613, 3869, 65536⟩ := by
  decide +kernel

theorem context_12_21613_194169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21613 ⟨194169, by decide⟩ :=
  accepted_of_selected 12 21613 ⟨194169, by decide⟩ ⟨12, 2, 0, 194169, 21613, 3869, 65536⟩
    (by decide) selected_cut_06508

theorem selected_cut_06509 : selected 9 ⟨194211, by decide⟩
    (prefixPartial 12 21614) = some ⟨12, 2, 0, 194211, 21614, 2949, 65536⟩ := by
  decide +kernel

theorem context_12_21614_194211 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21614 ⟨194211, by decide⟩ :=
  accepted_of_selected 12 21614 ⟨194211, by decide⟩ ⟨12, 2, 0, 194211, 21614, 2949, 65536⟩
    (by decide) selected_cut_06509

theorem selected_cut_06510 : selected 9 ⟨194248, by decide⟩
    (prefixPartial 12 21615) = some ⟨12, 2, 0, 194248, 21615, 2457, 65536⟩ := by
  decide +kernel

theorem context_12_21615_194248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21615 ⟨194248, by decide⟩ :=
  accepted_of_selected 12 21615 ⟨194248, by decide⟩ ⟨12, 2, 0, 194248, 21615, 2457, 65536⟩
    (by decide) selected_cut_06510

theorem unmarked_context_11_5403_194249 : frontier 10 ⟨194249, by decide⟩
    (prefixCache 11 5403) (prefixPartial 11 5403) = false := by
  decide +kernel

theorem node_context_11_5403_194249 : EJMOriginalGlobalDAGData.nodes 10 ⟨194249, by decide⟩ =
    .split (coordinate 11) (![⟨194118, by decide⟩,⟨194169, by decide⟩,⟨194211, by decide⟩,⟨194248, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5403_194249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5403 ⟨194249, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5403
    ⟨194249, by decide⟩ (by decide) (![⟨194118, by decide⟩,⟨194169, by decide⟩,⟨194211, by decide⟩,⟨194248, by decide⟩]) unmarked_context_11_5403_194249 node_context_11_5403_194249
  intro a
  fin_cases a
  · exact context_12_21612_194118
  · exact context_12_21613_194169
  · exact context_12_21614_194211
  · exact context_12_21615_194248

theorem unmarked_context_10_1350_194250 : frontier 11 ⟨194250, by decide⟩
    (prefixCache 10 1350) (prefixPartial 10 1350) = false := by
  decide +kernel

theorem node_context_10_1350_194250 : EJMOriginalGlobalDAGData.nodes 11 ⟨194250, by decide⟩ =
    .split (coordinate 10) (![⟨193704, by decide⟩,⟨193909, by decide⟩,⟨194079, by decide⟩,⟨194249, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1350_194250 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1350 ⟨194250, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1350
    ⟨194250, by decide⟩ (by decide) (![⟨193704, by decide⟩,⟨193909, by decide⟩,⟨194079, by decide⟩,⟨194249, by decide⟩]) unmarked_context_10_1350_194250 node_context_10_1350_194250
  intro a
  fin_cases a
  · exact context_11_5400_193704
  · exact context_11_5401_193909
  · exact context_11_5402_194079
  · exact context_11_5403_194249

theorem selected_cut_06511 : selected 11 ⟨3440, by decide⟩
    (prefixPartial 10 1351) = some ⟨10, 1, 0, 3440, 1351, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_1351_3440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1351 ⟨3440, by decide⟩ :=
  accepted_of_selected 10 1351 ⟨3440, by decide⟩ ⟨10, 1, 0, 3440, 1351, 1, 1048576⟩
    (by decide) selected_cut_06511

theorem unmarked_context_9_337_194251 : frontier 12 ⟨194251, by decide⟩
    (prefixCache 9 337) (prefixPartial 9 337) = false := by
  decide +kernel

theorem node_context_9_337_194251 : EJMOriginalGlobalDAGData.nodes 12 ⟨194251, by decide⟩ =
    .split (coordinate 9) (![⟨192903, by decide⟩,⟨193412, by decide⟩,⟨194250, by decide⟩,⟨3440, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_337_194251 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 337 ⟨194251, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 337
    ⟨194251, by decide⟩ (by decide) (![⟨192903, by decide⟩,⟨193412, by decide⟩,⟨194250, by decide⟩,⟨3440, by decide⟩]) unmarked_context_9_337_194251 node_context_9_337_194251
  intro a
  fin_cases a
  · exact context_10_1348_192903
  · exact context_10_1349_193412
  · exact context_10_1350_194250
  · exact context_10_1351_3440

theorem selected_cut_06512 : selected 9 ⟨194297, by decide⟩
    (prefixPartial 12 21632) = some ⟨12, 2, 0, 194297, 21632, 3705, 65536⟩ := by
  decide +kernel

theorem context_12_21632_194297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21632 ⟨194297, by decide⟩ :=
  accepted_of_selected 12 21632 ⟨194297, by decide⟩ ⟨12, 2, 0, 194297, 21632, 3705, 65536⟩
    (by decide) selected_cut_06512

theorem selected_cut_06513 : selected 9 ⟨194327, by decide⟩
    (prefixPartial 12 21633) = some ⟨12, 2, 0, 194327, 21633, 2105, 65536⟩ := by
  decide +kernel

theorem context_12_21633_194327 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21633 ⟨194327, by decide⟩ :=
  accepted_of_selected 12 21633 ⟨194327, by decide⟩ ⟨12, 2, 0, 194327, 21633, 2105, 65536⟩
    (by decide) selected_cut_06513

theorem selected_cut_06514 : selected 9 ⟨194362, by decide⟩
    (prefixPartial 12 21634) = some ⟨12, 2, 0, 194362, 21634, 2077, 65536⟩ := by
  decide +kernel

theorem context_12_21634_194362 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21634 ⟨194362, by decide⟩ :=
  accepted_of_selected 12 21634 ⟨194362, by decide⟩ ⟨12, 2, 0, 194362, 21634, 2077, 65536⟩
    (by decide) selected_cut_06514

theorem selected_cut_06515 : selected 9 ⟨194400, by decide⟩
    (prefixPartial 12 21635) = some ⟨12, 2, 0, 194400, 21635, 2233, 65536⟩ := by
  decide +kernel

theorem context_12_21635_194400 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21635 ⟨194400, by decide⟩ :=
  accepted_of_selected 12 21635 ⟨194400, by decide⟩ ⟨12, 2, 0, 194400, 21635, 2233, 65536⟩
    (by decide) selected_cut_06515

theorem unmarked_context_11_5408_194401 : frontier 10 ⟨194401, by decide⟩
    (prefixCache 11 5408) (prefixPartial 11 5408) = false := by
  decide +kernel

theorem node_context_11_5408_194401 : EJMOriginalGlobalDAGData.nodes 10 ⟨194401, by decide⟩ =
    .split (coordinate 11) (![⟨194297, by decide⟩,⟨194327, by decide⟩,⟨194362, by decide⟩,⟨194400, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5408_194401 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5408 ⟨194401, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5408
    ⟨194401, by decide⟩ (by decide) (![⟨194297, by decide⟩,⟨194327, by decide⟩,⟨194362, by decide⟩,⟨194400, by decide⟩]) unmarked_context_11_5408_194401 node_context_11_5408_194401
  intro a
  fin_cases a
  · exact context_12_21632_194297
  · exact context_12_21633_194327
  · exact context_12_21634_194362
  · exact context_12_21635_194400

theorem selected_cut_06516 : selected 9 ⟨194444, by decide⟩
    (prefixPartial 12 21636) = some ⟨12, 2, 0, 194444, 21636, 2365, 65536⟩ := by
  decide +kernel

theorem context_12_21636_194444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21636 ⟨194444, by decide⟩ :=
  accepted_of_selected 12 21636 ⟨194444, by decide⟩ ⟨12, 2, 0, 194444, 21636, 2365, 65536⟩
    (by decide) selected_cut_06516

theorem selected_cut_06517 : selected 9 ⟨194475, by decide⟩
    (prefixPartial 12 21637) = some ⟨12, 2, 0, 194475, 21637, 2009, 65536⟩ := by
  decide +kernel

theorem context_12_21637_194475 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21637 ⟨194475, by decide⟩ :=
  accepted_of_selected 12 21637 ⟨194475, by decide⟩ ⟨12, 2, 0, 194475, 21637, 2009, 65536⟩
    (by decide) selected_cut_06517

theorem selected_cut_06518 : selected 9 ⟨194512, by decide⟩
    (prefixPartial 12 21638) = some ⟨12, 2, 0, 194512, 21638, 2101, 65536⟩ := by
  decide +kernel

theorem context_12_21638_194512 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21638 ⟨194512, by decide⟩ :=
  accepted_of_selected 12 21638 ⟨194512, by decide⟩ ⟨12, 2, 0, 194512, 21638, 2101, 65536⟩
    (by decide) selected_cut_06518

theorem selected_cut_06519 : selected 9 ⟨194550, by decide⟩
    (prefixPartial 12 21639) = some ⟨12, 2, 0, 194550, 21639, 2141, 65536⟩ := by
  decide +kernel

theorem context_12_21639_194550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21639 ⟨194550, by decide⟩ :=
  accepted_of_selected 12 21639 ⟨194550, by decide⟩ ⟨12, 2, 0, 194550, 21639, 2141, 65536⟩
    (by decide) selected_cut_06519

theorem unmarked_context_11_5409_194551 : frontier 10 ⟨194551, by decide⟩
    (prefixCache 11 5409) (prefixPartial 11 5409) = false := by
  decide +kernel

theorem node_context_11_5409_194551 : EJMOriginalGlobalDAGData.nodes 10 ⟨194551, by decide⟩ =
    .split (coordinate 11) (![⟨194444, by decide⟩,⟨194475, by decide⟩,⟨194512, by decide⟩,⟨194550, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5409_194551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5409 ⟨194551, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5409
    ⟨194551, by decide⟩ (by decide) (![⟨194444, by decide⟩,⟨194475, by decide⟩,⟨194512, by decide⟩,⟨194550, by decide⟩]) unmarked_context_11_5409_194551 node_context_11_5409_194551
  intro a
  fin_cases a
  · exact context_12_21636_194444
  · exact context_12_21637_194475
  · exact context_12_21638_194512
  · exact context_12_21639_194550

theorem selected_cut_06520 : selected 9 ⟨194586, by decide⟩
    (prefixPartial 12 21640) = some ⟨12, 2, 0, 194586, 21640, 2157, 65536⟩ := by
  decide +kernel

theorem context_12_21640_194586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21640 ⟨194586, by decide⟩ :=
  accepted_of_selected 12 21640 ⟨194586, by decide⟩ ⟨12, 2, 0, 194586, 21640, 2157, 65536⟩
    (by decide) selected_cut_06520

theorem selected_cut_06521 : selected 9 ⟨194615, by decide⟩
    (prefixPartial 12 21641) = some ⟨12, 2, 0, 194615, 21641, 1881, 65536⟩ := by
  decide +kernel

theorem context_12_21641_194615 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21641 ⟨194615, by decide⟩ :=
  accepted_of_selected 12 21641 ⟨194615, by decide⟩ ⟨12, 2, 0, 194615, 21641, 1881, 65536⟩
    (by decide) selected_cut_06521

theorem selected_cut_06522 : selected 9 ⟨194643, by decide⟩
    (prefixPartial 12 21642) = some ⟨12, 2, 0, 194643, 21642, 1793, 65536⟩ := by
  decide +kernel

theorem context_12_21642_194643 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21642 ⟨194643, by decide⟩ :=
  accepted_of_selected 12 21642 ⟨194643, by decide⟩ ⟨12, 2, 0, 194643, 21642, 1793, 65536⟩
    (by decide) selected_cut_06522

theorem selected_cut_06523 : selected 9 ⟨194672, by decide⟩
    (prefixPartial 12 21643) = some ⟨12, 2, 0, 194672, 21643, 1965, 65536⟩ := by
  decide +kernel

theorem context_12_21643_194672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21643 ⟨194672, by decide⟩ :=
  accepted_of_selected 12 21643 ⟨194672, by decide⟩ ⟨12, 2, 0, 194672, 21643, 1965, 65536⟩
    (by decide) selected_cut_06523

theorem unmarked_context_11_5410_194673 : frontier 10 ⟨194673, by decide⟩
    (prefixCache 11 5410) (prefixPartial 11 5410) = false := by
  decide +kernel

theorem node_context_11_5410_194673 : EJMOriginalGlobalDAGData.nodes 10 ⟨194673, by decide⟩ =
    .split (coordinate 11) (![⟨194586, by decide⟩,⟨194615, by decide⟩,⟨194643, by decide⟩,⟨194672, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5410_194673 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5410 ⟨194673, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5410
    ⟨194673, by decide⟩ (by decide) (![⟨194586, by decide⟩,⟨194615, by decide⟩,⟨194643, by decide⟩,⟨194672, by decide⟩]) unmarked_context_11_5410_194673 node_context_11_5410_194673
  intro a
  fin_cases a
  · exact context_12_21640_194586
  · exact context_12_21641_194615
  · exact context_12_21642_194643
  · exact context_12_21643_194672

theorem selected_cut_06524 : selected 9 ⟨194706, by decide⟩
    (prefixPartial 12 21644) = some ⟨12, 2, 0, 194706, 21644, 1753, 65536⟩ := by
  decide +kernel

theorem context_12_21644_194706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21644 ⟨194706, by decide⟩ :=
  accepted_of_selected 12 21644 ⟨194706, by decide⟩ ⟨12, 2, 0, 194706, 21644, 1753, 65536⟩
    (by decide) selected_cut_06524

theorem selected_cut_06525 : selected 9 ⟨194729, by decide⟩
    (prefixPartial 12 21645) = some ⟨12, 2, 0, 194729, 21645, 1585, 65536⟩ := by
  decide +kernel

theorem context_12_21645_194729 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21645 ⟨194729, by decide⟩ :=
  accepted_of_selected 12 21645 ⟨194729, by decide⟩ ⟨12, 2, 0, 194729, 21645, 1585, 65536⟩
    (by decide) selected_cut_06525

theorem selected_cut_06526 : selected 9 ⟨194756, by decide⟩
    (prefixPartial 12 21646) = some ⟨12, 2, 0, 194756, 21646, 1565, 65536⟩ := by
  decide +kernel

theorem context_12_21646_194756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21646 ⟨194756, by decide⟩ :=
  accepted_of_selected 12 21646 ⟨194756, by decide⟩ ⟨12, 2, 0, 194756, 21646, 1565, 65536⟩
    (by decide) selected_cut_06526

theorem selected_cut_06527 : selected 9 ⟨194779, by decide⟩
    (prefixPartial 12 21647) = some ⟨12, 2, 0, 194779, 21647, 1653, 65536⟩ := by
  decide +kernel

theorem context_12_21647_194779 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21647 ⟨194779, by decide⟩ :=
  accepted_of_selected 12 21647 ⟨194779, by decide⟩ ⟨12, 2, 0, 194779, 21647, 1653, 65536⟩
    (by decide) selected_cut_06527

theorem unmarked_context_11_5411_194780 : frontier 10 ⟨194780, by decide⟩
    (prefixCache 11 5411) (prefixPartial 11 5411) = false := by
  decide +kernel

theorem node_context_11_5411_194780 : EJMOriginalGlobalDAGData.nodes 10 ⟨194780, by decide⟩ =
    .split (coordinate 11) (![⟨194706, by decide⟩,⟨194729, by decide⟩,⟨194756, by decide⟩,⟨194779, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5411_194780 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5411 ⟨194780, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5411
    ⟨194780, by decide⟩ (by decide) (![⟨194706, by decide⟩,⟨194729, by decide⟩,⟨194756, by decide⟩,⟨194779, by decide⟩]) unmarked_context_11_5411_194780 node_context_11_5411_194780
  intro a
  fin_cases a
  · exact context_12_21644_194706
  · exact context_12_21645_194729
  · exact context_12_21646_194756
  · exact context_12_21647_194779

theorem unmarked_context_10_1352_194781 : frontier 11 ⟨194781, by decide⟩
    (prefixCache 10 1352) (prefixPartial 10 1352) = false := by
  decide +kernel

theorem node_context_10_1352_194781 : EJMOriginalGlobalDAGData.nodes 11 ⟨194781, by decide⟩ =
    .split (coordinate 10) (![⟨194401, by decide⟩,⟨194551, by decide⟩,⟨194673, by decide⟩,⟨194780, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1352_194781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1352 ⟨194781, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1352
    ⟨194781, by decide⟩ (by decide) (![⟨194401, by decide⟩,⟨194551, by decide⟩,⟨194673, by decide⟩,⟨194780, by decide⟩]) unmarked_context_10_1352_194781 node_context_10_1352_194781
  intro a
  fin_cases a
  · exact context_11_5408_194401
  · exact context_11_5409_194551
  · exact context_11_5410_194673
  · exact context_11_5411_194780

theorem selected_cut_06528 : selected 9 ⟨194844, by decide⟩
    (prefixPartial 12 21648) = some ⟨12, 2, 0, 194844, 21648, 2841, 65536⟩ := by
  decide +kernel

theorem context_12_21648_194844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21648 ⟨194844, by decide⟩ :=
  accepted_of_selected 12 21648 ⟨194844, by decide⟩ ⟨12, 2, 0, 194844, 21648, 2841, 65536⟩
    (by decide) selected_cut_06528

theorem selected_cut_06529 : selected 9 ⟨194875, by decide⟩
    (prefixPartial 12 21649) = some ⟨12, 2, 0, 194875, 21649, 1997, 65536⟩ := by
  decide +kernel

theorem context_12_21649_194875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 21649 ⟨194875, by decide⟩ :=
  accepted_of_selected 12 21649 ⟨194875, by decide⟩ ⟨12, 2, 0, 194875, 21649, 1997, 65536⟩
    (by decide) selected_cut_06529

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
