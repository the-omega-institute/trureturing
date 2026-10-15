/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover486
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_46756 : selected 9 ⟨1305066, by decide⟩
    (prefixPartial 12 371500) = some ⟨12, 2, 0, 1305066, 371500, 2521, 65536⟩ := by
  decide +kernel

theorem context_12_371500_1305066 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371500 ⟨1305066, by decide⟩ :=
  accepted_of_selected 12 371500 ⟨1305066, by decide⟩ ⟨12, 2, 0, 1305066, 371500, 2521, 65536⟩
    (by decide) selected_cut_46756

theorem selected_cut_46757 : selected 9 ⟨1305102, by decide⟩
    (prefixPartial 12 371501) = some ⟨12, 2, 0, 1305102, 371501, 2401, 65536⟩ := by
  decide +kernel

theorem context_12_371501_1305102 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371501 ⟨1305102, by decide⟩ :=
  accepted_of_selected 12 371501 ⟨1305102, by decide⟩ ⟨12, 2, 0, 1305102, 371501, 2401, 65536⟩
    (by decide) selected_cut_46757

theorem selected_cut_46758 : selected 9 ⟨1305134, by decide⟩
    (prefixPartial 12 371502) = some ⟨12, 2, 0, 1305134, 371502, 2245, 65536⟩ := by
  decide +kernel

theorem context_12_371502_1305134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371502 ⟨1305134, by decide⟩ :=
  accepted_of_selected 12 371502 ⟨1305134, by decide⟩ ⟨12, 2, 0, 1305134, 371502, 2245, 65536⟩
    (by decide) selected_cut_46758

theorem selected_cut_46759 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 371503) = some ⟨12, 1, 0, 903806, 371503, 1, 65536⟩ := by
  decide +kernel

theorem context_12_371503_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371503 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 371503 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 371503, 1, 65536⟩
    (by decide) selected_cut_46759

theorem unmarked_context_11_92875_1305135 : frontier 10 ⟨1305135, by decide⟩
    (prefixCache 11 92875) (prefixPartial 11 92875) = false := by
  decide +kernel

theorem node_context_11_92875_1305135 : EJMOriginalGlobalDAGData.nodes 10 ⟨1305135, by decide⟩ =
    .split (coordinate 11) (![⟨1305066, by decide⟩,⟨1305102, by decide⟩,⟨1305134, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92875_1305135 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92875 ⟨1305135, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92875
    ⟨1305135, by decide⟩ (by decide) (![⟨1305066, by decide⟩,⟨1305102, by decide⟩,⟨1305134, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_92875_1305135 node_context_11_92875_1305135
  intro a
  fin_cases a
  · exact context_12_371500_1305066
  · exact context_12_371501_1305102
  · exact context_12_371502_1305134
  · exact context_12_371503_903806

theorem unmarked_context_10_23218_1305136 : frontier 11 ⟨1305136, by decide⟩
    (prefixCache 10 23218) (prefixPartial 10 23218) = false := by
  decide +kernel

theorem node_context_10_23218_1305136 : EJMOriginalGlobalDAGData.nodes 11 ⟨1305136, by decide⟩ =
    .split (coordinate 10) (![⟨1304834, by decide⟩,⟨1305025, by decide⟩,⟨900587, by decide⟩,⟨1305135, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23218_1305136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23218 ⟨1305136, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23218
    ⟨1305136, by decide⟩ (by decide) (![⟨1304834, by decide⟩,⟨1305025, by decide⟩,⟨900587, by decide⟩,⟨1305135, by decide⟩]) unmarked_context_10_23218_1305136 node_context_10_23218_1305136
  intro a
  fin_cases a
  · exact context_11_92872_1304834
  · exact context_11_92873_1305025
  · exact context_11_92874_900587
  · exact context_11_92875_1305135

theorem selected_cut_46760 : selected 9 ⟨766630, by decide⟩
    (prefixPartial 12 371504) = some ⟨12, 1, 0, 766630, 371504, 1, 65536⟩ := by
  decide +kernel

theorem context_12_371504_766630 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371504 ⟨766630, by decide⟩ :=
  accepted_of_selected 12 371504 ⟨766630, by decide⟩ ⟨12, 1, 0, 766630, 371504, 1, 65536⟩
    (by decide) selected_cut_46760

theorem selected_cut_46761 : selected 9 ⟨1305169, by decide⟩
    (prefixPartial 12 371505) = some ⟨12, 2, 0, 1305169, 371505, 2369, 65536⟩ := by
  decide +kernel

theorem context_12_371505_1305169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371505 ⟨1305169, by decide⟩ :=
  accepted_of_selected 12 371505 ⟨1305169, by decide⟩ ⟨12, 2, 0, 1305169, 371505, 2369, 65536⟩
    (by decide) selected_cut_46761

theorem selected_cut_46762 : selected 9 ⟨1305208, by decide⟩
    (prefixPartial 12 371506) = some ⟨12, 2, 0, 1305208, 371506, 2117, 65536⟩ := by
  decide +kernel

theorem context_12_371506_1305208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371506 ⟨1305208, by decide⟩ :=
  accepted_of_selected 12 371506 ⟨1305208, by decide⟩ ⟨12, 2, 0, 1305208, 371506, 2117, 65536⟩
    (by decide) selected_cut_46762

theorem selected_cut_46763 : selected 9 ⟨1305248, by decide⟩
    (prefixPartial 12 371507) = some ⟨12, 2, 0, 1305248, 371507, 2313, 65536⟩ := by
  decide +kernel

theorem context_12_371507_1305248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371507 ⟨1305248, by decide⟩ :=
  accepted_of_selected 12 371507 ⟨1305248, by decide⟩ ⟨12, 2, 0, 1305248, 371507, 2313, 65536⟩
    (by decide) selected_cut_46763

theorem unmarked_context_11_92876_1305249 : frontier 10 ⟨1305249, by decide⟩
    (prefixCache 11 92876) (prefixPartial 11 92876) = false := by
  decide +kernel

theorem node_context_11_92876_1305249 : EJMOriginalGlobalDAGData.nodes 10 ⟨1305249, by decide⟩ =
    .split (coordinate 11) (![⟨766630, by decide⟩,⟨1305169, by decide⟩,⟨1305208, by decide⟩,⟨1305248, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92876_1305249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92876 ⟨1305249, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92876
    ⟨1305249, by decide⟩ (by decide) (![⟨766630, by decide⟩,⟨1305169, by decide⟩,⟨1305208, by decide⟩,⟨1305248, by decide⟩]) unmarked_context_11_92876_1305249 node_context_11_92876_1305249
  intro a
  fin_cases a
  · exact context_12_371504_766630
  · exact context_12_371505_1305169
  · exact context_12_371506_1305208
  · exact context_12_371507_1305248

theorem selected_cut_46764 : selected 9 ⟨1305303, by decide⟩
    (prefixPartial 12 371508) = some ⟨12, 2, 0, 1305303, 371508, 2705, 65536⟩ := by
  decide +kernel

theorem context_12_371508_1305303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371508 ⟨1305303, by decide⟩ :=
  accepted_of_selected 12 371508 ⟨1305303, by decide⟩ ⟨12, 2, 0, 1305303, 371508, 2705, 65536⟩
    (by decide) selected_cut_46764

theorem selected_cut_46765 : selected 9 ⟨1305349, by decide⟩
    (prefixPartial 12 371509) = some ⟨12, 2, 0, 1305349, 371509, 2557, 65536⟩ := by
  decide +kernel

theorem context_12_371509_1305349 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371509 ⟨1305349, by decide⟩ :=
  accepted_of_selected 12 371509 ⟨1305349, by decide⟩ ⟨12, 2, 0, 1305349, 371509, 2557, 65536⟩
    (by decide) selected_cut_46765

theorem selected_cut_46766 : selected 9 ⟨1305387, by decide⟩
    (prefixPartial 12 371510) = some ⟨12, 2, 0, 1305387, 371510, 2209, 65536⟩ := by
  decide +kernel

theorem context_12_371510_1305387 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371510 ⟨1305387, by decide⟩ :=
  accepted_of_selected 12 371510 ⟨1305387, by decide⟩ ⟨12, 2, 0, 1305387, 371510, 2209, 65536⟩
    (by decide) selected_cut_46766

theorem selected_cut_46767 : selected 9 ⟨1305421, by decide⟩
    (prefixPartial 12 371511) = some ⟨12, 2, 0, 1305421, 371511, 2573, 65536⟩ := by
  decide +kernel

theorem context_12_371511_1305421 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371511 ⟨1305421, by decide⟩ :=
  accepted_of_selected 12 371511 ⟨1305421, by decide⟩ ⟨12, 2, 0, 1305421, 371511, 2573, 65536⟩
    (by decide) selected_cut_46767

theorem unmarked_context_11_92877_1305422 : frontier 10 ⟨1305422, by decide⟩
    (prefixCache 11 92877) (prefixPartial 11 92877) = false := by
  decide +kernel

theorem node_context_11_92877_1305422 : EJMOriginalGlobalDAGData.nodes 10 ⟨1305422, by decide⟩ =
    .split (coordinate 11) (![⟨1305303, by decide⟩,⟨1305349, by decide⟩,⟨1305387, by decide⟩,⟨1305421, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92877_1305422 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92877 ⟨1305422, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92877
    ⟨1305422, by decide⟩ (by decide) (![⟨1305303, by decide⟩,⟨1305349, by decide⟩,⟨1305387, by decide⟩,⟨1305421, by decide⟩]) unmarked_context_11_92877_1305422 node_context_11_92877_1305422
  intro a
  fin_cases a
  · exact context_12_371508_1305303
  · exact context_12_371509_1305349
  · exact context_12_371510_1305387
  · exact context_12_371511_1305421

theorem selected_cut_46768 : selected 9 ⟨1305464, by decide⟩
    (prefixPartial 12 371512) = some ⟨12, 2, 0, 1305464, 371512, 2145, 65536⟩ := by
  decide +kernel

theorem context_12_371512_1305464 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371512 ⟨1305464, by decide⟩ :=
  accepted_of_selected 12 371512 ⟨1305464, by decide⟩ ⟨12, 2, 0, 1305464, 371512, 2145, 65536⟩
    (by decide) selected_cut_46768

theorem selected_cut_46769 : selected 9 ⟨1305504, by decide⟩
    (prefixPartial 12 371513) = some ⟨12, 2, 0, 1305504, 371513, 2325, 65536⟩ := by
  decide +kernel

theorem context_12_371513_1305504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371513 ⟨1305504, by decide⟩ :=
  accepted_of_selected 12 371513 ⟨1305504, by decide⟩ ⟨12, 2, 0, 1305504, 371513, 2325, 65536⟩
    (by decide) selected_cut_46769

theorem selected_cut_46770 : selected 9 ⟨662655, by decide⟩
    (prefixPartial 12 371514) = some ⟨12, 1, 0, 662655, 371514, 1, 65536⟩ := by
  decide +kernel

theorem context_12_371514_662655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371514 ⟨662655, by decide⟩ :=
  accepted_of_selected 12 371514 ⟨662655, by decide⟩ ⟨12, 1, 0, 662655, 371514, 1, 65536⟩
    (by decide) selected_cut_46770

theorem selected_cut_46771 : selected 9 ⟨1305542, by decide⟩
    (prefixPartial 12 371515) = some ⟨12, 2, 0, 1305542, 371515, 2177, 65536⟩ := by
  decide +kernel

theorem context_12_371515_1305542 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371515 ⟨1305542, by decide⟩ :=
  accepted_of_selected 12 371515 ⟨1305542, by decide⟩ ⟨12, 2, 0, 1305542, 371515, 2177, 65536⟩
    (by decide) selected_cut_46771

theorem unmarked_context_11_92878_1305543 : frontier 10 ⟨1305543, by decide⟩
    (prefixCache 11 92878) (prefixPartial 11 92878) = false := by
  decide +kernel

theorem node_context_11_92878_1305543 : EJMOriginalGlobalDAGData.nodes 10 ⟨1305543, by decide⟩ =
    .split (coordinate 11) (![⟨1305464, by decide⟩,⟨1305504, by decide⟩,⟨662655, by decide⟩,⟨1305542, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92878_1305543 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92878 ⟨1305543, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92878
    ⟨1305543, by decide⟩ (by decide) (![⟨1305464, by decide⟩,⟨1305504, by decide⟩,⟨662655, by decide⟩,⟨1305542, by decide⟩]) unmarked_context_11_92878_1305543 node_context_11_92878_1305543
  intro a
  fin_cases a
  · exact context_12_371512_1305464
  · exact context_12_371513_1305504
  · exact context_12_371514_662655
  · exact context_12_371515_1305542

theorem selected_cut_46772 : selected 9 ⟨1305582, by decide⟩
    (prefixPartial 12 371516) = some ⟨12, 2, 0, 1305582, 371516, 2029, 65536⟩ := by
  decide +kernel

theorem context_12_371516_1305582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371516 ⟨1305582, by decide⟩ :=
  accepted_of_selected 12 371516 ⟨1305582, by decide⟩ ⟨12, 2, 0, 1305582, 371516, 2029, 65536⟩
    (by decide) selected_cut_46772

theorem selected_cut_46773 : selected 9 ⟨1305614, by decide⟩
    (prefixPartial 12 371517) = some ⟨12, 2, 0, 1305614, 371517, 2089, 65536⟩ := by
  decide +kernel

theorem context_12_371517_1305614 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371517 ⟨1305614, by decide⟩ :=
  accepted_of_selected 12 371517 ⟨1305614, by decide⟩ ⟨12, 2, 0, 1305614, 371517, 2089, 65536⟩
    (by decide) selected_cut_46773

theorem selected_cut_46774 : selected 9 ⟨762109, by decide⟩
    (prefixPartial 12 371518) = some ⟨12, 1, 0, 762109, 371518, 1, 65536⟩ := by
  decide +kernel

theorem context_12_371518_762109 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371518 ⟨762109, by decide⟩ :=
  accepted_of_selected 12 371518 ⟨762109, by decide⟩ ⟨12, 1, 0, 762109, 371518, 1, 65536⟩
    (by decide) selected_cut_46774

theorem selected_cut_46775 : selected 9 ⟨1120582, by decide⟩
    (prefixPartial 12 371519) = some ⟨12, 1, 0, 1120582, 371519, 1, 65536⟩ := by
  decide +kernel

theorem context_12_371519_1120582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371519 ⟨1120582, by decide⟩ :=
  accepted_of_selected 12 371519 ⟨1120582, by decide⟩ ⟨12, 1, 0, 1120582, 371519, 1, 65536⟩
    (by decide) selected_cut_46775

theorem unmarked_context_11_92879_1305615 : frontier 10 ⟨1305615, by decide⟩
    (prefixCache 11 92879) (prefixPartial 11 92879) = false := by
  decide +kernel

theorem node_context_11_92879_1305615 : EJMOriginalGlobalDAGData.nodes 10 ⟨1305615, by decide⟩ =
    .split (coordinate 11) (![⟨1305582, by decide⟩,⟨1305614, by decide⟩,⟨762109, by decide⟩,⟨1120582, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92879_1305615 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92879 ⟨1305615, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92879
    ⟨1305615, by decide⟩ (by decide) (![⟨1305582, by decide⟩,⟨1305614, by decide⟩,⟨762109, by decide⟩,⟨1120582, by decide⟩]) unmarked_context_11_92879_1305615 node_context_11_92879_1305615
  intro a
  fin_cases a
  · exact context_12_371516_1305582
  · exact context_12_371517_1305614
  · exact context_12_371518_762109
  · exact context_12_371519_1120582

theorem unmarked_context_10_23219_1305616 : frontier 11 ⟨1305616, by decide⟩
    (prefixCache 10 23219) (prefixPartial 10 23219) = false := by
  decide +kernel

theorem node_context_10_23219_1305616 : EJMOriginalGlobalDAGData.nodes 11 ⟨1305616, by decide⟩ =
    .split (coordinate 10) (![⟨1305249, by decide⟩,⟨1305422, by decide⟩,⟨1305543, by decide⟩,⟨1305615, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23219_1305616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23219 ⟨1305616, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23219
    ⟨1305616, by decide⟩ (by decide) (![⟨1305249, by decide⟩,⟨1305422, by decide⟩,⟨1305543, by decide⟩,⟨1305615, by decide⟩]) unmarked_context_10_23219_1305616 node_context_10_23219_1305616
  intro a
  fin_cases a
  · exact context_11_92876_1305249
  · exact context_11_92877_1305422
  · exact context_11_92878_1305543
  · exact context_11_92879_1305615

theorem unmarked_context_9_5804_1305617 : frontier 12 ⟨1305617, by decide⟩
    (prefixCache 9 5804) (prefixPartial 9 5804) = false := by
  decide +kernel

theorem node_context_9_5804_1305617 : EJMOriginalGlobalDAGData.nodes 12 ⟨1305617, by decide⟩ =
    .split (coordinate 9) (![⟨1304094, by decide⟩,⟨1304723, by decide⟩,⟨1305136, by decide⟩,⟨1305616, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5804_1305617 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5804 ⟨1305617, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5804
    ⟨1305617, by decide⟩ (by decide) (![⟨1304094, by decide⟩,⟨1304723, by decide⟩,⟨1305136, by decide⟩,⟨1305616, by decide⟩]) unmarked_context_9_5804_1305617 node_context_9_5804_1305617
  intro a
  fin_cases a
  · exact context_10_23216_1304094
  · exact context_10_23217_1304723
  · exact context_10_23218_1305136
  · exact context_10_23219_1305616

theorem selected_cut_46776 : selected 9 ⟨1120586, by decide⟩
    (prefixPartial 12 371520) = some ⟨12, 1, 0, 1120586, 371520, 1, 65536⟩ := by
  decide +kernel

theorem context_12_371520_1120586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371520 ⟨1120586, by decide⟩ :=
  accepted_of_selected 12 371520 ⟨1120586, by decide⟩ ⟨12, 1, 0, 1120586, 371520, 1, 65536⟩
    (by decide) selected_cut_46776

theorem selected_cut_46777 : selected 9 ⟨1305648, by decide⟩
    (prefixPartial 12 371521) = some ⟨12, 2, 0, 1305648, 371521, 1617, 65536⟩ := by
  decide +kernel

theorem context_12_371521_1305648 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371521 ⟨1305648, by decide⟩ :=
  accepted_of_selected 12 371521 ⟨1305648, by decide⟩ ⟨12, 2, 0, 1305648, 371521, 1617, 65536⟩
    (by decide) selected_cut_46777

theorem selected_cut_46778 : selected 9 ⟨1305681, by decide⟩
    (prefixPartial 12 371522) = some ⟨12, 2, 0, 1305681, 371522, 1481, 65536⟩ := by
  decide +kernel

theorem context_12_371522_1305681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371522 ⟨1305681, by decide⟩ :=
  accepted_of_selected 12 371522 ⟨1305681, by decide⟩ ⟨12, 2, 0, 1305681, 371522, 1481, 65536⟩
    (by decide) selected_cut_46778

theorem selected_cut_46779 : selected 9 ⟨1305709, by decide⟩
    (prefixPartial 12 371523) = some ⟨12, 2, 0, 1305709, 371523, 1757, 65536⟩ := by
  decide +kernel

theorem context_12_371523_1305709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371523 ⟨1305709, by decide⟩ :=
  accepted_of_selected 12 371523 ⟨1305709, by decide⟩ ⟨12, 2, 0, 1305709, 371523, 1757, 65536⟩
    (by decide) selected_cut_46779

theorem unmarked_context_11_92880_1305710 : frontier 10 ⟨1305710, by decide⟩
    (prefixCache 11 92880) (prefixPartial 11 92880) = false := by
  decide +kernel

theorem node_context_11_92880_1305710 : EJMOriginalGlobalDAGData.nodes 10 ⟨1305710, by decide⟩ =
    .split (coordinate 11) (![⟨1120586, by decide⟩,⟨1305648, by decide⟩,⟨1305681, by decide⟩,⟨1305709, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92880_1305710 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92880 ⟨1305710, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92880
    ⟨1305710, by decide⟩ (by decide) (![⟨1120586, by decide⟩,⟨1305648, by decide⟩,⟨1305681, by decide⟩,⟨1305709, by decide⟩]) unmarked_context_11_92880_1305710 node_context_11_92880_1305710
  intro a
  fin_cases a
  · exact context_12_371520_1120586
  · exact context_12_371521_1305648
  · exact context_12_371522_1305681
  · exact context_12_371523_1305709

theorem selected_cut_46780 : selected 9 ⟨1305753, by decide⟩
    (prefixPartial 12 371524) = some ⟨12, 2, 0, 1305753, 371524, 1957, 65536⟩ := by
  decide +kernel

theorem context_12_371524_1305753 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371524 ⟨1305753, by decide⟩ :=
  accepted_of_selected 12 371524 ⟨1305753, by decide⟩ ⟨12, 2, 0, 1305753, 371524, 1957, 65536⟩
    (by decide) selected_cut_46780

theorem selected_cut_46781 : selected 9 ⟨1257136, by decide⟩
    (prefixPartial 12 371525) = some ⟨12, 1, 0, 1257136, 371525, 1, 65536⟩ := by
  decide +kernel

theorem context_12_371525_1257136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371525 ⟨1257136, by decide⟩ :=
  accepted_of_selected 12 371525 ⟨1257136, by decide⟩ ⟨12, 1, 0, 1257136, 371525, 1, 65536⟩
    (by decide) selected_cut_46781

theorem selected_cut_46782 : selected 9 ⟨1305787, by decide⟩
    (prefixPartial 12 371526) = some ⟨12, 2, 0, 1305787, 371526, 1657, 65536⟩ := by
  decide +kernel

theorem context_12_371526_1305787 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371526 ⟨1305787, by decide⟩ :=
  accepted_of_selected 12 371526 ⟨1305787, by decide⟩ ⟨12, 2, 0, 1305787, 371526, 1657, 65536⟩
    (by decide) selected_cut_46782

theorem selected_cut_46783 : selected 9 ⟨1305819, by decide⟩
    (prefixPartial 12 371527) = some ⟨12, 2, 0, 1305819, 371527, 2037, 65536⟩ := by
  decide +kernel

theorem context_12_371527_1305819 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371527 ⟨1305819, by decide⟩ :=
  accepted_of_selected 12 371527 ⟨1305819, by decide⟩ ⟨12, 2, 0, 1305819, 371527, 2037, 65536⟩
    (by decide) selected_cut_46783

theorem unmarked_context_11_92881_1305820 : frontier 10 ⟨1305820, by decide⟩
    (prefixCache 11 92881) (prefixPartial 11 92881) = false := by
  decide +kernel

theorem node_context_11_92881_1305820 : EJMOriginalGlobalDAGData.nodes 10 ⟨1305820, by decide⟩ =
    .split (coordinate 11) (![⟨1305753, by decide⟩,⟨1257136, by decide⟩,⟨1305787, by decide⟩,⟨1305819, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92881_1305820 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92881 ⟨1305820, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92881
    ⟨1305820, by decide⟩ (by decide) (![⟨1305753, by decide⟩,⟨1257136, by decide⟩,⟨1305787, by decide⟩,⟨1305819, by decide⟩]) unmarked_context_11_92881_1305820 node_context_11_92881_1305820
  intro a
  fin_cases a
  · exact context_12_371524_1305753
  · exact context_12_371525_1257136
  · exact context_12_371526_1305787
  · exact context_12_371527_1305819

theorem selected_cut_46784 : selected 9 ⟨1305848, by decide⟩
    (prefixPartial 12 371528) = some ⟨12, 2, 0, 1305848, 371528, 1749, 65536⟩ := by
  decide +kernel

theorem context_12_371528_1305848 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371528 ⟨1305848, by decide⟩ :=
  accepted_of_selected 12 371528 ⟨1305848, by decide⟩ ⟨12, 2, 0, 1305848, 371528, 1749, 65536⟩
    (by decide) selected_cut_46784

theorem selected_cut_46785 : selected 9 ⟨1305880, by decide⟩
    (prefixPartial 12 371529) = some ⟨12, 2, 0, 1305880, 371529, 1737, 65536⟩ := by
  decide +kernel

theorem context_12_371529_1305880 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371529 ⟨1305880, by decide⟩ :=
  accepted_of_selected 12 371529 ⟨1305880, by decide⟩ ⟨12, 2, 0, 1305880, 371529, 1737, 65536⟩
    (by decide) selected_cut_46785

theorem selected_cut_46786 : selected 9 ⟨1305912, by decide⟩
    (prefixPartial 12 371530) = some ⟨12, 2, 0, 1305912, 371530, 1505, 65536⟩ := by
  decide +kernel

theorem context_12_371530_1305912 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371530 ⟨1305912, by decide⟩ :=
  accepted_of_selected 12 371530 ⟨1305912, by decide⟩ ⟨12, 2, 0, 1305912, 371530, 1505, 65536⟩
    (by decide) selected_cut_46786

theorem selected_cut_46787 : selected 9 ⟨1305937, by decide⟩
    (prefixPartial 12 371531) = some ⟨12, 2, 0, 1305937, 371531, 1673, 65536⟩ := by
  decide +kernel

theorem context_12_371531_1305937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371531 ⟨1305937, by decide⟩ :=
  accepted_of_selected 12 371531 ⟨1305937, by decide⟩ ⟨12, 2, 0, 1305937, 371531, 1673, 65536⟩
    (by decide) selected_cut_46787

theorem unmarked_context_11_92882_1305938 : frontier 10 ⟨1305938, by decide⟩
    (prefixCache 11 92882) (prefixPartial 11 92882) = false := by
  decide +kernel

theorem node_context_11_92882_1305938 : EJMOriginalGlobalDAGData.nodes 10 ⟨1305938, by decide⟩ =
    .split (coordinate 11) (![⟨1305848, by decide⟩,⟨1305880, by decide⟩,⟨1305912, by decide⟩,⟨1305937, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92882_1305938 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92882 ⟨1305938, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92882
    ⟨1305938, by decide⟩ (by decide) (![⟨1305848, by decide⟩,⟨1305880, by decide⟩,⟨1305912, by decide⟩,⟨1305937, by decide⟩]) unmarked_context_11_92882_1305938 node_context_11_92882_1305938
  intro a
  fin_cases a
  · exact context_12_371528_1305848
  · exact context_12_371529_1305880
  · exact context_12_371530_1305912
  · exact context_12_371531_1305937

theorem selected_cut_46788 : selected 9 ⟨1305962, by decide⟩
    (prefixPartial 12 371532) = some ⟨12, 2, 0, 1305962, 371532, 1489, 65536⟩ := by
  decide +kernel

theorem context_12_371532_1305962 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371532 ⟨1305962, by decide⟩ :=
  accepted_of_selected 12 371532 ⟨1305962, by decide⟩ ⟨12, 2, 0, 1305962, 371532, 1489, 65536⟩
    (by decide) selected_cut_46788

theorem selected_cut_46789 : selected 9 ⟨1305984, by decide⟩
    (prefixPartial 12 371533) = some ⟨12, 2, 0, 1305984, 371533, 1401, 65536⟩ := by
  decide +kernel

theorem context_12_371533_1305984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371533 ⟨1305984, by decide⟩ :=
  accepted_of_selected 12 371533 ⟨1305984, by decide⟩ ⟨12, 2, 0, 1305984, 371533, 1401, 65536⟩
    (by decide) selected_cut_46789

theorem selected_cut_46790 : selected 9 ⟨1306010, by decide⟩
    (prefixPartial 12 371534) = some ⟨12, 2, 0, 1306010, 371534, 1345, 65536⟩ := by
  decide +kernel

theorem context_12_371534_1306010 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371534 ⟨1306010, by decide⟩ :=
  accepted_of_selected 12 371534 ⟨1306010, by decide⟩ ⟨12, 2, 0, 1306010, 371534, 1345, 65536⟩
    (by decide) selected_cut_46790

theorem selected_cut_46791 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 371535) = some ⟨12, 1, 0, 903806, 371535, 1, 65536⟩ := by
  decide +kernel

theorem context_12_371535_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371535 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 371535 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 371535, 1, 65536⟩
    (by decide) selected_cut_46791

theorem unmarked_context_11_92883_1306011 : frontier 10 ⟨1306011, by decide⟩
    (prefixCache 11 92883) (prefixPartial 11 92883) = false := by
  decide +kernel

theorem node_context_11_92883_1306011 : EJMOriginalGlobalDAGData.nodes 10 ⟨1306011, by decide⟩ =
    .split (coordinate 11) (![⟨1305962, by decide⟩,⟨1305984, by decide⟩,⟨1306010, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92883_1306011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92883 ⟨1306011, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92883
    ⟨1306011, by decide⟩ (by decide) (![⟨1305962, by decide⟩,⟨1305984, by decide⟩,⟨1306010, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_92883_1306011 node_context_11_92883_1306011
  intro a
  fin_cases a
  · exact context_12_371532_1305962
  · exact context_12_371533_1305984
  · exact context_12_371534_1306010
  · exact context_12_371535_903806

theorem unmarked_context_10_23220_1306012 : frontier 11 ⟨1306012, by decide⟩
    (prefixCache 10 23220) (prefixPartial 10 23220) = false := by
  decide +kernel

theorem node_context_10_23220_1306012 : EJMOriginalGlobalDAGData.nodes 11 ⟨1306012, by decide⟩ =
    .split (coordinate 10) (![⟨1305710, by decide⟩,⟨1305820, by decide⟩,⟨1305938, by decide⟩,⟨1306011, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23220_1306012 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23220 ⟨1306012, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23220
    ⟨1306012, by decide⟩ (by decide) (![⟨1305710, by decide⟩,⟨1305820, by decide⟩,⟨1305938, by decide⟩,⟨1306011, by decide⟩]) unmarked_context_10_23220_1306012 node_context_10_23220_1306012
  intro a
  fin_cases a
  · exact context_11_92880_1305710
  · exact context_11_92881_1305820
  · exact context_11_92882_1305938
  · exact context_11_92883_1306011

theorem selected_cut_46792 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 23221) = some ⟨10, 1, 0, 893098, 23221, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_23221_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23221 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 23221 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 23221, 1, 1048576⟩
    (by decide) selected_cut_46792

theorem selected_cut_46793 : selected 10 ⟨1306071, by decide⟩
    (prefixPartial 11 92888) = some ⟨11, 2, 0, 1306071, 92888, 3445, 262144⟩ := by
  decide +kernel

theorem context_11_92888_1306071 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92888 ⟨1306071, by decide⟩ :=
  accepted_of_selected 11 92888 ⟨1306071, by decide⟩ ⟨11, 2, 0, 1306071, 92888, 3445, 262144⟩
    (by decide) selected_cut_46793

theorem selected_cut_46794 : selected 10 ⟨1306130, by decide⟩
    (prefixPartial 11 92889) = some ⟨11, 2, 0, 1306130, 92889, 3797, 262144⟩ := by
  decide +kernel

theorem context_11_92889_1306130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92889 ⟨1306130, by decide⟩ :=
  accepted_of_selected 11 92889 ⟨1306130, by decide⟩ ⟨11, 2, 0, 1306130, 92889, 3797, 262144⟩
    (by decide) selected_cut_46794

theorem selected_cut_46795 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 92890) = some ⟨11, 1, 0, 900587, 92890, 1, 262144⟩ := by
  decide +kernel

theorem context_11_92890_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92890 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 92890 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 92890, 1, 262144⟩
    (by decide) selected_cut_46795

theorem selected_cut_46796 : selected 10 ⟨1306170, by decide⟩
    (prefixPartial 11 92891) = some ⟨11, 2, 0, 1306170, 92891, 2129, 262144⟩ := by
  decide +kernel

theorem context_11_92891_1306170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92891 ⟨1306170, by decide⟩ :=
  accepted_of_selected 11 92891 ⟨1306170, by decide⟩ ⟨11, 2, 0, 1306170, 92891, 2129, 262144⟩
    (by decide) selected_cut_46796

theorem unmarked_context_10_23222_1306171 : frontier 11 ⟨1306171, by decide⟩
    (prefixCache 10 23222) (prefixPartial 10 23222) = false := by
  decide +kernel

theorem node_context_10_23222_1306171 : EJMOriginalGlobalDAGData.nodes 11 ⟨1306171, by decide⟩ =
    .split (coordinate 10) (![⟨1306071, by decide⟩,⟨1306130, by decide⟩,⟨900587, by decide⟩,⟨1306170, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23222_1306171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23222 ⟨1306171, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23222
    ⟨1306171, by decide⟩ (by decide) (![⟨1306071, by decide⟩,⟨1306130, by decide⟩,⟨900587, by decide⟩,⟨1306170, by decide⟩]) unmarked_context_10_23222_1306171 node_context_10_23222_1306171
  intro a
  fin_cases a
  · exact context_11_92888_1306071
  · exact context_11_92889_1306130
  · exact context_11_92890_900587
  · exact context_11_92891_1306170

theorem selected_cut_46797 : selected 9 ⟨1306190, by decide⟩
    (prefixPartial 12 371568) = some ⟨12, 2, 0, 1306190, 371568, 1185, 65536⟩ := by
  decide +kernel

theorem context_12_371568_1306190 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371568 ⟨1306190, by decide⟩ :=
  accepted_of_selected 12 371568 ⟨1306190, by decide⟩ ⟨12, 2, 0, 1306190, 371568, 1185, 65536⟩
    (by decide) selected_cut_46797

theorem selected_cut_46798 : selected 9 ⟨1306207, by decide⟩
    (prefixPartial 12 371569) = some ⟨12, 2, 0, 1306207, 371569, 1221, 65536⟩ := by
  decide +kernel

theorem context_12_371569_1306207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371569 ⟨1306207, by decide⟩ :=
  accepted_of_selected 12 371569 ⟨1306207, by decide⟩ ⟨12, 2, 0, 1306207, 371569, 1221, 65536⟩
    (by decide) selected_cut_46798

theorem selected_cut_46799 : selected 9 ⟨1306224, by decide⟩
    (prefixPartial 12 371570) = some ⟨12, 2, 0, 1306224, 371570, 1149, 65536⟩ := by
  decide +kernel

theorem context_12_371570_1306224 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371570 ⟨1306224, by decide⟩ :=
  accepted_of_selected 12 371570 ⟨1306224, by decide⟩ ⟨12, 2, 0, 1306224, 371570, 1149, 65536⟩
    (by decide) selected_cut_46799

theorem selected_cut_46800 : selected 9 ⟨1306244, by decide⟩
    (prefixPartial 12 371571) = some ⟨12, 2, 0, 1306244, 371571, 1137, 65536⟩ := by
  decide +kernel

theorem context_12_371571_1306244 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371571 ⟨1306244, by decide⟩ :=
  accepted_of_selected 12 371571 ⟨1306244, by decide⟩ ⟨12, 2, 0, 1306244, 371571, 1137, 65536⟩
    (by decide) selected_cut_46800

theorem unmarked_context_11_92892_1306245 : frontier 10 ⟨1306245, by decide⟩
    (prefixCache 11 92892) (prefixPartial 11 92892) = false := by
  decide +kernel

theorem node_context_11_92892_1306245 : EJMOriginalGlobalDAGData.nodes 10 ⟨1306245, by decide⟩ =
    .split (coordinate 11) (![⟨1306190, by decide⟩,⟨1306207, by decide⟩,⟨1306224, by decide⟩,⟨1306244, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92892_1306245 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92892 ⟨1306245, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92892
    ⟨1306245, by decide⟩ (by decide) (![⟨1306190, by decide⟩,⟨1306207, by decide⟩,⟨1306224, by decide⟩,⟨1306244, by decide⟩]) unmarked_context_11_92892_1306245 node_context_11_92892_1306245
  intro a
  fin_cases a
  · exact context_12_371568_1306190
  · exact context_12_371569_1306207
  · exact context_12_371570_1306224
  · exact context_12_371571_1306244

theorem selected_cut_46801 : selected 10 ⟨1306316, by decide⟩
    (prefixPartial 11 92893) = some ⟨11, 2, 0, 1306316, 92893, 3753, 262144⟩ := by
  decide +kernel

theorem context_11_92893_1306316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92893 ⟨1306316, by decide⟩ :=
  accepted_of_selected 11 92893 ⟨1306316, by decide⟩ ⟨11, 2, 0, 1306316, 92893, 3753, 262144⟩
    (by decide) selected_cut_46801

theorem selected_cut_46802 : selected 10 ⟨1306346, by decide⟩
    (prefixPartial 11 92894) = some ⟨11, 2, 0, 1306346, 92894, 2069, 262144⟩ := by
  decide +kernel

theorem context_11_92894_1306346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92894 ⟨1306346, by decide⟩ :=
  accepted_of_selected 11 92894 ⟨1306346, by decide⟩ ⟨11, 2, 0, 1306346, 92894, 2069, 262144⟩
    (by decide) selected_cut_46802

theorem selected_cut_46803 : selected 10 ⟨1306369, by decide⟩
    (prefixPartial 11 92895) = some ⟨11, 2, 0, 1306369, 92895, 1909, 262144⟩ := by
  decide +kernel

theorem context_11_92895_1306369 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92895 ⟨1306369, by decide⟩ :=
  accepted_of_selected 11 92895 ⟨1306369, by decide⟩ ⟨11, 2, 0, 1306369, 92895, 1909, 262144⟩
    (by decide) selected_cut_46803

theorem unmarked_context_10_23223_1306370 : frontier 11 ⟨1306370, by decide⟩
    (prefixCache 10 23223) (prefixPartial 10 23223) = false := by
  decide +kernel

theorem node_context_10_23223_1306370 : EJMOriginalGlobalDAGData.nodes 11 ⟨1306370, by decide⟩ =
    .split (coordinate 10) (![⟨1306245, by decide⟩,⟨1306316, by decide⟩,⟨1306346, by decide⟩,⟨1306369, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23223_1306370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23223 ⟨1306370, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23223
    ⟨1306370, by decide⟩ (by decide) (![⟨1306245, by decide⟩,⟨1306316, by decide⟩,⟨1306346, by decide⟩,⟨1306369, by decide⟩]) unmarked_context_10_23223_1306370 node_context_10_23223_1306370
  intro a
  fin_cases a
  · exact context_11_92892_1306245
  · exact context_11_92893_1306316
  · exact context_11_92894_1306346
  · exact context_11_92895_1306369

theorem unmarked_context_9_5805_1306371 : frontier 12 ⟨1306371, by decide⟩
    (prefixCache 9 5805) (prefixPartial 9 5805) = false := by
  decide +kernel

theorem node_context_9_5805_1306371 : EJMOriginalGlobalDAGData.nodes 12 ⟨1306371, by decide⟩ =
    .split (coordinate 9) (![⟨1306012, by decide⟩,⟨893098, by decide⟩,⟨1306171, by decide⟩,⟨1306370, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5805_1306371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5805 ⟨1306371, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5805
    ⟨1306371, by decide⟩ (by decide) (![⟨1306012, by decide⟩,⟨893098, by decide⟩,⟨1306171, by decide⟩,⟨1306370, by decide⟩]) unmarked_context_9_5805_1306371 node_context_9_5805_1306371
  intro a
  fin_cases a
  · exact context_10_23220_1306012
  · exact context_10_23221_893098
  · exact context_10_23222_1306171
  · exact context_10_23223_1306370

theorem selected_cut_46804 : selected 10 ⟨1306406, by decide⟩
    (prefixPartial 11 92896) = some ⟨11, 2, 0, 1306406, 92896, 1997, 262144⟩ := by
  decide +kernel

theorem context_11_92896_1306406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92896 ⟨1306406, by decide⟩ :=
  accepted_of_selected 11 92896 ⟨1306406, by decide⟩ ⟨11, 2, 0, 1306406, 92896, 1997, 262144⟩
    (by decide) selected_cut_46804

theorem selected_cut_46805 : selected 10 ⟨1306471, by decide⟩
    (prefixPartial 11 92897) = some ⟨11, 2, 0, 1306471, 92897, 3329, 262144⟩ := by
  decide +kernel

theorem context_11_92897_1306471 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92897 ⟨1306471, by decide⟩ :=
  accepted_of_selected 11 92897 ⟨1306471, by decide⟩ ⟨11, 2, 0, 1306471, 92897, 3329, 262144⟩
    (by decide) selected_cut_46805

theorem selected_cut_46806 : selected 10 ⟨1306523, by decide⟩
    (prefixPartial 11 92898) = some ⟨11, 2, 0, 1306523, 92898, 2861, 262144⟩ := by
  decide +kernel

theorem context_11_92898_1306523 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92898 ⟨1306523, by decide⟩ :=
  accepted_of_selected 11 92898 ⟨1306523, by decide⟩ ⟨11, 2, 0, 1306523, 92898, 2861, 262144⟩
    (by decide) selected_cut_46806

theorem selected_cut_46807 : selected 10 ⟨1306548, by decide⟩
    (prefixPartial 11 92899) = some ⟨11, 2, 0, 1306548, 92899, 1589, 262144⟩ := by
  decide +kernel

theorem context_11_92899_1306548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92899 ⟨1306548, by decide⟩ :=
  accepted_of_selected 11 92899 ⟨1306548, by decide⟩ ⟨11, 2, 0, 1306548, 92899, 1589, 262144⟩
    (by decide) selected_cut_46807

theorem unmarked_context_10_23224_1306549 : frontier 11 ⟨1306549, by decide⟩
    (prefixCache 10 23224) (prefixPartial 10 23224) = false := by
  decide +kernel

theorem node_context_10_23224_1306549 : EJMOriginalGlobalDAGData.nodes 11 ⟨1306549, by decide⟩ =
    .split (coordinate 10) (![⟨1306406, by decide⟩,⟨1306471, by decide⟩,⟨1306523, by decide⟩,⟨1306548, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23224_1306549 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23224 ⟨1306549, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23224
    ⟨1306549, by decide⟩ (by decide) (![⟨1306406, by decide⟩,⟨1306471, by decide⟩,⟨1306523, by decide⟩,⟨1306548, by decide⟩]) unmarked_context_10_23224_1306549 node_context_10_23224_1306549
  intro a
  fin_cases a
  · exact context_11_92896_1306406
  · exact context_11_92897_1306471
  · exact context_11_92898_1306523
  · exact context_11_92899_1306548

theorem selected_cut_46808 : selected 10 ⟨1306594, by decide⟩
    (prefixPartial 11 92900) = some ⟨11, 2, 0, 1306594, 92900, 2413, 262144⟩ := by
  decide +kernel

theorem context_11_92900_1306594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92900 ⟨1306594, by decide⟩ :=
  accepted_of_selected 11 92900 ⟨1306594, by decide⟩ ⟨11, 2, 0, 1306594, 92900, 2413, 262144⟩
    (by decide) selected_cut_46808

theorem selected_cut_46809 : selected 10 ⟨1192826, by decide⟩
    (prefixPartial 11 92901) = some ⟨11, 1, 0, 1192826, 92901, 1, 262144⟩ := by
  decide +kernel

theorem context_11_92901_1192826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92901 ⟨1192826, by decide⟩ :=
  accepted_of_selected 11 92901 ⟨1192826, by decide⟩ ⟨11, 1, 0, 1192826, 92901, 1, 262144⟩
    (by decide) selected_cut_46809

theorem selected_cut_46810 : selected 10 ⟨1306628, by decide⟩
    (prefixPartial 11 92902) = some ⟨11, 2, 0, 1306628, 92902, 2217, 262144⟩ := by
  decide +kernel

theorem context_11_92902_1306628 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92902 ⟨1306628, by decide⟩ :=
  accepted_of_selected 11 92902 ⟨1306628, by decide⟩ ⟨11, 2, 0, 1306628, 92902, 2217, 262144⟩
    (by decide) selected_cut_46810

theorem selected_cut_46811 : selected 10 ⟨1306647, by decide⟩
    (prefixPartial 11 92903) = some ⟨11, 2, 0, 1306647, 92903, 1345, 262144⟩ := by
  decide +kernel

theorem context_11_92903_1306647 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92903 ⟨1306647, by decide⟩ :=
  accepted_of_selected 11 92903 ⟨1306647, by decide⟩ ⟨11, 2, 0, 1306647, 92903, 1345, 262144⟩
    (by decide) selected_cut_46811

theorem unmarked_context_10_23225_1306648 : frontier 11 ⟨1306648, by decide⟩
    (prefixCache 10 23225) (prefixPartial 10 23225) = false := by
  decide +kernel

theorem node_context_10_23225_1306648 : EJMOriginalGlobalDAGData.nodes 11 ⟨1306648, by decide⟩ =
    .split (coordinate 10) (![⟨1306594, by decide⟩,⟨1192826, by decide⟩,⟨1306628, by decide⟩,⟨1306647, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23225_1306648 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23225 ⟨1306648, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23225
    ⟨1306648, by decide⟩ (by decide) (![⟨1306594, by decide⟩,⟨1192826, by decide⟩,⟨1306628, by decide⟩,⟨1306647, by decide⟩]) unmarked_context_10_23225_1306648 node_context_10_23225_1306648
  intro a
  fin_cases a
  · exact context_11_92900_1306594
  · exact context_11_92901_1192826
  · exact context_11_92902_1306628
  · exact context_11_92903_1306647

theorem selected_cut_46812 : selected 11 ⟨1306677, by decide⟩
    (prefixPartial 10 23226) = some ⟨10, 2, 0, 1306677, 23226, 1653, 1048576⟩ := by
  decide +kernel

theorem context_10_23226_1306677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23226 ⟨1306677, by decide⟩ :=
  accepted_of_selected 10 23226 ⟨1306677, by decide⟩ ⟨10, 2, 0, 1306677, 23226, 1653, 1048576⟩
    (by decide) selected_cut_46812

theorem selected_cut_46813 : selected 10 ⟨1306720, by decide⟩
    (prefixPartial 11 92908) = some ⟨11, 2, 0, 1306720, 92908, 1405, 262144⟩ := by
  decide +kernel

theorem context_11_92908_1306720 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92908 ⟨1306720, by decide⟩ :=
  accepted_of_selected 11 92908 ⟨1306720, by decide⟩ ⟨11, 2, 0, 1306720, 92908, 1405, 262144⟩
    (by decide) selected_cut_46813

theorem selected_cut_46814 : selected 10 ⟨1306749, by decide⟩
    (prefixPartial 11 92909) = some ⟨11, 2, 0, 1306749, 92909, 1373, 262144⟩ := by
  decide +kernel

theorem context_11_92909_1306749 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92909 ⟨1306749, by decide⟩ :=
  accepted_of_selected 11 92909 ⟨1306749, by decide⟩ ⟨11, 2, 0, 1306749, 92909, 1373, 262144⟩
    (by decide) selected_cut_46814

theorem selected_cut_46815 : selected 10 ⟨1306772, by decide⟩
    (prefixPartial 11 92910) = some ⟨11, 2, 0, 1306772, 92910, 1549, 262144⟩ := by
  decide +kernel

theorem context_11_92910_1306772 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92910 ⟨1306772, by decide⟩ :=
  accepted_of_selected 11 92910 ⟨1306772, by decide⟩ ⟨11, 2, 0, 1306772, 92910, 1549, 262144⟩
    (by decide) selected_cut_46815

theorem selected_cut_46816 : selected 10 ⟨1306780, by decide⟩
    (prefixPartial 11 92911) = some ⟨11, 2, 0, 1306780, 92911, 553, 262144⟩ := by
  decide +kernel

theorem context_11_92911_1306780 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92911 ⟨1306780, by decide⟩ :=
  accepted_of_selected 11 92911 ⟨1306780, by decide⟩ ⟨11, 2, 0, 1306780, 92911, 553, 262144⟩
    (by decide) selected_cut_46816

theorem unmarked_context_10_23227_1306781 : frontier 11 ⟨1306781, by decide⟩
    (prefixCache 10 23227) (prefixPartial 10 23227) = false := by
  decide +kernel

theorem node_context_10_23227_1306781 : EJMOriginalGlobalDAGData.nodes 11 ⟨1306781, by decide⟩ =
    .split (coordinate 10) (![⟨1306720, by decide⟩,⟨1306749, by decide⟩,⟨1306772, by decide⟩,⟨1306780, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23227_1306781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23227 ⟨1306781, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23227
    ⟨1306781, by decide⟩ (by decide) (![⟨1306720, by decide⟩,⟨1306749, by decide⟩,⟨1306772, by decide⟩,⟨1306780, by decide⟩]) unmarked_context_10_23227_1306781 node_context_10_23227_1306781
  intro a
  fin_cases a
  · exact context_11_92908_1306720
  · exact context_11_92909_1306749
  · exact context_11_92910_1306772
  · exact context_11_92911_1306780

theorem unmarked_context_9_5806_1306782 : frontier 12 ⟨1306782, by decide⟩
    (prefixCache 9 5806) (prefixPartial 9 5806) = false := by
  decide +kernel

theorem node_context_9_5806_1306782 : EJMOriginalGlobalDAGData.nodes 12 ⟨1306782, by decide⟩ =
    .split (coordinate 9) (![⟨1306549, by decide⟩,⟨1306648, by decide⟩,⟨1306677, by decide⟩,⟨1306781, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5806_1306782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5806 ⟨1306782, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5806
    ⟨1306782, by decide⟩ (by decide) (![⟨1306549, by decide⟩,⟨1306648, by decide⟩,⟨1306677, by decide⟩,⟨1306781, by decide⟩]) unmarked_context_9_5806_1306782 node_context_9_5806_1306782
  intro a
  fin_cases a
  · exact context_10_23224_1306549
  · exact context_10_23225_1306648
  · exact context_10_23226_1306677
  · exact context_10_23227_1306781

theorem selected_cut_46817 : selected 10 ⟨1306799, by decide⟩
    (prefixPartial 11 92912) = some ⟨11, 2, 0, 1306799, 92912, 1133, 262144⟩ := by
  decide +kernel

theorem context_11_92912_1306799 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92912 ⟨1306799, by decide⟩ :=
  accepted_of_selected 11 92912 ⟨1306799, by decide⟩ ⟨11, 2, 0, 1306799, 92912, 1133, 262144⟩
    (by decide) selected_cut_46817

theorem selected_cut_46818 : selected 10 ⟨1306822, by decide⟩
    (prefixPartial 11 92913) = some ⟨11, 2, 0, 1306822, 92913, 1657, 262144⟩ := by
  decide +kernel

theorem context_11_92913_1306822 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92913 ⟨1306822, by decide⟩ :=
  accepted_of_selected 11 92913 ⟨1306822, by decide⟩ ⟨11, 2, 0, 1306822, 92913, 1657, 262144⟩
    (by decide) selected_cut_46818

theorem selected_cut_46819 : selected 10 ⟨1306836, by decide⟩
    (prefixPartial 11 92914) = some ⟨11, 2, 0, 1306836, 92914, 805, 262144⟩ := by
  decide +kernel

theorem context_11_92914_1306836 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92914 ⟨1306836, by decide⟩ :=
  accepted_of_selected 11 92914 ⟨1306836, by decide⟩ ⟨11, 2, 0, 1306836, 92914, 805, 262144⟩
    (by decide) selected_cut_46819

theorem selected_cut_46820 : selected 10 ⟨1306853, by decide⟩
    (prefixPartial 11 92915) = some ⟨11, 2, 0, 1306853, 92915, 1085, 262144⟩ := by
  decide +kernel

theorem context_11_92915_1306853 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92915 ⟨1306853, by decide⟩ :=
  accepted_of_selected 11 92915 ⟨1306853, by decide⟩ ⟨11, 2, 0, 1306853, 92915, 1085, 262144⟩
    (by decide) selected_cut_46820

theorem unmarked_context_10_23228_1306854 : frontier 11 ⟨1306854, by decide⟩
    (prefixCache 10 23228) (prefixPartial 10 23228) = false := by
  decide +kernel

theorem node_context_10_23228_1306854 : EJMOriginalGlobalDAGData.nodes 11 ⟨1306854, by decide⟩ =
    .split (coordinate 10) (![⟨1306799, by decide⟩,⟨1306822, by decide⟩,⟨1306836, by decide⟩,⟨1306853, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23228_1306854 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23228 ⟨1306854, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23228
    ⟨1306854, by decide⟩ (by decide) (![⟨1306799, by decide⟩,⟨1306822, by decide⟩,⟨1306836, by decide⟩,⟨1306853, by decide⟩]) unmarked_context_10_23228_1306854 node_context_10_23228_1306854
  intro a
  fin_cases a
  · exact context_11_92912_1306799
  · exact context_11_92913_1306822
  · exact context_11_92914_1306836
  · exact context_11_92915_1306853

theorem selected_cut_46821 : selected 11 ⟨1306902, by decide⟩
    (prefixPartial 10 23229) = some ⟨10, 2, 0, 1306902, 23229, 2693, 1048576⟩ := by
  decide +kernel

theorem context_10_23229_1306902 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23229 ⟨1306902, by decide⟩ :=
  accepted_of_selected 10 23229 ⟨1306902, by decide⟩ ⟨10, 2, 0, 1306902, 23229, 2693, 1048576⟩
    (by decide) selected_cut_46821

theorem selected_cut_46822 : selected 11 ⟨1306936, by decide⟩
    (prefixPartial 10 23230) = some ⟨10, 2, 0, 1306936, 23230, 1089, 1048576⟩ := by
  decide +kernel

theorem context_10_23230_1306936 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23230 ⟨1306936, by decide⟩ :=
  accepted_of_selected 10 23230 ⟨1306936, by decide⟩ ⟨10, 2, 0, 1306936, 23230, 1089, 1048576⟩
    (by decide) selected_cut_46822

theorem selected_cut_46823 : selected 11 ⟨1306952, by decide⟩
    (prefixPartial 10 23231) = some ⟨10, 2, 0, 1306952, 23231, 193, 1048576⟩ := by
  decide +kernel

theorem context_10_23231_1306952 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23231 ⟨1306952, by decide⟩ :=
  accepted_of_selected 10 23231 ⟨1306952, by decide⟩ ⟨10, 2, 0, 1306952, 23231, 193, 1048576⟩
    (by decide) selected_cut_46823

theorem unmarked_context_9_5807_1306953 : frontier 12 ⟨1306953, by decide⟩
    (prefixCache 9 5807) (prefixPartial 9 5807) = false := by
  decide +kernel

theorem node_context_9_5807_1306953 : EJMOriginalGlobalDAGData.nodes 12 ⟨1306953, by decide⟩ =
    .split (coordinate 9) (![⟨1306854, by decide⟩,⟨1306902, by decide⟩,⟨1306936, by decide⟩,⟨1306952, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5807_1306953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5807 ⟨1306953, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5807
    ⟨1306953, by decide⟩ (by decide) (![⟨1306854, by decide⟩,⟨1306902, by decide⟩,⟨1306936, by decide⟩,⟨1306952, by decide⟩]) unmarked_context_9_5807_1306953 node_context_9_5807_1306953
  intro a
  fin_cases a
  · exact context_10_23228_1306854
  · exact context_10_23229_1306902
  · exact context_10_23230_1306936
  · exact context_10_23231_1306952

theorem unmarked_context_8_1451_1306954 : frontier 13 ⟨1306954, by decide⟩
    (prefixCache 8 1451) (prefixPartial 8 1451) = false := by
  decide +kernel

theorem node_context_8_1451_1306954 : EJMOriginalGlobalDAGData.nodes 13 ⟨1306954, by decide⟩ =
    .split (coordinate 8) (![⟨1305617, by decide⟩,⟨1306371, by decide⟩,⟨1306782, by decide⟩,⟨1306953, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1451_1306954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1451 ⟨1306954, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1451
    ⟨1306954, by decide⟩ (by decide) (![⟨1305617, by decide⟩,⟨1306371, by decide⟩,⟨1306782, by decide⟩,⟨1306953, by decide⟩]) unmarked_context_8_1451_1306954 node_context_8_1451_1306954
  intro a
  fin_cases a
  · exact context_9_5804_1305617
  · exact context_9_5805_1306371
  · exact context_9_5806_1306782
  · exact context_9_5807_1306953

theorem unmarked_context_7_362_1306955 : frontier 14 ⟨1306955, by decide⟩
    (prefixCache 7 362) (prefixPartial 7 362) = false := by
  decide +kernel

theorem node_context_7_362_1306955 : EJMOriginalGlobalDAGData.nodes 14 ⟨1306955, by decide⟩ =
    .split (coordinate 7) (![⟨1297457, by decide⟩,⟨1300531, by decide⟩,⟨1303668, by decide⟩,⟨1306954, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_362_1306955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 362 ⟨1306955, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 362
    ⟨1306955, by decide⟩ (by decide) (![⟨1297457, by decide⟩,⟨1300531, by decide⟩,⟨1303668, by decide⟩,⟨1306954, by decide⟩]) unmarked_context_7_362_1306955 node_context_7_362_1306955
  intro a
  fin_cases a
  · exact context_8_1448_1297457
  · exact context_8_1449_1300531
  · exact context_8_1450_1303668
  · exact context_8_1451_1306954

theorem selected_cut_46824 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 92928) = some ⟨11, 1, 0, 434745, 92928, 1, 262144⟩ := by
  decide +kernel

theorem context_11_92928_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92928 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 92928 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 92928, 1, 262144⟩
    (by decide) selected_cut_46824

theorem selected_cut_46825 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 371716) = some ⟨12, 1, 0, 448748, 371716, 1, 65536⟩ := by
  decide +kernel

theorem context_12_371716_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371716 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 371716 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 371716, 1, 65536⟩
    (by decide) selected_cut_46825

theorem selected_cut_46826 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 371717) = some ⟨12, 1, 0, 34034, 371717, 1, 65536⟩ := by
  decide +kernel

theorem context_12_371717_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371717 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 371717 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 371717, 1, 65536⟩
    (by decide) selected_cut_46826

theorem selected_cut_46827 : selected 9 ⟨1307040, by decide⟩
    (prefixPartial 12 371718) = some ⟨12, 2, 0, 1307040, 371718, 3585, 65536⟩ := by
  decide +kernel

theorem context_12_371718_1307040 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371718 ⟨1307040, by decide⟩ :=
  accepted_of_selected 12 371718 ⟨1307040, by decide⟩ ⟨12, 2, 0, 1307040, 371718, 3585, 65536⟩
    (by decide) selected_cut_46827

theorem selected_cut_46828 : selected 9 ⟨1307135, by decide⟩
    (prefixPartial 12 371719) = some ⟨12, 2, 0, 1307135, 371719, 2365, 65536⟩ := by
  decide +kernel

theorem context_12_371719_1307135 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371719 ⟨1307135, by decide⟩ :=
  accepted_of_selected 12 371719 ⟨1307135, by decide⟩ ⟨12, 2, 0, 1307135, 371719, 2365, 65536⟩
    (by decide) selected_cut_46828

theorem unmarked_context_11_92929_1307136 : frontier 10 ⟨1307136, by decide⟩
    (prefixCache 11 92929) (prefixPartial 11 92929) = false := by
  decide +kernel

theorem node_context_11_92929_1307136 : EJMOriginalGlobalDAGData.nodes 10 ⟨1307136, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1307040, by decide⟩,⟨1307135, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92929_1307136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92929 ⟨1307136, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92929
    ⟨1307136, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1307040, by decide⟩,⟨1307135, by decide⟩]) unmarked_context_11_92929_1307136 node_context_11_92929_1307136
  intro a
  fin_cases a
  · exact context_12_371716_448748
  · exact context_12_371717_34034
  · exact context_12_371718_1307040
  · exact context_12_371719_1307135

theorem selected_cut_46829 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 371720) = some ⟨12, 1, 0, 448748, 371720, 1, 65536⟩ := by
  decide +kernel

theorem context_12_371720_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371720 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 371720 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 371720, 1, 65536⟩
    (by decide) selected_cut_46829

theorem selected_cut_46830 : selected 9 ⟨1307253, by decide⟩
    (prefixPartial 12 371721) = some ⟨12, 2, 0, 1307253, 371721, 3937, 65536⟩ := by
  decide +kernel

theorem context_12_371721_1307253 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371721 ⟨1307253, by decide⟩ :=
  accepted_of_selected 12 371721 ⟨1307253, by decide⟩ ⟨12, 2, 0, 1307253, 371721, 3937, 65536⟩
    (by decide) selected_cut_46830

theorem selected_cut_46831 : selected 9 ⟨1307254, by decide⟩
    (prefixPartial 12 371722) = some ⟨12, 1, 0, 1307254, 371722, 1, 65536⟩ := by
  decide +kernel

theorem context_12_371722_1307254 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371722 ⟨1307254, by decide⟩ :=
  accepted_of_selected 12 371722 ⟨1307254, by decide⟩ ⟨12, 1, 0, 1307254, 371722, 1, 65536⟩
    (by decide) selected_cut_46831

theorem selected_cut_46832 : selected 9 ⟨1307339, by decide⟩
    (prefixPartial 12 371723) = some ⟨12, 2, 0, 1307339, 371723, 4073, 65536⟩ := by
  decide +kernel

theorem context_12_371723_1307339 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371723 ⟨1307339, by decide⟩ :=
  accepted_of_selected 12 371723 ⟨1307339, by decide⟩ ⟨12, 2, 0, 1307339, 371723, 4073, 65536⟩
    (by decide) selected_cut_46832

theorem unmarked_context_11_92930_1307340 : frontier 10 ⟨1307340, by decide⟩
    (prefixCache 11 92930) (prefixPartial 11 92930) = false := by
  decide +kernel

theorem node_context_11_92930_1307340 : EJMOriginalGlobalDAGData.nodes 10 ⟨1307340, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1307253, by decide⟩,⟨1307254, by decide⟩,⟨1307339, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92930_1307340 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92930 ⟨1307340, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92930
    ⟨1307340, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1307253, by decide⟩,⟨1307254, by decide⟩,⟨1307339, by decide⟩]) unmarked_context_11_92930_1307340 node_context_11_92930_1307340
  intro a
  fin_cases a
  · exact context_12_371720_448748
  · exact context_12_371721_1307253
  · exact context_12_371722_1307254
  · exact context_12_371723_1307339

theorem selected_cut_46833 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 371724) = some ⟨12, 1, 0, 448748, 371724, 1, 65536⟩ := by
  decide +kernel

theorem context_12_371724_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371724 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 371724 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 371724, 1, 65536⟩
    (by decide) selected_cut_46833

theorem selected_cut_46834 : selected 9 ⟨1307412, by decide⟩
    (prefixPartial 12 371725) = some ⟨12, 2, 0, 1307412, 371725, 3357, 65536⟩ := by
  decide +kernel

theorem context_12_371725_1307412 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371725 ⟨1307412, by decide⟩ :=
  accepted_of_selected 12 371725 ⟨1307412, by decide⟩ ⟨12, 2, 0, 1307412, 371725, 3357, 65536⟩
    (by decide) selected_cut_46834

theorem selected_cut_46835 : selected 9 ⟨1307471, by decide⟩
    (prefixPartial 12 371726) = some ⟨12, 2, 0, 1307471, 371726, 3037, 65536⟩ := by
  decide +kernel

theorem context_12_371726_1307471 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371726 ⟨1307471, by decide⟩ :=
  accepted_of_selected 12 371726 ⟨1307471, by decide⟩ ⟨12, 2, 0, 1307471, 371726, 3037, 65536⟩
    (by decide) selected_cut_46835

theorem selected_cut_46836 : selected 9 ⟨760511, by decide⟩
    (prefixPartial 12 371727) = some ⟨12, 1, 0, 760511, 371727, 1, 65536⟩ := by
  decide +kernel

theorem context_12_371727_760511 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371727 ⟨760511, by decide⟩ :=
  accepted_of_selected 12 371727 ⟨760511, by decide⟩ ⟨12, 1, 0, 760511, 371727, 1, 65536⟩
    (by decide) selected_cut_46836

theorem unmarked_context_11_92931_1307472 : frontier 10 ⟨1307472, by decide⟩
    (prefixCache 11 92931) (prefixPartial 11 92931) = false := by
  decide +kernel

theorem node_context_11_92931_1307472 : EJMOriginalGlobalDAGData.nodes 10 ⟨1307472, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1307412, by decide⟩,⟨1307471, by decide⟩,⟨760511, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92931_1307472 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92931 ⟨1307472, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92931
    ⟨1307472, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1307412, by decide⟩,⟨1307471, by decide⟩,⟨760511, by decide⟩]) unmarked_context_11_92931_1307472 node_context_11_92931_1307472
  intro a
  fin_cases a
  · exact context_12_371724_448748
  · exact context_12_371725_1307412
  · exact context_12_371726_1307471
  · exact context_12_371727_760511

theorem unmarked_context_10_23232_1307473 : frontier 11 ⟨1307473, by decide⟩
    (prefixCache 10 23232) (prefixPartial 10 23232) = false := by
  decide +kernel

theorem node_context_10_23232_1307473 : EJMOriginalGlobalDAGData.nodes 11 ⟨1307473, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨1307136, by decide⟩,⟨1307340, by decide⟩,⟨1307472, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23232_1307473 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23232 ⟨1307473, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23232
    ⟨1307473, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨1307136, by decide⟩,⟨1307340, by decide⟩,⟨1307472, by decide⟩]) unmarked_context_10_23232_1307473 node_context_10_23232_1307473
  intro a
  fin_cases a
  · exact context_11_92928_434745
  · exact context_11_92929_1307136
  · exact context_11_92930_1307340
  · exact context_11_92931_1307472

theorem selected_cut_46837 : selected 9 ⟨985390, by decide⟩
    (prefixPartial 12 371728) = some ⟨12, 1, 0, 985390, 371728, 1, 65536⟩ := by
  decide +kernel

theorem context_12_371728_985390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371728 ⟨985390, by decide⟩ :=
  accepted_of_selected 12 371728 ⟨985390, by decide⟩ ⟨12, 1, 0, 985390, 371728, 1, 65536⟩
    (by decide) selected_cut_46837

theorem selected_cut_46838 : selected 9 ⟨1307526, by decide⟩
    (prefixPartial 12 371729) = some ⟨12, 2, 0, 1307526, 371729, 3061, 65536⟩ := by
  decide +kernel

theorem context_12_371729_1307526 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371729 ⟨1307526, by decide⟩ :=
  accepted_of_selected 12 371729 ⟨1307526, by decide⟩ ⟨12, 2, 0, 1307526, 371729, 3061, 65536⟩
    (by decide) selected_cut_46838

theorem selected_cut_46839 : selected 9 ⟨1307581, by decide⟩
    (prefixPartial 12 371730) = some ⟨12, 2, 0, 1307581, 371730, 2725, 65536⟩ := by
  decide +kernel

theorem context_12_371730_1307581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371730 ⟨1307581, by decide⟩ :=
  accepted_of_selected 12 371730 ⟨1307581, by decide⟩ ⟨12, 2, 0, 1307581, 371730, 2725, 65536⟩
    (by decide) selected_cut_46839

theorem selected_cut_46840 : selected 9 ⟨1307641, by decide⟩
    (prefixPartial 12 371731) = some ⟨12, 2, 0, 1307641, 371731, 3245, 65536⟩ := by
  decide +kernel

theorem context_12_371731_1307641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371731 ⟨1307641, by decide⟩ :=
  accepted_of_selected 12 371731 ⟨1307641, by decide⟩ ⟨12, 2, 0, 1307641, 371731, 3245, 65536⟩
    (by decide) selected_cut_46840

theorem unmarked_context_11_92932_1307642 : frontier 10 ⟨1307642, by decide⟩
    (prefixCache 11 92932) (prefixPartial 11 92932) = false := by
  decide +kernel

theorem node_context_11_92932_1307642 : EJMOriginalGlobalDAGData.nodes 10 ⟨1307642, by decide⟩ =
    .split (coordinate 11) (![⟨985390, by decide⟩,⟨1307526, by decide⟩,⟨1307581, by decide⟩,⟨1307641, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92932_1307642 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92932 ⟨1307642, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92932
    ⟨1307642, by decide⟩ (by decide) (![⟨985390, by decide⟩,⟨1307526, by decide⟩,⟨1307581, by decide⟩,⟨1307641, by decide⟩]) unmarked_context_11_92932_1307642 node_context_11_92932_1307642
  intro a
  fin_cases a
  · exact context_12_371728_985390
  · exact context_12_371729_1307526
  · exact context_12_371730_1307581
  · exact context_12_371731_1307641

theorem selected_cut_46841 : selected 9 ⟨1307719, by decide⟩
    (prefixPartial 12 371732) = some ⟨12, 2, 0, 1307719, 371732, 3513, 65536⟩ := by
  decide +kernel

theorem context_12_371732_1307719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371732 ⟨1307719, by decide⟩ :=
  accepted_of_selected 12 371732 ⟨1307719, by decide⟩ ⟨12, 2, 0, 1307719, 371732, 3513, 65536⟩
    (by decide) selected_cut_46841

theorem selected_cut_46842 : selected 9 ⟨1172003, by decide⟩
    (prefixPartial 12 371733) = some ⟨12, 1, 0, 1172003, 371733, 1, 65536⟩ := by
  decide +kernel

theorem context_12_371733_1172003 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371733 ⟨1172003, by decide⟩ :=
  accepted_of_selected 12 371733 ⟨1172003, by decide⟩ ⟨12, 1, 0, 1172003, 371733, 1, 65536⟩
    (by decide) selected_cut_46842

theorem selected_cut_46843 : selected 9 ⟨1307784, by decide⟩
    (prefixPartial 12 371734) = some ⟨12, 2, 0, 1307784, 371734, 3209, 65536⟩ := by
  decide +kernel

theorem context_12_371734_1307784 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371734 ⟨1307784, by decide⟩ :=
  accepted_of_selected 12 371734 ⟨1307784, by decide⟩ ⟨12, 2, 0, 1307784, 371734, 3209, 65536⟩
    (by decide) selected_cut_46843

theorem selected_cut_46844 : selected 9 ⟨976576, by decide⟩
    (prefixPartial 12 371735) = some ⟨12, 1, 0, 976576, 371735, 1, 65536⟩ := by
  decide +kernel

theorem context_12_371735_976576 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371735 ⟨976576, by decide⟩ :=
  accepted_of_selected 12 371735 ⟨976576, by decide⟩ ⟨12, 1, 0, 976576, 371735, 1, 65536⟩
    (by decide) selected_cut_46844

theorem unmarked_context_11_92933_1307785 : frontier 10 ⟨1307785, by decide⟩
    (prefixCache 11 92933) (prefixPartial 11 92933) = false := by
  decide +kernel

theorem node_context_11_92933_1307785 : EJMOriginalGlobalDAGData.nodes 10 ⟨1307785, by decide⟩ =
    .split (coordinate 11) (![⟨1307719, by decide⟩,⟨1172003, by decide⟩,⟨1307784, by decide⟩,⟨976576, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92933_1307785 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92933 ⟨1307785, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92933
    ⟨1307785, by decide⟩ (by decide) (![⟨1307719, by decide⟩,⟨1172003, by decide⟩,⟨1307784, by decide⟩,⟨976576, by decide⟩]) unmarked_context_11_92933_1307785 node_context_11_92933_1307785
  intro a
  fin_cases a
  · exact context_12_371732_1307719
  · exact context_12_371733_1172003
  · exact context_12_371734_1307784
  · exact context_12_371735_976576

theorem selected_cut_46845 : selected 9 ⟨994572, by decide⟩
    (prefixPartial 12 371736) = some ⟨12, 1, 0, 994572, 371736, 1, 65536⟩ := by
  decide +kernel

theorem context_12_371736_994572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371736 ⟨994572, by decide⟩ :=
  accepted_of_selected 12 371736 ⟨994572, by decide⟩ ⟨12, 1, 0, 994572, 371736, 1, 65536⟩
    (by decide) selected_cut_46845

theorem selected_cut_46846 : selected 9 ⟨1307843, by decide⟩
    (prefixPartial 12 371737) = some ⟨12, 2, 0, 1307843, 371737, 3249, 65536⟩ := by
  decide +kernel

theorem context_12_371737_1307843 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371737 ⟨1307843, by decide⟩ :=
  accepted_of_selected 12 371737 ⟨1307843, by decide⟩ ⟨12, 2, 0, 1307843, 371737, 3249, 65536⟩
    (by decide) selected_cut_46846

theorem selected_cut_46847 : selected 9 ⟨806997, by decide⟩
    (prefixPartial 12 371738) = some ⟨12, 1, 0, 806997, 371738, 1, 65536⟩ := by
  decide +kernel

theorem context_12_371738_806997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371738 ⟨806997, by decide⟩ :=
  accepted_of_selected 12 371738 ⟨806997, by decide⟩ ⟨12, 1, 0, 806997, 371738, 1, 65536⟩
    (by decide) selected_cut_46847

theorem selected_cut_46848 : selected 9 ⟨1307914, by decide⟩
    (prefixPartial 12 371739) = some ⟨12, 2, 0, 1307914, 371739, 3577, 65536⟩ := by
  decide +kernel

theorem context_12_371739_1307914 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371739 ⟨1307914, by decide⟩ :=
  accepted_of_selected 12 371739 ⟨1307914, by decide⟩ ⟨12, 2, 0, 1307914, 371739, 3577, 65536⟩
    (by decide) selected_cut_46848

theorem unmarked_context_11_92934_1307915 : frontier 10 ⟨1307915, by decide⟩
    (prefixCache 11 92934) (prefixPartial 11 92934) = false := by
  decide +kernel

theorem node_context_11_92934_1307915 : EJMOriginalGlobalDAGData.nodes 10 ⟨1307915, by decide⟩ =
    .split (coordinate 11) (![⟨994572, by decide⟩,⟨1307843, by decide⟩,⟨806997, by decide⟩,⟨1307914, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92934_1307915 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92934 ⟨1307915, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92934
    ⟨1307915, by decide⟩ (by decide) (![⟨994572, by decide⟩,⟨1307843, by decide⟩,⟨806997, by decide⟩,⟨1307914, by decide⟩]) unmarked_context_11_92934_1307915 node_context_11_92934_1307915
  intro a
  fin_cases a
  · exact context_12_371736_994572
  · exact context_12_371737_1307843
  · exact context_12_371738_806997
  · exact context_12_371739_1307914

theorem selected_cut_46849 : selected 9 ⟨1307971, by decide⟩
    (prefixPartial 12 371740) = some ⟨12, 2, 0, 1307971, 371740, 2813, 65536⟩ := by
  decide +kernel

theorem context_12_371740_1307971 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371740 ⟨1307971, by decide⟩ :=
  accepted_of_selected 12 371740 ⟨1307971, by decide⟩ ⟨12, 2, 0, 1307971, 371740, 2813, 65536⟩
    (by decide) selected_cut_46849

theorem selected_cut_46850 : selected 9 ⟨1308028, by decide⟩
    (prefixPartial 12 371741) = some ⟨12, 2, 0, 1308028, 371741, 3009, 65536⟩ := by
  decide +kernel

theorem context_12_371741_1308028 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371741 ⟨1308028, by decide⟩ :=
  accepted_of_selected 12 371741 ⟨1308028, by decide⟩ ⟨12, 2, 0, 1308028, 371741, 3009, 65536⟩
    (by decide) selected_cut_46850

theorem selected_cut_46851 : selected 9 ⟨1308090, by decide⟩
    (prefixPartial 12 371742) = some ⟨12, 2, 0, 1308090, 371742, 2825, 65536⟩ := by
  decide +kernel

theorem context_12_371742_1308090 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371742 ⟨1308090, by decide⟩ :=
  accepted_of_selected 12 371742 ⟨1308090, by decide⟩ ⟨12, 2, 0, 1308090, 371742, 2825, 65536⟩
    (by decide) selected_cut_46851

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
