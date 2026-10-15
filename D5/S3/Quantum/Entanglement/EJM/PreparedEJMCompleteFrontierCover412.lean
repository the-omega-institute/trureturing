/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover411
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_10_19217_1073548 : frontier 11 ⟨1073548, by decide⟩
    (prefixCache 10 19217) (prefixPartial 10 19217) = false := by
  decide +kernel

theorem node_context_10_19217_1073548 : EJMOriginalGlobalDAGData.nodes 11 ⟨1073548, by decide⟩ =
    .split (coordinate 10) (![⟨1073055, by decide⟩,⟨1073186, by decide⟩,⟨1073345, by decide⟩,⟨1073547, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19217_1073548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19217 ⟨1073548, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19217
    ⟨1073548, by decide⟩ (by decide) (![⟨1073055, by decide⟩,⟨1073186, by decide⟩,⟨1073345, by decide⟩,⟨1073547, by decide⟩]) unmarked_context_10_19217_1073548 node_context_10_19217_1073548
  intro a
  fin_cases a
  · exact context_11_76868_1073055
  · exact context_11_76869_1073186
  · exact context_11_76870_1073345
  · exact context_11_76871_1073547

theorem selected_cut_39555 : selected 9 ⟨1072955, by decide⟩
    (prefixPartial 12 307488) = some ⟨12, 1, 0, 1072955, 307488, 1, 65536⟩ := by
  decide +kernel

theorem context_12_307488_1072955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307488 ⟨1072955, by decide⟩ :=
  accepted_of_selected 12 307488 ⟨1072955, by decide⟩ ⟨12, 1, 0, 1072955, 307488, 1, 65536⟩
    (by decide) selected_cut_39555

theorem selected_cut_39556 : selected 9 ⟨1073577, by decide⟩
    (prefixPartial 12 307489) = some ⟨12, 2, 0, 1073577, 307489, 2565, 65536⟩ := by
  decide +kernel

theorem context_12_307489_1073577 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307489 ⟨1073577, by decide⟩ :=
  accepted_of_selected 12 307489 ⟨1073577, by decide⟩ ⟨12, 2, 0, 1073577, 307489, 2565, 65536⟩
    (by decide) selected_cut_39556

theorem selected_cut_39557 : selected 9 ⟨1073606, by decide⟩
    (prefixPartial 12 307490) = some ⟨12, 2, 0, 1073606, 307490, 2389, 65536⟩ := by
  decide +kernel

theorem context_12_307490_1073606 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307490 ⟨1073606, by decide⟩ :=
  accepted_of_selected 12 307490 ⟨1073606, by decide⟩ ⟨12, 2, 0, 1073606, 307490, 2389, 65536⟩
    (by decide) selected_cut_39557

theorem selected_cut_39558 : selected 9 ⟨1073638, by decide⟩
    (prefixPartial 12 307491) = some ⟨12, 2, 0, 1073638, 307491, 2513, 65536⟩ := by
  decide +kernel

theorem context_12_307491_1073638 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307491 ⟨1073638, by decide⟩ :=
  accepted_of_selected 12 307491 ⟨1073638, by decide⟩ ⟨12, 2, 0, 1073638, 307491, 2513, 65536⟩
    (by decide) selected_cut_39558

theorem unmarked_context_11_76872_1073639 : frontier 10 ⟨1073639, by decide⟩
    (prefixCache 11 76872) (prefixPartial 11 76872) = false := by
  decide +kernel

theorem node_context_11_76872_1073639 : EJMOriginalGlobalDAGData.nodes 10 ⟨1073639, by decide⟩ =
    .split (coordinate 11) (![⟨1072955, by decide⟩,⟨1073577, by decide⟩,⟨1073606, by decide⟩,⟨1073638, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76872_1073639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76872 ⟨1073639, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76872
    ⟨1073639, by decide⟩ (by decide) (![⟨1072955, by decide⟩,⟨1073577, by decide⟩,⟨1073606, by decide⟩,⟨1073638, by decide⟩]) unmarked_context_11_76872_1073639 node_context_11_76872_1073639
  intro a
  fin_cases a
  · exact context_12_307488_1072955
  · exact context_12_307489_1073577
  · exact context_12_307490_1073606
  · exact context_12_307491_1073638

theorem selected_cut_39559 : selected 9 ⟨1073692, by decide⟩
    (prefixPartial 12 307492) = some ⟨12, 2, 0, 1073692, 307492, 3417, 65536⟩ := by
  decide +kernel

theorem context_12_307492_1073692 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307492 ⟨1073692, by decide⟩ :=
  accepted_of_selected 12 307492 ⟨1073692, by decide⟩ ⟨12, 2, 0, 1073692, 307492, 3417, 65536⟩
    (by decide) selected_cut_39559

theorem selected_cut_39560 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 307493) = some ⟨12, 1, 0, 891951, 307493, 1, 65536⟩ := by
  decide +kernel

theorem context_12_307493_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307493 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 307493 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 307493, 1, 65536⟩
    (by decide) selected_cut_39560

theorem selected_cut_39561 : selected 9 ⟨1073730, by decide⟩
    (prefixPartial 12 307494) = some ⟨12, 2, 0, 1073730, 307494, 2853, 65536⟩ := by
  decide +kernel

theorem context_12_307494_1073730 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307494 ⟨1073730, by decide⟩ :=
  accepted_of_selected 12 307494 ⟨1073730, by decide⟩ ⟨12, 2, 0, 1073730, 307494, 2853, 65536⟩
    (by decide) selected_cut_39561

theorem selected_cut_39562 : selected 9 ⟨1073766, by decide⟩
    (prefixPartial 12 307495) = some ⟨12, 2, 0, 1073766, 307495, 2813, 65536⟩ := by
  decide +kernel

theorem context_12_307495_1073766 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307495 ⟨1073766, by decide⟩ :=
  accepted_of_selected 12 307495 ⟨1073766, by decide⟩ ⟨12, 2, 0, 1073766, 307495, 2813, 65536⟩
    (by decide) selected_cut_39562

theorem unmarked_context_11_76873_1073767 : frontier 10 ⟨1073767, by decide⟩
    (prefixCache 11 76873) (prefixPartial 11 76873) = false := by
  decide +kernel

theorem node_context_11_76873_1073767 : EJMOriginalGlobalDAGData.nodes 10 ⟨1073767, by decide⟩ =
    .split (coordinate 11) (![⟨1073692, by decide⟩,⟨891951, by decide⟩,⟨1073730, by decide⟩,⟨1073766, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76873_1073767 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76873 ⟨1073767, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76873
    ⟨1073767, by decide⟩ (by decide) (![⟨1073692, by decide⟩,⟨891951, by decide⟩,⟨1073730, by decide⟩,⟨1073766, by decide⟩]) unmarked_context_11_76873_1073767 node_context_11_76873_1073767
  intro a
  fin_cases a
  · exact context_12_307492_1073692
  · exact context_12_307493_891951
  · exact context_12_307494_1073730
  · exact context_12_307495_1073766

theorem selected_cut_39563 : selected 9 ⟨1073811, by decide⟩
    (prefixPartial 12 307496) = some ⟨12, 2, 0, 1073811, 307496, 2917, 65536⟩ := by
  decide +kernel

theorem context_12_307496_1073811 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307496 ⟨1073811, by decide⟩ :=
  accepted_of_selected 12 307496 ⟨1073811, by decide⟩ ⟨12, 2, 0, 1073811, 307496, 2917, 65536⟩
    (by decide) selected_cut_39563

theorem selected_cut_39564 : selected 9 ⟨1073845, by decide⟩
    (prefixPartial 12 307497) = some ⟨12, 2, 0, 1073845, 307497, 2653, 65536⟩ := by
  decide +kernel

theorem context_12_307497_1073845 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307497 ⟨1073845, by decide⟩ :=
  accepted_of_selected 12 307497 ⟨1073845, by decide⟩ ⟨12, 2, 0, 1073845, 307497, 2653, 65536⟩
    (by decide) selected_cut_39564

theorem selected_cut_39565 : selected 9 ⟨101803, by decide⟩
    (prefixPartial 12 307498) = some ⟨12, 1, 0, 101803, 307498, 1, 65536⟩ := by
  decide +kernel

theorem context_12_307498_101803 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307498 ⟨101803, by decide⟩ :=
  accepted_of_selected 12 307498 ⟨101803, by decide⟩ ⟨12, 1, 0, 101803, 307498, 1, 65536⟩
    (by decide) selected_cut_39565

theorem selected_cut_39566 : selected 9 ⟨1073881, by decide⟩
    (prefixPartial 12 307499) = some ⟨12, 2, 0, 1073881, 307499, 2593, 65536⟩ := by
  decide +kernel

theorem context_12_307499_1073881 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307499 ⟨1073881, by decide⟩ :=
  accepted_of_selected 12 307499 ⟨1073881, by decide⟩ ⟨12, 2, 0, 1073881, 307499, 2593, 65536⟩
    (by decide) selected_cut_39566

theorem unmarked_context_11_76874_1073882 : frontier 10 ⟨1073882, by decide⟩
    (prefixCache 11 76874) (prefixPartial 11 76874) = false := by
  decide +kernel

theorem node_context_11_76874_1073882 : EJMOriginalGlobalDAGData.nodes 10 ⟨1073882, by decide⟩ =
    .split (coordinate 11) (![⟨1073811, by decide⟩,⟨1073845, by decide⟩,⟨101803, by decide⟩,⟨1073881, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76874_1073882 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76874 ⟨1073882, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76874
    ⟨1073882, by decide⟩ (by decide) (![⟨1073811, by decide⟩,⟨1073845, by decide⟩,⟨101803, by decide⟩,⟨1073881, by decide⟩]) unmarked_context_11_76874_1073882 node_context_11_76874_1073882
  intro a
  fin_cases a
  · exact context_12_307496_1073811
  · exact context_12_307497_1073845
  · exact context_12_307498_101803
  · exact context_12_307499_1073881

theorem selected_cut_39567 : selected 9 ⟨1073933, by decide⟩
    (prefixPartial 12 307500) = some ⟨12, 2, 0, 1073933, 307500, 3265, 65536⟩ := by
  decide +kernel

theorem context_12_307500_1073933 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307500 ⟨1073933, by decide⟩ :=
  accepted_of_selected 12 307500 ⟨1073933, by decide⟩ ⟨12, 2, 0, 1073933, 307500, 3265, 65536⟩
    (by decide) selected_cut_39567

theorem selected_cut_39568 : selected 9 ⟨1073974, by decide⟩
    (prefixPartial 12 307501) = some ⟨12, 2, 0, 1073974, 307501, 2865, 65536⟩ := by
  decide +kernel

theorem context_12_307501_1073974 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307501 ⟨1073974, by decide⟩ :=
  accepted_of_selected 12 307501 ⟨1073974, by decide⟩ ⟨12, 2, 0, 1073974, 307501, 2865, 65536⟩
    (by decide) selected_cut_39568

theorem selected_cut_39569 : selected 9 ⟨1074016, by decide⟩
    (prefixPartial 12 307502) = some ⟨12, 2, 0, 1074016, 307502, 2789, 65536⟩ := by
  decide +kernel

theorem context_12_307502_1074016 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307502 ⟨1074016, by decide⟩ :=
  accepted_of_selected 12 307502 ⟨1074016, by decide⟩ ⟨12, 2, 0, 1074016, 307502, 2789, 65536⟩
    (by decide) selected_cut_39569

theorem selected_cut_39570 : selected 9 ⟨1074054, by decide⟩
    (prefixPartial 12 307503) = some ⟨12, 2, 0, 1074054, 307503, 2801, 65536⟩ := by
  decide +kernel

theorem context_12_307503_1074054 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307503 ⟨1074054, by decide⟩ :=
  accepted_of_selected 12 307503 ⟨1074054, by decide⟩ ⟨12, 2, 0, 1074054, 307503, 2801, 65536⟩
    (by decide) selected_cut_39570

theorem unmarked_context_11_76875_1074055 : frontier 10 ⟨1074055, by decide⟩
    (prefixCache 11 76875) (prefixPartial 11 76875) = false := by
  decide +kernel

theorem node_context_11_76875_1074055 : EJMOriginalGlobalDAGData.nodes 10 ⟨1074055, by decide⟩ =
    .split (coordinate 11) (![⟨1073933, by decide⟩,⟨1073974, by decide⟩,⟨1074016, by decide⟩,⟨1074054, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76875_1074055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76875 ⟨1074055, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76875
    ⟨1074055, by decide⟩ (by decide) (![⟨1073933, by decide⟩,⟨1073974, by decide⟩,⟨1074016, by decide⟩,⟨1074054, by decide⟩]) unmarked_context_11_76875_1074055 node_context_11_76875_1074055
  intro a
  fin_cases a
  · exact context_12_307500_1073933
  · exact context_12_307501_1073974
  · exact context_12_307502_1074016
  · exact context_12_307503_1074054

theorem unmarked_context_10_19218_1074056 : frontier 11 ⟨1074056, by decide⟩
    (prefixCache 10 19218) (prefixPartial 10 19218) = false := by
  decide +kernel

theorem node_context_10_19218_1074056 : EJMOriginalGlobalDAGData.nodes 11 ⟨1074056, by decide⟩ =
    .split (coordinate 10) (![⟨1073639, by decide⟩,⟨1073767, by decide⟩,⟨1073882, by decide⟩,⟨1074055, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19218_1074056 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19218 ⟨1074056, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19218
    ⟨1074056, by decide⟩ (by decide) (![⟨1073639, by decide⟩,⟨1073767, by decide⟩,⟨1073882, by decide⟩,⟨1074055, by decide⟩]) unmarked_context_10_19218_1074056 node_context_10_19218_1074056
  intro a
  fin_cases a
  · exact context_11_76872_1073639
  · exact context_11_76873_1073767
  · exact context_11_76874_1073882
  · exact context_11_76875_1074055

theorem selected_cut_39571 : selected 9 ⟨1074097, by decide⟩
    (prefixPartial 12 307504) = some ⟨12, 2, 0, 1074097, 307504, 1205, 65536⟩ := by
  decide +kernel

theorem context_12_307504_1074097 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307504 ⟨1074097, by decide⟩ :=
  accepted_of_selected 12 307504 ⟨1074097, by decide⟩ ⟨12, 2, 0, 1074097, 307504, 1205, 65536⟩
    (by decide) selected_cut_39571

theorem selected_cut_39572 : selected 9 ⟨1074135, by decide⟩
    (prefixPartial 12 307505) = some ⟨12, 2, 0, 1074135, 307505, 2037, 65536⟩ := by
  decide +kernel

theorem context_12_307505_1074135 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307505 ⟨1074135, by decide⟩ :=
  accepted_of_selected 12 307505 ⟨1074135, by decide⟩ ⟨12, 2, 0, 1074135, 307505, 2037, 65536⟩
    (by decide) selected_cut_39572

theorem selected_cut_39573 : selected 9 ⟨1074164, by decide⟩
    (prefixPartial 12 307506) = some ⟨12, 2, 0, 1074164, 307506, 1965, 65536⟩ := by
  decide +kernel

theorem context_12_307506_1074164 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307506 ⟨1074164, by decide⟩ :=
  accepted_of_selected 12 307506 ⟨1074164, by decide⟩ ⟨12, 2, 0, 1074164, 307506, 1965, 65536⟩
    (by decide) selected_cut_39573

theorem selected_cut_39574 : selected 9 ⟨1074195, by decide⟩
    (prefixPartial 12 307507) = some ⟨12, 2, 0, 1074195, 307507, 1917, 65536⟩ := by
  decide +kernel

theorem context_12_307507_1074195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307507 ⟨1074195, by decide⟩ :=
  accepted_of_selected 12 307507 ⟨1074195, by decide⟩ ⟨12, 2, 0, 1074195, 307507, 1917, 65536⟩
    (by decide) selected_cut_39574

theorem unmarked_context_11_76876_1074196 : frontier 10 ⟨1074196, by decide⟩
    (prefixCache 11 76876) (prefixPartial 11 76876) = false := by
  decide +kernel

theorem node_context_11_76876_1074196 : EJMOriginalGlobalDAGData.nodes 10 ⟨1074196, by decide⟩ =
    .split (coordinate 11) (![⟨1074097, by decide⟩,⟨1074135, by decide⟩,⟨1074164, by decide⟩,⟨1074195, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76876_1074196 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76876 ⟨1074196, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76876
    ⟨1074196, by decide⟩ (by decide) (![⟨1074097, by decide⟩,⟨1074135, by decide⟩,⟨1074164, by decide⟩,⟨1074195, by decide⟩]) unmarked_context_11_76876_1074196 node_context_11_76876_1074196
  intro a
  fin_cases a
  · exact context_12_307504_1074097
  · exact context_12_307505_1074135
  · exact context_12_307506_1074164
  · exact context_12_307507_1074195

theorem selected_cut_39575 : selected 9 ⟨1074242, by decide⟩
    (prefixPartial 12 307508) = some ⟨12, 2, 0, 1074242, 307508, 2917, 65536⟩ := by
  decide +kernel

theorem context_12_307508_1074242 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307508 ⟨1074242, by decide⟩ :=
  accepted_of_selected 12 307508 ⟨1074242, by decide⟩ ⟨12, 2, 0, 1074242, 307508, 2917, 65536⟩
    (by decide) selected_cut_39575

theorem selected_cut_39576 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 307509) = some ⟨12, 1, 0, 891951, 307509, 1, 65536⟩ := by
  decide +kernel

theorem context_12_307509_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307509 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 307509 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 307509, 1, 65536⟩
    (by decide) selected_cut_39576

theorem selected_cut_39577 : selected 9 ⟨1074274, by decide⟩
    (prefixPartial 12 307510) = some ⟨12, 2, 0, 1074274, 307510, 2461, 65536⟩ := by
  decide +kernel

theorem context_12_307510_1074274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307510 ⟨1074274, by decide⟩ :=
  accepted_of_selected 12 307510 ⟨1074274, by decide⟩ ⟨12, 2, 0, 1074274, 307510, 2461, 65536⟩
    (by decide) selected_cut_39577

theorem selected_cut_39578 : selected 9 ⟨1074304, by decide⟩
    (prefixPartial 12 307511) = some ⟨12, 2, 0, 1074304, 307511, 2293, 65536⟩ := by
  decide +kernel

theorem context_12_307511_1074304 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307511 ⟨1074304, by decide⟩ :=
  accepted_of_selected 12 307511 ⟨1074304, by decide⟩ ⟨12, 2, 0, 1074304, 307511, 2293, 65536⟩
    (by decide) selected_cut_39578

theorem unmarked_context_11_76877_1074305 : frontier 10 ⟨1074305, by decide⟩
    (prefixCache 11 76877) (prefixPartial 11 76877) = false := by
  decide +kernel

theorem node_context_11_76877_1074305 : EJMOriginalGlobalDAGData.nodes 10 ⟨1074305, by decide⟩ =
    .split (coordinate 11) (![⟨1074242, by decide⟩,⟨891951, by decide⟩,⟨1074274, by decide⟩,⟨1074304, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76877_1074305 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76877 ⟨1074305, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76877
    ⟨1074305, by decide⟩ (by decide) (![⟨1074242, by decide⟩,⟨891951, by decide⟩,⟨1074274, by decide⟩,⟨1074304, by decide⟩]) unmarked_context_11_76877_1074305 node_context_11_76877_1074305
  intro a
  fin_cases a
  · exact context_12_307508_1074242
  · exact context_12_307509_891951
  · exact context_12_307510_1074274
  · exact context_12_307511_1074304

theorem selected_cut_39579 : selected 9 ⟨1074340, by decide⟩
    (prefixPartial 12 307512) = some ⟨12, 2, 0, 1074340, 307512, 2417, 65536⟩ := by
  decide +kernel

theorem context_12_307512_1074340 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307512 ⟨1074340, by decide⟩ :=
  accepted_of_selected 12 307512 ⟨1074340, by decide⟩ ⟨12, 2, 0, 1074340, 307512, 2417, 65536⟩
    (by decide) selected_cut_39579

theorem selected_cut_39580 : selected 9 ⟨1074372, by decide⟩
    (prefixPartial 12 307513) = some ⟨12, 2, 0, 1074372, 307513, 2225, 65536⟩ := by
  decide +kernel

theorem context_12_307513_1074372 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307513 ⟨1074372, by decide⟩ :=
  accepted_of_selected 12 307513 ⟨1074372, by decide⟩ ⟨12, 2, 0, 1074372, 307513, 2225, 65536⟩
    (by decide) selected_cut_39580

theorem selected_cut_39581 : selected 9 ⟨1074409, by decide⟩
    (prefixPartial 12 307514) = some ⟨12, 2, 0, 1074409, 307514, 2229, 65536⟩ := by
  decide +kernel

theorem context_12_307514_1074409 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307514 ⟨1074409, by decide⟩ :=
  accepted_of_selected 12 307514 ⟨1074409, by decide⟩ ⟨12, 2, 0, 1074409, 307514, 2229, 65536⟩
    (by decide) selected_cut_39581

theorem selected_cut_39582 : selected 9 ⟨1074441, by decide⟩
    (prefixPartial 12 307515) = some ⟨12, 2, 0, 1074441, 307515, 2137, 65536⟩ := by
  decide +kernel

theorem context_12_307515_1074441 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307515 ⟨1074441, by decide⟩ :=
  accepted_of_selected 12 307515 ⟨1074441, by decide⟩ ⟨12, 2, 0, 1074441, 307515, 2137, 65536⟩
    (by decide) selected_cut_39582

theorem unmarked_context_11_76878_1074442 : frontier 10 ⟨1074442, by decide⟩
    (prefixCache 11 76878) (prefixPartial 11 76878) = false := by
  decide +kernel

theorem node_context_11_76878_1074442 : EJMOriginalGlobalDAGData.nodes 10 ⟨1074442, by decide⟩ =
    .split (coordinate 11) (![⟨1074340, by decide⟩,⟨1074372, by decide⟩,⟨1074409, by decide⟩,⟨1074441, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76878_1074442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76878 ⟨1074442, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76878
    ⟨1074442, by decide⟩ (by decide) (![⟨1074340, by decide⟩,⟨1074372, by decide⟩,⟨1074409, by decide⟩,⟨1074441, by decide⟩]) unmarked_context_11_76878_1074442 node_context_11_76878_1074442
  intro a
  fin_cases a
  · exact context_12_307512_1074340
  · exact context_12_307513_1074372
  · exact context_12_307514_1074409
  · exact context_12_307515_1074441

theorem selected_cut_39583 : selected 9 ⟨1074486, by decide⟩
    (prefixPartial 12 307516) = some ⟨12, 2, 0, 1074486, 307516, 2653, 65536⟩ := by
  decide +kernel

theorem context_12_307516_1074486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307516 ⟨1074486, by decide⟩ :=
  accepted_of_selected 12 307516 ⟨1074486, by decide⟩ ⟨12, 2, 0, 1074486, 307516, 2653, 65536⟩
    (by decide) selected_cut_39583

theorem selected_cut_39584 : selected 9 ⟨1074519, by decide⟩
    (prefixPartial 12 307517) = some ⟨12, 2, 0, 1074519, 307517, 2369, 65536⟩ := by
  decide +kernel

theorem context_12_307517_1074519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307517 ⟨1074519, by decide⟩ :=
  accepted_of_selected 12 307517 ⟨1074519, by decide⟩ ⟨12, 2, 0, 1074519, 307517, 2369, 65536⟩
    (by decide) selected_cut_39584

theorem selected_cut_39585 : selected 9 ⟨1074548, by decide⟩
    (prefixPartial 12 307518) = some ⟨12, 2, 0, 1074548, 307518, 2333, 65536⟩ := by
  decide +kernel

theorem context_12_307518_1074548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307518 ⟨1074548, by decide⟩ :=
  accepted_of_selected 12 307518 ⟨1074548, by decide⟩ ⟨12, 2, 0, 1074548, 307518, 2333, 65536⟩
    (by decide) selected_cut_39585

theorem selected_cut_39586 : selected 9 ⟨394175, by decide⟩
    (prefixPartial 12 307519) = some ⟨12, 1, 0, 394175, 307519, 1, 65536⟩ := by
  decide +kernel

theorem context_12_307519_394175 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307519 ⟨394175, by decide⟩ :=
  accepted_of_selected 12 307519 ⟨394175, by decide⟩ ⟨12, 1, 0, 394175, 307519, 1, 65536⟩
    (by decide) selected_cut_39586

theorem unmarked_context_11_76879_1074549 : frontier 10 ⟨1074549, by decide⟩
    (prefixCache 11 76879) (prefixPartial 11 76879) = false := by
  decide +kernel

theorem node_context_11_76879_1074549 : EJMOriginalGlobalDAGData.nodes 10 ⟨1074549, by decide⟩ =
    .split (coordinate 11) (![⟨1074486, by decide⟩,⟨1074519, by decide⟩,⟨1074548, by decide⟩,⟨394175, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76879_1074549 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76879 ⟨1074549, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76879
    ⟨1074549, by decide⟩ (by decide) (![⟨1074486, by decide⟩,⟨1074519, by decide⟩,⟨1074548, by decide⟩,⟨394175, by decide⟩]) unmarked_context_11_76879_1074549 node_context_11_76879_1074549
  intro a
  fin_cases a
  · exact context_12_307516_1074486
  · exact context_12_307517_1074519
  · exact context_12_307518_1074548
  · exact context_12_307519_394175

theorem unmarked_context_10_19219_1074550 : frontier 11 ⟨1074550, by decide⟩
    (prefixCache 10 19219) (prefixPartial 10 19219) = false := by
  decide +kernel

theorem node_context_10_19219_1074550 : EJMOriginalGlobalDAGData.nodes 11 ⟨1074550, by decide⟩ =
    .split (coordinate 10) (![⟨1074196, by decide⟩,⟨1074305, by decide⟩,⟨1074442, by decide⟩,⟨1074549, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19219_1074550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19219 ⟨1074550, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19219
    ⟨1074550, by decide⟩ (by decide) (![⟨1074196, by decide⟩,⟨1074305, by decide⟩,⟨1074442, by decide⟩,⟨1074549, by decide⟩]) unmarked_context_10_19219_1074550 node_context_10_19219_1074550
  intro a
  fin_cases a
  · exact context_11_76876_1074196
  · exact context_11_76877_1074305
  · exact context_11_76878_1074442
  · exact context_11_76879_1074549

theorem unmarked_context_9_4804_1074551 : frontier 12 ⟨1074551, by decide⟩
    (prefixCache 9 4804) (prefixPartial 9 4804) = false := by
  decide +kernel

theorem node_context_9_4804_1074551 : EJMOriginalGlobalDAGData.nodes 12 ⟨1074551, by decide⟩ =
    .split (coordinate 9) (![⟨1072954, by decide⟩,⟨1073548, by decide⟩,⟨1074056, by decide⟩,⟨1074550, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4804_1074551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4804 ⟨1074551, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4804
    ⟨1074551, by decide⟩ (by decide) (![⟨1072954, by decide⟩,⟨1073548, by decide⟩,⟨1074056, by decide⟩,⟨1074550, by decide⟩]) unmarked_context_9_4804_1074551 node_context_9_4804_1074551
  intro a
  fin_cases a
  · exact context_10_19216_1072954
  · exact context_10_19217_1073548
  · exact context_10_19218_1074056
  · exact context_10_19219_1074550

theorem selected_cut_39587 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 76880) = some ⟨11, 1, 0, 907917, 76880, 1, 262144⟩ := by
  decide +kernel

theorem context_11_76880_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76880 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 76880 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 76880, 1, 262144⟩
    (by decide) selected_cut_39587

theorem selected_cut_39588 : selected 9 ⟨1074587, by decide⟩
    (prefixPartial 12 307524) = some ⟨12, 2, 0, 1074587, 307524, 2445, 65536⟩ := by
  decide +kernel

theorem context_12_307524_1074587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307524 ⟨1074587, by decide⟩ :=
  accepted_of_selected 12 307524 ⟨1074587, by decide⟩ ⟨12, 2, 0, 1074587, 307524, 2445, 65536⟩
    (by decide) selected_cut_39588

theorem selected_cut_39589 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 307525) = some ⟨12, 1, 0, 891951, 307525, 1, 65536⟩ := by
  decide +kernel

theorem context_12_307525_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307525 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 307525 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 307525, 1, 65536⟩
    (by decide) selected_cut_39589

theorem selected_cut_39590 : selected 9 ⟨1074616, by decide⟩
    (prefixPartial 12 307526) = some ⟨12, 2, 0, 1074616, 307526, 1961, 65536⟩ := by
  decide +kernel

theorem context_12_307526_1074616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307526 ⟨1074616, by decide⟩ :=
  accepted_of_selected 12 307526 ⟨1074616, by decide⟩ ⟨12, 2, 0, 1074616, 307526, 1961, 65536⟩
    (by decide) selected_cut_39590

theorem selected_cut_39591 : selected 9 ⟨1074645, by decide⟩
    (prefixPartial 12 307527) = some ⟨12, 2, 0, 1074645, 307527, 2021, 65536⟩ := by
  decide +kernel

theorem context_12_307527_1074645 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307527 ⟨1074645, by decide⟩ :=
  accepted_of_selected 12 307527 ⟨1074645, by decide⟩ ⟨12, 2, 0, 1074645, 307527, 2021, 65536⟩
    (by decide) selected_cut_39591

theorem unmarked_context_11_76881_1074646 : frontier 10 ⟨1074646, by decide⟩
    (prefixCache 11 76881) (prefixPartial 11 76881) = false := by
  decide +kernel

theorem node_context_11_76881_1074646 : EJMOriginalGlobalDAGData.nodes 10 ⟨1074646, by decide⟩ =
    .split (coordinate 11) (![⟨1074587, by decide⟩,⟨891951, by decide⟩,⟨1074616, by decide⟩,⟨1074645, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76881_1074646 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76881 ⟨1074646, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76881
    ⟨1074646, by decide⟩ (by decide) (![⟨1074587, by decide⟩,⟨891951, by decide⟩,⟨1074616, by decide⟩,⟨1074645, by decide⟩]) unmarked_context_11_76881_1074646 node_context_11_76881_1074646
  intro a
  fin_cases a
  · exact context_12_307524_1074587
  · exact context_12_307525_891951
  · exact context_12_307526_1074616
  · exact context_12_307527_1074645

theorem selected_cut_39592 : selected 9 ⟨1074691, by decide⟩
    (prefixPartial 12 307528) = some ⟨12, 2, 0, 1074691, 307528, 2369, 65536⟩ := by
  decide +kernel

theorem context_12_307528_1074691 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307528 ⟨1074691, by decide⟩ :=
  accepted_of_selected 12 307528 ⟨1074691, by decide⟩ ⟨12, 2, 0, 1074691, 307528, 2369, 65536⟩
    (by decide) selected_cut_39592

theorem selected_cut_39593 : selected 9 ⟨1074718, by decide⟩
    (prefixPartial 12 307529) = some ⟨12, 2, 0, 1074718, 307529, 1973, 65536⟩ := by
  decide +kernel

theorem context_12_307529_1074718 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307529 ⟨1074718, by decide⟩ :=
  accepted_of_selected 12 307529 ⟨1074718, by decide⟩ ⟨12, 2, 0, 1074718, 307529, 1973, 65536⟩
    (by decide) selected_cut_39593

theorem selected_cut_39594 : selected 9 ⟨1074747, by decide⟩
    (prefixPartial 12 307530) = some ⟨12, 2, 0, 1074747, 307530, 2081, 65536⟩ := by
  decide +kernel

theorem context_12_307530_1074747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307530 ⟨1074747, by decide⟩ :=
  accepted_of_selected 12 307530 ⟨1074747, by decide⟩ ⟨12, 2, 0, 1074747, 307530, 2081, 65536⟩
    (by decide) selected_cut_39594

theorem selected_cut_39595 : selected 9 ⟨1074776, by decide⟩
    (prefixPartial 12 307531) = some ⟨12, 2, 0, 1074776, 307531, 1989, 65536⟩ := by
  decide +kernel

theorem context_12_307531_1074776 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307531 ⟨1074776, by decide⟩ :=
  accepted_of_selected 12 307531 ⟨1074776, by decide⟩ ⟨12, 2, 0, 1074776, 307531, 1989, 65536⟩
    (by decide) selected_cut_39595

theorem unmarked_context_11_76882_1074777 : frontier 10 ⟨1074777, by decide⟩
    (prefixCache 11 76882) (prefixPartial 11 76882) = false := by
  decide +kernel

theorem node_context_11_76882_1074777 : EJMOriginalGlobalDAGData.nodes 10 ⟨1074777, by decide⟩ =
    .split (coordinate 11) (![⟨1074691, by decide⟩,⟨1074718, by decide⟩,⟨1074747, by decide⟩,⟨1074776, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76882_1074777 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76882 ⟨1074777, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76882
    ⟨1074777, by decide⟩ (by decide) (![⟨1074691, by decide⟩,⟨1074718, by decide⟩,⟨1074747, by decide⟩,⟨1074776, by decide⟩]) unmarked_context_11_76882_1074777 node_context_11_76882_1074777
  intro a
  fin_cases a
  · exact context_12_307528_1074691
  · exact context_12_307529_1074718
  · exact context_12_307530_1074747
  · exact context_12_307531_1074776

theorem selected_cut_39596 : selected 9 ⟨1074820, by decide⟩
    (prefixPartial 12 307532) = some ⟨12, 2, 0, 1074820, 307532, 2485, 65536⟩ := by
  decide +kernel

theorem context_12_307532_1074820 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307532 ⟨1074820, by decide⟩ :=
  accepted_of_selected 12 307532 ⟨1074820, by decide⟩ ⟨12, 2, 0, 1074820, 307532, 2485, 65536⟩
    (by decide) selected_cut_39596

theorem selected_cut_39597 : selected 9 ⟨1074851, by decide⟩
    (prefixPartial 12 307533) = some ⟨12, 2, 0, 1074851, 307533, 2077, 65536⟩ := by
  decide +kernel

theorem context_12_307533_1074851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307533 ⟨1074851, by decide⟩ :=
  accepted_of_selected 12 307533 ⟨1074851, by decide⟩ ⟨12, 2, 0, 1074851, 307533, 2077, 65536⟩
    (by decide) selected_cut_39597

theorem selected_cut_39598 : selected 9 ⟨1074882, by decide⟩
    (prefixPartial 12 307534) = some ⟨12, 2, 0, 1074882, 307534, 2085, 65536⟩ := by
  decide +kernel

theorem context_12_307534_1074882 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307534 ⟨1074882, by decide⟩ :=
  accepted_of_selected 12 307534 ⟨1074882, by decide⟩ ⟨12, 2, 0, 1074882, 307534, 2085, 65536⟩
    (by decide) selected_cut_39598

theorem selected_cut_39599 : selected 9 ⟨1074909, by decide⟩
    (prefixPartial 12 307535) = some ⟨12, 2, 0, 1074909, 307535, 2069, 65536⟩ := by
  decide +kernel

theorem context_12_307535_1074909 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307535 ⟨1074909, by decide⟩ :=
  accepted_of_selected 12 307535 ⟨1074909, by decide⟩ ⟨12, 2, 0, 1074909, 307535, 2069, 65536⟩
    (by decide) selected_cut_39599

theorem unmarked_context_11_76883_1074910 : frontier 10 ⟨1074910, by decide⟩
    (prefixCache 11 76883) (prefixPartial 11 76883) = false := by
  decide +kernel

theorem node_context_11_76883_1074910 : EJMOriginalGlobalDAGData.nodes 10 ⟨1074910, by decide⟩ =
    .split (coordinate 11) (![⟨1074820, by decide⟩,⟨1074851, by decide⟩,⟨1074882, by decide⟩,⟨1074909, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76883_1074910 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76883 ⟨1074910, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76883
    ⟨1074910, by decide⟩ (by decide) (![⟨1074820, by decide⟩,⟨1074851, by decide⟩,⟨1074882, by decide⟩,⟨1074909, by decide⟩]) unmarked_context_11_76883_1074910 node_context_11_76883_1074910
  intro a
  fin_cases a
  · exact context_12_307532_1074820
  · exact context_12_307533_1074851
  · exact context_12_307534_1074882
  · exact context_12_307535_1074909

theorem unmarked_context_10_19220_1074911 : frontier 11 ⟨1074911, by decide⟩
    (prefixCache 10 19220) (prefixPartial 10 19220) = false := by
  decide +kernel

theorem node_context_10_19220_1074911 : EJMOriginalGlobalDAGData.nodes 11 ⟨1074911, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨1074646, by decide⟩,⟨1074777, by decide⟩,⟨1074910, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19220_1074911 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19220 ⟨1074911, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19220
    ⟨1074911, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨1074646, by decide⟩,⟨1074777, by decide⟩,⟨1074910, by decide⟩]) unmarked_context_10_19220_1074911 node_context_10_19220_1074911
  intro a
  fin_cases a
  · exact context_11_76880_907917
  · exact context_11_76881_1074646
  · exact context_11_76882_1074777
  · exact context_11_76883_1074910

theorem selected_cut_39600 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 19221) = some ⟨10, 1, 0, 893098, 19221, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_19221_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19221 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 19221 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 19221, 1, 1048576⟩
    (by decide) selected_cut_39600

theorem selected_cut_39601 : selected 9 ⟨1074929, by decide⟩
    (prefixPartial 12 307552) = some ⟨12, 2, 0, 1074929, 307552, 1753, 65536⟩ := by
  decide +kernel

theorem context_12_307552_1074929 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307552 ⟨1074929, by decide⟩ :=
  accepted_of_selected 12 307552 ⟨1074929, by decide⟩ ⟨12, 2, 0, 1074929, 307552, 1753, 65536⟩
    (by decide) selected_cut_39601

theorem selected_cut_39602 : selected 9 ⟨1074947, by decide⟩
    (prefixPartial 12 307553) = some ⟨12, 2, 0, 1074947, 307553, 1681, 65536⟩ := by
  decide +kernel

theorem context_12_307553_1074947 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307553 ⟨1074947, by decide⟩ :=
  accepted_of_selected 12 307553 ⟨1074947, by decide⟩ ⟨12, 2, 0, 1074947, 307553, 1681, 65536⟩
    (by decide) selected_cut_39602

theorem selected_cut_39603 : selected 9 ⟨1074964, by decide⟩
    (prefixPartial 12 307554) = some ⟨12, 2, 0, 1074964, 307554, 1593, 65536⟩ := by
  decide +kernel

theorem context_12_307554_1074964 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307554 ⟨1074964, by decide⟩ :=
  accepted_of_selected 12 307554 ⟨1074964, by decide⟩ ⟨12, 2, 0, 1074964, 307554, 1593, 65536⟩
    (by decide) selected_cut_39603

theorem selected_cut_39604 : selected 9 ⟨1074982, by decide⟩
    (prefixPartial 12 307555) = some ⟨12, 2, 0, 1074982, 307555, 1609, 65536⟩ := by
  decide +kernel

theorem context_12_307555_1074982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307555 ⟨1074982, by decide⟩ :=
  accepted_of_selected 12 307555 ⟨1074982, by decide⟩ ⟨12, 2, 0, 1074982, 307555, 1609, 65536⟩
    (by decide) selected_cut_39604

theorem unmarked_context_11_76888_1074983 : frontier 10 ⟨1074983, by decide⟩
    (prefixCache 11 76888) (prefixPartial 11 76888) = false := by
  decide +kernel

theorem node_context_11_76888_1074983 : EJMOriginalGlobalDAGData.nodes 10 ⟨1074983, by decide⟩ =
    .split (coordinate 11) (![⟨1074929, by decide⟩,⟨1074947, by decide⟩,⟨1074964, by decide⟩,⟨1074982, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76888_1074983 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76888 ⟨1074983, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76888
    ⟨1074983, by decide⟩ (by decide) (![⟨1074929, by decide⟩,⟨1074947, by decide⟩,⟨1074964, by decide⟩,⟨1074982, by decide⟩]) unmarked_context_11_76888_1074983 node_context_11_76888_1074983
  intro a
  fin_cases a
  · exact context_12_307552_1074929
  · exact context_12_307553_1074947
  · exact context_12_307554_1074964
  · exact context_12_307555_1074982

theorem selected_cut_39605 : selected 9 ⟨1075012, by decide⟩
    (prefixPartial 12 307556) = some ⟨12, 2, 0, 1075012, 307556, 1869, 65536⟩ := by
  decide +kernel

theorem context_12_307556_1075012 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307556 ⟨1075012, by decide⟩ :=
  accepted_of_selected 12 307556 ⟨1075012, by decide⟩ ⟨12, 2, 0, 1075012, 307556, 1869, 65536⟩
    (by decide) selected_cut_39605

theorem selected_cut_39606 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 307557) = some ⟨12, 1, 0, 891951, 307557, 1, 65536⟩ := by
  decide +kernel

theorem context_12_307557_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307557 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 307557 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 307557, 1, 65536⟩
    (by decide) selected_cut_39606

theorem selected_cut_39607 : selected 9 ⟨1075032, by decide⟩
    (prefixPartial 12 307558) = some ⟨12, 2, 0, 1075032, 307558, 1629, 65536⟩ := by
  decide +kernel

theorem context_12_307558_1075032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307558 ⟨1075032, by decide⟩ :=
  accepted_of_selected 12 307558 ⟨1075032, by decide⟩ ⟨12, 2, 0, 1075032, 307558, 1629, 65536⟩
    (by decide) selected_cut_39607

theorem selected_cut_39608 : selected 9 ⟨1075050, by decide⟩
    (prefixPartial 12 307559) = some ⟨12, 2, 0, 1075050, 307559, 1697, 65536⟩ := by
  decide +kernel

theorem context_12_307559_1075050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307559 ⟨1075050, by decide⟩ :=
  accepted_of_selected 12 307559 ⟨1075050, by decide⟩ ⟨12, 2, 0, 1075050, 307559, 1697, 65536⟩
    (by decide) selected_cut_39608

theorem unmarked_context_11_76889_1075051 : frontier 10 ⟨1075051, by decide⟩
    (prefixCache 11 76889) (prefixPartial 11 76889) = false := by
  decide +kernel

theorem node_context_11_76889_1075051 : EJMOriginalGlobalDAGData.nodes 10 ⟨1075051, by decide⟩ =
    .split (coordinate 11) (![⟨1075012, by decide⟩,⟨891951, by decide⟩,⟨1075032, by decide⟩,⟨1075050, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76889_1075051 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76889 ⟨1075051, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76889
    ⟨1075051, by decide⟩ (by decide) (![⟨1075012, by decide⟩,⟨891951, by decide⟩,⟨1075032, by decide⟩,⟨1075050, by decide⟩]) unmarked_context_11_76889_1075051 node_context_11_76889_1075051
  intro a
  fin_cases a
  · exact context_12_307556_1075012
  · exact context_12_307557_891951
  · exact context_12_307558_1075032
  · exact context_12_307559_1075050

theorem selected_cut_39609 : selected 9 ⟨1075078, by decide⟩
    (prefixPartial 12 307560) = some ⟨12, 2, 0, 1075078, 307560, 1773, 65536⟩ := by
  decide +kernel

theorem context_12_307560_1075078 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307560 ⟨1075078, by decide⟩ :=
  accepted_of_selected 12 307560 ⟨1075078, by decide⟩ ⟨12, 2, 0, 1075078, 307560, 1773, 65536⟩
    (by decide) selected_cut_39609

theorem selected_cut_39610 : selected 9 ⟨1075111, by decide⟩
    (prefixPartial 12 307561) = some ⟨12, 2, 0, 1075111, 307561, 1865, 65536⟩ := by
  decide +kernel

theorem context_12_307561_1075111 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307561 ⟨1075111, by decide⟩ :=
  accepted_of_selected 12 307561 ⟨1075111, by decide⟩ ⟨12, 2, 0, 1075111, 307561, 1865, 65536⟩
    (by decide) selected_cut_39610

theorem selected_cut_39611 : selected 9 ⟨101803, by decide⟩
    (prefixPartial 12 307562) = some ⟨12, 1, 0, 101803, 307562, 1, 65536⟩ := by
  decide +kernel

theorem context_12_307562_101803 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307562 ⟨101803, by decide⟩ :=
  accepted_of_selected 12 307562 ⟨101803, by decide⟩ ⟨12, 1, 0, 101803, 307562, 1, 65536⟩
    (by decide) selected_cut_39611

theorem selected_cut_39612 : selected 9 ⟨1075144, by decide⟩
    (prefixPartial 12 307563) = some ⟨12, 2, 0, 1075144, 307563, 1841, 65536⟩ := by
  decide +kernel

theorem context_12_307563_1075144 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307563 ⟨1075144, by decide⟩ :=
  accepted_of_selected 12 307563 ⟨1075144, by decide⟩ ⟨12, 2, 0, 1075144, 307563, 1841, 65536⟩
    (by decide) selected_cut_39612

theorem unmarked_context_11_76890_1075145 : frontier 10 ⟨1075145, by decide⟩
    (prefixCache 11 76890) (prefixPartial 11 76890) = false := by
  decide +kernel

theorem node_context_11_76890_1075145 : EJMOriginalGlobalDAGData.nodes 10 ⟨1075145, by decide⟩ =
    .split (coordinate 11) (![⟨1075078, by decide⟩,⟨1075111, by decide⟩,⟨101803, by decide⟩,⟨1075144, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76890_1075145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76890 ⟨1075145, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76890
    ⟨1075145, by decide⟩ (by decide) (![⟨1075078, by decide⟩,⟨1075111, by decide⟩,⟨101803, by decide⟩,⟨1075144, by decide⟩]) unmarked_context_11_76890_1075145 node_context_11_76890_1075145
  intro a
  fin_cases a
  · exact context_12_307560_1075078
  · exact context_12_307561_1075111
  · exact context_12_307562_101803
  · exact context_12_307563_1075144

theorem selected_cut_39613 : selected 9 ⟨1075173, by decide⟩
    (prefixPartial 12 307564) = some ⟨12, 2, 0, 1075173, 307564, 1841, 65536⟩ := by
  decide +kernel

theorem context_12_307564_1075173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307564 ⟨1075173, by decide⟩ :=
  accepted_of_selected 12 307564 ⟨1075173, by decide⟩ ⟨12, 2, 0, 1075173, 307564, 1841, 65536⟩
    (by decide) selected_cut_39613

theorem selected_cut_39614 : selected 9 ⟨1075199, by decide⟩
    (prefixPartial 12 307565) = some ⟨12, 2, 0, 1075199, 307565, 1813, 65536⟩ := by
  decide +kernel

theorem context_12_307565_1075199 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307565 ⟨1075199, by decide⟩ :=
  accepted_of_selected 12 307565 ⟨1075199, by decide⟩ ⟨12, 2, 0, 1075199, 307565, 1813, 65536⟩
    (by decide) selected_cut_39614

theorem selected_cut_39615 : selected 9 ⟨1075231, by decide⟩
    (prefixPartial 12 307566) = some ⟨12, 2, 0, 1075231, 307566, 1693, 65536⟩ := by
  decide +kernel

theorem context_12_307566_1075231 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307566 ⟨1075231, by decide⟩ :=
  accepted_of_selected 12 307566 ⟨1075231, by decide⟩ ⟨12, 2, 0, 1075231, 307566, 1693, 65536⟩
    (by decide) selected_cut_39615

theorem selected_cut_39616 : selected 9 ⟨1075256, by decide⟩
    (prefixPartial 12 307567) = some ⟨12, 2, 0, 1075256, 307567, 1785, 65536⟩ := by
  decide +kernel

theorem context_12_307567_1075256 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307567 ⟨1075256, by decide⟩ :=
  accepted_of_selected 12 307567 ⟨1075256, by decide⟩ ⟨12, 2, 0, 1075256, 307567, 1785, 65536⟩
    (by decide) selected_cut_39616

theorem unmarked_context_11_76891_1075257 : frontier 10 ⟨1075257, by decide⟩
    (prefixCache 11 76891) (prefixPartial 11 76891) = false := by
  decide +kernel

theorem node_context_11_76891_1075257 : EJMOriginalGlobalDAGData.nodes 10 ⟨1075257, by decide⟩ =
    .split (coordinate 11) (![⟨1075173, by decide⟩,⟨1075199, by decide⟩,⟨1075231, by decide⟩,⟨1075256, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76891_1075257 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76891 ⟨1075257, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76891
    ⟨1075257, by decide⟩ (by decide) (![⟨1075173, by decide⟩,⟨1075199, by decide⟩,⟨1075231, by decide⟩,⟨1075256, by decide⟩]) unmarked_context_11_76891_1075257 node_context_11_76891_1075257
  intro a
  fin_cases a
  · exact context_12_307564_1075173
  · exact context_12_307565_1075199
  · exact context_12_307566_1075231
  · exact context_12_307567_1075256

theorem unmarked_context_10_19222_1075258 : frontier 11 ⟨1075258, by decide⟩
    (prefixCache 10 19222) (prefixPartial 10 19222) = false := by
  decide +kernel

theorem node_context_10_19222_1075258 : EJMOriginalGlobalDAGData.nodes 11 ⟨1075258, by decide⟩ =
    .split (coordinate 10) (![⟨1074983, by decide⟩,⟨1075051, by decide⟩,⟨1075145, by decide⟩,⟨1075257, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19222_1075258 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19222 ⟨1075258, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19222
    ⟨1075258, by decide⟩ (by decide) (![⟨1074983, by decide⟩,⟨1075051, by decide⟩,⟨1075145, by decide⟩,⟨1075257, by decide⟩]) unmarked_context_10_19222_1075258 node_context_10_19222_1075258
  intro a
  fin_cases a
  · exact context_11_76888_1074983
  · exact context_11_76889_1075051
  · exact context_11_76890_1075145
  · exact context_11_76891_1075257

theorem selected_cut_39617 : selected 9 ⟨1075275, by decide⟩
    (prefixPartial 12 307568) = some ⟨12, 2, 0, 1075275, 307568, 1453, 65536⟩ := by
  decide +kernel

theorem context_12_307568_1075275 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307568 ⟨1075275, by decide⟩ :=
  accepted_of_selected 12 307568 ⟨1075275, by decide⟩ ⟨12, 2, 0, 1075275, 307568, 1453, 65536⟩
    (by decide) selected_cut_39617

theorem selected_cut_39618 : selected 9 ⟨1075292, by decide⟩
    (prefixPartial 12 307569) = some ⟨12, 2, 0, 1075292, 307569, 1401, 65536⟩ := by
  decide +kernel

theorem context_12_307569_1075292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307569 ⟨1075292, by decide⟩ :=
  accepted_of_selected 12 307569 ⟨1075292, by decide⟩ ⟨12, 2, 0, 1075292, 307569, 1401, 65536⟩
    (by decide) selected_cut_39618

theorem selected_cut_39619 : selected 9 ⟨1075306, by decide⟩
    (prefixPartial 12 307570) = some ⟨12, 2, 0, 1075306, 307570, 1301, 65536⟩ := by
  decide +kernel

theorem context_12_307570_1075306 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307570 ⟨1075306, by decide⟩ :=
  accepted_of_selected 12 307570 ⟨1075306, by decide⟩ ⟨12, 2, 0, 1075306, 307570, 1301, 65536⟩
    (by decide) selected_cut_39619

theorem selected_cut_39620 : selected 9 ⟨1075325, by decide⟩
    (prefixPartial 12 307571) = some ⟨12, 2, 0, 1075325, 307571, 1321, 65536⟩ := by
  decide +kernel

theorem context_12_307571_1075325 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307571 ⟨1075325, by decide⟩ :=
  accepted_of_selected 12 307571 ⟨1075325, by decide⟩ ⟨12, 2, 0, 1075325, 307571, 1321, 65536⟩
    (by decide) selected_cut_39620

theorem unmarked_context_11_76892_1075326 : frontier 10 ⟨1075326, by decide⟩
    (prefixCache 11 76892) (prefixPartial 11 76892) = false := by
  decide +kernel

theorem node_context_11_76892_1075326 : EJMOriginalGlobalDAGData.nodes 10 ⟨1075326, by decide⟩ =
    .split (coordinate 11) (![⟨1075275, by decide⟩,⟨1075292, by decide⟩,⟨1075306, by decide⟩,⟨1075325, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76892_1075326 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76892 ⟨1075326, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76892
    ⟨1075326, by decide⟩ (by decide) (![⟨1075275, by decide⟩,⟨1075292, by decide⟩,⟨1075306, by decide⟩,⟨1075325, by decide⟩]) unmarked_context_11_76892_1075326 node_context_11_76892_1075326
  intro a
  fin_cases a
  · exact context_12_307568_1075275
  · exact context_12_307569_1075292
  · exact context_12_307570_1075306
  · exact context_12_307571_1075325

theorem selected_cut_39621 : selected 9 ⟨1075351, by decide⟩
    (prefixPartial 12 307572) = some ⟨12, 2, 0, 1075351, 307572, 1725, 65536⟩ := by
  decide +kernel

theorem context_12_307572_1075351 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307572 ⟨1075351, by decide⟩ :=
  accepted_of_selected 12 307572 ⟨1075351, by decide⟩ ⟨12, 2, 0, 1075351, 307572, 1725, 65536⟩
    (by decide) selected_cut_39621

theorem selected_cut_39622 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 307573) = some ⟨12, 1, 0, 891951, 307573, 1, 65536⟩ := by
  decide +kernel

theorem context_12_307573_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307573 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 307573 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 307573, 1, 65536⟩
    (by decide) selected_cut_39622

theorem selected_cut_39623 : selected 9 ⟨1075370, by decide⟩
    (prefixPartial 12 307574) = some ⟨12, 2, 0, 1075370, 307574, 1465, 65536⟩ := by
  decide +kernel

theorem context_12_307574_1075370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307574 ⟨1075370, by decide⟩ :=
  accepted_of_selected 12 307574 ⟨1075370, by decide⟩ ⟨12, 2, 0, 1075370, 307574, 1465, 65536⟩
    (by decide) selected_cut_39623

theorem selected_cut_39624 : selected 9 ⟨1075388, by decide⟩
    (prefixPartial 12 307575) = some ⟨12, 2, 0, 1075388, 307575, 1457, 65536⟩ := by
  decide +kernel

theorem context_12_307575_1075388 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307575 ⟨1075388, by decide⟩ :=
  accepted_of_selected 12 307575 ⟨1075388, by decide⟩ ⟨12, 2, 0, 1075388, 307575, 1457, 65536⟩
    (by decide) selected_cut_39624

theorem unmarked_context_11_76893_1075389 : frontier 10 ⟨1075389, by decide⟩
    (prefixCache 11 76893) (prefixPartial 11 76893) = false := by
  decide +kernel

theorem node_context_11_76893_1075389 : EJMOriginalGlobalDAGData.nodes 10 ⟨1075389, by decide⟩ =
    .split (coordinate 11) (![⟨1075351, by decide⟩,⟨891951, by decide⟩,⟨1075370, by decide⟩,⟨1075388, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76893_1075389 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76893 ⟨1075389, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76893
    ⟨1075389, by decide⟩ (by decide) (![⟨1075351, by decide⟩,⟨891951, by decide⟩,⟨1075370, by decide⟩,⟨1075388, by decide⟩]) unmarked_context_11_76893_1075389 node_context_11_76893_1075389
  intro a
  fin_cases a
  · exact context_12_307572_1075351
  · exact context_12_307573_891951
  · exact context_12_307574_1075370
  · exact context_12_307575_1075388

theorem selected_cut_39625 : selected 9 ⟨1075412, by decide⟩
    (prefixPartial 12 307576) = some ⟨12, 2, 0, 1075412, 307576, 1581, 65536⟩ := by
  decide +kernel

theorem context_12_307576_1075412 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307576 ⟨1075412, by decide⟩ :=
  accepted_of_selected 12 307576 ⟨1075412, by decide⟩ ⟨12, 2, 0, 1075412, 307576, 1581, 65536⟩
    (by decide) selected_cut_39625

theorem selected_cut_39626 : selected 9 ⟨1075436, by decide⟩
    (prefixPartial 12 307577) = some ⟨12, 2, 0, 1075436, 307577, 1565, 65536⟩ := by
  decide +kernel

theorem context_12_307577_1075436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307577 ⟨1075436, by decide⟩ :=
  accepted_of_selected 12 307577 ⟨1075436, by decide⟩ ⟨12, 2, 0, 1075436, 307577, 1565, 65536⟩
    (by decide) selected_cut_39626

theorem selected_cut_39627 : selected 9 ⟨1075456, by decide⟩
    (prefixPartial 12 307578) = some ⟨12, 2, 0, 1075456, 307578, 1413, 65536⟩ := by
  decide +kernel

theorem context_12_307578_1075456 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307578 ⟨1075456, by decide⟩ :=
  accepted_of_selected 12 307578 ⟨1075456, by decide⟩ ⟨12, 2, 0, 1075456, 307578, 1413, 65536⟩
    (by decide) selected_cut_39627

theorem selected_cut_39628 : selected 9 ⟨1075471, by decide⟩
    (prefixPartial 12 307579) = some ⟨12, 2, 0, 1075471, 307579, 1461, 65536⟩ := by
  decide +kernel

theorem context_12_307579_1075471 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307579 ⟨1075471, by decide⟩ :=
  accepted_of_selected 12 307579 ⟨1075471, by decide⟩ ⟨12, 2, 0, 1075471, 307579, 1461, 65536⟩
    (by decide) selected_cut_39628

theorem unmarked_context_11_76894_1075472 : frontier 10 ⟨1075472, by decide⟩
    (prefixCache 11 76894) (prefixPartial 11 76894) = false := by
  decide +kernel

theorem node_context_11_76894_1075472 : EJMOriginalGlobalDAGData.nodes 10 ⟨1075472, by decide⟩ =
    .split (coordinate 11) (![⟨1075412, by decide⟩,⟨1075436, by decide⟩,⟨1075456, by decide⟩,⟨1075471, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76894_1075472 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76894 ⟨1075472, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76894
    ⟨1075472, by decide⟩ (by decide) (![⟨1075412, by decide⟩,⟨1075436, by decide⟩,⟨1075456, by decide⟩,⟨1075471, by decide⟩]) unmarked_context_11_76894_1075472 node_context_11_76894_1075472
  intro a
  fin_cases a
  · exact context_12_307576_1075412
  · exact context_12_307577_1075436
  · exact context_12_307578_1075456
  · exact context_12_307579_1075471

theorem selected_cut_39629 : selected 9 ⟨1075494, by decide⟩
    (prefixPartial 12 307580) = some ⟨12, 2, 0, 1075494, 307580, 1537, 65536⟩ := by
  decide +kernel

theorem context_12_307580_1075494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307580 ⟨1075494, by decide⟩ :=
  accepted_of_selected 12 307580 ⟨1075494, by decide⟩ ⟨12, 2, 0, 1075494, 307580, 1537, 65536⟩
    (by decide) selected_cut_39629

theorem selected_cut_39630 : selected 9 ⟨1075521, by decide⟩
    (prefixPartial 12 307581) = some ⟨12, 2, 0, 1075521, 307581, 1521, 65536⟩ := by
  decide +kernel

theorem context_12_307581_1075521 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307581 ⟨1075521, by decide⟩ :=
  accepted_of_selected 12 307581 ⟨1075521, by decide⟩ ⟨12, 2, 0, 1075521, 307581, 1521, 65536⟩
    (by decide) selected_cut_39630

theorem selected_cut_39631 : selected 9 ⟨1075547, by decide⟩
    (prefixPartial 12 307582) = some ⟨12, 2, 0, 1075547, 307582, 1389, 65536⟩ := by
  decide +kernel

theorem context_12_307582_1075547 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307582 ⟨1075547, by decide⟩ :=
  accepted_of_selected 12 307582 ⟨1075547, by decide⟩ ⟨12, 2, 0, 1075547, 307582, 1389, 65536⟩
    (by decide) selected_cut_39631

theorem selected_cut_39632 : selected 9 ⟨394175, by decide⟩
    (prefixPartial 12 307583) = some ⟨12, 1, 0, 394175, 307583, 1, 65536⟩ := by
  decide +kernel

theorem context_12_307583_394175 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307583 ⟨394175, by decide⟩ :=
  accepted_of_selected 12 307583 ⟨394175, by decide⟩ ⟨12, 1, 0, 394175, 307583, 1, 65536⟩
    (by decide) selected_cut_39632

theorem unmarked_context_11_76895_1075548 : frontier 10 ⟨1075548, by decide⟩
    (prefixCache 11 76895) (prefixPartial 11 76895) = false := by
  decide +kernel

theorem node_context_11_76895_1075548 : EJMOriginalGlobalDAGData.nodes 10 ⟨1075548, by decide⟩ =
    .split (coordinate 11) (![⟨1075494, by decide⟩,⟨1075521, by decide⟩,⟨1075547, by decide⟩,⟨394175, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76895_1075548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76895 ⟨1075548, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76895
    ⟨1075548, by decide⟩ (by decide) (![⟨1075494, by decide⟩,⟨1075521, by decide⟩,⟨1075547, by decide⟩,⟨394175, by decide⟩]) unmarked_context_11_76895_1075548 node_context_11_76895_1075548
  intro a
  fin_cases a
  · exact context_12_307580_1075494
  · exact context_12_307581_1075521
  · exact context_12_307582_1075547
  · exact context_12_307583_394175

theorem unmarked_context_10_19223_1075549 : frontier 11 ⟨1075549, by decide⟩
    (prefixCache 10 19223) (prefixPartial 10 19223) = false := by
  decide +kernel

theorem node_context_10_19223_1075549 : EJMOriginalGlobalDAGData.nodes 11 ⟨1075549, by decide⟩ =
    .split (coordinate 10) (![⟨1075326, by decide⟩,⟨1075389, by decide⟩,⟨1075472, by decide⟩,⟨1075548, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19223_1075549 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19223 ⟨1075549, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19223
    ⟨1075549, by decide⟩ (by decide) (![⟨1075326, by decide⟩,⟨1075389, by decide⟩,⟨1075472, by decide⟩,⟨1075548, by decide⟩]) unmarked_context_10_19223_1075549 node_context_10_19223_1075549
  intro a
  fin_cases a
  · exact context_11_76892_1075326
  · exact context_11_76893_1075389
  · exact context_11_76894_1075472
  · exact context_11_76895_1075548

theorem unmarked_context_9_4805_1075550 : frontier 12 ⟨1075550, by decide⟩
    (prefixCache 9 4805) (prefixPartial 9 4805) = false := by
  decide +kernel

theorem node_context_9_4805_1075550 : EJMOriginalGlobalDAGData.nodes 12 ⟨1075550, by decide⟩ =
    .split (coordinate 9) (![⟨1074911, by decide⟩,⟨893098, by decide⟩,⟨1075258, by decide⟩,⟨1075549, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4805_1075550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4805 ⟨1075550, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4805
    ⟨1075550, by decide⟩ (by decide) (![⟨1074911, by decide⟩,⟨893098, by decide⟩,⟨1075258, by decide⟩,⟨1075549, by decide⟩]) unmarked_context_9_4805_1075550 node_context_9_4805_1075550
  intro a
  fin_cases a
  · exact context_10_19220_1074911
  · exact context_10_19221_893098
  · exact context_10_19222_1075258
  · exact context_10_19223_1075549

theorem selected_cut_39633 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 76896) = some ⟨11, 1, 0, 907917, 76896, 1, 262144⟩ := by
  decide +kernel

theorem context_11_76896_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76896 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 76896 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 76896, 1, 262144⟩
    (by decide) selected_cut_39633

theorem selected_cut_39634 : selected 10 ⟨1075587, by decide⟩
    (prefixPartial 11 76897) = some ⟨11, 2, 0, 1075587, 76897, 2309, 262144⟩ := by
  decide +kernel

theorem context_11_76897_1075587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76897 ⟨1075587, by decide⟩ :=
  accepted_of_selected 11 76897 ⟨1075587, by decide⟩ ⟨11, 2, 0, 1075587, 76897, 2309, 262144⟩
    (by decide) selected_cut_39634

theorem selected_cut_39635 : selected 10 ⟨1075635, by decide⟩
    (prefixPartial 11 76898) = some ⟨11, 2, 0, 1075635, 76898, 3433, 262144⟩ := by
  decide +kernel

theorem context_11_76898_1075635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76898 ⟨1075635, by decide⟩ :=
  accepted_of_selected 11 76898 ⟨1075635, by decide⟩ ⟨11, 2, 0, 1075635, 76898, 3433, 262144⟩
    (by decide) selected_cut_39635

theorem selected_cut_39636 : selected 10 ⟨1075685, by decide⟩
    (prefixPartial 11 76899) = some ⟨11, 2, 0, 1075685, 76899, 3389, 262144⟩ := by
  decide +kernel

theorem context_11_76899_1075685 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76899 ⟨1075685, by decide⟩ :=
  accepted_of_selected 11 76899 ⟨1075685, by decide⟩ ⟨11, 2, 0, 1075685, 76899, 3389, 262144⟩
    (by decide) selected_cut_39636

theorem unmarked_context_10_19224_1075686 : frontier 11 ⟨1075686, by decide⟩
    (prefixCache 10 19224) (prefixPartial 10 19224) = false := by
  decide +kernel

theorem node_context_10_19224_1075686 : EJMOriginalGlobalDAGData.nodes 11 ⟨1075686, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨1075587, by decide⟩,⟨1075635, by decide⟩,⟨1075685, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19224_1075686 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19224 ⟨1075686, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19224
    ⟨1075686, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨1075587, by decide⟩,⟨1075635, by decide⟩,⟨1075685, by decide⟩]) unmarked_context_10_19224_1075686 node_context_10_19224_1075686
  intro a
  fin_cases a
  · exact context_11_76896_907917
  · exact context_11_76897_1075587
  · exact context_11_76898_1075635
  · exact context_11_76899_1075685

theorem selected_cut_39637 : selected 10 ⟨1075733, by decide⟩
    (prefixPartial 11 76900) = some ⟨11, 2, 0, 1075733, 76900, 2989, 262144⟩ := by
  decide +kernel

theorem context_11_76900_1075733 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76900 ⟨1075733, by decide⟩ :=
  accepted_of_selected 11 76900 ⟨1075733, by decide⟩ ⟨11, 2, 0, 1075733, 76900, 2989, 262144⟩
    (by decide) selected_cut_39637

theorem selected_cut_39638 : selected 10 ⟨1075761, by decide⟩
    (prefixPartial 11 76901) = some ⟨11, 2, 0, 1075761, 76901, 1769, 262144⟩ := by
  decide +kernel

theorem context_11_76901_1075761 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76901 ⟨1075761, by decide⟩ :=
  accepted_of_selected 11 76901 ⟨1075761, by decide⟩ ⟨11, 2, 0, 1075761, 76901, 1769, 262144⟩
    (by decide) selected_cut_39638

theorem selected_cut_39639 : selected 10 ⟨1075795, by decide⟩
    (prefixPartial 11 76902) = some ⟨11, 2, 0, 1075795, 76902, 2605, 262144⟩ := by
  decide +kernel

theorem context_11_76902_1075795 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76902 ⟨1075795, by decide⟩ :=
  accepted_of_selected 11 76902 ⟨1075795, by decide⟩ ⟨11, 2, 0, 1075795, 76902, 2605, 262144⟩
    (by decide) selected_cut_39639

theorem selected_cut_39640 : selected 10 ⟨1075822, by decide⟩
    (prefixPartial 11 76903) = some ⟨11, 2, 0, 1075822, 76903, 2521, 262144⟩ := by
  decide +kernel

theorem context_11_76903_1075822 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76903 ⟨1075822, by decide⟩ :=
  accepted_of_selected 11 76903 ⟨1075822, by decide⟩ ⟨11, 2, 0, 1075822, 76903, 2521, 262144⟩
    (by decide) selected_cut_39640

theorem unmarked_context_10_19225_1075823 : frontier 11 ⟨1075823, by decide⟩
    (prefixCache 10 19225) (prefixPartial 10 19225) = false := by
  decide +kernel

theorem node_context_10_19225_1075823 : EJMOriginalGlobalDAGData.nodes 11 ⟨1075823, by decide⟩ =
    .split (coordinate 10) (![⟨1075733, by decide⟩,⟨1075761, by decide⟩,⟨1075795, by decide⟩,⟨1075822, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19225_1075823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19225 ⟨1075823, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19225
    ⟨1075823, by decide⟩ (by decide) (![⟨1075733, by decide⟩,⟨1075761, by decide⟩,⟨1075795, by decide⟩,⟨1075822, by decide⟩]) unmarked_context_10_19225_1075823 node_context_10_19225_1075823
  intro a
  fin_cases a
  · exact context_11_76900_1075733
  · exact context_11_76901_1075761
  · exact context_11_76902_1075795
  · exact context_11_76903_1075822

theorem selected_cut_39641 : selected 10 ⟨1075847, by decide⟩
    (prefixPartial 11 76904) = some ⟨11, 2, 0, 1075847, 76904, 2241, 262144⟩ := by
  decide +kernel

theorem context_11_76904_1075847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76904 ⟨1075847, by decide⟩ :=
  accepted_of_selected 11 76904 ⟨1075847, by decide⟩ ⟨11, 2, 0, 1075847, 76904, 2241, 262144⟩
    (by decide) selected_cut_39641

theorem selected_cut_39642 : selected 10 ⟨1075863, by decide⟩
    (prefixPartial 11 76905) = some ⟨11, 2, 0, 1075863, 76905, 1417, 262144⟩ := by
  decide +kernel

theorem context_11_76905_1075863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76905 ⟨1075863, by decide⟩ :=
  accepted_of_selected 11 76905 ⟨1075863, by decide⟩ ⟨11, 2, 0, 1075863, 76905, 1417, 262144⟩
    (by decide) selected_cut_39642

theorem selected_cut_39643 : selected 10 ⟨1075875, by decide⟩
    (prefixPartial 11 76906) = some ⟨11, 2, 0, 1075875, 76906, 269, 262144⟩ := by
  decide +kernel

theorem context_11_76906_1075875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76906 ⟨1075875, by decide⟩ :=
  accepted_of_selected 11 76906 ⟨1075875, by decide⟩ ⟨11, 2, 0, 1075875, 76906, 269, 262144⟩
    (by decide) selected_cut_39643

theorem selected_cut_39644 : selected 10 ⟨1075900, by decide⟩
    (prefixPartial 11 76907) = some ⟨11, 2, 0, 1075900, 76907, 2133, 262144⟩ := by
  decide +kernel

theorem context_11_76907_1075900 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76907 ⟨1075900, by decide⟩ :=
  accepted_of_selected 11 76907 ⟨1075900, by decide⟩ ⟨11, 2, 0, 1075900, 76907, 2133, 262144⟩
    (by decide) selected_cut_39644

theorem unmarked_context_10_19226_1075901 : frontier 11 ⟨1075901, by decide⟩
    (prefixCache 10 19226) (prefixPartial 10 19226) = false := by
  decide +kernel

theorem node_context_10_19226_1075901 : EJMOriginalGlobalDAGData.nodes 11 ⟨1075901, by decide⟩ =
    .split (coordinate 10) (![⟨1075847, by decide⟩,⟨1075863, by decide⟩,⟨1075875, by decide⟩,⟨1075900, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19226_1075901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19226 ⟨1075901, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19226
    ⟨1075901, by decide⟩ (by decide) (![⟨1075847, by decide⟩,⟨1075863, by decide⟩,⟨1075875, by decide⟩,⟨1075900, by decide⟩]) unmarked_context_10_19226_1075901 node_context_10_19226_1075901
  intro a
  fin_cases a
  · exact context_11_76904_1075847
  · exact context_11_76905_1075863
  · exact context_11_76906_1075875
  · exact context_11_76907_1075900

theorem selected_cut_39645 : selected 10 ⟨1075924, by decide⟩
    (prefixPartial 11 76908) = some ⟨11, 2, 0, 1075924, 76908, 1837, 262144⟩ := by
  decide +kernel

theorem context_11_76908_1075924 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76908 ⟨1075924, by decide⟩ :=
  accepted_of_selected 11 76908 ⟨1075924, by decide⟩ ⟨11, 2, 0, 1075924, 76908, 1837, 262144⟩
    (by decide) selected_cut_39645

theorem selected_cut_39646 : selected 10 ⟨1075939, by decide⟩
    (prefixPartial 11 76909) = some ⟨11, 2, 0, 1075939, 76909, 1221, 262144⟩ := by
  decide +kernel

theorem context_11_76909_1075939 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76909 ⟨1075939, by decide⟩ :=
  accepted_of_selected 11 76909 ⟨1075939, by decide⟩ ⟨11, 2, 0, 1075939, 76909, 1221, 262144⟩
    (by decide) selected_cut_39646

theorem selected_cut_39647 : selected 10 ⟨1075962, by decide⟩
    (prefixPartial 11 76910) = some ⟨11, 2, 0, 1075962, 76910, 1789, 262144⟩ := by
  decide +kernel

theorem context_11_76910_1075962 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76910 ⟨1075962, by decide⟩ :=
  accepted_of_selected 11 76910 ⟨1075962, by decide⟩ ⟨11, 2, 0, 1075962, 76910, 1789, 262144⟩
    (by decide) selected_cut_39647

theorem selected_cut_39648 : selected 10 ⟨1075979, by decide⟩
    (prefixPartial 11 76911) = some ⟨11, 2, 0, 1075979, 76911, 1677, 262144⟩ := by
  decide +kernel

theorem context_11_76911_1075979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76911 ⟨1075979, by decide⟩ :=
  accepted_of_selected 11 76911 ⟨1075979, by decide⟩ ⟨11, 2, 0, 1075979, 76911, 1677, 262144⟩
    (by decide) selected_cut_39648

theorem unmarked_context_10_19227_1075980 : frontier 11 ⟨1075980, by decide⟩
    (prefixCache 10 19227) (prefixPartial 10 19227) = false := by
  decide +kernel

theorem node_context_10_19227_1075980 : EJMOriginalGlobalDAGData.nodes 11 ⟨1075980, by decide⟩ =
    .split (coordinate 10) (![⟨1075924, by decide⟩,⟨1075939, by decide⟩,⟨1075962, by decide⟩,⟨1075979, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19227_1075980 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19227 ⟨1075980, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19227
    ⟨1075980, by decide⟩ (by decide) (![⟨1075924, by decide⟩,⟨1075939, by decide⟩,⟨1075962, by decide⟩,⟨1075979, by decide⟩]) unmarked_context_10_19227_1075980 node_context_10_19227_1075980
  intro a
  fin_cases a
  · exact context_11_76908_1075924
  · exact context_11_76909_1075939
  · exact context_11_76910_1075962
  · exact context_11_76911_1075979

theorem unmarked_context_9_4806_1075981 : frontier 12 ⟨1075981, by decide⟩
    (prefixCache 9 4806) (prefixPartial 9 4806) = false := by
  decide +kernel

theorem node_context_9_4806_1075981 : EJMOriginalGlobalDAGData.nodes 12 ⟨1075981, by decide⟩ =
    .split (coordinate 9) (![⟨1075686, by decide⟩,⟨1075823, by decide⟩,⟨1075901, by decide⟩,⟨1075980, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4806_1075981 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4806 ⟨1075981, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4806
    ⟨1075981, by decide⟩ (by decide) (![⟨1075686, by decide⟩,⟨1075823, by decide⟩,⟨1075901, by decide⟩,⟨1075980, by decide⟩]) unmarked_context_9_4806_1075981 node_context_9_4806_1075981
  intro a
  fin_cases a
  · exact context_10_19224_1075686
  · exact context_10_19225_1075823
  · exact context_10_19226_1075901
  · exact context_10_19227_1075980

theorem selected_cut_39649 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 76912) = some ⟨11, 1, 0, 907917, 76912, 1, 262144⟩ := by
  decide +kernel

theorem context_11_76912_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76912 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 76912 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 76912, 1, 262144⟩
    (by decide) selected_cut_39649

theorem selected_cut_39650 : selected 10 ⟨1076002, by decide⟩
    (prefixPartial 11 76913) = some ⟨11, 2, 0, 1076002, 76913, 1597, 262144⟩ := by
  decide +kernel

theorem context_11_76913_1076002 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76913 ⟨1076002, by decide⟩ :=
  accepted_of_selected 11 76913 ⟨1076002, by decide⟩ ⟨11, 2, 0, 1076002, 76913, 1597, 262144⟩
    (by decide) selected_cut_39650

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
