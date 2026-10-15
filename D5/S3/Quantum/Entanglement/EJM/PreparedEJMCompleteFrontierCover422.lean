/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover421
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_40516 : selected 9 ⟨1102531, by decide⟩
    (prefixPartial 12 310060) = some ⟨12, 2, 0, 1102531, 310060, 2637, 65536⟩ := by
  decide +kernel

theorem context_12_310060_1102531 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310060 ⟨1102531, by decide⟩ :=
  accepted_of_selected 12 310060 ⟨1102531, by decide⟩ ⟨12, 2, 0, 1102531, 310060, 2637, 65536⟩
    (by decide) selected_cut_40516

theorem selected_cut_40517 : selected 9 ⟨1102571, by decide⟩
    (prefixPartial 12 310061) = some ⟨12, 2, 0, 1102571, 310061, 2717, 65536⟩ := by
  decide +kernel

theorem context_12_310061_1102571 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310061 ⟨1102571, by decide⟩ :=
  accepted_of_selected 12 310061 ⟨1102571, by decide⟩ ⟨12, 2, 0, 1102571, 310061, 2717, 65536⟩
    (by decide) selected_cut_40517

theorem selected_cut_40518 : selected 9 ⟨1102605, by decide⟩
    (prefixPartial 12 310062) = some ⟨12, 2, 0, 1102605, 310062, 2381, 65536⟩ := by
  decide +kernel

theorem context_12_310062_1102605 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310062 ⟨1102605, by decide⟩ :=
  accepted_of_selected 12 310062 ⟨1102605, by decide⟩ ⟨12, 2, 0, 1102605, 310062, 2381, 65536⟩
    (by decide) selected_cut_40518

theorem selected_cut_40519 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 310063) = some ⟨12, 1, 0, 903806, 310063, 1, 65536⟩ := by
  decide +kernel

theorem context_12_310063_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310063 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 310063 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 310063, 1, 65536⟩
    (by decide) selected_cut_40519

theorem unmarked_context_11_77515_1102606 : frontier 10 ⟨1102606, by decide⟩
    (prefixCache 11 77515) (prefixPartial 11 77515) = false := by
  decide +kernel

theorem node_context_11_77515_1102606 : EJMOriginalGlobalDAGData.nodes 10 ⟨1102606, by decide⟩ =
    .split (coordinate 11) (![⟨1102531, by decide⟩,⟨1102571, by decide⟩,⟨1102605, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77515_1102606 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77515 ⟨1102606, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77515
    ⟨1102606, by decide⟩ (by decide) (![⟨1102531, by decide⟩,⟨1102571, by decide⟩,⟨1102605, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_77515_1102606 node_context_11_77515_1102606
  intro a
  fin_cases a
  · exact context_12_310060_1102531
  · exact context_12_310061_1102571
  · exact context_12_310062_1102605
  · exact context_12_310063_903806

theorem unmarked_context_10_19378_1102607 : frontier 11 ⟨1102607, by decide⟩
    (prefixCache 10 19378) (prefixPartial 10 19378) = false := by
  decide +kernel

theorem node_context_10_19378_1102607 : EJMOriginalGlobalDAGData.nodes 11 ⟨1102607, by decide⟩ =
    .split (coordinate 10) (![⟨1102321, by decide⟩,⟨1102491, by decide⟩,⟨900587, by decide⟩,⟨1102606, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19378_1102607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19378 ⟨1102607, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19378
    ⟨1102607, by decide⟩ (by decide) (![⟨1102321, by decide⟩,⟨1102491, by decide⟩,⟨900587, by decide⟩,⟨1102606, by decide⟩]) unmarked_context_10_19378_1102607 node_context_10_19378_1102607
  intro a
  fin_cases a
  · exact context_11_77512_1102321
  · exact context_11_77513_1102491
  · exact context_11_77514_900587
  · exact context_11_77515_1102606

theorem selected_cut_40520 : selected 9 ⟨1082322, by decide⟩
    (prefixPartial 12 310064) = some ⟨12, 1, 0, 1082322, 310064, 1, 65536⟩ := by
  decide +kernel

theorem context_12_310064_1082322 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310064 ⟨1082322, by decide⟩ :=
  accepted_of_selected 12 310064 ⟨1082322, by decide⟩ ⟨12, 1, 0, 1082322, 310064, 1, 65536⟩
    (by decide) selected_cut_40520

theorem selected_cut_40521 : selected 9 ⟨1102642, by decide⟩
    (prefixPartial 12 310065) = some ⟨12, 2, 0, 1102642, 310065, 2617, 65536⟩ := by
  decide +kernel

theorem context_12_310065_1102642 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310065 ⟨1102642, by decide⟩ :=
  accepted_of_selected 12 310065 ⟨1102642, by decide⟩ ⟨12, 2, 0, 1102642, 310065, 2617, 65536⟩
    (by decide) selected_cut_40521

theorem selected_cut_40522 : selected 9 ⟨1102680, by decide⟩
    (prefixPartial 12 310066) = some ⟨12, 2, 0, 1102680, 310066, 2337, 65536⟩ := by
  decide +kernel

theorem context_12_310066_1102680 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310066 ⟨1102680, by decide⟩ :=
  accepted_of_selected 12 310066 ⟨1102680, by decide⟩ ⟨12, 2, 0, 1102680, 310066, 2337, 65536⟩
    (by decide) selected_cut_40522

theorem selected_cut_40523 : selected 9 ⟨1102712, by decide⟩
    (prefixPartial 12 310067) = some ⟨12, 2, 0, 1102712, 310067, 1949, 65536⟩ := by
  decide +kernel

theorem context_12_310067_1102712 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310067 ⟨1102712, by decide⟩ :=
  accepted_of_selected 12 310067 ⟨1102712, by decide⟩ ⟨12, 2, 0, 1102712, 310067, 1949, 65536⟩
    (by decide) selected_cut_40523

theorem unmarked_context_11_77516_1102713 : frontier 10 ⟨1102713, by decide⟩
    (prefixCache 11 77516) (prefixPartial 11 77516) = false := by
  decide +kernel

theorem node_context_11_77516_1102713 : EJMOriginalGlobalDAGData.nodes 10 ⟨1102713, by decide⟩ =
    .split (coordinate 11) (![⟨1082322, by decide⟩,⟨1102642, by decide⟩,⟨1102680, by decide⟩,⟨1102712, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77516_1102713 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77516 ⟨1102713, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77516
    ⟨1102713, by decide⟩ (by decide) (![⟨1082322, by decide⟩,⟨1102642, by decide⟩,⟨1102680, by decide⟩,⟨1102712, by decide⟩]) unmarked_context_11_77516_1102713 node_context_11_77516_1102713
  intro a
  fin_cases a
  · exact context_12_310064_1082322
  · exact context_12_310065_1102642
  · exact context_12_310066_1102680
  · exact context_12_310067_1102712

theorem selected_cut_40524 : selected 9 ⟨1102751, by decide⟩
    (prefixPartial 12 310068) = some ⟨12, 2, 0, 1102751, 310068, 2445, 65536⟩ := by
  decide +kernel

theorem context_12_310068_1102751 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310068 ⟨1102751, by decide⟩ :=
  accepted_of_selected 12 310068 ⟨1102751, by decide⟩ ⟨12, 2, 0, 1102751, 310068, 2445, 65536⟩
    (by decide) selected_cut_40524

theorem selected_cut_40525 : selected 9 ⟨1102793, by decide⟩
    (prefixPartial 12 310069) = some ⟨12, 2, 0, 1102793, 310069, 2833, 65536⟩ := by
  decide +kernel

theorem context_12_310069_1102793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310069 ⟨1102793, by decide⟩ :=
  accepted_of_selected 12 310069 ⟨1102793, by decide⟩ ⟨12, 2, 0, 1102793, 310069, 2833, 65536⟩
    (by decide) selected_cut_40525

theorem selected_cut_40526 : selected 9 ⟨1102834, by decide⟩
    (prefixPartial 12 310070) = some ⟨12, 2, 0, 1102834, 310070, 2509, 65536⟩ := by
  decide +kernel

theorem context_12_310070_1102834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310070 ⟨1102834, by decide⟩ :=
  accepted_of_selected 12 310070 ⟨1102834, by decide⟩ ⟨12, 2, 0, 1102834, 310070, 2509, 65536⟩
    (by decide) selected_cut_40526

theorem selected_cut_40527 : selected 9 ⟨1102867, by decide⟩
    (prefixPartial 12 310071) = some ⟨12, 2, 0, 1102867, 310071, 2189, 65536⟩ := by
  decide +kernel

theorem context_12_310071_1102867 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310071 ⟨1102867, by decide⟩ :=
  accepted_of_selected 12 310071 ⟨1102867, by decide⟩ ⟨12, 2, 0, 1102867, 310071, 2189, 65536⟩
    (by decide) selected_cut_40527

theorem unmarked_context_11_77517_1102868 : frontier 10 ⟨1102868, by decide⟩
    (prefixCache 11 77517) (prefixPartial 11 77517) = false := by
  decide +kernel

theorem node_context_11_77517_1102868 : EJMOriginalGlobalDAGData.nodes 10 ⟨1102868, by decide⟩ =
    .split (coordinate 11) (![⟨1102751, by decide⟩,⟨1102793, by decide⟩,⟨1102834, by decide⟩,⟨1102867, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77517_1102868 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77517 ⟨1102868, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77517
    ⟨1102868, by decide⟩ (by decide) (![⟨1102751, by decide⟩,⟨1102793, by decide⟩,⟨1102834, by decide⟩,⟨1102867, by decide⟩]) unmarked_context_11_77517_1102868 node_context_11_77517_1102868
  intro a
  fin_cases a
  · exact context_12_310068_1102751
  · exact context_12_310069_1102793
  · exact context_12_310070_1102834
  · exact context_12_310071_1102867

theorem selected_cut_40528 : selected 9 ⟨1102898, by decide⟩
    (prefixPartial 12 310072) = some ⟨12, 2, 0, 1102898, 310072, 2125, 65536⟩ := by
  decide +kernel

theorem context_12_310072_1102898 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310072 ⟨1102898, by decide⟩ :=
  accepted_of_selected 12 310072 ⟨1102898, by decide⟩ ⟨12, 2, 0, 1102898, 310072, 2125, 65536⟩
    (by decide) selected_cut_40528

theorem selected_cut_40529 : selected 9 ⟨1102932, by decide⟩
    (prefixPartial 12 310073) = some ⟨12, 2, 0, 1102932, 310073, 2393, 65536⟩ := by
  decide +kernel

theorem context_12_310073_1102932 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310073 ⟨1102932, by decide⟩ :=
  accepted_of_selected 12 310073 ⟨1102932, by decide⟩ ⟨12, 2, 0, 1102932, 310073, 2393, 65536⟩
    (by decide) selected_cut_40529

theorem selected_cut_40530 : selected 9 ⟨1102963, by decide⟩
    (prefixPartial 12 310074) = some ⟨12, 2, 0, 1102963, 310074, 2209, 65536⟩ := by
  decide +kernel

theorem context_12_310074_1102963 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310074 ⟨1102963, by decide⟩ :=
  accepted_of_selected 12 310074 ⟨1102963, by decide⟩ ⟨12, 2, 0, 1102963, 310074, 2209, 65536⟩
    (by decide) selected_cut_40530

theorem selected_cut_40531 : selected 9 ⟨1102994, by decide⟩
    (prefixPartial 12 310075) = some ⟨12, 2, 0, 1102994, 310075, 2041, 65536⟩ := by
  decide +kernel

theorem context_12_310075_1102994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310075 ⟨1102994, by decide⟩ :=
  accepted_of_selected 12 310075 ⟨1102994, by decide⟩ ⟨12, 2, 0, 1102994, 310075, 2041, 65536⟩
    (by decide) selected_cut_40531

theorem unmarked_context_11_77518_1102995 : frontier 10 ⟨1102995, by decide⟩
    (prefixCache 11 77518) (prefixPartial 11 77518) = false := by
  decide +kernel

theorem node_context_11_77518_1102995 : EJMOriginalGlobalDAGData.nodes 10 ⟨1102995, by decide⟩ =
    .split (coordinate 11) (![⟨1102898, by decide⟩,⟨1102932, by decide⟩,⟨1102963, by decide⟩,⟨1102994, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77518_1102995 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77518 ⟨1102995, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77518
    ⟨1102995, by decide⟩ (by decide) (![⟨1102898, by decide⟩,⟨1102932, by decide⟩,⟨1102963, by decide⟩,⟨1102994, by decide⟩]) unmarked_context_11_77518_1102995 node_context_11_77518_1102995
  intro a
  fin_cases a
  · exact context_12_310072_1102898
  · exact context_12_310073_1102932
  · exact context_12_310074_1102963
  · exact context_12_310075_1102994

theorem selected_cut_40532 : selected 9 ⟨1103033, by decide⟩
    (prefixPartial 12 310076) = some ⟨12, 2, 0, 1103033, 310076, 2425, 65536⟩ := by
  decide +kernel

theorem context_12_310076_1103033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310076 ⟨1103033, by decide⟩ :=
  accepted_of_selected 12 310076 ⟨1103033, by decide⟩ ⟨12, 2, 0, 1103033, 310076, 2425, 65536⟩
    (by decide) selected_cut_40532

theorem selected_cut_40533 : selected 9 ⟨1103075, by decide⟩
    (prefixPartial 12 310077) = some ⟨12, 2, 0, 1103075, 310077, 2573, 65536⟩ := by
  decide +kernel

theorem context_12_310077_1103075 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310077 ⟨1103075, by decide⟩ :=
  accepted_of_selected 12 310077 ⟨1103075, by decide⟩ ⟨12, 2, 0, 1103075, 310077, 2573, 65536⟩
    (by decide) selected_cut_40533

theorem selected_cut_40534 : selected 9 ⟨1103118, by decide⟩
    (prefixPartial 12 310078) = some ⟨12, 2, 0, 1103118, 310078, 2405, 65536⟩ := by
  decide +kernel

theorem context_12_310078_1103118 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310078 ⟨1103118, by decide⟩ :=
  accepted_of_selected 12 310078 ⟨1103118, by decide⟩ ⟨12, 2, 0, 1103118, 310078, 2405, 65536⟩
    (by decide) selected_cut_40534

theorem selected_cut_40535 : selected 9 ⟨762109, by decide⟩
    (prefixPartial 12 310079) = some ⟨12, 1, 0, 762109, 310079, 1, 65536⟩ := by
  decide +kernel

theorem context_12_310079_762109 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310079 ⟨762109, by decide⟩ :=
  accepted_of_selected 12 310079 ⟨762109, by decide⟩ ⟨12, 1, 0, 762109, 310079, 1, 65536⟩
    (by decide) selected_cut_40535

theorem unmarked_context_11_77519_1103119 : frontier 10 ⟨1103119, by decide⟩
    (prefixCache 11 77519) (prefixPartial 11 77519) = false := by
  decide +kernel

theorem node_context_11_77519_1103119 : EJMOriginalGlobalDAGData.nodes 10 ⟨1103119, by decide⟩ =
    .split (coordinate 11) (![⟨1103033, by decide⟩,⟨1103075, by decide⟩,⟨1103118, by decide⟩,⟨762109, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77519_1103119 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77519 ⟨1103119, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77519
    ⟨1103119, by decide⟩ (by decide) (![⟨1103033, by decide⟩,⟨1103075, by decide⟩,⟨1103118, by decide⟩,⟨762109, by decide⟩]) unmarked_context_11_77519_1103119 node_context_11_77519_1103119
  intro a
  fin_cases a
  · exact context_12_310076_1103033
  · exact context_12_310077_1103075
  · exact context_12_310078_1103118
  · exact context_12_310079_762109

theorem unmarked_context_10_19379_1103120 : frontier 11 ⟨1103120, by decide⟩
    (prefixCache 10 19379) (prefixPartial 10 19379) = false := by
  decide +kernel

theorem node_context_10_19379_1103120 : EJMOriginalGlobalDAGData.nodes 11 ⟨1103120, by decide⟩ =
    .split (coordinate 10) (![⟨1102713, by decide⟩,⟨1102868, by decide⟩,⟨1102995, by decide⟩,⟨1103119, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19379_1103120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19379 ⟨1103120, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19379
    ⟨1103120, by decide⟩ (by decide) (![⟨1102713, by decide⟩,⟨1102868, by decide⟩,⟨1102995, by decide⟩,⟨1103119, by decide⟩]) unmarked_context_10_19379_1103120 node_context_10_19379_1103120
  intro a
  fin_cases a
  · exact context_11_77516_1102713
  · exact context_11_77517_1102868
  · exact context_11_77518_1102995
  · exact context_11_77519_1103119

theorem unmarked_context_9_4844_1103121 : frontier 12 ⟨1103121, by decide⟩
    (prefixCache 9 4844) (prefixPartial 9 4844) = false := by
  decide +kernel

theorem node_context_9_4844_1103121 : EJMOriginalGlobalDAGData.nodes 12 ⟨1103121, by decide⟩ =
    .split (coordinate 9) (![⟨1101614, by decide⟩,⟨1102211, by decide⟩,⟨1102607, by decide⟩,⟨1103120, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4844_1103121 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4844 ⟨1103121, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4844
    ⟨1103121, by decide⟩ (by decide) (![⟨1101614, by decide⟩,⟨1102211, by decide⟩,⟨1102607, by decide⟩,⟨1103120, by decide⟩]) unmarked_context_9_4844_1103121 node_context_9_4844_1103121
  intro a
  fin_cases a
  · exact context_10_19376_1101614
  · exact context_10_19377_1102211
  · exact context_10_19378_1102607
  · exact context_10_19379_1103120

theorem selected_cut_40536 : selected 9 ⟨1103233, by decide⟩
    (prefixPartial 12 310080) = some ⟨12, 2, 0, 1103233, 310080, 1369, 65536⟩ := by
  decide +kernel

theorem context_12_310080_1103233 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310080 ⟨1103233, by decide⟩ :=
  accepted_of_selected 12 310080 ⟨1103233, by decide⟩ ⟨12, 2, 0, 1103233, 310080, 1369, 65536⟩
    (by decide) selected_cut_40536

theorem selected_cut_40537 : selected 9 ⟨1103273, by decide⟩
    (prefixPartial 12 310081) = some ⟨12, 2, 0, 1103273, 310081, 2441, 65536⟩ := by
  decide +kernel

theorem context_12_310081_1103273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310081 ⟨1103273, by decide⟩ :=
  accepted_of_selected 12 310081 ⟨1103273, by decide⟩ ⟨12, 2, 0, 1103273, 310081, 2441, 65536⟩
    (by decide) selected_cut_40537

theorem selected_cut_40538 : selected 9 ⟨1103311, by decide⟩
    (prefixPartial 12 310082) = some ⟨12, 2, 0, 1103311, 310082, 2425, 65536⟩ := by
  decide +kernel

theorem context_12_310082_1103311 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310082 ⟨1103311, by decide⟩ :=
  accepted_of_selected 12 310082 ⟨1103311, by decide⟩ ⟨12, 2, 0, 1103311, 310082, 2425, 65536⟩
    (by decide) selected_cut_40538

theorem selected_cut_40539 : selected 9 ⟨1103340, by decide⟩
    (prefixPartial 12 310083) = some ⟨12, 2, 0, 1103340, 310083, 1973, 65536⟩ := by
  decide +kernel

theorem context_12_310083_1103340 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310083 ⟨1103340, by decide⟩ :=
  accepted_of_selected 12 310083 ⟨1103340, by decide⟩ ⟨12, 2, 0, 1103340, 310083, 1973, 65536⟩
    (by decide) selected_cut_40539

theorem unmarked_context_11_77520_1103341 : frontier 10 ⟨1103341, by decide⟩
    (prefixCache 11 77520) (prefixPartial 11 77520) = false := by
  decide +kernel

theorem node_context_11_77520_1103341 : EJMOriginalGlobalDAGData.nodes 10 ⟨1103341, by decide⟩ =
    .split (coordinate 11) (![⟨1103233, by decide⟩,⟨1103273, by decide⟩,⟨1103311, by decide⟩,⟨1103340, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77520_1103341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77520 ⟨1103341, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77520
    ⟨1103341, by decide⟩ (by decide) (![⟨1103233, by decide⟩,⟨1103273, by decide⟩,⟨1103311, by decide⟩,⟨1103340, by decide⟩]) unmarked_context_11_77520_1103341 node_context_11_77520_1103341
  intro a
  fin_cases a
  · exact context_12_310080_1103233
  · exact context_12_310081_1103273
  · exact context_12_310082_1103311
  · exact context_12_310083_1103340

theorem selected_cut_40540 : selected 9 ⟨1103398, by decide⟩
    (prefixPartial 12 310084) = some ⟨12, 2, 0, 1103398, 310084, 2893, 65536⟩ := by
  decide +kernel

theorem context_12_310084_1103398 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310084 ⟨1103398, by decide⟩ :=
  accepted_of_selected 12 310084 ⟨1103398, by decide⟩ ⟨12, 2, 0, 1103398, 310084, 2893, 65536⟩
    (by decide) selected_cut_40540

theorem selected_cut_40541 : selected 9 ⟨1025817, by decide⟩
    (prefixPartial 12 310085) = some ⟨12, 1, 0, 1025817, 310085, 1, 65536⟩ := by
  decide +kernel

theorem context_12_310085_1025817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310085 ⟨1025817, by decide⟩ :=
  accepted_of_selected 12 310085 ⟨1025817, by decide⟩ ⟨12, 1, 0, 1025817, 310085, 1, 65536⟩
    (by decide) selected_cut_40541

theorem selected_cut_40542 : selected 9 ⟨1103449, by decide⟩
    (prefixPartial 12 310086) = some ⟨12, 2, 0, 1103449, 310086, 2541, 65536⟩ := by
  decide +kernel

theorem context_12_310086_1103449 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310086 ⟨1103449, by decide⟩ :=
  accepted_of_selected 12 310086 ⟨1103449, by decide⟩ ⟨12, 2, 0, 1103449, 310086, 2541, 65536⟩
    (by decide) selected_cut_40542

theorem selected_cut_40543 : selected 9 ⟨1103481, by decide⟩
    (prefixPartial 12 310087) = some ⟨12, 2, 0, 1103481, 310087, 2121, 65536⟩ := by
  decide +kernel

theorem context_12_310087_1103481 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310087 ⟨1103481, by decide⟩ :=
  accepted_of_selected 12 310087 ⟨1103481, by decide⟩ ⟨12, 2, 0, 1103481, 310087, 2121, 65536⟩
    (by decide) selected_cut_40543

theorem unmarked_context_11_77521_1103482 : frontier 10 ⟨1103482, by decide⟩
    (prefixCache 11 77521) (prefixPartial 11 77521) = false := by
  decide +kernel

theorem node_context_11_77521_1103482 : EJMOriginalGlobalDAGData.nodes 10 ⟨1103482, by decide⟩ =
    .split (coordinate 11) (![⟨1103398, by decide⟩,⟨1025817, by decide⟩,⟨1103449, by decide⟩,⟨1103481, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77521_1103482 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77521 ⟨1103482, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77521
    ⟨1103482, by decide⟩ (by decide) (![⟨1103398, by decide⟩,⟨1025817, by decide⟩,⟨1103449, by decide⟩,⟨1103481, by decide⟩]) unmarked_context_11_77521_1103482 node_context_11_77521_1103482
  intro a
  fin_cases a
  · exact context_12_310084_1103398
  · exact context_12_310085_1025817
  · exact context_12_310086_1103449
  · exact context_12_310087_1103481

theorem selected_cut_40544 : selected 9 ⟨1103532, by decide⟩
    (prefixPartial 12 310088) = some ⟨12, 2, 0, 1103532, 310088, 2621, 65536⟩ := by
  decide +kernel

theorem context_12_310088_1103532 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310088 ⟨1103532, by decide⟩ :=
  accepted_of_selected 12 310088 ⟨1103532, by decide⟩ ⟨12, 2, 0, 1103532, 310088, 2621, 65536⟩
    (by decide) selected_cut_40544

theorem selected_cut_40545 : selected 9 ⟨1103571, by decide⟩
    (prefixPartial 12 310089) = some ⟨12, 2, 0, 1103571, 310089, 2269, 65536⟩ := by
  decide +kernel

theorem context_12_310089_1103571 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310089 ⟨1103571, by decide⟩ :=
  accepted_of_selected 12 310089 ⟨1103571, by decide⟩ ⟨12, 2, 0, 1103571, 310089, 2269, 65536⟩
    (by decide) selected_cut_40545

theorem selected_cut_40546 : selected 9 ⟨1103612, by decide⟩
    (prefixPartial 12 310090) = some ⟨12, 2, 0, 1103612, 310090, 2149, 65536⟩ := by
  decide +kernel

theorem context_12_310090_1103612 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310090 ⟨1103612, by decide⟩ :=
  accepted_of_selected 12 310090 ⟨1103612, by decide⟩ ⟨12, 2, 0, 1103612, 310090, 2149, 65536⟩
    (by decide) selected_cut_40546

theorem selected_cut_40547 : selected 9 ⟨1103640, by decide⟩
    (prefixPartial 12 310091) = some ⟨12, 2, 0, 1103640, 310091, 1969, 65536⟩ := by
  decide +kernel

theorem context_12_310091_1103640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310091 ⟨1103640, by decide⟩ :=
  accepted_of_selected 12 310091 ⟨1103640, by decide⟩ ⟨12, 2, 0, 1103640, 310091, 1969, 65536⟩
    (by decide) selected_cut_40547

theorem unmarked_context_11_77522_1103641 : frontier 10 ⟨1103641, by decide⟩
    (prefixCache 11 77522) (prefixPartial 11 77522) = false := by
  decide +kernel

theorem node_context_11_77522_1103641 : EJMOriginalGlobalDAGData.nodes 10 ⟨1103641, by decide⟩ =
    .split (coordinate 11) (![⟨1103532, by decide⟩,⟨1103571, by decide⟩,⟨1103612, by decide⟩,⟨1103640, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77522_1103641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77522 ⟨1103641, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77522
    ⟨1103641, by decide⟩ (by decide) (![⟨1103532, by decide⟩,⟨1103571, by decide⟩,⟨1103612, by decide⟩,⟨1103640, by decide⟩]) unmarked_context_11_77522_1103641 node_context_11_77522_1103641
  intro a
  fin_cases a
  · exact context_12_310088_1103532
  · exact context_12_310089_1103571
  · exact context_12_310090_1103612
  · exact context_12_310091_1103640

theorem selected_cut_40548 : selected 9 ⟨1103693, by decide⟩
    (prefixPartial 12 310092) = some ⟨12, 2, 0, 1103693, 310092, 2733, 65536⟩ := by
  decide +kernel

theorem context_12_310092_1103693 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310092 ⟨1103693, by decide⟩ :=
  accepted_of_selected 12 310092 ⟨1103693, by decide⟩ ⟨12, 2, 0, 1103693, 310092, 2733, 65536⟩
    (by decide) selected_cut_40548

theorem selected_cut_40549 : selected 9 ⟨1103732, by decide⟩
    (prefixPartial 12 310093) = some ⟨12, 2, 0, 1103732, 310093, 2377, 65536⟩ := by
  decide +kernel

theorem context_12_310093_1103732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310093 ⟨1103732, by decide⟩ :=
  accepted_of_selected 12 310093 ⟨1103732, by decide⟩ ⟨12, 2, 0, 1103732, 310093, 2377, 65536⟩
    (by decide) selected_cut_40549

theorem selected_cut_40550 : selected 9 ⟨1103791, by decide⟩
    (prefixPartial 12 310094) = some ⟨12, 2, 0, 1103791, 310094, 2441, 65536⟩ := by
  decide +kernel

theorem context_12_310094_1103791 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310094 ⟨1103791, by decide⟩ :=
  accepted_of_selected 12 310094 ⟨1103791, by decide⟩ ⟨12, 2, 0, 1103791, 310094, 2441, 65536⟩
    (by decide) selected_cut_40550

theorem selected_cut_40551 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 310095) = some ⟨12, 1, 0, 903806, 310095, 1, 65536⟩ := by
  decide +kernel

theorem context_12_310095_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310095 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 310095 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 310095, 1, 65536⟩
    (by decide) selected_cut_40551

theorem unmarked_context_11_77523_1103792 : frontier 10 ⟨1103792, by decide⟩
    (prefixCache 11 77523) (prefixPartial 11 77523) = false := by
  decide +kernel

theorem node_context_11_77523_1103792 : EJMOriginalGlobalDAGData.nodes 10 ⟨1103792, by decide⟩ =
    .split (coordinate 11) (![⟨1103693, by decide⟩,⟨1103732, by decide⟩,⟨1103791, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77523_1103792 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77523 ⟨1103792, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77523
    ⟨1103792, by decide⟩ (by decide) (![⟨1103693, by decide⟩,⟨1103732, by decide⟩,⟨1103791, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_77523_1103792 node_context_11_77523_1103792
  intro a
  fin_cases a
  · exact context_12_310092_1103693
  · exact context_12_310093_1103732
  · exact context_12_310094_1103791
  · exact context_12_310095_903806

theorem unmarked_context_10_19380_1103793 : frontier 11 ⟨1103793, by decide⟩
    (prefixCache 10 19380) (prefixPartial 10 19380) = false := by
  decide +kernel

theorem node_context_10_19380_1103793 : EJMOriginalGlobalDAGData.nodes 11 ⟨1103793, by decide⟩ =
    .split (coordinate 10) (![⟨1103341, by decide⟩,⟨1103482, by decide⟩,⟨1103641, by decide⟩,⟨1103792, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19380_1103793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19380 ⟨1103793, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19380
    ⟨1103793, by decide⟩ (by decide) (![⟨1103341, by decide⟩,⟨1103482, by decide⟩,⟨1103641, by decide⟩,⟨1103792, by decide⟩]) unmarked_context_10_19380_1103793 node_context_10_19380_1103793
  intro a
  fin_cases a
  · exact context_11_77520_1103341
  · exact context_11_77521_1103482
  · exact context_11_77522_1103641
  · exact context_11_77523_1103792

theorem selected_cut_40552 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 19381) = some ⟨10, 1, 0, 893098, 19381, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_19381_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19381 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 19381 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 19381, 1, 1048576⟩
    (by decide) selected_cut_40552

theorem selected_cut_40553 : selected 9 ⟨1103812, by decide⟩
    (prefixPartial 12 310112) = some ⟨12, 2, 0, 1103812, 310112, 1613, 65536⟩ := by
  decide +kernel

theorem context_12_310112_1103812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310112 ⟨1103812, by decide⟩ :=
  accepted_of_selected 12 310112 ⟨1103812, by decide⟩ ⟨12, 2, 0, 1103812, 310112, 1613, 65536⟩
    (by decide) selected_cut_40553

theorem selected_cut_40554 : selected 9 ⟨1103834, by decide⟩
    (prefixPartial 12 310113) = some ⟨12, 2, 0, 1103834, 310113, 1669, 65536⟩ := by
  decide +kernel

theorem context_12_310113_1103834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310113 ⟨1103834, by decide⟩ :=
  accepted_of_selected 12 310113 ⟨1103834, by decide⟩ ⟨12, 2, 0, 1103834, 310113, 1669, 65536⟩
    (by decide) selected_cut_40554

theorem selected_cut_40555 : selected 9 ⟨1103859, by decide⟩
    (prefixPartial 12 310114) = some ⟨12, 2, 0, 1103859, 310114, 1649, 65536⟩ := by
  decide +kernel

theorem context_12_310114_1103859 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310114 ⟨1103859, by decide⟩ :=
  accepted_of_selected 12 310114 ⟨1103859, by decide⟩ ⟨12, 2, 0, 1103859, 310114, 1649, 65536⟩
    (by decide) selected_cut_40555

theorem selected_cut_40556 : selected 9 ⟨1103875, by decide⟩
    (prefixPartial 12 310115) = some ⟨12, 2, 0, 1103875, 310115, 1405, 65536⟩ := by
  decide +kernel

theorem context_12_310115_1103875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310115 ⟨1103875, by decide⟩ :=
  accepted_of_selected 12 310115 ⟨1103875, by decide⟩ ⟨12, 2, 0, 1103875, 310115, 1405, 65536⟩
    (by decide) selected_cut_40556

theorem unmarked_context_11_77528_1103876 : frontier 10 ⟨1103876, by decide⟩
    (prefixCache 11 77528) (prefixPartial 11 77528) = false := by
  decide +kernel

theorem node_context_11_77528_1103876 : EJMOriginalGlobalDAGData.nodes 10 ⟨1103876, by decide⟩ =
    .split (coordinate 11) (![⟨1103812, by decide⟩,⟨1103834, by decide⟩,⟨1103859, by decide⟩,⟨1103875, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77528_1103876 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77528 ⟨1103876, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77528
    ⟨1103876, by decide⟩ (by decide) (![⟨1103812, by decide⟩,⟨1103834, by decide⟩,⟨1103859, by decide⟩,⟨1103875, by decide⟩]) unmarked_context_11_77528_1103876 node_context_11_77528_1103876
  intro a
  fin_cases a
  · exact context_12_310112_1103812
  · exact context_12_310113_1103834
  · exact context_12_310114_1103859
  · exact context_12_310115_1103875

theorem selected_cut_40557 : selected 9 ⟨1103901, by decide⟩
    (prefixPartial 12 310116) = some ⟨12, 2, 0, 1103901, 310116, 1761, 65536⟩ := by
  decide +kernel

theorem context_12_310116_1103901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310116 ⟨1103901, by decide⟩ :=
  accepted_of_selected 12 310116 ⟨1103901, by decide⟩ ⟨12, 2, 0, 1103901, 310116, 1761, 65536⟩
    (by decide) selected_cut_40557

theorem selected_cut_40558 : selected 9 ⟨1084018, by decide⟩
    (prefixPartial 12 310117) = some ⟨12, 1, 0, 1084018, 310117, 1, 65536⟩ := by
  decide +kernel

theorem context_12_310117_1084018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310117 ⟨1084018, by decide⟩ :=
  accepted_of_selected 12 310117 ⟨1084018, by decide⟩ ⟨12, 1, 0, 1084018, 310117, 1, 65536⟩
    (by decide) selected_cut_40558

theorem selected_cut_40559 : selected 9 ⟨1103934, by decide⟩
    (prefixPartial 12 310118) = some ⟨12, 2, 0, 1103934, 310118, 1769, 65536⟩ := by
  decide +kernel

theorem context_12_310118_1103934 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310118 ⟨1103934, by decide⟩ :=
  accepted_of_selected 12 310118 ⟨1103934, by decide⟩ ⟨12, 2, 0, 1103934, 310118, 1769, 65536⟩
    (by decide) selected_cut_40559

theorem selected_cut_40560 : selected 9 ⟨1103959, by decide⟩
    (prefixPartial 12 310119) = some ⟨12, 2, 0, 1103959, 310119, 1621, 65536⟩ := by
  decide +kernel

theorem context_12_310119_1103959 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310119 ⟨1103959, by decide⟩ :=
  accepted_of_selected 12 310119 ⟨1103959, by decide⟩ ⟨12, 2, 0, 1103959, 310119, 1621, 65536⟩
    (by decide) selected_cut_40560

theorem unmarked_context_11_77529_1103960 : frontier 10 ⟨1103960, by decide⟩
    (prefixCache 11 77529) (prefixPartial 11 77529) = false := by
  decide +kernel

theorem node_context_11_77529_1103960 : EJMOriginalGlobalDAGData.nodes 10 ⟨1103960, by decide⟩ =
    .split (coordinate 11) (![⟨1103901, by decide⟩,⟨1084018, by decide⟩,⟨1103934, by decide⟩,⟨1103959, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77529_1103960 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77529 ⟨1103960, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77529
    ⟨1103960, by decide⟩ (by decide) (![⟨1103901, by decide⟩,⟨1084018, by decide⟩,⟨1103934, by decide⟩,⟨1103959, by decide⟩]) unmarked_context_11_77529_1103960 node_context_11_77529_1103960
  intro a
  fin_cases a
  · exact context_12_310116_1103901
  · exact context_12_310117_1084018
  · exact context_12_310118_1103934
  · exact context_12_310119_1103959

theorem selected_cut_40561 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 77530) = some ⟨11, 1, 0, 900587, 77530, 1, 262144⟩ := by
  decide +kernel

theorem context_11_77530_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77530 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 77530 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 77530, 1, 262144⟩
    (by decide) selected_cut_40561

theorem selected_cut_40562 : selected 9 ⟨1103990, by decide⟩
    (prefixPartial 12 310124) = some ⟨12, 2, 0, 1103990, 310124, 1721, 65536⟩ := by
  decide +kernel

theorem context_12_310124_1103990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310124 ⟨1103990, by decide⟩ :=
  accepted_of_selected 12 310124 ⟨1103990, by decide⟩ ⟨12, 2, 0, 1103990, 310124, 1721, 65536⟩
    (by decide) selected_cut_40562

theorem selected_cut_40563 : selected 9 ⟨1104019, by decide⟩
    (prefixPartial 12 310125) = some ⟨12, 2, 0, 1104019, 310125, 1697, 65536⟩ := by
  decide +kernel

theorem context_12_310125_1104019 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310125 ⟨1104019, by decide⟩ :=
  accepted_of_selected 12 310125 ⟨1104019, by decide⟩ ⟨12, 2, 0, 1104019, 310125, 1697, 65536⟩
    (by decide) selected_cut_40563

theorem selected_cut_40564 : selected 9 ⟨1104046, by decide⟩
    (prefixPartial 12 310126) = some ⟨12, 2, 0, 1104046, 310126, 1581, 65536⟩ := by
  decide +kernel

theorem context_12_310126_1104046 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310126 ⟨1104046, by decide⟩ :=
  accepted_of_selected 12 310126 ⟨1104046, by decide⟩ ⟨12, 2, 0, 1104046, 310126, 1581, 65536⟩
    (by decide) selected_cut_40564

theorem selected_cut_40565 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 310127) = some ⟨12, 1, 0, 903806, 310127, 1, 65536⟩ := by
  decide +kernel

theorem context_12_310127_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310127 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 310127 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 310127, 1, 65536⟩
    (by decide) selected_cut_40565

theorem unmarked_context_11_77531_1104047 : frontier 10 ⟨1104047, by decide⟩
    (prefixCache 11 77531) (prefixPartial 11 77531) = false := by
  decide +kernel

theorem node_context_11_77531_1104047 : EJMOriginalGlobalDAGData.nodes 10 ⟨1104047, by decide⟩ =
    .split (coordinate 11) (![⟨1103990, by decide⟩,⟨1104019, by decide⟩,⟨1104046, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77531_1104047 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77531 ⟨1104047, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77531
    ⟨1104047, by decide⟩ (by decide) (![⟨1103990, by decide⟩,⟨1104019, by decide⟩,⟨1104046, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_77531_1104047 node_context_11_77531_1104047
  intro a
  fin_cases a
  · exact context_12_310124_1103990
  · exact context_12_310125_1104019
  · exact context_12_310126_1104046
  · exact context_12_310127_903806

theorem unmarked_context_10_19382_1104048 : frontier 11 ⟨1104048, by decide⟩
    (prefixCache 10 19382) (prefixPartial 10 19382) = false := by
  decide +kernel

theorem node_context_10_19382_1104048 : EJMOriginalGlobalDAGData.nodes 11 ⟨1104048, by decide⟩ =
    .split (coordinate 10) (![⟨1103876, by decide⟩,⟨1103960, by decide⟩,⟨900587, by decide⟩,⟨1104047, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19382_1104048 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19382 ⟨1104048, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19382
    ⟨1104048, by decide⟩ (by decide) (![⟨1103876, by decide⟩,⟨1103960, by decide⟩,⟨900587, by decide⟩,⟨1104047, by decide⟩]) unmarked_context_10_19382_1104048 node_context_10_19382_1104048
  intro a
  fin_cases a
  · exact context_11_77528_1103876
  · exact context_11_77529_1103960
  · exact context_11_77530_900587
  · exact context_11_77531_1104047

theorem selected_cut_40566 : selected 9 ⟨1104070, by decide⟩
    (prefixPartial 12 310128) = some ⟨12, 2, 0, 1104070, 310128, 1469, 65536⟩ := by
  decide +kernel

theorem context_12_310128_1104070 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310128 ⟨1104070, by decide⟩ :=
  accepted_of_selected 12 310128 ⟨1104070, by decide⟩ ⟨12, 2, 0, 1104070, 310128, 1469, 65536⟩
    (by decide) selected_cut_40566

theorem selected_cut_40567 : selected 9 ⟨1104099, by decide⟩
    (prefixPartial 12 310129) = some ⟨12, 2, 0, 1104099, 310129, 1757, 65536⟩ := by
  decide +kernel

theorem context_12_310129_1104099 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310129 ⟨1104099, by decide⟩ :=
  accepted_of_selected 12 310129 ⟨1104099, by decide⟩ ⟨12, 2, 0, 1104099, 310129, 1757, 65536⟩
    (by decide) selected_cut_40567

theorem selected_cut_40568 : selected 9 ⟨1104126, by decide⟩
    (prefixPartial 12 310130) = some ⟨12, 2, 0, 1104126, 310130, 1617, 65536⟩ := by
  decide +kernel

theorem context_12_310130_1104126 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310130 ⟨1104126, by decide⟩ :=
  accepted_of_selected 12 310130 ⟨1104126, by decide⟩ ⟨12, 2, 0, 1104126, 310130, 1617, 65536⟩
    (by decide) selected_cut_40568

theorem selected_cut_40569 : selected 9 ⟨1104141, by decide⟩
    (prefixPartial 12 310131) = some ⟨12, 2, 0, 1104141, 310131, 1237, 65536⟩ := by
  decide +kernel

theorem context_12_310131_1104141 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310131 ⟨1104141, by decide⟩ :=
  accepted_of_selected 12 310131 ⟨1104141, by decide⟩ ⟨12, 2, 0, 1104141, 310131, 1237, 65536⟩
    (by decide) selected_cut_40569

theorem unmarked_context_11_77532_1104142 : frontier 10 ⟨1104142, by decide⟩
    (prefixCache 11 77532) (prefixPartial 11 77532) = false := by
  decide +kernel

theorem node_context_11_77532_1104142 : EJMOriginalGlobalDAGData.nodes 10 ⟨1104142, by decide⟩ =
    .split (coordinate 11) (![⟨1104070, by decide⟩,⟨1104099, by decide⟩,⟨1104126, by decide⟩,⟨1104141, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77532_1104142 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77532 ⟨1104142, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77532
    ⟨1104142, by decide⟩ (by decide) (![⟨1104070, by decide⟩,⟨1104099, by decide⟩,⟨1104126, by decide⟩,⟨1104141, by decide⟩]) unmarked_context_11_77532_1104142 node_context_11_77532_1104142
  intro a
  fin_cases a
  · exact context_12_310128_1104070
  · exact context_12_310129_1104099
  · exact context_12_310130_1104126
  · exact context_12_310131_1104141

theorem selected_cut_40570 : selected 9 ⟨1104165, by decide⟩
    (prefixPartial 12 310132) = some ⟨12, 2, 0, 1104165, 310132, 1565, 65536⟩ := by
  decide +kernel

theorem context_12_310132_1104165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310132 ⟨1104165, by decide⟩ :=
  accepted_of_selected 12 310132 ⟨1104165, by decide⟩ ⟨12, 2, 0, 1104165, 310132, 1565, 65536⟩
    (by decide) selected_cut_40570

theorem selected_cut_40571 : selected 9 ⟨1084018, by decide⟩
    (prefixPartial 12 310133) = some ⟨12, 1, 0, 1084018, 310133, 1, 65536⟩ := by
  decide +kernel

theorem context_12_310133_1084018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310133 ⟨1084018, by decide⟩ :=
  accepted_of_selected 12 310133 ⟨1084018, by decide⟩ ⟨12, 1, 0, 1084018, 310133, 1, 65536⟩
    (by decide) selected_cut_40571

theorem selected_cut_40572 : selected 9 ⟨1104192, by decide⟩
    (prefixPartial 12 310134) = some ⟨12, 2, 0, 1104192, 310134, 1697, 65536⟩ := by
  decide +kernel

theorem context_12_310134_1104192 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310134 ⟨1104192, by decide⟩ :=
  accepted_of_selected 12 310134 ⟨1104192, by decide⟩ ⟨12, 2, 0, 1104192, 310134, 1697, 65536⟩
    (by decide) selected_cut_40572

theorem selected_cut_40573 : selected 9 ⟨1104212, by decide⟩
    (prefixPartial 12 310135) = some ⟨12, 2, 0, 1104212, 310135, 1377, 65536⟩ := by
  decide +kernel

theorem context_12_310135_1104212 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310135 ⟨1104212, by decide⟩ :=
  accepted_of_selected 12 310135 ⟨1104212, by decide⟩ ⟨12, 2, 0, 1104212, 310135, 1377, 65536⟩
    (by decide) selected_cut_40573

theorem unmarked_context_11_77533_1104213 : frontier 10 ⟨1104213, by decide⟩
    (prefixCache 11 77533) (prefixPartial 11 77533) = false := by
  decide +kernel

theorem node_context_11_77533_1104213 : EJMOriginalGlobalDAGData.nodes 10 ⟨1104213, by decide⟩ =
    .split (coordinate 11) (![⟨1104165, by decide⟩,⟨1084018, by decide⟩,⟨1104192, by decide⟩,⟨1104212, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77533_1104213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77533 ⟨1104213, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77533
    ⟨1104213, by decide⟩ (by decide) (![⟨1104165, by decide⟩,⟨1084018, by decide⟩,⟨1104192, by decide⟩,⟨1104212, by decide⟩]) unmarked_context_11_77533_1104213 node_context_11_77533_1104213
  intro a
  fin_cases a
  · exact context_12_310132_1104165
  · exact context_12_310133_1084018
  · exact context_12_310134_1104192
  · exact context_12_310135_1104212

theorem selected_cut_40574 : selected 9 ⟨1104238, by decide⟩
    (prefixPartial 12 310136) = some ⟨12, 2, 0, 1104238, 310136, 1377, 65536⟩ := by
  decide +kernel

theorem context_12_310136_1104238 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310136 ⟨1104238, by decide⟩ :=
  accepted_of_selected 12 310136 ⟨1104238, by decide⟩ ⟨12, 2, 0, 1104238, 310136, 1377, 65536⟩
    (by decide) selected_cut_40574

theorem selected_cut_40575 : selected 9 ⟨1104257, by decide⟩
    (prefixPartial 12 310137) = some ⟨12, 2, 0, 1104257, 310137, 1445, 65536⟩ := by
  decide +kernel

theorem context_12_310137_1104257 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310137 ⟨1104257, by decide⟩ :=
  accepted_of_selected 12 310137 ⟨1104257, by decide⟩ ⟨12, 2, 0, 1104257, 310137, 1445, 65536⟩
    (by decide) selected_cut_40575

theorem selected_cut_40576 : selected 9 ⟨1104284, by decide⟩
    (prefixPartial 12 310138) = some ⟨12, 2, 0, 1104284, 310138, 1437, 65536⟩ := by
  decide +kernel

theorem context_12_310138_1104284 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310138 ⟨1104284, by decide⟩ :=
  accepted_of_selected 12 310138 ⟨1104284, by decide⟩ ⟨12, 2, 0, 1104284, 310138, 1437, 65536⟩
    (by decide) selected_cut_40576

theorem selected_cut_40577 : selected 9 ⟨1104298, by decide⟩
    (prefixPartial 12 310139) = some ⟨12, 2, 0, 1104298, 310139, 1201, 65536⟩ := by
  decide +kernel

theorem context_12_310139_1104298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310139 ⟨1104298, by decide⟩ :=
  accepted_of_selected 12 310139 ⟨1104298, by decide⟩ ⟨12, 2, 0, 1104298, 310139, 1201, 65536⟩
    (by decide) selected_cut_40577

theorem unmarked_context_11_77534_1104299 : frontier 10 ⟨1104299, by decide⟩
    (prefixCache 11 77534) (prefixPartial 11 77534) = false := by
  decide +kernel

theorem node_context_11_77534_1104299 : EJMOriginalGlobalDAGData.nodes 10 ⟨1104299, by decide⟩ =
    .split (coordinate 11) (![⟨1104238, by decide⟩,⟨1104257, by decide⟩,⟨1104284, by decide⟩,⟨1104298, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77534_1104299 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77534 ⟨1104299, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77534
    ⟨1104299, by decide⟩ (by decide) (![⟨1104238, by decide⟩,⟨1104257, by decide⟩,⟨1104284, by decide⟩,⟨1104298, by decide⟩]) unmarked_context_11_77534_1104299 node_context_11_77534_1104299
  intro a
  fin_cases a
  · exact context_12_310136_1104238
  · exact context_12_310137_1104257
  · exact context_12_310138_1104284
  · exact context_12_310139_1104298

theorem selected_cut_40578 : selected 9 ⟨1104326, by decide⟩
    (prefixPartial 12 310140) = some ⟨12, 2, 0, 1104326, 310140, 1405, 65536⟩ := by
  decide +kernel

theorem context_12_310140_1104326 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310140 ⟨1104326, by decide⟩ :=
  accepted_of_selected 12 310140 ⟨1104326, by decide⟩ ⟨12, 2, 0, 1104326, 310140, 1405, 65536⟩
    (by decide) selected_cut_40578

theorem selected_cut_40579 : selected 9 ⟨1104354, by decide⟩
    (prefixPartial 12 310141) = some ⟨12, 2, 0, 1104354, 310141, 1517, 65536⟩ := by
  decide +kernel

theorem context_12_310141_1104354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310141 ⟨1104354, by decide⟩ :=
  accepted_of_selected 12 310141 ⟨1104354, by decide⟩ ⟨12, 2, 0, 1104354, 310141, 1517, 65536⟩
    (by decide) selected_cut_40579

theorem selected_cut_40580 : selected 9 ⟨1104383, by decide⟩
    (prefixPartial 12 310142) = some ⟨12, 2, 0, 1104383, 310142, 1465, 65536⟩ := by
  decide +kernel

theorem context_12_310142_1104383 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310142 ⟨1104383, by decide⟩ :=
  accepted_of_selected 12 310142 ⟨1104383, by decide⟩ ⟨12, 2, 0, 1104383, 310142, 1465, 65536⟩
    (by decide) selected_cut_40580

theorem selected_cut_40581 : selected 9 ⟨762109, by decide⟩
    (prefixPartial 12 310143) = some ⟨12, 1, 0, 762109, 310143, 1, 65536⟩ := by
  decide +kernel

theorem context_12_310143_762109 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310143 ⟨762109, by decide⟩ :=
  accepted_of_selected 12 310143 ⟨762109, by decide⟩ ⟨12, 1, 0, 762109, 310143, 1, 65536⟩
    (by decide) selected_cut_40581

theorem unmarked_context_11_77535_1104384 : frontier 10 ⟨1104384, by decide⟩
    (prefixCache 11 77535) (prefixPartial 11 77535) = false := by
  decide +kernel

theorem node_context_11_77535_1104384 : EJMOriginalGlobalDAGData.nodes 10 ⟨1104384, by decide⟩ =
    .split (coordinate 11) (![⟨1104326, by decide⟩,⟨1104354, by decide⟩,⟨1104383, by decide⟩,⟨762109, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77535_1104384 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77535 ⟨1104384, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77535
    ⟨1104384, by decide⟩ (by decide) (![⟨1104326, by decide⟩,⟨1104354, by decide⟩,⟨1104383, by decide⟩,⟨762109, by decide⟩]) unmarked_context_11_77535_1104384 node_context_11_77535_1104384
  intro a
  fin_cases a
  · exact context_12_310140_1104326
  · exact context_12_310141_1104354
  · exact context_12_310142_1104383
  · exact context_12_310143_762109

theorem unmarked_context_10_19383_1104385 : frontier 11 ⟨1104385, by decide⟩
    (prefixCache 10 19383) (prefixPartial 10 19383) = false := by
  decide +kernel

theorem node_context_10_19383_1104385 : EJMOriginalGlobalDAGData.nodes 11 ⟨1104385, by decide⟩ =
    .split (coordinate 10) (![⟨1104142, by decide⟩,⟨1104213, by decide⟩,⟨1104299, by decide⟩,⟨1104384, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19383_1104385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19383 ⟨1104385, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19383
    ⟨1104385, by decide⟩ (by decide) (![⟨1104142, by decide⟩,⟨1104213, by decide⟩,⟨1104299, by decide⟩,⟨1104384, by decide⟩]) unmarked_context_10_19383_1104385 node_context_10_19383_1104385
  intro a
  fin_cases a
  · exact context_11_77532_1104142
  · exact context_11_77533_1104213
  · exact context_11_77534_1104299
  · exact context_11_77535_1104384

theorem unmarked_context_9_4845_1104386 : frontier 12 ⟨1104386, by decide⟩
    (prefixCache 9 4845) (prefixPartial 9 4845) = false := by
  decide +kernel

theorem node_context_9_4845_1104386 : EJMOriginalGlobalDAGData.nodes 12 ⟨1104386, by decide⟩ =
    .split (coordinate 9) (![⟨1103793, by decide⟩,⟨893098, by decide⟩,⟨1104048, by decide⟩,⟨1104385, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4845_1104386 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4845 ⟨1104386, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4845
    ⟨1104386, by decide⟩ (by decide) (![⟨1103793, by decide⟩,⟨893098, by decide⟩,⟨1104048, by decide⟩,⟨1104385, by decide⟩]) unmarked_context_9_4845_1104386 node_context_9_4845_1104386
  intro a
  fin_cases a
  · exact context_10_19380_1103793
  · exact context_10_19381_893098
  · exact context_10_19382_1104048
  · exact context_10_19383_1104385

theorem selected_cut_40582 : selected 10 ⟨1104425, by decide⟩
    (prefixPartial 11 77536) = some ⟨11, 2, 0, 1104425, 77536, 2401, 262144⟩ := by
  decide +kernel

theorem context_11_77536_1104425 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77536 ⟨1104425, by decide⟩ :=
  accepted_of_selected 11 77536 ⟨1104425, by decide⟩ ⟨11, 2, 0, 1104425, 77536, 2401, 262144⟩
    (by decide) selected_cut_40582

theorem selected_cut_40583 : selected 9 ⟨1104455, by decide⟩
    (prefixPartial 12 310148) = some ⟨12, 2, 0, 1104455, 310148, 1541, 65536⟩ := by
  decide +kernel

theorem context_12_310148_1104455 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310148 ⟨1104455, by decide⟩ :=
  accepted_of_selected 12 310148 ⟨1104455, by decide⟩ ⟨12, 2, 0, 1104455, 310148, 1541, 65536⟩
    (by decide) selected_cut_40583

theorem selected_cut_40584 : selected 9 ⟨1104486, by decide⟩
    (prefixPartial 12 310149) = some ⟨12, 2, 0, 1104486, 310149, 1473, 65536⟩ := by
  decide +kernel

theorem context_12_310149_1104486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310149 ⟨1104486, by decide⟩ :=
  accepted_of_selected 12 310149 ⟨1104486, by decide⟩ ⟨12, 2, 0, 1104486, 310149, 1473, 65536⟩
    (by decide) selected_cut_40584

theorem selected_cut_40585 : selected 9 ⟨984676, by decide⟩
    (prefixPartial 12 310150) = some ⟨12, 1, 0, 984676, 310150, 1, 65536⟩ := by
  decide +kernel

theorem context_12_310150_984676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310150 ⟨984676, by decide⟩ :=
  accepted_of_selected 12 310150 ⟨984676, by decide⟩ ⟨12, 1, 0, 984676, 310150, 1, 65536⟩
    (by decide) selected_cut_40585

theorem selected_cut_40586 : selected 9 ⟨1104506, by decide⟩
    (prefixPartial 12 310151) = some ⟨12, 2, 0, 1104506, 310151, 1289, 65536⟩ := by
  decide +kernel

theorem context_12_310151_1104506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 310151 ⟨1104506, by decide⟩ :=
  accepted_of_selected 12 310151 ⟨1104506, by decide⟩ ⟨12, 2, 0, 1104506, 310151, 1289, 65536⟩
    (by decide) selected_cut_40586

theorem unmarked_context_11_77537_1104507 : frontier 10 ⟨1104507, by decide⟩
    (prefixCache 11 77537) (prefixPartial 11 77537) = false := by
  decide +kernel

theorem node_context_11_77537_1104507 : EJMOriginalGlobalDAGData.nodes 10 ⟨1104507, by decide⟩ =
    .split (coordinate 11) (![⟨1104455, by decide⟩,⟨1104486, by decide⟩,⟨984676, by decide⟩,⟨1104506, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77537_1104507 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77537 ⟨1104507, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77537
    ⟨1104507, by decide⟩ (by decide) (![⟨1104455, by decide⟩,⟨1104486, by decide⟩,⟨984676, by decide⟩,⟨1104506, by decide⟩]) unmarked_context_11_77537_1104507 node_context_11_77537_1104507
  intro a
  fin_cases a
  · exact context_12_310148_1104455
  · exact context_12_310149_1104486
  · exact context_12_310150_984676
  · exact context_12_310151_1104506

theorem selected_cut_40587 : selected 10 ⟨1104576, by decide⟩
    (prefixPartial 11 77538) = some ⟨11, 2, 0, 1104576, 77538, 3749, 262144⟩ := by
  decide +kernel

theorem context_11_77538_1104576 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77538 ⟨1104576, by decide⟩ :=
  accepted_of_selected 11 77538 ⟨1104576, by decide⟩ ⟨11, 2, 0, 1104576, 77538, 3749, 262144⟩
    (by decide) selected_cut_40587

theorem selected_cut_40588 : selected 10 ⟨1104624, by decide⟩
    (prefixPartial 11 77539) = some ⟨11, 2, 0, 1104624, 77539, 2589, 262144⟩ := by
  decide +kernel

theorem context_11_77539_1104624 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77539 ⟨1104624, by decide⟩ :=
  accepted_of_selected 11 77539 ⟨1104624, by decide⟩ ⟨11, 2, 0, 1104624, 77539, 2589, 262144⟩
    (by decide) selected_cut_40588

theorem unmarked_context_10_19384_1104625 : frontier 11 ⟨1104625, by decide⟩
    (prefixCache 10 19384) (prefixPartial 10 19384) = false := by
  decide +kernel

theorem node_context_10_19384_1104625 : EJMOriginalGlobalDAGData.nodes 11 ⟨1104625, by decide⟩ =
    .split (coordinate 10) (![⟨1104425, by decide⟩,⟨1104507, by decide⟩,⟨1104576, by decide⟩,⟨1104624, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19384_1104625 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19384 ⟨1104625, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19384
    ⟨1104625, by decide⟩ (by decide) (![⟨1104425, by decide⟩,⟨1104507, by decide⟩,⟨1104576, by decide⟩,⟨1104624, by decide⟩]) unmarked_context_10_19384_1104625 node_context_10_19384_1104625
  intro a
  fin_cases a
  · exact context_11_77536_1104425
  · exact context_11_77537_1104507
  · exact context_11_77538_1104576
  · exact context_11_77539_1104624

theorem selected_cut_40589 : selected 10 ⟨1104664, by decide⟩
    (prefixPartial 11 77540) = some ⟨11, 2, 0, 1104664, 77540, 2873, 262144⟩ := by
  decide +kernel

theorem context_11_77540_1104664 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77540 ⟨1104664, by decide⟩ :=
  accepted_of_selected 11 77540 ⟨1104664, by decide⟩ ⟨11, 2, 0, 1104664, 77540, 2873, 262144⟩
    (by decide) selected_cut_40589

theorem selected_cut_40590 : selected 10 ⟨1104702, by decide⟩
    (prefixPartial 11 77541) = some ⟨11, 2, 0, 1104702, 77541, 2089, 262144⟩ := by
  decide +kernel

theorem context_11_77541_1104702 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77541 ⟨1104702, by decide⟩ :=
  accepted_of_selected 11 77541 ⟨1104702, by decide⟩ ⟨11, 2, 0, 1104702, 77541, 2089, 262144⟩
    (by decide) selected_cut_40590

theorem selected_cut_40591 : selected 10 ⟨1104743, by decide⟩
    (prefixPartial 11 77542) = some ⟨11, 2, 0, 1104743, 77542, 2721, 262144⟩ := by
  decide +kernel

theorem context_11_77542_1104743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77542 ⟨1104743, by decide⟩ :=
  accepted_of_selected 11 77542 ⟨1104743, by decide⟩ ⟨11, 2, 0, 1104743, 77542, 2721, 262144⟩
    (by decide) selected_cut_40591

theorem selected_cut_40592 : selected 10 ⟨1104770, by decide⟩
    (prefixPartial 11 77543) = some ⟨11, 2, 0, 1104770, 77543, 1845, 262144⟩ := by
  decide +kernel

theorem context_11_77543_1104770 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77543 ⟨1104770, by decide⟩ :=
  accepted_of_selected 11 77543 ⟨1104770, by decide⟩ ⟨11, 2, 0, 1104770, 77543, 1845, 262144⟩
    (by decide) selected_cut_40592

theorem unmarked_context_10_19385_1104771 : frontier 11 ⟨1104771, by decide⟩
    (prefixCache 10 19385) (prefixPartial 10 19385) = false := by
  decide +kernel

theorem node_context_10_19385_1104771 : EJMOriginalGlobalDAGData.nodes 11 ⟨1104771, by decide⟩ =
    .split (coordinate 10) (![⟨1104664, by decide⟩,⟨1104702, by decide⟩,⟨1104743, by decide⟩,⟨1104770, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19385_1104771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19385 ⟨1104771, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19385
    ⟨1104771, by decide⟩ (by decide) (![⟨1104664, by decide⟩,⟨1104702, by decide⟩,⟨1104743, by decide⟩,⟨1104770, by decide⟩]) unmarked_context_10_19385_1104771 node_context_10_19385_1104771
  intro a
  fin_cases a
  · exact context_11_77540_1104664
  · exact context_11_77541_1104702
  · exact context_11_77542_1104743
  · exact context_11_77543_1104770

theorem selected_cut_40593 : selected 10 ⟨1104797, by decide⟩
    (prefixPartial 11 77544) = some ⟨11, 2, 0, 1104797, 77544, 2217, 262144⟩ := by
  decide +kernel

theorem context_11_77544_1104797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77544 ⟨1104797, by decide⟩ :=
  accepted_of_selected 11 77544 ⟨1104797, by decide⟩ ⟨11, 2, 0, 1104797, 77544, 2217, 262144⟩
    (by decide) selected_cut_40593

theorem selected_cut_40594 : selected 10 ⟨1104835, by decide⟩
    (prefixPartial 11 77545) = some ⟨11, 2, 0, 1104835, 77545, 2629, 262144⟩ := by
  decide +kernel

theorem context_11_77545_1104835 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77545 ⟨1104835, by decide⟩ :=
  accepted_of_selected 11 77545 ⟨1104835, by decide⟩ ⟨11, 2, 0, 1104835, 77545, 2629, 262144⟩
    (by decide) selected_cut_40594

theorem selected_cut_40595 : selected 10 ⟨906566, by decide⟩
    (prefixPartial 11 77546) = some ⟨11, 1, 0, 906566, 77546, 1, 262144⟩ := by
  decide +kernel

theorem context_11_77546_906566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77546 ⟨906566, by decide⟩ :=
  accepted_of_selected 11 77546 ⟨906566, by decide⟩ ⟨11, 1, 0, 906566, 77546, 1, 262144⟩
    (by decide) selected_cut_40595

theorem selected_cut_40596 : selected 10 ⟨1104852, by decide⟩
    (prefixPartial 11 77547) = some ⟨11, 2, 0, 1104852, 77547, 1521, 262144⟩ := by
  decide +kernel

theorem context_11_77547_1104852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77547 ⟨1104852, by decide⟩ :=
  accepted_of_selected 11 77547 ⟨1104852, by decide⟩ ⟨11, 2, 0, 1104852, 77547, 1521, 262144⟩
    (by decide) selected_cut_40596

theorem unmarked_context_10_19386_1104853 : frontier 11 ⟨1104853, by decide⟩
    (prefixCache 10 19386) (prefixPartial 10 19386) = false := by
  decide +kernel

theorem node_context_10_19386_1104853 : EJMOriginalGlobalDAGData.nodes 11 ⟨1104853, by decide⟩ =
    .split (coordinate 10) (![⟨1104797, by decide⟩,⟨1104835, by decide⟩,⟨906566, by decide⟩,⟨1104852, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19386_1104853 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19386 ⟨1104853, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19386
    ⟨1104853, by decide⟩ (by decide) (![⟨1104797, by decide⟩,⟨1104835, by decide⟩,⟨906566, by decide⟩,⟨1104852, by decide⟩]) unmarked_context_10_19386_1104853 node_context_10_19386_1104853
  intro a
  fin_cases a
  · exact context_11_77544_1104797
  · exact context_11_77545_1104835
  · exact context_11_77546_906566
  · exact context_11_77547_1104852

theorem selected_cut_40597 : selected 10 ⟨1104882, by decide⟩
    (prefixPartial 11 77548) = some ⟨11, 2, 0, 1104882, 77548, 2085, 262144⟩ := by
  decide +kernel

theorem context_11_77548_1104882 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77548 ⟨1104882, by decide⟩ :=
  accepted_of_selected 11 77548 ⟨1104882, by decide⟩ ⟨11, 2, 0, 1104882, 77548, 2085, 262144⟩
    (by decide) selected_cut_40597

theorem selected_cut_40598 : selected 10 ⟨1104910, by decide⟩
    (prefixPartial 11 77549) = some ⟨11, 2, 0, 1104910, 77549, 2265, 262144⟩ := by
  decide +kernel

theorem context_11_77549_1104910 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77549 ⟨1104910, by decide⟩ :=
  accepted_of_selected 11 77549 ⟨1104910, by decide⟩ ⟨11, 2, 0, 1104910, 77549, 2265, 262144⟩
    (by decide) selected_cut_40598

theorem selected_cut_40599 : selected 10 ⟨1104939, by decide⟩
    (prefixPartial 11 77550) = some ⟨11, 2, 0, 1104939, 77550, 1885, 262144⟩ := by
  decide +kernel

theorem context_11_77550_1104939 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77550 ⟨1104939, by decide⟩ :=
  accepted_of_selected 11 77550 ⟨1104939, by decide⟩ ⟨11, 2, 0, 1104939, 77550, 1885, 262144⟩
    (by decide) selected_cut_40599

theorem selected_cut_40600 : selected 10 ⟨1104963, by decide⟩
    (prefixPartial 11 77551) = some ⟨11, 2, 0, 1104963, 77551, 1337, 262144⟩ := by
  decide +kernel

theorem context_11_77551_1104963 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77551 ⟨1104963, by decide⟩ :=
  accepted_of_selected 11 77551 ⟨1104963, by decide⟩ ⟨11, 2, 0, 1104963, 77551, 1337, 262144⟩
    (by decide) selected_cut_40600

theorem unmarked_context_10_19387_1104964 : frontier 11 ⟨1104964, by decide⟩
    (prefixCache 10 19387) (prefixPartial 10 19387) = false := by
  decide +kernel

theorem node_context_10_19387_1104964 : EJMOriginalGlobalDAGData.nodes 11 ⟨1104964, by decide⟩ =
    .split (coordinate 10) (![⟨1104882, by decide⟩,⟨1104910, by decide⟩,⟨1104939, by decide⟩,⟨1104963, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19387_1104964 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19387 ⟨1104964, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19387
    ⟨1104964, by decide⟩ (by decide) (![⟨1104882, by decide⟩,⟨1104910, by decide⟩,⟨1104939, by decide⟩,⟨1104963, by decide⟩]) unmarked_context_10_19387_1104964 node_context_10_19387_1104964
  intro a
  fin_cases a
  · exact context_11_77548_1104882
  · exact context_11_77549_1104910
  · exact context_11_77550_1104939
  · exact context_11_77551_1104963

theorem unmarked_context_9_4846_1104965 : frontier 12 ⟨1104965, by decide⟩
    (prefixCache 9 4846) (prefixPartial 9 4846) = false := by
  decide +kernel

theorem node_context_9_4846_1104965 : EJMOriginalGlobalDAGData.nodes 12 ⟨1104965, by decide⟩ =
    .split (coordinate 9) (![⟨1104625, by decide⟩,⟨1104771, by decide⟩,⟨1104853, by decide⟩,⟨1104964, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4846_1104965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4846 ⟨1104965, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4846
    ⟨1104965, by decide⟩ (by decide) (![⟨1104625, by decide⟩,⟨1104771, by decide⟩,⟨1104853, by decide⟩,⟨1104964, by decide⟩]) unmarked_context_9_4846_1104965 node_context_9_4846_1104965
  intro a
  fin_cases a
  · exact context_10_19384_1104625
  · exact context_10_19385_1104771
  · exact context_10_19386_1104853
  · exact context_10_19387_1104964

theorem selected_cut_40601 : selected 10 ⟨1104989, by decide⟩
    (prefixPartial 11 77552) = some ⟨11, 2, 0, 1104989, 77552, 1357, 262144⟩ := by
  decide +kernel

theorem context_11_77552_1104989 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77552 ⟨1104989, by decide⟩ :=
  accepted_of_selected 11 77552 ⟨1104989, by decide⟩ ⟨11, 2, 0, 1104989, 77552, 1357, 262144⟩
    (by decide) selected_cut_40601

theorem selected_cut_40602 : selected 10 ⟨1105015, by decide⟩
    (prefixPartial 11 77553) = some ⟨11, 2, 0, 1105015, 77553, 1897, 262144⟩ := by
  decide +kernel

theorem context_11_77553_1105015 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77553 ⟨1105015, by decide⟩ :=
  accepted_of_selected 11 77553 ⟨1105015, by decide⟩ ⟨11, 2, 0, 1105015, 77553, 1897, 262144⟩
    (by decide) selected_cut_40602

theorem selected_cut_40603 : selected 10 ⟨1105045, by decide⟩
    (prefixPartial 11 77554) = some ⟨11, 2, 0, 1105045, 77554, 1801, 262144⟩ := by
  decide +kernel

theorem context_11_77554_1105045 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77554 ⟨1105045, by decide⟩ :=
  accepted_of_selected 11 77554 ⟨1105045, by decide⟩ ⟨11, 2, 0, 1105045, 77554, 1801, 262144⟩
    (by decide) selected_cut_40603

theorem selected_cut_40604 : selected 10 ⟨1105069, by decide⟩
    (prefixPartial 11 77555) = some ⟨11, 2, 0, 1105069, 77555, 1345, 262144⟩ := by
  decide +kernel

theorem context_11_77555_1105069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77555 ⟨1105069, by decide⟩ :=
  accepted_of_selected 11 77555 ⟨1105069, by decide⟩ ⟨11, 2, 0, 1105069, 77555, 1345, 262144⟩
    (by decide) selected_cut_40604

theorem unmarked_context_10_19388_1105070 : frontier 11 ⟨1105070, by decide⟩
    (prefixCache 10 19388) (prefixPartial 10 19388) = false := by
  decide +kernel

theorem node_context_10_19388_1105070 : EJMOriginalGlobalDAGData.nodes 11 ⟨1105070, by decide⟩ =
    .split (coordinate 10) (![⟨1104989, by decide⟩,⟨1105015, by decide⟩,⟨1105045, by decide⟩,⟨1105069, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19388_1105070 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19388 ⟨1105070, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19388
    ⟨1105070, by decide⟩ (by decide) (![⟨1104989, by decide⟩,⟨1105015, by decide⟩,⟨1105045, by decide⟩,⟨1105069, by decide⟩]) unmarked_context_10_19388_1105070 node_context_10_19388_1105070
  intro a
  fin_cases a
  · exact context_11_77552_1104989
  · exact context_11_77553_1105015
  · exact context_11_77554_1105045
  · exact context_11_77555_1105069

theorem selected_cut_40605 : selected 10 ⟨1105084, by decide⟩
    (prefixPartial 11 77556) = some ⟨11, 2, 0, 1105084, 77556, 1261, 262144⟩ := by
  decide +kernel

theorem context_11_77556_1105084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77556 ⟨1105084, by decide⟩ :=
  accepted_of_selected 11 77556 ⟨1105084, by decide⟩ ⟨11, 2, 0, 1105084, 77556, 1261, 262144⟩
    (by decide) selected_cut_40605

theorem selected_cut_40606 : selected 10 ⟨1105098, by decide⟩
    (prefixPartial 11 77557) = some ⟨11, 2, 0, 1105098, 77557, 1013, 262144⟩ := by
  decide +kernel

theorem context_11_77557_1105098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77557 ⟨1105098, by decide⟩ :=
  accepted_of_selected 11 77557 ⟨1105098, by decide⟩ ⟨11, 2, 0, 1105098, 77557, 1013, 262144⟩
    (by decide) selected_cut_40606

theorem selected_cut_40607 : selected 10 ⟨1105110, by decide⟩
    (prefixPartial 11 77558) = some ⟨11, 2, 0, 1105110, 77558, 1105, 262144⟩ := by
  decide +kernel

theorem context_11_77558_1105110 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77558 ⟨1105110, by decide⟩ :=
  accepted_of_selected 11 77558 ⟨1105110, by decide⟩ ⟨11, 2, 0, 1105110, 77558, 1105, 262144⟩
    (by decide) selected_cut_40607

theorem selected_cut_40608 : selected 10 ⟨1105124, by decide⟩
    (prefixPartial 11 77559) = some ⟨11, 2, 0, 1105124, 77559, 785, 262144⟩ := by
  decide +kernel

theorem context_11_77559_1105124 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77559 ⟨1105124, by decide⟩ :=
  accepted_of_selected 11 77559 ⟨1105124, by decide⟩ ⟨11, 2, 0, 1105124, 77559, 785, 262144⟩
    (by decide) selected_cut_40608

theorem unmarked_context_10_19389_1105125 : frontier 11 ⟨1105125, by decide⟩
    (prefixCache 10 19389) (prefixPartial 10 19389) = false := by
  decide +kernel

theorem node_context_10_19389_1105125 : EJMOriginalGlobalDAGData.nodes 11 ⟨1105125, by decide⟩ =
    .split (coordinate 10) (![⟨1105084, by decide⟩,⟨1105098, by decide⟩,⟨1105110, by decide⟩,⟨1105124, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19389_1105125 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19389 ⟨1105125, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19389
    ⟨1105125, by decide⟩ (by decide) (![⟨1105084, by decide⟩,⟨1105098, by decide⟩,⟨1105110, by decide⟩,⟨1105124, by decide⟩]) unmarked_context_10_19389_1105125 node_context_10_19389_1105125
  intro a
  fin_cases a
  · exact context_11_77556_1105084
  · exact context_11_77557_1105098
  · exact context_11_77558_1105110
  · exact context_11_77559_1105124

theorem selected_cut_40609 : selected 11 ⟨1105170, by decide⟩
    (prefixPartial 10 19390) = some ⟨10, 2, 0, 1105170, 19390, 2057, 1048576⟩ := by
  decide +kernel

theorem context_10_19390_1105170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19390 ⟨1105170, by decide⟩ :=
  accepted_of_selected 10 19390 ⟨1105170, by decide⟩ ⟨10, 2, 0, 1105170, 19390, 2057, 1048576⟩
    (by decide) selected_cut_40609

theorem selected_cut_40610 : selected 11 ⟨1105205, by decide⟩
    (prefixPartial 10 19391) = some ⟨10, 2, 0, 1105205, 19391, 617, 1048576⟩ := by
  decide +kernel

theorem context_10_19391_1105205 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19391 ⟨1105205, by decide⟩ :=
  accepted_of_selected 10 19391 ⟨1105205, by decide⟩ ⟨10, 2, 0, 1105205, 19391, 617, 1048576⟩
    (by decide) selected_cut_40610

theorem unmarked_context_9_4847_1105206 : frontier 12 ⟨1105206, by decide⟩
    (prefixCache 9 4847) (prefixPartial 9 4847) = false := by
  decide +kernel

theorem node_context_9_4847_1105206 : EJMOriginalGlobalDAGData.nodes 12 ⟨1105206, by decide⟩ =
    .split (coordinate 9) (![⟨1105070, by decide⟩,⟨1105125, by decide⟩,⟨1105170, by decide⟩,⟨1105205, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4847_1105206 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4847 ⟨1105206, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4847
    ⟨1105206, by decide⟩ (by decide) (![⟨1105070, by decide⟩,⟨1105125, by decide⟩,⟨1105170, by decide⟩,⟨1105205, by decide⟩]) unmarked_context_9_4847_1105206 node_context_9_4847_1105206
  intro a
  fin_cases a
  · exact context_10_19388_1105070
  · exact context_10_19389_1105125
  · exact context_10_19390_1105170
  · exact context_10_19391_1105205

theorem unmarked_context_8_1211_1105207 : frontier 13 ⟨1105207, by decide⟩
    (prefixCache 8 1211) (prefixPartial 8 1211) = false := by
  decide +kernel

theorem node_context_8_1211_1105207 : EJMOriginalGlobalDAGData.nodes 13 ⟨1105207, by decide⟩ =
    .split (coordinate 8) (![⟨1103121, by decide⟩,⟨1104386, by decide⟩,⟨1104965, by decide⟩,⟨1105206, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1211_1105207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1211 ⟨1105207, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1211
    ⟨1105207, by decide⟩ (by decide) (![⟨1103121, by decide⟩,⟨1104386, by decide⟩,⟨1104965, by decide⟩,⟨1105206, by decide⟩]) unmarked_context_8_1211_1105207 node_context_8_1211_1105207
  intro a
  fin_cases a
  · exact context_9_4844_1103121
  · exact context_9_4845_1104386
  · exact context_9_4846_1104965
  · exact context_9_4847_1105206

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
