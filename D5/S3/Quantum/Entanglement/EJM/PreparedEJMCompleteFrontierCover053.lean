/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover052
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_05091 : selected 10 ⟨158323, by decide⟩
    (prefixPartial 11 4731) = some ⟨11, 2, 0, 158323, 4731, 961, 262144⟩ := by
  decide +kernel

theorem context_11_4731_158323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4731 ⟨158323, by decide⟩ :=
  accepted_of_selected 11 4731 ⟨158323, by decide⟩ ⟨11, 2, 0, 158323, 4731, 961, 262144⟩
    (by decide) selected_cut_05091

theorem unmarked_context_10_1182_158324 : frontier 11 ⟨158324, by decide⟩
    (prefixCache 10 1182) (prefixPartial 10 1182) = false := by
  decide +kernel

theorem node_context_10_1182_158324 : EJMOriginalGlobalDAGData.nodes 11 ⟨158324, by decide⟩ =
    .split (coordinate 10) (![⟨158267, by decide⟩,⟨158287, by decide⟩,⟨158307, by decide⟩,⟨158323, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1182_158324 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1182 ⟨158324, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1182
    ⟨158324, by decide⟩ (by decide) (![⟨158267, by decide⟩,⟨158287, by decide⟩,⟨158307, by decide⟩,⟨158323, by decide⟩]) unmarked_context_10_1182_158324 node_context_10_1182_158324
  intro a
  fin_cases a
  · exact context_11_4728_158267
  · exact context_11_4729_158287
  · exact context_11_4730_158307
  · exact context_11_4731_158323

theorem selected_cut_05092 : selected 11 ⟨158376, by decide⟩
    (prefixPartial 10 1183) = some ⟨10, 2, 0, 158376, 1183, 1961, 1048576⟩ := by
  decide +kernel

theorem context_10_1183_158376 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1183 ⟨158376, by decide⟩ :=
  accepted_of_selected 10 1183 ⟨158376, by decide⟩ ⟨10, 2, 0, 158376, 1183, 1961, 1048576⟩
    (by decide) selected_cut_05092

theorem unmarked_context_9_295_158377 : frontier 12 ⟨158377, by decide⟩
    (prefixCache 9 295) (prefixPartial 9 295) = false := by
  decide +kernel

theorem node_context_9_295_158377 : EJMOriginalGlobalDAGData.nodes 12 ⟨158377, by decide⟩ =
    .split (coordinate 9) (![⟨158156, by decide⟩,⟨158249, by decide⟩,⟨158324, by decide⟩,⟨158376, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_295_158377 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 295 ⟨158377, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 295
    ⟨158377, by decide⟩ (by decide) (![⟨158156, by decide⟩,⟨158249, by decide⟩,⟨158324, by decide⟩,⟨158376, by decide⟩]) unmarked_context_9_295_158377 node_context_9_295_158377
  intro a
  fin_cases a
  · exact context_10_1180_158156
  · exact context_10_1181_158249
  · exact context_10_1182_158324
  · exact context_10_1183_158376

theorem unmarked_context_8_73_158378 : frontier 13 ⟨158378, by decide⟩
    (prefixCache 8 73) (prefixPartial 8 73) = false := by
  decide +kernel

theorem node_context_8_73_158378 : EJMOriginalGlobalDAGData.nodes 13 ⟨158378, by decide⟩ =
    .split (coordinate 8) (![⟨153377, by decide⟩,⟨156655, by decide⟩,⟨158014, by decide⟩,⟨158377, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_73_158378 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 73 ⟨158378, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 73
    ⟨158378, by decide⟩ (by decide) (![⟨153377, by decide⟩,⟨156655, by decide⟩,⟨158014, by decide⟩,⟨158377, by decide⟩]) unmarked_context_8_73_158378 node_context_8_73_158378
  intro a
  fin_cases a
  · exact context_9_292_153377
  · exact context_9_293_156655
  · exact context_9_294_158014
  · exact context_9_295_158377

theorem selected_cut_05093 : selected 13 ⟨158379, by decide⟩
    (prefixPartial 8 74) = some ⟨8, 1, 0, 158379, 74, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_74_158379 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 74 ⟨158379, by decide⟩ :=
  accepted_of_selected 8 74 ⟨158379, by decide⟩ ⟨8, 1, 0, 158379, 74, 1, 16777216⟩
    (by decide) selected_cut_05093

theorem selected_cut_05094 : selected 8 ⟨158447, by decide⟩
    (prefixPartial 13 76800) = some ⟨13, 2, 0, 158447, 76800, 3321, 16384⟩ := by
  decide +kernel

theorem context_13_76800_158447 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76800 ⟨158447, by decide⟩ :=
  accepted_of_selected 13 76800 ⟨158447, by decide⟩ ⟨13, 2, 0, 158447, 76800, 3321, 16384⟩
    (by decide) selected_cut_05094

theorem selected_cut_05095 : selected 8 ⟨158519, by decide⟩
    (prefixPartial 13 76801) = some ⟨13, 2, 0, 158519, 76801, 2053, 16384⟩ := by
  decide +kernel

theorem context_13_76801_158519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76801 ⟨158519, by decide⟩ :=
  accepted_of_selected 13 76801 ⟨158519, by decide⟩ ⟨13, 2, 0, 158519, 76801, 2053, 16384⟩
    (by decide) selected_cut_05095

theorem selected_cut_05096 : selected 8 ⟨158547, by decide⟩
    (prefixPartial 13 76802) = some ⟨13, 2, 0, 158547, 76802, 517, 16384⟩ := by
  decide +kernel

theorem context_13_76802_158547 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76802 ⟨158547, by decide⟩ :=
  accepted_of_selected 13 76802 ⟨158547, by decide⟩ ⟨13, 2, 0, 158547, 76802, 517, 16384⟩
    (by decide) selected_cut_05096

theorem selected_cut_05097 : selected 8 ⟨158551, by decide⟩
    (prefixPartial 13 76803) = some ⟨13, 2, 0, 158551, 76803, 109, 16384⟩ := by
  decide +kernel

theorem context_13_76803_158551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76803 ⟨158551, by decide⟩ :=
  accepted_of_selected 13 76803 ⟨158551, by decide⟩ ⟨13, 2, 0, 158551, 76803, 109, 16384⟩
    (by decide) selected_cut_05097

theorem unmarked_context_12_19200_158552 : frontier 9 ⟨158552, by decide⟩
    (prefixCache 12 19200) (prefixPartial 12 19200) = false := by
  decide +kernel

theorem node_context_12_19200_158552 : EJMOriginalGlobalDAGData.nodes 9 ⟨158552, by decide⟩ =
    .split (coordinate 12) (![⟨158447, by decide⟩,⟨158519, by decide⟩,⟨158547, by decide⟩,⟨158551, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_19200_158552 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19200 ⟨158552, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 19200
    ⟨158552, by decide⟩ (by decide) (![⟨158447, by decide⟩,⟨158519, by decide⟩,⟨158547, by decide⟩,⟨158551, by decide⟩]) unmarked_context_12_19200_158552 node_context_12_19200_158552
  intro a
  fin_cases a
  · exact context_13_76800_158447
  · exact context_13_76801_158519
  · exact context_13_76802_158547
  · exact context_13_76803_158551

theorem selected_cut_05098 : selected 7 ⟨158574, by decide⟩
    (prefixPartial 14 307216) = some ⟨14, 2, 0, 158574, 307216, 1201, 4096⟩ := by
  decide +kernel

theorem context_14_307216_158574 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 307216 ⟨158574, by decide⟩ :=
  accepted_of_selected 14 307216 ⟨158574, by decide⟩ ⟨14, 2, 0, 158574, 307216, 1201, 4096⟩
    (by decide) selected_cut_05098

theorem selected_cut_05099 : selected 7 ⟨158592, by decide⟩
    (prefixPartial 14 307217) = some ⟨14, 2, 0, 158592, 307217, 1081, 4096⟩ := by
  decide +kernel

theorem context_14_307217_158592 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 307217 ⟨158592, by decide⟩ :=
  accepted_of_selected 14 307217 ⟨158592, by decide⟩ ⟨14, 2, 0, 158592, 307217, 1081, 4096⟩
    (by decide) selected_cut_05099

theorem selected_cut_05100 : selected 7 ⟨158606, by decide⟩
    (prefixPartial 14 307218) = some ⟨14, 2, 0, 158606, 307218, 1133, 4096⟩ := by
  decide +kernel

theorem context_14_307218_158606 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 307218 ⟨158606, by decide⟩ :=
  accepted_of_selected 14 307218 ⟨158606, by decide⟩ ⟨14, 2, 0, 158606, 307218, 1133, 4096⟩
    (by decide) selected_cut_05100

theorem selected_cut_05101 : selected 7 ⟨158618, by decide⟩
    (prefixPartial 14 307219) = some ⟨14, 2, 0, 158618, 307219, 953, 4096⟩ := by
  decide +kernel

theorem context_14_307219_158618 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 307219 ⟨158618, by decide⟩ :=
  accepted_of_selected 14 307219 ⟨158618, by decide⟩ ⟨14, 2, 0, 158618, 307219, 953, 4096⟩
    (by decide) selected_cut_05101

theorem unmarked_context_13_76804_158619 : frontier 8 ⟨158619, by decide⟩
    (prefixCache 13 76804) (prefixPartial 13 76804) = false := by
  decide +kernel

theorem node_context_13_76804_158619 : EJMOriginalGlobalDAGData.nodes 8 ⟨158619, by decide⟩ =
    .split (coordinate 13) (![⟨158574, by decide⟩,⟨158592, by decide⟩,⟨158606, by decide⟩,⟨158618, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_76804_158619 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76804 ⟨158619, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 76804
    ⟨158619, by decide⟩ (by decide) (![⟨158574, by decide⟩,⟨158592, by decide⟩,⟨158606, by decide⟩,⟨158618, by decide⟩]) unmarked_context_13_76804_158619 node_context_13_76804_158619
  intro a
  fin_cases a
  · exact context_14_307216_158574
  · exact context_14_307217_158592
  · exact context_14_307218_158606
  · exact context_14_307219_158618

theorem selected_cut_05102 : selected 8 ⟨158673, by decide⟩
    (prefixPartial 13 76805) = some ⟨13, 2, 0, 158673, 76805, 3409, 16384⟩ := by
  decide +kernel

theorem context_13_76805_158673 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76805 ⟨158673, by decide⟩ :=
  accepted_of_selected 13 76805 ⟨158673, by decide⟩ ⟨13, 2, 0, 158673, 76805, 3409, 16384⟩
    (by decide) selected_cut_05102

theorem selected_cut_05103 : selected 8 ⟨158698, by decide⟩
    (prefixPartial 13 76806) = some ⟨13, 2, 0, 158698, 76806, 2045, 16384⟩ := by
  decide +kernel

theorem context_13_76806_158698 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76806 ⟨158698, by decide⟩ :=
  accepted_of_selected 13 76806 ⟨158698, by decide⟩ ⟨13, 2, 0, 158698, 76806, 2045, 16384⟩
    (by decide) selected_cut_05103

theorem selected_cut_05104 : selected 8 ⟨158706, by decide⟩
    (prefixPartial 13 76807) = some ⟨13, 2, 0, 158706, 76807, 721, 16384⟩ := by
  decide +kernel

theorem context_13_76807_158706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76807 ⟨158706, by decide⟩ :=
  accepted_of_selected 13 76807 ⟨158706, by decide⟩ ⟨13, 2, 0, 158706, 76807, 721, 16384⟩
    (by decide) selected_cut_05104

theorem unmarked_context_12_19201_158707 : frontier 9 ⟨158707, by decide⟩
    (prefixCache 12 19201) (prefixPartial 12 19201) = false := by
  decide +kernel

theorem node_context_12_19201_158707 : EJMOriginalGlobalDAGData.nodes 9 ⟨158707, by decide⟩ =
    .split (coordinate 12) (![⟨158619, by decide⟩,⟨158673, by decide⟩,⟨158698, by decide⟩,⟨158706, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_19201_158707 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19201 ⟨158707, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 19201
    ⟨158707, by decide⟩ (by decide) (![⟨158619, by decide⟩,⟨158673, by decide⟩,⟨158698, by decide⟩,⟨158706, by decide⟩]) unmarked_context_12_19201_158707 node_context_12_19201_158707
  intro a
  fin_cases a
  · exact context_13_76804_158619
  · exact context_13_76805_158673
  · exact context_13_76806_158698
  · exact context_13_76807_158706

theorem selected_cut_05105 : selected 7 ⟨158726, by decide⟩
    (prefixPartial 14 307232) = some ⟨14, 2, 0, 158726, 307232, 1117, 4096⟩ := by
  decide +kernel

theorem context_14_307232_158726 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 307232 ⟨158726, by decide⟩ :=
  accepted_of_selected 14 307232 ⟨158726, by decide⟩ ⟨14, 2, 0, 158726, 307232, 1117, 4096⟩
    (by decide) selected_cut_05105

theorem selected_cut_05106 : selected 7 ⟨158744, by decide⟩
    (prefixPartial 14 307233) = some ⟨14, 2, 0, 158744, 307233, 1117, 4096⟩ := by
  decide +kernel

theorem context_14_307233_158744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 307233 ⟨158744, by decide⟩ :=
  accepted_of_selected 14 307233 ⟨158744, by decide⟩ ⟨14, 2, 0, 158744, 307233, 1117, 4096⟩
    (by decide) selected_cut_05106

theorem selected_cut_05107 : selected 7 ⟨158758, by decide⟩
    (prefixPartial 14 307234) = some ⟨14, 2, 0, 158758, 307234, 1145, 4096⟩ := by
  decide +kernel

theorem context_14_307234_158758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 307234 ⟨158758, by decide⟩ :=
  accepted_of_selected 14 307234 ⟨158758, by decide⟩ ⟨14, 2, 0, 158758, 307234, 1145, 4096⟩
    (by decide) selected_cut_05107

theorem selected_cut_05108 : selected 7 ⟨158772, by decide⟩
    (prefixPartial 14 307235) = some ⟨14, 2, 0, 158772, 307235, 961, 4096⟩ := by
  decide +kernel

theorem context_14_307235_158772 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 307235 ⟨158772, by decide⟩ :=
  accepted_of_selected 14 307235 ⟨158772, by decide⟩ ⟨14, 2, 0, 158772, 307235, 961, 4096⟩
    (by decide) selected_cut_05108

theorem unmarked_context_13_76808_158773 : frontier 8 ⟨158773, by decide⟩
    (prefixCache 13 76808) (prefixPartial 13 76808) = false := by
  decide +kernel

theorem node_context_13_76808_158773 : EJMOriginalGlobalDAGData.nodes 8 ⟨158773, by decide⟩ =
    .split (coordinate 13) (![⟨158726, by decide⟩,⟨158744, by decide⟩,⟨158758, by decide⟩,⟨158772, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_76808_158773 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76808 ⟨158773, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 76808
    ⟨158773, by decide⟩ (by decide) (![⟨158726, by decide⟩,⟨158744, by decide⟩,⟨158758, by decide⟩,⟨158772, by decide⟩]) unmarked_context_13_76808_158773 node_context_13_76808_158773
  intro a
  fin_cases a
  · exact context_14_307232_158726
  · exact context_14_307233_158744
  · exact context_14_307234_158758
  · exact context_14_307235_158772

theorem selected_cut_05109 : selected 8 ⟨158851, by decide⟩
    (prefixPartial 13 76809) = some ⟨13, 2, 0, 158851, 76809, 3857, 16384⟩ := by
  decide +kernel

theorem context_13_76809_158851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76809 ⟨158851, by decide⟩ :=
  accepted_of_selected 13 76809 ⟨158851, by decide⟩ ⟨13, 2, 0, 158851, 76809, 3857, 16384⟩
    (by decide) selected_cut_05109

theorem selected_cut_05110 : selected 8 ⟨158881, by decide⟩
    (prefixPartial 13 76810) = some ⟨13, 2, 0, 158881, 76810, 2029, 16384⟩ := by
  decide +kernel

theorem context_13_76810_158881 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76810 ⟨158881, by decide⟩ :=
  accepted_of_selected 13 76810 ⟨158881, by decide⟩ ⟨13, 2, 0, 158881, 76810, 2029, 16384⟩
    (by decide) selected_cut_05110

theorem selected_cut_05111 : selected 8 ⟨158892, by decide⟩
    (prefixPartial 13 76811) = some ⟨13, 2, 0, 158892, 76811, 737, 16384⟩ := by
  decide +kernel

theorem context_13_76811_158892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76811 ⟨158892, by decide⟩ :=
  accepted_of_selected 13 76811 ⟨158892, by decide⟩ ⟨13, 2, 0, 158892, 76811, 737, 16384⟩
    (by decide) selected_cut_05111

theorem unmarked_context_12_19202_158893 : frontier 9 ⟨158893, by decide⟩
    (prefixCache 12 19202) (prefixPartial 12 19202) = false := by
  decide +kernel

theorem node_context_12_19202_158893 : EJMOriginalGlobalDAGData.nodes 9 ⟨158893, by decide⟩ =
    .split (coordinate 12) (![⟨158773, by decide⟩,⟨158851, by decide⟩,⟨158881, by decide⟩,⟨158892, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_19202_158893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19202 ⟨158893, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 19202
    ⟨158893, by decide⟩ (by decide) (![⟨158773, by decide⟩,⟨158851, by decide⟩,⟨158881, by decide⟩,⟨158892, by decide⟩]) unmarked_context_12_19202_158893 node_context_12_19202_158893
  intro a
  fin_cases a
  · exact context_13_76808_158773
  · exact context_13_76809_158851
  · exact context_13_76810_158881
  · exact context_13_76811_158892

theorem selected_cut_05112 : selected 8 ⟨158943, by decide⟩
    (prefixPartial 13 76812) = some ⟨13, 2, 0, 158943, 76812, 3601, 16384⟩ := by
  decide +kernel

theorem context_13_76812_158943 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76812 ⟨158943, by decide⟩ :=
  accepted_of_selected 13 76812 ⟨158943, by decide⟩ ⟨13, 2, 0, 158943, 76812, 3601, 16384⟩
    (by decide) selected_cut_05112

theorem selected_cut_05113 : selected 8 ⟨159000, by decide⟩
    (prefixPartial 13 76813) = some ⟨13, 2, 0, 159000, 76813, 3469, 16384⟩ := by
  decide +kernel

theorem context_13_76813_159000 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76813 ⟨159000, by decide⟩ :=
  accepted_of_selected 13 76813 ⟨159000, by decide⟩ ⟨13, 2, 0, 159000, 76813, 3469, 16384⟩
    (by decide) selected_cut_05113

theorem selected_cut_05114 : selected 8 ⟨159025, by decide⟩
    (prefixPartial 13 76814) = some ⟨13, 2, 0, 159025, 76814, 1985, 16384⟩ := by
  decide +kernel

theorem context_13_76814_159025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76814 ⟨159025, by decide⟩ :=
  accepted_of_selected 13 76814 ⟨159025, by decide⟩ ⟨13, 2, 0, 159025, 76814, 1985, 16384⟩
    (by decide) selected_cut_05114

theorem selected_cut_05115 : selected 8 ⟨159033, by decide⟩
    (prefixPartial 13 76815) = some ⟨13, 2, 0, 159033, 76815, 721, 16384⟩ := by
  decide +kernel

theorem context_13_76815_159033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76815 ⟨159033, by decide⟩ :=
  accepted_of_selected 13 76815 ⟨159033, by decide⟩ ⟨13, 2, 0, 159033, 76815, 721, 16384⟩
    (by decide) selected_cut_05115

theorem unmarked_context_12_19203_159034 : frontier 9 ⟨159034, by decide⟩
    (prefixCache 12 19203) (prefixPartial 12 19203) = false := by
  decide +kernel

theorem node_context_12_19203_159034 : EJMOriginalGlobalDAGData.nodes 9 ⟨159034, by decide⟩ =
    .split (coordinate 12) (![⟨158943, by decide⟩,⟨159000, by decide⟩,⟨159025, by decide⟩,⟨159033, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_19203_159034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19203 ⟨159034, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 19203
    ⟨159034, by decide⟩ (by decide) (![⟨158943, by decide⟩,⟨159000, by decide⟩,⟨159025, by decide⟩,⟨159033, by decide⟩]) unmarked_context_12_19203_159034 node_context_12_19203_159034
  intro a
  fin_cases a
  · exact context_13_76812_158943
  · exact context_13_76813_159000
  · exact context_13_76814_159025
  · exact context_13_76815_159033

theorem unmarked_context_11_4800_159035 : frontier 10 ⟨159035, by decide⟩
    (prefixCache 11 4800) (prefixPartial 11 4800) = false := by
  decide +kernel

theorem node_context_11_4800_159035 : EJMOriginalGlobalDAGData.nodes 10 ⟨159035, by decide⟩ =
    .split (coordinate 11) (![⟨158552, by decide⟩,⟨158707, by decide⟩,⟨158893, by decide⟩,⟨159034, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4800_159035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4800 ⟨159035, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4800
    ⟨159035, by decide⟩ (by decide) (![⟨158552, by decide⟩,⟨158707, by decide⟩,⟨158893, by decide⟩,⟨159034, by decide⟩]) unmarked_context_11_4800_159035 node_context_11_4800_159035
  intro a
  fin_cases a
  · exact context_12_19200_158552
  · exact context_12_19201_158707
  · exact context_12_19202_158893
  · exact context_12_19203_159034

theorem selected_cut_05116 : selected 9 ⟨4595, by decide⟩
    (prefixPartial 12 19204) = some ⟨12, 1, 0, 4595, 19204, 1, 65536⟩ := by
  decide +kernel

theorem context_12_19204_4595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19204 ⟨4595, by decide⟩ :=
  accepted_of_selected 12 19204 ⟨4595, by decide⟩ ⟨12, 1, 0, 4595, 19204, 1, 65536⟩
    (by decide) selected_cut_05116

theorem selected_cut_05117 : selected 8 ⟨159100, by decide⟩
    (prefixPartial 13 76820) = some ⟨13, 2, 0, 159100, 76820, 4013, 16384⟩ := by
  decide +kernel

theorem context_13_76820_159100 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76820 ⟨159100, by decide⟩ :=
  accepted_of_selected 13 76820 ⟨159100, by decide⟩ ⟨13, 2, 0, 159100, 76820, 4013, 16384⟩
    (by decide) selected_cut_05117

theorem selected_cut_05118 : selected 8 ⟨159150, by decide⟩
    (prefixPartial 13 76821) = some ⟨13, 2, 0, 159150, 76821, 3537, 16384⟩ := by
  decide +kernel

theorem context_13_76821_159150 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76821 ⟨159150, by decide⟩ :=
  accepted_of_selected 13 76821 ⟨159150, by decide⟩ ⟨13, 2, 0, 159150, 76821, 3537, 16384⟩
    (by decide) selected_cut_05118

theorem selected_cut_05119 : selected 8 ⟨159180, by decide⟩
    (prefixPartial 13 76822) = some ⟨13, 2, 0, 159180, 76822, 2253, 16384⟩ := by
  decide +kernel

theorem context_13_76822_159180 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76822 ⟨159180, by decide⟩ :=
  accepted_of_selected 13 76822 ⟨159180, by decide⟩ ⟨13, 2, 0, 159180, 76822, 2253, 16384⟩
    (by decide) selected_cut_05119

theorem selected_cut_05120 : selected 8 ⟨159194, by decide⟩
    (prefixPartial 13 76823) = some ⟨13, 2, 0, 159194, 76823, 953, 16384⟩ := by
  decide +kernel

theorem context_13_76823_159194 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76823 ⟨159194, by decide⟩ :=
  accepted_of_selected 13 76823 ⟨159194, by decide⟩ ⟨13, 2, 0, 159194, 76823, 953, 16384⟩
    (by decide) selected_cut_05120

theorem unmarked_context_12_19205_159195 : frontier 9 ⟨159195, by decide⟩
    (prefixCache 12 19205) (prefixPartial 12 19205) = false := by
  decide +kernel

theorem node_context_12_19205_159195 : EJMOriginalGlobalDAGData.nodes 9 ⟨159195, by decide⟩ =
    .split (coordinate 12) (![⟨159100, by decide⟩,⟨159150, by decide⟩,⟨159180, by decide⟩,⟨159194, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_19205_159195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19205 ⟨159195, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 19205
    ⟨159195, by decide⟩ (by decide) (![⟨159100, by decide⟩,⟨159150, by decide⟩,⟨159180, by decide⟩,⟨159194, by decide⟩]) unmarked_context_12_19205_159195 node_context_12_19205_159195
  intro a
  fin_cases a
  · exact context_13_76820_159100
  · exact context_13_76821_159150
  · exact context_13_76822_159180
  · exact context_13_76823_159194

theorem selected_cut_05121 : selected 8 ⟨159286, by decide⟩
    (prefixPartial 13 76824) = some ⟨13, 2, 0, 159286, 76824, 3765, 16384⟩ := by
  decide +kernel

theorem context_13_76824_159286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76824 ⟨159286, by decide⟩ :=
  accepted_of_selected 13 76824 ⟨159286, by decide⟩ ⟨13, 2, 0, 159286, 76824, 3765, 16384⟩
    (by decide) selected_cut_05121

theorem selected_cut_05122 : selected 8 ⟨159360, by decide⟩
    (prefixPartial 13 76825) = some ⟨13, 2, 0, 159360, 76825, 2253, 16384⟩ := by
  decide +kernel

theorem context_13_76825_159360 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76825 ⟨159360, by decide⟩ :=
  accepted_of_selected 13 76825 ⟨159360, by decide⟩ ⟨13, 2, 0, 159360, 76825, 2253, 16384⟩
    (by decide) selected_cut_05122

theorem selected_cut_05123 : selected 8 ⟨159391, by decide⟩
    (prefixPartial 13 76826) = some ⟨13, 2, 0, 159391, 76826, 705, 16384⟩ := by
  decide +kernel

theorem context_13_76826_159391 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76826 ⟨159391, by decide⟩ :=
  accepted_of_selected 13 76826 ⟨159391, by decide⟩ ⟨13, 2, 0, 159391, 76826, 705, 16384⟩
    (by decide) selected_cut_05123

theorem selected_cut_05124 : selected 8 ⟨159393, by decide⟩
    (prefixPartial 13 76827) = some ⟨13, 2, 0, 159393, 76827, 105, 16384⟩ := by
  decide +kernel

theorem context_13_76827_159393 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76827 ⟨159393, by decide⟩ :=
  accepted_of_selected 13 76827 ⟨159393, by decide⟩ ⟨13, 2, 0, 159393, 76827, 105, 16384⟩
    (by decide) selected_cut_05124

theorem unmarked_context_12_19206_159394 : frontier 9 ⟨159394, by decide⟩
    (prefixCache 12 19206) (prefixPartial 12 19206) = false := by
  decide +kernel

theorem node_context_12_19206_159394 : EJMOriginalGlobalDAGData.nodes 9 ⟨159394, by decide⟩ =
    .split (coordinate 12) (![⟨159286, by decide⟩,⟨159360, by decide⟩,⟨159391, by decide⟩,⟨159393, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_19206_159394 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19206 ⟨159394, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 19206
    ⟨159394, by decide⟩ (by decide) (![⟨159286, by decide⟩,⟨159360, by decide⟩,⟨159391, by decide⟩,⟨159393, by decide⟩]) unmarked_context_12_19206_159394 node_context_12_19206_159394
  intro a
  fin_cases a
  · exact context_13_76824_159286
  · exact context_13_76825_159360
  · exact context_13_76826_159391
  · exact context_13_76827_159393

theorem selected_cut_05125 : selected 8 ⟨159442, by decide⟩
    (prefixPartial 13 76828) = some ⟨13, 2, 0, 159442, 76828, 3473, 16384⟩ := by
  decide +kernel

theorem context_13_76828_159442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76828 ⟨159442, by decide⟩ :=
  accepted_of_selected 13 76828 ⟨159442, by decide⟩ ⟨13, 2, 0, 159442, 76828, 3473, 16384⟩
    (by decide) selected_cut_05125

theorem selected_cut_05126 : selected 8 ⟨159503, by decide⟩
    (prefixPartial 13 76829) = some ⟨13, 2, 0, 159503, 76829, 3809, 16384⟩ := by
  decide +kernel

theorem context_13_76829_159503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76829 ⟨159503, by decide⟩ :=
  accepted_of_selected 13 76829 ⟨159503, by decide⟩ ⟨13, 2, 0, 159503, 76829, 3809, 16384⟩
    (by decide) selected_cut_05126

theorem selected_cut_05127 : selected 8 ⟨159536, by decide⟩
    (prefixPartial 13 76830) = some ⟨13, 2, 0, 159536, 76830, 2393, 16384⟩ := by
  decide +kernel

theorem context_13_76830_159536 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76830 ⟨159536, by decide⟩ :=
  accepted_of_selected 13 76830 ⟨159536, by decide⟩ ⟨13, 2, 0, 159536, 76830, 2393, 16384⟩
    (by decide) selected_cut_05127

theorem selected_cut_05128 : selected 8 ⟨159546, by decide⟩
    (prefixPartial 13 76831) = some ⟨13, 2, 0, 159546, 76831, 957, 16384⟩ := by
  decide +kernel

theorem context_13_76831_159546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76831 ⟨159546, by decide⟩ :=
  accepted_of_selected 13 76831 ⟨159546, by decide⟩ ⟨13, 2, 0, 159546, 76831, 957, 16384⟩
    (by decide) selected_cut_05128

theorem unmarked_context_12_19207_159547 : frontier 9 ⟨159547, by decide⟩
    (prefixCache 12 19207) (prefixPartial 12 19207) = false := by
  decide +kernel

theorem node_context_12_19207_159547 : EJMOriginalGlobalDAGData.nodes 9 ⟨159547, by decide⟩ =
    .split (coordinate 12) (![⟨159442, by decide⟩,⟨159503, by decide⟩,⟨159536, by decide⟩,⟨159546, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_19207_159547 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19207 ⟨159547, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 19207
    ⟨159547, by decide⟩ (by decide) (![⟨159442, by decide⟩,⟨159503, by decide⟩,⟨159536, by decide⟩,⟨159546, by decide⟩]) unmarked_context_12_19207_159547 node_context_12_19207_159547
  intro a
  fin_cases a
  · exact context_13_76828_159442
  · exact context_13_76829_159503
  · exact context_13_76830_159536
  · exact context_13_76831_159546

theorem unmarked_context_11_4801_159548 : frontier 10 ⟨159548, by decide⟩
    (prefixCache 11 4801) (prefixPartial 11 4801) = false := by
  decide +kernel

theorem node_context_11_4801_159548 : EJMOriginalGlobalDAGData.nodes 10 ⟨159548, by decide⟩ =
    .split (coordinate 11) (![⟨4595, by decide⟩,⟨159195, by decide⟩,⟨159394, by decide⟩,⟨159547, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4801_159548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4801 ⟨159548, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4801
    ⟨159548, by decide⟩ (by decide) (![⟨4595, by decide⟩,⟨159195, by decide⟩,⟨159394, by decide⟩,⟨159547, by decide⟩]) unmarked_context_11_4801_159548 node_context_11_4801_159548
  intro a
  fin_cases a
  · exact context_12_19204_4595
  · exact context_12_19205_159195
  · exact context_12_19206_159394
  · exact context_12_19207_159547

theorem selected_cut_05129 : selected 9 ⟨4595, by decide⟩
    (prefixPartial 12 19208) = some ⟨12, 1, 0, 4595, 19208, 1, 65536⟩ := by
  decide +kernel

theorem context_12_19208_4595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19208 ⟨4595, by decide⟩ :=
  accepted_of_selected 12 19208 ⟨4595, by decide⟩ ⟨12, 1, 0, 4595, 19208, 1, 65536⟩
    (by decide) selected_cut_05129

theorem selected_cut_05130 : selected 8 ⟨159617, by decide⟩
    (prefixPartial 13 76836) = some ⟨13, 2, 0, 159617, 76836, 3461, 16384⟩ := by
  decide +kernel

theorem context_13_76836_159617 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76836 ⟨159617, by decide⟩ :=
  accepted_of_selected 13 76836 ⟨159617, by decide⟩ ⟨13, 2, 0, 159617, 76836, 3461, 16384⟩
    (by decide) selected_cut_05130

theorem selected_cut_05131 : selected 8 ⟨159684, by decide⟩
    (prefixPartial 13 76837) = some ⟨13, 2, 0, 159684, 76837, 2173, 16384⟩ := by
  decide +kernel

theorem context_13_76837_159684 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76837 ⟨159684, by decide⟩ :=
  accepted_of_selected 13 76837 ⟨159684, by decide⟩ ⟨13, 2, 0, 159684, 76837, 2173, 16384⟩
    (by decide) selected_cut_05131

theorem selected_cut_05132 : selected 8 ⟨159705, by decide⟩
    (prefixPartial 13 76838) = some ⟨13, 2, 0, 159705, 76838, 661, 16384⟩ := by
  decide +kernel

theorem context_13_76838_159705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76838 ⟨159705, by decide⟩ :=
  accepted_of_selected 13 76838 ⟨159705, by decide⟩ ⟨13, 2, 0, 159705, 76838, 661, 16384⟩
    (by decide) selected_cut_05132

theorem selected_cut_05133 : selected 8 ⟨158551, by decide⟩
    (prefixPartial 13 76839) = some ⟨13, 2, 0, 158551, 76839, 109, 16384⟩ := by
  decide +kernel

theorem context_13_76839_158551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76839 ⟨158551, by decide⟩ :=
  accepted_of_selected 13 76839 ⟨158551, by decide⟩ ⟨13, 2, 0, 158551, 76839, 109, 16384⟩
    (by decide) selected_cut_05133

theorem unmarked_context_12_19209_159706 : frontier 9 ⟨159706, by decide⟩
    (prefixCache 12 19209) (prefixPartial 12 19209) = false := by
  decide +kernel

theorem node_context_12_19209_159706 : EJMOriginalGlobalDAGData.nodes 9 ⟨159706, by decide⟩ =
    .split (coordinate 12) (![⟨159617, by decide⟩,⟨159684, by decide⟩,⟨159705, by decide⟩,⟨158551, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_19209_159706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19209 ⟨159706, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 19209
    ⟨159706, by decide⟩ (by decide) (![⟨159617, by decide⟩,⟨159684, by decide⟩,⟨159705, by decide⟩,⟨158551, by decide⟩]) unmarked_context_12_19209_159706 node_context_12_19209_159706
  intro a
  fin_cases a
  · exact context_13_76836_159617
  · exact context_13_76837_159684
  · exact context_13_76838_159705
  · exact context_13_76839_158551

theorem selected_cut_05134 : selected 9 ⟨4595, by decide⟩
    (prefixPartial 12 19210) = some ⟨12, 1, 0, 4595, 19210, 1, 65536⟩ := by
  decide +kernel

theorem context_12_19210_4595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19210 ⟨4595, by decide⟩ :=
  accepted_of_selected 12 19210 ⟨4595, by decide⟩ ⟨12, 1, 0, 4595, 19210, 1, 65536⟩
    (by decide) selected_cut_05134

theorem selected_cut_05135 : selected 8 ⟨159753, by decide⟩
    (prefixPartial 13 76844) = some ⟨13, 2, 0, 159753, 76844, 3097, 16384⟩ := by
  decide +kernel

theorem context_13_76844_159753 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76844 ⟨159753, by decide⟩ :=
  accepted_of_selected 13 76844 ⟨159753, by decide⟩ ⟨13, 2, 0, 159753, 76844, 3097, 16384⟩
    (by decide) selected_cut_05135

theorem selected_cut_05136 : selected 8 ⟨159814, by decide⟩
    (prefixPartial 13 76845) = some ⟨13, 2, 0, 159814, 76845, 3885, 16384⟩ := by
  decide +kernel

theorem context_13_76845_159814 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76845 ⟨159814, by decide⟩ :=
  accepted_of_selected 13 76845 ⟨159814, by decide⟩ ⟨13, 2, 0, 159814, 76845, 3885, 16384⟩
    (by decide) selected_cut_05136

theorem selected_cut_05137 : selected 8 ⟨159839, by decide⟩
    (prefixPartial 13 76846) = some ⟨13, 2, 0, 159839, 76846, 2189, 16384⟩ := by
  decide +kernel

theorem context_13_76846_159839 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76846 ⟨159839, by decide⟩ :=
  accepted_of_selected 13 76846 ⟨159839, by decide⟩ ⟨13, 2, 0, 159839, 76846, 2189, 16384⟩
    (by decide) selected_cut_05137

theorem selected_cut_05138 : selected 8 ⟨159848, by decide⟩
    (prefixPartial 13 76847) = some ⟨13, 2, 0, 159848, 76847, 913, 16384⟩ := by
  decide +kernel

theorem context_13_76847_159848 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76847 ⟨159848, by decide⟩ :=
  accepted_of_selected 13 76847 ⟨159848, by decide⟩ ⟨13, 2, 0, 159848, 76847, 913, 16384⟩
    (by decide) selected_cut_05138

theorem unmarked_context_12_19211_159849 : frontier 9 ⟨159849, by decide⟩
    (prefixCache 12 19211) (prefixPartial 12 19211) = false := by
  decide +kernel

theorem node_context_12_19211_159849 : EJMOriginalGlobalDAGData.nodes 9 ⟨159849, by decide⟩ =
    .split (coordinate 12) (![⟨159753, by decide⟩,⟨159814, by decide⟩,⟨159839, by decide⟩,⟨159848, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_19211_159849 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19211 ⟨159849, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 19211
    ⟨159849, by decide⟩ (by decide) (![⟨159753, by decide⟩,⟨159814, by decide⟩,⟨159839, by decide⟩,⟨159848, by decide⟩]) unmarked_context_12_19211_159849 node_context_12_19211_159849
  intro a
  fin_cases a
  · exact context_13_76844_159753
  · exact context_13_76845_159814
  · exact context_13_76846_159839
  · exact context_13_76847_159848

theorem unmarked_context_11_4802_159850 : frontier 10 ⟨159850, by decide⟩
    (prefixCache 11 4802) (prefixPartial 11 4802) = false := by
  decide +kernel

theorem node_context_11_4802_159850 : EJMOriginalGlobalDAGData.nodes 10 ⟨159850, by decide⟩ =
    .split (coordinate 11) (![⟨4595, by decide⟩,⟨159706, by decide⟩,⟨4595, by decide⟩,⟨159849, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4802_159850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4802 ⟨159850, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4802
    ⟨159850, by decide⟩ (by decide) (![⟨4595, by decide⟩,⟨159706, by decide⟩,⟨4595, by decide⟩,⟨159849, by decide⟩]) unmarked_context_11_4802_159850 node_context_11_4802_159850
  intro a
  fin_cases a
  · exact context_12_19208_4595
  · exact context_12_19209_159706
  · exact context_12_19210_4595
  · exact context_12_19211_159849

theorem selected_cut_05139 : selected 9 ⟨4595, by decide⟩
    (prefixPartial 12 19212) = some ⟨12, 1, 0, 4595, 19212, 1, 65536⟩ := by
  decide +kernel

theorem context_12_19212_4595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19212 ⟨4595, by decide⟩ :=
  accepted_of_selected 12 19212 ⟨4595, by decide⟩ ⟨12, 1, 0, 4595, 19212, 1, 65536⟩
    (by decide) selected_cut_05139

theorem selected_cut_05140 : selected 9 ⟨4595, by decide⟩
    (prefixPartial 12 19213) = some ⟨12, 1, 0, 4595, 19213, 1, 65536⟩ := by
  decide +kernel

theorem context_12_19213_4595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19213 ⟨4595, by decide⟩ :=
  accepted_of_selected 12 19213 ⟨4595, by decide⟩ ⟨12, 1, 0, 4595, 19213, 1, 65536⟩
    (by decide) selected_cut_05140

theorem selected_cut_05141 : selected 9 ⟨4595, by decide⟩
    (prefixPartial 12 19214) = some ⟨12, 1, 0, 4595, 19214, 1, 65536⟩ := by
  decide +kernel

theorem context_12_19214_4595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19214 ⟨4595, by decide⟩ :=
  accepted_of_selected 12 19214 ⟨4595, by decide⟩ ⟨12, 1, 0, 4595, 19214, 1, 65536⟩
    (by decide) selected_cut_05141

theorem selected_cut_05142 : selected 8 ⟨159921, by decide⟩
    (prefixPartial 13 76860) = some ⟨13, 2, 0, 159921, 76860, 3921, 16384⟩ := by
  decide +kernel

theorem context_13_76860_159921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76860 ⟨159921, by decide⟩ :=
  accepted_of_selected 13 76860 ⟨159921, by decide⟩ ⟨13, 2, 0, 159921, 76860, 3921, 16384⟩
    (by decide) selected_cut_05142

theorem selected_cut_05143 : selected 8 ⟨160031, by decide⟩
    (prefixPartial 13 76861) = some ⟨13, 2, 0, 160031, 76861, 3021, 16384⟩ := by
  decide +kernel

theorem context_13_76861_160031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76861 ⟨160031, by decide⟩ :=
  accepted_of_selected 13 76861 ⟨160031, by decide⟩ ⟨13, 2, 0, 160031, 76861, 3021, 16384⟩
    (by decide) selected_cut_05143

theorem selected_cut_05144 : selected 8 ⟨160068, by decide⟩
    (prefixPartial 13 76862) = some ⟨13, 2, 0, 160068, 76862, 849, 16384⟩ := by
  decide +kernel

theorem context_13_76862_160068 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76862 ⟨160068, by decide⟩ :=
  accepted_of_selected 13 76862 ⟨160068, by decide⟩ ⟨13, 2, 0, 160068, 76862, 849, 16384⟩
    (by decide) selected_cut_05144

theorem selected_cut_05145 : selected 8 ⟨160075, by decide⟩
    (prefixPartial 13 76863) = some ⟨13, 2, 0, 160075, 76863, 109, 16384⟩ := by
  decide +kernel

theorem context_13_76863_160075 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76863 ⟨160075, by decide⟩ :=
  accepted_of_selected 13 76863 ⟨160075, by decide⟩ ⟨13, 2, 0, 160075, 76863, 109, 16384⟩
    (by decide) selected_cut_05145

theorem unmarked_context_12_19215_160076 : frontier 9 ⟨160076, by decide⟩
    (prefixCache 12 19215) (prefixPartial 12 19215) = false := by
  decide +kernel

theorem node_context_12_19215_160076 : EJMOriginalGlobalDAGData.nodes 9 ⟨160076, by decide⟩ =
    .split (coordinate 12) (![⟨159921, by decide⟩,⟨160031, by decide⟩,⟨160068, by decide⟩,⟨160075, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_19215_160076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19215 ⟨160076, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 19215
    ⟨160076, by decide⟩ (by decide) (![⟨159921, by decide⟩,⟨160031, by decide⟩,⟨160068, by decide⟩,⟨160075, by decide⟩]) unmarked_context_12_19215_160076 node_context_12_19215_160076
  intro a
  fin_cases a
  · exact context_13_76860_159921
  · exact context_13_76861_160031
  · exact context_13_76862_160068
  · exact context_13_76863_160075

theorem unmarked_context_11_4803_160077 : frontier 10 ⟨160077, by decide⟩
    (prefixCache 11 4803) (prefixPartial 11 4803) = false := by
  decide +kernel

theorem node_context_11_4803_160077 : EJMOriginalGlobalDAGData.nodes 10 ⟨160077, by decide⟩ =
    .split (coordinate 11) (![⟨4595, by decide⟩,⟨4595, by decide⟩,⟨4595, by decide⟩,⟨160076, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4803_160077 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4803 ⟨160077, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4803
    ⟨160077, by decide⟩ (by decide) (![⟨4595, by decide⟩,⟨4595, by decide⟩,⟨4595, by decide⟩,⟨160076, by decide⟩]) unmarked_context_11_4803_160077 node_context_11_4803_160077
  intro a
  fin_cases a
  · exact context_12_19212_4595
  · exact context_12_19213_4595
  · exact context_12_19214_4595
  · exact context_12_19215_160076

theorem unmarked_context_10_1200_160078 : frontier 11 ⟨160078, by decide⟩
    (prefixCache 10 1200) (prefixPartial 10 1200) = false := by
  decide +kernel

theorem node_context_10_1200_160078 : EJMOriginalGlobalDAGData.nodes 11 ⟨160078, by decide⟩ =
    .split (coordinate 10) (![⟨159035, by decide⟩,⟨159548, by decide⟩,⟨159850, by decide⟩,⟨160077, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1200_160078 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1200 ⟨160078, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1200
    ⟨160078, by decide⟩ (by decide) (![⟨159035, by decide⟩,⟨159548, by decide⟩,⟨159850, by decide⟩,⟨160077, by decide⟩]) unmarked_context_10_1200_160078 node_context_10_1200_160078
  intro a
  fin_cases a
  · exact context_11_4800_159035
  · exact context_11_4801_159548
  · exact context_11_4802_159850
  · exact context_11_4803_160077

theorem selected_cut_05146 : selected 8 ⟨160106, by decide⟩
    (prefixPartial 13 76864) = some ⟨13, 2, 0, 160106, 76864, 2453, 16384⟩ := by
  decide +kernel

theorem context_13_76864_160106 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76864 ⟨160106, by decide⟩ :=
  accepted_of_selected 13 76864 ⟨160106, by decide⟩ ⟨13, 2, 0, 160106, 76864, 2453, 16384⟩
    (by decide) selected_cut_05146

theorem selected_cut_05147 : selected 8 ⟨160135, by decide⟩
    (prefixPartial 13 76865) = some ⟨13, 2, 0, 160135, 76865, 2865, 16384⟩ := by
  decide +kernel

theorem context_13_76865_160135 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76865 ⟨160135, by decide⟩ :=
  accepted_of_selected 13 76865 ⟨160135, by decide⟩ ⟨13, 2, 0, 160135, 76865, 2865, 16384⟩
    (by decide) selected_cut_05147

theorem selected_cut_05148 : selected 8 ⟨160162, by decide⟩
    (prefixPartial 13 76866) = some ⟨13, 2, 0, 160162, 76866, 1653, 16384⟩ := by
  decide +kernel

theorem context_13_76866_160162 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76866 ⟨160162, by decide⟩ :=
  accepted_of_selected 13 76866 ⟨160162, by decide⟩ ⟨13, 2, 0, 160162, 76866, 1653, 16384⟩
    (by decide) selected_cut_05148

theorem selected_cut_05149 : selected 8 ⟨160167, by decide⟩
    (prefixPartial 13 76867) = some ⟨13, 2, 0, 160167, 76867, 905, 16384⟩ := by
  decide +kernel

theorem context_13_76867_160167 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76867 ⟨160167, by decide⟩ :=
  accepted_of_selected 13 76867 ⟨160167, by decide⟩ ⟨13, 2, 0, 160167, 76867, 905, 16384⟩
    (by decide) selected_cut_05149

theorem unmarked_context_12_19216_160168 : frontier 9 ⟨160168, by decide⟩
    (prefixCache 12 19216) (prefixPartial 12 19216) = false := by
  decide +kernel

theorem node_context_12_19216_160168 : EJMOriginalGlobalDAGData.nodes 9 ⟨160168, by decide⟩ =
    .split (coordinate 12) (![⟨160106, by decide⟩,⟨160135, by decide⟩,⟨160162, by decide⟩,⟨160167, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_19216_160168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19216 ⟨160168, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 19216
    ⟨160168, by decide⟩ (by decide) (![⟨160106, by decide⟩,⟨160135, by decide⟩,⟨160162, by decide⟩,⟨160167, by decide⟩]) unmarked_context_12_19216_160168 node_context_12_19216_160168
  intro a
  fin_cases a
  · exact context_13_76864_160106
  · exact context_13_76865_160135
  · exact context_13_76866_160162
  · exact context_13_76867_160167

theorem selected_cut_05150 : selected 8 ⟨160201, by decide⟩
    (prefixPartial 13 76868) = some ⟨13, 2, 0, 160201, 76868, 2489, 16384⟩ := by
  decide +kernel

theorem context_13_76868_160201 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76868 ⟨160201, by decide⟩ :=
  accepted_of_selected 13 76868 ⟨160201, by decide⟩ ⟨13, 2, 0, 160201, 76868, 2489, 16384⟩
    (by decide) selected_cut_05150

theorem selected_cut_05151 : selected 8 ⟨160242, by decide⟩
    (prefixPartial 13 76869) = some ⟨13, 2, 0, 160242, 76869, 2497, 16384⟩ := by
  decide +kernel

theorem context_13_76869_160242 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76869 ⟨160242, by decide⟩ :=
  accepted_of_selected 13 76869 ⟨160242, by decide⟩ ⟨13, 2, 0, 160242, 76869, 2497, 16384⟩
    (by decide) selected_cut_05151

theorem selected_cut_05152 : selected 8 ⟨160267, by decide⟩
    (prefixPartial 13 76870) = some ⟨13, 2, 0, 160267, 76870, 1785, 16384⟩ := by
  decide +kernel

theorem context_13_76870_160267 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76870 ⟨160267, by decide⟩ :=
  accepted_of_selected 13 76870 ⟨160267, by decide⟩ ⟨13, 2, 0, 160267, 76870, 1785, 16384⟩
    (by decide) selected_cut_05152

theorem selected_cut_05153 : selected 8 ⟨160271, by decide⟩
    (prefixPartial 13 76871) = some ⟨13, 2, 0, 160271, 76871, 645, 16384⟩ := by
  decide +kernel

theorem context_13_76871_160271 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76871 ⟨160271, by decide⟩ :=
  accepted_of_selected 13 76871 ⟨160271, by decide⟩ ⟨13, 2, 0, 160271, 76871, 645, 16384⟩
    (by decide) selected_cut_05153

theorem unmarked_context_12_19217_160272 : frontier 9 ⟨160272, by decide⟩
    (prefixCache 12 19217) (prefixPartial 12 19217) = false := by
  decide +kernel

theorem node_context_12_19217_160272 : EJMOriginalGlobalDAGData.nodes 9 ⟨160272, by decide⟩ =
    .split (coordinate 12) (![⟨160201, by decide⟩,⟨160242, by decide⟩,⟨160267, by decide⟩,⟨160271, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_19217_160272 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19217 ⟨160272, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 19217
    ⟨160272, by decide⟩ (by decide) (![⟨160201, by decide⟩,⟨160242, by decide⟩,⟨160267, by decide⟩,⟨160271, by decide⟩]) unmarked_context_12_19217_160272 node_context_12_19217_160272
  intro a
  fin_cases a
  · exact context_13_76868_160201
  · exact context_13_76869_160242
  · exact context_13_76870_160267
  · exact context_13_76871_160271

theorem selected_cut_05154 : selected 8 ⟨160302, by decide⟩
    (prefixPartial 13 76872) = some ⟨13, 2, 0, 160302, 76872, 2473, 16384⟩ := by
  decide +kernel

theorem context_13_76872_160302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76872 ⟨160302, by decide⟩ :=
  accepted_of_selected 13 76872 ⟨160302, by decide⟩ ⟨13, 2, 0, 160302, 76872, 2473, 16384⟩
    (by decide) selected_cut_05154

theorem selected_cut_05155 : selected 8 ⟨160345, by decide⟩
    (prefixPartial 13 76873) = some ⟨13, 2, 0, 160345, 76873, 3041, 16384⟩ := by
  decide +kernel

theorem context_13_76873_160345 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76873 ⟨160345, by decide⟩ :=
  accepted_of_selected 13 76873 ⟨160345, by decide⟩ ⟨13, 2, 0, 160345, 76873, 3041, 16384⟩
    (by decide) selected_cut_05155

theorem selected_cut_05156 : selected 8 ⟨160371, by decide⟩
    (prefixPartial 13 76874) = some ⟨13, 2, 0, 160371, 76874, 1829, 16384⟩ := by
  decide +kernel

theorem context_13_76874_160371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76874 ⟨160371, by decide⟩ :=
  accepted_of_selected 13 76874 ⟨160371, by decide⟩ ⟨13, 2, 0, 160371, 76874, 1829, 16384⟩
    (by decide) selected_cut_05156

theorem selected_cut_05157 : selected 8 ⟨160376, by decide⟩
    (prefixPartial 13 76875) = some ⟨13, 2, 0, 160376, 76875, 745, 16384⟩ := by
  decide +kernel

theorem context_13_76875_160376 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76875 ⟨160376, by decide⟩ :=
  accepted_of_selected 13 76875 ⟨160376, by decide⟩ ⟨13, 2, 0, 160376, 76875, 745, 16384⟩
    (by decide) selected_cut_05157

theorem unmarked_context_12_19218_160377 : frontier 9 ⟨160377, by decide⟩
    (prefixCache 12 19218) (prefixPartial 12 19218) = false := by
  decide +kernel

theorem node_context_12_19218_160377 : EJMOriginalGlobalDAGData.nodes 9 ⟨160377, by decide⟩ =
    .split (coordinate 12) (![⟨160302, by decide⟩,⟨160345, by decide⟩,⟨160371, by decide⟩,⟨160376, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_19218_160377 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19218 ⟨160377, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 19218
    ⟨160377, by decide⟩ (by decide) (![⟨160302, by decide⟩,⟨160345, by decide⟩,⟨160371, by decide⟩,⟨160376, by decide⟩]) unmarked_context_12_19218_160377 node_context_12_19218_160377
  intro a
  fin_cases a
  · exact context_13_76872_160302
  · exact context_13_76873_160345
  · exact context_13_76874_160371
  · exact context_13_76875_160376

theorem selected_cut_05158 : selected 8 ⟨160406, by decide⟩
    (prefixPartial 13 76876) = some ⟨13, 2, 0, 160406, 76876, 2153, 16384⟩ := by
  decide +kernel

theorem context_13_76876_160406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76876 ⟨160406, by decide⟩ :=
  accepted_of_selected 13 76876 ⟨160406, by decide⟩ ⟨13, 2, 0, 160406, 76876, 2153, 16384⟩
    (by decide) selected_cut_05158

theorem selected_cut_05159 : selected 8 ⟨160444, by decide⟩
    (prefixPartial 13 76877) = some ⟨13, 2, 0, 160444, 76877, 2701, 16384⟩ := by
  decide +kernel

theorem context_13_76877_160444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76877 ⟨160444, by decide⟩ :=
  accepted_of_selected 13 76877 ⟨160444, by decide⟩ ⟨13, 2, 0, 160444, 76877, 2701, 16384⟩
    (by decide) selected_cut_05159

theorem selected_cut_05160 : selected 8 ⟨160469, by decide⟩
    (prefixPartial 13 76878) = some ⟨13, 2, 0, 160469, 76878, 1657, 16384⟩ := by
  decide +kernel

theorem context_13_76878_160469 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76878 ⟨160469, by decide⟩ :=
  accepted_of_selected 13 76878 ⟨160469, by decide⟩ ⟨13, 2, 0, 160469, 76878, 1657, 16384⟩
    (by decide) selected_cut_05160

theorem selected_cut_05161 : selected 8 ⟨160474, by decide⟩
    (prefixPartial 13 76879) = some ⟨13, 2, 0, 160474, 76879, 633, 16384⟩ := by
  decide +kernel

theorem context_13_76879_160474 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76879 ⟨160474, by decide⟩ :=
  accepted_of_selected 13 76879 ⟨160474, by decide⟩ ⟨13, 2, 0, 160474, 76879, 633, 16384⟩
    (by decide) selected_cut_05161

theorem unmarked_context_12_19219_160475 : frontier 9 ⟨160475, by decide⟩
    (prefixCache 12 19219) (prefixPartial 12 19219) = false := by
  decide +kernel

theorem node_context_12_19219_160475 : EJMOriginalGlobalDAGData.nodes 9 ⟨160475, by decide⟩ =
    .split (coordinate 12) (![⟨160406, by decide⟩,⟨160444, by decide⟩,⟨160469, by decide⟩,⟨160474, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_19219_160475 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19219 ⟨160475, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 19219
    ⟨160475, by decide⟩ (by decide) (![⟨160406, by decide⟩,⟨160444, by decide⟩,⟨160469, by decide⟩,⟨160474, by decide⟩]) unmarked_context_12_19219_160475 node_context_12_19219_160475
  intro a
  fin_cases a
  · exact context_13_76876_160406
  · exact context_13_76877_160444
  · exact context_13_76878_160469
  · exact context_13_76879_160474

theorem unmarked_context_11_4804_160476 : frontier 10 ⟨160476, by decide⟩
    (prefixCache 11 4804) (prefixPartial 11 4804) = false := by
  decide +kernel

theorem node_context_11_4804_160476 : EJMOriginalGlobalDAGData.nodes 10 ⟨160476, by decide⟩ =
    .split (coordinate 11) (![⟨160168, by decide⟩,⟨160272, by decide⟩,⟨160377, by decide⟩,⟨160475, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4804_160476 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4804 ⟨160476, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4804
    ⟨160476, by decide⟩ (by decide) (![⟨160168, by decide⟩,⟨160272, by decide⟩,⟨160377, by decide⟩,⟨160475, by decide⟩]) unmarked_context_11_4804_160476 node_context_11_4804_160476
  intro a
  fin_cases a
  · exact context_12_19216_160168
  · exact context_12_19217_160272
  · exact context_12_19218_160377
  · exact context_12_19219_160475

theorem selected_cut_05162 : selected 8 ⟨160499, by decide⟩
    (prefixPartial 13 76880) = some ⟨13, 2, 0, 160499, 76880, 1825, 16384⟩ := by
  decide +kernel

theorem context_13_76880_160499 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76880 ⟨160499, by decide⟩ :=
  accepted_of_selected 13 76880 ⟨160499, by decide⟩ ⟨13, 2, 0, 160499, 76880, 1825, 16384⟩
    (by decide) selected_cut_05162

theorem selected_cut_05163 : selected 8 ⟨160542, by decide⟩
    (prefixPartial 13 76881) = some ⟨13, 2, 0, 160542, 76881, 2877, 16384⟩ := by
  decide +kernel

theorem context_13_76881_160542 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76881 ⟨160542, by decide⟩ :=
  accepted_of_selected 13 76881 ⟨160542, by decide⟩ ⟨13, 2, 0, 160542, 76881, 2877, 16384⟩
    (by decide) selected_cut_05163

theorem selected_cut_05164 : selected 8 ⟨160564, by decide⟩
    (prefixPartial 13 76882) = some ⟨13, 2, 0, 160564, 76882, 1401, 16384⟩ := by
  decide +kernel

theorem context_13_76882_160564 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76882 ⟨160564, by decide⟩ :=
  accepted_of_selected 13 76882 ⟨160564, by decide⟩ ⟨13, 2, 0, 160564, 76882, 1401, 16384⟩
    (by decide) selected_cut_05164

theorem selected_cut_05165 : selected 8 ⟨160569, by decide⟩
    (prefixPartial 13 76883) = some ⟨13, 2, 0, 160569, 76883, 957, 16384⟩ := by
  decide +kernel

theorem context_13_76883_160569 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76883 ⟨160569, by decide⟩ :=
  accepted_of_selected 13 76883 ⟨160569, by decide⟩ ⟨13, 2, 0, 160569, 76883, 957, 16384⟩
    (by decide) selected_cut_05165

theorem unmarked_context_12_19220_160570 : frontier 9 ⟨160570, by decide⟩
    (prefixCache 12 19220) (prefixPartial 12 19220) = false := by
  decide +kernel

theorem node_context_12_19220_160570 : EJMOriginalGlobalDAGData.nodes 9 ⟨160570, by decide⟩ =
    .split (coordinate 12) (![⟨160499, by decide⟩,⟨160542, by decide⟩,⟨160564, by decide⟩,⟨160569, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_19220_160570 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19220 ⟨160570, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 19220
    ⟨160570, by decide⟩ (by decide) (![⟨160499, by decide⟩,⟨160542, by decide⟩,⟨160564, by decide⟩,⟨160569, by decide⟩]) unmarked_context_12_19220_160570 node_context_12_19220_160570
  intro a
  fin_cases a
  · exact context_13_76880_160499
  · exact context_13_76881_160542
  · exact context_13_76882_160564
  · exact context_13_76883_160569

theorem selected_cut_05166 : selected 8 ⟨160603, by decide⟩
    (prefixPartial 13 76884) = some ⟨13, 2, 0, 160603, 76884, 2057, 16384⟩ := by
  decide +kernel

theorem context_13_76884_160603 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76884 ⟨160603, by decide⟩ :=
  accepted_of_selected 13 76884 ⟨160603, by decide⟩ ⟨13, 2, 0, 160603, 76884, 2057, 16384⟩
    (by decide) selected_cut_05166

theorem selected_cut_05167 : selected 8 ⟨160633, by decide⟩
    (prefixPartial 13 76885) = some ⟨13, 2, 0, 160633, 76885, 2369, 16384⟩ := by
  decide +kernel

theorem context_13_76885_160633 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76885 ⟨160633, by decide⟩ :=
  accepted_of_selected 13 76885 ⟨160633, by decide⟩ ⟨13, 2, 0, 160633, 76885, 2369, 16384⟩
    (by decide) selected_cut_05167

theorem selected_cut_05168 : selected 8 ⟨160658, by decide⟩
    (prefixPartial 13 76886) = some ⟨13, 2, 0, 160658, 76886, 1441, 16384⟩ := by
  decide +kernel

theorem context_13_76886_160658 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76886 ⟨160658, by decide⟩ :=
  accepted_of_selected 13 76886 ⟨160658, by decide⟩ ⟨13, 2, 0, 160658, 76886, 1441, 16384⟩
    (by decide) selected_cut_05168

theorem selected_cut_05169 : selected 8 ⟨160663, by decide⟩
    (prefixPartial 13 76887) = some ⟨13, 2, 0, 160663, 76887, 769, 16384⟩ := by
  decide +kernel

theorem context_13_76887_160663 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76887 ⟨160663, by decide⟩ :=
  accepted_of_selected 13 76887 ⟨160663, by decide⟩ ⟨13, 2, 0, 160663, 76887, 769, 16384⟩
    (by decide) selected_cut_05169

theorem unmarked_context_12_19221_160664 : frontier 9 ⟨160664, by decide⟩
    (prefixCache 12 19221) (prefixPartial 12 19221) = false := by
  decide +kernel

theorem node_context_12_19221_160664 : EJMOriginalGlobalDAGData.nodes 9 ⟨160664, by decide⟩ =
    .split (coordinate 12) (![⟨160603, by decide⟩,⟨160633, by decide⟩,⟨160658, by decide⟩,⟨160663, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_19221_160664 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19221 ⟨160664, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 19221
    ⟨160664, by decide⟩ (by decide) (![⟨160603, by decide⟩,⟨160633, by decide⟩,⟨160658, by decide⟩,⟨160663, by decide⟩]) unmarked_context_12_19221_160664 node_context_12_19221_160664
  intro a
  fin_cases a
  · exact context_13_76884_160603
  · exact context_13_76885_160633
  · exact context_13_76886_160658
  · exact context_13_76887_160663

theorem selected_cut_05170 : selected 8 ⟨160702, by decide⟩
    (prefixPartial 13 76888) = some ⟨13, 2, 0, 160702, 76888, 2385, 16384⟩ := by
  decide +kernel

theorem context_13_76888_160702 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76888 ⟨160702, by decide⟩ :=
  accepted_of_selected 13 76888 ⟨160702, by decide⟩ ⟨13, 2, 0, 160702, 76888, 2385, 16384⟩
    (by decide) selected_cut_05170

theorem selected_cut_05171 : selected 8 ⟨160746, by decide⟩
    (prefixPartial 13 76889) = some ⟨13, 2, 0, 160746, 76889, 3101, 16384⟩ := by
  decide +kernel

theorem context_13_76889_160746 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76889 ⟨160746, by decide⟩ :=
  accepted_of_selected 13 76889 ⟨160746, by decide⟩ ⟨13, 2, 0, 160746, 76889, 3101, 16384⟩
    (by decide) selected_cut_05171

theorem selected_cut_05172 : selected 8 ⟨160770, by decide⟩
    (prefixPartial 13 76890) = some ⟨13, 2, 0, 160770, 76890, 1869, 16384⟩ := by
  decide +kernel

theorem context_13_76890_160770 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76890 ⟨160770, by decide⟩ :=
  accepted_of_selected 13 76890 ⟨160770, by decide⟩ ⟨13, 2, 0, 160770, 76890, 1869, 16384⟩
    (by decide) selected_cut_05172

theorem selected_cut_05173 : selected 8 ⟨160776, by decide⟩
    (prefixPartial 13 76891) = some ⟨13, 2, 0, 160776, 76891, 969, 16384⟩ := by
  decide +kernel

theorem context_13_76891_160776 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76891 ⟨160776, by decide⟩ :=
  accepted_of_selected 13 76891 ⟨160776, by decide⟩ ⟨13, 2, 0, 160776, 76891, 969, 16384⟩
    (by decide) selected_cut_05173

theorem unmarked_context_12_19222_160777 : frontier 9 ⟨160777, by decide⟩
    (prefixCache 12 19222) (prefixPartial 12 19222) = false := by
  decide +kernel

theorem node_context_12_19222_160777 : EJMOriginalGlobalDAGData.nodes 9 ⟨160777, by decide⟩ =
    .split (coordinate 12) (![⟨160702, by decide⟩,⟨160746, by decide⟩,⟨160770, by decide⟩,⟨160776, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_19222_160777 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19222 ⟨160777, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 19222
    ⟨160777, by decide⟩ (by decide) (![⟨160702, by decide⟩,⟨160746, by decide⟩,⟨160770, by decide⟩,⟨160776, by decide⟩]) unmarked_context_12_19222_160777 node_context_12_19222_160777
  intro a
  fin_cases a
  · exact context_13_76888_160702
  · exact context_13_76889_160746
  · exact context_13_76890_160770
  · exact context_13_76891_160776

theorem selected_cut_05174 : selected 8 ⟨160808, by decide⟩
    (prefixPartial 13 76892) = some ⟨13, 2, 0, 160808, 76892, 2005, 16384⟩ := by
  decide +kernel

theorem context_13_76892_160808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76892 ⟨160808, by decide⟩ :=
  accepted_of_selected 13 76892 ⟨160808, by decide⟩ ⟨13, 2, 0, 160808, 76892, 2005, 16384⟩
    (by decide) selected_cut_05174

theorem selected_cut_05175 : selected 8 ⟨160843, by decide⟩
    (prefixPartial 13 76893) = some ⟨13, 2, 0, 160843, 76893, 2833, 16384⟩ := by
  decide +kernel

theorem context_13_76893_160843 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76893 ⟨160843, by decide⟩ :=
  accepted_of_selected 13 76893 ⟨160843, by decide⟩ ⟨13, 2, 0, 160843, 76893, 2833, 16384⟩
    (by decide) selected_cut_05175

theorem selected_cut_05176 : selected 8 ⟨160864, by decide⟩
    (prefixPartial 13 76894) = some ⟨13, 2, 0, 160864, 76894, 1509, 16384⟩ := by
  decide +kernel

theorem context_13_76894_160864 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76894 ⟨160864, by decide⟩ :=
  accepted_of_selected 13 76894 ⟨160864, by decide⟩ ⟨13, 2, 0, 160864, 76894, 1509, 16384⟩
    (by decide) selected_cut_05176

theorem selected_cut_05177 : selected 8 ⟨160872, by decide⟩
    (prefixPartial 13 76895) = some ⟨13, 2, 0, 160872, 76895, 821, 16384⟩ := by
  decide +kernel

theorem context_13_76895_160872 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76895 ⟨160872, by decide⟩ :=
  accepted_of_selected 13 76895 ⟨160872, by decide⟩ ⟨13, 2, 0, 160872, 76895, 821, 16384⟩
    (by decide) selected_cut_05177

theorem unmarked_context_12_19223_160873 : frontier 9 ⟨160873, by decide⟩
    (prefixCache 12 19223) (prefixPartial 12 19223) = false := by
  decide +kernel

theorem node_context_12_19223_160873 : EJMOriginalGlobalDAGData.nodes 9 ⟨160873, by decide⟩ =
    .split (coordinate 12) (![⟨160808, by decide⟩,⟨160843, by decide⟩,⟨160864, by decide⟩,⟨160872, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_19223_160873 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19223 ⟨160873, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 19223
    ⟨160873, by decide⟩ (by decide) (![⟨160808, by decide⟩,⟨160843, by decide⟩,⟨160864, by decide⟩,⟨160872, by decide⟩]) unmarked_context_12_19223_160873 node_context_12_19223_160873
  intro a
  fin_cases a
  · exact context_13_76892_160808
  · exact context_13_76893_160843
  · exact context_13_76894_160864
  · exact context_13_76895_160872

theorem unmarked_context_11_4805_160874 : frontier 10 ⟨160874, by decide⟩
    (prefixCache 11 4805) (prefixPartial 11 4805) = false := by
  decide +kernel

theorem node_context_11_4805_160874 : EJMOriginalGlobalDAGData.nodes 10 ⟨160874, by decide⟩ =
    .split (coordinate 11) (![⟨160570, by decide⟩,⟨160664, by decide⟩,⟨160777, by decide⟩,⟨160873, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4805_160874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4805 ⟨160874, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4805
    ⟨160874, by decide⟩ (by decide) (![⟨160570, by decide⟩,⟨160664, by decide⟩,⟨160777, by decide⟩,⟨160873, by decide⟩]) unmarked_context_11_4805_160874 node_context_11_4805_160874
  intro a
  fin_cases a
  · exact context_12_19220_160570
  · exact context_12_19221_160664
  · exact context_12_19222_160777
  · exact context_12_19223_160873

theorem selected_cut_05178 : selected 8 ⟨160891, by decide⟩
    (prefixPartial 13 76896) = some ⟨13, 2, 0, 160891, 76896, 1449, 16384⟩ := by
  decide +kernel

theorem context_13_76896_160891 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76896 ⟨160891, by decide⟩ :=
  accepted_of_selected 13 76896 ⟨160891, by decide⟩ ⟨13, 2, 0, 160891, 76896, 1449, 16384⟩
    (by decide) selected_cut_05178

theorem selected_cut_05179 : selected 8 ⟨160929, by decide⟩
    (prefixPartial 13 76897) = some ⟨13, 2, 0, 160929, 76897, 2813, 16384⟩ := by
  decide +kernel

theorem context_13_76897_160929 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76897 ⟨160929, by decide⟩ :=
  accepted_of_selected 13 76897 ⟨160929, by decide⟩ ⟨13, 2, 0, 160929, 76897, 2813, 16384⟩
    (by decide) selected_cut_05179

theorem selected_cut_05180 : selected 8 ⟨160951, by decide⟩
    (prefixPartial 13 76898) = some ⟨13, 2, 0, 160951, 76898, 1445, 16384⟩ := by
  decide +kernel

theorem context_13_76898_160951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76898 ⟨160951, by decide⟩ :=
  accepted_of_selected 13 76898 ⟨160951, by decide⟩ ⟨13, 2, 0, 160951, 76898, 1445, 16384⟩
    (by decide) selected_cut_05180

theorem selected_cut_05181 : selected 8 ⟨160955, by decide⟩
    (prefixPartial 13 76899) = some ⟨13, 2, 0, 160955, 76899, 909, 16384⟩ := by
  decide +kernel

theorem context_13_76899_160955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76899 ⟨160955, by decide⟩ :=
  accepted_of_selected 13 76899 ⟨160955, by decide⟩ ⟨13, 2, 0, 160955, 76899, 909, 16384⟩
    (by decide) selected_cut_05181

theorem unmarked_context_12_19224_160956 : frontier 9 ⟨160956, by decide⟩
    (prefixCache 12 19224) (prefixPartial 12 19224) = false := by
  decide +kernel

theorem node_context_12_19224_160956 : EJMOriginalGlobalDAGData.nodes 9 ⟨160956, by decide⟩ =
    .split (coordinate 12) (![⟨160891, by decide⟩,⟨160929, by decide⟩,⟨160951, by decide⟩,⟨160955, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_19224_160956 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19224 ⟨160956, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 19224
    ⟨160956, by decide⟩ (by decide) (![⟨160891, by decide⟩,⟨160929, by decide⟩,⟨160951, by decide⟩,⟨160955, by decide⟩]) unmarked_context_12_19224_160956 node_context_12_19224_160956
  intro a
  fin_cases a
  · exact context_13_76896_160891
  · exact context_13_76897_160929
  · exact context_13_76898_160951
  · exact context_13_76899_160955

theorem selected_cut_05182 : selected 8 ⟨160991, by decide⟩
    (prefixPartial 13 76900) = some ⟨13, 2, 0, 160991, 76900, 1949, 16384⟩ := by
  decide +kernel

theorem context_13_76900_160991 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76900 ⟨160991, by decide⟩ :=
  accepted_of_selected 13 76900 ⟨160991, by decide⟩ ⟨13, 2, 0, 160991, 76900, 1949, 16384⟩
    (by decide) selected_cut_05182

theorem selected_cut_05183 : selected 8 ⟨161030, by decide⟩
    (prefixPartial 13 76901) = some ⟨13, 2, 0, 161030, 76901, 2841, 16384⟩ := by
  decide +kernel

theorem context_13_76901_161030 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76901 ⟨161030, by decide⟩ :=
  accepted_of_selected 13 76901 ⟨161030, by decide⟩ ⟨13, 2, 0, 161030, 76901, 2841, 16384⟩
    (by decide) selected_cut_05183

theorem selected_cut_05184 : selected 8 ⟨161057, by decide⟩
    (prefixPartial 13 76902) = some ⟨13, 2, 0, 161057, 76902, 1573, 16384⟩ := by
  decide +kernel

theorem context_13_76902_161057 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76902 ⟨161057, by decide⟩ :=
  accepted_of_selected 13 76902 ⟨161057, by decide⟩ ⟨13, 2, 0, 161057, 76902, 1573, 16384⟩
    (by decide) selected_cut_05184

theorem selected_cut_05185 : selected 8 ⟨161063, by decide⟩
    (prefixPartial 13 76903) = some ⟨13, 2, 0, 161063, 76903, 829, 16384⟩ := by
  decide +kernel

theorem context_13_76903_161063 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76903 ⟨161063, by decide⟩ :=
  accepted_of_selected 13 76903 ⟨161063, by decide⟩ ⟨13, 2, 0, 161063, 76903, 829, 16384⟩
    (by decide) selected_cut_05185

theorem unmarked_context_12_19225_161064 : frontier 9 ⟨161064, by decide⟩
    (prefixCache 12 19225) (prefixPartial 12 19225) = false := by
  decide +kernel

theorem node_context_12_19225_161064 : EJMOriginalGlobalDAGData.nodes 9 ⟨161064, by decide⟩ =
    .split (coordinate 12) (![⟨160991, by decide⟩,⟨161030, by decide⟩,⟨161057, by decide⟩,⟨161063, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_19225_161064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19225 ⟨161064, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 19225
    ⟨161064, by decide⟩ (by decide) (![⟨160991, by decide⟩,⟨161030, by decide⟩,⟨161057, by decide⟩,⟨161063, by decide⟩]) unmarked_context_12_19225_161064 node_context_12_19225_161064
  intro a
  fin_cases a
  · exact context_13_76900_160991
  · exact context_13_76901_161030
  · exact context_13_76902_161057
  · exact context_13_76903_161063

theorem selected_cut_05186 : selected 8 ⟨161087, by decide⟩
    (prefixPartial 13 76904) = some ⟨13, 2, 0, 161087, 76904, 1681, 16384⟩ := by
  decide +kernel

theorem context_13_76904_161087 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76904 ⟨161087, by decide⟩ :=
  accepted_of_selected 13 76904 ⟨161087, by decide⟩ ⟨13, 2, 0, 161087, 76904, 1681, 16384⟩
    (by decide) selected_cut_05186

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
