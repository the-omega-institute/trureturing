/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover542
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_52131 : selected 10 ⟨1514012, by decide⟩
    (prefixPartial 11 287436) = some ⟨11, 2, 0, 1514012, 287436, 2689, 262144⟩ := by
  decide +kernel

theorem context_11_287436_1514012 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287436 ⟨1514012, by decide⟩ :=
  accepted_of_selected 11 287436 ⟨1514012, by decide⟩ ⟨11, 2, 0, 1514012, 287436, 2689, 262144⟩
    (by decide) selected_cut_52131

theorem selected_cut_52132 : selected 10 ⟨1514049, by decide⟩
    (prefixPartial 11 287437) = some ⟨11, 2, 0, 1514049, 287437, 2061, 262144⟩ := by
  decide +kernel

theorem context_11_287437_1514049 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287437 ⟨1514049, by decide⟩ :=
  accepted_of_selected 11 287437 ⟨1514049, by decide⟩ ⟨11, 2, 0, 1514049, 287437, 2061, 262144⟩
    (by decide) selected_cut_52132

theorem selected_cut_52133 : selected 10 ⟨1514074, by decide⟩
    (prefixPartial 11 287438) = some ⟨11, 2, 0, 1514074, 287438, 1089, 262144⟩ := by
  decide +kernel

theorem context_11_287438_1514074 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287438 ⟨1514074, by decide⟩ :=
  accepted_of_selected 11 287438 ⟨1514074, by decide⟩ ⟨11, 2, 0, 1514074, 287438, 1089, 262144⟩
    (by decide) selected_cut_52133

theorem selected_cut_52134 : selected 10 ⟨1470044, by decide⟩
    (prefixPartial 11 287439) = some ⟨11, 1, 0, 1470044, 287439, 1, 262144⟩ := by
  decide +kernel

theorem context_11_287439_1470044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287439 ⟨1470044, by decide⟩ :=
  accepted_of_selected 11 287439 ⟨1470044, by decide⟩ ⟨11, 1, 0, 1470044, 287439, 1, 262144⟩
    (by decide) selected_cut_52134

theorem unmarked_context_10_71859_1514075 : frontier 11 ⟨1514075, by decide⟩
    (prefixCache 10 71859) (prefixPartial 10 71859) = false := by
  decide +kernel

theorem node_context_10_71859_1514075 : EJMOriginalGlobalDAGData.nodes 11 ⟨1514075, by decide⟩ =
    .split (coordinate 10) (![⟨1514012, by decide⟩,⟨1514049, by decide⟩,⟨1514074, by decide⟩,⟨1470044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71859_1514075 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71859 ⟨1514075, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71859
    ⟨1514075, by decide⟩ (by decide) (![⟨1514012, by decide⟩,⟨1514049, by decide⟩,⟨1514074, by decide⟩,⟨1470044, by decide⟩]) unmarked_context_10_71859_1514075 node_context_10_71859_1514075
  intro a
  fin_cases a
  · exact context_11_287436_1514012
  · exact context_11_287437_1514049
  · exact context_11_287438_1514074
  · exact context_11_287439_1470044

theorem unmarked_context_9_17964_1514076 : frontier 12 ⟨1514076, by decide⟩
    (prefixCache 9 17964) (prefixPartial 9 17964) = false := by
  decide +kernel

theorem node_context_9_17964_1514076 : EJMOriginalGlobalDAGData.nodes 12 ⟨1514076, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1513878, by decide⟩,⟨1513932, by decide⟩,⟨1514075, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17964_1514076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17964 ⟨1514076, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17964
    ⟨1514076, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1513878, by decide⟩,⟨1513932, by decide⟩,⟨1514075, by decide⟩]) unmarked_context_9_17964_1514076 node_context_9_17964_1514076
  intro a
  fin_cases a
  · exact context_10_71856_1468246
  · exact context_10_71857_1513878
  · exact context_10_71858_1513932
  · exact context_10_71859_1514075

theorem selected_cut_52135 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 287440) = some ⟨11, 1, 0, 434745, 287440, 1, 262144⟩ := by
  decide +kernel

theorem context_11_287440_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287440 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 287440 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 287440, 1, 262144⟩
    (by decide) selected_cut_52135

theorem selected_cut_52136 : selected 10 ⟨1514127, by decide⟩
    (prefixPartial 11 287441) = some ⟨11, 2, 0, 1514127, 287441, 1769, 262144⟩ := by
  decide +kernel

theorem context_11_287441_1514127 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287441 ⟨1514127, by decide⟩ :=
  accepted_of_selected 11 287441 ⟨1514127, by decide⟩ ⟨11, 2, 0, 1514127, 287441, 1769, 262144⟩
    (by decide) selected_cut_52136

theorem selected_cut_52137 : selected 10 ⟨1514160, by decide⟩
    (prefixPartial 11 287442) = some ⟨11, 2, 0, 1514160, 287442, 1525, 262144⟩ := by
  decide +kernel

theorem context_11_287442_1514160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287442 ⟨1514160, by decide⟩ :=
  accepted_of_selected 11 287442 ⟨1514160, by decide⟩ ⟨11, 2, 0, 1514160, 287442, 1525, 262144⟩
    (by decide) selected_cut_52137

theorem selected_cut_52138 : selected 10 ⟨1514192, by decide⟩
    (prefixPartial 11 287443) = some ⟨11, 2, 0, 1514192, 287443, 1629, 262144⟩ := by
  decide +kernel

theorem context_11_287443_1514192 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287443 ⟨1514192, by decide⟩ :=
  accepted_of_selected 11 287443 ⟨1514192, by decide⟩ ⟨11, 2, 0, 1514192, 287443, 1629, 262144⟩
    (by decide) selected_cut_52138

theorem unmarked_context_10_71860_1514193 : frontier 11 ⟨1514193, by decide⟩
    (prefixCache 10 71860) (prefixPartial 10 71860) = false := by
  decide +kernel

theorem node_context_10_71860_1514193 : EJMOriginalGlobalDAGData.nodes 11 ⟨1514193, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨1514127, by decide⟩,⟨1514160, by decide⟩,⟨1514192, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71860_1514193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71860 ⟨1514193, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71860
    ⟨1514193, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨1514127, by decide⟩,⟨1514160, by decide⟩,⟨1514192, by decide⟩]) unmarked_context_10_71860_1514193 node_context_10_71860_1514193
  intro a
  fin_cases a
  · exact context_11_287440_434745
  · exact context_11_287441_1514127
  · exact context_11_287442_1514160
  · exact context_11_287443_1514192

theorem selected_cut_52139 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 71861) = some ⟨10, 1, 0, 1468874, 71861, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_71861_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71861 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 71861 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 71861, 1, 1048576⟩
    (by decide) selected_cut_52139

theorem selected_cut_52140 : selected 11 ⟨1514285, by decide⟩
    (prefixPartial 10 71862) = some ⟨10, 2, 0, 1514285, 71862, 3857, 1048576⟩ := by
  decide +kernel

theorem context_10_71862_1514285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71862 ⟨1514285, by decide⟩ :=
  accepted_of_selected 10 71862 ⟨1514285, by decide⟩ ⟨10, 2, 0, 1514285, 71862, 3857, 1048576⟩
    (by decide) selected_cut_52140

theorem selected_cut_52141 : selected 11 ⟨1514374, by decide⟩
    (prefixPartial 10 71863) = some ⟨10, 2, 0, 1514374, 71863, 3269, 1048576⟩ := by
  decide +kernel

theorem context_10_71863_1514374 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71863 ⟨1514374, by decide⟩ :=
  accepted_of_selected 10 71863 ⟨1514374, by decide⟩ ⟨10, 2, 0, 1514374, 71863, 3269, 1048576⟩
    (by decide) selected_cut_52141

theorem unmarked_context_9_17965_1514375 : frontier 12 ⟨1514375, by decide⟩
    (prefixCache 9 17965) (prefixPartial 9 17965) = false := by
  decide +kernel

theorem node_context_9_17965_1514375 : EJMOriginalGlobalDAGData.nodes 12 ⟨1514375, by decide⟩ =
    .split (coordinate 9) (![⟨1514193, by decide⟩,⟨1468874, by decide⟩,⟨1514285, by decide⟩,⟨1514374, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17965_1514375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17965 ⟨1514375, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17965
    ⟨1514375, by decide⟩ (by decide) (![⟨1514193, by decide⟩,⟨1468874, by decide⟩,⟨1514285, by decide⟩,⟨1514374, by decide⟩]) unmarked_context_9_17965_1514375 node_context_9_17965_1514375
  intro a
  fin_cases a
  · exact context_10_71860_1514193
  · exact context_10_71861_1468874
  · exact context_10_71862_1514285
  · exact context_10_71863_1514374

theorem selected_cut_52142 : selected 11 ⟨1514401, by decide⟩
    (prefixPartial 10 71864) = some ⟨10, 2, 0, 1514401, 71864, 961, 1048576⟩ := by
  decide +kernel

theorem context_10_71864_1514401 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71864 ⟨1514401, by decide⟩ :=
  accepted_of_selected 10 71864 ⟨1514401, by decide⟩ ⟨10, 2, 0, 1514401, 71864, 961, 1048576⟩
    (by decide) selected_cut_52142

theorem selected_cut_52143 : selected 11 ⟨1514494, by decide⟩
    (prefixPartial 10 71865) = some ⟨10, 2, 0, 1514494, 71865, 2897, 1048576⟩ := by
  decide +kernel

theorem context_10_71865_1514494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71865 ⟨1514494, by decide⟩ :=
  accepted_of_selected 10 71865 ⟨1514494, by decide⟩ ⟨10, 2, 0, 1514494, 71865, 2897, 1048576⟩
    (by decide) selected_cut_52143

theorem selected_cut_52144 : selected 11 ⟨1469103, by decide⟩
    (prefixPartial 10 71866) = some ⟨10, 1, 0, 1469103, 71866, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_71866_1469103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71866 ⟨1469103, by decide⟩ :=
  accepted_of_selected 10 71866 ⟨1469103, by decide⟩ ⟨10, 1, 0, 1469103, 71866, 1, 1048576⟩
    (by decide) selected_cut_52144

theorem selected_cut_52145 : selected 11 ⟨1514534, by decide⟩
    (prefixPartial 10 71867) = some ⟨10, 2, 0, 1514534, 71867, 1641, 1048576⟩ := by
  decide +kernel

theorem context_10_71867_1514534 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71867 ⟨1514534, by decide⟩ :=
  accepted_of_selected 10 71867 ⟨1514534, by decide⟩ ⟨10, 2, 0, 1514534, 71867, 1641, 1048576⟩
    (by decide) selected_cut_52145

theorem unmarked_context_9_17966_1514535 : frontier 12 ⟨1514535, by decide⟩
    (prefixCache 9 17966) (prefixPartial 9 17966) = false := by
  decide +kernel

theorem node_context_9_17966_1514535 : EJMOriginalGlobalDAGData.nodes 12 ⟨1514535, by decide⟩ =
    .split (coordinate 9) (![⟨1514401, by decide⟩,⟨1514494, by decide⟩,⟨1469103, by decide⟩,⟨1514534, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17966_1514535 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17966 ⟨1514535, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17966
    ⟨1514535, by decide⟩ (by decide) (![⟨1514401, by decide⟩,⟨1514494, by decide⟩,⟨1469103, by decide⟩,⟨1514534, by decide⟩]) unmarked_context_9_17966_1514535 node_context_9_17966_1514535
  intro a
  fin_cases a
  · exact context_10_71864_1514401
  · exact context_10_71865_1514494
  · exact context_10_71866_1469103
  · exact context_10_71867_1514534

theorem selected_cut_52146 : selected 12 ⟨1514615, by decide⟩
    (prefixPartial 9 17967) = some ⟨9, 2, 0, 1514615, 17967, 2113, 4194304⟩ := by
  decide +kernel

theorem context_9_17967_1514615 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17967 ⟨1514615, by decide⟩ :=
  accepted_of_selected 9 17967 ⟨1514615, by decide⟩ ⟨9, 2, 0, 1514615, 17967, 2113, 4194304⟩
    (by decide) selected_cut_52146

theorem unmarked_context_8_4491_1514616 : frontier 13 ⟨1514616, by decide⟩
    (prefixCache 8 4491) (prefixPartial 8 4491) = false := by
  decide +kernel

theorem node_context_8_4491_1514616 : EJMOriginalGlobalDAGData.nodes 13 ⟨1514616, by decide⟩ =
    .split (coordinate 8) (![⟨1514076, by decide⟩,⟨1514375, by decide⟩,⟨1514535, by decide⟩,⟨1514615, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4491_1514616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4491 ⟨1514616, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4491
    ⟨1514616, by decide⟩ (by decide) (![⟨1514076, by decide⟩,⟨1514375, by decide⟩,⟨1514535, by decide⟩,⟨1514615, by decide⟩]) unmarked_context_8_4491_1514616 node_context_8_4491_1514616
  intro a
  fin_cases a
  · exact context_9_17964_1514076
  · exact context_9_17965_1514375
  · exact context_9_17966_1514535
  · exact context_9_17967_1514615

theorem unmarked_context_7_1122_1514617 : frontier 14 ⟨1514617, by decide⟩
    (prefixCache 7 1122) (prefixPartial 7 1122) = false := by
  decide +kernel

theorem node_context_7_1122_1514617 : EJMOriginalGlobalDAGData.nodes 14 ⟨1514617, by decide⟩ =
    .split (coordinate 7) (![⟨1511436, by decide⟩,⟨1512363, by decide⟩,⟨1513480, by decide⟩,⟨1514616, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_1122_1514617 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 1122 ⟨1514617, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 1122
    ⟨1514617, by decide⟩ (by decide) (![⟨1511436, by decide⟩,⟨1512363, by decide⟩,⟨1513480, by decide⟩,⟨1514616, by decide⟩]) unmarked_context_7_1122_1514617 node_context_7_1122_1514617
  intro a
  fin_cases a
  · exact context_8_4488_1511436
  · exact context_8_4489_1512363
  · exact context_8_4490_1513480
  · exact context_8_4491_1514616

theorem selected_cut_52147 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 71872) = some ⟨10, 1, 0, 1468246, 71872, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_71872_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71872 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 71872 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 71872, 1, 1048576⟩
    (by decide) selected_cut_52147

theorem selected_cut_52148 : selected 10 ⟨1514790, by decide⟩
    (prefixPartial 11 287492) = some ⟨11, 2, 0, 1514790, 287492, 2585, 262144⟩ := by
  decide +kernel

theorem context_11_287492_1514790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287492 ⟨1514790, by decide⟩ :=
  accepted_of_selected 11 287492 ⟨1514790, by decide⟩ ⟨11, 2, 0, 1514790, 287492, 2585, 262144⟩
    (by decide) selected_cut_52148

theorem selected_cut_52149 : selected 10 ⟨1468419, by decide⟩
    (prefixPartial 11 287493) = some ⟨11, 1, 0, 1468419, 287493, 1, 262144⟩ := by
  decide +kernel

theorem context_11_287493_1468419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287493 ⟨1468419, by decide⟩ :=
  accepted_of_selected 11 287493 ⟨1468419, by decide⟩ ⟨11, 1, 0, 1468419, 287493, 1, 262144⟩
    (by decide) selected_cut_52149

theorem selected_cut_52150 : selected 10 ⟨1514879, by decide⟩
    (prefixPartial 11 287494) = some ⟨11, 2, 0, 1514879, 287494, 2713, 262144⟩ := by
  decide +kernel

theorem context_11_287494_1514879 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287494 ⟨1514879, by decide⟩ :=
  accepted_of_selected 11 287494 ⟨1514879, by decide⟩ ⟨11, 2, 0, 1514879, 287494, 2713, 262144⟩
    (by decide) selected_cut_52150

theorem selected_cut_52151 : selected 10 ⟨1514966, by decide⟩
    (prefixPartial 11 287495) = some ⟨11, 2, 0, 1514966, 287495, 2381, 262144⟩ := by
  decide +kernel

theorem context_11_287495_1514966 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287495 ⟨1514966, by decide⟩ :=
  accepted_of_selected 11 287495 ⟨1514966, by decide⟩ ⟨11, 2, 0, 1514966, 287495, 2381, 262144⟩
    (by decide) selected_cut_52151

theorem unmarked_context_10_71873_1514967 : frontier 11 ⟨1514967, by decide⟩
    (prefixCache 10 71873) (prefixPartial 10 71873) = false := by
  decide +kernel

theorem node_context_10_71873_1514967 : EJMOriginalGlobalDAGData.nodes 11 ⟨1514967, by decide⟩ =
    .split (coordinate 10) (![⟨1514790, by decide⟩,⟨1468419, by decide⟩,⟨1514879, by decide⟩,⟨1514966, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71873_1514967 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71873 ⟨1514967, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71873
    ⟨1514967, by decide⟩ (by decide) (![⟨1514790, by decide⟩,⟨1468419, by decide⟩,⟨1514879, by decide⟩,⟨1514966, by decide⟩]) unmarked_context_10_71873_1514967 node_context_10_71873_1514967
  intro a
  fin_cases a
  · exact context_11_287492_1514790
  · exact context_11_287493_1468419
  · exact context_11_287494_1514879
  · exact context_11_287495_1514966

theorem selected_cut_52152 : selected 11 ⟨1515081, by decide⟩
    (prefixPartial 10 71874) = some ⟨10, 2, 0, 1515081, 71874, 2673, 1048576⟩ := by
  decide +kernel

theorem context_10_71874_1515081 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71874 ⟨1515081, by decide⟩ :=
  accepted_of_selected 10 71874 ⟨1515081, by decide⟩ ⟨10, 2, 0, 1515081, 71874, 2673, 1048576⟩
    (by decide) selected_cut_52152

theorem selected_cut_52153 : selected 11 ⟨1515172, by decide⟩
    (prefixPartial 10 71875) = some ⟨10, 2, 0, 1515172, 71875, 3165, 1048576⟩ := by
  decide +kernel

theorem context_10_71875_1515172 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71875 ⟨1515172, by decide⟩ :=
  accepted_of_selected 10 71875 ⟨1515172, by decide⟩ ⟨10, 2, 0, 1515172, 71875, 3165, 1048576⟩
    (by decide) selected_cut_52153

theorem unmarked_context_9_17968_1515173 : frontier 12 ⟨1515173, by decide⟩
    (prefixCache 9 17968) (prefixPartial 9 17968) = false := by
  decide +kernel

theorem node_context_9_17968_1515173 : EJMOriginalGlobalDAGData.nodes 12 ⟨1515173, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1514967, by decide⟩,⟨1515081, by decide⟩,⟨1515172, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17968_1515173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17968 ⟨1515173, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17968
    ⟨1515173, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1514967, by decide⟩,⟨1515081, by decide⟩,⟨1515172, by decide⟩]) unmarked_context_9_17968_1515173 node_context_9_17968_1515173
  intro a
  fin_cases a
  · exact context_10_71872_1468246
  · exact context_10_71873_1514967
  · exact context_10_71874_1515081
  · exact context_10_71875_1515172

theorem selected_cut_52154 : selected 11 ⟨1515314, by decide⟩
    (prefixPartial 10 71876) = some ⟨10, 2, 0, 1515314, 71876, 2513, 1048576⟩ := by
  decide +kernel

theorem context_10_71876_1515314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71876 ⟨1515314, by decide⟩ :=
  accepted_of_selected 10 71876 ⟨1515314, by decide⟩ ⟨10, 2, 0, 1515314, 71876, 2513, 1048576⟩
    (by decide) selected_cut_52154

theorem selected_cut_52155 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 71877) = some ⟨10, 1, 0, 1468874, 71877, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_71877_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71877 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 71877 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 71877, 1, 1048576⟩
    (by decide) selected_cut_52155

theorem selected_cut_52156 : selected 11 ⟨1515404, by decide⟩
    (prefixPartial 10 71878) = some ⟨10, 2, 0, 1515404, 71878, 1213, 1048576⟩ := by
  decide +kernel

theorem context_10_71878_1515404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71878 ⟨1515404, by decide⟩ :=
  accepted_of_selected 10 71878 ⟨1515404, by decide⟩ ⟨10, 2, 0, 1515404, 71878, 1213, 1048576⟩
    (by decide) selected_cut_52156

theorem selected_cut_52157 : selected 11 ⟨1515444, by decide⟩
    (prefixPartial 10 71879) = some ⟨10, 2, 0, 1515444, 71879, 849, 1048576⟩ := by
  decide +kernel

theorem context_10_71879_1515444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71879 ⟨1515444, by decide⟩ :=
  accepted_of_selected 10 71879 ⟨1515444, by decide⟩ ⟨10, 2, 0, 1515444, 71879, 849, 1048576⟩
    (by decide) selected_cut_52157

theorem unmarked_context_9_17969_1515445 : frontier 12 ⟨1515445, by decide⟩
    (prefixCache 9 17969) (prefixPartial 9 17969) = false := by
  decide +kernel

theorem node_context_9_17969_1515445 : EJMOriginalGlobalDAGData.nodes 12 ⟨1515445, by decide⟩ =
    .split (coordinate 9) (![⟨1515314, by decide⟩,⟨1468874, by decide⟩,⟨1515404, by decide⟩,⟨1515444, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17969_1515445 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17969 ⟨1515445, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17969
    ⟨1515445, by decide⟩ (by decide) (![⟨1515314, by decide⟩,⟨1468874, by decide⟩,⟨1515404, by decide⟩,⟨1515444, by decide⟩]) unmarked_context_9_17969_1515445 node_context_9_17969_1515445
  intro a
  fin_cases a
  · exact context_10_71876_1515314
  · exact context_10_71877_1468874
  · exact context_10_71878_1515404
  · exact context_10_71879_1515444

theorem selected_cut_52158 : selected 12 ⟨1515538, by decide⟩
    (prefixPartial 9 17970) = some ⟨9, 2, 0, 1515538, 17970, 1157, 4194304⟩ := by
  decide +kernel

theorem context_9_17970_1515538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17970 ⟨1515538, by decide⟩ :=
  accepted_of_selected 9 17970 ⟨1515538, by decide⟩ ⟨9, 2, 0, 1515538, 17970, 1157, 4194304⟩
    (by decide) selected_cut_52158

theorem selected_cut_52159 : selected 12 ⟨1515556, by decide⟩
    (prefixPartial 9 17971) = some ⟨9, 2, 0, 1515556, 17971, 161, 4194304⟩ := by
  decide +kernel

theorem context_9_17971_1515556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17971 ⟨1515556, by decide⟩ :=
  accepted_of_selected 9 17971 ⟨1515556, by decide⟩ ⟨9, 2, 0, 1515556, 17971, 161, 4194304⟩
    (by decide) selected_cut_52159

theorem unmarked_context_8_4492_1515557 : frontier 13 ⟨1515557, by decide⟩
    (prefixCache 8 4492) (prefixPartial 8 4492) = false := by
  decide +kernel

theorem node_context_8_4492_1515557 : EJMOriginalGlobalDAGData.nodes 13 ⟨1515557, by decide⟩ =
    .split (coordinate 8) (![⟨1515173, by decide⟩,⟨1515445, by decide⟩,⟨1515538, by decide⟩,⟨1515556, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4492_1515557 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4492 ⟨1515557, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4492
    ⟨1515557, by decide⟩ (by decide) (![⟨1515173, by decide⟩,⟨1515445, by decide⟩,⟨1515538, by decide⟩,⟨1515556, by decide⟩]) unmarked_context_8_4492_1515557 node_context_8_4492_1515557
  intro a
  fin_cases a
  · exact context_9_17968_1515173
  · exact context_9_17969_1515445
  · exact context_9_17970_1515538
  · exact context_9_17971_1515556

theorem selected_cut_52160 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 71888) = some ⟨10, 1, 0, 1468246, 71888, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_71888_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71888 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 71888 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 71888, 1, 1048576⟩
    (by decide) selected_cut_52160

theorem selected_cut_52161 : selected 10 ⟨1515678, by decide⟩
    (prefixPartial 11 287556) = some ⟨11, 2, 0, 1515678, 287556, 3549, 262144⟩ := by
  decide +kernel

theorem context_11_287556_1515678 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287556 ⟨1515678, by decide⟩ :=
  accepted_of_selected 11 287556 ⟨1515678, by decide⟩ ⟨11, 2, 0, 1515678, 287556, 3549, 262144⟩
    (by decide) selected_cut_52161

theorem selected_cut_52162 : selected 10 ⟨1468419, by decide⟩
    (prefixPartial 11 287557) = some ⟨11, 1, 0, 1468419, 287557, 1, 262144⟩ := by
  decide +kernel

theorem context_11_287557_1468419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287557 ⟨1468419, by decide⟩ :=
  accepted_of_selected 11 287557 ⟨1468419, by decide⟩ ⟨11, 1, 0, 1468419, 287557, 1, 262144⟩
    (by decide) selected_cut_52162

theorem selected_cut_52163 : selected 10 ⟨1515751, by decide⟩
    (prefixPartial 11 287558) = some ⟨11, 2, 0, 1515751, 287558, 2681, 262144⟩ := by
  decide +kernel

theorem context_11_287558_1515751 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287558 ⟨1515751, by decide⟩ :=
  accepted_of_selected 11 287558 ⟨1515751, by decide⟩ ⟨11, 2, 0, 1515751, 287558, 2681, 262144⟩
    (by decide) selected_cut_52163

theorem selected_cut_52164 : selected 10 ⟨1515793, by decide⟩
    (prefixPartial 11 287559) = some ⟨11, 2, 0, 1515793, 287559, 1237, 262144⟩ := by
  decide +kernel

theorem context_11_287559_1515793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287559 ⟨1515793, by decide⟩ :=
  accepted_of_selected 11 287559 ⟨1515793, by decide⟩ ⟨11, 2, 0, 1515793, 287559, 1237, 262144⟩
    (by decide) selected_cut_52164

theorem unmarked_context_10_71889_1515794 : frontier 11 ⟨1515794, by decide⟩
    (prefixCache 10 71889) (prefixPartial 10 71889) = false := by
  decide +kernel

theorem node_context_10_71889_1515794 : EJMOriginalGlobalDAGData.nodes 11 ⟨1515794, by decide⟩ =
    .split (coordinate 10) (![⟨1515678, by decide⟩,⟨1468419, by decide⟩,⟨1515751, by decide⟩,⟨1515793, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71889_1515794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71889 ⟨1515794, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71889
    ⟨1515794, by decide⟩ (by decide) (![⟨1515678, by decide⟩,⟨1468419, by decide⟩,⟨1515751, by decide⟩,⟨1515793, by decide⟩]) unmarked_context_10_71889_1515794 node_context_10_71889_1515794
  intro a
  fin_cases a
  · exact context_11_287556_1515678
  · exact context_11_287557_1468419
  · exact context_11_287558_1515751
  · exact context_11_287559_1515793

theorem selected_cut_52165 : selected 11 ⟨1515912, by decide⟩
    (prefixPartial 10 71890) = some ⟨10, 2, 0, 1515912, 71890, 3385, 1048576⟩ := by
  decide +kernel

theorem context_10_71890_1515912 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71890 ⟨1515912, by decide⟩ :=
  accepted_of_selected 10 71890 ⟨1515912, by decide⟩ ⟨10, 2, 0, 1515912, 71890, 3385, 1048576⟩
    (by decide) selected_cut_52165

theorem selected_cut_52166 : selected 11 ⟨1515990, by decide⟩
    (prefixPartial 10 71891) = some ⟨10, 2, 0, 1515990, 71891, 1969, 1048576⟩ := by
  decide +kernel

theorem context_10_71891_1515990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71891 ⟨1515990, by decide⟩ :=
  accepted_of_selected 10 71891 ⟨1515990, by decide⟩ ⟨10, 2, 0, 1515990, 71891, 1969, 1048576⟩
    (by decide) selected_cut_52166

theorem unmarked_context_9_17972_1515991 : frontier 12 ⟨1515991, by decide⟩
    (prefixCache 9 17972) (prefixPartial 9 17972) = false := by
  decide +kernel

theorem node_context_9_17972_1515991 : EJMOriginalGlobalDAGData.nodes 12 ⟨1515991, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1515794, by decide⟩,⟨1515912, by decide⟩,⟨1515990, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17972_1515991 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17972 ⟨1515991, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17972
    ⟨1515991, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1515794, by decide⟩,⟨1515912, by decide⟩,⟨1515990, by decide⟩]) unmarked_context_9_17972_1515991 node_context_9_17972_1515991
  intro a
  fin_cases a
  · exact context_10_71888_1468246
  · exact context_10_71889_1515794
  · exact context_10_71890_1515912
  · exact context_10_71891_1515990

theorem selected_cut_52167 : selected 11 ⟨1516180, by decide⟩
    (prefixPartial 10 71892) = some ⟨10, 2, 0, 1516180, 71892, 3853, 1048576⟩ := by
  decide +kernel

theorem context_10_71892_1516180 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71892 ⟨1516180, by decide⟩ :=
  accepted_of_selected 10 71892 ⟨1516180, by decide⟩ ⟨10, 2, 0, 1516180, 71892, 3853, 1048576⟩
    (by decide) selected_cut_52167

theorem selected_cut_52168 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 71893) = some ⟨10, 1, 0, 1468874, 71893, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_71893_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71893 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 71893 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 71893, 1, 1048576⟩
    (by decide) selected_cut_52168

theorem selected_cut_52169 : selected 11 ⟨1516319, by decide⟩
    (prefixPartial 10 71894) = some ⟨10, 2, 0, 1516319, 71894, 2833, 1048576⟩ := by
  decide +kernel

theorem context_10_71894_1516319 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71894 ⟨1516319, by decide⟩ :=
  accepted_of_selected 10 71894 ⟨1516319, by decide⟩ ⟨10, 2, 0, 1516319, 71894, 2833, 1048576⟩
    (by decide) selected_cut_52169

theorem selected_cut_52170 : selected 11 ⟨1516366, by decide⟩
    (prefixPartial 10 71895) = some ⟨10, 2, 0, 1516366, 71895, 1025, 1048576⟩ := by
  decide +kernel

theorem context_10_71895_1516366 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71895 ⟨1516366, by decide⟩ :=
  accepted_of_selected 10 71895 ⟨1516366, by decide⟩ ⟨10, 2, 0, 1516366, 71895, 1025, 1048576⟩
    (by decide) selected_cut_52170

theorem unmarked_context_9_17973_1516367 : frontier 12 ⟨1516367, by decide⟩
    (prefixCache 9 17973) (prefixPartial 9 17973) = false := by
  decide +kernel

theorem node_context_9_17973_1516367 : EJMOriginalGlobalDAGData.nodes 12 ⟨1516367, by decide⟩ =
    .split (coordinate 9) (![⟨1516180, by decide⟩,⟨1468874, by decide⟩,⟨1516319, by decide⟩,⟨1516366, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17973_1516367 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17973 ⟨1516367, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17973
    ⟨1516367, by decide⟩ (by decide) (![⟨1516180, by decide⟩,⟨1468874, by decide⟩,⟨1516319, by decide⟩,⟨1516366, by decide⟩]) unmarked_context_9_17973_1516367 node_context_9_17973_1516367
  intro a
  fin_cases a
  · exact context_10_71892_1516180
  · exact context_10_71893_1468874
  · exact context_10_71894_1516319
  · exact context_10_71895_1516366

theorem selected_cut_52171 : selected 12 ⟨1516436, by decide⟩
    (prefixPartial 9 17974) = some ⟨9, 2, 0, 1516436, 17974, 957, 4194304⟩ := by
  decide +kernel

theorem context_9_17974_1516436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17974 ⟨1516436, by decide⟩ :=
  accepted_of_selected 9 17974 ⟨1516436, by decide⟩ ⟨9, 2, 0, 1516436, 17974, 957, 4194304⟩
    (by decide) selected_cut_52171

theorem selected_cut_52172 : selected 12 ⟨1516438, by decide⟩
    (prefixPartial 9 17975) = some ⟨9, 2, 0, 1516438, 17975, 49, 4194304⟩ := by
  decide +kernel

theorem context_9_17975_1516438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17975 ⟨1516438, by decide⟩ :=
  accepted_of_selected 9 17975 ⟨1516438, by decide⟩ ⟨9, 2, 0, 1516438, 17975, 49, 4194304⟩
    (by decide) selected_cut_52172

theorem unmarked_context_8_4493_1516439 : frontier 13 ⟨1516439, by decide⟩
    (prefixCache 8 4493) (prefixPartial 8 4493) = false := by
  decide +kernel

theorem node_context_8_4493_1516439 : EJMOriginalGlobalDAGData.nodes 13 ⟨1516439, by decide⟩ =
    .split (coordinate 8) (![⟨1515991, by decide⟩,⟨1516367, by decide⟩,⟨1516436, by decide⟩,⟨1516438, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4493_1516439 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4493 ⟨1516439, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4493
    ⟨1516439, by decide⟩ (by decide) (![⟨1515991, by decide⟩,⟨1516367, by decide⟩,⟨1516436, by decide⟩,⟨1516438, by decide⟩]) unmarked_context_8_4493_1516439 node_context_8_4493_1516439
  intro a
  fin_cases a
  · exact context_9_17972_1515991
  · exact context_9_17973_1516367
  · exact context_9_17974_1516436
  · exact context_9_17975_1516438

theorem selected_cut_52173 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 71904) = some ⟨10, 1, 0, 1468246, 71904, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_71904_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71904 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 71904 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 71904, 1, 1048576⟩
    (by decide) selected_cut_52173

theorem selected_cut_52174 : selected 10 ⟨1516580, by decide⟩
    (prefixPartial 11 287620) = some ⟨11, 2, 0, 1516580, 287620, 3917, 262144⟩ := by
  decide +kernel

theorem context_11_287620_1516580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287620 ⟨1516580, by decide⟩ :=
  accepted_of_selected 11 287620 ⟨1516580, by decide⟩ ⟨11, 2, 0, 1516580, 287620, 3917, 262144⟩
    (by decide) selected_cut_52174

theorem selected_cut_52175 : selected 10 ⟨1468419, by decide⟩
    (prefixPartial 11 287621) = some ⟨11, 1, 0, 1468419, 287621, 1, 262144⟩ := by
  decide +kernel

theorem context_11_287621_1468419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287621 ⟨1468419, by decide⟩ :=
  accepted_of_selected 11 287621 ⟨1468419, by decide⟩ ⟨11, 1, 0, 1468419, 287621, 1, 262144⟩
    (by decide) selected_cut_52175

theorem selected_cut_52176 : selected 10 ⟨1516692, by decide⟩
    (prefixPartial 11 287622) = some ⟨11, 2, 0, 1516692, 287622, 3661, 262144⟩ := by
  decide +kernel

theorem context_11_287622_1516692 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287622 ⟨1516692, by decide⟩ :=
  accepted_of_selected 11 287622 ⟨1516692, by decide⟩ ⟨11, 2, 0, 1516692, 287622, 3661, 262144⟩
    (by decide) selected_cut_52176

theorem selected_cut_52177 : selected 10 ⟨1516795, by decide⟩
    (prefixPartial 11 287623) = some ⟨11, 2, 0, 1516795, 287623, 3249, 262144⟩ := by
  decide +kernel

theorem context_11_287623_1516795 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287623 ⟨1516795, by decide⟩ :=
  accepted_of_selected 11 287623 ⟨1516795, by decide⟩ ⟨11, 2, 0, 1516795, 287623, 3249, 262144⟩
    (by decide) selected_cut_52177

theorem unmarked_context_10_71905_1516796 : frontier 11 ⟨1516796, by decide⟩
    (prefixCache 10 71905) (prefixPartial 10 71905) = false := by
  decide +kernel

theorem node_context_10_71905_1516796 : EJMOriginalGlobalDAGData.nodes 11 ⟨1516796, by decide⟩ =
    .split (coordinate 10) (![⟨1516580, by decide⟩,⟨1468419, by decide⟩,⟨1516692, by decide⟩,⟨1516795, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71905_1516796 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71905 ⟨1516796, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71905
    ⟨1516796, by decide⟩ (by decide) (![⟨1516580, by decide⟩,⟨1468419, by decide⟩,⟨1516692, by decide⟩,⟨1516795, by decide⟩]) unmarked_context_10_71905_1516796 node_context_10_71905_1516796
  intro a
  fin_cases a
  · exact context_11_287620_1516580
  · exact context_11_287621_1468419
  · exact context_11_287622_1516692
  · exact context_11_287623_1516795

theorem selected_cut_52178 : selected 10 ⟨1516867, by decide⟩
    (prefixPartial 11 287624) = some ⟨11, 2, 0, 1516867, 287624, 2777, 262144⟩ := by
  decide +kernel

theorem context_11_287624_1516867 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287624 ⟨1516867, by decide⟩ :=
  accepted_of_selected 11 287624 ⟨1516867, by decide⟩ ⟨11, 2, 0, 1516867, 287624, 2777, 262144⟩
    (by decide) selected_cut_52178

theorem selected_cut_52179 : selected 10 ⟨1516897, by decide⟩
    (prefixPartial 11 287625) = some ⟨11, 2, 0, 1516897, 287625, 1269, 262144⟩ := by
  decide +kernel

theorem context_11_287625_1516897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287625 ⟨1516897, by decide⟩ :=
  accepted_of_selected 11 287625 ⟨1516897, by decide⟩ ⟨11, 2, 0, 1516897, 287625, 1269, 262144⟩
    (by decide) selected_cut_52179

theorem selected_cut_52180 : selected 10 ⟨1468743, by decide⟩
    (prefixPartial 11 287626) = some ⟨11, 1, 0, 1468743, 287626, 1, 262144⟩ := by
  decide +kernel

theorem context_11_287626_1468743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287626 ⟨1468743, by decide⟩ :=
  accepted_of_selected 11 287626 ⟨1468743, by decide⟩ ⟨11, 1, 0, 1468743, 287626, 1, 262144⟩
    (by decide) selected_cut_52180

theorem selected_cut_52181 : selected 10 ⟨1516927, by decide⟩
    (prefixPartial 11 287627) = some ⟨11, 2, 0, 1516927, 287627, 1249, 262144⟩ := by
  decide +kernel

theorem context_11_287627_1516927 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287627 ⟨1516927, by decide⟩ :=
  accepted_of_selected 11 287627 ⟨1516927, by decide⟩ ⟨11, 2, 0, 1516927, 287627, 1249, 262144⟩
    (by decide) selected_cut_52181

theorem unmarked_context_10_71906_1516928 : frontier 11 ⟨1516928, by decide⟩
    (prefixCache 10 71906) (prefixPartial 10 71906) = false := by
  decide +kernel

theorem node_context_10_71906_1516928 : EJMOriginalGlobalDAGData.nodes 11 ⟨1516928, by decide⟩ =
    .split (coordinate 10) (![⟨1516867, by decide⟩,⟨1516897, by decide⟩,⟨1468743, by decide⟩,⟨1516927, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71906_1516928 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71906 ⟨1516928, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71906
    ⟨1516928, by decide⟩ (by decide) (![⟨1516867, by decide⟩,⟨1516897, by decide⟩,⟨1468743, by decide⟩,⟨1516927, by decide⟩]) unmarked_context_10_71906_1516928 node_context_10_71906_1516928
  intro a
  fin_cases a
  · exact context_11_287624_1516867
  · exact context_11_287625_1516897
  · exact context_11_287626_1468743
  · exact context_11_287627_1516927

theorem selected_cut_52182 : selected 11 ⟨1517006, by decide⟩
    (prefixPartial 10 71907) = some ⟨10, 2, 0, 1517006, 71907, 3325, 1048576⟩ := by
  decide +kernel

theorem context_10_71907_1517006 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71907 ⟨1517006, by decide⟩ :=
  accepted_of_selected 10 71907 ⟨1517006, by decide⟩ ⟨10, 2, 0, 1517006, 71907, 3325, 1048576⟩
    (by decide) selected_cut_52182

theorem unmarked_context_9_17976_1517007 : frontier 12 ⟨1517007, by decide⟩
    (prefixCache 9 17976) (prefixPartial 9 17976) = false := by
  decide +kernel

theorem node_context_9_17976_1517007 : EJMOriginalGlobalDAGData.nodes 12 ⟨1517007, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1516796, by decide⟩,⟨1516928, by decide⟩,⟨1517006, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17976_1517007 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17976 ⟨1517007, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17976
    ⟨1517007, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1516796, by decide⟩,⟨1516928, by decide⟩,⟨1517006, by decide⟩]) unmarked_context_9_17976_1517007 node_context_9_17976_1517007
  intro a
  fin_cases a
  · exact context_10_71904_1468246
  · exact context_10_71905_1516796
  · exact context_10_71906_1516928
  · exact context_10_71907_1517006

theorem selected_cut_52183 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 287632) = some ⟨11, 1, 0, 434745, 287632, 1, 262144⟩ := by
  decide +kernel

theorem context_11_287632_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287632 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 287632 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 287632, 1, 262144⟩
    (by decide) selected_cut_52183

theorem selected_cut_52184 : selected 10 ⟨1517065, by decide⟩
    (prefixPartial 11 287633) = some ⟨11, 2, 0, 1517065, 287633, 2005, 262144⟩ := by
  decide +kernel

theorem context_11_287633_1517065 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287633 ⟨1517065, by decide⟩ :=
  accepted_of_selected 11 287633 ⟨1517065, by decide⟩ ⟨11, 2, 0, 1517065, 287633, 2005, 262144⟩
    (by decide) selected_cut_52184

theorem selected_cut_52185 : selected 10 ⟨1517113, by decide⟩
    (prefixPartial 11 287634) = some ⟨11, 2, 0, 1517113, 287634, 2001, 262144⟩ := by
  decide +kernel

theorem context_11_287634_1517113 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287634 ⟨1517113, by decide⟩ :=
  accepted_of_selected 11 287634 ⟨1517113, by decide⟩ ⟨11, 2, 0, 1517113, 287634, 2001, 262144⟩
    (by decide) selected_cut_52185

theorem selected_cut_52186 : selected 10 ⟨1517152, by decide⟩
    (prefixPartial 11 287635) = some ⟨11, 2, 0, 1517152, 287635, 1641, 262144⟩ := by
  decide +kernel

theorem context_11_287635_1517152 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287635 ⟨1517152, by decide⟩ :=
  accepted_of_selected 11 287635 ⟨1517152, by decide⟩ ⟨11, 2, 0, 1517152, 287635, 1641, 262144⟩
    (by decide) selected_cut_52186

theorem unmarked_context_10_71908_1517153 : frontier 11 ⟨1517153, by decide⟩
    (prefixCache 10 71908) (prefixPartial 10 71908) = false := by
  decide +kernel

theorem node_context_10_71908_1517153 : EJMOriginalGlobalDAGData.nodes 11 ⟨1517153, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨1517065, by decide⟩,⟨1517113, by decide⟩,⟨1517152, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71908_1517153 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71908 ⟨1517153, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71908
    ⟨1517153, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨1517065, by decide⟩,⟨1517113, by decide⟩,⟨1517152, by decide⟩]) unmarked_context_10_71908_1517153 node_context_10_71908_1517153
  intro a
  fin_cases a
  · exact context_11_287632_434745
  · exact context_11_287633_1517065
  · exact context_11_287634_1517113
  · exact context_11_287635_1517152

theorem selected_cut_52187 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 71909) = some ⟨10, 1, 0, 1468874, 71909, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_71909_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71909 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 71909 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 71909, 1, 1048576⟩
    (by decide) selected_cut_52187

theorem selected_cut_52188 : selected 11 ⟨1517258, by decide⟩
    (prefixPartial 10 71910) = some ⟨10, 2, 0, 1517258, 71910, 4053, 1048576⟩ := by
  decide +kernel

theorem context_10_71910_1517258 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71910 ⟨1517258, by decide⟩ :=
  accepted_of_selected 10 71910 ⟨1517258, by decide⟩ ⟨10, 2, 0, 1517258, 71910, 4053, 1048576⟩
    (by decide) selected_cut_52188

theorem selected_cut_52189 : selected 11 ⟨1517341, by decide⟩
    (prefixPartial 10 71911) = some ⟨10, 2, 0, 1517341, 71911, 3385, 1048576⟩ := by
  decide +kernel

theorem context_10_71911_1517341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71911 ⟨1517341, by decide⟩ :=
  accepted_of_selected 10 71911 ⟨1517341, by decide⟩ ⟨10, 2, 0, 1517341, 71911, 3385, 1048576⟩
    (by decide) selected_cut_52189

theorem unmarked_context_9_17977_1517342 : frontier 12 ⟨1517342, by decide⟩
    (prefixCache 9 17977) (prefixPartial 9 17977) = false := by
  decide +kernel

theorem node_context_9_17977_1517342 : EJMOriginalGlobalDAGData.nodes 12 ⟨1517342, by decide⟩ =
    .split (coordinate 9) (![⟨1517153, by decide⟩,⟨1468874, by decide⟩,⟨1517258, by decide⟩,⟨1517341, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17977_1517342 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17977 ⟨1517342, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17977
    ⟨1517342, by decide⟩ (by decide) (![⟨1517153, by decide⟩,⟨1468874, by decide⟩,⟨1517258, by decide⟩,⟨1517341, by decide⟩]) unmarked_context_9_17977_1517342 node_context_9_17977_1517342
  intro a
  fin_cases a
  · exact context_10_71908_1517153
  · exact context_10_71909_1468874
  · exact context_10_71910_1517258
  · exact context_10_71911_1517341

theorem selected_cut_52190 : selected 11 ⟨1517396, by decide⟩
    (prefixPartial 10 71912) = some ⟨10, 2, 0, 1517396, 71912, 2229, 1048576⟩ := by
  decide +kernel

theorem context_10_71912_1517396 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71912 ⟨1517396, by decide⟩ :=
  accepted_of_selected 10 71912 ⟨1517396, by decide⟩ ⟨10, 2, 0, 1517396, 71912, 2229, 1048576⟩
    (by decide) selected_cut_52190

theorem selected_cut_52191 : selected 11 ⟨1517459, by decide⟩
    (prefixPartial 10 71913) = some ⟨10, 2, 0, 1517459, 71913, 2777, 1048576⟩ := by
  decide +kernel

theorem context_10_71913_1517459 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71913 ⟨1517459, by decide⟩ :=
  accepted_of_selected 10 71913 ⟨1517459, by decide⟩ ⟨10, 2, 0, 1517459, 71913, 2777, 1048576⟩
    (by decide) selected_cut_52191

theorem selected_cut_52192 : selected 11 ⟨1469103, by decide⟩
    (prefixPartial 10 71914) = some ⟨10, 1, 0, 1469103, 71914, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_71914_1469103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71914 ⟨1469103, by decide⟩ :=
  accepted_of_selected 10 71914 ⟨1469103, by decide⟩ ⟨10, 1, 0, 1469103, 71914, 1, 1048576⟩
    (by decide) selected_cut_52192

theorem selected_cut_52193 : selected 11 ⟨1517493, by decide⟩
    (prefixPartial 10 71915) = some ⟨10, 2, 0, 1517493, 71915, 1653, 1048576⟩ := by
  decide +kernel

theorem context_10_71915_1517493 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71915 ⟨1517493, by decide⟩ :=
  accepted_of_selected 10 71915 ⟨1517493, by decide⟩ ⟨10, 2, 0, 1517493, 71915, 1653, 1048576⟩
    (by decide) selected_cut_52193

theorem unmarked_context_9_17978_1517494 : frontier 12 ⟨1517494, by decide⟩
    (prefixCache 9 17978) (prefixPartial 9 17978) = false := by
  decide +kernel

theorem node_context_9_17978_1517494 : EJMOriginalGlobalDAGData.nodes 12 ⟨1517494, by decide⟩ =
    .split (coordinate 9) (![⟨1517396, by decide⟩,⟨1517459, by decide⟩,⟨1469103, by decide⟩,⟨1517493, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17978_1517494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17978 ⟨1517494, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17978
    ⟨1517494, by decide⟩ (by decide) (![⟨1517396, by decide⟩,⟨1517459, by decide⟩,⟨1469103, by decide⟩,⟨1517493, by decide⟩]) unmarked_context_9_17978_1517494 node_context_9_17978_1517494
  intro a
  fin_cases a
  · exact context_10_71912_1517396
  · exact context_10_71913_1517459
  · exact context_10_71914_1469103
  · exact context_10_71915_1517493

theorem selected_cut_52194 : selected 12 ⟨1517555, by decide⟩
    (prefixPartial 9 17979) = some ⟨9, 2, 0, 1517555, 17979, 1641, 4194304⟩ := by
  decide +kernel

theorem context_9_17979_1517555 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17979 ⟨1517555, by decide⟩ :=
  accepted_of_selected 9 17979 ⟨1517555, by decide⟩ ⟨9, 2, 0, 1517555, 17979, 1641, 4194304⟩
    (by decide) selected_cut_52194

theorem unmarked_context_8_4494_1517556 : frontier 13 ⟨1517556, by decide⟩
    (prefixCache 8 4494) (prefixPartial 8 4494) = false := by
  decide +kernel

theorem node_context_8_4494_1517556 : EJMOriginalGlobalDAGData.nodes 13 ⟨1517556, by decide⟩ =
    .split (coordinate 8) (![⟨1517007, by decide⟩,⟨1517342, by decide⟩,⟨1517494, by decide⟩,⟨1517555, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4494_1517556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4494 ⟨1517556, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4494
    ⟨1517556, by decide⟩ (by decide) (![⟨1517007, by decide⟩,⟨1517342, by decide⟩,⟨1517494, by decide⟩,⟨1517555, by decide⟩]) unmarked_context_8_4494_1517556 node_context_8_4494_1517556
  intro a
  fin_cases a
  · exact context_9_17976_1517007
  · exact context_9_17977_1517342
  · exact context_9_17978_1517494
  · exact context_9_17979_1517555

theorem selected_cut_52195 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 71920) = some ⟨10, 1, 0, 1468246, 71920, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_71920_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71920 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 71920 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 71920, 1, 1048576⟩
    (by decide) selected_cut_52195

theorem selected_cut_52196 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 1150736) = some ⟨12, 1, 0, 448748, 1150736, 1, 65536⟩ := by
  decide +kernel

theorem context_12_1150736_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1150736 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 1150736 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 1150736, 1, 65536⟩
    (by decide) selected_cut_52196

theorem selected_cut_52197 : selected 9 ⟨1517658, by decide⟩
    (prefixPartial 12 1150737) = some ⟨12, 2, 0, 1517658, 1150737, 2033, 65536⟩ := by
  decide +kernel

theorem context_12_1150737_1517658 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1150737 ⟨1517658, by decide⟩ :=
  accepted_of_selected 12 1150737 ⟨1517658, by decide⟩ ⟨12, 2, 0, 1517658, 1150737, 2033, 65536⟩
    (by decide) selected_cut_52197

theorem selected_cut_52198 : selected 9 ⟨1517719, by decide⟩
    (prefixPartial 12 1150738) = some ⟨12, 2, 0, 1517719, 1150738, 1789, 65536⟩ := by
  decide +kernel

theorem context_12_1150738_1517719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1150738 ⟨1517719, by decide⟩ :=
  accepted_of_selected 12 1150738 ⟨1517719, by decide⟩ ⟨12, 2, 0, 1517719, 1150738, 1789, 65536⟩
    (by decide) selected_cut_52198

theorem selected_cut_52199 : selected 9 ⟨1517760, by decide⟩
    (prefixPartial 12 1150739) = some ⟨12, 2, 0, 1517760, 1150739, 1641, 65536⟩ := by
  decide +kernel

theorem context_12_1150739_1517760 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1150739 ⟨1517760, by decide⟩ :=
  accepted_of_selected 12 1150739 ⟨1517760, by decide⟩ ⟨12, 2, 0, 1517760, 1150739, 1641, 65536⟩
    (by decide) selected_cut_52199

theorem unmarked_context_11_287684_1517761 : frontier 10 ⟨1517761, by decide⟩
    (prefixCache 11 287684) (prefixPartial 11 287684) = false := by
  decide +kernel

theorem node_context_11_287684_1517761 : EJMOriginalGlobalDAGData.nodes 10 ⟨1517761, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1517658, by decide⟩,⟨1517719, by decide⟩,⟨1517760, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_287684_1517761 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287684 ⟨1517761, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 287684
    ⟨1517761, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1517658, by decide⟩,⟨1517719, by decide⟩,⟨1517760, by decide⟩]) unmarked_context_11_287684_1517761 node_context_11_287684_1517761
  intro a
  fin_cases a
  · exact context_12_1150736_448748
  · exact context_12_1150737_1517658
  · exact context_12_1150738_1517719
  · exact context_12_1150739_1517760

theorem selected_cut_52200 : selected 10 ⟨1468419, by decide⟩
    (prefixPartial 11 287685) = some ⟨11, 1, 0, 1468419, 287685, 1, 262144⟩ := by
  decide +kernel

theorem context_11_287685_1468419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287685 ⟨1468419, by decide⟩ :=
  accepted_of_selected 11 287685 ⟨1468419, by decide⟩ ⟨11, 1, 0, 1468419, 287685, 1, 262144⟩
    (by decide) selected_cut_52200

theorem selected_cut_52201 : selected 10 ⟨1517872, by decide⟩
    (prefixPartial 11 287686) = some ⟨11, 2, 0, 1517872, 287686, 3501, 262144⟩ := by
  decide +kernel

theorem context_11_287686_1517872 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287686 ⟨1517872, by decide⟩ :=
  accepted_of_selected 11 287686 ⟨1517872, by decide⟩ ⟨11, 2, 0, 1517872, 287686, 3501, 262144⟩
    (by decide) selected_cut_52201

theorem selected_cut_52202 : selected 10 ⟨1517912, by decide⟩
    (prefixPartial 11 287687) = some ⟨11, 2, 0, 1517912, 287687, 1513, 262144⟩ := by
  decide +kernel

theorem context_11_287687_1517912 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287687 ⟨1517912, by decide⟩ :=
  accepted_of_selected 11 287687 ⟨1517912, by decide⟩ ⟨11, 2, 0, 1517912, 287687, 1513, 262144⟩
    (by decide) selected_cut_52202

theorem unmarked_context_10_71921_1517913 : frontier 11 ⟨1517913, by decide⟩
    (prefixCache 10 71921) (prefixPartial 10 71921) = false := by
  decide +kernel

theorem node_context_10_71921_1517913 : EJMOriginalGlobalDAGData.nodes 11 ⟨1517913, by decide⟩ =
    .split (coordinate 10) (![⟨1517761, by decide⟩,⟨1468419, by decide⟩,⟨1517872, by decide⟩,⟨1517912, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71921_1517913 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71921 ⟨1517913, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71921
    ⟨1517913, by decide⟩ (by decide) (![⟨1517761, by decide⟩,⟨1468419, by decide⟩,⟨1517872, by decide⟩,⟨1517912, by decide⟩]) unmarked_context_10_71921_1517913 node_context_10_71921_1517913
  intro a
  fin_cases a
  · exact context_11_287684_1517761
  · exact context_11_287685_1468419
  · exact context_11_287686_1517872
  · exact context_11_287687_1517912

theorem selected_cut_52203 : selected 10 ⟨1517990, by decide⟩
    (prefixPartial 11 287688) = some ⟨11, 2, 0, 1517990, 287688, 2761, 262144⟩ := by
  decide +kernel

theorem context_11_287688_1517990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287688 ⟨1517990, by decide⟩ :=
  accepted_of_selected 11 287688 ⟨1517990, by decide⟩ ⟨11, 2, 0, 1517990, 287688, 2761, 262144⟩
    (by decide) selected_cut_52203

theorem selected_cut_52204 : selected 10 ⟨1518020, by decide⟩
    (prefixPartial 11 287689) = some ⟨11, 2, 0, 1518020, 287689, 1217, 262144⟩ := by
  decide +kernel

theorem context_11_287689_1518020 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287689 ⟨1518020, by decide⟩ :=
  accepted_of_selected 11 287689 ⟨1518020, by decide⟩ ⟨11, 2, 0, 1518020, 287689, 1217, 262144⟩
    (by decide) selected_cut_52204

theorem selected_cut_52205 : selected 10 ⟨1468743, by decide⟩
    (prefixPartial 11 287690) = some ⟨11, 1, 0, 1468743, 287690, 1, 262144⟩ := by
  decide +kernel

theorem context_11_287690_1468743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287690 ⟨1468743, by decide⟩ :=
  accepted_of_selected 11 287690 ⟨1468743, by decide⟩ ⟨11, 1, 0, 1468743, 287690, 1, 262144⟩
    (by decide) selected_cut_52205

theorem selected_cut_52206 : selected 10 ⟨1518045, by decide⟩
    (prefixPartial 11 287691) = some ⟨11, 2, 0, 1518045, 287691, 1213, 262144⟩ := by
  decide +kernel

theorem context_11_287691_1518045 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287691 ⟨1518045, by decide⟩ :=
  accepted_of_selected 11 287691 ⟨1518045, by decide⟩ ⟨11, 2, 0, 1518045, 287691, 1213, 262144⟩
    (by decide) selected_cut_52206

theorem unmarked_context_10_71922_1518046 : frontier 11 ⟨1518046, by decide⟩
    (prefixCache 10 71922) (prefixPartial 10 71922) = false := by
  decide +kernel

theorem node_context_10_71922_1518046 : EJMOriginalGlobalDAGData.nodes 11 ⟨1518046, by decide⟩ =
    .split (coordinate 10) (![⟨1517990, by decide⟩,⟨1518020, by decide⟩,⟨1468743, by decide⟩,⟨1518045, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71922_1518046 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71922 ⟨1518046, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71922
    ⟨1518046, by decide⟩ (by decide) (![⟨1517990, by decide⟩,⟨1518020, by decide⟩,⟨1468743, by decide⟩,⟨1518045, by decide⟩]) unmarked_context_10_71922_1518046 node_context_10_71922_1518046
  intro a
  fin_cases a
  · exact context_11_287688_1517990
  · exact context_11_287689_1518020
  · exact context_11_287690_1468743
  · exact context_11_287691_1518045

theorem selected_cut_52207 : selected 10 ⟨793294, by decide⟩
    (prefixPartial 11 287692) = some ⟨11, 1, 0, 793294, 287692, 1, 262144⟩ := by
  decide +kernel

theorem context_11_287692_793294 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287692 ⟨793294, by decide⟩ :=
  accepted_of_selected 11 287692 ⟨793294, by decide⟩ ⟨11, 1, 0, 793294, 287692, 1, 262144⟩
    (by decide) selected_cut_52207

theorem selected_cut_52208 : selected 10 ⟨1518090, by decide⟩
    (prefixPartial 11 287693) = some ⟨11, 2, 0, 1518090, 287693, 2073, 262144⟩ := by
  decide +kernel

theorem context_11_287693_1518090 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287693 ⟨1518090, by decide⟩ :=
  accepted_of_selected 11 287693 ⟨1518090, by decide⟩ ⟨11, 2, 0, 1518090, 287693, 2073, 262144⟩
    (by decide) selected_cut_52208

theorem selected_cut_52209 : selected 10 ⟨1518144, by decide⟩
    (prefixPartial 11 287694) = some ⟨11, 2, 0, 1518144, 287694, 2233, 262144⟩ := by
  decide +kernel

theorem context_11_287694_1518144 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287694 ⟨1518144, by decide⟩ :=
  accepted_of_selected 11 287694 ⟨1518144, by decide⟩ ⟨11, 2, 0, 1518144, 287694, 2233, 262144⟩
    (by decide) selected_cut_52209

theorem selected_cut_52210 : selected 10 ⟨1470044, by decide⟩
    (prefixPartial 11 287695) = some ⟨11, 1, 0, 1470044, 287695, 1, 262144⟩ := by
  decide +kernel

theorem context_11_287695_1470044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287695 ⟨1470044, by decide⟩ :=
  accepted_of_selected 11 287695 ⟨1470044, by decide⟩ ⟨11, 1, 0, 1470044, 287695, 1, 262144⟩
    (by decide) selected_cut_52210

theorem unmarked_context_10_71923_1518145 : frontier 11 ⟨1518145, by decide⟩
    (prefixCache 10 71923) (prefixPartial 10 71923) = false := by
  decide +kernel

theorem node_context_10_71923_1518145 : EJMOriginalGlobalDAGData.nodes 11 ⟨1518145, by decide⟩ =
    .split (coordinate 10) (![⟨793294, by decide⟩,⟨1518090, by decide⟩,⟨1518144, by decide⟩,⟨1470044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71923_1518145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71923 ⟨1518145, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71923
    ⟨1518145, by decide⟩ (by decide) (![⟨793294, by decide⟩,⟨1518090, by decide⟩,⟨1518144, by decide⟩,⟨1470044, by decide⟩]) unmarked_context_10_71923_1518145 node_context_10_71923_1518145
  intro a
  fin_cases a
  · exact context_11_287692_793294
  · exact context_11_287693_1518090
  · exact context_11_287694_1518144
  · exact context_11_287695_1470044

theorem unmarked_context_9_17980_1518146 : frontier 12 ⟨1518146, by decide⟩
    (prefixCache 9 17980) (prefixPartial 9 17980) = false := by
  decide +kernel

theorem node_context_9_17980_1518146 : EJMOriginalGlobalDAGData.nodes 12 ⟨1518146, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1517913, by decide⟩,⟨1518046, by decide⟩,⟨1518145, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17980_1518146 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17980 ⟨1518146, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17980
    ⟨1518146, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1517913, by decide⟩,⟨1518046, by decide⟩,⟨1518145, by decide⟩]) unmarked_context_9_17980_1518146 node_context_9_17980_1518146
  intro a
  fin_cases a
  · exact context_10_71920_1468246
  · exact context_10_71921_1517913
  · exact context_10_71922_1518046
  · exact context_10_71923_1518145

theorem selected_cut_52211 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 287696) = some ⟨11, 1, 0, 434745, 287696, 1, 262144⟩ := by
  decide +kernel

theorem context_11_287696_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287696 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 287696 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 287696, 1, 262144⟩
    (by decide) selected_cut_52211

theorem selected_cut_52212 : selected 10 ⟨1518190, by decide⟩
    (prefixPartial 11 287697) = some ⟨11, 2, 0, 1518190, 287697, 1709, 262144⟩ := by
  decide +kernel

theorem context_11_287697_1518190 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287697 ⟨1518190, by decide⟩ :=
  accepted_of_selected 11 287697 ⟨1518190, by decide⟩ ⟨11, 2, 0, 1518190, 287697, 1709, 262144⟩
    (by decide) selected_cut_52212

theorem selected_cut_52213 : selected 10 ⟨1518239, by decide⟩
    (prefixPartial 11 287698) = some ⟨11, 2, 0, 1518239, 287698, 1833, 262144⟩ := by
  decide +kernel

theorem context_11_287698_1518239 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287698 ⟨1518239, by decide⟩ :=
  accepted_of_selected 11 287698 ⟨1518239, by decide⟩ ⟨11, 2, 0, 1518239, 287698, 1833, 262144⟩
    (by decide) selected_cut_52213

theorem selected_cut_52214 : selected 10 ⟨1518260, by decide⟩
    (prefixPartial 11 287699) = some ⟨11, 2, 0, 1518260, 287699, 821, 262144⟩ := by
  decide +kernel

theorem context_11_287699_1518260 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 287699 ⟨1518260, by decide⟩ :=
  accepted_of_selected 11 287699 ⟨1518260, by decide⟩ ⟨11, 2, 0, 1518260, 287699, 821, 262144⟩
    (by decide) selected_cut_52214

theorem unmarked_context_10_71924_1518261 : frontier 11 ⟨1518261, by decide⟩
    (prefixCache 10 71924) (prefixPartial 10 71924) = false := by
  decide +kernel

theorem node_context_10_71924_1518261 : EJMOriginalGlobalDAGData.nodes 11 ⟨1518261, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨1518190, by decide⟩,⟨1518239, by decide⟩,⟨1518260, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71924_1518261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71924 ⟨1518261, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71924
    ⟨1518261, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨1518190, by decide⟩,⟨1518239, by decide⟩,⟨1518260, by decide⟩]) unmarked_context_10_71924_1518261 node_context_10_71924_1518261
  intro a
  fin_cases a
  · exact context_11_287696_434745
  · exact context_11_287697_1518190
  · exact context_11_287698_1518239
  · exact context_11_287699_1518260

theorem selected_cut_52215 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 71925) = some ⟨10, 1, 0, 1468874, 71925, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_71925_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71925 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 71925 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 71925, 1, 1048576⟩
    (by decide) selected_cut_52215

theorem selected_cut_52216 : selected 11 ⟨1518375, by decide⟩
    (prefixPartial 10 71926) = some ⟨10, 2, 0, 1518375, 71926, 4089, 1048576⟩ := by
  decide +kernel

theorem context_10_71926_1518375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71926 ⟨1518375, by decide⟩ :=
  accepted_of_selected 10 71926 ⟨1518375, by decide⟩ ⟨10, 2, 0, 1518375, 71926, 4089, 1048576⟩
    (by decide) selected_cut_52216

theorem selected_cut_52217 : selected 11 ⟨1518450, by decide⟩
    (prefixPartial 10 71927) = some ⟨10, 2, 0, 1518450, 71927, 3529, 1048576⟩ := by
  decide +kernel

theorem context_10_71927_1518450 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71927 ⟨1518450, by decide⟩ :=
  accepted_of_selected 10 71927 ⟨1518450, by decide⟩ ⟨10, 2, 0, 1518450, 71927, 3529, 1048576⟩
    (by decide) selected_cut_52217

theorem unmarked_context_9_17981_1518451 : frontier 12 ⟨1518451, by decide⟩
    (prefixCache 9 17981) (prefixPartial 9 17981) = false := by
  decide +kernel

theorem node_context_9_17981_1518451 : EJMOriginalGlobalDAGData.nodes 12 ⟨1518451, by decide⟩ =
    .split (coordinate 9) (![⟨1518261, by decide⟩,⟨1468874, by decide⟩,⟨1518375, by decide⟩,⟨1518450, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17981_1518451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17981 ⟨1518451, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17981
    ⟨1518451, by decide⟩ (by decide) (![⟨1518261, by decide⟩,⟨1468874, by decide⟩,⟨1518375, by decide⟩,⟨1518450, by decide⟩]) unmarked_context_9_17981_1518451 node_context_9_17981_1518451
  intro a
  fin_cases a
  · exact context_10_71924_1518261
  · exact context_10_71925_1468874
  · exact context_10_71926_1518375
  · exact context_10_71927_1518450

theorem selected_cut_52218 : selected 11 ⟨1518486, by decide⟩
    (prefixPartial 10 71928) = some ⟨10, 2, 0, 1518486, 71928, 1341, 1048576⟩ := by
  decide +kernel

theorem context_10_71928_1518486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71928 ⟨1518486, by decide⟩ :=
  accepted_of_selected 10 71928 ⟨1518486, by decide⟩ ⟨10, 2, 0, 1518486, 71928, 1341, 1048576⟩
    (by decide) selected_cut_52218

theorem selected_cut_52219 : selected 11 ⟨1518538, by decide⟩
    (prefixPartial 10 71929) = some ⟨10, 2, 0, 1518538, 71929, 1945, 1048576⟩ := by
  decide +kernel

theorem context_10_71929_1518538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71929 ⟨1518538, by decide⟩ :=
  accepted_of_selected 10 71929 ⟨1518538, by decide⟩ ⟨10, 2, 0, 1518538, 71929, 1945, 1048576⟩
    (by decide) selected_cut_52219

theorem selected_cut_52220 : selected 11 ⟨1469103, by decide⟩
    (prefixPartial 10 71930) = some ⟨10, 1, 0, 1469103, 71930, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_71930_1469103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71930 ⟨1469103, by decide⟩ :=
  accepted_of_selected 10 71930 ⟨1469103, by decide⟩ ⟨10, 1, 0, 1469103, 71930, 1, 1048576⟩
    (by decide) selected_cut_52220

theorem selected_cut_52221 : selected 11 ⟨1518575, by decide⟩
    (prefixPartial 10 71931) = some ⟨10, 2, 0, 1518575, 71931, 1509, 1048576⟩ := by
  decide +kernel

theorem context_10_71931_1518575 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71931 ⟨1518575, by decide⟩ :=
  accepted_of_selected 10 71931 ⟨1518575, by decide⟩ ⟨10, 2, 0, 1518575, 71931, 1509, 1048576⟩
    (by decide) selected_cut_52221

theorem unmarked_context_9_17982_1518576 : frontier 12 ⟨1518576, by decide⟩
    (prefixCache 9 17982) (prefixPartial 9 17982) = false := by
  decide +kernel

theorem node_context_9_17982_1518576 : EJMOriginalGlobalDAGData.nodes 12 ⟨1518576, by decide⟩ =
    .split (coordinate 9) (![⟨1518486, by decide⟩,⟨1518538, by decide⟩,⟨1469103, by decide⟩,⟨1518575, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17982_1518576 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17982 ⟨1518576, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17982
    ⟨1518576, by decide⟩ (by decide) (![⟨1518486, by decide⟩,⟨1518538, by decide⟩,⟨1469103, by decide⟩,⟨1518575, by decide⟩]) unmarked_context_9_17982_1518576 node_context_9_17982_1518576
  intro a
  fin_cases a
  · exact context_10_71928_1518486
  · exact context_10_71929_1518538
  · exact context_10_71930_1469103
  · exact context_10_71931_1518575

theorem selected_cut_52222 : selected 12 ⟨1518607, by decide⟩
    (prefixPartial 9 17983) = some ⟨9, 2, 0, 1518607, 17983, 1553, 4194304⟩ := by
  decide +kernel

theorem context_9_17983_1518607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17983 ⟨1518607, by decide⟩ :=
  accepted_of_selected 9 17983 ⟨1518607, by decide⟩ ⟨9, 2, 0, 1518607, 17983, 1553, 4194304⟩
    (by decide) selected_cut_52222

theorem unmarked_context_8_4495_1518608 : frontier 13 ⟨1518608, by decide⟩
    (prefixCache 8 4495) (prefixPartial 8 4495) = false := by
  decide +kernel

theorem node_context_8_4495_1518608 : EJMOriginalGlobalDAGData.nodes 13 ⟨1518608, by decide⟩ =
    .split (coordinate 8) (![⟨1518146, by decide⟩,⟨1518451, by decide⟩,⟨1518576, by decide⟩,⟨1518607, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4495_1518608 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4495 ⟨1518608, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4495
    ⟨1518608, by decide⟩ (by decide) (![⟨1518146, by decide⟩,⟨1518451, by decide⟩,⟨1518576, by decide⟩,⟨1518607, by decide⟩]) unmarked_context_8_4495_1518608 node_context_8_4495_1518608
  intro a
  fin_cases a
  · exact context_9_17980_1518146
  · exact context_9_17981_1518451
  · exact context_9_17982_1518576
  · exact context_9_17983_1518607

theorem unmarked_context_7_1123_1518609 : frontier 14 ⟨1518609, by decide⟩
    (prefixCache 7 1123) (prefixPartial 7 1123) = false := by
  decide +kernel

theorem node_context_7_1123_1518609 : EJMOriginalGlobalDAGData.nodes 14 ⟨1518609, by decide⟩ =
    .split (coordinate 7) (![⟨1515557, by decide⟩,⟨1516439, by decide⟩,⟨1517556, by decide⟩,⟨1518608, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_1123_1518609 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 1123 ⟨1518609, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 1123
    ⟨1518609, by decide⟩ (by decide) (![⟨1515557, by decide⟩,⟨1516439, by decide⟩,⟨1517556, by decide⟩,⟨1518608, by decide⟩]) unmarked_context_7_1123_1518609 node_context_7_1123_1518609
  intro a
  fin_cases a
  · exact context_8_4492_1515557
  · exact context_8_4493_1516439
  · exact context_8_4494_1517556
  · exact context_8_4495_1518608

theorem unmarked_context_6_280_1518610 : frontier 15 ⟨1518610, by decide⟩
    (prefixCache 6 280) (prefixPartial 6 280) = false := by
  decide +kernel

theorem node_context_6_280_1518610 : EJMOriginalGlobalDAGData.nodes 15 ⟨1518610, by decide⟩ =
    .split (coordinate 6) (![⟨1510459, by decide⟩,⟨1510460, by decide⟩,⟨1514617, by decide⟩,⟨1518609, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_6_280_1518610 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 280 ⟨1518610, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 6 280
    ⟨1518610, by decide⟩ (by decide) (![⟨1510459, by decide⟩,⟨1510460, by decide⟩,⟨1514617, by decide⟩,⟨1518609, by decide⟩]) unmarked_context_6_280_1518610 node_context_6_280_1518610
  intro a
  fin_cases a
  · exact context_7_1120_1510459
  · exact context_7_1121_1510460
  · exact context_7_1122_1514617
  · exact context_7_1123_1518609

theorem selected_cut_52223 : selected 15 ⟨1475984, by decide⟩
    (prefixPartial 6 281) = some ⟨6, 1, 0, 1475984, 281, 1, 268435456⟩ := by
  decide +kernel

theorem context_6_281_1475984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 281 ⟨1475984, by decide⟩ :=
  accepted_of_selected 6 281 ⟨1475984, by decide⟩ ⟨6, 1, 0, 1475984, 281, 1, 268435456⟩
    (by decide) selected_cut_52223

theorem selected_cut_52224 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 72192) = some ⟨10, 1, 0, 1468246, 72192, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_72192_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72192 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 72192 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 72192, 1, 1048576⟩
    (by decide) selected_cut_52224

theorem selected_cut_52225 : selected 10 ⟨1518654, by decide⟩
    (prefixPartial 11 288772) = some ⟨11, 2, 0, 1518654, 288772, 1225, 262144⟩ := by
  decide +kernel

theorem context_11_288772_1518654 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 288772 ⟨1518654, by decide⟩ :=
  accepted_of_selected 11 288772 ⟨1518654, by decide⟩ ⟨11, 2, 0, 1518654, 288772, 1225, 262144⟩
    (by decide) selected_cut_52225

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
