/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover422
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_7_302_1105208 : frontier 14 ⟨1105208, by decide⟩
    (prefixCache 7 302) (prefixPartial 7 302) = false := by
  decide +kernel

theorem node_context_7_302_1105208 : EJMOriginalGlobalDAGData.nodes 14 ⟨1105208, by decide⟩ =
    .split (coordinate 7) (![⟨979897, by decide⟩,⟨1101012, by decide⟩,⟨979897, by decide⟩,⟨1105207, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_302_1105208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 302 ⟨1105208, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 302
    ⟨1105208, by decide⟩ (by decide) (![⟨979897, by decide⟩,⟨1101012, by decide⟩,⟨979897, by decide⟩,⟨1105207, by decide⟩]) unmarked_context_7_302_1105208 node_context_7_302_1105208
  intro a
  fin_cases a
  · exact context_8_1208_979897
  · exact context_8_1209_1101012
  · exact context_8_1210_979897
  · exact context_8_1211_1105207

theorem selected_cut_40611 : selected 13 ⟨979897, by decide⟩
    (prefixPartial 8 1212) = some ⟨8, 1, 0, 979897, 1212, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_1212_979897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1212 ⟨979897, by decide⟩ :=
  accepted_of_selected 8 1212 ⟨979897, by decide⟩ ⟨8, 1, 0, 979897, 1212, 1, 16777216⟩
    (by decide) selected_cut_40611

theorem selected_cut_40612 : selected 13 ⟨979897, by decide⟩
    (prefixPartial 8 1213) = some ⟨8, 1, 0, 979897, 1213, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_1213_979897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1213 ⟨979897, by decide⟩ :=
  accepted_of_selected 8 1213 ⟨979897, by decide⟩ ⟨8, 1, 0, 979897, 1213, 1, 16777216⟩
    (by decide) selected_cut_40612

theorem selected_cut_40613 : selected 13 ⟨979897, by decide⟩
    (prefixPartial 8 1214) = some ⟨8, 1, 0, 979897, 1214, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_1214_979897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1214 ⟨979897, by decide⟩ :=
  accepted_of_selected 8 1214 ⟨979897, by decide⟩ ⟨8, 1, 0, 979897, 1214, 1, 16777216⟩
    (by decide) selected_cut_40613

theorem selected_cut_40614 : selected 10 ⟨1105210, by decide⟩
    (prefixPartial 11 77760) = some ⟨11, 2, 0, 1105210, 77760, 5, 262144⟩ := by
  decide +kernel

theorem context_11_77760_1105210 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77760 ⟨1105210, by decide⟩ :=
  accepted_of_selected 11 77760 ⟨1105210, by decide⟩ ⟨11, 2, 0, 1105210, 77760, 5, 262144⟩
    (by decide) selected_cut_40614

theorem selected_cut_40615 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 311044) = some ⟨12, 1, 0, 34034, 311044, 1, 65536⟩ := by
  decide +kernel

theorem context_12_311044_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 311044 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 311044 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 311044, 1, 65536⟩
    (by decide) selected_cut_40615

theorem selected_cut_40616 : selected 8 ⟨1105245, by decide⟩
    (prefixPartial 13 1244180) = some ⟨13, 2, 0, 1105245, 1244180, 1857, 16384⟩ := by
  decide +kernel

theorem context_13_1244180_1105245 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1244180 ⟨1105245, by decide⟩ :=
  accepted_of_selected 13 1244180 ⟨1105245, by decide⟩ ⟨13, 2, 0, 1105245, 1244180, 1857, 16384⟩
    (by decide) selected_cut_40616

theorem selected_cut_40617 : selected 8 ⟨1105265, by decide⟩
    (prefixPartial 13 1244181) = some ⟨13, 2, 0, 1105265, 1244181, 1233, 16384⟩ := by
  decide +kernel

theorem context_13_1244181_1105265 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1244181 ⟨1105265, by decide⟩ :=
  accepted_of_selected 13 1244181 ⟨1105265, by decide⟩ ⟨13, 2, 0, 1105265, 1244181, 1233, 16384⟩
    (by decide) selected_cut_40617

theorem selected_cut_40618 : selected 8 ⟨1105277, by decide⟩
    (prefixPartial 13 1244182) = some ⟨13, 2, 0, 1105277, 1244182, 889, 16384⟩ := by
  decide +kernel

theorem context_13_1244182_1105277 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1244182 ⟨1105277, by decide⟩ :=
  accepted_of_selected 13 1244182 ⟨1105277, by decide⟩ ⟨13, 2, 0, 1105277, 1244182, 889, 16384⟩
    (by decide) selected_cut_40618

theorem selected_cut_40619 : selected 8 ⟨1105282, by decide⟩
    (prefixPartial 13 1244183) = some ⟨13, 2, 0, 1105282, 1244183, 517, 16384⟩ := by
  decide +kernel

theorem context_13_1244183_1105282 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1244183 ⟨1105282, by decide⟩ :=
  accepted_of_selected 13 1244183 ⟨1105282, by decide⟩ ⟨13, 2, 0, 1105282, 1244183, 517, 16384⟩
    (by decide) selected_cut_40619

theorem unmarked_context_12_311045_1105283 : frontier 9 ⟨1105283, by decide⟩
    (prefixCache 12 311045) (prefixPartial 12 311045) = false := by
  decide +kernel

theorem node_context_12_311045_1105283 : EJMOriginalGlobalDAGData.nodes 9 ⟨1105283, by decide⟩ =
    .split (coordinate 12) (![⟨1105245, by decide⟩,⟨1105265, by decide⟩,⟨1105277, by decide⟩,⟨1105282, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_311045_1105283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 311045 ⟨1105283, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 311045
    ⟨1105283, by decide⟩ (by decide) (![⟨1105245, by decide⟩,⟨1105265, by decide⟩,⟨1105277, by decide⟩,⟨1105282, by decide⟩]) unmarked_context_12_311045_1105283 node_context_12_311045_1105283
  intro a
  fin_cases a
  · exact context_13_1244180_1105245
  · exact context_13_1244181_1105265
  · exact context_13_1244182_1105277
  · exact context_13_1244183_1105282

theorem selected_cut_40620 : selected 8 ⟨1105317, by decide⟩
    (prefixPartial 13 1244184) = some ⟨13, 2, 0, 1105317, 1244184, 1725, 16384⟩ := by
  decide +kernel

theorem context_13_1244184_1105317 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1244184 ⟨1105317, by decide⟩ :=
  accepted_of_selected 13 1244184 ⟨1105317, by decide⟩ ⟨13, 2, 0, 1105317, 1244184, 1725, 16384⟩
    (by decide) selected_cut_40620

theorem selected_cut_40621 : selected 8 ⟨1105334, by decide⟩
    (prefixPartial 13 1244185) = some ⟨13, 2, 0, 1105334, 1244185, 1077, 16384⟩ := by
  decide +kernel

theorem context_13_1244185_1105334 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1244185 ⟨1105334, by decide⟩ :=
  accepted_of_selected 13 1244185 ⟨1105334, by decide⟩ ⟨13, 2, 0, 1105334, 1244185, 1077, 16384⟩
    (by decide) selected_cut_40621

theorem selected_cut_40622 : selected 8 ⟨1105344, by decide⟩
    (prefixPartial 13 1244186) = some ⟨13, 2, 0, 1105344, 1244186, 789, 16384⟩ := by
  decide +kernel

theorem context_13_1244186_1105344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1244186 ⟨1105344, by decide⟩ :=
  accepted_of_selected 13 1244186 ⟨1105344, by decide⟩ ⟨13, 2, 0, 1105344, 1244186, 789, 16384⟩
    (by decide) selected_cut_40622

theorem selected_cut_40623 : selected 8 ⟨1105348, by decide⟩
    (prefixPartial 13 1244187) = some ⟨13, 2, 0, 1105348, 1244187, 581, 16384⟩ := by
  decide +kernel

theorem context_13_1244187_1105348 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1244187 ⟨1105348, by decide⟩ :=
  accepted_of_selected 13 1244187 ⟨1105348, by decide⟩ ⟨13, 2, 0, 1105348, 1244187, 581, 16384⟩
    (by decide) selected_cut_40623

theorem unmarked_context_12_311046_1105349 : frontier 9 ⟨1105349, by decide⟩
    (prefixCache 12 311046) (prefixPartial 12 311046) = false := by
  decide +kernel

theorem node_context_12_311046_1105349 : EJMOriginalGlobalDAGData.nodes 9 ⟨1105349, by decide⟩ =
    .split (coordinate 12) (![⟨1105317, by decide⟩,⟨1105334, by decide⟩,⟨1105344, by decide⟩,⟨1105348, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_311046_1105349 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 311046 ⟨1105349, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 311046
    ⟨1105349, by decide⟩ (by decide) (![⟨1105317, by decide⟩,⟨1105334, by decide⟩,⟨1105344, by decide⟩,⟨1105348, by decide⟩]) unmarked_context_12_311046_1105349 node_context_12_311046_1105349
  intro a
  fin_cases a
  · exact context_13_1244184_1105317
  · exact context_13_1244185_1105334
  · exact context_13_1244186_1105344
  · exact context_13_1244187_1105348

theorem selected_cut_40624 : selected 9 ⟨1105407, by decide⟩
    (prefixPartial 12 311047) = some ⟨12, 2, 0, 1105407, 311047, 3797, 65536⟩ := by
  decide +kernel

theorem context_12_311047_1105407 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 311047 ⟨1105407, by decide⟩ :=
  accepted_of_selected 12 311047 ⟨1105407, by decide⟩ ⟨12, 2, 0, 1105407, 311047, 3797, 65536⟩
    (by decide) selected_cut_40624

theorem unmarked_context_11_77761_1105408 : frontier 10 ⟨1105408, by decide⟩
    (prefixCache 11 77761) (prefixPartial 11 77761) = false := by
  decide +kernel

theorem node_context_11_77761_1105408 : EJMOriginalGlobalDAGData.nodes 10 ⟨1105408, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨1105283, by decide⟩,⟨1105349, by decide⟩,⟨1105407, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77761_1105408 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77761 ⟨1105408, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77761
    ⟨1105408, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨1105283, by decide⟩,⟨1105349, by decide⟩,⟨1105407, by decide⟩]) unmarked_context_11_77761_1105408 node_context_11_77761_1105408
  intro a
  fin_cases a
  · exact context_12_311044_34034
  · exact context_12_311045_1105283
  · exact context_12_311046_1105349
  · exact context_12_311047_1105407

theorem selected_cut_40625 : selected 9 ⟨3161, by decide⟩
    (prefixPartial 12 311048) = some ⟨12, 1, 0, 3161, 311048, 1, 65536⟩ := by
  decide +kernel

theorem context_12_311048_3161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 311048 ⟨3161, by decide⟩ :=
  accepted_of_selected 12 311048 ⟨3161, by decide⟩ ⟨12, 1, 0, 3161, 311048, 1, 65536⟩
    (by decide) selected_cut_40625

theorem selected_cut_40626 : selected 9 ⟨1105474, by decide⟩
    (prefixPartial 12 311049) = some ⟨12, 2, 0, 1105474, 311049, 3993, 65536⟩ := by
  decide +kernel

theorem context_12_311049_1105474 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 311049 ⟨1105474, by decide⟩ :=
  accepted_of_selected 12 311049 ⟨1105474, by decide⟩ ⟨12, 2, 0, 1105474, 311049, 3993, 65536⟩
    (by decide) selected_cut_40626

theorem selected_cut_40627 : selected 9 ⟨1105524, by decide⟩
    (prefixPartial 12 311050) = some ⟨12, 2, 0, 1105524, 311050, 3773, 65536⟩ := by
  decide +kernel

theorem context_12_311050_1105524 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 311050 ⟨1105524, by decide⟩ :=
  accepted_of_selected 12 311050 ⟨1105524, by decide⟩ ⟨12, 2, 0, 1105524, 311050, 3773, 65536⟩
    (by decide) selected_cut_40627

theorem selected_cut_40628 : selected 9 ⟨1105585, by decide⟩
    (prefixPartial 12 311051) = some ⟨12, 2, 0, 1105585, 311051, 3633, 65536⟩ := by
  decide +kernel

theorem context_12_311051_1105585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 311051 ⟨1105585, by decide⟩ :=
  accepted_of_selected 12 311051 ⟨1105585, by decide⟩ ⟨12, 2, 0, 1105585, 311051, 3633, 65536⟩
    (by decide) selected_cut_40628

theorem unmarked_context_11_77762_1105586 : frontier 10 ⟨1105586, by decide⟩
    (prefixCache 11 77762) (prefixPartial 11 77762) = false := by
  decide +kernel

theorem node_context_11_77762_1105586 : EJMOriginalGlobalDAGData.nodes 10 ⟨1105586, by decide⟩ =
    .split (coordinate 11) (![⟨3161, by decide⟩,⟨1105474, by decide⟩,⟨1105524, by decide⟩,⟨1105585, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77762_1105586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77762 ⟨1105586, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77762
    ⟨1105586, by decide⟩ (by decide) (![⟨3161, by decide⟩,⟨1105474, by decide⟩,⟨1105524, by decide⟩,⟨1105585, by decide⟩]) unmarked_context_11_77762_1105586 node_context_11_77762_1105586
  intro a
  fin_cases a
  · exact context_12_311048_3161
  · exact context_12_311049_1105474
  · exact context_12_311050_1105524
  · exact context_12_311051_1105585

theorem selected_cut_40629 : selected 9 ⟨1105682, by decide⟩
    (prefixPartial 12 311052) = some ⟨12, 2, 0, 1105682, 311052, 2605, 65536⟩ := by
  decide +kernel

theorem context_12_311052_1105682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 311052 ⟨1105682, by decide⟩ :=
  accepted_of_selected 12 311052 ⟨1105682, by decide⟩ ⟨12, 2, 0, 1105682, 311052, 2605, 65536⟩
    (by decide) selected_cut_40629

theorem selected_cut_40630 : selected 9 ⟨1105746, by decide⟩
    (prefixPartial 12 311053) = some ⟨12, 2, 0, 1105746, 311053, 3669, 65536⟩ := by
  decide +kernel

theorem context_12_311053_1105746 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 311053 ⟨1105746, by decide⟩ :=
  accepted_of_selected 12 311053 ⟨1105746, by decide⟩ ⟨12, 2, 0, 1105746, 311053, 3669, 65536⟩
    (by decide) selected_cut_40630

theorem selected_cut_40631 : selected 9 ⟨1105805, by decide⟩
    (prefixPartial 12 311054) = some ⟨12, 2, 0, 1105805, 311054, 3525, 65536⟩ := by
  decide +kernel

theorem context_12_311054_1105805 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 311054 ⟨1105805, by decide⟩ :=
  accepted_of_selected 12 311054 ⟨1105805, by decide⟩ ⟨12, 2, 0, 1105805, 311054, 3525, 65536⟩
    (by decide) selected_cut_40631

theorem selected_cut_40632 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 311055) = some ⟨12, 1, 0, 903806, 311055, 1, 65536⟩ := by
  decide +kernel

theorem context_12_311055_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 311055 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 311055 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 311055, 1, 65536⟩
    (by decide) selected_cut_40632

theorem unmarked_context_11_77763_1105806 : frontier 10 ⟨1105806, by decide⟩
    (prefixCache 11 77763) (prefixPartial 11 77763) = false := by
  decide +kernel

theorem node_context_11_77763_1105806 : EJMOriginalGlobalDAGData.nodes 10 ⟨1105806, by decide⟩ =
    .split (coordinate 11) (![⟨1105682, by decide⟩,⟨1105746, by decide⟩,⟨1105805, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77763_1105806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77763 ⟨1105806, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77763
    ⟨1105806, by decide⟩ (by decide) (![⟨1105682, by decide⟩,⟨1105746, by decide⟩,⟨1105805, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_77763_1105806 node_context_11_77763_1105806
  intro a
  fin_cases a
  · exact context_12_311052_1105682
  · exact context_12_311053_1105746
  · exact context_12_311054_1105805
  · exact context_12_311055_903806

theorem unmarked_context_10_19440_1105807 : frontier 11 ⟨1105807, by decide⟩
    (prefixCache 10 19440) (prefixPartial 10 19440) = false := by
  decide +kernel

theorem node_context_10_19440_1105807 : EJMOriginalGlobalDAGData.nodes 11 ⟨1105807, by decide⟩ =
    .split (coordinate 10) (![⟨1105210, by decide⟩,⟨1105408, by decide⟩,⟨1105586, by decide⟩,⟨1105806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19440_1105807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19440 ⟨1105807, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19440
    ⟨1105807, by decide⟩ (by decide) (![⟨1105210, by decide⟩,⟨1105408, by decide⟩,⟨1105586, by decide⟩,⟨1105806, by decide⟩]) unmarked_context_10_19440_1105807 node_context_10_19440_1105807
  intro a
  fin_cases a
  · exact context_11_77760_1105210
  · exact context_11_77761_1105408
  · exact context_11_77762_1105586
  · exact context_11_77763_1105806

theorem selected_cut_40633 : selected 9 ⟨26677, by decide⟩
    (prefixPartial 12 311056) = some ⟨12, 1, 0, 26677, 311056, 1, 65536⟩ := by
  decide +kernel

theorem context_12_311056_26677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 311056 ⟨26677, by decide⟩ :=
  accepted_of_selected 12 311056 ⟨26677, by decide⟩ ⟨12, 1, 0, 26677, 311056, 1, 65536⟩
    (by decide) selected_cut_40633

theorem selected_cut_40634 : selected 9 ⟨1105871, by decide⟩
    (prefixPartial 12 311057) = some ⟨12, 2, 0, 1105871, 311057, 3333, 65536⟩ := by
  decide +kernel

theorem context_12_311057_1105871 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 311057 ⟨1105871, by decide⟩ :=
  accepted_of_selected 12 311057 ⟨1105871, by decide⟩ ⟨12, 2, 0, 1105871, 311057, 3333, 65536⟩
    (by decide) selected_cut_40634

theorem selected_cut_40635 : selected 9 ⟨1105916, by decide⟩
    (prefixPartial 12 311058) = some ⟨12, 2, 0, 1105916, 311058, 1789, 65536⟩ := by
  decide +kernel

theorem context_12_311058_1105916 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 311058 ⟨1105916, by decide⟩ :=
  accepted_of_selected 12 311058 ⟨1105916, by decide⟩ ⟨12, 2, 0, 1105916, 311058, 1789, 65536⟩
    (by decide) selected_cut_40635

theorem selected_cut_40636 : selected 9 ⟨1105965, by decide⟩
    (prefixPartial 12 311059) = some ⟨12, 2, 0, 1105965, 311059, 2861, 65536⟩ := by
  decide +kernel

theorem context_12_311059_1105965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 311059 ⟨1105965, by decide⟩ :=
  accepted_of_selected 12 311059 ⟨1105965, by decide⟩ ⟨12, 2, 0, 1105965, 311059, 2861, 65536⟩
    (by decide) selected_cut_40636

theorem unmarked_context_11_77764_1105966 : frontier 10 ⟨1105966, by decide⟩
    (prefixCache 11 77764) (prefixPartial 11 77764) = false := by
  decide +kernel

theorem node_context_11_77764_1105966 : EJMOriginalGlobalDAGData.nodes 10 ⟨1105966, by decide⟩ =
    .split (coordinate 11) (![⟨26677, by decide⟩,⟨1105871, by decide⟩,⟨1105916, by decide⟩,⟨1105965, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77764_1105966 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77764 ⟨1105966, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77764
    ⟨1105966, by decide⟩ (by decide) (![⟨26677, by decide⟩,⟨1105871, by decide⟩,⟨1105916, by decide⟩,⟨1105965, by decide⟩]) unmarked_context_11_77764_1105966 node_context_11_77764_1105966
  intro a
  fin_cases a
  · exact context_12_311056_26677
  · exact context_12_311057_1105871
  · exact context_12_311058_1105916
  · exact context_12_311059_1105965

theorem selected_cut_40637 : selected 9 ⟨26677, by decide⟩
    (prefixPartial 12 311060) = some ⟨12, 1, 0, 26677, 311060, 1, 65536⟩ := by
  decide +kernel

theorem context_12_311060_26677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 311060 ⟨26677, by decide⟩ :=
  accepted_of_selected 12 311060 ⟨26677, by decide⟩ ⟨12, 1, 0, 26677, 311060, 1, 65536⟩
    (by decide) selected_cut_40637

theorem selected_cut_40638 : selected 9 ⟨692794, by decide⟩
    (prefixPartial 12 311061) = some ⟨12, 1, 0, 692794, 311061, 1, 65536⟩ := by
  decide +kernel

theorem context_12_311061_692794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 311061 ⟨692794, by decide⟩ :=
  accepted_of_selected 12 311061 ⟨692794, by decide⟩ ⟨12, 1, 0, 692794, 311061, 1, 65536⟩
    (by decide) selected_cut_40638

theorem selected_cut_40639 : selected 9 ⟨1106019, by decide⟩
    (prefixPartial 12 311062) = some ⟨12, 2, 0, 1106019, 311062, 3141, 65536⟩ := by
  decide +kernel

theorem context_12_311062_1106019 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 311062 ⟨1106019, by decide⟩ :=
  accepted_of_selected 12 311062 ⟨1106019, by decide⟩ ⟨12, 2, 0, 1106019, 311062, 3141, 65536⟩
    (by decide) selected_cut_40639

theorem selected_cut_40640 : selected 9 ⟨1106076, by decide⟩
    (prefixPartial 12 311063) = some ⟨12, 2, 0, 1106076, 311063, 2941, 65536⟩ := by
  decide +kernel

theorem context_12_311063_1106076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 311063 ⟨1106076, by decide⟩ :=
  accepted_of_selected 12 311063 ⟨1106076, by decide⟩ ⟨12, 2, 0, 1106076, 311063, 2941, 65536⟩
    (by decide) selected_cut_40640

theorem unmarked_context_11_77765_1106077 : frontier 10 ⟨1106077, by decide⟩
    (prefixCache 11 77765) (prefixPartial 11 77765) = false := by
  decide +kernel

theorem node_context_11_77765_1106077 : EJMOriginalGlobalDAGData.nodes 10 ⟨1106077, by decide⟩ =
    .split (coordinate 11) (![⟨26677, by decide⟩,⟨692794, by decide⟩,⟨1106019, by decide⟩,⟨1106076, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77765_1106077 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77765 ⟨1106077, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77765
    ⟨1106077, by decide⟩ (by decide) (![⟨26677, by decide⟩,⟨692794, by decide⟩,⟨1106019, by decide⟩,⟨1106076, by decide⟩]) unmarked_context_11_77765_1106077 node_context_11_77765_1106077
  intro a
  fin_cases a
  · exact context_12_311060_26677
  · exact context_12_311061_692794
  · exact context_12_311062_1106019
  · exact context_12_311063_1106076

theorem selected_cut_40641 : selected 9 ⟨26677, by decide⟩
    (prefixPartial 12 311064) = some ⟨12, 1, 0, 26677, 311064, 1, 65536⟩ := by
  decide +kernel

theorem context_12_311064_26677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 311064 ⟨26677, by decide⟩ :=
  accepted_of_selected 12 311064 ⟨26677, by decide⟩ ⟨12, 1, 0, 26677, 311064, 1, 65536⟩
    (by decide) selected_cut_40641

theorem selected_cut_40642 : selected 9 ⟨1106138, by decide⟩
    (prefixPartial 12 311065) = some ⟨12, 2, 0, 1106138, 311065, 3209, 65536⟩ := by
  decide +kernel

theorem context_12_311065_1106138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 311065 ⟨1106138, by decide⟩ :=
  accepted_of_selected 12 311065 ⟨1106138, by decide⟩ ⟨12, 2, 0, 1106138, 311065, 3209, 65536⟩
    (by decide) selected_cut_40642

theorem selected_cut_40643 : selected 9 ⟨3161, by decide⟩
    (prefixPartial 12 311066) = some ⟨12, 1, 0, 3161, 311066, 1, 65536⟩ := by
  decide +kernel

theorem context_12_311066_3161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 311066 ⟨3161, by decide⟩ :=
  accepted_of_selected 12 311066 ⟨3161, by decide⟩ ⟨12, 1, 0, 3161, 311066, 1, 65536⟩
    (by decide) selected_cut_40643

theorem selected_cut_40644 : selected 9 ⟨1106196, by decide⟩
    (prefixPartial 12 311067) = some ⟨12, 2, 0, 1106196, 311067, 2969, 65536⟩ := by
  decide +kernel

theorem context_12_311067_1106196 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 311067 ⟨1106196, by decide⟩ :=
  accepted_of_selected 12 311067 ⟨1106196, by decide⟩ ⟨12, 2, 0, 1106196, 311067, 2969, 65536⟩
    (by decide) selected_cut_40644

theorem unmarked_context_11_77766_1106197 : frontier 10 ⟨1106197, by decide⟩
    (prefixCache 11 77766) (prefixPartial 11 77766) = false := by
  decide +kernel

theorem node_context_11_77766_1106197 : EJMOriginalGlobalDAGData.nodes 10 ⟨1106197, by decide⟩ =
    .split (coordinate 11) (![⟨26677, by decide⟩,⟨1106138, by decide⟩,⟨3161, by decide⟩,⟨1106196, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77766_1106197 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77766 ⟨1106197, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77766
    ⟨1106197, by decide⟩ (by decide) (![⟨26677, by decide⟩,⟨1106138, by decide⟩,⟨3161, by decide⟩,⟨1106196, by decide⟩]) unmarked_context_11_77766_1106197 node_context_11_77766_1106197
  intro a
  fin_cases a
  · exact context_12_311064_26677
  · exact context_12_311065_1106138
  · exact context_12_311066_3161
  · exact context_12_311067_1106196

theorem selected_cut_40645 : selected 9 ⟨26677, by decide⟩
    (prefixPartial 12 311068) = some ⟨12, 1, 0, 26677, 311068, 1, 65536⟩ := by
  decide +kernel

theorem context_12_311068_26677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 311068 ⟨26677, by decide⟩ :=
  accepted_of_selected 12 311068 ⟨26677, by decide⟩ ⟨12, 1, 0, 26677, 311068, 1, 65536⟩
    (by decide) selected_cut_40645

theorem selected_cut_40646 : selected 9 ⟨1106251, by decide⟩
    (prefixPartial 12 311069) = some ⟨12, 2, 0, 1106251, 311069, 2829, 65536⟩ := by
  decide +kernel

theorem context_12_311069_1106251 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 311069 ⟨1106251, by decide⟩ :=
  accepted_of_selected 12 311069 ⟨1106251, by decide⟩ ⟨12, 2, 0, 1106251, 311069, 2829, 65536⟩
    (by decide) selected_cut_40646

theorem selected_cut_40647 : selected 9 ⟨1106285, by decide⟩
    (prefixPartial 12 311070) = some ⟨12, 2, 0, 1106285, 311070, 1509, 65536⟩ := by
  decide +kernel

theorem context_12_311070_1106285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 311070 ⟨1106285, by decide⟩ :=
  accepted_of_selected 12 311070 ⟨1106285, by decide⟩ ⟨12, 2, 0, 1106285, 311070, 1509, 65536⟩
    (by decide) selected_cut_40647

theorem selected_cut_40648 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 311071) = some ⟨12, 1, 0, 903806, 311071, 1, 65536⟩ := by
  decide +kernel

theorem context_12_311071_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 311071 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 311071 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 311071, 1, 65536⟩
    (by decide) selected_cut_40648

theorem unmarked_context_11_77767_1106286 : frontier 10 ⟨1106286, by decide⟩
    (prefixCache 11 77767) (prefixPartial 11 77767) = false := by
  decide +kernel

theorem node_context_11_77767_1106286 : EJMOriginalGlobalDAGData.nodes 10 ⟨1106286, by decide⟩ =
    .split (coordinate 11) (![⟨26677, by decide⟩,⟨1106251, by decide⟩,⟨1106285, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77767_1106286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77767 ⟨1106286, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77767
    ⟨1106286, by decide⟩ (by decide) (![⟨26677, by decide⟩,⟨1106251, by decide⟩,⟨1106285, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_77767_1106286 node_context_11_77767_1106286
  intro a
  fin_cases a
  · exact context_12_311068_26677
  · exact context_12_311069_1106251
  · exact context_12_311070_1106285
  · exact context_12_311071_903806

theorem unmarked_context_10_19441_1106287 : frontier 11 ⟨1106287, by decide⟩
    (prefixCache 10 19441) (prefixPartial 10 19441) = false := by
  decide +kernel

theorem node_context_10_19441_1106287 : EJMOriginalGlobalDAGData.nodes 11 ⟨1106287, by decide⟩ =
    .split (coordinate 10) (![⟨1105966, by decide⟩,⟨1106077, by decide⟩,⟨1106197, by decide⟩,⟨1106286, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19441_1106287 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19441 ⟨1106287, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19441
    ⟨1106287, by decide⟩ (by decide) (![⟨1105966, by decide⟩,⟨1106077, by decide⟩,⟨1106197, by decide⟩,⟨1106286, by decide⟩]) unmarked_context_10_19441_1106287 node_context_10_19441_1106287
  intro a
  fin_cases a
  · exact context_11_77764_1105966
  · exact context_11_77765_1106077
  · exact context_11_77766_1106197
  · exact context_11_77767_1106286

theorem selected_cut_40649 : selected 10 ⟨1106358, by decide⟩
    (prefixPartial 11 77768) = some ⟨11, 2, 0, 1106358, 77768, 3949, 262144⟩ := by
  decide +kernel

theorem context_11_77768_1106358 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77768 ⟨1106358, by decide⟩ :=
  accepted_of_selected 11 77768 ⟨1106358, by decide⟩ ⟨11, 2, 0, 1106358, 77768, 3949, 262144⟩
    (by decide) selected_cut_40649

theorem selected_cut_40650 : selected 9 ⟨26677, by decide⟩
    (prefixPartial 12 311076) = some ⟨12, 1, 0, 26677, 311076, 1, 65536⟩ := by
  decide +kernel

theorem context_12_311076_26677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 311076 ⟨26677, by decide⟩ :=
  accepted_of_selected 12 311076 ⟨26677, by decide⟩ ⟨12, 1, 0, 26677, 311076, 1, 65536⟩
    (by decide) selected_cut_40650

theorem selected_cut_40651 : selected 9 ⟨1106408, by decide⟩
    (prefixPartial 12 311077) = some ⟨12, 2, 0, 1106408, 311077, 3033, 65536⟩ := by
  decide +kernel

theorem context_12_311077_1106408 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 311077 ⟨1106408, by decide⟩ :=
  accepted_of_selected 12 311077 ⟨1106408, by decide⟩ ⟨12, 2, 0, 1106408, 311077, 3033, 65536⟩
    (by decide) selected_cut_40651

theorem selected_cut_40652 : selected 9 ⟨26677, by decide⟩
    (prefixPartial 12 311078) = some ⟨12, 1, 0, 26677, 311078, 1, 65536⟩ := by
  decide +kernel

theorem context_12_311078_26677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 311078 ⟨26677, by decide⟩ :=
  accepted_of_selected 12 311078 ⟨26677, by decide⟩ ⟨12, 1, 0, 26677, 311078, 1, 65536⟩
    (by decide) selected_cut_40652

theorem selected_cut_40653 : selected 9 ⟨1106452, by decide⟩
    (prefixPartial 12 311079) = some ⟨12, 2, 0, 1106452, 311079, 2613, 65536⟩ := by
  decide +kernel

theorem context_12_311079_1106452 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 311079 ⟨1106452, by decide⟩ :=
  accepted_of_selected 12 311079 ⟨1106452, by decide⟩ ⟨12, 2, 0, 1106452, 311079, 2613, 65536⟩
    (by decide) selected_cut_40653

theorem unmarked_context_11_77769_1106453 : frontier 10 ⟨1106453, by decide⟩
    (prefixCache 11 77769) (prefixPartial 11 77769) = false := by
  decide +kernel

theorem node_context_11_77769_1106453 : EJMOriginalGlobalDAGData.nodes 10 ⟨1106453, by decide⟩ =
    .split (coordinate 11) (![⟨26677, by decide⟩,⟨1106408, by decide⟩,⟨26677, by decide⟩,⟨1106452, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77769_1106453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77769 ⟨1106453, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77769
    ⟨1106453, by decide⟩ (by decide) (![⟨26677, by decide⟩,⟨1106408, by decide⟩,⟨26677, by decide⟩,⟨1106452, by decide⟩]) unmarked_context_11_77769_1106453 node_context_11_77769_1106453
  intro a
  fin_cases a
  · exact context_12_311076_26677
  · exact context_12_311077_1106408
  · exact context_12_311078_26677
  · exact context_12_311079_1106452

theorem selected_cut_40654 : selected 10 ⟨1106497, by decide⟩
    (prefixPartial 11 77770) = some ⟨11, 2, 0, 1106497, 77770, 2513, 262144⟩ := by
  decide +kernel

theorem context_11_77770_1106497 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77770 ⟨1106497, by decide⟩ :=
  accepted_of_selected 11 77770 ⟨1106497, by decide⟩ ⟨11, 2, 0, 1106497, 77770, 2513, 262144⟩
    (by decide) selected_cut_40654

theorem selected_cut_40655 : selected 10 ⟨1106527, by decide⟩
    (prefixPartial 11 77771) = some ⟨11, 2, 0, 1106527, 77771, 1529, 262144⟩ := by
  decide +kernel

theorem context_11_77771_1106527 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77771 ⟨1106527, by decide⟩ :=
  accepted_of_selected 11 77771 ⟨1106527, by decide⟩ ⟨11, 2, 0, 1106527, 77771, 1529, 262144⟩
    (by decide) selected_cut_40655

theorem unmarked_context_10_19442_1106528 : frontier 11 ⟨1106528, by decide⟩
    (prefixCache 10 19442) (prefixPartial 10 19442) = false := by
  decide +kernel

theorem node_context_10_19442_1106528 : EJMOriginalGlobalDAGData.nodes 11 ⟨1106528, by decide⟩ =
    .split (coordinate 10) (![⟨1106358, by decide⟩,⟨1106453, by decide⟩,⟨1106497, by decide⟩,⟨1106527, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19442_1106528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19442 ⟨1106528, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19442
    ⟨1106528, by decide⟩ (by decide) (![⟨1106358, by decide⟩,⟨1106453, by decide⟩,⟨1106497, by decide⟩,⟨1106527, by decide⟩]) unmarked_context_10_19442_1106528 node_context_10_19442_1106528
  intro a
  fin_cases a
  · exact context_11_77768_1106358
  · exact context_11_77769_1106453
  · exact context_11_77770_1106497
  · exact context_11_77771_1106527

theorem selected_cut_40656 : selected 11 ⟨1106598, by decide⟩
    (prefixPartial 10 19443) = some ⟨10, 2, 0, 1106598, 19443, 3305, 1048576⟩ := by
  decide +kernel

theorem context_10_19443_1106598 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19443 ⟨1106598, by decide⟩ :=
  accepted_of_selected 10 19443 ⟨1106598, by decide⟩ ⟨10, 2, 0, 1106598, 19443, 3305, 1048576⟩
    (by decide) selected_cut_40656

theorem unmarked_context_9_4860_1106599 : frontier 12 ⟨1106599, by decide⟩
    (prefixCache 9 4860) (prefixPartial 9 4860) = false := by
  decide +kernel

theorem node_context_9_4860_1106599 : EJMOriginalGlobalDAGData.nodes 12 ⟨1106599, by decide⟩ =
    .split (coordinate 9) (![⟨1105807, by decide⟩,⟨1106287, by decide⟩,⟨1106528, by decide⟩,⟨1106598, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4860_1106599 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4860 ⟨1106599, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4860
    ⟨1106599, by decide⟩ (by decide) (![⟨1105807, by decide⟩,⟨1106287, by decide⟩,⟨1106528, by decide⟩,⟨1106598, by decide⟩]) unmarked_context_9_4860_1106599 node_context_9_4860_1106599
  intro a
  fin_cases a
  · exact context_10_19440_1105807
  · exact context_10_19441_1106287
  · exact context_10_19442_1106528
  · exact context_10_19443_1106598

theorem selected_cut_40657 : selected 9 ⟨1051681, by decide⟩
    (prefixPartial 12 311104) = some ⟨12, 1, 0, 1051681, 311104, 1, 65536⟩ := by
  decide +kernel

theorem context_12_311104_1051681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 311104 ⟨1051681, by decide⟩ :=
  accepted_of_selected 12 311104 ⟨1051681, by decide⟩ ⟨12, 1, 0, 1051681, 311104, 1, 65536⟩
    (by decide) selected_cut_40657

theorem selected_cut_40658 : selected 9 ⟨1106639, by decide⟩
    (prefixPartial 12 311105) = some ⟨12, 2, 0, 1106639, 311105, 2613, 65536⟩ := by
  decide +kernel

theorem context_12_311105_1106639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 311105 ⟨1106639, by decide⟩ :=
  accepted_of_selected 12 311105 ⟨1106639, by decide⟩ ⟨12, 2, 0, 1106639, 311105, 2613, 65536⟩
    (by decide) selected_cut_40658

theorem selected_cut_40659 : selected 9 ⟨1106678, by decide⟩
    (prefixPartial 12 311106) = some ⟨12, 2, 0, 1106678, 311106, 2617, 65536⟩ := by
  decide +kernel

theorem context_12_311106_1106678 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 311106 ⟨1106678, by decide⟩ :=
  accepted_of_selected 12 311106 ⟨1106678, by decide⟩ ⟨12, 2, 0, 1106678, 311106, 2617, 65536⟩
    (by decide) selected_cut_40659

theorem selected_cut_40660 : selected 9 ⟨1106715, by decide⟩
    (prefixPartial 12 311107) = some ⟨12, 2, 0, 1106715, 311107, 2301, 65536⟩ := by
  decide +kernel

theorem context_12_311107_1106715 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 311107 ⟨1106715, by decide⟩ :=
  accepted_of_selected 12 311107 ⟨1106715, by decide⟩ ⟨12, 2, 0, 1106715, 311107, 2301, 65536⟩
    (by decide) selected_cut_40660

theorem unmarked_context_11_77776_1106716 : frontier 10 ⟨1106716, by decide⟩
    (prefixCache 11 77776) (prefixPartial 11 77776) = false := by
  decide +kernel

theorem node_context_11_77776_1106716 : EJMOriginalGlobalDAGData.nodes 10 ⟨1106716, by decide⟩ =
    .split (coordinate 11) (![⟨1051681, by decide⟩,⟨1106639, by decide⟩,⟨1106678, by decide⟩,⟨1106715, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77776_1106716 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77776 ⟨1106716, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77776
    ⟨1106716, by decide⟩ (by decide) (![⟨1051681, by decide⟩,⟨1106639, by decide⟩,⟨1106678, by decide⟩,⟨1106715, by decide⟩]) unmarked_context_11_77776_1106716 node_context_11_77776_1106716
  intro a
  fin_cases a
  · exact context_12_311104_1051681
  · exact context_12_311105_1106639
  · exact context_12_311106_1106678
  · exact context_12_311107_1106715

theorem selected_cut_40661 : selected 9 ⟨1106774, by decide⟩
    (prefixPartial 12 311108) = some ⟨12, 2, 0, 1106774, 311108, 3045, 65536⟩ := by
  decide +kernel

theorem context_12_311108_1106774 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 311108 ⟨1106774, by decide⟩ :=
  accepted_of_selected 12 311108 ⟨1106774, by decide⟩ ⟨12, 2, 0, 1106774, 311108, 3045, 65536⟩
    (by decide) selected_cut_40661

theorem selected_cut_40662 : selected 9 ⟨1025817, by decide⟩
    (prefixPartial 12 311109) = some ⟨12, 1, 0, 1025817, 311109, 1, 65536⟩ := by
  decide +kernel

theorem context_12_311109_1025817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 311109 ⟨1025817, by decide⟩ :=
  accepted_of_selected 12 311109 ⟨1025817, by decide⟩ ⟨12, 1, 0, 1025817, 311109, 1, 65536⟩
    (by decide) selected_cut_40662

theorem selected_cut_40663 : selected 9 ⟨1106815, by decide⟩
    (prefixPartial 12 311110) = some ⟨12, 2, 0, 1106815, 311110, 2581, 65536⟩ := by
  decide +kernel

theorem context_12_311110_1106815 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 311110 ⟨1106815, by decide⟩ :=
  accepted_of_selected 12 311110 ⟨1106815, by decide⟩ ⟨12, 2, 0, 1106815, 311110, 2581, 65536⟩
    (by decide) selected_cut_40663

theorem selected_cut_40664 : selected 9 ⟨1106860, by decide⟩
    (prefixPartial 12 311111) = some ⟨12, 2, 0, 1106860, 311111, 2465, 65536⟩ := by
  decide +kernel

theorem context_12_311111_1106860 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 311111 ⟨1106860, by decide⟩ :=
  accepted_of_selected 12 311111 ⟨1106860, by decide⟩ ⟨12, 2, 0, 1106860, 311111, 2465, 65536⟩
    (by decide) selected_cut_40664

theorem unmarked_context_11_77777_1106861 : frontier 10 ⟨1106861, by decide⟩
    (prefixCache 11 77777) (prefixPartial 11 77777) = false := by
  decide +kernel

theorem node_context_11_77777_1106861 : EJMOriginalGlobalDAGData.nodes 10 ⟨1106861, by decide⟩ =
    .split (coordinate 11) (![⟨1106774, by decide⟩,⟨1025817, by decide⟩,⟨1106815, by decide⟩,⟨1106860, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77777_1106861 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77777 ⟨1106861, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77777
    ⟨1106861, by decide⟩ (by decide) (![⟨1106774, by decide⟩,⟨1025817, by decide⟩,⟨1106815, by decide⟩,⟨1106860, by decide⟩]) unmarked_context_11_77777_1106861 node_context_11_77777_1106861
  intro a
  fin_cases a
  · exact context_12_311108_1106774
  · exact context_12_311109_1025817
  · exact context_12_311110_1106815
  · exact context_12_311111_1106860

theorem selected_cut_40665 : selected 9 ⟨1106917, by decide⟩
    (prefixPartial 12 311112) = some ⟨12, 2, 0, 1106917, 311112, 2781, 65536⟩ := by
  decide +kernel

theorem context_12_311112_1106917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 311112 ⟨1106917, by decide⟩ :=
  accepted_of_selected 12 311112 ⟨1106917, by decide⟩ ⟨12, 2, 0, 1106917, 311112, 2781, 65536⟩
    (by decide) selected_cut_40665

theorem selected_cut_40666 : selected 9 ⟨1106964, by decide⟩
    (prefixPartial 12 311113) = some ⟨12, 2, 0, 1106964, 311113, 2381, 65536⟩ := by
  decide +kernel

theorem context_12_311113_1106964 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 311113 ⟨1106964, by decide⟩ :=
  accepted_of_selected 12 311113 ⟨1106964, by decide⟩ ⟨12, 2, 0, 1106964, 311113, 2381, 65536⟩
    (by decide) selected_cut_40666

theorem selected_cut_40667 : selected 9 ⟨1107004, by decide⟩
    (prefixPartial 12 311114) = some ⟨12, 2, 0, 1107004, 311114, 2277, 65536⟩ := by
  decide +kernel

theorem context_12_311114_1107004 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 311114 ⟨1107004, by decide⟩ :=
  accepted_of_selected 12 311114 ⟨1107004, by decide⟩ ⟨12, 2, 0, 1107004, 311114, 2277, 65536⟩
    (by decide) selected_cut_40667

theorem selected_cut_40668 : selected 9 ⟨1107045, by decide⟩
    (prefixPartial 12 311115) = some ⟨12, 2, 0, 1107045, 311115, 2249, 65536⟩ := by
  decide +kernel

theorem context_12_311115_1107045 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 311115 ⟨1107045, by decide⟩ :=
  accepted_of_selected 12 311115 ⟨1107045, by decide⟩ ⟨12, 2, 0, 1107045, 311115, 2249, 65536⟩
    (by decide) selected_cut_40668

theorem unmarked_context_11_77778_1107046 : frontier 10 ⟨1107046, by decide⟩
    (prefixCache 11 77778) (prefixPartial 11 77778) = false := by
  decide +kernel

theorem node_context_11_77778_1107046 : EJMOriginalGlobalDAGData.nodes 10 ⟨1107046, by decide⟩ =
    .split (coordinate 11) (![⟨1106917, by decide⟩,⟨1106964, by decide⟩,⟨1107004, by decide⟩,⟨1107045, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77778_1107046 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77778 ⟨1107046, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77778
    ⟨1107046, by decide⟩ (by decide) (![⟨1106917, by decide⟩,⟨1106964, by decide⟩,⟨1107004, by decide⟩,⟨1107045, by decide⟩]) unmarked_context_11_77778_1107046 node_context_11_77778_1107046
  intro a
  fin_cases a
  · exact context_12_311112_1106917
  · exact context_12_311113_1106964
  · exact context_12_311114_1107004
  · exact context_12_311115_1107045

theorem selected_cut_40669 : selected 9 ⟨1107098, by decide⟩
    (prefixPartial 12 311116) = some ⟨12, 2, 0, 1107098, 311116, 2461, 65536⟩ := by
  decide +kernel

theorem context_12_311116_1107098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 311116 ⟨1107098, by decide⟩ :=
  accepted_of_selected 12 311116 ⟨1107098, by decide⟩ ⟨12, 2, 0, 1107098, 311116, 2461, 65536⟩
    (by decide) selected_cut_40669

theorem selected_cut_40670 : selected 9 ⟨1107133, by decide⟩
    (prefixPartial 12 311117) = some ⟨12, 2, 0, 1107133, 311117, 2037, 65536⟩ := by
  decide +kernel

theorem context_12_311117_1107133 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 311117 ⟨1107133, by decide⟩ :=
  accepted_of_selected 12 311117 ⟨1107133, by decide⟩ ⟨12, 2, 0, 1107133, 311117, 2037, 65536⟩
    (by decide) selected_cut_40670

theorem selected_cut_40671 : selected 9 ⟨1107163, by decide⟩
    (prefixPartial 12 311118) = some ⟨12, 2, 0, 1107163, 311118, 1989, 65536⟩ := by
  decide +kernel

theorem context_12_311118_1107163 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 311118 ⟨1107163, by decide⟩ :=
  accepted_of_selected 12 311118 ⟨1107163, by decide⟩ ⟨12, 2, 0, 1107163, 311118, 1989, 65536⟩
    (by decide) selected_cut_40671

theorem selected_cut_40672 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 311119) = some ⟨12, 1, 0, 903806, 311119, 1, 65536⟩ := by
  decide +kernel

theorem context_12_311119_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 311119 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 311119 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 311119, 1, 65536⟩
    (by decide) selected_cut_40672

theorem unmarked_context_11_77779_1107164 : frontier 10 ⟨1107164, by decide⟩
    (prefixCache 11 77779) (prefixPartial 11 77779) = false := by
  decide +kernel

theorem node_context_11_77779_1107164 : EJMOriginalGlobalDAGData.nodes 10 ⟨1107164, by decide⟩ =
    .split (coordinate 11) (![⟨1107098, by decide⟩,⟨1107133, by decide⟩,⟨1107163, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77779_1107164 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77779 ⟨1107164, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77779
    ⟨1107164, by decide⟩ (by decide) (![⟨1107098, by decide⟩,⟨1107133, by decide⟩,⟨1107163, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_77779_1107164 node_context_11_77779_1107164
  intro a
  fin_cases a
  · exact context_12_311116_1107098
  · exact context_12_311117_1107133
  · exact context_12_311118_1107163
  · exact context_12_311119_903806

theorem unmarked_context_10_19444_1107165 : frontier 11 ⟨1107165, by decide⟩
    (prefixCache 10 19444) (prefixPartial 10 19444) = false := by
  decide +kernel

theorem node_context_10_19444_1107165 : EJMOriginalGlobalDAGData.nodes 11 ⟨1107165, by decide⟩ =
    .split (coordinate 10) (![⟨1106716, by decide⟩,⟨1106861, by decide⟩,⟨1107046, by decide⟩,⟨1107164, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19444_1107165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19444 ⟨1107165, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19444
    ⟨1107165, by decide⟩ (by decide) (![⟨1106716, by decide⟩,⟨1106861, by decide⟩,⟨1107046, by decide⟩,⟨1107164, by decide⟩]) unmarked_context_10_19444_1107165 node_context_10_19444_1107165
  intro a
  fin_cases a
  · exact context_11_77776_1106716
  · exact context_11_77777_1106861
  · exact context_11_77778_1107046
  · exact context_11_77779_1107164

theorem selected_cut_40673 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 19445) = some ⟨10, 1, 0, 893098, 19445, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_19445_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19445 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 19445 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 19445, 1, 1048576⟩
    (by decide) selected_cut_40673

theorem selected_cut_40674 : selected 9 ⟨1107210, by decide⟩
    (prefixPartial 12 311136) = some ⟨12, 2, 0, 1107210, 311136, 1657, 65536⟩ := by
  decide +kernel

theorem context_12_311136_1107210 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 311136 ⟨1107210, by decide⟩ :=
  accepted_of_selected 12 311136 ⟨1107210, by decide⟩ ⟨12, 2, 0, 1107210, 311136, 1657, 65536⟩
    (by decide) selected_cut_40674

theorem selected_cut_40675 : selected 9 ⟨1107243, by decide⟩
    (prefixPartial 12 311137) = some ⟨12, 2, 0, 1107243, 311137, 1765, 65536⟩ := by
  decide +kernel

theorem context_12_311137_1107243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 311137 ⟨1107243, by decide⟩ :=
  accepted_of_selected 12 311137 ⟨1107243, by decide⟩ ⟨12, 2, 0, 1107243, 311137, 1765, 65536⟩
    (by decide) selected_cut_40675

theorem selected_cut_40676 : selected 9 ⟨1107285, by decide⟩
    (prefixPartial 12 311138) = some ⟨12, 2, 0, 1107285, 311138, 1741, 65536⟩ := by
  decide +kernel

theorem context_12_311138_1107285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 311138 ⟨1107285, by decide⟩ :=
  accepted_of_selected 12 311138 ⟨1107285, by decide⟩ ⟨12, 2, 0, 1107285, 311138, 1741, 65536⟩
    (by decide) selected_cut_40676

theorem selected_cut_40677 : selected 9 ⟨1107313, by decide⟩
    (prefixPartial 12 311139) = some ⟨12, 2, 0, 1107313, 311139, 1505, 65536⟩ := by
  decide +kernel

theorem context_12_311139_1107313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 311139 ⟨1107313, by decide⟩ :=
  accepted_of_selected 12 311139 ⟨1107313, by decide⟩ ⟨12, 2, 0, 1107313, 311139, 1505, 65536⟩
    (by decide) selected_cut_40677

theorem unmarked_context_11_77784_1107314 : frontier 10 ⟨1107314, by decide⟩
    (prefixCache 11 77784) (prefixPartial 11 77784) = false := by
  decide +kernel

theorem node_context_11_77784_1107314 : EJMOriginalGlobalDAGData.nodes 10 ⟨1107314, by decide⟩ =
    .split (coordinate 11) (![⟨1107210, by decide⟩,⟨1107243, by decide⟩,⟨1107285, by decide⟩,⟨1107313, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77784_1107314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77784 ⟨1107314, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77784
    ⟨1107314, by decide⟩ (by decide) (![⟨1107210, by decide⟩,⟨1107243, by decide⟩,⟨1107285, by decide⟩,⟨1107313, by decide⟩]) unmarked_context_11_77784_1107314 node_context_11_77784_1107314
  intro a
  fin_cases a
  · exact context_12_311136_1107210
  · exact context_12_311137_1107243
  · exact context_12_311138_1107285
  · exact context_12_311139_1107313

theorem selected_cut_40678 : selected 9 ⟨1107349, by decide⟩
    (prefixPartial 12 311140) = some ⟨12, 2, 0, 1107349, 311140, 1557, 65536⟩ := by
  decide +kernel

theorem context_12_311140_1107349 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 311140 ⟨1107349, by decide⟩ :=
  accepted_of_selected 12 311140 ⟨1107349, by decide⟩ ⟨12, 2, 0, 1107349, 311140, 1557, 65536⟩
    (by decide) selected_cut_40678

theorem selected_cut_40679 : selected 9 ⟨1084018, by decide⟩
    (prefixPartial 12 311141) = some ⟨12, 1, 0, 1084018, 311141, 1, 65536⟩ := by
  decide +kernel

theorem context_12_311141_1084018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 311141 ⟨1084018, by decide⟩ :=
  accepted_of_selected 12 311141 ⟨1084018, by decide⟩ ⟨12, 1, 0, 1084018, 311141, 1, 65536⟩
    (by decide) selected_cut_40679

theorem selected_cut_40680 : selected 9 ⟨1107379, by decide⟩
    (prefixPartial 12 311142) = some ⟨12, 2, 0, 1107379, 311142, 1617, 65536⟩ := by
  decide +kernel

theorem context_12_311142_1107379 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 311142 ⟨1107379, by decide⟩ :=
  accepted_of_selected 12 311142 ⟨1107379, by decide⟩ ⟨12, 2, 0, 1107379, 311142, 1617, 65536⟩
    (by decide) selected_cut_40680

theorem selected_cut_40681 : selected 9 ⟨1107407, by decide⟩
    (prefixPartial 12 311143) = some ⟨12, 2, 0, 1107407, 311143, 1513, 65536⟩ := by
  decide +kernel

theorem context_12_311143_1107407 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 311143 ⟨1107407, by decide⟩ :=
  accepted_of_selected 12 311143 ⟨1107407, by decide⟩ ⟨12, 2, 0, 1107407, 311143, 1513, 65536⟩
    (by decide) selected_cut_40681

theorem unmarked_context_11_77785_1107408 : frontier 10 ⟨1107408, by decide⟩
    (prefixCache 11 77785) (prefixPartial 11 77785) = false := by
  decide +kernel

theorem node_context_11_77785_1107408 : EJMOriginalGlobalDAGData.nodes 10 ⟨1107408, by decide⟩ =
    .split (coordinate 11) (![⟨1107349, by decide⟩,⟨1084018, by decide⟩,⟨1107379, by decide⟩,⟨1107407, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77785_1107408 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77785 ⟨1107408, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77785
    ⟨1107408, by decide⟩ (by decide) (![⟨1107349, by decide⟩,⟨1084018, by decide⟩,⟨1107379, by decide⟩,⟨1107407, by decide⟩]) unmarked_context_11_77785_1107408 node_context_11_77785_1107408
  intro a
  fin_cases a
  · exact context_12_311140_1107349
  · exact context_12_311141_1084018
  · exact context_12_311142_1107379
  · exact context_12_311143_1107407

theorem selected_cut_40682 : selected 10 ⟨1107484, by decide⟩
    (prefixPartial 11 77786) = some ⟨11, 2, 0, 1107484, 77786, 3985, 262144⟩ := by
  decide +kernel

theorem context_11_77786_1107484 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77786 ⟨1107484, by decide⟩ :=
  accepted_of_selected 11 77786 ⟨1107484, by decide⟩ ⟨11, 2, 0, 1107484, 77786, 3985, 262144⟩
    (by decide) selected_cut_40682

theorem selected_cut_40683 : selected 10 ⟨1107546, by decide⟩
    (prefixPartial 11 77787) = some ⟨11, 2, 0, 1107546, 77787, 3453, 262144⟩ := by
  decide +kernel

theorem context_11_77787_1107546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77787 ⟨1107546, by decide⟩ :=
  accepted_of_selected 11 77787 ⟨1107546, by decide⟩ ⟨11, 2, 0, 1107546, 77787, 3453, 262144⟩
    (by decide) selected_cut_40683

theorem unmarked_context_10_19446_1107547 : frontier 11 ⟨1107547, by decide⟩
    (prefixCache 10 19446) (prefixPartial 10 19446) = false := by
  decide +kernel

theorem node_context_10_19446_1107547 : EJMOriginalGlobalDAGData.nodes 11 ⟨1107547, by decide⟩ =
    .split (coordinate 10) (![⟨1107314, by decide⟩,⟨1107408, by decide⟩,⟨1107484, by decide⟩,⟨1107546, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19446_1107547 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19446 ⟨1107547, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19446
    ⟨1107547, by decide⟩ (by decide) (![⟨1107314, by decide⟩,⟨1107408, by decide⟩,⟨1107484, by decide⟩,⟨1107546, by decide⟩]) unmarked_context_10_19446_1107547 node_context_10_19446_1107547
  intro a
  fin_cases a
  · exact context_11_77784_1107314
  · exact context_11_77785_1107408
  · exact context_11_77786_1107484
  · exact context_11_77787_1107546

theorem selected_cut_40684 : selected 10 ⟨1107632, by decide⟩
    (prefixPartial 11 77788) = some ⟨11, 2, 0, 1107632, 77788, 3741, 262144⟩ := by
  decide +kernel

theorem context_11_77788_1107632 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77788 ⟨1107632, by decide⟩ :=
  accepted_of_selected 11 77788 ⟨1107632, by decide⟩ ⟨11, 2, 0, 1107632, 77788, 3741, 262144⟩
    (by decide) selected_cut_40684

theorem selected_cut_40685 : selected 10 ⟨1107690, by decide⟩
    (prefixPartial 11 77789) = some ⟨11, 2, 0, 1107690, 77789, 2693, 262144⟩ := by
  decide +kernel

theorem context_11_77789_1107690 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77789 ⟨1107690, by decide⟩ :=
  accepted_of_selected 11 77789 ⟨1107690, by decide⟩ ⟨11, 2, 0, 1107690, 77789, 2693, 262144⟩
    (by decide) selected_cut_40685

theorem selected_cut_40686 : selected 10 ⟨1107735, by decide⟩
    (prefixPartial 11 77790) = some ⟨11, 2, 0, 1107735, 77790, 2805, 262144⟩ := by
  decide +kernel

theorem context_11_77790_1107735 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77790 ⟨1107735, by decide⟩ :=
  accepted_of_selected 11 77790 ⟨1107735, by decide⟩ ⟨11, 2, 0, 1107735, 77790, 2805, 262144⟩
    (by decide) selected_cut_40686

theorem selected_cut_40687 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 77791) = some ⟨11, 1, 0, 977886, 77791, 1, 262144⟩ := by
  decide +kernel

theorem context_11_77791_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77791 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 77791 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 77791, 1, 262144⟩
    (by decide) selected_cut_40687

theorem unmarked_context_10_19447_1107736 : frontier 11 ⟨1107736, by decide⟩
    (prefixCache 10 19447) (prefixPartial 10 19447) = false := by
  decide +kernel

theorem node_context_10_19447_1107736 : EJMOriginalGlobalDAGData.nodes 11 ⟨1107736, by decide⟩ =
    .split (coordinate 10) (![⟨1107632, by decide⟩,⟨1107690, by decide⟩,⟨1107735, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19447_1107736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19447 ⟨1107736, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19447
    ⟨1107736, by decide⟩ (by decide) (![⟨1107632, by decide⟩,⟨1107690, by decide⟩,⟨1107735, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_19447_1107736 node_context_10_19447_1107736
  intro a
  fin_cases a
  · exact context_11_77788_1107632
  · exact context_11_77789_1107690
  · exact context_11_77790_1107735
  · exact context_11_77791_977886

theorem unmarked_context_9_4861_1107737 : frontier 12 ⟨1107737, by decide⟩
    (prefixCache 9 4861) (prefixPartial 9 4861) = false := by
  decide +kernel

theorem node_context_9_4861_1107737 : EJMOriginalGlobalDAGData.nodes 12 ⟨1107737, by decide⟩ =
    .split (coordinate 9) (![⟨1107165, by decide⟩,⟨893098, by decide⟩,⟨1107547, by decide⟩,⟨1107736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4861_1107737 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4861 ⟨1107737, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4861
    ⟨1107737, by decide⟩ (by decide) (![⟨1107165, by decide⟩,⟨893098, by decide⟩,⟨1107547, by decide⟩,⟨1107736, by decide⟩]) unmarked_context_9_4861_1107737 node_context_9_4861_1107737
  intro a
  fin_cases a
  · exact context_10_19444_1107165
  · exact context_10_19445_893098
  · exact context_10_19446_1107547
  · exact context_10_19447_1107736

theorem selected_cut_40688 : selected 12 ⟨33466, by decide⟩
    (prefixPartial 9 4862) = some ⟨9, 1, 0, 33466, 4862, 1, 4194304⟩ := by
  decide +kernel

theorem context_9_4862_33466 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4862 ⟨33466, by decide⟩ :=
  accepted_of_selected 9 4862 ⟨33466, by decide⟩ ⟨9, 1, 0, 33466, 4862, 1, 4194304⟩
    (by decide) selected_cut_40688

theorem selected_cut_40689 : selected 10 ⟨1107758, by decide⟩
    (prefixPartial 11 77808) = some ⟨11, 2, 0, 1107758, 77808, 1149, 262144⟩ := by
  decide +kernel

theorem context_11_77808_1107758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77808 ⟨1107758, by decide⟩ :=
  accepted_of_selected 11 77808 ⟨1107758, by decide⟩ ⟨11, 2, 0, 1107758, 77808, 1149, 262144⟩
    (by decide) selected_cut_40689

theorem selected_cut_40690 : selected 10 ⟨1107797, by decide⟩
    (prefixPartial 11 77809) = some ⟨11, 2, 0, 1107797, 77809, 1773, 262144⟩ := by
  decide +kernel

theorem context_11_77809_1107797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77809 ⟨1107797, by decide⟩ :=
  accepted_of_selected 11 77809 ⟨1107797, by decide⟩ ⟨11, 2, 0, 1107797, 77809, 1773, 262144⟩
    (by decide) selected_cut_40690

theorem selected_cut_40691 : selected 10 ⟨1107827, by decide⟩
    (prefixPartial 11 77810) = some ⟨11, 2, 0, 1107827, 77810, 1113, 262144⟩ := by
  decide +kernel

theorem context_11_77810_1107827 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77810 ⟨1107827, by decide⟩ :=
  accepted_of_selected 11 77810 ⟨1107827, by decide⟩ ⟨11, 2, 0, 1107827, 77810, 1113, 262144⟩
    (by decide) selected_cut_40691

theorem selected_cut_40692 : selected 10 ⟨1107849, by decide⟩
    (prefixPartial 11 77811) = some ⟨11, 2, 0, 1107849, 77811, 857, 262144⟩ := by
  decide +kernel

theorem context_11_77811_1107849 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77811 ⟨1107849, by decide⟩ :=
  accepted_of_selected 11 77811 ⟨1107849, by decide⟩ ⟨11, 2, 0, 1107849, 77811, 857, 262144⟩
    (by decide) selected_cut_40692

theorem unmarked_context_10_19452_1107850 : frontier 11 ⟨1107850, by decide⟩
    (prefixCache 10 19452) (prefixPartial 10 19452) = false := by
  decide +kernel

theorem node_context_10_19452_1107850 : EJMOriginalGlobalDAGData.nodes 11 ⟨1107850, by decide⟩ =
    .split (coordinate 10) (![⟨1107758, by decide⟩,⟨1107797, by decide⟩,⟨1107827, by decide⟩,⟨1107849, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19452_1107850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19452 ⟨1107850, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19452
    ⟨1107850, by decide⟩ (by decide) (![⟨1107758, by decide⟩,⟨1107797, by decide⟩,⟨1107827, by decide⟩,⟨1107849, by decide⟩]) unmarked_context_10_19452_1107850 node_context_10_19452_1107850
  intro a
  fin_cases a
  · exact context_11_77808_1107758
  · exact context_11_77809_1107797
  · exact context_11_77810_1107827
  · exact context_11_77811_1107849

theorem selected_cut_40693 : selected 11 ⟨1107929, by decide⟩
    (prefixPartial 10 19453) = some ⟨10, 2, 0, 1107929, 19453, 1709, 1048576⟩ := by
  decide +kernel

theorem context_10_19453_1107929 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19453 ⟨1107929, by decide⟩ :=
  accepted_of_selected 10 19453 ⟨1107929, by decide⟩ ⟨10, 2, 0, 1107929, 19453, 1709, 1048576⟩
    (by decide) selected_cut_40693

theorem selected_cut_40694 : selected 11 ⟨1107966, by decide⟩
    (prefixPartial 10 19454) = some ⟨10, 2, 0, 1107966, 19454, 493, 1048576⟩ := by
  decide +kernel

theorem context_10_19454_1107966 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19454 ⟨1107966, by decide⟩ :=
  accepted_of_selected 10 19454 ⟨1107966, by decide⟩ ⟨10, 2, 0, 1107966, 19454, 493, 1048576⟩
    (by decide) selected_cut_40694

theorem selected_cut_40695 : selected 11 ⟨1107968, by decide⟩
    (prefixPartial 10 19455) = some ⟨10, 2, 0, 1107968, 19455, 17, 1048576⟩ := by
  decide +kernel

theorem context_10_19455_1107968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19455 ⟨1107968, by decide⟩ :=
  accepted_of_selected 10 19455 ⟨1107968, by decide⟩ ⟨10, 2, 0, 1107968, 19455, 17, 1048576⟩
    (by decide) selected_cut_40695

theorem unmarked_context_9_4863_1107969 : frontier 12 ⟨1107969, by decide⟩
    (prefixCache 9 4863) (prefixPartial 9 4863) = false := by
  decide +kernel

theorem node_context_9_4863_1107969 : EJMOriginalGlobalDAGData.nodes 12 ⟨1107969, by decide⟩ =
    .split (coordinate 9) (![⟨1107850, by decide⟩,⟨1107929, by decide⟩,⟨1107966, by decide⟩,⟨1107968, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4863_1107969 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4863 ⟨1107969, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4863
    ⟨1107969, by decide⟩ (by decide) (![⟨1107850, by decide⟩,⟨1107929, by decide⟩,⟨1107966, by decide⟩,⟨1107968, by decide⟩]) unmarked_context_9_4863_1107969 node_context_9_4863_1107969
  intro a
  fin_cases a
  · exact context_10_19452_1107850
  · exact context_10_19453_1107929
  · exact context_10_19454_1107966
  · exact context_10_19455_1107968

theorem unmarked_context_8_1215_1107970 : frontier 13 ⟨1107970, by decide⟩
    (prefixCache 8 1215) (prefixPartial 8 1215) = false := by
  decide +kernel

theorem node_context_8_1215_1107970 : EJMOriginalGlobalDAGData.nodes 13 ⟨1107970, by decide⟩ =
    .split (coordinate 8) (![⟨1106599, by decide⟩,⟨1107737, by decide⟩,⟨33466, by decide⟩,⟨1107969, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1215_1107970 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1215 ⟨1107970, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1215
    ⟨1107970, by decide⟩ (by decide) (![⟨1106599, by decide⟩,⟨1107737, by decide⟩,⟨33466, by decide⟩,⟨1107969, by decide⟩]) unmarked_context_8_1215_1107970 node_context_8_1215_1107970
  intro a
  fin_cases a
  · exact context_9_4860_1106599
  · exact context_9_4861_1107737
  · exact context_9_4862_33466
  · exact context_9_4863_1107969

theorem unmarked_context_7_303_1107971 : frontier 14 ⟨1107971, by decide⟩
    (prefixCache 7 303) (prefixPartial 7 303) = false := by
  decide +kernel

theorem node_context_7_303_1107971 : EJMOriginalGlobalDAGData.nodes 14 ⟨1107971, by decide⟩ =
    .split (coordinate 7) (![⟨979897, by decide⟩,⟨979897, by decide⟩,⟨979897, by decide⟩,⟨1107970, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_303_1107971 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 303 ⟨1107971, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 303
    ⟨1107971, by decide⟩ (by decide) (![⟨979897, by decide⟩,⟨979897, by decide⟩,⟨979897, by decide⟩,⟨1107970, by decide⟩]) unmarked_context_7_303_1107971 node_context_7_303_1107971
  intro a
  fin_cases a
  · exact context_8_1212_979897
  · exact context_8_1213_979897
  · exact context_8_1214_979897
  · exact context_8_1215_1107970

theorem unmarked_context_6_75_1107972 : frontier 15 ⟨1107972, by decide⟩
    (prefixCache 6 75) (prefixPartial 6 75) = false := by
  decide +kernel

theorem node_context_6_75_1107972 : EJMOriginalGlobalDAGData.nodes 15 ⟨1107972, by decide⟩ =
    .split (coordinate 6) (![⟨1085252, by decide⟩,⟨1098370, by decide⟩,⟨1105208, by decide⟩,⟨1107971, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_6_75_1107972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 75 ⟨1107972, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 6 75
    ⟨1107972, by decide⟩ (by decide) (![⟨1085252, by decide⟩,⟨1098370, by decide⟩,⟨1105208, by decide⟩,⟨1107971, by decide⟩]) unmarked_context_6_75_1107972 node_context_6_75_1107972
  intro a
  fin_cases a
  · exact context_7_300_1085252
  · exact context_7_301_1098370
  · exact context_7_302_1105208
  · exact context_7_303_1107971

theorem unmarked_context_5_18_1107973 : frontier 16 ⟨1107973, by decide⟩
    (prefixCache 5 18) (prefixPartial 5 18) = false := by
  decide +kernel

theorem node_context_5_18_1107973 : EJMOriginalGlobalDAGData.nodes 16 ⟨1107973, by decide⟩ =
    .split (coordinate 5) (![⟨984704, by decide⟩,⟨1070117, by decide⟩,⟨1070118, by decide⟩,⟨1107972, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_5_18_1107973 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 5 18 ⟨1107973, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 5 18
    ⟨1107973, by decide⟩ (by decide) (![⟨984704, by decide⟩,⟨1070117, by decide⟩,⟨1070118, by decide⟩,⟨1107972, by decide⟩]) unmarked_context_5_18_1107973 node_context_5_18_1107973
  intro a
  fin_cases a
  · exact context_6_72_984704
  · exact context_6_73_1070117
  · exact context_6_74_1070118
  · exact context_6_75_1107972

theorem selected_cut_40696 : selected 16 ⟨434742, by decide⟩
    (prefixPartial 5 19) = some ⟨5, 1, 0, 434742, 19, 1, 1073741824⟩ := by
  decide +kernel

theorem context_5_19_434742 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 5 19 ⟨434742, by decide⟩ :=
  accepted_of_selected 5 19 ⟨434742, by decide⟩ ⟨5, 1, 0, 434742, 19, 1, 1073741824⟩
    (by decide) selected_cut_40696

theorem unmarked_context_4_4_1107974 : frontier 17 ⟨1107974, by decide⟩
    (prefixCache 4 4) (prefixPartial 4 4) = false := by
  decide +kernel

theorem node_context_4_4_1107974 : EJMOriginalGlobalDAGData.nodes 17 ⟨1107974, by decide⟩ =
    .split (coordinate 4) (![⟨891587, by decide⟩,⟨979896, by decide⟩,⟨1107973, by decide⟩,⟨434742, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_4_4_1107974 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 4 4 ⟨1107974, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 4 4
    ⟨1107974, by decide⟩ (by decide) (![⟨891587, by decide⟩,⟨979896, by decide⟩,⟨1107973, by decide⟩,⟨434742, by decide⟩]) unmarked_context_4_4_1107974 node_context_4_4_1107974
  intro a
  fin_cases a
  · exact context_5_16_891587
  · exact context_5_17_979896
  · exact context_5_18_1107973
  · exact context_5_19_434742

theorem selected_cut_40697 : selected 15 ⟨434744, by decide⟩
    (prefixPartial 6 80) = some ⟨6, 1, 0, 434744, 80, 1, 268435456⟩ := by
  decide +kernel

theorem context_6_80_434744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 80 ⟨434744, by decide⟩ :=
  accepted_of_selected 6 80 ⟨434744, by decide⟩ ⟨6, 1, 0, 434744, 80, 1, 268435456⟩
    (by decide) selected_cut_40697

theorem selected_cut_40698 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 82944) = some ⟨11, 1, 0, 434745, 82944, 1, 262144⟩ := by
  decide +kernel

theorem context_11_82944_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 82944 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 82944 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 82944, 1, 262144⟩
    (by decide) selected_cut_40698

theorem selected_cut_40699 : selected 10 ⟨1108069, by decide⟩
    (prefixPartial 11 82945) = some ⟨11, 2, 0, 1108069, 82945, 2761, 262144⟩ := by
  decide +kernel

theorem context_11_82945_1108069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 82945 ⟨1108069, by decide⟩ :=
  accepted_of_selected 11 82945 ⟨1108069, by decide⟩ ⟨11, 2, 0, 1108069, 82945, 2761, 262144⟩
    (by decide) selected_cut_40699

theorem selected_cut_40700 : selected 10 ⟨1108172, by decide⟩
    (prefixPartial 11 82946) = some ⟨11, 2, 0, 1108172, 82946, 2497, 262144⟩ := by
  decide +kernel

theorem context_11_82946_1108172 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 82946 ⟨1108172, by decide⟩ :=
  accepted_of_selected 11 82946 ⟨1108172, by decide⟩ ⟨11, 2, 0, 1108172, 82946, 2497, 262144⟩
    (by decide) selected_cut_40700

theorem selected_cut_40701 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 82947) = some ⟨11, 1, 0, 1736, 82947, 1, 262144⟩ := by
  decide +kernel

theorem context_11_82947_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 82947 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 82947 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 82947, 1, 262144⟩
    (by decide) selected_cut_40701

theorem unmarked_context_10_20736_1108173 : frontier 11 ⟨1108173, by decide⟩
    (prefixCache 10 20736) (prefixPartial 10 20736) = false := by
  decide +kernel

theorem node_context_10_20736_1108173 : EJMOriginalGlobalDAGData.nodes 11 ⟨1108173, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨1108069, by decide⟩,⟨1108172, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_20736_1108173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20736 ⟨1108173, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 20736
    ⟨1108173, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨1108069, by decide⟩,⟨1108172, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_20736_1108173 node_context_10_20736_1108173
  intro a
  fin_cases a
  · exact context_11_82944_434745
  · exact context_11_82945_1108069
  · exact context_11_82946_1108172
  · exact context_11_82947_1736

theorem selected_cut_40702 : selected 10 ⟨1108255, by decide⟩
    (prefixPartial 11 82948) = some ⟨11, 2, 0, 1108255, 82948, 2813, 262144⟩ := by
  decide +kernel

theorem context_11_82948_1108255 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 82948 ⟨1108255, by decide⟩ :=
  accepted_of_selected 11 82948 ⟨1108255, by decide⟩ ⟨11, 2, 0, 1108255, 82948, 2813, 262144⟩
    (by decide) selected_cut_40702

theorem selected_cut_40703 : selected 10 ⟨1108307, by decide⟩
    (prefixPartial 11 82949) = some ⟨11, 2, 0, 1108307, 82949, 2177, 262144⟩ := by
  decide +kernel

theorem context_11_82949_1108307 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 82949 ⟨1108307, by decide⟩ :=
  accepted_of_selected 11 82949 ⟨1108307, by decide⟩ ⟨11, 2, 0, 1108307, 82949, 2177, 262144⟩
    (by decide) selected_cut_40703

theorem selected_cut_40704 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 331800) = some ⟨12, 1, 0, 1108174, 331800, 1, 65536⟩ := by
  decide +kernel

theorem context_12_331800_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 331800 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 331800 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 331800, 1, 65536⟩
    (by decide) selected_cut_40704

theorem selected_cut_40705 : selected 9 ⟨1108376, by decide⟩
    (prefixPartial 12 331801) = some ⟨12, 2, 0, 1108376, 331801, 2245, 65536⟩ := by
  decide +kernel

theorem context_12_331801_1108376 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 331801 ⟨1108376, by decide⟩ :=
  accepted_of_selected 12 331801 ⟨1108376, by decide⟩ ⟨12, 2, 0, 1108376, 331801, 2245, 65536⟩
    (by decide) selected_cut_40705

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
