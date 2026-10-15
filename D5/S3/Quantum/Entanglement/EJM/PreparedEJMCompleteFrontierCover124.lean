/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover123
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_11907 : selected 8 ⟨318045, by decide⟩
    (prefixPartial 13 103596) = some ⟨13, 2, 0, 318045, 103596, 1217, 16384⟩ := by
  decide +kernel

theorem context_13_103596_318045 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103596 ⟨318045, by decide⟩ :=
  accepted_of_selected 13 103596 ⟨318045, by decide⟩ ⟨13, 2, 0, 318045, 103596, 1217, 16384⟩
    (by decide) selected_cut_11907

theorem selected_cut_11908 : selected 8 ⟨318076, by decide⟩
    (prefixPartial 13 103597) = some ⟨13, 2, 0, 318076, 103597, 2641, 16384⟩ := by
  decide +kernel

theorem context_13_103597_318076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103597 ⟨318076, by decide⟩ :=
  accepted_of_selected 13 103597 ⟨318076, by decide⟩ ⟨13, 2, 0, 318076, 103597, 2641, 16384⟩
    (by decide) selected_cut_11908

theorem selected_cut_11909 : selected 8 ⟨318097, by decide⟩
    (prefixPartial 13 103598) = some ⟨13, 2, 0, 318097, 103598, 1653, 16384⟩ := by
  decide +kernel

theorem context_13_103598_318097 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103598 ⟨318097, by decide⟩ :=
  accepted_of_selected 13 103598 ⟨318097, by decide⟩ ⟨13, 2, 0, 318097, 103598, 1653, 16384⟩
    (by decide) selected_cut_11909

theorem selected_cut_11910 : selected 8 ⟨318104, by decide⟩
    (prefixPartial 13 103599) = some ⟨13, 2, 0, 318104, 103599, 1053, 16384⟩ := by
  decide +kernel

theorem context_13_103599_318104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103599 ⟨318104, by decide⟩ :=
  accepted_of_selected 13 103599 ⟨318104, by decide⟩ ⟨13, 2, 0, 318104, 103599, 1053, 16384⟩
    (by decide) selected_cut_11910

theorem unmarked_context_12_25899_318105 : frontier 9 ⟨318105, by decide⟩
    (prefixCache 12 25899) (prefixPartial 12 25899) = false := by
  decide +kernel

theorem node_context_12_25899_318105 : EJMOriginalGlobalDAGData.nodes 9 ⟨318105, by decide⟩ =
    .split (coordinate 12) (![⟨318045, by decide⟩,⟨318076, by decide⟩,⟨318097, by decide⟩,⟨318104, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25899_318105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25899 ⟨318105, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25899
    ⟨318105, by decide⟩ (by decide) (![⟨318045, by decide⟩,⟨318076, by decide⟩,⟨318097, by decide⟩,⟨318104, by decide⟩]) unmarked_context_12_25899_318105 node_context_12_25899_318105
  intro a
  fin_cases a
  · exact context_13_103596_318045
  · exact context_13_103597_318076
  · exact context_13_103598_318097
  · exact context_13_103599_318104

theorem unmarked_context_11_6474_318106 : frontier 10 ⟨318106, by decide⟩
    (prefixCache 11 6474) (prefixPartial 11 6474) = false := by
  decide +kernel

theorem node_context_11_6474_318106 : EJMOriginalGlobalDAGData.nodes 10 ⟨318106, by decide⟩ =
    .split (coordinate 11) (![⟨317870, by decide⟩,⟨317948, by decide⟩,⟨318028, by decide⟩,⟨318105, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6474_318106 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6474 ⟨318106, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6474
    ⟨318106, by decide⟩ (by decide) (![⟨317870, by decide⟩,⟨317948, by decide⟩,⟨318028, by decide⟩,⟨318105, by decide⟩]) unmarked_context_11_6474_318106 node_context_11_6474_318106
  intro a
  fin_cases a
  · exact context_12_25896_317870
  · exact context_12_25897_317948
  · exact context_12_25898_318028
  · exact context_12_25899_318105

theorem selected_cut_11911 : selected 8 ⟨318115, by decide⟩
    (prefixPartial 13 103600) = some ⟨13, 2, 0, 318115, 103600, 681, 16384⟩ := by
  decide +kernel

theorem context_13_103600_318115 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103600 ⟨318115, by decide⟩ :=
  accepted_of_selected 13 103600 ⟨318115, by decide⟩ ⟨13, 2, 0, 318115, 103600, 681, 16384⟩
    (by decide) selected_cut_11911

theorem selected_cut_11912 : selected 8 ⟨318143, by decide⟩
    (prefixPartial 13 103601) = some ⟨13, 2, 0, 318143, 103601, 1973, 16384⟩ := by
  decide +kernel

theorem context_13_103601_318143 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103601 ⟨318143, by decide⟩ :=
  accepted_of_selected 13 103601 ⟨318143, by decide⟩ ⟨13, 2, 0, 318143, 103601, 1973, 16384⟩
    (by decide) selected_cut_11912

theorem selected_cut_11913 : selected 8 ⟨318162, by decide⟩
    (prefixPartial 13 103602) = some ⟨13, 2, 0, 318162, 103602, 1357, 16384⟩ := by
  decide +kernel

theorem context_13_103602_318162 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103602 ⟨318162, by decide⟩ :=
  accepted_of_selected 13 103602 ⟨318162, by decide⟩ ⟨13, 2, 0, 318162, 103602, 1357, 16384⟩
    (by decide) selected_cut_11913

theorem selected_cut_11914 : selected 8 ⟨318171, by decide⟩
    (prefixPartial 13 103603) = some ⟨13, 2, 0, 318171, 103603, 1041, 16384⟩ := by
  decide +kernel

theorem context_13_103603_318171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103603 ⟨318171, by decide⟩ :=
  accepted_of_selected 13 103603 ⟨318171, by decide⟩ ⟨13, 2, 0, 318171, 103603, 1041, 16384⟩
    (by decide) selected_cut_11914

theorem unmarked_context_12_25900_318172 : frontier 9 ⟨318172, by decide⟩
    (prefixCache 12 25900) (prefixPartial 12 25900) = false := by
  decide +kernel

theorem node_context_12_25900_318172 : EJMOriginalGlobalDAGData.nodes 9 ⟨318172, by decide⟩ =
    .split (coordinate 12) (![⟨318115, by decide⟩,⟨318143, by decide⟩,⟨318162, by decide⟩,⟨318171, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25900_318172 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25900 ⟨318172, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25900
    ⟨318172, by decide⟩ (by decide) (![⟨318115, by decide⟩,⟨318143, by decide⟩,⟨318162, by decide⟩,⟨318171, by decide⟩]) unmarked_context_12_25900_318172 node_context_12_25900_318172
  intro a
  fin_cases a
  · exact context_13_103600_318115
  · exact context_13_103601_318143
  · exact context_13_103602_318162
  · exact context_13_103603_318171

theorem selected_cut_11915 : selected 8 ⟨318188, by decide⟩
    (prefixPartial 13 103604) = some ⟨13, 2, 0, 318188, 103604, 953, 16384⟩ := by
  decide +kernel

theorem context_13_103604_318188 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103604 ⟨318188, by decide⟩ :=
  accepted_of_selected 13 103604 ⟨318188, by decide⟩ ⟨13, 2, 0, 318188, 103604, 953, 16384⟩
    (by decide) selected_cut_11915

theorem selected_cut_11916 : selected 8 ⟨318215, by decide⟩
    (prefixPartial 13 103605) = some ⟨13, 2, 0, 318215, 103605, 2121, 16384⟩ := by
  decide +kernel

theorem context_13_103605_318215 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103605 ⟨318215, by decide⟩ :=
  accepted_of_selected 13 103605 ⟨318215, by decide⟩ ⟨13, 2, 0, 318215, 103605, 2121, 16384⟩
    (by decide) selected_cut_11916

theorem selected_cut_11917 : selected 8 ⟨318236, by decide⟩
    (prefixPartial 13 103606) = some ⟨13, 2, 0, 318236, 103606, 1469, 16384⟩ := by
  decide +kernel

theorem context_13_103606_318236 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103606 ⟨318236, by decide⟩ :=
  accepted_of_selected 13 103606 ⟨318236, by decide⟩ ⟨13, 2, 0, 318236, 103606, 1469, 16384⟩
    (by decide) selected_cut_11917

theorem selected_cut_11918 : selected 8 ⟨318244, by decide⟩
    (prefixPartial 13 103607) = some ⟨13, 2, 0, 318244, 103607, 909, 16384⟩ := by
  decide +kernel

theorem context_13_103607_318244 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103607 ⟨318244, by decide⟩ :=
  accepted_of_selected 13 103607 ⟨318244, by decide⟩ ⟨13, 2, 0, 318244, 103607, 909, 16384⟩
    (by decide) selected_cut_11918

theorem unmarked_context_12_25901_318245 : frontier 9 ⟨318245, by decide⟩
    (prefixCache 12 25901) (prefixPartial 12 25901) = false := by
  decide +kernel

theorem node_context_12_25901_318245 : EJMOriginalGlobalDAGData.nodes 9 ⟨318245, by decide⟩ =
    .split (coordinate 12) (![⟨318188, by decide⟩,⟨318215, by decide⟩,⟨318236, by decide⟩,⟨318244, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25901_318245 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25901 ⟨318245, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25901
    ⟨318245, by decide⟩ (by decide) (![⟨318188, by decide⟩,⟨318215, by decide⟩,⟨318236, by decide⟩,⟨318244, by decide⟩]) unmarked_context_12_25901_318245 node_context_12_25901_318245
  intro a
  fin_cases a
  · exact context_13_103604_318188
  · exact context_13_103605_318215
  · exact context_13_103606_318236
  · exact context_13_103607_318244

theorem selected_cut_11919 : selected 8 ⟨318263, by decide⟩
    (prefixPartial 13 103608) = some ⟨13, 2, 0, 318263, 103608, 957, 16384⟩ := by
  decide +kernel

theorem context_13_103608_318263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103608 ⟨318263, by decide⟩ :=
  accepted_of_selected 13 103608 ⟨318263, by decide⟩ ⟨13, 2, 0, 318263, 103608, 957, 16384⟩
    (by decide) selected_cut_11919

theorem selected_cut_11920 : selected 8 ⟨318293, by decide⟩
    (prefixPartial 13 103609) = some ⟨13, 2, 0, 318293, 103609, 2357, 16384⟩ := by
  decide +kernel

theorem context_13_103609_318293 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103609 ⟨318293, by decide⟩ :=
  accepted_of_selected 13 103609 ⟨318293, by decide⟩ ⟨13, 2, 0, 318293, 103609, 2357, 16384⟩
    (by decide) selected_cut_11920

theorem selected_cut_11921 : selected 8 ⟨318311, by decide⟩
    (prefixPartial 13 103610) = some ⟨13, 2, 0, 318311, 103610, 1345, 16384⟩ := by
  decide +kernel

theorem context_13_103610_318311 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103610 ⟨318311, by decide⟩ :=
  accepted_of_selected 13 103610 ⟨318311, by decide⟩ ⟨13, 2, 0, 318311, 103610, 1345, 16384⟩
    (by decide) selected_cut_11921

theorem selected_cut_11922 : selected 8 ⟨318324, by decide⟩
    (prefixPartial 13 103611) = some ⟨13, 2, 0, 318324, 103611, 1009, 16384⟩ := by
  decide +kernel

theorem context_13_103611_318324 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103611 ⟨318324, by decide⟩ :=
  accepted_of_selected 13 103611 ⟨318324, by decide⟩ ⟨13, 2, 0, 318324, 103611, 1009, 16384⟩
    (by decide) selected_cut_11922

theorem unmarked_context_12_25902_318325 : frontier 9 ⟨318325, by decide⟩
    (prefixCache 12 25902) (prefixPartial 12 25902) = false := by
  decide +kernel

theorem node_context_12_25902_318325 : EJMOriginalGlobalDAGData.nodes 9 ⟨318325, by decide⟩ =
    .split (coordinate 12) (![⟨318263, by decide⟩,⟨318293, by decide⟩,⟨318311, by decide⟩,⟨318324, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25902_318325 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25902 ⟨318325, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25902
    ⟨318325, by decide⟩ (by decide) (![⟨318263, by decide⟩,⟨318293, by decide⟩,⟨318311, by decide⟩,⟨318324, by decide⟩]) unmarked_context_12_25902_318325 node_context_12_25902_318325
  intro a
  fin_cases a
  · exact context_13_103608_318263
  · exact context_13_103609_318293
  · exact context_13_103610_318311
  · exact context_13_103611_318324

theorem selected_cut_11923 : selected 8 ⟨318344, by decide⟩
    (prefixPartial 13 103612) = some ⟨13, 2, 0, 318344, 103612, 997, 16384⟩ := by
  decide +kernel

theorem context_13_103612_318344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103612 ⟨318344, by decide⟩ :=
  accepted_of_selected 13 103612 ⟨318344, by decide⟩ ⟨13, 2, 0, 318344, 103612, 997, 16384⟩
    (by decide) selected_cut_11923

theorem selected_cut_11924 : selected 8 ⟨318371, by decide⟩
    (prefixPartial 13 103613) = some ⟨13, 2, 0, 318371, 103613, 2413, 16384⟩ := by
  decide +kernel

theorem context_13_103613_318371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103613 ⟨318371, by decide⟩ :=
  accepted_of_selected 13 103613 ⟨318371, by decide⟩ ⟨13, 2, 0, 318371, 103613, 2413, 16384⟩
    (by decide) selected_cut_11924

theorem selected_cut_11925 : selected 8 ⟨318391, by decide⟩
    (prefixPartial 13 103614) = some ⟨13, 2, 0, 318391, 103614, 1505, 16384⟩ := by
  decide +kernel

theorem context_13_103614_318391 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103614 ⟨318391, by decide⟩ :=
  accepted_of_selected 13 103614 ⟨318391, by decide⟩ ⟨13, 2, 0, 318391, 103614, 1505, 16384⟩
    (by decide) selected_cut_11925

theorem selected_cut_11926 : selected 8 ⟨318401, by decide⟩
    (prefixPartial 13 103615) = some ⟨13, 2, 0, 318401, 103615, 1089, 16384⟩ := by
  decide +kernel

theorem context_13_103615_318401 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103615 ⟨318401, by decide⟩ :=
  accepted_of_selected 13 103615 ⟨318401, by decide⟩ ⟨13, 2, 0, 318401, 103615, 1089, 16384⟩
    (by decide) selected_cut_11926

theorem unmarked_context_12_25903_318402 : frontier 9 ⟨318402, by decide⟩
    (prefixCache 12 25903) (prefixPartial 12 25903) = false := by
  decide +kernel

theorem node_context_12_25903_318402 : EJMOriginalGlobalDAGData.nodes 9 ⟨318402, by decide⟩ =
    .split (coordinate 12) (![⟨318344, by decide⟩,⟨318371, by decide⟩,⟨318391, by decide⟩,⟨318401, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25903_318402 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25903 ⟨318402, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25903
    ⟨318402, by decide⟩ (by decide) (![⟨318344, by decide⟩,⟨318371, by decide⟩,⟨318391, by decide⟩,⟨318401, by decide⟩]) unmarked_context_12_25903_318402 node_context_12_25903_318402
  intro a
  fin_cases a
  · exact context_13_103612_318344
  · exact context_13_103613_318371
  · exact context_13_103614_318391
  · exact context_13_103615_318401

theorem unmarked_context_11_6475_318403 : frontier 10 ⟨318403, by decide⟩
    (prefixCache 11 6475) (prefixPartial 11 6475) = false := by
  decide +kernel

theorem node_context_11_6475_318403 : EJMOriginalGlobalDAGData.nodes 10 ⟨318403, by decide⟩ =
    .split (coordinate 11) (![⟨318172, by decide⟩,⟨318245, by decide⟩,⟨318325, by decide⟩,⟨318402, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6475_318403 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6475 ⟨318403, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6475
    ⟨318403, by decide⟩ (by decide) (![⟨318172, by decide⟩,⟨318245, by decide⟩,⟨318325, by decide⟩,⟨318402, by decide⟩]) unmarked_context_11_6475_318403 node_context_11_6475_318403
  intro a
  fin_cases a
  · exact context_12_25900_318172
  · exact context_12_25901_318245
  · exact context_12_25902_318325
  · exact context_12_25903_318402

theorem unmarked_context_10_1618_318404 : frontier 11 ⟨318404, by decide⟩
    (prefixCache 10 1618) (prefixPartial 10 1618) = false := by
  decide +kernel

theorem node_context_10_1618_318404 : EJMOriginalGlobalDAGData.nodes 11 ⟨318404, by decide⟩ =
    .split (coordinate 10) (![⟨317511, by decide⟩,⟨317804, by decide⟩,⟨318106, by decide⟩,⟨318403, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1618_318404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1618 ⟨318404, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1618
    ⟨318404, by decide⟩ (by decide) (![⟨317511, by decide⟩,⟨317804, by decide⟩,⟨318106, by decide⟩,⟨318403, by decide⟩]) unmarked_context_10_1618_318404 node_context_10_1618_318404
  intro a
  fin_cases a
  · exact context_11_6472_317511
  · exact context_11_6473_317804
  · exact context_11_6474_318106
  · exact context_11_6475_318403

theorem selected_cut_11927 : selected 8 ⟨318411, by decide⟩
    (prefixPartial 13 103616) = some ⟨13, 2, 0, 318411, 103616, 889, 16384⟩ := by
  decide +kernel

theorem context_13_103616_318411 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103616 ⟨318411, by decide⟩ :=
  accepted_of_selected 13 103616 ⟨318411, by decide⟩ ⟨13, 2, 0, 318411, 103616, 889, 16384⟩
    (by decide) selected_cut_11927

theorem selected_cut_11928 : selected 8 ⟨318432, by decide⟩
    (prefixPartial 13 103617) = some ⟨13, 2, 0, 318432, 103617, 1989, 16384⟩ := by
  decide +kernel

theorem context_13_103617_318432 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103617 ⟨318432, by decide⟩ :=
  accepted_of_selected 13 103617 ⟨318432, by decide⟩ ⟨13, 2, 0, 318432, 103617, 1989, 16384⟩
    (by decide) selected_cut_11928

theorem selected_cut_11929 : selected 8 ⟨318452, by decide⟩
    (prefixPartial 13 103618) = some ⟨13, 2, 0, 318452, 103618, 1581, 16384⟩ := by
  decide +kernel

theorem context_13_103618_318452 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103618 ⟨318452, by decide⟩ :=
  accepted_of_selected 13 103618 ⟨318452, by decide⟩ ⟨13, 2, 0, 318452, 103618, 1581, 16384⟩
    (by decide) selected_cut_11929

theorem selected_cut_11930 : selected 8 ⟨318459, by decide⟩
    (prefixPartial 13 103619) = some ⟨13, 2, 0, 318459, 103619, 889, 16384⟩ := by
  decide +kernel

theorem context_13_103619_318459 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103619 ⟨318459, by decide⟩ :=
  accepted_of_selected 13 103619 ⟨318459, by decide⟩ ⟨13, 2, 0, 318459, 103619, 889, 16384⟩
    (by decide) selected_cut_11930

theorem unmarked_context_12_25904_318460 : frontier 9 ⟨318460, by decide⟩
    (prefixCache 12 25904) (prefixPartial 12 25904) = false := by
  decide +kernel

theorem node_context_12_25904_318460 : EJMOriginalGlobalDAGData.nodes 9 ⟨318460, by decide⟩ =
    .split (coordinate 12) (![⟨318411, by decide⟩,⟨318432, by decide⟩,⟨318452, by decide⟩,⟨318459, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25904_318460 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25904 ⟨318460, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25904
    ⟨318460, by decide⟩ (by decide) (![⟨318411, by decide⟩,⟨318432, by decide⟩,⟨318452, by decide⟩,⟨318459, by decide⟩]) unmarked_context_12_25904_318460 node_context_12_25904_318460
  intro a
  fin_cases a
  · exact context_13_103616_318411
  · exact context_13_103617_318432
  · exact context_13_103618_318452
  · exact context_13_103619_318459

theorem selected_cut_11931 : selected 8 ⟨318471, by decide⟩
    (prefixPartial 13 103620) = some ⟨13, 2, 0, 318471, 103620, 925, 16384⟩ := by
  decide +kernel

theorem context_13_103620_318471 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103620 ⟨318471, by decide⟩ :=
  accepted_of_selected 13 103620 ⟨318471, by decide⟩ ⟨13, 2, 0, 318471, 103620, 925, 16384⟩
    (by decide) selected_cut_11931

theorem selected_cut_11932 : selected 8 ⟨318497, by decide⟩
    (prefixPartial 13 103621) = some ⟨13, 2, 0, 318497, 103621, 2193, 16384⟩ := by
  decide +kernel

theorem context_13_103621_318497 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103621 ⟨318497, by decide⟩ :=
  accepted_of_selected 13 103621 ⟨318497, by decide⟩ ⟨13, 2, 0, 318497, 103621, 2193, 16384⟩
    (by decide) selected_cut_11932

theorem selected_cut_11933 : selected 8 ⟨318518, by decide⟩
    (prefixPartial 13 103622) = some ⟨13, 2, 0, 318518, 103622, 1837, 16384⟩ := by
  decide +kernel

theorem context_13_103622_318518 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103622 ⟨318518, by decide⟩ :=
  accepted_of_selected 13 103622 ⟨318518, by decide⟩ ⟨13, 2, 0, 318518, 103622, 1837, 16384⟩
    (by decide) selected_cut_11933

theorem selected_cut_11934 : selected 8 ⟨318525, by decide⟩
    (prefixPartial 13 103623) = some ⟨13, 2, 0, 318525, 103623, 941, 16384⟩ := by
  decide +kernel

theorem context_13_103623_318525 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103623 ⟨318525, by decide⟩ :=
  accepted_of_selected 13 103623 ⟨318525, by decide⟩ ⟨13, 2, 0, 318525, 103623, 941, 16384⟩
    (by decide) selected_cut_11934

theorem unmarked_context_12_25905_318526 : frontier 9 ⟨318526, by decide⟩
    (prefixCache 12 25905) (prefixPartial 12 25905) = false := by
  decide +kernel

theorem node_context_12_25905_318526 : EJMOriginalGlobalDAGData.nodes 9 ⟨318526, by decide⟩ =
    .split (coordinate 12) (![⟨318471, by decide⟩,⟨318497, by decide⟩,⟨318518, by decide⟩,⟨318525, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25905_318526 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25905 ⟨318526, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25905
    ⟨318526, by decide⟩ (by decide) (![⟨318471, by decide⟩,⟨318497, by decide⟩,⟨318518, by decide⟩,⟨318525, by decide⟩]) unmarked_context_12_25905_318526 node_context_12_25905_318526
  intro a
  fin_cases a
  · exact context_13_103620_318471
  · exact context_13_103621_318497
  · exact context_13_103622_318518
  · exact context_13_103623_318525

theorem selected_cut_11935 : selected 8 ⟨318539, by decide⟩
    (prefixPartial 13 103624) = some ⟨13, 2, 0, 318539, 103624, 973, 16384⟩ := by
  decide +kernel

theorem context_13_103624_318539 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103624 ⟨318539, by decide⟩ :=
  accepted_of_selected 13 103624 ⟨318539, by decide⟩ ⟨13, 2, 0, 318539, 103624, 973, 16384⟩
    (by decide) selected_cut_11935

theorem selected_cut_11936 : selected 8 ⟨318579, by decide⟩
    (prefixPartial 13 103625) = some ⟨13, 2, 0, 318579, 103625, 2369, 16384⟩ := by
  decide +kernel

theorem context_13_103625_318579 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103625 ⟨318579, by decide⟩ :=
  accepted_of_selected 13 103625 ⟨318579, by decide⟩ ⟨13, 2, 0, 318579, 103625, 2369, 16384⟩
    (by decide) selected_cut_11936

theorem selected_cut_11937 : selected 8 ⟨318604, by decide⟩
    (prefixPartial 13 103626) = some ⟨13, 2, 0, 318604, 103626, 1849, 16384⟩ := by
  decide +kernel

theorem context_13_103626_318604 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103626 ⟨318604, by decide⟩ :=
  accepted_of_selected 13 103626 ⟨318604, by decide⟩ ⟨13, 2, 0, 318604, 103626, 1849, 16384⟩
    (by decide) selected_cut_11937

theorem selected_cut_11938 : selected 8 ⟨318618, by decide⟩
    (prefixPartial 13 103627) = some ⟨13, 2, 0, 318618, 103627, 1109, 16384⟩ := by
  decide +kernel

theorem context_13_103627_318618 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103627 ⟨318618, by decide⟩ :=
  accepted_of_selected 13 103627 ⟨318618, by decide⟩ ⟨13, 2, 0, 318618, 103627, 1109, 16384⟩
    (by decide) selected_cut_11938

theorem unmarked_context_12_25906_318619 : frontier 9 ⟨318619, by decide⟩
    (prefixCache 12 25906) (prefixPartial 12 25906) = false := by
  decide +kernel

theorem node_context_12_25906_318619 : EJMOriginalGlobalDAGData.nodes 9 ⟨318619, by decide⟩ =
    .split (coordinate 12) (![⟨318539, by decide⟩,⟨318579, by decide⟩,⟨318604, by decide⟩,⟨318618, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25906_318619 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25906 ⟨318619, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25906
    ⟨318619, by decide⟩ (by decide) (![⟨318539, by decide⟩,⟨318579, by decide⟩,⟨318604, by decide⟩,⟨318618, by decide⟩]) unmarked_context_12_25906_318619 node_context_12_25906_318619
  intro a
  fin_cases a
  · exact context_13_103624_318539
  · exact context_13_103625_318579
  · exact context_13_103626_318604
  · exact context_13_103627_318618

theorem selected_cut_11939 : selected 8 ⟨318637, by decide⟩
    (prefixPartial 13 103628) = some ⟨13, 2, 0, 318637, 103628, 1153, 16384⟩ := by
  decide +kernel

theorem context_13_103628_318637 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103628 ⟨318637, by decide⟩ :=
  accepted_of_selected 13 103628 ⟨318637, by decide⟩ ⟨13, 2, 0, 318637, 103628, 1153, 16384⟩
    (by decide) selected_cut_11939

theorem selected_cut_11940 : selected 8 ⟨318680, by decide⟩
    (prefixPartial 13 103629) = some ⟨13, 2, 0, 318680, 103629, 2761, 16384⟩ := by
  decide +kernel

theorem context_13_103629_318680 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103629 ⟨318680, by decide⟩ :=
  accepted_of_selected 13 103629 ⟨318680, by decide⟩ ⟨13, 2, 0, 318680, 103629, 2761, 16384⟩
    (by decide) selected_cut_11940

theorem selected_cut_11941 : selected 8 ⟨318714, by decide⟩
    (prefixPartial 13 103630) = some ⟨13, 2, 0, 318714, 103630, 2153, 16384⟩ := by
  decide +kernel

theorem context_13_103630_318714 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103630 ⟨318714, by decide⟩ :=
  accepted_of_selected 13 103630 ⟨318714, by decide⟩ ⟨13, 2, 0, 318714, 103630, 2153, 16384⟩
    (by decide) selected_cut_11941

theorem selected_cut_11942 : selected 8 ⟨318726, by decide⟩
    (prefixPartial 13 103631) = some ⟨13, 2, 0, 318726, 103631, 1113, 16384⟩ := by
  decide +kernel

theorem context_13_103631_318726 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103631 ⟨318726, by decide⟩ :=
  accepted_of_selected 13 103631 ⟨318726, by decide⟩ ⟨13, 2, 0, 318726, 103631, 1113, 16384⟩
    (by decide) selected_cut_11942

theorem unmarked_context_12_25907_318727 : frontier 9 ⟨318727, by decide⟩
    (prefixCache 12 25907) (prefixPartial 12 25907) = false := by
  decide +kernel

theorem node_context_12_25907_318727 : EJMOriginalGlobalDAGData.nodes 9 ⟨318727, by decide⟩ =
    .split (coordinate 12) (![⟨318637, by decide⟩,⟨318680, by decide⟩,⟨318714, by decide⟩,⟨318726, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25907_318727 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25907 ⟨318727, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25907
    ⟨318727, by decide⟩ (by decide) (![⟨318637, by decide⟩,⟨318680, by decide⟩,⟨318714, by decide⟩,⟨318726, by decide⟩]) unmarked_context_12_25907_318727 node_context_12_25907_318727
  intro a
  fin_cases a
  · exact context_13_103628_318637
  · exact context_13_103629_318680
  · exact context_13_103630_318714
  · exact context_13_103631_318726

theorem unmarked_context_11_6476_318728 : frontier 10 ⟨318728, by decide⟩
    (prefixCache 11 6476) (prefixPartial 11 6476) = false := by
  decide +kernel

theorem node_context_11_6476_318728 : EJMOriginalGlobalDAGData.nodes 10 ⟨318728, by decide⟩ =
    .split (coordinate 11) (![⟨318460, by decide⟩,⟨318526, by decide⟩,⟨318619, by decide⟩,⟨318727, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6476_318728 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6476 ⟨318728, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6476
    ⟨318728, by decide⟩ (by decide) (![⟨318460, by decide⟩,⟨318526, by decide⟩,⟨318619, by decide⟩,⟨318727, by decide⟩]) unmarked_context_11_6476_318728 node_context_11_6476_318728
  intro a
  fin_cases a
  · exact context_12_25904_318460
  · exact context_12_25905_318526
  · exact context_12_25906_318619
  · exact context_12_25907_318727

theorem selected_cut_11943 : selected 8 ⟨318733, by decide⟩
    (prefixPartial 13 103632) = some ⟨13, 2, 0, 318733, 103632, 505, 16384⟩ := by
  decide +kernel

theorem context_13_103632_318733 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103632 ⟨318733, by decide⟩ :=
  accepted_of_selected 13 103632 ⟨318733, by decide⟩ ⟨13, 2, 0, 318733, 103632, 505, 16384⟩
    (by decide) selected_cut_11943

theorem selected_cut_11944 : selected 8 ⟨318756, by decide⟩
    (prefixPartial 13 103633) = some ⟨13, 2, 0, 318756, 103633, 1757, 16384⟩ := by
  decide +kernel

theorem context_13_103633_318756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103633 ⟨318756, by decide⟩ :=
  accepted_of_selected 13 103633 ⟨318756, by decide⟩ ⟨13, 2, 0, 318756, 103633, 1757, 16384⟩
    (by decide) selected_cut_11944

theorem selected_cut_11945 : selected 8 ⟨318772, by decide⟩
    (prefixPartial 13 103634) = some ⟨13, 2, 0, 318772, 103634, 1333, 16384⟩ := by
  decide +kernel

theorem context_13_103634_318772 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103634 ⟨318772, by decide⟩ :=
  accepted_of_selected 13 103634 ⟨318772, by decide⟩ ⟨13, 2, 0, 318772, 103634, 1333, 16384⟩
    (by decide) selected_cut_11945

theorem selected_cut_11946 : selected 8 ⟨318778, by decide⟩
    (prefixPartial 13 103635) = some ⟨13, 2, 0, 318778, 103635, 873, 16384⟩ := by
  decide +kernel

theorem context_13_103635_318778 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103635 ⟨318778, by decide⟩ :=
  accepted_of_selected 13 103635 ⟨318778, by decide⟩ ⟨13, 2, 0, 318778, 103635, 873, 16384⟩
    (by decide) selected_cut_11946

theorem unmarked_context_12_25908_318779 : frontier 9 ⟨318779, by decide⟩
    (prefixCache 12 25908) (prefixPartial 12 25908) = false := by
  decide +kernel

theorem node_context_12_25908_318779 : EJMOriginalGlobalDAGData.nodes 9 ⟨318779, by decide⟩ =
    .split (coordinate 12) (![⟨318733, by decide⟩,⟨318756, by decide⟩,⟨318772, by decide⟩,⟨318778, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25908_318779 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25908 ⟨318779, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25908
    ⟨318779, by decide⟩ (by decide) (![⟨318733, by decide⟩,⟨318756, by decide⟩,⟨318772, by decide⟩,⟨318778, by decide⟩]) unmarked_context_12_25908_318779 node_context_12_25908_318779
  intro a
  fin_cases a
  · exact context_13_103632_318733
  · exact context_13_103633_318756
  · exact context_13_103634_318772
  · exact context_13_103635_318778

theorem selected_cut_11947 : selected 8 ⟨318790, by decide⟩
    (prefixPartial 13 103636) = some ⟨13, 2, 0, 318790, 103636, 909, 16384⟩ := by
  decide +kernel

theorem context_13_103636_318790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103636 ⟨318790, by decide⟩ :=
  accepted_of_selected 13 103636 ⟨318790, by decide⟩ ⟨13, 2, 0, 318790, 103636, 909, 16384⟩
    (by decide) selected_cut_11947

theorem selected_cut_11948 : selected 8 ⟨318824, by decide⟩
    (prefixPartial 13 103637) = some ⟨13, 2, 0, 318824, 103637, 3349, 16384⟩ := by
  decide +kernel

theorem context_13_103637_318824 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103637 ⟨318824, by decide⟩ :=
  accepted_of_selected 13 103637 ⟨318824, by decide⟩ ⟨13, 2, 0, 318824, 103637, 3349, 16384⟩
    (by decide) selected_cut_11948

theorem selected_cut_11949 : selected 8 ⟨318847, by decide⟩
    (prefixPartial 13 103638) = some ⟨13, 2, 0, 318847, 103638, 2305, 16384⟩ := by
  decide +kernel

theorem context_13_103638_318847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103638 ⟨318847, by decide⟩ :=
  accepted_of_selected 13 103638 ⟨318847, by decide⟩ ⟨13, 2, 0, 318847, 103638, 2305, 16384⟩
    (by decide) selected_cut_11949

theorem selected_cut_11950 : selected 8 ⟨318856, by decide⟩
    (prefixPartial 13 103639) = some ⟨13, 2, 0, 318856, 103639, 1157, 16384⟩ := by
  decide +kernel

theorem context_13_103639_318856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103639 ⟨318856, by decide⟩ :=
  accepted_of_selected 13 103639 ⟨318856, by decide⟩ ⟨13, 2, 0, 318856, 103639, 1157, 16384⟩
    (by decide) selected_cut_11950

theorem unmarked_context_12_25909_318857 : frontier 9 ⟨318857, by decide⟩
    (prefixCache 12 25909) (prefixPartial 12 25909) = false := by
  decide +kernel

theorem node_context_12_25909_318857 : EJMOriginalGlobalDAGData.nodes 9 ⟨318857, by decide⟩ =
    .split (coordinate 12) (![⟨318790, by decide⟩,⟨318824, by decide⟩,⟨318847, by decide⟩,⟨318856, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25909_318857 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25909 ⟨318857, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25909
    ⟨318857, by decide⟩ (by decide) (![⟨318790, by decide⟩,⟨318824, by decide⟩,⟨318847, by decide⟩,⟨318856, by decide⟩]) unmarked_context_12_25909_318857 node_context_12_25909_318857
  intro a
  fin_cases a
  · exact context_13_103636_318790
  · exact context_13_103637_318824
  · exact context_13_103638_318847
  · exact context_13_103639_318856

theorem selected_cut_11951 : selected 8 ⟨318865, by decide⟩
    (prefixPartial 13 103640) = some ⟨13, 2, 0, 318865, 103640, 617, 16384⟩ := by
  decide +kernel

theorem context_13_103640_318865 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103640 ⟨318865, by decide⟩ :=
  accepted_of_selected 13 103640 ⟨318865, by decide⟩ ⟨13, 2, 0, 318865, 103640, 617, 16384⟩
    (by decide) selected_cut_11951

theorem selected_cut_11952 : selected 8 ⟨318890, by decide⟩
    (prefixPartial 13 103641) = some ⟨13, 2, 0, 318890, 103641, 2049, 16384⟩ := by
  decide +kernel

theorem context_13_103641_318890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103641 ⟨318890, by decide⟩ :=
  accepted_of_selected 13 103641 ⟨318890, by decide⟩ ⟨13, 2, 0, 318890, 103641, 2049, 16384⟩
    (by decide) selected_cut_11952

theorem selected_cut_11953 : selected 8 ⟨318906, by decide⟩
    (prefixPartial 13 103642) = some ⟨13, 2, 0, 318906, 103642, 1393, 16384⟩ := by
  decide +kernel

theorem context_13_103642_318906 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103642 ⟨318906, by decide⟩ :=
  accepted_of_selected 13 103642 ⟨318906, by decide⟩ ⟨13, 2, 0, 318906, 103642, 1393, 16384⟩
    (by decide) selected_cut_11953

theorem selected_cut_11954 : selected 8 ⟨318916, by decide⟩
    (prefixPartial 13 103643) = some ⟨13, 2, 0, 318916, 103643, 981, 16384⟩ := by
  decide +kernel

theorem context_13_103643_318916 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103643 ⟨318916, by decide⟩ :=
  accepted_of_selected 13 103643 ⟨318916, by decide⟩ ⟨13, 2, 0, 318916, 103643, 981, 16384⟩
    (by decide) selected_cut_11954

theorem unmarked_context_12_25910_318917 : frontier 9 ⟨318917, by decide⟩
    (prefixCache 12 25910) (prefixPartial 12 25910) = false := by
  decide +kernel

theorem node_context_12_25910_318917 : EJMOriginalGlobalDAGData.nodes 9 ⟨318917, by decide⟩ =
    .split (coordinate 12) (![⟨318865, by decide⟩,⟨318890, by decide⟩,⟨318906, by decide⟩,⟨318916, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25910_318917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25910 ⟨318917, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25910
    ⟨318917, by decide⟩ (by decide) (![⟨318865, by decide⟩,⟨318890, by decide⟩,⟨318906, by decide⟩,⟨318916, by decide⟩]) unmarked_context_12_25910_318917 node_context_12_25910_318917
  intro a
  fin_cases a
  · exact context_13_103640_318865
  · exact context_13_103641_318890
  · exact context_13_103642_318906
  · exact context_13_103643_318916

theorem selected_cut_11955 : selected 8 ⟨318928, by decide⟩
    (prefixPartial 13 103644) = some ⟨13, 2, 0, 318928, 103644, 565, 16384⟩ := by
  decide +kernel

theorem context_13_103644_318928 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103644 ⟨318928, by decide⟩ :=
  accepted_of_selected 13 103644 ⟨318928, by decide⟩ ⟨13, 2, 0, 318928, 103644, 565, 16384⟩
    (by decide) selected_cut_11955

theorem selected_cut_11956 : selected 8 ⟨318961, by decide⟩
    (prefixPartial 13 103645) = some ⟨13, 2, 0, 318961, 103645, 2557, 16384⟩ := by
  decide +kernel

theorem context_13_103645_318961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103645 ⟨318961, by decide⟩ :=
  accepted_of_selected 13 103645 ⟨318961, by decide⟩ ⟨13, 2, 0, 318961, 103645, 2557, 16384⟩
    (by decide) selected_cut_11956

theorem selected_cut_11957 : selected 8 ⟨318984, by decide⟩
    (prefixPartial 13 103646) = some ⟨13, 2, 0, 318984, 103646, 1649, 16384⟩ := by
  decide +kernel

theorem context_13_103646_318984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103646 ⟨318984, by decide⟩ :=
  accepted_of_selected 13 103646 ⟨318984, by decide⟩ ⟨13, 2, 0, 318984, 103646, 1649, 16384⟩
    (by decide) selected_cut_11957

theorem selected_cut_11958 : selected 8 ⟨318989, by decide⟩
    (prefixPartial 13 103647) = some ⟨13, 2, 0, 318989, 103647, 993, 16384⟩ := by
  decide +kernel

theorem context_13_103647_318989 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103647 ⟨318989, by decide⟩ :=
  accepted_of_selected 13 103647 ⟨318989, by decide⟩ ⟨13, 2, 0, 318989, 103647, 993, 16384⟩
    (by decide) selected_cut_11958

theorem unmarked_context_12_25911_318990 : frontier 9 ⟨318990, by decide⟩
    (prefixCache 12 25911) (prefixPartial 12 25911) = false := by
  decide +kernel

theorem node_context_12_25911_318990 : EJMOriginalGlobalDAGData.nodes 9 ⟨318990, by decide⟩ =
    .split (coordinate 12) (![⟨318928, by decide⟩,⟨318961, by decide⟩,⟨318984, by decide⟩,⟨318989, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25911_318990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25911 ⟨318990, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25911
    ⟨318990, by decide⟩ (by decide) (![⟨318928, by decide⟩,⟨318961, by decide⟩,⟨318984, by decide⟩,⟨318989, by decide⟩]) unmarked_context_12_25911_318990 node_context_12_25911_318990
  intro a
  fin_cases a
  · exact context_13_103644_318928
  · exact context_13_103645_318961
  · exact context_13_103646_318984
  · exact context_13_103647_318989

theorem unmarked_context_11_6477_318991 : frontier 10 ⟨318991, by decide⟩
    (prefixCache 11 6477) (prefixPartial 11 6477) = false := by
  decide +kernel

theorem node_context_11_6477_318991 : EJMOriginalGlobalDAGData.nodes 10 ⟨318991, by decide⟩ =
    .split (coordinate 11) (![⟨318779, by decide⟩,⟨318857, by decide⟩,⟨318917, by decide⟩,⟨318990, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6477_318991 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6477 ⟨318991, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6477
    ⟨318991, by decide⟩ (by decide) (![⟨318779, by decide⟩,⟨318857, by decide⟩,⟨318917, by decide⟩,⟨318990, by decide⟩]) unmarked_context_11_6477_318991 node_context_11_6477_318991
  intro a
  fin_cases a
  · exact context_12_25908_318779
  · exact context_12_25909_318857
  · exact context_12_25910_318917
  · exact context_12_25911_318990

theorem selected_cut_11959 : selected 8 ⟨318997, by decide⟩
    (prefixPartial 13 103648) = some ⟨13, 2, 0, 318997, 103648, 429, 16384⟩ := by
  decide +kernel

theorem context_13_103648_318997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103648 ⟨318997, by decide⟩ :=
  accepted_of_selected 13 103648 ⟨318997, by decide⟩ ⟨13, 2, 0, 318997, 103648, 429, 16384⟩
    (by decide) selected_cut_11959

theorem selected_cut_11960 : selected 8 ⟨319029, by decide⟩
    (prefixPartial 13 103649) = some ⟨13, 2, 0, 319029, 103649, 2113, 16384⟩ := by
  decide +kernel

theorem context_13_103649_319029 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103649 ⟨319029, by decide⟩ :=
  accepted_of_selected 13 103649 ⟨319029, by decide⟩ ⟨13, 2, 0, 319029, 103649, 2113, 16384⟩
    (by decide) selected_cut_11960

theorem selected_cut_11961 : selected 8 ⟨319051, by decide⟩
    (prefixPartial 13 103650) = some ⟨13, 2, 0, 319051, 103650, 1825, 16384⟩ := by
  decide +kernel

theorem context_13_103650_319051 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103650 ⟨319051, by decide⟩ :=
  accepted_of_selected 13 103650 ⟨319051, by decide⟩ ⟨13, 2, 0, 319051, 103650, 1825, 16384⟩
    (by decide) selected_cut_11961

theorem selected_cut_11962 : selected 8 ⟨319058, by decide⟩
    (prefixPartial 13 103651) = some ⟨13, 2, 0, 319058, 103651, 1009, 16384⟩ := by
  decide +kernel

theorem context_13_103651_319058 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103651 ⟨319058, by decide⟩ :=
  accepted_of_selected 13 103651 ⟨319058, by decide⟩ ⟨13, 2, 0, 319058, 103651, 1009, 16384⟩
    (by decide) selected_cut_11962

theorem unmarked_context_12_25912_319059 : frontier 9 ⟨319059, by decide⟩
    (prefixCache 12 25912) (prefixPartial 12 25912) = false := by
  decide +kernel

theorem node_context_12_25912_319059 : EJMOriginalGlobalDAGData.nodes 9 ⟨319059, by decide⟩ =
    .split (coordinate 12) (![⟨318997, by decide⟩,⟨319029, by decide⟩,⟨319051, by decide⟩,⟨319058, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25912_319059 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25912 ⟨319059, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25912
    ⟨319059, by decide⟩ (by decide) (![⟨318997, by decide⟩,⟨319029, by decide⟩,⟨319051, by decide⟩,⟨319058, by decide⟩]) unmarked_context_12_25912_319059 node_context_12_25912_319059
  intro a
  fin_cases a
  · exact context_13_103648_318997
  · exact context_13_103649_319029
  · exact context_13_103650_319051
  · exact context_13_103651_319058

theorem selected_cut_11963 : selected 8 ⟨319067, by decide⟩
    (prefixPartial 13 103652) = some ⟨13, 2, 0, 319067, 103652, 505, 16384⟩ := by
  decide +kernel

theorem context_13_103652_319067 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103652 ⟨319067, by decide⟩ :=
  accepted_of_selected 13 103652 ⟨319067, by decide⟩ ⟨13, 2, 0, 319067, 103652, 505, 16384⟩
    (by decide) selected_cut_11963

theorem selected_cut_11964 : selected 8 ⟨319094, by decide⟩
    (prefixPartial 13 103653) = some ⟨13, 2, 0, 319094, 103653, 2101, 16384⟩ := by
  decide +kernel

theorem context_13_103653_319094 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103653 ⟨319094, by decide⟩ :=
  accepted_of_selected 13 103653 ⟨319094, by decide⟩ ⟨13, 2, 0, 319094, 103653, 2101, 16384⟩
    (by decide) selected_cut_11964

theorem selected_cut_11965 : selected 8 ⟨319114, by decide⟩
    (prefixPartial 13 103654) = some ⟨13, 2, 0, 319114, 103654, 1781, 16384⟩ := by
  decide +kernel

theorem context_13_103654_319114 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103654 ⟨319114, by decide⟩ :=
  accepted_of_selected 13 103654 ⟨319114, by decide⟩ ⟨13, 2, 0, 319114, 103654, 1781, 16384⟩
    (by decide) selected_cut_11965

theorem selected_cut_11966 : selected 8 ⟨319120, by decide⟩
    (prefixPartial 13 103655) = some ⟨13, 2, 0, 319120, 103655, 989, 16384⟩ := by
  decide +kernel

theorem context_13_103655_319120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103655 ⟨319120, by decide⟩ :=
  accepted_of_selected 13 103655 ⟨319120, by decide⟩ ⟨13, 2, 0, 319120, 103655, 989, 16384⟩
    (by decide) selected_cut_11966

theorem unmarked_context_12_25913_319121 : frontier 9 ⟨319121, by decide⟩
    (prefixCache 12 25913) (prefixPartial 12 25913) = false := by
  decide +kernel

theorem node_context_12_25913_319121 : EJMOriginalGlobalDAGData.nodes 9 ⟨319121, by decide⟩ =
    .split (coordinate 12) (![⟨319067, by decide⟩,⟨319094, by decide⟩,⟨319114, by decide⟩,⟨319120, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25913_319121 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25913 ⟨319121, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25913
    ⟨319121, by decide⟩ (by decide) (![⟨319067, by decide⟩,⟨319094, by decide⟩,⟨319114, by decide⟩,⟨319120, by decide⟩]) unmarked_context_12_25913_319121 node_context_12_25913_319121
  intro a
  fin_cases a
  · exact context_13_103652_319067
  · exact context_13_103653_319094
  · exact context_13_103654_319114
  · exact context_13_103655_319120

theorem selected_cut_11967 : selected 8 ⟨319128, by decide⟩
    (prefixPartial 13 103656) = some ⟨13, 2, 0, 319128, 103656, 425, 16384⟩ := by
  decide +kernel

theorem context_13_103656_319128 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103656 ⟨319128, by decide⟩ :=
  accepted_of_selected 13 103656 ⟨319128, by decide⟩ ⟨13, 2, 0, 319128, 103656, 425, 16384⟩
    (by decide) selected_cut_11967

theorem selected_cut_11968 : selected 8 ⟨319162, by decide⟩
    (prefixPartial 13 103657) = some ⟨13, 2, 0, 319162, 103657, 2325, 16384⟩ := by
  decide +kernel

theorem context_13_103657_319162 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103657 ⟨319162, by decide⟩ :=
  accepted_of_selected 13 103657 ⟨319162, by decide⟩ ⟨13, 2, 0, 319162, 103657, 2325, 16384⟩
    (by decide) selected_cut_11968

theorem selected_cut_11969 : selected 8 ⟨319184, by decide⟩
    (prefixPartial 13 103658) = some ⟨13, 2, 0, 319184, 103658, 1709, 16384⟩ := by
  decide +kernel

theorem context_13_103658_319184 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103658 ⟨319184, by decide⟩ :=
  accepted_of_selected 13 103658 ⟨319184, by decide⟩ ⟨13, 2, 0, 319184, 103658, 1709, 16384⟩
    (by decide) selected_cut_11969

theorem selected_cut_11970 : selected 8 ⟨319196, by decide⟩
    (prefixPartial 13 103659) = some ⟨13, 2, 0, 319196, 103659, 1077, 16384⟩ := by
  decide +kernel

theorem context_13_103659_319196 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103659 ⟨319196, by decide⟩ :=
  accepted_of_selected 13 103659 ⟨319196, by decide⟩ ⟨13, 2, 0, 319196, 103659, 1077, 16384⟩
    (by decide) selected_cut_11970

theorem unmarked_context_12_25914_319197 : frontier 9 ⟨319197, by decide⟩
    (prefixCache 12 25914) (prefixPartial 12 25914) = false := by
  decide +kernel

theorem node_context_12_25914_319197 : EJMOriginalGlobalDAGData.nodes 9 ⟨319197, by decide⟩ =
    .split (coordinate 12) (![⟨319128, by decide⟩,⟨319162, by decide⟩,⟨319184, by decide⟩,⟨319196, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25914_319197 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25914 ⟨319197, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25914
    ⟨319197, by decide⟩ (by decide) (![⟨319128, by decide⟩,⟨319162, by decide⟩,⟨319184, by decide⟩,⟨319196, by decide⟩]) unmarked_context_12_25914_319197 node_context_12_25914_319197
  intro a
  fin_cases a
  · exact context_13_103656_319128
  · exact context_13_103657_319162
  · exact context_13_103658_319184
  · exact context_13_103659_319196

theorem selected_cut_11971 : selected 8 ⟨319206, by decide⟩
    (prefixPartial 13 103660) = some ⟨13, 2, 0, 319206, 103660, 477, 16384⟩ := by
  decide +kernel

theorem context_13_103660_319206 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103660 ⟨319206, by decide⟩ :=
  accepted_of_selected 13 103660 ⟨319206, by decide⟩ ⟨13, 2, 0, 319206, 103660, 477, 16384⟩
    (by decide) selected_cut_11971

theorem selected_cut_11972 : selected 8 ⟨319252, by decide⟩
    (prefixPartial 13 103661) = some ⟨13, 2, 0, 319252, 103661, 3185, 16384⟩ := by
  decide +kernel

theorem context_13_103661_319252 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103661 ⟨319252, by decide⟩ :=
  accepted_of_selected 13 103661 ⟨319252, by decide⟩ ⟨13, 2, 0, 319252, 103661, 3185, 16384⟩
    (by decide) selected_cut_11972

theorem selected_cut_11973 : selected 8 ⟨319274, by decide⟩
    (prefixPartial 13 103662) = some ⟨13, 2, 0, 319274, 103662, 1925, 16384⟩ := by
  decide +kernel

theorem context_13_103662_319274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103662 ⟨319274, by decide⟩ :=
  accepted_of_selected 13 103662 ⟨319274, by decide⟩ ⟨13, 2, 0, 319274, 103662, 1925, 16384⟩
    (by decide) selected_cut_11973

theorem selected_cut_11974 : selected 8 ⟨319285, by decide⟩
    (prefixPartial 13 103663) = some ⟨13, 2, 0, 319285, 103663, 1085, 16384⟩ := by
  decide +kernel

theorem context_13_103663_319285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103663 ⟨319285, by decide⟩ :=
  accepted_of_selected 13 103663 ⟨319285, by decide⟩ ⟨13, 2, 0, 319285, 103663, 1085, 16384⟩
    (by decide) selected_cut_11974

theorem unmarked_context_12_25915_319286 : frontier 9 ⟨319286, by decide⟩
    (prefixCache 12 25915) (prefixPartial 12 25915) = false := by
  decide +kernel

theorem node_context_12_25915_319286 : EJMOriginalGlobalDAGData.nodes 9 ⟨319286, by decide⟩ =
    .split (coordinate 12) (![⟨319206, by decide⟩,⟨319252, by decide⟩,⟨319274, by decide⟩,⟨319285, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25915_319286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25915 ⟨319286, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25915
    ⟨319286, by decide⟩ (by decide) (![⟨319206, by decide⟩,⟨319252, by decide⟩,⟨319274, by decide⟩,⟨319285, by decide⟩]) unmarked_context_12_25915_319286 node_context_12_25915_319286
  intro a
  fin_cases a
  · exact context_13_103660_319206
  · exact context_13_103661_319252
  · exact context_13_103662_319274
  · exact context_13_103663_319285

theorem unmarked_context_11_6478_319287 : frontier 10 ⟨319287, by decide⟩
    (prefixCache 11 6478) (prefixPartial 11 6478) = false := by
  decide +kernel

theorem node_context_11_6478_319287 : EJMOriginalGlobalDAGData.nodes 10 ⟨319287, by decide⟩ =
    .split (coordinate 11) (![⟨319059, by decide⟩,⟨319121, by decide⟩,⟨319197, by decide⟩,⟨319286, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6478_319287 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6478 ⟨319287, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6478
    ⟨319287, by decide⟩ (by decide) (![⟨319059, by decide⟩,⟨319121, by decide⟩,⟨319197, by decide⟩,⟨319286, by decide⟩]) unmarked_context_11_6478_319287 node_context_11_6478_319287
  intro a
  fin_cases a
  · exact context_12_25912_319059
  · exact context_12_25913_319121
  · exact context_12_25914_319197
  · exact context_12_25915_319286

theorem selected_cut_11975 : selected 8 ⟨319290, by decide⟩
    (prefixPartial 13 103664) = some ⟨13, 2, 0, 319290, 103664, 109, 16384⟩ := by
  decide +kernel

theorem context_13_103664_319290 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103664 ⟨319290, by decide⟩ :=
  accepted_of_selected 13 103664 ⟨319290, by decide⟩ ⟨13, 2, 0, 319290, 103664, 109, 16384⟩
    (by decide) selected_cut_11975

theorem selected_cut_11976 : selected 8 ⟨319313, by decide⟩
    (prefixPartial 13 103665) = some ⟨13, 2, 0, 319313, 103665, 1893, 16384⟩ := by
  decide +kernel

theorem context_13_103665_319313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103665 ⟨319313, by decide⟩ :=
  accepted_of_selected 13 103665 ⟨319313, by decide⟩ ⟨13, 2, 0, 319313, 103665, 1893, 16384⟩
    (by decide) selected_cut_11976

theorem selected_cut_11977 : selected 8 ⟨319333, by decide⟩
    (prefixPartial 13 103666) = some ⟨13, 2, 0, 319333, 103666, 1589, 16384⟩ := by
  decide +kernel

theorem context_13_103666_319333 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103666 ⟨319333, by decide⟩ :=
  accepted_of_selected 13 103666 ⟨319333, by decide⟩ ⟨13, 2, 0, 319333, 103666, 1589, 16384⟩
    (by decide) selected_cut_11977

theorem selected_cut_11978 : selected 8 ⟨319338, by decide⟩
    (prefixPartial 13 103667) = some ⟨13, 2, 0, 319338, 103667, 1061, 16384⟩ := by
  decide +kernel

theorem context_13_103667_319338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103667 ⟨319338, by decide⟩ :=
  accepted_of_selected 13 103667 ⟨319338, by decide⟩ ⟨13, 2, 0, 319338, 103667, 1061, 16384⟩
    (by decide) selected_cut_11978

theorem unmarked_context_12_25916_319339 : frontier 9 ⟨319339, by decide⟩
    (prefixCache 12 25916) (prefixPartial 12 25916) = false := by
  decide +kernel

theorem node_context_12_25916_319339 : EJMOriginalGlobalDAGData.nodes 9 ⟨319339, by decide⟩ =
    .split (coordinate 12) (![⟨319290, by decide⟩,⟨319313, by decide⟩,⟨319333, by decide⟩,⟨319338, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25916_319339 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25916 ⟨319339, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25916
    ⟨319339, by decide⟩ (by decide) (![⟨319290, by decide⟩,⟨319313, by decide⟩,⟨319333, by decide⟩,⟨319338, by decide⟩]) unmarked_context_12_25916_319339 node_context_12_25916_319339
  intro a
  fin_cases a
  · exact context_13_103664_319290
  · exact context_13_103665_319313
  · exact context_13_103666_319333
  · exact context_13_103667_319338

theorem selected_cut_11979 : selected 8 ⟨319344, by decide⟩
    (prefixPartial 13 103668) = some ⟨13, 2, 0, 319344, 103668, 149, 16384⟩ := by
  decide +kernel

theorem context_13_103668_319344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103668 ⟨319344, by decide⟩ :=
  accepted_of_selected 13 103668 ⟨319344, by decide⟩ ⟨13, 2, 0, 319344, 103668, 149, 16384⟩
    (by decide) selected_cut_11979

theorem selected_cut_11980 : selected 8 ⟨319369, by decide⟩
    (prefixPartial 13 103669) = some ⟨13, 2, 0, 319369, 103669, 2089, 16384⟩ := by
  decide +kernel

theorem context_13_103669_319369 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103669 ⟨319369, by decide⟩ :=
  accepted_of_selected 13 103669 ⟨319369, by decide⟩ ⟨13, 2, 0, 319369, 103669, 2089, 16384⟩
    (by decide) selected_cut_11980

theorem selected_cut_11981 : selected 8 ⟨319390, by decide⟩
    (prefixPartial 13 103670) = some ⟨13, 2, 0, 319390, 103670, 1669, 16384⟩ := by
  decide +kernel

theorem context_13_103670_319390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103670 ⟨319390, by decide⟩ :=
  accepted_of_selected 13 103670 ⟨319390, by decide⟩ ⟨13, 2, 0, 319390, 103670, 1669, 16384⟩
    (by decide) selected_cut_11981

theorem selected_cut_11982 : selected 8 ⟨319398, by decide⟩
    (prefixPartial 13 103671) = some ⟨13, 2, 0, 319398, 103671, 901, 16384⟩ := by
  decide +kernel

theorem context_13_103671_319398 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103671 ⟨319398, by decide⟩ :=
  accepted_of_selected 13 103671 ⟨319398, by decide⟩ ⟨13, 2, 0, 319398, 103671, 901, 16384⟩
    (by decide) selected_cut_11982

theorem unmarked_context_12_25917_319399 : frontier 9 ⟨319399, by decide⟩
    (prefixCache 12 25917) (prefixPartial 12 25917) = false := by
  decide +kernel

theorem node_context_12_25917_319399 : EJMOriginalGlobalDAGData.nodes 9 ⟨319399, by decide⟩ =
    .split (coordinate 12) (![⟨319344, by decide⟩,⟨319369, by decide⟩,⟨319390, by decide⟩,⟨319398, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25917_319399 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25917 ⟨319399, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25917
    ⟨319399, by decide⟩ (by decide) (![⟨319344, by decide⟩,⟨319369, by decide⟩,⟨319390, by decide⟩,⟨319398, by decide⟩]) unmarked_context_12_25917_319399 node_context_12_25917_319399
  intro a
  fin_cases a
  · exact context_13_103668_319344
  · exact context_13_103669_319369
  · exact context_13_103670_319390
  · exact context_13_103671_319398

theorem selected_cut_11983 : selected 8 ⟨319404, by decide⟩
    (prefixPartial 13 103672) = some ⟨13, 2, 0, 319404, 103672, 105, 16384⟩ := by
  decide +kernel

theorem context_13_103672_319404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103672 ⟨319404, by decide⟩ :=
  accepted_of_selected 13 103672 ⟨319404, by decide⟩ ⟨13, 2, 0, 319404, 103672, 105, 16384⟩
    (by decide) selected_cut_11983

theorem selected_cut_11984 : selected 8 ⟨319433, by decide⟩
    (prefixPartial 13 103673) = some ⟨13, 2, 0, 319433, 103673, 2253, 16384⟩ := by
  decide +kernel

theorem context_13_103673_319433 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103673 ⟨319433, by decide⟩ :=
  accepted_of_selected 13 103673 ⟨319433, by decide⟩ ⟨13, 2, 0, 319433, 103673, 2253, 16384⟩
    (by decide) selected_cut_11984

theorem selected_cut_11985 : selected 8 ⟨319456, by decide⟩
    (prefixPartial 13 103674) = some ⟨13, 2, 0, 319456, 103674, 1537, 16384⟩ := by
  decide +kernel

theorem context_13_103674_319456 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103674 ⟨319456, by decide⟩ :=
  accepted_of_selected 13 103674 ⟨319456, by decide⟩ ⟨13, 2, 0, 319456, 103674, 1537, 16384⟩
    (by decide) selected_cut_11985

theorem selected_cut_11986 : selected 8 ⟨319467, by decide⟩
    (prefixPartial 13 103675) = some ⟨13, 2, 0, 319467, 103675, 1029, 16384⟩ := by
  decide +kernel

theorem context_13_103675_319467 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103675 ⟨319467, by decide⟩ :=
  accepted_of_selected 13 103675 ⟨319467, by decide⟩ ⟨13, 2, 0, 319467, 103675, 1029, 16384⟩
    (by decide) selected_cut_11986

theorem unmarked_context_12_25918_319468 : frontier 9 ⟨319468, by decide⟩
    (prefixCache 12 25918) (prefixPartial 12 25918) = false := by
  decide +kernel

theorem node_context_12_25918_319468 : EJMOriginalGlobalDAGData.nodes 9 ⟨319468, by decide⟩ =
    .split (coordinate 12) (![⟨319404, by decide⟩,⟨319433, by decide⟩,⟨319456, by decide⟩,⟨319467, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25918_319468 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25918 ⟨319468, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25918
    ⟨319468, by decide⟩ (by decide) (![⟨319404, by decide⟩,⟨319433, by decide⟩,⟨319456, by decide⟩,⟨319467, by decide⟩]) unmarked_context_12_25918_319468 node_context_12_25918_319468
  intro a
  fin_cases a
  · exact context_13_103672_319404
  · exact context_13_103673_319433
  · exact context_13_103674_319456
  · exact context_13_103675_319467

theorem selected_cut_11987 : selected 8 ⟨319472, by decide⟩
    (prefixPartial 13 103676) = some ⟨13, 2, 0, 319472, 103676, 73, 16384⟩ := by
  decide +kernel

theorem context_13_103676_319472 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103676 ⟨319472, by decide⟩ :=
  accepted_of_selected 13 103676 ⟨319472, by decide⟩ ⟨13, 2, 0, 319472, 103676, 73, 16384⟩
    (by decide) selected_cut_11987

theorem selected_cut_11988 : selected 8 ⟨319501, by decide⟩
    (prefixPartial 13 103677) = some ⟨13, 2, 0, 319501, 103677, 2573, 16384⟩ := by
  decide +kernel

theorem context_13_103677_319501 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103677 ⟨319501, by decide⟩ :=
  accepted_of_selected 13 103677 ⟨319501, by decide⟩ ⟨13, 2, 0, 319501, 103677, 2573, 16384⟩
    (by decide) selected_cut_11988

theorem selected_cut_11989 : selected 8 ⟨319525, by decide⟩
    (prefixPartial 13 103678) = some ⟨13, 2, 0, 319525, 103678, 1829, 16384⟩ := by
  decide +kernel

theorem context_13_103678_319525 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103678 ⟨319525, by decide⟩ :=
  accepted_of_selected 13 103678 ⟨319525, by decide⟩ ⟨13, 2, 0, 319525, 103678, 1829, 16384⟩
    (by decide) selected_cut_11989

theorem selected_cut_11990 : selected 8 ⟨319531, by decide⟩
    (prefixPartial 13 103679) = some ⟨13, 2, 0, 319531, 103679, 1093, 16384⟩ := by
  decide +kernel

theorem context_13_103679_319531 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103679 ⟨319531, by decide⟩ :=
  accepted_of_selected 13 103679 ⟨319531, by decide⟩ ⟨13, 2, 0, 319531, 103679, 1093, 16384⟩
    (by decide) selected_cut_11990

theorem unmarked_context_12_25919_319532 : frontier 9 ⟨319532, by decide⟩
    (prefixCache 12 25919) (prefixPartial 12 25919) = false := by
  decide +kernel

theorem node_context_12_25919_319532 : EJMOriginalGlobalDAGData.nodes 9 ⟨319532, by decide⟩ =
    .split (coordinate 12) (![⟨319472, by decide⟩,⟨319501, by decide⟩,⟨319525, by decide⟩,⟨319531, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25919_319532 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25919 ⟨319532, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25919
    ⟨319532, by decide⟩ (by decide) (![⟨319472, by decide⟩,⟨319501, by decide⟩,⟨319525, by decide⟩,⟨319531, by decide⟩]) unmarked_context_12_25919_319532 node_context_12_25919_319532
  intro a
  fin_cases a
  · exact context_13_103676_319472
  · exact context_13_103677_319501
  · exact context_13_103678_319525
  · exact context_13_103679_319531

theorem unmarked_context_11_6479_319533 : frontier 10 ⟨319533, by decide⟩
    (prefixCache 11 6479) (prefixPartial 11 6479) = false := by
  decide +kernel

theorem node_context_11_6479_319533 : EJMOriginalGlobalDAGData.nodes 10 ⟨319533, by decide⟩ =
    .split (coordinate 11) (![⟨319339, by decide⟩,⟨319399, by decide⟩,⟨319468, by decide⟩,⟨319532, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6479_319533 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6479 ⟨319533, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6479
    ⟨319533, by decide⟩ (by decide) (![⟨319339, by decide⟩,⟨319399, by decide⟩,⟨319468, by decide⟩,⟨319532, by decide⟩]) unmarked_context_11_6479_319533 node_context_11_6479_319533
  intro a
  fin_cases a
  · exact context_12_25916_319339
  · exact context_12_25917_319399
  · exact context_12_25918_319468
  · exact context_12_25919_319532

theorem unmarked_context_10_1619_319534 : frontier 11 ⟨319534, by decide⟩
    (prefixCache 10 1619) (prefixPartial 10 1619) = false := by
  decide +kernel

theorem node_context_10_1619_319534 : EJMOriginalGlobalDAGData.nodes 11 ⟨319534, by decide⟩ =
    .split (coordinate 10) (![⟨318728, by decide⟩,⟨318991, by decide⟩,⟨319287, by decide⟩,⟨319533, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1619_319534 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1619 ⟨319534, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1619
    ⟨319534, by decide⟩ (by decide) (![⟨318728, by decide⟩,⟨318991, by decide⟩,⟨319287, by decide⟩,⟨319533, by decide⟩]) unmarked_context_10_1619_319534 node_context_10_1619_319534
  intro a
  fin_cases a
  · exact context_11_6476_318728
  · exact context_11_6477_318991
  · exact context_11_6478_319287
  · exact context_11_6479_319533

theorem unmarked_context_9_404_319535 : frontier 12 ⟨319535, by decide⟩
    (prefixCache 9 404) (prefixPartial 9 404) = false := by
  decide +kernel

theorem node_context_9_404_319535 : EJMOriginalGlobalDAGData.nodes 12 ⟨319535, by decide⟩ =
    .split (coordinate 9) (![⟨315885, by decide⟩,⟨317156, by decide⟩,⟨318404, by decide⟩,⟨319534, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_404_319535 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 404 ⟨319535, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 404
    ⟨319535, by decide⟩ (by decide) (![⟨315885, by decide⟩,⟨317156, by decide⟩,⟨318404, by decide⟩,⟨319534, by decide⟩]) unmarked_context_9_404_319535 node_context_9_404_319535
  intro a
  fin_cases a
  · exact context_10_1616_315885
  · exact context_10_1617_317156
  · exact context_10_1618_318404
  · exact context_10_1619_319534

theorem selected_cut_11991 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 103680) = some ⟨13, 1, 0, 3444, 103680, 1, 16384⟩ := by
  decide +kernel

theorem context_13_103680_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103680 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 103680 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 103680, 1, 16384⟩
    (by decide) selected_cut_11991

theorem selected_cut_11992 : selected 8 ⟨319558, by decide⟩
    (prefixPartial 13 103681) = some ⟨13, 2, 0, 319558, 103681, 2461, 16384⟩ := by
  decide +kernel

theorem context_13_103681_319558 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103681 ⟨319558, by decide⟩ :=
  accepted_of_selected 13 103681 ⟨319558, by decide⟩ ⟨13, 2, 0, 319558, 103681, 2461, 16384⟩
    (by decide) selected_cut_11992

theorem selected_cut_11993 : selected 8 ⟨319580, by decide⟩
    (prefixPartial 13 103682) = some ⟨13, 2, 0, 319580, 103682, 2109, 16384⟩ := by
  decide +kernel

theorem context_13_103682_319580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103682 ⟨319580, by decide⟩ :=
  accepted_of_selected 13 103682 ⟨319580, by decide⟩ ⟨13, 2, 0, 319580, 103682, 2109, 16384⟩
    (by decide) selected_cut_11993

theorem selected_cut_11994 : selected 8 ⟨319589, by decide⟩
    (prefixPartial 13 103683) = some ⟨13, 2, 0, 319589, 103683, 889, 16384⟩ := by
  decide +kernel

theorem context_13_103683_319589 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103683 ⟨319589, by decide⟩ :=
  accepted_of_selected 13 103683 ⟨319589, by decide⟩ ⟨13, 2, 0, 319589, 103683, 889, 16384⟩
    (by decide) selected_cut_11994

theorem unmarked_context_12_25920_319590 : frontier 9 ⟨319590, by decide⟩
    (prefixCache 12 25920) (prefixPartial 12 25920) = false := by
  decide +kernel

theorem node_context_12_25920_319590 : EJMOriginalGlobalDAGData.nodes 9 ⟨319590, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨319558, by decide⟩,⟨319580, by decide⟩,⟨319589, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25920_319590 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25920 ⟨319590, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25920
    ⟨319590, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨319558, by decide⟩,⟨319580, by decide⟩,⟨319589, by decide⟩]) unmarked_context_12_25920_319590 node_context_12_25920_319590
  intro a
  fin_cases a
  · exact context_13_103680_3444
  · exact context_13_103681_319558
  · exact context_13_103682_319580
  · exact context_13_103683_319589

theorem selected_cut_11995 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 103684) = some ⟨13, 1, 0, 3444, 103684, 1, 16384⟩ := by
  decide +kernel

theorem context_13_103684_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103684 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 103684 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 103684, 1, 16384⟩
    (by decide) selected_cut_11995

theorem selected_cut_11996 : selected 8 ⟨319627, by decide⟩
    (prefixPartial 13 103685) = some ⟨13, 2, 0, 319627, 103685, 3049, 16384⟩ := by
  decide +kernel

theorem context_13_103685_319627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103685 ⟨319627, by decide⟩ :=
  accepted_of_selected 13 103685 ⟨319627, by decide⟩ ⟨13, 2, 0, 319627, 103685, 3049, 16384⟩
    (by decide) selected_cut_11996

theorem selected_cut_11997 : selected 8 ⟨319686, by decide⟩
    (prefixPartial 13 103686) = some ⟨13, 2, 0, 319686, 103686, 3077, 16384⟩ := by
  decide +kernel

theorem context_13_103686_319686 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103686 ⟨319686, by decide⟩ :=
  accepted_of_selected 13 103686 ⟨319686, by decide⟩ ⟨13, 2, 0, 319686, 103686, 3077, 16384⟩
    (by decide) selected_cut_11997

theorem selected_cut_11998 : selected 8 ⟨319698, by decide⟩
    (prefixPartial 13 103687) = some ⟨13, 2, 0, 319698, 103687, 1253, 16384⟩ := by
  decide +kernel

theorem context_13_103687_319698 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103687 ⟨319698, by decide⟩ :=
  accepted_of_selected 13 103687 ⟨319698, by decide⟩ ⟨13, 2, 0, 319698, 103687, 1253, 16384⟩
    (by decide) selected_cut_11998

theorem unmarked_context_12_25921_319699 : frontier 9 ⟨319699, by decide⟩
    (prefixCache 12 25921) (prefixPartial 12 25921) = false := by
  decide +kernel

theorem node_context_12_25921_319699 : EJMOriginalGlobalDAGData.nodes 9 ⟨319699, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨319627, by decide⟩,⟨319686, by decide⟩,⟨319698, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25921_319699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25921 ⟨319699, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25921
    ⟨319699, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨319627, by decide⟩,⟨319686, by decide⟩,⟨319698, by decide⟩]) unmarked_context_12_25921_319699 node_context_12_25921_319699
  intro a
  fin_cases a
  · exact context_13_103684_3444
  · exact context_13_103685_319627
  · exact context_13_103686_319686
  · exact context_13_103687_319698

theorem selected_cut_11999 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 103688) = some ⟨13, 1, 0, 3444, 103688, 1, 16384⟩ := by
  decide +kernel

theorem context_13_103688_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103688 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 103688 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 103688, 1, 16384⟩
    (by decide) selected_cut_11999

theorem selected_cut_12000 : selected 8 ⟨319737, by decide⟩
    (prefixPartial 13 103689) = some ⟨13, 2, 0, 319737, 103689, 2369, 16384⟩ := by
  decide +kernel

theorem context_13_103689_319737 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103689 ⟨319737, by decide⟩ :=
  accepted_of_selected 13 103689 ⟨319737, by decide⟩ ⟨13, 2, 0, 319737, 103689, 2369, 16384⟩
    (by decide) selected_cut_12000

theorem selected_cut_12001 : selected 8 ⟨319761, by decide⟩
    (prefixPartial 13 103690) = some ⟨13, 2, 0, 319761, 103690, 2481, 16384⟩ := by
  decide +kernel

theorem context_13_103690_319761 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103690 ⟨319761, by decide⟩ :=
  accepted_of_selected 13 103690 ⟨319761, by decide⟩ ⟨13, 2, 0, 319761, 103690, 2481, 16384⟩
    (by decide) selected_cut_12001

theorem selected_cut_12002 : selected 8 ⟨319768, by decide⟩
    (prefixPartial 13 103691) = some ⟨13, 2, 0, 319768, 103691, 1049, 16384⟩ := by
  decide +kernel

theorem context_13_103691_319768 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103691 ⟨319768, by decide⟩ :=
  accepted_of_selected 13 103691 ⟨319768, by decide⟩ ⟨13, 2, 0, 319768, 103691, 1049, 16384⟩
    (by decide) selected_cut_12002

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
