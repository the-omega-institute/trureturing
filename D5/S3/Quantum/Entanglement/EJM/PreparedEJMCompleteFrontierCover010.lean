/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover009
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_11_1048_37927 : frontier 10 ⟨37927, by decide⟩
    (prefixCache 11 1048) (prefixPartial 11 1048) = false := by
  decide +kernel

theorem node_context_11_1048_37927 : EJMOriginalGlobalDAGData.nodes 10 ⟨37927, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨37881, by decide⟩,⟨37926, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1048_37927 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1048 ⟨37927, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1048
    ⟨37927, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨37881, by decide⟩,⟨37926, by decide⟩]) unmarked_context_11_1048_37927 node_context_11_1048_37927
  intro a
  fin_cases a
  · exact context_12_4192_1738
  · exact context_12_4193_1738
  · exact context_12_4194_37881
  · exact context_12_4195_37926

theorem selected_cut_00962 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 4196) = some ⟨12, 1, 0, 1738, 4196, 1, 65536⟩ := by
  decide +kernel

theorem context_12_4196_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4196 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 4196 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 4196, 1, 65536⟩
    (by decide) selected_cut_00962

theorem selected_cut_00963 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 4197) = some ⟨12, 1, 0, 1738, 4197, 1, 65536⟩ := by
  decide +kernel

theorem context_12_4197_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4197 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 4197 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 4197, 1, 65536⟩
    (by decide) selected_cut_00963

theorem selected_cut_00964 : selected 9 ⟨38048, by decide⟩
    (prefixPartial 12 4198) = some ⟨12, 2, 0, 38048, 4198, 3505, 65536⟩ := by
  decide +kernel

theorem context_12_4198_38048 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4198 ⟨38048, by decide⟩ :=
  accepted_of_selected 12 4198 ⟨38048, by decide⟩ ⟨12, 2, 0, 38048, 4198, 3505, 65536⟩
    (by decide) selected_cut_00964

theorem selected_cut_00965 : selected 9 ⟨38139, by decide⟩
    (prefixPartial 12 4199) = some ⟨12, 2, 0, 38139, 4199, 2861, 65536⟩ := by
  decide +kernel

theorem context_12_4199_38139 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4199 ⟨38139, by decide⟩ :=
  accepted_of_selected 12 4199 ⟨38139, by decide⟩ ⟨12, 2, 0, 38139, 4199, 2861, 65536⟩
    (by decide) selected_cut_00965

theorem unmarked_context_11_1049_38140 : frontier 10 ⟨38140, by decide⟩
    (prefixCache 11 1049) (prefixPartial 11 1049) = false := by
  decide +kernel

theorem node_context_11_1049_38140 : EJMOriginalGlobalDAGData.nodes 10 ⟨38140, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨38048, by decide⟩,⟨38139, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1049_38140 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1049 ⟨38140, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1049
    ⟨38140, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨38048, by decide⟩,⟨38139, by decide⟩]) unmarked_context_11_1049_38140 node_context_11_1049_38140
  intro a
  fin_cases a
  · exact context_12_4196_1738
  · exact context_12_4197_1738
  · exact context_12_4198_38048
  · exact context_12_4199_38139

theorem selected_cut_00966 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 4200) = some ⟨12, 1, 0, 1738, 4200, 1, 65536⟩ := by
  decide +kernel

theorem context_12_4200_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4200 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 4200 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 4200, 1, 65536⟩
    (by decide) selected_cut_00966

theorem selected_cut_00967 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 4201) = some ⟨12, 1, 0, 1738, 4201, 1, 65536⟩ := by
  decide +kernel

theorem context_12_4201_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4201 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 4201 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 4201, 1, 65536⟩
    (by decide) selected_cut_00967

theorem selected_cut_00968 : selected 9 ⟨38220, by decide⟩
    (prefixPartial 12 4202) = some ⟨12, 2, 0, 38220, 4202, 2917, 65536⟩ := by
  decide +kernel

theorem context_12_4202_38220 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4202 ⟨38220, by decide⟩ :=
  accepted_of_selected 12 4202 ⟨38220, by decide⟩ ⟨12, 2, 0, 38220, 4202, 2917, 65536⟩
    (by decide) selected_cut_00968

theorem selected_cut_00969 : selected 9 ⟨38290, by decide⟩
    (prefixPartial 12 4203) = some ⟨12, 2, 0, 38290, 4203, 4065, 65536⟩ := by
  decide +kernel

theorem context_12_4203_38290 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4203 ⟨38290, by decide⟩ :=
  accepted_of_selected 12 4203 ⟨38290, by decide⟩ ⟨12, 2, 0, 38290, 4203, 4065, 65536⟩
    (by decide) selected_cut_00969

theorem unmarked_context_11_1050_38291 : frontier 10 ⟨38291, by decide⟩
    (prefixCache 11 1050) (prefixPartial 11 1050) = false := by
  decide +kernel

theorem node_context_11_1050_38291 : EJMOriginalGlobalDAGData.nodes 10 ⟨38291, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨38220, by decide⟩,⟨38290, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1050_38291 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1050 ⟨38291, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1050
    ⟨38291, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨38220, by decide⟩,⟨38290, by decide⟩]) unmarked_context_11_1050_38291 node_context_11_1050_38291
  intro a
  fin_cases a
  · exact context_12_4200_1738
  · exact context_12_4201_1738
  · exact context_12_4202_38220
  · exact context_12_4203_38290

theorem selected_cut_00970 : selected 10 ⟨38409, by decide⟩
    (prefixPartial 11 1051) = some ⟨11, 2, 0, 38409, 1051, 2973, 262144⟩ := by
  decide +kernel

theorem context_11_1051_38409 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1051 ⟨38409, by decide⟩ :=
  accepted_of_selected 11 1051 ⟨38409, by decide⟩ ⟨11, 2, 0, 38409, 1051, 2973, 262144⟩
    (by decide) selected_cut_00970

theorem unmarked_context_10_262_38410 : frontier 11 ⟨38410, by decide⟩
    (prefixCache 10 262) (prefixPartial 10 262) = false := by
  decide +kernel

theorem node_context_10_262_38410 : EJMOriginalGlobalDAGData.nodes 11 ⟨38410, by decide⟩ =
    .split (coordinate 10) (![⟨37927, by decide⟩,⟨38140, by decide⟩,⟨38291, by decide⟩,⟨38409, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_262_38410 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 262 ⟨38410, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 262
    ⟨38410, by decide⟩ (by decide) (![⟨37927, by decide⟩,⟨38140, by decide⟩,⟨38291, by decide⟩,⟨38409, by decide⟩]) unmarked_context_10_262_38410 node_context_10_262_38410
  intro a
  fin_cases a
  · exact context_11_1048_37927
  · exact context_11_1049_38140
  · exact context_11_1050_38291
  · exact context_11_1051_38409

theorem selected_cut_00971 : selected 11 ⟨3440, by decide⟩
    (prefixPartial 10 263) = some ⟨10, 1, 0, 3440, 263, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_263_3440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 263 ⟨3440, by decide⟩ :=
  accepted_of_selected 10 263 ⟨3440, by decide⟩ ⟨10, 1, 0, 3440, 263, 1, 1048576⟩
    (by decide) selected_cut_00971

theorem unmarked_context_9_65_38411 : frontier 12 ⟨38411, by decide⟩
    (prefixCache 9 65) (prefixPartial 9 65) = false := by
  decide +kernel

theorem node_context_9_65_38411 : EJMOriginalGlobalDAGData.nodes 12 ⟨38411, by decide⟩ =
    .split (coordinate 9) (![⟨37189, by decide⟩,⟨37817, by decide⟩,⟨38410, by decide⟩,⟨3440, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_65_38411 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 65 ⟨38411, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 65
    ⟨38411, by decide⟩ (by decide) (![⟨37189, by decide⟩,⟨37817, by decide⟩,⟨38410, by decide⟩,⟨3440, by decide⟩]) unmarked_context_9_65_38411 node_context_9_65_38411
  intro a
  fin_cases a
  · exact context_10_260_37189
  · exact context_10_261_37817
  · exact context_10_262_38410
  · exact context_10_263_3440

theorem selected_cut_00972 : selected 9 ⟨38521, by decide⟩
    (prefixPartial 12 4224) = some ⟨12, 2, 0, 38521, 4224, 925, 65536⟩ := by
  decide +kernel

theorem context_12_4224_38521 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4224 ⟨38521, by decide⟩ :=
  accepted_of_selected 12 4224 ⟨38521, by decide⟩ ⟨12, 2, 0, 38521, 4224, 925, 65536⟩
    (by decide) selected_cut_00972

theorem selected_cut_00973 : selected 9 ⟨38570, by decide⟩
    (prefixPartial 12 4225) = some ⟨12, 2, 0, 38570, 4225, 3385, 65536⟩ := by
  decide +kernel

theorem context_12_4225_38570 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4225 ⟨38570, by decide⟩ :=
  accepted_of_selected 12 4225 ⟨38570, by decide⟩ ⟨12, 2, 0, 38570, 4225, 3385, 65536⟩
    (by decide) selected_cut_00973

theorem selected_cut_00974 : selected 9 ⟨38623, by decide⟩
    (prefixPartial 12 4226) = some ⟨12, 2, 0, 38623, 4226, 2977, 65536⟩ := by
  decide +kernel

theorem context_12_4226_38623 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4226 ⟨38623, by decide⟩ :=
  accepted_of_selected 12 4226 ⟨38623, by decide⟩ ⟨12, 2, 0, 38623, 4226, 2977, 65536⟩
    (by decide) selected_cut_00974

theorem selected_cut_00975 : selected 9 ⟨38685, by decide⟩
    (prefixPartial 12 4227) = some ⟨12, 2, 0, 38685, 4227, 2985, 65536⟩ := by
  decide +kernel

theorem context_12_4227_38685 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4227 ⟨38685, by decide⟩ :=
  accepted_of_selected 12 4227 ⟨38685, by decide⟩ ⟨12, 2, 0, 38685, 4227, 2985, 65536⟩
    (by decide) selected_cut_00975

theorem unmarked_context_11_1056_38686 : frontier 10 ⟨38686, by decide⟩
    (prefixCache 11 1056) (prefixPartial 11 1056) = false := by
  decide +kernel

theorem node_context_11_1056_38686 : EJMOriginalGlobalDAGData.nodes 10 ⟨38686, by decide⟩ =
    .split (coordinate 11) (![⟨38521, by decide⟩,⟨38570, by decide⟩,⟨38623, by decide⟩,⟨38685, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1056_38686 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1056 ⟨38686, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1056
    ⟨38686, by decide⟩ (by decide) (![⟨38521, by decide⟩,⟨38570, by decide⟩,⟨38623, by decide⟩,⟨38685, by decide⟩]) unmarked_context_11_1056_38686 node_context_11_1056_38686
  intro a
  fin_cases a
  · exact context_12_4224_38521
  · exact context_12_4225_38570
  · exact context_12_4226_38623
  · exact context_12_4227_38685

theorem selected_cut_00976 : selected 9 ⟨38713, by decide⟩
    (prefixPartial 12 4228) = some ⟨12, 2, 0, 38713, 4228, 1009, 65536⟩ := by
  decide +kernel

theorem context_12_4228_38713 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4228 ⟨38713, by decide⟩ :=
  accepted_of_selected 12 4228 ⟨38713, by decide⟩ ⟨12, 2, 0, 38713, 4228, 1009, 65536⟩
    (by decide) selected_cut_00976

theorem selected_cut_00977 : selected 9 ⟨38779, by decide⟩
    (prefixPartial 12 4229) = some ⟨12, 2, 0, 38779, 4229, 2401, 65536⟩ := by
  decide +kernel

theorem context_12_4229_38779 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4229 ⟨38779, by decide⟩ :=
  accepted_of_selected 12 4229 ⟨38779, by decide⟩ ⟨12, 2, 0, 38779, 4229, 2401, 65536⟩
    (by decide) selected_cut_00977

theorem selected_cut_00978 : selected 9 ⟨38825, by decide⟩
    (prefixPartial 12 4230) = some ⟨12, 2, 0, 38825, 4230, 2173, 65536⟩ := by
  decide +kernel

theorem context_12_4230_38825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4230 ⟨38825, by decide⟩ :=
  accepted_of_selected 12 4230 ⟨38825, by decide⟩ ⟨12, 2, 0, 38825, 4230, 2173, 65536⟩
    (by decide) selected_cut_00978

theorem selected_cut_00979 : selected 9 ⟨38871, by decide⟩
    (prefixPartial 12 4231) = some ⟨12, 2, 0, 38871, 4231, 2141, 65536⟩ := by
  decide +kernel

theorem context_12_4231_38871 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4231 ⟨38871, by decide⟩ :=
  accepted_of_selected 12 4231 ⟨38871, by decide⟩ ⟨12, 2, 0, 38871, 4231, 2141, 65536⟩
    (by decide) selected_cut_00979

theorem unmarked_context_11_1057_38872 : frontier 10 ⟨38872, by decide⟩
    (prefixCache 11 1057) (prefixPartial 11 1057) = false := by
  decide +kernel

theorem node_context_11_1057_38872 : EJMOriginalGlobalDAGData.nodes 10 ⟨38872, by decide⟩ =
    .split (coordinate 11) (![⟨38713, by decide⟩,⟨38779, by decide⟩,⟨38825, by decide⟩,⟨38871, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1057_38872 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1057 ⟨38872, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1057
    ⟨38872, by decide⟩ (by decide) (![⟨38713, by decide⟩,⟨38779, by decide⟩,⟨38825, by decide⟩,⟨38871, by decide⟩]) unmarked_context_11_1057_38872 node_context_11_1057_38872
  intro a
  fin_cases a
  · exact context_12_4228_38713
  · exact context_12_4229_38779
  · exact context_12_4230_38825
  · exact context_12_4231_38871

theorem selected_cut_00980 : selected 9 ⟨38908, by decide⟩
    (prefixPartial 12 4232) = some ⟨12, 2, 0, 38908, 4232, 1053, 65536⟩ := by
  decide +kernel

theorem context_12_4232_38908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4232 ⟨38908, by decide⟩ :=
  accepted_of_selected 12 4232 ⟨38908, by decide⟩ ⟨12, 2, 0, 38908, 4232, 1053, 65536⟩
    (by decide) selected_cut_00980

theorem selected_cut_00981 : selected 9 ⟨38963, by decide⟩
    (prefixPartial 12 4233) = some ⟨12, 2, 0, 38963, 4233, 2205, 65536⟩ := by
  decide +kernel

theorem context_12_4233_38963 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4233 ⟨38963, by decide⟩ :=
  accepted_of_selected 12 4233 ⟨38963, by decide⟩ ⟨12, 2, 0, 38963, 4233, 2205, 65536⟩
    (by decide) selected_cut_00981

theorem selected_cut_00982 : selected 9 ⟨38999, by decide⟩
    (prefixPartial 12 4234) = some ⟨12, 2, 0, 38999, 4234, 1761, 65536⟩ := by
  decide +kernel

theorem context_12_4234_38999 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4234 ⟨38999, by decide⟩ :=
  accepted_of_selected 12 4234 ⟨38999, by decide⟩ ⟨12, 2, 0, 38999, 4234, 1761, 65536⟩
    (by decide) selected_cut_00982

theorem selected_cut_00983 : selected 9 ⟨39041, by decide⟩
    (prefixPartial 12 4235) = some ⟨12, 2, 0, 39041, 4235, 1905, 65536⟩ := by
  decide +kernel

theorem context_12_4235_39041 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4235 ⟨39041, by decide⟩ :=
  accepted_of_selected 12 4235 ⟨39041, by decide⟩ ⟨12, 2, 0, 39041, 4235, 1905, 65536⟩
    (by decide) selected_cut_00983

theorem unmarked_context_11_1058_39042 : frontier 10 ⟨39042, by decide⟩
    (prefixCache 11 1058) (prefixPartial 11 1058) = false := by
  decide +kernel

theorem node_context_11_1058_39042 : EJMOriginalGlobalDAGData.nodes 10 ⟨39042, by decide⟩ =
    .split (coordinate 11) (![⟨38908, by decide⟩,⟨38963, by decide⟩,⟨38999, by decide⟩,⟨39041, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1058_39042 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1058 ⟨39042, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1058
    ⟨39042, by decide⟩ (by decide) (![⟨38908, by decide⟩,⟨38963, by decide⟩,⟨38999, by decide⟩,⟨39041, by decide⟩]) unmarked_context_11_1058_39042 node_context_11_1058_39042
  intro a
  fin_cases a
  · exact context_12_4232_38908
  · exact context_12_4233_38963
  · exact context_12_4234_38999
  · exact context_12_4235_39041

theorem selected_cut_00984 : selected 9 ⟨39063, by decide⟩
    (prefixPartial 12 4236) = some ⟨12, 2, 0, 39063, 4236, 845, 65536⟩ := by
  decide +kernel

theorem context_12_4236_39063 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4236 ⟨39063, by decide⟩ :=
  accepted_of_selected 12 4236 ⟨39063, by decide⟩ ⟨12, 2, 0, 39063, 4236, 845, 65536⟩
    (by decide) selected_cut_00984

theorem selected_cut_00985 : selected 9 ⟨39113, by decide⟩
    (prefixPartial 12 4237) = some ⟨12, 2, 0, 39113, 4237, 1837, 65536⟩ := by
  decide +kernel

theorem context_12_4237_39113 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4237 ⟨39113, by decide⟩ :=
  accepted_of_selected 12 4237 ⟨39113, by decide⟩ ⟨12, 2, 0, 39113, 4237, 1837, 65536⟩
    (by decide) selected_cut_00985

theorem selected_cut_00986 : selected 9 ⟨39157, by decide⟩
    (prefixPartial 12 4238) = some ⟨12, 2, 0, 39157, 4238, 1565, 65536⟩ := by
  decide +kernel

theorem context_12_4238_39157 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4238 ⟨39157, by decide⟩ :=
  accepted_of_selected 12 4238 ⟨39157, by decide⟩ ⟨12, 2, 0, 39157, 4238, 1565, 65536⟩
    (by decide) selected_cut_00986

theorem selected_cut_00987 : selected 9 ⟨39194, by decide⟩
    (prefixPartial 12 4239) = some ⟨12, 2, 0, 39194, 4239, 1553, 65536⟩ := by
  decide +kernel

theorem context_12_4239_39194 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4239 ⟨39194, by decide⟩ :=
  accepted_of_selected 12 4239 ⟨39194, by decide⟩ ⟨12, 2, 0, 39194, 4239, 1553, 65536⟩
    (by decide) selected_cut_00987

theorem unmarked_context_11_1059_39195 : frontier 10 ⟨39195, by decide⟩
    (prefixCache 11 1059) (prefixPartial 11 1059) = false := by
  decide +kernel

theorem node_context_11_1059_39195 : EJMOriginalGlobalDAGData.nodes 10 ⟨39195, by decide⟩ =
    .split (coordinate 11) (![⟨39063, by decide⟩,⟨39113, by decide⟩,⟨39157, by decide⟩,⟨39194, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1059_39195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1059 ⟨39195, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1059
    ⟨39195, by decide⟩ (by decide) (![⟨39063, by decide⟩,⟨39113, by decide⟩,⟨39157, by decide⟩,⟨39194, by decide⟩]) unmarked_context_11_1059_39195 node_context_11_1059_39195
  intro a
  fin_cases a
  · exact context_12_4236_39063
  · exact context_12_4237_39113
  · exact context_12_4238_39157
  · exact context_12_4239_39194

theorem unmarked_context_10_264_39196 : frontier 11 ⟨39196, by decide⟩
    (prefixCache 10 264) (prefixPartial 10 264) = false := by
  decide +kernel

theorem node_context_10_264_39196 : EJMOriginalGlobalDAGData.nodes 11 ⟨39196, by decide⟩ =
    .split (coordinate 10) (![⟨38686, by decide⟩,⟨38872, by decide⟩,⟨39042, by decide⟩,⟨39195, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_264_39196 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 264 ⟨39196, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 264
    ⟨39196, by decide⟩ (by decide) (![⟨38686, by decide⟩,⟨38872, by decide⟩,⟨39042, by decide⟩,⟨39195, by decide⟩]) unmarked_context_10_264_39196 node_context_10_264_39196
  intro a
  fin_cases a
  · exact context_11_1056_38686
  · exact context_11_1057_38872
  · exact context_11_1058_39042
  · exact context_11_1059_39195

theorem selected_cut_00988 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 4240) = some ⟨12, 1, 0, 1738, 4240, 1, 65536⟩ := by
  decide +kernel

theorem context_12_4240_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4240 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 4240 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 4240, 1, 65536⟩
    (by decide) selected_cut_00988

theorem selected_cut_00989 : selected 9 ⟨39228, by decide⟩
    (prefixPartial 12 4241) = some ⟨12, 2, 0, 39228, 4241, 1225, 65536⟩ := by
  decide +kernel

theorem context_12_4241_39228 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4241 ⟨39228, by decide⟩ :=
  accepted_of_selected 12 4241 ⟨39228, by decide⟩ ⟨12, 2, 0, 39228, 4241, 1225, 65536⟩
    (by decide) selected_cut_00989

theorem selected_cut_00990 : selected 9 ⟨39262, by decide⟩
    (prefixPartial 12 4242) = some ⟨12, 2, 0, 39262, 4242, 1517, 65536⟩ := by
  decide +kernel

theorem context_12_4242_39262 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4242 ⟨39262, by decide⟩ :=
  accepted_of_selected 12 4242 ⟨39262, by decide⟩ ⟨12, 2, 0, 39262, 4242, 1517, 65536⟩
    (by decide) selected_cut_00990

theorem selected_cut_00991 : selected 9 ⟨39292, by decide⟩
    (prefixPartial 12 4243) = some ⟨12, 2, 0, 39292, 4243, 1449, 65536⟩ := by
  decide +kernel

theorem context_12_4243_39292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4243 ⟨39292, by decide⟩ :=
  accepted_of_selected 12 4243 ⟨39292, by decide⟩ ⟨12, 2, 0, 39292, 4243, 1449, 65536⟩
    (by decide) selected_cut_00991

theorem unmarked_context_11_1060_39293 : frontier 10 ⟨39293, by decide⟩
    (prefixCache 11 1060) (prefixPartial 11 1060) = false := by
  decide +kernel

theorem node_context_11_1060_39293 : EJMOriginalGlobalDAGData.nodes 10 ⟨39293, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨39228, by decide⟩,⟨39262, by decide⟩,⟨39292, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1060_39293 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1060 ⟨39293, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1060
    ⟨39293, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨39228, by decide⟩,⟨39262, by decide⟩,⟨39292, by decide⟩]) unmarked_context_11_1060_39293 node_context_11_1060_39293
  intro a
  fin_cases a
  · exact context_12_4240_1738
  · exact context_12_4241_39228
  · exact context_12_4242_39262
  · exact context_12_4243_39292

theorem selected_cut_00992 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 4244) = some ⟨12, 1, 0, 1738, 4244, 1, 65536⟩ := by
  decide +kernel

theorem context_12_4244_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4244 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 4244 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 4244, 1, 65536⟩
    (by decide) selected_cut_00992

theorem selected_cut_00993 : selected 9 ⟨39346, by decide⟩
    (prefixPartial 12 4245) = some ⟨12, 2, 0, 39346, 4245, 1189, 65536⟩ := by
  decide +kernel

theorem context_12_4245_39346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4245 ⟨39346, by decide⟩ :=
  accepted_of_selected 12 4245 ⟨39346, by decide⟩ ⟨12, 2, 0, 39346, 4245, 1189, 65536⟩
    (by decide) selected_cut_00993

theorem selected_cut_00994 : selected 9 ⟨39384, by decide⟩
    (prefixPartial 12 4246) = some ⟨12, 2, 0, 39384, 4246, 1505, 65536⟩ := by
  decide +kernel

theorem context_12_4246_39384 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4246 ⟨39384, by decide⟩ :=
  accepted_of_selected 12 4246 ⟨39384, by decide⟩ ⟨12, 2, 0, 39384, 4246, 1505, 65536⟩
    (by decide) selected_cut_00994

theorem selected_cut_00995 : selected 9 ⟨39429, by decide⟩
    (prefixPartial 12 4247) = some ⟨12, 2, 0, 39429, 4247, 1457, 65536⟩ := by
  decide +kernel

theorem context_12_4247_39429 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4247 ⟨39429, by decide⟩ :=
  accepted_of_selected 12 4247 ⟨39429, by decide⟩ ⟨12, 2, 0, 39429, 4247, 1457, 65536⟩
    (by decide) selected_cut_00995

theorem unmarked_context_11_1061_39430 : frontier 10 ⟨39430, by decide⟩
    (prefixCache 11 1061) (prefixPartial 11 1061) = false := by
  decide +kernel

theorem node_context_11_1061_39430 : EJMOriginalGlobalDAGData.nodes 10 ⟨39430, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨39346, by decide⟩,⟨39384, by decide⟩,⟨39429, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1061_39430 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1061 ⟨39430, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1061
    ⟨39430, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨39346, by decide⟩,⟨39384, by decide⟩,⟨39429, by decide⟩]) unmarked_context_11_1061_39430 node_context_11_1061_39430
  intro a
  fin_cases a
  · exact context_12_4244_1738
  · exact context_12_4245_39346
  · exact context_12_4246_39384
  · exact context_12_4247_39429

theorem selected_cut_00996 : selected 10 ⟨39555, by decide⟩
    (prefixPartial 11 1062) = some ⟨11, 2, 0, 39555, 1062, 3681, 262144⟩ := by
  decide +kernel

theorem context_11_1062_39555 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1062 ⟨39555, by decide⟩ :=
  accepted_of_selected 11 1062 ⟨39555, by decide⟩ ⟨11, 2, 0, 39555, 1062, 3681, 262144⟩
    (by decide) selected_cut_00996

theorem selected_cut_00997 : selected 10 ⟨39631, by decide⟩
    (prefixPartial 11 1063) = some ⟨11, 2, 0, 39631, 1063, 2733, 262144⟩ := by
  decide +kernel

theorem context_11_1063_39631 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1063 ⟨39631, by decide⟩ :=
  accepted_of_selected 11 1063 ⟨39631, by decide⟩ ⟨11, 2, 0, 39631, 1063, 2733, 262144⟩
    (by decide) selected_cut_00997

theorem unmarked_context_10_265_39632 : frontier 11 ⟨39632, by decide⟩
    (prefixCache 10 265) (prefixPartial 10 265) = false := by
  decide +kernel

theorem node_context_10_265_39632 : EJMOriginalGlobalDAGData.nodes 11 ⟨39632, by decide⟩ =
    .split (coordinate 10) (![⟨39293, by decide⟩,⟨39430, by decide⟩,⟨39555, by decide⟩,⟨39631, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_265_39632 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 265 ⟨39632, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 265
    ⟨39632, by decide⟩ (by decide) (![⟨39293, by decide⟩,⟨39430, by decide⟩,⟨39555, by decide⟩,⟨39631, by decide⟩]) unmarked_context_10_265_39632 node_context_10_265_39632
  intro a
  fin_cases a
  · exact context_11_1060_39293
  · exact context_11_1061_39430
  · exact context_11_1062_39555
  · exact context_11_1063_39631

theorem selected_cut_00998 : selected 11 ⟨39781, by decide⟩
    (prefixPartial 10 266) = some ⟨10, 2, 0, 39781, 266, 3409, 1048576⟩ := by
  decide +kernel

theorem context_10_266_39781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 266 ⟨39781, by decide⟩ :=
  accepted_of_selected 10 266 ⟨39781, by decide⟩ ⟨10, 2, 0, 39781, 266, 3409, 1048576⟩
    (by decide) selected_cut_00998

theorem selected_cut_00999 : selected 11 ⟨39811, by decide⟩
    (prefixPartial 10 267) = some ⟨10, 2, 0, 39811, 267, 473, 1048576⟩ := by
  decide +kernel

theorem context_10_267_39811 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 267 ⟨39811, by decide⟩ :=
  accepted_of_selected 10 267 ⟨39811, by decide⟩ ⟨10, 2, 0, 39811, 267, 473, 1048576⟩
    (by decide) selected_cut_00999

theorem unmarked_context_9_66_39812 : frontier 12 ⟨39812, by decide⟩
    (prefixCache 9 66) (prefixPartial 9 66) = false := by
  decide +kernel

theorem node_context_9_66_39812 : EJMOriginalGlobalDAGData.nodes 12 ⟨39812, by decide⟩ =
    .split (coordinate 9) (![⟨39196, by decide⟩,⟨39632, by decide⟩,⟨39781, by decide⟩,⟨39811, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_66_39812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 66 ⟨39812, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 66
    ⟨39812, by decide⟩ (by decide) (![⟨39196, by decide⟩,⟨39632, by decide⟩,⟨39781, by decide⟩,⟨39811, by decide⟩]) unmarked_context_9_66_39812 node_context_9_66_39812
  intro a
  fin_cases a
  · exact context_10_264_39196
  · exact context_10_265_39632
  · exact context_10_266_39781
  · exact context_10_267_39811

theorem selected_cut_01000 : selected 12 ⟨4601, by decide⟩
    (prefixPartial 9 67) = some ⟨9, 1, 0, 4601, 67, 1, 4194304⟩ := by
  decide +kernel

theorem context_9_67_4601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 67 ⟨4601, by decide⟩ :=
  accepted_of_selected 9 67 ⟨4601, by decide⟩ ⟨9, 1, 0, 4601, 67, 1, 4194304⟩
    (by decide) selected_cut_01000

theorem unmarked_context_8_16_39813 : frontier 13 ⟨39813, by decide⟩
    (prefixCache 8 16) (prefixPartial 8 16) = false := by
  decide +kernel

theorem node_context_8_16_39813 : EJMOriginalGlobalDAGData.nodes 13 ⟨39813, by decide⟩ =
    .split (coordinate 8) (![⟨36317, by decide⟩,⟨38411, by decide⟩,⟨39812, by decide⟩,⟨4601, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_16_39813 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 16 ⟨39813, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 16
    ⟨39813, by decide⟩ (by decide) (![⟨36317, by decide⟩,⟨38411, by decide⟩,⟨39812, by decide⟩,⟨4601, by decide⟩]) unmarked_context_8_16_39813 node_context_8_16_39813
  intro a
  fin_cases a
  · exact context_9_64_36317
  · exact context_9_65_38411
  · exact context_9_66_39812
  · exact context_9_67_4601

theorem selected_cut_01001 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 4352) = some ⟨12, 1, 0, 34034, 4352, 1, 65536⟩ := by
  decide +kernel

theorem context_12_4352_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4352 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 4352 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 4352, 1, 65536⟩
    (by decide) selected_cut_01001

theorem selected_cut_01002 : selected 8 ⟨39888, by decide⟩
    (prefixPartial 13 17412) = some ⟨13, 2, 0, 39888, 17412, 2497, 16384⟩ := by
  decide +kernel

theorem context_13_17412_39888 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17412 ⟨39888, by decide⟩ :=
  accepted_of_selected 13 17412 ⟨39888, by decide⟩ ⟨13, 2, 0, 39888, 17412, 2497, 16384⟩
    (by decide) selected_cut_01002

theorem selected_cut_01003 : selected 8 ⟨39941, by decide⟩
    (prefixPartial 13 17413) = some ⟨13, 2, 0, 39941, 17413, 1325, 16384⟩ := by
  decide +kernel

theorem context_13_17413_39941 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17413 ⟨39941, by decide⟩ :=
  accepted_of_selected 13 17413 ⟨39941, by decide⟩ ⟨13, 2, 0, 39941, 17413, 1325, 16384⟩
    (by decide) selected_cut_01003

theorem selected_cut_01004 : selected 8 ⟨39984, by decide⟩
    (prefixPartial 13 17414) = some ⟨13, 2, 0, 39984, 17414, 657, 16384⟩ := by
  decide +kernel

theorem context_13_17414_39984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17414 ⟨39984, by decide⟩ :=
  accepted_of_selected 13 17414 ⟨39984, by decide⟩ ⟨13, 2, 0, 39984, 17414, 657, 16384⟩
    (by decide) selected_cut_01004

theorem selected_cut_01005 : selected 8 ⟨414, by decide⟩
    (prefixPartial 13 17415) = some ⟨13, 1, 0, 414, 17415, 1, 16384⟩ := by
  decide +kernel

theorem context_13_17415_414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17415 ⟨414, by decide⟩ :=
  accepted_of_selected 13 17415 ⟨414, by decide⟩ ⟨13, 1, 0, 414, 17415, 1, 16384⟩
    (by decide) selected_cut_01005

theorem unmarked_context_12_4353_39985 : frontier 9 ⟨39985, by decide⟩
    (prefixCache 12 4353) (prefixPartial 12 4353) = false := by
  decide +kernel

theorem node_context_12_4353_39985 : EJMOriginalGlobalDAGData.nodes 9 ⟨39985, by decide⟩ =
    .split (coordinate 12) (![⟨39888, by decide⟩,⟨39941, by decide⟩,⟨39984, by decide⟩,⟨414, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4353_39985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4353 ⟨39985, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4353
    ⟨39985, by decide⟩ (by decide) (![⟨39888, by decide⟩,⟨39941, by decide⟩,⟨39984, by decide⟩,⟨414, by decide⟩]) unmarked_context_12_4353_39985 node_context_12_4353_39985
  intro a
  fin_cases a
  · exact context_13_17412_39888
  · exact context_13_17413_39941
  · exact context_13_17414_39984
  · exact context_13_17415_414

theorem selected_cut_01006 : selected 7 ⟨40031, by decide⟩
    (prefixPartial 14 69664) = some ⟨14, 2, 0, 40031, 69664, 2301, 4096⟩ := by
  decide +kernel

theorem context_14_69664_40031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 69664 ⟨40031, by decide⟩ :=
  accepted_of_selected 14 69664 ⟨40031, by decide⟩ ⟨14, 2, 0, 40031, 69664, 2301, 4096⟩
    (by decide) selected_cut_01006

theorem selected_cut_01007 : selected 7 ⟨40054, by decide⟩
    (prefixPartial 14 69665) = some ⟨14, 2, 0, 40054, 69665, 1665, 4096⟩ := by
  decide +kernel

theorem context_14_69665_40054 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 69665 ⟨40054, by decide⟩ :=
  accepted_of_selected 14 69665 ⟨40054, by decide⟩ ⟨14, 2, 0, 40054, 69665, 1665, 4096⟩
    (by decide) selected_cut_01007

theorem selected_cut_01008 : selected 7 ⟨40078, by decide⟩
    (prefixPartial 14 69666) = some ⟨14, 2, 0, 40078, 69666, 1657, 4096⟩ := by
  decide +kernel

theorem context_14_69666_40078 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 69666 ⟨40078, by decide⟩ :=
  accepted_of_selected 14 69666 ⟨40078, by decide⟩ ⟨14, 2, 0, 40078, 69666, 1657, 4096⟩
    (by decide) selected_cut_01008

theorem selected_cut_01009 : selected 7 ⟨40102, by decide⟩
    (prefixPartial 14 69667) = some ⟨14, 2, 0, 40102, 69667, 1577, 4096⟩ := by
  decide +kernel

theorem context_14_69667_40102 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 69667 ⟨40102, by decide⟩ :=
  accepted_of_selected 14 69667 ⟨40102, by decide⟩ ⟨14, 2, 0, 40102, 69667, 1577, 4096⟩
    (by decide) selected_cut_01009

theorem unmarked_context_13_17416_40103 : frontier 8 ⟨40103, by decide⟩
    (prefixCache 13 17416) (prefixPartial 13 17416) = false := by
  decide +kernel

theorem node_context_13_17416_40103 : EJMOriginalGlobalDAGData.nodes 8 ⟨40103, by decide⟩ =
    .split (coordinate 13) (![⟨40031, by decide⟩,⟨40054, by decide⟩,⟨40078, by decide⟩,⟨40102, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_17416_40103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17416 ⟨40103, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 17416
    ⟨40103, by decide⟩ (by decide) (![⟨40031, by decide⟩,⟨40054, by decide⟩,⟨40078, by decide⟩,⟨40102, by decide⟩]) unmarked_context_13_17416_40103 node_context_13_17416_40103
  intro a
  fin_cases a
  · exact context_14_69664_40031
  · exact context_14_69665_40054
  · exact context_14_69666_40078
  · exact context_14_69667_40102

theorem selected_cut_01010 : selected 7 ⟨40123, by decide⟩
    (prefixPartial 14 69668) = some ⟨14, 2, 0, 40123, 69668, 1341, 4096⟩ := by
  decide +kernel

theorem context_14_69668_40123 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 69668 ⟨40123, by decide⟩ :=
  accepted_of_selected 14 69668 ⟨40123, by decide⟩ ⟨14, 2, 0, 40123, 69668, 1341, 4096⟩
    (by decide) selected_cut_01010

theorem selected_cut_01011 : selected 7 ⟨40144, by decide⟩
    (prefixPartial 14 69669) = some ⟨14, 2, 0, 40144, 69669, 1353, 4096⟩ := by
  decide +kernel

theorem context_14_69669_40144 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 69669 ⟨40144, by decide⟩ :=
  accepted_of_selected 14 69669 ⟨40144, by decide⟩ ⟨14, 2, 0, 40144, 69669, 1353, 4096⟩
    (by decide) selected_cut_01011

theorem selected_cut_01012 : selected 7 ⟨40167, by decide⟩
    (prefixPartial 14 69670) = some ⟨14, 2, 0, 40167, 69670, 1549, 4096⟩ := by
  decide +kernel

theorem context_14_69670_40167 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 69670 ⟨40167, by decide⟩ :=
  accepted_of_selected 14 69670 ⟨40167, by decide⟩ ⟨14, 2, 0, 40167, 69670, 1549, 4096⟩
    (by decide) selected_cut_01012

theorem selected_cut_01013 : selected 7 ⟨40192, by decide⟩
    (prefixPartial 14 69671) = some ⟨14, 2, 0, 40192, 69671, 1433, 4096⟩ := by
  decide +kernel

theorem context_14_69671_40192 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 69671 ⟨40192, by decide⟩ :=
  accepted_of_selected 14 69671 ⟨40192, by decide⟩ ⟨14, 2, 0, 40192, 69671, 1433, 4096⟩
    (by decide) selected_cut_01013

theorem unmarked_context_13_17417_40193 : frontier 8 ⟨40193, by decide⟩
    (prefixCache 13 17417) (prefixPartial 13 17417) = false := by
  decide +kernel

theorem node_context_13_17417_40193 : EJMOriginalGlobalDAGData.nodes 8 ⟨40193, by decide⟩ =
    .split (coordinate 13) (![⟨40123, by decide⟩,⟨40144, by decide⟩,⟨40167, by decide⟩,⟨40192, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_17417_40193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17417 ⟨40193, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 17417
    ⟨40193, by decide⟩ (by decide) (![⟨40123, by decide⟩,⟨40144, by decide⟩,⟨40167, by decide⟩,⟨40192, by decide⟩]) unmarked_context_13_17417_40193 node_context_13_17417_40193
  intro a
  fin_cases a
  · exact context_14_69668_40123
  · exact context_14_69669_40144
  · exact context_14_69670_40167
  · exact context_14_69671_40192

theorem selected_cut_01014 : selected 8 ⟨40257, by decide⟩
    (prefixPartial 13 17418) = some ⟨13, 2, 0, 40257, 17418, 3577, 16384⟩ := by
  decide +kernel

theorem context_13_17418_40257 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17418 ⟨40257, by decide⟩ :=
  accepted_of_selected 13 17418 ⟨40257, by decide⟩ ⟨13, 2, 0, 40257, 17418, 3577, 16384⟩
    (by decide) selected_cut_01014

theorem selected_cut_01015 : selected 8 ⟨40292, by decide⟩
    (prefixPartial 13 17419) = some ⟨13, 2, 0, 40292, 17419, 1649, 16384⟩ := by
  decide +kernel

theorem context_13_17419_40292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17419 ⟨40292, by decide⟩ :=
  accepted_of_selected 13 17419 ⟨40292, by decide⟩ ⟨13, 2, 0, 40292, 17419, 1649, 16384⟩
    (by decide) selected_cut_01015

theorem unmarked_context_12_4354_40293 : frontier 9 ⟨40293, by decide⟩
    (prefixCache 12 4354) (prefixPartial 12 4354) = false := by
  decide +kernel

theorem node_context_12_4354_40293 : EJMOriginalGlobalDAGData.nodes 9 ⟨40293, by decide⟩ =
    .split (coordinate 12) (![⟨40103, by decide⟩,⟨40193, by decide⟩,⟨40257, by decide⟩,⟨40292, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4354_40293 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4354 ⟨40293, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4354
    ⟨40293, by decide⟩ (by decide) (![⟨40103, by decide⟩,⟨40193, by decide⟩,⟨40257, by decide⟩,⟨40292, by decide⟩]) unmarked_context_12_4354_40293 node_context_12_4354_40293
  intro a
  fin_cases a
  · exact context_13_17416_40103
  · exact context_13_17417_40193
  · exact context_13_17418_40257
  · exact context_13_17419_40292

theorem selected_cut_01016 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 4355) = some ⟨12, 1, 0, 893, 4355, 1, 65536⟩ := by
  decide +kernel

theorem context_12_4355_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4355 ⟨893, by decide⟩ :=
  accepted_of_selected 12 4355 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 4355, 1, 65536⟩
    (by decide) selected_cut_01016

theorem unmarked_context_11_1088_40294 : frontier 10 ⟨40294, by decide⟩
    (prefixCache 11 1088) (prefixPartial 11 1088) = false := by
  decide +kernel

theorem node_context_11_1088_40294 : EJMOriginalGlobalDAGData.nodes 10 ⟨40294, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨39985, by decide⟩,⟨40293, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1088_40294 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1088 ⟨40294, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1088
    ⟨40294, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨39985, by decide⟩,⟨40293, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_1088_40294 node_context_11_1088_40294
  intro a
  fin_cases a
  · exact context_12_4352_34034
  · exact context_12_4353_39985
  · exact context_12_4354_40293
  · exact context_12_4355_893

theorem selected_cut_01017 : selected 8 ⟨40344, by decide⟩
    (prefixPartial 13 17424) = some ⟨13, 2, 0, 40344, 17424, 2113, 16384⟩ := by
  decide +kernel

theorem context_13_17424_40344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17424 ⟨40344, by decide⟩ :=
  accepted_of_selected 13 17424 ⟨40344, by decide⟩ ⟨13, 2, 0, 40344, 17424, 2113, 16384⟩
    (by decide) selected_cut_01017

theorem selected_cut_01018 : selected 8 ⟨40388, by decide⟩
    (prefixPartial 13 17425) = some ⟨13, 2, 0, 40388, 17425, 2389, 16384⟩ := by
  decide +kernel

theorem context_13_17425_40388 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17425 ⟨40388, by decide⟩ :=
  accepted_of_selected 13 17425 ⟨40388, by decide⟩ ⟨13, 2, 0, 40388, 17425, 2389, 16384⟩
    (by decide) selected_cut_01018

theorem selected_cut_01019 : selected 8 ⟨40452, by decide⟩
    (prefixPartial 13 17426) = some ⟨13, 2, 0, 40452, 17426, 2389, 16384⟩ := by
  decide +kernel

theorem context_13_17426_40452 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17426 ⟨40452, by decide⟩ :=
  accepted_of_selected 13 17426 ⟨40452, by decide⟩ ⟨13, 2, 0, 40452, 17426, 2389, 16384⟩
    (by decide) selected_cut_01019

theorem selected_cut_01020 : selected 8 ⟨414, by decide⟩
    (prefixPartial 13 17427) = some ⟨13, 1, 0, 414, 17427, 1, 16384⟩ := by
  decide +kernel

theorem context_13_17427_414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17427 ⟨414, by decide⟩ :=
  accepted_of_selected 13 17427 ⟨414, by decide⟩ ⟨13, 1, 0, 414, 17427, 1, 16384⟩
    (by decide) selected_cut_01020

theorem unmarked_context_12_4356_40453 : frontier 9 ⟨40453, by decide⟩
    (prefixCache 12 4356) (prefixPartial 12 4356) = false := by
  decide +kernel

theorem node_context_12_4356_40453 : EJMOriginalGlobalDAGData.nodes 9 ⟨40453, by decide⟩ =
    .split (coordinate 12) (![⟨40344, by decide⟩,⟨40388, by decide⟩,⟨40452, by decide⟩,⟨414, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4356_40453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4356 ⟨40453, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4356
    ⟨40453, by decide⟩ (by decide) (![⟨40344, by decide⟩,⟨40388, by decide⟩,⟨40452, by decide⟩,⟨414, by decide⟩]) unmarked_context_12_4356_40453 node_context_12_4356_40453
  intro a
  fin_cases a
  · exact context_13_17424_40344
  · exact context_13_17425_40388
  · exact context_13_17426_40452
  · exact context_13_17427_414

theorem selected_cut_01021 : selected 8 ⟨40513, by decide⟩
    (prefixPartial 13 17428) = some ⟨13, 2, 0, 40513, 17428, 3169, 16384⟩ := by
  decide +kernel

theorem context_13_17428_40513 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17428 ⟨40513, by decide⟩ :=
  accepted_of_selected 13 17428 ⟨40513, by decide⟩ ⟨13, 2, 0, 40513, 17428, 3169, 16384⟩
    (by decide) selected_cut_01021

theorem selected_cut_01022 : selected 8 ⟨40578, by decide⟩
    (prefixPartial 13 17429) = some ⟨13, 2, 0, 40578, 17429, 3117, 16384⟩ := by
  decide +kernel

theorem context_13_17429_40578 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17429 ⟨40578, by decide⟩ :=
  accepted_of_selected 13 17429 ⟨40578, by decide⟩ ⟨13, 2, 0, 40578, 17429, 3117, 16384⟩
    (by decide) selected_cut_01022

theorem selected_cut_01023 : selected 8 ⟨40645, by decide⟩
    (prefixPartial 13 17430) = some ⟨13, 2, 0, 40645, 17430, 2709, 16384⟩ := by
  decide +kernel

theorem context_13_17430_40645 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17430 ⟨40645, by decide⟩ :=
  accepted_of_selected 13 17430 ⟨40645, by decide⟩ ⟨13, 2, 0, 40645, 17430, 2709, 16384⟩
    (by decide) selected_cut_01023

theorem selected_cut_01024 : selected 8 ⟨414, by decide⟩
    (prefixPartial 13 17431) = some ⟨13, 1, 0, 414, 17431, 1, 16384⟩ := by
  decide +kernel

theorem context_13_17431_414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17431 ⟨414, by decide⟩ :=
  accepted_of_selected 13 17431 ⟨414, by decide⟩ ⟨13, 1, 0, 414, 17431, 1, 16384⟩
    (by decide) selected_cut_01024

theorem unmarked_context_12_4357_40646 : frontier 9 ⟨40646, by decide⟩
    (prefixCache 12 4357) (prefixPartial 12 4357) = false := by
  decide +kernel

theorem node_context_12_4357_40646 : EJMOriginalGlobalDAGData.nodes 9 ⟨40646, by decide⟩ =
    .split (coordinate 12) (![⟨40513, by decide⟩,⟨40578, by decide⟩,⟨40645, by decide⟩,⟨414, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4357_40646 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4357 ⟨40646, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4357
    ⟨40646, by decide⟩ (by decide) (![⟨40513, by decide⟩,⟨40578, by decide⟩,⟨40645, by decide⟩,⟨414, by decide⟩]) unmarked_context_12_4357_40646 node_context_12_4357_40646
  intro a
  fin_cases a
  · exact context_13_17428_40513
  · exact context_13_17429_40578
  · exact context_13_17430_40645
  · exact context_13_17431_414

theorem selected_cut_01025 : selected 8 ⟨40722, by decide⟩
    (prefixPartial 13 17432) = some ⟨13, 2, 0, 40722, 17432, 3949, 16384⟩ := by
  decide +kernel

theorem context_13_17432_40722 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17432 ⟨40722, by decide⟩ :=
  accepted_of_selected 13 17432 ⟨40722, by decide⟩ ⟨13, 2, 0, 40722, 17432, 3949, 16384⟩
    (by decide) selected_cut_01025

theorem selected_cut_01026 : selected 8 ⟨40782, by decide⟩
    (prefixPartial 13 17433) = some ⟨13, 2, 0, 40782, 17433, 4069, 16384⟩ := by
  decide +kernel

theorem context_13_17433_40782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17433 ⟨40782, by decide⟩ :=
  accepted_of_selected 13 17433 ⟨40782, by decide⟩ ⟨13, 2, 0, 40782, 17433, 4069, 16384⟩
    (by decide) selected_cut_01026

theorem selected_cut_01027 : selected 8 ⟨40819, by decide⟩
    (prefixPartial 13 17434) = some ⟨13, 2, 0, 40819, 17434, 2365, 16384⟩ := by
  decide +kernel

theorem context_13_17434_40819 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17434 ⟨40819, by decide⟩ :=
  accepted_of_selected 13 17434 ⟨40819, by decide⟩ ⟨13, 2, 0, 40819, 17434, 2365, 16384⟩
    (by decide) selected_cut_01027

theorem selected_cut_01028 : selected 8 ⟨40837, by decide⟩
    (prefixPartial 13 17435) = some ⟨13, 2, 0, 40837, 17435, 1201, 16384⟩ := by
  decide +kernel

theorem context_13_17435_40837 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17435 ⟨40837, by decide⟩ :=
  accepted_of_selected 13 17435 ⟨40837, by decide⟩ ⟨13, 2, 0, 40837, 17435, 1201, 16384⟩
    (by decide) selected_cut_01028

theorem unmarked_context_12_4358_40838 : frontier 9 ⟨40838, by decide⟩
    (prefixCache 12 4358) (prefixPartial 12 4358) = false := by
  decide +kernel

theorem node_context_12_4358_40838 : EJMOriginalGlobalDAGData.nodes 9 ⟨40838, by decide⟩ =
    .split (coordinate 12) (![⟨40722, by decide⟩,⟨40782, by decide⟩,⟨40819, by decide⟩,⟨40837, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4358_40838 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4358 ⟨40838, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4358
    ⟨40838, by decide⟩ (by decide) (![⟨40722, by decide⟩,⟨40782, by decide⟩,⟨40819, by decide⟩,⟨40837, by decide⟩]) unmarked_context_12_4358_40838 node_context_12_4358_40838
  intro a
  fin_cases a
  · exact context_13_17432_40722
  · exact context_13_17433_40782
  · exact context_13_17434_40819
  · exact context_13_17435_40837

theorem selected_cut_01029 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 4359) = some ⟨12, 1, 0, 893, 4359, 1, 65536⟩ := by
  decide +kernel

theorem context_12_4359_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4359 ⟨893, by decide⟩ :=
  accepted_of_selected 12 4359 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 4359, 1, 65536⟩
    (by decide) selected_cut_01029

theorem unmarked_context_11_1089_40839 : frontier 10 ⟨40839, by decide⟩
    (prefixCache 11 1089) (prefixPartial 11 1089) = false := by
  decide +kernel

theorem node_context_11_1089_40839 : EJMOriginalGlobalDAGData.nodes 10 ⟨40839, by decide⟩ =
    .split (coordinate 11) (![⟨40453, by decide⟩,⟨40646, by decide⟩,⟨40838, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1089_40839 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1089 ⟨40839, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1089
    ⟨40839, by decide⟩ (by decide) (![⟨40453, by decide⟩,⟨40646, by decide⟩,⟨40838, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_1089_40839 node_context_11_1089_40839
  intro a
  fin_cases a
  · exact context_12_4356_40453
  · exact context_12_4357_40646
  · exact context_12_4358_40838
  · exact context_12_4359_893

theorem selected_cut_01030 : selected 8 ⟨40903, by decide⟩
    (prefixPartial 13 17440) = some ⟨13, 2, 0, 40903, 17440, 3017, 16384⟩ := by
  decide +kernel

theorem context_13_17440_40903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17440 ⟨40903, by decide⟩ :=
  accepted_of_selected 13 17440 ⟨40903, by decide⟩ ⟨13, 2, 0, 40903, 17440, 3017, 16384⟩
    (by decide) selected_cut_01030

theorem selected_cut_01031 : selected 7 ⟨40931, by decide⟩
    (prefixPartial 14 69764) = some ⟨14, 2, 0, 40931, 69764, 1553, 4096⟩ := by
  decide +kernel

theorem context_14_69764_40931 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 69764 ⟨40931, by decide⟩ :=
  accepted_of_selected 14 69764 ⟨40931, by decide⟩ ⟨14, 2, 0, 40931, 69764, 1553, 4096⟩
    (by decide) selected_cut_01031

theorem selected_cut_01032 : selected 7 ⟨40945, by decide⟩
    (prefixPartial 14 69765) = some ⟨14, 2, 0, 40945, 69765, 889, 4096⟩ := by
  decide +kernel

theorem context_14_69765_40945 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 69765 ⟨40945, by decide⟩ :=
  accepted_of_selected 14 69765 ⟨40945, by decide⟩ ⟨14, 2, 0, 40945, 69765, 889, 4096⟩
    (by decide) selected_cut_01032

theorem selected_cut_01033 : selected 7 ⟨40957, by decide⟩
    (prefixPartial 14 69766) = some ⟨14, 2, 0, 40957, 69766, 1129, 4096⟩ := by
  decide +kernel

theorem context_14_69766_40957 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 69766 ⟨40957, by decide⟩ :=
  accepted_of_selected 14 69766 ⟨40957, by decide⟩ ⟨14, 2, 0, 40957, 69766, 1129, 4096⟩
    (by decide) selected_cut_01033

theorem selected_cut_01034 : selected 7 ⟨40974, by decide⟩
    (prefixPartial 14 69767) = some ⟨14, 2, 0, 40974, 69767, 1057, 4096⟩ := by
  decide +kernel

theorem context_14_69767_40974 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 69767 ⟨40974, by decide⟩ :=
  accepted_of_selected 14 69767 ⟨40974, by decide⟩ ⟨14, 2, 0, 40974, 69767, 1057, 4096⟩
    (by decide) selected_cut_01034

theorem unmarked_context_13_17441_40975 : frontier 8 ⟨40975, by decide⟩
    (prefixCache 13 17441) (prefixPartial 13 17441) = false := by
  decide +kernel

theorem node_context_13_17441_40975 : EJMOriginalGlobalDAGData.nodes 8 ⟨40975, by decide⟩ =
    .split (coordinate 13) (![⟨40931, by decide⟩,⟨40945, by decide⟩,⟨40957, by decide⟩,⟨40974, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_17441_40975 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17441 ⟨40975, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 17441
    ⟨40975, by decide⟩ (by decide) (![⟨40931, by decide⟩,⟨40945, by decide⟩,⟨40957, by decide⟩,⟨40974, by decide⟩]) unmarked_context_13_17441_40975 node_context_13_17441_40975
  intro a
  fin_cases a
  · exact context_14_69764_40931
  · exact context_14_69765_40945
  · exact context_14_69766_40957
  · exact context_14_69767_40974

theorem selected_cut_01035 : selected 8 ⟨41034, by decide⟩
    (prefixPartial 13 17442) = some ⟨13, 2, 0, 41034, 17442, 3121, 16384⟩ := by
  decide +kernel

theorem context_13_17442_41034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17442 ⟨41034, by decide⟩ :=
  accepted_of_selected 13 17442 ⟨41034, by decide⟩ ⟨13, 2, 0, 41034, 17442, 3121, 16384⟩
    (by decide) selected_cut_01035

theorem selected_cut_01036 : selected 8 ⟨41061, by decide⟩
    (prefixPartial 13 17443) = some ⟨13, 2, 0, 41061, 17443, 1341, 16384⟩ := by
  decide +kernel

theorem context_13_17443_41061 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17443 ⟨41061, by decide⟩ :=
  accepted_of_selected 13 17443 ⟨41061, by decide⟩ ⟨13, 2, 0, 41061, 17443, 1341, 16384⟩
    (by decide) selected_cut_01036

theorem unmarked_context_12_4360_41062 : frontier 9 ⟨41062, by decide⟩
    (prefixCache 12 4360) (prefixPartial 12 4360) = false := by
  decide +kernel

theorem node_context_12_4360_41062 : EJMOriginalGlobalDAGData.nodes 9 ⟨41062, by decide⟩ =
    .split (coordinate 12) (![⟨40903, by decide⟩,⟨40975, by decide⟩,⟨41034, by decide⟩,⟨41061, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4360_41062 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4360 ⟨41062, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4360
    ⟨41062, by decide⟩ (by decide) (![⟨40903, by decide⟩,⟨40975, by decide⟩,⟨41034, by decide⟩,⟨41061, by decide⟩]) unmarked_context_12_4360_41062 node_context_12_4360_41062
  intro a
  fin_cases a
  · exact context_13_17440_40903
  · exact context_13_17441_40975
  · exact context_13_17442_41034
  · exact context_13_17443_41061

theorem selected_cut_01037 : selected 8 ⟨41122, by decide⟩
    (prefixPartial 13 17444) = some ⟨13, 2, 0, 41122, 17444, 2893, 16384⟩ := by
  decide +kernel

theorem context_13_17444_41122 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17444 ⟨41122, by decide⟩ :=
  accepted_of_selected 13 17444 ⟨41122, by decide⟩ ⟨13, 2, 0, 41122, 17444, 2893, 16384⟩
    (by decide) selected_cut_01037

theorem selected_cut_01038 : selected 8 ⟨41153, by decide⟩
    (prefixPartial 13 17445) = some ⟨13, 2, 0, 41153, 17445, 3233, 16384⟩ := by
  decide +kernel

theorem context_13_17445_41153 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17445 ⟨41153, by decide⟩ :=
  accepted_of_selected 13 17445 ⟨41153, by decide⟩ ⟨13, 2, 0, 41153, 17445, 3233, 16384⟩
    (by decide) selected_cut_01038

theorem selected_cut_01039 : selected 8 ⟨41180, by decide⟩
    (prefixPartial 13 17446) = some ⟨13, 2, 0, 41180, 17446, 2257, 16384⟩ := by
  decide +kernel

theorem context_13_17446_41180 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17446 ⟨41180, by decide⟩ :=
  accepted_of_selected 13 17446 ⟨41180, by decide⟩ ⟨13, 2, 0, 41180, 17446, 2257, 16384⟩
    (by decide) selected_cut_01039

theorem selected_cut_01040 : selected 8 ⟨41193, by decide⟩
    (prefixPartial 13 17447) = some ⟨13, 2, 0, 41193, 17447, 1165, 16384⟩ := by
  decide +kernel

theorem context_13_17447_41193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17447 ⟨41193, by decide⟩ :=
  accepted_of_selected 13 17447 ⟨41193, by decide⟩ ⟨13, 2, 0, 41193, 17447, 1165, 16384⟩
    (by decide) selected_cut_01040

theorem unmarked_context_12_4361_41194 : frontier 9 ⟨41194, by decide⟩
    (prefixCache 12 4361) (prefixPartial 12 4361) = false := by
  decide +kernel

theorem node_context_12_4361_41194 : EJMOriginalGlobalDAGData.nodes 9 ⟨41194, by decide⟩ =
    .split (coordinate 12) (![⟨41122, by decide⟩,⟨41153, by decide⟩,⟨41180, by decide⟩,⟨41193, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4361_41194 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4361 ⟨41194, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4361
    ⟨41194, by decide⟩ (by decide) (![⟨41122, by decide⟩,⟨41153, by decide⟩,⟨41180, by decide⟩,⟨41193, by decide⟩]) unmarked_context_12_4361_41194 node_context_12_4361_41194
  intro a
  fin_cases a
  · exact context_13_17444_41122
  · exact context_13_17445_41153
  · exact context_13_17446_41180
  · exact context_13_17447_41193

theorem selected_cut_01041 : selected 8 ⟨41258, by decide⟩
    (prefixPartial 13 17448) = some ⟨13, 2, 0, 41258, 17448, 3233, 16384⟩ := by
  decide +kernel

theorem context_13_17448_41258 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17448 ⟨41258, by decide⟩ :=
  accepted_of_selected 13 17448 ⟨41258, by decide⟩ ⟨13, 2, 0, 41258, 17448, 3233, 16384⟩
    (by decide) selected_cut_01041

theorem selected_cut_01042 : selected 8 ⟨41300, by decide⟩
    (prefixPartial 13 17449) = some ⟨13, 2, 0, 41300, 17449, 3781, 16384⟩ := by
  decide +kernel

theorem context_13_17449_41300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17449 ⟨41300, by decide⟩ :=
  accepted_of_selected 13 17449 ⟨41300, by decide⟩ ⟨13, 2, 0, 41300, 17449, 3781, 16384⟩
    (by decide) selected_cut_01042

theorem selected_cut_01043 : selected 8 ⟨41330, by decide⟩
    (prefixPartial 13 17450) = some ⟨13, 2, 0, 41330, 17450, 2305, 16384⟩ := by
  decide +kernel

theorem context_13_17450_41330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17450 ⟨41330, by decide⟩ :=
  accepted_of_selected 13 17450 ⟨41330, by decide⟩ ⟨13, 2, 0, 41330, 17450, 2305, 16384⟩
    (by decide) selected_cut_01043

theorem selected_cut_01044 : selected 8 ⟨41347, by decide⟩
    (prefixPartial 13 17451) = some ⟨13, 2, 0, 41347, 17451, 1201, 16384⟩ := by
  decide +kernel

theorem context_13_17451_41347 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17451 ⟨41347, by decide⟩ :=
  accepted_of_selected 13 17451 ⟨41347, by decide⟩ ⟨13, 2, 0, 41347, 17451, 1201, 16384⟩
    (by decide) selected_cut_01044

theorem unmarked_context_12_4362_41348 : frontier 9 ⟨41348, by decide⟩
    (prefixCache 12 4362) (prefixPartial 12 4362) = false := by
  decide +kernel

theorem node_context_12_4362_41348 : EJMOriginalGlobalDAGData.nodes 9 ⟨41348, by decide⟩ =
    .split (coordinate 12) (![⟨41258, by decide⟩,⟨41300, by decide⟩,⟨41330, by decide⟩,⟨41347, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4362_41348 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4362 ⟨41348, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4362
    ⟨41348, by decide⟩ (by decide) (![⟨41258, by decide⟩,⟨41300, by decide⟩,⟨41330, by decide⟩,⟨41347, by decide⟩]) unmarked_context_12_4362_41348 node_context_12_4362_41348
  intro a
  fin_cases a
  · exact context_13_17448_41258
  · exact context_13_17449_41300
  · exact context_13_17450_41330
  · exact context_13_17451_41347

theorem selected_cut_01045 : selected 8 ⟨41407, by decide⟩
    (prefixPartial 13 17452) = some ⟨13, 2, 0, 41407, 17452, 3229, 16384⟩ := by
  decide +kernel

theorem context_13_17452_41407 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17452 ⟨41407, by decide⟩ :=
  accepted_of_selected 13 17452 ⟨41407, by decide⟩ ⟨13, 2, 0, 41407, 17452, 3229, 16384⟩
    (by decide) selected_cut_01045

theorem selected_cut_01046 : selected 8 ⟨41452, by decide⟩
    (prefixPartial 13 17453) = some ⟨13, 2, 0, 41452, 17453, 3881, 16384⟩ := by
  decide +kernel

theorem context_13_17453_41452 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17453 ⟨41452, by decide⟩ :=
  accepted_of_selected 13 17453 ⟨41452, by decide⟩ ⟨13, 2, 0, 41452, 17453, 3881, 16384⟩
    (by decide) selected_cut_01046

theorem selected_cut_01047 : selected 8 ⟨41483, by decide⟩
    (prefixPartial 13 17454) = some ⟨13, 2, 0, 41483, 17454, 2361, 16384⟩ := by
  decide +kernel

theorem context_13_17454_41483 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17454 ⟨41483, by decide⟩ :=
  accepted_of_selected 13 17454 ⟨41483, by decide⟩ ⟨13, 2, 0, 41483, 17454, 2361, 16384⟩
    (by decide) selected_cut_01047

theorem selected_cut_01048 : selected 8 ⟨41498, by decide⟩
    (prefixPartial 13 17455) = some ⟨13, 2, 0, 41498, 17455, 1265, 16384⟩ := by
  decide +kernel

theorem context_13_17455_41498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17455 ⟨41498, by decide⟩ :=
  accepted_of_selected 13 17455 ⟨41498, by decide⟩ ⟨13, 2, 0, 41498, 17455, 1265, 16384⟩
    (by decide) selected_cut_01048

theorem unmarked_context_12_4363_41499 : frontier 9 ⟨41499, by decide⟩
    (prefixCache 12 4363) (prefixPartial 12 4363) = false := by
  decide +kernel

theorem node_context_12_4363_41499 : EJMOriginalGlobalDAGData.nodes 9 ⟨41499, by decide⟩ =
    .split (coordinate 12) (![⟨41407, by decide⟩,⟨41452, by decide⟩,⟨41483, by decide⟩,⟨41498, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4363_41499 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4363 ⟨41499, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4363
    ⟨41499, by decide⟩ (by decide) (![⟨41407, by decide⟩,⟨41452, by decide⟩,⟨41483, by decide⟩,⟨41498, by decide⟩]) unmarked_context_12_4363_41499 node_context_12_4363_41499
  intro a
  fin_cases a
  · exact context_13_17452_41407
  · exact context_13_17453_41452
  · exact context_13_17454_41483
  · exact context_13_17455_41498

theorem unmarked_context_11_1090_41500 : frontier 10 ⟨41500, by decide⟩
    (prefixCache 11 1090) (prefixPartial 11 1090) = false := by
  decide +kernel

theorem node_context_11_1090_41500 : EJMOriginalGlobalDAGData.nodes 10 ⟨41500, by decide⟩ =
    .split (coordinate 11) (![⟨41062, by decide⟩,⟨41194, by decide⟩,⟨41348, by decide⟩,⟨41499, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1090_41500 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1090 ⟨41500, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1090
    ⟨41500, by decide⟩ (by decide) (![⟨41062, by decide⟩,⟨41194, by decide⟩,⟨41348, by decide⟩,⟨41499, by decide⟩]) unmarked_context_11_1090_41500 node_context_11_1090_41500
  intro a
  fin_cases a
  · exact context_12_4360_41062
  · exact context_12_4361_41194
  · exact context_12_4362_41348
  · exact context_12_4363_41499

theorem selected_cut_01049 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 1091) = some ⟨11, 1, 0, 1736, 1091, 1, 262144⟩ := by
  decide +kernel

theorem context_11_1091_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1091 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 1091 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 1091, 1, 262144⟩
    (by decide) selected_cut_01049

theorem unmarked_context_10_272_41501 : frontier 11 ⟨41501, by decide⟩
    (prefixCache 10 272) (prefixPartial 10 272) = false := by
  decide +kernel

theorem node_context_10_272_41501 : EJMOriginalGlobalDAGData.nodes 11 ⟨41501, by decide⟩ =
    .split (coordinate 10) (![⟨40294, by decide⟩,⟨40839, by decide⟩,⟨41500, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_272_41501 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 272 ⟨41501, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 272
    ⟨41501, by decide⟩ (by decide) (![⟨40294, by decide⟩,⟨40839, by decide⟩,⟨41500, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_272_41501 node_context_10_272_41501
  intro a
  fin_cases a
  · exact context_11_1088_40294
  · exact context_11_1089_40839
  · exact context_11_1090_41500
  · exact context_11_1091_1736

theorem selected_cut_01050 : selected 9 ⟨41574, by decide⟩
    (prefixPartial 12 4368) = some ⟨12, 2, 0, 41574, 4368, 3201, 65536⟩ := by
  decide +kernel

theorem context_12_4368_41574 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4368 ⟨41574, by decide⟩ :=
  accepted_of_selected 12 4368 ⟨41574, by decide⟩ ⟨12, 2, 0, 41574, 4368, 3201, 65536⟩
    (by decide) selected_cut_01050

theorem selected_cut_01051 : selected 9 ⟨41627, by decide⟩
    (prefixPartial 12 4369) = some ⟨12, 2, 0, 41627, 4369, 2309, 65536⟩ := by
  decide +kernel

theorem context_12_4369_41627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4369 ⟨41627, by decide⟩ :=
  accepted_of_selected 12 4369 ⟨41627, by decide⟩ ⟨12, 2, 0, 41627, 4369, 2309, 65536⟩
    (by decide) selected_cut_01051

theorem selected_cut_01052 : selected 8 ⟨41664, by decide⟩
    (prefixPartial 13 17480) = some ⟨13, 2, 0, 41664, 17480, 1461, 16384⟩ := by
  decide +kernel

theorem context_13_17480_41664 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17480 ⟨41664, by decide⟩ :=
  accepted_of_selected 13 17480 ⟨41664, by decide⟩ ⟨13, 2, 0, 41664, 17480, 1461, 16384⟩
    (by decide) selected_cut_01052

theorem selected_cut_01053 : selected 8 ⟨41707, by decide⟩
    (prefixPartial 13 17481) = some ⟨13, 2, 0, 41707, 17481, 2029, 16384⟩ := by
  decide +kernel

theorem context_13_17481_41707 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17481 ⟨41707, by decide⟩ :=
  accepted_of_selected 13 17481 ⟨41707, by decide⟩ ⟨13, 2, 0, 41707, 17481, 2029, 16384⟩
    (by decide) selected_cut_01053

theorem selected_cut_01054 : selected 8 ⟨41728, by decide⟩
    (prefixPartial 13 17482) = some ⟨13, 2, 0, 41728, 17482, 1321, 16384⟩ := by
  decide +kernel

theorem context_13_17482_41728 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17482 ⟨41728, by decide⟩ :=
  accepted_of_selected 13 17482 ⟨41728, by decide⟩ ⟨13, 2, 0, 41728, 17482, 1321, 16384⟩
    (by decide) selected_cut_01054

theorem selected_cut_01055 : selected 8 ⟨41739, by decide⟩
    (prefixPartial 13 17483) = some ⟨13, 2, 0, 41739, 17483, 849, 16384⟩ := by
  decide +kernel

theorem context_13_17483_41739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17483 ⟨41739, by decide⟩ :=
  accepted_of_selected 13 17483 ⟨41739, by decide⟩ ⟨13, 2, 0, 41739, 17483, 849, 16384⟩
    (by decide) selected_cut_01055

theorem unmarked_context_12_4370_41740 : frontier 9 ⟨41740, by decide⟩
    (prefixCache 12 4370) (prefixPartial 12 4370) = false := by
  decide +kernel

theorem node_context_12_4370_41740 : EJMOriginalGlobalDAGData.nodes 9 ⟨41740, by decide⟩ =
    .split (coordinate 12) (![⟨41664, by decide⟩,⟨41707, by decide⟩,⟨41728, by decide⟩,⟨41739, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4370_41740 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4370 ⟨41740, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4370
    ⟨41740, by decide⟩ (by decide) (![⟨41664, by decide⟩,⟨41707, by decide⟩,⟨41728, by decide⟩,⟨41739, by decide⟩]) unmarked_context_12_4370_41740 node_context_12_4370_41740
  intro a
  fin_cases a
  · exact context_13_17480_41664
  · exact context_13_17481_41707
  · exact context_13_17482_41728
  · exact context_13_17483_41739

theorem selected_cut_01056 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 4371) = some ⟨12, 1, 0, 893, 4371, 1, 65536⟩ := by
  decide +kernel

theorem context_12_4371_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4371 ⟨893, by decide⟩ :=
  accepted_of_selected 12 4371 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 4371, 1, 65536⟩
    (by decide) selected_cut_01056

theorem unmarked_context_11_1092_41741 : frontier 10 ⟨41741, by decide⟩
    (prefixCache 11 1092) (prefixPartial 11 1092) = false := by
  decide +kernel

theorem node_context_11_1092_41741 : EJMOriginalGlobalDAGData.nodes 10 ⟨41741, by decide⟩ =
    .split (coordinate 11) (![⟨41574, by decide⟩,⟨41627, by decide⟩,⟨41740, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1092_41741 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1092 ⟨41741, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1092
    ⟨41741, by decide⟩ (by decide) (![⟨41574, by decide⟩,⟨41627, by decide⟩,⟨41740, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_1092_41741 node_context_11_1092_41741
  intro a
  fin_cases a
  · exact context_12_4368_41574
  · exact context_12_4369_41627
  · exact context_12_4370_41740
  · exact context_12_4371_893

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
