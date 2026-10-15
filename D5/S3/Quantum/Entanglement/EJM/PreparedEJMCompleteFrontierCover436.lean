/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover435
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_41859 : selected 9 ⟨1144105, by decide⟩
    (prefixPartial 12 336786) = some ⟨12, 2, 0, 1144105, 336786, 1257, 65536⟩ := by
  decide +kernel

theorem context_12_336786_1144105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336786 ⟨1144105, by decide⟩ :=
  accepted_of_selected 12 336786 ⟨1144105, by decide⟩ ⟨12, 2, 0, 1144105, 336786, 1257, 65536⟩
    (by decide) selected_cut_41859

theorem selected_cut_41860 : selected 9 ⟨1144118, by decide⟩
    (prefixPartial 12 336787) = some ⟨12, 2, 0, 1144118, 336787, 1029, 65536⟩ := by
  decide +kernel

theorem context_12_336787_1144118 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336787 ⟨1144118, by decide⟩ :=
  accepted_of_selected 12 336787 ⟨1144118, by decide⟩ ⟨12, 2, 0, 1144118, 336787, 1029, 65536⟩
    (by decide) selected_cut_41860

theorem unmarked_context_11_84196_1144119 : frontier 10 ⟨1144119, by decide⟩
    (prefixCache 11 84196) (prefixPartial 11 84196) = false := by
  decide +kernel

theorem node_context_11_84196_1144119 : EJMOriginalGlobalDAGData.nodes 10 ⟨1144119, by decide⟩ =
    .split (coordinate 11) (![⟨1144061, by decide⟩,⟨1144083, by decide⟩,⟨1144105, by decide⟩,⟨1144118, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84196_1144119 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84196 ⟨1144119, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84196
    ⟨1144119, by decide⟩ (by decide) (![⟨1144061, by decide⟩,⟨1144083, by decide⟩,⟨1144105, by decide⟩,⟨1144118, by decide⟩]) unmarked_context_11_84196_1144119 node_context_11_84196_1144119
  intro a
  fin_cases a
  · exact context_12_336784_1144061
  · exact context_12_336785_1144083
  · exact context_12_336786_1144105
  · exact context_12_336787_1144118

theorem selected_cut_41861 : selected 10 ⟨1144181, by decide⟩
    (prefixPartial 11 84197) = some ⟨11, 2, 0, 1144181, 84197, 3421, 262144⟩ := by
  decide +kernel

theorem context_11_84197_1144181 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84197 ⟨1144181, by decide⟩ :=
  accepted_of_selected 11 84197 ⟨1144181, by decide⟩ ⟨11, 2, 0, 1144181, 84197, 3421, 262144⟩
    (by decide) selected_cut_41861

theorem selected_cut_41862 : selected 10 ⟨1144227, by decide⟩
    (prefixPartial 11 84198) = some ⟨11, 2, 0, 1144227, 84198, 2913, 262144⟩ := by
  decide +kernel

theorem context_11_84198_1144227 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84198 ⟨1144227, by decide⟩ :=
  accepted_of_selected 11 84198 ⟨1144227, by decide⟩ ⟨11, 2, 0, 1144227, 84198, 2913, 262144⟩
    (by decide) selected_cut_41862

theorem selected_cut_41863 : selected 10 ⟨1144271, by decide⟩
    (prefixPartial 11 84199) = some ⟨11, 2, 0, 1144271, 84199, 2721, 262144⟩ := by
  decide +kernel

theorem context_11_84199_1144271 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84199 ⟨1144271, by decide⟩ :=
  accepted_of_selected 11 84199 ⟨1144271, by decide⟩ ⟨11, 2, 0, 1144271, 84199, 2721, 262144⟩
    (by decide) selected_cut_41863

theorem unmarked_context_10_21049_1144272 : frontier 11 ⟨1144272, by decide⟩
    (prefixCache 10 21049) (prefixPartial 10 21049) = false := by
  decide +kernel

theorem node_context_10_21049_1144272 : EJMOriginalGlobalDAGData.nodes 11 ⟨1144272, by decide⟩ =
    .split (coordinate 10) (![⟨1144119, by decide⟩,⟨1144181, by decide⟩,⟨1144227, by decide⟩,⟨1144271, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21049_1144272 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21049 ⟨1144272, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21049
    ⟨1144272, by decide⟩ (by decide) (![⟨1144119, by decide⟩,⟨1144181, by decide⟩,⟨1144227, by decide⟩,⟨1144271, by decide⟩]) unmarked_context_10_21049_1144272 node_context_10_21049_1144272
  intro a
  fin_cases a
  · exact context_11_84196_1144119
  · exact context_11_84197_1144181
  · exact context_11_84198_1144227
  · exact context_11_84199_1144271

theorem selected_cut_41864 : selected 10 ⟨1144302, by decide⟩
    (prefixPartial 11 84200) = some ⟨11, 2, 0, 1144302, 84200, 2433, 262144⟩ := by
  decide +kernel

theorem context_11_84200_1144302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84200 ⟨1144302, by decide⟩ :=
  accepted_of_selected 11 84200 ⟨1144302, by decide⟩ ⟨11, 2, 0, 1144302, 84200, 2433, 262144⟩
    (by decide) selected_cut_41864

theorem selected_cut_41865 : selected 10 ⟨1144337, by decide⟩
    (prefixPartial 11 84201) = some ⟨11, 2, 0, 1144337, 84201, 2497, 262144⟩ := by
  decide +kernel

theorem context_11_84201_1144337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84201 ⟨1144337, by decide⟩ :=
  accepted_of_selected 11 84201 ⟨1144337, by decide⟩ ⟨11, 2, 0, 1144337, 84201, 2497, 262144⟩
    (by decide) selected_cut_41865

theorem selected_cut_41866 : selected 10 ⟨1109453, by decide⟩
    (prefixPartial 11 84202) = some ⟨11, 1, 0, 1109453, 84202, 1, 262144⟩ := by
  decide +kernel

theorem context_11_84202_1109453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84202 ⟨1109453, by decide⟩ :=
  accepted_of_selected 11 84202 ⟨1109453, by decide⟩ ⟨11, 1, 0, 1109453, 84202, 1, 262144⟩
    (by decide) selected_cut_41866

theorem selected_cut_41867 : selected 10 ⟨1144361, by decide⟩
    (prefixPartial 11 84203) = some ⟨11, 2, 0, 1144361, 84203, 1513, 262144⟩ := by
  decide +kernel

theorem context_11_84203_1144361 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84203 ⟨1144361, by decide⟩ :=
  accepted_of_selected 11 84203 ⟨1144361, by decide⟩ ⟨11, 2, 0, 1144361, 84203, 1513, 262144⟩
    (by decide) selected_cut_41867

theorem unmarked_context_10_21050_1144362 : frontier 11 ⟨1144362, by decide⟩
    (prefixCache 10 21050) (prefixPartial 10 21050) = false := by
  decide +kernel

theorem node_context_10_21050_1144362 : EJMOriginalGlobalDAGData.nodes 11 ⟨1144362, by decide⟩ =
    .split (coordinate 10) (![⟨1144302, by decide⟩,⟨1144337, by decide⟩,⟨1109453, by decide⟩,⟨1144361, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21050_1144362 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21050 ⟨1144362, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21050
    ⟨1144362, by decide⟩ (by decide) (![⟨1144302, by decide⟩,⟨1144337, by decide⟩,⟨1109453, by decide⟩,⟨1144361, by decide⟩]) unmarked_context_10_21050_1144362 node_context_10_21050_1144362
  intro a
  fin_cases a
  · exact context_11_84200_1144302
  · exact context_11_84201_1144337
  · exact context_11_84202_1109453
  · exact context_11_84203_1144361

theorem selected_cut_41868 : selected 10 ⟨1144429, by decide⟩
    (prefixPartial 11 84204) = some ⟨11, 2, 0, 1144429, 84204, 2797, 262144⟩ := by
  decide +kernel

theorem context_11_84204_1144429 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84204 ⟨1144429, by decide⟩ :=
  accepted_of_selected 11 84204 ⟨1144429, by decide⟩ ⟨11, 2, 0, 1144429, 84204, 2797, 262144⟩
    (by decide) selected_cut_41868

theorem selected_cut_41869 : selected 10 ⟨1144479, by decide⟩
    (prefixPartial 11 84205) = some ⟨11, 2, 0, 1144479, 84205, 3005, 262144⟩ := by
  decide +kernel

theorem context_11_84205_1144479 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84205 ⟨1144479, by decide⟩ :=
  accepted_of_selected 11 84205 ⟨1144479, by decide⟩ ⟨11, 2, 0, 1144479, 84205, 3005, 262144⟩
    (by decide) selected_cut_41869

theorem selected_cut_41870 : selected 10 ⟨1144520, by decide⟩
    (prefixPartial 11 84206) = some ⟨11, 2, 0, 1144520, 84206, 2257, 262144⟩ := by
  decide +kernel

theorem context_11_84206_1144520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84206 ⟨1144520, by decide⟩ :=
  accepted_of_selected 11 84206 ⟨1144520, by decide⟩ ⟨11, 2, 0, 1144520, 84206, 2257, 262144⟩
    (by decide) selected_cut_41870

theorem selected_cut_41871 : selected 10 ⟨1144554, by decide⟩
    (prefixPartial 11 84207) = some ⟨11, 2, 0, 1144554, 84207, 2153, 262144⟩ := by
  decide +kernel

theorem context_11_84207_1144554 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84207 ⟨1144554, by decide⟩ :=
  accepted_of_selected 11 84207 ⟨1144554, by decide⟩ ⟨11, 2, 0, 1144554, 84207, 2153, 262144⟩
    (by decide) selected_cut_41871

theorem unmarked_context_10_21051_1144555 : frontier 11 ⟨1144555, by decide⟩
    (prefixCache 10 21051) (prefixPartial 10 21051) = false := by
  decide +kernel

theorem node_context_10_21051_1144555 : EJMOriginalGlobalDAGData.nodes 11 ⟨1144555, by decide⟩ =
    .split (coordinate 10) (![⟨1144429, by decide⟩,⟨1144479, by decide⟩,⟨1144520, by decide⟩,⟨1144554, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21051_1144555 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21051 ⟨1144555, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21051
    ⟨1144555, by decide⟩ (by decide) (![⟨1144429, by decide⟩,⟨1144479, by decide⟩,⟨1144520, by decide⟩,⟨1144554, by decide⟩]) unmarked_context_10_21051_1144555 node_context_10_21051_1144555
  intro a
  fin_cases a
  · exact context_11_84204_1144429
  · exact context_11_84205_1144479
  · exact context_11_84206_1144520
  · exact context_11_84207_1144554

theorem unmarked_context_9_5262_1144556 : frontier 12 ⟨1144556, by decide⟩
    (prefixCache 9 5262) (prefixPartial 9 5262) = false := by
  decide +kernel

theorem node_context_9_5262_1144556 : EJMOriginalGlobalDAGData.nodes 12 ⟨1144556, by decide⟩ =
    .split (coordinate 9) (![⟨1144038, by decide⟩,⟨1144272, by decide⟩,⟨1144362, by decide⟩,⟨1144555, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5262_1144556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5262 ⟨1144556, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5262
    ⟨1144556, by decide⟩ (by decide) (![⟨1144038, by decide⟩,⟨1144272, by decide⟩,⟨1144362, by decide⟩,⟨1144555, by decide⟩]) unmarked_context_9_5262_1144556 node_context_9_5262_1144556
  intro a
  fin_cases a
  · exact context_10_21048_1144038
  · exact context_10_21049_1144272
  · exact context_10_21050_1144362
  · exact context_10_21051_1144555

theorem selected_cut_41872 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 84208) = some ⟨11, 1, 0, 907917, 84208, 1, 262144⟩ := by
  decide +kernel

theorem context_11_84208_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84208 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 84208 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 84208, 1, 262144⟩
    (by decide) selected_cut_41872

theorem selected_cut_41873 : selected 10 ⟨1144580, by decide⟩
    (prefixPartial 11 84209) = some ⟨11, 2, 0, 1144580, 84209, 1749, 262144⟩ := by
  decide +kernel

theorem context_11_84209_1144580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84209 ⟨1144580, by decide⟩ :=
  accepted_of_selected 11 84209 ⟨1144580, by decide⟩ ⟨11, 2, 0, 1144580, 84209, 1749, 262144⟩
    (by decide) selected_cut_41873

theorem selected_cut_41874 : selected 10 ⟨1144603, by decide⟩
    (prefixPartial 11 84210) = some ⟨11, 2, 0, 1144603, 84210, 1661, 262144⟩ := by
  decide +kernel

theorem context_11_84210_1144603 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84210 ⟨1144603, by decide⟩ :=
  accepted_of_selected 11 84210 ⟨1144603, by decide⟩ ⟨11, 2, 0, 1144603, 84210, 1661, 262144⟩
    (by decide) selected_cut_41874

theorem selected_cut_41875 : selected 10 ⟨1144619, by decide⟩
    (prefixPartial 11 84211) = some ⟨11, 2, 0, 1144619, 84211, 1149, 262144⟩ := by
  decide +kernel

theorem context_11_84211_1144619 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84211 ⟨1144619, by decide⟩ :=
  accepted_of_selected 11 84211 ⟨1144619, by decide⟩ ⟨11, 2, 0, 1144619, 84211, 1149, 262144⟩
    (by decide) selected_cut_41875

theorem unmarked_context_10_21052_1144620 : frontier 11 ⟨1144620, by decide⟩
    (prefixCache 10 21052) (prefixPartial 10 21052) = false := by
  decide +kernel

theorem node_context_10_21052_1144620 : EJMOriginalGlobalDAGData.nodes 11 ⟨1144620, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨1144580, by decide⟩,⟨1144603, by decide⟩,⟨1144619, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21052_1144620 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21052 ⟨1144620, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21052
    ⟨1144620, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨1144580, by decide⟩,⟨1144603, by decide⟩,⟨1144619, by decide⟩]) unmarked_context_10_21052_1144620 node_context_10_21052_1144620
  intro a
  fin_cases a
  · exact context_11_84208_907917
  · exact context_11_84209_1144580
  · exact context_11_84210_1144603
  · exact context_11_84211_1144619

theorem selected_cut_41876 : selected 11 ⟨1144675, by decide⟩
    (prefixPartial 10 21053) = some ⟨10, 2, 0, 1144675, 21053, 3829, 1048576⟩ := by
  decide +kernel

theorem context_10_21053_1144675 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21053 ⟨1144675, by decide⟩ :=
  accepted_of_selected 10 21053 ⟨1144675, by decide⟩ ⟨10, 2, 0, 1144675, 21053, 3829, 1048576⟩
    (by decide) selected_cut_41876

theorem selected_cut_41877 : selected 11 ⟨1144740, by decide⟩
    (prefixPartial 10 21054) = some ⟨10, 2, 0, 1144740, 21054, 2565, 1048576⟩ := by
  decide +kernel

theorem context_10_21054_1144740 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21054 ⟨1144740, by decide⟩ :=
  accepted_of_selected 10 21054 ⟨1144740, by decide⟩ ⟨10, 2, 0, 1144740, 21054, 2565, 1048576⟩
    (by decide) selected_cut_41877

theorem selected_cut_41878 : selected 11 ⟨1144760, by decide⟩
    (prefixPartial 10 21055) = some ⟨10, 2, 0, 1144760, 21055, 517, 1048576⟩ := by
  decide +kernel

theorem context_10_21055_1144760 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21055 ⟨1144760, by decide⟩ :=
  accepted_of_selected 10 21055 ⟨1144760, by decide⟩ ⟨10, 2, 0, 1144760, 21055, 517, 1048576⟩
    (by decide) selected_cut_41878

theorem unmarked_context_9_5263_1144761 : frontier 12 ⟨1144761, by decide⟩
    (prefixCache 9 5263) (prefixPartial 9 5263) = false := by
  decide +kernel

theorem node_context_9_5263_1144761 : EJMOriginalGlobalDAGData.nodes 12 ⟨1144761, by decide⟩ =
    .split (coordinate 9) (![⟨1144620, by decide⟩,⟨1144675, by decide⟩,⟨1144740, by decide⟩,⟨1144760, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5263_1144761 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5263 ⟨1144761, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5263
    ⟨1144761, by decide⟩ (by decide) (![⟨1144620, by decide⟩,⟨1144675, by decide⟩,⟨1144740, by decide⟩,⟨1144760, by decide⟩]) unmarked_context_9_5263_1144761 node_context_9_5263_1144761
  intro a
  fin_cases a
  · exact context_10_21052_1144620
  · exact context_10_21053_1144675
  · exact context_10_21054_1144740
  · exact context_10_21055_1144760

theorem unmarked_context_8_1315_1144762 : frontier 13 ⟨1144762, by decide⟩
    (prefixCache 8 1315) (prefixPartial 8 1315) = false := by
  decide +kernel

theorem node_context_8_1315_1144762 : EJMOriginalGlobalDAGData.nodes 13 ⟨1144762, by decide⟩ =
    .split (coordinate 8) (![⟨1142870, by decide⟩,⟨1143858, by decide⟩,⟨1144556, by decide⟩,⟨1144761, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1315_1144762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1315 ⟨1144762, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1315
    ⟨1144762, by decide⟩ (by decide) (![⟨1142870, by decide⟩,⟨1143858, by decide⟩,⟨1144556, by decide⟩,⟨1144761, by decide⟩]) unmarked_context_8_1315_1144762 node_context_8_1315_1144762
  intro a
  fin_cases a
  · exact context_9_5260_1142870
  · exact context_9_5261_1143858
  · exact context_9_5262_1144556
  · exact context_9_5263_1144761

theorem unmarked_context_7_328_1144763 : frontier 14 ⟨1144763, by decide⟩
    (prefixCache 7 328) (prefixPartial 7 328) = false := by
  decide +kernel

theorem node_context_7_328_1144763 : EJMOriginalGlobalDAGData.nodes 14 ⟨1144763, by decide⟩ =
    .split (coordinate 7) (![⟨1135261, by decide⟩,⟨1138131, by decide⟩,⟨1141357, by decide⟩,⟨1144762, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_328_1144763 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 328 ⟨1144763, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 328
    ⟨1144763, by decide⟩ (by decide) (![⟨1135261, by decide⟩,⟨1138131, by decide⟩,⟨1141357, by decide⟩,⟨1144762, by decide⟩]) unmarked_context_7_328_1144763 node_context_7_328_1144763
  intro a
  fin_cases a
  · exact context_8_1312_1135261
  · exact context_8_1313_1138131
  · exact context_8_1314_1141357
  · exact context_8_1315_1144762

theorem selected_cut_41879 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 84224) = some ⟨11, 1, 0, 434745, 84224, 1, 262144⟩ := by
  decide +kernel

theorem context_11_84224_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84224 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 84224 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 84224, 1, 262144⟩
    (by decide) selected_cut_41879

theorem selected_cut_41880 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 336900) = some ⟨12, 1, 0, 448748, 336900, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336900_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336900 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 336900 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 336900, 1, 65536⟩
    (by decide) selected_cut_41880

theorem selected_cut_41881 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 336901) = some ⟨12, 1, 0, 34034, 336901, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336901_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336901 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 336901 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 336901, 1, 65536⟩
    (by decide) selected_cut_41881

theorem selected_cut_41882 : selected 9 ⟨1144808, by decide⟩
    (prefixPartial 12 336902) = some ⟨12, 2, 0, 1144808, 336902, 2673, 65536⟩ := by
  decide +kernel

theorem context_12_336902_1144808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336902 ⟨1144808, by decide⟩ :=
  accepted_of_selected 12 336902 ⟨1144808, by decide⟩ ⟨12, 2, 0, 1144808, 336902, 2673, 65536⟩
    (by decide) selected_cut_41882

theorem selected_cut_41883 : selected 9 ⟨1144855, by decide⟩
    (prefixPartial 12 336903) = some ⟨12, 2, 0, 1144855, 336903, 2813, 65536⟩ := by
  decide +kernel

theorem context_12_336903_1144855 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336903 ⟨1144855, by decide⟩ :=
  accepted_of_selected 12 336903 ⟨1144855, by decide⟩ ⟨12, 2, 0, 1144855, 336903, 2813, 65536⟩
    (by decide) selected_cut_41883

theorem unmarked_context_11_84225_1144856 : frontier 10 ⟨1144856, by decide⟩
    (prefixCache 11 84225) (prefixPartial 11 84225) = false := by
  decide +kernel

theorem node_context_11_84225_1144856 : EJMOriginalGlobalDAGData.nodes 10 ⟨1144856, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1144808, by decide⟩,⟨1144855, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84225_1144856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84225 ⟨1144856, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84225
    ⟨1144856, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1144808, by decide⟩,⟨1144855, by decide⟩]) unmarked_context_11_84225_1144856 node_context_11_84225_1144856
  intro a
  fin_cases a
  · exact context_12_336900_448748
  · exact context_12_336901_34034
  · exact context_12_336902_1144808
  · exact context_12_336903_1144855

theorem selected_cut_41884 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 336904) = some ⟨12, 1, 0, 448748, 336904, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336904_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336904 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 336904 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 336904, 1, 65536⟩
    (by decide) selected_cut_41884

theorem selected_cut_41885 : selected 9 ⟨1144922, by decide⟩
    (prefixPartial 12 336905) = some ⟨12, 2, 0, 1144922, 336905, 2805, 65536⟩ := by
  decide +kernel

theorem context_12_336905_1144922 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336905 ⟨1144922, by decide⟩ :=
  accepted_of_selected 12 336905 ⟨1144922, by decide⟩ ⟨12, 2, 0, 1144922, 336905, 2805, 65536⟩
    (by decide) selected_cut_41885

theorem selected_cut_41886 : selected 9 ⟨1144976, by decide⟩
    (prefixPartial 12 336906) = some ⟨12, 2, 0, 1144976, 336906, 2845, 65536⟩ := by
  decide +kernel

theorem context_12_336906_1144976 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336906 ⟨1144976, by decide⟩ :=
  accepted_of_selected 12 336906 ⟨1144976, by decide⟩ ⟨12, 2, 0, 1144976, 336906, 2845, 65536⟩
    (by decide) selected_cut_41886

theorem selected_cut_41887 : selected 9 ⟨1145035, by decide⟩
    (prefixPartial 12 336907) = some ⟨12, 2, 0, 1145035, 336907, 3145, 65536⟩ := by
  decide +kernel

theorem context_12_336907_1145035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336907 ⟨1145035, by decide⟩ :=
  accepted_of_selected 12 336907 ⟨1145035, by decide⟩ ⟨12, 2, 0, 1145035, 336907, 3145, 65536⟩
    (by decide) selected_cut_41887

theorem unmarked_context_11_84226_1145036 : frontier 10 ⟨1145036, by decide⟩
    (prefixCache 11 84226) (prefixPartial 11 84226) = false := by
  decide +kernel

theorem node_context_11_84226_1145036 : EJMOriginalGlobalDAGData.nodes 10 ⟨1145036, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1144922, by decide⟩,⟨1144976, by decide⟩,⟨1145035, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84226_1145036 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84226 ⟨1145036, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84226
    ⟨1145036, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1144922, by decide⟩,⟨1144976, by decide⟩,⟨1145035, by decide⟩]) unmarked_context_11_84226_1145036 node_context_11_84226_1145036
  intro a
  fin_cases a
  · exact context_12_336904_448748
  · exact context_12_336905_1144922
  · exact context_12_336906_1144976
  · exact context_12_336907_1145035

theorem selected_cut_41888 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 336908) = some ⟨12, 1, 0, 448748, 336908, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336908_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336908 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 336908 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 336908, 1, 65536⟩
    (by decide) selected_cut_41888

theorem selected_cut_41889 : selected 9 ⟨1145090, by decide⟩
    (prefixPartial 12 336909) = some ⟨12, 2, 0, 1145090, 336909, 1433, 65536⟩ := by
  decide +kernel

theorem context_12_336909_1145090 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336909 ⟨1145090, by decide⟩ :=
  accepted_of_selected 12 336909 ⟨1145090, by decide⟩ ⟨12, 2, 0, 1145090, 336909, 1433, 65536⟩
    (by decide) selected_cut_41889

theorem selected_cut_41890 : selected 9 ⟨1145142, by decide⟩
    (prefixPartial 12 336910) = some ⟨12, 2, 0, 1145142, 336910, 2849, 65536⟩ := by
  decide +kernel

theorem context_12_336910_1145142 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336910 ⟨1145142, by decide⟩ :=
  accepted_of_selected 12 336910 ⟨1145142, by decide⟩ ⟨12, 2, 0, 1145142, 336910, 2849, 65536⟩
    (by decide) selected_cut_41890

theorem selected_cut_41891 : selected 9 ⟨1145183, by decide⟩
    (prefixPartial 12 336911) = some ⟨12, 2, 0, 1145183, 336911, 2865, 65536⟩ := by
  decide +kernel

theorem context_12_336911_1145183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336911 ⟨1145183, by decide⟩ :=
  accepted_of_selected 12 336911 ⟨1145183, by decide⟩ ⟨12, 2, 0, 1145183, 336911, 2865, 65536⟩
    (by decide) selected_cut_41891

theorem unmarked_context_11_84227_1145184 : frontier 10 ⟨1145184, by decide⟩
    (prefixCache 11 84227) (prefixPartial 11 84227) = false := by
  decide +kernel

theorem node_context_11_84227_1145184 : EJMOriginalGlobalDAGData.nodes 10 ⟨1145184, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1145090, by decide⟩,⟨1145142, by decide⟩,⟨1145183, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84227_1145184 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84227 ⟨1145184, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84227
    ⟨1145184, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1145090, by decide⟩,⟨1145142, by decide⟩,⟨1145183, by decide⟩]) unmarked_context_11_84227_1145184 node_context_11_84227_1145184
  intro a
  fin_cases a
  · exact context_12_336908_448748
  · exact context_12_336909_1145090
  · exact context_12_336910_1145142
  · exact context_12_336911_1145183

theorem unmarked_context_10_21056_1145185 : frontier 11 ⟨1145185, by decide⟩
    (prefixCache 10 21056) (prefixPartial 10 21056) = false := by
  decide +kernel

theorem node_context_10_21056_1145185 : EJMOriginalGlobalDAGData.nodes 11 ⟨1145185, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨1144856, by decide⟩,⟨1145036, by decide⟩,⟨1145184, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21056_1145185 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21056 ⟨1145185, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21056
    ⟨1145185, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨1144856, by decide⟩,⟨1145036, by decide⟩,⟨1145184, by decide⟩]) unmarked_context_10_21056_1145185 node_context_10_21056_1145185
  intro a
  fin_cases a
  · exact context_11_84224_434745
  · exact context_11_84225_1144856
  · exact context_11_84226_1145036
  · exact context_11_84227_1145184

theorem selected_cut_41892 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 336912) = some ⟨12, 1, 0, 1108174, 336912, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336912_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336912 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 336912 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 336912, 1, 65536⟩
    (by decide) selected_cut_41892

theorem selected_cut_41893 : selected 9 ⟨1145217, by decide⟩
    (prefixPartial 12 336913) = some ⟨12, 2, 0, 1145217, 336913, 2045, 65536⟩ := by
  decide +kernel

theorem context_12_336913_1145217 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336913 ⟨1145217, by decide⟩ :=
  accepted_of_selected 12 336913 ⟨1145217, by decide⟩ ⟨12, 2, 0, 1145217, 336913, 2045, 65536⟩
    (by decide) selected_cut_41893

theorem selected_cut_41894 : selected 9 ⟨1145258, by decide⟩
    (prefixPartial 12 336914) = some ⟨12, 2, 0, 1145258, 336914, 2605, 65536⟩ := by
  decide +kernel

theorem context_12_336914_1145258 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336914 ⟨1145258, by decide⟩ :=
  accepted_of_selected 12 336914 ⟨1145258, by decide⟩ ⟨12, 2, 0, 1145258, 336914, 2605, 65536⟩
    (by decide) selected_cut_41894

theorem selected_cut_41895 : selected 9 ⟨1145302, by decide⟩
    (prefixPartial 12 336915) = some ⟨12, 2, 0, 1145302, 336915, 2673, 65536⟩ := by
  decide +kernel

theorem context_12_336915_1145302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336915 ⟨1145302, by decide⟩ :=
  accepted_of_selected 12 336915 ⟨1145302, by decide⟩ ⟨12, 2, 0, 1145302, 336915, 2673, 65536⟩
    (by decide) selected_cut_41895

theorem unmarked_context_11_84228_1145303 : frontier 10 ⟨1145303, by decide⟩
    (prefixCache 11 84228) (prefixPartial 11 84228) = false := by
  decide +kernel

theorem node_context_11_84228_1145303 : EJMOriginalGlobalDAGData.nodes 10 ⟨1145303, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1145217, by decide⟩,⟨1145258, by decide⟩,⟨1145302, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84228_1145303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84228 ⟨1145303, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84228
    ⟨1145303, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1145217, by decide⟩,⟨1145258, by decide⟩,⟨1145302, by decide⟩]) unmarked_context_11_84228_1145303 node_context_11_84228_1145303
  intro a
  fin_cases a
  · exact context_12_336912_1108174
  · exact context_12_336913_1145217
  · exact context_12_336914_1145258
  · exact context_12_336915_1145302

theorem selected_cut_41896 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 84229) = some ⟨11, 1, 0, 892405, 84229, 1, 262144⟩ := by
  decide +kernel

theorem context_11_84229_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84229 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 84229 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 84229, 1, 262144⟩
    (by decide) selected_cut_41896

theorem selected_cut_41897 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 336920) = some ⟨12, 1, 0, 1108174, 336920, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336920_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336920 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 336920 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 336920, 1, 65536⟩
    (by decide) selected_cut_41897

theorem selected_cut_41898 : selected 9 ⟨1145336, by decide⟩
    (prefixPartial 12 336921) = some ⟨12, 2, 0, 1145336, 336921, 2261, 65536⟩ := by
  decide +kernel

theorem context_12_336921_1145336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336921 ⟨1145336, by decide⟩ :=
  accepted_of_selected 12 336921 ⟨1145336, by decide⟩ ⟨12, 2, 0, 1145336, 336921, 2261, 65536⟩
    (by decide) selected_cut_41898

theorem selected_cut_41899 : selected 9 ⟨1145377, by decide⟩
    (prefixPartial 12 336922) = some ⟨12, 2, 0, 1145377, 336922, 2681, 65536⟩ := by
  decide +kernel

theorem context_12_336922_1145377 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336922 ⟨1145377, by decide⟩ :=
  accepted_of_selected 12 336922 ⟨1145377, by decide⟩ ⟨12, 2, 0, 1145377, 336922, 2681, 65536⟩
    (by decide) selected_cut_41899

theorem selected_cut_41900 : selected 9 ⟨1145434, by decide⟩
    (prefixPartial 12 336923) = some ⟨12, 2, 0, 1145434, 336923, 2941, 65536⟩ := by
  decide +kernel

theorem context_12_336923_1145434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336923 ⟨1145434, by decide⟩ :=
  accepted_of_selected 12 336923 ⟨1145434, by decide⟩ ⟨12, 2, 0, 1145434, 336923, 2941, 65536⟩
    (by decide) selected_cut_41900

theorem unmarked_context_11_84230_1145435 : frontier 10 ⟨1145435, by decide⟩
    (prefixCache 11 84230) (prefixPartial 11 84230) = false := by
  decide +kernel

theorem node_context_11_84230_1145435 : EJMOriginalGlobalDAGData.nodes 10 ⟨1145435, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1145336, by decide⟩,⟨1145377, by decide⟩,⟨1145434, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84230_1145435 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84230 ⟨1145435, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84230
    ⟨1145435, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1145336, by decide⟩,⟨1145377, by decide⟩,⟨1145434, by decide⟩]) unmarked_context_11_84230_1145435 node_context_11_84230_1145435
  intro a
  fin_cases a
  · exact context_12_336920_1108174
  · exact context_12_336921_1145336
  · exact context_12_336922_1145377
  · exact context_12_336923_1145434

theorem selected_cut_41901 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 336924) = some ⟨12, 1, 0, 1108174, 336924, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336924_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336924 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 336924 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 336924, 1, 65536⟩
    (by decide) selected_cut_41901

theorem selected_cut_41902 : selected 9 ⟨1145468, by decide⟩
    (prefixPartial 12 336925) = some ⟨12, 2, 0, 1145468, 336925, 2241, 65536⟩ := by
  decide +kernel

theorem context_12_336925_1145468 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336925 ⟨1145468, by decide⟩ :=
  accepted_of_selected 12 336925 ⟨1145468, by decide⟩ ⟨12, 2, 0, 1145468, 336925, 2241, 65536⟩
    (by decide) selected_cut_41902

theorem selected_cut_41903 : selected 9 ⟨1145526, by decide⟩
    (prefixPartial 12 336926) = some ⟨12, 2, 0, 1145526, 336926, 2885, 65536⟩ := by
  decide +kernel

theorem context_12_336926_1145526 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336926 ⟨1145526, by decide⟩ :=
  accepted_of_selected 12 336926 ⟨1145526, by decide⟩ ⟨12, 2, 0, 1145526, 336926, 2885, 65536⟩
    (by decide) selected_cut_41903

theorem selected_cut_41904 : selected 9 ⟨1145578, by decide⟩
    (prefixPartial 12 336927) = some ⟨12, 2, 0, 1145578, 336927, 2881, 65536⟩ := by
  decide +kernel

theorem context_12_336927_1145578 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336927 ⟨1145578, by decide⟩ :=
  accepted_of_selected 12 336927 ⟨1145578, by decide⟩ ⟨12, 2, 0, 1145578, 336927, 2881, 65536⟩
    (by decide) selected_cut_41904

theorem unmarked_context_11_84231_1145579 : frontier 10 ⟨1145579, by decide⟩
    (prefixCache 11 84231) (prefixPartial 11 84231) = false := by
  decide +kernel

theorem node_context_11_84231_1145579 : EJMOriginalGlobalDAGData.nodes 10 ⟨1145579, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1145468, by decide⟩,⟨1145526, by decide⟩,⟨1145578, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84231_1145579 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84231 ⟨1145579, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84231
    ⟨1145579, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1145468, by decide⟩,⟨1145526, by decide⟩,⟨1145578, by decide⟩]) unmarked_context_11_84231_1145579 node_context_11_84231_1145579
  intro a
  fin_cases a
  · exact context_12_336924_1108174
  · exact context_12_336925_1145468
  · exact context_12_336926_1145526
  · exact context_12_336927_1145578

theorem unmarked_context_10_21057_1145580 : frontier 11 ⟨1145580, by decide⟩
    (prefixCache 10 21057) (prefixPartial 10 21057) = false := by
  decide +kernel

theorem node_context_10_21057_1145580 : EJMOriginalGlobalDAGData.nodes 11 ⟨1145580, by decide⟩ =
    .split (coordinate 10) (![⟨1145303, by decide⟩,⟨892405, by decide⟩,⟨1145435, by decide⟩,⟨1145579, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21057_1145580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21057 ⟨1145580, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21057
    ⟨1145580, by decide⟩ (by decide) (![⟨1145303, by decide⟩,⟨892405, by decide⟩,⟨1145435, by decide⟩,⟨1145579, by decide⟩]) unmarked_context_10_21057_1145580 node_context_10_21057_1145580
  intro a
  fin_cases a
  · exact context_11_84228_1145303
  · exact context_11_84229_892405
  · exact context_11_84230_1145435
  · exact context_11_84231_1145579

theorem selected_cut_41905 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 336928) = some ⟨12, 1, 0, 1108174, 336928, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336928_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336928 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 336928 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 336928, 1, 65536⟩
    (by decide) selected_cut_41905

theorem selected_cut_41906 : selected 9 ⟨1145618, by decide⟩
    (prefixPartial 12 336929) = some ⟨12, 2, 0, 1145618, 336929, 2309, 65536⟩ := by
  decide +kernel

theorem context_12_336929_1145618 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336929 ⟨1145618, by decide⟩ :=
  accepted_of_selected 12 336929 ⟨1145618, by decide⟩ ⟨12, 2, 0, 1145618, 336929, 2309, 65536⟩
    (by decide) selected_cut_41906

theorem selected_cut_41907 : selected 9 ⟨1145665, by decide⟩
    (prefixPartial 12 336930) = some ⟨12, 2, 0, 1145665, 336930, 2705, 65536⟩ := by
  decide +kernel

theorem context_12_336930_1145665 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336930 ⟨1145665, by decide⟩ :=
  accepted_of_selected 12 336930 ⟨1145665, by decide⟩ ⟨12, 2, 0, 1145665, 336930, 2705, 65536⟩
    (by decide) selected_cut_41907

theorem selected_cut_41908 : selected 9 ⟨1145710, by decide⟩
    (prefixPartial 12 336931) = some ⟨12, 2, 0, 1145710, 336931, 2817, 65536⟩ := by
  decide +kernel

theorem context_12_336931_1145710 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336931 ⟨1145710, by decide⟩ :=
  accepted_of_selected 12 336931 ⟨1145710, by decide⟩ ⟨12, 2, 0, 1145710, 336931, 2817, 65536⟩
    (by decide) selected_cut_41908

theorem unmarked_context_11_84232_1145711 : frontier 10 ⟨1145711, by decide⟩
    (prefixCache 11 84232) (prefixPartial 11 84232) = false := by
  decide +kernel

theorem node_context_11_84232_1145711 : EJMOriginalGlobalDAGData.nodes 10 ⟨1145711, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1145618, by decide⟩,⟨1145665, by decide⟩,⟨1145710, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84232_1145711 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84232 ⟨1145711, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84232
    ⟨1145711, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1145618, by decide⟩,⟨1145665, by decide⟩,⟨1145710, by decide⟩]) unmarked_context_11_84232_1145711 node_context_11_84232_1145711
  intro a
  fin_cases a
  · exact context_12_336928_1108174
  · exact context_12_336929_1145618
  · exact context_12_336930_1145665
  · exact context_12_336931_1145710

theorem selected_cut_41909 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 336932) = some ⟨12, 1, 0, 1108174, 336932, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336932_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336932 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 336932 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 336932, 1, 65536⟩
    (by decide) selected_cut_41909

theorem selected_cut_41910 : selected 9 ⟨1145748, by decide⟩
    (prefixPartial 12 336933) = some ⟨12, 2, 0, 1145748, 336933, 2261, 65536⟩ := by
  decide +kernel

theorem context_12_336933_1145748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336933 ⟨1145748, by decide⟩ :=
  accepted_of_selected 12 336933 ⟨1145748, by decide⟩ ⟨12, 2, 0, 1145748, 336933, 2261, 65536⟩
    (by decide) selected_cut_41910

theorem selected_cut_41911 : selected 9 ⟨1145799, by decide⟩
    (prefixPartial 12 336934) = some ⟨12, 2, 0, 1145799, 336934, 2709, 65536⟩ := by
  decide +kernel

theorem context_12_336934_1145799 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336934 ⟨1145799, by decide⟩ :=
  accepted_of_selected 12 336934 ⟨1145799, by decide⟩ ⟨12, 2, 0, 1145799, 336934, 2709, 65536⟩
    (by decide) selected_cut_41911

theorem selected_cut_41912 : selected 9 ⟨1145855, by decide⟩
    (prefixPartial 12 336935) = some ⟨12, 2, 0, 1145855, 336935, 2905, 65536⟩ := by
  decide +kernel

theorem context_12_336935_1145855 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336935 ⟨1145855, by decide⟩ :=
  accepted_of_selected 12 336935 ⟨1145855, by decide⟩ ⟨12, 2, 0, 1145855, 336935, 2905, 65536⟩
    (by decide) selected_cut_41912

theorem unmarked_context_11_84233_1145856 : frontier 10 ⟨1145856, by decide⟩
    (prefixCache 11 84233) (prefixPartial 11 84233) = false := by
  decide +kernel

theorem node_context_11_84233_1145856 : EJMOriginalGlobalDAGData.nodes 10 ⟨1145856, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1145748, by decide⟩,⟨1145799, by decide⟩,⟨1145855, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84233_1145856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84233 ⟨1145856, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84233
    ⟨1145856, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1145748, by decide⟩,⟨1145799, by decide⟩,⟨1145855, by decide⟩]) unmarked_context_11_84233_1145856 node_context_11_84233_1145856
  intro a
  fin_cases a
  · exact context_12_336932_1108174
  · exact context_12_336933_1145748
  · exact context_12_336934_1145799
  · exact context_12_336935_1145855

theorem selected_cut_41913 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 336936) = some ⟨12, 1, 0, 1108174, 336936, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336936_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336936 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 336936 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 336936, 1, 65536⟩
    (by decide) selected_cut_41913

theorem selected_cut_41914 : selected 9 ⟨1145888, by decide⟩
    (prefixPartial 12 336937) = some ⟨12, 2, 0, 1145888, 336937, 2273, 65536⟩ := by
  decide +kernel

theorem context_12_336937_1145888 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336937 ⟨1145888, by decide⟩ :=
  accepted_of_selected 12 336937 ⟨1145888, by decide⟩ ⟨12, 2, 0, 1145888, 336937, 2273, 65536⟩
    (by decide) selected_cut_41914

theorem selected_cut_41915 : selected 9 ⟨1113261, by decide⟩
    (prefixPartial 12 336938) = some ⟨12, 1, 0, 1113261, 336938, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336938_1113261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336938 ⟨1113261, by decide⟩ :=
  accepted_of_selected 12 336938 ⟨1113261, by decide⟩ ⟨12, 1, 0, 1113261, 336938, 1, 65536⟩
    (by decide) selected_cut_41915

theorem selected_cut_41916 : selected 9 ⟨1145941, by decide⟩
    (prefixPartial 12 336939) = some ⟨12, 2, 0, 1145941, 336939, 2841, 65536⟩ := by
  decide +kernel

theorem context_12_336939_1145941 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336939 ⟨1145941, by decide⟩ :=
  accepted_of_selected 12 336939 ⟨1145941, by decide⟩ ⟨12, 2, 0, 1145941, 336939, 2841, 65536⟩
    (by decide) selected_cut_41916

theorem unmarked_context_11_84234_1145942 : frontier 10 ⟨1145942, by decide⟩
    (prefixCache 11 84234) (prefixPartial 11 84234) = false := by
  decide +kernel

theorem node_context_11_84234_1145942 : EJMOriginalGlobalDAGData.nodes 10 ⟨1145942, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1145888, by decide⟩,⟨1113261, by decide⟩,⟨1145941, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84234_1145942 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84234 ⟨1145942, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84234
    ⟨1145942, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1145888, by decide⟩,⟨1113261, by decide⟩,⟨1145941, by decide⟩]) unmarked_context_11_84234_1145942 node_context_11_84234_1145942
  intro a
  fin_cases a
  · exact context_12_336936_1108174
  · exact context_12_336937_1145888
  · exact context_12_336938_1113261
  · exact context_12_336939_1145941

theorem selected_cut_41917 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 336940) = some ⟨12, 1, 0, 1108174, 336940, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336940_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336940 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 336940 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 336940, 1, 65536⟩
    (by decide) selected_cut_41917

theorem selected_cut_41918 : selected 9 ⟨1145982, by decide⟩
    (prefixPartial 12 336941) = some ⟨12, 2, 0, 1145982, 336941, 2473, 65536⟩ := by
  decide +kernel

theorem context_12_336941_1145982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336941 ⟨1145982, by decide⟩ :=
  accepted_of_selected 12 336941 ⟨1145982, by decide⟩ ⟨12, 2, 0, 1145982, 336941, 2473, 65536⟩
    (by decide) selected_cut_41918

theorem selected_cut_41919 : selected 9 ⟨1146042, by decide⟩
    (prefixPartial 12 336942) = some ⟨12, 2, 0, 1146042, 336942, 2909, 65536⟩ := by
  decide +kernel

theorem context_12_336942_1146042 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336942 ⟨1146042, by decide⟩ :=
  accepted_of_selected 12 336942 ⟨1146042, by decide⟩ ⟨12, 2, 0, 1146042, 336942, 2909, 65536⟩
    (by decide) selected_cut_41919

theorem selected_cut_41920 : selected 9 ⟨1146099, by decide⟩
    (prefixPartial 12 336943) = some ⟨12, 2, 0, 1146099, 336943, 3045, 65536⟩ := by
  decide +kernel

theorem context_12_336943_1146099 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336943 ⟨1146099, by decide⟩ :=
  accepted_of_selected 12 336943 ⟨1146099, by decide⟩ ⟨12, 2, 0, 1146099, 336943, 3045, 65536⟩
    (by decide) selected_cut_41920

theorem unmarked_context_11_84235_1146100 : frontier 10 ⟨1146100, by decide⟩
    (prefixCache 11 84235) (prefixPartial 11 84235) = false := by
  decide +kernel

theorem node_context_11_84235_1146100 : EJMOriginalGlobalDAGData.nodes 10 ⟨1146100, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1145982, by decide⟩,⟨1146042, by decide⟩,⟨1146099, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84235_1146100 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84235 ⟨1146100, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84235
    ⟨1146100, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1145982, by decide⟩,⟨1146042, by decide⟩,⟨1146099, by decide⟩]) unmarked_context_11_84235_1146100 node_context_11_84235_1146100
  intro a
  fin_cases a
  · exact context_12_336940_1108174
  · exact context_12_336941_1145982
  · exact context_12_336942_1146042
  · exact context_12_336943_1146099

theorem unmarked_context_10_21058_1146101 : frontier 11 ⟨1146101, by decide⟩
    (prefixCache 10 21058) (prefixPartial 10 21058) = false := by
  decide +kernel

theorem node_context_10_21058_1146101 : EJMOriginalGlobalDAGData.nodes 11 ⟨1146101, by decide⟩ =
    .split (coordinate 10) (![⟨1145711, by decide⟩,⟨1145856, by decide⟩,⟨1145942, by decide⟩,⟨1146100, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21058_1146101 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21058 ⟨1146101, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21058
    ⟨1146101, by decide⟩ (by decide) (![⟨1145711, by decide⟩,⟨1145856, by decide⟩,⟨1145942, by decide⟩,⟨1146100, by decide⟩]) unmarked_context_10_21058_1146101 node_context_10_21058_1146101
  intro a
  fin_cases a
  · exact context_11_84232_1145711
  · exact context_11_84233_1145856
  · exact context_11_84234_1145942
  · exact context_11_84235_1146100

theorem selected_cut_41921 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 336944) = some ⟨12, 1, 0, 1108174, 336944, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336944_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336944 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 336944 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 336944, 1, 65536⟩
    (by decide) selected_cut_41921

theorem selected_cut_41922 : selected 9 ⟨1146133, by decide⟩
    (prefixPartial 12 336945) = some ⟨12, 2, 0, 1146133, 336945, 2109, 65536⟩ := by
  decide +kernel

theorem context_12_336945_1146133 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336945 ⟨1146133, by decide⟩ :=
  accepted_of_selected 12 336945 ⟨1146133, by decide⟩ ⟨12, 2, 0, 1146133, 336945, 2109, 65536⟩
    (by decide) selected_cut_41922

theorem selected_cut_41923 : selected 9 ⟨1146168, by decide⟩
    (prefixPartial 12 336946) = some ⟨12, 2, 0, 1146168, 336946, 2449, 65536⟩ := by
  decide +kernel

theorem context_12_336946_1146168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336946 ⟨1146168, by decide⟩ :=
  accepted_of_selected 12 336946 ⟨1146168, by decide⟩ ⟨12, 2, 0, 1146168, 336946, 2449, 65536⟩
    (by decide) selected_cut_41923

theorem selected_cut_41924 : selected 9 ⟨1146217, by decide⟩
    (prefixPartial 12 336947) = some ⟨12, 2, 0, 1146217, 336947, 2581, 65536⟩ := by
  decide +kernel

theorem context_12_336947_1146217 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336947 ⟨1146217, by decide⟩ :=
  accepted_of_selected 12 336947 ⟨1146217, by decide⟩ ⟨12, 2, 0, 1146217, 336947, 2581, 65536⟩
    (by decide) selected_cut_41924

theorem unmarked_context_11_84236_1146218 : frontier 10 ⟨1146218, by decide⟩
    (prefixCache 11 84236) (prefixPartial 11 84236) = false := by
  decide +kernel

theorem node_context_11_84236_1146218 : EJMOriginalGlobalDAGData.nodes 10 ⟨1146218, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1146133, by decide⟩,⟨1146168, by decide⟩,⟨1146217, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84236_1146218 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84236 ⟨1146218, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84236
    ⟨1146218, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1146133, by decide⟩,⟨1146168, by decide⟩,⟨1146217, by decide⟩]) unmarked_context_11_84236_1146218 node_context_11_84236_1146218
  intro a
  fin_cases a
  · exact context_12_336944_1108174
  · exact context_12_336945_1146133
  · exact context_12_336946_1146168
  · exact context_12_336947_1146217

theorem selected_cut_41925 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 336948) = some ⟨12, 1, 0, 1108174, 336948, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336948_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336948 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 336948 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 336948, 1, 65536⟩
    (by decide) selected_cut_41925

theorem selected_cut_41926 : selected 9 ⟨1146245, by decide⟩
    (prefixPartial 12 336949) = some ⟨12, 2, 0, 1146245, 336949, 2081, 65536⟩ := by
  decide +kernel

theorem context_12_336949_1146245 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336949 ⟨1146245, by decide⟩ :=
  accepted_of_selected 12 336949 ⟨1146245, by decide⟩ ⟨12, 2, 0, 1146245, 336949, 2081, 65536⟩
    (by decide) selected_cut_41926

theorem selected_cut_41927 : selected 9 ⟨1146295, by decide⟩
    (prefixPartial 12 336950) = some ⟨12, 2, 0, 1146295, 336950, 2537, 65536⟩ := by
  decide +kernel

theorem context_12_336950_1146295 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336950 ⟨1146295, by decide⟩ :=
  accepted_of_selected 12 336950 ⟨1146295, by decide⟩ ⟨12, 2, 0, 1146295, 336950, 2537, 65536⟩
    (by decide) selected_cut_41927

theorem selected_cut_41928 : selected 9 ⟨1146355, by decide⟩
    (prefixPartial 12 336951) = some ⟨12, 2, 0, 1146355, 336951, 2889, 65536⟩ := by
  decide +kernel

theorem context_12_336951_1146355 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336951 ⟨1146355, by decide⟩ :=
  accepted_of_selected 12 336951 ⟨1146355, by decide⟩ ⟨12, 2, 0, 1146355, 336951, 2889, 65536⟩
    (by decide) selected_cut_41928

theorem unmarked_context_11_84237_1146356 : frontier 10 ⟨1146356, by decide⟩
    (prefixCache 11 84237) (prefixPartial 11 84237) = false := by
  decide +kernel

theorem node_context_11_84237_1146356 : EJMOriginalGlobalDAGData.nodes 10 ⟨1146356, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1146245, by decide⟩,⟨1146295, by decide⟩,⟨1146355, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84237_1146356 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84237 ⟨1146356, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84237
    ⟨1146356, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1146245, by decide⟩,⟨1146295, by decide⟩,⟨1146355, by decide⟩]) unmarked_context_11_84237_1146356 node_context_11_84237_1146356
  intro a
  fin_cases a
  · exact context_12_336948_1108174
  · exact context_12_336949_1146245
  · exact context_12_336950_1146295
  · exact context_12_336951_1146355

theorem selected_cut_41929 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 336952) = some ⟨12, 1, 0, 1108174, 336952, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336952_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336952 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 336952 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 336952, 1, 65536⟩
    (by decide) selected_cut_41929

theorem selected_cut_41930 : selected 9 ⟨1146392, by decide⟩
    (prefixPartial 12 336953) = some ⟨12, 2, 0, 1146392, 336953, 2205, 65536⟩ := by
  decide +kernel

theorem context_12_336953_1146392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336953 ⟨1146392, by decide⟩ :=
  accepted_of_selected 12 336953 ⟨1146392, by decide⟩ ⟨12, 2, 0, 1146392, 336953, 2205, 65536⟩
    (by decide) selected_cut_41930

theorem selected_cut_41931 : selected 9 ⟨1146436, by decide⟩
    (prefixPartial 12 336954) = some ⟨12, 2, 0, 1146436, 336954, 2545, 65536⟩ := by
  decide +kernel

theorem context_12_336954_1146436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336954 ⟨1146436, by decide⟩ :=
  accepted_of_selected 12 336954 ⟨1146436, by decide⟩ ⟨12, 2, 0, 1146436, 336954, 2545, 65536⟩
    (by decide) selected_cut_41931

theorem selected_cut_41932 : selected 9 ⟨1146496, by decide⟩
    (prefixPartial 12 336955) = some ⟨12, 2, 0, 1146496, 336955, 2937, 65536⟩ := by
  decide +kernel

theorem context_12_336955_1146496 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336955 ⟨1146496, by decide⟩ :=
  accepted_of_selected 12 336955 ⟨1146496, by decide⟩ ⟨12, 2, 0, 1146496, 336955, 2937, 65536⟩
    (by decide) selected_cut_41932

theorem unmarked_context_11_84238_1146497 : frontier 10 ⟨1146497, by decide⟩
    (prefixCache 11 84238) (prefixPartial 11 84238) = false := by
  decide +kernel

theorem node_context_11_84238_1146497 : EJMOriginalGlobalDAGData.nodes 10 ⟨1146497, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1146392, by decide⟩,⟨1146436, by decide⟩,⟨1146496, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84238_1146497 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84238 ⟨1146497, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84238
    ⟨1146497, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1146392, by decide⟩,⟨1146436, by decide⟩,⟨1146496, by decide⟩]) unmarked_context_11_84238_1146497 node_context_11_84238_1146497
  intro a
  fin_cases a
  · exact context_12_336952_1108174
  · exact context_12_336953_1146392
  · exact context_12_336954_1146436
  · exact context_12_336955_1146496

theorem selected_cut_41933 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 336956) = some ⟨12, 1, 0, 1108174, 336956, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336956_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336956 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 336956 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 336956, 1, 65536⟩
    (by decide) selected_cut_41933

theorem selected_cut_41934 : selected 9 ⟨1146529, by decide⟩
    (prefixPartial 12 336957) = some ⟨12, 2, 0, 1146529, 336957, 2049, 65536⟩ := by
  decide +kernel

theorem context_12_336957_1146529 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336957 ⟨1146529, by decide⟩ :=
  accepted_of_selected 12 336957 ⟨1146529, by decide⟩ ⟨12, 2, 0, 1146529, 336957, 2049, 65536⟩
    (by decide) selected_cut_41934

theorem selected_cut_41935 : selected 9 ⟨1146573, by decide⟩
    (prefixPartial 12 336958) = some ⟨12, 2, 0, 1146573, 336958, 2377, 65536⟩ := by
  decide +kernel

theorem context_12_336958_1146573 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336958 ⟨1146573, by decide⟩ :=
  accepted_of_selected 12 336958 ⟨1146573, by decide⟩ ⟨12, 2, 0, 1146573, 336958, 2377, 65536⟩
    (by decide) selected_cut_41935

theorem selected_cut_41936 : selected 9 ⟨1116246, by decide⟩
    (prefixPartial 12 336959) = some ⟨12, 1, 0, 1116246, 336959, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336959_1116246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336959 ⟨1116246, by decide⟩ :=
  accepted_of_selected 12 336959 ⟨1116246, by decide⟩ ⟨12, 1, 0, 1116246, 336959, 1, 65536⟩
    (by decide) selected_cut_41936

theorem unmarked_context_11_84239_1146574 : frontier 10 ⟨1146574, by decide⟩
    (prefixCache 11 84239) (prefixPartial 11 84239) = false := by
  decide +kernel

theorem node_context_11_84239_1146574 : EJMOriginalGlobalDAGData.nodes 10 ⟨1146574, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1146529, by decide⟩,⟨1146573, by decide⟩,⟨1116246, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84239_1146574 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84239 ⟨1146574, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84239
    ⟨1146574, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1146529, by decide⟩,⟨1146573, by decide⟩,⟨1116246, by decide⟩]) unmarked_context_11_84239_1146574 node_context_11_84239_1146574
  intro a
  fin_cases a
  · exact context_12_336956_1108174
  · exact context_12_336957_1146529
  · exact context_12_336958_1146573
  · exact context_12_336959_1116246

theorem unmarked_context_10_21059_1146575 : frontier 11 ⟨1146575, by decide⟩
    (prefixCache 10 21059) (prefixPartial 10 21059) = false := by
  decide +kernel

theorem node_context_10_21059_1146575 : EJMOriginalGlobalDAGData.nodes 11 ⟨1146575, by decide⟩ =
    .split (coordinate 10) (![⟨1146218, by decide⟩,⟨1146356, by decide⟩,⟨1146497, by decide⟩,⟨1146574, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21059_1146575 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21059 ⟨1146575, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21059
    ⟨1146575, by decide⟩ (by decide) (![⟨1146218, by decide⟩,⟨1146356, by decide⟩,⟨1146497, by decide⟩,⟨1146574, by decide⟩]) unmarked_context_10_21059_1146575 node_context_10_21059_1146575
  intro a
  fin_cases a
  · exact context_11_84236_1146218
  · exact context_11_84237_1146356
  · exact context_11_84238_1146497
  · exact context_11_84239_1146574

theorem unmarked_context_9_5264_1146576 : frontier 12 ⟨1146576, by decide⟩
    (prefixCache 9 5264) (prefixPartial 9 5264) = false := by
  decide +kernel

theorem node_context_9_5264_1146576 : EJMOriginalGlobalDAGData.nodes 12 ⟨1146576, by decide⟩ =
    .split (coordinate 9) (![⟨1145185, by decide⟩,⟨1145580, by decide⟩,⟨1146101, by decide⟩,⟨1146575, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5264_1146576 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5264 ⟨1146576, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5264
    ⟨1146576, by decide⟩ (by decide) (![⟨1145185, by decide⟩,⟨1145580, by decide⟩,⟨1146101, by decide⟩,⟨1146575, by decide⟩]) unmarked_context_9_5264_1146576 node_context_9_5264_1146576
  intro a
  fin_cases a
  · exact context_10_21056_1145185
  · exact context_10_21057_1145580
  · exact context_10_21058_1146101
  · exact context_10_21059_1146575

theorem selected_cut_41937 : selected 9 ⟨1113480, by decide⟩
    (prefixPartial 12 336960) = some ⟨12, 1, 0, 1113480, 336960, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336960_1113480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336960 ⟨1113480, by decide⟩ :=
  accepted_of_selected 12 336960 ⟨1113480, by decide⟩ ⟨12, 1, 0, 1113480, 336960, 1, 65536⟩
    (by decide) selected_cut_41937

theorem selected_cut_41938 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 336961) = some ⟨12, 1, 0, 170504, 336961, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336961_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336961 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 336961 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 336961, 1, 65536⟩
    (by decide) selected_cut_41938

theorem selected_cut_41939 : selected 9 ⟨1146618, by decide⟩
    (prefixPartial 12 336962) = some ⟨12, 2, 0, 1146618, 336962, 2265, 65536⟩ := by
  decide +kernel

theorem context_12_336962_1146618 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336962 ⟨1146618, by decide⟩ :=
  accepted_of_selected 12 336962 ⟨1146618, by decide⟩ ⟨12, 2, 0, 1146618, 336962, 2265, 65536⟩
    (by decide) selected_cut_41939

theorem selected_cut_41940 : selected 9 ⟨1146650, by decide⟩
    (prefixPartial 12 336963) = some ⟨12, 2, 0, 1146650, 336963, 2101, 65536⟩ := by
  decide +kernel

theorem context_12_336963_1146650 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336963 ⟨1146650, by decide⟩ :=
  accepted_of_selected 12 336963 ⟨1146650, by decide⟩ ⟨12, 2, 0, 1146650, 336963, 2101, 65536⟩
    (by decide) selected_cut_41940

theorem unmarked_context_11_84240_1146651 : frontier 10 ⟨1146651, by decide⟩
    (prefixCache 11 84240) (prefixPartial 11 84240) = false := by
  decide +kernel

theorem node_context_11_84240_1146651 : EJMOriginalGlobalDAGData.nodes 10 ⟨1146651, by decide⟩ =
    .split (coordinate 11) (![⟨1113480, by decide⟩,⟨170504, by decide⟩,⟨1146618, by decide⟩,⟨1146650, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84240_1146651 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84240 ⟨1146651, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84240
    ⟨1146651, by decide⟩ (by decide) (![⟨1113480, by decide⟩,⟨170504, by decide⟩,⟨1146618, by decide⟩,⟨1146650, by decide⟩]) unmarked_context_11_84240_1146651 node_context_11_84240_1146651
  intro a
  fin_cases a
  · exact context_12_336960_1113480
  · exact context_12_336961_170504
  · exact context_12_336962_1146618
  · exact context_12_336963_1146650

theorem selected_cut_41941 : selected 9 ⟨1146672, by decide⟩
    (prefixPartial 12 336964) = some ⟨12, 2, 0, 1146672, 336964, 1465, 65536⟩ := by
  decide +kernel

theorem context_12_336964_1146672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336964 ⟨1146672, by decide⟩ :=
  accepted_of_selected 12 336964 ⟨1146672, by decide⟩ ⟨12, 2, 0, 1146672, 336964, 1465, 65536⟩
    (by decide) selected_cut_41941

theorem selected_cut_41942 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 336965) = some ⟨12, 1, 0, 170504, 336965, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336965_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336965 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 336965 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 336965, 1, 65536⟩
    (by decide) selected_cut_41942

theorem selected_cut_41943 : selected 9 ⟨1146704, by decide⟩
    (prefixPartial 12 336966) = some ⟨12, 2, 0, 1146704, 336966, 1949, 65536⟩ := by
  decide +kernel

theorem context_12_336966_1146704 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336966 ⟨1146704, by decide⟩ :=
  accepted_of_selected 12 336966 ⟨1146704, by decide⟩ ⟨12, 2, 0, 1146704, 336966, 1949, 65536⟩
    (by decide) selected_cut_41943

theorem selected_cut_41944 : selected 9 ⟨1146735, by decide⟩
    (prefixPartial 12 336967) = some ⟨12, 2, 0, 1146735, 336967, 1901, 65536⟩ := by
  decide +kernel

theorem context_12_336967_1146735 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336967 ⟨1146735, by decide⟩ :=
  accepted_of_selected 12 336967 ⟨1146735, by decide⟩ ⟨12, 2, 0, 1146735, 336967, 1901, 65536⟩
    (by decide) selected_cut_41944

theorem unmarked_context_11_84241_1146736 : frontier 10 ⟨1146736, by decide⟩
    (prefixCache 11 84241) (prefixPartial 11 84241) = false := by
  decide +kernel

theorem node_context_11_84241_1146736 : EJMOriginalGlobalDAGData.nodes 10 ⟨1146736, by decide⟩ =
    .split (coordinate 11) (![⟨1146672, by decide⟩,⟨170504, by decide⟩,⟨1146704, by decide⟩,⟨1146735, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84241_1146736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84241 ⟨1146736, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84241
    ⟨1146736, by decide⟩ (by decide) (![⟨1146672, by decide⟩,⟨170504, by decide⟩,⟨1146704, by decide⟩,⟨1146735, by decide⟩]) unmarked_context_11_84241_1146736 node_context_11_84241_1146736
  intro a
  fin_cases a
  · exact context_12_336964_1146672
  · exact context_12_336965_170504
  · exact context_12_336966_1146704
  · exact context_12_336967_1146735

theorem selected_cut_41945 : selected 9 ⟨1146762, by decide⟩
    (prefixPartial 12 336968) = some ⟨12, 2, 0, 1146762, 336968, 1729, 65536⟩ := by
  decide +kernel

theorem context_12_336968_1146762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336968 ⟨1146762, by decide⟩ :=
  accepted_of_selected 12 336968 ⟨1146762, by decide⟩ ⟨12, 2, 0, 1146762, 336968, 1729, 65536⟩
    (by decide) selected_cut_41945

theorem selected_cut_41946 : selected 9 ⟨1146794, by decide⟩
    (prefixPartial 12 336969) = some ⟨12, 2, 0, 1146794, 336969, 817, 65536⟩ := by
  decide +kernel

theorem context_12_336969_1146794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336969 ⟨1146794, by decide⟩ :=
  accepted_of_selected 12 336969 ⟨1146794, by decide⟩ ⟨12, 2, 0, 1146794, 336969, 817, 65536⟩
    (by decide) selected_cut_41946

theorem selected_cut_41947 : selected 9 ⟨1146840, by decide⟩
    (prefixPartial 12 336970) = some ⟨12, 2, 0, 1146840, 336970, 2341, 65536⟩ := by
  decide +kernel

theorem context_12_336970_1146840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336970 ⟨1146840, by decide⟩ :=
  accepted_of_selected 12 336970 ⟨1146840, by decide⟩ ⟨12, 2, 0, 1146840, 336970, 2341, 65536⟩
    (by decide) selected_cut_41947

theorem selected_cut_41948 : selected 9 ⟨1146874, by decide⟩
    (prefixPartial 12 336971) = some ⟨12, 2, 0, 1146874, 336971, 2185, 65536⟩ := by
  decide +kernel

theorem context_12_336971_1146874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336971 ⟨1146874, by decide⟩ :=
  accepted_of_selected 12 336971 ⟨1146874, by decide⟩ ⟨12, 2, 0, 1146874, 336971, 2185, 65536⟩
    (by decide) selected_cut_41948

theorem unmarked_context_11_84242_1146875 : frontier 10 ⟨1146875, by decide⟩
    (prefixCache 11 84242) (prefixPartial 11 84242) = false := by
  decide +kernel

theorem node_context_11_84242_1146875 : EJMOriginalGlobalDAGData.nodes 10 ⟨1146875, by decide⟩ =
    .split (coordinate 11) (![⟨1146762, by decide⟩,⟨1146794, by decide⟩,⟨1146840, by decide⟩,⟨1146874, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84242_1146875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84242 ⟨1146875, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84242
    ⟨1146875, by decide⟩ (by decide) (![⟨1146762, by decide⟩,⟨1146794, by decide⟩,⟨1146840, by decide⟩,⟨1146874, by decide⟩]) unmarked_context_11_84242_1146875 node_context_11_84242_1146875
  intro a
  fin_cases a
  · exact context_12_336968_1146762
  · exact context_12_336969_1146794
  · exact context_12_336970_1146840
  · exact context_12_336971_1146874

theorem selected_cut_41949 : selected 9 ⟨1146897, by decide⟩
    (prefixPartial 12 336972) = some ⟨12, 2, 0, 1146897, 336972, 1621, 65536⟩ := by
  decide +kernel

theorem context_12_336972_1146897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336972 ⟨1146897, by decide⟩ :=
  accepted_of_selected 12 336972 ⟨1146897, by decide⟩ ⟨12, 2, 0, 1146897, 336972, 1621, 65536⟩
    (by decide) selected_cut_41949

theorem selected_cut_41950 : selected 9 ⟨1146919, by decide⟩
    (prefixPartial 12 336973) = some ⟨12, 2, 0, 1146919, 336973, 801, 65536⟩ := by
  decide +kernel

theorem context_12_336973_1146919 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336973 ⟨1146919, by decide⟩ :=
  accepted_of_selected 12 336973 ⟨1146919, by decide⟩ ⟨12, 2, 0, 1146919, 336973, 801, 65536⟩
    (by decide) selected_cut_41950

theorem selected_cut_41951 : selected 9 ⟨1146961, by decide⟩
    (prefixPartial 12 336974) = some ⟨12, 2, 0, 1146961, 336974, 2177, 65536⟩ := by
  decide +kernel

theorem context_12_336974_1146961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336974 ⟨1146961, by decide⟩ :=
  accepted_of_selected 12 336974 ⟨1146961, by decide⟩ ⟨12, 2, 0, 1146961, 336974, 2177, 65536⟩
    (by decide) selected_cut_41951

theorem selected_cut_41952 : selected 9 ⟨1146990, by decide⟩
    (prefixPartial 12 336975) = some ⟨12, 2, 0, 1146990, 336975, 2137, 65536⟩ := by
  decide +kernel

theorem context_12_336975_1146990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336975 ⟨1146990, by decide⟩ :=
  accepted_of_selected 12 336975 ⟨1146990, by decide⟩ ⟨12, 2, 0, 1146990, 336975, 2137, 65536⟩
    (by decide) selected_cut_41952

theorem unmarked_context_11_84243_1146991 : frontier 10 ⟨1146991, by decide⟩
    (prefixCache 11 84243) (prefixPartial 11 84243) = false := by
  decide +kernel

theorem node_context_11_84243_1146991 : EJMOriginalGlobalDAGData.nodes 10 ⟨1146991, by decide⟩ =
    .split (coordinate 11) (![⟨1146897, by decide⟩,⟨1146919, by decide⟩,⟨1146961, by decide⟩,⟨1146990, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84243_1146991 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84243 ⟨1146991, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84243
    ⟨1146991, by decide⟩ (by decide) (![⟨1146897, by decide⟩,⟨1146919, by decide⟩,⟨1146961, by decide⟩,⟨1146990, by decide⟩]) unmarked_context_11_84243_1146991 node_context_11_84243_1146991
  intro a
  fin_cases a
  · exact context_12_336972_1146897
  · exact context_12_336973_1146919
  · exact context_12_336974_1146961
  · exact context_12_336975_1146990

theorem unmarked_context_10_21060_1146992 : frontier 11 ⟨1146992, by decide⟩
    (prefixCache 10 21060) (prefixPartial 10 21060) = false := by
  decide +kernel

theorem node_context_10_21060_1146992 : EJMOriginalGlobalDAGData.nodes 11 ⟨1146992, by decide⟩ =
    .split (coordinate 10) (![⟨1146651, by decide⟩,⟨1146736, by decide⟩,⟨1146875, by decide⟩,⟨1146991, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21060_1146992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21060 ⟨1146992, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21060
    ⟨1146992, by decide⟩ (by decide) (![⟨1146651, by decide⟩,⟨1146736, by decide⟩,⟨1146875, by decide⟩,⟨1146991, by decide⟩]) unmarked_context_10_21060_1146992 node_context_10_21060_1146992
  intro a
  fin_cases a
  · exact context_11_84240_1146651
  · exact context_11_84241_1146736
  · exact context_11_84242_1146875
  · exact context_11_84243_1146991

theorem selected_cut_41953 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 21061) = some ⟨10, 1, 0, 893098, 21061, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_21061_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21061 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 21061 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 21061, 1, 1048576⟩
    (by decide) selected_cut_41953

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
