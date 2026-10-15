/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover508
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_48867 : selected 11 ⟨1375695, by decide⟩
    (prefixPartial 10 25239) = some ⟨10, 2, 0, 1375695, 25239, 2593, 1048576⟩ := by
  decide +kernel

theorem context_10_25239_1375695 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25239 ⟨1375695, by decide⟩ :=
  accepted_of_selected 10 25239 ⟨1375695, by decide⟩ ⟨10, 2, 0, 1375695, 25239, 2593, 1048576⟩
    (by decide) selected_cut_48867

theorem unmarked_context_9_6309_1375696 : frontier 12 ⟨1375696, by decide⟩
    (prefixCache 9 6309) (prefixPartial 9 6309) = false := by
  decide +kernel

theorem node_context_9_6309_1375696 : EJMOriginalGlobalDAGData.nodes 12 ⟨1375696, by decide⟩ =
    .split (coordinate 9) (![⟨1375326, by decide⟩,⟨893098, by decide⟩,⟨1375533, by decide⟩,⟨1375695, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6309_1375696 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6309 ⟨1375696, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6309
    ⟨1375696, by decide⟩ (by decide) (![⟨1375326, by decide⟩,⟨893098, by decide⟩,⟨1375533, by decide⟩,⟨1375695, by decide⟩]) unmarked_context_9_6309_1375696 node_context_9_6309_1375696
  intro a
  fin_cases a
  · exact context_10_25236_1375326
  · exact context_10_25237_893098
  · exact context_10_25238_1375533
  · exact context_10_25239_1375695

theorem selected_cut_48868 : selected 11 ⟨1375811, by decide⟩
    (prefixPartial 10 25240) = some ⟨10, 2, 0, 1375811, 25240, 1549, 1048576⟩ := by
  decide +kernel

theorem context_10_25240_1375811 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25240 ⟨1375811, by decide⟩ :=
  accepted_of_selected 10 25240 ⟨1375811, by decide⟩ ⟨10, 2, 0, 1375811, 25240, 1549, 1048576⟩
    (by decide) selected_cut_48868

theorem selected_cut_48869 : selected 11 ⟨1375956, by decide⟩
    (prefixPartial 10 25241) = some ⟨10, 2, 0, 1375956, 25241, 1929, 1048576⟩ := by
  decide +kernel

theorem context_10_25241_1375956 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25241 ⟨1375956, by decide⟩ :=
  accepted_of_selected 10 25241 ⟨1375956, by decide⟩ ⟨10, 2, 0, 1375956, 25241, 1929, 1048576⟩
    (by decide) selected_cut_48869

theorem selected_cut_48870 : selected 11 ⟨1376008, by decide⟩
    (prefixPartial 10 25242) = some ⟨10, 2, 0, 1376008, 25242, 697, 1048576⟩ := by
  decide +kernel

theorem context_10_25242_1376008 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25242 ⟨1376008, by decide⟩ :=
  accepted_of_selected 10 25242 ⟨1376008, by decide⟩ ⟨10, 2, 0, 1376008, 25242, 697, 1048576⟩
    (by decide) selected_cut_48870

theorem selected_cut_48871 : selected 11 ⟨1376022, by decide⟩
    (prefixPartial 10 25243) = some ⟨10, 2, 0, 1376022, 25243, 141, 1048576⟩ := by
  decide +kernel

theorem context_10_25243_1376022 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25243 ⟨1376022, by decide⟩ :=
  accepted_of_selected 10 25243 ⟨1376022, by decide⟩ ⟨10, 2, 0, 1376022, 25243, 141, 1048576⟩
    (by decide) selected_cut_48871

theorem unmarked_context_9_6310_1376023 : frontier 12 ⟨1376023, by decide⟩
    (prefixCache 9 6310) (prefixPartial 9 6310) = false := by
  decide +kernel

theorem node_context_9_6310_1376023 : EJMOriginalGlobalDAGData.nodes 12 ⟨1376023, by decide⟩ =
    .split (coordinate 9) (![⟨1375811, by decide⟩,⟨1375956, by decide⟩,⟨1376008, by decide⟩,⟨1376022, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6310_1376023 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6310 ⟨1376023, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6310
    ⟨1376023, by decide⟩ (by decide) (![⟨1375811, by decide⟩,⟨1375956, by decide⟩,⟨1376008, by decide⟩,⟨1376022, by decide⟩]) unmarked_context_9_6310_1376023 node_context_9_6310_1376023
  intro a
  fin_cases a
  · exact context_10_25240_1375811
  · exact context_10_25241_1375956
  · exact context_10_25242_1376008
  · exact context_10_25243_1376022

theorem selected_cut_48872 : selected 12 ⟨1376082, by decide⟩
    (prefixPartial 9 6311) = some ⟨9, 2, 0, 1376082, 6311, 581, 4194304⟩ := by
  decide +kernel

theorem context_9_6311_1376082 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6311 ⟨1376082, by decide⟩ :=
  accepted_of_selected 9 6311 ⟨1376082, by decide⟩ ⟨9, 2, 0, 1376082, 6311, 581, 4194304⟩
    (by decide) selected_cut_48872

theorem unmarked_context_8_1577_1376083 : frontier 13 ⟨1376083, by decide⟩
    (prefixCache 8 1577) (prefixPartial 8 1577) = false := by
  decide +kernel

theorem node_context_8_1577_1376083 : EJMOriginalGlobalDAGData.nodes 13 ⟨1376083, by decide⟩ =
    .split (coordinate 8) (![⟨1375056, by decide⟩,⟨1375696, by decide⟩,⟨1376023, by decide⟩,⟨1376082, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1577_1376083 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1577 ⟨1376083, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1577
    ⟨1376083, by decide⟩ (by decide) (![⟨1375056, by decide⟩,⟨1375696, by decide⟩,⟨1376023, by decide⟩,⟨1376082, by decide⟩]) unmarked_context_8_1577_1376083 node_context_8_1577_1376083
  intro a
  fin_cases a
  · exact context_9_6308_1375056
  · exact context_9_6309_1375696
  · exact context_9_6310_1376023
  · exact context_9_6311_1376082

theorem selected_cut_48873 : selected 13 ⟨1366235, by decide⟩
    (prefixPartial 8 1578) = some ⟨8, 1, 0, 1366235, 1578, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_1578_1366235 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1578 ⟨1366235, by decide⟩ :=
  accepted_of_selected 8 1578 ⟨1366235, by decide⟩ ⟨8, 1, 0, 1366235, 1578, 1, 16777216⟩
    (by decide) selected_cut_48873

theorem selected_cut_48874 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 101056) = some ⟨11, 1, 0, 434745, 101056, 1, 262144⟩ := by
  decide +kernel

theorem context_11_101056_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101056 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 101056 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 101056, 1, 262144⟩
    (by decide) selected_cut_48874

theorem selected_cut_48875 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 101057) = some ⟨11, 1, 0, 434745, 101057, 1, 262144⟩ := by
  decide +kernel

theorem context_11_101057_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101057 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 101057 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 101057, 1, 262144⟩
    (by decide) selected_cut_48875

theorem selected_cut_48876 : selected 10 ⟨1376216, by decide⟩
    (prefixPartial 11 101058) = some ⟨11, 2, 0, 1376216, 101058, 3181, 262144⟩ := by
  decide +kernel

theorem context_11_101058_1376216 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101058 ⟨1376216, by decide⟩ :=
  accepted_of_selected 11 101058 ⟨1376216, by decide⟩ ⟨11, 2, 0, 1376216, 101058, 3181, 262144⟩
    (by decide) selected_cut_48876

theorem selected_cut_48877 : selected 10 ⟨1376270, by decide⟩
    (prefixPartial 11 101059) = some ⟨11, 2, 0, 1376270, 101059, 2109, 262144⟩ := by
  decide +kernel

theorem context_11_101059_1376270 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101059 ⟨1376270, by decide⟩ :=
  accepted_of_selected 11 101059 ⟨1376270, by decide⟩ ⟨11, 2, 0, 1376270, 101059, 2109, 262144⟩
    (by decide) selected_cut_48877

theorem unmarked_context_10_25264_1376271 : frontier 11 ⟨1376271, by decide⟩
    (prefixCache 10 25264) (prefixPartial 10 25264) = false := by
  decide +kernel

theorem node_context_10_25264_1376271 : EJMOriginalGlobalDAGData.nodes 11 ⟨1376271, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨434745, by decide⟩,⟨1376216, by decide⟩,⟨1376270, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25264_1376271 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25264 ⟨1376271, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25264
    ⟨1376271, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨434745, by decide⟩,⟨1376216, by decide⟩,⟨1376270, by decide⟩]) unmarked_context_10_25264_1376271 node_context_10_25264_1376271
  intro a
  fin_cases a
  · exact context_11_101056_434745
  · exact context_11_101057_434745
  · exact context_11_101058_1376216
  · exact context_11_101059_1376270

theorem selected_cut_48878 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 404240) = some ⟨12, 1, 0, 1108174, 404240, 1, 65536⟩ := by
  decide +kernel

theorem context_12_404240_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 404240 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 404240 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 404240, 1, 65536⟩
    (by decide) selected_cut_48878

theorem selected_cut_48879 : selected 9 ⟨1376377, by decide⟩
    (prefixPartial 12 404241) = some ⟨12, 2, 0, 1376377, 404241, 2825, 65536⟩ := by
  decide +kernel

theorem context_12_404241_1376377 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 404241 ⟨1376377, by decide⟩ :=
  accepted_of_selected 12 404241 ⟨1376377, by decide⟩ ⟨12, 2, 0, 1376377, 404241, 2825, 65536⟩
    (by decide) selected_cut_48879

theorem selected_cut_48880 : selected 9 ⟨1376449, by decide⟩
    (prefixPartial 12 404242) = some ⟨12, 2, 0, 1376449, 404242, 2341, 65536⟩ := by
  decide +kernel

theorem context_12_404242_1376449 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 404242 ⟨1376449, by decide⟩ :=
  accepted_of_selected 12 404242 ⟨1376449, by decide⟩ ⟨12, 2, 0, 1376449, 404242, 2341, 65536⟩
    (by decide) selected_cut_48880

theorem selected_cut_48881 : selected 9 ⟨1376530, by decide⟩
    (prefixPartial 12 404243) = some ⟨12, 2, 0, 1376530, 404243, 2645, 65536⟩ := by
  decide +kernel

theorem context_12_404243_1376530 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 404243 ⟨1376530, by decide⟩ :=
  accepted_of_selected 12 404243 ⟨1376530, by decide⟩ ⟨12, 2, 0, 1376530, 404243, 2645, 65536⟩
    (by decide) selected_cut_48881

theorem unmarked_context_11_101060_1376531 : frontier 10 ⟨1376531, by decide⟩
    (prefixCache 11 101060) (prefixPartial 11 101060) = false := by
  decide +kernel

theorem node_context_11_101060_1376531 : EJMOriginalGlobalDAGData.nodes 10 ⟨1376531, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1376377, by decide⟩,⟨1376449, by decide⟩,⟨1376530, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_101060_1376531 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101060 ⟨1376531, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 101060
    ⟨1376531, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1376377, by decide⟩,⟨1376449, by decide⟩,⟨1376530, by decide⟩]) unmarked_context_11_101060_1376531 node_context_11_101060_1376531
  intro a
  fin_cases a
  · exact context_12_404240_1108174
  · exact context_12_404241_1376377
  · exact context_12_404242_1376449
  · exact context_12_404243_1376530

theorem selected_cut_48882 : selected 10 ⟨1376594, by decide⟩
    (prefixPartial 11 101061) = some ⟨11, 2, 0, 1376594, 101061, 2073, 262144⟩ := by
  decide +kernel

theorem context_11_101061_1376594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101061 ⟨1376594, by decide⟩ :=
  accepted_of_selected 11 101061 ⟨1376594, by decide⟩ ⟨11, 2, 0, 1376594, 101061, 2073, 262144⟩
    (by decide) selected_cut_48882

theorem selected_cut_48883 : selected 10 ⟨1376718, by decide⟩
    (prefixPartial 11 101062) = some ⟨11, 2, 0, 1376718, 101062, 3309, 262144⟩ := by
  decide +kernel

theorem context_11_101062_1376718 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101062 ⟨1376718, by decide⟩ :=
  accepted_of_selected 11 101062 ⟨1376718, by decide⟩ ⟨11, 2, 0, 1376718, 101062, 3309, 262144⟩
    (by decide) selected_cut_48883

theorem selected_cut_48884 : selected 10 ⟨1376833, by decide⟩
    (prefixPartial 11 101063) = some ⟨11, 2, 0, 1376833, 101063, 3957, 262144⟩ := by
  decide +kernel

theorem context_11_101063_1376833 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101063 ⟨1376833, by decide⟩ :=
  accepted_of_selected 11 101063 ⟨1376833, by decide⟩ ⟨11, 2, 0, 1376833, 101063, 3957, 262144⟩
    (by decide) selected_cut_48884

theorem unmarked_context_10_25265_1376834 : frontier 11 ⟨1376834, by decide⟩
    (prefixCache 10 25265) (prefixPartial 10 25265) = false := by
  decide +kernel

theorem node_context_10_25265_1376834 : EJMOriginalGlobalDAGData.nodes 11 ⟨1376834, by decide⟩ =
    .split (coordinate 10) (![⟨1376531, by decide⟩,⟨1376594, by decide⟩,⟨1376718, by decide⟩,⟨1376833, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25265_1376834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25265 ⟨1376834, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25265
    ⟨1376834, by decide⟩ (by decide) (![⟨1376531, by decide⟩,⟨1376594, by decide⟩,⟨1376718, by decide⟩,⟨1376833, by decide⟩]) unmarked_context_10_25265_1376834 node_context_10_25265_1376834
  intro a
  fin_cases a
  · exact context_11_101060_1376531
  · exact context_11_101061_1376594
  · exact context_11_101062_1376718
  · exact context_11_101063_1376833

theorem selected_cut_48885 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 404256) = some ⟨12, 1, 0, 1108174, 404256, 1, 65536⟩ := by
  decide +kernel

theorem context_12_404256_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 404256 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 404256 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 404256, 1, 65536⟩
    (by decide) selected_cut_48885

theorem selected_cut_48886 : selected 9 ⟨1376892, by decide⟩
    (prefixPartial 12 404257) = some ⟨12, 2, 0, 1376892, 404257, 1877, 65536⟩ := by
  decide +kernel

theorem context_12_404257_1376892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 404257 ⟨1376892, by decide⟩ :=
  accepted_of_selected 12 404257 ⟨1376892, by decide⟩ ⟨12, 2, 0, 1376892, 404257, 1877, 65536⟩
    (by decide) selected_cut_48886

theorem selected_cut_48887 : selected 9 ⟨1376935, by decide⟩
    (prefixPartial 12 404258) = some ⟨12, 2, 0, 1376935, 404258, 1581, 65536⟩ := by
  decide +kernel

theorem context_12_404258_1376935 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 404258 ⟨1376935, by decide⟩ :=
  accepted_of_selected 12 404258 ⟨1376935, by decide⟩ ⟨12, 2, 0, 1376935, 404258, 1581, 65536⟩
    (by decide) selected_cut_48887

theorem selected_cut_48888 : selected 9 ⟨1376978, by decide⟩
    (prefixPartial 12 404259) = some ⟨12, 2, 0, 1376978, 404259, 1705, 65536⟩ := by
  decide +kernel

theorem context_12_404259_1376978 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 404259 ⟨1376978, by decide⟩ :=
  accepted_of_selected 12 404259 ⟨1376978, by decide⟩ ⟨12, 2, 0, 1376978, 404259, 1705, 65536⟩
    (by decide) selected_cut_48888

theorem unmarked_context_11_101064_1376979 : frontier 10 ⟨1376979, by decide⟩
    (prefixCache 11 101064) (prefixPartial 11 101064) = false := by
  decide +kernel

theorem node_context_11_101064_1376979 : EJMOriginalGlobalDAGData.nodes 10 ⟨1376979, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1376892, by decide⟩,⟨1376935, by decide⟩,⟨1376978, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_101064_1376979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101064 ⟨1376979, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 101064
    ⟨1376979, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1376892, by decide⟩,⟨1376935, by decide⟩,⟨1376978, by decide⟩]) unmarked_context_11_101064_1376979 node_context_11_101064_1376979
  intro a
  fin_cases a
  · exact context_12_404256_1108174
  · exact context_12_404257_1376892
  · exact context_12_404258_1376935
  · exact context_12_404259_1376978

theorem selected_cut_48889 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 404260) = some ⟨12, 1, 0, 1108174, 404260, 1, 65536⟩ := by
  decide +kernel

theorem context_12_404260_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 404260 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 404260 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 404260, 1, 65536⟩
    (by decide) selected_cut_48889

theorem selected_cut_48890 : selected 9 ⟨1377016, by decide⟩
    (prefixPartial 12 404261) = some ⟨12, 2, 0, 1377016, 404261, 1573, 65536⟩ := by
  decide +kernel

theorem context_12_404261_1377016 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 404261 ⟨1377016, by decide⟩ :=
  accepted_of_selected 12 404261 ⟨1377016, by decide⟩ ⟨12, 2, 0, 1377016, 404261, 1573, 65536⟩
    (by decide) selected_cut_48890

theorem selected_cut_48891 : selected 9 ⟨1377052, by decide⟩
    (prefixPartial 12 404262) = some ⟨12, 2, 0, 1377052, 404262, 1449, 65536⟩ := by
  decide +kernel

theorem context_12_404262_1377052 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 404262 ⟨1377052, by decide⟩ :=
  accepted_of_selected 12 404262 ⟨1377052, by decide⟩ ⟨12, 2, 0, 1377052, 404262, 1449, 65536⟩
    (by decide) selected_cut_48891

theorem selected_cut_48892 : selected 9 ⟨1377083, by decide⟩
    (prefixPartial 12 404263) = some ⟨12, 2, 0, 1377083, 404263, 1465, 65536⟩ := by
  decide +kernel

theorem context_12_404263_1377083 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 404263 ⟨1377083, by decide⟩ :=
  accepted_of_selected 12 404263 ⟨1377083, by decide⟩ ⟨12, 2, 0, 1377083, 404263, 1465, 65536⟩
    (by decide) selected_cut_48892

theorem unmarked_context_11_101065_1377084 : frontier 10 ⟨1377084, by decide⟩
    (prefixCache 11 101065) (prefixPartial 11 101065) = false := by
  decide +kernel

theorem node_context_11_101065_1377084 : EJMOriginalGlobalDAGData.nodes 10 ⟨1377084, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1377016, by decide⟩,⟨1377052, by decide⟩,⟨1377083, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_101065_1377084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101065 ⟨1377084, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 101065
    ⟨1377084, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1377016, by decide⟩,⟨1377052, by decide⟩,⟨1377083, by decide⟩]) unmarked_context_11_101065_1377084 node_context_11_101065_1377084
  intro a
  fin_cases a
  · exact context_12_404260_1108174
  · exact context_12_404261_1377016
  · exact context_12_404262_1377052
  · exact context_12_404263_1377083

theorem selected_cut_48893 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 101066) = some ⟨11, 1, 0, 900587, 101066, 1, 262144⟩ := by
  decide +kernel

theorem context_11_101066_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101066 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 101066 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 101066, 1, 262144⟩
    (by decide) selected_cut_48893

theorem selected_cut_48894 : selected 10 ⟨1377155, by decide⟩
    (prefixPartial 11 101067) = some ⟨11, 2, 0, 1377155, 101067, 2853, 262144⟩ := by
  decide +kernel

theorem context_11_101067_1377155 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101067 ⟨1377155, by decide⟩ :=
  accepted_of_selected 11 101067 ⟨1377155, by decide⟩ ⟨11, 2, 0, 1377155, 101067, 2853, 262144⟩
    (by decide) selected_cut_48894

theorem unmarked_context_10_25266_1377156 : frontier 11 ⟨1377156, by decide⟩
    (prefixCache 10 25266) (prefixPartial 10 25266) = false := by
  decide +kernel

theorem node_context_10_25266_1377156 : EJMOriginalGlobalDAGData.nodes 11 ⟨1377156, by decide⟩ =
    .split (coordinate 10) (![⟨1376979, by decide⟩,⟨1377084, by decide⟩,⟨900587, by decide⟩,⟨1377155, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25266_1377156 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25266 ⟨1377156, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25266
    ⟨1377156, by decide⟩ (by decide) (![⟨1376979, by decide⟩,⟨1377084, by decide⟩,⟨900587, by decide⟩,⟨1377155, by decide⟩]) unmarked_context_10_25266_1377156 node_context_10_25266_1377156
  intro a
  fin_cases a
  · exact context_11_101064_1376979
  · exact context_11_101065_1377084
  · exact context_11_101066_900587
  · exact context_11_101067_1377155

theorem selected_cut_48895 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 404272) = some ⟨12, 1, 0, 1108174, 404272, 1, 65536⟩ := by
  decide +kernel

theorem context_12_404272_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 404272 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 404272 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 404272, 1, 65536⟩
    (by decide) selected_cut_48895

theorem selected_cut_48896 : selected 9 ⟨1377231, by decide⟩
    (prefixPartial 12 404273) = some ⟨12, 2, 0, 1377231, 404273, 1937, 65536⟩ := by
  decide +kernel

theorem context_12_404273_1377231 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 404273 ⟨1377231, by decide⟩ :=
  accepted_of_selected 12 404273 ⟨1377231, by decide⟩ ⟨12, 2, 0, 1377231, 404273, 1937, 65536⟩
    (by decide) selected_cut_48896

theorem selected_cut_48897 : selected 9 ⟨1377283, by decide⟩
    (prefixPartial 12 404274) = some ⟨12, 2, 0, 1377283, 404274, 1669, 65536⟩ := by
  decide +kernel

theorem context_12_404274_1377283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 404274 ⟨1377283, by decide⟩ :=
  accepted_of_selected 12 404274 ⟨1377283, by decide⟩ ⟨12, 2, 0, 1377283, 404274, 1669, 65536⟩
    (by decide) selected_cut_48897

theorem selected_cut_48898 : selected 9 ⟨1377337, by decide⟩
    (prefixPartial 12 404275) = some ⟨12, 2, 0, 1377337, 404275, 1897, 65536⟩ := by
  decide +kernel

theorem context_12_404275_1377337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 404275 ⟨1377337, by decide⟩ :=
  accepted_of_selected 12 404275 ⟨1377337, by decide⟩ ⟨12, 2, 0, 1377337, 404275, 1897, 65536⟩
    (by decide) selected_cut_48898

theorem unmarked_context_11_101068_1377338 : frontier 10 ⟨1377338, by decide⟩
    (prefixCache 11 101068) (prefixPartial 11 101068) = false := by
  decide +kernel

theorem node_context_11_101068_1377338 : EJMOriginalGlobalDAGData.nodes 10 ⟨1377338, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1377231, by decide⟩,⟨1377283, by decide⟩,⟨1377337, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_101068_1377338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101068 ⟨1377338, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 101068
    ⟨1377338, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1377231, by decide⟩,⟨1377283, by decide⟩,⟨1377337, by decide⟩]) unmarked_context_11_101068_1377338 node_context_11_101068_1377338
  intro a
  fin_cases a
  · exact context_12_404272_1108174
  · exact context_12_404273_1377231
  · exact context_12_404274_1377283
  · exact context_12_404275_1377337

theorem selected_cut_48899 : selected 10 ⟨1377425, by decide⟩
    (prefixPartial 11 101069) = some ⟨11, 2, 0, 1377425, 101069, 3025, 262144⟩ := by
  decide +kernel

theorem context_11_101069_1377425 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101069 ⟨1377425, by decide⟩ :=
  accepted_of_selected 11 101069 ⟨1377425, by decide⟩ ⟨11, 2, 0, 1377425, 101069, 3025, 262144⟩
    (by decide) selected_cut_48899

theorem selected_cut_48900 : selected 10 ⟨1377487, by decide⟩
    (prefixPartial 11 101070) = some ⟨11, 2, 0, 1377487, 101070, 865, 262144⟩ := by
  decide +kernel

theorem context_11_101070_1377487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101070 ⟨1377487, by decide⟩ :=
  accepted_of_selected 11 101070 ⟨1377487, by decide⟩ ⟨11, 2, 0, 1377487, 101070, 865, 262144⟩
    (by decide) selected_cut_48900

theorem selected_cut_48901 : selected 10 ⟨1377520, by decide⟩
    (prefixPartial 11 101071) = some ⟨11, 2, 0, 1377520, 101071, 1261, 262144⟩ := by
  decide +kernel

theorem context_11_101071_1377520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101071 ⟨1377520, by decide⟩ :=
  accepted_of_selected 11 101071 ⟨1377520, by decide⟩ ⟨11, 2, 0, 1377520, 101071, 1261, 262144⟩
    (by decide) selected_cut_48901

theorem unmarked_context_10_25267_1377521 : frontier 11 ⟨1377521, by decide⟩
    (prefixCache 10 25267) (prefixPartial 10 25267) = false := by
  decide +kernel

theorem node_context_10_25267_1377521 : EJMOriginalGlobalDAGData.nodes 11 ⟨1377521, by decide⟩ =
    .split (coordinate 10) (![⟨1377338, by decide⟩,⟨1377425, by decide⟩,⟨1377487, by decide⟩,⟨1377520, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25267_1377521 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25267 ⟨1377521, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25267
    ⟨1377521, by decide⟩ (by decide) (![⟨1377338, by decide⟩,⟨1377425, by decide⟩,⟨1377487, by decide⟩,⟨1377520, by decide⟩]) unmarked_context_10_25267_1377521 node_context_10_25267_1377521
  intro a
  fin_cases a
  · exact context_11_101068_1377338
  · exact context_11_101069_1377425
  · exact context_11_101070_1377487
  · exact context_11_101071_1377520

theorem unmarked_context_9_6316_1377522 : frontier 12 ⟨1377522, by decide⟩
    (prefixCache 9 6316) (prefixPartial 9 6316) = false := by
  decide +kernel

theorem node_context_9_6316_1377522 : EJMOriginalGlobalDAGData.nodes 12 ⟨1377522, by decide⟩ =
    .split (coordinate 9) (![⟨1376271, by decide⟩,⟨1376834, by decide⟩,⟨1377156, by decide⟩,⟨1377521, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6316_1377522 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6316 ⟨1377522, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6316
    ⟨1377522, by decide⟩ (by decide) (![⟨1376271, by decide⟩,⟨1376834, by decide⟩,⟨1377156, by decide⟩,⟨1377521, by decide⟩]) unmarked_context_9_6316_1377522 node_context_9_6316_1377522
  intro a
  fin_cases a
  · exact context_10_25264_1376271
  · exact context_10_25265_1376834
  · exact context_10_25266_1377156
  · exact context_10_25267_1377521

theorem selected_cut_48902 : selected 10 ⟨1377641, by decide⟩
    (prefixPartial 11 101072) = some ⟨11, 2, 0, 1377641, 101072, 1453, 262144⟩ := by
  decide +kernel

theorem context_11_101072_1377641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101072 ⟨1377641, by decide⟩ :=
  accepted_of_selected 11 101072 ⟨1377641, by decide⟩ ⟨11, 2, 0, 1377641, 101072, 1453, 262144⟩
    (by decide) selected_cut_48902

theorem selected_cut_48903 : selected 10 ⟨1377800, by decide⟩
    (prefixPartial 11 101073) = some ⟨11, 2, 0, 1377800, 101073, 3409, 262144⟩ := by
  decide +kernel

theorem context_11_101073_1377800 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101073 ⟨1377800, by decide⟩ :=
  accepted_of_selected 11 101073 ⟨1377800, by decide⟩ ⟨11, 2, 0, 1377800, 101073, 3409, 262144⟩
    (by decide) selected_cut_48903

theorem selected_cut_48904 : selected 10 ⟨1377801, by decide⟩
    (prefixPartial 11 101074) = some ⟨11, 1, 0, 1377801, 101074, 1, 262144⟩ := by
  decide +kernel

theorem context_11_101074_1377801 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101074 ⟨1377801, by decide⟩ :=
  accepted_of_selected 11 101074 ⟨1377801, by decide⟩ ⟨11, 1, 0, 1377801, 101074, 1, 262144⟩
    (by decide) selected_cut_48904

theorem selected_cut_48905 : selected 10 ⟨1377877, by decide⟩
    (prefixPartial 11 101075) = some ⟨11, 2, 0, 1377877, 101075, 1569, 262144⟩ := by
  decide +kernel

theorem context_11_101075_1377877 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101075 ⟨1377877, by decide⟩ :=
  accepted_of_selected 11 101075 ⟨1377877, by decide⟩ ⟨11, 2, 0, 1377877, 101075, 1569, 262144⟩
    (by decide) selected_cut_48905

theorem unmarked_context_10_25268_1377878 : frontier 11 ⟨1377878, by decide⟩
    (prefixCache 10 25268) (prefixPartial 10 25268) = false := by
  decide +kernel

theorem node_context_10_25268_1377878 : EJMOriginalGlobalDAGData.nodes 11 ⟨1377878, by decide⟩ =
    .split (coordinate 10) (![⟨1377641, by decide⟩,⟨1377800, by decide⟩,⟨1377801, by decide⟩,⟨1377877, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25268_1377878 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25268 ⟨1377878, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25268
    ⟨1377878, by decide⟩ (by decide) (![⟨1377641, by decide⟩,⟨1377800, by decide⟩,⟨1377801, by decide⟩,⟨1377877, by decide⟩]) unmarked_context_10_25268_1377878 node_context_10_25268_1377878
  intro a
  fin_cases a
  · exact context_11_101072_1377641
  · exact context_11_101073_1377800
  · exact context_11_101074_1377801
  · exact context_11_101075_1377877

theorem selected_cut_48906 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 25269) = some ⟨10, 1, 0, 893098, 25269, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_25269_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25269 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 25269 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 25269, 1, 1048576⟩
    (by decide) selected_cut_48906

theorem selected_cut_48907 : selected 10 ⟨1377989, by decide⟩
    (prefixPartial 11 101080) = some ⟨11, 2, 0, 1377989, 101080, 2609, 262144⟩ := by
  decide +kernel

theorem context_11_101080_1377989 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101080 ⟨1377989, by decide⟩ :=
  accepted_of_selected 11 101080 ⟨1377989, by decide⟩ ⟨11, 2, 0, 1377989, 101080, 2609, 262144⟩
    (by decide) selected_cut_48907

theorem selected_cut_48908 : selected 10 ⟨1378063, by decide⟩
    (prefixPartial 11 101081) = some ⟨11, 2, 0, 1378063, 101081, 2189, 262144⟩ := by
  decide +kernel

theorem context_11_101081_1378063 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101081 ⟨1378063, by decide⟩ :=
  accepted_of_selected 11 101081 ⟨1378063, by decide⟩ ⟨11, 2, 0, 1378063, 101081, 2189, 262144⟩
    (by decide) selected_cut_48908

theorem selected_cut_48909 : selected 10 ⟨1377801, by decide⟩
    (prefixPartial 11 101082) = some ⟨11, 1, 0, 1377801, 101082, 1, 262144⟩ := by
  decide +kernel

theorem context_11_101082_1377801 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101082 ⟨1377801, by decide⟩ :=
  accepted_of_selected 11 101082 ⟨1377801, by decide⟩ ⟨11, 1, 0, 1377801, 101082, 1, 262144⟩
    (by decide) selected_cut_48909

theorem selected_cut_48910 : selected 10 ⟨1378098, by decide⟩
    (prefixPartial 11 101083) = some ⟨11, 2, 0, 1378098, 101083, 1033, 262144⟩ := by
  decide +kernel

theorem context_11_101083_1378098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101083 ⟨1378098, by decide⟩ :=
  accepted_of_selected 11 101083 ⟨1378098, by decide⟩ ⟨11, 2, 0, 1378098, 101083, 1033, 262144⟩
    (by decide) selected_cut_48910

theorem unmarked_context_10_25270_1378099 : frontier 11 ⟨1378099, by decide⟩
    (prefixCache 10 25270) (prefixPartial 10 25270) = false := by
  decide +kernel

theorem node_context_10_25270_1378099 : EJMOriginalGlobalDAGData.nodes 11 ⟨1378099, by decide⟩ =
    .split (coordinate 10) (![⟨1377989, by decide⟩,⟨1378063, by decide⟩,⟨1377801, by decide⟩,⟨1378098, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25270_1378099 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25270 ⟨1378099, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25270
    ⟨1378099, by decide⟩ (by decide) (![⟨1377989, by decide⟩,⟨1378063, by decide⟩,⟨1377801, by decide⟩,⟨1378098, by decide⟩]) unmarked_context_10_25270_1378099 node_context_10_25270_1378099
  intro a
  fin_cases a
  · exact context_11_101080_1377989
  · exact context_11_101081_1378063
  · exact context_11_101082_1377801
  · exact context_11_101083_1378098

theorem selected_cut_48911 : selected 11 ⟨1378300, by decide⟩
    (prefixPartial 10 25271) = some ⟨10, 2, 0, 1378300, 25271, 3769, 1048576⟩ := by
  decide +kernel

theorem context_10_25271_1378300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25271 ⟨1378300, by decide⟩ :=
  accepted_of_selected 10 25271 ⟨1378300, by decide⟩ ⟨10, 2, 0, 1378300, 25271, 3769, 1048576⟩
    (by decide) selected_cut_48911

theorem unmarked_context_9_6317_1378301 : frontier 12 ⟨1378301, by decide⟩
    (prefixCache 9 6317) (prefixPartial 9 6317) = false := by
  decide +kernel

theorem node_context_9_6317_1378301 : EJMOriginalGlobalDAGData.nodes 12 ⟨1378301, by decide⟩ =
    .split (coordinate 9) (![⟨1377878, by decide⟩,⟨893098, by decide⟩,⟨1378099, by decide⟩,⟨1378300, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6317_1378301 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6317 ⟨1378301, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6317
    ⟨1378301, by decide⟩ (by decide) (![⟨1377878, by decide⟩,⟨893098, by decide⟩,⟨1378099, by decide⟩,⟨1378300, by decide⟩]) unmarked_context_9_6317_1378301 node_context_9_6317_1378301
  intro a
  fin_cases a
  · exact context_10_25268_1377878
  · exact context_10_25269_893098
  · exact context_10_25270_1378099
  · exact context_10_25271_1378300

theorem selected_cut_48912 : selected 12 ⟨1378618, by decide⟩
    (prefixPartial 9 6318) = some ⟨9, 2, 0, 1378618, 6318, 3669, 4194304⟩ := by
  decide +kernel

theorem context_9_6318_1378618 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6318 ⟨1378618, by decide⟩ :=
  accepted_of_selected 9 6318 ⟨1378618, by decide⟩ ⟨9, 2, 0, 1378618, 6318, 3669, 4194304⟩
    (by decide) selected_cut_48912

theorem selected_cut_48913 : selected 12 ⟨1378651, by decide⟩
    (prefixPartial 9 6319) = some ⟨9, 2, 0, 1378651, 6319, 253, 4194304⟩ := by
  decide +kernel

theorem context_9_6319_1378651 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6319 ⟨1378651, by decide⟩ :=
  accepted_of_selected 9 6319 ⟨1378651, by decide⟩ ⟨9, 2, 0, 1378651, 6319, 253, 4194304⟩
    (by decide) selected_cut_48913

theorem unmarked_context_8_1579_1378652 : frontier 13 ⟨1378652, by decide⟩
    (prefixCache 8 1579) (prefixPartial 8 1579) = false := by
  decide +kernel

theorem node_context_8_1579_1378652 : EJMOriginalGlobalDAGData.nodes 13 ⟨1378652, by decide⟩ =
    .split (coordinate 8) (![⟨1377522, by decide⟩,⟨1378301, by decide⟩,⟨1378618, by decide⟩,⟨1378651, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1579_1378652 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1579 ⟨1378652, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1579
    ⟨1378652, by decide⟩ (by decide) (![⟨1377522, by decide⟩,⟨1378301, by decide⟩,⟨1378618, by decide⟩,⟨1378651, by decide⟩]) unmarked_context_8_1579_1378652 node_context_8_1579_1378652
  intro a
  fin_cases a
  · exact context_9_6316_1377522
  · exact context_9_6317_1378301
  · exact context_9_6318_1378618
  · exact context_9_6319_1378651

theorem unmarked_context_7_394_1378653 : frontier 14 ⟨1378653, by decide⟩
    (prefixCache 7 394) (prefixPartial 7 394) = false := by
  decide +kernel

theorem node_context_7_394_1378653 : EJMOriginalGlobalDAGData.nodes 14 ⟨1378653, by decide⟩ =
    .split (coordinate 7) (![⟨1364555, by decide⟩,⟨1376083, by decide⟩,⟨1366235, by decide⟩,⟨1378652, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_394_1378653 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 394 ⟨1378653, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 394
    ⟨1378653, by decide⟩ (by decide) (![⟨1364555, by decide⟩,⟨1376083, by decide⟩,⟨1366235, by decide⟩,⟨1378652, by decide⟩]) unmarked_context_7_394_1378653 node_context_7_394_1378653
  intro a
  fin_cases a
  · exact context_8_1576_1364555
  · exact context_8_1577_1376083
  · exact context_8_1578_1366235
  · exact context_8_1579_1378652

theorem selected_cut_48914 : selected 13 ⟨1364555, by decide⟩
    (prefixPartial 8 1580) = some ⟨8, 1, 0, 1364555, 1580, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_1580_1364555 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1580 ⟨1364555, by decide⟩ :=
  accepted_of_selected 8 1580 ⟨1364555, by decide⟩ ⟨8, 1, 0, 1364555, 1580, 1, 16777216⟩
    (by decide) selected_cut_48914

theorem selected_cut_48915 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 101184) = some ⟨11, 1, 0, 434745, 101184, 1, 262144⟩ := by
  decide +kernel

theorem context_11_101184_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101184 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 101184 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 101184, 1, 262144⟩
    (by decide) selected_cut_48915

theorem selected_cut_48916 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 101185) = some ⟨11, 1, 0, 434745, 101185, 1, 262144⟩ := by
  decide +kernel

theorem context_11_101185_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101185 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 101185 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 101185, 1, 262144⟩
    (by decide) selected_cut_48916

theorem selected_cut_48917 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 404744) = some ⟨12, 1, 0, 448748, 404744, 1, 65536⟩ := by
  decide +kernel

theorem context_12_404744_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 404744 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 404744 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 404744, 1, 65536⟩
    (by decide) selected_cut_48917

theorem selected_cut_48918 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 404745) = some ⟨12, 1, 0, 448748, 404745, 1, 65536⟩ := by
  decide +kernel

theorem context_12_404745_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 404745 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 404745 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 404745, 1, 65536⟩
    (by decide) selected_cut_48918

theorem selected_cut_48919 : selected 9 ⟨1378748, by decide⟩
    (prefixPartial 12 404746) = some ⟨12, 2, 0, 1378748, 404746, 2061, 65536⟩ := by
  decide +kernel

theorem context_12_404746_1378748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 404746 ⟨1378748, by decide⟩ :=
  accepted_of_selected 12 404746 ⟨1378748, by decide⟩ ⟨12, 2, 0, 1378748, 404746, 2061, 65536⟩
    (by decide) selected_cut_48919

theorem selected_cut_48920 : selected 9 ⟨1378820, by decide⟩
    (prefixPartial 12 404747) = some ⟨12, 2, 0, 1378820, 404747, 2217, 65536⟩ := by
  decide +kernel

theorem context_12_404747_1378820 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 404747 ⟨1378820, by decide⟩ :=
  accepted_of_selected 12 404747 ⟨1378820, by decide⟩ ⟨12, 2, 0, 1378820, 404747, 2217, 65536⟩
    (by decide) selected_cut_48920

theorem unmarked_context_11_101186_1378821 : frontier 10 ⟨1378821, by decide⟩
    (prefixCache 11 101186) (prefixPartial 11 101186) = false := by
  decide +kernel

theorem node_context_11_101186_1378821 : EJMOriginalGlobalDAGData.nodes 10 ⟨1378821, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨448748, by decide⟩,⟨1378748, by decide⟩,⟨1378820, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_101186_1378821 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101186 ⟨1378821, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 101186
    ⟨1378821, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨448748, by decide⟩,⟨1378748, by decide⟩,⟨1378820, by decide⟩]) unmarked_context_11_101186_1378821 node_context_11_101186_1378821
  intro a
  fin_cases a
  · exact context_12_404744_448748
  · exact context_12_404745_448748
  · exact context_12_404746_1378748
  · exact context_12_404747_1378820

theorem selected_cut_48921 : selected 10 ⟨1378875, by decide⟩
    (prefixPartial 11 101187) = some ⟨11, 2, 0, 1378875, 101187, 1993, 262144⟩ := by
  decide +kernel

theorem context_11_101187_1378875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101187 ⟨1378875, by decide⟩ :=
  accepted_of_selected 11 101187 ⟨1378875, by decide⟩ ⟨11, 2, 0, 1378875, 101187, 1993, 262144⟩
    (by decide) selected_cut_48921

theorem unmarked_context_10_25296_1378876 : frontier 11 ⟨1378876, by decide⟩
    (prefixCache 10 25296) (prefixPartial 10 25296) = false := by
  decide +kernel

theorem node_context_10_25296_1378876 : EJMOriginalGlobalDAGData.nodes 11 ⟨1378876, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨434745, by decide⟩,⟨1378821, by decide⟩,⟨1378875, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25296_1378876 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25296 ⟨1378876, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25296
    ⟨1378876, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨434745, by decide⟩,⟨1378821, by decide⟩,⟨1378875, by decide⟩]) unmarked_context_10_25296_1378876 node_context_10_25296_1378876
  intro a
  fin_cases a
  · exact context_11_101184_434745
  · exact context_11_101185_434745
  · exact context_11_101186_1378821
  · exact context_11_101187_1378875

theorem selected_cut_48922 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 404752) = some ⟨12, 1, 0, 1108174, 404752, 1, 65536⟩ := by
  decide +kernel

theorem context_12_404752_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 404752 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 404752 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 404752, 1, 65536⟩
    (by decide) selected_cut_48922

theorem selected_cut_48923 : selected 9 ⟨1378958, by decide⟩
    (prefixPartial 12 404753) = some ⟨12, 2, 0, 1378958, 404753, 2441, 65536⟩ := by
  decide +kernel

theorem context_12_404753_1378958 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 404753 ⟨1378958, by decide⟩ :=
  accepted_of_selected 12 404753 ⟨1378958, by decide⟩ ⟨12, 2, 0, 1378958, 404753, 2441, 65536⟩
    (by decide) selected_cut_48923

theorem selected_cut_48924 : selected 9 ⟨1379028, by decide⟩
    (prefixPartial 12 404754) = some ⟨12, 2, 0, 1379028, 404754, 2297, 65536⟩ := by
  decide +kernel

theorem context_12_404754_1379028 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 404754 ⟨1379028, by decide⟩ :=
  accepted_of_selected 12 404754 ⟨1379028, by decide⟩ ⟨12, 2, 0, 1379028, 404754, 2297, 65536⟩
    (by decide) selected_cut_48924

theorem selected_cut_48925 : selected 9 ⟨1379099, by decide⟩
    (prefixPartial 12 404755) = some ⟨12, 2, 0, 1379099, 404755, 2413, 65536⟩ := by
  decide +kernel

theorem context_12_404755_1379099 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 404755 ⟨1379099, by decide⟩ :=
  accepted_of_selected 12 404755 ⟨1379099, by decide⟩ ⟨12, 2, 0, 1379099, 404755, 2413, 65536⟩
    (by decide) selected_cut_48925

theorem unmarked_context_11_101188_1379100 : frontier 10 ⟨1379100, by decide⟩
    (prefixCache 11 101188) (prefixPartial 11 101188) = false := by
  decide +kernel

theorem node_context_11_101188_1379100 : EJMOriginalGlobalDAGData.nodes 10 ⟨1379100, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1378958, by decide⟩,⟨1379028, by decide⟩,⟨1379099, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_101188_1379100 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101188 ⟨1379100, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 101188
    ⟨1379100, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1378958, by decide⟩,⟨1379028, by decide⟩,⟨1379099, by decide⟩]) unmarked_context_11_101188_1379100 node_context_11_101188_1379100
  intro a
  fin_cases a
  · exact context_12_404752_1108174
  · exact context_12_404753_1378958
  · exact context_12_404754_1379028
  · exact context_12_404755_1379099

theorem selected_cut_48926 : selected 10 ⟨1379165, by decide⟩
    (prefixPartial 11 101189) = some ⟨11, 2, 0, 1379165, 101189, 2221, 262144⟩ := by
  decide +kernel

theorem context_11_101189_1379165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101189 ⟨1379165, by decide⟩ :=
  accepted_of_selected 11 101189 ⟨1379165, by decide⟩ ⟨11, 2, 0, 1379165, 101189, 2221, 262144⟩
    (by decide) selected_cut_48926

theorem selected_cut_48927 : selected 10 ⟨1379262, by decide⟩
    (prefixPartial 11 101190) = some ⟨11, 2, 0, 1379262, 101190, 4005, 262144⟩ := by
  decide +kernel

theorem context_11_101190_1379262 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101190 ⟨1379262, by decide⟩ :=
  accepted_of_selected 11 101190 ⟨1379262, by decide⟩ ⟨11, 2, 0, 1379262, 101190, 4005, 262144⟩
    (by decide) selected_cut_48927

theorem selected_cut_48928 : selected 10 ⟨1379349, by decide⟩
    (prefixPartial 11 101191) = some ⟨11, 2, 0, 1379349, 101191, 3673, 262144⟩ := by
  decide +kernel

theorem context_11_101191_1379349 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101191 ⟨1379349, by decide⟩ :=
  accepted_of_selected 11 101191 ⟨1379349, by decide⟩ ⟨11, 2, 0, 1379349, 101191, 3673, 262144⟩
    (by decide) selected_cut_48928

theorem unmarked_context_10_25297_1379350 : frontier 11 ⟨1379350, by decide⟩
    (prefixCache 10 25297) (prefixPartial 10 25297) = false := by
  decide +kernel

theorem node_context_10_25297_1379350 : EJMOriginalGlobalDAGData.nodes 11 ⟨1379350, by decide⟩ =
    .split (coordinate 10) (![⟨1379100, by decide⟩,⟨1379165, by decide⟩,⟨1379262, by decide⟩,⟨1379349, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25297_1379350 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25297 ⟨1379350, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25297
    ⟨1379350, by decide⟩ (by decide) (![⟨1379100, by decide⟩,⟨1379165, by decide⟩,⟨1379262, by decide⟩,⟨1379349, by decide⟩]) unmarked_context_10_25297_1379350 node_context_10_25297_1379350
  intro a
  fin_cases a
  · exact context_11_101188_1379100
  · exact context_11_101189_1379165
  · exact context_11_101190_1379262
  · exact context_11_101191_1379349

theorem selected_cut_48929 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 404768) = some ⟨12, 1, 0, 1108174, 404768, 1, 65536⟩ := by
  decide +kernel

theorem context_12_404768_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 404768 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 404768 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 404768, 1, 65536⟩
    (by decide) selected_cut_48929

theorem selected_cut_48930 : selected 9 ⟨1379437, by decide⟩
    (prefixPartial 12 404769) = some ⟨12, 2, 0, 1379437, 404769, 2313, 65536⟩ := by
  decide +kernel

theorem context_12_404769_1379437 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 404769 ⟨1379437, by decide⟩ :=
  accepted_of_selected 12 404769 ⟨1379437, by decide⟩ ⟨12, 2, 0, 1379437, 404769, 2313, 65536⟩
    (by decide) selected_cut_48930

theorem selected_cut_48931 : selected 9 ⟨1379488, by decide⟩
    (prefixPartial 12 404770) = some ⟨12, 2, 0, 1379488, 404770, 1981, 65536⟩ := by
  decide +kernel

theorem context_12_404770_1379488 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 404770 ⟨1379488, by decide⟩ :=
  accepted_of_selected 12 404770 ⟨1379488, by decide⟩ ⟨12, 2, 0, 1379488, 404770, 1981, 65536⟩
    (by decide) selected_cut_48931

theorem selected_cut_48932 : selected 9 ⟨1379541, by decide⟩
    (prefixPartial 12 404771) = some ⟨12, 2, 0, 1379541, 404771, 2077, 65536⟩ := by
  decide +kernel

theorem context_12_404771_1379541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 404771 ⟨1379541, by decide⟩ :=
  accepted_of_selected 12 404771 ⟨1379541, by decide⟩ ⟨12, 2, 0, 1379541, 404771, 2077, 65536⟩
    (by decide) selected_cut_48932

theorem unmarked_context_11_101192_1379542 : frontier 10 ⟨1379542, by decide⟩
    (prefixCache 11 101192) (prefixPartial 11 101192) = false := by
  decide +kernel

theorem node_context_11_101192_1379542 : EJMOriginalGlobalDAGData.nodes 10 ⟨1379542, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1379437, by decide⟩,⟨1379488, by decide⟩,⟨1379541, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_101192_1379542 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101192 ⟨1379542, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 101192
    ⟨1379542, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1379437, by decide⟩,⟨1379488, by decide⟩,⟨1379541, by decide⟩]) unmarked_context_11_101192_1379542 node_context_11_101192_1379542
  intro a
  fin_cases a
  · exact context_12_404768_1108174
  · exact context_12_404769_1379437
  · exact context_12_404770_1379488
  · exact context_12_404771_1379541

theorem selected_cut_48933 : selected 10 ⟨1379643, by decide⟩
    (prefixPartial 11 101193) = some ⟨11, 2, 0, 1379643, 101193, 3877, 262144⟩ := by
  decide +kernel

theorem context_11_101193_1379643 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101193 ⟨1379643, by decide⟩ :=
  accepted_of_selected 11 101193 ⟨1379643, by decide⟩ ⟨11, 2, 0, 1379643, 101193, 3877, 262144⟩
    (by decide) selected_cut_48933

theorem selected_cut_48934 : selected 10 ⟨1379698, by decide⟩
    (prefixPartial 11 101194) = some ⟨11, 2, 0, 1379698, 101194, 1801, 262144⟩ := by
  decide +kernel

theorem context_11_101194_1379698 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101194 ⟨1379698, by decide⟩ :=
  accepted_of_selected 11 101194 ⟨1379698, by decide⟩ ⟨11, 2, 0, 1379698, 101194, 1801, 262144⟩
    (by decide) selected_cut_48934

theorem selected_cut_48935 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 404780) = some ⟨12, 1, 0, 1108174, 404780, 1, 65536⟩ := by
  decide +kernel

theorem context_12_404780_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 404780 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 404780 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 404780, 1, 65536⟩
    (by decide) selected_cut_48935

theorem selected_cut_48936 : selected 9 ⟨1379738, by decide⟩
    (prefixPartial 12 404781) = some ⟨12, 2, 0, 1379738, 404781, 1617, 65536⟩ := by
  decide +kernel

theorem context_12_404781_1379738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 404781 ⟨1379738, by decide⟩ :=
  accepted_of_selected 12 404781 ⟨1379738, by decide⟩ ⟨12, 2, 0, 1379738, 404781, 1617, 65536⟩
    (by decide) selected_cut_48936

theorem selected_cut_48937 : selected 9 ⟨1379769, by decide⟩
    (prefixPartial 12 404782) = some ⟨12, 2, 0, 1379769, 404782, 1457, 65536⟩ := by
  decide +kernel

theorem context_12_404782_1379769 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 404782 ⟨1379769, by decide⟩ :=
  accepted_of_selected 12 404782 ⟨1379769, by decide⟩ ⟨12, 2, 0, 1379769, 404782, 1457, 65536⟩
    (by decide) selected_cut_48937

theorem selected_cut_48938 : selected 9 ⟨1379802, by decide⟩
    (prefixPartial 12 404783) = some ⟨12, 2, 0, 1379802, 404783, 1589, 65536⟩ := by
  decide +kernel

theorem context_12_404783_1379802 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 404783 ⟨1379802, by decide⟩ :=
  accepted_of_selected 12 404783 ⟨1379802, by decide⟩ ⟨12, 2, 0, 1379802, 404783, 1589, 65536⟩
    (by decide) selected_cut_48938

theorem unmarked_context_11_101195_1379803 : frontier 10 ⟨1379803, by decide⟩
    (prefixCache 11 101195) (prefixPartial 11 101195) = false := by
  decide +kernel

theorem node_context_11_101195_1379803 : EJMOriginalGlobalDAGData.nodes 10 ⟨1379803, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1379738, by decide⟩,⟨1379769, by decide⟩,⟨1379802, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_101195_1379803 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101195 ⟨1379803, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 101195
    ⟨1379803, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1379738, by decide⟩,⟨1379769, by decide⟩,⟨1379802, by decide⟩]) unmarked_context_11_101195_1379803 node_context_11_101195_1379803
  intro a
  fin_cases a
  · exact context_12_404780_1108174
  · exact context_12_404781_1379738
  · exact context_12_404782_1379769
  · exact context_12_404783_1379802

theorem unmarked_context_10_25298_1379804 : frontier 11 ⟨1379804, by decide⟩
    (prefixCache 10 25298) (prefixPartial 10 25298) = false := by
  decide +kernel

theorem node_context_10_25298_1379804 : EJMOriginalGlobalDAGData.nodes 11 ⟨1379804, by decide⟩ =
    .split (coordinate 10) (![⟨1379542, by decide⟩,⟨1379643, by decide⟩,⟨1379698, by decide⟩,⟨1379803, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25298_1379804 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25298 ⟨1379804, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25298
    ⟨1379804, by decide⟩ (by decide) (![⟨1379542, by decide⟩,⟨1379643, by decide⟩,⟨1379698, by decide⟩,⟨1379803, by decide⟩]) unmarked_context_10_25298_1379804 node_context_10_25298_1379804
  intro a
  fin_cases a
  · exact context_11_101192_1379542
  · exact context_11_101193_1379643
  · exact context_11_101194_1379698
  · exact context_11_101195_1379803

theorem selected_cut_48939 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 404784) = some ⟨12, 1, 0, 1108174, 404784, 1, 65536⟩ := by
  decide +kernel

theorem context_12_404784_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 404784 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 404784 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 404784, 1, 65536⟩
    (by decide) selected_cut_48939

theorem selected_cut_48940 : selected 9 ⟨1379858, by decide⟩
    (prefixPartial 12 404785) = some ⟨12, 2, 0, 1379858, 404785, 1881, 65536⟩ := by
  decide +kernel

theorem context_12_404785_1379858 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 404785 ⟨1379858, by decide⟩ :=
  accepted_of_selected 12 404785 ⟨1379858, by decide⟩ ⟨12, 2, 0, 1379858, 404785, 1881, 65536⟩
    (by decide) selected_cut_48940

theorem selected_cut_48941 : selected 9 ⟨1379892, by decide⟩
    (prefixPartial 12 404786) = some ⟨12, 2, 0, 1379892, 404786, 1629, 65536⟩ := by
  decide +kernel

theorem context_12_404786_1379892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 404786 ⟨1379892, by decide⟩ :=
  accepted_of_selected 12 404786 ⟨1379892, by decide⟩ ⟨12, 2, 0, 1379892, 404786, 1629, 65536⟩
    (by decide) selected_cut_48941

theorem selected_cut_48942 : selected 9 ⟨1379954, by decide⟩
    (prefixPartial 12 404787) = some ⟨12, 2, 0, 1379954, 404787, 1993, 65536⟩ := by
  decide +kernel

theorem context_12_404787_1379954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 404787 ⟨1379954, by decide⟩ :=
  accepted_of_selected 12 404787 ⟨1379954, by decide⟩ ⟨12, 2, 0, 1379954, 404787, 1993, 65536⟩
    (by decide) selected_cut_48942

theorem unmarked_context_11_101196_1379955 : frontier 10 ⟨1379955, by decide⟩
    (prefixCache 11 101196) (prefixPartial 11 101196) = false := by
  decide +kernel

theorem node_context_11_101196_1379955 : EJMOriginalGlobalDAGData.nodes 10 ⟨1379955, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1379858, by decide⟩,⟨1379892, by decide⟩,⟨1379954, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_101196_1379955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101196 ⟨1379955, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 101196
    ⟨1379955, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1379858, by decide⟩,⟨1379892, by decide⟩,⟨1379954, by decide⟩]) unmarked_context_11_101196_1379955 node_context_11_101196_1379955
  intro a
  fin_cases a
  · exact context_12_404784_1108174
  · exact context_12_404785_1379858
  · exact context_12_404786_1379892
  · exact context_12_404787_1379954

theorem selected_cut_48943 : selected 10 ⟨1380028, by decide⟩
    (prefixPartial 11 101197) = some ⟨11, 2, 0, 1380028, 101197, 3509, 262144⟩ := by
  decide +kernel

theorem context_11_101197_1380028 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101197 ⟨1380028, by decide⟩ :=
  accepted_of_selected 11 101197 ⟨1380028, by decide⟩ ⟨11, 2, 0, 1380028, 101197, 3509, 262144⟩
    (by decide) selected_cut_48943

theorem selected_cut_48944 : selected 10 ⟨1380112, by decide⟩
    (prefixPartial 11 101198) = some ⟨11, 2, 0, 1380112, 101198, 4017, 262144⟩ := by
  decide +kernel

theorem context_11_101198_1380112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101198 ⟨1380112, by decide⟩ :=
  accepted_of_selected 11 101198 ⟨1380112, by decide⟩ ⟨11, 2, 0, 1380112, 101198, 4017, 262144⟩
    (by decide) selected_cut_48944

theorem selected_cut_48945 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 101199) = some ⟨11, 1, 0, 977886, 101199, 1, 262144⟩ := by
  decide +kernel

theorem context_11_101199_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101199 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 101199 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 101199, 1, 262144⟩
    (by decide) selected_cut_48945

theorem unmarked_context_10_25299_1380113 : frontier 11 ⟨1380113, by decide⟩
    (prefixCache 10 25299) (prefixPartial 10 25299) = false := by
  decide +kernel

theorem node_context_10_25299_1380113 : EJMOriginalGlobalDAGData.nodes 11 ⟨1380113, by decide⟩ =
    .split (coordinate 10) (![⟨1379955, by decide⟩,⟨1380028, by decide⟩,⟨1380112, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25299_1380113 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25299 ⟨1380113, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25299
    ⟨1380113, by decide⟩ (by decide) (![⟨1379955, by decide⟩,⟨1380028, by decide⟩,⟨1380112, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_25299_1380113 node_context_10_25299_1380113
  intro a
  fin_cases a
  · exact context_11_101196_1379955
  · exact context_11_101197_1380028
  · exact context_11_101198_1380112
  · exact context_11_101199_977886

theorem unmarked_context_9_6324_1380114 : frontier 12 ⟨1380114, by decide⟩
    (prefixCache 9 6324) (prefixPartial 9 6324) = false := by
  decide +kernel

theorem node_context_9_6324_1380114 : EJMOriginalGlobalDAGData.nodes 12 ⟨1380114, by decide⟩ =
    .split (coordinate 9) (![⟨1378876, by decide⟩,⟨1379350, by decide⟩,⟨1379804, by decide⟩,⟨1380113, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6324_1380114 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6324 ⟨1380114, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6324
    ⟨1380114, by decide⟩ (by decide) (![⟨1378876, by decide⟩,⟨1379350, by decide⟩,⟨1379804, by decide⟩,⟨1380113, by decide⟩]) unmarked_context_9_6324_1380114 node_context_9_6324_1380114
  intro a
  fin_cases a
  · exact context_10_25296_1378876
  · exact context_10_25297_1379350
  · exact context_10_25298_1379804
  · exact context_10_25299_1380113

theorem selected_cut_48946 : selected 10 ⟨1380153, by decide⟩
    (prefixPartial 11 101200) = some ⟨11, 2, 0, 1380153, 101200, 1589, 262144⟩ := by
  decide +kernel

theorem context_11_101200_1380153 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101200 ⟨1380153, by decide⟩ :=
  accepted_of_selected 11 101200 ⟨1380153, by decide⟩ ⟨11, 2, 0, 1380153, 101200, 1589, 262144⟩
    (by decide) selected_cut_48946

theorem selected_cut_48947 : selected 9 ⟨1380176, by decide⟩
    (prefixPartial 12 404804) = some ⟨12, 2, 0, 1380176, 404804, 1333, 65536⟩ := by
  decide +kernel

theorem context_12_404804_1380176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 404804 ⟨1380176, by decide⟩ :=
  accepted_of_selected 12 404804 ⟨1380176, by decide⟩ ⟨12, 2, 0, 1380176, 404804, 1333, 65536⟩
    (by decide) selected_cut_48947

theorem selected_cut_48948 : selected 9 ⟨642341, by decide⟩
    (prefixPartial 12 404805) = some ⟨12, 1, 0, 642341, 404805, 1, 65536⟩ := by
  decide +kernel

theorem context_12_404805_642341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 404805 ⟨642341, by decide⟩ :=
  accepted_of_selected 12 404805 ⟨642341, by decide⟩ ⟨12, 1, 0, 642341, 404805, 1, 65536⟩
    (by decide) selected_cut_48948

theorem selected_cut_48949 : selected 9 ⟨1380203, by decide⟩
    (prefixPartial 12 404806) = some ⟨12, 2, 0, 1380203, 404806, 1453, 65536⟩ := by
  decide +kernel

theorem context_12_404806_1380203 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 404806 ⟨1380203, by decide⟩ :=
  accepted_of_selected 12 404806 ⟨1380203, by decide⟩ ⟨12, 2, 0, 1380203, 404806, 1453, 65536⟩
    (by decide) selected_cut_48949

theorem selected_cut_48950 : selected 9 ⟨1380228, by decide⟩
    (prefixPartial 12 404807) = some ⟨12, 2, 0, 1380228, 404807, 1465, 65536⟩ := by
  decide +kernel

theorem context_12_404807_1380228 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 404807 ⟨1380228, by decide⟩ :=
  accepted_of_selected 12 404807 ⟨1380228, by decide⟩ ⟨12, 2, 0, 1380228, 404807, 1465, 65536⟩
    (by decide) selected_cut_48950

theorem unmarked_context_11_101201_1380229 : frontier 10 ⟨1380229, by decide⟩
    (prefixCache 11 101201) (prefixPartial 11 101201) = false := by
  decide +kernel

theorem node_context_11_101201_1380229 : EJMOriginalGlobalDAGData.nodes 10 ⟨1380229, by decide⟩ =
    .split (coordinate 11) (![⟨1380176, by decide⟩,⟨642341, by decide⟩,⟨1380203, by decide⟩,⟨1380228, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_101201_1380229 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101201 ⟨1380229, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 101201
    ⟨1380229, by decide⟩ (by decide) (![⟨1380176, by decide⟩,⟨642341, by decide⟩,⟨1380203, by decide⟩,⟨1380228, by decide⟩]) unmarked_context_11_101201_1380229 node_context_11_101201_1380229
  intro a
  fin_cases a
  · exact context_12_404804_1380176
  · exact context_12_404805_642341
  · exact context_12_404806_1380203
  · exact context_12_404807_1380228

theorem selected_cut_48951 : selected 10 ⟨1380290, by decide⟩
    (prefixPartial 11 101202) = some ⟨11, 2, 0, 1380290, 101202, 2741, 262144⟩ := by
  decide +kernel

theorem context_11_101202_1380290 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101202 ⟨1380290, by decide⟩ :=
  accepted_of_selected 11 101202 ⟨1380290, by decide⟩ ⟨11, 2, 0, 1380290, 101202, 2741, 262144⟩
    (by decide) selected_cut_48951

theorem selected_cut_48952 : selected 10 ⟨1380334, by decide⟩
    (prefixPartial 11 101203) = some ⟨11, 2, 0, 1380334, 101203, 2277, 262144⟩ := by
  decide +kernel

theorem context_11_101203_1380334 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101203 ⟨1380334, by decide⟩ :=
  accepted_of_selected 11 101203 ⟨1380334, by decide⟩ ⟨11, 2, 0, 1380334, 101203, 2277, 262144⟩
    (by decide) selected_cut_48952

theorem unmarked_context_10_25300_1380335 : frontier 11 ⟨1380335, by decide⟩
    (prefixCache 10 25300) (prefixPartial 10 25300) = false := by
  decide +kernel

theorem node_context_10_25300_1380335 : EJMOriginalGlobalDAGData.nodes 11 ⟨1380335, by decide⟩ =
    .split (coordinate 10) (![⟨1380153, by decide⟩,⟨1380229, by decide⟩,⟨1380290, by decide⟩,⟨1380334, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25300_1380335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25300 ⟨1380335, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25300
    ⟨1380335, by decide⟩ (by decide) (![⟨1380153, by decide⟩,⟨1380229, by decide⟩,⟨1380290, by decide⟩,⟨1380334, by decide⟩]) unmarked_context_10_25300_1380335 node_context_10_25300_1380335
  intro a
  fin_cases a
  · exact context_11_101200_1380153
  · exact context_11_101201_1380229
  · exact context_11_101202_1380290
  · exact context_11_101203_1380334

theorem selected_cut_48953 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 25301) = some ⟨10, 1, 0, 893098, 25301, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_25301_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25301 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 25301 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 25301, 1, 1048576⟩
    (by decide) selected_cut_48953

theorem selected_cut_48954 : selected 10 ⟨1380404, by decide⟩
    (prefixPartial 11 101208) = some ⟨11, 2, 0, 1380404, 101208, 2769, 262144⟩ := by
  decide +kernel

theorem context_11_101208_1380404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101208 ⟨1380404, by decide⟩ :=
  accepted_of_selected 11 101208 ⟨1380404, by decide⟩ ⟨11, 2, 0, 1380404, 101208, 2769, 262144⟩
    (by decide) selected_cut_48954

theorem selected_cut_48955 : selected 10 ⟨1380495, by decide⟩
    (prefixPartial 11 101209) = some ⟨11, 2, 0, 1380495, 101209, 3733, 262144⟩ := by
  decide +kernel

theorem context_11_101209_1380495 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101209 ⟨1380495, by decide⟩ :=
  accepted_of_selected 11 101209 ⟨1380495, by decide⟩ ⟨11, 2, 0, 1380495, 101209, 3733, 262144⟩
    (by decide) selected_cut_48955

theorem selected_cut_48956 : selected 10 ⟨1380520, by decide⟩
    (prefixPartial 11 101210) = some ⟨11, 2, 0, 1380520, 101210, 1069, 262144⟩ := by
  decide +kernel

theorem context_11_101210_1380520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101210 ⟨1380520, by decide⟩ :=
  accepted_of_selected 11 101210 ⟨1380520, by decide⟩ ⟨11, 2, 0, 1380520, 101210, 1069, 262144⟩
    (by decide) selected_cut_48956

theorem selected_cut_48957 : selected 10 ⟨1380581, by decide⟩
    (prefixPartial 11 101211) = some ⟨11, 2, 0, 1380581, 101211, 2957, 262144⟩ := by
  decide +kernel

theorem context_11_101211_1380581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101211 ⟨1380581, by decide⟩ :=
  accepted_of_selected 11 101211 ⟨1380581, by decide⟩ ⟨11, 2, 0, 1380581, 101211, 2957, 262144⟩
    (by decide) selected_cut_48957

theorem unmarked_context_10_25302_1380582 : frontier 11 ⟨1380582, by decide⟩
    (prefixCache 10 25302) (prefixPartial 10 25302) = false := by
  decide +kernel

theorem node_context_10_25302_1380582 : EJMOriginalGlobalDAGData.nodes 11 ⟨1380582, by decide⟩ =
    .split (coordinate 10) (![⟨1380404, by decide⟩,⟨1380495, by decide⟩,⟨1380520, by decide⟩,⟨1380581, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25302_1380582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25302 ⟨1380582, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25302
    ⟨1380582, by decide⟩ (by decide) (![⟨1380404, by decide⟩,⟨1380495, by decide⟩,⟨1380520, by decide⟩,⟨1380581, by decide⟩]) unmarked_context_10_25302_1380582 node_context_10_25302_1380582
  intro a
  fin_cases a
  · exact context_11_101208_1380404
  · exact context_11_101209_1380495
  · exact context_11_101210_1380520
  · exact context_11_101211_1380581

theorem selected_cut_48958 : selected 10 ⟨1380655, by decide⟩
    (prefixPartial 11 101212) = some ⟨11, 2, 0, 1380655, 101212, 2717, 262144⟩ := by
  decide +kernel

theorem context_11_101212_1380655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101212 ⟨1380655, by decide⟩ :=
  accepted_of_selected 11 101212 ⟨1380655, by decide⟩ ⟨11, 2, 0, 1380655, 101212, 2717, 262144⟩
    (by decide) selected_cut_48958

theorem selected_cut_48959 : selected 10 ⟨1380731, by decide⟩
    (prefixPartial 11 101213) = some ⟨11, 2, 0, 1380731, 101213, 3373, 262144⟩ := by
  decide +kernel

theorem context_11_101213_1380731 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101213 ⟨1380731, by decide⟩ :=
  accepted_of_selected 11 101213 ⟨1380731, by decide⟩ ⟨11, 2, 0, 1380731, 101213, 3373, 262144⟩
    (by decide) selected_cut_48959

theorem selected_cut_48960 : selected 10 ⟨1380796, by decide⟩
    (prefixPartial 11 101214) = some ⟨11, 2, 0, 1380796, 101214, 2837, 262144⟩ := by
  decide +kernel

theorem context_11_101214_1380796 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101214 ⟨1380796, by decide⟩ :=
  accepted_of_selected 11 101214 ⟨1380796, by decide⟩ ⟨11, 2, 0, 1380796, 101214, 2837, 262144⟩
    (by decide) selected_cut_48960

theorem selected_cut_48961 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 101215) = some ⟨11, 1, 0, 977886, 101215, 1, 262144⟩ := by
  decide +kernel

theorem context_11_101215_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101215 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 101215 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 101215, 1, 262144⟩
    (by decide) selected_cut_48961

theorem unmarked_context_10_25303_1380797 : frontier 11 ⟨1380797, by decide⟩
    (prefixCache 10 25303) (prefixPartial 10 25303) = false := by
  decide +kernel

theorem node_context_10_25303_1380797 : EJMOriginalGlobalDAGData.nodes 11 ⟨1380797, by decide⟩ =
    .split (coordinate 10) (![⟨1380655, by decide⟩,⟨1380731, by decide⟩,⟨1380796, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25303_1380797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25303 ⟨1380797, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25303
    ⟨1380797, by decide⟩ (by decide) (![⟨1380655, by decide⟩,⟨1380731, by decide⟩,⟨1380796, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_25303_1380797 node_context_10_25303_1380797
  intro a
  fin_cases a
  · exact context_11_101212_1380655
  · exact context_11_101213_1380731
  · exact context_11_101214_1380796
  · exact context_11_101215_977886

theorem unmarked_context_9_6325_1380798 : frontier 12 ⟨1380798, by decide⟩
    (prefixCache 9 6325) (prefixPartial 9 6325) = false := by
  decide +kernel

theorem node_context_9_6325_1380798 : EJMOriginalGlobalDAGData.nodes 12 ⟨1380798, by decide⟩ =
    .split (coordinate 9) (![⟨1380335, by decide⟩,⟨893098, by decide⟩,⟨1380582, by decide⟩,⟨1380797, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6325_1380798 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6325 ⟨1380798, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6325
    ⟨1380798, by decide⟩ (by decide) (![⟨1380335, by decide⟩,⟨893098, by decide⟩,⟨1380582, by decide⟩,⟨1380797, by decide⟩]) unmarked_context_9_6325_1380798 node_context_9_6325_1380798
  intro a
  fin_cases a
  · exact context_10_25300_1380335
  · exact context_10_25301_893098
  · exact context_10_25302_1380582
  · exact context_10_25303_1380797

theorem selected_cut_48962 : selected 10 ⟨1380832, by decide⟩
    (prefixPartial 11 101216) = some ⟨11, 2, 0, 1380832, 101216, 1097, 262144⟩ := by
  decide +kernel

theorem context_11_101216_1380832 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101216 ⟨1380832, by decide⟩ :=
  accepted_of_selected 11 101216 ⟨1380832, by decide⟩ ⟨11, 2, 0, 1380832, 101216, 1097, 262144⟩
    (by decide) selected_cut_48962

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
