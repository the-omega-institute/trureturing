/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover166
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_16035 : selected 9 ⟨408409, by decide⟩
    (prefixPartial 12 28020) = some ⟨12, 2, 0, 408409, 28020, 3025, 65536⟩ := by
  decide +kernel

theorem context_12_28020_408409 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28020 ⟨408409, by decide⟩ :=
  accepted_of_selected 12 28020 ⟨408409, by decide⟩ ⟨12, 2, 0, 408409, 28020, 3025, 65536⟩
    (by decide) selected_cut_16035

theorem selected_cut_16036 : selected 9 ⟨126884, by decide⟩
    (prefixPartial 12 28021) = some ⟨12, 1, 0, 126884, 28021, 1, 65536⟩ := by
  decide +kernel

theorem context_12_28021_126884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28021 ⟨126884, by decide⟩ :=
  accepted_of_selected 12 28021 ⟨126884, by decide⟩ ⟨12, 1, 0, 126884, 28021, 1, 65536⟩
    (by decide) selected_cut_16036

theorem selected_cut_16037 : selected 9 ⟨408441, by decide⟩
    (prefixPartial 12 28022) = some ⟨12, 2, 0, 408441, 28022, 3425, 65536⟩ := by
  decide +kernel

theorem context_12_28022_408441 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28022 ⟨408441, by decide⟩ :=
  accepted_of_selected 12 28022 ⟨408441, by decide⟩ ⟨12, 2, 0, 408441, 28022, 3425, 65536⟩
    (by decide) selected_cut_16037

theorem selected_cut_16038 : selected 9 ⟨408478, by decide⟩
    (prefixPartial 12 28023) = some ⟨12, 2, 0, 408478, 28023, 3505, 65536⟩ := by
  decide +kernel

theorem context_12_28023_408478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28023 ⟨408478, by decide⟩ :=
  accepted_of_selected 12 28023 ⟨408478, by decide⟩ ⟨12, 2, 0, 408478, 28023, 3505, 65536⟩
    (by decide) selected_cut_16038

theorem unmarked_context_11_7005_408479 : frontier 10 ⟨408479, by decide⟩
    (prefixCache 11 7005) (prefixPartial 11 7005) = false := by
  decide +kernel

theorem node_context_11_7005_408479 : EJMOriginalGlobalDAGData.nodes 10 ⟨408479, by decide⟩ =
    .split (coordinate 11) (![⟨408409, by decide⟩,⟨126884, by decide⟩,⟨408441, by decide⟩,⟨408478, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7005_408479 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7005 ⟨408479, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7005
    ⟨408479, by decide⟩ (by decide) (![⟨408409, by decide⟩,⟨126884, by decide⟩,⟨408441, by decide⟩,⟨408478, by decide⟩]) unmarked_context_11_7005_408479 node_context_11_7005_408479
  intro a
  fin_cases a
  · exact context_12_28020_408409
  · exact context_12_28021_126884
  · exact context_12_28022_408441
  · exact context_12_28023_408478

theorem selected_cut_16039 : selected 9 ⟨408528, by decide⟩
    (prefixPartial 12 28024) = some ⟨12, 2, 0, 408528, 28024, 3489, 65536⟩ := by
  decide +kernel

theorem context_12_28024_408528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28024 ⟨408528, by decide⟩ :=
  accepted_of_selected 12 28024 ⟨408528, by decide⟩ ⟨12, 2, 0, 408528, 28024, 3489, 65536⟩
    (by decide) selected_cut_16039

theorem selected_cut_16040 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 112100) = some ⟨13, 1, 0, 3444, 112100, 1, 16384⟩ := by
  decide +kernel

theorem context_13_112100_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112100 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 112100 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 112100, 1, 16384⟩
    (by decide) selected_cut_16040

theorem selected_cut_16041 : selected 8 ⟨408545, by decide⟩
    (prefixPartial 13 112101) = some ⟨13, 2, 0, 408545, 112101, 585, 16384⟩ := by
  decide +kernel

theorem context_13_112101_408545 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112101 ⟨408545, by decide⟩ :=
  accepted_of_selected 13 112101 ⟨408545, by decide⟩ ⟨13, 2, 0, 408545, 112101, 585, 16384⟩
    (by decide) selected_cut_16041

theorem selected_cut_16042 : selected 8 ⟨408594, by decide⟩
    (prefixPartial 13 112102) = some ⟨13, 2, 0, 408594, 112102, 2889, 16384⟩ := by
  decide +kernel

theorem context_13_112102_408594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112102 ⟨408594, by decide⟩ :=
  accepted_of_selected 13 112102 ⟨408594, by decide⟩ ⟨13, 2, 0, 408594, 112102, 2889, 16384⟩
    (by decide) selected_cut_16042

theorem selected_cut_16043 : selected 8 ⟨408612, by decide⟩
    (prefixPartial 13 112103) = some ⟨13, 2, 0, 408612, 112103, 1181, 16384⟩ := by
  decide +kernel

theorem context_13_112103_408612 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112103 ⟨408612, by decide⟩ :=
  accepted_of_selected 13 112103 ⟨408612, by decide⟩ ⟨13, 2, 0, 408612, 112103, 1181, 16384⟩
    (by decide) selected_cut_16043

theorem unmarked_context_12_28025_408613 : frontier 9 ⟨408613, by decide⟩
    (prefixCache 12 28025) (prefixPartial 12 28025) = false := by
  decide +kernel

theorem node_context_12_28025_408613 : EJMOriginalGlobalDAGData.nodes 9 ⟨408613, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨408545, by decide⟩,⟨408594, by decide⟩,⟨408612, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28025_408613 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28025 ⟨408613, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28025
    ⟨408613, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨408545, by decide⟩,⟨408594, by decide⟩,⟨408612, by decide⟩]) unmarked_context_12_28025_408613 node_context_12_28025_408613
  intro a
  fin_cases a
  · exact context_13_112100_3444
  · exact context_13_112101_408545
  · exact context_13_112102_408594
  · exact context_13_112103_408612

theorem selected_cut_16044 : selected 9 ⟨408658, by decide⟩
    (prefixPartial 12 28026) = some ⟨12, 2, 0, 408658, 28026, 3573, 65536⟩ := by
  decide +kernel

theorem context_12_28026_408658 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28026 ⟨408658, by decide⟩ :=
  accepted_of_selected 12 28026 ⟨408658, by decide⟩ ⟨12, 2, 0, 408658, 28026, 3573, 65536⟩
    (by decide) selected_cut_16044

theorem selected_cut_16045 : selected 9 ⟨408707, by decide⟩
    (prefixPartial 12 28027) = some ⟨12, 2, 0, 408707, 28027, 3701, 65536⟩ := by
  decide +kernel

theorem context_12_28027_408707 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28027 ⟨408707, by decide⟩ :=
  accepted_of_selected 12 28027 ⟨408707, by decide⟩ ⟨12, 2, 0, 408707, 28027, 3701, 65536⟩
    (by decide) selected_cut_16045

theorem unmarked_context_11_7006_408708 : frontier 10 ⟨408708, by decide⟩
    (prefixCache 11 7006) (prefixPartial 11 7006) = false := by
  decide +kernel

theorem node_context_11_7006_408708 : EJMOriginalGlobalDAGData.nodes 10 ⟨408708, by decide⟩ =
    .split (coordinate 11) (![⟨408528, by decide⟩,⟨408613, by decide⟩,⟨408658, by decide⟩,⟨408707, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7006_408708 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7006 ⟨408708, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7006
    ⟨408708, by decide⟩ (by decide) (![⟨408528, by decide⟩,⟨408613, by decide⟩,⟨408658, by decide⟩,⟨408707, by decide⟩]) unmarked_context_11_7006_408708 node_context_11_7006_408708
  intro a
  fin_cases a
  · exact context_12_28024_408528
  · exact context_12_28025_408613
  · exact context_12_28026_408658
  · exact context_12_28027_408707

theorem selected_cut_16046 : selected 9 ⟨408765, by decide⟩
    (prefixPartial 12 28028) = some ⟨12, 2, 0, 408765, 28028, 3733, 65536⟩ := by
  decide +kernel

theorem context_12_28028_408765 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28028 ⟨408765, by decide⟩ :=
  accepted_of_selected 12 28028 ⟨408765, by decide⟩ ⟨12, 2, 0, 408765, 28028, 3733, 65536⟩
    (by decide) selected_cut_16046

theorem selected_cut_16047 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 112116) = some ⟨13, 1, 0, 3444, 112116, 1, 16384⟩ := by
  decide +kernel

theorem context_13_112116_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112116 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 112116 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 112116, 1, 16384⟩
    (by decide) selected_cut_16047

theorem selected_cut_16048 : selected 8 ⟨408773, by decide⟩
    (prefixPartial 13 112117) = some ⟨13, 2, 0, 408773, 112117, 261, 16384⟩ := by
  decide +kernel

theorem context_13_112117_408773 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112117 ⟨408773, by decide⟩ :=
  accepted_of_selected 13 112117 ⟨408773, by decide⟩ ⟨13, 2, 0, 408773, 112117, 261, 16384⟩
    (by decide) selected_cut_16048

theorem selected_cut_16049 : selected 8 ⟨408859, by decide⟩
    (prefixPartial 13 112118) = some ⟨13, 2, 0, 408859, 112118, 3613, 16384⟩ := by
  decide +kernel

theorem context_13_112118_408859 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112118 ⟨408859, by decide⟩ :=
  accepted_of_selected 13 112118 ⟨408859, by decide⟩ ⟨13, 2, 0, 408859, 112118, 3613, 16384⟩
    (by decide) selected_cut_16049

theorem selected_cut_16050 : selected 8 ⟨408884, by decide⟩
    (prefixPartial 13 112119) = some ⟨13, 2, 0, 408884, 112119, 1485, 16384⟩ := by
  decide +kernel

theorem context_13_112119_408884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112119 ⟨408884, by decide⟩ :=
  accepted_of_selected 13 112119 ⟨408884, by decide⟩ ⟨13, 2, 0, 408884, 112119, 1485, 16384⟩
    (by decide) selected_cut_16050

theorem unmarked_context_12_28029_408885 : frontier 9 ⟨408885, by decide⟩
    (prefixCache 12 28029) (prefixPartial 12 28029) = false := by
  decide +kernel

theorem node_context_12_28029_408885 : EJMOriginalGlobalDAGData.nodes 9 ⟨408885, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨408773, by decide⟩,⟨408859, by decide⟩,⟨408884, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28029_408885 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28029 ⟨408885, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28029
    ⟨408885, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨408773, by decide⟩,⟨408859, by decide⟩,⟨408884, by decide⟩]) unmarked_context_12_28029_408885 node_context_12_28029_408885
  intro a
  fin_cases a
  · exact context_13_112116_3444
  · exact context_13_112117_408773
  · exact context_13_112118_408859
  · exact context_13_112119_408884

theorem selected_cut_16051 : selected 9 ⟨408929, by decide⟩
    (prefixPartial 12 28030) = some ⟨12, 2, 0, 408929, 28030, 3805, 65536⟩ := by
  decide +kernel

theorem context_12_28030_408929 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28030 ⟨408929, by decide⟩ :=
  accepted_of_selected 12 28030 ⟨408929, by decide⟩ ⟨12, 2, 0, 408929, 28030, 3805, 65536⟩
    (by decide) selected_cut_16051

theorem selected_cut_16052 : selected 9 ⟨408930, by decide⟩
    (prefixPartial 12 28031) = some ⟨12, 1, 0, 408930, 28031, 1, 65536⟩ := by
  decide +kernel

theorem context_12_28031_408930 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28031 ⟨408930, by decide⟩ :=
  accepted_of_selected 12 28031 ⟨408930, by decide⟩ ⟨12, 1, 0, 408930, 28031, 1, 65536⟩
    (by decide) selected_cut_16052

theorem unmarked_context_11_7007_408931 : frontier 10 ⟨408931, by decide⟩
    (prefixCache 11 7007) (prefixPartial 11 7007) = false := by
  decide +kernel

theorem node_context_11_7007_408931 : EJMOriginalGlobalDAGData.nodes 10 ⟨408931, by decide⟩ =
    .split (coordinate 11) (![⟨408765, by decide⟩,⟨408885, by decide⟩,⟨408929, by decide⟩,⟨408930, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7007_408931 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7007 ⟨408931, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7007
    ⟨408931, by decide⟩ (by decide) (![⟨408765, by decide⟩,⟨408885, by decide⟩,⟨408929, by decide⟩,⟨408930, by decide⟩]) unmarked_context_11_7007_408931 node_context_11_7007_408931
  intro a
  fin_cases a
  · exact context_12_28028_408765
  · exact context_12_28029_408885
  · exact context_12_28030_408929
  · exact context_12_28031_408930

theorem unmarked_context_10_1751_408932 : frontier 11 ⟨408932, by decide⟩
    (prefixCache 10 1751) (prefixPartial 10 1751) = false := by
  decide +kernel

theorem node_context_10_1751_408932 : EJMOriginalGlobalDAGData.nodes 11 ⟨408932, by decide⟩ =
    .split (coordinate 10) (![⟨408377, by decide⟩,⟨408479, by decide⟩,⟨408708, by decide⟩,⟨408931, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1751_408932 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1751 ⟨408932, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1751
    ⟨408932, by decide⟩ (by decide) (![⟨408377, by decide⟩,⟨408479, by decide⟩,⟨408708, by decide⟩,⟨408931, by decide⟩]) unmarked_context_10_1751_408932 node_context_10_1751_408932
  intro a
  fin_cases a
  · exact context_11_7004_408377
  · exact context_11_7005_408479
  · exact context_11_7006_408708
  · exact context_11_7007_408931

theorem unmarked_context_9_437_408933 : frontier 12 ⟨408933, by decide⟩
    (prefixCache 9 437) (prefixPartial 9 437) = false := by
  decide +kernel

theorem node_context_9_437_408933 : EJMOriginalGlobalDAGData.nodes 12 ⟨408933, by decide⟩ =
    .split (coordinate 9) (![⟨406577, by decide⟩,⟨407180, by decide⟩,⟨408103, by decide⟩,⟨408932, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_437_408933 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 437 ⟨408933, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 437
    ⟨408933, by decide⟩ (by decide) (![⟨406577, by decide⟩,⟨407180, by decide⟩,⟨408103, by decide⟩,⟨408932, by decide⟩]) unmarked_context_9_437_408933 node_context_9_437_408933
  intro a
  fin_cases a
  · exact context_10_1748_406577
  · exact context_10_1749_407180
  · exact context_10_1750_408103
  · exact context_10_1751_408932

theorem selected_cut_16053 : selected 9 ⟨408967, by decide⟩
    (prefixPartial 12 28032) = some ⟨12, 2, 0, 408967, 28032, 2853, 65536⟩ := by
  decide +kernel

theorem context_12_28032_408967 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28032 ⟨408967, by decide⟩ :=
  accepted_of_selected 12 28032 ⟨408967, by decide⟩ ⟨12, 2, 0, 408967, 28032, 2853, 65536⟩
    (by decide) selected_cut_16053

theorem selected_cut_16054 : selected 9 ⟨409001, by decide⟩
    (prefixPartial 12 28033) = some ⟨12, 2, 0, 409001, 28033, 3221, 65536⟩ := by
  decide +kernel

theorem context_12_28033_409001 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28033 ⟨409001, by decide⟩ :=
  accepted_of_selected 12 28033 ⟨409001, by decide⟩ ⟨12, 2, 0, 409001, 28033, 3221, 65536⟩
    (by decide) selected_cut_16054

theorem selected_cut_16055 : selected 9 ⟨409032, by decide⟩
    (prefixPartial 12 28034) = some ⟨12, 2, 0, 409032, 28034, 3309, 65536⟩ := by
  decide +kernel

theorem context_12_28034_409032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28034 ⟨409032, by decide⟩ :=
  accepted_of_selected 12 28034 ⟨409032, by decide⟩ ⟨12, 2, 0, 409032, 28034, 3309, 65536⟩
    (by decide) selected_cut_16055

theorem selected_cut_16056 : selected 9 ⟨409073, by decide⟩
    (prefixPartial 12 28035) = some ⟨12, 2, 0, 409073, 28035, 3425, 65536⟩ := by
  decide +kernel

theorem context_12_28035_409073 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28035 ⟨409073, by decide⟩ :=
  accepted_of_selected 12 28035 ⟨409073, by decide⟩ ⟨12, 2, 0, 409073, 28035, 3425, 65536⟩
    (by decide) selected_cut_16056

theorem unmarked_context_11_7008_409074 : frontier 10 ⟨409074, by decide⟩
    (prefixCache 11 7008) (prefixPartial 11 7008) = false := by
  decide +kernel

theorem node_context_11_7008_409074 : EJMOriginalGlobalDAGData.nodes 10 ⟨409074, by decide⟩ =
    .split (coordinate 11) (![⟨408967, by decide⟩,⟨409001, by decide⟩,⟨409032, by decide⟩,⟨409073, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7008_409074 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7008 ⟨409074, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7008
    ⟨409074, by decide⟩ (by decide) (![⟨408967, by decide⟩,⟨409001, by decide⟩,⟨409032, by decide⟩,⟨409073, by decide⟩]) unmarked_context_11_7008_409074 node_context_11_7008_409074
  intro a
  fin_cases a
  · exact context_12_28032_408967
  · exact context_12_28033_409001
  · exact context_12_28034_409032
  · exact context_12_28035_409073

theorem selected_cut_16057 : selected 9 ⟨409106, by decide⟩
    (prefixPartial 12 28036) = some ⟨12, 2, 0, 409106, 28036, 2553, 65536⟩ := by
  decide +kernel

theorem context_12_28036_409106 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28036 ⟨409106, by decide⟩ :=
  accepted_of_selected 12 28036 ⟨409106, by decide⟩ ⟨12, 2, 0, 409106, 28036, 2553, 65536⟩
    (by decide) selected_cut_16057

theorem selected_cut_16058 : selected 9 ⟨409181, by decide⟩
    (prefixPartial 12 28037) = some ⟨12, 2, 0, 409181, 28037, 3905, 65536⟩ := by
  decide +kernel

theorem context_12_28037_409181 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28037 ⟨409181, by decide⟩ :=
  accepted_of_selected 12 28037 ⟨409181, by decide⟩ ⟨12, 2, 0, 409181, 28037, 3905, 65536⟩
    (by decide) selected_cut_16058

theorem selected_cut_16059 : selected 9 ⟨409209, by decide⟩
    (prefixPartial 12 28038) = some ⟨12, 2, 0, 409209, 28038, 2793, 65536⟩ := by
  decide +kernel

theorem context_12_28038_409209 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28038 ⟨409209, by decide⟩ :=
  accepted_of_selected 12 28038 ⟨409209, by decide⟩ ⟨12, 2, 0, 409209, 28038, 2793, 65536⟩
    (by decide) selected_cut_16059

theorem selected_cut_16060 : selected 9 ⟨409240, by decide⟩
    (prefixPartial 12 28039) = some ⟨12, 2, 0, 409240, 28039, 2913, 65536⟩ := by
  decide +kernel

theorem context_12_28039_409240 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28039 ⟨409240, by decide⟩ :=
  accepted_of_selected 12 28039 ⟨409240, by decide⟩ ⟨12, 2, 0, 409240, 28039, 2913, 65536⟩
    (by decide) selected_cut_16060

theorem unmarked_context_11_7009_409241 : frontier 10 ⟨409241, by decide⟩
    (prefixCache 11 7009) (prefixPartial 11 7009) = false := by
  decide +kernel

theorem node_context_11_7009_409241 : EJMOriginalGlobalDAGData.nodes 10 ⟨409241, by decide⟩ =
    .split (coordinate 11) (![⟨409106, by decide⟩,⟨409181, by decide⟩,⟨409209, by decide⟩,⟨409240, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7009_409241 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7009 ⟨409241, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7009
    ⟨409241, by decide⟩ (by decide) (![⟨409106, by decide⟩,⟨409181, by decide⟩,⟨409209, by decide⟩,⟨409240, by decide⟩]) unmarked_context_11_7009_409241 node_context_11_7009_409241
  intro a
  fin_cases a
  · exact context_12_28036_409106
  · exact context_12_28037_409181
  · exact context_12_28038_409209
  · exact context_12_28039_409240

theorem selected_cut_16061 : selected 9 ⟨409287, by decide⟩
    (prefixPartial 12 28040) = some ⟨12, 2, 0, 409287, 28040, 2949, 65536⟩ := by
  decide +kernel

theorem context_12_28040_409287 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28040 ⟨409287, by decide⟩ :=
  accepted_of_selected 12 28040 ⟨409287, by decide⟩ ⟨12, 2, 0, 409287, 28040, 2949, 65536⟩
    (by decide) selected_cut_16061

theorem selected_cut_16062 : selected 9 ⟨409313, by decide⟩
    (prefixPartial 12 28041) = some ⟨12, 2, 0, 409313, 28041, 3025, 65536⟩ := by
  decide +kernel

theorem context_12_28041_409313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28041 ⟨409313, by decide⟩ :=
  accepted_of_selected 12 28041 ⟨409313, by decide⟩ ⟨12, 2, 0, 409313, 28041, 3025, 65536⟩
    (by decide) selected_cut_16062

theorem selected_cut_16063 : selected 9 ⟨409341, by decide⟩
    (prefixPartial 12 28042) = some ⟨12, 2, 0, 409341, 28042, 3017, 65536⟩ := by
  decide +kernel

theorem context_12_28042_409341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28042 ⟨409341, by decide⟩ :=
  accepted_of_selected 12 28042 ⟨409341, by decide⟩ ⟨12, 2, 0, 409341, 28042, 3017, 65536⟩
    (by decide) selected_cut_16063

theorem selected_cut_16064 : selected 9 ⟨409371, by decide⟩
    (prefixPartial 12 28043) = some ⟨12, 2, 0, 409371, 28043, 2969, 65536⟩ := by
  decide +kernel

theorem context_12_28043_409371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28043 ⟨409371, by decide⟩ :=
  accepted_of_selected 12 28043 ⟨409371, by decide⟩ ⟨12, 2, 0, 409371, 28043, 2969, 65536⟩
    (by decide) selected_cut_16064

theorem unmarked_context_11_7010_409372 : frontier 10 ⟨409372, by decide⟩
    (prefixCache 11 7010) (prefixPartial 11 7010) = false := by
  decide +kernel

theorem node_context_11_7010_409372 : EJMOriginalGlobalDAGData.nodes 10 ⟨409372, by decide⟩ =
    .split (coordinate 11) (![⟨409287, by decide⟩,⟨409313, by decide⟩,⟨409341, by decide⟩,⟨409371, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7010_409372 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7010 ⟨409372, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7010
    ⟨409372, by decide⟩ (by decide) (![⟨409287, by decide⟩,⟨409313, by decide⟩,⟨409341, by decide⟩,⟨409371, by decide⟩]) unmarked_context_11_7010_409372 node_context_11_7010_409372
  intro a
  fin_cases a
  · exact context_12_28040_409287
  · exact context_12_28041_409313
  · exact context_12_28042_409341
  · exact context_12_28043_409371

theorem selected_cut_16065 : selected 9 ⟨409399, by decide⟩
    (prefixPartial 12 28044) = some ⟨12, 2, 0, 409399, 28044, 2533, 65536⟩ := by
  decide +kernel

theorem context_12_28044_409399 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28044 ⟨409399, by decide⟩ :=
  accepted_of_selected 12 28044 ⟨409399, by decide⟩ ⟨12, 2, 0, 409399, 28044, 2533, 65536⟩
    (by decide) selected_cut_16065

theorem selected_cut_16066 : selected 9 ⟨409426, by decide⟩
    (prefixPartial 12 28045) = some ⟨12, 2, 0, 409426, 28045, 2593, 65536⟩ := by
  decide +kernel

theorem context_12_28045_409426 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28045 ⟨409426, by decide⟩ :=
  accepted_of_selected 12 28045 ⟨409426, by decide⟩ ⟨12, 2, 0, 409426, 28045, 2593, 65536⟩
    (by decide) selected_cut_16066

theorem selected_cut_16067 : selected 9 ⟨409455, by decide⟩
    (prefixPartial 12 28046) = some ⟨12, 2, 0, 409455, 28046, 2685, 65536⟩ := by
  decide +kernel

theorem context_12_28046_409455 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28046 ⟨409455, by decide⟩ :=
  accepted_of_selected 12 28046 ⟨409455, by decide⟩ ⟨12, 2, 0, 409455, 28046, 2685, 65536⟩
    (by decide) selected_cut_16067

theorem selected_cut_16068 : selected 9 ⟨409480, by decide⟩
    (prefixPartial 12 28047) = some ⟨12, 2, 0, 409480, 28047, 2665, 65536⟩ := by
  decide +kernel

theorem context_12_28047_409480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28047 ⟨409480, by decide⟩ :=
  accepted_of_selected 12 28047 ⟨409480, by decide⟩ ⟨12, 2, 0, 409480, 28047, 2665, 65536⟩
    (by decide) selected_cut_16068

theorem unmarked_context_11_7011_409481 : frontier 10 ⟨409481, by decide⟩
    (prefixCache 11 7011) (prefixPartial 11 7011) = false := by
  decide +kernel

theorem node_context_11_7011_409481 : EJMOriginalGlobalDAGData.nodes 10 ⟨409481, by decide⟩ =
    .split (coordinate 11) (![⟨409399, by decide⟩,⟨409426, by decide⟩,⟨409455, by decide⟩,⟨409480, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7011_409481 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7011 ⟨409481, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7011
    ⟨409481, by decide⟩ (by decide) (![⟨409399, by decide⟩,⟨409426, by decide⟩,⟨409455, by decide⟩,⟨409480, by decide⟩]) unmarked_context_11_7011_409481 node_context_11_7011_409481
  intro a
  fin_cases a
  · exact context_12_28044_409399
  · exact context_12_28045_409426
  · exact context_12_28046_409455
  · exact context_12_28047_409480

theorem unmarked_context_10_1752_409482 : frontier 11 ⟨409482, by decide⟩
    (prefixCache 10 1752) (prefixPartial 10 1752) = false := by
  decide +kernel

theorem node_context_10_1752_409482 : EJMOriginalGlobalDAGData.nodes 11 ⟨409482, by decide⟩ =
    .split (coordinate 10) (![⟨409074, by decide⟩,⟨409241, by decide⟩,⟨409372, by decide⟩,⟨409481, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1752_409482 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1752 ⟨409482, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1752
    ⟨409482, by decide⟩ (by decide) (![⟨409074, by decide⟩,⟨409241, by decide⟩,⟨409372, by decide⟩,⟨409481, by decide⟩]) unmarked_context_10_1752_409482 node_context_10_1752_409482
  intro a
  fin_cases a
  · exact context_11_7008_409074
  · exact context_11_7009_409241
  · exact context_11_7010_409372
  · exact context_11_7011_409481

theorem selected_cut_16069 : selected 9 ⟨409505, by decide⟩
    (prefixPartial 12 28048) = some ⟨12, 2, 0, 409505, 28048, 2077, 65536⟩ := by
  decide +kernel

theorem context_12_28048_409505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28048 ⟨409505, by decide⟩ :=
  accepted_of_selected 12 28048 ⟨409505, by decide⟩ ⟨12, 2, 0, 409505, 28048, 2077, 65536⟩
    (by decide) selected_cut_16069

theorem selected_cut_16070 : selected 9 ⟨409531, by decide⟩
    (prefixPartial 12 28049) = some ⟨12, 2, 0, 409531, 28049, 2469, 65536⟩ := by
  decide +kernel

theorem context_12_28049_409531 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28049 ⟨409531, by decide⟩ :=
  accepted_of_selected 12 28049 ⟨409531, by decide⟩ ⟨12, 2, 0, 409531, 28049, 2469, 65536⟩
    (by decide) selected_cut_16070

theorem selected_cut_16071 : selected 9 ⟨409566, by decide⟩
    (prefixPartial 12 28050) = some ⟨12, 2, 0, 409566, 28050, 2749, 65536⟩ := by
  decide +kernel

theorem context_12_28050_409566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28050 ⟨409566, by decide⟩ :=
  accepted_of_selected 12 28050 ⟨409566, by decide⟩ ⟨12, 2, 0, 409566, 28050, 2749, 65536⟩
    (by decide) selected_cut_16071

theorem selected_cut_16072 : selected 9 ⟨409608, by decide⟩
    (prefixPartial 12 28051) = some ⟨12, 2, 0, 409608, 28051, 2797, 65536⟩ := by
  decide +kernel

theorem context_12_28051_409608 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28051 ⟨409608, by decide⟩ :=
  accepted_of_selected 12 28051 ⟨409608, by decide⟩ ⟨12, 2, 0, 409608, 28051, 2797, 65536⟩
    (by decide) selected_cut_16072

theorem unmarked_context_11_7012_409609 : frontier 10 ⟨409609, by decide⟩
    (prefixCache 11 7012) (prefixPartial 11 7012) = false := by
  decide +kernel

theorem node_context_11_7012_409609 : EJMOriginalGlobalDAGData.nodes 10 ⟨409609, by decide⟩ =
    .split (coordinate 11) (![⟨409505, by decide⟩,⟨409531, by decide⟩,⟨409566, by decide⟩,⟨409608, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7012_409609 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7012 ⟨409609, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7012
    ⟨409609, by decide⟩ (by decide) (![⟨409505, by decide⟩,⟨409531, by decide⟩,⟨409566, by decide⟩,⟨409608, by decide⟩]) unmarked_context_11_7012_409609 node_context_11_7012_409609
  intro a
  fin_cases a
  · exact context_12_28048_409505
  · exact context_12_28049_409531
  · exact context_12_28050_409566
  · exact context_12_28051_409608

theorem selected_cut_16073 : selected 9 ⟨409629, by decide⟩
    (prefixPartial 12 28052) = some ⟨12, 2, 0, 409629, 28052, 1713, 65536⟩ := by
  decide +kernel

theorem context_12_28052_409629 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28052 ⟨409629, by decide⟩ :=
  accepted_of_selected 12 28052 ⟨409629, by decide⟩ ⟨12, 2, 0, 409629, 28052, 1713, 65536⟩
    (by decide) selected_cut_16073

theorem selected_cut_16074 : selected 9 ⟨409630, by decide⟩
    (prefixPartial 12 28053) = some ⟨12, 1, 0, 409630, 28053, 1, 65536⟩ := by
  decide +kernel

theorem context_12_28053_409630 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28053 ⟨409630, by decide⟩ :=
  accepted_of_selected 12 28053 ⟨409630, by decide⟩ ⟨12, 1, 0, 409630, 28053, 1, 65536⟩
    (by decide) selected_cut_16074

theorem selected_cut_16075 : selected 9 ⟨409653, by decide⟩
    (prefixPartial 12 28054) = some ⟨12, 2, 0, 409653, 28054, 2117, 65536⟩ := by
  decide +kernel

theorem context_12_28054_409653 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28054 ⟨409653, by decide⟩ :=
  accepted_of_selected 12 28054 ⟨409653, by decide⟩ ⟨12, 2, 0, 409653, 28054, 2117, 65536⟩
    (by decide) selected_cut_16075

theorem selected_cut_16076 : selected 9 ⟨409672, by decide⟩
    (prefixPartial 12 28055) = some ⟨12, 2, 0, 409672, 28055, 2197, 65536⟩ := by
  decide +kernel

theorem context_12_28055_409672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28055 ⟨409672, by decide⟩ :=
  accepted_of_selected 12 28055 ⟨409672, by decide⟩ ⟨12, 2, 0, 409672, 28055, 2197, 65536⟩
    (by decide) selected_cut_16076

theorem unmarked_context_11_7013_409673 : frontier 10 ⟨409673, by decide⟩
    (prefixCache 11 7013) (prefixPartial 11 7013) = false := by
  decide +kernel

theorem node_context_11_7013_409673 : EJMOriginalGlobalDAGData.nodes 10 ⟨409673, by decide⟩ =
    .split (coordinate 11) (![⟨409629, by decide⟩,⟨409630, by decide⟩,⟨409653, by decide⟩,⟨409672, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7013_409673 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7013 ⟨409673, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7013
    ⟨409673, by decide⟩ (by decide) (![⟨409629, by decide⟩,⟨409630, by decide⟩,⟨409653, by decide⟩,⟨409672, by decide⟩]) unmarked_context_11_7013_409673 node_context_11_7013_409673
  intro a
  fin_cases a
  · exact context_12_28052_409629
  · exact context_12_28053_409630
  · exact context_12_28054_409653
  · exact context_12_28055_409672

theorem selected_cut_16077 : selected 9 ⟨409693, by decide⟩
    (prefixPartial 12 28056) = some ⟨12, 2, 0, 409693, 28056, 1853, 65536⟩ := by
  decide +kernel

theorem context_12_28056_409693 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28056 ⟨409693, by decide⟩ :=
  accepted_of_selected 12 28056 ⟨409693, by decide⟩ ⟨12, 2, 0, 409693, 28056, 1853, 65536⟩
    (by decide) selected_cut_16077

theorem selected_cut_16078 : selected 9 ⟨409714, by decide⟩
    (prefixPartial 12 28057) = some ⟨12, 2, 0, 409714, 28057, 1949, 65536⟩ := by
  decide +kernel

theorem context_12_28057_409714 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28057 ⟨409714, by decide⟩ :=
  accepted_of_selected 12 28057 ⟨409714, by decide⟩ ⟨12, 2, 0, 409714, 28057, 1949, 65536⟩
    (by decide) selected_cut_16078

theorem selected_cut_16079 : selected 9 ⟨409741, by decide⟩
    (prefixPartial 12 28058) = some ⟨12, 2, 0, 409741, 28058, 2117, 65536⟩ := by
  decide +kernel

theorem context_12_28058_409741 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28058 ⟨409741, by decide⟩ :=
  accepted_of_selected 12 28058 ⟨409741, by decide⟩ ⟨12, 2, 0, 409741, 28058, 2117, 65536⟩
    (by decide) selected_cut_16079

theorem selected_cut_16080 : selected 9 ⟨409765, by decide⟩
    (prefixPartial 12 28059) = some ⟨12, 2, 0, 409765, 28059, 2189, 65536⟩ := by
  decide +kernel

theorem context_12_28059_409765 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28059 ⟨409765, by decide⟩ :=
  accepted_of_selected 12 28059 ⟨409765, by decide⟩ ⟨12, 2, 0, 409765, 28059, 2189, 65536⟩
    (by decide) selected_cut_16080

theorem unmarked_context_11_7014_409766 : frontier 10 ⟨409766, by decide⟩
    (prefixCache 11 7014) (prefixPartial 11 7014) = false := by
  decide +kernel

theorem node_context_11_7014_409766 : EJMOriginalGlobalDAGData.nodes 10 ⟨409766, by decide⟩ =
    .split (coordinate 11) (![⟨409693, by decide⟩,⟨409714, by decide⟩,⟨409741, by decide⟩,⟨409765, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7014_409766 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7014 ⟨409766, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7014
    ⟨409766, by decide⟩ (by decide) (![⟨409693, by decide⟩,⟨409714, by decide⟩,⟨409741, by decide⟩,⟨409765, by decide⟩]) unmarked_context_11_7014_409766 node_context_11_7014_409766
  intro a
  fin_cases a
  · exact context_12_28056_409693
  · exact context_12_28057_409714
  · exact context_12_28058_409741
  · exact context_12_28059_409765

theorem selected_cut_16081 : selected 9 ⟨409786, by decide⟩
    (prefixPartial 12 28060) = some ⟨12, 2, 0, 409786, 28060, 1777, 65536⟩ := by
  decide +kernel

theorem context_12_28060_409786 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28060 ⟨409786, by decide⟩ :=
  accepted_of_selected 12 28060 ⟨409786, by decide⟩ ⟨12, 2, 0, 409786, 28060, 1777, 65536⟩
    (by decide) selected_cut_16081

theorem selected_cut_16082 : selected 9 ⟨409803, by decide⟩
    (prefixPartial 12 28061) = some ⟨12, 2, 0, 409803, 28061, 1777, 65536⟩ := by
  decide +kernel

theorem context_12_28061_409803 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28061 ⟨409803, by decide⟩ :=
  accepted_of_selected 12 28061 ⟨409803, by decide⟩ ⟨12, 2, 0, 409803, 28061, 1777, 65536⟩
    (by decide) selected_cut_16082

theorem selected_cut_16083 : selected 9 ⟨409831, by decide⟩
    (prefixPartial 12 28062) = some ⟨12, 2, 0, 409831, 28062, 1981, 65536⟩ := by
  decide +kernel

theorem context_12_28062_409831 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28062 ⟨409831, by decide⟩ :=
  accepted_of_selected 12 28062 ⟨409831, by decide⟩ ⟨12, 2, 0, 409831, 28062, 1981, 65536⟩
    (by decide) selected_cut_16083

theorem selected_cut_16084 : selected 9 ⟨409850, by decide⟩
    (prefixPartial 12 28063) = some ⟨12, 2, 0, 409850, 28063, 2093, 65536⟩ := by
  decide +kernel

theorem context_12_28063_409850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28063 ⟨409850, by decide⟩ :=
  accepted_of_selected 12 28063 ⟨409850, by decide⟩ ⟨12, 2, 0, 409850, 28063, 2093, 65536⟩
    (by decide) selected_cut_16084

theorem unmarked_context_11_7015_409851 : frontier 10 ⟨409851, by decide⟩
    (prefixCache 11 7015) (prefixPartial 11 7015) = false := by
  decide +kernel

theorem node_context_11_7015_409851 : EJMOriginalGlobalDAGData.nodes 10 ⟨409851, by decide⟩ =
    .split (coordinate 11) (![⟨409786, by decide⟩,⟨409803, by decide⟩,⟨409831, by decide⟩,⟨409850, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7015_409851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7015 ⟨409851, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7015
    ⟨409851, by decide⟩ (by decide) (![⟨409786, by decide⟩,⟨409803, by decide⟩,⟨409831, by decide⟩,⟨409850, by decide⟩]) unmarked_context_11_7015_409851 node_context_11_7015_409851
  intro a
  fin_cases a
  · exact context_12_28060_409786
  · exact context_12_28061_409803
  · exact context_12_28062_409831
  · exact context_12_28063_409850

theorem unmarked_context_10_1753_409852 : frontier 11 ⟨409852, by decide⟩
    (prefixCache 10 1753) (prefixPartial 10 1753) = false := by
  decide +kernel

theorem node_context_10_1753_409852 : EJMOriginalGlobalDAGData.nodes 11 ⟨409852, by decide⟩ =
    .split (coordinate 10) (![⟨409609, by decide⟩,⟨409673, by decide⟩,⟨409766, by decide⟩,⟨409851, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1753_409852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1753 ⟨409852, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1753
    ⟨409852, by decide⟩ (by decide) (![⟨409609, by decide⟩,⟨409673, by decide⟩,⟨409766, by decide⟩,⟨409851, by decide⟩]) unmarked_context_10_1753_409852 node_context_10_1753_409852
  intro a
  fin_cases a
  · exact context_11_7012_409609
  · exact context_11_7013_409673
  · exact context_11_7014_409766
  · exact context_11_7015_409851

theorem selected_cut_16085 : selected 9 ⟨409871, by decide⟩
    (prefixPartial 12 28064) = some ⟨12, 2, 0, 409871, 28064, 1681, 65536⟩ := by
  decide +kernel

theorem context_12_28064_409871 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28064 ⟨409871, by decide⟩ :=
  accepted_of_selected 12 28064 ⟨409871, by decide⟩ ⟨12, 2, 0, 409871, 28064, 1681, 65536⟩
    (by decide) selected_cut_16085

theorem selected_cut_16086 : selected 9 ⟨409888, by decide⟩
    (prefixPartial 12 28065) = some ⟨12, 2, 0, 409888, 28065, 2077, 65536⟩ := by
  decide +kernel

theorem context_12_28065_409888 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28065 ⟨409888, by decide⟩ :=
  accepted_of_selected 12 28065 ⟨409888, by decide⟩ ⟨12, 2, 0, 409888, 28065, 2077, 65536⟩
    (by decide) selected_cut_16086

theorem selected_cut_16087 : selected 9 ⟨409916, by decide⟩
    (prefixPartial 12 28066) = some ⟨12, 2, 0, 409916, 28066, 2057, 65536⟩ := by
  decide +kernel

theorem context_12_28066_409916 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28066 ⟨409916, by decide⟩ :=
  accepted_of_selected 12 28066 ⟨409916, by decide⟩ ⟨12, 2, 0, 409916, 28066, 2057, 65536⟩
    (by decide) selected_cut_16087

theorem selected_cut_16088 : selected 9 ⟨409952, by decide⟩
    (prefixPartial 12 28067) = some ⟨12, 2, 0, 409952, 28067, 2225, 65536⟩ := by
  decide +kernel

theorem context_12_28067_409952 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28067 ⟨409952, by decide⟩ :=
  accepted_of_selected 12 28067 ⟨409952, by decide⟩ ⟨12, 2, 0, 409952, 28067, 2225, 65536⟩
    (by decide) selected_cut_16088

theorem unmarked_context_11_7016_409953 : frontier 10 ⟨409953, by decide⟩
    (prefixCache 11 7016) (prefixPartial 11 7016) = false := by
  decide +kernel

theorem node_context_11_7016_409953 : EJMOriginalGlobalDAGData.nodes 10 ⟨409953, by decide⟩ =
    .split (coordinate 11) (![⟨409871, by decide⟩,⟨409888, by decide⟩,⟨409916, by decide⟩,⟨409952, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7016_409953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7016 ⟨409953, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7016
    ⟨409953, by decide⟩ (by decide) (![⟨409871, by decide⟩,⟨409888, by decide⟩,⟨409916, by decide⟩,⟨409952, by decide⟩]) unmarked_context_11_7016_409953 node_context_11_7016_409953
  intro a
  fin_cases a
  · exact context_12_28064_409871
  · exact context_12_28065_409888
  · exact context_12_28066_409916
  · exact context_12_28067_409952

theorem selected_cut_16089 : selected 9 ⟨409967, by decide⟩
    (prefixPartial 12 28068) = some ⟨12, 2, 0, 409967, 28068, 1409, 65536⟩ := by
  decide +kernel

theorem context_12_28068_409967 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28068 ⟨409967, by decide⟩ :=
  accepted_of_selected 12 28068 ⟨409967, by decide⟩ ⟨12, 2, 0, 409967, 28068, 1409, 65536⟩
    (by decide) selected_cut_16089

theorem selected_cut_16090 : selected 9 ⟨410006, by decide⟩
    (prefixPartial 12 28069) = some ⟨12, 2, 0, 410006, 28069, 2301, 65536⟩ := by
  decide +kernel

theorem context_12_28069_410006 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28069 ⟨410006, by decide⟩ :=
  accepted_of_selected 12 28069 ⟨410006, by decide⟩ ⟨12, 2, 0, 410006, 28069, 2301, 65536⟩
    (by decide) selected_cut_16090

theorem selected_cut_16091 : selected 9 ⟨410023, by decide⟩
    (prefixPartial 12 28070) = some ⟨12, 2, 0, 410023, 28070, 1525, 65536⟩ := by
  decide +kernel

theorem context_12_28070_410023 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28070 ⟨410023, by decide⟩ :=
  accepted_of_selected 12 28070 ⟨410023, by decide⟩ ⟨12, 2, 0, 410023, 28070, 1525, 65536⟩
    (by decide) selected_cut_16091

theorem selected_cut_16092 : selected 9 ⟨410042, by decide⟩
    (prefixPartial 12 28071) = some ⟨12, 2, 0, 410042, 28071, 1733, 65536⟩ := by
  decide +kernel

theorem context_12_28071_410042 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28071 ⟨410042, by decide⟩ :=
  accepted_of_selected 12 28071 ⟨410042, by decide⟩ ⟨12, 2, 0, 410042, 28071, 1733, 65536⟩
    (by decide) selected_cut_16092

theorem unmarked_context_11_7017_410043 : frontier 10 ⟨410043, by decide⟩
    (prefixCache 11 7017) (prefixPartial 11 7017) = false := by
  decide +kernel

theorem node_context_11_7017_410043 : EJMOriginalGlobalDAGData.nodes 10 ⟨410043, by decide⟩ =
    .split (coordinate 11) (![⟨409967, by decide⟩,⟨410006, by decide⟩,⟨410023, by decide⟩,⟨410042, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7017_410043 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7017 ⟨410043, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7017
    ⟨410043, by decide⟩ (by decide) (![⟨409967, by decide⟩,⟨410006, by decide⟩,⟨410023, by decide⟩,⟨410042, by decide⟩]) unmarked_context_11_7017_410043 node_context_11_7017_410043
  intro a
  fin_cases a
  · exact context_12_28068_409967
  · exact context_12_28069_410006
  · exact context_12_28070_410023
  · exact context_12_28071_410042

theorem selected_cut_16093 : selected 9 ⟨410059, by decide⟩
    (prefixPartial 12 28072) = some ⟨12, 2, 0, 410059, 28072, 1509, 65536⟩ := by
  decide +kernel

theorem context_12_28072_410059 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28072 ⟨410059, by decide⟩ :=
  accepted_of_selected 12 28072 ⟨410059, by decide⟩ ⟨12, 2, 0, 410059, 28072, 1509, 65536⟩
    (by decide) selected_cut_16093

theorem selected_cut_16094 : selected 9 ⟨410076, by decide⟩
    (prefixPartial 12 28073) = some ⟨12, 2, 0, 410076, 28073, 1657, 65536⟩ := by
  decide +kernel

theorem context_12_28073_410076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28073 ⟨410076, by decide⟩ :=
  accepted_of_selected 12 28073 ⟨410076, by decide⟩ ⟨12, 2, 0, 410076, 28073, 1657, 65536⟩
    (by decide) selected_cut_16094

theorem selected_cut_16095 : selected 9 ⟨410094, by decide⟩
    (prefixPartial 12 28074) = some ⟨12, 2, 0, 410094, 28074, 1577, 65536⟩ := by
  decide +kernel

theorem context_12_28074_410094 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28074 ⟨410094, by decide⟩ :=
  accepted_of_selected 12 28074 ⟨410094, by decide⟩ ⟨12, 2, 0, 410094, 28074, 1577, 65536⟩
    (by decide) selected_cut_16095

theorem selected_cut_16096 : selected 9 ⟨410113, by decide⟩
    (prefixPartial 12 28075) = some ⟨12, 2, 0, 410113, 28075, 1645, 65536⟩ := by
  decide +kernel

theorem context_12_28075_410113 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28075 ⟨410113, by decide⟩ :=
  accepted_of_selected 12 28075 ⟨410113, by decide⟩ ⟨12, 2, 0, 410113, 28075, 1645, 65536⟩
    (by decide) selected_cut_16096

theorem unmarked_context_11_7018_410114 : frontier 10 ⟨410114, by decide⟩
    (prefixCache 11 7018) (prefixPartial 11 7018) = false := by
  decide +kernel

theorem node_context_11_7018_410114 : EJMOriginalGlobalDAGData.nodes 10 ⟨410114, by decide⟩ =
    .split (coordinate 11) (![⟨410059, by decide⟩,⟨410076, by decide⟩,⟨410094, by decide⟩,⟨410113, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7018_410114 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7018 ⟨410114, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7018
    ⟨410114, by decide⟩ (by decide) (![⟨410059, by decide⟩,⟨410076, by decide⟩,⟨410094, by decide⟩,⟨410113, by decide⟩]) unmarked_context_11_7018_410114 node_context_11_7018_410114
  intro a
  fin_cases a
  · exact context_12_28072_410059
  · exact context_12_28073_410076
  · exact context_12_28074_410094
  · exact context_12_28075_410113

theorem selected_cut_16097 : selected 9 ⟨410127, by decide⟩
    (prefixPartial 12 28076) = some ⟨12, 2, 0, 410127, 28076, 1481, 65536⟩ := by
  decide +kernel

theorem context_12_28076_410127 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28076 ⟨410127, by decide⟩ :=
  accepted_of_selected 12 28076 ⟨410127, by decide⟩ ⟨12, 2, 0, 410127, 28076, 1481, 65536⟩
    (by decide) selected_cut_16097

theorem selected_cut_16098 : selected 9 ⟨410142, by decide⟩
    (prefixPartial 12 28077) = some ⟨12, 2, 0, 410142, 28077, 1521, 65536⟩ := by
  decide +kernel

theorem context_12_28077_410142 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28077 ⟨410142, by decide⟩ :=
  accepted_of_selected 12 28077 ⟨410142, by decide⟩ ⟨12, 2, 0, 410142, 28077, 1521, 65536⟩
    (by decide) selected_cut_16098

theorem selected_cut_16099 : selected 9 ⟨410159, by decide⟩
    (prefixPartial 12 28078) = some ⟨12, 2, 0, 410159, 28078, 1517, 65536⟩ := by
  decide +kernel

theorem context_12_28078_410159 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28078 ⟨410159, by decide⟩ :=
  accepted_of_selected 12 28078 ⟨410159, by decide⟩ ⟨12, 2, 0, 410159, 28078, 1517, 65536⟩
    (by decide) selected_cut_16099

theorem selected_cut_16100 : selected 9 ⟨410180, by decide⟩
    (prefixPartial 12 28079) = some ⟨12, 2, 0, 410180, 28079, 1693, 65536⟩ := by
  decide +kernel

theorem context_12_28079_410180 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28079 ⟨410180, by decide⟩ :=
  accepted_of_selected 12 28079 ⟨410180, by decide⟩ ⟨12, 2, 0, 410180, 28079, 1693, 65536⟩
    (by decide) selected_cut_16100

theorem unmarked_context_11_7019_410181 : frontier 10 ⟨410181, by decide⟩
    (prefixCache 11 7019) (prefixPartial 11 7019) = false := by
  decide +kernel

theorem node_context_11_7019_410181 : EJMOriginalGlobalDAGData.nodes 10 ⟨410181, by decide⟩ =
    .split (coordinate 11) (![⟨410127, by decide⟩,⟨410142, by decide⟩,⟨410159, by decide⟩,⟨410180, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7019_410181 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7019 ⟨410181, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7019
    ⟨410181, by decide⟩ (by decide) (![⟨410127, by decide⟩,⟨410142, by decide⟩,⟨410159, by decide⟩,⟨410180, by decide⟩]) unmarked_context_11_7019_410181 node_context_11_7019_410181
  intro a
  fin_cases a
  · exact context_12_28076_410127
  · exact context_12_28077_410142
  · exact context_12_28078_410159
  · exact context_12_28079_410180

theorem unmarked_context_10_1754_410182 : frontier 11 ⟨410182, by decide⟩
    (prefixCache 10 1754) (prefixPartial 10 1754) = false := by
  decide +kernel

theorem node_context_10_1754_410182 : EJMOriginalGlobalDAGData.nodes 11 ⟨410182, by decide⟩ =
    .split (coordinate 10) (![⟨409953, by decide⟩,⟨410043, by decide⟩,⟨410114, by decide⟩,⟨410181, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1754_410182 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1754 ⟨410182, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1754
    ⟨410182, by decide⟩ (by decide) (![⟨409953, by decide⟩,⟨410043, by decide⟩,⟨410114, by decide⟩,⟨410181, by decide⟩]) unmarked_context_10_1754_410182 node_context_10_1754_410182
  intro a
  fin_cases a
  · exact context_11_7016_409953
  · exact context_11_7017_410043
  · exact context_11_7018_410114
  · exact context_11_7019_410181

theorem selected_cut_16101 : selected 9 ⟨410196, by decide⟩
    (prefixPartial 12 28080) = some ⟨12, 2, 0, 410196, 28080, 1305, 65536⟩ := by
  decide +kernel

theorem context_12_28080_410196 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28080 ⟨410196, by decide⟩ :=
  accepted_of_selected 12 28080 ⟨410196, by decide⟩ ⟨12, 2, 0, 410196, 28080, 1305, 65536⟩
    (by decide) selected_cut_16101

theorem selected_cut_16102 : selected 9 ⟨410213, by decide⟩
    (prefixPartial 12 28081) = some ⟨12, 2, 0, 410213, 28081, 1469, 65536⟩ := by
  decide +kernel

theorem context_12_28081_410213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28081 ⟨410213, by decide⟩ :=
  accepted_of_selected 12 28081 ⟨410213, by decide⟩ ⟨12, 2, 0, 410213, 28081, 1469, 65536⟩
    (by decide) selected_cut_16102

theorem selected_cut_16103 : selected 9 ⟨410230, by decide⟩
    (prefixPartial 12 28082) = some ⟨12, 2, 0, 410230, 28082, 1493, 65536⟩ := by
  decide +kernel

theorem context_12_28082_410230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28082 ⟨410230, by decide⟩ :=
  accepted_of_selected 12 28082 ⟨410230, by decide⟩ ⟨12, 2, 0, 410230, 28082, 1493, 65536⟩
    (by decide) selected_cut_16103

theorem selected_cut_16104 : selected 9 ⟨410253, by decide⟩
    (prefixPartial 12 28083) = some ⟨12, 2, 0, 410253, 28083, 1557, 65536⟩ := by
  decide +kernel

theorem context_12_28083_410253 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28083 ⟨410253, by decide⟩ :=
  accepted_of_selected 12 28083 ⟨410253, by decide⟩ ⟨12, 2, 0, 410253, 28083, 1557, 65536⟩
    (by decide) selected_cut_16104

theorem unmarked_context_11_7020_410254 : frontier 10 ⟨410254, by decide⟩
    (prefixCache 11 7020) (prefixPartial 11 7020) = false := by
  decide +kernel

theorem node_context_11_7020_410254 : EJMOriginalGlobalDAGData.nodes 10 ⟨410254, by decide⟩ =
    .split (coordinate 11) (![⟨410196, by decide⟩,⟨410213, by decide⟩,⟨410230, by decide⟩,⟨410253, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7020_410254 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7020 ⟨410254, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7020
    ⟨410254, by decide⟩ (by decide) (![⟨410196, by decide⟩,⟨410213, by decide⟩,⟨410230, by decide⟩,⟨410253, by decide⟩]) unmarked_context_11_7020_410254 node_context_11_7020_410254
  intro a
  fin_cases a
  · exact context_12_28080_410196
  · exact context_12_28081_410213
  · exact context_12_28082_410230
  · exact context_12_28083_410253

theorem selected_cut_16105 : selected 9 ⟨410266, by decide⟩
    (prefixPartial 12 28084) = some ⟨12, 2, 0, 410266, 28084, 1157, 65536⟩ := by
  decide +kernel

theorem context_12_28084_410266 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28084 ⟨410266, by decide⟩ :=
  accepted_of_selected 12 28084 ⟨410266, by decide⟩ ⟨12, 2, 0, 410266, 28084, 1157, 65536⟩
    (by decide) selected_cut_16105

theorem selected_cut_16106 : selected 9 ⟨410288, by decide⟩
    (prefixPartial 12 28085) = some ⟨12, 2, 0, 410288, 28085, 1669, 65536⟩ := by
  decide +kernel

theorem context_12_28085_410288 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28085 ⟨410288, by decide⟩ :=
  accepted_of_selected 12 28085 ⟨410288, by decide⟩ ⟨12, 2, 0, 410288, 28085, 1669, 65536⟩
    (by decide) selected_cut_16106

theorem selected_cut_16107 : selected 9 ⟨410300, by decide⟩
    (prefixPartial 12 28086) = some ⟨12, 2, 0, 410300, 28086, 1217, 65536⟩ := by
  decide +kernel

theorem context_12_28086_410300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28086 ⟨410300, by decide⟩ :=
  accepted_of_selected 12 28086 ⟨410300, by decide⟩ ⟨12, 2, 0, 410300, 28086, 1217, 65536⟩
    (by decide) selected_cut_16107

theorem selected_cut_16108 : selected 9 ⟨410311, by decide⟩
    (prefixPartial 12 28087) = some ⟨12, 2, 0, 410311, 28087, 1277, 65536⟩ := by
  decide +kernel

theorem context_12_28087_410311 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28087 ⟨410311, by decide⟩ :=
  accepted_of_selected 12 28087 ⟨410311, by decide⟩ ⟨12, 2, 0, 410311, 28087, 1277, 65536⟩
    (by decide) selected_cut_16108

theorem unmarked_context_11_7021_410312 : frontier 10 ⟨410312, by decide⟩
    (prefixCache 11 7021) (prefixPartial 11 7021) = false := by
  decide +kernel

theorem node_context_11_7021_410312 : EJMOriginalGlobalDAGData.nodes 10 ⟨410312, by decide⟩ =
    .split (coordinate 11) (![⟨410266, by decide⟩,⟨410288, by decide⟩,⟨410300, by decide⟩,⟨410311, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7021_410312 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7021 ⟨410312, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7021
    ⟨410312, by decide⟩ (by decide) (![⟨410266, by decide⟩,⟨410288, by decide⟩,⟨410300, by decide⟩,⟨410311, by decide⟩]) unmarked_context_11_7021_410312 node_context_11_7021_410312
  intro a
  fin_cases a
  · exact context_12_28084_410266
  · exact context_12_28085_410288
  · exact context_12_28086_410300
  · exact context_12_28087_410311

theorem selected_cut_16109 : selected 9 ⟨410326, by decide⟩
    (prefixPartial 12 28088) = some ⟨12, 2, 0, 410326, 28088, 1089, 65536⟩ := by
  decide +kernel

theorem context_12_28088_410326 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28088 ⟨410326, by decide⟩ :=
  accepted_of_selected 12 28088 ⟨410326, by decide⟩ ⟨12, 2, 0, 410326, 28088, 1089, 65536⟩
    (by decide) selected_cut_16109

theorem selected_cut_16110 : selected 9 ⟨410337, by decide⟩
    (prefixPartial 12 28089) = some ⟨12, 2, 0, 410337, 28089, 1149, 65536⟩ := by
  decide +kernel

theorem context_12_28089_410337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28089 ⟨410337, by decide⟩ :=
  accepted_of_selected 12 28089 ⟨410337, by decide⟩ ⟨12, 2, 0, 410337, 28089, 1149, 65536⟩
    (by decide) selected_cut_16110

theorem selected_cut_16111 : selected 9 ⟨410355, by decide⟩
    (prefixPartial 12 28090) = some ⟨12, 2, 0, 410355, 28090, 1141, 65536⟩ := by
  decide +kernel

theorem context_12_28090_410355 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28090 ⟨410355, by decide⟩ :=
  accepted_of_selected 12 28090 ⟨410355, by decide⟩ ⟨12, 2, 0, 410355, 28090, 1141, 65536⟩
    (by decide) selected_cut_16111

theorem selected_cut_16112 : selected 9 ⟨410382, by decide⟩
    (prefixPartial 12 28091) = some ⟨12, 2, 0, 410382, 28091, 1217, 65536⟩ := by
  decide +kernel

theorem context_12_28091_410382 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28091 ⟨410382, by decide⟩ :=
  accepted_of_selected 12 28091 ⟨410382, by decide⟩ ⟨12, 2, 0, 410382, 28091, 1217, 65536⟩
    (by decide) selected_cut_16112

theorem unmarked_context_11_7022_410383 : frontier 10 ⟨410383, by decide⟩
    (prefixCache 11 7022) (prefixPartial 11 7022) = false := by
  decide +kernel

theorem node_context_11_7022_410383 : EJMOriginalGlobalDAGData.nodes 10 ⟨410383, by decide⟩ =
    .split (coordinate 11) (![⟨410326, by decide⟩,⟨410337, by decide⟩,⟨410355, by decide⟩,⟨410382, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7022_410383 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7022 ⟨410383, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7022
    ⟨410383, by decide⟩ (by decide) (![⟨410326, by decide⟩,⟨410337, by decide⟩,⟨410355, by decide⟩,⟨410382, by decide⟩]) unmarked_context_11_7022_410383 node_context_11_7022_410383
  intro a
  fin_cases a
  · exact context_12_28088_410326
  · exact context_12_28089_410337
  · exact context_12_28090_410355
  · exact context_12_28091_410382

theorem selected_cut_16113 : selected 10 ⟨410457, by decide⟩
    (prefixPartial 11 7023) = some ⟨11, 2, 0, 410457, 7023, 3949, 262144⟩ := by
  decide +kernel

theorem context_11_7023_410457 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7023 ⟨410457, by decide⟩ :=
  accepted_of_selected 11 7023 ⟨410457, by decide⟩ ⟨11, 2, 0, 410457, 7023, 3949, 262144⟩
    (by decide) selected_cut_16113

theorem unmarked_context_10_1755_410458 : frontier 11 ⟨410458, by decide⟩
    (prefixCache 10 1755) (prefixPartial 10 1755) = false := by
  decide +kernel

theorem node_context_10_1755_410458 : EJMOriginalGlobalDAGData.nodes 11 ⟨410458, by decide⟩ =
    .split (coordinate 10) (![⟨410254, by decide⟩,⟨410312, by decide⟩,⟨410383, by decide⟩,⟨410457, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1755_410458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1755 ⟨410458, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1755
    ⟨410458, by decide⟩ (by decide) (![⟨410254, by decide⟩,⟨410312, by decide⟩,⟨410383, by decide⟩,⟨410457, by decide⟩]) unmarked_context_10_1755_410458 node_context_10_1755_410458
  intro a
  fin_cases a
  · exact context_11_7020_410254
  · exact context_11_7021_410312
  · exact context_11_7022_410383
  · exact context_11_7023_410457

theorem unmarked_context_9_438_410459 : frontier 12 ⟨410459, by decide⟩
    (prefixCache 9 438) (prefixPartial 9 438) = false := by
  decide +kernel

theorem node_context_9_438_410459 : EJMOriginalGlobalDAGData.nodes 12 ⟨410459, by decide⟩ =
    .split (coordinate 9) (![⟨409482, by decide⟩,⟨409852, by decide⟩,⟨410182, by decide⟩,⟨410458, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_438_410459 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 438 ⟨410459, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 438
    ⟨410459, by decide⟩ (by decide) (![⟨409482, by decide⟩,⟨409852, by decide⟩,⟨410182, by decide⟩,⟨410458, by decide⟩]) unmarked_context_9_438_410459 node_context_9_438_410459
  intro a
  fin_cases a
  · exact context_10_1752_409482
  · exact context_10_1753_409852
  · exact context_10_1754_410182
  · exact context_10_1755_410458

theorem selected_cut_16114 : selected 10 ⟨410489, by decide⟩
    (prefixPartial 11 7024) = some ⟨11, 2, 0, 410489, 7024, 3997, 262144⟩ := by
  decide +kernel

theorem context_11_7024_410489 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7024 ⟨410489, by decide⟩ :=
  accepted_of_selected 11 7024 ⟨410489, by decide⟩ ⟨11, 2, 0, 410489, 7024, 3997, 262144⟩
    (by decide) selected_cut_16114

theorem selected_cut_16115 : selected 10 ⟨410520, by decide⟩
    (prefixPartial 11 7025) = some ⟨11, 2, 0, 410520, 7025, 3617, 262144⟩ := by
  decide +kernel

theorem context_11_7025_410520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7025 ⟨410520, by decide⟩ :=
  accepted_of_selected 11 7025 ⟨410520, by decide⟩ ⟨11, 2, 0, 410520, 7025, 3617, 262144⟩
    (by decide) selected_cut_16115

theorem selected_cut_16116 : selected 10 ⟨410547, by decide⟩
    (prefixPartial 11 7026) = some ⟨11, 2, 0, 410547, 7026, 3485, 262144⟩ := by
  decide +kernel

theorem context_11_7026_410547 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7026 ⟨410547, by decide⟩ :=
  accepted_of_selected 11 7026 ⟨410547, by decide⟩ ⟨11, 2, 0, 410547, 7026, 3485, 262144⟩
    (by decide) selected_cut_16116

theorem selected_cut_16117 : selected 10 ⟨410580, by decide⟩
    (prefixPartial 11 7027) = some ⟨11, 2, 0, 410580, 7027, 3225, 262144⟩ := by
  decide +kernel

theorem context_11_7027_410580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7027 ⟨410580, by decide⟩ :=
  accepted_of_selected 11 7027 ⟨410580, by decide⟩ ⟨11, 2, 0, 410580, 7027, 3225, 262144⟩
    (by decide) selected_cut_16117

theorem unmarked_context_10_1756_410581 : frontier 11 ⟨410581, by decide⟩
    (prefixCache 10 1756) (prefixPartial 10 1756) = false := by
  decide +kernel

theorem node_context_10_1756_410581 : EJMOriginalGlobalDAGData.nodes 11 ⟨410581, by decide⟩ =
    .split (coordinate 10) (![⟨410489, by decide⟩,⟨410520, by decide⟩,⟨410547, by decide⟩,⟨410580, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1756_410581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1756 ⟨410581, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1756
    ⟨410581, by decide⟩ (by decide) (![⟨410489, by decide⟩,⟨410520, by decide⟩,⟨410547, by decide⟩,⟨410580, by decide⟩]) unmarked_context_10_1756_410581 node_context_10_1756_410581
  intro a
  fin_cases a
  · exact context_11_7024_410489
  · exact context_11_7025_410520
  · exact context_11_7026_410547
  · exact context_11_7027_410580

theorem selected_cut_16118 : selected 10 ⟨410610, by decide⟩
    (prefixPartial 11 7028) = some ⟨11, 2, 0, 410610, 7028, 2717, 262144⟩ := by
  decide +kernel

theorem context_11_7028_410610 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7028 ⟨410610, by decide⟩ :=
  accepted_of_selected 11 7028 ⟨410610, by decide⟩ ⟨11, 2, 0, 410610, 7028, 2717, 262144⟩
    (by decide) selected_cut_16118

theorem selected_cut_16119 : selected 10 ⟨410626, by decide⟩
    (prefixPartial 11 7029) = some ⟨11, 2, 0, 410626, 7029, 1549, 262144⟩ := by
  decide +kernel

theorem context_11_7029_410626 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7029 ⟨410626, by decide⟩ :=
  accepted_of_selected 11 7029 ⟨410626, by decide⟩ ⟨11, 2, 0, 410626, 7029, 1549, 262144⟩
    (by decide) selected_cut_16119

theorem selected_cut_16120 : selected 10 ⟨410644, by decide⟩
    (prefixPartial 11 7030) = some ⟨11, 2, 0, 410644, 7030, 2105, 262144⟩ := by
  decide +kernel

theorem context_11_7030_410644 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7030 ⟨410644, by decide⟩ :=
  accepted_of_selected 11 7030 ⟨410644, by decide⟩ ⟨11, 2, 0, 410644, 7030, 2105, 262144⟩
    (by decide) selected_cut_16120

theorem selected_cut_16121 : selected 10 ⟨410666, by decide⟩
    (prefixPartial 11 7031) = some ⟨11, 2, 0, 410666, 7031, 1905, 262144⟩ := by
  decide +kernel

theorem context_11_7031_410666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7031 ⟨410666, by decide⟩ :=
  accepted_of_selected 11 7031 ⟨410666, by decide⟩ ⟨11, 2, 0, 410666, 7031, 1905, 262144⟩
    (by decide) selected_cut_16121

theorem unmarked_context_10_1757_410667 : frontier 11 ⟨410667, by decide⟩
    (prefixCache 10 1757) (prefixPartial 10 1757) = false := by
  decide +kernel

theorem node_context_10_1757_410667 : EJMOriginalGlobalDAGData.nodes 11 ⟨410667, by decide⟩ =
    .split (coordinate 10) (![⟨410610, by decide⟩,⟨410626, by decide⟩,⟨410644, by decide⟩,⟨410666, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1757_410667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1757 ⟨410667, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1757
    ⟨410667, by decide⟩ (by decide) (![⟨410610, by decide⟩,⟨410626, by decide⟩,⟨410644, by decide⟩,⟨410666, by decide⟩]) unmarked_context_10_1757_410667 node_context_10_1757_410667
  intro a
  fin_cases a
  · exact context_11_7028_410610
  · exact context_11_7029_410626
  · exact context_11_7030_410644
  · exact context_11_7031_410666

theorem selected_cut_16122 : selected 10 ⟨410683, by decide⟩
    (prefixPartial 11 7032) = some ⟨11, 2, 0, 410683, 7032, 1773, 262144⟩ := by
  decide +kernel

theorem context_11_7032_410683 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7032 ⟨410683, by decide⟩ :=
  accepted_of_selected 11 7032 ⟨410683, by decide⟩ ⟨11, 2, 0, 410683, 7032, 1773, 262144⟩
    (by decide) selected_cut_16122

theorem selected_cut_16123 : selected 10 ⟨410697, by decide⟩
    (prefixPartial 11 7033) = some ⟨11, 2, 0, 410697, 7033, 1405, 262144⟩ := by
  decide +kernel

theorem context_11_7033_410697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7033 ⟨410697, by decide⟩ :=
  accepted_of_selected 11 7033 ⟨410697, by decide⟩ ⟨11, 2, 0, 410697, 7033, 1405, 262144⟩
    (by decide) selected_cut_16123

theorem selected_cut_16124 : selected 10 ⟨410712, by decide⟩
    (prefixPartial 11 7034) = some ⟨11, 2, 0, 410712, 7034, 1181, 262144⟩ := by
  decide +kernel

theorem context_11_7034_410712 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7034 ⟨410712, by decide⟩ :=
  accepted_of_selected 11 7034 ⟨410712, by decide⟩ ⟨11, 2, 0, 410712, 7034, 1181, 262144⟩
    (by decide) selected_cut_16124

theorem selected_cut_16125 : selected 10 ⟨410721, by decide⟩
    (prefixPartial 11 7035) = some ⟨11, 2, 0, 410721, 7035, 897, 262144⟩ := by
  decide +kernel

theorem context_11_7035_410721 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7035 ⟨410721, by decide⟩ :=
  accepted_of_selected 11 7035 ⟨410721, by decide⟩ ⟨11, 2, 0, 410721, 7035, 897, 262144⟩
    (by decide) selected_cut_16125

theorem unmarked_context_10_1758_410722 : frontier 11 ⟨410722, by decide⟩
    (prefixCache 10 1758) (prefixPartial 10 1758) = false := by
  decide +kernel

theorem node_context_10_1758_410722 : EJMOriginalGlobalDAGData.nodes 11 ⟨410722, by decide⟩ =
    .split (coordinate 10) (![⟨410683, by decide⟩,⟨410697, by decide⟩,⟨410712, by decide⟩,⟨410721, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1758_410722 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1758 ⟨410722, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1758
    ⟨410722, by decide⟩ (by decide) (![⟨410683, by decide⟩,⟨410697, by decide⟩,⟨410712, by decide⟩,⟨410721, by decide⟩]) unmarked_context_10_1758_410722 node_context_10_1758_410722
  intro a
  fin_cases a
  · exact context_11_7032_410683
  · exact context_11_7033_410697
  · exact context_11_7034_410712
  · exact context_11_7035_410721

theorem selected_cut_16126 : selected 11 ⟨410766, by decide⟩
    (prefixPartial 10 1759) = some ⟨10, 2, 0, 410766, 1759, 1385, 1048576⟩ := by
  decide +kernel

theorem context_10_1759_410766 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1759 ⟨410766, by decide⟩ :=
  accepted_of_selected 10 1759 ⟨410766, by decide⟩ ⟨10, 2, 0, 410766, 1759, 1385, 1048576⟩
    (by decide) selected_cut_16126

theorem unmarked_context_9_439_410767 : frontier 12 ⟨410767, by decide⟩
    (prefixCache 9 439) (prefixPartial 9 439) = false := by
  decide +kernel

theorem node_context_9_439_410767 : EJMOriginalGlobalDAGData.nodes 12 ⟨410767, by decide⟩ =
    .split (coordinate 9) (![⟨410581, by decide⟩,⟨410667, by decide⟩,⟨410722, by decide⟩,⟨410766, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_439_410767 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 439 ⟨410767, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 439
    ⟨410767, by decide⟩ (by decide) (![⟨410581, by decide⟩,⟨410667, by decide⟩,⟨410722, by decide⟩,⟨410766, by decide⟩]) unmarked_context_9_439_410767 node_context_9_439_410767
  intro a
  fin_cases a
  · exact context_10_1756_410581
  · exact context_10_1757_410667
  · exact context_10_1758_410722
  · exact context_10_1759_410766

theorem unmarked_context_8_109_410768 : frontier 13 ⟨410768, by decide⟩
    (prefixCache 8 109) (prefixPartial 8 109) = false := by
  decide +kernel

theorem node_context_8_109_410768 : EJMOriginalGlobalDAGData.nodes 13 ⟨410768, by decide⟩ =
    .split (coordinate 8) (![⟨405548, by decide⟩,⟨408933, by decide⟩,⟨410459, by decide⟩,⟨410767, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_109_410768 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 109 ⟨410768, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 109
    ⟨410768, by decide⟩ (by decide) (![⟨405548, by decide⟩,⟨408933, by decide⟩,⟨410459, by decide⟩,⟨410767, by decide⟩]) unmarked_context_8_109_410768 node_context_8_109_410768
  intro a
  fin_cases a
  · exact context_9_436_405548
  · exact context_9_437_408933
  · exact context_9_438_410459
  · exact context_9_439_410767

theorem selected_cut_16127 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 28160) = some ⟨12, 1, 0, 34034, 28160, 1, 65536⟩ := by
  decide +kernel

theorem context_12_28160_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28160 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 28160 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 28160, 1, 65536⟩
    (by decide) selected_cut_16127

theorem selected_cut_16128 : selected 9 ⟨388829, by decide⟩
    (prefixPartial 12 28161) = some ⟨12, 1, 0, 388829, 28161, 1, 65536⟩ := by
  decide +kernel

theorem context_12_28161_388829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28161 ⟨388829, by decide⟩ :=
  accepted_of_selected 12 28161 ⟨388829, by decide⟩ ⟨12, 1, 0, 388829, 28161, 1, 65536⟩
    (by decide) selected_cut_16128

theorem selected_cut_16129 : selected 8 ⟨410838, by decide⟩
    (prefixPartial 13 112648) = some ⟨13, 2, 0, 410838, 112648, 3033, 16384⟩ := by
  decide +kernel

theorem context_13_112648_410838 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112648 ⟨410838, by decide⟩ :=
  accepted_of_selected 13 112648 ⟨410838, by decide⟩ ⟨13, 2, 0, 410838, 112648, 3033, 16384⟩
    (by decide) selected_cut_16129

theorem selected_cut_16130 : selected 8 ⟨410903, by decide⟩
    (prefixPartial 13 112649) = some ⟨13, 2, 0, 410903, 112649, 1753, 16384⟩ := by
  decide +kernel

theorem context_13_112649_410903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112649 ⟨410903, by decide⟩ :=
  accepted_of_selected 13 112649 ⟨410903, by decide⟩ ⟨13, 2, 0, 410903, 112649, 1753, 16384⟩
    (by decide) selected_cut_16130

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
