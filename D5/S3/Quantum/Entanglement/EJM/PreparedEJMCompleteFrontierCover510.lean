/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover509
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_48963 : selected 10 ⟨1380866, by decide⟩
    (prefixPartial 11 101217) = some ⟨11, 2, 0, 1380866, 101217, 1773, 262144⟩ := by
  decide +kernel

theorem context_11_101217_1380866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101217 ⟨1380866, by decide⟩ :=
  accepted_of_selected 11 101217 ⟨1380866, by decide⟩ ⟨11, 2, 0, 1380866, 101217, 1773, 262144⟩
    (by decide) selected_cut_48963

theorem selected_cut_48964 : selected 10 ⟨1380901, by decide⟩
    (prefixPartial 11 101218) = some ⟨11, 2, 0, 1380901, 101218, 2481, 262144⟩ := by
  decide +kernel

theorem context_11_101218_1380901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101218 ⟨1380901, by decide⟩ :=
  accepted_of_selected 11 101218 ⟨1380901, by decide⟩ ⟨11, 2, 0, 1380901, 101218, 2481, 262144⟩
    (by decide) selected_cut_48964

theorem selected_cut_48965 : selected 10 ⟨1380939, by decide⟩
    (prefixPartial 11 101219) = some ⟨11, 2, 0, 1380939, 101219, 2249, 262144⟩ := by
  decide +kernel

theorem context_11_101219_1380939 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101219 ⟨1380939, by decide⟩ :=
  accepted_of_selected 11 101219 ⟨1380939, by decide⟩ ⟨11, 2, 0, 1380939, 101219, 2249, 262144⟩
    (by decide) selected_cut_48965

theorem unmarked_context_10_25304_1380940 : frontier 11 ⟨1380940, by decide⟩
    (prefixCache 10 25304) (prefixPartial 10 25304) = false := by
  decide +kernel

theorem node_context_10_25304_1380940 : EJMOriginalGlobalDAGData.nodes 11 ⟨1380940, by decide⟩ =
    .split (coordinate 10) (![⟨1380832, by decide⟩,⟨1380866, by decide⟩,⟨1380901, by decide⟩,⟨1380939, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25304_1380940 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25304 ⟨1380940, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25304
    ⟨1380940, by decide⟩ (by decide) (![⟨1380832, by decide⟩,⟨1380866, by decide⟩,⟨1380901, by decide⟩,⟨1380939, by decide⟩]) unmarked_context_10_25304_1380940 node_context_10_25304_1380940
  intro a
  fin_cases a
  · exact context_11_101216_1380832
  · exact context_11_101217_1380866
  · exact context_11_101218_1380901
  · exact context_11_101219_1380939

theorem selected_cut_48966 : selected 10 ⟨1380986, by decide⟩
    (prefixPartial 11 101220) = some ⟨11, 2, 0, 1380986, 101220, 1581, 262144⟩ := by
  decide +kernel

theorem context_11_101220_1380986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101220 ⟨1380986, by decide⟩ :=
  accepted_of_selected 11 101220 ⟨1380986, by decide⟩ ⟨11, 2, 0, 1380986, 101220, 1581, 262144⟩
    (by decide) selected_cut_48966

theorem selected_cut_48967 : selected 10 ⟨1381003, by decide⟩
    (prefixPartial 11 101221) = some ⟨11, 2, 0, 1381003, 101221, 621, 262144⟩ := by
  decide +kernel

theorem context_11_101221_1381003 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101221 ⟨1381003, by decide⟩ :=
  accepted_of_selected 11 101221 ⟨1381003, by decide⟩ ⟨11, 2, 0, 1381003, 101221, 621, 262144⟩
    (by decide) selected_cut_48967

theorem selected_cut_48968 : selected 10 ⟨1381034, by decide⟩
    (prefixPartial 11 101222) = some ⟨11, 2, 0, 1381034, 101222, 1877, 262144⟩ := by
  decide +kernel

theorem context_11_101222_1381034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101222 ⟨1381034, by decide⟩ :=
  accepted_of_selected 11 101222 ⟨1381034, by decide⟩ ⟨11, 2, 0, 1381034, 101222, 1877, 262144⟩
    (by decide) selected_cut_48968

theorem selected_cut_48969 : selected 10 ⟨1381067, by decide⟩
    (prefixPartial 11 101223) = some ⟨11, 2, 0, 1381067, 101223, 1609, 262144⟩ := by
  decide +kernel

theorem context_11_101223_1381067 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101223 ⟨1381067, by decide⟩ :=
  accepted_of_selected 11 101223 ⟨1381067, by decide⟩ ⟨11, 2, 0, 1381067, 101223, 1609, 262144⟩
    (by decide) selected_cut_48969

theorem unmarked_context_10_25305_1381068 : frontier 11 ⟨1381068, by decide⟩
    (prefixCache 10 25305) (prefixPartial 10 25305) = false := by
  decide +kernel

theorem node_context_10_25305_1381068 : EJMOriginalGlobalDAGData.nodes 11 ⟨1381068, by decide⟩ =
    .split (coordinate 10) (![⟨1380986, by decide⟩,⟨1381003, by decide⟩,⟨1381034, by decide⟩,⟨1381067, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25305_1381068 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25305 ⟨1381068, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25305
    ⟨1381068, by decide⟩ (by decide) (![⟨1380986, by decide⟩,⟨1381003, by decide⟩,⟨1381034, by decide⟩,⟨1381067, by decide⟩]) unmarked_context_10_25305_1381068 node_context_10_25305_1381068
  intro a
  fin_cases a
  · exact context_11_101220_1380986
  · exact context_11_101221_1381003
  · exact context_11_101222_1381034
  · exact context_11_101223_1381067

theorem selected_cut_48970 : selected 11 ⟨1381116, by decide⟩
    (prefixPartial 10 25306) = some ⟨10, 2, 0, 1381116, 25306, 1405, 1048576⟩ := by
  decide +kernel

theorem context_10_25306_1381116 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25306 ⟨1381116, by decide⟩ :=
  accepted_of_selected 10 25306 ⟨1381116, by decide⟩ ⟨10, 2, 0, 1381116, 25306, 1405, 1048576⟩
    (by decide) selected_cut_48970

theorem selected_cut_48971 : selected 11 ⟨1381201, by decide⟩
    (prefixPartial 10 25307) = some ⟨10, 2, 0, 1381201, 25307, 3665, 1048576⟩ := by
  decide +kernel

theorem context_10_25307_1381201 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25307 ⟨1381201, by decide⟩ :=
  accepted_of_selected 10 25307 ⟨1381201, by decide⟩ ⟨10, 2, 0, 1381201, 25307, 3665, 1048576⟩
    (by decide) selected_cut_48971

theorem unmarked_context_9_6326_1381202 : frontier 12 ⟨1381202, by decide⟩
    (prefixCache 9 6326) (prefixPartial 9 6326) = false := by
  decide +kernel

theorem node_context_9_6326_1381202 : EJMOriginalGlobalDAGData.nodes 12 ⟨1381202, by decide⟩ =
    .split (coordinate 9) (![⟨1380940, by decide⟩,⟨1381068, by decide⟩,⟨1381116, by decide⟩,⟨1381201, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6326_1381202 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6326 ⟨1381202, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6326
    ⟨1381202, by decide⟩ (by decide) (![⟨1380940, by decide⟩,⟨1381068, by decide⟩,⟨1381116, by decide⟩,⟨1381201, by decide⟩]) unmarked_context_9_6326_1381202 node_context_9_6326_1381202
  intro a
  fin_cases a
  · exact context_10_25304_1380940
  · exact context_10_25305_1381068
  · exact context_10_25306_1381116
  · exact context_10_25307_1381201

theorem selected_cut_48972 : selected 11 ⟨1381257, by decide⟩
    (prefixPartial 10 25308) = some ⟨10, 2, 0, 1381257, 25308, 2469, 1048576⟩ := by
  decide +kernel

theorem context_10_25308_1381257 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25308 ⟨1381257, by decide⟩ :=
  accepted_of_selected 10 25308 ⟨1381257, by decide⟩ ⟨10, 2, 0, 1381257, 25308, 2469, 1048576⟩
    (by decide) selected_cut_48972

theorem selected_cut_48973 : selected 11 ⟨1381305, by decide⟩
    (prefixPartial 10 25309) = some ⟨10, 2, 0, 1381305, 25309, 1733, 1048576⟩ := by
  decide +kernel

theorem context_10_25309_1381305 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25309 ⟨1381305, by decide⟩ :=
  accepted_of_selected 10 25309 ⟨1381305, by decide⟩ ⟨10, 2, 0, 1381305, 25309, 1733, 1048576⟩
    (by decide) selected_cut_48973

theorem selected_cut_48974 : selected 11 ⟨1381345, by decide⟩
    (prefixPartial 10 25310) = some ⟨10, 2, 0, 1381345, 25310, 993, 1048576⟩ := by
  decide +kernel

theorem context_10_25310_1381345 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25310 ⟨1381345, by decide⟩ :=
  accepted_of_selected 10 25310 ⟨1381345, by decide⟩ ⟨10, 2, 0, 1381345, 25310, 993, 1048576⟩
    (by decide) selected_cut_48974

theorem selected_cut_48975 : selected 11 ⟨1381354, by decide⟩
    (prefixPartial 10 25311) = some ⟨10, 2, 0, 1381354, 25311, 77, 1048576⟩ := by
  decide +kernel

theorem context_10_25311_1381354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25311 ⟨1381354, by decide⟩ :=
  accepted_of_selected 10 25311 ⟨1381354, by decide⟩ ⟨10, 2, 0, 1381354, 25311, 77, 1048576⟩
    (by decide) selected_cut_48975

theorem unmarked_context_9_6327_1381355 : frontier 12 ⟨1381355, by decide⟩
    (prefixCache 9 6327) (prefixPartial 9 6327) = false := by
  decide +kernel

theorem node_context_9_6327_1381355 : EJMOriginalGlobalDAGData.nodes 12 ⟨1381355, by decide⟩ =
    .split (coordinate 9) (![⟨1381257, by decide⟩,⟨1381305, by decide⟩,⟨1381345, by decide⟩,⟨1381354, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6327_1381355 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6327 ⟨1381355, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6327
    ⟨1381355, by decide⟩ (by decide) (![⟨1381257, by decide⟩,⟨1381305, by decide⟩,⟨1381345, by decide⟩,⟨1381354, by decide⟩]) unmarked_context_9_6327_1381355 node_context_9_6327_1381355
  intro a
  fin_cases a
  · exact context_10_25308_1381257
  · exact context_10_25309_1381305
  · exact context_10_25310_1381345
  · exact context_10_25311_1381354

theorem unmarked_context_8_1581_1381356 : frontier 13 ⟨1381356, by decide⟩
    (prefixCache 8 1581) (prefixPartial 8 1581) = false := by
  decide +kernel

theorem node_context_8_1581_1381356 : EJMOriginalGlobalDAGData.nodes 13 ⟨1381356, by decide⟩ =
    .split (coordinate 8) (![⟨1380114, by decide⟩,⟨1380798, by decide⟩,⟨1381202, by decide⟩,⟨1381355, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1581_1381356 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1581 ⟨1381356, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1581
    ⟨1381356, by decide⟩ (by decide) (![⟨1380114, by decide⟩,⟨1380798, by decide⟩,⟨1381202, by decide⟩,⟨1381355, by decide⟩]) unmarked_context_8_1581_1381356 node_context_8_1581_1381356
  intro a
  fin_cases a
  · exact context_9_6324_1380114
  · exact context_9_6325_1380798
  · exact context_9_6326_1381202
  · exact context_9_6327_1381355

theorem selected_cut_48976 : selected 13 ⟨1366235, by decide⟩
    (prefixPartial 8 1582) = some ⟨8, 1, 0, 1366235, 1582, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_1582_1366235 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1582 ⟨1366235, by decide⟩ :=
  accepted_of_selected 8 1582 ⟨1366235, by decide⟩ ⟨8, 1, 0, 1366235, 1582, 1, 16777216⟩
    (by decide) selected_cut_48976

theorem selected_cut_48977 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 101312) = some ⟨11, 1, 0, 434745, 101312, 1, 262144⟩ := by
  decide +kernel

theorem context_11_101312_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101312 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 101312 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 101312, 1, 262144⟩
    (by decide) selected_cut_48977

theorem selected_cut_48978 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 101313) = some ⟨11, 1, 0, 434745, 101313, 1, 262144⟩ := by
  decide +kernel

theorem context_11_101313_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101313 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 101313 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 101313, 1, 262144⟩
    (by decide) selected_cut_48978

theorem selected_cut_48979 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 405256) = some ⟨12, 1, 0, 448748, 405256, 1, 65536⟩ := by
  decide +kernel

theorem context_12_405256_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 405256 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 405256 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 405256, 1, 65536⟩
    (by decide) selected_cut_48979

theorem selected_cut_48980 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 405257) = some ⟨12, 1, 0, 448748, 405257, 1, 65536⟩ := by
  decide +kernel

theorem context_12_405257_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 405257 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 405257 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 405257, 1, 65536⟩
    (by decide) selected_cut_48980

theorem selected_cut_48981 : selected 9 ⟨1381433, by decide⟩
    (prefixPartial 12 405258) = some ⟨12, 2, 0, 1381433, 405258, 2361, 65536⟩ := by
  decide +kernel

theorem context_12_405258_1381433 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 405258 ⟨1381433, by decide⟩ :=
  accepted_of_selected 12 405258 ⟨1381433, by decide⟩ ⟨12, 2, 0, 1381433, 405258, 2361, 65536⟩
    (by decide) selected_cut_48981

theorem selected_cut_48982 : selected 9 ⟨1381493, by decide⟩
    (prefixPartial 12 405259) = some ⟨12, 2, 0, 1381493, 405259, 2381, 65536⟩ := by
  decide +kernel

theorem context_12_405259_1381493 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 405259 ⟨1381493, by decide⟩ :=
  accepted_of_selected 12 405259 ⟨1381493, by decide⟩ ⟨12, 2, 0, 1381493, 405259, 2381, 65536⟩
    (by decide) selected_cut_48982

theorem unmarked_context_11_101314_1381494 : frontier 10 ⟨1381494, by decide⟩
    (prefixCache 11 101314) (prefixPartial 11 101314) = false := by
  decide +kernel

theorem node_context_11_101314_1381494 : EJMOriginalGlobalDAGData.nodes 10 ⟨1381494, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨448748, by decide⟩,⟨1381433, by decide⟩,⟨1381493, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_101314_1381494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101314 ⟨1381494, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 101314
    ⟨1381494, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨448748, by decide⟩,⟨1381433, by decide⟩,⟨1381493, by decide⟩]) unmarked_context_11_101314_1381494 node_context_11_101314_1381494
  intro a
  fin_cases a
  · exact context_12_405256_448748
  · exact context_12_405257_448748
  · exact context_12_405258_1381433
  · exact context_12_405259_1381493

theorem selected_cut_48983 : selected 10 ⟨1381551, by decide⟩
    (prefixPartial 11 101315) = some ⟨11, 2, 0, 1381551, 101315, 2349, 262144⟩ := by
  decide +kernel

theorem context_11_101315_1381551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101315 ⟨1381551, by decide⟩ :=
  accepted_of_selected 11 101315 ⟨1381551, by decide⟩ ⟨11, 2, 0, 1381551, 101315, 2349, 262144⟩
    (by decide) selected_cut_48983

theorem unmarked_context_10_25328_1381552 : frontier 11 ⟨1381552, by decide⟩
    (prefixCache 10 25328) (prefixPartial 10 25328) = false := by
  decide +kernel

theorem node_context_10_25328_1381552 : EJMOriginalGlobalDAGData.nodes 11 ⟨1381552, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨434745, by decide⟩,⟨1381494, by decide⟩,⟨1381551, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25328_1381552 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25328 ⟨1381552, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25328
    ⟨1381552, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨434745, by decide⟩,⟨1381494, by decide⟩,⟨1381551, by decide⟩]) unmarked_context_10_25328_1381552 node_context_10_25328_1381552
  intro a
  fin_cases a
  · exact context_11_101312_434745
  · exact context_11_101313_434745
  · exact context_11_101314_1381494
  · exact context_11_101315_1381551

theorem selected_cut_48984 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 405264) = some ⟨12, 1, 0, 1108174, 405264, 1, 65536⟩ := by
  decide +kernel

theorem context_12_405264_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 405264 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 405264 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 405264, 1, 65536⟩
    (by decide) selected_cut_48984

theorem selected_cut_48985 : selected 9 ⟨1381658, by decide⟩
    (prefixPartial 12 405265) = some ⟨12, 2, 0, 1381658, 405265, 3013, 65536⟩ := by
  decide +kernel

theorem context_12_405265_1381658 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 405265 ⟨1381658, by decide⟩ :=
  accepted_of_selected 12 405265 ⟨1381658, by decide⟩ ⟨12, 2, 0, 1381658, 405265, 3013, 65536⟩
    (by decide) selected_cut_48985

theorem selected_cut_48986 : selected 9 ⟨1381742, by decide⟩
    (prefixPartial 12 405266) = some ⟨12, 2, 0, 1381742, 405266, 2865, 65536⟩ := by
  decide +kernel

theorem context_12_405266_1381742 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 405266 ⟨1381742, by decide⟩ :=
  accepted_of_selected 12 405266 ⟨1381742, by decide⟩ ⟨12, 2, 0, 1381742, 405266, 2865, 65536⟩
    (by decide) selected_cut_48986

theorem selected_cut_48987 : selected 9 ⟨1381827, by decide⟩
    (prefixPartial 12 405267) = some ⟨12, 2, 0, 1381827, 405267, 3085, 65536⟩ := by
  decide +kernel

theorem context_12_405267_1381827 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 405267 ⟨1381827, by decide⟩ :=
  accepted_of_selected 12 405267 ⟨1381827, by decide⟩ ⟨12, 2, 0, 1381827, 405267, 3085, 65536⟩
    (by decide) selected_cut_48987

theorem unmarked_context_11_101316_1381828 : frontier 10 ⟨1381828, by decide⟩
    (prefixCache 11 101316) (prefixPartial 11 101316) = false := by
  decide +kernel

theorem node_context_11_101316_1381828 : EJMOriginalGlobalDAGData.nodes 10 ⟨1381828, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1381658, by decide⟩,⟨1381742, by decide⟩,⟨1381827, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_101316_1381828 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101316 ⟨1381828, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 101316
    ⟨1381828, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1381658, by decide⟩,⟨1381742, by decide⟩,⟨1381827, by decide⟩]) unmarked_context_11_101316_1381828 node_context_11_101316_1381828
  intro a
  fin_cases a
  · exact context_12_405264_1108174
  · exact context_12_405265_1381658
  · exact context_12_405266_1381742
  · exact context_12_405267_1381827

theorem selected_cut_48988 : selected 10 ⟨1381903, by decide⟩
    (prefixPartial 11 101317) = some ⟨11, 2, 0, 1381903, 101317, 2729, 262144⟩ := by
  decide +kernel

theorem context_11_101317_1381903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101317 ⟨1381903, by decide⟩ :=
  accepted_of_selected 11 101317 ⟨1381903, by decide⟩ ⟨11, 2, 0, 1381903, 101317, 2729, 262144⟩
    (by decide) selected_cut_48988

theorem selected_cut_48989 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 405272) = some ⟨12, 1, 0, 1108174, 405272, 1, 65536⟩ := by
  decide +kernel

theorem context_12_405272_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 405272 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 405272 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 405272, 1, 65536⟩
    (by decide) selected_cut_48989

theorem selected_cut_48990 : selected 9 ⟨1381976, by decide⟩
    (prefixPartial 12 405273) = some ⟨12, 2, 0, 1381976, 405273, 2389, 65536⟩ := by
  decide +kernel

theorem context_12_405273_1381976 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 405273 ⟨1381976, by decide⟩ :=
  accepted_of_selected 12 405273 ⟨1381976, by decide⟩ ⟨12, 2, 0, 1381976, 405273, 2389, 65536⟩
    (by decide) selected_cut_48990

theorem selected_cut_48991 : selected 9 ⟨1382034, by decide⟩
    (prefixPartial 12 405274) = some ⟨12, 2, 0, 1382034, 405274, 2313, 65536⟩ := by
  decide +kernel

theorem context_12_405274_1382034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 405274 ⟨1382034, by decide⟩ :=
  accepted_of_selected 12 405274 ⟨1382034, by decide⟩ ⟨12, 2, 0, 1382034, 405274, 2313, 65536⟩
    (by decide) selected_cut_48991

theorem selected_cut_48992 : selected 9 ⟨1382094, by decide⟩
    (prefixPartial 12 405275) = some ⟨12, 2, 0, 1382094, 405275, 2449, 65536⟩ := by
  decide +kernel

theorem context_12_405275_1382094 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 405275 ⟨1382094, by decide⟩ :=
  accepted_of_selected 12 405275 ⟨1382094, by decide⟩ ⟨12, 2, 0, 1382094, 405275, 2449, 65536⟩
    (by decide) selected_cut_48992

theorem unmarked_context_11_101318_1382095 : frontier 10 ⟨1382095, by decide⟩
    (prefixCache 11 101318) (prefixPartial 11 101318) = false := by
  decide +kernel

theorem node_context_11_101318_1382095 : EJMOriginalGlobalDAGData.nodes 10 ⟨1382095, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1381976, by decide⟩,⟨1382034, by decide⟩,⟨1382094, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_101318_1382095 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101318 ⟨1382095, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 101318
    ⟨1382095, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1381976, by decide⟩,⟨1382034, by decide⟩,⟨1382094, by decide⟩]) unmarked_context_11_101318_1382095 node_context_11_101318_1382095
  intro a
  fin_cases a
  · exact context_12_405272_1108174
  · exact context_12_405273_1381976
  · exact context_12_405274_1382034
  · exact context_12_405275_1382094

theorem selected_cut_48993 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 405276) = some ⟨12, 1, 0, 1108174, 405276, 1, 65536⟩ := by
  decide +kernel

theorem context_12_405276_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 405276 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 405276 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 405276, 1, 65536⟩
    (by decide) selected_cut_48993

theorem selected_cut_48994 : selected 9 ⟨1382157, by decide⟩
    (prefixPartial 12 405277) = some ⟨12, 2, 0, 1382157, 405277, 2229, 65536⟩ := by
  decide +kernel

theorem context_12_405277_1382157 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 405277 ⟨1382157, by decide⟩ :=
  accepted_of_selected 12 405277 ⟨1382157, by decide⟩ ⟨12, 2, 0, 1382157, 405277, 2229, 65536⟩
    (by decide) selected_cut_48994

theorem selected_cut_48995 : selected 9 ⟨1382214, by decide⟩
    (prefixPartial 12 405278) = some ⟨12, 2, 0, 1382214, 405278, 2329, 65536⟩ := by
  decide +kernel

theorem context_12_405278_1382214 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 405278 ⟨1382214, by decide⟩ :=
  accepted_of_selected 12 405278 ⟨1382214, by decide⟩ ⟨12, 2, 0, 1382214, 405278, 2329, 65536⟩
    (by decide) selected_cut_48995

theorem selected_cut_48996 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 405279) = some ⟨12, 1, 0, 903806, 405279, 1, 65536⟩ := by
  decide +kernel

theorem context_12_405279_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 405279 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 405279 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 405279, 1, 65536⟩
    (by decide) selected_cut_48996

theorem unmarked_context_11_101319_1382215 : frontier 10 ⟨1382215, by decide⟩
    (prefixCache 11 101319) (prefixPartial 11 101319) = false := by
  decide +kernel

theorem node_context_11_101319_1382215 : EJMOriginalGlobalDAGData.nodes 10 ⟨1382215, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1382157, by decide⟩,⟨1382214, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_101319_1382215 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101319 ⟨1382215, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 101319
    ⟨1382215, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1382157, by decide⟩,⟨1382214, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_101319_1382215 node_context_11_101319_1382215
  intro a
  fin_cases a
  · exact context_12_405276_1108174
  · exact context_12_405277_1382157
  · exact context_12_405278_1382214
  · exact context_12_405279_903806

theorem unmarked_context_10_25329_1382216 : frontier 11 ⟨1382216, by decide⟩
    (prefixCache 10 25329) (prefixPartial 10 25329) = false := by
  decide +kernel

theorem node_context_10_25329_1382216 : EJMOriginalGlobalDAGData.nodes 11 ⟨1382216, by decide⟩ =
    .split (coordinate 10) (![⟨1381828, by decide⟩,⟨1381903, by decide⟩,⟨1382095, by decide⟩,⟨1382215, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25329_1382216 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25329 ⟨1382216, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25329
    ⟨1382216, by decide⟩ (by decide) (![⟨1381828, by decide⟩,⟨1381903, by decide⟩,⟨1382095, by decide⟩,⟨1382215, by decide⟩]) unmarked_context_10_25329_1382216 node_context_10_25329_1382216
  intro a
  fin_cases a
  · exact context_11_101316_1381828
  · exact context_11_101317_1381903
  · exact context_11_101318_1382095
  · exact context_11_101319_1382215

theorem selected_cut_48997 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 405280) = some ⟨12, 1, 0, 1108174, 405280, 1, 65536⟩ := by
  decide +kernel

theorem context_12_405280_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 405280 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 405280 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 405280, 1, 65536⟩
    (by decide) selected_cut_48997

theorem selected_cut_48998 : selected 9 ⟨1382286, by decide⟩
    (prefixPartial 12 405281) = some ⟨12, 2, 0, 1382286, 405281, 2593, 65536⟩ := by
  decide +kernel

theorem context_12_405281_1382286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 405281 ⟨1382286, by decide⟩ :=
  accepted_of_selected 12 405281 ⟨1382286, by decide⟩ ⟨12, 2, 0, 1382286, 405281, 2593, 65536⟩
    (by decide) selected_cut_48998

theorem selected_cut_48999 : selected 9 ⟨1382342, by decide⟩
    (prefixPartial 12 405282) = some ⟨12, 2, 0, 1382342, 405282, 2357, 65536⟩ := by
  decide +kernel

theorem context_12_405282_1382342 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 405282 ⟨1382342, by decide⟩ :=
  accepted_of_selected 12 405282 ⟨1382342, by decide⟩ ⟨12, 2, 0, 1382342, 405282, 2357, 65536⟩
    (by decide) selected_cut_48999

theorem selected_cut_49000 : selected 9 ⟨1382408, by decide⟩
    (prefixPartial 12 405283) = some ⟨12, 2, 0, 1382408, 405283, 2517, 65536⟩ := by
  decide +kernel

theorem context_12_405283_1382408 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 405283 ⟨1382408, by decide⟩ :=
  accepted_of_selected 12 405283 ⟨1382408, by decide⟩ ⟨12, 2, 0, 1382408, 405283, 2517, 65536⟩
    (by decide) selected_cut_49000

theorem unmarked_context_11_101320_1382409 : frontier 10 ⟨1382409, by decide⟩
    (prefixCache 11 101320) (prefixPartial 11 101320) = false := by
  decide +kernel

theorem node_context_11_101320_1382409 : EJMOriginalGlobalDAGData.nodes 10 ⟨1382409, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1382286, by decide⟩,⟨1382342, by decide⟩,⟨1382408, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_101320_1382409 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101320 ⟨1382409, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 101320
    ⟨1382409, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1382286, by decide⟩,⟨1382342, by decide⟩,⟨1382408, by decide⟩]) unmarked_context_11_101320_1382409 node_context_11_101320_1382409
  intro a
  fin_cases a
  · exact context_12_405280_1108174
  · exact context_12_405281_1382286
  · exact context_12_405282_1382342
  · exact context_12_405283_1382408

theorem selected_cut_49001 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 405284) = some ⟨12, 1, 0, 1108174, 405284, 1, 65536⟩ := by
  decide +kernel

theorem context_12_405284_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 405284 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 405284 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 405284, 1, 65536⟩
    (by decide) selected_cut_49001

theorem selected_cut_49002 : selected 9 ⟨1382464, by decide⟩
    (prefixPartial 12 405285) = some ⟨12, 2, 0, 1382464, 405285, 2117, 65536⟩ := by
  decide +kernel

theorem context_12_405285_1382464 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 405285 ⟨1382464, by decide⟩ :=
  accepted_of_selected 12 405285 ⟨1382464, by decide⟩ ⟨12, 2, 0, 1382464, 405285, 2117, 65536⟩
    (by decide) selected_cut_49002

theorem selected_cut_49003 : selected 9 ⟨1382517, by decide⟩
    (prefixPartial 12 405286) = some ⟨12, 2, 0, 1382517, 405286, 1977, 65536⟩ := by
  decide +kernel

theorem context_12_405286_1382517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 405286 ⟨1382517, by decide⟩ :=
  accepted_of_selected 12 405286 ⟨1382517, by decide⟩ ⟨12, 2, 0, 1382517, 405286, 1977, 65536⟩
    (by decide) selected_cut_49003

theorem selected_cut_49004 : selected 9 ⟨1382565, by decide⟩
    (prefixPartial 12 405287) = some ⟨12, 2, 0, 1382565, 405287, 2053, 65536⟩ := by
  decide +kernel

theorem context_12_405287_1382565 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 405287 ⟨1382565, by decide⟩ :=
  accepted_of_selected 12 405287 ⟨1382565, by decide⟩ ⟨12, 2, 0, 1382565, 405287, 2053, 65536⟩
    (by decide) selected_cut_49004

theorem unmarked_context_11_101321_1382566 : frontier 10 ⟨1382566, by decide⟩
    (prefixCache 11 101321) (prefixPartial 11 101321) = false := by
  decide +kernel

theorem node_context_11_101321_1382566 : EJMOriginalGlobalDAGData.nodes 10 ⟨1382566, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1382464, by decide⟩,⟨1382517, by decide⟩,⟨1382565, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_101321_1382566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101321 ⟨1382566, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 101321
    ⟨1382566, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1382464, by decide⟩,⟨1382517, by decide⟩,⟨1382565, by decide⟩]) unmarked_context_11_101321_1382566 node_context_11_101321_1382566
  intro a
  fin_cases a
  · exact context_12_405284_1108174
  · exact context_12_405285_1382464
  · exact context_12_405286_1382517
  · exact context_12_405287_1382565

theorem selected_cut_49005 : selected 10 ⟨1382613, by decide⟩
    (prefixPartial 11 101322) = some ⟨11, 2, 0, 1382613, 101322, 2129, 262144⟩ := by
  decide +kernel

theorem context_11_101322_1382613 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101322 ⟨1382613, by decide⟩ :=
  accepted_of_selected 11 101322 ⟨1382613, by decide⟩ ⟨11, 2, 0, 1382613, 101322, 2129, 262144⟩
    (by decide) selected_cut_49005

theorem selected_cut_49006 : selected 10 ⟨1382689, by decide⟩
    (prefixPartial 11 101323) = some ⟨11, 2, 0, 1382689, 101323, 3625, 262144⟩ := by
  decide +kernel

theorem context_11_101323_1382689 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101323 ⟨1382689, by decide⟩ :=
  accepted_of_selected 11 101323 ⟨1382689, by decide⟩ ⟨11, 2, 0, 1382689, 101323, 3625, 262144⟩
    (by decide) selected_cut_49006

theorem unmarked_context_10_25330_1382690 : frontier 11 ⟨1382690, by decide⟩
    (prefixCache 10 25330) (prefixPartial 10 25330) = false := by
  decide +kernel

theorem node_context_10_25330_1382690 : EJMOriginalGlobalDAGData.nodes 11 ⟨1382690, by decide⟩ =
    .split (coordinate 10) (![⟨1382409, by decide⟩,⟨1382566, by decide⟩,⟨1382613, by decide⟩,⟨1382689, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25330_1382690 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25330 ⟨1382690, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25330
    ⟨1382690, by decide⟩ (by decide) (![⟨1382409, by decide⟩,⟨1382566, by decide⟩,⟨1382613, by decide⟩,⟨1382689, by decide⟩]) unmarked_context_10_25330_1382690 node_context_10_25330_1382690
  intro a
  fin_cases a
  · exact context_11_101320_1382409
  · exact context_11_101321_1382566
  · exact context_11_101322_1382613
  · exact context_11_101323_1382689

theorem selected_cut_49007 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 405296) = some ⟨12, 1, 0, 1108174, 405296, 1, 65536⟩ := by
  decide +kernel

theorem context_12_405296_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 405296 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 405296 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 405296, 1, 65536⟩
    (by decide) selected_cut_49007

theorem selected_cut_49008 : selected 9 ⟨1382758, by decide⟩
    (prefixPartial 12 405297) = some ⟨12, 2, 0, 1382758, 405297, 2265, 65536⟩ := by
  decide +kernel

theorem context_12_405297_1382758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 405297 ⟨1382758, by decide⟩ :=
  accepted_of_selected 12 405297 ⟨1382758, by decide⟩ ⟨12, 2, 0, 1382758, 405297, 2265, 65536⟩
    (by decide) selected_cut_49008

theorem selected_cut_49009 : selected 9 ⟨1382809, by decide⟩
    (prefixPartial 12 405298) = some ⟨12, 2, 0, 1382809, 405298, 2021, 65536⟩ := by
  decide +kernel

theorem context_12_405298_1382809 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 405298 ⟨1382809, by decide⟩ :=
  accepted_of_selected 12 405298 ⟨1382809, by decide⟩ ⟨12, 2, 0, 1382809, 405298, 2021, 65536⟩
    (by decide) selected_cut_49009

theorem selected_cut_49010 : selected 9 ⟨1382875, by decide⟩
    (prefixPartial 12 405299) = some ⟨12, 2, 0, 1382875, 405299, 2233, 65536⟩ := by
  decide +kernel

theorem context_12_405299_1382875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 405299 ⟨1382875, by decide⟩ :=
  accepted_of_selected 12 405299 ⟨1382875, by decide⟩ ⟨12, 2, 0, 1382875, 405299, 2233, 65536⟩
    (by decide) selected_cut_49010

theorem unmarked_context_11_101324_1382876 : frontier 10 ⟨1382876, by decide⟩
    (prefixCache 11 101324) (prefixPartial 11 101324) = false := by
  decide +kernel

theorem node_context_11_101324_1382876 : EJMOriginalGlobalDAGData.nodes 10 ⟨1382876, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1382758, by decide⟩,⟨1382809, by decide⟩,⟨1382875, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_101324_1382876 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101324 ⟨1382876, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 101324
    ⟨1382876, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1382758, by decide⟩,⟨1382809, by decide⟩,⟨1382875, by decide⟩]) unmarked_context_11_101324_1382876 node_context_11_101324_1382876
  intro a
  fin_cases a
  · exact context_12_405296_1108174
  · exact context_12_405297_1382758
  · exact context_12_405298_1382809
  · exact context_12_405299_1382875

theorem selected_cut_49011 : selected 10 ⟨1382967, by decide⟩
    (prefixPartial 11 101325) = some ⟨11, 2, 0, 1382967, 101325, 3605, 262144⟩ := by
  decide +kernel

theorem context_11_101325_1382967 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101325 ⟨1382967, by decide⟩ :=
  accepted_of_selected 11 101325 ⟨1382967, by decide⟩ ⟨11, 2, 0, 1382967, 101325, 3605, 262144⟩
    (by decide) selected_cut_49011

theorem selected_cut_49012 : selected 10 ⟨1383033, by decide⟩
    (prefixPartial 11 101326) = some ⟨11, 2, 0, 1383033, 101326, 3273, 262144⟩ := by
  decide +kernel

theorem context_11_101326_1383033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101326 ⟨1383033, by decide⟩ :=
  accepted_of_selected 11 101326 ⟨1383033, by decide⟩ ⟨11, 2, 0, 1383033, 101326, 3273, 262144⟩
    (by decide) selected_cut_49012

theorem selected_cut_49013 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 101327) = some ⟨11, 1, 0, 977886, 101327, 1, 262144⟩ := by
  decide +kernel

theorem context_11_101327_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101327 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 101327 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 101327, 1, 262144⟩
    (by decide) selected_cut_49013

theorem unmarked_context_10_25331_1383034 : frontier 11 ⟨1383034, by decide⟩
    (prefixCache 10 25331) (prefixPartial 10 25331) = false := by
  decide +kernel

theorem node_context_10_25331_1383034 : EJMOriginalGlobalDAGData.nodes 11 ⟨1383034, by decide⟩ =
    .split (coordinate 10) (![⟨1382876, by decide⟩,⟨1382967, by decide⟩,⟨1383033, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25331_1383034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25331 ⟨1383034, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25331
    ⟨1383034, by decide⟩ (by decide) (![⟨1382876, by decide⟩,⟨1382967, by decide⟩,⟨1383033, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_25331_1383034 node_context_10_25331_1383034
  intro a
  fin_cases a
  · exact context_11_101324_1382876
  · exact context_11_101325_1382967
  · exact context_11_101326_1383033
  · exact context_11_101327_977886

theorem unmarked_context_9_6332_1383035 : frontier 12 ⟨1383035, by decide⟩
    (prefixCache 9 6332) (prefixPartial 9 6332) = false := by
  decide +kernel

theorem node_context_9_6332_1383035 : EJMOriginalGlobalDAGData.nodes 12 ⟨1383035, by decide⟩ =
    .split (coordinate 9) (![⟨1381552, by decide⟩,⟨1382216, by decide⟩,⟨1382690, by decide⟩,⟨1383034, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6332_1383035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6332 ⟨1383035, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6332
    ⟨1383035, by decide⟩ (by decide) (![⟨1381552, by decide⟩,⟨1382216, by decide⟩,⟨1382690, by decide⟩,⟨1383034, by decide⟩]) unmarked_context_9_6332_1383035 node_context_9_6332_1383035
  intro a
  fin_cases a
  · exact context_10_25328_1381552
  · exact context_10_25329_1382216
  · exact context_10_25330_1382690
  · exact context_10_25331_1383034

theorem selected_cut_49014 : selected 10 ⟨1383082, by decide⟩
    (prefixPartial 11 101328) = some ⟨11, 2, 0, 1383082, 101328, 1889, 262144⟩ := by
  decide +kernel

theorem context_11_101328_1383082 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101328 ⟨1383082, by decide⟩ :=
  accepted_of_selected 11 101328 ⟨1383082, by decide⟩ ⟨11, 2, 0, 1383082, 101328, 1889, 262144⟩
    (by decide) selected_cut_49014

theorem selected_cut_49015 : selected 9 ⟨1383112, by decide⟩
    (prefixPartial 12 405316) = some ⟨12, 2, 0, 1383112, 405316, 1505, 65536⟩ := by
  decide +kernel

theorem context_12_405316_1383112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 405316 ⟨1383112, by decide⟩ :=
  accepted_of_selected 12 405316 ⟨1383112, by decide⟩ ⟨12, 2, 0, 1383112, 405316, 1505, 65536⟩
    (by decide) selected_cut_49015

theorem selected_cut_49016 : selected 9 ⟨642341, by decide⟩
    (prefixPartial 12 405317) = some ⟨12, 1, 0, 642341, 405317, 1, 65536⟩ := by
  decide +kernel

theorem context_12_405317_642341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 405317 ⟨642341, by decide⟩ :=
  accepted_of_selected 12 405317 ⟨642341, by decide⟩ ⟨12, 1, 0, 642341, 405317, 1, 65536⟩
    (by decide) selected_cut_49016

theorem selected_cut_49017 : selected 9 ⟨1383141, by decide⟩
    (prefixPartial 12 405318) = some ⟨12, 2, 0, 1383141, 405318, 1621, 65536⟩ := by
  decide +kernel

theorem context_12_405318_1383141 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 405318 ⟨1383141, by decide⟩ :=
  accepted_of_selected 12 405318 ⟨1383141, by decide⟩ ⟨12, 2, 0, 1383141, 405318, 1621, 65536⟩
    (by decide) selected_cut_49017

theorem selected_cut_49018 : selected 9 ⟨1383176, by decide⟩
    (prefixPartial 12 405319) = some ⟨12, 2, 0, 1383176, 405319, 1613, 65536⟩ := by
  decide +kernel

theorem context_12_405319_1383176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 405319 ⟨1383176, by decide⟩ :=
  accepted_of_selected 12 405319 ⟨1383176, by decide⟩ ⟨12, 2, 0, 1383176, 405319, 1613, 65536⟩
    (by decide) selected_cut_49018

theorem unmarked_context_11_101329_1383177 : frontier 10 ⟨1383177, by decide⟩
    (prefixCache 11 101329) (prefixPartial 11 101329) = false := by
  decide +kernel

theorem node_context_11_101329_1383177 : EJMOriginalGlobalDAGData.nodes 10 ⟨1383177, by decide⟩ =
    .split (coordinate 11) (![⟨1383112, by decide⟩,⟨642341, by decide⟩,⟨1383141, by decide⟩,⟨1383176, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_101329_1383177 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101329 ⟨1383177, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 101329
    ⟨1383177, by decide⟩ (by decide) (![⟨1383112, by decide⟩,⟨642341, by decide⟩,⟨1383141, by decide⟩,⟨1383176, by decide⟩]) unmarked_context_11_101329_1383177 node_context_11_101329_1383177
  intro a
  fin_cases a
  · exact context_12_405316_1383112
  · exact context_12_405317_642341
  · exact context_12_405318_1383141
  · exact context_12_405319_1383176

theorem selected_cut_49019 : selected 9 ⟨1383206, by decide⟩
    (prefixPartial 12 405320) = some ⟨12, 2, 0, 1383206, 405320, 1377, 65536⟩ := by
  decide +kernel

theorem context_12_405320_1383206 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 405320 ⟨1383206, by decide⟩ :=
  accepted_of_selected 12 405320 ⟨1383206, by decide⟩ ⟨12, 2, 0, 1383206, 405320, 1377, 65536⟩
    (by decide) selected_cut_49019

theorem selected_cut_49020 : selected 9 ⟨642341, by decide⟩
    (prefixPartial 12 405321) = some ⟨12, 1, 0, 642341, 405321, 1, 65536⟩ := by
  decide +kernel

theorem context_12_405321_642341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 405321 ⟨642341, by decide⟩ :=
  accepted_of_selected 12 405321 ⟨642341, by decide⟩ ⟨12, 1, 0, 642341, 405321, 1, 65536⟩
    (by decide) selected_cut_49020

theorem selected_cut_49021 : selected 9 ⟨1383230, by decide⟩
    (prefixPartial 12 405322) = some ⟨12, 2, 0, 1383230, 405322, 1509, 65536⟩ := by
  decide +kernel

theorem context_12_405322_1383230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 405322 ⟨1383230, by decide⟩ :=
  accepted_of_selected 12 405322 ⟨1383230, by decide⟩ ⟨12, 2, 0, 1383230, 405322, 1509, 65536⟩
    (by decide) selected_cut_49021

theorem selected_cut_49022 : selected 9 ⟨1383258, by decide⟩
    (prefixPartial 12 405323) = some ⟨12, 2, 0, 1383258, 405323, 1613, 65536⟩ := by
  decide +kernel

theorem context_12_405323_1383258 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 405323 ⟨1383258, by decide⟩ :=
  accepted_of_selected 12 405323 ⟨1383258, by decide⟩ ⟨12, 2, 0, 1383258, 405323, 1613, 65536⟩
    (by decide) selected_cut_49022

theorem unmarked_context_11_101330_1383259 : frontier 10 ⟨1383259, by decide⟩
    (prefixCache 11 101330) (prefixPartial 11 101330) = false := by
  decide +kernel

theorem node_context_11_101330_1383259 : EJMOriginalGlobalDAGData.nodes 10 ⟨1383259, by decide⟩ =
    .split (coordinate 11) (![⟨1383206, by decide⟩,⟨642341, by decide⟩,⟨1383230, by decide⟩,⟨1383258, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_101330_1383259 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101330 ⟨1383259, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 101330
    ⟨1383259, by decide⟩ (by decide) (![⟨1383206, by decide⟩,⟨642341, by decide⟩,⟨1383230, by decide⟩,⟨1383258, by decide⟩]) unmarked_context_11_101330_1383259 node_context_11_101330_1383259
  intro a
  fin_cases a
  · exact context_12_405320_1383206
  · exact context_12_405321_642341
  · exact context_12_405322_1383230
  · exact context_12_405323_1383258

theorem selected_cut_49023 : selected 10 ⟨1383300, by decide⟩
    (prefixPartial 11 101331) = some ⟨11, 2, 0, 1383300, 101331, 2465, 262144⟩ := by
  decide +kernel

theorem context_11_101331_1383300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101331 ⟨1383300, by decide⟩ :=
  accepted_of_selected 11 101331 ⟨1383300, by decide⟩ ⟨11, 2, 0, 1383300, 101331, 2465, 262144⟩
    (by decide) selected_cut_49023

theorem unmarked_context_10_25332_1383301 : frontier 11 ⟨1383301, by decide⟩
    (prefixCache 10 25332) (prefixPartial 10 25332) = false := by
  decide +kernel

theorem node_context_10_25332_1383301 : EJMOriginalGlobalDAGData.nodes 11 ⟨1383301, by decide⟩ =
    .split (coordinate 10) (![⟨1383082, by decide⟩,⟨1383177, by decide⟩,⟨1383259, by decide⟩,⟨1383300, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25332_1383301 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25332 ⟨1383301, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25332
    ⟨1383301, by decide⟩ (by decide) (![⟨1383082, by decide⟩,⟨1383177, by decide⟩,⟨1383259, by decide⟩,⟨1383300, by decide⟩]) unmarked_context_10_25332_1383301 node_context_10_25332_1383301
  intro a
  fin_cases a
  · exact context_11_101328_1383082
  · exact context_11_101329_1383177
  · exact context_11_101330_1383259
  · exact context_11_101331_1383300

theorem selected_cut_49024 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 25333) = some ⟨10, 1, 0, 893098, 25333, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_25333_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25333 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 25333 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 25333, 1, 1048576⟩
    (by decide) selected_cut_49024

theorem selected_cut_49025 : selected 9 ⟨1383335, by decide⟩
    (prefixPartial 12 405344) = some ⟨12, 2, 0, 1383335, 405344, 1521, 65536⟩ := by
  decide +kernel

theorem context_12_405344_1383335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 405344 ⟨1383335, by decide⟩ :=
  accepted_of_selected 12 405344 ⟨1383335, by decide⟩ ⟨12, 2, 0, 1383335, 405344, 1521, 65536⟩
    (by decide) selected_cut_49025

theorem selected_cut_49026 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 405345) = some ⟨12, 1, 0, 170504, 405345, 1, 65536⟩ := by
  decide +kernel

theorem context_12_405345_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 405345 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 405345 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 405345, 1, 65536⟩
    (by decide) selected_cut_49026

theorem selected_cut_49027 : selected 9 ⟨1383358, by decide⟩
    (prefixPartial 12 405346) = some ⟨12, 2, 0, 1383358, 405346, 1365, 65536⟩ := by
  decide +kernel

theorem context_12_405346_1383358 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 405346 ⟨1383358, by decide⟩ :=
  accepted_of_selected 12 405346 ⟨1383358, by decide⟩ ⟨12, 2, 0, 1383358, 405346, 1365, 65536⟩
    (by decide) selected_cut_49027

theorem selected_cut_49028 : selected 9 ⟨1383382, by decide⟩
    (prefixPartial 12 405347) = some ⟨12, 2, 0, 1383382, 405347, 1481, 65536⟩ := by
  decide +kernel

theorem context_12_405347_1383382 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 405347 ⟨1383382, by decide⟩ :=
  accepted_of_selected 12 405347 ⟨1383382, by decide⟩ ⟨12, 2, 0, 1383382, 405347, 1481, 65536⟩
    (by decide) selected_cut_49028

theorem unmarked_context_11_101336_1383383 : frontier 10 ⟨1383383, by decide⟩
    (prefixCache 11 101336) (prefixPartial 11 101336) = false := by
  decide +kernel

theorem node_context_11_101336_1383383 : EJMOriginalGlobalDAGData.nodes 10 ⟨1383383, by decide⟩ =
    .split (coordinate 11) (![⟨1383335, by decide⟩,⟨170504, by decide⟩,⟨1383358, by decide⟩,⟨1383382, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_101336_1383383 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101336 ⟨1383383, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 101336
    ⟨1383383, by decide⟩ (by decide) (![⟨1383335, by decide⟩,⟨170504, by decide⟩,⟨1383358, by decide⟩,⟨1383382, by decide⟩]) unmarked_context_11_101336_1383383 node_context_11_101336_1383383
  intro a
  fin_cases a
  · exact context_12_405344_1383335
  · exact context_12_405345_170504
  · exact context_12_405346_1383358
  · exact context_12_405347_1383382

theorem selected_cut_49029 : selected 10 ⟨1383448, by decide⟩
    (prefixPartial 11 101337) = some ⟨11, 2, 0, 1383448, 101337, 3761, 262144⟩ := by
  decide +kernel

theorem context_11_101337_1383448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101337 ⟨1383448, by decide⟩ :=
  accepted_of_selected 11 101337 ⟨1383448, by decide⟩ ⟨11, 2, 0, 1383448, 101337, 3761, 262144⟩
    (by decide) selected_cut_49029

theorem selected_cut_49030 : selected 10 ⟨1383492, by decide⟩
    (prefixPartial 11 101338) = some ⟨11, 2, 0, 1383492, 101338, 1697, 262144⟩ := by
  decide +kernel

theorem context_11_101338_1383492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101338 ⟨1383492, by decide⟩ :=
  accepted_of_selected 11 101338 ⟨1383492, by decide⟩ ⟨11, 2, 0, 1383492, 101338, 1697, 262144⟩
    (by decide) selected_cut_49030

theorem selected_cut_49031 : selected 10 ⟨1383541, by decide⟩
    (prefixPartial 11 101339) = some ⟨11, 2, 0, 1383541, 101339, 2901, 262144⟩ := by
  decide +kernel

theorem context_11_101339_1383541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101339 ⟨1383541, by decide⟩ :=
  accepted_of_selected 11 101339 ⟨1383541, by decide⟩ ⟨11, 2, 0, 1383541, 101339, 2901, 262144⟩
    (by decide) selected_cut_49031

theorem unmarked_context_10_25334_1383542 : frontier 11 ⟨1383542, by decide⟩
    (prefixCache 10 25334) (prefixPartial 10 25334) = false := by
  decide +kernel

theorem node_context_10_25334_1383542 : EJMOriginalGlobalDAGData.nodes 11 ⟨1383542, by decide⟩ =
    .split (coordinate 10) (![⟨1383383, by decide⟩,⟨1383448, by decide⟩,⟨1383492, by decide⟩,⟨1383541, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25334_1383542 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25334 ⟨1383542, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25334
    ⟨1383542, by decide⟩ (by decide) (![⟨1383383, by decide⟩,⟨1383448, by decide⟩,⟨1383492, by decide⟩,⟨1383541, by decide⟩]) unmarked_context_10_25334_1383542 node_context_10_25334_1383542
  intro a
  fin_cases a
  · exact context_11_101336_1383383
  · exact context_11_101337_1383448
  · exact context_11_101338_1383492
  · exact context_11_101339_1383541

theorem selected_cut_49032 : selected 10 ⟨1383597, by decide⟩
    (prefixPartial 11 101340) = some ⟨11, 2, 0, 1383597, 101340, 2585, 262144⟩ := by
  decide +kernel

theorem context_11_101340_1383597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101340 ⟨1383597, by decide⟩ :=
  accepted_of_selected 11 101340 ⟨1383597, by decide⟩ ⟨11, 2, 0, 1383597, 101340, 2585, 262144⟩
    (by decide) selected_cut_49032

theorem selected_cut_49033 : selected 10 ⟨1383675, by decide⟩
    (prefixPartial 11 101341) = some ⟨11, 2, 0, 1383675, 101341, 3237, 262144⟩ := by
  decide +kernel

theorem context_11_101341_1383675 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101341 ⟨1383675, by decide⟩ :=
  accepted_of_selected 11 101341 ⟨1383675, by decide⟩ ⟨11, 2, 0, 1383675, 101341, 3237, 262144⟩
    (by decide) selected_cut_49033

theorem selected_cut_49034 : selected 10 ⟨1383728, by decide⟩
    (prefixPartial 11 101342) = some ⟨11, 2, 0, 1383728, 101342, 2633, 262144⟩ := by
  decide +kernel

theorem context_11_101342_1383728 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101342 ⟨1383728, by decide⟩ :=
  accepted_of_selected 11 101342 ⟨1383728, by decide⟩ ⟨11, 2, 0, 1383728, 101342, 2633, 262144⟩
    (by decide) selected_cut_49034

theorem selected_cut_49035 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 101343) = some ⟨11, 1, 0, 977886, 101343, 1, 262144⟩ := by
  decide +kernel

theorem context_11_101343_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101343 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 101343 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 101343, 1, 262144⟩
    (by decide) selected_cut_49035

theorem unmarked_context_10_25335_1383729 : frontier 11 ⟨1383729, by decide⟩
    (prefixCache 10 25335) (prefixPartial 10 25335) = false := by
  decide +kernel

theorem node_context_10_25335_1383729 : EJMOriginalGlobalDAGData.nodes 11 ⟨1383729, by decide⟩ =
    .split (coordinate 10) (![⟨1383597, by decide⟩,⟨1383675, by decide⟩,⟨1383728, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25335_1383729 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25335 ⟨1383729, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25335
    ⟨1383729, by decide⟩ (by decide) (![⟨1383597, by decide⟩,⟨1383675, by decide⟩,⟨1383728, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_25335_1383729 node_context_10_25335_1383729
  intro a
  fin_cases a
  · exact context_11_101340_1383597
  · exact context_11_101341_1383675
  · exact context_11_101342_1383728
  · exact context_11_101343_977886

theorem unmarked_context_9_6333_1383730 : frontier 12 ⟨1383730, by decide⟩
    (prefixCache 9 6333) (prefixPartial 9 6333) = false := by
  decide +kernel

theorem node_context_9_6333_1383730 : EJMOriginalGlobalDAGData.nodes 12 ⟨1383730, by decide⟩ =
    .split (coordinate 9) (![⟨1383301, by decide⟩,⟨893098, by decide⟩,⟨1383542, by decide⟩,⟨1383729, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6333_1383730 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6333 ⟨1383730, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6333
    ⟨1383730, by decide⟩ (by decide) (![⟨1383301, by decide⟩,⟨893098, by decide⟩,⟨1383542, by decide⟩,⟨1383729, by decide⟩]) unmarked_context_9_6333_1383730 node_context_9_6333_1383730
  intro a
  fin_cases a
  · exact context_10_25332_1383301
  · exact context_10_25333_893098
  · exact context_10_25334_1383542
  · exact context_10_25335_1383729

theorem selected_cut_49036 : selected 10 ⟨1383757, by decide⟩
    (prefixPartial 11 101344) = some ⟨11, 2, 0, 1383757, 101344, 1105, 262144⟩ := by
  decide +kernel

theorem context_11_101344_1383757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101344 ⟨1383757, by decide⟩ :=
  accepted_of_selected 11 101344 ⟨1383757, by decide⟩ ⟨11, 2, 0, 1383757, 101344, 1105, 262144⟩
    (by decide) selected_cut_49036

theorem selected_cut_49037 : selected 10 ⟨1383807, by decide⟩
    (prefixPartial 11 101345) = some ⟨11, 2, 0, 1383807, 101345, 2477, 262144⟩ := by
  decide +kernel

theorem context_11_101345_1383807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101345 ⟨1383807, by decide⟩ :=
  accepted_of_selected 11 101345 ⟨1383807, by decide⟩ ⟨11, 2, 0, 1383807, 101345, 2477, 262144⟩
    (by decide) selected_cut_49037

theorem selected_cut_49038 : selected 10 ⟨1383848, by decide⟩
    (prefixPartial 11 101346) = some ⟨11, 2, 0, 1383848, 101346, 2453, 262144⟩ := by
  decide +kernel

theorem context_11_101346_1383848 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101346 ⟨1383848, by decide⟩ :=
  accepted_of_selected 11 101346 ⟨1383848, by decide⟩ ⟨11, 2, 0, 1383848, 101346, 2453, 262144⟩
    (by decide) selected_cut_49038

theorem selected_cut_49039 : selected 10 ⟨1383875, by decide⟩
    (prefixPartial 11 101347) = some ⟨11, 2, 0, 1383875, 101347, 1449, 262144⟩ := by
  decide +kernel

theorem context_11_101347_1383875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101347 ⟨1383875, by decide⟩ :=
  accepted_of_selected 11 101347 ⟨1383875, by decide⟩ ⟨11, 2, 0, 1383875, 101347, 1449, 262144⟩
    (by decide) selected_cut_49039

theorem unmarked_context_10_25336_1383876 : frontier 11 ⟨1383876, by decide⟩
    (prefixCache 10 25336) (prefixPartial 10 25336) = false := by
  decide +kernel

theorem node_context_10_25336_1383876 : EJMOriginalGlobalDAGData.nodes 11 ⟨1383876, by decide⟩ =
    .split (coordinate 10) (![⟨1383757, by decide⟩,⟨1383807, by decide⟩,⟨1383848, by decide⟩,⟨1383875, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25336_1383876 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25336 ⟨1383876, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25336
    ⟨1383876, by decide⟩ (by decide) (![⟨1383757, by decide⟩,⟨1383807, by decide⟩,⟨1383848, by decide⟩,⟨1383875, by decide⟩]) unmarked_context_10_25336_1383876 node_context_10_25336_1383876
  intro a
  fin_cases a
  · exact context_11_101344_1383757
  · exact context_11_101345_1383807
  · exact context_11_101346_1383848
  · exact context_11_101347_1383875

theorem selected_cut_49040 : selected 10 ⟨1383932, by decide⟩
    (prefixPartial 11 101348) = some ⟨11, 2, 0, 1383932, 101348, 2441, 262144⟩ := by
  decide +kernel

theorem context_11_101348_1383932 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101348 ⟨1383932, by decide⟩ :=
  accepted_of_selected 11 101348 ⟨1383932, by decide⟩ ⟨11, 2, 0, 1383932, 101348, 2441, 262144⟩
    (by decide) selected_cut_49040

theorem selected_cut_49041 : selected 10 ⟨1383946, by decide⟩
    (prefixPartial 11 101349) = some ⟨11, 2, 0, 1383946, 101349, 657, 262144⟩ := by
  decide +kernel

theorem context_11_101349_1383946 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101349 ⟨1383946, by decide⟩ :=
  accepted_of_selected 11 101349 ⟨1383946, by decide⟩ ⟨11, 2, 0, 1383946, 101349, 657, 262144⟩
    (by decide) selected_cut_49041

theorem selected_cut_49042 : selected 10 ⟨1383981, by decide⟩
    (prefixPartial 11 101350) = some ⟨11, 2, 0, 1383981, 101350, 1873, 262144⟩ := by
  decide +kernel

theorem context_11_101350_1383981 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101350 ⟨1383981, by decide⟩ :=
  accepted_of_selected 11 101350 ⟨1383981, by decide⟩ ⟨11, 2, 0, 1383981, 101350, 1873, 262144⟩
    (by decide) selected_cut_49042

theorem selected_cut_49043 : selected 10 ⟨1384014, by decide⟩
    (prefixPartial 11 101351) = some ⟨11, 2, 0, 1384014, 101351, 1657, 262144⟩ := by
  decide +kernel

theorem context_11_101351_1384014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101351 ⟨1384014, by decide⟩ :=
  accepted_of_selected 11 101351 ⟨1384014, by decide⟩ ⟨11, 2, 0, 1384014, 101351, 1657, 262144⟩
    (by decide) selected_cut_49043

theorem unmarked_context_10_25337_1384015 : frontier 11 ⟨1384015, by decide⟩
    (prefixCache 10 25337) (prefixPartial 10 25337) = false := by
  decide +kernel

theorem node_context_10_25337_1384015 : EJMOriginalGlobalDAGData.nodes 11 ⟨1384015, by decide⟩ =
    .split (coordinate 10) (![⟨1383932, by decide⟩,⟨1383946, by decide⟩,⟨1383981, by decide⟩,⟨1384014, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25337_1384015 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25337 ⟨1384015, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25337
    ⟨1384015, by decide⟩ (by decide) (![⟨1383932, by decide⟩,⟨1383946, by decide⟩,⟨1383981, by decide⟩,⟨1384014, by decide⟩]) unmarked_context_10_25337_1384015 node_context_10_25337_1384015
  intro a
  fin_cases a
  · exact context_11_101348_1383932
  · exact context_11_101349_1383946
  · exact context_11_101350_1383981
  · exact context_11_101351_1384014

theorem selected_cut_49044 : selected 11 ⟨1384031, by decide⟩
    (prefixPartial 10 25338) = some ⟨10, 2, 0, 1384031, 25338, 937, 1048576⟩ := by
  decide +kernel

theorem context_10_25338_1384031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25338 ⟨1384031, by decide⟩ :=
  accepted_of_selected 10 25338 ⟨1384031, by decide⟩ ⟨10, 2, 0, 1384031, 25338, 937, 1048576⟩
    (by decide) selected_cut_49044

theorem selected_cut_49045 : selected 11 ⟨1384109, by decide⟩
    (prefixPartial 10 25339) = some ⟨10, 2, 0, 1384109, 25339, 3501, 1048576⟩ := by
  decide +kernel

theorem context_10_25339_1384109 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25339 ⟨1384109, by decide⟩ :=
  accepted_of_selected 10 25339 ⟨1384109, by decide⟩ ⟨10, 2, 0, 1384109, 25339, 3501, 1048576⟩
    (by decide) selected_cut_49045

theorem unmarked_context_9_6334_1384110 : frontier 12 ⟨1384110, by decide⟩
    (prefixCache 9 6334) (prefixPartial 9 6334) = false := by
  decide +kernel

theorem node_context_9_6334_1384110 : EJMOriginalGlobalDAGData.nodes 12 ⟨1384110, by decide⟩ =
    .split (coordinate 9) (![⟨1383876, by decide⟩,⟨1384015, by decide⟩,⟨1384031, by decide⟩,⟨1384109, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6334_1384110 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6334 ⟨1384110, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6334
    ⟨1384110, by decide⟩ (by decide) (![⟨1383876, by decide⟩,⟨1384015, by decide⟩,⟨1384031, by decide⟩,⟨1384109, by decide⟩]) unmarked_context_9_6334_1384110 node_context_9_6334_1384110
  intro a
  fin_cases a
  · exact context_10_25336_1383876
  · exact context_10_25337_1384015
  · exact context_10_25338_1384031
  · exact context_10_25339_1384109

theorem selected_cut_49046 : selected 12 ⟨1384216, by decide⟩
    (prefixPartial 9 6335) = some ⟨9, 2, 0, 1384216, 6335, 3673, 4194304⟩ := by
  decide +kernel

theorem context_9_6335_1384216 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6335 ⟨1384216, by decide⟩ :=
  accepted_of_selected 9 6335 ⟨1384216, by decide⟩ ⟨9, 2, 0, 1384216, 6335, 3673, 4194304⟩
    (by decide) selected_cut_49046

theorem unmarked_context_8_1583_1384217 : frontier 13 ⟨1384217, by decide⟩
    (prefixCache 8 1583) (prefixPartial 8 1583) = false := by
  decide +kernel

theorem node_context_8_1583_1384217 : EJMOriginalGlobalDAGData.nodes 13 ⟨1384217, by decide⟩ =
    .split (coordinate 8) (![⟨1383035, by decide⟩,⟨1383730, by decide⟩,⟨1384110, by decide⟩,⟨1384216, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1583_1384217 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1583 ⟨1384217, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1583
    ⟨1384217, by decide⟩ (by decide) (![⟨1383035, by decide⟩,⟨1383730, by decide⟩,⟨1384110, by decide⟩,⟨1384216, by decide⟩]) unmarked_context_8_1583_1384217 node_context_8_1583_1384217
  intro a
  fin_cases a
  · exact context_9_6332_1383035
  · exact context_9_6333_1383730
  · exact context_9_6334_1384110
  · exact context_9_6335_1384216

theorem unmarked_context_7_395_1384218 : frontier 14 ⟨1384218, by decide⟩
    (prefixCache 7 395) (prefixPartial 7 395) = false := by
  decide +kernel

theorem node_context_7_395_1384218 : EJMOriginalGlobalDAGData.nodes 14 ⟨1384218, by decide⟩ =
    .split (coordinate 7) (![⟨1364555, by decide⟩,⟨1381356, by decide⟩,⟨1366235, by decide⟩,⟨1384217, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_395_1384218 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 395 ⟨1384218, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 395
    ⟨1384218, by decide⟩ (by decide) (![⟨1364555, by decide⟩,⟨1381356, by decide⟩,⟨1366235, by decide⟩,⟨1384217, by decide⟩]) unmarked_context_7_395_1384218 node_context_7_395_1384218
  intro a
  fin_cases a
  · exact context_8_1580_1364555
  · exact context_8_1581_1381356
  · exact context_8_1582_1366235
  · exact context_8_1583_1384217

theorem unmarked_context_6_98_1384219 : frontier 15 ⟨1384219, by decide⟩
    (prefixCache 6 98) (prefixPartial 6 98) = false := by
  decide +kernel

theorem node_context_6_98_1384219 : EJMOriginalGlobalDAGData.nodes 15 ⟨1384219, by decide⟩ =
    .split (coordinate 6) (![⟨1367837, by decide⟩,⟨1373651, by decide⟩,⟨1378653, by decide⟩,⟨1384218, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_6_98_1384219 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 98 ⟨1384219, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 6 98
    ⟨1384219, by decide⟩ (by decide) (![⟨1367837, by decide⟩,⟨1373651, by decide⟩,⟨1378653, by decide⟩,⟨1384218, by decide⟩]) unmarked_context_6_98_1384219 node_context_6_98_1384219
  intro a
  fin_cases a
  · exact context_7_392_1367837
  · exact context_7_393_1373651
  · exact context_7_394_1378653
  · exact context_7_395_1384218

theorem selected_cut_49047 : selected 11 ⟨1384295, by decide⟩
    (prefixPartial 10 25344) = some ⟨10, 2, 0, 1384295, 25344, 1645, 1048576⟩ := by
  decide +kernel

theorem context_10_25344_1384295 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25344 ⟨1384295, by decide⟩ :=
  accepted_of_selected 10 25344 ⟨1384295, by decide⟩ ⟨10, 2, 0, 1384295, 25344, 1645, 1048576⟩
    (by decide) selected_cut_49047

theorem selected_cut_49048 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 405520) = some ⟨12, 1, 0, 1108174, 405520, 1, 65536⟩ := by
  decide +kernel

theorem context_12_405520_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 405520 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 405520 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 405520, 1, 65536⟩
    (by decide) selected_cut_49048

theorem selected_cut_49049 : selected 9 ⟨1384341, by decide⟩
    (prefixPartial 12 405521) = some ⟨12, 2, 0, 1384341, 405521, 1545, 65536⟩ := by
  decide +kernel

theorem context_12_405521_1384341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 405521 ⟨1384341, by decide⟩ :=
  accepted_of_selected 12 405521 ⟨1384341, by decide⟩ ⟨12, 2, 0, 1384341, 405521, 1545, 65536⟩
    (by decide) selected_cut_49049

theorem selected_cut_49050 : selected 9 ⟨1384375, by decide⟩
    (prefixPartial 12 405522) = some ⟨12, 2, 0, 1384375, 405522, 1569, 65536⟩ := by
  decide +kernel

theorem context_12_405522_1384375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 405522 ⟨1384375, by decide⟩ :=
  accepted_of_selected 12 405522 ⟨1384375, by decide⟩ ⟨12, 2, 0, 1384375, 405522, 1569, 65536⟩
    (by decide) selected_cut_49050

theorem selected_cut_49051 : selected 9 ⟨1384411, by decide⟩
    (prefixPartial 12 405523) = some ⟨12, 2, 0, 1384411, 405523, 1425, 65536⟩ := by
  decide +kernel

theorem context_12_405523_1384411 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 405523 ⟨1384411, by decide⟩ :=
  accepted_of_selected 12 405523 ⟨1384411, by decide⟩ ⟨12, 2, 0, 1384411, 405523, 1425, 65536⟩
    (by decide) selected_cut_49051

theorem unmarked_context_11_101380_1384412 : frontier 10 ⟨1384412, by decide⟩
    (prefixCache 11 101380) (prefixPartial 11 101380) = false := by
  decide +kernel

theorem node_context_11_101380_1384412 : EJMOriginalGlobalDAGData.nodes 10 ⟨1384412, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1384341, by decide⟩,⟨1384375, by decide⟩,⟨1384411, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_101380_1384412 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101380 ⟨1384412, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 101380
    ⟨1384412, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1384341, by decide⟩,⟨1384375, by decide⟩,⟨1384411, by decide⟩]) unmarked_context_11_101380_1384412 node_context_11_101380_1384412
  intro a
  fin_cases a
  · exact context_12_405520_1108174
  · exact context_12_405521_1384341
  · exact context_12_405522_1384375
  · exact context_12_405523_1384411

theorem selected_cut_49052 : selected 10 ⟨451541, by decide⟩
    (prefixPartial 11 101381) = some ⟨11, 1, 0, 451541, 101381, 1, 262144⟩ := by
  decide +kernel

theorem context_11_101381_451541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101381 ⟨451541, by decide⟩ :=
  accepted_of_selected 11 101381 ⟨451541, by decide⟩ ⟨11, 1, 0, 451541, 101381, 1, 262144⟩
    (by decide) selected_cut_49052

theorem selected_cut_49053 : selected 10 ⟨1384481, by decide⟩
    (prefixPartial 11 101382) = some ⟨11, 2, 0, 1384481, 101382, 3085, 262144⟩ := by
  decide +kernel

theorem context_11_101382_1384481 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101382 ⟨1384481, by decide⟩ :=
  accepted_of_selected 11 101382 ⟨1384481, by decide⟩ ⟨11, 2, 0, 1384481, 101382, 3085, 262144⟩
    (by decide) selected_cut_49053

theorem selected_cut_49054 : selected 10 ⟨1384551, by decide⟩
    (prefixPartial 11 101383) = some ⟨11, 2, 0, 1384551, 101383, 3221, 262144⟩ := by
  decide +kernel

theorem context_11_101383_1384551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101383 ⟨1384551, by decide⟩ :=
  accepted_of_selected 11 101383 ⟨1384551, by decide⟩ ⟨11, 2, 0, 1384551, 101383, 3221, 262144⟩
    (by decide) selected_cut_49054

theorem unmarked_context_10_25345_1384552 : frontier 11 ⟨1384552, by decide⟩
    (prefixCache 10 25345) (prefixPartial 10 25345) = false := by
  decide +kernel

theorem node_context_10_25345_1384552 : EJMOriginalGlobalDAGData.nodes 11 ⟨1384552, by decide⟩ =
    .split (coordinate 10) (![⟨1384412, by decide⟩,⟨451541, by decide⟩,⟨1384481, by decide⟩,⟨1384551, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25345_1384552 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25345 ⟨1384552, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25345
    ⟨1384552, by decide⟩ (by decide) (![⟨1384412, by decide⟩,⟨451541, by decide⟩,⟨1384481, by decide⟩,⟨1384551, by decide⟩]) unmarked_context_10_25345_1384552 node_context_10_25345_1384552
  intro a
  fin_cases a
  · exact context_11_101380_1384412
  · exact context_11_101381_451541
  · exact context_11_101382_1384481
  · exact context_11_101383_1384551

theorem selected_cut_49055 : selected 10 ⟨1384641, by decide⟩
    (prefixPartial 11 101384) = some ⟨11, 2, 0, 1384641, 101384, 4037, 262144⟩ := by
  decide +kernel

theorem context_11_101384_1384641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101384 ⟨1384641, by decide⟩ :=
  accepted_of_selected 11 101384 ⟨1384641, by decide⟩ ⟨11, 2, 0, 1384641, 101384, 4037, 262144⟩
    (by decide) selected_cut_49055

theorem selected_cut_49056 : selected 10 ⟨1384702, by decide⟩
    (prefixPartial 11 101385) = some ⟨11, 2, 0, 1384702, 101385, 2725, 262144⟩ := by
  decide +kernel

theorem context_11_101385_1384702 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101385 ⟨1384702, by decide⟩ :=
  accepted_of_selected 11 101385 ⟨1384702, by decide⟩ ⟨11, 2, 0, 1384702, 101385, 2725, 262144⟩
    (by decide) selected_cut_49056

theorem selected_cut_49057 : selected 10 ⟨479708, by decide⟩
    (prefixPartial 11 101386) = some ⟨11, 1, 0, 479708, 101386, 1, 262144⟩ := by
  decide +kernel

theorem context_11_101386_479708 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101386 ⟨479708, by decide⟩ :=
  accepted_of_selected 11 101386 ⟨479708, by decide⟩ ⟨11, 1, 0, 479708, 101386, 1, 262144⟩
    (by decide) selected_cut_49057

theorem selected_cut_49058 : selected 10 ⟨1384764, by decide⟩
    (prefixPartial 11 101387) = some ⟨11, 2, 0, 1384764, 101387, 2785, 262144⟩ := by
  decide +kernel

theorem context_11_101387_1384764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101387 ⟨1384764, by decide⟩ :=
  accepted_of_selected 11 101387 ⟨1384764, by decide⟩ ⟨11, 2, 0, 1384764, 101387, 2785, 262144⟩
    (by decide) selected_cut_49058

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
