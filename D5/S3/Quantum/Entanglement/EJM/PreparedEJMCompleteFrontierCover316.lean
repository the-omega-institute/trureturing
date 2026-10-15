/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover315
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_30339 : selected 8 ⟨765803, by decide⟩
    (prefixPartial 13 417927) = some ⟨13, 2, 0, 765803, 417927, 873, 16384⟩ := by
  decide +kernel

theorem context_13_417927_765803 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417927 ⟨765803, by decide⟩ :=
  accepted_of_selected 13 417927 ⟨765803, by decide⟩ ⟨13, 2, 0, 765803, 417927, 873, 16384⟩
    (by decide) selected_cut_30339

theorem unmarked_context_12_104481_765804 : frontier 9 ⟨765804, by decide⟩
    (prefixCache 12 104481) (prefixPartial 12 104481) = false := by
  decide +kernel

theorem node_context_12_104481_765804 : EJMOriginalGlobalDAGData.nodes 9 ⟨765804, by decide⟩ =
    .split (coordinate 12) (![⟨765743, by decide⟩,⟨765769, by decide⟩,⟨765788, by decide⟩,⟨765803, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104481_765804 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104481 ⟨765804, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104481
    ⟨765804, by decide⟩ (by decide) (![⟨765743, by decide⟩,⟨765769, by decide⟩,⟨765788, by decide⟩,⟨765803, by decide⟩]) unmarked_context_12_104481_765804 node_context_12_104481_765804
  intro a
  fin_cases a
  · exact context_13_417924_765743
  · exact context_13_417925_765769
  · exact context_13_417926_765788
  · exact context_13_417927_765803

theorem selected_cut_30340 : selected 9 ⟨765893, by decide⟩
    (prefixPartial 12 104482) = some ⟨12, 2, 0, 765893, 104482, 3993, 65536⟩ := by
  decide +kernel

theorem context_12_104482_765893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104482 ⟨765893, by decide⟩ :=
  accepted_of_selected 12 104482 ⟨765893, by decide⟩ ⟨12, 2, 0, 765893, 104482, 3993, 65536⟩
    (by decide) selected_cut_30340

theorem selected_cut_30341 : selected 8 ⟨765920, by decide⟩
    (prefixPartial 13 417932) = some ⟨13, 2, 0, 765920, 417932, 969, 16384⟩ := by
  decide +kernel

theorem context_13_417932_765920 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417932 ⟨765920, by decide⟩ :=
  accepted_of_selected 13 417932 ⟨765920, by decide⟩ ⟨13, 2, 0, 765920, 417932, 969, 16384⟩
    (by decide) selected_cut_30341

theorem selected_cut_30342 : selected 8 ⟨765945, by decide⟩
    (prefixPartial 13 417933) = some ⟨13, 2, 0, 765945, 417933, 1849, 16384⟩ := by
  decide +kernel

theorem context_13_417933_765945 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417933 ⟨765945, by decide⟩ :=
  accepted_of_selected 13 417933 ⟨765945, by decide⟩ ⟨13, 2, 0, 765945, 417933, 1849, 16384⟩
    (by decide) selected_cut_30342

theorem selected_cut_30343 : selected 8 ⟨765963, by decide⟩
    (prefixPartial 13 417934) = some ⟨13, 2, 0, 765963, 417934, 873, 16384⟩ := by
  decide +kernel

theorem context_13_417934_765963 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417934 ⟨765963, by decide⟩ :=
  accepted_of_selected 13 417934 ⟨765963, by decide⟩ ⟨13, 2, 0, 765963, 417934, 873, 16384⟩
    (by decide) selected_cut_30343

theorem selected_cut_30344 : selected 8 ⟨765974, by decide⟩
    (prefixPartial 13 417935) = some ⟨13, 2, 0, 765974, 417935, 729, 16384⟩ := by
  decide +kernel

theorem context_13_417935_765974 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417935 ⟨765974, by decide⟩ :=
  accepted_of_selected 13 417935 ⟨765974, by decide⟩ ⟨13, 2, 0, 765974, 417935, 729, 16384⟩
    (by decide) selected_cut_30344

theorem unmarked_context_12_104483_765975 : frontier 9 ⟨765975, by decide⟩
    (prefixCache 12 104483) (prefixPartial 12 104483) = false := by
  decide +kernel

theorem node_context_12_104483_765975 : EJMOriginalGlobalDAGData.nodes 9 ⟨765975, by decide⟩ =
    .split (coordinate 12) (![⟨765920, by decide⟩,⟨765945, by decide⟩,⟨765963, by decide⟩,⟨765974, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104483_765975 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104483 ⟨765975, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104483
    ⟨765975, by decide⟩ (by decide) (![⟨765920, by decide⟩,⟨765945, by decide⟩,⟨765963, by decide⟩,⟨765974, by decide⟩]) unmarked_context_12_104483_765975 node_context_12_104483_765975
  intro a
  fin_cases a
  · exact context_13_417932_765920
  · exact context_13_417933_765945
  · exact context_13_417934_765963
  · exact context_13_417935_765974

theorem unmarked_context_11_26120_765976 : frontier 10 ⟨765976, by decide⟩
    (prefixCache 11 26120) (prefixPartial 11 26120) = false := by
  decide +kernel

theorem node_context_11_26120_765976 : EJMOriginalGlobalDAGData.nodes 10 ⟨765976, by decide⟩ =
    .split (coordinate 11) (![⟨765706, by decide⟩,⟨765804, by decide⟩,⟨765893, by decide⟩,⟨765975, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26120_765976 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26120 ⟨765976, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26120
    ⟨765976, by decide⟩ (by decide) (![⟨765706, by decide⟩,⟨765804, by decide⟩,⟨765893, by decide⟩,⟨765975, by decide⟩]) unmarked_context_11_26120_765976 node_context_11_26120_765976
  intro a
  fin_cases a
  · exact context_12_104480_765706
  · exact context_12_104481_765804
  · exact context_12_104482_765893
  · exact context_12_104483_765975

theorem selected_cut_30345 : selected 8 ⟨765994, by decide⟩
    (prefixPartial 13 417936) = some ⟨13, 2, 0, 765994, 417936, 785, 16384⟩ := by
  decide +kernel

theorem context_13_417936_765994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417936 ⟨765994, by decide⟩ :=
  accepted_of_selected 13 417936 ⟨765994, by decide⟩ ⟨13, 2, 0, 765994, 417936, 785, 16384⟩
    (by decide) selected_cut_30345

theorem selected_cut_30346 : selected 8 ⟨766029, by decide⟩
    (prefixPartial 13 417937) = some ⟨13, 2, 0, 766029, 417937, 1633, 16384⟩ := by
  decide +kernel

theorem context_13_417937_766029 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417937 ⟨766029, by decide⟩ :=
  accepted_of_selected 13 417937 ⟨766029, by decide⟩ ⟨13, 2, 0, 766029, 417937, 1633, 16384⟩
    (by decide) selected_cut_30346

theorem selected_cut_30347 : selected 8 ⟨766048, by decide⟩
    (prefixPartial 13 417938) = some ⟨13, 2, 0, 766048, 417938, 1013, 16384⟩ := by
  decide +kernel

theorem context_13_417938_766048 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417938 ⟨766048, by decide⟩ :=
  accepted_of_selected 13 417938 ⟨766048, by decide⟩ ⟨13, 2, 0, 766048, 417938, 1013, 16384⟩
    (by decide) selected_cut_30347

theorem selected_cut_30348 : selected 8 ⟨766055, by decide⟩
    (prefixPartial 13 417939) = some ⟨13, 2, 0, 766055, 417939, 873, 16384⟩ := by
  decide +kernel

theorem context_13_417939_766055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417939 ⟨766055, by decide⟩ :=
  accepted_of_selected 13 417939 ⟨766055, by decide⟩ ⟨13, 2, 0, 766055, 417939, 873, 16384⟩
    (by decide) selected_cut_30348

theorem unmarked_context_12_104484_766056 : frontier 9 ⟨766056, by decide⟩
    (prefixCache 12 104484) (prefixPartial 12 104484) = false := by
  decide +kernel

theorem node_context_12_104484_766056 : EJMOriginalGlobalDAGData.nodes 9 ⟨766056, by decide⟩ =
    .split (coordinate 12) (![⟨765994, by decide⟩,⟨766029, by decide⟩,⟨766048, by decide⟩,⟨766055, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104484_766056 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104484 ⟨766056, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104484
    ⟨766056, by decide⟩ (by decide) (![⟨765994, by decide⟩,⟨766029, by decide⟩,⟨766048, by decide⟩,⟨766055, by decide⟩]) unmarked_context_12_104484_766056 node_context_12_104484_766056
  intro a
  fin_cases a
  · exact context_13_417936_765994
  · exact context_13_417937_766029
  · exact context_13_417938_766048
  · exact context_13_417939_766055

theorem selected_cut_30349 : selected 8 ⟨766085, by decide⟩
    (prefixPartial 13 417940) = some ⟨13, 2, 0, 766085, 417940, 1049, 16384⟩ := by
  decide +kernel

theorem context_13_417940_766085 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417940 ⟨766085, by decide⟩ :=
  accepted_of_selected 13 417940 ⟨766085, by decide⟩ ⟨13, 2, 0, 766085, 417940, 1049, 16384⟩
    (by decide) selected_cut_30349

theorem selected_cut_30350 : selected 8 ⟨766116, by decide⟩
    (prefixPartial 13 417941) = some ⟨13, 2, 0, 766116, 417941, 1605, 16384⟩ := by
  decide +kernel

theorem context_13_417941_766116 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417941 ⟨766116, by decide⟩ :=
  accepted_of_selected 13 417941 ⟨766116, by decide⟩ ⟨13, 2, 0, 766116, 417941, 1605, 16384⟩
    (by decide) selected_cut_30350

theorem selected_cut_30351 : selected 8 ⟨766135, by decide⟩
    (prefixPartial 13 417942) = some ⟨13, 2, 0, 766135, 417942, 961, 16384⟩ := by
  decide +kernel

theorem context_13_417942_766135 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417942 ⟨766135, by decide⟩ :=
  accepted_of_selected 13 417942 ⟨766135, by decide⟩ ⟨13, 2, 0, 766135, 417942, 961, 16384⟩
    (by decide) selected_cut_30351

theorem selected_cut_30352 : selected 8 ⟨766142, by decide⟩
    (prefixPartial 13 417943) = some ⟨13, 2, 0, 766142, 417943, 925, 16384⟩ := by
  decide +kernel

theorem context_13_417943_766142 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417943 ⟨766142, by decide⟩ :=
  accepted_of_selected 13 417943 ⟨766142, by decide⟩ ⟨13, 2, 0, 766142, 417943, 925, 16384⟩
    (by decide) selected_cut_30352

theorem unmarked_context_12_104485_766143 : frontier 9 ⟨766143, by decide⟩
    (prefixCache 12 104485) (prefixPartial 12 104485) = false := by
  decide +kernel

theorem node_context_12_104485_766143 : EJMOriginalGlobalDAGData.nodes 9 ⟨766143, by decide⟩ =
    .split (coordinate 12) (![⟨766085, by decide⟩,⟨766116, by decide⟩,⟨766135, by decide⟩,⟨766142, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104485_766143 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104485 ⟨766143, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104485
    ⟨766143, by decide⟩ (by decide) (![⟨766085, by decide⟩,⟨766116, by decide⟩,⟨766135, by decide⟩,⟨766142, by decide⟩]) unmarked_context_12_104485_766143 node_context_12_104485_766143
  intro a
  fin_cases a
  · exact context_13_417940_766085
  · exact context_13_417941_766116
  · exact context_13_417942_766135
  · exact context_13_417943_766142

theorem selected_cut_30353 : selected 8 ⟨766168, by decide⟩
    (prefixPartial 13 417944) = some ⟨13, 2, 0, 766168, 417944, 1097, 16384⟩ := by
  decide +kernel

theorem context_13_417944_766168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417944 ⟨766168, by decide⟩ :=
  accepted_of_selected 13 417944 ⟨766168, by decide⟩ ⟨13, 2, 0, 766168, 417944, 1097, 16384⟩
    (by decide) selected_cut_30353

theorem selected_cut_30354 : selected 8 ⟨766201, by decide⟩
    (prefixPartial 13 417945) = some ⟨13, 2, 0, 766201, 417945, 1861, 16384⟩ := by
  decide +kernel

theorem context_13_417945_766201 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417945 ⟨766201, by decide⟩ :=
  accepted_of_selected 13 417945 ⟨766201, by decide⟩ ⟨13, 2, 0, 766201, 417945, 1861, 16384⟩
    (by decide) selected_cut_30354

theorem selected_cut_30355 : selected 8 ⟨766228, by decide⟩
    (prefixPartial 13 417946) = some ⟨13, 2, 0, 766228, 417946, 857, 16384⟩ := by
  decide +kernel

theorem context_13_417946_766228 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417946 ⟨766228, by decide⟩ :=
  accepted_of_selected 13 417946 ⟨766228, by decide⟩ ⟨13, 2, 0, 766228, 417946, 857, 16384⟩
    (by decide) selected_cut_30355

theorem selected_cut_30356 : selected 8 ⟨766239, by decide⟩
    (prefixPartial 13 417947) = some ⟨13, 2, 0, 766239, 417947, 849, 16384⟩ := by
  decide +kernel

theorem context_13_417947_766239 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417947 ⟨766239, by decide⟩ :=
  accepted_of_selected 13 417947 ⟨766239, by decide⟩ ⟨13, 2, 0, 766239, 417947, 849, 16384⟩
    (by decide) selected_cut_30356

theorem unmarked_context_12_104486_766240 : frontier 9 ⟨766240, by decide⟩
    (prefixCache 12 104486) (prefixPartial 12 104486) = false := by
  decide +kernel

theorem node_context_12_104486_766240 : EJMOriginalGlobalDAGData.nodes 9 ⟨766240, by decide⟩ =
    .split (coordinate 12) (![⟨766168, by decide⟩,⟨766201, by decide⟩,⟨766228, by decide⟩,⟨766239, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104486_766240 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104486 ⟨766240, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104486
    ⟨766240, by decide⟩ (by decide) (![⟨766168, by decide⟩,⟨766201, by decide⟩,⟨766228, by decide⟩,⟨766239, by decide⟩]) unmarked_context_12_104486_766240 node_context_12_104486_766240
  intro a
  fin_cases a
  · exact context_13_417944_766168
  · exact context_13_417945_766201
  · exact context_13_417946_766228
  · exact context_13_417947_766239

theorem selected_cut_30357 : selected 8 ⟨766263, by decide⟩
    (prefixPartial 13 417948) = some ⟨13, 2, 0, 766263, 417948, 1001, 16384⟩ := by
  decide +kernel

theorem context_13_417948_766263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417948 ⟨766263, by decide⟩ :=
  accepted_of_selected 13 417948 ⟨766263, by decide⟩ ⟨13, 2, 0, 766263, 417948, 1001, 16384⟩
    (by decide) selected_cut_30357

theorem selected_cut_30358 : selected 8 ⟨766309, by decide⟩
    (prefixPartial 13 417949) = some ⟨13, 2, 0, 766309, 417949, 2185, 16384⟩ := by
  decide +kernel

theorem context_13_417949_766309 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417949 ⟨766309, by decide⟩ :=
  accepted_of_selected 13 417949 ⟨766309, by decide⟩ ⟨13, 2, 0, 766309, 417949, 2185, 16384⟩
    (by decide) selected_cut_30358

theorem selected_cut_30359 : selected 8 ⟨766329, by decide⟩
    (prefixPartial 13 417950) = some ⟨13, 2, 0, 766329, 417950, 965, 16384⟩ := by
  decide +kernel

theorem context_13_417950_766329 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417950 ⟨766329, by decide⟩ :=
  accepted_of_selected 13 417950 ⟨766329, by decide⟩ ⟨13, 2, 0, 766329, 417950, 965, 16384⟩
    (by decide) selected_cut_30359

theorem selected_cut_30360 : selected 8 ⟨766335, by decide⟩
    (prefixPartial 13 417951) = some ⟨13, 2, 0, 766335, 417951, 889, 16384⟩ := by
  decide +kernel

theorem context_13_417951_766335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417951 ⟨766335, by decide⟩ :=
  accepted_of_selected 13 417951 ⟨766335, by decide⟩ ⟨13, 2, 0, 766335, 417951, 889, 16384⟩
    (by decide) selected_cut_30360

theorem unmarked_context_12_104487_766336 : frontier 9 ⟨766336, by decide⟩
    (prefixCache 12 104487) (prefixPartial 12 104487) = false := by
  decide +kernel

theorem node_context_12_104487_766336 : EJMOriginalGlobalDAGData.nodes 9 ⟨766336, by decide⟩ =
    .split (coordinate 12) (![⟨766263, by decide⟩,⟨766309, by decide⟩,⟨766329, by decide⟩,⟨766335, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104487_766336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104487 ⟨766336, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104487
    ⟨766336, by decide⟩ (by decide) (![⟨766263, by decide⟩,⟨766309, by decide⟩,⟨766329, by decide⟩,⟨766335, by decide⟩]) unmarked_context_12_104487_766336 node_context_12_104487_766336
  intro a
  fin_cases a
  · exact context_13_417948_766263
  · exact context_13_417949_766309
  · exact context_13_417950_766329
  · exact context_13_417951_766335

theorem unmarked_context_11_26121_766337 : frontier 10 ⟨766337, by decide⟩
    (prefixCache 11 26121) (prefixPartial 11 26121) = false := by
  decide +kernel

theorem node_context_11_26121_766337 : EJMOriginalGlobalDAGData.nodes 10 ⟨766337, by decide⟩ =
    .split (coordinate 11) (![⟨766056, by decide⟩,⟨766143, by decide⟩,⟨766240, by decide⟩,⟨766336, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26121_766337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26121 ⟨766337, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26121
    ⟨766337, by decide⟩ (by decide) (![⟨766056, by decide⟩,⟨766143, by decide⟩,⟨766240, by decide⟩,⟨766336, by decide⟩]) unmarked_context_11_26121_766337 node_context_11_26121_766337
  intro a
  fin_cases a
  · exact context_12_104484_766056
  · exact context_12_104485_766143
  · exact context_12_104486_766240
  · exact context_12_104487_766336

theorem selected_cut_30361 : selected 10 ⟨766338, by decide⟩
    (prefixPartial 11 26122) = some ⟨11, 1, 0, 766338, 26122, 1, 262144⟩ := by
  decide +kernel

theorem context_11_26122_766338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26122 ⟨766338, by decide⟩ :=
  accepted_of_selected 11 26122 ⟨766338, by decide⟩ ⟨11, 1, 0, 766338, 26122, 1, 262144⟩
    (by decide) selected_cut_30361

theorem selected_cut_30362 : selected 9 ⟨766400, by decide⟩
    (prefixPartial 12 104492) = some ⟨12, 2, 0, 766400, 104492, 4025, 65536⟩ := by
  decide +kernel

theorem context_12_104492_766400 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104492 ⟨766400, by decide⟩ :=
  accepted_of_selected 12 104492 ⟨766400, by decide⟩ ⟨12, 2, 0, 766400, 104492, 4025, 65536⟩
    (by decide) selected_cut_30362

theorem selected_cut_30363 : selected 8 ⟨766422, by decide⟩
    (prefixPartial 13 417972) = some ⟨13, 2, 0, 766422, 417972, 881, 16384⟩ := by
  decide +kernel

theorem context_13_417972_766422 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417972 ⟨766422, by decide⟩ :=
  accepted_of_selected 13 417972 ⟨766422, by decide⟩ ⟨13, 2, 0, 766422, 417972, 881, 16384⟩
    (by decide) selected_cut_30363

theorem selected_cut_30364 : selected 8 ⟨766449, by decide⟩
    (prefixPartial 13 417973) = some ⟨13, 2, 0, 766449, 417973, 1873, 16384⟩ := by
  decide +kernel

theorem context_13_417973_766449 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417973 ⟨766449, by decide⟩ :=
  accepted_of_selected 13 417973 ⟨766449, by decide⟩ ⟨13, 2, 0, 766449, 417973, 1873, 16384⟩
    (by decide) selected_cut_30364

theorem selected_cut_30365 : selected 8 ⟨766470, by decide⟩
    (prefixPartial 13 417974) = some ⟨13, 2, 0, 766470, 417974, 1053, 16384⟩ := by
  decide +kernel

theorem context_13_417974_766470 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417974 ⟨766470, by decide⟩ :=
  accepted_of_selected 13 417974 ⟨766470, by decide⟩ ⟨13, 2, 0, 766470, 417974, 1053, 16384⟩
    (by decide) selected_cut_30365

theorem selected_cut_30366 : selected 8 ⟨766477, by decide⟩
    (prefixPartial 13 417975) = some ⟨13, 2, 0, 766477, 417975, 921, 16384⟩ := by
  decide +kernel

theorem context_13_417975_766477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417975 ⟨766477, by decide⟩ :=
  accepted_of_selected 13 417975 ⟨766477, by decide⟩ ⟨13, 2, 0, 766477, 417975, 921, 16384⟩
    (by decide) selected_cut_30366

theorem unmarked_context_12_104493_766478 : frontier 9 ⟨766478, by decide⟩
    (prefixCache 12 104493) (prefixPartial 12 104493) = false := by
  decide +kernel

theorem node_context_12_104493_766478 : EJMOriginalGlobalDAGData.nodes 9 ⟨766478, by decide⟩ =
    .split (coordinate 12) (![⟨766422, by decide⟩,⟨766449, by decide⟩,⟨766470, by decide⟩,⟨766477, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104493_766478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104493 ⟨766478, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104493
    ⟨766478, by decide⟩ (by decide) (![⟨766422, by decide⟩,⟨766449, by decide⟩,⟨766470, by decide⟩,⟨766477, by decide⟩]) unmarked_context_12_104493_766478 node_context_12_104493_766478
  intro a
  fin_cases a
  · exact context_13_417972_766422
  · exact context_13_417973_766449
  · exact context_13_417974_766470
  · exact context_13_417975_766477

theorem selected_cut_30367 : selected 8 ⟨766491, by decide⟩
    (prefixPartial 13 417976) = some ⟨13, 2, 0, 766491, 417976, 701, 16384⟩ := by
  decide +kernel

theorem context_13_417976_766491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417976 ⟨766491, by decide⟩ :=
  accepted_of_selected 13 417976 ⟨766491, by decide⟩ ⟨13, 2, 0, 766491, 417976, 701, 16384⟩
    (by decide) selected_cut_30367

theorem selected_cut_30368 : selected 8 ⟨766520, by decide⟩
    (prefixPartial 13 417977) = some ⟨13, 2, 0, 766520, 417977, 1905, 16384⟩ := by
  decide +kernel

theorem context_13_417977_766520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417977 ⟨766520, by decide⟩ :=
  accepted_of_selected 13 417977 ⟨766520, by decide⟩ ⟨13, 2, 0, 766520, 417977, 1905, 16384⟩
    (by decide) selected_cut_30368

theorem selected_cut_30369 : selected 8 ⟨766535, by decide⟩
    (prefixPartial 13 417978) = some ⟨13, 2, 0, 766535, 417978, 849, 16384⟩ := by
  decide +kernel

theorem context_13_417978_766535 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417978 ⟨766535, by decide⟩ :=
  accepted_of_selected 13 417978 ⟨766535, by decide⟩ ⟨13, 2, 0, 766535, 417978, 849, 16384⟩
    (by decide) selected_cut_30369

theorem selected_cut_30370 : selected 8 ⟨766540, by decide⟩
    (prefixPartial 13 417979) = some ⟨13, 2, 0, 766540, 417979, 757, 16384⟩ := by
  decide +kernel

theorem context_13_417979_766540 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417979 ⟨766540, by decide⟩ :=
  accepted_of_selected 13 417979 ⟨766540, by decide⟩ ⟨13, 2, 0, 766540, 417979, 757, 16384⟩
    (by decide) selected_cut_30370

theorem unmarked_context_12_104494_766541 : frontier 9 ⟨766541, by decide⟩
    (prefixCache 12 104494) (prefixPartial 12 104494) = false := by
  decide +kernel

theorem node_context_12_104494_766541 : EJMOriginalGlobalDAGData.nodes 9 ⟨766541, by decide⟩ =
    .split (coordinate 12) (![⟨766491, by decide⟩,⟨766520, by decide⟩,⟨766535, by decide⟩,⟨766540, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104494_766541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104494 ⟨766541, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104494
    ⟨766541, by decide⟩ (by decide) (![⟨766491, by decide⟩,⟨766520, by decide⟩,⟨766535, by decide⟩,⟨766540, by decide⟩]) unmarked_context_12_104494_766541 node_context_12_104494_766541
  intro a
  fin_cases a
  · exact context_13_417976_766491
  · exact context_13_417977_766520
  · exact context_13_417978_766535
  · exact context_13_417979_766540

theorem selected_cut_30371 : selected 8 ⟨766557, by decide⟩
    (prefixPartial 13 417980) = some ⟨13, 2, 0, 766557, 417980, 621, 16384⟩ := by
  decide +kernel

theorem context_13_417980_766557 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417980 ⟨766557, by decide⟩ :=
  accepted_of_selected 13 417980 ⟨766557, by decide⟩ ⟨13, 2, 0, 766557, 417980, 621, 16384⟩
    (by decide) selected_cut_30371

theorem selected_cut_30372 : selected 8 ⟨766601, by decide⟩
    (prefixPartial 13 417981) = some ⟨13, 2, 0, 766601, 417981, 2013, 16384⟩ := by
  decide +kernel

theorem context_13_417981_766601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417981 ⟨766601, by decide⟩ :=
  accepted_of_selected 13 417981 ⟨766601, by decide⟩ ⟨13, 2, 0, 766601, 417981, 2013, 16384⟩
    (by decide) selected_cut_30372

theorem selected_cut_30373 : selected 8 ⟨766620, by decide⟩
    (prefixPartial 13 417982) = some ⟨13, 2, 0, 766620, 417982, 877, 16384⟩ := by
  decide +kernel

theorem context_13_417982_766620 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417982 ⟨766620, by decide⟩ :=
  accepted_of_selected 13 417982 ⟨766620, by decide⟩ ⟨13, 2, 0, 766620, 417982, 877, 16384⟩
    (by decide) selected_cut_30373

theorem selected_cut_30374 : selected 8 ⟨766626, by decide⟩
    (prefixPartial 13 417983) = some ⟨13, 2, 0, 766626, 417983, 753, 16384⟩ := by
  decide +kernel

theorem context_13_417983_766626 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417983 ⟨766626, by decide⟩ :=
  accepted_of_selected 13 417983 ⟨766626, by decide⟩ ⟨13, 2, 0, 766626, 417983, 753, 16384⟩
    (by decide) selected_cut_30374

theorem unmarked_context_12_104495_766627 : frontier 9 ⟨766627, by decide⟩
    (prefixCache 12 104495) (prefixPartial 12 104495) = false := by
  decide +kernel

theorem node_context_12_104495_766627 : EJMOriginalGlobalDAGData.nodes 9 ⟨766627, by decide⟩ =
    .split (coordinate 12) (![⟨766557, by decide⟩,⟨766601, by decide⟩,⟨766620, by decide⟩,⟨766626, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104495_766627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104495 ⟨766627, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104495
    ⟨766627, by decide⟩ (by decide) (![⟨766557, by decide⟩,⟨766601, by decide⟩,⟨766620, by decide⟩,⟨766626, by decide⟩]) unmarked_context_12_104495_766627 node_context_12_104495_766627
  intro a
  fin_cases a
  · exact context_13_417980_766557
  · exact context_13_417981_766601
  · exact context_13_417982_766620
  · exact context_13_417983_766626

theorem unmarked_context_11_26123_766628 : frontier 10 ⟨766628, by decide⟩
    (prefixCache 11 26123) (prefixPartial 11 26123) = false := by
  decide +kernel

theorem node_context_11_26123_766628 : EJMOriginalGlobalDAGData.nodes 10 ⟨766628, by decide⟩ =
    .split (coordinate 11) (![⟨766400, by decide⟩,⟨766478, by decide⟩,⟨766541, by decide⟩,⟨766627, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26123_766628 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26123 ⟨766628, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26123
    ⟨766628, by decide⟩ (by decide) (![⟨766400, by decide⟩,⟨766478, by decide⟩,⟨766541, by decide⟩,⟨766627, by decide⟩]) unmarked_context_11_26123_766628 node_context_11_26123_766628
  intro a
  fin_cases a
  · exact context_12_104492_766400
  · exact context_12_104493_766478
  · exact context_12_104494_766541
  · exact context_12_104495_766627

theorem unmarked_context_10_6530_766629 : frontier 11 ⟨766629, by decide⟩
    (prefixCache 10 6530) (prefixPartial 10 6530) = false := by
  decide +kernel

theorem node_context_10_6530_766629 : EJMOriginalGlobalDAGData.nodes 11 ⟨766629, by decide⟩ =
    .split (coordinate 10) (![⟨765976, by decide⟩,⟨766337, by decide⟩,⟨766338, by decide⟩,⟨766628, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6530_766629 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6530 ⟨766629, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6530
    ⟨766629, by decide⟩ (by decide) (![⟨765976, by decide⟩,⟨766337, by decide⟩,⟨766338, by decide⟩,⟨766628, by decide⟩]) unmarked_context_10_6530_766629 node_context_10_6530_766629
  intro a
  fin_cases a
  · exact context_11_26120_765976
  · exact context_11_26121_766337
  · exact context_11_26122_766338
  · exact context_11_26123_766628

theorem selected_cut_30375 : selected 9 ⟨766630, by decide⟩
    (prefixPartial 12 104496) = some ⟨12, 1, 0, 766630, 104496, 1, 65536⟩ := by
  decide +kernel

theorem context_12_104496_766630 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104496 ⟨766630, by decide⟩ :=
  accepted_of_selected 12 104496 ⟨766630, by decide⟩ ⟨12, 1, 0, 766630, 104496, 1, 65536⟩
    (by decide) selected_cut_30375

theorem selected_cut_30376 : selected 8 ⟨766654, by decide⟩
    (prefixPartial 13 417988) = some ⟨13, 2, 0, 766654, 417988, 721, 16384⟩ := by
  decide +kernel

theorem context_13_417988_766654 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417988 ⟨766654, by decide⟩ :=
  accepted_of_selected 13 417988 ⟨766654, by decide⟩ ⟨13, 2, 0, 766654, 417988, 721, 16384⟩
    (by decide) selected_cut_30376

theorem selected_cut_30377 : selected 8 ⟨766720, by decide⟩
    (prefixPartial 13 417989) = some ⟨13, 2, 0, 766720, 417989, 2033, 16384⟩ := by
  decide +kernel

theorem context_13_417989_766720 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417989 ⟨766720, by decide⟩ :=
  accepted_of_selected 13 417989 ⟨766720, by decide⟩ ⟨13, 2, 0, 766720, 417989, 2033, 16384⟩
    (by decide) selected_cut_30377

theorem selected_cut_30378 : selected 8 ⟨766736, by decide⟩
    (prefixPartial 13 417990) = some ⟨13, 2, 0, 766736, 417990, 877, 16384⟩ := by
  decide +kernel

theorem context_13_417990_766736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417990 ⟨766736, by decide⟩ :=
  accepted_of_selected 13 417990 ⟨766736, by decide⟩ ⟨13, 2, 0, 766736, 417990, 877, 16384⟩
    (by decide) selected_cut_30378

theorem selected_cut_30379 : selected 8 ⟨766750, by decide⟩
    (prefixPartial 13 417991) = some ⟨13, 2, 0, 766750, 417991, 821, 16384⟩ := by
  decide +kernel

theorem context_13_417991_766750 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417991 ⟨766750, by decide⟩ :=
  accepted_of_selected 13 417991 ⟨766750, by decide⟩ ⟨13, 2, 0, 766750, 417991, 821, 16384⟩
    (by decide) selected_cut_30379

theorem unmarked_context_12_104497_766751 : frontier 9 ⟨766751, by decide⟩
    (prefixCache 12 104497) (prefixPartial 12 104497) = false := by
  decide +kernel

theorem node_context_12_104497_766751 : EJMOriginalGlobalDAGData.nodes 9 ⟨766751, by decide⟩ =
    .split (coordinate 12) (![⟨766654, by decide⟩,⟨766720, by decide⟩,⟨766736, by decide⟩,⟨766750, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104497_766751 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104497 ⟨766751, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104497
    ⟨766751, by decide⟩ (by decide) (![⟨766654, by decide⟩,⟨766720, by decide⟩,⟨766736, by decide⟩,⟨766750, by decide⟩]) unmarked_context_12_104497_766751 node_context_12_104497_766751
  intro a
  fin_cases a
  · exact context_13_417988_766654
  · exact context_13_417989_766720
  · exact context_13_417990_766736
  · exact context_13_417991_766750

theorem selected_cut_30380 : selected 9 ⟨766844, by decide⟩
    (prefixPartial 12 104498) = some ⟨12, 2, 0, 766844, 104498, 3745, 65536⟩ := by
  decide +kernel

theorem context_12_104498_766844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104498 ⟨766844, by decide⟩ :=
  accepted_of_selected 12 104498 ⟨766844, by decide⟩ ⟨12, 2, 0, 766844, 104498, 3745, 65536⟩
    (by decide) selected_cut_30380

theorem selected_cut_30381 : selected 8 ⟨766860, by decide⟩
    (prefixPartial 13 417996) = some ⟨13, 2, 0, 766860, 417996, 617, 16384⟩ := by
  decide +kernel

theorem context_13_417996_766860 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417996 ⟨766860, by decide⟩ :=
  accepted_of_selected 13 417996 ⟨766860, by decide⟩ ⟨13, 2, 0, 766860, 417996, 617, 16384⟩
    (by decide) selected_cut_30381

theorem selected_cut_30382 : selected 8 ⟨766927, by decide⟩
    (prefixPartial 13 417997) = some ⟨13, 2, 0, 766927, 417997, 2189, 16384⟩ := by
  decide +kernel

theorem context_13_417997_766927 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417997 ⟨766927, by decide⟩ :=
  accepted_of_selected 13 417997 ⟨766927, by decide⟩ ⟨13, 2, 0, 766927, 417997, 2189, 16384⟩
    (by decide) selected_cut_30382

theorem selected_cut_30383 : selected 8 ⟨766948, by decide⟩
    (prefixPartial 13 417998) = some ⟨13, 2, 0, 766948, 417998, 1013, 16384⟩ := by
  decide +kernel

theorem context_13_417998_766948 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417998 ⟨766948, by decide⟩ :=
  accepted_of_selected 13 417998 ⟨766948, by decide⟩ ⟨13, 2, 0, 766948, 417998, 1013, 16384⟩
    (by decide) selected_cut_30383

theorem selected_cut_30384 : selected 8 ⟨766955, by decide⟩
    (prefixPartial 13 417999) = some ⟨13, 2, 0, 766955, 417999, 701, 16384⟩ := by
  decide +kernel

theorem context_13_417999_766955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 417999 ⟨766955, by decide⟩ :=
  accepted_of_selected 13 417999 ⟨766955, by decide⟩ ⟨13, 2, 0, 766955, 417999, 701, 16384⟩
    (by decide) selected_cut_30384

theorem unmarked_context_12_104499_766956 : frontier 9 ⟨766956, by decide⟩
    (prefixCache 12 104499) (prefixPartial 12 104499) = false := by
  decide +kernel

theorem node_context_12_104499_766956 : EJMOriginalGlobalDAGData.nodes 9 ⟨766956, by decide⟩ =
    .split (coordinate 12) (![⟨766860, by decide⟩,⟨766927, by decide⟩,⟨766948, by decide⟩,⟨766955, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104499_766956 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104499 ⟨766956, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104499
    ⟨766956, by decide⟩ (by decide) (![⟨766860, by decide⟩,⟨766927, by decide⟩,⟨766948, by decide⟩,⟨766955, by decide⟩]) unmarked_context_12_104499_766956 node_context_12_104499_766956
  intro a
  fin_cases a
  · exact context_13_417996_766860
  · exact context_13_417997_766927
  · exact context_13_417998_766948
  · exact context_13_417999_766955

theorem unmarked_context_11_26124_766957 : frontier 10 ⟨766957, by decide⟩
    (prefixCache 11 26124) (prefixPartial 11 26124) = false := by
  decide +kernel

theorem node_context_11_26124_766957 : EJMOriginalGlobalDAGData.nodes 10 ⟨766957, by decide⟩ =
    .split (coordinate 11) (![⟨766630, by decide⟩,⟨766751, by decide⟩,⟨766844, by decide⟩,⟨766956, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26124_766957 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26124 ⟨766957, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26124
    ⟨766957, by decide⟩ (by decide) (![⟨766630, by decide⟩,⟨766751, by decide⟩,⟨766844, by decide⟩,⟨766956, by decide⟩]) unmarked_context_11_26124_766957 node_context_11_26124_766957
  intro a
  fin_cases a
  · exact context_12_104496_766630
  · exact context_12_104497_766751
  · exact context_12_104498_766844
  · exact context_12_104499_766956

theorem selected_cut_30385 : selected 9 ⟨767049, by decide⟩
    (prefixPartial 12 104500) = some ⟨12, 2, 0, 767049, 104500, 3789, 65536⟩ := by
  decide +kernel

theorem context_12_104500_767049 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104500 ⟨767049, by decide⟩ :=
  accepted_of_selected 12 104500 ⟨767049, by decide⟩ ⟨12, 2, 0, 767049, 104500, 3789, 65536⟩
    (by decide) selected_cut_30385

theorem selected_cut_30386 : selected 9 ⟨767139, by decide⟩
    (prefixPartial 12 104501) = some ⟨12, 2, 0, 767139, 104501, 4081, 65536⟩ := by
  decide +kernel

theorem context_12_104501_767139 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104501 ⟨767139, by decide⟩ :=
  accepted_of_selected 12 104501 ⟨767139, by decide⟩ ⟨12, 2, 0, 767139, 104501, 4081, 65536⟩
    (by decide) selected_cut_30386

theorem selected_cut_30387 : selected 9 ⟨767228, by decide⟩
    (prefixPartial 12 104502) = some ⟨12, 2, 0, 767228, 104502, 3885, 65536⟩ := by
  decide +kernel

theorem context_12_104502_767228 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104502 ⟨767228, by decide⟩ :=
  accepted_of_selected 12 104502 ⟨767228, by decide⟩ ⟨12, 2, 0, 767228, 104502, 3885, 65536⟩
    (by decide) selected_cut_30387

theorem selected_cut_30388 : selected 8 ⟨767237, by decide⟩
    (prefixPartial 13 418012) = some ⟨13, 2, 0, 767237, 418012, 457, 16384⟩ := by
  decide +kernel

theorem context_13_418012_767237 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418012 ⟨767237, by decide⟩ :=
  accepted_of_selected 13 418012 ⟨767237, by decide⟩ ⟨13, 2, 0, 767237, 418012, 457, 16384⟩
    (by decide) selected_cut_30388

theorem selected_cut_30389 : selected 8 ⟨767302, by decide⟩
    (prefixPartial 13 418013) = some ⟨13, 2, 0, 767302, 418013, 2289, 16384⟩ := by
  decide +kernel

theorem context_13_418013_767302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418013 ⟨767302, by decide⟩ :=
  accepted_of_selected 13 418013 ⟨767302, by decide⟩ ⟨13, 2, 0, 767302, 418013, 2289, 16384⟩
    (by decide) selected_cut_30389

theorem selected_cut_30390 : selected 8 ⟨767332, by decide⟩
    (prefixPartial 13 418014) = some ⟨13, 2, 0, 767332, 418014, 1165, 16384⟩ := by
  decide +kernel

theorem context_13_418014_767332 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418014 ⟨767332, by decide⟩ :=
  accepted_of_selected 13 418014 ⟨767332, by decide⟩ ⟨13, 2, 0, 767332, 418014, 1165, 16384⟩
    (by decide) selected_cut_30390

theorem selected_cut_30391 : selected 8 ⟨767340, by decide⟩
    (prefixPartial 13 418015) = some ⟨13, 2, 0, 767340, 418015, 741, 16384⟩ := by
  decide +kernel

theorem context_13_418015_767340 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 418015 ⟨767340, by decide⟩ :=
  accepted_of_selected 13 418015 ⟨767340, by decide⟩ ⟨13, 2, 0, 767340, 418015, 741, 16384⟩
    (by decide) selected_cut_30391

theorem unmarked_context_12_104503_767341 : frontier 9 ⟨767341, by decide⟩
    (prefixCache 12 104503) (prefixPartial 12 104503) = false := by
  decide +kernel

theorem node_context_12_104503_767341 : EJMOriginalGlobalDAGData.nodes 9 ⟨767341, by decide⟩ =
    .split (coordinate 12) (![⟨767237, by decide⟩,⟨767302, by decide⟩,⟨767332, by decide⟩,⟨767340, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_104503_767341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104503 ⟨767341, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 104503
    ⟨767341, by decide⟩ (by decide) (![⟨767237, by decide⟩,⟨767302, by decide⟩,⟨767332, by decide⟩,⟨767340, by decide⟩]) unmarked_context_12_104503_767341 node_context_12_104503_767341
  intro a
  fin_cases a
  · exact context_13_418012_767237
  · exact context_13_418013_767302
  · exact context_13_418014_767332
  · exact context_13_418015_767340

theorem unmarked_context_11_26125_767342 : frontier 10 ⟨767342, by decide⟩
    (prefixCache 11 26125) (prefixPartial 11 26125) = false := by
  decide +kernel

theorem node_context_11_26125_767342 : EJMOriginalGlobalDAGData.nodes 10 ⟨767342, by decide⟩ =
    .split (coordinate 11) (![⟨767049, by decide⟩,⟨767139, by decide⟩,⟨767228, by decide⟩,⟨767341, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26125_767342 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26125 ⟨767342, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26125
    ⟨767342, by decide⟩ (by decide) (![⟨767049, by decide⟩,⟨767139, by decide⟩,⟨767228, by decide⟩,⟨767341, by decide⟩]) unmarked_context_11_26125_767342 node_context_11_26125_767342
  intro a
  fin_cases a
  · exact context_12_104500_767049
  · exact context_12_104501_767139
  · exact context_12_104502_767228
  · exact context_12_104503_767341

theorem selected_cut_30392 : selected 9 ⟨767411, by decide⟩
    (prefixPartial 12 104504) = some ⟨12, 2, 0, 767411, 104504, 3425, 65536⟩ := by
  decide +kernel

theorem context_12_104504_767411 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104504 ⟨767411, by decide⟩ :=
  accepted_of_selected 12 104504 ⟨767411, by decide⟩ ⟨12, 2, 0, 767411, 104504, 3425, 65536⟩
    (by decide) selected_cut_30392

theorem selected_cut_30393 : selected 9 ⟨767511, by decide⟩
    (prefixPartial 12 104505) = some ⟨12, 2, 0, 767511, 104505, 3833, 65536⟩ := by
  decide +kernel

theorem context_12_104505_767511 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104505 ⟨767511, by decide⟩ :=
  accepted_of_selected 12 104505 ⟨767511, by decide⟩ ⟨12, 2, 0, 767511, 104505, 3833, 65536⟩
    (by decide) selected_cut_30393

theorem selected_cut_30394 : selected 9 ⟨767574, by decide⟩
    (prefixPartial 12 104506) = some ⟨12, 2, 0, 767574, 104506, 3001, 65536⟩ := by
  decide +kernel

theorem context_12_104506_767574 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104506 ⟨767574, by decide⟩ :=
  accepted_of_selected 12 104506 ⟨767574, by decide⟩ ⟨12, 2, 0, 767574, 104506, 3001, 65536⟩
    (by decide) selected_cut_30394

theorem selected_cut_30395 : selected 9 ⟨767649, by decide⟩
    (prefixPartial 12 104507) = some ⟨12, 2, 0, 767649, 104507, 3945, 65536⟩ := by
  decide +kernel

theorem context_12_104507_767649 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104507 ⟨767649, by decide⟩ :=
  accepted_of_selected 12 104507 ⟨767649, by decide⟩ ⟨12, 2, 0, 767649, 104507, 3945, 65536⟩
    (by decide) selected_cut_30395

theorem unmarked_context_11_26126_767650 : frontier 10 ⟨767650, by decide⟩
    (prefixCache 11 26126) (prefixPartial 11 26126) = false := by
  decide +kernel

theorem node_context_11_26126_767650 : EJMOriginalGlobalDAGData.nodes 10 ⟨767650, by decide⟩ =
    .split (coordinate 11) (![⟨767411, by decide⟩,⟨767511, by decide⟩,⟨767574, by decide⟩,⟨767649, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26126_767650 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26126 ⟨767650, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26126
    ⟨767650, by decide⟩ (by decide) (![⟨767411, by decide⟩,⟨767511, by decide⟩,⟨767574, by decide⟩,⟨767649, by decide⟩]) unmarked_context_11_26126_767650 node_context_11_26126_767650
  intro a
  fin_cases a
  · exact context_12_104504_767411
  · exact context_12_104505_767511
  · exact context_12_104506_767574
  · exact context_12_104507_767649

theorem selected_cut_30396 : selected 9 ⟨767712, by decide⟩
    (prefixPartial 12 104508) = some ⟨12, 2, 0, 767712, 104508, 3313, 65536⟩ := by
  decide +kernel

theorem context_12_104508_767712 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104508 ⟨767712, by decide⟩ :=
  accepted_of_selected 12 104508 ⟨767712, by decide⟩ ⟨12, 2, 0, 767712, 104508, 3313, 65536⟩
    (by decide) selected_cut_30396

theorem selected_cut_30397 : selected 9 ⟨767785, by decide⟩
    (prefixPartial 12 104509) = some ⟨12, 2, 0, 767785, 104509, 3769, 65536⟩ := by
  decide +kernel

theorem context_12_104509_767785 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104509 ⟨767785, by decide⟩ :=
  accepted_of_selected 12 104509 ⟨767785, by decide⟩ ⟨12, 2, 0, 767785, 104509, 3769, 65536⟩
    (by decide) selected_cut_30397

theorem selected_cut_30398 : selected 9 ⟨767847, by decide⟩
    (prefixPartial 12 104510) = some ⟨12, 2, 0, 767847, 104510, 3325, 65536⟩ := by
  decide +kernel

theorem context_12_104510_767847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104510 ⟨767847, by decide⟩ :=
  accepted_of_selected 12 104510 ⟨767847, by decide⟩ ⟨12, 2, 0, 767847, 104510, 3325, 65536⟩
    (by decide) selected_cut_30398

theorem selected_cut_30399 : selected 9 ⟨767913, by decide⟩
    (prefixPartial 12 104511) = some ⟨12, 2, 0, 767913, 104511, 3713, 65536⟩ := by
  decide +kernel

theorem context_12_104511_767913 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104511 ⟨767913, by decide⟩ :=
  accepted_of_selected 12 104511 ⟨767913, by decide⟩ ⟨12, 2, 0, 767913, 104511, 3713, 65536⟩
    (by decide) selected_cut_30399

theorem unmarked_context_11_26127_767914 : frontier 10 ⟨767914, by decide⟩
    (prefixCache 11 26127) (prefixPartial 11 26127) = false := by
  decide +kernel

theorem node_context_11_26127_767914 : EJMOriginalGlobalDAGData.nodes 10 ⟨767914, by decide⟩ =
    .split (coordinate 11) (![⟨767712, by decide⟩,⟨767785, by decide⟩,⟨767847, by decide⟩,⟨767913, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26127_767914 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26127 ⟨767914, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26127
    ⟨767914, by decide⟩ (by decide) (![⟨767712, by decide⟩,⟨767785, by decide⟩,⟨767847, by decide⟩,⟨767913, by decide⟩]) unmarked_context_11_26127_767914 node_context_11_26127_767914
  intro a
  fin_cases a
  · exact context_12_104508_767712
  · exact context_12_104509_767785
  · exact context_12_104510_767847
  · exact context_12_104511_767913

theorem unmarked_context_10_6531_767915 : frontier 11 ⟨767915, by decide⟩
    (prefixCache 10 6531) (prefixPartial 10 6531) = false := by
  decide +kernel

theorem node_context_10_6531_767915 : EJMOriginalGlobalDAGData.nodes 11 ⟨767915, by decide⟩ =
    .split (coordinate 10) (![⟨766957, by decide⟩,⟨767342, by decide⟩,⟨767650, by decide⟩,⟨767914, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6531_767915 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6531 ⟨767915, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6531
    ⟨767915, by decide⟩ (by decide) (![⟨766957, by decide⟩,⟨767342, by decide⟩,⟨767650, by decide⟩,⟨767914, by decide⟩]) unmarked_context_10_6531_767915 node_context_10_6531_767915
  intro a
  fin_cases a
  · exact context_11_26124_766957
  · exact context_11_26125_767342
  · exact context_11_26126_767650
  · exact context_11_26127_767914

theorem unmarked_context_9_1632_767916 : frontier 12 ⟨767916, by decide⟩
    (prefixCache 9 1632) (prefixPartial 9 1632) = false := by
  decide +kernel

theorem node_context_9_1632_767916 : EJMOriginalGlobalDAGData.nodes 12 ⟨767916, by decide⟩ =
    .split (coordinate 9) (![⟨764334, by decide⟩,⟨765705, by decide⟩,⟨766629, by decide⟩,⟨767915, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1632_767916 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1632 ⟨767916, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1632
    ⟨767916, by decide⟩ (by decide) (![⟨764334, by decide⟩,⟨765705, by decide⟩,⟨766629, by decide⟩,⟨767915, by decide⟩]) unmarked_context_9_1632_767916 node_context_9_1632_767916
  intro a
  fin_cases a
  · exact context_10_6528_764334
  · exact context_10_6529_765705
  · exact context_10_6530_766629
  · exact context_10_6531_767915

theorem selected_cut_30400 : selected 11 ⟨3442, by decide⟩
    (prefixPartial 10 6532) = some ⟨10, 1, 0, 3442, 6532, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_6532_3442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6532 ⟨3442, by decide⟩ :=
  accepted_of_selected 10 6532 ⟨3442, by decide⟩ ⟨10, 1, 0, 3442, 6532, 1, 1048576⟩
    (by decide) selected_cut_30400

theorem selected_cut_30401 : selected 9 ⟨768002, by decide⟩
    (prefixPartial 12 104528) = some ⟨12, 2, 0, 768002, 104528, 1093, 65536⟩ := by
  decide +kernel

theorem context_12_104528_768002 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104528 ⟨768002, by decide⟩ :=
  accepted_of_selected 12 104528 ⟨768002, by decide⟩ ⟨12, 2, 0, 768002, 104528, 1093, 65536⟩
    (by decide) selected_cut_30401

theorem selected_cut_30402 : selected 9 ⟨768099, by decide⟩
    (prefixPartial 12 104529) = some ⟨12, 2, 0, 768099, 104529, 3201, 65536⟩ := by
  decide +kernel

theorem context_12_104529_768099 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104529 ⟨768099, by decide⟩ :=
  accepted_of_selected 12 104529 ⟨768099, by decide⟩ ⟨12, 2, 0, 768099, 104529, 3201, 65536⟩
    (by decide) selected_cut_30402

theorem selected_cut_30403 : selected 9 ⟨768173, by decide⟩
    (prefixPartial 12 104530) = some ⟨12, 2, 0, 768173, 104530, 3045, 65536⟩ := by
  decide +kernel

theorem context_12_104530_768173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104530 ⟨768173, by decide⟩ :=
  accepted_of_selected 12 104530 ⟨768173, by decide⟩ ⟨12, 2, 0, 768173, 104530, 3045, 65536⟩
    (by decide) selected_cut_30403

theorem selected_cut_30404 : selected 9 ⟨768256, by decide⟩
    (prefixPartial 12 104531) = some ⟨12, 2, 0, 768256, 104531, 3181, 65536⟩ := by
  decide +kernel

theorem context_12_104531_768256 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104531 ⟨768256, by decide⟩ :=
  accepted_of_selected 12 104531 ⟨768256, by decide⟩ ⟨12, 2, 0, 768256, 104531, 3181, 65536⟩
    (by decide) selected_cut_30404

theorem unmarked_context_11_26132_768257 : frontier 10 ⟨768257, by decide⟩
    (prefixCache 11 26132) (prefixPartial 11 26132) = false := by
  decide +kernel

theorem node_context_11_26132_768257 : EJMOriginalGlobalDAGData.nodes 10 ⟨768257, by decide⟩ =
    .split (coordinate 11) (![⟨768002, by decide⟩,⟨768099, by decide⟩,⟨768173, by decide⟩,⟨768256, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26132_768257 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26132 ⟨768257, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26132
    ⟨768257, by decide⟩ (by decide) (![⟨768002, by decide⟩,⟨768099, by decide⟩,⟨768173, by decide⟩,⟨768256, by decide⟩]) unmarked_context_11_26132_768257 node_context_11_26132_768257
  intro a
  fin_cases a
  · exact context_12_104528_768002
  · exact context_12_104529_768099
  · exact context_12_104530_768173
  · exact context_12_104531_768256

theorem selected_cut_30405 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 104532) = some ⟨12, 1, 0, 895, 104532, 1, 65536⟩ := by
  decide +kernel

theorem context_12_104532_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104532 ⟨895, by decide⟩ :=
  accepted_of_selected 12 104532 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 104532, 1, 65536⟩
    (by decide) selected_cut_30405

theorem selected_cut_30406 : selected 9 ⟨768318, by decide⟩
    (prefixPartial 12 104533) = some ⟨12, 2, 0, 768318, 104533, 1665, 65536⟩ := by
  decide +kernel

theorem context_12_104533_768318 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104533 ⟨768318, by decide⟩ :=
  accepted_of_selected 12 104533 ⟨768318, by decide⟩ ⟨12, 2, 0, 768318, 104533, 1665, 65536⟩
    (by decide) selected_cut_30406

theorem selected_cut_30407 : selected 9 ⟨768382, by decide⟩
    (prefixPartial 12 104534) = some ⟨12, 2, 0, 768382, 104534, 2837, 65536⟩ := by
  decide +kernel

theorem context_12_104534_768382 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104534 ⟨768382, by decide⟩ :=
  accepted_of_selected 12 104534 ⟨768382, by decide⟩ ⟨12, 2, 0, 768382, 104534, 2837, 65536⟩
    (by decide) selected_cut_30407

theorem selected_cut_30408 : selected 9 ⟨768479, by decide⟩
    (prefixPartial 12 104535) = some ⟨12, 2, 0, 768479, 104535, 2973, 65536⟩ := by
  decide +kernel

theorem context_12_104535_768479 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104535 ⟨768479, by decide⟩ :=
  accepted_of_selected 12 104535 ⟨768479, by decide⟩ ⟨12, 2, 0, 768479, 104535, 2973, 65536⟩
    (by decide) selected_cut_30408

theorem unmarked_context_11_26133_768480 : frontier 10 ⟨768480, by decide⟩
    (prefixCache 11 26133) (prefixPartial 11 26133) = false := by
  decide +kernel

theorem node_context_11_26133_768480 : EJMOriginalGlobalDAGData.nodes 10 ⟨768480, by decide⟩ =
    .split (coordinate 11) (![⟨895, by decide⟩,⟨768318, by decide⟩,⟨768382, by decide⟩,⟨768479, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26133_768480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26133 ⟨768480, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26133
    ⟨768480, by decide⟩ (by decide) (![⟨895, by decide⟩,⟨768318, by decide⟩,⟨768382, by decide⟩,⟨768479, by decide⟩]) unmarked_context_11_26133_768480 node_context_11_26133_768480
  intro a
  fin_cases a
  · exact context_12_104532_895
  · exact context_12_104533_768318
  · exact context_12_104534_768382
  · exact context_12_104535_768479

theorem selected_cut_30409 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 104536) = some ⟨12, 1, 0, 895, 104536, 1, 65536⟩ := by
  decide +kernel

theorem context_12_104536_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104536 ⟨895, by decide⟩ :=
  accepted_of_selected 12 104536 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 104536, 1, 65536⟩
    (by decide) selected_cut_30409

theorem selected_cut_30410 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 104537) = some ⟨12, 1, 0, 895, 104537, 1, 65536⟩ := by
  decide +kernel

theorem context_12_104537_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104537 ⟨895, by decide⟩ :=
  accepted_of_selected 12 104537 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 104537, 1, 65536⟩
    (by decide) selected_cut_30410

theorem selected_cut_30411 : selected 9 ⟨768533, by decide⟩
    (prefixPartial 12 104538) = some ⟨12, 2, 0, 768533, 104538, 1561, 65536⟩ := by
  decide +kernel

theorem context_12_104538_768533 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104538 ⟨768533, by decide⟩ :=
  accepted_of_selected 12 104538 ⟨768533, by decide⟩ ⟨12, 2, 0, 768533, 104538, 1561, 65536⟩
    (by decide) selected_cut_30411

theorem selected_cut_30412 : selected 9 ⟨768586, by decide⟩
    (prefixPartial 12 104539) = some ⟨12, 2, 0, 768586, 104539, 2693, 65536⟩ := by
  decide +kernel

theorem context_12_104539_768586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104539 ⟨768586, by decide⟩ :=
  accepted_of_selected 12 104539 ⟨768586, by decide⟩ ⟨12, 2, 0, 768586, 104539, 2693, 65536⟩
    (by decide) selected_cut_30412

theorem unmarked_context_11_26134_768587 : frontier 10 ⟨768587, by decide⟩
    (prefixCache 11 26134) (prefixPartial 11 26134) = false := by
  decide +kernel

theorem node_context_11_26134_768587 : EJMOriginalGlobalDAGData.nodes 10 ⟨768587, by decide⟩ =
    .split (coordinate 11) (![⟨895, by decide⟩,⟨895, by decide⟩,⟨768533, by decide⟩,⟨768586, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26134_768587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26134 ⟨768587, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26134
    ⟨768587, by decide⟩ (by decide) (![⟨895, by decide⟩,⟨895, by decide⟩,⟨768533, by decide⟩,⟨768586, by decide⟩]) unmarked_context_11_26134_768587 node_context_11_26134_768587
  intro a
  fin_cases a
  · exact context_12_104536_895
  · exact context_12_104537_895
  · exact context_12_104538_768533
  · exact context_12_104539_768586

theorem selected_cut_30413 : selected 10 ⟨768637, by decide⟩
    (prefixPartial 11 26135) = some ⟨11, 2, 0, 768637, 26135, 1645, 262144⟩ := by
  decide +kernel

theorem context_11_26135_768637 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26135 ⟨768637, by decide⟩ :=
  accepted_of_selected 11 26135 ⟨768637, by decide⟩ ⟨11, 2, 0, 768637, 26135, 1645, 262144⟩
    (by decide) selected_cut_30413

theorem unmarked_context_10_6533_768638 : frontier 11 ⟨768638, by decide⟩
    (prefixCache 10 6533) (prefixPartial 10 6533) = false := by
  decide +kernel

theorem node_context_10_6533_768638 : EJMOriginalGlobalDAGData.nodes 11 ⟨768638, by decide⟩ =
    .split (coordinate 10) (![⟨768257, by decide⟩,⟨768480, by decide⟩,⟨768587, by decide⟩,⟨768637, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6533_768638 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6533 ⟨768638, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6533
    ⟨768638, by decide⟩ (by decide) (![⟨768257, by decide⟩,⟨768480, by decide⟩,⟨768587, by decide⟩,⟨768637, by decide⟩]) unmarked_context_10_6533_768638 node_context_10_6533_768638
  intro a
  fin_cases a
  · exact context_11_26132_768257
  · exact context_11_26133_768480
  · exact context_11_26134_768587
  · exact context_11_26135_768637

theorem selected_cut_30414 : selected 9 ⟨765706, by decide⟩
    (prefixPartial 12 104544) = some ⟨12, 1, 0, 765706, 104544, 1, 65536⟩ := by
  decide +kernel

theorem context_12_104544_765706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104544 ⟨765706, by decide⟩ :=
  accepted_of_selected 12 104544 ⟨765706, by decide⟩ ⟨12, 1, 0, 765706, 104544, 1, 65536⟩
    (by decide) selected_cut_30414

theorem selected_cut_30415 : selected 9 ⟨768694, by decide⟩
    (prefixPartial 12 104545) = some ⟨12, 2, 0, 768694, 104545, 2425, 65536⟩ := by
  decide +kernel

theorem context_12_104545_768694 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104545 ⟨768694, by decide⟩ :=
  accepted_of_selected 12 104545 ⟨768694, by decide⟩ ⟨12, 2, 0, 768694, 104545, 2425, 65536⟩
    (by decide) selected_cut_30415

theorem selected_cut_30416 : selected 9 ⟨768739, by decide⟩
    (prefixPartial 12 104546) = some ⟨12, 2, 0, 768739, 104546, 2369, 65536⟩ := by
  decide +kernel

theorem context_12_104546_768739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104546 ⟨768739, by decide⟩ :=
  accepted_of_selected 12 104546 ⟨768739, by decide⟩ ⟨12, 2, 0, 768739, 104546, 2369, 65536⟩
    (by decide) selected_cut_30416

theorem selected_cut_30417 : selected 9 ⟨768787, by decide⟩
    (prefixPartial 12 104547) = some ⟨12, 2, 0, 768787, 104547, 2509, 65536⟩ := by
  decide +kernel

theorem context_12_104547_768787 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104547 ⟨768787, by decide⟩ :=
  accepted_of_selected 12 104547 ⟨768787, by decide⟩ ⟨12, 2, 0, 768787, 104547, 2509, 65536⟩
    (by decide) selected_cut_30417

theorem unmarked_context_11_26136_768788 : frontier 10 ⟨768788, by decide⟩
    (prefixCache 11 26136) (prefixPartial 11 26136) = false := by
  decide +kernel

theorem node_context_11_26136_768788 : EJMOriginalGlobalDAGData.nodes 10 ⟨768788, by decide⟩ =
    .split (coordinate 11) (![⟨765706, by decide⟩,⟨768694, by decide⟩,⟨768739, by decide⟩,⟨768787, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26136_768788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26136 ⟨768788, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26136
    ⟨768788, by decide⟩ (by decide) (![⟨765706, by decide⟩,⟨768694, by decide⟩,⟨768739, by decide⟩,⟨768787, by decide⟩]) unmarked_context_11_26136_768788 node_context_11_26136_768788
  intro a
  fin_cases a
  · exact context_12_104544_765706
  · exact context_12_104545_768694
  · exact context_12_104546_768739
  · exact context_12_104547_768787

theorem selected_cut_30418 : selected 9 ⟨768866, by decide⟩
    (prefixPartial 12 104548) = some ⟨12, 2, 0, 768866, 104548, 2589, 65536⟩ := by
  decide +kernel

theorem context_12_104548_768866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104548 ⟨768866, by decide⟩ :=
  accepted_of_selected 12 104548 ⟨768866, by decide⟩ ⟨12, 2, 0, 768866, 104548, 2589, 65536⟩
    (by decide) selected_cut_30418

theorem selected_cut_30419 : selected 9 ⟨768922, by decide⟩
    (prefixPartial 12 104549) = some ⟨12, 2, 0, 768922, 104549, 2205, 65536⟩ := by
  decide +kernel

theorem context_12_104549_768922 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104549 ⟨768922, by decide⟩ :=
  accepted_of_selected 12 104549 ⟨768922, by decide⟩ ⟨12, 2, 0, 768922, 104549, 2205, 65536⟩
    (by decide) selected_cut_30419

theorem selected_cut_30420 : selected 9 ⟨768980, by decide⟩
    (prefixPartial 12 104550) = some ⟨12, 2, 0, 768980, 104550, 2373, 65536⟩ := by
  decide +kernel

theorem context_12_104550_768980 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104550 ⟨768980, by decide⟩ :=
  accepted_of_selected 12 104550 ⟨768980, by decide⟩ ⟨12, 2, 0, 768980, 104550, 2373, 65536⟩
    (by decide) selected_cut_30420

theorem selected_cut_30421 : selected 9 ⟨769028, by decide⟩
    (prefixPartial 12 104551) = some ⟨12, 2, 0, 769028, 104551, 2505, 65536⟩ := by
  decide +kernel

theorem context_12_104551_769028 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104551 ⟨769028, by decide⟩ :=
  accepted_of_selected 12 104551 ⟨769028, by decide⟩ ⟨12, 2, 0, 769028, 104551, 2505, 65536⟩
    (by decide) selected_cut_30421

theorem unmarked_context_11_26137_769029 : frontier 10 ⟨769029, by decide⟩
    (prefixCache 11 26137) (prefixPartial 11 26137) = false := by
  decide +kernel

theorem node_context_11_26137_769029 : EJMOriginalGlobalDAGData.nodes 10 ⟨769029, by decide⟩ =
    .split (coordinate 11) (![⟨768866, by decide⟩,⟨768922, by decide⟩,⟨768980, by decide⟩,⟨769028, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26137_769029 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26137 ⟨769029, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26137
    ⟨769029, by decide⟩ (by decide) (![⟨768866, by decide⟩,⟨768922, by decide⟩,⟨768980, by decide⟩,⟨769028, by decide⟩]) unmarked_context_11_26137_769029 node_context_11_26137_769029
  intro a
  fin_cases a
  · exact context_12_104548_768866
  · exact context_12_104549_768922
  · exact context_12_104550_768980
  · exact context_12_104551_769028

theorem selected_cut_30422 : selected 9 ⟨242157, by decide⟩
    (prefixPartial 12 104552) = some ⟨12, 1, 0, 242157, 104552, 1, 65536⟩ := by
  decide +kernel

theorem context_12_104552_242157 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104552 ⟨242157, by decide⟩ :=
  accepted_of_selected 12 104552 ⟨242157, by decide⟩ ⟨12, 1, 0, 242157, 104552, 1, 65536⟩
    (by decide) selected_cut_30422

theorem selected_cut_30423 : selected 9 ⟨769103, by decide⟩
    (prefixPartial 12 104553) = some ⟨12, 2, 0, 769103, 104553, 885, 65536⟩ := by
  decide +kernel

theorem context_12_104553_769103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104553 ⟨769103, by decide⟩ :=
  accepted_of_selected 12 104553 ⟨769103, by decide⟩ ⟨12, 2, 0, 769103, 104553, 885, 65536⟩
    (by decide) selected_cut_30423

theorem selected_cut_30424 : selected 9 ⟨769104, by decide⟩
    (prefixPartial 12 104554) = some ⟨12, 1, 0, 769104, 104554, 1, 65536⟩ := by
  decide +kernel

theorem context_12_104554_769104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104554 ⟨769104, by decide⟩ :=
  accepted_of_selected 12 104554 ⟨769104, by decide⟩ ⟨12, 1, 0, 769104, 104554, 1, 65536⟩
    (by decide) selected_cut_30424

theorem selected_cut_30425 : selected 9 ⟨769227, by decide⟩
    (prefixPartial 12 104555) = some ⟨12, 2, 0, 769227, 104555, 3273, 65536⟩ := by
  decide +kernel

theorem context_12_104555_769227 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104555 ⟨769227, by decide⟩ :=
  accepted_of_selected 12 104555 ⟨769227, by decide⟩ ⟨12, 2, 0, 769227, 104555, 3273, 65536⟩
    (by decide) selected_cut_30425

theorem unmarked_context_11_26138_769228 : frontier 10 ⟨769228, by decide⟩
    (prefixCache 11 26138) (prefixPartial 11 26138) = false := by
  decide +kernel

theorem node_context_11_26138_769228 : EJMOriginalGlobalDAGData.nodes 10 ⟨769228, by decide⟩ =
    .split (coordinate 11) (![⟨242157, by decide⟩,⟨769103, by decide⟩,⟨769104, by decide⟩,⟨769227, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26138_769228 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26138 ⟨769228, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26138
    ⟨769228, by decide⟩ (by decide) (![⟨242157, by decide⟩,⟨769103, by decide⟩,⟨769104, by decide⟩,⟨769227, by decide⟩]) unmarked_context_11_26138_769228 node_context_11_26138_769228
  intro a
  fin_cases a
  · exact context_12_104552_242157
  · exact context_12_104553_769103
  · exact context_12_104554_769104
  · exact context_12_104555_769227

theorem selected_cut_30426 : selected 9 ⟨769268, by decide⟩
    (prefixPartial 12 104556) = some ⟨12, 2, 0, 769268, 104556, 2001, 65536⟩ := by
  decide +kernel

theorem context_12_104556_769268 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104556 ⟨769268, by decide⟩ :=
  accepted_of_selected 12 104556 ⟨769268, by decide⟩ ⟨12, 2, 0, 769268, 104556, 2001, 65536⟩
    (by decide) selected_cut_30426

theorem selected_cut_30427 : selected 9 ⟨769303, by decide⟩
    (prefixPartial 12 104557) = some ⟨12, 2, 0, 769303, 104557, 1869, 65536⟩ := by
  decide +kernel

theorem context_12_104557_769303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104557 ⟨769303, by decide⟩ :=
  accepted_of_selected 12 104557 ⟨769303, by decide⟩ ⟨12, 2, 0, 769303, 104557, 1869, 65536⟩
    (by decide) selected_cut_30427

theorem selected_cut_30428 : selected 9 ⟨769332, by decide⟩
    (prefixPartial 12 104558) = some ⟨12, 2, 0, 769332, 104558, 1793, 65536⟩ := by
  decide +kernel

theorem context_12_104558_769332 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104558 ⟨769332, by decide⟩ :=
  accepted_of_selected 12 104558 ⟨769332, by decide⟩ ⟨12, 2, 0, 769332, 104558, 1793, 65536⟩
    (by decide) selected_cut_30428

theorem selected_cut_30429 : selected 9 ⟨769362, by decide⟩
    (prefixPartial 12 104559) = some ⟨12, 2, 0, 769362, 104559, 1717, 65536⟩ := by
  decide +kernel

theorem context_12_104559_769362 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104559 ⟨769362, by decide⟩ :=
  accepted_of_selected 12 104559 ⟨769362, by decide⟩ ⟨12, 2, 0, 769362, 104559, 1717, 65536⟩
    (by decide) selected_cut_30429

theorem unmarked_context_11_26139_769363 : frontier 10 ⟨769363, by decide⟩
    (prefixCache 11 26139) (prefixPartial 11 26139) = false := by
  decide +kernel

theorem node_context_11_26139_769363 : EJMOriginalGlobalDAGData.nodes 10 ⟨769363, by decide⟩ =
    .split (coordinate 11) (![⟨769268, by decide⟩,⟨769303, by decide⟩,⟨769332, by decide⟩,⟨769362, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26139_769363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26139 ⟨769363, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26139
    ⟨769363, by decide⟩ (by decide) (![⟨769268, by decide⟩,⟨769303, by decide⟩,⟨769332, by decide⟩,⟨769362, by decide⟩]) unmarked_context_11_26139_769363 node_context_11_26139_769363
  intro a
  fin_cases a
  · exact context_12_104556_769268
  · exact context_12_104557_769303
  · exact context_12_104558_769332
  · exact context_12_104559_769362

theorem unmarked_context_10_6534_769364 : frontier 11 ⟨769364, by decide⟩
    (prefixCache 10 6534) (prefixPartial 10 6534) = false := by
  decide +kernel

theorem node_context_10_6534_769364 : EJMOriginalGlobalDAGData.nodes 11 ⟨769364, by decide⟩ =
    .split (coordinate 10) (![⟨768788, by decide⟩,⟨769029, by decide⟩,⟨769228, by decide⟩,⟨769363, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6534_769364 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6534 ⟨769364, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6534
    ⟨769364, by decide⟩ (by decide) (![⟨768788, by decide⟩,⟨769029, by decide⟩,⟨769228, by decide⟩,⟨769363, by decide⟩]) unmarked_context_10_6534_769364 node_context_10_6534_769364
  intro a
  fin_cases a
  · exact context_11_26136_768788
  · exact context_11_26137_769029
  · exact context_11_26138_769228
  · exact context_11_26139_769363

theorem selected_cut_30430 : selected 9 ⟨769468, by decide⟩
    (prefixPartial 12 104560) = some ⟨12, 2, 0, 769468, 104560, 2757, 65536⟩ := by
  decide +kernel

theorem context_12_104560_769468 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104560 ⟨769468, by decide⟩ :=
  accepted_of_selected 12 104560 ⟨769468, by decide⟩ ⟨12, 2, 0, 769468, 104560, 2757, 65536⟩
    (by decide) selected_cut_30430

theorem selected_cut_30431 : selected 9 ⟨769507, by decide⟩
    (prefixPartial 12 104561) = some ⟨12, 2, 0, 769507, 104561, 1809, 65536⟩ := by
  decide +kernel

theorem context_12_104561_769507 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104561 ⟨769507, by decide⟩ :=
  accepted_of_selected 12 104561 ⟨769507, by decide⟩ ⟨12, 2, 0, 769507, 104561, 1809, 65536⟩
    (by decide) selected_cut_30431

theorem selected_cut_30432 : selected 9 ⟨769536, by decide⟩
    (prefixPartial 12 104562) = some ⟨12, 2, 0, 769536, 104562, 1621, 65536⟩ := by
  decide +kernel

theorem context_12_104562_769536 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104562 ⟨769536, by decide⟩ :=
  accepted_of_selected 12 104562 ⟨769536, by decide⟩ ⟨12, 2, 0, 769536, 104562, 1621, 65536⟩
    (by decide) selected_cut_30432

theorem selected_cut_30433 : selected 9 ⟨769575, by decide⟩
    (prefixPartial 12 104563) = some ⟨12, 2, 0, 769575, 104563, 1841, 65536⟩ := by
  decide +kernel

theorem context_12_104563_769575 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104563 ⟨769575, by decide⟩ :=
  accepted_of_selected 12 104563 ⟨769575, by decide⟩ ⟨12, 2, 0, 769575, 104563, 1841, 65536⟩
    (by decide) selected_cut_30433

theorem unmarked_context_11_26140_769576 : frontier 10 ⟨769576, by decide⟩
    (prefixCache 11 26140) (prefixPartial 11 26140) = false := by
  decide +kernel

theorem node_context_11_26140_769576 : EJMOriginalGlobalDAGData.nodes 10 ⟨769576, by decide⟩ =
    .split (coordinate 11) (![⟨769468, by decide⟩,⟨769507, by decide⟩,⟨769536, by decide⟩,⟨769575, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26140_769576 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26140 ⟨769576, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26140
    ⟨769576, by decide⟩ (by decide) (![⟨769468, by decide⟩,⟨769507, by decide⟩,⟨769536, by decide⟩,⟨769575, by decide⟩]) unmarked_context_11_26140_769576 node_context_11_26140_769576
  intro a
  fin_cases a
  · exact context_12_104560_769468
  · exact context_12_104561_769507
  · exact context_12_104562_769536
  · exact context_12_104563_769575

theorem selected_cut_30434 : selected 9 ⟨769616, by decide⟩
    (prefixPartial 12 104564) = some ⟨12, 2, 0, 769616, 104564, 1697, 65536⟩ := by
  decide +kernel

theorem context_12_104564_769616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 104564 ⟨769616, by decide⟩ :=
  accepted_of_selected 12 104564 ⟨769616, by decide⟩ ⟨12, 2, 0, 769616, 104564, 1697, 65536⟩
    (by decide) selected_cut_30434

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
