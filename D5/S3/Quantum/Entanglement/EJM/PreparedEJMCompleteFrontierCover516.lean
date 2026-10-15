/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover515
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_9_6375_1402375 : frontier 12 ⟨1402375, by decide⟩
    (prefixCache 9 6375) (prefixPartial 9 6375) = false := by
  decide +kernel

theorem node_context_9_6375_1402375 : EJMOriginalGlobalDAGData.nodes 12 ⟨1402375, by decide⟩ =
    .split (coordinate 9) (![⟨1402288, by decide⟩,⟨1402333, by decide⟩,⟨1402365, by decide⟩,⟨1402374, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6375_1402375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6375 ⟨1402375, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6375
    ⟨1402375, by decide⟩ (by decide) (![⟨1402288, by decide⟩,⟨1402333, by decide⟩,⟨1402365, by decide⟩,⟨1402374, by decide⟩]) unmarked_context_9_6375_1402375 node_context_9_6375_1402375
  intro a
  fin_cases a
  · exact context_10_25500_1402288
  · exact context_10_25501_1402333
  · exact context_10_25502_1402365
  · exact context_10_25503_1402374

theorem unmarked_context_8_1593_1402376 : frontier 13 ⟨1402376, by decide⟩
    (prefixCache 8 1593) (prefixPartial 8 1593) = false := by
  decide +kernel

theorem node_context_8_1593_1402376 : EJMOriginalGlobalDAGData.nodes 13 ⟨1402376, by decide⟩ =
    .split (coordinate 8) (![⟨1401347, by decide⟩,⟨1401877, by decide⟩,⟨1402223, by decide⟩,⟨1402375, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1593_1402376 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1593 ⟨1402376, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1593
    ⟨1402376, by decide⟩ (by decide) (![⟨1401347, by decide⟩,⟨1401877, by decide⟩,⟨1402223, by decide⟩,⟨1402375, by decide⟩]) unmarked_context_8_1593_1402376 node_context_8_1593_1402376
  intro a
  fin_cases a
  · exact context_9_6372_1401347
  · exact context_9_6373_1401877
  · exact context_9_6374_1402223
  · exact context_9_6375_1402375

theorem selected_cut_49540 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 102016) = some ⟨11, 1, 0, 434745, 102016, 1, 262144⟩ := by
  decide +kernel

theorem context_11_102016_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102016 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 102016 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 102016, 1, 262144⟩
    (by decide) selected_cut_49540

theorem selected_cut_49541 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 102017) = some ⟨11, 1, 0, 434745, 102017, 1, 262144⟩ := by
  decide +kernel

theorem context_11_102017_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102017 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 102017 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 102017, 1, 262144⟩
    (by decide) selected_cut_49541

theorem selected_cut_49542 : selected 10 ⟨1402416, by decide⟩
    (prefixPartial 11 102018) = some ⟨11, 2, 0, 1402416, 102018, 1905, 262144⟩ := by
  decide +kernel

theorem context_11_102018_1402416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102018 ⟨1402416, by decide⟩ :=
  accepted_of_selected 11 102018 ⟨1402416, by decide⟩ ⟨11, 2, 0, 1402416, 102018, 1905, 262144⟩
    (by decide) selected_cut_49542

theorem selected_cut_49543 : selected 10 ⟨1402498, by decide⟩
    (prefixPartial 11 102019) = some ⟨11, 2, 0, 1402498, 102019, 2645, 262144⟩ := by
  decide +kernel

theorem context_11_102019_1402498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102019 ⟨1402498, by decide⟩ :=
  accepted_of_selected 11 102019 ⟨1402498, by decide⟩ ⟨11, 2, 0, 1402498, 102019, 2645, 262144⟩
    (by decide) selected_cut_49543

theorem unmarked_context_10_25504_1402499 : frontier 11 ⟨1402499, by decide⟩
    (prefixCache 10 25504) (prefixPartial 10 25504) = false := by
  decide +kernel

theorem node_context_10_25504_1402499 : EJMOriginalGlobalDAGData.nodes 11 ⟨1402499, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨434745, by decide⟩,⟨1402416, by decide⟩,⟨1402498, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25504_1402499 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25504 ⟨1402499, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25504
    ⟨1402499, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨434745, by decide⟩,⟨1402416, by decide⟩,⟨1402498, by decide⟩]) unmarked_context_10_25504_1402499 node_context_10_25504_1402499
  intro a
  fin_cases a
  · exact context_11_102016_434745
  · exact context_11_102017_434745
  · exact context_11_102018_1402416
  · exact context_11_102019_1402498

theorem selected_cut_49544 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 408080) = some ⟨12, 1, 0, 1108174, 408080, 1, 65536⟩ := by
  decide +kernel

theorem context_12_408080_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408080 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 408080 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 408080, 1, 65536⟩
    (by decide) selected_cut_49544

theorem selected_cut_49545 : selected 9 ⟨1402570, by decide⟩
    (prefixPartial 12 408081) = some ⟨12, 2, 0, 1402570, 408081, 2581, 65536⟩ := by
  decide +kernel

theorem context_12_408081_1402570 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408081 ⟨1402570, by decide⟩ :=
  accepted_of_selected 12 408081 ⟨1402570, by decide⟩ ⟨12, 2, 0, 1402570, 408081, 2581, 65536⟩
    (by decide) selected_cut_49545

theorem selected_cut_49546 : selected 9 ⟨1402626, by decide⟩
    (prefixPartial 12 408082) = some ⟨12, 2, 0, 1402626, 408082, 2229, 65536⟩ := by
  decide +kernel

theorem context_12_408082_1402626 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408082 ⟨1402626, by decide⟩ :=
  accepted_of_selected 12 408082 ⟨1402626, by decide⟩ ⟨12, 2, 0, 1402626, 408082, 2229, 65536⟩
    (by decide) selected_cut_49546

theorem selected_cut_49547 : selected 9 ⟨1402685, by decide⟩
    (prefixPartial 12 408083) = some ⟨12, 2, 0, 1402685, 408083, 2401, 65536⟩ := by
  decide +kernel

theorem context_12_408083_1402685 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408083 ⟨1402685, by decide⟩ :=
  accepted_of_selected 12 408083 ⟨1402685, by decide⟩ ⟨12, 2, 0, 1402685, 408083, 2401, 65536⟩
    (by decide) selected_cut_49547

theorem unmarked_context_11_102020_1402686 : frontier 10 ⟨1402686, by decide⟩
    (prefixCache 11 102020) (prefixPartial 11 102020) = false := by
  decide +kernel

theorem node_context_11_102020_1402686 : EJMOriginalGlobalDAGData.nodes 10 ⟨1402686, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1402570, by decide⟩,⟨1402626, by decide⟩,⟨1402685, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_102020_1402686 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102020 ⟨1402686, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 102020
    ⟨1402686, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1402570, by decide⟩,⟨1402626, by decide⟩,⟨1402685, by decide⟩]) unmarked_context_11_102020_1402686 node_context_11_102020_1402686
  intro a
  fin_cases a
  · exact context_12_408080_1108174
  · exact context_12_408081_1402570
  · exact context_12_408082_1402626
  · exact context_12_408083_1402685

theorem selected_cut_49548 : selected 10 ⟨1400670, by decide⟩
    (prefixPartial 11 102021) = some ⟨11, 2, 0, 1400670, 102021, 5, 262144⟩ := by
  decide +kernel

theorem context_11_102021_1400670 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102021 ⟨1400670, by decide⟩ :=
  accepted_of_selected 11 102021 ⟨1400670, by decide⟩ ⟨11, 2, 0, 1400670, 102021, 5, 262144⟩
    (by decide) selected_cut_49548

theorem selected_cut_49549 : selected 10 ⟨1402774, by decide⟩
    (prefixPartial 11 102022) = some ⟨11, 2, 0, 1402774, 102022, 3781, 262144⟩ := by
  decide +kernel

theorem context_11_102022_1402774 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102022 ⟨1402774, by decide⟩ :=
  accepted_of_selected 11 102022 ⟨1402774, by decide⟩ ⟨11, 2, 0, 1402774, 102022, 3781, 262144⟩
    (by decide) selected_cut_49549

theorem selected_cut_49550 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 408092) = some ⟨12, 1, 0, 1108174, 408092, 1, 65536⟩ := by
  decide +kernel

theorem context_12_408092_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408092 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 408092 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 408092, 1, 65536⟩
    (by decide) selected_cut_49550

theorem selected_cut_49551 : selected 9 ⟨1402823, by decide⟩
    (prefixPartial 12 408093) = some ⟨12, 2, 0, 1402823, 408093, 2117, 65536⟩ := by
  decide +kernel

theorem context_12_408093_1402823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408093 ⟨1402823, by decide⟩ :=
  accepted_of_selected 12 408093 ⟨1402823, by decide⟩ ⟨12, 2, 0, 1402823, 408093, 2117, 65536⟩
    (by decide) selected_cut_49551

theorem selected_cut_49552 : selected 9 ⟨1402871, by decide⟩
    (prefixPartial 12 408094) = some ⟨12, 2, 0, 1402871, 408094, 2113, 65536⟩ := by
  decide +kernel

theorem context_12_408094_1402871 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408094 ⟨1402871, by decide⟩ :=
  accepted_of_selected 12 408094 ⟨1402871, by decide⟩ ⟨12, 2, 0, 1402871, 408094, 2113, 65536⟩
    (by decide) selected_cut_49552

theorem selected_cut_49553 : selected 9 ⟨1402912, by decide⟩
    (prefixPartial 12 408095) = some ⟨12, 2, 0, 1402912, 408095, 1965, 65536⟩ := by
  decide +kernel

theorem context_12_408095_1402912 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408095 ⟨1402912, by decide⟩ :=
  accepted_of_selected 12 408095 ⟨1402912, by decide⟩ ⟨12, 2, 0, 1402912, 408095, 1965, 65536⟩
    (by decide) selected_cut_49553

theorem unmarked_context_11_102023_1402913 : frontier 10 ⟨1402913, by decide⟩
    (prefixCache 11 102023) (prefixPartial 11 102023) = false := by
  decide +kernel

theorem node_context_11_102023_1402913 : EJMOriginalGlobalDAGData.nodes 10 ⟨1402913, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1402823, by decide⟩,⟨1402871, by decide⟩,⟨1402912, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_102023_1402913 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102023 ⟨1402913, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 102023
    ⟨1402913, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1402823, by decide⟩,⟨1402871, by decide⟩,⟨1402912, by decide⟩]) unmarked_context_11_102023_1402913 node_context_11_102023_1402913
  intro a
  fin_cases a
  · exact context_12_408092_1108174
  · exact context_12_408093_1402823
  · exact context_12_408094_1402871
  · exact context_12_408095_1402912

theorem unmarked_context_10_25505_1402914 : frontier 11 ⟨1402914, by decide⟩
    (prefixCache 10 25505) (prefixPartial 10 25505) = false := by
  decide +kernel

theorem node_context_10_25505_1402914 : EJMOriginalGlobalDAGData.nodes 11 ⟨1402914, by decide⟩ =
    .split (coordinate 10) (![⟨1402686, by decide⟩,⟨1400670, by decide⟩,⟨1402774, by decide⟩,⟨1402913, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25505_1402914 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25505 ⟨1402914, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25505
    ⟨1402914, by decide⟩ (by decide) (![⟨1402686, by decide⟩,⟨1400670, by decide⟩,⟨1402774, by decide⟩,⟨1402913, by decide⟩]) unmarked_context_10_25505_1402914 node_context_10_25505_1402914
  intro a
  fin_cases a
  · exact context_11_102020_1402686
  · exact context_11_102021_1400670
  · exact context_11_102022_1402774
  · exact context_11_102023_1402913

theorem selected_cut_49554 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 408096) = some ⟨12, 1, 0, 1108174, 408096, 1, 65536⟩ := by
  decide +kernel

theorem context_12_408096_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408096 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 408096 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 408096, 1, 65536⟩
    (by decide) selected_cut_49554

theorem selected_cut_49555 : selected 9 ⟨1402982, by decide⟩
    (prefixPartial 12 408097) = some ⟨12, 2, 0, 1402982, 408097, 2337, 65536⟩ := by
  decide +kernel

theorem context_12_408097_1402982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408097 ⟨1402982, by decide⟩ :=
  accepted_of_selected 12 408097 ⟨1402982, by decide⟩ ⟨12, 2, 0, 1402982, 408097, 2337, 65536⟩
    (by decide) selected_cut_49555

theorem selected_cut_49556 : selected 9 ⟨1403031, by decide⟩
    (prefixPartial 12 408098) = some ⟨12, 2, 0, 1403031, 408098, 1885, 65536⟩ := by
  decide +kernel

theorem context_12_408098_1403031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408098 ⟨1403031, by decide⟩ :=
  accepted_of_selected 12 408098 ⟨1403031, by decide⟩ ⟨12, 2, 0, 1403031, 408098, 1885, 65536⟩
    (by decide) selected_cut_49556

theorem selected_cut_49557 : selected 9 ⟨1403085, by decide⟩
    (prefixPartial 12 408099) = some ⟨12, 2, 0, 1403085, 408099, 1957, 65536⟩ := by
  decide +kernel

theorem context_12_408099_1403085 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408099 ⟨1403085, by decide⟩ :=
  accepted_of_selected 12 408099 ⟨1403085, by decide⟩ ⟨12, 2, 0, 1403085, 408099, 1957, 65536⟩
    (by decide) selected_cut_49557

theorem unmarked_context_11_102024_1403086 : frontier 10 ⟨1403086, by decide⟩
    (prefixCache 11 102024) (prefixPartial 11 102024) = false := by
  decide +kernel

theorem node_context_11_102024_1403086 : EJMOriginalGlobalDAGData.nodes 10 ⟨1403086, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1402982, by decide⟩,⟨1403031, by decide⟩,⟨1403085, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_102024_1403086 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102024 ⟨1403086, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 102024
    ⟨1403086, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1402982, by decide⟩,⟨1403031, by decide⟩,⟨1403085, by decide⟩]) unmarked_context_11_102024_1403086 node_context_11_102024_1403086
  intro a
  fin_cases a
  · exact context_12_408096_1108174
  · exact context_12_408097_1402982
  · exact context_12_408098_1403031
  · exact context_12_408099_1403085

theorem selected_cut_49558 : selected 10 ⟨1403184, by decide⟩
    (prefixPartial 11 102025) = some ⟨11, 2, 0, 1403184, 102025, 3753, 262144⟩ := by
  decide +kernel

theorem context_11_102025_1403184 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102025 ⟨1403184, by decide⟩ :=
  accepted_of_selected 11 102025 ⟨1403184, by decide⟩ ⟨11, 2, 0, 1403184, 102025, 3753, 262144⟩
    (by decide) selected_cut_49558

theorem selected_cut_49559 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 102026) = some ⟨11, 1, 0, 900587, 102026, 1, 262144⟩ := by
  decide +kernel

theorem context_11_102026_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102026 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 102026 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 102026, 1, 262144⟩
    (by decide) selected_cut_49559

theorem selected_cut_49560 : selected 10 ⟨1403276, by decide⟩
    (prefixPartial 11 102027) = some ⟨11, 2, 0, 1403276, 102027, 3689, 262144⟩ := by
  decide +kernel

theorem context_11_102027_1403276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102027 ⟨1403276, by decide⟩ :=
  accepted_of_selected 11 102027 ⟨1403276, by decide⟩ ⟨11, 2, 0, 1403276, 102027, 3689, 262144⟩
    (by decide) selected_cut_49560

theorem unmarked_context_10_25506_1403277 : frontier 11 ⟨1403277, by decide⟩
    (prefixCache 10 25506) (prefixPartial 10 25506) = false := by
  decide +kernel

theorem node_context_10_25506_1403277 : EJMOriginalGlobalDAGData.nodes 11 ⟨1403277, by decide⟩ =
    .split (coordinate 10) (![⟨1403086, by decide⟩,⟨1403184, by decide⟩,⟨900587, by decide⟩,⟨1403276, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25506_1403277 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25506 ⟨1403277, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25506
    ⟨1403277, by decide⟩ (by decide) (![⟨1403086, by decide⟩,⟨1403184, by decide⟩,⟨900587, by decide⟩,⟨1403276, by decide⟩]) unmarked_context_10_25506_1403277 node_context_10_25506_1403277
  intro a
  fin_cases a
  · exact context_11_102024_1403086
  · exact context_11_102025_1403184
  · exact context_11_102026_900587
  · exact context_11_102027_1403276

theorem selected_cut_49561 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 408112) = some ⟨12, 1, 0, 1108174, 408112, 1, 65536⟩ := by
  decide +kernel

theorem context_12_408112_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408112 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 408112 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 408112, 1, 65536⟩
    (by decide) selected_cut_49561

theorem selected_cut_49562 : selected 9 ⟨1403325, by decide⟩
    (prefixPartial 12 408113) = some ⟨12, 2, 0, 1403325, 408113, 1913, 65536⟩ := by
  decide +kernel

theorem context_12_408113_1403325 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408113 ⟨1403325, by decide⟩ :=
  accepted_of_selected 12 408113 ⟨1403325, by decide⟩ ⟨12, 2, 0, 1403325, 408113, 1913, 65536⟩
    (by decide) selected_cut_49562

theorem selected_cut_49563 : selected 9 ⟨1403368, by decide⟩
    (prefixPartial 12 408114) = some ⟨12, 2, 0, 1403368, 408114, 1641, 65536⟩ := by
  decide +kernel

theorem context_12_408114_1403368 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408114 ⟨1403368, by decide⟩ :=
  accepted_of_selected 12 408114 ⟨1403368, by decide⟩ ⟨12, 2, 0, 1403368, 408114, 1641, 65536⟩
    (by decide) selected_cut_49563

theorem selected_cut_49564 : selected 9 ⟨1403400, by decide⟩
    (prefixPartial 12 408115) = some ⟨12, 2, 0, 1403400, 408115, 1621, 65536⟩ := by
  decide +kernel

theorem context_12_408115_1403400 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408115 ⟨1403400, by decide⟩ :=
  accepted_of_selected 12 408115 ⟨1403400, by decide⟩ ⟨12, 2, 0, 1403400, 408115, 1621, 65536⟩
    (by decide) selected_cut_49564

theorem unmarked_context_11_102028_1403401 : frontier 10 ⟨1403401, by decide⟩
    (prefixCache 11 102028) (prefixPartial 11 102028) = false := by
  decide +kernel

theorem node_context_11_102028_1403401 : EJMOriginalGlobalDAGData.nodes 10 ⟨1403401, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1403325, by decide⟩,⟨1403368, by decide⟩,⟨1403400, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_102028_1403401 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102028 ⟨1403401, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 102028
    ⟨1403401, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1403325, by decide⟩,⟨1403368, by decide⟩,⟨1403400, by decide⟩]) unmarked_context_11_102028_1403401 node_context_11_102028_1403401
  intro a
  fin_cases a
  · exact context_12_408112_1108174
  · exact context_12_408113_1403325
  · exact context_12_408114_1403368
  · exact context_12_408115_1403400

theorem selected_cut_49565 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 408116) = some ⟨12, 1, 0, 1108174, 408116, 1, 65536⟩ := by
  decide +kernel

theorem context_12_408116_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408116 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 408116 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 408116, 1, 65536⟩
    (by decide) selected_cut_49565

theorem selected_cut_49566 : selected 9 ⟨1403443, by decide⟩
    (prefixPartial 12 408117) = some ⟨12, 2, 0, 1403443, 408117, 1745, 65536⟩ := by
  decide +kernel

theorem context_12_408117_1403443 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408117 ⟨1403443, by decide⟩ :=
  accepted_of_selected 12 408117 ⟨1403443, by decide⟩ ⟨12, 2, 0, 1403443, 408117, 1745, 65536⟩
    (by decide) selected_cut_49566

theorem selected_cut_49567 : selected 9 ⟨1403475, by decide⟩
    (prefixPartial 12 408118) = some ⟨12, 2, 0, 1403475, 408118, 1553, 65536⟩ := by
  decide +kernel

theorem context_12_408118_1403475 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408118 ⟨1403475, by decide⟩ :=
  accepted_of_selected 12 408118 ⟨1403475, by decide⟩ ⟨12, 2, 0, 1403475, 408118, 1553, 65536⟩
    (by decide) selected_cut_49567

theorem selected_cut_49568 : selected 9 ⟨1403502, by decide⟩
    (prefixPartial 12 408119) = some ⟨12, 2, 0, 1403502, 408119, 1477, 65536⟩ := by
  decide +kernel

theorem context_12_408119_1403502 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408119 ⟨1403502, by decide⟩ :=
  accepted_of_selected 12 408119 ⟨1403502, by decide⟩ ⟨12, 2, 0, 1403502, 408119, 1477, 65536⟩
    (by decide) selected_cut_49568

theorem unmarked_context_11_102029_1403503 : frontier 10 ⟨1403503, by decide⟩
    (prefixCache 11 102029) (prefixPartial 11 102029) = false := by
  decide +kernel

theorem node_context_11_102029_1403503 : EJMOriginalGlobalDAGData.nodes 10 ⟨1403503, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1403443, by decide⟩,⟨1403475, by decide⟩,⟨1403502, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_102029_1403503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102029 ⟨1403503, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 102029
    ⟨1403503, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1403443, by decide⟩,⟨1403475, by decide⟩,⟨1403502, by decide⟩]) unmarked_context_11_102029_1403503 node_context_11_102029_1403503
  intro a
  fin_cases a
  · exact context_12_408116_1108174
  · exact context_12_408117_1403443
  · exact context_12_408118_1403475
  · exact context_12_408119_1403502

theorem selected_cut_49569 : selected 10 ⟨1403551, by decide⟩
    (prefixPartial 11 102030) = some ⟨11, 2, 0, 1403551, 102030, 2573, 262144⟩ := by
  decide +kernel

theorem context_11_102030_1403551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102030 ⟨1403551, by decide⟩ :=
  accepted_of_selected 11 102030 ⟨1403551, by decide⟩ ⟨11, 2, 0, 1403551, 102030, 2573, 262144⟩
    (by decide) selected_cut_49569

theorem selected_cut_49570 : selected 10 ⟨1403584, by decide⟩
    (prefixPartial 11 102031) = some ⟨11, 2, 0, 1403584, 102031, 1425, 262144⟩ := by
  decide +kernel

theorem context_11_102031_1403584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102031 ⟨1403584, by decide⟩ :=
  accepted_of_selected 11 102031 ⟨1403584, by decide⟩ ⟨11, 2, 0, 1403584, 102031, 1425, 262144⟩
    (by decide) selected_cut_49570

theorem unmarked_context_10_25507_1403585 : frontier 11 ⟨1403585, by decide⟩
    (prefixCache 10 25507) (prefixPartial 10 25507) = false := by
  decide +kernel

theorem node_context_10_25507_1403585 : EJMOriginalGlobalDAGData.nodes 11 ⟨1403585, by decide⟩ =
    .split (coordinate 10) (![⟨1403401, by decide⟩,⟨1403503, by decide⟩,⟨1403551, by decide⟩,⟨1403584, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25507_1403585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25507 ⟨1403585, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25507
    ⟨1403585, by decide⟩ (by decide) (![⟨1403401, by decide⟩,⟨1403503, by decide⟩,⟨1403551, by decide⟩,⟨1403584, by decide⟩]) unmarked_context_10_25507_1403585 node_context_10_25507_1403585
  intro a
  fin_cases a
  · exact context_11_102028_1403401
  · exact context_11_102029_1403503
  · exact context_11_102030_1403551
  · exact context_11_102031_1403584

theorem unmarked_context_9_6376_1403586 : frontier 12 ⟨1403586, by decide⟩
    (prefixCache 9 6376) (prefixPartial 9 6376) = false := by
  decide +kernel

theorem node_context_9_6376_1403586 : EJMOriginalGlobalDAGData.nodes 12 ⟨1403586, by decide⟩ =
    .split (coordinate 9) (![⟨1402499, by decide⟩,⟨1402914, by decide⟩,⟨1403277, by decide⟩,⟨1403585, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6376_1403586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6376 ⟨1403586, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6376
    ⟨1403586, by decide⟩ (by decide) (![⟨1402499, by decide⟩,⟨1402914, by decide⟩,⟨1403277, by decide⟩,⟨1403585, by decide⟩]) unmarked_context_9_6376_1403586 node_context_9_6376_1403586
  intro a
  fin_cases a
  · exact context_10_25504_1402499
  · exact context_10_25505_1402914
  · exact context_10_25506_1403277
  · exact context_10_25507_1403585

theorem selected_cut_49571 : selected 10 ⟨1403625, by decide⟩
    (prefixPartial 11 102032) = some ⟨11, 2, 0, 1403625, 102032, 1701, 262144⟩ := by
  decide +kernel

theorem context_11_102032_1403625 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102032 ⟨1403625, by decide⟩ :=
  accepted_of_selected 11 102032 ⟨1403625, by decide⟩ ⟨11, 2, 0, 1403625, 102032, 1701, 262144⟩
    (by decide) selected_cut_49571

theorem selected_cut_49572 : selected 9 ⟨1403658, by decide⟩
    (prefixPartial 12 408132) = some ⟨12, 2, 0, 1403658, 408132, 1453, 65536⟩ := by
  decide +kernel

theorem context_12_408132_1403658 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408132 ⟨1403658, by decide⟩ :=
  accepted_of_selected 12 408132 ⟨1403658, by decide⟩ ⟨12, 2, 0, 1403658, 408132, 1453, 65536⟩
    (by decide) selected_cut_49572

theorem selected_cut_49573 : selected 9 ⟨642341, by decide⟩
    (prefixPartial 12 408133) = some ⟨12, 1, 0, 642341, 408133, 1, 65536⟩ := by
  decide +kernel

theorem context_12_408133_642341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408133 ⟨642341, by decide⟩ :=
  accepted_of_selected 12 408133 ⟨642341, by decide⟩ ⟨12, 1, 0, 642341, 408133, 1, 65536⟩
    (by decide) selected_cut_49573

theorem selected_cut_49574 : selected 9 ⟨1403692, by decide⟩
    (prefixPartial 12 408134) = some ⟨12, 2, 0, 1403692, 408134, 1553, 65536⟩ := by
  decide +kernel

theorem context_12_408134_1403692 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408134 ⟨1403692, by decide⟩ :=
  accepted_of_selected 12 408134 ⟨1403692, by decide⟩ ⟨12, 2, 0, 1403692, 408134, 1553, 65536⟩
    (by decide) selected_cut_49574

theorem selected_cut_49575 : selected 9 ⟨1403726, by decide⟩
    (prefixPartial 12 408135) = some ⟨12, 2, 0, 1403726, 408135, 1465, 65536⟩ := by
  decide +kernel

theorem context_12_408135_1403726 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408135 ⟨1403726, by decide⟩ :=
  accepted_of_selected 12 408135 ⟨1403726, by decide⟩ ⟨12, 2, 0, 1403726, 408135, 1465, 65536⟩
    (by decide) selected_cut_49575

theorem unmarked_context_11_102033_1403727 : frontier 10 ⟨1403727, by decide⟩
    (prefixCache 11 102033) (prefixPartial 11 102033) = false := by
  decide +kernel

theorem node_context_11_102033_1403727 : EJMOriginalGlobalDAGData.nodes 10 ⟨1403727, by decide⟩ =
    .split (coordinate 11) (![⟨1403658, by decide⟩,⟨642341, by decide⟩,⟨1403692, by decide⟩,⟨1403726, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_102033_1403727 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102033 ⟨1403727, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 102033
    ⟨1403727, by decide⟩ (by decide) (![⟨1403658, by decide⟩,⟨642341, by decide⟩,⟨1403692, by decide⟩,⟨1403726, by decide⟩]) unmarked_context_11_102033_1403727 node_context_11_102033_1403727
  intro a
  fin_cases a
  · exact context_12_408132_1403658
  · exact context_12_408133_642341
  · exact context_12_408134_1403692
  · exact context_12_408135_1403726

theorem selected_cut_49576 : selected 10 ⟨1403773, by decide⟩
    (prefixPartial 11 102034) = some ⟨11, 2, 0, 1403773, 102034, 2241, 262144⟩ := by
  decide +kernel

theorem context_11_102034_1403773 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102034 ⟨1403773, by decide⟩ :=
  accepted_of_selected 11 102034 ⟨1403773, by decide⟩ ⟨11, 2, 0, 1403773, 102034, 2241, 262144⟩
    (by decide) selected_cut_49576

theorem selected_cut_49577 : selected 9 ⟨1403795, by decide⟩
    (prefixPartial 12 408140) = some ⟨12, 2, 0, 1403795, 408140, 1377, 65536⟩ := by
  decide +kernel

theorem context_12_408140_1403795 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408140 ⟨1403795, by decide⟩ :=
  accepted_of_selected 12 408140 ⟨1403795, by decide⟩ ⟨12, 2, 0, 1403795, 408140, 1377, 65536⟩
    (by decide) selected_cut_49577

theorem selected_cut_49578 : selected 9 ⟨642341, by decide⟩
    (prefixPartial 12 408141) = some ⟨12, 1, 0, 642341, 408141, 1, 65536⟩ := by
  decide +kernel

theorem context_12_408141_642341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408141 ⟨642341, by decide⟩ :=
  accepted_of_selected 12 408141 ⟨642341, by decide⟩ ⟨12, 1, 0, 642341, 408141, 1, 65536⟩
    (by decide) selected_cut_49578

theorem selected_cut_49579 : selected 9 ⟨1403828, by decide⟩
    (prefixPartial 12 408142) = some ⟨12, 2, 0, 1403828, 408142, 1497, 65536⟩ := by
  decide +kernel

theorem context_12_408142_1403828 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408142 ⟨1403828, by decide⟩ :=
  accepted_of_selected 12 408142 ⟨1403828, by decide⟩ ⟨12, 2, 0, 1403828, 408142, 1497, 65536⟩
    (by decide) selected_cut_49579

theorem selected_cut_49580 : selected 9 ⟨1403855, by decide⟩
    (prefixPartial 12 408143) = some ⟨12, 2, 0, 1403855, 408143, 1309, 65536⟩ := by
  decide +kernel

theorem context_12_408143_1403855 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408143 ⟨1403855, by decide⟩ :=
  accepted_of_selected 12 408143 ⟨1403855, by decide⟩ ⟨12, 2, 0, 1403855, 408143, 1309, 65536⟩
    (by decide) selected_cut_49580

theorem unmarked_context_11_102035_1403856 : frontier 10 ⟨1403856, by decide⟩
    (prefixCache 11 102035) (prefixPartial 11 102035) = false := by
  decide +kernel

theorem node_context_11_102035_1403856 : EJMOriginalGlobalDAGData.nodes 10 ⟨1403856, by decide⟩ =
    .split (coordinate 11) (![⟨1403795, by decide⟩,⟨642341, by decide⟩,⟨1403828, by decide⟩,⟨1403855, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_102035_1403856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102035 ⟨1403856, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 102035
    ⟨1403856, by decide⟩ (by decide) (![⟨1403795, by decide⟩,⟨642341, by decide⟩,⟨1403828, by decide⟩,⟨1403855, by decide⟩]) unmarked_context_11_102035_1403856 node_context_11_102035_1403856
  intro a
  fin_cases a
  · exact context_12_408140_1403795
  · exact context_12_408141_642341
  · exact context_12_408142_1403828
  · exact context_12_408143_1403855

theorem unmarked_context_10_25508_1403857 : frontier 11 ⟨1403857, by decide⟩
    (prefixCache 10 25508) (prefixPartial 10 25508) = false := by
  decide +kernel

theorem node_context_10_25508_1403857 : EJMOriginalGlobalDAGData.nodes 11 ⟨1403857, by decide⟩ =
    .split (coordinate 10) (![⟨1403625, by decide⟩,⟨1403727, by decide⟩,⟨1403773, by decide⟩,⟨1403856, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25508_1403857 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25508 ⟨1403857, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25508
    ⟨1403857, by decide⟩ (by decide) (![⟨1403625, by decide⟩,⟨1403727, by decide⟩,⟨1403773, by decide⟩,⟨1403856, by decide⟩]) unmarked_context_10_25508_1403857 node_context_10_25508_1403857
  intro a
  fin_cases a
  · exact context_11_102032_1403625
  · exact context_11_102033_1403727
  · exact context_11_102034_1403773
  · exact context_11_102035_1403856

theorem selected_cut_49581 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 25509) = some ⟨10, 1, 0, 893098, 25509, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_25509_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25509 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 25509 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 25509, 1, 1048576⟩
    (by decide) selected_cut_49581

theorem selected_cut_49582 : selected 10 ⟨1403915, by decide⟩
    (prefixPartial 11 102040) = some ⟨11, 2, 0, 1403915, 102040, 2525, 262144⟩ := by
  decide +kernel

theorem context_11_102040_1403915 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102040 ⟨1403915, by decide⟩ :=
  accepted_of_selected 11 102040 ⟨1403915, by decide⟩ ⟨11, 2, 0, 1403915, 102040, 2525, 262144⟩
    (by decide) selected_cut_49582

theorem selected_cut_49583 : selected 10 ⟨1404006, by decide⟩
    (prefixPartial 11 102041) = some ⟨11, 2, 0, 1404006, 102041, 3585, 262144⟩ := by
  decide +kernel

theorem context_11_102041_1404006 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102041 ⟨1404006, by decide⟩ :=
  accepted_of_selected 11 102041 ⟨1404006, by decide⟩ ⟨11, 2, 0, 1404006, 102041, 3585, 262144⟩
    (by decide) selected_cut_49583

theorem selected_cut_49584 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 102042) = some ⟨11, 1, 0, 900587, 102042, 1, 262144⟩ := by
  decide +kernel

theorem context_11_102042_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102042 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 102042 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 102042, 1, 262144⟩
    (by decide) selected_cut_49584

theorem selected_cut_49585 : selected 10 ⟨1404073, by decide⟩
    (prefixPartial 11 102043) = some ⟨11, 2, 0, 1404073, 102043, 2581, 262144⟩ := by
  decide +kernel

theorem context_11_102043_1404073 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102043 ⟨1404073, by decide⟩ :=
  accepted_of_selected 11 102043 ⟨1404073, by decide⟩ ⟨11, 2, 0, 1404073, 102043, 2581, 262144⟩
    (by decide) selected_cut_49585

theorem unmarked_context_10_25510_1404074 : frontier 11 ⟨1404074, by decide⟩
    (prefixCache 10 25510) (prefixPartial 10 25510) = false := by
  decide +kernel

theorem node_context_10_25510_1404074 : EJMOriginalGlobalDAGData.nodes 11 ⟨1404074, by decide⟩ =
    .split (coordinate 10) (![⟨1403915, by decide⟩,⟨1404006, by decide⟩,⟨900587, by decide⟩,⟨1404073, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25510_1404074 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25510 ⟨1404074, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25510
    ⟨1404074, by decide⟩ (by decide) (![⟨1403915, by decide⟩,⟨1404006, by decide⟩,⟨900587, by decide⟩,⟨1404073, by decide⟩]) unmarked_context_10_25510_1404074 node_context_10_25510_1404074
  intro a
  fin_cases a
  · exact context_11_102040_1403915
  · exact context_11_102041_1404006
  · exact context_11_102042_900587
  · exact context_11_102043_1404073

theorem selected_cut_49586 : selected 10 ⟨1404117, by decide⟩
    (prefixPartial 11 102044) = some ⟨11, 2, 0, 1404117, 102044, 2005, 262144⟩ := by
  decide +kernel

theorem context_11_102044_1404117 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102044 ⟨1404117, by decide⟩ :=
  accepted_of_selected 11 102044 ⟨1404117, by decide⟩ ⟨11, 2, 0, 1404117, 102044, 2005, 262144⟩
    (by decide) selected_cut_49586

theorem selected_cut_49587 : selected 10 ⟨1404182, by decide⟩
    (prefixPartial 11 102045) = some ⟨11, 2, 0, 1404182, 102045, 2937, 262144⟩ := by
  decide +kernel

theorem context_11_102045_1404182 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102045 ⟨1404182, by decide⟩ :=
  accepted_of_selected 11 102045 ⟨1404182, by decide⟩ ⟨11, 2, 0, 1404182, 102045, 2937, 262144⟩
    (by decide) selected_cut_49587

theorem selected_cut_49588 : selected 10 ⟨1404226, by decide⟩
    (prefixPartial 11 102046) = some ⟨11, 2, 0, 1404226, 102046, 2089, 262144⟩ := by
  decide +kernel

theorem context_11_102046_1404226 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102046 ⟨1404226, by decide⟩ :=
  accepted_of_selected 11 102046 ⟨1404226, by decide⟩ ⟨11, 2, 0, 1404226, 102046, 2089, 262144⟩
    (by decide) selected_cut_49588

theorem selected_cut_49589 : selected 10 ⟨1404241, by decide⟩
    (prefixPartial 11 102047) = some ⟨11, 2, 0, 1404241, 102047, 765, 262144⟩ := by
  decide +kernel

theorem context_11_102047_1404241 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102047 ⟨1404241, by decide⟩ :=
  accepted_of_selected 11 102047 ⟨1404241, by decide⟩ ⟨11, 2, 0, 1404241, 102047, 765, 262144⟩
    (by decide) selected_cut_49589

theorem unmarked_context_10_25511_1404242 : frontier 11 ⟨1404242, by decide⟩
    (prefixCache 10 25511) (prefixPartial 10 25511) = false := by
  decide +kernel

theorem node_context_10_25511_1404242 : EJMOriginalGlobalDAGData.nodes 11 ⟨1404242, by decide⟩ =
    .split (coordinate 10) (![⟨1404117, by decide⟩,⟨1404182, by decide⟩,⟨1404226, by decide⟩,⟨1404241, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25511_1404242 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25511 ⟨1404242, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25511
    ⟨1404242, by decide⟩ (by decide) (![⟨1404117, by decide⟩,⟨1404182, by decide⟩,⟨1404226, by decide⟩,⟨1404241, by decide⟩]) unmarked_context_10_25511_1404242 node_context_10_25511_1404242
  intro a
  fin_cases a
  · exact context_11_102044_1404117
  · exact context_11_102045_1404182
  · exact context_11_102046_1404226
  · exact context_11_102047_1404241

theorem unmarked_context_9_6377_1404243 : frontier 12 ⟨1404243, by decide⟩
    (prefixCache 9 6377) (prefixPartial 9 6377) = false := by
  decide +kernel

theorem node_context_9_6377_1404243 : EJMOriginalGlobalDAGData.nodes 12 ⟨1404243, by decide⟩ =
    .split (coordinate 9) (![⟨1403857, by decide⟩,⟨893098, by decide⟩,⟨1404074, by decide⟩,⟨1404242, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6377_1404243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6377 ⟨1404243, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6377
    ⟨1404243, by decide⟩ (by decide) (![⟨1403857, by decide⟩,⟨893098, by decide⟩,⟨1404074, by decide⟩,⟨1404242, by decide⟩]) unmarked_context_9_6377_1404243 node_context_9_6377_1404243
  intro a
  fin_cases a
  · exact context_10_25508_1403857
  · exact context_10_25509_893098
  · exact context_10_25510_1404074
  · exact context_10_25511_1404242

theorem selected_cut_49590 : selected 10 ⟨1375697, by decide⟩
    (prefixPartial 11 102048) = some ⟨11, 1, 0, 1375697, 102048, 1, 262144⟩ := by
  decide +kernel

theorem context_11_102048_1375697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102048 ⟨1375697, by decide⟩ :=
  accepted_of_selected 11 102048 ⟨1375697, by decide⟩ ⟨11, 1, 0, 1375697, 102048, 1, 262144⟩
    (by decide) selected_cut_49590

theorem selected_cut_49591 : selected 10 ⟨1404280, by decide⟩
    (prefixPartial 11 102049) = some ⟨11, 2, 0, 1404280, 102049, 1701, 262144⟩ := by
  decide +kernel

theorem context_11_102049_1404280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102049 ⟨1404280, by decide⟩ :=
  accepted_of_selected 11 102049 ⟨1404280, by decide⟩ ⟨11, 2, 0, 1404280, 102049, 1701, 262144⟩
    (by decide) selected_cut_49591

theorem selected_cut_49592 : selected 10 ⟨1404317, by decide⟩
    (prefixPartial 11 102050) = some ⟨11, 2, 0, 1404317, 102050, 1865, 262144⟩ := by
  decide +kernel

theorem context_11_102050_1404317 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102050 ⟨1404317, by decide⟩ :=
  accepted_of_selected 11 102050 ⟨1404317, by decide⟩ ⟨11, 2, 0, 1404317, 102050, 1865, 262144⟩
    (by decide) selected_cut_49592

theorem selected_cut_49593 : selected 10 ⟨1404345, by decide⟩
    (prefixPartial 11 102051) = some ⟨11, 2, 0, 1404345, 102051, 1401, 262144⟩ := by
  decide +kernel

theorem context_11_102051_1404345 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102051 ⟨1404345, by decide⟩ :=
  accepted_of_selected 11 102051 ⟨1404345, by decide⟩ ⟨11, 2, 0, 1404345, 102051, 1401, 262144⟩
    (by decide) selected_cut_49593

theorem unmarked_context_10_25512_1404346 : frontier 11 ⟨1404346, by decide⟩
    (prefixCache 10 25512) (prefixPartial 10 25512) = false := by
  decide +kernel

theorem node_context_10_25512_1404346 : EJMOriginalGlobalDAGData.nodes 11 ⟨1404346, by decide⟩ =
    .split (coordinate 10) (![⟨1375697, by decide⟩,⟨1404280, by decide⟩,⟨1404317, by decide⟩,⟨1404345, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25512_1404346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25512 ⟨1404346, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25512
    ⟨1404346, by decide⟩ (by decide) (![⟨1375697, by decide⟩,⟨1404280, by decide⟩,⟨1404317, by decide⟩,⟨1404345, by decide⟩]) unmarked_context_10_25512_1404346 node_context_10_25512_1404346
  intro a
  fin_cases a
  · exact context_11_102048_1375697
  · exact context_11_102049_1404280
  · exact context_11_102050_1404317
  · exact context_11_102051_1404345

theorem selected_cut_49594 : selected 10 ⟨1404378, by decide⟩
    (prefixPartial 11 102052) = some ⟨11, 2, 0, 1404378, 102052, 1469, 262144⟩ := by
  decide +kernel

theorem context_11_102052_1404378 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102052 ⟨1404378, by decide⟩ :=
  accepted_of_selected 11 102052 ⟨1404378, by decide⟩ ⟨11, 2, 0, 1404378, 102052, 1469, 262144⟩
    (by decide) selected_cut_49594

theorem selected_cut_49595 : selected 10 ⟨1378525, by decide⟩
    (prefixPartial 11 102053) = some ⟨11, 1, 0, 1378525, 102053, 1, 262144⟩ := by
  decide +kernel

theorem context_11_102053_1378525 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102053 ⟨1378525, by decide⟩ :=
  accepted_of_selected 11 102053 ⟨1378525, by decide⟩ ⟨11, 1, 0, 1378525, 102053, 1, 262144⟩
    (by decide) selected_cut_49595

theorem selected_cut_49596 : selected 10 ⟨1404407, by decide⟩
    (prefixPartial 11 102054) = some ⟨11, 2, 0, 1404407, 102054, 1605, 262144⟩ := by
  decide +kernel

theorem context_11_102054_1404407 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102054 ⟨1404407, by decide⟩ :=
  accepted_of_selected 11 102054 ⟨1404407, by decide⟩ ⟨11, 2, 0, 1404407, 102054, 1605, 262144⟩
    (by decide) selected_cut_49596

theorem selected_cut_49597 : selected 10 ⟨1404433, by decide⟩
    (prefixPartial 11 102055) = some ⟨11, 2, 0, 1404433, 102055, 1573, 262144⟩ := by
  decide +kernel

theorem context_11_102055_1404433 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102055 ⟨1404433, by decide⟩ :=
  accepted_of_selected 11 102055 ⟨1404433, by decide⟩ ⟨11, 2, 0, 1404433, 102055, 1573, 262144⟩
    (by decide) selected_cut_49597

theorem unmarked_context_10_25513_1404434 : frontier 11 ⟨1404434, by decide⟩
    (prefixCache 10 25513) (prefixPartial 10 25513) = false := by
  decide +kernel

theorem node_context_10_25513_1404434 : EJMOriginalGlobalDAGData.nodes 11 ⟨1404434, by decide⟩ =
    .split (coordinate 10) (![⟨1404378, by decide⟩,⟨1378525, by decide⟩,⟨1404407, by decide⟩,⟨1404433, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25513_1404434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25513 ⟨1404434, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25513
    ⟨1404434, by decide⟩ (by decide) (![⟨1404378, by decide⟩,⟨1378525, by decide⟩,⟨1404407, by decide⟩,⟨1404433, by decide⟩]) unmarked_context_10_25513_1404434 node_context_10_25513_1404434
  intro a
  fin_cases a
  · exact context_11_102052_1404378
  · exact context_11_102053_1378525
  · exact context_11_102054_1404407
  · exact context_11_102055_1404433

theorem selected_cut_49598 : selected 11 ⟨1404447, by decide⟩
    (prefixPartial 10 25514) = some ⟨10, 2, 0, 1404447, 25514, 465, 1048576⟩ := by
  decide +kernel

theorem context_10_25514_1404447 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25514 ⟨1404447, by decide⟩ :=
  accepted_of_selected 10 25514 ⟨1404447, by decide⟩ ⟨10, 2, 0, 1404447, 25514, 465, 1048576⟩
    (by decide) selected_cut_49598

theorem selected_cut_49599 : selected 11 ⟨1404528, by decide⟩
    (prefixPartial 10 25515) = some ⟨10, 2, 0, 1404528, 25515, 3297, 1048576⟩ := by
  decide +kernel

theorem context_10_25515_1404528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25515 ⟨1404528, by decide⟩ :=
  accepted_of_selected 10 25515 ⟨1404528, by decide⟩ ⟨10, 2, 0, 1404528, 25515, 3297, 1048576⟩
    (by decide) selected_cut_49599

theorem unmarked_context_9_6378_1404529 : frontier 12 ⟨1404529, by decide⟩
    (prefixCache 9 6378) (prefixPartial 9 6378) = false := by
  decide +kernel

theorem node_context_9_6378_1404529 : EJMOriginalGlobalDAGData.nodes 12 ⟨1404529, by decide⟩ =
    .split (coordinate 9) (![⟨1404346, by decide⟩,⟨1404434, by decide⟩,⟨1404447, by decide⟩,⟨1404528, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6378_1404529 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6378 ⟨1404529, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6378
    ⟨1404529, by decide⟩ (by decide) (![⟨1404346, by decide⟩,⟨1404434, by decide⟩,⟨1404447, by decide⟩,⟨1404528, by decide⟩]) unmarked_context_9_6378_1404529 node_context_9_6378_1404529
  intro a
  fin_cases a
  · exact context_10_25512_1404346
  · exact context_10_25513_1404434
  · exact context_10_25514_1404447
  · exact context_10_25515_1404528

theorem selected_cut_49600 : selected 11 ⟨1404587, by decide⟩
    (prefixPartial 10 25516) = some ⟨10, 2, 0, 1404587, 25516, 3133, 1048576⟩ := by
  decide +kernel

theorem context_10_25516_1404587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25516 ⟨1404587, by decide⟩ :=
  accepted_of_selected 10 25516 ⟨1404587, by decide⟩ ⟨10, 2, 0, 1404587, 25516, 3133, 1048576⟩
    (by decide) selected_cut_49600

theorem selected_cut_49601 : selected 11 ⟨1404622, by decide⟩
    (prefixPartial 10 25517) = some ⟨10, 2, 0, 1404622, 25517, 1597, 1048576⟩ := by
  decide +kernel

theorem context_10_25517_1404622 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25517 ⟨1404622, by decide⟩ :=
  accepted_of_selected 10 25517 ⟨1404622, by decide⟩ ⟨10, 2, 0, 1404622, 25517, 1597, 1048576⟩
    (by decide) selected_cut_49601

theorem selected_cut_49602 : selected 11 ⟨1404655, by decide⟩
    (prefixPartial 10 25518) = some ⟨10, 2, 0, 1404655, 25518, 845, 1048576⟩ := by
  decide +kernel

theorem context_10_25518_1404655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25518 ⟨1404655, by decide⟩ :=
  accepted_of_selected 10 25518 ⟨1404655, by decide⟩ ⟨10, 2, 0, 1404655, 25518, 845, 1048576⟩
    (by decide) selected_cut_49602

theorem selected_cut_49603 : selected 11 ⟨1396051, by decide⟩
    (prefixPartial 10 25519) = some ⟨10, 2, 0, 1396051, 25519, 73, 1048576⟩ := by
  decide +kernel

theorem context_10_25519_1396051 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25519 ⟨1396051, by decide⟩ :=
  accepted_of_selected 10 25519 ⟨1396051, by decide⟩ ⟨10, 2, 0, 1396051, 25519, 73, 1048576⟩
    (by decide) selected_cut_49603

theorem unmarked_context_9_6379_1404656 : frontier 12 ⟨1404656, by decide⟩
    (prefixCache 9 6379) (prefixPartial 9 6379) = false := by
  decide +kernel

theorem node_context_9_6379_1404656 : EJMOriginalGlobalDAGData.nodes 12 ⟨1404656, by decide⟩ =
    .split (coordinate 9) (![⟨1404587, by decide⟩,⟨1404622, by decide⟩,⟨1404655, by decide⟩,⟨1396051, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6379_1404656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6379 ⟨1404656, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6379
    ⟨1404656, by decide⟩ (by decide) (![⟨1404587, by decide⟩,⟨1404622, by decide⟩,⟨1404655, by decide⟩,⟨1396051, by decide⟩]) unmarked_context_9_6379_1404656 node_context_9_6379_1404656
  intro a
  fin_cases a
  · exact context_10_25516_1404587
  · exact context_10_25517_1404622
  · exact context_10_25518_1404655
  · exact context_10_25519_1396051

theorem unmarked_context_8_1594_1404657 : frontier 13 ⟨1404657, by decide⟩
    (prefixCache 8 1594) (prefixPartial 8 1594) = false := by
  decide +kernel

theorem node_context_8_1594_1404657 : EJMOriginalGlobalDAGData.nodes 13 ⟨1404657, by decide⟩ =
    .split (coordinate 8) (![⟨1403586, by decide⟩,⟨1404243, by decide⟩,⟨1404529, by decide⟩,⟨1404656, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1594_1404657 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1594 ⟨1404657, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1594
    ⟨1404657, by decide⟩ (by decide) (![⟨1403586, by decide⟩,⟨1404243, by decide⟩,⟨1404529, by decide⟩,⟨1404656, by decide⟩]) unmarked_context_8_1594_1404657 node_context_8_1594_1404657
  intro a
  fin_cases a
  · exact context_9_6376_1403586
  · exact context_9_6377_1404243
  · exact context_9_6378_1404529
  · exact context_9_6379_1404656

theorem selected_cut_49604 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 102080) = some ⟨11, 1, 0, 434745, 102080, 1, 262144⟩ := by
  decide +kernel

theorem context_11_102080_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102080 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 102080 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 102080, 1, 262144⟩
    (by decide) selected_cut_49604

theorem selected_cut_49605 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 102081) = some ⟨11, 1, 0, 434745, 102081, 1, 262144⟩ := by
  decide +kernel

theorem context_11_102081_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102081 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 102081 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 102081, 1, 262144⟩
    (by decide) selected_cut_49605

theorem selected_cut_49606 : selected 10 ⟨1404694, by decide⟩
    (prefixPartial 11 102082) = some ⟨11, 2, 0, 1404694, 102082, 1905, 262144⟩ := by
  decide +kernel

theorem context_11_102082_1404694 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102082 ⟨1404694, by decide⟩ :=
  accepted_of_selected 11 102082 ⟨1404694, by decide⟩ ⟨11, 2, 0, 1404694, 102082, 1905, 262144⟩
    (by decide) selected_cut_49606

theorem selected_cut_49607 : selected 10 ⟨1404757, by decide⟩
    (prefixPartial 11 102083) = some ⟨11, 2, 0, 1404757, 102083, 2657, 262144⟩ := by
  decide +kernel

theorem context_11_102083_1404757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102083 ⟨1404757, by decide⟩ :=
  accepted_of_selected 11 102083 ⟨1404757, by decide⟩ ⟨11, 2, 0, 1404757, 102083, 2657, 262144⟩
    (by decide) selected_cut_49607

theorem unmarked_context_10_25520_1404758 : frontier 11 ⟨1404758, by decide⟩
    (prefixCache 10 25520) (prefixPartial 10 25520) = false := by
  decide +kernel

theorem node_context_10_25520_1404758 : EJMOriginalGlobalDAGData.nodes 11 ⟨1404758, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨434745, by decide⟩,⟨1404694, by decide⟩,⟨1404757, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25520_1404758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25520 ⟨1404758, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25520
    ⟨1404758, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨434745, by decide⟩,⟨1404694, by decide⟩,⟨1404757, by decide⟩]) unmarked_context_10_25520_1404758 node_context_10_25520_1404758
  intro a
  fin_cases a
  · exact context_11_102080_434745
  · exact context_11_102081_434745
  · exact context_11_102082_1404694
  · exact context_11_102083_1404757

theorem selected_cut_49608 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 408336) = some ⟨12, 1, 0, 1108174, 408336, 1, 65536⟩ := by
  decide +kernel

theorem context_12_408336_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408336 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 408336 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 408336, 1, 65536⟩
    (by decide) selected_cut_49608

theorem selected_cut_49609 : selected 9 ⟨1404818, by decide⟩
    (prefixPartial 12 408337) = some ⟨12, 2, 0, 1404818, 408337, 2545, 65536⟩ := by
  decide +kernel

theorem context_12_408337_1404818 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408337 ⟨1404818, by decide⟩ :=
  accepted_of_selected 12 408337 ⟨1404818, by decide⟩ ⟨12, 2, 0, 1404818, 408337, 2545, 65536⟩
    (by decide) selected_cut_49609

theorem selected_cut_49610 : selected 9 ⟨1404866, by decide⟩
    (prefixPartial 12 408338) = some ⟨12, 2, 0, 1404866, 408338, 2313, 65536⟩ := by
  decide +kernel

theorem context_12_408338_1404866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408338 ⟨1404866, by decide⟩ :=
  accepted_of_selected 12 408338 ⟨1404866, by decide⟩ ⟨12, 2, 0, 1404866, 408338, 2313, 65536⟩
    (by decide) selected_cut_49610

theorem selected_cut_49611 : selected 9 ⟨1404911, by decide⟩
    (prefixPartial 12 408339) = some ⟨12, 2, 0, 1404911, 408339, 2133, 65536⟩ := by
  decide +kernel

theorem context_12_408339_1404911 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408339 ⟨1404911, by decide⟩ :=
  accepted_of_selected 12 408339 ⟨1404911, by decide⟩ ⟨12, 2, 0, 1404911, 408339, 2133, 65536⟩
    (by decide) selected_cut_49611

theorem unmarked_context_11_102084_1404912 : frontier 10 ⟨1404912, by decide⟩
    (prefixCache 11 102084) (prefixPartial 11 102084) = false := by
  decide +kernel

theorem node_context_11_102084_1404912 : EJMOriginalGlobalDAGData.nodes 10 ⟨1404912, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1404818, by decide⟩,⟨1404866, by decide⟩,⟨1404911, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_102084_1404912 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102084 ⟨1404912, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 102084
    ⟨1404912, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1404818, by decide⟩,⟨1404866, by decide⟩,⟨1404911, by decide⟩]) unmarked_context_11_102084_1404912 node_context_11_102084_1404912
  intro a
  fin_cases a
  · exact context_12_408336_1108174
  · exact context_12_408337_1404818
  · exact context_12_408338_1404866
  · exact context_12_408339_1404911

theorem selected_cut_49612 : selected 10 ⟨1404954, by decide⟩
    (prefixPartial 11 102085) = some ⟨11, 2, 0, 1404954, 102085, 1933, 262144⟩ := by
  decide +kernel

theorem context_11_102085_1404954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102085 ⟨1404954, by decide⟩ :=
  accepted_of_selected 11 102085 ⟨1404954, by decide⟩ ⟨11, 2, 0, 1404954, 102085, 1933, 262144⟩
    (by decide) selected_cut_49612

theorem selected_cut_49613 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 408344) = some ⟨12, 1, 0, 1108174, 408344, 1, 65536⟩ := by
  decide +kernel

theorem context_12_408344_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408344 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 408344 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 408344, 1, 65536⟩
    (by decide) selected_cut_49613

theorem selected_cut_49614 : selected 9 ⟨1404993, by decide⟩
    (prefixPartial 12 408345) = some ⟨12, 2, 0, 1404993, 408345, 2025, 65536⟩ := by
  decide +kernel

theorem context_12_408345_1404993 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408345 ⟨1404993, by decide⟩ :=
  accepted_of_selected 12 408345 ⟨1404993, by decide⟩ ⟨12, 2, 0, 1404993, 408345, 2025, 65536⟩
    (by decide) selected_cut_49614

theorem selected_cut_49615 : selected 9 ⟨1405029, by decide⟩
    (prefixPartial 12 408346) = some ⟨12, 2, 0, 1405029, 408346, 1741, 65536⟩ := by
  decide +kernel

theorem context_12_408346_1405029 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408346 ⟨1405029, by decide⟩ :=
  accepted_of_selected 12 408346 ⟨1405029, by decide⟩ ⟨12, 2, 0, 1405029, 408346, 1741, 65536⟩
    (by decide) selected_cut_49615

theorem selected_cut_49616 : selected 9 ⟨1405060, by decide⟩
    (prefixPartial 12 408347) = some ⟨12, 2, 0, 1405060, 408347, 1677, 65536⟩ := by
  decide +kernel

theorem context_12_408347_1405060 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408347 ⟨1405060, by decide⟩ :=
  accepted_of_selected 12 408347 ⟨1405060, by decide⟩ ⟨12, 2, 0, 1405060, 408347, 1677, 65536⟩
    (by decide) selected_cut_49616

theorem unmarked_context_11_102086_1405061 : frontier 10 ⟨1405061, by decide⟩
    (prefixCache 11 102086) (prefixPartial 11 102086) = false := by
  decide +kernel

theorem node_context_11_102086_1405061 : EJMOriginalGlobalDAGData.nodes 10 ⟨1405061, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1404993, by decide⟩,⟨1405029, by decide⟩,⟨1405060, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_102086_1405061 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102086 ⟨1405061, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 102086
    ⟨1405061, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1404993, by decide⟩,⟨1405029, by decide⟩,⟨1405060, by decide⟩]) unmarked_context_11_102086_1405061 node_context_11_102086_1405061
  intro a
  fin_cases a
  · exact context_12_408344_1108174
  · exact context_12_408345_1404993
  · exact context_12_408346_1405029
  · exact context_12_408347_1405060

theorem selected_cut_49617 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 408348) = some ⟨12, 1, 0, 1108174, 408348, 1, 65536⟩ := by
  decide +kernel

theorem context_12_408348_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408348 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 408348 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 408348, 1, 65536⟩
    (by decide) selected_cut_49617

theorem selected_cut_49618 : selected 9 ⟨1405108, by decide⟩
    (prefixPartial 12 408349) = some ⟨12, 2, 0, 1405108, 408349, 2101, 65536⟩ := by
  decide +kernel

theorem context_12_408349_1405108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408349 ⟨1405108, by decide⟩ :=
  accepted_of_selected 12 408349 ⟨1405108, by decide⟩ ⟨12, 2, 0, 1405108, 408349, 2101, 65536⟩
    (by decide) selected_cut_49618

theorem selected_cut_49619 : selected 9 ⟨1405148, by decide⟩
    (prefixPartial 12 408350) = some ⟨12, 2, 0, 1405148, 408350, 2029, 65536⟩ := by
  decide +kernel

theorem context_12_408350_1405148 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408350 ⟨1405148, by decide⟩ :=
  accepted_of_selected 12 408350 ⟨1405148, by decide⟩ ⟨12, 2, 0, 1405148, 408350, 2029, 65536⟩
    (by decide) selected_cut_49619

theorem selected_cut_49620 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 408351) = some ⟨12, 1, 0, 903806, 408351, 1, 65536⟩ := by
  decide +kernel

theorem context_12_408351_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408351 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 408351 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 408351, 1, 65536⟩
    (by decide) selected_cut_49620

theorem unmarked_context_11_102087_1405149 : frontier 10 ⟨1405149, by decide⟩
    (prefixCache 11 102087) (prefixPartial 11 102087) = false := by
  decide +kernel

theorem node_context_11_102087_1405149 : EJMOriginalGlobalDAGData.nodes 10 ⟨1405149, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1405108, by decide⟩,⟨1405148, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_102087_1405149 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102087 ⟨1405149, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 102087
    ⟨1405149, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1405108, by decide⟩,⟨1405148, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_102087_1405149 node_context_11_102087_1405149
  intro a
  fin_cases a
  · exact context_12_408348_1108174
  · exact context_12_408349_1405108
  · exact context_12_408350_1405148
  · exact context_12_408351_903806

theorem unmarked_context_10_25521_1405150 : frontier 11 ⟨1405150, by decide⟩
    (prefixCache 10 25521) (prefixPartial 10 25521) = false := by
  decide +kernel

theorem node_context_10_25521_1405150 : EJMOriginalGlobalDAGData.nodes 11 ⟨1405150, by decide⟩ =
    .split (coordinate 10) (![⟨1404912, by decide⟩,⟨1404954, by decide⟩,⟨1405061, by decide⟩,⟨1405149, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25521_1405150 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25521 ⟨1405150, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25521
    ⟨1405150, by decide⟩ (by decide) (![⟨1404912, by decide⟩,⟨1404954, by decide⟩,⟨1405061, by decide⟩,⟨1405149, by decide⟩]) unmarked_context_10_25521_1405150 node_context_10_25521_1405150
  intro a
  fin_cases a
  · exact context_11_102084_1404912
  · exact context_11_102085_1404954
  · exact context_11_102086_1405061
  · exact context_11_102087_1405149

theorem selected_cut_49621 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 408352) = some ⟨12, 1, 0, 1108174, 408352, 1, 65536⟩ := by
  decide +kernel

theorem context_12_408352_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408352 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 408352 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 408352, 1, 65536⟩
    (by decide) selected_cut_49621

theorem selected_cut_49622 : selected 9 ⟨1405191, by decide⟩
    (prefixPartial 12 408353) = some ⟨12, 2, 0, 1405191, 408353, 1993, 65536⟩ := by
  decide +kernel

theorem context_12_408353_1405191 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408353 ⟨1405191, by decide⟩ :=
  accepted_of_selected 12 408353 ⟨1405191, by decide⟩ ⟨12, 2, 0, 1405191, 408353, 1993, 65536⟩
    (by decide) selected_cut_49622

theorem selected_cut_49623 : selected 9 ⟨1405235, by decide⟩
    (prefixPartial 12 408354) = some ⟨12, 2, 0, 1405235, 408354, 1893, 65536⟩ := by
  decide +kernel

theorem context_12_408354_1405235 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408354 ⟨1405235, by decide⟩ :=
  accepted_of_selected 12 408354 ⟨1405235, by decide⟩ ⟨12, 2, 0, 1405235, 408354, 1893, 65536⟩
    (by decide) selected_cut_49623

theorem selected_cut_49624 : selected 9 ⟨1405261, by decide⟩
    (prefixPartial 12 408355) = some ⟨12, 2, 0, 1405261, 408355, 1581, 65536⟩ := by
  decide +kernel

theorem context_12_408355_1405261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408355 ⟨1405261, by decide⟩ :=
  accepted_of_selected 12 408355 ⟨1405261, by decide⟩ ⟨12, 2, 0, 1405261, 408355, 1581, 65536⟩
    (by decide) selected_cut_49624

theorem unmarked_context_11_102088_1405262 : frontier 10 ⟨1405262, by decide⟩
    (prefixCache 11 102088) (prefixPartial 11 102088) = false := by
  decide +kernel

theorem node_context_11_102088_1405262 : EJMOriginalGlobalDAGData.nodes 10 ⟨1405262, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1405191, by decide⟩,⟨1405235, by decide⟩,⟨1405261, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_102088_1405262 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102088 ⟨1405262, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 102088
    ⟨1405262, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1405191, by decide⟩,⟨1405235, by decide⟩,⟨1405261, by decide⟩]) unmarked_context_11_102088_1405262 node_context_11_102088_1405262
  intro a
  fin_cases a
  · exact context_12_408352_1108174
  · exact context_12_408353_1405191
  · exact context_12_408354_1405235
  · exact context_12_408355_1405261

theorem selected_cut_49625 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 408356) = some ⟨12, 1, 0, 1108174, 408356, 1, 65536⟩ := by
  decide +kernel

theorem context_12_408356_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408356 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 408356 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 408356, 1, 65536⟩
    (by decide) selected_cut_49625

theorem selected_cut_49626 : selected 9 ⟨1405303, by decide⟩
    (prefixPartial 12 408357) = some ⟨12, 2, 0, 1405303, 408357, 1885, 65536⟩ := by
  decide +kernel

theorem context_12_408357_1405303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408357 ⟨1405303, by decide⟩ :=
  accepted_of_selected 12 408357 ⟨1405303, by decide⟩ ⟨12, 2, 0, 1405303, 408357, 1885, 65536⟩
    (by decide) selected_cut_49626

theorem selected_cut_49627 : selected 9 ⟨1405335, by decide⟩
    (prefixPartial 12 408358) = some ⟨12, 2, 0, 1405335, 408358, 1741, 65536⟩ := by
  decide +kernel

theorem context_12_408358_1405335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408358 ⟨1405335, by decide⟩ :=
  accepted_of_selected 12 408358 ⟨1405335, by decide⟩ ⟨12, 2, 0, 1405335, 408358, 1741, 65536⟩
    (by decide) selected_cut_49627

theorem selected_cut_49628 : selected 9 ⟨1405368, by decide⟩
    (prefixPartial 12 408359) = some ⟨12, 2, 0, 1405368, 408359, 1493, 65536⟩ := by
  decide +kernel

theorem context_12_408359_1405368 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408359 ⟨1405368, by decide⟩ :=
  accepted_of_selected 12 408359 ⟨1405368, by decide⟩ ⟨12, 2, 0, 1405368, 408359, 1493, 65536⟩
    (by decide) selected_cut_49628

theorem unmarked_context_11_102089_1405369 : frontier 10 ⟨1405369, by decide⟩
    (prefixCache 11 102089) (prefixPartial 11 102089) = false := by
  decide +kernel

theorem node_context_11_102089_1405369 : EJMOriginalGlobalDAGData.nodes 10 ⟨1405369, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1405303, by decide⟩,⟨1405335, by decide⟩,⟨1405368, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_102089_1405369 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102089 ⟨1405369, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 102089
    ⟨1405369, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1405303, by decide⟩,⟨1405335, by decide⟩,⟨1405368, by decide⟩]) unmarked_context_11_102089_1405369 node_context_11_102089_1405369
  intro a
  fin_cases a
  · exact context_12_408356_1108174
  · exact context_12_408357_1405303
  · exact context_12_408358_1405335
  · exact context_12_408359_1405368

theorem selected_cut_49629 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 102090) = some ⟨11, 1, 0, 900587, 102090, 1, 262144⟩ := by
  decide +kernel

theorem context_11_102090_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102090 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 102090 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 102090, 1, 262144⟩
    (by decide) selected_cut_49629

theorem selected_cut_49630 : selected 10 ⟨1405429, by decide⟩
    (prefixPartial 11 102091) = some ⟨11, 2, 0, 1405429, 102091, 3337, 262144⟩ := by
  decide +kernel

theorem context_11_102091_1405429 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102091 ⟨1405429, by decide⟩ :=
  accepted_of_selected 11 102091 ⟨1405429, by decide⟩ ⟨11, 2, 0, 1405429, 102091, 3337, 262144⟩
    (by decide) selected_cut_49630

theorem unmarked_context_10_25522_1405430 : frontier 11 ⟨1405430, by decide⟩
    (prefixCache 10 25522) (prefixPartial 10 25522) = false := by
  decide +kernel

theorem node_context_10_25522_1405430 : EJMOriginalGlobalDAGData.nodes 11 ⟨1405430, by decide⟩ =
    .split (coordinate 10) (![⟨1405262, by decide⟩,⟨1405369, by decide⟩,⟨900587, by decide⟩,⟨1405429, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25522_1405430 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25522 ⟨1405430, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25522
    ⟨1405430, by decide⟩ (by decide) (![⟨1405262, by decide⟩,⟨1405369, by decide⟩,⟨900587, by decide⟩,⟨1405429, by decide⟩]) unmarked_context_10_25522_1405430 node_context_10_25522_1405430
  intro a
  fin_cases a
  · exact context_11_102088_1405262
  · exact context_11_102089_1405369
  · exact context_11_102090_900587
  · exact context_11_102091_1405429

theorem selected_cut_49631 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 408368) = some ⟨12, 1, 0, 1108174, 408368, 1, 65536⟩ := by
  decide +kernel

theorem context_12_408368_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408368 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 408368 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 408368, 1, 65536⟩
    (by decide) selected_cut_49631

theorem selected_cut_49632 : selected 9 ⟨1405471, by decide⟩
    (prefixPartial 12 408369) = some ⟨12, 2, 0, 1405471, 408369, 1825, 65536⟩ := by
  decide +kernel

theorem context_12_408369_1405471 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408369 ⟨1405471, by decide⟩ :=
  accepted_of_selected 12 408369 ⟨1405471, by decide⟩ ⟨12, 2, 0, 1405471, 408369, 1825, 65536⟩
    (by decide) selected_cut_49632

theorem selected_cut_49633 : selected 9 ⟨1405511, by decide⟩
    (prefixPartial 12 408370) = some ⟨12, 2, 0, 1405511, 408370, 1801, 65536⟩ := by
  decide +kernel

theorem context_12_408370_1405511 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408370 ⟨1405511, by decide⟩ :=
  accepted_of_selected 12 408370 ⟨1405511, by decide⟩ ⟨12, 2, 0, 1405511, 408370, 1801, 65536⟩
    (by decide) selected_cut_49633

theorem selected_cut_49634 : selected 9 ⟨1405540, by decide⟩
    (prefixPartial 12 408371) = some ⟨12, 2, 0, 1405540, 408371, 1525, 65536⟩ := by
  decide +kernel

theorem context_12_408371_1405540 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 408371 ⟨1405540, by decide⟩ :=
  accepted_of_selected 12 408371 ⟨1405540, by decide⟩ ⟨12, 2, 0, 1405540, 408371, 1525, 65536⟩
    (by decide) selected_cut_49634

theorem unmarked_context_11_102092_1405541 : frontier 10 ⟨1405541, by decide⟩
    (prefixCache 11 102092) (prefixPartial 11 102092) = false := by
  decide +kernel

theorem node_context_11_102092_1405541 : EJMOriginalGlobalDAGData.nodes 10 ⟨1405541, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1405471, by decide⟩,⟨1405511, by decide⟩,⟨1405540, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_102092_1405541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102092 ⟨1405541, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 102092
    ⟨1405541, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1405471, by decide⟩,⟨1405511, by decide⟩,⟨1405540, by decide⟩]) unmarked_context_11_102092_1405541 node_context_11_102092_1405541
  intro a
  fin_cases a
  · exact context_12_408368_1108174
  · exact context_12_408369_1405471
  · exact context_12_408370_1405511
  · exact context_12_408371_1405540

theorem selected_cut_49635 : selected 10 ⟨1405604, by decide⟩
    (prefixPartial 11 102093) = some ⟨11, 2, 0, 1405604, 102093, 3281, 262144⟩ := by
  decide +kernel

theorem context_11_102093_1405604 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102093 ⟨1405604, by decide⟩ :=
  accepted_of_selected 11 102093 ⟨1405604, by decide⟩ ⟨11, 2, 0, 1405604, 102093, 3281, 262144⟩
    (by decide) selected_cut_49635

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
