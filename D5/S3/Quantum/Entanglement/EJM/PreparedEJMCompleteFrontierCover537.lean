/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover536
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_51554 : selected 11 ⟨1488516, by decide⟩
    (prefixPartial 10 70697) = some ⟨10, 2, 0, 1488516, 70697, 2985, 1048576⟩ := by
  decide +kernel

theorem context_10_70697_1488516 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70697 ⟨1488516, by decide⟩ :=
  accepted_of_selected 10 70697 ⟨1488516, by decide⟩ ⟨10, 2, 0, 1488516, 70697, 2985, 1048576⟩
    (by decide) selected_cut_51554

theorem selected_cut_51555 : selected 11 ⟨1469103, by decide⟩
    (prefixPartial 10 70698) = some ⟨10, 1, 0, 1469103, 70698, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_70698_1469103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70698 ⟨1469103, by decide⟩ :=
  accepted_of_selected 10 70698 ⟨1469103, by decide⟩ ⟨10, 1, 0, 1469103, 70698, 1, 1048576⟩
    (by decide) selected_cut_51555

theorem selected_cut_51556 : selected 11 ⟨1488575, by decide⟩
    (prefixPartial 10 70699) = some ⟨10, 2, 0, 1488575, 70699, 2373, 1048576⟩ := by
  decide +kernel

theorem context_10_70699_1488575 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70699 ⟨1488575, by decide⟩ :=
  accepted_of_selected 10 70699 ⟨1488575, by decide⟩ ⟨10, 2, 0, 1488575, 70699, 2373, 1048576⟩
    (by decide) selected_cut_51556

theorem unmarked_context_9_17674_1488576 : frontier 12 ⟨1488576, by decide⟩
    (prefixCache 9 17674) (prefixPartial 9 17674) = false := by
  decide +kernel

theorem node_context_9_17674_1488576 : EJMOriginalGlobalDAGData.nodes 12 ⟨1488576, by decide⟩ =
    .split (coordinate 9) (![⟨1488444, by decide⟩,⟨1488516, by decide⟩,⟨1469103, by decide⟩,⟨1488575, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17674_1488576 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17674 ⟨1488576, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17674
    ⟨1488576, by decide⟩ (by decide) (![⟨1488444, by decide⟩,⟨1488516, by decide⟩,⟨1469103, by decide⟩,⟨1488575, by decide⟩]) unmarked_context_9_17674_1488576 node_context_9_17674_1488576
  intro a
  fin_cases a
  · exact context_10_70696_1488444
  · exact context_10_70697_1488516
  · exact context_10_70698_1469103
  · exact context_10_70699_1488575

theorem selected_cut_51557 : selected 12 ⟨1488618, by decide⟩
    (prefixPartial 9 17675) = some ⟨9, 2, 0, 1488618, 17675, 2109, 4194304⟩ := by
  decide +kernel

theorem context_9_17675_1488618 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17675 ⟨1488618, by decide⟩ :=
  accepted_of_selected 9 17675 ⟨1488618, by decide⟩ ⟨9, 2, 0, 1488618, 17675, 2109, 4194304⟩
    (by decide) selected_cut_51557

theorem unmarked_context_8_4418_1488619 : frontier 13 ⟨1488619, by decide⟩
    (prefixCache 8 4418) (prefixPartial 8 4418) = false := by
  decide +kernel

theorem node_context_8_4418_1488619 : EJMOriginalGlobalDAGData.nodes 13 ⟨1488619, by decide⟩ =
    .split (coordinate 8) (![⟨1488122, by decide⟩,⟨1488409, by decide⟩,⟨1488576, by decide⟩,⟨1488618, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4418_1488619 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4418 ⟨1488619, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4418
    ⟨1488619, by decide⟩ (by decide) (![⟨1488122, by decide⟩,⟨1488409, by decide⟩,⟨1488576, by decide⟩,⟨1488618, by decide⟩]) unmarked_context_8_4418_1488619 node_context_8_4418_1488619
  intro a
  fin_cases a
  · exact context_9_17672_1488122
  · exact context_9_17673_1488409
  · exact context_9_17674_1488576
  · exact context_9_17675_1488618

theorem selected_cut_51558 : selected 13 ⟨14298, by decide⟩
    (prefixPartial 8 4419) = some ⟨8, 1, 0, 14298, 4419, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_4419_14298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4419 ⟨14298, by decide⟩ :=
  accepted_of_selected 8 4419 ⟨14298, by decide⟩ ⟨8, 1, 0, 14298, 4419, 1, 16777216⟩
    (by decide) selected_cut_51558

theorem unmarked_context_7_1104_1488620 : frontier 14 ⟨1488620, by decide⟩
    (prefixCache 7 1104) (prefixPartial 7 1104) = false := by
  decide +kernel

theorem node_context_7_1104_1488620 : EJMOriginalGlobalDAGData.nodes 14 ⟨1488620, by decide⟩ =
    .split (coordinate 7) (![⟨1487329, by decide⟩,⟨1487330, by decide⟩,⟨1488619, by decide⟩,⟨14298, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_1104_1488620 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 1104 ⟨1488620, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 1104
    ⟨1488620, by decide⟩ (by decide) (![⟨1487329, by decide⟩,⟨1487330, by decide⟩,⟨1488619, by decide⟩,⟨14298, by decide⟩]) unmarked_context_7_1104_1488620 node_context_7_1104_1488620
  intro a
  fin_cases a
  · exact context_8_4416_1487329
  · exact context_8_4417_1487330
  · exact context_8_4418_1488619
  · exact context_8_4419_14298

theorem selected_cut_51559 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 70720) = some ⟨10, 1, 0, 1468246, 70720, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_70720_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70720 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 70720 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 70720, 1, 1048576⟩
    (by decide) selected_cut_51559

theorem selected_cut_51560 : selected 11 ⟨1488803, by decide⟩
    (prefixPartial 10 70721) = some ⟨10, 2, 0, 1488803, 70721, 3009, 1048576⟩ := by
  decide +kernel

theorem context_10_70721_1488803 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70721 ⟨1488803, by decide⟩ :=
  accepted_of_selected 10 70721 ⟨1488803, by decide⟩ ⟨10, 2, 0, 1488803, 70721, 3009, 1048576⟩
    (by decide) selected_cut_51560

theorem selected_cut_51561 : selected 11 ⟨1489016, by decide⟩
    (prefixPartial 10 70722) = some ⟨10, 2, 0, 1489016, 70722, 3317, 1048576⟩ := by
  decide +kernel

theorem context_10_70722_1489016 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70722 ⟨1489016, by decide⟩ :=
  accepted_of_selected 10 70722 ⟨1489016, by decide⟩ ⟨10, 2, 0, 1489016, 70722, 3317, 1048576⟩
    (by decide) selected_cut_51561

theorem selected_cut_51562 : selected 11 ⟨3440, by decide⟩
    (prefixPartial 10 70723) = some ⟨10, 1, 0, 3440, 70723, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_70723_3440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70723 ⟨3440, by decide⟩ :=
  accepted_of_selected 10 70723 ⟨3440, by decide⟩ ⟨10, 1, 0, 3440, 70723, 1, 1048576⟩
    (by decide) selected_cut_51562

theorem unmarked_context_9_17680_1489017 : frontier 12 ⟨1489017, by decide⟩
    (prefixCache 9 17680) (prefixPartial 9 17680) = false := by
  decide +kernel

theorem node_context_9_17680_1489017 : EJMOriginalGlobalDAGData.nodes 12 ⟨1489017, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1488803, by decide⟩,⟨1489016, by decide⟩,⟨3440, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17680_1489017 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17680 ⟨1489017, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17680
    ⟨1489017, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1488803, by decide⟩,⟨1489016, by decide⟩,⟨3440, by decide⟩]) unmarked_context_9_17680_1489017 node_context_9_17680_1489017
  intro a
  fin_cases a
  · exact context_10_70720_1468246
  · exact context_10_70721_1488803
  · exact context_10_70722_1489016
  · exact context_10_70723_3440

theorem selected_cut_51563 : selected 12 ⟨1489148, by decide⟩
    (prefixPartial 9 17681) = some ⟨9, 2, 0, 1489148, 17681, 1089, 4194304⟩ := by
  decide +kernel

theorem context_9_17681_1489148 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17681 ⟨1489148, by decide⟩ :=
  accepted_of_selected 9 17681 ⟨1489148, by decide⟩ ⟨9, 2, 0, 1489148, 17681, 1089, 4194304⟩
    (by decide) selected_cut_51563

theorem selected_cut_51564 : selected 12 ⟨1489158, by decide⟩
    (prefixPartial 9 17682) = some ⟨9, 2, 0, 1489158, 17682, 57, 4194304⟩ := by
  decide +kernel

theorem context_9_17682_1489158 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17682 ⟨1489158, by decide⟩ :=
  accepted_of_selected 9 17682 ⟨1489158, by decide⟩ ⟨9, 2, 0, 1489158, 17682, 57, 4194304⟩
    (by decide) selected_cut_51564

theorem selected_cut_51565 : selected 12 ⟨4601, by decide⟩
    (prefixPartial 9 17683) = some ⟨9, 1, 0, 4601, 17683, 1, 4194304⟩ := by
  decide +kernel

theorem context_9_17683_4601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17683 ⟨4601, by decide⟩ :=
  accepted_of_selected 9 17683 ⟨4601, by decide⟩ ⟨9, 1, 0, 4601, 17683, 1, 4194304⟩
    (by decide) selected_cut_51565

theorem unmarked_context_8_4420_1489159 : frontier 13 ⟨1489159, by decide⟩
    (prefixCache 8 4420) (prefixPartial 8 4420) = false := by
  decide +kernel

theorem node_context_8_4420_1489159 : EJMOriginalGlobalDAGData.nodes 13 ⟨1489159, by decide⟩ =
    .split (coordinate 8) (![⟨1489017, by decide⟩,⟨1489148, by decide⟩,⟨1489158, by decide⟩,⟨4601, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4420_1489159 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4420 ⟨1489159, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4420
    ⟨1489159, by decide⟩ (by decide) (![⟨1489017, by decide⟩,⟨1489148, by decide⟩,⟨1489158, by decide⟩,⟨4601, by decide⟩]) unmarked_context_8_4420_1489159 node_context_8_4420_1489159
  intro a
  fin_cases a
  · exact context_9_17680_1489017
  · exact context_9_17681_1489148
  · exact context_9_17682_1489158
  · exact context_9_17683_4601

theorem selected_cut_51566 : selected 13 ⟨1489160, by decide⟩
    (prefixPartial 8 4421) = some ⟨8, 1, 0, 1489160, 4421, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_4421_1489160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4421 ⟨1489160, by decide⟩ :=
  accepted_of_selected 8 4421 ⟨1489160, by decide⟩ ⟨8, 1, 0, 1489160, 4421, 1, 16777216⟩
    (by decide) selected_cut_51566

theorem selected_cut_51567 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 70752) = some ⟨10, 1, 0, 1468246, 70752, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_70752_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70752 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 70752 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 70752, 1, 1048576⟩
    (by decide) selected_cut_51567

theorem selected_cut_51568 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 1132048) = some ⟨12, 1, 0, 448748, 1132048, 1, 65536⟩ := by
  decide +kernel

theorem context_12_1132048_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1132048 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 1132048 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 1132048, 1, 65536⟩
    (by decide) selected_cut_51568

theorem selected_cut_51569 : selected 9 ⟨1489222, by decide⟩
    (prefixPartial 12 1132049) = some ⟨12, 2, 0, 1489222, 1132049, 2157, 65536⟩ := by
  decide +kernel

theorem context_12_1132049_1489222 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1132049 ⟨1489222, by decide⟩ :=
  accepted_of_selected 12 1132049 ⟨1489222, by decide⟩ ⟨12, 2, 0, 1489222, 1132049, 2157, 65536⟩
    (by decide) selected_cut_51569

theorem selected_cut_51570 : selected 9 ⟨1489263, by decide⟩
    (prefixPartial 12 1132050) = some ⟨12, 2, 0, 1489263, 1132050, 1689, 65536⟩ := by
  decide +kernel

theorem context_12_1132050_1489263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1132050 ⟨1489263, by decide⟩ :=
  accepted_of_selected 12 1132050 ⟨1489263, by decide⟩ ⟨12, 2, 0, 1489263, 1132050, 1689, 65536⟩
    (by decide) selected_cut_51570

theorem selected_cut_51571 : selected 9 ⟨1489303, by decide⟩
    (prefixPartial 12 1132051) = some ⟨12, 2, 0, 1489303, 1132051, 1881, 65536⟩ := by
  decide +kernel

theorem context_12_1132051_1489303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1132051 ⟨1489303, by decide⟩ :=
  accepted_of_selected 12 1132051 ⟨1489303, by decide⟩ ⟨12, 2, 0, 1489303, 1132051, 1881, 65536⟩
    (by decide) selected_cut_51571

theorem unmarked_context_11_283012_1489304 : frontier 10 ⟨1489304, by decide⟩
    (prefixCache 11 283012) (prefixPartial 11 283012) = false := by
  decide +kernel

theorem node_context_11_283012_1489304 : EJMOriginalGlobalDAGData.nodes 10 ⟨1489304, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1489222, by decide⟩,⟨1489263, by decide⟩,⟨1489303, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_283012_1489304 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283012 ⟨1489304, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 283012
    ⟨1489304, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1489222, by decide⟩,⟨1489263, by decide⟩,⟨1489303, by decide⟩]) unmarked_context_11_283012_1489304 node_context_11_283012_1489304
  intro a
  fin_cases a
  · exact context_12_1132048_448748
  · exact context_12_1132049_1489222
  · exact context_12_1132050_1489263
  · exact context_12_1132051_1489303

theorem selected_cut_51572 : selected 10 ⟨1468419, by decide⟩
    (prefixPartial 11 283013) = some ⟨11, 1, 0, 1468419, 283013, 1, 262144⟩ := by
  decide +kernel

theorem context_11_283013_1468419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283013 ⟨1468419, by decide⟩ :=
  accepted_of_selected 11 283013 ⟨1468419, by decide⟩ ⟨11, 1, 0, 1468419, 283013, 1, 262144⟩
    (by decide) selected_cut_51572

theorem selected_cut_51573 : selected 10 ⟨1489376, by decide⟩
    (prefixPartial 11 283014) = some ⟨11, 2, 0, 1489376, 283014, 3469, 262144⟩ := by
  decide +kernel

theorem context_11_283014_1489376 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283014 ⟨1489376, by decide⟩ :=
  accepted_of_selected 11 283014 ⟨1489376, by decide⟩ ⟨11, 2, 0, 1489376, 283014, 3469, 262144⟩
    (by decide) selected_cut_51573

theorem selected_cut_51574 : selected 10 ⟨1489449, by decide⟩
    (prefixPartial 11 283015) = some ⟨11, 2, 0, 1489449, 283015, 3285, 262144⟩ := by
  decide +kernel

theorem context_11_283015_1489449 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283015 ⟨1489449, by decide⟩ :=
  accepted_of_selected 11 283015 ⟨1489449, by decide⟩ ⟨11, 2, 0, 1489449, 283015, 3285, 262144⟩
    (by decide) selected_cut_51574

theorem unmarked_context_10_70753_1489450 : frontier 11 ⟨1489450, by decide⟩
    (prefixCache 10 70753) (prefixPartial 10 70753) = false := by
  decide +kernel

theorem node_context_10_70753_1489450 : EJMOriginalGlobalDAGData.nodes 11 ⟨1489450, by decide⟩ =
    .split (coordinate 10) (![⟨1489304, by decide⟩,⟨1468419, by decide⟩,⟨1489376, by decide⟩,⟨1489449, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_70753_1489450 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70753 ⟨1489450, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 70753
    ⟨1489450, by decide⟩ (by decide) (![⟨1489304, by decide⟩,⟨1468419, by decide⟩,⟨1489376, by decide⟩,⟨1489449, by decide⟩]) unmarked_context_10_70753_1489450 node_context_10_70753_1489450
  intro a
  fin_cases a
  · exact context_11_283012_1489304
  · exact context_11_283013_1468419
  · exact context_11_283014_1489376
  · exact context_11_283015_1489449

theorem selected_cut_51575 : selected 9 ⟨1469342, by decide⟩
    (prefixPartial 12 1132064) = some ⟨12, 1, 0, 1469342, 1132064, 1, 65536⟩ := by
  decide +kernel

theorem context_12_1132064_1469342 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1132064 ⟨1469342, by decide⟩ :=
  accepted_of_selected 12 1132064 ⟨1469342, by decide⟩ ⟨12, 1, 0, 1469342, 1132064, 1, 65536⟩
    (by decide) selected_cut_51575

theorem selected_cut_51576 : selected 9 ⟨1489481, by decide⟩
    (prefixPartial 12 1132065) = some ⟨12, 2, 0, 1489481, 1132065, 1649, 65536⟩ := by
  decide +kernel

theorem context_12_1132065_1489481 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1132065 ⟨1489481, by decide⟩ :=
  accepted_of_selected 12 1132065 ⟨1489481, by decide⟩ ⟨12, 2, 0, 1489481, 1132065, 1649, 65536⟩
    (by decide) selected_cut_51576

theorem selected_cut_51577 : selected 9 ⟨1489509, by decide⟩
    (prefixPartial 12 1132066) = some ⟨12, 2, 0, 1489509, 1132066, 1313, 65536⟩ := by
  decide +kernel

theorem context_12_1132066_1489509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1132066 ⟨1489509, by decide⟩ :=
  accepted_of_selected 12 1132066 ⟨1489509, by decide⟩ ⟨12, 2, 0, 1489509, 1132066, 1313, 65536⟩
    (by decide) selected_cut_51577

theorem selected_cut_51578 : selected 9 ⟨1489537, by decide⟩
    (prefixPartial 12 1132067) = some ⟨12, 2, 0, 1489537, 1132067, 1465, 65536⟩ := by
  decide +kernel

theorem context_12_1132067_1489537 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1132067 ⟨1489537, by decide⟩ :=
  accepted_of_selected 12 1132067 ⟨1489537, by decide⟩ ⟨12, 2, 0, 1489537, 1132067, 1465, 65536⟩
    (by decide) selected_cut_51578

theorem unmarked_context_11_283016_1489538 : frontier 10 ⟨1489538, by decide⟩
    (prefixCache 11 283016) (prefixPartial 11 283016) = false := by
  decide +kernel

theorem node_context_11_283016_1489538 : EJMOriginalGlobalDAGData.nodes 10 ⟨1489538, by decide⟩ =
    .split (coordinate 11) (![⟨1469342, by decide⟩,⟨1489481, by decide⟩,⟨1489509, by decide⟩,⟨1489537, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_283016_1489538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283016 ⟨1489538, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 283016
    ⟨1489538, by decide⟩ (by decide) (![⟨1469342, by decide⟩,⟨1489481, by decide⟩,⟨1489509, by decide⟩,⟨1489537, by decide⟩]) unmarked_context_11_283016_1489538 node_context_11_283016_1489538
  intro a
  fin_cases a
  · exact context_12_1132064_1469342
  · exact context_12_1132065_1489481
  · exact context_12_1132066_1489509
  · exact context_12_1132067_1489537

theorem selected_cut_51579 : selected 10 ⟨1489575, by decide⟩
    (prefixPartial 11 283017) = some ⟨11, 2, 0, 1489575, 283017, 2469, 262144⟩ := by
  decide +kernel

theorem context_11_283017_1489575 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283017 ⟨1489575, by decide⟩ :=
  accepted_of_selected 11 283017 ⟨1489575, by decide⟩ ⟨11, 2, 0, 1489575, 283017, 2469, 262144⟩
    (by decide) selected_cut_51579

theorem selected_cut_51580 : selected 10 ⟨1468743, by decide⟩
    (prefixPartial 11 283018) = some ⟨11, 1, 0, 1468743, 283018, 1, 262144⟩ := by
  decide +kernel

theorem context_11_283018_1468743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283018 ⟨1468743, by decide⟩ :=
  accepted_of_selected 11 283018 ⟨1468743, by decide⟩ ⟨11, 1, 0, 1468743, 283018, 1, 262144⟩
    (by decide) selected_cut_51580

theorem selected_cut_51581 : selected 10 ⟨1489632, by decide⟩
    (prefixPartial 11 283019) = some ⟨11, 2, 0, 1489632, 283019, 2733, 262144⟩ := by
  decide +kernel

theorem context_11_283019_1489632 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283019 ⟨1489632, by decide⟩ :=
  accepted_of_selected 11 283019 ⟨1489632, by decide⟩ ⟨11, 2, 0, 1489632, 283019, 2733, 262144⟩
    (by decide) selected_cut_51581

theorem unmarked_context_10_70754_1489633 : frontier 11 ⟨1489633, by decide⟩
    (prefixCache 10 70754) (prefixPartial 10 70754) = false := by
  decide +kernel

theorem node_context_10_70754_1489633 : EJMOriginalGlobalDAGData.nodes 11 ⟨1489633, by decide⟩ =
    .split (coordinate 10) (![⟨1489538, by decide⟩,⟨1489575, by decide⟩,⟨1468743, by decide⟩,⟨1489632, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_70754_1489633 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70754 ⟨1489633, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 70754
    ⟨1489633, by decide⟩ (by decide) (![⟨1489538, by decide⟩,⟨1489575, by decide⟩,⟨1468743, by decide⟩,⟨1489632, by decide⟩]) unmarked_context_10_70754_1489633 node_context_10_70754_1489633
  intro a
  fin_cases a
  · exact context_11_283016_1489538
  · exact context_11_283017_1489575
  · exact context_11_283018_1468743
  · exact context_11_283019_1489632

theorem selected_cut_51582 : selected 10 ⟨1489703, by decide⟩
    (prefixPartial 11 283020) = some ⟨11, 2, 0, 1489703, 283020, 3785, 262144⟩ := by
  decide +kernel

theorem context_11_283020_1489703 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283020 ⟨1489703, by decide⟩ :=
  accepted_of_selected 11 283020 ⟨1489703, by decide⟩ ⟨11, 2, 0, 1489703, 283020, 3785, 262144⟩
    (by decide) selected_cut_51582

theorem selected_cut_51583 : selected 10 ⟨1489743, by decide⟩
    (prefixPartial 11 283021) = some ⟨11, 2, 0, 1489743, 283021, 2185, 262144⟩ := by
  decide +kernel

theorem context_11_283021_1489743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283021 ⟨1489743, by decide⟩ :=
  accepted_of_selected 11 283021 ⟨1489743, by decide⟩ ⟨11, 2, 0, 1489743, 283021, 2185, 262144⟩
    (by decide) selected_cut_51583

theorem selected_cut_51584 : selected 10 ⟨1489784, by decide⟩
    (prefixPartial 11 283022) = some ⟨11, 2, 0, 1489784, 283022, 2341, 262144⟩ := by
  decide +kernel

theorem context_11_283022_1489784 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283022 ⟨1489784, by decide⟩ :=
  accepted_of_selected 11 283022 ⟨1489784, by decide⟩ ⟨11, 2, 0, 1489784, 283022, 2341, 262144⟩
    (by decide) selected_cut_51584

theorem selected_cut_51585 : selected 10 ⟨1470044, by decide⟩
    (prefixPartial 11 283023) = some ⟨11, 1, 0, 1470044, 283023, 1, 262144⟩ := by
  decide +kernel

theorem context_11_283023_1470044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283023 ⟨1470044, by decide⟩ :=
  accepted_of_selected 11 283023 ⟨1470044, by decide⟩ ⟨11, 1, 0, 1470044, 283023, 1, 262144⟩
    (by decide) selected_cut_51585

theorem unmarked_context_10_70755_1489785 : frontier 11 ⟨1489785, by decide⟩
    (prefixCache 10 70755) (prefixPartial 10 70755) = false := by
  decide +kernel

theorem node_context_10_70755_1489785 : EJMOriginalGlobalDAGData.nodes 11 ⟨1489785, by decide⟩ =
    .split (coordinate 10) (![⟨1489703, by decide⟩,⟨1489743, by decide⟩,⟨1489784, by decide⟩,⟨1470044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_70755_1489785 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70755 ⟨1489785, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 70755
    ⟨1489785, by decide⟩ (by decide) (![⟨1489703, by decide⟩,⟨1489743, by decide⟩,⟨1489784, by decide⟩,⟨1470044, by decide⟩]) unmarked_context_10_70755_1489785 node_context_10_70755_1489785
  intro a
  fin_cases a
  · exact context_11_283020_1489703
  · exact context_11_283021_1489743
  · exact context_11_283022_1489784
  · exact context_11_283023_1470044

theorem unmarked_context_9_17688_1489786 : frontier 12 ⟨1489786, by decide⟩
    (prefixCache 9 17688) (prefixPartial 9 17688) = false := by
  decide +kernel

theorem node_context_9_17688_1489786 : EJMOriginalGlobalDAGData.nodes 12 ⟨1489786, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1489450, by decide⟩,⟨1489633, by decide⟩,⟨1489785, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17688_1489786 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17688 ⟨1489786, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17688
    ⟨1489786, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1489450, by decide⟩,⟨1489633, by decide⟩,⟨1489785, by decide⟩]) unmarked_context_9_17688_1489786 node_context_9_17688_1489786
  intro a
  fin_cases a
  · exact context_10_70752_1468246
  · exact context_10_70753_1489450
  · exact context_10_70754_1489633
  · exact context_10_70755_1489785

theorem selected_cut_51586 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 283024) = some ⟨11, 1, 0, 434745, 283024, 1, 262144⟩ := by
  decide +kernel

theorem context_11_283024_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283024 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 283024 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 283024, 1, 262144⟩
    (by decide) selected_cut_51586

theorem selected_cut_51587 : selected 10 ⟨1489834, by decide⟩
    (prefixPartial 11 283025) = some ⟨11, 2, 0, 1489834, 283025, 1569, 262144⟩ := by
  decide +kernel

theorem context_11_283025_1489834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283025 ⟨1489834, by decide⟩ :=
  accepted_of_selected 11 283025 ⟨1489834, by decide⟩ ⟨11, 2, 0, 1489834, 283025, 1569, 262144⟩
    (by decide) selected_cut_51587

theorem selected_cut_51588 : selected 10 ⟨1489867, by decide⟩
    (prefixPartial 11 283026) = some ⟨11, 2, 0, 1489867, 283026, 1573, 262144⟩ := by
  decide +kernel

theorem context_11_283026_1489867 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283026 ⟨1489867, by decide⟩ :=
  accepted_of_selected 11 283026 ⟨1489867, by decide⟩ ⟨11, 2, 0, 1489867, 283026, 1573, 262144⟩
    (by decide) selected_cut_51588

theorem selected_cut_51589 : selected 10 ⟨1489899, by decide⟩
    (prefixPartial 11 283027) = some ⟨11, 2, 0, 1489899, 283027, 1477, 262144⟩ := by
  decide +kernel

theorem context_11_283027_1489899 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283027 ⟨1489899, by decide⟩ :=
  accepted_of_selected 11 283027 ⟨1489899, by decide⟩ ⟨11, 2, 0, 1489899, 283027, 1477, 262144⟩
    (by decide) selected_cut_51589

theorem unmarked_context_10_70756_1489900 : frontier 11 ⟨1489900, by decide⟩
    (prefixCache 10 70756) (prefixPartial 10 70756) = false := by
  decide +kernel

theorem node_context_10_70756_1489900 : EJMOriginalGlobalDAGData.nodes 11 ⟨1489900, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨1489834, by decide⟩,⟨1489867, by decide⟩,⟨1489899, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_70756_1489900 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70756 ⟨1489900, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 70756
    ⟨1489900, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨1489834, by decide⟩,⟨1489867, by decide⟩,⟨1489899, by decide⟩]) unmarked_context_10_70756_1489900 node_context_10_70756_1489900
  intro a
  fin_cases a
  · exact context_11_283024_434745
  · exact context_11_283025_1489834
  · exact context_11_283026_1489867
  · exact context_11_283027_1489899

theorem selected_cut_51590 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 70757) = some ⟨10, 1, 0, 1468874, 70757, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_70757_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70757 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 70757 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 70757, 1, 1048576⟩
    (by decide) selected_cut_51590

theorem selected_cut_51591 : selected 10 ⟨1489928, by decide⟩
    (prefixPartial 11 283032) = some ⟨11, 2, 0, 1489928, 283032, 1525, 262144⟩ := by
  decide +kernel

theorem context_11_283032_1489928 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283032 ⟨1489928, by decide⟩ :=
  accepted_of_selected 11 283032 ⟨1489928, by decide⟩ ⟨11, 2, 0, 1489928, 283032, 1525, 262144⟩
    (by decide) selected_cut_51591

theorem selected_cut_51592 : selected 10 ⟨1489982, by decide⟩
    (prefixPartial 11 283033) = some ⟨11, 2, 0, 1489982, 283033, 1713, 262144⟩ := by
  decide +kernel

theorem context_11_283033_1489982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283033 ⟨1489982, by decide⟩ :=
  accepted_of_selected 11 283033 ⟨1489982, by decide⟩ ⟨11, 2, 0, 1489982, 283033, 1713, 262144⟩
    (by decide) selected_cut_51592

theorem selected_cut_51593 : selected 10 ⟨1468743, by decide⟩
    (prefixPartial 11 283034) = some ⟨11, 1, 0, 1468743, 283034, 1, 262144⟩ := by
  decide +kernel

theorem context_11_283034_1468743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283034 ⟨1468743, by decide⟩ :=
  accepted_of_selected 11 283034 ⟨1468743, by decide⟩ ⟨11, 1, 0, 1468743, 283034, 1, 262144⟩
    (by decide) selected_cut_51593

theorem selected_cut_51594 : selected 10 ⟨1490005, by decide⟩
    (prefixPartial 11 283035) = some ⟨11, 2, 0, 1490005, 283035, 1453, 262144⟩ := by
  decide +kernel

theorem context_11_283035_1490005 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283035 ⟨1490005, by decide⟩ :=
  accepted_of_selected 11 283035 ⟨1490005, by decide⟩ ⟨11, 2, 0, 1490005, 283035, 1453, 262144⟩
    (by decide) selected_cut_51594

theorem unmarked_context_10_70758_1490006 : frontier 11 ⟨1490006, by decide⟩
    (prefixCache 10 70758) (prefixPartial 10 70758) = false := by
  decide +kernel

theorem node_context_10_70758_1490006 : EJMOriginalGlobalDAGData.nodes 11 ⟨1490006, by decide⟩ =
    .split (coordinate 10) (![⟨1489928, by decide⟩,⟨1489982, by decide⟩,⟨1468743, by decide⟩,⟨1490005, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_70758_1490006 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70758 ⟨1490006, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 70758
    ⟨1490006, by decide⟩ (by decide) (![⟨1489928, by decide⟩,⟨1489982, by decide⟩,⟨1468743, by decide⟩,⟨1490005, by decide⟩]) unmarked_context_10_70758_1490006 node_context_10_70758_1490006
  intro a
  fin_cases a
  · exact context_11_283032_1489928
  · exact context_11_283033_1489982
  · exact context_11_283034_1468743
  · exact context_11_283035_1490005

theorem selected_cut_51595 : selected 10 ⟨1490036, by decide⟩
    (prefixPartial 11 283036) = some ⟨11, 2, 0, 1490036, 283036, 1357, 262144⟩ := by
  decide +kernel

theorem context_11_283036_1490036 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283036 ⟨1490036, by decide⟩ :=
  accepted_of_selected 11 283036 ⟨1490036, by decide⟩ ⟨11, 2, 0, 1490036, 283036, 1357, 262144⟩
    (by decide) selected_cut_51595

theorem selected_cut_51596 : selected 10 ⟨1490074, by decide⟩
    (prefixPartial 11 283037) = some ⟨11, 2, 0, 1490074, 283037, 1665, 262144⟩ := by
  decide +kernel

theorem context_11_283037_1490074 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283037 ⟨1490074, by decide⟩ :=
  accepted_of_selected 11 283037 ⟨1490074, by decide⟩ ⟨11, 2, 0, 1490074, 283037, 1665, 262144⟩
    (by decide) selected_cut_51596

theorem selected_cut_51597 : selected 10 ⟨1490101, by decide⟩
    (prefixPartial 11 283038) = some ⟨11, 2, 0, 1490101, 283038, 1217, 262144⟩ := by
  decide +kernel

theorem context_11_283038_1490101 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283038 ⟨1490101, by decide⟩ :=
  accepted_of_selected 11 283038 ⟨1490101, by decide⟩ ⟨11, 2, 0, 1490101, 283038, 1217, 262144⟩
    (by decide) selected_cut_51597

theorem selected_cut_51598 : selected 10 ⟨1470044, by decide⟩
    (prefixPartial 11 283039) = some ⟨11, 1, 0, 1470044, 283039, 1, 262144⟩ := by
  decide +kernel

theorem context_11_283039_1470044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283039 ⟨1470044, by decide⟩ :=
  accepted_of_selected 11 283039 ⟨1470044, by decide⟩ ⟨11, 1, 0, 1470044, 283039, 1, 262144⟩
    (by decide) selected_cut_51598

theorem unmarked_context_10_70759_1490102 : frontier 11 ⟨1490102, by decide⟩
    (prefixCache 10 70759) (prefixPartial 10 70759) = false := by
  decide +kernel

theorem node_context_10_70759_1490102 : EJMOriginalGlobalDAGData.nodes 11 ⟨1490102, by decide⟩ =
    .split (coordinate 10) (![⟨1490036, by decide⟩,⟨1490074, by decide⟩,⟨1490101, by decide⟩,⟨1470044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_70759_1490102 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70759 ⟨1490102, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 70759
    ⟨1490102, by decide⟩ (by decide) (![⟨1490036, by decide⟩,⟨1490074, by decide⟩,⟨1490101, by decide⟩,⟨1470044, by decide⟩]) unmarked_context_10_70759_1490102 node_context_10_70759_1490102
  intro a
  fin_cases a
  · exact context_11_283036_1490036
  · exact context_11_283037_1490074
  · exact context_11_283038_1490101
  · exact context_11_283039_1470044

theorem unmarked_context_9_17689_1490103 : frontier 12 ⟨1490103, by decide⟩
    (prefixCache 9 17689) (prefixPartial 9 17689) = false := by
  decide +kernel

theorem node_context_9_17689_1490103 : EJMOriginalGlobalDAGData.nodes 12 ⟨1490103, by decide⟩ =
    .split (coordinate 9) (![⟨1489900, by decide⟩,⟨1468874, by decide⟩,⟨1490006, by decide⟩,⟨1490102, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17689_1490103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17689 ⟨1490103, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17689
    ⟨1490103, by decide⟩ (by decide) (![⟨1489900, by decide⟩,⟨1468874, by decide⟩,⟨1490006, by decide⟩,⟨1490102, by decide⟩]) unmarked_context_9_17689_1490103 node_context_9_17689_1490103
  intro a
  fin_cases a
  · exact context_10_70756_1489900
  · exact context_10_70757_1468874
  · exact context_10_70758_1490006
  · exact context_10_70759_1490102

theorem selected_cut_51599 : selected 11 ⟨1490156, by decide⟩
    (prefixPartial 10 70760) = some ⟨10, 2, 0, 1490156, 70760, 3517, 1048576⟩ := by
  decide +kernel

theorem context_10_70760_1490156 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70760 ⟨1490156, by decide⟩ :=
  accepted_of_selected 10 70760 ⟨1490156, by decide⟩ ⟨10, 2, 0, 1490156, 70760, 3517, 1048576⟩
    (by decide) selected_cut_51599

theorem selected_cut_51600 : selected 11 ⟨1490224, by decide⟩
    (prefixPartial 10 70761) = some ⟨10, 2, 0, 1490224, 70761, 3049, 1048576⟩ := by
  decide +kernel

theorem context_10_70761_1490224 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70761 ⟨1490224, by decide⟩ :=
  accepted_of_selected 10 70761 ⟨1490224, by decide⟩ ⟨10, 2, 0, 1490224, 70761, 3049, 1048576⟩
    (by decide) selected_cut_51600

theorem selected_cut_51601 : selected 11 ⟨1469103, by decide⟩
    (prefixPartial 10 70762) = some ⟨10, 1, 0, 1469103, 70762, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_70762_1469103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70762 ⟨1469103, by decide⟩ :=
  accepted_of_selected 10 70762 ⟨1469103, by decide⟩ ⟨10, 1, 0, 1469103, 70762, 1, 1048576⟩
    (by decide) selected_cut_51601

theorem selected_cut_51602 : selected 11 ⟨1490257, by decide⟩
    (prefixPartial 10 70763) = some ⟨10, 2, 0, 1490257, 70763, 2293, 1048576⟩ := by
  decide +kernel

theorem context_10_70763_1490257 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70763 ⟨1490257, by decide⟩ :=
  accepted_of_selected 10 70763 ⟨1490257, by decide⟩ ⟨10, 2, 0, 1490257, 70763, 2293, 1048576⟩
    (by decide) selected_cut_51602

theorem unmarked_context_9_17690_1490258 : frontier 12 ⟨1490258, by decide⟩
    (prefixCache 9 17690) (prefixPartial 9 17690) = false := by
  decide +kernel

theorem node_context_9_17690_1490258 : EJMOriginalGlobalDAGData.nodes 12 ⟨1490258, by decide⟩ =
    .split (coordinate 9) (![⟨1490156, by decide⟩,⟨1490224, by decide⟩,⟨1469103, by decide⟩,⟨1490257, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17690_1490258 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17690 ⟨1490258, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17690
    ⟨1490258, by decide⟩ (by decide) (![⟨1490156, by decide⟩,⟨1490224, by decide⟩,⟨1469103, by decide⟩,⟨1490257, by decide⟩]) unmarked_context_9_17690_1490258 node_context_9_17690_1490258
  intro a
  fin_cases a
  · exact context_10_70760_1490156
  · exact context_10_70761_1490224
  · exact context_10_70762_1469103
  · exact context_10_70763_1490257

theorem selected_cut_51603 : selected 12 ⟨1490302, by decide⟩
    (prefixPartial 9 17691) = some ⟨9, 2, 0, 1490302, 17691, 2933, 4194304⟩ := by
  decide +kernel

theorem context_9_17691_1490302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17691 ⟨1490302, by decide⟩ :=
  accepted_of_selected 9 17691 ⟨1490302, by decide⟩ ⟨9, 2, 0, 1490302, 17691, 2933, 4194304⟩
    (by decide) selected_cut_51603

theorem unmarked_context_8_4422_1490303 : frontier 13 ⟨1490303, by decide⟩
    (prefixCache 8 4422) (prefixPartial 8 4422) = false := by
  decide +kernel

theorem node_context_8_4422_1490303 : EJMOriginalGlobalDAGData.nodes 13 ⟨1490303, by decide⟩ =
    .split (coordinate 8) (![⟨1489786, by decide⟩,⟨1490103, by decide⟩,⟨1490258, by decide⟩,⟨1490302, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4422_1490303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4422 ⟨1490303, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4422
    ⟨1490303, by decide⟩ (by decide) (![⟨1489786, by decide⟩,⟨1490103, by decide⟩,⟨1490258, by decide⟩,⟨1490302, by decide⟩]) unmarked_context_8_4422_1490303 node_context_8_4422_1490303
  intro a
  fin_cases a
  · exact context_9_17688_1489786
  · exact context_9_17689_1490103
  · exact context_9_17690_1490258
  · exact context_9_17691_1490302

theorem selected_cut_51604 : selected 13 ⟨14298, by decide⟩
    (prefixPartial 8 4423) = some ⟨8, 1, 0, 14298, 4423, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_4423_14298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4423 ⟨14298, by decide⟩ :=
  accepted_of_selected 8 4423 ⟨14298, by decide⟩ ⟨8, 1, 0, 14298, 4423, 1, 16777216⟩
    (by decide) selected_cut_51604

theorem unmarked_context_7_1105_1490304 : frontier 14 ⟨1490304, by decide⟩
    (prefixCache 7 1105) (prefixPartial 7 1105) = false := by
  decide +kernel

theorem node_context_7_1105_1490304 : EJMOriginalGlobalDAGData.nodes 14 ⟨1490304, by decide⟩ =
    .split (coordinate 7) (![⟨1489159, by decide⟩,⟨1489160, by decide⟩,⟨1490303, by decide⟩,⟨14298, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_1105_1490304 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 1105 ⟨1490304, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 1105
    ⟨1490304, by decide⟩ (by decide) (![⟨1489159, by decide⟩,⟨1489160, by decide⟩,⟨1490303, by decide⟩,⟨14298, by decide⟩]) unmarked_context_7_1105_1490304 node_context_7_1105_1490304
  intro a
  fin_cases a
  · exact context_8_4420_1489159
  · exact context_8_4421_1489160
  · exact context_8_4422_1490303
  · exact context_8_4423_14298

theorem selected_cut_51605 : selected 13 ⟨1490305, by decide⟩
    (prefixPartial 8 4424) = some ⟨8, 1, 0, 1490305, 4424, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_4424_1490305 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4424 ⟨1490305, by decide⟩ :=
  accepted_of_selected 8 4424 ⟨1490305, by decide⟩ ⟨8, 1, 0, 1490305, 4424, 1, 16777216⟩
    (by decide) selected_cut_51605

theorem selected_cut_51606 : selected 13 ⟨1487330, by decide⟩
    (prefixPartial 8 4425) = some ⟨8, 1, 0, 1487330, 4425, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_4425_1487330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4425 ⟨1487330, by decide⟩ :=
  accepted_of_selected 8 4425 ⟨1487330, by decide⟩ ⟨8, 1, 0, 1487330, 4425, 1, 16777216⟩
    (by decide) selected_cut_51606

theorem selected_cut_51607 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 70816) = some ⟨10, 1, 0, 1468246, 70816, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_70816_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70816 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 70816 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 70816, 1, 1048576⟩
    (by decide) selected_cut_51607

theorem selected_cut_51608 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 1133072) = some ⟨12, 1, 0, 448748, 1133072, 1, 65536⟩ := by
  decide +kernel

theorem context_12_1133072_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1133072 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 1133072 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 1133072, 1, 65536⟩
    (by decide) selected_cut_51608

theorem selected_cut_51609 : selected 9 ⟨1490372, by decide⟩
    (prefixPartial 12 1133073) = some ⟨12, 2, 0, 1490372, 1133073, 2125, 65536⟩ := by
  decide +kernel

theorem context_12_1133073_1490372 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1133073 ⟨1490372, by decide⟩ :=
  accepted_of_selected 12 1133073 ⟨1490372, by decide⟩ ⟨12, 2, 0, 1490372, 1133073, 2125, 65536⟩
    (by decide) selected_cut_51609

theorem selected_cut_51610 : selected 9 ⟨1490422, by decide⟩
    (prefixPartial 12 1133074) = some ⟨12, 2, 0, 1490422, 1133074, 1729, 65536⟩ := by
  decide +kernel

theorem context_12_1133074_1490422 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1133074 ⟨1490422, by decide⟩ :=
  accepted_of_selected 12 1133074 ⟨1490422, by decide⟩ ⟨12, 2, 0, 1490422, 1133074, 1729, 65536⟩
    (by decide) selected_cut_51610

theorem selected_cut_51611 : selected 9 ⟨1490476, by decide⟩
    (prefixPartial 12 1133075) = some ⟨12, 2, 0, 1490476, 1133075, 1933, 65536⟩ := by
  decide +kernel

theorem context_12_1133075_1490476 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1133075 ⟨1490476, by decide⟩ :=
  accepted_of_selected 12 1133075 ⟨1490476, by decide⟩ ⟨12, 2, 0, 1490476, 1133075, 1933, 65536⟩
    (by decide) selected_cut_51611

theorem unmarked_context_11_283268_1490477 : frontier 10 ⟨1490477, by decide⟩
    (prefixCache 11 283268) (prefixPartial 11 283268) = false := by
  decide +kernel

theorem node_context_11_283268_1490477 : EJMOriginalGlobalDAGData.nodes 10 ⟨1490477, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1490372, by decide⟩,⟨1490422, by decide⟩,⟨1490476, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_283268_1490477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283268 ⟨1490477, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 283268
    ⟨1490477, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1490372, by decide⟩,⟨1490422, by decide⟩,⟨1490476, by decide⟩]) unmarked_context_11_283268_1490477 node_context_11_283268_1490477
  intro a
  fin_cases a
  · exact context_12_1133072_448748
  · exact context_12_1133073_1490372
  · exact context_12_1133074_1490422
  · exact context_12_1133075_1490476

theorem selected_cut_51612 : selected 10 ⟨1468419, by decide⟩
    (prefixPartial 11 283269) = some ⟨11, 1, 0, 1468419, 283269, 1, 262144⟩ := by
  decide +kernel

theorem context_11_283269_1468419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283269 ⟨1468419, by decide⟩ :=
  accepted_of_selected 11 283269 ⟨1468419, by decide⟩ ⟨11, 1, 0, 1468419, 283269, 1, 262144⟩
    (by decide) selected_cut_51612

theorem selected_cut_51613 : selected 10 ⟨1490518, by decide⟩
    (prefixPartial 11 283270) = some ⟨11, 2, 0, 1490518, 283270, 1633, 262144⟩ := by
  decide +kernel

theorem context_11_283270_1490518 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283270 ⟨1490518, by decide⟩ :=
  accepted_of_selected 11 283270 ⟨1490518, by decide⟩ ⟨11, 2, 0, 1490518, 283270, 1633, 262144⟩
    (by decide) selected_cut_51613

theorem selected_cut_51614 : selected 10 ⟨1490590, by decide⟩
    (prefixPartial 11 283271) = some ⟨11, 2, 0, 1490590, 283271, 3329, 262144⟩ := by
  decide +kernel

theorem context_11_283271_1490590 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283271 ⟨1490590, by decide⟩ :=
  accepted_of_selected 11 283271 ⟨1490590, by decide⟩ ⟨11, 2, 0, 1490590, 283271, 3329, 262144⟩
    (by decide) selected_cut_51614

theorem unmarked_context_10_70817_1490591 : frontier 11 ⟨1490591, by decide⟩
    (prefixCache 10 70817) (prefixPartial 10 70817) = false := by
  decide +kernel

theorem node_context_10_70817_1490591 : EJMOriginalGlobalDAGData.nodes 11 ⟨1490591, by decide⟩ =
    .split (coordinate 10) (![⟨1490477, by decide⟩,⟨1468419, by decide⟩,⟨1490518, by decide⟩,⟨1490590, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_70817_1490591 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70817 ⟨1490591, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 70817
    ⟨1490591, by decide⟩ (by decide) (![⟨1490477, by decide⟩,⟨1468419, by decide⟩,⟨1490518, by decide⟩,⟨1490590, by decide⟩]) unmarked_context_10_70817_1490591 node_context_10_70817_1490591
  intro a
  fin_cases a
  · exact context_11_283268_1490477
  · exact context_11_283269_1468419
  · exact context_11_283270_1490518
  · exact context_11_283271_1490590

theorem selected_cut_51615 : selected 10 ⟨1490658, by decide⟩
    (prefixPartial 11 283272) = some ⟨11, 2, 0, 1490658, 283272, 3117, 262144⟩ := by
  decide +kernel

theorem context_11_283272_1490658 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283272 ⟨1490658, by decide⟩ :=
  accepted_of_selected 11 283272 ⟨1490658, by decide⟩ ⟨11, 2, 0, 1490658, 283272, 3117, 262144⟩
    (by decide) selected_cut_51615

theorem selected_cut_51616 : selected 10 ⟨1490729, by decide⟩
    (prefixPartial 11 283273) = some ⟨11, 2, 0, 1490729, 283273, 2909, 262144⟩ := by
  decide +kernel

theorem context_11_283273_1490729 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283273 ⟨1490729, by decide⟩ :=
  accepted_of_selected 11 283273 ⟨1490729, by decide⟩ ⟨11, 2, 0, 1490729, 283273, 2909, 262144⟩
    (by decide) selected_cut_51616

theorem selected_cut_51617 : selected 10 ⟨1468743, by decide⟩
    (prefixPartial 11 283274) = some ⟨11, 1, 0, 1468743, 283274, 1, 262144⟩ := by
  decide +kernel

theorem context_11_283274_1468743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283274 ⟨1468743, by decide⟩ :=
  accepted_of_selected 11 283274 ⟨1468743, by decide⟩ ⟨11, 1, 0, 1468743, 283274, 1, 262144⟩
    (by decide) selected_cut_51617

theorem selected_cut_51618 : selected 10 ⟨1490790, by decide⟩
    (prefixPartial 11 283275) = some ⟨11, 2, 0, 1490790, 283275, 2757, 262144⟩ := by
  decide +kernel

theorem context_11_283275_1490790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283275 ⟨1490790, by decide⟩ :=
  accepted_of_selected 11 283275 ⟨1490790, by decide⟩ ⟨11, 2, 0, 1490790, 283275, 2757, 262144⟩
    (by decide) selected_cut_51618

theorem unmarked_context_10_70818_1490791 : frontier 11 ⟨1490791, by decide⟩
    (prefixCache 10 70818) (prefixPartial 10 70818) = false := by
  decide +kernel

theorem node_context_10_70818_1490791 : EJMOriginalGlobalDAGData.nodes 11 ⟨1490791, by decide⟩ =
    .split (coordinate 10) (![⟨1490658, by decide⟩,⟨1490729, by decide⟩,⟨1468743, by decide⟩,⟨1490790, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_70818_1490791 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70818 ⟨1490791, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 70818
    ⟨1490791, by decide⟩ (by decide) (![⟨1490658, by decide⟩,⟨1490729, by decide⟩,⟨1468743, by decide⟩,⟨1490790, by decide⟩]) unmarked_context_10_70818_1490791 node_context_10_70818_1490791
  intro a
  fin_cases a
  · exact context_11_283272_1490658
  · exact context_11_283273_1490729
  · exact context_11_283274_1468743
  · exact context_11_283275_1490790

theorem selected_cut_51619 : selected 10 ⟨1490873, by decide⟩
    (prefixPartial 11 283276) = some ⟨11, 2, 0, 1490873, 283276, 4061, 262144⟩ := by
  decide +kernel

theorem context_11_283276_1490873 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283276 ⟨1490873, by decide⟩ :=
  accepted_of_selected 11 283276 ⟨1490873, by decide⟩ ⟨11, 2, 0, 1490873, 283276, 4061, 262144⟩
    (by decide) selected_cut_51619

theorem selected_cut_51620 : selected 10 ⟨1490923, by decide⟩
    (prefixPartial 11 283277) = some ⟨11, 2, 0, 1490923, 283277, 2577, 262144⟩ := by
  decide +kernel

theorem context_11_283277_1490923 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283277 ⟨1490923, by decide⟩ :=
  accepted_of_selected 11 283277 ⟨1490923, by decide⟩ ⟨11, 2, 0, 1490923, 283277, 2577, 262144⟩
    (by decide) selected_cut_51620

theorem selected_cut_51621 : selected 10 ⟨1490946, by decide⟩
    (prefixPartial 11 283278) = some ⟨11, 2, 0, 1490946, 283278, 1113, 262144⟩ := by
  decide +kernel

theorem context_11_283278_1490946 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283278 ⟨1490946, by decide⟩ :=
  accepted_of_selected 11 283278 ⟨1490946, by decide⟩ ⟨11, 2, 0, 1490946, 283278, 1113, 262144⟩
    (by decide) selected_cut_51621

theorem selected_cut_51622 : selected 10 ⟨1470044, by decide⟩
    (prefixPartial 11 283279) = some ⟨11, 1, 0, 1470044, 283279, 1, 262144⟩ := by
  decide +kernel

theorem context_11_283279_1470044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283279 ⟨1470044, by decide⟩ :=
  accepted_of_selected 11 283279 ⟨1470044, by decide⟩ ⟨11, 1, 0, 1470044, 283279, 1, 262144⟩
    (by decide) selected_cut_51622

theorem unmarked_context_10_70819_1490947 : frontier 11 ⟨1490947, by decide⟩
    (prefixCache 10 70819) (prefixPartial 10 70819) = false := by
  decide +kernel

theorem node_context_10_70819_1490947 : EJMOriginalGlobalDAGData.nodes 11 ⟨1490947, by decide⟩ =
    .split (coordinate 10) (![⟨1490873, by decide⟩,⟨1490923, by decide⟩,⟨1490946, by decide⟩,⟨1470044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_70819_1490947 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70819 ⟨1490947, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 70819
    ⟨1490947, by decide⟩ (by decide) (![⟨1490873, by decide⟩,⟨1490923, by decide⟩,⟨1490946, by decide⟩,⟨1470044, by decide⟩]) unmarked_context_10_70819_1490947 node_context_10_70819_1490947
  intro a
  fin_cases a
  · exact context_11_283276_1490873
  · exact context_11_283277_1490923
  · exact context_11_283278_1490946
  · exact context_11_283279_1470044

theorem unmarked_context_9_17704_1490948 : frontier 12 ⟨1490948, by decide⟩
    (prefixCache 9 17704) (prefixPartial 9 17704) = false := by
  decide +kernel

theorem node_context_9_17704_1490948 : EJMOriginalGlobalDAGData.nodes 12 ⟨1490948, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1490591, by decide⟩,⟨1490791, by decide⟩,⟨1490947, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17704_1490948 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17704 ⟨1490948, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17704
    ⟨1490948, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1490591, by decide⟩,⟨1490791, by decide⟩,⟨1490947, by decide⟩]) unmarked_context_9_17704_1490948 node_context_9_17704_1490948
  intro a
  fin_cases a
  · exact context_10_70816_1468246
  · exact context_10_70817_1490591
  · exact context_10_70818_1490791
  · exact context_10_70819_1490947

theorem selected_cut_51623 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 283280) = some ⟨11, 1, 0, 434745, 283280, 1, 262144⟩ := by
  decide +kernel

theorem context_11_283280_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283280 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 283280 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 283280, 1, 262144⟩
    (by decide) selected_cut_51623

theorem selected_cut_51624 : selected 10 ⟨1491014, by decide⟩
    (prefixPartial 11 283281) = some ⟨11, 2, 0, 1491014, 283281, 2101, 262144⟩ := by
  decide +kernel

theorem context_11_283281_1491014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283281 ⟨1491014, by decide⟩ :=
  accepted_of_selected 11 283281 ⟨1491014, by decide⟩ ⟨11, 2, 0, 1491014, 283281, 2101, 262144⟩
    (by decide) selected_cut_51624

theorem selected_cut_51625 : selected 10 ⟨1491032, by decide⟩
    (prefixPartial 11 283282) = some ⟨11, 2, 0, 1491032, 283282, 917, 262144⟩ := by
  decide +kernel

theorem context_11_283282_1491032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283282 ⟨1491032, by decide⟩ :=
  accepted_of_selected 11 283282 ⟨1491032, by decide⟩ ⟨11, 2, 0, 1491032, 283282, 917, 262144⟩
    (by decide) selected_cut_51625

theorem selected_cut_51626 : selected 10 ⟨1491068, by decide⟩
    (prefixPartial 11 283283) = some ⟨11, 2, 0, 1491068, 283283, 1745, 262144⟩ := by
  decide +kernel

theorem context_11_283283_1491068 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283283 ⟨1491068, by decide⟩ :=
  accepted_of_selected 11 283283 ⟨1491068, by decide⟩ ⟨11, 2, 0, 1491068, 283283, 1745, 262144⟩
    (by decide) selected_cut_51626

theorem unmarked_context_10_70820_1491069 : frontier 11 ⟨1491069, by decide⟩
    (prefixCache 10 70820) (prefixPartial 10 70820) = false := by
  decide +kernel

theorem node_context_10_70820_1491069 : EJMOriginalGlobalDAGData.nodes 11 ⟨1491069, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨1491014, by decide⟩,⟨1491032, by decide⟩,⟨1491068, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_70820_1491069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70820 ⟨1491069, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 70820
    ⟨1491069, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨1491014, by decide⟩,⟨1491032, by decide⟩,⟨1491068, by decide⟩]) unmarked_context_10_70820_1491069 node_context_10_70820_1491069
  intro a
  fin_cases a
  · exact context_11_283280_434745
  · exact context_11_283281_1491014
  · exact context_11_283282_1491032
  · exact context_11_283283_1491068

theorem selected_cut_51627 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 70821) = some ⟨10, 1, 0, 1468874, 70821, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_70821_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70821 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 70821 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 70821, 1, 1048576⟩
    (by decide) selected_cut_51627

theorem selected_cut_51628 : selected 10 ⟨1491112, by decide⟩
    (prefixPartial 11 283288) = some ⟨11, 2, 0, 1491112, 283288, 1769, 262144⟩ := by
  decide +kernel

theorem context_11_283288_1491112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283288 ⟨1491112, by decide⟩ :=
  accepted_of_selected 11 283288 ⟨1491112, by decide⟩ ⟨11, 2, 0, 1491112, 283288, 1769, 262144⟩
    (by decide) selected_cut_51628

theorem selected_cut_51629 : selected 10 ⟨1491145, by decide⟩
    (prefixPartial 11 283289) = some ⟨11, 2, 0, 1491145, 283289, 1665, 262144⟩ := by
  decide +kernel

theorem context_11_283289_1491145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283289 ⟨1491145, by decide⟩ :=
  accepted_of_selected 11 283289 ⟨1491145, by decide⟩ ⟨11, 2, 0, 1491145, 283289, 1665, 262144⟩
    (by decide) selected_cut_51629

theorem selected_cut_51630 : selected 10 ⟨1468743, by decide⟩
    (prefixPartial 11 283290) = some ⟨11, 1, 0, 1468743, 283290, 1, 262144⟩ := by
  decide +kernel

theorem context_11_283290_1468743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283290 ⟨1468743, by decide⟩ :=
  accepted_of_selected 11 283290 ⟨1468743, by decide⟩ ⟨11, 1, 0, 1468743, 283290, 1, 262144⟩
    (by decide) selected_cut_51630

theorem selected_cut_51631 : selected 10 ⟨1491183, by decide⟩
    (prefixPartial 11 283291) = some ⟨11, 2, 0, 1491183, 283291, 1509, 262144⟩ := by
  decide +kernel

theorem context_11_283291_1491183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283291 ⟨1491183, by decide⟩ :=
  accepted_of_selected 11 283291 ⟨1491183, by decide⟩ ⟨11, 2, 0, 1491183, 283291, 1509, 262144⟩
    (by decide) selected_cut_51631

theorem unmarked_context_10_70822_1491184 : frontier 11 ⟨1491184, by decide⟩
    (prefixCache 10 70822) (prefixPartial 10 70822) = false := by
  decide +kernel

theorem node_context_10_70822_1491184 : EJMOriginalGlobalDAGData.nodes 11 ⟨1491184, by decide⟩ =
    .split (coordinate 10) (![⟨1491112, by decide⟩,⟨1491145, by decide⟩,⟨1468743, by decide⟩,⟨1491183, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_70822_1491184 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70822 ⟨1491184, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 70822
    ⟨1491184, by decide⟩ (by decide) (![⟨1491112, by decide⟩,⟨1491145, by decide⟩,⟨1468743, by decide⟩,⟨1491183, by decide⟩]) unmarked_context_10_70822_1491184 node_context_10_70822_1491184
  intro a
  fin_cases a
  · exact context_11_283288_1491112
  · exact context_11_283289_1491145
  · exact context_11_283290_1468743
  · exact context_11_283291_1491183

theorem selected_cut_51632 : selected 10 ⟨1491218, by decide⟩
    (prefixPartial 11 283292) = some ⟨11, 2, 0, 1491218, 283292, 1653, 262144⟩ := by
  decide +kernel

theorem context_11_283292_1491218 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283292 ⟨1491218, by decide⟩ :=
  accepted_of_selected 11 283292 ⟨1491218, by decide⟩ ⟨11, 2, 0, 1491218, 283292, 1653, 262144⟩
    (by decide) selected_cut_51632

theorem selected_cut_51633 : selected 10 ⟨1491256, by decide⟩
    (prefixPartial 11 283293) = some ⟨11, 2, 0, 1491256, 283293, 2093, 262144⟩ := by
  decide +kernel

theorem context_11_283293_1491256 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283293 ⟨1491256, by decide⟩ :=
  accepted_of_selected 11 283293 ⟨1491256, by decide⟩ ⟨11, 2, 0, 1491256, 283293, 2093, 262144⟩
    (by decide) selected_cut_51633

theorem selected_cut_51634 : selected 10 ⟨1491269, by decide⟩
    (prefixPartial 11 283294) = some ⟨11, 2, 0, 1491269, 283294, 665, 262144⟩ := by
  decide +kernel

theorem context_11_283294_1491269 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283294 ⟨1491269, by decide⟩ :=
  accepted_of_selected 11 283294 ⟨1491269, by decide⟩ ⟨11, 2, 0, 1491269, 283294, 665, 262144⟩
    (by decide) selected_cut_51634

theorem selected_cut_51635 : selected 10 ⟨1470044, by decide⟩
    (prefixPartial 11 283295) = some ⟨11, 1, 0, 1470044, 283295, 1, 262144⟩ := by
  decide +kernel

theorem context_11_283295_1470044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283295 ⟨1470044, by decide⟩ :=
  accepted_of_selected 11 283295 ⟨1470044, by decide⟩ ⟨11, 1, 0, 1470044, 283295, 1, 262144⟩
    (by decide) selected_cut_51635

theorem unmarked_context_10_70823_1491270 : frontier 11 ⟨1491270, by decide⟩
    (prefixCache 10 70823) (prefixPartial 10 70823) = false := by
  decide +kernel

theorem node_context_10_70823_1491270 : EJMOriginalGlobalDAGData.nodes 11 ⟨1491270, by decide⟩ =
    .split (coordinate 10) (![⟨1491218, by decide⟩,⟨1491256, by decide⟩,⟨1491269, by decide⟩,⟨1470044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_70823_1491270 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70823 ⟨1491270, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 70823
    ⟨1491270, by decide⟩ (by decide) (![⟨1491218, by decide⟩,⟨1491256, by decide⟩,⟨1491269, by decide⟩,⟨1470044, by decide⟩]) unmarked_context_10_70823_1491270 node_context_10_70823_1491270
  intro a
  fin_cases a
  · exact context_11_283292_1491218
  · exact context_11_283293_1491256
  · exact context_11_283294_1491269
  · exact context_11_283295_1470044

theorem unmarked_context_9_17705_1491271 : frontier 12 ⟨1491271, by decide⟩
    (prefixCache 9 17705) (prefixPartial 9 17705) = false := by
  decide +kernel

theorem node_context_9_17705_1491271 : EJMOriginalGlobalDAGData.nodes 12 ⟨1491271, by decide⟩ =
    .split (coordinate 9) (![⟨1491069, by decide⟩,⟨1468874, by decide⟩,⟨1491184, by decide⟩,⟨1491270, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17705_1491271 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17705 ⟨1491271, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17705
    ⟨1491271, by decide⟩ (by decide) (![⟨1491069, by decide⟩,⟨1468874, by decide⟩,⟨1491184, by decide⟩,⟨1491270, by decide⟩]) unmarked_context_9_17705_1491271 node_context_9_17705_1491271
  intro a
  fin_cases a
  · exact context_10_70820_1491069
  · exact context_10_70821_1468874
  · exact context_10_70822_1491184
  · exact context_10_70823_1491270

theorem selected_cut_51636 : selected 11 ⟨1491325, by decide⟩
    (prefixPartial 10 70824) = some ⟨10, 2, 0, 1491325, 70824, 3033, 1048576⟩ := by
  decide +kernel

theorem context_10_70824_1491325 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70824 ⟨1491325, by decide⟩ :=
  accepted_of_selected 10 70824 ⟨1491325, by decide⟩ ⟨10, 2, 0, 1491325, 70824, 3033, 1048576⟩
    (by decide) selected_cut_51636

theorem selected_cut_51637 : selected 11 ⟨1491377, by decide⟩
    (prefixPartial 10 70825) = some ⟨10, 2, 0, 1491377, 70825, 2725, 1048576⟩ := by
  decide +kernel

theorem context_10_70825_1491377 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70825 ⟨1491377, by decide⟩ :=
  accepted_of_selected 10 70825 ⟨1491377, by decide⟩ ⟨10, 2, 0, 1491377, 70825, 2725, 1048576⟩
    (by decide) selected_cut_51637

theorem selected_cut_51638 : selected 11 ⟨1469103, by decide⟩
    (prefixPartial 10 70826) = some ⟨10, 1, 0, 1469103, 70826, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_70826_1469103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70826 ⟨1469103, by decide⟩ :=
  accepted_of_selected 10 70826 ⟨1469103, by decide⟩ ⟨10, 1, 0, 1469103, 70826, 1, 1048576⟩
    (by decide) selected_cut_51638

theorem selected_cut_51639 : selected 11 ⟨1491433, by decide⟩
    (prefixPartial 10 70827) = some ⟨10, 2, 0, 1491433, 70827, 2197, 1048576⟩ := by
  decide +kernel

theorem context_10_70827_1491433 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70827 ⟨1491433, by decide⟩ :=
  accepted_of_selected 10 70827 ⟨1491433, by decide⟩ ⟨10, 2, 0, 1491433, 70827, 2197, 1048576⟩
    (by decide) selected_cut_51639

theorem unmarked_context_9_17706_1491434 : frontier 12 ⟨1491434, by decide⟩
    (prefixCache 9 17706) (prefixPartial 9 17706) = false := by
  decide +kernel

theorem node_context_9_17706_1491434 : EJMOriginalGlobalDAGData.nodes 12 ⟨1491434, by decide⟩ =
    .split (coordinate 9) (![⟨1491325, by decide⟩,⟨1491377, by decide⟩,⟨1469103, by decide⟩,⟨1491433, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17706_1491434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17706 ⟨1491434, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17706
    ⟨1491434, by decide⟩ (by decide) (![⟨1491325, by decide⟩,⟨1491377, by decide⟩,⟨1469103, by decide⟩,⟨1491433, by decide⟩]) unmarked_context_9_17706_1491434 node_context_9_17706_1491434
  intro a
  fin_cases a
  · exact context_10_70824_1491325
  · exact context_10_70825_1491377
  · exact context_10_70826_1469103
  · exact context_10_70827_1491433

theorem selected_cut_51640 : selected 12 ⟨1491506, by decide⟩
    (prefixPartial 9 17707) = some ⟨9, 2, 0, 1491506, 17707, 2861, 4194304⟩ := by
  decide +kernel

theorem context_9_17707_1491506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17707 ⟨1491506, by decide⟩ :=
  accepted_of_selected 9 17707 ⟨1491506, by decide⟩ ⟨9, 2, 0, 1491506, 17707, 2861, 4194304⟩
    (by decide) selected_cut_51640

theorem unmarked_context_8_4426_1491507 : frontier 13 ⟨1491507, by decide⟩
    (prefixCache 8 4426) (prefixPartial 8 4426) = false := by
  decide +kernel

theorem node_context_8_4426_1491507 : EJMOriginalGlobalDAGData.nodes 13 ⟨1491507, by decide⟩ =
    .split (coordinate 8) (![⟨1490948, by decide⟩,⟨1491271, by decide⟩,⟨1491434, by decide⟩,⟨1491506, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4426_1491507 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4426 ⟨1491507, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4426
    ⟨1491507, by decide⟩ (by decide) (![⟨1490948, by decide⟩,⟨1491271, by decide⟩,⟨1491434, by decide⟩,⟨1491506, by decide⟩]) unmarked_context_8_4426_1491507 node_context_8_4426_1491507
  intro a
  fin_cases a
  · exact context_9_17704_1490948
  · exact context_9_17705_1491271
  · exact context_9_17706_1491434
  · exact context_9_17707_1491506

theorem selected_cut_51641 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 70832) = some ⟨10, 1, 0, 1468246, 70832, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_70832_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70832 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 70832 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 70832, 1, 1048576⟩
    (by decide) selected_cut_51641

theorem selected_cut_51642 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 1133328) = some ⟨12, 1, 0, 448748, 1133328, 1, 65536⟩ := by
  decide +kernel

theorem context_12_1133328_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1133328 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 1133328 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 1133328, 1, 65536⟩
    (by decide) selected_cut_51642

theorem selected_cut_51643 : selected 9 ⟨1491571, by decide⟩
    (prefixPartial 12 1133329) = some ⟨12, 2, 0, 1491571, 1133329, 2365, 65536⟩ := by
  decide +kernel

theorem context_12_1133329_1491571 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1133329 ⟨1491571, by decide⟩ :=
  accepted_of_selected 12 1133329 ⟨1491571, by decide⟩ ⟨12, 2, 0, 1491571, 1133329, 2365, 65536⟩
    (by decide) selected_cut_51643

theorem selected_cut_51644 : selected 9 ⟨1491626, by decide⟩
    (prefixPartial 12 1133330) = some ⟨12, 2, 0, 1491626, 1133330, 2205, 65536⟩ := by
  decide +kernel

theorem context_12_1133330_1491626 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1133330 ⟨1491626, by decide⟩ :=
  accepted_of_selected 12 1133330 ⟨1491626, by decide⟩ ⟨12, 2, 0, 1491626, 1133330, 2205, 65536⟩
    (by decide) selected_cut_51644

theorem selected_cut_51645 : selected 9 ⟨1491670, by decide⟩
    (prefixPartial 12 1133331) = some ⟨12, 2, 0, 1491670, 1133331, 1985, 65536⟩ := by
  decide +kernel

theorem context_12_1133331_1491670 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1133331 ⟨1491670, by decide⟩ :=
  accepted_of_selected 12 1133331 ⟨1491670, by decide⟩ ⟨12, 2, 0, 1491670, 1133331, 1985, 65536⟩
    (by decide) selected_cut_51645

theorem unmarked_context_11_283332_1491671 : frontier 10 ⟨1491671, by decide⟩
    (prefixCache 11 283332) (prefixPartial 11 283332) = false := by
  decide +kernel

theorem node_context_11_283332_1491671 : EJMOriginalGlobalDAGData.nodes 10 ⟨1491671, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1491571, by decide⟩,⟨1491626, by decide⟩,⟨1491670, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_283332_1491671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283332 ⟨1491671, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 283332
    ⟨1491671, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1491571, by decide⟩,⟨1491626, by decide⟩,⟨1491670, by decide⟩]) unmarked_context_11_283332_1491671 node_context_11_283332_1491671
  intro a
  fin_cases a
  · exact context_12_1133328_448748
  · exact context_12_1133329_1491571
  · exact context_12_1133330_1491626
  · exact context_12_1133331_1491670

theorem selected_cut_51646 : selected 10 ⟨1468419, by decide⟩
    (prefixPartial 11 283333) = some ⟨11, 1, 0, 1468419, 283333, 1, 262144⟩ := by
  decide +kernel

theorem context_11_283333_1468419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283333 ⟨1468419, by decide⟩ :=
  accepted_of_selected 11 283333 ⟨1468419, by decide⟩ ⟨11, 1, 0, 1468419, 283333, 1, 262144⟩
    (by decide) selected_cut_51646

theorem selected_cut_51647 : selected 10 ⟨1491741, by decide⟩
    (prefixPartial 11 283334) = some ⟨11, 2, 0, 1491741, 283334, 3425, 262144⟩ := by
  decide +kernel

theorem context_11_283334_1491741 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283334 ⟨1491741, by decide⟩ :=
  accepted_of_selected 11 283334 ⟨1491741, by decide⟩ ⟨11, 2, 0, 1491741, 283334, 3425, 262144⟩
    (by decide) selected_cut_51647

theorem selected_cut_51648 : selected 10 ⟨1491817, by decide⟩
    (prefixPartial 11 283335) = some ⟨11, 2, 0, 1491817, 283335, 3613, 262144⟩ := by
  decide +kernel

theorem context_11_283335_1491817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 283335 ⟨1491817, by decide⟩ :=
  accepted_of_selected 11 283335 ⟨1491817, by decide⟩ ⟨11, 2, 0, 1491817, 283335, 3613, 262144⟩
    (by decide) selected_cut_51648

theorem unmarked_context_10_70833_1491818 : frontier 11 ⟨1491818, by decide⟩
    (prefixCache 10 70833) (prefixPartial 10 70833) = false := by
  decide +kernel

theorem node_context_10_70833_1491818 : EJMOriginalGlobalDAGData.nodes 11 ⟨1491818, by decide⟩ =
    .split (coordinate 10) (![⟨1491671, by decide⟩,⟨1468419, by decide⟩,⟨1491741, by decide⟩,⟨1491817, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_70833_1491818 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70833 ⟨1491818, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 70833
    ⟨1491818, by decide⟩ (by decide) (![⟨1491671, by decide⟩,⟨1468419, by decide⟩,⟨1491741, by decide⟩,⟨1491817, by decide⟩]) unmarked_context_10_70833_1491818 node_context_10_70833_1491818
  intro a
  fin_cases a
  · exact context_11_283332_1491671
  · exact context_11_283333_1468419
  · exact context_11_283334_1491741
  · exact context_11_283335_1491817

theorem selected_cut_51649 : selected 9 ⟨1469342, by decide⟩
    (prefixPartial 12 1133344) = some ⟨12, 1, 0, 1469342, 1133344, 1, 65536⟩ := by
  decide +kernel

theorem context_12_1133344_1469342 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1133344 ⟨1469342, by decide⟩ :=
  accepted_of_selected 12 1133344 ⟨1469342, by decide⟩ ⟨12, 1, 0, 1469342, 1133344, 1, 65536⟩
    (by decide) selected_cut_51649

theorem selected_cut_51650 : selected 9 ⟨1491855, by decide⟩
    (prefixPartial 12 1133345) = some ⟨12, 2, 0, 1491855, 1133345, 1725, 65536⟩ := by
  decide +kernel

theorem context_12_1133345_1491855 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1133345 ⟨1491855, by decide⟩ :=
  accepted_of_selected 12 1133345 ⟨1491855, by decide⟩ ⟨12, 2, 0, 1491855, 1133345, 1725, 65536⟩
    (by decide) selected_cut_51650

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
