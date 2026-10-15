/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover504
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_11_94093_1360647 : frontier 10 ⟨1360647, by decide⟩
    (prefixCache 11 94093) (prefixPartial 11 94093) = false := by
  decide +kernel

theorem node_context_11_94093_1360647 : EJMOriginalGlobalDAGData.nodes 10 ⟨1360647, by decide⟩ =
    .split (coordinate 11) (![⟨1360528, by decide⟩,⟨1360565, by decide⟩,⟨1360606, by decide⟩,⟨1360646, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_94093_1360647 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94093 ⟨1360647, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 94093
    ⟨1360647, by decide⟩ (by decide) (![⟨1360528, by decide⟩,⟨1360565, by decide⟩,⟨1360606, by decide⟩,⟨1360646, by decide⟩]) unmarked_context_11_94093_1360647 node_context_11_94093_1360647
  intro a
  fin_cases a
  · exact context_12_376372_1360528
  · exact context_12_376373_1360565
  · exact context_12_376374_1360606
  · exact context_12_376375_1360646

theorem selected_cut_48485 : selected 10 ⟨1360707, by decide⟩
    (prefixPartial 11 94094) = some ⟨11, 2, 0, 1360707, 94094, 3621, 262144⟩ := by
  decide +kernel

theorem context_11_94094_1360707 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94094 ⟨1360707, by decide⟩ :=
  accepted_of_selected 11 94094 ⟨1360707, by decide⟩ ⟨11, 2, 0, 1360707, 94094, 3621, 262144⟩
    (by decide) selected_cut_48485

theorem selected_cut_48486 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 94095) = some ⟨11, 1, 0, 977886, 94095, 1, 262144⟩ := by
  decide +kernel

theorem context_11_94095_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94095 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 94095 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 94095, 1, 262144⟩
    (by decide) selected_cut_48486

theorem unmarked_context_10_23523_1360708 : frontier 11 ⟨1360708, by decide⟩
    (prefixCache 10 23523) (prefixPartial 10 23523) = false := by
  decide +kernel

theorem node_context_10_23523_1360708 : EJMOriginalGlobalDAGData.nodes 11 ⟨1360708, by decide⟩ =
    .split (coordinate 10) (![⟨1360479, by decide⟩,⟨1360647, by decide⟩,⟨1360707, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23523_1360708 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23523 ⟨1360708, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23523
    ⟨1360708, by decide⟩ (by decide) (![⟨1360479, by decide⟩,⟨1360647, by decide⟩,⟨1360707, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_23523_1360708 node_context_10_23523_1360708
  intro a
  fin_cases a
  · exact context_11_94092_1360479
  · exact context_11_94093_1360647
  · exact context_11_94094_1360707
  · exact context_11_94095_977886

theorem unmarked_context_9_5880_1360709 : frontier 12 ⟨1360709, by decide⟩
    (prefixCache 9 5880) (prefixPartial 9 5880) = false := by
  decide +kernel

theorem node_context_9_5880_1360709 : EJMOriginalGlobalDAGData.nodes 12 ⟨1360709, by decide⟩ =
    .split (coordinate 9) (![⟨1359463, by decide⟩,⟨1360025, by decide⟩,⟨1360379, by decide⟩,⟨1360708, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5880_1360709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5880 ⟨1360709, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5880
    ⟨1360709, by decide⟩ (by decide) (![⟨1359463, by decide⟩,⟨1360025, by decide⟩,⟨1360379, by decide⟩,⟨1360708, by decide⟩]) unmarked_context_9_5880_1360709 node_context_9_5880_1360709
  intro a
  fin_cases a
  · exact context_10_23520_1359463
  · exact context_10_23521_1360025
  · exact context_10_23522_1360379
  · exact context_10_23523_1360708

theorem selected_cut_48487 : selected 9 ⟨1173556, by decide⟩
    (prefixPartial 12 376384) = some ⟨12, 1, 0, 1173556, 376384, 1, 65536⟩ := by
  decide +kernel

theorem context_12_376384_1173556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376384 ⟨1173556, by decide⟩ :=
  accepted_of_selected 12 376384 ⟨1173556, by decide⟩ ⟨12, 1, 0, 1173556, 376384, 1, 65536⟩
    (by decide) selected_cut_48487

theorem selected_cut_48488 : selected 9 ⟨1360737, by decide⟩
    (prefixPartial 12 376385) = some ⟨12, 2, 0, 1360737, 376385, 1865, 65536⟩ := by
  decide +kernel

theorem context_12_376385_1360737 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376385 ⟨1360737, by decide⟩ :=
  accepted_of_selected 12 376385 ⟨1360737, by decide⟩ ⟨12, 2, 0, 1360737, 376385, 1865, 65536⟩
    (by decide) selected_cut_48488

theorem selected_cut_48489 : selected 9 ⟨1360768, by decide⟩
    (prefixPartial 12 376386) = some ⟨12, 2, 0, 1360768, 376386, 1953, 65536⟩ := by
  decide +kernel

theorem context_12_376386_1360768 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376386 ⟨1360768, by decide⟩ :=
  accepted_of_selected 12 376386 ⟨1360768, by decide⟩ ⟨12, 2, 0, 1360768, 376386, 1953, 65536⟩
    (by decide) selected_cut_48489

theorem selected_cut_48490 : selected 9 ⟨1360865, by decide⟩
    (prefixPartial 12 376387) = some ⟨12, 2, 0, 1360865, 376387, 1145, 65536⟩ := by
  decide +kernel

theorem context_12_376387_1360865 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376387 ⟨1360865, by decide⟩ :=
  accepted_of_selected 12 376387 ⟨1360865, by decide⟩ ⟨12, 2, 0, 1360865, 376387, 1145, 65536⟩
    (by decide) selected_cut_48490

theorem unmarked_context_11_94096_1360866 : frontier 10 ⟨1360866, by decide⟩
    (prefixCache 11 94096) (prefixPartial 11 94096) = false := by
  decide +kernel

theorem node_context_11_94096_1360866 : EJMOriginalGlobalDAGData.nodes 10 ⟨1360866, by decide⟩ =
    .split (coordinate 11) (![⟨1173556, by decide⟩,⟨1360737, by decide⟩,⟨1360768, by decide⟩,⟨1360865, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_94096_1360866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94096 ⟨1360866, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 94096
    ⟨1360866, by decide⟩ (by decide) (![⟨1173556, by decide⟩,⟨1360737, by decide⟩,⟨1360768, by decide⟩,⟨1360865, by decide⟩]) unmarked_context_11_94096_1360866 node_context_11_94096_1360866
  intro a
  fin_cases a
  · exact context_12_376384_1173556
  · exact context_12_376385_1360737
  · exact context_12_376386_1360768
  · exact context_12_376387_1360865

theorem selected_cut_48491 : selected 9 ⟨1360904, by decide⟩
    (prefixPartial 12 376388) = some ⟨12, 2, 0, 1360904, 376388, 2181, 65536⟩ := by
  decide +kernel

theorem context_12_376388_1360904 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376388 ⟨1360904, by decide⟩ :=
  accepted_of_selected 12 376388 ⟨1360904, by decide⟩ ⟨12, 2, 0, 1360904, 376388, 2181, 65536⟩
    (by decide) selected_cut_48491

theorem selected_cut_48492 : selected 9 ⟨1257136, by decide⟩
    (prefixPartial 12 376389) = some ⟨12, 1, 0, 1257136, 376389, 1, 65536⟩ := by
  decide +kernel

theorem context_12_376389_1257136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376389 ⟨1257136, by decide⟩ :=
  accepted_of_selected 12 376389 ⟨1257136, by decide⟩ ⟨12, 1, 0, 1257136, 376389, 1, 65536⟩
    (by decide) selected_cut_48492

theorem selected_cut_48493 : selected 9 ⟨1360936, by decide⟩
    (prefixPartial 12 376390) = some ⟨12, 2, 0, 1360936, 376390, 2033, 65536⟩ := by
  decide +kernel

theorem context_12_376390_1360936 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376390 ⟨1360936, by decide⟩ :=
  accepted_of_selected 12 376390 ⟨1360936, by decide⟩ ⟨12, 2, 0, 1360936, 376390, 2033, 65536⟩
    (by decide) selected_cut_48493

theorem selected_cut_48494 : selected 9 ⟨1360972, by decide⟩
    (prefixPartial 12 376391) = some ⟨12, 2, 0, 1360972, 376391, 1973, 65536⟩ := by
  decide +kernel

theorem context_12_376391_1360972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376391 ⟨1360972, by decide⟩ :=
  accepted_of_selected 12 376391 ⟨1360972, by decide⟩ ⟨12, 2, 0, 1360972, 376391, 1973, 65536⟩
    (by decide) selected_cut_48494

theorem unmarked_context_11_94097_1360973 : frontier 10 ⟨1360973, by decide⟩
    (prefixCache 11 94097) (prefixPartial 11 94097) = false := by
  decide +kernel

theorem node_context_11_94097_1360973 : EJMOriginalGlobalDAGData.nodes 10 ⟨1360973, by decide⟩ =
    .split (coordinate 11) (![⟨1360904, by decide⟩,⟨1257136, by decide⟩,⟨1360936, by decide⟩,⟨1360972, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_94097_1360973 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94097 ⟨1360973, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 94097
    ⟨1360973, by decide⟩ (by decide) (![⟨1360904, by decide⟩,⟨1257136, by decide⟩,⟨1360936, by decide⟩,⟨1360972, by decide⟩]) unmarked_context_11_94097_1360973 node_context_11_94097_1360973
  intro a
  fin_cases a
  · exact context_12_376388_1360904
  · exact context_12_376389_1257136
  · exact context_12_376390_1360936
  · exact context_12_376391_1360972

theorem selected_cut_48495 : selected 10 ⟨1361030, by decide⟩
    (prefixPartial 11 94098) = some ⟨11, 2, 0, 1361030, 94098, 3537, 262144⟩ := by
  decide +kernel

theorem context_11_94098_1361030 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94098 ⟨1361030, by decide⟩ :=
  accepted_of_selected 11 94098 ⟨1361030, by decide⟩ ⟨11, 2, 0, 1361030, 94098, 3537, 262144⟩
    (by decide) selected_cut_48495

theorem selected_cut_48496 : selected 9 ⟨1361062, by decide⟩
    (prefixPartial 12 376396) = some ⟨12, 2, 0, 1361062, 376396, 1921, 65536⟩ := by
  decide +kernel

theorem context_12_376396_1361062 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376396 ⟨1361062, by decide⟩ :=
  accepted_of_selected 12 376396 ⟨1361062, by decide⟩ ⟨12, 2, 0, 1361062, 376396, 1921, 65536⟩
    (by decide) selected_cut_48496

theorem selected_cut_48497 : selected 9 ⟨1361087, by decide⟩
    (prefixPartial 12 376397) = some ⟨12, 2, 0, 1361087, 376397, 1689, 65536⟩ := by
  decide +kernel

theorem context_12_376397_1361087 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376397 ⟨1361087, by decide⟩ :=
  accepted_of_selected 12 376397 ⟨1361087, by decide⟩ ⟨12, 2, 0, 1361087, 376397, 1689, 65536⟩
    (by decide) selected_cut_48497

theorem selected_cut_48498 : selected 9 ⟨1361115, by decide⟩
    (prefixPartial 12 376398) = some ⟨12, 2, 0, 1361115, 376398, 1633, 65536⟩ := by
  decide +kernel

theorem context_12_376398_1361115 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376398 ⟨1361115, by decide⟩ :=
  accepted_of_selected 12 376398 ⟨1361115, by decide⟩ ⟨12, 2, 0, 1361115, 376398, 1633, 65536⟩
    (by decide) selected_cut_48498

theorem selected_cut_48499 : selected 9 ⟨1361141, by decide⟩
    (prefixPartial 12 376399) = some ⟨12, 2, 0, 1361141, 376399, 1669, 65536⟩ := by
  decide +kernel

theorem context_12_376399_1361141 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376399 ⟨1361141, by decide⟩ :=
  accepted_of_selected 12 376399 ⟨1361141, by decide⟩ ⟨12, 2, 0, 1361141, 376399, 1669, 65536⟩
    (by decide) selected_cut_48499

theorem unmarked_context_11_94099_1361142 : frontier 10 ⟨1361142, by decide⟩
    (prefixCache 11 94099) (prefixPartial 11 94099) = false := by
  decide +kernel

theorem node_context_11_94099_1361142 : EJMOriginalGlobalDAGData.nodes 10 ⟨1361142, by decide⟩ =
    .split (coordinate 11) (![⟨1361062, by decide⟩,⟨1361087, by decide⟩,⟨1361115, by decide⟩,⟨1361141, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_94099_1361142 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94099 ⟨1361142, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 94099
    ⟨1361142, by decide⟩ (by decide) (![⟨1361062, by decide⟩,⟨1361087, by decide⟩,⟨1361115, by decide⟩,⟨1361141, by decide⟩]) unmarked_context_11_94099_1361142 node_context_11_94099_1361142
  intro a
  fin_cases a
  · exact context_12_376396_1361062
  · exact context_12_376397_1361087
  · exact context_12_376398_1361115
  · exact context_12_376399_1361141

theorem unmarked_context_10_23524_1361143 : frontier 11 ⟨1361143, by decide⟩
    (prefixCache 10 23524) (prefixPartial 10 23524) = false := by
  decide +kernel

theorem node_context_10_23524_1361143 : EJMOriginalGlobalDAGData.nodes 11 ⟨1361143, by decide⟩ =
    .split (coordinate 10) (![⟨1360866, by decide⟩,⟨1360973, by decide⟩,⟨1361030, by decide⟩,⟨1361142, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23524_1361143 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23524 ⟨1361143, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23524
    ⟨1361143, by decide⟩ (by decide) (![⟨1360866, by decide⟩,⟨1360973, by decide⟩,⟨1361030, by decide⟩,⟨1361142, by decide⟩]) unmarked_context_10_23524_1361143 node_context_10_23524_1361143
  intro a
  fin_cases a
  · exact context_11_94096_1360866
  · exact context_11_94097_1360973
  · exact context_11_94098_1361030
  · exact context_11_94099_1361142

theorem selected_cut_48500 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 23525) = some ⟨10, 1, 0, 893098, 23525, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_23525_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23525 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 23525 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 23525, 1, 1048576⟩
    (by decide) selected_cut_48500

theorem selected_cut_48501 : selected 10 ⟨1361195, by decide⟩
    (prefixPartial 11 94104) = some ⟨11, 2, 0, 1361195, 94104, 2869, 262144⟩ := by
  decide +kernel

theorem context_11_94104_1361195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94104 ⟨1361195, by decide⟩ :=
  accepted_of_selected 11 94104 ⟨1361195, by decide⟩ ⟨11, 2, 0, 1361195, 94104, 2869, 262144⟩
    (by decide) selected_cut_48501

theorem selected_cut_48502 : selected 9 ⟨1361217, by decide⟩
    (prefixPartial 12 376420) = some ⟨12, 2, 0, 1361217, 376420, 1501, 65536⟩ := by
  decide +kernel

theorem context_12_376420_1361217 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376420 ⟨1361217, by decide⟩ :=
  accepted_of_selected 12 376420 ⟨1361217, by decide⟩ ⟨12, 2, 0, 1361217, 376420, 1501, 65536⟩
    (by decide) selected_cut_48502

theorem selected_cut_48503 : selected 9 ⟨1256866, by decide⟩
    (prefixPartial 12 376421) = some ⟨12, 1, 0, 1256866, 376421, 1, 65536⟩ := by
  decide +kernel

theorem context_12_376421_1256866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376421 ⟨1256866, by decide⟩ :=
  accepted_of_selected 12 376421 ⟨1256866, by decide⟩ ⟨12, 1, 0, 1256866, 376421, 1, 65536⟩
    (by decide) selected_cut_48503

theorem selected_cut_48504 : selected 9 ⟨1361241, by decide⟩
    (prefixPartial 12 376422) = some ⟨12, 2, 0, 1361241, 376422, 1401, 65536⟩ := by
  decide +kernel

theorem context_12_376422_1361241 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376422 ⟨1361241, by decide⟩ :=
  accepted_of_selected 12 376422 ⟨1361241, by decide⟩ ⟨12, 2, 0, 1361241, 376422, 1401, 65536⟩
    (by decide) selected_cut_48504

theorem selected_cut_48505 : selected 9 ⟨1361268, by decide⟩
    (prefixPartial 12 376423) = some ⟨12, 2, 0, 1361268, 376423, 1469, 65536⟩ := by
  decide +kernel

theorem context_12_376423_1361268 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376423 ⟨1361268, by decide⟩ :=
  accepted_of_selected 12 376423 ⟨1361268, by decide⟩ ⟨12, 2, 0, 1361268, 376423, 1469, 65536⟩
    (by decide) selected_cut_48505

theorem unmarked_context_11_94105_1361269 : frontier 10 ⟨1361269, by decide⟩
    (prefixCache 11 94105) (prefixPartial 11 94105) = false := by
  decide +kernel

theorem node_context_11_94105_1361269 : EJMOriginalGlobalDAGData.nodes 10 ⟨1361269, by decide⟩ =
    .split (coordinate 11) (![⟨1361217, by decide⟩,⟨1256866, by decide⟩,⟨1361241, by decide⟩,⟨1361268, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_94105_1361269 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94105 ⟨1361269, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 94105
    ⟨1361269, by decide⟩ (by decide) (![⟨1361217, by decide⟩,⟨1256866, by decide⟩,⟨1361241, by decide⟩,⟨1361268, by decide⟩]) unmarked_context_11_94105_1361269 node_context_11_94105_1361269
  intro a
  fin_cases a
  · exact context_12_376420_1361217
  · exact context_12_376421_1256866
  · exact context_12_376422_1361241
  · exact context_12_376423_1361268

theorem selected_cut_48506 : selected 10 ⟨1361288, by decide⟩
    (prefixPartial 11 94106) = some ⟨11, 2, 0, 1361288, 94106, 1153, 262144⟩ := by
  decide +kernel

theorem context_11_94106_1361288 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94106 ⟨1361288, by decide⟩ :=
  accepted_of_selected 11 94106 ⟨1361288, by decide⟩ ⟨11, 2, 0, 1361288, 94106, 1153, 262144⟩
    (by decide) selected_cut_48506

theorem selected_cut_48507 : selected 10 ⟨1361329, by decide⟩
    (prefixPartial 11 94107) = some ⟨11, 2, 0, 1361329, 94107, 2373, 262144⟩ := by
  decide +kernel

theorem context_11_94107_1361329 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94107 ⟨1361329, by decide⟩ :=
  accepted_of_selected 11 94107 ⟨1361329, by decide⟩ ⟨11, 2, 0, 1361329, 94107, 2373, 262144⟩
    (by decide) selected_cut_48507

theorem unmarked_context_10_23526_1361330 : frontier 11 ⟨1361330, by decide⟩
    (prefixCache 10 23526) (prefixPartial 10 23526) = false := by
  decide +kernel

theorem node_context_10_23526_1361330 : EJMOriginalGlobalDAGData.nodes 11 ⟨1361330, by decide⟩ =
    .split (coordinate 10) (![⟨1361195, by decide⟩,⟨1361269, by decide⟩,⟨1361288, by decide⟩,⟨1361329, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23526_1361330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23526 ⟨1361330, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23526
    ⟨1361330, by decide⟩ (by decide) (![⟨1361195, by decide⟩,⟨1361269, by decide⟩,⟨1361288, by decide⟩,⟨1361329, by decide⟩]) unmarked_context_10_23526_1361330 node_context_10_23526_1361330
  intro a
  fin_cases a
  · exact context_11_94104_1361195
  · exact context_11_94105_1361269
  · exact context_11_94106_1361288
  · exact context_11_94107_1361329

theorem selected_cut_48508 : selected 10 ⟨1361399, by decide⟩
    (prefixPartial 11 94108) = some ⟨11, 2, 0, 1361399, 94108, 4021, 262144⟩ := by
  decide +kernel

theorem context_11_94108_1361399 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94108 ⟨1361399, by decide⟩ :=
  accepted_of_selected 11 94108 ⟨1361399, by decide⟩ ⟨11, 2, 0, 1361399, 94108, 4021, 262144⟩
    (by decide) selected_cut_48508

theorem selected_cut_48509 : selected 10 ⟨1361457, by decide⟩
    (prefixPartial 11 94109) = some ⟨11, 2, 0, 1361457, 94109, 2885, 262144⟩ := by
  decide +kernel

theorem context_11_94109_1361457 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94109 ⟨1361457, by decide⟩ :=
  accepted_of_selected 11 94109 ⟨1361457, by decide⟩ ⟨11, 2, 0, 1361457, 94109, 2885, 262144⟩
    (by decide) selected_cut_48509

theorem selected_cut_48510 : selected 10 ⟨1361484, by decide⟩
    (prefixPartial 11 94110) = some ⟨11, 2, 0, 1361484, 94110, 1605, 262144⟩ := by
  decide +kernel

theorem context_11_94110_1361484 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94110 ⟨1361484, by decide⟩ :=
  accepted_of_selected 11 94110 ⟨1361484, by decide⟩ ⟨11, 2, 0, 1361484, 94110, 1605, 262144⟩
    (by decide) selected_cut_48510

theorem selected_cut_48511 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 94111) = some ⟨11, 1, 0, 977886, 94111, 1, 262144⟩ := by
  decide +kernel

theorem context_11_94111_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94111 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 94111 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 94111, 1, 262144⟩
    (by decide) selected_cut_48511

theorem unmarked_context_10_23527_1361485 : frontier 11 ⟨1361485, by decide⟩
    (prefixCache 10 23527) (prefixPartial 10 23527) = false := by
  decide +kernel

theorem node_context_10_23527_1361485 : EJMOriginalGlobalDAGData.nodes 11 ⟨1361485, by decide⟩ =
    .split (coordinate 10) (![⟨1361399, by decide⟩,⟨1361457, by decide⟩,⟨1361484, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23527_1361485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23527 ⟨1361485, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23527
    ⟨1361485, by decide⟩ (by decide) (![⟨1361399, by decide⟩,⟨1361457, by decide⟩,⟨1361484, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_23527_1361485 node_context_10_23527_1361485
  intro a
  fin_cases a
  · exact context_11_94108_1361399
  · exact context_11_94109_1361457
  · exact context_11_94110_1361484
  · exact context_11_94111_977886

theorem unmarked_context_9_5881_1361486 : frontier 12 ⟨1361486, by decide⟩
    (prefixCache 9 5881) (prefixPartial 9 5881) = false := by
  decide +kernel

theorem node_context_9_5881_1361486 : EJMOriginalGlobalDAGData.nodes 12 ⟨1361486, by decide⟩ =
    .split (coordinate 9) (![⟨1361143, by decide⟩,⟨893098, by decide⟩,⟨1361330, by decide⟩,⟨1361485, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5881_1361486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5881 ⟨1361486, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5881
    ⟨1361486, by decide⟩ (by decide) (![⟨1361143, by decide⟩,⟨893098, by decide⟩,⟨1361330, by decide⟩,⟨1361485, by decide⟩]) unmarked_context_9_5881_1361486 node_context_9_5881_1361486
  intro a
  fin_cases a
  · exact context_10_23524_1361143
  · exact context_10_23525_893098
  · exact context_10_23526_1361330
  · exact context_10_23527_1361485

theorem selected_cut_48512 : selected 10 ⟨1361505, by decide⟩
    (prefixPartial 11 94112) = some ⟨11, 2, 0, 1361505, 94112, 1137, 262144⟩ := by
  decide +kernel

theorem context_11_94112_1361505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94112 ⟨1361505, by decide⟩ :=
  accepted_of_selected 11 94112 ⟨1361505, by decide⟩ ⟨11, 2, 0, 1361505, 94112, 1137, 262144⟩
    (by decide) selected_cut_48512

theorem selected_cut_48513 : selected 10 ⟨1361544, by decide⟩
    (prefixPartial 11 94113) = some ⟨11, 2, 0, 1361544, 94113, 2465, 262144⟩ := by
  decide +kernel

theorem context_11_94113_1361544 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94113 ⟨1361544, by decide⟩ :=
  accepted_of_selected 11 94113 ⟨1361544, by decide⟩ ⟨11, 2, 0, 1361544, 94113, 2465, 262144⟩
    (by decide) selected_cut_48513

theorem selected_cut_48514 : selected 10 ⟨1361591, by decide⟩
    (prefixPartial 11 94114) = some ⟨11, 2, 0, 1361591, 94114, 2909, 262144⟩ := by
  decide +kernel

theorem context_11_94114_1361591 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94114 ⟨1361591, by decide⟩ :=
  accepted_of_selected 11 94114 ⟨1361591, by decide⟩ ⟨11, 2, 0, 1361591, 94114, 2909, 262144⟩
    (by decide) selected_cut_48514

theorem selected_cut_48515 : selected 10 ⟨1361621, by decide⟩
    (prefixPartial 11 94115) = some ⟨11, 2, 0, 1361621, 94115, 1873, 262144⟩ := by
  decide +kernel

theorem context_11_94115_1361621 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94115 ⟨1361621, by decide⟩ :=
  accepted_of_selected 11 94115 ⟨1361621, by decide⟩ ⟨11, 2, 0, 1361621, 94115, 1873, 262144⟩
    (by decide) selected_cut_48515

theorem unmarked_context_10_23528_1361622 : frontier 11 ⟨1361622, by decide⟩
    (prefixCache 10 23528) (prefixPartial 10 23528) = false := by
  decide +kernel

theorem node_context_10_23528_1361622 : EJMOriginalGlobalDAGData.nodes 11 ⟨1361622, by decide⟩ =
    .split (coordinate 10) (![⟨1361505, by decide⟩,⟨1361544, by decide⟩,⟨1361591, by decide⟩,⟨1361621, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23528_1361622 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23528 ⟨1361622, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23528
    ⟨1361622, by decide⟩ (by decide) (![⟨1361505, by decide⟩,⟨1361544, by decide⟩,⟨1361591, by decide⟩,⟨1361621, by decide⟩]) unmarked_context_10_23528_1361622 node_context_10_23528_1361622
  intro a
  fin_cases a
  · exact context_11_94112_1361505
  · exact context_11_94113_1361544
  · exact context_11_94114_1361591
  · exact context_11_94115_1361621

theorem selected_cut_48516 : selected 10 ⟨1361657, by decide⟩
    (prefixPartial 11 94116) = some ⟨11, 2, 0, 1361657, 94116, 2009, 262144⟩ := by
  decide +kernel

theorem context_11_94116_1361657 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94116 ⟨1361657, by decide⟩ :=
  accepted_of_selected 11 94116 ⟨1361657, by decide⟩ ⟨11, 2, 0, 1361657, 94116, 2009, 262144⟩
    (by decide) selected_cut_48516

theorem selected_cut_48517 : selected 10 ⟨1361678, by decide⟩
    (prefixPartial 11 94117) = some ⟨11, 2, 0, 1361678, 94117, 949, 262144⟩ := by
  decide +kernel

theorem context_11_94117_1361678 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94117 ⟨1361678, by decide⟩ :=
  accepted_of_selected 11 94117 ⟨1361678, by decide⟩ ⟨11, 2, 0, 1361678, 94117, 949, 262144⟩
    (by decide) selected_cut_48517

theorem selected_cut_48518 : selected 10 ⟨1361715, by decide⟩
    (prefixPartial 11 94118) = some ⟨11, 2, 0, 1361715, 94118, 2205, 262144⟩ := by
  decide +kernel

theorem context_11_94118_1361715 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94118 ⟨1361715, by decide⟩ :=
  accepted_of_selected 11 94118 ⟨1361715, by decide⟩ ⟨11, 2, 0, 1361715, 94118, 2205, 262144⟩
    (by decide) selected_cut_48518

theorem selected_cut_48519 : selected 10 ⟨1361737, by decide⟩
    (prefixPartial 11 94119) = some ⟨11, 2, 0, 1361737, 94119, 1321, 262144⟩ := by
  decide +kernel

theorem context_11_94119_1361737 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94119 ⟨1361737, by decide⟩ :=
  accepted_of_selected 11 94119 ⟨1361737, by decide⟩ ⟨11, 2, 0, 1361737, 94119, 1321, 262144⟩
    (by decide) selected_cut_48519

theorem unmarked_context_10_23529_1361738 : frontier 11 ⟨1361738, by decide⟩
    (prefixCache 10 23529) (prefixPartial 10 23529) = false := by
  decide +kernel

theorem node_context_10_23529_1361738 : EJMOriginalGlobalDAGData.nodes 11 ⟨1361738, by decide⟩ =
    .split (coordinate 10) (![⟨1361657, by decide⟩,⟨1361678, by decide⟩,⟨1361715, by decide⟩,⟨1361737, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23529_1361738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23529 ⟨1361738, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23529
    ⟨1361738, by decide⟩ (by decide) (![⟨1361657, by decide⟩,⟨1361678, by decide⟩,⟨1361715, by decide⟩,⟨1361737, by decide⟩]) unmarked_context_10_23529_1361738 node_context_10_23529_1361738
  intro a
  fin_cases a
  · exact context_11_94116_1361657
  · exact context_11_94117_1361678
  · exact context_11_94118_1361715
  · exact context_11_94119_1361737

theorem selected_cut_48520 : selected 11 ⟨1361760, by decide⟩
    (prefixPartial 10 23530) = some ⟨10, 2, 0, 1361760, 23530, 1125, 1048576⟩ := by
  decide +kernel

theorem context_10_23530_1361760 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23530 ⟨1361760, by decide⟩ :=
  accepted_of_selected 10 23530 ⟨1361760, by decide⟩ ⟨10, 2, 0, 1361760, 23530, 1125, 1048576⟩
    (by decide) selected_cut_48520

theorem selected_cut_48521 : selected 11 ⟨1361817, by decide⟩
    (prefixPartial 10 23531) = some ⟨10, 2, 0, 1361817, 23531, 3137, 1048576⟩ := by
  decide +kernel

theorem context_10_23531_1361817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23531 ⟨1361817, by decide⟩ :=
  accepted_of_selected 10 23531 ⟨1361817, by decide⟩ ⟨10, 2, 0, 1361817, 23531, 3137, 1048576⟩
    (by decide) selected_cut_48521

theorem unmarked_context_9_5882_1361818 : frontier 12 ⟨1361818, by decide⟩
    (prefixCache 9 5882) (prefixPartial 9 5882) = false := by
  decide +kernel

theorem node_context_9_5882_1361818 : EJMOriginalGlobalDAGData.nodes 12 ⟨1361818, by decide⟩ =
    .split (coordinate 9) (![⟨1361622, by decide⟩,⟨1361738, by decide⟩,⟨1361760, by decide⟩,⟨1361817, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5882_1361818 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5882 ⟨1361818, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5882
    ⟨1361818, by decide⟩ (by decide) (![⟨1361622, by decide⟩,⟨1361738, by decide⟩,⟨1361760, by decide⟩,⟨1361817, by decide⟩]) unmarked_context_9_5882_1361818 node_context_9_5882_1361818
  intro a
  fin_cases a
  · exact context_10_23528_1361622
  · exact context_10_23529_1361738
  · exact context_10_23530_1361760
  · exact context_10_23531_1361817

theorem selected_cut_48522 : selected 11 ⟨1361875, by decide⟩
    (prefixPartial 10 23532) = some ⟨10, 2, 0, 1361875, 23532, 3541, 1048576⟩ := by
  decide +kernel

theorem context_10_23532_1361875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23532 ⟨1361875, by decide⟩ :=
  accepted_of_selected 10 23532 ⟨1361875, by decide⟩ ⟨10, 2, 0, 1361875, 23532, 3541, 1048576⟩
    (by decide) selected_cut_48522

theorem selected_cut_48523 : selected 11 ⟨1361909, by decide⟩
    (prefixPartial 10 23533) = some ⟨10, 2, 0, 1361909, 23533, 1685, 1048576⟩ := by
  decide +kernel

theorem context_10_23533_1361909 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23533 ⟨1361909, by decide⟩ :=
  accepted_of_selected 10 23533 ⟨1361909, by decide⟩ ⟨10, 2, 0, 1361909, 23533, 1685, 1048576⟩
    (by decide) selected_cut_48523

theorem selected_cut_48524 : selected 11 ⟨1361932, by decide⟩
    (prefixPartial 10 23534) = some ⟨10, 2, 0, 1361932, 23534, 617, 1048576⟩ := by
  decide +kernel

theorem context_10_23534_1361932 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23534 ⟨1361932, by decide⟩ :=
  accepted_of_selected 10 23534 ⟨1361932, by decide⟩ ⟨10, 2, 0, 1361932, 23534, 617, 1048576⟩
    (by decide) selected_cut_48524

theorem selected_cut_48525 : selected 11 ⟨1361943, by decide⟩
    (prefixPartial 10 23535) = some ⟨10, 2, 0, 1361943, 23535, 93, 1048576⟩ := by
  decide +kernel

theorem context_10_23535_1361943 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23535 ⟨1361943, by decide⟩ :=
  accepted_of_selected 10 23535 ⟨1361943, by decide⟩ ⟨10, 2, 0, 1361943, 23535, 93, 1048576⟩
    (by decide) selected_cut_48525

theorem unmarked_context_9_5883_1361944 : frontier 12 ⟨1361944, by decide⟩
    (prefixCache 9 5883) (prefixPartial 9 5883) = false := by
  decide +kernel

theorem node_context_9_5883_1361944 : EJMOriginalGlobalDAGData.nodes 12 ⟨1361944, by decide⟩ =
    .split (coordinate 9) (![⟨1361875, by decide⟩,⟨1361909, by decide⟩,⟨1361932, by decide⟩,⟨1361943, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5883_1361944 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5883 ⟨1361944, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5883
    ⟨1361944, by decide⟩ (by decide) (![⟨1361875, by decide⟩,⟨1361909, by decide⟩,⟨1361932, by decide⟩,⟨1361943, by decide⟩]) unmarked_context_9_5883_1361944 node_context_9_5883_1361944
  intro a
  fin_cases a
  · exact context_10_23532_1361875
  · exact context_10_23533_1361909
  · exact context_10_23534_1361932
  · exact context_10_23535_1361943

theorem unmarked_context_8_1470_1361945 : frontier 13 ⟨1361945, by decide⟩
    (prefixCache 8 1470) (prefixPartial 8 1470) = false := by
  decide +kernel

theorem node_context_8_1470_1361945 : EJMOriginalGlobalDAGData.nodes 13 ⟨1361945, by decide⟩ =
    .split (coordinate 8) (![⟨1360709, by decide⟩,⟨1361486, by decide⟩,⟨1361818, by decide⟩,⟨1361944, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1470_1361945 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1470 ⟨1361945, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1470
    ⟨1361945, by decide⟩ (by decide) (![⟨1360709, by decide⟩,⟨1361486, by decide⟩,⟨1361818, by decide⟩,⟨1361944, by decide⟩]) unmarked_context_8_1470_1361945 node_context_8_1470_1361945
  intro a
  fin_cases a
  · exact context_9_5880_1360709
  · exact context_9_5881_1361486
  · exact context_9_5882_1361818
  · exact context_9_5883_1361944

theorem selected_cut_48526 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 94144) = some ⟨11, 1, 0, 434745, 94144, 1, 262144⟩ := by
  decide +kernel

theorem context_11_94144_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94144 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 94144 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 94144, 1, 262144⟩
    (by decide) selected_cut_48526

theorem selected_cut_48527 : selected 10 ⟨1361946, by decide⟩
    (prefixPartial 11 94145) = some ⟨11, 2, 0, 1361946, 94145, 5, 262144⟩ := by
  decide +kernel

theorem context_11_94145_1361946 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94145 ⟨1361946, by decide⟩ :=
  accepted_of_selected 11 94145 ⟨1361946, by decide⟩ ⟨11, 2, 0, 1361946, 94145, 5, 262144⟩
    (by decide) selected_cut_48527

theorem selected_cut_48528 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 376584) = some ⟨12, 1, 0, 448748, 376584, 1, 65536⟩ := by
  decide +kernel

theorem context_12_376584_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376584 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 376584 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 376584, 1, 65536⟩
    (by decide) selected_cut_48528

theorem selected_cut_48529 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 376585) = some ⟨12, 1, 0, 34034, 376585, 1, 65536⟩ := by
  decide +kernel

theorem context_12_376585_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376585 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 376585 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 376585, 1, 65536⟩
    (by decide) selected_cut_48529

theorem selected_cut_48530 : selected 9 ⟨1362011, by decide⟩
    (prefixPartial 12 376586) = some ⟨12, 2, 0, 1362011, 376586, 3101, 65536⟩ := by
  decide +kernel

theorem context_12_376586_1362011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376586 ⟨1362011, by decide⟩ :=
  accepted_of_selected 12 376586 ⟨1362011, by decide⟩ ⟨12, 2, 0, 1362011, 376586, 3101, 65536⟩
    (by decide) selected_cut_48530

theorem selected_cut_48531 : selected 9 ⟨1362067, by decide⟩
    (prefixPartial 12 376587) = some ⟨12, 2, 0, 1362067, 376587, 2849, 65536⟩ := by
  decide +kernel

theorem context_12_376587_1362067 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376587 ⟨1362067, by decide⟩ :=
  accepted_of_selected 12 376587 ⟨1362067, by decide⟩ ⟨12, 2, 0, 1362067, 376587, 2849, 65536⟩
    (by decide) selected_cut_48531

theorem unmarked_context_11_94146_1362068 : frontier 10 ⟨1362068, by decide⟩
    (prefixCache 11 94146) (prefixPartial 11 94146) = false := by
  decide +kernel

theorem node_context_11_94146_1362068 : EJMOriginalGlobalDAGData.nodes 10 ⟨1362068, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1362011, by decide⟩,⟨1362067, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_94146_1362068 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94146 ⟨1362068, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 94146
    ⟨1362068, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1362011, by decide⟩,⟨1362067, by decide⟩]) unmarked_context_11_94146_1362068 node_context_11_94146_1362068
  intro a
  fin_cases a
  · exact context_12_376584_448748
  · exact context_12_376585_34034
  · exact context_12_376586_1362011
  · exact context_12_376587_1362067

theorem selected_cut_48532 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 376588) = some ⟨12, 1, 0, 448748, 376588, 1, 65536⟩ := by
  decide +kernel

theorem context_12_376588_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376588 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 376588 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 376588, 1, 65536⟩
    (by decide) selected_cut_48532

theorem selected_cut_48533 : selected 9 ⟨1362132, by decide⟩
    (prefixPartial 12 376589) = some ⟨12, 2, 0, 1362132, 376589, 3013, 65536⟩ := by
  decide +kernel

theorem context_12_376589_1362132 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376589 ⟨1362132, by decide⟩ :=
  accepted_of_selected 12 376589 ⟨1362132, by decide⟩ ⟨12, 2, 0, 1362132, 376589, 3013, 65536⟩
    (by decide) selected_cut_48533

theorem selected_cut_48534 : selected 9 ⟨1362190, by decide⟩
    (prefixPartial 12 376590) = some ⟨12, 2, 0, 1362190, 376590, 3029, 65536⟩ := by
  decide +kernel

theorem context_12_376590_1362190 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376590 ⟨1362190, by decide⟩ :=
  accepted_of_selected 12 376590 ⟨1362190, by decide⟩ ⟨12, 2, 0, 1362190, 376590, 3029, 65536⟩
    (by decide) selected_cut_48534

theorem selected_cut_48535 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 376591) = some ⟨12, 1, 0, 903806, 376591, 1, 65536⟩ := by
  decide +kernel

theorem context_12_376591_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376591 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 376591 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 376591, 1, 65536⟩
    (by decide) selected_cut_48535

theorem unmarked_context_11_94147_1362191 : frontier 10 ⟨1362191, by decide⟩
    (prefixCache 11 94147) (prefixPartial 11 94147) = false := by
  decide +kernel

theorem node_context_11_94147_1362191 : EJMOriginalGlobalDAGData.nodes 10 ⟨1362191, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1362132, by decide⟩,⟨1362190, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_94147_1362191 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94147 ⟨1362191, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 94147
    ⟨1362191, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1362132, by decide⟩,⟨1362190, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_94147_1362191 node_context_11_94147_1362191
  intro a
  fin_cases a
  · exact context_12_376588_448748
  · exact context_12_376589_1362132
  · exact context_12_376590_1362190
  · exact context_12_376591_903806

theorem unmarked_context_10_23536_1362192 : frontier 11 ⟨1362192, by decide⟩
    (prefixCache 10 23536) (prefixPartial 10 23536) = false := by
  decide +kernel

theorem node_context_10_23536_1362192 : EJMOriginalGlobalDAGData.nodes 11 ⟨1362192, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨1361946, by decide⟩,⟨1362068, by decide⟩,⟨1362191, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23536_1362192 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23536 ⟨1362192, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23536
    ⟨1362192, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨1361946, by decide⟩,⟨1362068, by decide⟩,⟨1362191, by decide⟩]) unmarked_context_10_23536_1362192 node_context_10_23536_1362192
  intro a
  fin_cases a
  · exact context_11_94144_434745
  · exact context_11_94145_1361946
  · exact context_11_94146_1362068
  · exact context_11_94147_1362191

theorem selected_cut_48536 : selected 9 ⟨1255011, by decide⟩
    (prefixPartial 12 376592) = some ⟨12, 1, 0, 1255011, 376592, 1, 65536⟩ := by
  decide +kernel

theorem context_12_376592_1255011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376592 ⟨1255011, by decide⟩ :=
  accepted_of_selected 12 376592 ⟨1255011, by decide⟩ ⟨12, 1, 0, 1255011, 376592, 1, 65536⟩
    (by decide) selected_cut_48536

theorem selected_cut_48537 : selected 9 ⟨1362245, by decide⟩
    (prefixPartial 12 376593) = some ⟨12, 2, 0, 1362245, 376593, 2781, 65536⟩ := by
  decide +kernel

theorem context_12_376593_1362245 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376593 ⟨1362245, by decide⟩ :=
  accepted_of_selected 12 376593 ⟨1362245, by decide⟩ ⟨12, 2, 0, 1362245, 376593, 2781, 65536⟩
    (by decide) selected_cut_48537

theorem selected_cut_48538 : selected 9 ⟨1362299, by decide⟩
    (prefixPartial 12 376594) = some ⟨12, 2, 0, 1362299, 376594, 2909, 65536⟩ := by
  decide +kernel

theorem context_12_376594_1362299 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376594 ⟨1362299, by decide⟩ :=
  accepted_of_selected 12 376594 ⟨1362299, by decide⟩ ⟨12, 2, 0, 1362299, 376594, 2909, 65536⟩
    (by decide) selected_cut_48538

theorem selected_cut_48539 : selected 9 ⟨1362340, by decide⟩
    (prefixPartial 12 376595) = some ⟨12, 2, 0, 1362340, 376595, 2729, 65536⟩ := by
  decide +kernel

theorem context_12_376595_1362340 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376595 ⟨1362340, by decide⟩ :=
  accepted_of_selected 12 376595 ⟨1362340, by decide⟩ ⟨12, 2, 0, 1362340, 376595, 2729, 65536⟩
    (by decide) selected_cut_48539

theorem unmarked_context_11_94148_1362341 : frontier 10 ⟨1362341, by decide⟩
    (prefixCache 11 94148) (prefixPartial 11 94148) = false := by
  decide +kernel

theorem node_context_11_94148_1362341 : EJMOriginalGlobalDAGData.nodes 10 ⟨1362341, by decide⟩ =
    .split (coordinate 11) (![⟨1255011, by decide⟩,⟨1362245, by decide⟩,⟨1362299, by decide⟩,⟨1362340, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_94148_1362341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94148 ⟨1362341, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 94148
    ⟨1362341, by decide⟩ (by decide) (![⟨1255011, by decide⟩,⟨1362245, by decide⟩,⟨1362299, by decide⟩,⟨1362340, by decide⟩]) unmarked_context_11_94148_1362341 node_context_11_94148_1362341
  intro a
  fin_cases a
  · exact context_12_376592_1255011
  · exact context_12_376593_1362245
  · exact context_12_376594_1362299
  · exact context_12_376595_1362340

theorem selected_cut_48540 : selected 9 ⟨1362406, by decide⟩
    (prefixPartial 12 376596) = some ⟨12, 2, 0, 1362406, 376596, 3161, 65536⟩ := by
  decide +kernel

theorem context_12_376596_1362406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376596 ⟨1362406, by decide⟩ :=
  accepted_of_selected 12 376596 ⟨1362406, by decide⟩ ⟨12, 2, 0, 1362406, 376596, 3161, 65536⟩
    (by decide) selected_cut_48540

theorem selected_cut_48541 : selected 9 ⟨1172003, by decide⟩
    (prefixPartial 12 376597) = some ⟨12, 1, 0, 1172003, 376597, 1, 65536⟩ := by
  decide +kernel

theorem context_12_376597_1172003 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376597 ⟨1172003, by decide⟩ :=
  accepted_of_selected 12 376597 ⟨1172003, by decide⟩ ⟨12, 1, 0, 1172003, 376597, 1, 65536⟩
    (by decide) selected_cut_48541

theorem selected_cut_48542 : selected 9 ⟨1362462, by decide⟩
    (prefixPartial 12 376598) = some ⟨12, 2, 0, 1362462, 376598, 3165, 65536⟩ := by
  decide +kernel

theorem context_12_376598_1362462 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376598 ⟨1362462, by decide⟩ :=
  accepted_of_selected 12 376598 ⟨1362462, by decide⟩ ⟨12, 2, 0, 1362462, 376598, 3165, 65536⟩
    (by decide) selected_cut_48542

theorem selected_cut_48543 : selected 9 ⟨692794, by decide⟩
    (prefixPartial 12 376599) = some ⟨12, 1, 0, 692794, 376599, 1, 65536⟩ := by
  decide +kernel

theorem context_12_376599_692794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376599 ⟨692794, by decide⟩ :=
  accepted_of_selected 12 376599 ⟨692794, by decide⟩ ⟨12, 1, 0, 692794, 376599, 1, 65536⟩
    (by decide) selected_cut_48543

theorem unmarked_context_11_94149_1362463 : frontier 10 ⟨1362463, by decide⟩
    (prefixCache 11 94149) (prefixPartial 11 94149) = false := by
  decide +kernel

theorem node_context_11_94149_1362463 : EJMOriginalGlobalDAGData.nodes 10 ⟨1362463, by decide⟩ =
    .split (coordinate 11) (![⟨1362406, by decide⟩,⟨1172003, by decide⟩,⟨1362462, by decide⟩,⟨692794, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_94149_1362463 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94149 ⟨1362463, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 94149
    ⟨1362463, by decide⟩ (by decide) (![⟨1362406, by decide⟩,⟨1172003, by decide⟩,⟨1362462, by decide⟩,⟨692794, by decide⟩]) unmarked_context_11_94149_1362463 node_context_11_94149_1362463
  intro a
  fin_cases a
  · exact context_12_376596_1362406
  · exact context_12_376597_1172003
  · exact context_12_376598_1362462
  · exact context_12_376599_692794

theorem selected_cut_48544 : selected 9 ⟨1066629, by decide⟩
    (prefixPartial 12 376600) = some ⟨12, 1, 0, 1066629, 376600, 1, 65536⟩ := by
  decide +kernel

theorem context_12_376600_1066629 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376600 ⟨1066629, by decide⟩ :=
  accepted_of_selected 12 376600 ⟨1066629, by decide⟩ ⟨12, 1, 0, 1066629, 376600, 1, 65536⟩
    (by decide) selected_cut_48544

theorem selected_cut_48545 : selected 9 ⟨1362512, by decide⟩
    (prefixPartial 12 376601) = some ⟨12, 2, 0, 1362512, 376601, 2745, 65536⟩ := by
  decide +kernel

theorem context_12_376601_1362512 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376601 ⟨1362512, by decide⟩ :=
  accepted_of_selected 12 376601 ⟨1362512, by decide⟩ ⟨12, 2, 0, 1362512, 376601, 2745, 65536⟩
    (by decide) selected_cut_48545

theorem selected_cut_48546 : selected 9 ⟨1362555, by decide⟩
    (prefixPartial 12 376602) = some ⟨12, 2, 0, 1362555, 376602, 2669, 65536⟩ := by
  decide +kernel

theorem context_12_376602_1362555 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376602 ⟨1362555, by decide⟩ :=
  accepted_of_selected 12 376602 ⟨1362555, by decide⟩ ⟨12, 2, 0, 1362555, 376602, 2669, 65536⟩
    (by decide) selected_cut_48546

theorem selected_cut_48547 : selected 9 ⟨1362603, by decide⟩
    (prefixPartial 12 376603) = some ⟨12, 2, 0, 1362603, 376603, 2725, 65536⟩ := by
  decide +kernel

theorem context_12_376603_1362603 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376603 ⟨1362603, by decide⟩ :=
  accepted_of_selected 12 376603 ⟨1362603, by decide⟩ ⟨12, 2, 0, 1362603, 376603, 2725, 65536⟩
    (by decide) selected_cut_48547

theorem unmarked_context_11_94150_1362604 : frontier 10 ⟨1362604, by decide⟩
    (prefixCache 11 94150) (prefixPartial 11 94150) = false := by
  decide +kernel

theorem node_context_11_94150_1362604 : EJMOriginalGlobalDAGData.nodes 10 ⟨1362604, by decide⟩ =
    .split (coordinate 11) (![⟨1066629, by decide⟩,⟨1362512, by decide⟩,⟨1362555, by decide⟩,⟨1362603, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_94150_1362604 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94150 ⟨1362604, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 94150
    ⟨1362604, by decide⟩ (by decide) (![⟨1066629, by decide⟩,⟨1362512, by decide⟩,⟨1362555, by decide⟩,⟨1362603, by decide⟩]) unmarked_context_11_94150_1362604 node_context_11_94150_1362604
  intro a
  fin_cases a
  · exact context_12_376600_1066629
  · exact context_12_376601_1362512
  · exact context_12_376602_1362555
  · exact context_12_376603_1362603

theorem selected_cut_48548 : selected 9 ⟨1362646, by decide⟩
    (prefixPartial 12 376604) = some ⟨12, 2, 0, 1362646, 376604, 2397, 65536⟩ := by
  decide +kernel

theorem context_12_376604_1362646 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376604 ⟨1362646, by decide⟩ :=
  accepted_of_selected 12 376604 ⟨1362646, by decide⟩ ⟨12, 2, 0, 1362646, 376604, 2397, 65536⟩
    (by decide) selected_cut_48548

theorem selected_cut_48549 : selected 9 ⟨1362690, by decide⟩
    (prefixPartial 12 376605) = some ⟨12, 2, 0, 1362690, 376605, 2413, 65536⟩ := by
  decide +kernel

theorem context_12_376605_1362690 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376605 ⟨1362690, by decide⟩ :=
  accepted_of_selected 12 376605 ⟨1362690, by decide⟩ ⟨12, 2, 0, 1362690, 376605, 2413, 65536⟩
    (by decide) selected_cut_48549

theorem selected_cut_48550 : selected 9 ⟨1362731, by decide⟩
    (prefixPartial 12 376606) = some ⟨12, 2, 0, 1362731, 376606, 2389, 65536⟩ := by
  decide +kernel

theorem context_12_376606_1362731 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376606 ⟨1362731, by decide⟩ :=
  accepted_of_selected 12 376606 ⟨1362731, by decide⟩ ⟨12, 2, 0, 1362731, 376606, 2389, 65536⟩
    (by decide) selected_cut_48550

theorem selected_cut_48551 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 376607) = some ⟨12, 1, 0, 903806, 376607, 1, 65536⟩ := by
  decide +kernel

theorem context_12_376607_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376607 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 376607 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 376607, 1, 65536⟩
    (by decide) selected_cut_48551

theorem unmarked_context_11_94151_1362732 : frontier 10 ⟨1362732, by decide⟩
    (prefixCache 11 94151) (prefixPartial 11 94151) = false := by
  decide +kernel

theorem node_context_11_94151_1362732 : EJMOriginalGlobalDAGData.nodes 10 ⟨1362732, by decide⟩ =
    .split (coordinate 11) (![⟨1362646, by decide⟩,⟨1362690, by decide⟩,⟨1362731, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_94151_1362732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94151 ⟨1362732, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 94151
    ⟨1362732, by decide⟩ (by decide) (![⟨1362646, by decide⟩,⟨1362690, by decide⟩,⟨1362731, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_94151_1362732 node_context_11_94151_1362732
  intro a
  fin_cases a
  · exact context_12_376604_1362646
  · exact context_12_376605_1362690
  · exact context_12_376606_1362731
  · exact context_12_376607_903806

theorem unmarked_context_10_23537_1362733 : frontier 11 ⟨1362733, by decide⟩
    (prefixCache 10 23537) (prefixPartial 10 23537) = false := by
  decide +kernel

theorem node_context_10_23537_1362733 : EJMOriginalGlobalDAGData.nodes 11 ⟨1362733, by decide⟩ =
    .split (coordinate 10) (![⟨1362341, by decide⟩,⟨1362463, by decide⟩,⟨1362604, by decide⟩,⟨1362732, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23537_1362733 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23537 ⟨1362733, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23537
    ⟨1362733, by decide⟩ (by decide) (![⟨1362341, by decide⟩,⟨1362463, by decide⟩,⟨1362604, by decide⟩,⟨1362732, by decide⟩]) unmarked_context_10_23537_1362733 node_context_10_23537_1362733
  intro a
  fin_cases a
  · exact context_11_94148_1362341
  · exact context_11_94149_1362463
  · exact context_11_94150_1362604
  · exact context_11_94151_1362732

theorem selected_cut_48552 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 376608) = some ⟨12, 1, 0, 435790, 376608, 1, 65536⟩ := by
  decide +kernel

theorem context_12_376608_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376608 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 376608 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 376608, 1, 65536⟩
    (by decide) selected_cut_48552

theorem selected_cut_48553 : selected 9 ⟨1362778, by decide⟩
    (prefixPartial 12 376609) = some ⟨12, 2, 0, 1362778, 376609, 2581, 65536⟩ := by
  decide +kernel

theorem context_12_376609_1362778 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376609 ⟨1362778, by decide⟩ :=
  accepted_of_selected 12 376609 ⟨1362778, by decide⟩ ⟨12, 2, 0, 1362778, 376609, 2581, 65536⟩
    (by decide) selected_cut_48553

theorem selected_cut_48554 : selected 9 ⟨1362827, by decide⟩
    (prefixPartial 12 376610) = some ⟨12, 2, 0, 1362827, 376610, 2557, 65536⟩ := by
  decide +kernel

theorem context_12_376610_1362827 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376610 ⟨1362827, by decide⟩ :=
  accepted_of_selected 12 376610 ⟨1362827, by decide⟩ ⟨12, 2, 0, 1362827, 376610, 2557, 65536⟩
    (by decide) selected_cut_48554

theorem selected_cut_48555 : selected 9 ⟨1362860, by decide⟩
    (prefixPartial 12 376611) = some ⟨12, 2, 0, 1362860, 376611, 2397, 65536⟩ := by
  decide +kernel

theorem context_12_376611_1362860 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376611 ⟨1362860, by decide⟩ :=
  accepted_of_selected 12 376611 ⟨1362860, by decide⟩ ⟨12, 2, 0, 1362860, 376611, 2397, 65536⟩
    (by decide) selected_cut_48555

theorem unmarked_context_11_94152_1362861 : frontier 10 ⟨1362861, by decide⟩
    (prefixCache 11 94152) (prefixPartial 11 94152) = false := by
  decide +kernel

theorem node_context_11_94152_1362861 : EJMOriginalGlobalDAGData.nodes 10 ⟨1362861, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨1362778, by decide⟩,⟨1362827, by decide⟩,⟨1362860, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_94152_1362861 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94152 ⟨1362861, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 94152
    ⟨1362861, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨1362778, by decide⟩,⟨1362827, by decide⟩,⟨1362860, by decide⟩]) unmarked_context_11_94152_1362861 node_context_11_94152_1362861
  intro a
  fin_cases a
  · exact context_12_376608_435790
  · exact context_12_376609_1362778
  · exact context_12_376610_1362827
  · exact context_12_376611_1362860

theorem selected_cut_48556 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 376612) = some ⟨12, 1, 0, 435790, 376612, 1, 65536⟩ := by
  decide +kernel

theorem context_12_376612_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376612 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 376612 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 376612, 1, 65536⟩
    (by decide) selected_cut_48556

theorem selected_cut_48557 : selected 9 ⟨1362911, by decide⟩
    (prefixPartial 12 376613) = some ⟨12, 2, 0, 1362911, 376613, 2973, 65536⟩ := by
  decide +kernel

theorem context_12_376613_1362911 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376613 ⟨1362911, by decide⟩ :=
  accepted_of_selected 12 376613 ⟨1362911, by decide⟩ ⟨12, 2, 0, 1362911, 376613, 2973, 65536⟩
    (by decide) selected_cut_48557

theorem selected_cut_48558 : selected 9 ⟨1362973, by decide⟩
    (prefixPartial 12 376614) = some ⟨12, 2, 0, 1362973, 376614, 2901, 65536⟩ := by
  decide +kernel

theorem context_12_376614_1362973 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376614 ⟨1362973, by decide⟩ :=
  accepted_of_selected 12 376614 ⟨1362973, by decide⟩ ⟨12, 2, 0, 1362973, 376614, 2901, 65536⟩
    (by decide) selected_cut_48558

theorem selected_cut_48559 : selected 9 ⟨1363027, by decide⟩
    (prefixPartial 12 376615) = some ⟨12, 2, 0, 1363027, 376615, 2553, 65536⟩ := by
  decide +kernel

theorem context_12_376615_1363027 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376615 ⟨1363027, by decide⟩ :=
  accepted_of_selected 12 376615 ⟨1363027, by decide⟩ ⟨12, 2, 0, 1363027, 376615, 2553, 65536⟩
    (by decide) selected_cut_48559

theorem unmarked_context_11_94153_1363028 : frontier 10 ⟨1363028, by decide⟩
    (prefixCache 11 94153) (prefixPartial 11 94153) = false := by
  decide +kernel

theorem node_context_11_94153_1363028 : EJMOriginalGlobalDAGData.nodes 10 ⟨1363028, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨1362911, by decide⟩,⟨1362973, by decide⟩,⟨1363027, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_94153_1363028 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94153 ⟨1363028, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 94153
    ⟨1363028, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨1362911, by decide⟩,⟨1362973, by decide⟩,⟨1363027, by decide⟩]) unmarked_context_11_94153_1363028 node_context_11_94153_1363028
  intro a
  fin_cases a
  · exact context_12_376612_435790
  · exact context_12_376613_1362911
  · exact context_12_376614_1362973
  · exact context_12_376615_1363027

theorem selected_cut_48560 : selected 10 ⟨1363071, by decide⟩
    (prefixPartial 11 94154) = some ⟨11, 2, 0, 1363071, 94154, 2405, 262144⟩ := by
  decide +kernel

theorem context_11_94154_1363071 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94154 ⟨1363071, by decide⟩ :=
  accepted_of_selected 11 94154 ⟨1363071, by decide⟩ ⟨11, 2, 0, 1363071, 94154, 2405, 262144⟩
    (by decide) selected_cut_48560

theorem selected_cut_48561 : selected 9 ⟨1363103, by decide⟩
    (prefixPartial 12 376620) = some ⟨12, 2, 0, 1363103, 376620, 1289, 65536⟩ := by
  decide +kernel

theorem context_12_376620_1363103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376620 ⟨1363103, by decide⟩ :=
  accepted_of_selected 12 376620 ⟨1363103, by decide⟩ ⟨12, 2, 0, 1363103, 376620, 1289, 65536⟩
    (by decide) selected_cut_48561

theorem selected_cut_48562 : selected 9 ⟨1363141, by decide⟩
    (prefixPartial 12 376621) = some ⟨12, 2, 0, 1363141, 376621, 2353, 65536⟩ := by
  decide +kernel

theorem context_12_376621_1363141 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376621 ⟨1363141, by decide⟩ :=
  accepted_of_selected 12 376621 ⟨1363141, by decide⟩ ⟨12, 2, 0, 1363141, 376621, 2353, 65536⟩
    (by decide) selected_cut_48562

theorem selected_cut_48563 : selected 9 ⟨1363189, by decide⟩
    (prefixPartial 12 376622) = some ⟨12, 2, 0, 1363189, 376622, 2289, 65536⟩ := by
  decide +kernel

theorem context_12_376622_1363189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376622 ⟨1363189, by decide⟩ :=
  accepted_of_selected 12 376622 ⟨1363189, by decide⟩ ⟨12, 2, 0, 1363189, 376622, 2289, 65536⟩
    (by decide) selected_cut_48563

theorem selected_cut_48564 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 376623) = some ⟨12, 1, 0, 903806, 376623, 1, 65536⟩ := by
  decide +kernel

theorem context_12_376623_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376623 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 376623 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 376623, 1, 65536⟩
    (by decide) selected_cut_48564

theorem unmarked_context_11_94155_1363190 : frontier 10 ⟨1363190, by decide⟩
    (prefixCache 11 94155) (prefixPartial 11 94155) = false := by
  decide +kernel

theorem node_context_11_94155_1363190 : EJMOriginalGlobalDAGData.nodes 10 ⟨1363190, by decide⟩ =
    .split (coordinate 11) (![⟨1363103, by decide⟩,⟨1363141, by decide⟩,⟨1363189, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_94155_1363190 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94155 ⟨1363190, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 94155
    ⟨1363190, by decide⟩ (by decide) (![⟨1363103, by decide⟩,⟨1363141, by decide⟩,⟨1363189, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_94155_1363190 node_context_11_94155_1363190
  intro a
  fin_cases a
  · exact context_12_376620_1363103
  · exact context_12_376621_1363141
  · exact context_12_376622_1363189
  · exact context_12_376623_903806

theorem unmarked_context_10_23538_1363191 : frontier 11 ⟨1363191, by decide⟩
    (prefixCache 10 23538) (prefixPartial 10 23538) = false := by
  decide +kernel

theorem node_context_10_23538_1363191 : EJMOriginalGlobalDAGData.nodes 11 ⟨1363191, by decide⟩ =
    .split (coordinate 10) (![⟨1362861, by decide⟩,⟨1363028, by decide⟩,⟨1363071, by decide⟩,⟨1363190, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23538_1363191 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23538 ⟨1363191, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23538
    ⟨1363191, by decide⟩ (by decide) (![⟨1362861, by decide⟩,⟨1363028, by decide⟩,⟨1363071, by decide⟩,⟨1363190, by decide⟩]) unmarked_context_10_23538_1363191 node_context_10_23538_1363191
  intro a
  fin_cases a
  · exact context_11_94152_1362861
  · exact context_11_94153_1363028
  · exact context_11_94154_1363071
  · exact context_11_94155_1363190

theorem selected_cut_48565 : selected 9 ⟨792260, by decide⟩
    (prefixPartial 12 376624) = some ⟨12, 1, 0, 792260, 376624, 1, 65536⟩ := by
  decide +kernel

theorem context_12_376624_792260 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376624 ⟨792260, by decide⟩ :=
  accepted_of_selected 12 376624 ⟨792260, by decide⟩ ⟨12, 1, 0, 792260, 376624, 1, 65536⟩
    (by decide) selected_cut_48565

theorem selected_cut_48566 : selected 9 ⟨1363220, by decide⟩
    (prefixPartial 12 376625) = some ⟨12, 2, 0, 1363220, 376625, 1741, 65536⟩ := by
  decide +kernel

theorem context_12_376625_1363220 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376625 ⟨1363220, by decide⟩ :=
  accepted_of_selected 12 376625 ⟨1363220, by decide⟩ ⟨12, 2, 0, 1363220, 376625, 1741, 65536⟩
    (by decide) selected_cut_48566

theorem selected_cut_48567 : selected 9 ⟨1363257, by decide⟩
    (prefixPartial 12 376626) = some ⟨12, 2, 0, 1363257, 376626, 1925, 65536⟩ := by
  decide +kernel

theorem context_12_376626_1363257 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376626 ⟨1363257, by decide⟩ :=
  accepted_of_selected 12 376626 ⟨1363257, by decide⟩ ⟨12, 2, 0, 1363257, 376626, 1925, 65536⟩
    (by decide) selected_cut_48567

theorem selected_cut_48568 : selected 9 ⟨1363282, by decide⟩
    (prefixPartial 12 376627) = some ⟨12, 2, 0, 1363282, 376627, 1665, 65536⟩ := by
  decide +kernel

theorem context_12_376627_1363282 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376627 ⟨1363282, by decide⟩ :=
  accepted_of_selected 12 376627 ⟨1363282, by decide⟩ ⟨12, 2, 0, 1363282, 376627, 1665, 65536⟩
    (by decide) selected_cut_48568

theorem unmarked_context_11_94156_1363283 : frontier 10 ⟨1363283, by decide⟩
    (prefixCache 11 94156) (prefixPartial 11 94156) = false := by
  decide +kernel

theorem node_context_11_94156_1363283 : EJMOriginalGlobalDAGData.nodes 10 ⟨1363283, by decide⟩ =
    .split (coordinate 11) (![⟨792260, by decide⟩,⟨1363220, by decide⟩,⟨1363257, by decide⟩,⟨1363282, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_94156_1363283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94156 ⟨1363283, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 94156
    ⟨1363283, by decide⟩ (by decide) (![⟨792260, by decide⟩,⟨1363220, by decide⟩,⟨1363257, by decide⟩,⟨1363282, by decide⟩]) unmarked_context_11_94156_1363283 node_context_11_94156_1363283
  intro a
  fin_cases a
  · exact context_12_376624_792260
  · exact context_12_376625_1363220
  · exact context_12_376626_1363257
  · exact context_12_376627_1363282

theorem selected_cut_48569 : selected 9 ⟨1363331, by decide⟩
    (prefixPartial 12 376628) = some ⟨12, 2, 0, 1363331, 376628, 2229, 65536⟩ := by
  decide +kernel

theorem context_12_376628_1363331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376628 ⟨1363331, by decide⟩ :=
  accepted_of_selected 12 376628 ⟨1363331, by decide⟩ ⟨12, 2, 0, 1363331, 376628, 2229, 65536⟩
    (by decide) selected_cut_48569

theorem selected_cut_48570 : selected 9 ⟨689956, by decide⟩
    (prefixPartial 12 376629) = some ⟨12, 1, 0, 689956, 376629, 1, 65536⟩ := by
  decide +kernel

theorem context_12_376629_689956 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376629 ⟨689956, by decide⟩ :=
  accepted_of_selected 12 376629 ⟨689956, by decide⟩ ⟨12, 1, 0, 689956, 376629, 1, 65536⟩
    (by decide) selected_cut_48570

theorem selected_cut_48571 : selected 9 ⟨1363369, by decide⟩
    (prefixPartial 12 376630) = some ⟨12, 2, 0, 1363369, 376630, 2021, 65536⟩ := by
  decide +kernel

theorem context_12_376630_1363369 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376630 ⟨1363369, by decide⟩ :=
  accepted_of_selected 12 376630 ⟨1363369, by decide⟩ ⟨12, 2, 0, 1363369, 376630, 2021, 65536⟩
    (by decide) selected_cut_48571

theorem selected_cut_48572 : selected 9 ⟨1363402, by decide⟩
    (prefixPartial 12 376631) = some ⟨12, 2, 0, 1363402, 376631, 1709, 65536⟩ := by
  decide +kernel

theorem context_12_376631_1363402 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376631 ⟨1363402, by decide⟩ :=
  accepted_of_selected 12 376631 ⟨1363402, by decide⟩ ⟨12, 2, 0, 1363402, 376631, 1709, 65536⟩
    (by decide) selected_cut_48572

theorem unmarked_context_11_94157_1363403 : frontier 10 ⟨1363403, by decide⟩
    (prefixCache 11 94157) (prefixPartial 11 94157) = false := by
  decide +kernel

theorem node_context_11_94157_1363403 : EJMOriginalGlobalDAGData.nodes 10 ⟨1363403, by decide⟩ =
    .split (coordinate 11) (![⟨1363331, by decide⟩,⟨689956, by decide⟩,⟨1363369, by decide⟩,⟨1363402, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_94157_1363403 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94157 ⟨1363403, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 94157
    ⟨1363403, by decide⟩ (by decide) (![⟨1363331, by decide⟩,⟨689956, by decide⟩,⟨1363369, by decide⟩,⟨1363402, by decide⟩]) unmarked_context_11_94157_1363403 node_context_11_94157_1363403
  intro a
  fin_cases a
  · exact context_12_376628_1363331
  · exact context_12_376629_689956
  · exact context_12_376630_1363369
  · exact context_12_376631_1363402

theorem selected_cut_48573 : selected 10 ⟨1363461, by decide⟩
    (prefixPartial 11 94158) = some ⟨11, 2, 0, 1363461, 94158, 3181, 262144⟩ := by
  decide +kernel

theorem context_11_94158_1363461 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94158 ⟨1363461, by decide⟩ :=
  accepted_of_selected 11 94158 ⟨1363461, by decide⟩ ⟨11, 2, 0, 1363461, 94158, 3181, 262144⟩
    (by decide) selected_cut_48573

theorem selected_cut_48574 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 94159) = some ⟨11, 1, 0, 977886, 94159, 1, 262144⟩ := by
  decide +kernel

theorem context_11_94159_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94159 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 94159 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 94159, 1, 262144⟩
    (by decide) selected_cut_48574

theorem unmarked_context_10_23539_1363462 : frontier 11 ⟨1363462, by decide⟩
    (prefixCache 10 23539) (prefixPartial 10 23539) = false := by
  decide +kernel

theorem node_context_10_23539_1363462 : EJMOriginalGlobalDAGData.nodes 11 ⟨1363462, by decide⟩ =
    .split (coordinate 10) (![⟨1363283, by decide⟩,⟨1363403, by decide⟩,⟨1363461, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23539_1363462 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23539 ⟨1363462, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23539
    ⟨1363462, by decide⟩ (by decide) (![⟨1363283, by decide⟩,⟨1363403, by decide⟩,⟨1363461, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_23539_1363462 node_context_10_23539_1363462
  intro a
  fin_cases a
  · exact context_11_94156_1363283
  · exact context_11_94157_1363403
  · exact context_11_94158_1363461
  · exact context_11_94159_977886

theorem unmarked_context_9_5884_1363463 : frontier 12 ⟨1363463, by decide⟩
    (prefixCache 9 5884) (prefixPartial 9 5884) = false := by
  decide +kernel

theorem node_context_9_5884_1363463 : EJMOriginalGlobalDAGData.nodes 12 ⟨1363463, by decide⟩ =
    .split (coordinate 9) (![⟨1362192, by decide⟩,⟨1362733, by decide⟩,⟨1363191, by decide⟩,⟨1363462, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5884_1363463 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5884 ⟨1363463, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5884
    ⟨1363463, by decide⟩ (by decide) (![⟨1362192, by decide⟩,⟨1362733, by decide⟩,⟨1363191, by decide⟩,⟨1363462, by decide⟩]) unmarked_context_9_5884_1363463 node_context_9_5884_1363463
  intro a
  fin_cases a
  · exact context_10_23536_1362192
  · exact context_10_23537_1362733
  · exact context_10_23538_1363191
  · exact context_10_23539_1363462

theorem selected_cut_48575 : selected 10 ⟨1363523, by decide⟩
    (prefixPartial 11 94160) = some ⟨11, 2, 0, 1363523, 94160, 3733, 262144⟩ := by
  decide +kernel

theorem context_11_94160_1363523 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94160 ⟨1363523, by decide⟩ :=
  accepted_of_selected 11 94160 ⟨1363523, by decide⟩ ⟨11, 2, 0, 1363523, 94160, 3733, 262144⟩
    (by decide) selected_cut_48575

theorem selected_cut_48576 : selected 9 ⟨1363567, by decide⟩
    (prefixPartial 12 376644) = some ⟨12, 2, 0, 1363567, 376644, 2273, 65536⟩ := by
  decide +kernel

theorem context_12_376644_1363567 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376644 ⟨1363567, by decide⟩ :=
  accepted_of_selected 12 376644 ⟨1363567, by decide⟩ ⟨12, 2, 0, 1363567, 376644, 2273, 65536⟩
    (by decide) selected_cut_48576

theorem selected_cut_48577 : selected 9 ⟨1257136, by decide⟩
    (prefixPartial 12 376645) = some ⟨12, 1, 0, 1257136, 376645, 1, 65536⟩ := by
  decide +kernel

theorem context_12_376645_1257136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376645 ⟨1257136, by decide⟩ :=
  accepted_of_selected 12 376645 ⟨1257136, by decide⟩ ⟨12, 1, 0, 1257136, 376645, 1, 65536⟩
    (by decide) selected_cut_48577

theorem selected_cut_48578 : selected 9 ⟨1363606, by decide⟩
    (prefixPartial 12 376646) = some ⟨12, 2, 0, 1363606, 376646, 2013, 65536⟩ := by
  decide +kernel

theorem context_12_376646_1363606 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376646 ⟨1363606, by decide⟩ :=
  accepted_of_selected 12 376646 ⟨1363606, by decide⟩ ⟨12, 2, 0, 1363606, 376646, 2013, 65536⟩
    (by decide) selected_cut_48578

theorem selected_cut_48579 : selected 9 ⟨1363639, by decide⟩
    (prefixPartial 12 376647) = some ⟨12, 2, 0, 1363639, 376647, 1913, 65536⟩ := by
  decide +kernel

theorem context_12_376647_1363639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376647 ⟨1363639, by decide⟩ :=
  accepted_of_selected 12 376647 ⟨1363639, by decide⟩ ⟨12, 2, 0, 1363639, 376647, 1913, 65536⟩
    (by decide) selected_cut_48579

theorem unmarked_context_11_94161_1363640 : frontier 10 ⟨1363640, by decide⟩
    (prefixCache 11 94161) (prefixPartial 11 94161) = false := by
  decide +kernel

theorem node_context_11_94161_1363640 : EJMOriginalGlobalDAGData.nodes 10 ⟨1363640, by decide⟩ =
    .split (coordinate 11) (![⟨1363567, by decide⟩,⟨1257136, by decide⟩,⟨1363606, by decide⟩,⟨1363639, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_94161_1363640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94161 ⟨1363640, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 94161
    ⟨1363640, by decide⟩ (by decide) (![⟨1363567, by decide⟩,⟨1257136, by decide⟩,⟨1363606, by decide⟩,⟨1363639, by decide⟩]) unmarked_context_11_94161_1363640 node_context_11_94161_1363640
  intro a
  fin_cases a
  · exact context_12_376644_1363567
  · exact context_12_376645_1257136
  · exact context_12_376646_1363606
  · exact context_12_376647_1363639

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
