/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover546
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_10_72546_1533610 : frontier 11 ⟨1533610, by decide⟩
    (prefixCache 10 72546) (prefixPartial 10 72546) = false := by
  decide +kernel

theorem node_context_10_72546_1533610 : EJMOriginalGlobalDAGData.nodes 11 ⟨1533610, by decide⟩ =
    .split (coordinate 10) (![⟨1533558, by decide⟩,⟨1533582, by decide⟩,⟨1468743, by decide⟩,⟨1533609, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_72546_1533610 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72546 ⟨1533610, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 72546
    ⟨1533610, by decide⟩ (by decide) (![⟨1533558, by decide⟩,⟨1533582, by decide⟩,⟨1468743, by decide⟩,⟨1533609, by decide⟩]) unmarked_context_10_72546_1533610 node_context_10_72546_1533610
  intro a
  fin_cases a
  · exact context_11_290184_1533558
  · exact context_11_290185_1533582
  · exact context_11_290186_1468743
  · exact context_11_290187_1533609

theorem selected_cut_52516 : selected 11 ⟨1533698, by decide⟩
    (prefixPartial 10 72547) = some ⟨10, 2, 0, 1533698, 72547, 3401, 1048576⟩ := by
  decide +kernel

theorem context_10_72547_1533698 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72547 ⟨1533698, by decide⟩ :=
  accepted_of_selected 10 72547 ⟨1533698, by decide⟩ ⟨10, 2, 0, 1533698, 72547, 3401, 1048576⟩
    (by decide) selected_cut_52516

theorem unmarked_context_9_18136_1533699 : frontier 12 ⟨1533699, by decide⟩
    (prefixCache 9 18136) (prefixPartial 9 18136) = false := by
  decide +kernel

theorem node_context_9_18136_1533699 : EJMOriginalGlobalDAGData.nodes 12 ⟨1533699, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1533485, by decide⟩,⟨1533610, by decide⟩,⟨1533698, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18136_1533699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18136 ⟨1533699, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18136
    ⟨1533699, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1533485, by decide⟩,⟨1533610, by decide⟩,⟨1533698, by decide⟩]) unmarked_context_9_18136_1533699 node_context_9_18136_1533699
  intro a
  fin_cases a
  · exact context_10_72544_1468246
  · exact context_10_72545_1533485
  · exact context_10_72546_1533610
  · exact context_10_72547_1533698

theorem selected_cut_52517 : selected 11 ⟨1533754, by decide⟩
    (prefixPartial 10 72548) = some ⟨10, 2, 0, 1533754, 72548, 2369, 1048576⟩ := by
  decide +kernel

theorem context_10_72548_1533754 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72548 ⟨1533754, by decide⟩ :=
  accepted_of_selected 10 72548 ⟨1533754, by decide⟩ ⟨10, 2, 0, 1533754, 72548, 2369, 1048576⟩
    (by decide) selected_cut_52517

theorem selected_cut_52518 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 72549) = some ⟨10, 1, 0, 1468874, 72549, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_72549_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72549 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 72549 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 72549, 1, 1048576⟩
    (by decide) selected_cut_52518

theorem selected_cut_52519 : selected 11 ⟨1533842, by decide⟩
    (prefixPartial 10 72550) = some ⟨10, 2, 0, 1533842, 72550, 3661, 1048576⟩ := by
  decide +kernel

theorem context_10_72550_1533842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72550 ⟨1533842, by decide⟩ :=
  accepted_of_selected 10 72550 ⟨1533842, by decide⟩ ⟨10, 2, 0, 1533842, 72550, 3661, 1048576⟩
    (by decide) selected_cut_52519

theorem selected_cut_52520 : selected 11 ⟨1533894, by decide⟩
    (prefixPartial 10 72551) = some ⟨10, 2, 0, 1533894, 72551, 1825, 1048576⟩ := by
  decide +kernel

theorem context_10_72551_1533894 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72551 ⟨1533894, by decide⟩ :=
  accepted_of_selected 10 72551 ⟨1533894, by decide⟩ ⟨10, 2, 0, 1533894, 72551, 1825, 1048576⟩
    (by decide) selected_cut_52520

theorem unmarked_context_9_18137_1533895 : frontier 12 ⟨1533895, by decide⟩
    (prefixCache 9 18137) (prefixPartial 9 18137) = false := by
  decide +kernel

theorem node_context_9_18137_1533895 : EJMOriginalGlobalDAGData.nodes 12 ⟨1533895, by decide⟩ =
    .split (coordinate 9) (![⟨1533754, by decide⟩,⟨1468874, by decide⟩,⟨1533842, by decide⟩,⟨1533894, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18137_1533895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18137 ⟨1533895, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18137
    ⟨1533895, by decide⟩ (by decide) (![⟨1533754, by decide⟩,⟨1468874, by decide⟩,⟨1533842, by decide⟩,⟨1533894, by decide⟩]) unmarked_context_9_18137_1533895 node_context_9_18137_1533895
  intro a
  fin_cases a
  · exact context_10_72548_1533754
  · exact context_10_72549_1468874
  · exact context_10_72550_1533842
  · exact context_10_72551_1533894

theorem selected_cut_52521 : selected 12 ⟨1533959, by decide⟩
    (prefixPartial 9 18138) = some ⟨9, 2, 0, 1533959, 18138, 2141, 4194304⟩ := by
  decide +kernel

theorem context_9_18138_1533959 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18138 ⟨1533959, by decide⟩ :=
  accepted_of_selected 9 18138 ⟨1533959, by decide⟩ ⟨9, 2, 0, 1533959, 18138, 2141, 4194304⟩
    (by decide) selected_cut_52521

theorem selected_cut_52522 : selected 12 ⟨1534002, by decide⟩
    (prefixPartial 9 18139) = some ⟨9, 2, 0, 1534002, 18139, 897, 4194304⟩ := by
  decide +kernel

theorem context_9_18139_1534002 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18139 ⟨1534002, by decide⟩ :=
  accepted_of_selected 9 18139 ⟨1534002, by decide⟩ ⟨9, 2, 0, 1534002, 18139, 897, 4194304⟩
    (by decide) selected_cut_52522

theorem unmarked_context_8_4534_1534003 : frontier 13 ⟨1534003, by decide⟩
    (prefixCache 8 4534) (prefixPartial 8 4534) = false := by
  decide +kernel

theorem node_context_8_4534_1534003 : EJMOriginalGlobalDAGData.nodes 13 ⟨1534003, by decide⟩ =
    .split (coordinate 8) (![⟨1533699, by decide⟩,⟨1533895, by decide⟩,⟨1533959, by decide⟩,⟨1534002, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4534_1534003 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4534 ⟨1534003, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4534
    ⟨1534003, by decide⟩ (by decide) (![⟨1533699, by decide⟩,⟨1533895, by decide⟩,⟨1533959, by decide⟩,⟨1534002, by decide⟩]) unmarked_context_8_4534_1534003 node_context_8_4534_1534003
  intro a
  fin_cases a
  · exact context_9_18136_1533699
  · exact context_9_18137_1533895
  · exact context_9_18138_1533959
  · exact context_9_18139_1534002

theorem selected_cut_52523 : selected 13 ⟨1534004, by decide⟩
    (prefixPartial 8 4535) = some ⟨8, 1, 0, 1534004, 4535, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_4535_1534004 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4535 ⟨1534004, by decide⟩ :=
  accepted_of_selected 8 4535 ⟨1534004, by decide⟩ ⟨8, 1, 0, 1534004, 4535, 1, 16777216⟩
    (by decide) selected_cut_52523

theorem unmarked_context_7_1133_1534005 : frontier 14 ⟨1534005, by decide⟩
    (prefixCache 7 1133) (prefixPartial 7 1133) = false := by
  decide +kernel

theorem node_context_7_1133_1534005 : EJMOriginalGlobalDAGData.nodes 14 ⟨1534005, by decide⟩ =
    .split (coordinate 7) (![⟨1532732, by decide⟩,⟨1533353, by decide⟩,⟨1534003, by decide⟩,⟨1534004, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_1133_1534005 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 1133 ⟨1534005, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 1133
    ⟨1534005, by decide⟩ (by decide) (![⟨1532732, by decide⟩,⟨1533353, by decide⟩,⟨1534003, by decide⟩,⟨1534004, by decide⟩]) unmarked_context_7_1133_1534005 node_context_7_1133_1534005
  intro a
  fin_cases a
  · exact context_8_4532_1532732
  · exact context_8_4533_1533353
  · exact context_8_4534_1534003
  · exact context_8_4535_1534004

theorem selected_cut_52524 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 72576) = some ⟨10, 1, 0, 1468246, 72576, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_72576_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72576 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 72576 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 72576, 1, 1048576⟩
    (by decide) selected_cut_52524

theorem selected_cut_52525 : selected 10 ⟨1534050, by decide⟩
    (prefixPartial 11 290308) = some ⟨11, 2, 0, 1534050, 290308, 1193, 262144⟩ := by
  decide +kernel

theorem context_11_290308_1534050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 290308 ⟨1534050, by decide⟩ :=
  accepted_of_selected 11 290308 ⟨1534050, by decide⟩ ⟨11, 2, 0, 1534050, 290308, 1193, 262144⟩
    (by decide) selected_cut_52525

theorem selected_cut_52526 : selected 10 ⟨1468419, by decide⟩
    (prefixPartial 11 290309) = some ⟨11, 1, 0, 1468419, 290309, 1, 262144⟩ := by
  decide +kernel

theorem context_11_290309_1468419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 290309 ⟨1468419, by decide⟩ :=
  accepted_of_selected 11 290309 ⟨1468419, by decide⟩ ⟨11, 1, 0, 1468419, 290309, 1, 262144⟩
    (by decide) selected_cut_52526

theorem selected_cut_52527 : selected 10 ⟨1534083, by decide⟩
    (prefixPartial 11 290310) = some ⟨11, 2, 0, 1534083, 290310, 1105, 262144⟩ := by
  decide +kernel

theorem context_11_290310_1534083 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 290310 ⟨1534083, by decide⟩ :=
  accepted_of_selected 11 290310 ⟨1534083, by decide⟩ ⟨11, 2, 0, 1534083, 290310, 1105, 262144⟩
    (by decide) selected_cut_52527

theorem selected_cut_52528 : selected 10 ⟨1534182, by decide⟩
    (prefixPartial 11 290311) = some ⟨11, 2, 0, 1534182, 290311, 2441, 262144⟩ := by
  decide +kernel

theorem context_11_290311_1534182 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 290311 ⟨1534182, by decide⟩ :=
  accepted_of_selected 11 290311 ⟨1534182, by decide⟩ ⟨11, 2, 0, 1534182, 290311, 2441, 262144⟩
    (by decide) selected_cut_52528

theorem unmarked_context_10_72577_1534183 : frontier 11 ⟨1534183, by decide⟩
    (prefixCache 10 72577) (prefixPartial 10 72577) = false := by
  decide +kernel

theorem node_context_10_72577_1534183 : EJMOriginalGlobalDAGData.nodes 11 ⟨1534183, by decide⟩ =
    .split (coordinate 10) (![⟨1534050, by decide⟩,⟨1468419, by decide⟩,⟨1534083, by decide⟩,⟨1534182, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_72577_1534183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72577 ⟨1534183, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 72577
    ⟨1534183, by decide⟩ (by decide) (![⟨1534050, by decide⟩,⟨1468419, by decide⟩,⟨1534083, by decide⟩,⟨1534182, by decide⟩]) unmarked_context_10_72577_1534183 node_context_10_72577_1534183
  intro a
  fin_cases a
  · exact context_11_290308_1534050
  · exact context_11_290309_1468419
  · exact context_11_290310_1534083
  · exact context_11_290311_1534182

theorem selected_cut_52529 : selected 11 ⟨1534239, by decide⟩
    (prefixPartial 10 72578) = some ⟨10, 2, 0, 1534239, 72578, 1793, 1048576⟩ := by
  decide +kernel

theorem context_10_72578_1534239 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72578 ⟨1534239, by decide⟩ :=
  accepted_of_selected 10 72578 ⟨1534239, by decide⟩ ⟨10, 2, 0, 1534239, 72578, 1793, 1048576⟩
    (by decide) selected_cut_52529

theorem selected_cut_52530 : selected 11 ⟨1534331, by decide⟩
    (prefixPartial 10 72579) = some ⟨10, 2, 0, 1534331, 72579, 2813, 1048576⟩ := by
  decide +kernel

theorem context_10_72579_1534331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72579 ⟨1534331, by decide⟩ :=
  accepted_of_selected 10 72579 ⟨1534331, by decide⟩ ⟨10, 2, 0, 1534331, 72579, 2813, 1048576⟩
    (by decide) selected_cut_52530

theorem unmarked_context_9_18144_1534332 : frontier 12 ⟨1534332, by decide⟩
    (prefixCache 9 18144) (prefixPartial 9 18144) = false := by
  decide +kernel

theorem node_context_9_18144_1534332 : EJMOriginalGlobalDAGData.nodes 12 ⟨1534332, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1534183, by decide⟩,⟨1534239, by decide⟩,⟨1534331, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18144_1534332 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18144 ⟨1534332, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18144
    ⟨1534332, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1534183, by decide⟩,⟨1534239, by decide⟩,⟨1534331, by decide⟩]) unmarked_context_9_18144_1534332 node_context_9_18144_1534332
  intro a
  fin_cases a
  · exact context_10_72576_1468246
  · exact context_10_72577_1534183
  · exact context_10_72578_1534239
  · exact context_10_72579_1534331

theorem selected_cut_52531 : selected 11 ⟨1534425, by decide⟩
    (prefixPartial 10 72580) = some ⟨10, 2, 0, 1534425, 72580, 2061, 1048576⟩ := by
  decide +kernel

theorem context_10_72580_1534425 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72580 ⟨1534425, by decide⟩ :=
  accepted_of_selected 10 72580 ⟨1534425, by decide⟩ ⟨10, 2, 0, 1534425, 72580, 2061, 1048576⟩
    (by decide) selected_cut_52531

theorem selected_cut_52532 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 72581) = some ⟨10, 1, 0, 1468874, 72581, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_72581_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72581 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 72581 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 72581, 1, 1048576⟩
    (by decide) selected_cut_52532

theorem selected_cut_52533 : selected 11 ⟨1534532, by decide⟩
    (prefixPartial 10 72582) = some ⟨10, 2, 0, 1534532, 72582, 1901, 1048576⟩ := by
  decide +kernel

theorem context_10_72582_1534532 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72582 ⟨1534532, by decide⟩ :=
  accepted_of_selected 10 72582 ⟨1534532, by decide⟩ ⟨10, 2, 0, 1534532, 72582, 1901, 1048576⟩
    (by decide) selected_cut_52533

theorem selected_cut_52534 : selected 11 ⟨1534604, by decide⟩
    (prefixPartial 10 72583) = some ⟨10, 2, 0, 1534604, 72583, 1617, 1048576⟩ := by
  decide +kernel

theorem context_10_72583_1534604 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72583 ⟨1534604, by decide⟩ :=
  accepted_of_selected 10 72583 ⟨1534604, by decide⟩ ⟨10, 2, 0, 1534604, 72583, 1617, 1048576⟩
    (by decide) selected_cut_52534

theorem unmarked_context_9_18145_1534605 : frontier 12 ⟨1534605, by decide⟩
    (prefixCache 9 18145) (prefixPartial 9 18145) = false := by
  decide +kernel

theorem node_context_9_18145_1534605 : EJMOriginalGlobalDAGData.nodes 12 ⟨1534605, by decide⟩ =
    .split (coordinate 9) (![⟨1534425, by decide⟩,⟨1468874, by decide⟩,⟨1534532, by decide⟩,⟨1534604, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18145_1534605 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18145 ⟨1534605, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18145
    ⟨1534605, by decide⟩ (by decide) (![⟨1534425, by decide⟩,⟨1468874, by decide⟩,⟨1534532, by decide⟩,⟨1534604, by decide⟩]) unmarked_context_9_18145_1534605 node_context_9_18145_1534605
  intro a
  fin_cases a
  · exact context_10_72580_1534425
  · exact context_10_72581_1468874
  · exact context_10_72582_1534532
  · exact context_10_72583_1534604

theorem selected_cut_52535 : selected 12 ⟨1534715, by decide⟩
    (prefixPartial 9 18146) = some ⟨9, 2, 0, 1534715, 18146, 2525, 4194304⟩ := by
  decide +kernel

theorem context_9_18146_1534715 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18146 ⟨1534715, by decide⟩ :=
  accepted_of_selected 9 18146 ⟨1534715, by decide⟩ ⟨9, 2, 0, 1534715, 18146, 2525, 4194304⟩
    (by decide) selected_cut_52535

theorem selected_cut_52536 : selected 12 ⟨1534816, by decide⟩
    (prefixPartial 9 18147) = some ⟨9, 2, 0, 1534816, 18147, 1253, 4194304⟩ := by
  decide +kernel

theorem context_9_18147_1534816 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18147 ⟨1534816, by decide⟩ :=
  accepted_of_selected 9 18147 ⟨1534816, by decide⟩ ⟨9, 2, 0, 1534816, 18147, 1253, 4194304⟩
    (by decide) selected_cut_52536

theorem unmarked_context_8_4536_1534817 : frontier 13 ⟨1534817, by decide⟩
    (prefixCache 8 4536) (prefixPartial 8 4536) = false := by
  decide +kernel

theorem node_context_8_4536_1534817 : EJMOriginalGlobalDAGData.nodes 13 ⟨1534817, by decide⟩ =
    .split (coordinate 8) (![⟨1534332, by decide⟩,⟨1534605, by decide⟩,⟨1534715, by decide⟩,⟨1534816, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4536_1534817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4536 ⟨1534817, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4536
    ⟨1534817, by decide⟩ (by decide) (![⟨1534332, by decide⟩,⟨1534605, by decide⟩,⟨1534715, by decide⟩,⟨1534816, by decide⟩]) unmarked_context_8_4536_1534817 node_context_8_4536_1534817
  intro a
  fin_cases a
  · exact context_9_18144_1534332
  · exact context_9_18145_1534605
  · exact context_9_18146_1534715
  · exact context_9_18147_1534816

theorem selected_cut_52537 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 72592) = some ⟨10, 1, 0, 1468246, 72592, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_72592_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72592 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 72592 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 72592, 1, 1048576⟩
    (by decide) selected_cut_52537

theorem selected_cut_52538 : selected 11 ⟨1534949, by decide⟩
    (prefixPartial 10 72593) = some ⟨10, 2, 0, 1534949, 72593, 3961, 1048576⟩ := by
  decide +kernel

theorem context_10_72593_1534949 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72593 ⟨1534949, by decide⟩ :=
  accepted_of_selected 10 72593 ⟨1534949, by decide⟩ ⟨10, 2, 0, 1534949, 72593, 3961, 1048576⟩
    (by decide) selected_cut_52538

theorem selected_cut_52539 : selected 11 ⟨1534991, by decide⟩
    (prefixPartial 10 72594) = some ⟨10, 2, 0, 1534991, 72594, 1565, 1048576⟩ := by
  decide +kernel

theorem context_10_72594_1534991 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72594 ⟨1534991, by decide⟩ :=
  accepted_of_selected 10 72594 ⟨1534991, by decide⟩ ⟨10, 2, 0, 1534991, 72594, 1565, 1048576⟩
    (by decide) selected_cut_52539

theorem selected_cut_52540 : selected 11 ⟨1535081, by decide⟩
    (prefixPartial 10 72595) = some ⟨10, 2, 0, 1535081, 72595, 2461, 1048576⟩ := by
  decide +kernel

theorem context_10_72595_1535081 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72595 ⟨1535081, by decide⟩ :=
  accepted_of_selected 10 72595 ⟨1535081, by decide⟩ ⟨10, 2, 0, 1535081, 72595, 2461, 1048576⟩
    (by decide) selected_cut_52540

theorem unmarked_context_9_18148_1535082 : frontier 12 ⟨1535082, by decide⟩
    (prefixCache 9 18148) (prefixPartial 9 18148) = false := by
  decide +kernel

theorem node_context_9_18148_1535082 : EJMOriginalGlobalDAGData.nodes 12 ⟨1535082, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1534949, by decide⟩,⟨1534991, by decide⟩,⟨1535081, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18148_1535082 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18148 ⟨1535082, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18148
    ⟨1535082, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1534949, by decide⟩,⟨1534991, by decide⟩,⟨1535081, by decide⟩]) unmarked_context_9_18148_1535082 node_context_9_18148_1535082
  intro a
  fin_cases a
  · exact context_10_72592_1468246
  · exact context_10_72593_1534949
  · exact context_10_72594_1534991
  · exact context_10_72595_1535081

theorem selected_cut_52541 : selected 11 ⟨1535141, by decide⟩
    (prefixPartial 10 72596) = some ⟨10, 2, 0, 1535141, 72596, 1981, 1048576⟩ := by
  decide +kernel

theorem context_10_72596_1535141 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72596 ⟨1535141, by decide⟩ :=
  accepted_of_selected 10 72596 ⟨1535141, by decide⟩ ⟨10, 2, 0, 1535141, 72596, 1981, 1048576⟩
    (by decide) selected_cut_52541

theorem selected_cut_52542 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 72597) = some ⟨10, 1, 0, 1468874, 72597, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_72597_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72597 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 72597 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 72597, 1, 1048576⟩
    (by decide) selected_cut_52542

theorem selected_cut_52543 : selected 11 ⟨1535201, by decide⟩
    (prefixPartial 10 72598) = some ⟨10, 2, 0, 1535201, 72598, 2229, 1048576⟩ := by
  decide +kernel

theorem context_10_72598_1535201 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72598 ⟨1535201, by decide⟩ :=
  accepted_of_selected 10 72598 ⟨1535201, by decide⟩ ⟨10, 2, 0, 1535201, 72598, 2229, 1048576⟩
    (by decide) selected_cut_52543

theorem selected_cut_52544 : selected 11 ⟨1535253, by decide⟩
    (prefixPartial 10 72599) = some ⟨10, 2, 0, 1535253, 72599, 1697, 1048576⟩ := by
  decide +kernel

theorem context_10_72599_1535253 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72599 ⟨1535253, by decide⟩ :=
  accepted_of_selected 10 72599 ⟨1535253, by decide⟩ ⟨10, 2, 0, 1535253, 72599, 1697, 1048576⟩
    (by decide) selected_cut_52544

theorem unmarked_context_9_18149_1535254 : frontier 12 ⟨1535254, by decide⟩
    (prefixCache 9 18149) (prefixPartial 9 18149) = false := by
  decide +kernel

theorem node_context_9_18149_1535254 : EJMOriginalGlobalDAGData.nodes 12 ⟨1535254, by decide⟩ =
    .split (coordinate 9) (![⟨1535141, by decide⟩,⟨1468874, by decide⟩,⟨1535201, by decide⟩,⟨1535253, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18149_1535254 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18149 ⟨1535254, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18149
    ⟨1535254, by decide⟩ (by decide) (![⟨1535141, by decide⟩,⟨1468874, by decide⟩,⟨1535201, by decide⟩,⟨1535253, by decide⟩]) unmarked_context_9_18149_1535254 node_context_9_18149_1535254
  intro a
  fin_cases a
  · exact context_10_72596_1535141
  · exact context_10_72597_1468874
  · exact context_10_72598_1535201
  · exact context_10_72599_1535253

theorem selected_cut_52545 : selected 12 ⟨1535317, by decide⟩
    (prefixPartial 9 18150) = some ⟨9, 2, 0, 1535317, 18150, 2321, 4194304⟩ := by
  decide +kernel

theorem context_9_18150_1535317 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18150 ⟨1535317, by decide⟩ :=
  accepted_of_selected 9 18150 ⟨1535317, by decide⟩ ⟨9, 2, 0, 1535317, 18150, 2321, 4194304⟩
    (by decide) selected_cut_52545

theorem selected_cut_52546 : selected 12 ⟨1535384, by decide⟩
    (prefixPartial 9 18151) = some ⟨9, 2, 0, 1535384, 18151, 1081, 4194304⟩ := by
  decide +kernel

theorem context_9_18151_1535384 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18151 ⟨1535384, by decide⟩ :=
  accepted_of_selected 9 18151 ⟨1535384, by decide⟩ ⟨9, 2, 0, 1535384, 18151, 1081, 4194304⟩
    (by decide) selected_cut_52546

theorem unmarked_context_8_4537_1535385 : frontier 13 ⟨1535385, by decide⟩
    (prefixCache 8 4537) (prefixPartial 8 4537) = false := by
  decide +kernel

theorem node_context_8_4537_1535385 : EJMOriginalGlobalDAGData.nodes 13 ⟨1535385, by decide⟩ =
    .split (coordinate 8) (![⟨1535082, by decide⟩,⟨1535254, by decide⟩,⟨1535317, by decide⟩,⟨1535384, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4537_1535385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4537 ⟨1535385, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4537
    ⟨1535385, by decide⟩ (by decide) (![⟨1535082, by decide⟩,⟨1535254, by decide⟩,⟨1535317, by decide⟩,⟨1535384, by decide⟩]) unmarked_context_8_4537_1535385 node_context_8_4537_1535385
  intro a
  fin_cases a
  · exact context_9_18148_1535082
  · exact context_9_18149_1535254
  · exact context_9_18150_1535317
  · exact context_9_18151_1535384

theorem selected_cut_52547 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 72608) = some ⟨10, 1, 0, 1468246, 72608, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_72608_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72608 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 72608 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 72608, 1, 1048576⟩
    (by decide) selected_cut_52547

theorem selected_cut_52548 : selected 10 ⟨1535434, by decide⟩
    (prefixPartial 11 290436) = some ⟨11, 2, 0, 1535434, 290436, 1497, 262144⟩ := by
  decide +kernel

theorem context_11_290436_1535434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 290436 ⟨1535434, by decide⟩ :=
  accepted_of_selected 11 290436 ⟨1535434, by decide⟩ ⟨11, 2, 0, 1535434, 290436, 1497, 262144⟩
    (by decide) selected_cut_52548

theorem selected_cut_52549 : selected 10 ⟨1468419, by decide⟩
    (prefixPartial 11 290437) = some ⟨11, 1, 0, 1468419, 290437, 1, 262144⟩ := by
  decide +kernel

theorem context_11_290437_1468419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 290437 ⟨1468419, by decide⟩ :=
  accepted_of_selected 11 290437 ⟨1468419, by decide⟩ ⟨11, 1, 0, 1468419, 290437, 1, 262144⟩
    (by decide) selected_cut_52549

theorem selected_cut_52550 : selected 10 ⟨1535473, by decide⟩
    (prefixPartial 11 290438) = some ⟨11, 2, 0, 1535473, 290438, 1217, 262144⟩ := by
  decide +kernel

theorem context_11_290438_1535473 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 290438 ⟨1535473, by decide⟩ :=
  accepted_of_selected 11 290438 ⟨1535473, by decide⟩ ⟨11, 2, 0, 1535473, 290438, 1217, 262144⟩
    (by decide) selected_cut_52550

theorem selected_cut_52551 : selected 10 ⟨1535575, by decide⟩
    (prefixPartial 11 290439) = some ⟨11, 2, 0, 1535575, 290439, 2677, 262144⟩ := by
  decide +kernel

theorem context_11_290439_1535575 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 290439 ⟨1535575, by decide⟩ :=
  accepted_of_selected 11 290439 ⟨1535575, by decide⟩ ⟨11, 2, 0, 1535575, 290439, 2677, 262144⟩
    (by decide) selected_cut_52551

theorem unmarked_context_10_72609_1535576 : frontier 11 ⟨1535576, by decide⟩
    (prefixCache 10 72609) (prefixPartial 10 72609) = false := by
  decide +kernel

theorem node_context_10_72609_1535576 : EJMOriginalGlobalDAGData.nodes 11 ⟨1535576, by decide⟩ =
    .split (coordinate 10) (![⟨1535434, by decide⟩,⟨1468419, by decide⟩,⟨1535473, by decide⟩,⟨1535575, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_72609_1535576 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72609 ⟨1535576, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 72609
    ⟨1535576, by decide⟩ (by decide) (![⟨1535434, by decide⟩,⟨1468419, by decide⟩,⟨1535473, by decide⟩,⟨1535575, by decide⟩]) unmarked_context_10_72609_1535576 node_context_10_72609_1535576
  intro a
  fin_cases a
  · exact context_11_290436_1535434
  · exact context_11_290437_1468419
  · exact context_11_290438_1535473
  · exact context_11_290439_1535575

theorem selected_cut_52552 : selected 11 ⟨1535626, by decide⟩
    (prefixPartial 10 72610) = some ⟨10, 2, 0, 1535626, 72610, 1785, 1048576⟩ := by
  decide +kernel

theorem context_10_72610_1535626 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72610 ⟨1535626, by decide⟩ :=
  accepted_of_selected 10 72610 ⟨1535626, by decide⟩ ⟨10, 2, 0, 1535626, 72610, 1785, 1048576⟩
    (by decide) selected_cut_52552

theorem selected_cut_52553 : selected 11 ⟨1535719, by decide⟩
    (prefixPartial 10 72611) = some ⟨10, 2, 0, 1535719, 72611, 2997, 1048576⟩ := by
  decide +kernel

theorem context_10_72611_1535719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72611 ⟨1535719, by decide⟩ :=
  accepted_of_selected 10 72611 ⟨1535719, by decide⟩ ⟨10, 2, 0, 1535719, 72611, 2997, 1048576⟩
    (by decide) selected_cut_52553

theorem unmarked_context_9_18152_1535720 : frontier 12 ⟨1535720, by decide⟩
    (prefixCache 9 18152) (prefixPartial 9 18152) = false := by
  decide +kernel

theorem node_context_9_18152_1535720 : EJMOriginalGlobalDAGData.nodes 12 ⟨1535720, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1535576, by decide⟩,⟨1535626, by decide⟩,⟨1535719, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18152_1535720 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18152 ⟨1535720, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18152
    ⟨1535720, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1535576, by decide⟩,⟨1535626, by decide⟩,⟨1535719, by decide⟩]) unmarked_context_9_18152_1535720 node_context_9_18152_1535720
  intro a
  fin_cases a
  · exact context_10_72608_1468246
  · exact context_10_72609_1535576
  · exact context_10_72610_1535626
  · exact context_10_72611_1535719

theorem selected_cut_52554 : selected 11 ⟨1535790, by decide⟩
    (prefixPartial 10 72612) = some ⟨10, 2, 0, 1535790, 72612, 2489, 1048576⟩ := by
  decide +kernel

theorem context_10_72612_1535790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72612 ⟨1535790, by decide⟩ :=
  accepted_of_selected 10 72612 ⟨1535790, by decide⟩ ⟨10, 2, 0, 1535790, 72612, 2489, 1048576⟩
    (by decide) selected_cut_52554

theorem selected_cut_52555 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 72613) = some ⟨10, 1, 0, 1468874, 72613, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_72613_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72613 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 72613 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 72613, 1, 1048576⟩
    (by decide) selected_cut_52555

theorem selected_cut_52556 : selected 11 ⟨1535854, by decide⟩
    (prefixPartial 10 72614) = some ⟨10, 2, 0, 1535854, 72614, 2457, 1048576⟩ := by
  decide +kernel

theorem context_10_72614_1535854 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72614 ⟨1535854, by decide⟩ :=
  accepted_of_selected 10 72614 ⟨1535854, by decide⟩ ⟨10, 2, 0, 1535854, 72614, 2457, 1048576⟩
    (by decide) selected_cut_52556

theorem selected_cut_52557 : selected 11 ⟨1535918, by decide⟩
    (prefixPartial 10 72615) = some ⟨10, 2, 0, 1535918, 72615, 2597, 1048576⟩ := by
  decide +kernel

theorem context_10_72615_1535918 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72615 ⟨1535918, by decide⟩ :=
  accepted_of_selected 10 72615 ⟨1535918, by decide⟩ ⟨10, 2, 0, 1535918, 72615, 2597, 1048576⟩
    (by decide) selected_cut_52557

theorem unmarked_context_9_18153_1535919 : frontier 12 ⟨1535919, by decide⟩
    (prefixCache 9 18153) (prefixPartial 9 18153) = false := by
  decide +kernel

theorem node_context_9_18153_1535919 : EJMOriginalGlobalDAGData.nodes 12 ⟨1535919, by decide⟩ =
    .split (coordinate 9) (![⟨1535790, by decide⟩,⟨1468874, by decide⟩,⟨1535854, by decide⟩,⟨1535918, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18153_1535919 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18153 ⟨1535919, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18153
    ⟨1535919, by decide⟩ (by decide) (![⟨1535790, by decide⟩,⟨1468874, by decide⟩,⟨1535854, by decide⟩,⟨1535918, by decide⟩]) unmarked_context_9_18153_1535919 node_context_9_18153_1535919
  intro a
  fin_cases a
  · exact context_10_72612_1535790
  · exact context_10_72613_1468874
  · exact context_10_72614_1535854
  · exact context_10_72615_1535918

theorem selected_cut_52558 : selected 12 ⟨1535996, by decide⟩
    (prefixPartial 9 18154) = some ⟨9, 2, 0, 1535996, 18154, 3229, 4194304⟩ := by
  decide +kernel

theorem context_9_18154_1535996 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18154 ⟨1535996, by decide⟩ :=
  accepted_of_selected 9 18154 ⟨1535996, by decide⟩ ⟨9, 2, 0, 1535996, 18154, 3229, 4194304⟩
    (by decide) selected_cut_52558

theorem selected_cut_52559 : selected 12 ⟨1536056, by decide⟩
    (prefixPartial 9 18155) = some ⟨9, 2, 0, 1536056, 18155, 1485, 4194304⟩ := by
  decide +kernel

theorem context_9_18155_1536056 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18155 ⟨1536056, by decide⟩ :=
  accepted_of_selected 9 18155 ⟨1536056, by decide⟩ ⟨9, 2, 0, 1536056, 18155, 1485, 4194304⟩
    (by decide) selected_cut_52559

theorem unmarked_context_8_4538_1536057 : frontier 13 ⟨1536057, by decide⟩
    (prefixCache 8 4538) (prefixPartial 8 4538) = false := by
  decide +kernel

theorem node_context_8_4538_1536057 : EJMOriginalGlobalDAGData.nodes 13 ⟨1536057, by decide⟩ =
    .split (coordinate 8) (![⟨1535720, by decide⟩,⟨1535919, by decide⟩,⟨1535996, by decide⟩,⟨1536056, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4538_1536057 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4538 ⟨1536057, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4538
    ⟨1536057, by decide⟩ (by decide) (![⟨1535720, by decide⟩,⟨1535919, by decide⟩,⟨1535996, by decide⟩,⟨1536056, by decide⟩]) unmarked_context_8_4538_1536057 node_context_8_4538_1536057
  intro a
  fin_cases a
  · exact context_9_18152_1535720
  · exact context_9_18153_1535919
  · exact context_9_18154_1535996
  · exact context_9_18155_1536056

theorem selected_cut_52560 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 72624) = some ⟨10, 1, 0, 1468246, 72624, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_72624_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72624 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 72624 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 72624, 1, 1048576⟩
    (by decide) selected_cut_52560

theorem selected_cut_52561 : selected 11 ⟨1536263, by decide⟩
    (prefixPartial 10 72625) = some ⟨10, 2, 0, 1536263, 72625, 2669, 1048576⟩ := by
  decide +kernel

theorem context_10_72625_1536263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72625 ⟨1536263, by decide⟩ :=
  accepted_of_selected 10 72625 ⟨1536263, by decide⟩ ⟨10, 2, 0, 1536263, 72625, 2669, 1048576⟩
    (by decide) selected_cut_52561

theorem selected_cut_52562 : selected 11 ⟨1536293, by decide⟩
    (prefixPartial 10 72626) = some ⟨10, 2, 0, 1536293, 72626, 617, 1048576⟩ := by
  decide +kernel

theorem context_10_72626_1536293 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72626 ⟨1536293, by decide⟩ :=
  accepted_of_selected 10 72626 ⟨1536293, by decide⟩ ⟨10, 2, 0, 1536293, 72626, 617, 1048576⟩
    (by decide) selected_cut_52562

theorem selected_cut_52563 : selected 11 ⟨1536389, by decide⟩
    (prefixPartial 10 72627) = some ⟨10, 2, 0, 1536389, 72627, 2005, 1048576⟩ := by
  decide +kernel

theorem context_10_72627_1536389 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72627 ⟨1536389, by decide⟩ :=
  accepted_of_selected 10 72627 ⟨1536389, by decide⟩ ⟨10, 2, 0, 1536389, 72627, 2005, 1048576⟩
    (by decide) selected_cut_52563

theorem unmarked_context_9_18156_1536390 : frontier 12 ⟨1536390, by decide⟩
    (prefixCache 9 18156) (prefixPartial 9 18156) = false := by
  decide +kernel

theorem node_context_9_18156_1536390 : EJMOriginalGlobalDAGData.nodes 12 ⟨1536390, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1536263, by decide⟩,⟨1536293, by decide⟩,⟨1536389, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18156_1536390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18156 ⟨1536390, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18156
    ⟨1536390, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1536263, by decide⟩,⟨1536293, by decide⟩,⟨1536389, by decide⟩]) unmarked_context_9_18156_1536390 node_context_9_18156_1536390
  intro a
  fin_cases a
  · exact context_10_72624_1468246
  · exact context_10_72625_1536263
  · exact context_10_72626_1536293
  · exact context_10_72627_1536389

theorem selected_cut_52564 : selected 12 ⟨1536591, by decide⟩
    (prefixPartial 9 18157) = some ⟨9, 2, 0, 1536591, 18157, 2601, 4194304⟩ := by
  decide +kernel

theorem context_9_18157_1536591 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18157 ⟨1536591, by decide⟩ :=
  accepted_of_selected 9 18157 ⟨1536591, by decide⟩ ⟨9, 2, 0, 1536591, 18157, 2601, 4194304⟩
    (by decide) selected_cut_52564

theorem selected_cut_52565 : selected 12 ⟨1536673, by decide⟩
    (prefixPartial 9 18158) = some ⟨9, 2, 0, 1536673, 18158, 713, 4194304⟩ := by
  decide +kernel

theorem context_9_18158_1536673 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18158 ⟨1536673, by decide⟩ :=
  accepted_of_selected 9 18158 ⟨1536673, by decide⟩ ⟨9, 2, 0, 1536673, 18158, 713, 4194304⟩
    (by decide) selected_cut_52565

theorem selected_cut_52566 : selected 12 ⟨1536704, by decide⟩
    (prefixPartial 9 18159) = some ⟨9, 2, 0, 1536704, 18159, 185, 4194304⟩ := by
  decide +kernel

theorem context_9_18159_1536704 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18159 ⟨1536704, by decide⟩ :=
  accepted_of_selected 9 18159 ⟨1536704, by decide⟩ ⟨9, 2, 0, 1536704, 18159, 185, 4194304⟩
    (by decide) selected_cut_52566

theorem unmarked_context_8_4539_1536705 : frontier 13 ⟨1536705, by decide⟩
    (prefixCache 8 4539) (prefixPartial 8 4539) = false := by
  decide +kernel

theorem node_context_8_4539_1536705 : EJMOriginalGlobalDAGData.nodes 13 ⟨1536705, by decide⟩ =
    .split (coordinate 8) (![⟨1536390, by decide⟩,⟨1536591, by decide⟩,⟨1536673, by decide⟩,⟨1536704, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4539_1536705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4539 ⟨1536705, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4539
    ⟨1536705, by decide⟩ (by decide) (![⟨1536390, by decide⟩,⟨1536591, by decide⟩,⟨1536673, by decide⟩,⟨1536704, by decide⟩]) unmarked_context_8_4539_1536705 node_context_8_4539_1536705
  intro a
  fin_cases a
  · exact context_9_18156_1536390
  · exact context_9_18157_1536591
  · exact context_9_18158_1536673
  · exact context_9_18159_1536704

theorem unmarked_context_7_1134_1536706 : frontier 14 ⟨1536706, by decide⟩
    (prefixCache 7 1134) (prefixPartial 7 1134) = false := by
  decide +kernel

theorem node_context_7_1134_1536706 : EJMOriginalGlobalDAGData.nodes 14 ⟨1536706, by decide⟩ =
    .split (coordinate 7) (![⟨1534817, by decide⟩,⟨1535385, by decide⟩,⟨1536057, by decide⟩,⟨1536705, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_1134_1536706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 1134 ⟨1536706, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 1134
    ⟨1536706, by decide⟩ (by decide) (![⟨1534817, by decide⟩,⟨1535385, by decide⟩,⟨1536057, by decide⟩,⟨1536705, by decide⟩]) unmarked_context_7_1134_1536706 node_context_7_1134_1536706
  intro a
  fin_cases a
  · exact context_8_4536_1534817
  · exact context_8_4537_1535385
  · exact context_8_4538_1536057
  · exact context_8_4539_1536705

theorem selected_cut_52567 : selected 13 ⟨1536707, by decide⟩
    (prefixPartial 8 4540) = some ⟨8, 1, 0, 1536707, 4540, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_4540_1536707 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4540 ⟨1536707, by decide⟩ :=
  accepted_of_selected 8 4540 ⟨1536707, by decide⟩ ⟨8, 1, 0, 1536707, 4540, 1, 16777216⟩
    (by decide) selected_cut_52567

theorem selected_cut_52568 : selected 13 ⟨1536708, by decide⟩
    (prefixPartial 8 4541) = some ⟨8, 1, 0, 1536708, 4541, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_4541_1536708 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4541 ⟨1536708, by decide⟩ :=
  accepted_of_selected 8 4541 ⟨1536708, by decide⟩ ⟨8, 1, 0, 1536708, 4541, 1, 16777216⟩
    (by decide) selected_cut_52568

theorem selected_cut_52569 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 72672) = some ⟨10, 1, 0, 1468246, 72672, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_72672_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72672 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 72672 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 72672, 1, 1048576⟩
    (by decide) selected_cut_52569

theorem selected_cut_52570 : selected 11 ⟨1537063, by decide⟩
    (prefixPartial 10 72673) = some ⟨10, 2, 0, 1537063, 72673, 4033, 1048576⟩ := by
  decide +kernel

theorem context_10_72673_1537063 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72673 ⟨1537063, by decide⟩ :=
  accepted_of_selected 10 72673 ⟨1537063, by decide⟩ ⟨10, 2, 0, 1537063, 72673, 4033, 1048576⟩
    (by decide) selected_cut_52570

theorem selected_cut_52571 : selected 11 ⟨1537251, by decide⟩
    (prefixPartial 10 72674) = some ⟨10, 2, 0, 1537251, 72674, 3161, 1048576⟩ := by
  decide +kernel

theorem context_10_72674_1537251 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72674 ⟨1537251, by decide⟩ :=
  accepted_of_selected 10 72674 ⟨1537251, by decide⟩ ⟨10, 2, 0, 1537251, 72674, 3161, 1048576⟩
    (by decide) selected_cut_52571

theorem selected_cut_52572 : selected 11 ⟨1537304, by decide⟩
    (prefixPartial 10 72675) = some ⟨10, 2, 0, 1537304, 72675, 1173, 1048576⟩ := by
  decide +kernel

theorem context_10_72675_1537304 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 72675 ⟨1537304, by decide⟩ :=
  accepted_of_selected 10 72675 ⟨1537304, by decide⟩ ⟨10, 2, 0, 1537304, 72675, 1173, 1048576⟩
    (by decide) selected_cut_52572

theorem unmarked_context_9_18168_1537305 : frontier 12 ⟨1537305, by decide⟩
    (prefixCache 9 18168) (prefixPartial 9 18168) = false := by
  decide +kernel

theorem node_context_9_18168_1537305 : EJMOriginalGlobalDAGData.nodes 12 ⟨1537305, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1537063, by decide⟩,⟨1537251, by decide⟩,⟨1537304, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18168_1537305 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18168 ⟨1537305, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18168
    ⟨1537305, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1537063, by decide⟩,⟨1537251, by decide⟩,⟨1537304, by decide⟩]) unmarked_context_9_18168_1537305 node_context_9_18168_1537305
  intro a
  fin_cases a
  · exact context_10_72672_1468246
  · exact context_10_72673_1537063
  · exact context_10_72674_1537251
  · exact context_10_72675_1537304

theorem selected_cut_52573 : selected 12 ⟨1537545, by decide⟩
    (prefixPartial 9 18169) = some ⟨9, 2, 0, 1537545, 18169, 2873, 4194304⟩ := by
  decide +kernel

theorem context_9_18169_1537545 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18169 ⟨1537545, by decide⟩ :=
  accepted_of_selected 9 18169 ⟨1537545, by decide⟩ ⟨9, 2, 0, 1537545, 18169, 2873, 4194304⟩
    (by decide) selected_cut_52573

theorem selected_cut_52574 : selected 12 ⟨1537629, by decide⟩
    (prefixPartial 9 18170) = some ⟨9, 2, 0, 1537629, 18170, 577, 4194304⟩ := by
  decide +kernel

theorem context_9_18170_1537629 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18170 ⟨1537629, by decide⟩ :=
  accepted_of_selected 9 18170 ⟨1537629, by decide⟩ ⟨9, 2, 0, 1537629, 18170, 577, 4194304⟩
    (by decide) selected_cut_52574

theorem selected_cut_52575 : selected 12 ⟨1537651, by decide⟩
    (prefixPartial 9 18171) = some ⟨9, 2, 0, 1537651, 18171, 189, 4194304⟩ := by
  decide +kernel

theorem context_9_18171_1537651 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18171 ⟨1537651, by decide⟩ :=
  accepted_of_selected 9 18171 ⟨1537651, by decide⟩ ⟨9, 2, 0, 1537651, 18171, 189, 4194304⟩
    (by decide) selected_cut_52575

theorem unmarked_context_8_4542_1537652 : frontier 13 ⟨1537652, by decide⟩
    (prefixCache 8 4542) (prefixPartial 8 4542) = false := by
  decide +kernel

theorem node_context_8_4542_1537652 : EJMOriginalGlobalDAGData.nodes 13 ⟨1537652, by decide⟩ =
    .split (coordinate 8) (![⟨1537305, by decide⟩,⟨1537545, by decide⟩,⟨1537629, by decide⟩,⟨1537651, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4542_1537652 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4542 ⟨1537652, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4542
    ⟨1537652, by decide⟩ (by decide) (![⟨1537305, by decide⟩,⟨1537545, by decide⟩,⟨1537629, by decide⟩,⟨1537651, by decide⟩]) unmarked_context_8_4542_1537652 node_context_8_4542_1537652
  intro a
  fin_cases a
  · exact context_9_18168_1537305
  · exact context_9_18169_1537545
  · exact context_9_18170_1537629
  · exact context_9_18171_1537651

theorem selected_cut_52576 : selected 13 ⟨1536708, by decide⟩
    (prefixPartial 8 4543) = some ⟨8, 1, 0, 1536708, 4543, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_4543_1536708 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4543 ⟨1536708, by decide⟩ :=
  accepted_of_selected 8 4543 ⟨1536708, by decide⟩ ⟨8, 1, 0, 1536708, 4543, 1, 16777216⟩
    (by decide) selected_cut_52576

theorem unmarked_context_7_1135_1537653 : frontier 14 ⟨1537653, by decide⟩
    (prefixCache 7 1135) (prefixPartial 7 1135) = false := by
  decide +kernel

theorem node_context_7_1135_1537653 : EJMOriginalGlobalDAGData.nodes 14 ⟨1537653, by decide⟩ =
    .split (coordinate 7) (![⟨1536707, by decide⟩,⟨1536708, by decide⟩,⟨1537652, by decide⟩,⟨1536708, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_1135_1537653 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 1135 ⟨1537653, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 1135
    ⟨1537653, by decide⟩ (by decide) (![⟨1536707, by decide⟩,⟨1536708, by decide⟩,⟨1537652, by decide⟩,⟨1536708, by decide⟩]) unmarked_context_7_1135_1537653 node_context_7_1135_1537653
  intro a
  fin_cases a
  · exact context_8_4540_1536707
  · exact context_8_4541_1536708
  · exact context_8_4542_1537652
  · exact context_8_4543_1536708

theorem unmarked_context_6_283_1537654 : frontier 15 ⟨1537654, by decide⟩
    (prefixCache 6 283) (prefixPartial 6 283) = false := by
  decide +kernel

theorem node_context_6_283_1537654 : EJMOriginalGlobalDAGData.nodes 15 ⟨1537654, by decide⟩ =
    .split (coordinate 6) (![⟨1532097, by decide⟩,⟨1534005, by decide⟩,⟨1536706, by decide⟩,⟨1537653, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_6_283_1537654 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 283 ⟨1537654, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 6 283
    ⟨1537654, by decide⟩ (by decide) (![⟨1532097, by decide⟩,⟨1534005, by decide⟩,⟨1536706, by decide⟩,⟨1537653, by decide⟩]) unmarked_context_6_283_1537654 node_context_6_283_1537654
  intro a
  fin_cases a
  · exact context_7_1132_1532097
  · exact context_7_1133_1534005
  · exact context_7_1134_1536706
  · exact context_7_1135_1537653

theorem unmarked_context_5_70_1537655 : frontier 16 ⟨1537655, by decide⟩
    (prefixCache 5 70) (prefixPartial 5 70) = false := by
  decide +kernel

theorem node_context_5_70_1537655 : EJMOriginalGlobalDAGData.nodes 16 ⟨1537655, by decide⟩ =
    .split (coordinate 5) (![⟨1518610, by decide⟩,⟨1475984, by decide⟩,⟨1529636, by decide⟩,⟨1537654, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_5_70_1537655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 5 70 ⟨1537655, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 5 70
    ⟨1537655, by decide⟩ (by decide) (![⟨1518610, by decide⟩,⟨1475984, by decide⟩,⟨1529636, by decide⟩,⟨1537654, by decide⟩]) unmarked_context_5_70_1537655 node_context_5_70_1537655
  intro a
  fin_cases a
  · exact context_6_280_1518610
  · exact context_6_281_1475984
  · exact context_6_282_1529636
  · exact context_6_283_1537654

theorem selected_cut_52577 : selected 16 ⟨434742, by decide⟩
    (prefixPartial 5 71) = some ⟨5, 1, 0, 434742, 71, 1, 1073741824⟩ := by
  decide +kernel

theorem context_5_71_434742 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 5 71 ⟨434742, by decide⟩ :=
  accepted_of_selected 5 71 ⟨434742, by decide⟩ ⟨5, 1, 0, 434742, 71, 1, 1073741824⟩
    (by decide) selected_cut_52577

theorem unmarked_context_4_17_1537656 : frontier 17 ⟨1537656, by decide⟩
    (prefixCache 4 17) (prefixPartial 4 17) = false := by
  decide +kernel

theorem node_context_4_17_1537656 : EJMOriginalGlobalDAGData.nodes 17 ⟨1537656, by decide⟩ =
    .split (coordinate 4) (![⟨1487328, by decide⟩,⟨1507378, by decide⟩,⟨1537655, by decide⟩,⟨434742, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_4_17_1537656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 4 17 ⟨1537656, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 4 17
    ⟨1537656, by decide⟩ (by decide) (![⟨1487328, by decide⟩,⟨1507378, by decide⟩,⟨1537655, by decide⟩,⟨434742, by decide⟩]) unmarked_context_4_17_1537656 node_context_4_17_1537656
  intro a
  fin_cases a
  · exact context_5_68_1487328
  · exact context_5_69_1507378
  · exact context_5_70_1537655
  · exact context_5_71_434742

theorem selected_cut_52578 : selected 12 ⟨1537889, by decide⟩
    (prefixPartial 9 18432) = some ⟨9, 2, 0, 1537889, 18432, 3405, 4194304⟩ := by
  decide +kernel

theorem context_9_18432_1537889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18432 ⟨1537889, by decide⟩ :=
  accepted_of_selected 9 18432 ⟨1537889, by decide⟩ ⟨9, 2, 0, 1537889, 18432, 3405, 4194304⟩
    (by decide) selected_cut_52578

theorem selected_cut_52579 : selected 12 ⟨1538113, by decide⟩
    (prefixPartial 9 18433) = some ⟨9, 2, 0, 1538113, 18433, 2757, 4194304⟩ := by
  decide +kernel

theorem context_9_18433_1538113 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18433 ⟨1538113, by decide⟩ :=
  accepted_of_selected 9 18433 ⟨1538113, by decide⟩ ⟨9, 2, 0, 1538113, 18433, 2757, 4194304⟩
    (by decide) selected_cut_52579

theorem selected_cut_52580 : selected 12 ⟨33466, by decide⟩
    (prefixPartial 9 18434) = some ⟨9, 1, 0, 33466, 18434, 1, 4194304⟩ := by
  decide +kernel

theorem context_9_18434_33466 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18434 ⟨33466, by decide⟩ :=
  accepted_of_selected 9 18434 ⟨33466, by decide⟩ ⟨9, 1, 0, 33466, 18434, 1, 4194304⟩
    (by decide) selected_cut_52580

theorem selected_cut_52581 : selected 12 ⟨1538133, by decide⟩
    (prefixPartial 9 18435) = some ⟨9, 2, 0, 1538133, 18435, 169, 4194304⟩ := by
  decide +kernel

theorem context_9_18435_1538133 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18435 ⟨1538133, by decide⟩ :=
  accepted_of_selected 9 18435 ⟨1538133, by decide⟩ ⟨9, 2, 0, 1538133, 18435, 169, 4194304⟩
    (by decide) selected_cut_52581

theorem unmarked_context_8_4608_1538134 : frontier 13 ⟨1538134, by decide⟩
    (prefixCache 8 4608) (prefixPartial 8 4608) = false := by
  decide +kernel

theorem node_context_8_4608_1538134 : EJMOriginalGlobalDAGData.nodes 13 ⟨1538134, by decide⟩ =
    .split (coordinate 8) (![⟨1537889, by decide⟩,⟨1538113, by decide⟩,⟨33466, by decide⟩,⟨1538133, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4608_1538134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4608 ⟨1538134, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4608
    ⟨1538134, by decide⟩ (by decide) (![⟨1537889, by decide⟩,⟨1538113, by decide⟩,⟨33466, by decide⟩,⟨1538133, by decide⟩]) unmarked_context_8_4608_1538134 node_context_8_4608_1538134
  intro a
  fin_cases a
  · exact context_9_18432_1537889
  · exact context_9_18433_1538113
  · exact context_9_18434_33466
  · exact context_9_18435_1538133

theorem selected_cut_52582 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 73744) = some ⟨10, 1, 0, 1468246, 73744, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_73744_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 73744 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 73744 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 73744, 1, 1048576⟩
    (by decide) selected_cut_52582

theorem selected_cut_52583 : selected 11 ⟨1538298, by decide⟩
    (prefixPartial 10 73745) = some ⟨10, 2, 0, 1538298, 73745, 3025, 1048576⟩ := by
  decide +kernel

theorem context_10_73745_1538298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 73745 ⟨1538298, by decide⟩ :=
  accepted_of_selected 10 73745 ⟨1538298, by decide⟩ ⟨10, 2, 0, 1538298, 73745, 3025, 1048576⟩
    (by decide) selected_cut_52583

theorem selected_cut_52584 : selected 11 ⟨1538355, by decide⟩
    (prefixPartial 10 73746) = some ⟨10, 2, 0, 1538355, 73746, 1989, 1048576⟩ := by
  decide +kernel

theorem context_10_73746_1538355 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 73746 ⟨1538355, by decide⟩ :=
  accepted_of_selected 10 73746 ⟨1538355, by decide⟩ ⟨10, 2, 0, 1538355, 73746, 1989, 1048576⟩
    (by decide) selected_cut_52584

theorem selected_cut_52585 : selected 11 ⟨1538425, by decide⟩
    (prefixPartial 10 73747) = some ⟨10, 2, 0, 1538425, 73747, 1885, 1048576⟩ := by
  decide +kernel

theorem context_10_73747_1538425 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 73747 ⟨1538425, by decide⟩ :=
  accepted_of_selected 10 73747 ⟨1538425, by decide⟩ ⟨10, 2, 0, 1538425, 73747, 1885, 1048576⟩
    (by decide) selected_cut_52585

theorem unmarked_context_9_18436_1538426 : frontier 12 ⟨1538426, by decide⟩
    (prefixCache 9 18436) (prefixPartial 9 18436) = false := by
  decide +kernel

theorem node_context_9_18436_1538426 : EJMOriginalGlobalDAGData.nodes 12 ⟨1538426, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1538298, by decide⟩,⟨1538355, by decide⟩,⟨1538425, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18436_1538426 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18436 ⟨1538426, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18436
    ⟨1538426, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1538298, by decide⟩,⟨1538355, by decide⟩,⟨1538425, by decide⟩]) unmarked_context_9_18436_1538426 node_context_9_18436_1538426
  intro a
  fin_cases a
  · exact context_10_73744_1468246
  · exact context_10_73745_1538298
  · exact context_10_73746_1538355
  · exact context_10_73747_1538425

theorem selected_cut_52586 : selected 11 ⟨1538497, by decide⟩
    (prefixPartial 10 73748) = some ⟨10, 2, 0, 1538497, 73748, 1481, 1048576⟩ := by
  decide +kernel

theorem context_10_73748_1538497 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 73748 ⟨1538497, by decide⟩ :=
  accepted_of_selected 10 73748 ⟨1538497, by decide⟩ ⟨10, 2, 0, 1538497, 73748, 1481, 1048576⟩
    (by decide) selected_cut_52586

theorem selected_cut_52587 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 73749) = some ⟨10, 1, 0, 1468874, 73749, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_73749_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 73749 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 73749 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 73749, 1, 1048576⟩
    (by decide) selected_cut_52587

theorem selected_cut_52588 : selected 11 ⟨1538559, by decide⟩
    (prefixPartial 10 73750) = some ⟨10, 2, 0, 1538559, 73750, 1873, 1048576⟩ := by
  decide +kernel

theorem context_10_73750_1538559 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 73750 ⟨1538559, by decide⟩ :=
  accepted_of_selected 10 73750 ⟨1538559, by decide⟩ ⟨10, 2, 0, 1538559, 73750, 1873, 1048576⟩
    (by decide) selected_cut_52588

theorem selected_cut_52589 : selected 11 ⟨1538625, by decide⟩
    (prefixPartial 10 73751) = some ⟨10, 2, 0, 1538625, 73751, 1625, 1048576⟩ := by
  decide +kernel

theorem context_10_73751_1538625 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 73751 ⟨1538625, by decide⟩ :=
  accepted_of_selected 10 73751 ⟨1538625, by decide⟩ ⟨10, 2, 0, 1538625, 73751, 1625, 1048576⟩
    (by decide) selected_cut_52589

theorem unmarked_context_9_18437_1538626 : frontier 12 ⟨1538626, by decide⟩
    (prefixCache 9 18437) (prefixPartial 9 18437) = false := by
  decide +kernel

theorem node_context_9_18437_1538626 : EJMOriginalGlobalDAGData.nodes 12 ⟨1538626, by decide⟩ =
    .split (coordinate 9) (![⟨1538497, by decide⟩,⟨1468874, by decide⟩,⟨1538559, by decide⟩,⟨1538625, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18437_1538626 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18437 ⟨1538626, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18437
    ⟨1538626, by decide⟩ (by decide) (![⟨1538497, by decide⟩,⟨1468874, by decide⟩,⟨1538559, by decide⟩,⟨1538625, by decide⟩]) unmarked_context_9_18437_1538626 node_context_9_18437_1538626
  intro a
  fin_cases a
  · exact context_10_73748_1538497
  · exact context_10_73749_1468874
  · exact context_10_73750_1538559
  · exact context_10_73751_1538625

theorem selected_cut_52590 : selected 12 ⟨1538694, by decide⟩
    (prefixPartial 9 18438) = some ⟨9, 2, 0, 1538694, 18438, 2261, 4194304⟩ := by
  decide +kernel

theorem context_9_18438_1538694 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18438 ⟨1538694, by decide⟩ :=
  accepted_of_selected 9 18438 ⟨1538694, by decide⟩ ⟨9, 2, 0, 1538694, 18438, 2261, 4194304⟩
    (by decide) selected_cut_52590

theorem selected_cut_52591 : selected 12 ⟨1538735, by decide⟩
    (prefixPartial 9 18439) = some ⟨9, 2, 0, 1538735, 18439, 861, 4194304⟩ := by
  decide +kernel

theorem context_9_18439_1538735 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18439 ⟨1538735, by decide⟩ :=
  accepted_of_selected 9 18439 ⟨1538735, by decide⟩ ⟨9, 2, 0, 1538735, 18439, 861, 4194304⟩
    (by decide) selected_cut_52591

theorem unmarked_context_8_4609_1538736 : frontier 13 ⟨1538736, by decide⟩
    (prefixCache 8 4609) (prefixPartial 8 4609) = false := by
  decide +kernel

theorem node_context_8_4609_1538736 : EJMOriginalGlobalDAGData.nodes 13 ⟨1538736, by decide⟩ =
    .split (coordinate 8) (![⟨1538426, by decide⟩,⟨1538626, by decide⟩,⟨1538694, by decide⟩,⟨1538735, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4609_1538736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4609 ⟨1538736, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4609
    ⟨1538736, by decide⟩ (by decide) (![⟨1538426, by decide⟩,⟨1538626, by decide⟩,⟨1538694, by decide⟩,⟨1538735, by decide⟩]) unmarked_context_8_4609_1538736 node_context_8_4609_1538736
  intro a
  fin_cases a
  · exact context_9_18436_1538426
  · exact context_9_18437_1538626
  · exact context_9_18438_1538694
  · exact context_9_18439_1538735

theorem selected_cut_52592 : selected 13 ⟨1364555, by decide⟩
    (prefixPartial 8 4610) = some ⟨8, 1, 0, 1364555, 4610, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_4610_1364555 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4610 ⟨1364555, by decide⟩ :=
  accepted_of_selected 8 4610 ⟨1364555, by decide⟩ ⟨8, 1, 0, 1364555, 4610, 1, 16777216⟩
    (by decide) selected_cut_52592

theorem selected_cut_52593 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 73776) = some ⟨10, 1, 0, 1468246, 73776, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_73776_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 73776 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 73776 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 73776, 1, 1048576⟩
    (by decide) selected_cut_52593

theorem selected_cut_52594 : selected 11 ⟨1538841, by decide⟩
    (prefixPartial 10 73777) = some ⟨10, 2, 0, 1538841, 73777, 2309, 1048576⟩ := by
  decide +kernel

theorem context_10_73777_1538841 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 73777 ⟨1538841, by decide⟩ :=
  accepted_of_selected 10 73777 ⟨1538841, by decide⟩ ⟨10, 2, 0, 1538841, 73777, 2309, 1048576⟩
    (by decide) selected_cut_52594

theorem selected_cut_52595 : selected 11 ⟨1538906, by decide⟩
    (prefixPartial 10 73778) = some ⟨10, 2, 0, 1538906, 73778, 1509, 1048576⟩ := by
  decide +kernel

theorem context_10_73778_1538906 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 73778 ⟨1538906, by decide⟩ :=
  accepted_of_selected 10 73778 ⟨1538906, by decide⟩ ⟨10, 2, 0, 1538906, 73778, 1509, 1048576⟩
    (by decide) selected_cut_52595

theorem selected_cut_52596 : selected 11 ⟨1538962, by decide⟩
    (prefixPartial 10 73779) = some ⟨10, 2, 0, 1538962, 73779, 1281, 1048576⟩ := by
  decide +kernel

theorem context_10_73779_1538962 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 73779 ⟨1538962, by decide⟩ :=
  accepted_of_selected 10 73779 ⟨1538962, by decide⟩ ⟨10, 2, 0, 1538962, 73779, 1281, 1048576⟩
    (by decide) selected_cut_52596

theorem unmarked_context_9_18444_1538963 : frontier 12 ⟨1538963, by decide⟩
    (prefixCache 9 18444) (prefixPartial 9 18444) = false := by
  decide +kernel

theorem node_context_9_18444_1538963 : EJMOriginalGlobalDAGData.nodes 12 ⟨1538963, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1538841, by decide⟩,⟨1538906, by decide⟩,⟨1538962, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18444_1538963 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18444 ⟨1538963, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18444
    ⟨1538963, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1538841, by decide⟩,⟨1538906, by decide⟩,⟨1538962, by decide⟩]) unmarked_context_9_18444_1538963 node_context_9_18444_1538963
  intro a
  fin_cases a
  · exact context_10_73776_1468246
  · exact context_10_73777_1538841
  · exact context_10_73778_1538906
  · exact context_10_73779_1538962

theorem selected_cut_52597 : selected 12 ⟨1539126, by decide⟩
    (prefixPartial 9 18445) = some ⟨9, 2, 0, 1539126, 18445, 3965, 4194304⟩ := by
  decide +kernel

theorem context_9_18445_1539126 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18445 ⟨1539126, by decide⟩ :=
  accepted_of_selected 9 18445 ⟨1539126, by decide⟩ ⟨9, 2, 0, 1539126, 18445, 3965, 4194304⟩
    (by decide) selected_cut_52597

theorem selected_cut_52598 : selected 12 ⟨1539203, by decide⟩
    (prefixPartial 9 18446) = some ⟨9, 2, 0, 1539203, 18446, 2157, 4194304⟩ := by
  decide +kernel

theorem context_9_18446_1539203 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18446 ⟨1539203, by decide⟩ :=
  accepted_of_selected 9 18446 ⟨1539203, by decide⟩ ⟨9, 2, 0, 1539203, 18446, 2157, 4194304⟩
    (by decide) selected_cut_52598

theorem selected_cut_52599 : selected 12 ⟨1539244, by decide⟩
    (prefixPartial 9 18447) = some ⟨9, 2, 0, 1539244, 18447, 813, 4194304⟩ := by
  decide +kernel

theorem context_9_18447_1539244 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18447 ⟨1539244, by decide⟩ :=
  accepted_of_selected 9 18447 ⟨1539244, by decide⟩ ⟨9, 2, 0, 1539244, 18447, 813, 4194304⟩
    (by decide) selected_cut_52599

theorem unmarked_context_8_4611_1539245 : frontier 13 ⟨1539245, by decide⟩
    (prefixCache 8 4611) (prefixPartial 8 4611) = false := by
  decide +kernel

theorem node_context_8_4611_1539245 : EJMOriginalGlobalDAGData.nodes 13 ⟨1539245, by decide⟩ =
    .split (coordinate 8) (![⟨1538963, by decide⟩,⟨1539126, by decide⟩,⟨1539203, by decide⟩,⟨1539244, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4611_1539245 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4611 ⟨1539245, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4611
    ⟨1539245, by decide⟩ (by decide) (![⟨1538963, by decide⟩,⟨1539126, by decide⟩,⟨1539203, by decide⟩,⟨1539244, by decide⟩]) unmarked_context_8_4611_1539245 node_context_8_4611_1539245
  intro a
  fin_cases a
  · exact context_9_18444_1538963
  · exact context_9_18445_1539126
  · exact context_9_18446_1539203
  · exact context_9_18447_1539244

theorem unmarked_context_7_1152_1539246 : frontier 14 ⟨1539246, by decide⟩
    (prefixCache 7 1152) (prefixPartial 7 1152) = false := by
  decide +kernel

theorem node_context_7_1152_1539246 : EJMOriginalGlobalDAGData.nodes 14 ⟨1539246, by decide⟩ =
    .split (coordinate 7) (![⟨1538134, by decide⟩,⟨1538736, by decide⟩,⟨1364555, by decide⟩,⟨1539245, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_1152_1539246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 1152 ⟨1539246, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 1152
    ⟨1539246, by decide⟩ (by decide) (![⟨1538134, by decide⟩,⟨1538736, by decide⟩,⟨1364555, by decide⟩,⟨1539245, by decide⟩]) unmarked_context_7_1152_1539246 node_context_7_1152_1539246
  intro a
  fin_cases a
  · exact context_8_4608_1538134
  · exact context_8_4609_1538736
  · exact context_8_4610_1364555
  · exact context_8_4611_1539245

theorem selected_cut_52600 : selected 14 ⟨1539247, by decide⟩
    (prefixPartial 7 1153) = some ⟨7, 1, 0, 1539247, 1153, 1, 67108864⟩ := by
  decide +kernel

theorem context_7_1153_1539247 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 1153 ⟨1539247, by decide⟩ :=
  accepted_of_selected 7 1153 ⟨1539247, by decide⟩ ⟨7, 1, 0, 1539247, 1153, 1, 67108864⟩
    (by decide) selected_cut_52600

theorem selected_cut_52601 : selected 13 ⟨979897, by decide⟩
    (prefixPartial 8 4616) = some ⟨8, 1, 0, 979897, 4616, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_4616_979897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4616 ⟨979897, by decide⟩ :=
  accepted_of_selected 8 4616 ⟨979897, by decide⟩ ⟨8, 1, 0, 979897, 4616, 1, 16777216⟩
    (by decide) selected_cut_52601

theorem selected_cut_52602 : selected 12 ⟨1539448, by decide⟩
    (prefixPartial 9 18468) = some ⟨9, 2, 0, 1539448, 18468, 3785, 4194304⟩ := by
  decide +kernel

theorem context_9_18468_1539448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18468 ⟨1539448, by decide⟩ :=
  accepted_of_selected 9 18468 ⟨1539448, by decide⟩ ⟨9, 2, 0, 1539448, 18468, 3785, 4194304⟩
    (by decide) selected_cut_52602

theorem selected_cut_52603 : selected 11 ⟨1539540, by decide⟩
    (prefixPartial 10 73876) = some ⟨10, 2, 0, 1539540, 73876, 1781, 1048576⟩ := by
  decide +kernel

theorem context_10_73876_1539540 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 73876 ⟨1539540, by decide⟩ :=
  accepted_of_selected 10 73876 ⟨1539540, by decide⟩ ⟨10, 2, 0, 1539540, 73876, 1781, 1048576⟩
    (by decide) selected_cut_52603

theorem selected_cut_52604 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 73877) = some ⟨10, 1, 0, 1468874, 73877, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_73877_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 73877 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 73877 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 73877, 1, 1048576⟩
    (by decide) selected_cut_52604

theorem selected_cut_52605 : selected 11 ⟨1539630, by decide⟩
    (prefixPartial 10 73878) = some ⟨10, 2, 0, 1539630, 73878, 1653, 1048576⟩ := by
  decide +kernel

theorem context_10_73878_1539630 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 73878 ⟨1539630, by decide⟩ :=
  accepted_of_selected 10 73878 ⟨1539630, by decide⟩ ⟨10, 2, 0, 1539630, 73878, 1653, 1048576⟩
    (by decide) selected_cut_52605

theorem selected_cut_52606 : selected 11 ⟨1539680, by decide⟩
    (prefixPartial 10 73879) = some ⟨10, 2, 0, 1539680, 73879, 1069, 1048576⟩ := by
  decide +kernel

theorem context_10_73879_1539680 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 73879 ⟨1539680, by decide⟩ :=
  accepted_of_selected 10 73879 ⟨1539680, by decide⟩ ⟨10, 2, 0, 1539680, 73879, 1069, 1048576⟩
    (by decide) selected_cut_52606

theorem unmarked_context_9_18469_1539681 : frontier 12 ⟨1539681, by decide⟩
    (prefixCache 9 18469) (prefixPartial 9 18469) = false := by
  decide +kernel

theorem node_context_9_18469_1539681 : EJMOriginalGlobalDAGData.nodes 12 ⟨1539681, by decide⟩ =
    .split (coordinate 9) (![⟨1539540, by decide⟩,⟨1468874, by decide⟩,⟨1539630, by decide⟩,⟨1539680, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_18469_1539681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18469 ⟨1539681, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 18469
    ⟨1539681, by decide⟩ (by decide) (![⟨1539540, by decide⟩,⟨1468874, by decide⟩,⟨1539630, by decide⟩,⟨1539680, by decide⟩]) unmarked_context_9_18469_1539681 node_context_9_18469_1539681
  intro a
  fin_cases a
  · exact context_10_73876_1539540
  · exact context_10_73877_1468874
  · exact context_10_73878_1539630
  · exact context_10_73879_1539680

theorem selected_cut_52607 : selected 12 ⟨33466, by decide⟩
    (prefixPartial 9 18470) = some ⟨9, 1, 0, 33466, 18470, 1, 4194304⟩ := by
  decide +kernel

theorem context_9_18470_33466 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18470 ⟨33466, by decide⟩ :=
  accepted_of_selected 9 18470 ⟨33466, by decide⟩ ⟨9, 1, 0, 33466, 18470, 1, 4194304⟩
    (by decide) selected_cut_52607

theorem selected_cut_52608 : selected 12 ⟨1539726, by decide⟩
    (prefixPartial 9 18471) = some ⟨9, 2, 0, 1539726, 18471, 501, 4194304⟩ := by
  decide +kernel

theorem context_9_18471_1539726 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 18471 ⟨1539726, by decide⟩ :=
  accepted_of_selected 9 18471 ⟨1539726, by decide⟩ ⟨9, 2, 0, 1539726, 18471, 501, 4194304⟩
    (by decide) selected_cut_52608

theorem unmarked_context_8_4617_1539727 : frontier 13 ⟨1539727, by decide⟩
    (prefixCache 8 4617) (prefixPartial 8 4617) = false := by
  decide +kernel

theorem node_context_8_4617_1539727 : EJMOriginalGlobalDAGData.nodes 13 ⟨1539727, by decide⟩ =
    .split (coordinate 8) (![⟨1539448, by decide⟩,⟨1539681, by decide⟩,⟨33466, by decide⟩,⟨1539726, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4617_1539727 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4617 ⟨1539727, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4617
    ⟨1539727, by decide⟩ (by decide) (![⟨1539448, by decide⟩,⟨1539681, by decide⟩,⟨33466, by decide⟩,⟨1539726, by decide⟩]) unmarked_context_8_4617_1539727 node_context_8_4617_1539727
  intro a
  fin_cases a
  · exact context_9_18468_1539448
  · exact context_9_18469_1539681
  · exact context_9_18470_33466
  · exact context_9_18471_1539726

theorem selected_cut_52609 : selected 13 ⟨979897, by decide⟩
    (prefixPartial 8 4618) = some ⟨8, 1, 0, 979897, 4618, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_4618_979897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4618 ⟨979897, by decide⟩ :=
  accepted_of_selected 8 4618 ⟨979897, by decide⟩ ⟨8, 1, 0, 979897, 4618, 1, 16777216⟩
    (by decide) selected_cut_52609

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
