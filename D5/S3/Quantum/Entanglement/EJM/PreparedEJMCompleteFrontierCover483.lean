/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover482
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_46371 : selected 9 ⟨1292976, by decide⟩
    (prefixPartial 12 370500) = some ⟨12, 2, 0, 1292976, 370500, 2045, 65536⟩ := by
  decide +kernel

theorem context_12_370500_1292976 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370500 ⟨1292976, by decide⟩ :=
  accepted_of_selected 12 370500 ⟨1292976, by decide⟩ ⟨12, 2, 0, 1292976, 370500, 2045, 65536⟩
    (by decide) selected_cut_46371

theorem selected_cut_46372 : selected 9 ⟨1257136, by decide⟩
    (prefixPartial 12 370501) = some ⟨12, 1, 0, 1257136, 370501, 1, 65536⟩ := by
  decide +kernel

theorem context_12_370501_1257136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370501 ⟨1257136, by decide⟩ :=
  accepted_of_selected 12 370501 ⟨1257136, by decide⟩ ⟨12, 1, 0, 1257136, 370501, 1, 65536⟩
    (by decide) selected_cut_46372

theorem selected_cut_46373 : selected 9 ⟨1293014, by decide⟩
    (prefixPartial 12 370502) = some ⟨12, 2, 0, 1293014, 370502, 1841, 65536⟩ := by
  decide +kernel

theorem context_12_370502_1293014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370502 ⟨1293014, by decide⟩ :=
  accepted_of_selected 12 370502 ⟨1293014, by decide⟩ ⟨12, 2, 0, 1293014, 370502, 1841, 65536⟩
    (by decide) selected_cut_46373

theorem selected_cut_46374 : selected 9 ⟨1293068, by decide⟩
    (prefixPartial 12 370503) = some ⟨12, 2, 0, 1293068, 370503, 2089, 65536⟩ := by
  decide +kernel

theorem context_12_370503_1293068 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370503 ⟨1293068, by decide⟩ :=
  accepted_of_selected 12 370503 ⟨1293068, by decide⟩ ⟨12, 2, 0, 1293068, 370503, 2089, 65536⟩
    (by decide) selected_cut_46374

theorem unmarked_context_11_92625_1293069 : frontier 10 ⟨1293069, by decide⟩
    (prefixCache 11 92625) (prefixPartial 11 92625) = false := by
  decide +kernel

theorem node_context_11_92625_1293069 : EJMOriginalGlobalDAGData.nodes 10 ⟨1293069, by decide⟩ =
    .split (coordinate 11) (![⟨1292976, by decide⟩,⟨1257136, by decide⟩,⟨1293014, by decide⟩,⟨1293068, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92625_1293069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92625 ⟨1293069, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92625
    ⟨1293069, by decide⟩ (by decide) (![⟨1292976, by decide⟩,⟨1257136, by decide⟩,⟨1293014, by decide⟩,⟨1293068, by decide⟩]) unmarked_context_11_92625_1293069 node_context_11_92625_1293069
  intro a
  fin_cases a
  · exact context_12_370500_1292976
  · exact context_12_370501_1257136
  · exact context_12_370502_1293014
  · exact context_12_370503_1293068

theorem selected_cut_46375 : selected 9 ⟨1293107, by decide⟩
    (prefixPartial 12 370504) = some ⟨12, 2, 0, 1293107, 370504, 1949, 65536⟩ := by
  decide +kernel

theorem context_12_370504_1293107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370504 ⟨1293107, by decide⟩ :=
  accepted_of_selected 12 370504 ⟨1293107, by decide⟩ ⟨12, 2, 0, 1293107, 370504, 1949, 65536⟩
    (by decide) selected_cut_46375

theorem selected_cut_46376 : selected 9 ⟨1293136, by decide⟩
    (prefixPartial 12 370505) = some ⟨12, 2, 0, 1293136, 370505, 1553, 65536⟩ := by
  decide +kernel

theorem context_12_370505_1293136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370505 ⟨1293136, by decide⟩ :=
  accepted_of_selected 12 370505 ⟨1293136, by decide⟩ ⟨12, 2, 0, 1293136, 370505, 1553, 65536⟩
    (by decide) selected_cut_46376

theorem selected_cut_46377 : selected 9 ⟨1293165, by decide⟩
    (prefixPartial 12 370506) = some ⟨12, 2, 0, 1293165, 370506, 1709, 65536⟩ := by
  decide +kernel

theorem context_12_370506_1293165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370506 ⟨1293165, by decide⟩ :=
  accepted_of_selected 12 370506 ⟨1293165, by decide⟩ ⟨12, 2, 0, 1293165, 370506, 1709, 65536⟩
    (by decide) selected_cut_46377

theorem selected_cut_46378 : selected 9 ⟨1293204, by decide⟩
    (prefixPartial 12 370507) = some ⟨12, 2, 0, 1293204, 370507, 1965, 65536⟩ := by
  decide +kernel

theorem context_12_370507_1293204 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370507 ⟨1293204, by decide⟩ :=
  accepted_of_selected 12 370507 ⟨1293204, by decide⟩ ⟨12, 2, 0, 1293204, 370507, 1965, 65536⟩
    (by decide) selected_cut_46378

theorem unmarked_context_11_92626_1293205 : frontier 10 ⟨1293205, by decide⟩
    (prefixCache 11 92626) (prefixPartial 11 92626) = false := by
  decide +kernel

theorem node_context_11_92626_1293205 : EJMOriginalGlobalDAGData.nodes 10 ⟨1293205, by decide⟩ =
    .split (coordinate 11) (![⟨1293107, by decide⟩,⟨1293136, by decide⟩,⟨1293165, by decide⟩,⟨1293204, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92626_1293205 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92626 ⟨1293205, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92626
    ⟨1293205, by decide⟩ (by decide) (![⟨1293107, by decide⟩,⟨1293136, by decide⟩,⟨1293165, by decide⟩,⟨1293204, by decide⟩]) unmarked_context_11_92626_1293205 node_context_11_92626_1293205
  intro a
  fin_cases a
  · exact context_12_370504_1293107
  · exact context_12_370505_1293136
  · exact context_12_370506_1293165
  · exact context_12_370507_1293204

theorem selected_cut_46379 : selected 9 ⟨1293246, by decide⟩
    (prefixPartial 12 370508) = some ⟨12, 2, 0, 1293246, 370508, 1821, 65536⟩ := by
  decide +kernel

theorem context_12_370508_1293246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370508 ⟨1293246, by decide⟩ :=
  accepted_of_selected 12 370508 ⟨1293246, by decide⟩ ⟨12, 2, 0, 1293246, 370508, 1821, 65536⟩
    (by decide) selected_cut_46379

theorem selected_cut_46380 : selected 9 ⟨1293266, by decide⟩
    (prefixPartial 12 370509) = some ⟨12, 2, 0, 1293266, 370509, 1397, 65536⟩ := by
  decide +kernel

theorem context_12_370509_1293266 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370509 ⟨1293266, by decide⟩ :=
  accepted_of_selected 12 370509 ⟨1293266, by decide⟩ ⟨12, 2, 0, 1293266, 370509, 1397, 65536⟩
    (by decide) selected_cut_46380

theorem selected_cut_46381 : selected 9 ⟨1293302, by decide⟩
    (prefixPartial 12 370510) = some ⟨12, 2, 0, 1293302, 370510, 1689, 65536⟩ := by
  decide +kernel

theorem context_12_370510_1293302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370510 ⟨1293302, by decide⟩ :=
  accepted_of_selected 12 370510 ⟨1293302, by decide⟩ ⟨12, 2, 0, 1293302, 370510, 1689, 65536⟩
    (by decide) selected_cut_46381

theorem selected_cut_46382 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 370511) = some ⟨12, 1, 0, 903806, 370511, 1, 65536⟩ := by
  decide +kernel

theorem context_12_370511_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370511 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 370511 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 370511, 1, 65536⟩
    (by decide) selected_cut_46382

theorem unmarked_context_11_92627_1293303 : frontier 10 ⟨1293303, by decide⟩
    (prefixCache 11 92627) (prefixPartial 11 92627) = false := by
  decide +kernel

theorem node_context_11_92627_1293303 : EJMOriginalGlobalDAGData.nodes 10 ⟨1293303, by decide⟩ =
    .split (coordinate 11) (![⟨1293246, by decide⟩,⟨1293266, by decide⟩,⟨1293302, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92627_1293303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92627 ⟨1293303, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92627
    ⟨1293303, by decide⟩ (by decide) (![⟨1293246, by decide⟩,⟨1293266, by decide⟩,⟨1293302, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_92627_1293303 node_context_11_92627_1293303
  intro a
  fin_cases a
  · exact context_12_370508_1293246
  · exact context_12_370509_1293266
  · exact context_12_370510_1293302
  · exact context_12_370511_903806

theorem unmarked_context_10_23156_1293304 : frontier 11 ⟨1293304, by decide⟩
    (prefixCache 10 23156) (prefixPartial 10 23156) = false := by
  decide +kernel

theorem node_context_10_23156_1293304 : EJMOriginalGlobalDAGData.nodes 11 ⟨1293304, by decide⟩ =
    .split (coordinate 10) (![⟨1283168, by decide⟩,⟨1293069, by decide⟩,⟨1293205, by decide⟩,⟨1293303, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23156_1293304 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23156 ⟨1293304, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23156
    ⟨1293304, by decide⟩ (by decide) (![⟨1283168, by decide⟩,⟨1293069, by decide⟩,⟨1293205, by decide⟩,⟨1293303, by decide⟩]) unmarked_context_10_23156_1293304 node_context_10_23156_1293304
  intro a
  fin_cases a
  · exact context_11_92624_1283168
  · exact context_11_92625_1293069
  · exact context_11_92626_1293205
  · exact context_11_92627_1293303

theorem selected_cut_46383 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 23157) = some ⟨10, 1, 0, 893098, 23157, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_23157_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23157 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 23157 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 23157, 1, 1048576⟩
    (by decide) selected_cut_46383

theorem selected_cut_46384 : selected 9 ⟨1293337, by decide⟩
    (prefixPartial 12 370528) = some ⟨12, 2, 0, 1293337, 370528, 1557, 65536⟩ := by
  decide +kernel

theorem context_12_370528_1293337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370528 ⟨1293337, by decide⟩ :=
  accepted_of_selected 12 370528 ⟨1293337, by decide⟩ ⟨12, 2, 0, 1293337, 370528, 1557, 65536⟩
    (by decide) selected_cut_46384

theorem selected_cut_46385 : selected 9 ⟨1256866, by decide⟩
    (prefixPartial 12 370529) = some ⟨12, 1, 0, 1256866, 370529, 1, 65536⟩ := by
  decide +kernel

theorem context_12_370529_1256866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370529 ⟨1256866, by decide⟩ :=
  accepted_of_selected 12 370529 ⟨1256866, by decide⟩ ⟨12, 1, 0, 1256866, 370529, 1, 65536⟩
    (by decide) selected_cut_46385

theorem selected_cut_46386 : selected 9 ⟨1293371, by decide⟩
    (prefixPartial 12 370530) = some ⟨12, 2, 0, 1293371, 370530, 1469, 65536⟩ := by
  decide +kernel

theorem context_12_370530_1293371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370530 ⟨1293371, by decide⟩ :=
  accepted_of_selected 12 370530 ⟨1293371, by decide⟩ ⟨12, 2, 0, 1293371, 370530, 1469, 65536⟩
    (by decide) selected_cut_46386

theorem selected_cut_46387 : selected 9 ⟨1293397, by decide⟩
    (prefixPartial 12 370531) = some ⟨12, 2, 0, 1293397, 370531, 1513, 65536⟩ := by
  decide +kernel

theorem context_12_370531_1293397 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370531 ⟨1293397, by decide⟩ :=
  accepted_of_selected 12 370531 ⟨1293397, by decide⟩ ⟨12, 2, 0, 1293397, 370531, 1513, 65536⟩
    (by decide) selected_cut_46387

theorem unmarked_context_11_92632_1293398 : frontier 10 ⟨1293398, by decide⟩
    (prefixCache 11 92632) (prefixPartial 11 92632) = false := by
  decide +kernel

theorem node_context_11_92632_1293398 : EJMOriginalGlobalDAGData.nodes 10 ⟨1293398, by decide⟩ =
    .split (coordinate 11) (![⟨1293337, by decide⟩,⟨1256866, by decide⟩,⟨1293371, by decide⟩,⟨1293397, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92632_1293398 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92632 ⟨1293398, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92632
    ⟨1293398, by decide⟩ (by decide) (![⟨1293337, by decide⟩,⟨1256866, by decide⟩,⟨1293371, by decide⟩,⟨1293397, by decide⟩]) unmarked_context_11_92632_1293398 node_context_11_92632_1293398
  intro a
  fin_cases a
  · exact context_12_370528_1293337
  · exact context_12_370529_1256866
  · exact context_12_370530_1293371
  · exact context_12_370531_1293397

theorem selected_cut_46388 : selected 9 ⟨1293426, by decide⟩
    (prefixPartial 12 370532) = some ⟨12, 2, 0, 1293426, 370532, 1493, 65536⟩ := by
  decide +kernel

theorem context_12_370532_1293426 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370532 ⟨1293426, by decide⟩ :=
  accepted_of_selected 12 370532 ⟨1293426, by decide⟩ ⟨12, 2, 0, 1293426, 370532, 1493, 65536⟩
    (by decide) selected_cut_46388

theorem selected_cut_46389 : selected 9 ⟨1256866, by decide⟩
    (prefixPartial 12 370533) = some ⟨12, 1, 0, 1256866, 370533, 1, 65536⟩ := by
  decide +kernel

theorem context_12_370533_1256866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370533 ⟨1256866, by decide⟩ :=
  accepted_of_selected 12 370533 ⟨1256866, by decide⟩ ⟨12, 1, 0, 1256866, 370533, 1, 65536⟩
    (by decide) selected_cut_46389

theorem selected_cut_46390 : selected 9 ⟨1293449, by decide⟩
    (prefixPartial 12 370534) = some ⟨12, 2, 0, 1293449, 370534, 1245, 65536⟩ := by
  decide +kernel

theorem context_12_370534_1293449 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370534 ⟨1293449, by decide⟩ :=
  accepted_of_selected 12 370534 ⟨1293449, by decide⟩ ⟨12, 2, 0, 1293449, 370534, 1245, 65536⟩
    (by decide) selected_cut_46390

theorem selected_cut_46391 : selected 9 ⟨1293472, by decide⟩
    (prefixPartial 12 370535) = some ⟨12, 2, 0, 1293472, 370535, 1401, 65536⟩ := by
  decide +kernel

theorem context_12_370535_1293472 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370535 ⟨1293472, by decide⟩ :=
  accepted_of_selected 12 370535 ⟨1293472, by decide⟩ ⟨12, 2, 0, 1293472, 370535, 1401, 65536⟩
    (by decide) selected_cut_46391

theorem unmarked_context_11_92633_1293473 : frontier 10 ⟨1293473, by decide⟩
    (prefixCache 11 92633) (prefixPartial 11 92633) = false := by
  decide +kernel

theorem node_context_11_92633_1293473 : EJMOriginalGlobalDAGData.nodes 10 ⟨1293473, by decide⟩ =
    .split (coordinate 11) (![⟨1293426, by decide⟩,⟨1256866, by decide⟩,⟨1293449, by decide⟩,⟨1293472, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92633_1293473 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92633 ⟨1293473, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92633
    ⟨1293473, by decide⟩ (by decide) (![⟨1293426, by decide⟩,⟨1256866, by decide⟩,⟨1293449, by decide⟩,⟨1293472, by decide⟩]) unmarked_context_11_92633_1293473 node_context_11_92633_1293473
  intro a
  fin_cases a
  · exact context_12_370532_1293426
  · exact context_12_370533_1256866
  · exact context_12_370534_1293449
  · exact context_12_370535_1293472

theorem selected_cut_46392 : selected 10 ⟨1283737, by decide⟩
    (prefixPartial 11 92634) = some ⟨11, 1, 0, 1283737, 92634, 1, 262144⟩ := by
  decide +kernel

theorem context_11_92634_1283737 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92634 ⟨1283737, by decide⟩ :=
  accepted_of_selected 11 92634 ⟨1283737, by decide⟩ ⟨11, 1, 0, 1283737, 92634, 1, 262144⟩
    (by decide) selected_cut_46392

theorem selected_cut_46393 : selected 10 ⟨1293527, by decide⟩
    (prefixPartial 11 92635) = some ⟨11, 2, 0, 1293527, 92635, 2873, 262144⟩ := by
  decide +kernel

theorem context_11_92635_1293527 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92635 ⟨1293527, by decide⟩ :=
  accepted_of_selected 11 92635 ⟨1293527, by decide⟩ ⟨11, 2, 0, 1293527, 92635, 2873, 262144⟩
    (by decide) selected_cut_46393

theorem unmarked_context_10_23158_1293528 : frontier 11 ⟨1293528, by decide⟩
    (prefixCache 10 23158) (prefixPartial 10 23158) = false := by
  decide +kernel

theorem node_context_10_23158_1293528 : EJMOriginalGlobalDAGData.nodes 11 ⟨1293528, by decide⟩ =
    .split (coordinate 10) (![⟨1293398, by decide⟩,⟨1293473, by decide⟩,⟨1283737, by decide⟩,⟨1293527, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23158_1293528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23158 ⟨1293528, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23158
    ⟨1293528, by decide⟩ (by decide) (![⟨1293398, by decide⟩,⟨1293473, by decide⟩,⟨1283737, by decide⟩,⟨1293527, by decide⟩]) unmarked_context_10_23158_1293528 node_context_10_23158_1293528
  intro a
  fin_cases a
  · exact context_11_92632_1293398
  · exact context_11_92633_1293473
  · exact context_11_92634_1283737
  · exact context_11_92635_1293527

theorem selected_cut_46394 : selected 9 ⟨1293553, by decide⟩
    (prefixPartial 12 370544) = some ⟨12, 2, 0, 1293553, 370544, 1473, 65536⟩ := by
  decide +kernel

theorem context_12_370544_1293553 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370544 ⟨1293553, by decide⟩ :=
  accepted_of_selected 12 370544 ⟨1293553, by decide⟩ ⟨12, 2, 0, 1293553, 370544, 1473, 65536⟩
    (by decide) selected_cut_46394

theorem selected_cut_46395 : selected 9 ⟨1293569, by decide⟩
    (prefixPartial 12 370545) = some ⟨12, 2, 0, 1293569, 370545, 1181, 65536⟩ := by
  decide +kernel

theorem context_12_370545_1293569 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370545 ⟨1293569, by decide⟩ :=
  accepted_of_selected 12 370545 ⟨1293569, by decide⟩ ⟨12, 2, 0, 1293569, 370545, 1181, 65536⟩
    (by decide) selected_cut_46395

theorem selected_cut_46396 : selected 9 ⟨1293590, by decide⟩
    (prefixPartial 12 370546) = some ⟨12, 2, 0, 1293590, 370546, 1377, 65536⟩ := by
  decide +kernel

theorem context_12_370546_1293590 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370546 ⟨1293590, by decide⟩ :=
  accepted_of_selected 12 370546 ⟨1293590, by decide⟩ ⟨12, 2, 0, 1293590, 370546, 1377, 65536⟩
    (by decide) selected_cut_46396

theorem selected_cut_46397 : selected 9 ⟨1293616, by decide⟩
    (prefixPartial 12 370547) = some ⟨12, 2, 0, 1293616, 370547, 1425, 65536⟩ := by
  decide +kernel

theorem context_12_370547_1293616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370547 ⟨1293616, by decide⟩ :=
  accepted_of_selected 12 370547 ⟨1293616, by decide⟩ ⟨12, 2, 0, 1293616, 370547, 1425, 65536⟩
    (by decide) selected_cut_46397

theorem unmarked_context_11_92636_1293617 : frontier 10 ⟨1293617, by decide⟩
    (prefixCache 11 92636) (prefixPartial 11 92636) = false := by
  decide +kernel

theorem node_context_11_92636_1293617 : EJMOriginalGlobalDAGData.nodes 10 ⟨1293617, by decide⟩ =
    .split (coordinate 11) (![⟨1293553, by decide⟩,⟨1293569, by decide⟩,⟨1293590, by decide⟩,⟨1293616, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92636_1293617 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92636 ⟨1293617, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92636
    ⟨1293617, by decide⟩ (by decide) (![⟨1293553, by decide⟩,⟨1293569, by decide⟩,⟨1293590, by decide⟩,⟨1293616, by decide⟩]) unmarked_context_11_92636_1293617 node_context_11_92636_1293617
  intro a
  fin_cases a
  · exact context_12_370544_1293553
  · exact context_12_370545_1293569
  · exact context_12_370546_1293590
  · exact context_12_370547_1293616

theorem selected_cut_46398 : selected 10 ⟨1293676, by decide⟩
    (prefixPartial 11 92637) = some ⟨11, 2, 0, 1293676, 92637, 3629, 262144⟩ := by
  decide +kernel

theorem context_11_92637_1293676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92637 ⟨1293676, by decide⟩ :=
  accepted_of_selected 11 92637 ⟨1293676, by decide⟩ ⟨11, 2, 0, 1293676, 92637, 3629, 262144⟩
    (by decide) selected_cut_46398

theorem selected_cut_46399 : selected 10 ⟨1293730, by decide⟩
    (prefixPartial 11 92638) = some ⟨11, 2, 0, 1293730, 92638, 2549, 262144⟩ := by
  decide +kernel

theorem context_11_92638_1293730 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92638 ⟨1293730, by decide⟩ :=
  accepted_of_selected 11 92638 ⟨1293730, by decide⟩ ⟨11, 2, 0, 1293730, 92638, 2549, 262144⟩
    (by decide) selected_cut_46399

theorem selected_cut_46400 : selected 10 ⟨1284138, by decide⟩
    (prefixPartial 11 92639) = some ⟨11, 1, 0, 1284138, 92639, 1, 262144⟩ := by
  decide +kernel

theorem context_11_92639_1284138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92639 ⟨1284138, by decide⟩ :=
  accepted_of_selected 11 92639 ⟨1284138, by decide⟩ ⟨11, 1, 0, 1284138, 92639, 1, 262144⟩
    (by decide) selected_cut_46400

theorem unmarked_context_10_23159_1293731 : frontier 11 ⟨1293731, by decide⟩
    (prefixCache 10 23159) (prefixPartial 10 23159) = false := by
  decide +kernel

theorem node_context_10_23159_1293731 : EJMOriginalGlobalDAGData.nodes 11 ⟨1293731, by decide⟩ =
    .split (coordinate 10) (![⟨1293617, by decide⟩,⟨1293676, by decide⟩,⟨1293730, by decide⟩,⟨1284138, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23159_1293731 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23159 ⟨1293731, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23159
    ⟨1293731, by decide⟩ (by decide) (![⟨1293617, by decide⟩,⟨1293676, by decide⟩,⟨1293730, by decide⟩,⟨1284138, by decide⟩]) unmarked_context_10_23159_1293731 node_context_10_23159_1293731
  intro a
  fin_cases a
  · exact context_11_92636_1293617
  · exact context_11_92637_1293676
  · exact context_11_92638_1293730
  · exact context_11_92639_1284138

theorem unmarked_context_9_5789_1293732 : frontier 12 ⟨1293732, by decide⟩
    (prefixCache 9 5789) (prefixPartial 9 5789) = false := by
  decide +kernel

theorem node_context_9_5789_1293732 : EJMOriginalGlobalDAGData.nodes 12 ⟨1293732, by decide⟩ =
    .split (coordinate 9) (![⟨1293304, by decide⟩,⟨893098, by decide⟩,⟨1293528, by decide⟩,⟨1293731, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5789_1293732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5789 ⟨1293732, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5789
    ⟨1293732, by decide⟩ (by decide) (![⟨1293304, by decide⟩,⟨893098, by decide⟩,⟨1293528, by decide⟩,⟨1293731, by decide⟩]) unmarked_context_9_5789_1293732 node_context_9_5789_1293732
  intro a
  fin_cases a
  · exact context_10_23156_1293304
  · exact context_10_23157_893098
  · exact context_10_23158_1293528
  · exact context_10_23159_1293731

theorem selected_cut_46401 : selected 10 ⟨1293762, by decide⟩
    (prefixPartial 11 92640) = some ⟨11, 2, 0, 1293762, 92640, 1941, 262144⟩ := by
  decide +kernel

theorem context_11_92640_1293762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92640 ⟨1293762, by decide⟩ :=
  accepted_of_selected 11 92640 ⟨1293762, by decide⟩ ⟨11, 2, 0, 1293762, 92640, 1941, 262144⟩
    (by decide) selected_cut_46401

theorem selected_cut_46402 : selected 10 ⟨1293808, by decide⟩
    (prefixPartial 11 92641) = some ⟨11, 2, 0, 1293808, 92641, 2789, 262144⟩ := by
  decide +kernel

theorem context_11_92641_1293808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92641 ⟨1293808, by decide⟩ :=
  accepted_of_selected 11 92641 ⟨1293808, by decide⟩ ⟨11, 2, 0, 1293808, 92641, 2789, 262144⟩
    (by decide) selected_cut_46402

theorem selected_cut_46403 : selected 10 ⟨1293851, by decide⟩
    (prefixPartial 11 92642) = some ⟨11, 2, 0, 1293851, 92642, 2713, 262144⟩ := by
  decide +kernel

theorem context_11_92642_1293851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92642 ⟨1293851, by decide⟩ :=
  accepted_of_selected 11 92642 ⟨1293851, by decide⟩ ⟨11, 2, 0, 1293851, 92642, 2713, 262144⟩
    (by decide) selected_cut_46403

theorem selected_cut_46404 : selected 10 ⟨1293866, by decide⟩
    (prefixPartial 11 92643) = some ⟨11, 2, 0, 1293866, 92643, 1461, 262144⟩ := by
  decide +kernel

theorem context_11_92643_1293866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92643 ⟨1293866, by decide⟩ :=
  accepted_of_selected 11 92643 ⟨1293866, by decide⟩ ⟨11, 2, 0, 1293866, 92643, 1461, 262144⟩
    (by decide) selected_cut_46404

theorem unmarked_context_10_23160_1293867 : frontier 11 ⟨1293867, by decide⟩
    (prefixCache 10 23160) (prefixPartial 10 23160) = false := by
  decide +kernel

theorem node_context_10_23160_1293867 : EJMOriginalGlobalDAGData.nodes 11 ⟨1293867, by decide⟩ =
    .split (coordinate 10) (![⟨1293762, by decide⟩,⟨1293808, by decide⟩,⟨1293851, by decide⟩,⟨1293866, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23160_1293867 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23160 ⟨1293867, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23160
    ⟨1293867, by decide⟩ (by decide) (![⟨1293762, by decide⟩,⟨1293808, by decide⟩,⟨1293851, by decide⟩,⟨1293866, by decide⟩]) unmarked_context_10_23160_1293867 node_context_10_23160_1293867
  intro a
  fin_cases a
  · exact context_11_92640_1293762
  · exact context_11_92641_1293808
  · exact context_11_92642_1293851
  · exact context_11_92643_1293866

theorem selected_cut_46405 : selected 10 ⟨1293895, by decide⟩
    (prefixPartial 11 92644) = some ⟨11, 2, 0, 1293895, 92644, 2089, 262144⟩ := by
  decide +kernel

theorem context_11_92644_1293895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92644 ⟨1293895, by decide⟩ :=
  accepted_of_selected 11 92644 ⟨1293895, by decide⟩ ⟨11, 2, 0, 1293895, 92644, 2089, 262144⟩
    (by decide) selected_cut_46405

theorem selected_cut_46406 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 92645) = some ⟨11, 1, 0, 892405, 92645, 1, 262144⟩ := by
  decide +kernel

theorem context_11_92645_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92645 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 92645 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 92645, 1, 262144⟩
    (by decide) selected_cut_46406

theorem selected_cut_46407 : selected 10 ⟨1293924, by decide⟩
    (prefixPartial 11 92646) = some ⟨11, 2, 0, 1293924, 92646, 2025, 262144⟩ := by
  decide +kernel

theorem context_11_92646_1293924 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92646 ⟨1293924, by decide⟩ :=
  accepted_of_selected 11 92646 ⟨1293924, by decide⟩ ⟨11, 2, 0, 1293924, 92646, 2025, 262144⟩
    (by decide) selected_cut_46407

theorem selected_cut_46408 : selected 10 ⟨1293935, by decide⟩
    (prefixPartial 11 92647) = some ⟨11, 2, 0, 1293935, 92647, 1177, 262144⟩ := by
  decide +kernel

theorem context_11_92647_1293935 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92647 ⟨1293935, by decide⟩ :=
  accepted_of_selected 11 92647 ⟨1293935, by decide⟩ ⟨11, 2, 0, 1293935, 92647, 1177, 262144⟩
    (by decide) selected_cut_46408

theorem unmarked_context_10_23161_1293936 : frontier 11 ⟨1293936, by decide⟩
    (prefixCache 10 23161) (prefixPartial 10 23161) = false := by
  decide +kernel

theorem node_context_10_23161_1293936 : EJMOriginalGlobalDAGData.nodes 11 ⟨1293936, by decide⟩ =
    .split (coordinate 10) (![⟨1293895, by decide⟩,⟨892405, by decide⟩,⟨1293924, by decide⟩,⟨1293935, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23161_1293936 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23161 ⟨1293936, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23161
    ⟨1293936, by decide⟩ (by decide) (![⟨1293895, by decide⟩,⟨892405, by decide⟩,⟨1293924, by decide⟩,⟨1293935, by decide⟩]) unmarked_context_10_23161_1293936 node_context_10_23161_1293936
  intro a
  fin_cases a
  · exact context_11_92644_1293895
  · exact context_11_92645_892405
  · exact context_11_92646_1293924
  · exact context_11_92647_1293935

theorem selected_cut_46409 : selected 11 ⟨1293956, by decide⟩
    (prefixPartial 10 23162) = some ⟨10, 2, 0, 1293956, 23162, 1653, 1048576⟩ := by
  decide +kernel

theorem context_10_23162_1293956 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23162 ⟨1293956, by decide⟩ :=
  accepted_of_selected 10 23162 ⟨1293956, by decide⟩ ⟨10, 2, 0, 1293956, 23162, 1653, 1048576⟩
    (by decide) selected_cut_46409

theorem selected_cut_46410 : selected 10 ⟨1293978, by decide⟩
    (prefixPartial 11 92652) = some ⟨11, 2, 0, 1293978, 92652, 1645, 262144⟩ := by
  decide +kernel

theorem context_11_92652_1293978 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92652 ⟨1293978, by decide⟩ :=
  accepted_of_selected 11 92652 ⟨1293978, by decide⟩ ⟨11, 2, 0, 1293978, 92652, 1645, 262144⟩
    (by decide) selected_cut_46410

theorem selected_cut_46411 : selected 10 ⟨1293997, by decide⟩
    (prefixPartial 11 92653) = some ⟨11, 2, 0, 1293997, 92653, 1053, 262144⟩ := by
  decide +kernel

theorem context_11_92653_1293997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92653 ⟨1293997, by decide⟩ :=
  accepted_of_selected 11 92653 ⟨1293997, by decide⟩ ⟨11, 2, 0, 1293997, 92653, 1053, 262144⟩
    (by decide) selected_cut_46411

theorem selected_cut_46412 : selected 10 ⟨1294021, by decide⟩
    (prefixPartial 11 92654) = some ⟨11, 2, 0, 1294021, 92654, 1429, 262144⟩ := by
  decide +kernel

theorem context_11_92654_1294021 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92654 ⟨1294021, by decide⟩ :=
  accepted_of_selected 11 92654 ⟨1294021, by decide⟩ ⟨11, 2, 0, 1294021, 92654, 1429, 262144⟩
    (by decide) selected_cut_46412

theorem selected_cut_46413 : selected 10 ⟨1294028, by decide⟩
    (prefixPartial 11 92655) = some ⟨11, 2, 0, 1294028, 92655, 405, 262144⟩ := by
  decide +kernel

theorem context_11_92655_1294028 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92655 ⟨1294028, by decide⟩ :=
  accepted_of_selected 11 92655 ⟨1294028, by decide⟩ ⟨11, 2, 0, 1294028, 92655, 405, 262144⟩
    (by decide) selected_cut_46413

theorem unmarked_context_10_23163_1294029 : frontier 11 ⟨1294029, by decide⟩
    (prefixCache 10 23163) (prefixPartial 10 23163) = false := by
  decide +kernel

theorem node_context_10_23163_1294029 : EJMOriginalGlobalDAGData.nodes 11 ⟨1294029, by decide⟩ =
    .split (coordinate 10) (![⟨1293978, by decide⟩,⟨1293997, by decide⟩,⟨1294021, by decide⟩,⟨1294028, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23163_1294029 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23163 ⟨1294029, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23163
    ⟨1294029, by decide⟩ (by decide) (![⟨1293978, by decide⟩,⟨1293997, by decide⟩,⟨1294021, by decide⟩,⟨1294028, by decide⟩]) unmarked_context_10_23163_1294029 node_context_10_23163_1294029
  intro a
  fin_cases a
  · exact context_11_92652_1293978
  · exact context_11_92653_1293997
  · exact context_11_92654_1294021
  · exact context_11_92655_1294028

theorem unmarked_context_9_5790_1294030 : frontier 12 ⟨1294030, by decide⟩
    (prefixCache 9 5790) (prefixPartial 9 5790) = false := by
  decide +kernel

theorem node_context_9_5790_1294030 : EJMOriginalGlobalDAGData.nodes 12 ⟨1294030, by decide⟩ =
    .split (coordinate 9) (![⟨1293867, by decide⟩,⟨1293936, by decide⟩,⟨1293956, by decide⟩,⟨1294029, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5790_1294030 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5790 ⟨1294030, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5790
    ⟨1294030, by decide⟩ (by decide) (![⟨1293867, by decide⟩,⟨1293936, by decide⟩,⟨1293956, by decide⟩,⟨1294029, by decide⟩]) unmarked_context_9_5790_1294030 node_context_9_5790_1294030
  intro a
  fin_cases a
  · exact context_10_23160_1293867
  · exact context_10_23161_1293936
  · exact context_10_23162_1293956
  · exact context_10_23163_1294029

theorem selected_cut_46414 : selected 11 ⟨1294089, by decide⟩
    (prefixPartial 10 23164) = some ⟨10, 2, 0, 1294089, 23164, 3465, 1048576⟩ := by
  decide +kernel

theorem context_10_23164_1294089 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23164 ⟨1294089, by decide⟩ :=
  accepted_of_selected 10 23164 ⟨1294089, by decide⟩ ⟨10, 2, 0, 1294089, 23164, 3465, 1048576⟩
    (by decide) selected_cut_46414

theorem selected_cut_46415 : selected 11 ⟨1294126, by decide⟩
    (prefixPartial 10 23165) = some ⟨10, 2, 0, 1294126, 23165, 1925, 1048576⟩ := by
  decide +kernel

theorem context_10_23165_1294126 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23165 ⟨1294126, by decide⟩ :=
  accepted_of_selected 10 23165 ⟨1294126, by decide⟩ ⟨10, 2, 0, 1294126, 23165, 1925, 1048576⟩
    (by decide) selected_cut_46415

theorem selected_cut_46416 : selected 11 ⟨1294162, by decide⟩
    (prefixPartial 10 23166) = some ⟨10, 2, 0, 1294162, 23166, 1181, 1048576⟩ := by
  decide +kernel

theorem context_10_23166_1294162 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23166 ⟨1294162, by decide⟩ :=
  accepted_of_selected 10 23166 ⟨1294162, by decide⟩ ⟨10, 2, 0, 1294162, 23166, 1181, 1048576⟩
    (by decide) selected_cut_46416

theorem selected_cut_46417 : selected 11 ⟨1294175, by decide⟩
    (prefixPartial 10 23167) = some ⟨10, 2, 0, 1294175, 23167, 121, 1048576⟩ := by
  decide +kernel

theorem context_10_23167_1294175 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23167 ⟨1294175, by decide⟩ :=
  accepted_of_selected 10 23167 ⟨1294175, by decide⟩ ⟨10, 2, 0, 1294175, 23167, 121, 1048576⟩
    (by decide) selected_cut_46417

theorem unmarked_context_9_5791_1294176 : frontier 12 ⟨1294176, by decide⟩
    (prefixCache 9 5791) (prefixPartial 9 5791) = false := by
  decide +kernel

theorem node_context_9_5791_1294176 : EJMOriginalGlobalDAGData.nodes 12 ⟨1294176, by decide⟩ =
    .split (coordinate 9) (![⟨1294089, by decide⟩,⟨1294126, by decide⟩,⟨1294162, by decide⟩,⟨1294175, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5791_1294176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5791 ⟨1294176, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5791
    ⟨1294176, by decide⟩ (by decide) (![⟨1294089, by decide⟩,⟨1294126, by decide⟩,⟨1294162, by decide⟩,⟨1294175, by decide⟩]) unmarked_context_9_5791_1294176 node_context_9_5791_1294176
  intro a
  fin_cases a
  · exact context_10_23164_1294089
  · exact context_10_23165_1294126
  · exact context_10_23166_1294162
  · exact context_10_23167_1294175

theorem unmarked_context_8_1447_1294177 : frontier 13 ⟨1294177, by decide⟩
    (prefixCache 8 1447) (prefixPartial 8 1447) = false := by
  decide +kernel

theorem node_context_8_1447_1294177 : EJMOriginalGlobalDAGData.nodes 13 ⟨1294177, by decide⟩ =
    .split (coordinate 8) (![⟨1292922, by decide⟩,⟨1293732, by decide⟩,⟨1294030, by decide⟩,⟨1294176, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1447_1294177 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1447 ⟨1294177, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1447
    ⟨1294177, by decide⟩ (by decide) (![⟨1292922, by decide⟩,⟨1293732, by decide⟩,⟨1294030, by decide⟩,⟨1294176, by decide⟩]) unmarked_context_8_1447_1294177 node_context_8_1447_1294177
  intro a
  fin_cases a
  · exact context_9_5788_1292922
  · exact context_9_5789_1293732
  · exact context_9_5790_1294030
  · exact context_9_5791_1294176

theorem unmarked_context_7_361_1294178 : frontier 14 ⟨1294178, by decide⟩
    (prefixCache 7 361) (prefixPartial 7 361) = false := by
  decide +kernel

theorem node_context_7_361_1294178 : EJMOriginalGlobalDAGData.nodes 14 ⟨1294178, by decide⟩ =
    .split (coordinate 7) (![⟨1284682, by decide⟩,⟨1287593, by decide⟩,⟨1291003, by decide⟩,⟨1294177, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_361_1294178 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 361 ⟨1294178, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 361
    ⟨1294178, by decide⟩ (by decide) (![⟨1284682, by decide⟩,⟨1287593, by decide⟩,⟨1291003, by decide⟩,⟨1294177, by decide⟩]) unmarked_context_7_361_1294178 node_context_7_361_1294178
  intro a
  fin_cases a
  · exact context_8_1444_1284682
  · exact context_8_1445_1287593
  · exact context_8_1446_1291003
  · exact context_8_1447_1294177

theorem selected_cut_46418 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 92672) = some ⟨11, 1, 0, 434745, 92672, 1, 262144⟩ := by
  decide +kernel

theorem context_11_92672_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92672 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 92672 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 92672, 1, 262144⟩
    (by decide) selected_cut_46418

theorem selected_cut_46419 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 370692) = some ⟨12, 1, 0, 448748, 370692, 1, 65536⟩ := by
  decide +kernel

theorem context_12_370692_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370692 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 370692 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 370692, 1, 65536⟩
    (by decide) selected_cut_46419

theorem selected_cut_46420 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 370693) = some ⟨12, 1, 0, 34034, 370693, 1, 65536⟩ := by
  decide +kernel

theorem context_12_370693_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370693 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 370693 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 370693, 1, 65536⟩
    (by decide) selected_cut_46420

theorem selected_cut_46421 : selected 9 ⟨1294249, by decide⟩
    (prefixPartial 12 370694) = some ⟨12, 2, 0, 1294249, 370694, 1773, 65536⟩ := by
  decide +kernel

theorem context_12_370694_1294249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370694 ⟨1294249, by decide⟩ :=
  accepted_of_selected 12 370694 ⟨1294249, by decide⟩ ⟨12, 2, 0, 1294249, 370694, 1773, 65536⟩
    (by decide) selected_cut_46421

theorem selected_cut_46422 : selected 9 ⟨1294321, by decide⟩
    (prefixPartial 12 370695) = some ⟨12, 2, 0, 1294321, 370695, 3593, 65536⟩ := by
  decide +kernel

theorem context_12_370695_1294321 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370695 ⟨1294321, by decide⟩ :=
  accepted_of_selected 12 370695 ⟨1294321, by decide⟩ ⟨12, 2, 0, 1294321, 370695, 3593, 65536⟩
    (by decide) selected_cut_46422

theorem unmarked_context_11_92673_1294322 : frontier 10 ⟨1294322, by decide⟩
    (prefixCache 11 92673) (prefixPartial 11 92673) = false := by
  decide +kernel

theorem node_context_11_92673_1294322 : EJMOriginalGlobalDAGData.nodes 10 ⟨1294322, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1294249, by decide⟩,⟨1294321, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92673_1294322 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92673 ⟨1294322, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92673
    ⟨1294322, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1294249, by decide⟩,⟨1294321, by decide⟩]) unmarked_context_11_92673_1294322 node_context_11_92673_1294322
  intro a
  fin_cases a
  · exact context_12_370692_448748
  · exact context_12_370693_34034
  · exact context_12_370694_1294249
  · exact context_12_370695_1294321

theorem selected_cut_46423 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 370696) = some ⟨12, 1, 0, 448748, 370696, 1, 65536⟩ := by
  decide +kernel

theorem context_12_370696_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370696 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 370696 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 370696, 1, 65536⟩
    (by decide) selected_cut_46423

theorem selected_cut_46424 : selected 9 ⟨1294406, by decide⟩
    (prefixPartial 12 370697) = some ⟨12, 2, 0, 1294406, 370697, 3629, 65536⟩ := by
  decide +kernel

theorem context_12_370697_1294406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370697 ⟨1294406, by decide⟩ :=
  accepted_of_selected 12 370697 ⟨1294406, by decide⟩ ⟨12, 2, 0, 1294406, 370697, 3629, 65536⟩
    (by decide) selected_cut_46424

theorem selected_cut_46425 : selected 9 ⟨663554, by decide⟩
    (prefixPartial 12 370698) = some ⟨12, 1, 0, 663554, 370698, 1, 65536⟩ := by
  decide +kernel

theorem context_12_370698_663554 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370698 ⟨663554, by decide⟩ :=
  accepted_of_selected 12 370698 ⟨663554, by decide⟩ ⟨12, 1, 0, 663554, 370698, 1, 65536⟩
    (by decide) selected_cut_46425

theorem selected_cut_46426 : selected 9 ⟨1294476, by decide⟩
    (prefixPartial 12 370699) = some ⟨12, 2, 0, 1294476, 370699, 3701, 65536⟩ := by
  decide +kernel

theorem context_12_370699_1294476 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370699 ⟨1294476, by decide⟩ :=
  accepted_of_selected 12 370699 ⟨1294476, by decide⟩ ⟨12, 2, 0, 1294476, 370699, 3701, 65536⟩
    (by decide) selected_cut_46426

theorem unmarked_context_11_92674_1294477 : frontier 10 ⟨1294477, by decide⟩
    (prefixCache 11 92674) (prefixPartial 11 92674) = false := by
  decide +kernel

theorem node_context_11_92674_1294477 : EJMOriginalGlobalDAGData.nodes 10 ⟨1294477, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1294406, by decide⟩,⟨663554, by decide⟩,⟨1294476, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92674_1294477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92674 ⟨1294477, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92674
    ⟨1294477, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1294406, by decide⟩,⟨663554, by decide⟩,⟨1294476, by decide⟩]) unmarked_context_11_92674_1294477 node_context_11_92674_1294477
  intro a
  fin_cases a
  · exact context_12_370696_448748
  · exact context_12_370697_1294406
  · exact context_12_370698_663554
  · exact context_12_370699_1294476

theorem selected_cut_46427 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 370700) = some ⟨12, 1, 0, 448748, 370700, 1, 65536⟩ := by
  decide +kernel

theorem context_12_370700_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370700 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 370700 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 370700, 1, 65536⟩
    (by decide) selected_cut_46427

theorem selected_cut_46428 : selected 9 ⟨1294545, by decide⟩
    (prefixPartial 12 370701) = some ⟨12, 2, 0, 1294545, 370701, 3305, 65536⟩ := by
  decide +kernel

theorem context_12_370701_1294545 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370701 ⟨1294545, by decide⟩ :=
  accepted_of_selected 12 370701 ⟨1294545, by decide⟩ ⟨12, 2, 0, 1294545, 370701, 3305, 65536⟩
    (by decide) selected_cut_46428

theorem selected_cut_46429 : selected 9 ⟨1294594, by decide⟩
    (prefixPartial 12 370702) = some ⟨12, 2, 0, 1294594, 370702, 2833, 65536⟩ := by
  decide +kernel

theorem context_12_370702_1294594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370702 ⟨1294594, by decide⟩ :=
  accepted_of_selected 12 370702 ⟨1294594, by decide⟩ ⟨12, 2, 0, 1294594, 370702, 2833, 65536⟩
    (by decide) selected_cut_46429

theorem selected_cut_46430 : selected 9 ⟨1294595, by decide⟩
    (prefixPartial 12 370703) = some ⟨12, 1, 0, 1294595, 370703, 1, 65536⟩ := by
  decide +kernel

theorem context_12_370703_1294595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370703 ⟨1294595, by decide⟩ :=
  accepted_of_selected 12 370703 ⟨1294595, by decide⟩ ⟨12, 1, 0, 1294595, 370703, 1, 65536⟩
    (by decide) selected_cut_46430

theorem unmarked_context_11_92675_1294596 : frontier 10 ⟨1294596, by decide⟩
    (prefixCache 11 92675) (prefixPartial 11 92675) = false := by
  decide +kernel

theorem node_context_11_92675_1294596 : EJMOriginalGlobalDAGData.nodes 10 ⟨1294596, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1294545, by decide⟩,⟨1294594, by decide⟩,⟨1294595, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92675_1294596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92675 ⟨1294596, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92675
    ⟨1294596, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1294545, by decide⟩,⟨1294594, by decide⟩,⟨1294595, by decide⟩]) unmarked_context_11_92675_1294596 node_context_11_92675_1294596
  intro a
  fin_cases a
  · exact context_12_370700_448748
  · exact context_12_370701_1294545
  · exact context_12_370702_1294594
  · exact context_12_370703_1294595

theorem unmarked_context_10_23168_1294597 : frontier 11 ⟨1294597, by decide⟩
    (prefixCache 10 23168) (prefixPartial 10 23168) = false := by
  decide +kernel

theorem node_context_10_23168_1294597 : EJMOriginalGlobalDAGData.nodes 11 ⟨1294597, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨1294322, by decide⟩,⟨1294477, by decide⟩,⟨1294596, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23168_1294597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23168 ⟨1294597, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23168
    ⟨1294597, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨1294322, by decide⟩,⟨1294477, by decide⟩,⟨1294596, by decide⟩]) unmarked_context_10_23168_1294597 node_context_10_23168_1294597
  intro a
  fin_cases a
  · exact context_11_92672_434745
  · exact context_11_92673_1294322
  · exact context_11_92674_1294477
  · exact context_11_92675_1294596

theorem selected_cut_46431 : selected 9 ⟨985390, by decide⟩
    (prefixPartial 12 370704) = some ⟨12, 1, 0, 985390, 370704, 1, 65536⟩ := by
  decide +kernel

theorem context_12_370704_985390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370704 ⟨985390, by decide⟩ :=
  accepted_of_selected 12 370704 ⟨985390, by decide⟩ ⟨12, 1, 0, 985390, 370704, 1, 65536⟩
    (by decide) selected_cut_46431

theorem selected_cut_46432 : selected 9 ⟨1294643, by decide⟩
    (prefixPartial 12 370705) = some ⟨12, 2, 0, 1294643, 370705, 2865, 65536⟩ := by
  decide +kernel

theorem context_12_370705_1294643 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370705 ⟨1294643, by decide⟩ :=
  accepted_of_selected 12 370705 ⟨1294643, by decide⟩ ⟨12, 2, 0, 1294643, 370705, 2865, 65536⟩
    (by decide) selected_cut_46432

theorem selected_cut_46433 : selected 9 ⟨1294678, by decide⟩
    (prefixPartial 12 370706) = some ⟨12, 2, 0, 1294678, 370706, 2349, 65536⟩ := by
  decide +kernel

theorem context_12_370706_1294678 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370706 ⟨1294678, by decide⟩ :=
  accepted_of_selected 12 370706 ⟨1294678, by decide⟩ ⟨12, 2, 0, 1294678, 370706, 2349, 65536⟩
    (by decide) selected_cut_46433

theorem selected_cut_46434 : selected 9 ⟨1294728, by decide⟩
    (prefixPartial 12 370707) = some ⟨12, 2, 0, 1294728, 370707, 2945, 65536⟩ := by
  decide +kernel

theorem context_12_370707_1294728 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370707 ⟨1294728, by decide⟩ :=
  accepted_of_selected 12 370707 ⟨1294728, by decide⟩ ⟨12, 2, 0, 1294728, 370707, 2945, 65536⟩
    (by decide) selected_cut_46434

theorem unmarked_context_11_92676_1294729 : frontier 10 ⟨1294729, by decide⟩
    (prefixCache 11 92676) (prefixPartial 11 92676) = false := by
  decide +kernel

theorem node_context_11_92676_1294729 : EJMOriginalGlobalDAGData.nodes 10 ⟨1294729, by decide⟩ =
    .split (coordinate 11) (![⟨985390, by decide⟩,⟨1294643, by decide⟩,⟨1294678, by decide⟩,⟨1294728, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92676_1294729 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92676 ⟨1294729, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92676
    ⟨1294729, by decide⟩ (by decide) (![⟨985390, by decide⟩,⟨1294643, by decide⟩,⟨1294678, by decide⟩,⟨1294728, by decide⟩]) unmarked_context_11_92676_1294729 node_context_11_92676_1294729
  intro a
  fin_cases a
  · exact context_12_370704_985390
  · exact context_12_370705_1294643
  · exact context_12_370706_1294678
  · exact context_12_370707_1294728

theorem selected_cut_46435 : selected 9 ⟨1294797, by decide⟩
    (prefixPartial 12 370708) = some ⟨12, 2, 0, 1294797, 370708, 3013, 65536⟩ := by
  decide +kernel

theorem context_12_370708_1294797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370708 ⟨1294797, by decide⟩ :=
  accepted_of_selected 12 370708 ⟨1294797, by decide⟩ ⟨12, 2, 0, 1294797, 370708, 3013, 65536⟩
    (by decide) selected_cut_46435

theorem selected_cut_46436 : selected 9 ⟨1118965, by decide⟩
    (prefixPartial 12 370709) = some ⟨12, 1, 0, 1118965, 370709, 1, 65536⟩ := by
  decide +kernel

theorem context_12_370709_1118965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370709 ⟨1118965, by decide⟩ :=
  accepted_of_selected 12 370709 ⟨1118965, by decide⟩ ⟨12, 1, 0, 1118965, 370709, 1, 65536⟩
    (by decide) selected_cut_46436

theorem selected_cut_46437 : selected 9 ⟨928104, by decide⟩
    (prefixPartial 12 370710) = some ⟨12, 1, 0, 928104, 370710, 1, 65536⟩ := by
  decide +kernel

theorem context_12_370710_928104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370710 ⟨928104, by decide⟩ :=
  accepted_of_selected 12 370710 ⟨928104, by decide⟩ ⟨12, 1, 0, 928104, 370710, 1, 65536⟩
    (by decide) selected_cut_46437

theorem selected_cut_46438 : selected 9 ⟨1294873, by decide⟩
    (prefixPartial 12 370711) = some ⟨12, 2, 0, 1294873, 370711, 3489, 65536⟩ := by
  decide +kernel

theorem context_12_370711_1294873 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370711 ⟨1294873, by decide⟩ :=
  accepted_of_selected 12 370711 ⟨1294873, by decide⟩ ⟨12, 2, 0, 1294873, 370711, 3489, 65536⟩
    (by decide) selected_cut_46438

theorem unmarked_context_11_92677_1294874 : frontier 10 ⟨1294874, by decide⟩
    (prefixCache 11 92677) (prefixPartial 11 92677) = false := by
  decide +kernel

theorem node_context_11_92677_1294874 : EJMOriginalGlobalDAGData.nodes 10 ⟨1294874, by decide⟩ =
    .split (coordinate 11) (![⟨1294797, by decide⟩,⟨1118965, by decide⟩,⟨928104, by decide⟩,⟨1294873, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92677_1294874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92677 ⟨1294874, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92677
    ⟨1294874, by decide⟩ (by decide) (![⟨1294797, by decide⟩,⟨1118965, by decide⟩,⟨928104, by decide⟩,⟨1294873, by decide⟩]) unmarked_context_11_92677_1294874 node_context_11_92677_1294874
  intro a
  fin_cases a
  · exact context_12_370708_1294797
  · exact context_12_370709_1118965
  · exact context_12_370710_928104
  · exact context_12_370711_1294873

theorem selected_cut_46439 : selected 9 ⟨994572, by decide⟩
    (prefixPartial 12 370712) = some ⟨12, 1, 0, 994572, 370712, 1, 65536⟩ := by
  decide +kernel

theorem context_12_370712_994572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370712 ⟨994572, by decide⟩ :=
  accepted_of_selected 12 370712 ⟨994572, by decide⟩ ⟨12, 1, 0, 994572, 370712, 1, 65536⟩
    (by decide) selected_cut_46439

theorem selected_cut_46440 : selected 9 ⟨1294919, by decide⟩
    (prefixPartial 12 370713) = some ⟨12, 2, 0, 1294919, 370713, 3025, 65536⟩ := by
  decide +kernel

theorem context_12_370713_1294919 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370713 ⟨1294919, by decide⟩ :=
  accepted_of_selected 12 370713 ⟨1294919, by decide⟩ ⟨12, 2, 0, 1294919, 370713, 3025, 65536⟩
    (by decide) selected_cut_46440

theorem selected_cut_46441 : selected 9 ⟨806997, by decide⟩
    (prefixPartial 12 370714) = some ⟨12, 1, 0, 806997, 370714, 1, 65536⟩ := by
  decide +kernel

theorem context_12_370714_806997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370714 ⟨806997, by decide⟩ :=
  accepted_of_selected 12 370714 ⟨806997, by decide⟩ ⟨12, 1, 0, 806997, 370714, 1, 65536⟩
    (by decide) selected_cut_46441

theorem selected_cut_46442 : selected 9 ⟨1294976, by decide⟩
    (prefixPartial 12 370715) = some ⟨12, 2, 0, 1294976, 370715, 3253, 65536⟩ := by
  decide +kernel

theorem context_12_370715_1294976 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370715 ⟨1294976, by decide⟩ :=
  accepted_of_selected 12 370715 ⟨1294976, by decide⟩ ⟨12, 2, 0, 1294976, 370715, 3253, 65536⟩
    (by decide) selected_cut_46442

theorem unmarked_context_11_92678_1294977 : frontier 10 ⟨1294977, by decide⟩
    (prefixCache 11 92678) (prefixPartial 11 92678) = false := by
  decide +kernel

theorem node_context_11_92678_1294977 : EJMOriginalGlobalDAGData.nodes 10 ⟨1294977, by decide⟩ =
    .split (coordinate 11) (![⟨994572, by decide⟩,⟨1294919, by decide⟩,⟨806997, by decide⟩,⟨1294976, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92678_1294977 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92678 ⟨1294977, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92678
    ⟨1294977, by decide⟩ (by decide) (![⟨994572, by decide⟩,⟨1294919, by decide⟩,⟨806997, by decide⟩,⟨1294976, by decide⟩]) unmarked_context_11_92678_1294977 node_context_11_92678_1294977
  intro a
  fin_cases a
  · exact context_12_370712_994572
  · exact context_12_370713_1294919
  · exact context_12_370714_806997
  · exact context_12_370715_1294976

theorem selected_cut_46443 : selected 9 ⟨1295016, by decide⟩
    (prefixPartial 12 370716) = some ⟨12, 2, 0, 1295016, 370716, 2473, 65536⟩ := by
  decide +kernel

theorem context_12_370716_1295016 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370716 ⟨1295016, by decide⟩ :=
  accepted_of_selected 12 370716 ⟨1295016, by decide⟩ ⟨12, 2, 0, 1295016, 370716, 2473, 65536⟩
    (by decide) selected_cut_46443

theorem selected_cut_46444 : selected 9 ⟨1295060, by decide⟩
    (prefixPartial 12 370717) = some ⟨12, 2, 0, 1295060, 370717, 2833, 65536⟩ := by
  decide +kernel

theorem context_12_370717_1295060 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370717 ⟨1295060, by decide⟩ :=
  accepted_of_selected 12 370717 ⟨1295060, by decide⟩ ⟨12, 2, 0, 1295060, 370717, 2833, 65536⟩
    (by decide) selected_cut_46444

theorem selected_cut_46445 : selected 9 ⟨1295101, by decide⟩
    (prefixPartial 12 370718) = some ⟨12, 2, 0, 1295101, 370718, 2469, 65536⟩ := by
  decide +kernel

theorem context_12_370718_1295101 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370718 ⟨1295101, by decide⟩ :=
  accepted_of_selected 12 370718 ⟨1295101, by decide⟩ ⟨12, 2, 0, 1295101, 370718, 2469, 65536⟩
    (by decide) selected_cut_46445

theorem selected_cut_46446 : selected 9 ⟨1295147, by decide⟩
    (prefixPartial 12 370719) = some ⟨12, 2, 0, 1295147, 370719, 2865, 65536⟩ := by
  decide +kernel

theorem context_12_370719_1295147 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370719 ⟨1295147, by decide⟩ :=
  accepted_of_selected 12 370719 ⟨1295147, by decide⟩ ⟨12, 2, 0, 1295147, 370719, 2865, 65536⟩
    (by decide) selected_cut_46446

theorem unmarked_context_11_92679_1295148 : frontier 10 ⟨1295148, by decide⟩
    (prefixCache 11 92679) (prefixPartial 11 92679) = false := by
  decide +kernel

theorem node_context_11_92679_1295148 : EJMOriginalGlobalDAGData.nodes 10 ⟨1295148, by decide⟩ =
    .split (coordinate 11) (![⟨1295016, by decide⟩,⟨1295060, by decide⟩,⟨1295101, by decide⟩,⟨1295147, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92679_1295148 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92679 ⟨1295148, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92679
    ⟨1295148, by decide⟩ (by decide) (![⟨1295016, by decide⟩,⟨1295060, by decide⟩,⟨1295101, by decide⟩,⟨1295147, by decide⟩]) unmarked_context_11_92679_1295148 node_context_11_92679_1295148
  intro a
  fin_cases a
  · exact context_12_370716_1295016
  · exact context_12_370717_1295060
  · exact context_12_370718_1295101
  · exact context_12_370719_1295147

theorem unmarked_context_10_23169_1295149 : frontier 11 ⟨1295149, by decide⟩
    (prefixCache 10 23169) (prefixPartial 10 23169) = false := by
  decide +kernel

theorem node_context_10_23169_1295149 : EJMOriginalGlobalDAGData.nodes 11 ⟨1295149, by decide⟩ =
    .split (coordinate 10) (![⟨1294729, by decide⟩,⟨1294874, by decide⟩,⟨1294977, by decide⟩,⟨1295148, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23169_1295149 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23169 ⟨1295149, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23169
    ⟨1295149, by decide⟩ (by decide) (![⟨1294729, by decide⟩,⟨1294874, by decide⟩,⟨1294977, by decide⟩,⟨1295148, by decide⟩]) unmarked_context_10_23169_1295149 node_context_10_23169_1295149
  intro a
  fin_cases a
  · exact context_11_92676_1294729
  · exact context_11_92677_1294874
  · exact context_11_92678_1294977
  · exact context_11_92679_1295148

theorem selected_cut_46447 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 370720) = some ⟨12, 1, 0, 435790, 370720, 1, 65536⟩ := by
  decide +kernel

theorem context_12_370720_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370720 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 370720 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 370720, 1, 65536⟩
    (by decide) selected_cut_46447

theorem selected_cut_46448 : selected 9 ⟨1295188, by decide⟩
    (prefixPartial 12 370721) = some ⟨12, 2, 0, 1295188, 370721, 2605, 65536⟩ := by
  decide +kernel

theorem context_12_370721_1295188 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370721 ⟨1295188, by decide⟩ :=
  accepted_of_selected 12 370721 ⟨1295188, by decide⟩ ⟨12, 2, 0, 1295188, 370721, 2605, 65536⟩
    (by decide) selected_cut_46448

theorem selected_cut_46449 : selected 9 ⟨1295225, by decide⟩
    (prefixPartial 12 370722) = some ⟨12, 2, 0, 1295225, 370722, 2265, 65536⟩ := by
  decide +kernel

theorem context_12_370722_1295225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370722 ⟨1295225, by decide⟩ :=
  accepted_of_selected 12 370722 ⟨1295225, by decide⟩ ⟨12, 2, 0, 1295225, 370722, 2265, 65536⟩
    (by decide) selected_cut_46449

theorem selected_cut_46450 : selected 9 ⟨1295266, by decide⟩
    (prefixPartial 12 370723) = some ⟨12, 2, 0, 1295266, 370723, 2617, 65536⟩ := by
  decide +kernel

theorem context_12_370723_1295266 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370723 ⟨1295266, by decide⟩ :=
  accepted_of_selected 12 370723 ⟨1295266, by decide⟩ ⟨12, 2, 0, 1295266, 370723, 2617, 65536⟩
    (by decide) selected_cut_46450

theorem unmarked_context_11_92680_1295267 : frontier 10 ⟨1295267, by decide⟩
    (prefixCache 11 92680) (prefixPartial 11 92680) = false := by
  decide +kernel

theorem node_context_11_92680_1295267 : EJMOriginalGlobalDAGData.nodes 10 ⟨1295267, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨1295188, by decide⟩,⟨1295225, by decide⟩,⟨1295266, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92680_1295267 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92680 ⟨1295267, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92680
    ⟨1295267, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨1295188, by decide⟩,⟨1295225, by decide⟩,⟨1295266, by decide⟩]) unmarked_context_11_92680_1295267 node_context_11_92680_1295267
  intro a
  fin_cases a
  · exact context_12_370720_435790
  · exact context_12_370721_1295188
  · exact context_12_370722_1295225
  · exact context_12_370723_1295266

theorem selected_cut_46451 : selected 9 ⟨450498, by decide⟩
    (prefixPartial 12 370724) = some ⟨12, 1, 0, 450498, 370724, 1, 65536⟩ := by
  decide +kernel

theorem context_12_370724_450498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370724 ⟨450498, by decide⟩ :=
  accepted_of_selected 12 370724 ⟨450498, by decide⟩ ⟨12, 1, 0, 450498, 370724, 1, 65536⟩
    (by decide) selected_cut_46451

theorem selected_cut_46452 : selected 9 ⟨1295331, by decide⟩
    (prefixPartial 12 370725) = some ⟨12, 2, 0, 1295331, 370725, 1857, 65536⟩ := by
  decide +kernel

theorem context_12_370725_1295331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370725 ⟨1295331, by decide⟩ :=
  accepted_of_selected 12 370725 ⟨1295331, by decide⟩ ⟨12, 2, 0, 1295331, 370725, 1857, 65536⟩
    (by decide) selected_cut_46452

theorem selected_cut_46453 : selected 9 ⟨1295381, by decide⟩
    (prefixPartial 12 370726) = some ⟨12, 2, 0, 1295381, 370726, 2761, 65536⟩ := by
  decide +kernel

theorem context_12_370726_1295381 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370726 ⟨1295381, by decide⟩ :=
  accepted_of_selected 12 370726 ⟨1295381, by decide⟩ ⟨12, 2, 0, 1295381, 370726, 2761, 65536⟩
    (by decide) selected_cut_46453

theorem selected_cut_46454 : selected 9 ⟨1295444, by decide⟩
    (prefixPartial 12 370727) = some ⟨12, 2, 0, 1295444, 370727, 3325, 65536⟩ := by
  decide +kernel

theorem context_12_370727_1295444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370727 ⟨1295444, by decide⟩ :=
  accepted_of_selected 12 370727 ⟨1295444, by decide⟩ ⟨12, 2, 0, 1295444, 370727, 3325, 65536⟩
    (by decide) selected_cut_46454

theorem unmarked_context_11_92681_1295445 : frontier 10 ⟨1295445, by decide⟩
    (prefixCache 11 92681) (prefixPartial 11 92681) = false := by
  decide +kernel

theorem node_context_11_92681_1295445 : EJMOriginalGlobalDAGData.nodes 10 ⟨1295445, by decide⟩ =
    .split (coordinate 11) (![⟨450498, by decide⟩,⟨1295331, by decide⟩,⟨1295381, by decide⟩,⟨1295444, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92681_1295445 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92681 ⟨1295445, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92681
    ⟨1295445, by decide⟩ (by decide) (![⟨450498, by decide⟩,⟨1295331, by decide⟩,⟨1295381, by decide⟩,⟨1295444, by decide⟩]) unmarked_context_11_92681_1295445 node_context_11_92681_1295445
  intro a
  fin_cases a
  · exact context_12_370724_450498
  · exact context_12_370725_1295331
  · exact context_12_370726_1295381
  · exact context_12_370727_1295444

theorem selected_cut_46455 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 92682) = some ⟨11, 1, 0, 900587, 92682, 1, 262144⟩ := by
  decide +kernel

theorem context_11_92682_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92682 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 92682 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 92682, 1, 262144⟩
    (by decide) selected_cut_46455

theorem selected_cut_46456 : selected 9 ⟨1295485, by decide⟩
    (prefixPartial 12 370732) = some ⟨12, 2, 0, 1295485, 370732, 2561, 65536⟩ := by
  decide +kernel

theorem context_12_370732_1295485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370732 ⟨1295485, by decide⟩ :=
  accepted_of_selected 12 370732 ⟨1295485, by decide⟩ ⟨12, 2, 0, 1295485, 370732, 2561, 65536⟩
    (by decide) selected_cut_46456

theorem selected_cut_46457 : selected 9 ⟨1295528, by decide⟩
    (prefixPartial 12 370733) = some ⟨12, 2, 0, 1295528, 370733, 2657, 65536⟩ := by
  decide +kernel

theorem context_12_370733_1295528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370733 ⟨1295528, by decide⟩ :=
  accepted_of_selected 12 370733 ⟨1295528, by decide⟩ ⟨12, 2, 0, 1295528, 370733, 2657, 65536⟩
    (by decide) selected_cut_46457

theorem selected_cut_46458 : selected 9 ⟨1295564, by decide⟩
    (prefixPartial 12 370734) = some ⟨12, 2, 0, 1295564, 370734, 2381, 65536⟩ := by
  decide +kernel

theorem context_12_370734_1295564 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370734 ⟨1295564, by decide⟩ :=
  accepted_of_selected 12 370734 ⟨1295564, by decide⟩ ⟨12, 2, 0, 1295564, 370734, 2381, 65536⟩
    (by decide) selected_cut_46458

theorem selected_cut_46459 : selected 9 ⟨1295608, by decide⟩
    (prefixPartial 12 370735) = some ⟨12, 2, 0, 1295608, 370735, 2597, 65536⟩ := by
  decide +kernel

theorem context_12_370735_1295608 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370735 ⟨1295608, by decide⟩ :=
  accepted_of_selected 12 370735 ⟨1295608, by decide⟩ ⟨12, 2, 0, 1295608, 370735, 2597, 65536⟩
    (by decide) selected_cut_46459

theorem unmarked_context_11_92683_1295609 : frontier 10 ⟨1295609, by decide⟩
    (prefixCache 11 92683) (prefixPartial 11 92683) = false := by
  decide +kernel

theorem node_context_11_92683_1295609 : EJMOriginalGlobalDAGData.nodes 10 ⟨1295609, by decide⟩ =
    .split (coordinate 11) (![⟨1295485, by decide⟩,⟨1295528, by decide⟩,⟨1295564, by decide⟩,⟨1295608, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92683_1295609 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92683 ⟨1295609, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92683
    ⟨1295609, by decide⟩ (by decide) (![⟨1295485, by decide⟩,⟨1295528, by decide⟩,⟨1295564, by decide⟩,⟨1295608, by decide⟩]) unmarked_context_11_92683_1295609 node_context_11_92683_1295609
  intro a
  fin_cases a
  · exact context_12_370732_1295485
  · exact context_12_370733_1295528
  · exact context_12_370734_1295564
  · exact context_12_370735_1295608

theorem unmarked_context_10_23170_1295610 : frontier 11 ⟨1295610, by decide⟩
    (prefixCache 10 23170) (prefixPartial 10 23170) = false := by
  decide +kernel

theorem node_context_10_23170_1295610 : EJMOriginalGlobalDAGData.nodes 11 ⟨1295610, by decide⟩ =
    .split (coordinate 10) (![⟨1295267, by decide⟩,⟨1295445, by decide⟩,⟨900587, by decide⟩,⟨1295609, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23170_1295610 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23170 ⟨1295610, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23170
    ⟨1295610, by decide⟩ (by decide) (![⟨1295267, by decide⟩,⟨1295445, by decide⟩,⟨900587, by decide⟩,⟨1295609, by decide⟩]) unmarked_context_10_23170_1295610 node_context_10_23170_1295610
  intro a
  fin_cases a
  · exact context_11_92680_1295267
  · exact context_11_92681_1295445
  · exact context_11_92682_900587
  · exact context_11_92683_1295609

theorem selected_cut_46460 : selected 9 ⟨985390, by decide⟩
    (prefixPartial 12 370736) = some ⟨12, 1, 0, 985390, 370736, 1, 65536⟩ := by
  decide +kernel

theorem context_12_370736_985390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370736 ⟨985390, by decide⟩ :=
  accepted_of_selected 12 370736 ⟨985390, by decide⟩ ⟨12, 1, 0, 985390, 370736, 1, 65536⟩
    (by decide) selected_cut_46460

theorem selected_cut_46461 : selected 9 ⟨1295645, by decide⟩
    (prefixPartial 12 370737) = some ⟨12, 2, 0, 1295645, 370737, 2237, 65536⟩ := by
  decide +kernel

theorem context_12_370737_1295645 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370737 ⟨1295645, by decide⟩ :=
  accepted_of_selected 12 370737 ⟨1295645, by decide⟩ ⟨12, 2, 0, 1295645, 370737, 2237, 65536⟩
    (by decide) selected_cut_46461

theorem selected_cut_46462 : selected 9 ⟨1295681, by decide⟩
    (prefixPartial 12 370738) = some ⟨12, 2, 0, 1295681, 370738, 2117, 65536⟩ := by
  decide +kernel

theorem context_12_370738_1295681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370738 ⟨1295681, by decide⟩ :=
  accepted_of_selected 12 370738 ⟨1295681, by decide⟩ ⟨12, 2, 0, 1295681, 370738, 2117, 65536⟩
    (by decide) selected_cut_46462

theorem selected_cut_46463 : selected 9 ⟨1295720, by decide⟩
    (prefixPartial 12 370739) = some ⟨12, 2, 0, 1295720, 370739, 2457, 65536⟩ := by
  decide +kernel

theorem context_12_370739_1295720 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370739 ⟨1295720, by decide⟩ :=
  accepted_of_selected 12 370739 ⟨1295720, by decide⟩ ⟨12, 2, 0, 1295720, 370739, 2457, 65536⟩
    (by decide) selected_cut_46463

theorem unmarked_context_11_92684_1295721 : frontier 10 ⟨1295721, by decide⟩
    (prefixCache 11 92684) (prefixPartial 11 92684) = false := by
  decide +kernel

theorem node_context_11_92684_1295721 : EJMOriginalGlobalDAGData.nodes 10 ⟨1295721, by decide⟩ =
    .split (coordinate 11) (![⟨985390, by decide⟩,⟨1295645, by decide⟩,⟨1295681, by decide⟩,⟨1295720, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92684_1295721 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92684 ⟨1295721, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92684
    ⟨1295721, by decide⟩ (by decide) (![⟨985390, by decide⟩,⟨1295645, by decide⟩,⟨1295681, by decide⟩,⟨1295720, by decide⟩]) unmarked_context_11_92684_1295721 node_context_11_92684_1295721
  intro a
  fin_cases a
  · exact context_12_370736_985390
  · exact context_12_370737_1295645
  · exact context_12_370738_1295681
  · exact context_12_370739_1295720

theorem selected_cut_46464 : selected 9 ⟨1295767, by decide⟩
    (prefixPartial 12 370740) = some ⟨12, 2, 0, 1295767, 370740, 2685, 65536⟩ := by
  decide +kernel

theorem context_12_370740_1295767 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370740 ⟨1295767, by decide⟩ :=
  accepted_of_selected 12 370740 ⟨1295767, by decide⟩ ⟨12, 2, 0, 1295767, 370740, 2685, 65536⟩
    (by decide) selected_cut_46464

theorem selected_cut_46465 : selected 9 ⟨1295803, by decide⟩
    (prefixPartial 12 370741) = some ⟨12, 2, 0, 1295803, 370741, 2437, 65536⟩ := by
  decide +kernel

theorem context_12_370741_1295803 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370741 ⟨1295803, by decide⟩ :=
  accepted_of_selected 12 370741 ⟨1295803, by decide⟩ ⟨12, 2, 0, 1295803, 370741, 2437, 65536⟩
    (by decide) selected_cut_46465

theorem selected_cut_46466 : selected 9 ⟨1295844, by decide⟩
    (prefixPartial 12 370742) = some ⟨12, 2, 0, 1295844, 370742, 2381, 65536⟩ := by
  decide +kernel

theorem context_12_370742_1295844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370742 ⟨1295844, by decide⟩ :=
  accepted_of_selected 12 370742 ⟨1295844, by decide⟩ ⟨12, 2, 0, 1295844, 370742, 2381, 65536⟩
    (by decide) selected_cut_46466

theorem selected_cut_46467 : selected 9 ⟨1295894, by decide⟩
    (prefixPartial 12 370743) = some ⟨12, 2, 0, 1295894, 370743, 2901, 65536⟩ := by
  decide +kernel

theorem context_12_370743_1295894 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370743 ⟨1295894, by decide⟩ :=
  accepted_of_selected 12 370743 ⟨1295894, by decide⟩ ⟨12, 2, 0, 1295894, 370743, 2901, 65536⟩
    (by decide) selected_cut_46467

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
