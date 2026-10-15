/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover534
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_9_17549_1480454 : frontier 12 ⟨1480454, by decide⟩
    (prefixCache 9 17549) (prefixPartial 9 17549) = false := by
  decide +kernel

theorem node_context_9_17549_1480454 : EJMOriginalGlobalDAGData.nodes 12 ⟨1480454, by decide⟩ =
    .split (coordinate 9) (![⟨1480216, by decide⟩,⟨1468874, by decide⟩,⟨1480343, by decide⟩,⟨1480453, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17549_1480454 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17549 ⟨1480454, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17549
    ⟨1480454, by decide⟩ (by decide) (![⟨1480216, by decide⟩,⟨1468874, by decide⟩,⟨1480343, by decide⟩,⟨1480453, by decide⟩]) unmarked_context_9_17549_1480454 node_context_9_17549_1480454
  intro a
  fin_cases a
  · exact context_10_70196_1480216
  · exact context_10_70197_1468874
  · exact context_10_70198_1480343
  · exact context_10_70199_1480453

theorem selected_cut_51363 : selected 11 ⟨1480510, by decide⟩
    (prefixPartial 10 70200) = some ⟨10, 2, 0, 1480510, 70200, 2213, 1048576⟩ := by
  decide +kernel

theorem context_10_70200_1480510 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70200 ⟨1480510, by decide⟩ :=
  accepted_of_selected 10 70200 ⟨1480510, by decide⟩ ⟨10, 2, 0, 1480510, 70200, 2213, 1048576⟩
    (by decide) selected_cut_51363

theorem selected_cut_51364 : selected 11 ⟨1480608, by decide⟩
    (prefixPartial 10 70201) = some ⟨10, 2, 0, 1480608, 70201, 4057, 1048576⟩ := by
  decide +kernel

theorem context_10_70201_1480608 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70201 ⟨1480608, by decide⟩ :=
  accepted_of_selected 10 70201 ⟨1480608, by decide⟩ ⟨10, 2, 0, 1480608, 70201, 4057, 1048576⟩
    (by decide) selected_cut_51364

theorem selected_cut_51365 : selected 11 ⟨1469103, by decide⟩
    (prefixPartial 10 70202) = some ⟨10, 1, 0, 1469103, 70202, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_70202_1469103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70202 ⟨1469103, by decide⟩ :=
  accepted_of_selected 10 70202 ⟨1469103, by decide⟩ ⟨10, 1, 0, 1469103, 70202, 1, 1048576⟩
    (by decide) selected_cut_51365

theorem selected_cut_51366 : selected 11 ⟨1480677, by decide⟩
    (prefixPartial 10 70203) = some ⟨10, 2, 0, 1480677, 70203, 2689, 1048576⟩ := by
  decide +kernel

theorem context_10_70203_1480677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70203 ⟨1480677, by decide⟩ :=
  accepted_of_selected 10 70203 ⟨1480677, by decide⟩ ⟨10, 2, 0, 1480677, 70203, 2689, 1048576⟩
    (by decide) selected_cut_51366

theorem unmarked_context_9_17550_1480678 : frontier 12 ⟨1480678, by decide⟩
    (prefixCache 9 17550) (prefixPartial 9 17550) = false := by
  decide +kernel

theorem node_context_9_17550_1480678 : EJMOriginalGlobalDAGData.nodes 12 ⟨1480678, by decide⟩ =
    .split (coordinate 9) (![⟨1480510, by decide⟩,⟨1480608, by decide⟩,⟨1469103, by decide⟩,⟨1480677, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17550_1480678 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17550 ⟨1480678, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17550
    ⟨1480678, by decide⟩ (by decide) (![⟨1480510, by decide⟩,⟨1480608, by decide⟩,⟨1469103, by decide⟩,⟨1480677, by decide⟩]) unmarked_context_9_17550_1480678 node_context_9_17550_1480678
  intro a
  fin_cases a
  · exact context_10_70200_1480510
  · exact context_10_70201_1480608
  · exact context_10_70202_1469103
  · exact context_10_70203_1480677

theorem selected_cut_51367 : selected 12 ⟨1480754, by decide⟩
    (prefixPartial 9 17551) = some ⟨9, 2, 0, 1480754, 17551, 2365, 4194304⟩ := by
  decide +kernel

theorem context_9_17551_1480754 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17551 ⟨1480754, by decide⟩ :=
  accepted_of_selected 9 17551 ⟨1480754, by decide⟩ ⟨9, 2, 0, 1480754, 17551, 2365, 4194304⟩
    (by decide) selected_cut_51367

theorem unmarked_context_8_4387_1480755 : frontier 13 ⟨1480755, by decide⟩
    (prefixCache 8 4387) (prefixPartial 8 4387) = false := by
  decide +kernel

theorem node_context_8_4387_1480755 : EJMOriginalGlobalDAGData.nodes 13 ⟨1480755, by decide⟩ =
    .split (coordinate 8) (![⟨1480144, by decide⟩,⟨1480454, by decide⟩,⟨1480678, by decide⟩,⟨1480754, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4387_1480755 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4387 ⟨1480755, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4387
    ⟨1480755, by decide⟩ (by decide) (![⟨1480144, by decide⟩,⟨1480454, by decide⟩,⟨1480678, by decide⟩,⟨1480754, by decide⟩]) unmarked_context_8_4387_1480755 node_context_8_4387_1480755
  intro a
  fin_cases a
  · exact context_9_17548_1480144
  · exact context_9_17549_1480454
  · exact context_9_17550_1480678
  · exact context_9_17551_1480754

theorem unmarked_context_7_1096_1480756 : frontier 14 ⟨1480756, by decide⟩
    (prefixCache 7 1096) (prefixPartial 7 1096) = false := by
  decide +kernel

theorem node_context_7_1096_1480756 : EJMOriginalGlobalDAGData.nodes 14 ⟨1480756, by decide⟩ =
    .split (coordinate 7) (![⟨1477358, by decide⟩,⟨1478495, by decide⟩,⟨1479614, by decide⟩,⟨1480755, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_1096_1480756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 1096 ⟨1480756, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 1096
    ⟨1480756, by decide⟩ (by decide) (![⟨1477358, by decide⟩,⟨1478495, by decide⟩,⟨1479614, by decide⟩,⟨1480755, by decide⟩]) unmarked_context_7_1096_1480756 node_context_7_1096_1480756
  intro a
  fin_cases a
  · exact context_8_4384_1477358
  · exact context_8_4385_1478495
  · exact context_8_4386_1479614
  · exact context_8_4387_1480755

theorem selected_cut_51368 : selected 13 ⟨14300, by decide⟩
    (prefixPartial 8 4388) = some ⟨8, 1, 0, 14300, 4388, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_4388_14300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4388 ⟨14300, by decide⟩ :=
  accepted_of_selected 8 4388 ⟨14300, by decide⟩ ⟨8, 1, 0, 14300, 4388, 1, 16777216⟩
    (by decide) selected_cut_51368

theorem selected_cut_51369 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 70224) = some ⟨10, 1, 0, 1468246, 70224, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_70224_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70224 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 70224 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 70224, 1, 1048576⟩
    (by decide) selected_cut_51369

theorem selected_cut_51370 : selected 10 ⟨1480817, by decide⟩
    (prefixPartial 11 280900) = some ⟨11, 2, 0, 1480817, 280900, 2677, 262144⟩ := by
  decide +kernel

theorem context_11_280900_1480817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280900 ⟨1480817, by decide⟩ :=
  accepted_of_selected 11 280900 ⟨1480817, by decide⟩ ⟨11, 2, 0, 1480817, 280900, 2677, 262144⟩
    (by decide) selected_cut_51370

theorem selected_cut_51371 : selected 10 ⟨1468419, by decide⟩
    (prefixPartial 11 280901) = some ⟨11, 1, 0, 1468419, 280901, 1, 262144⟩ := by
  decide +kernel

theorem context_11_280901_1468419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280901 ⟨1468419, by decide⟩ :=
  accepted_of_selected 11 280901 ⟨1468419, by decide⟩ ⟨11, 1, 0, 1468419, 280901, 1, 262144⟩
    (by decide) selected_cut_51371

theorem selected_cut_51372 : selected 10 ⟨1480886, by decide⟩
    (prefixPartial 11 280902) = some ⟨11, 2, 0, 1480886, 280902, 2521, 262144⟩ := by
  decide +kernel

theorem context_11_280902_1480886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280902 ⟨1480886, by decide⟩ :=
  accepted_of_selected 11 280902 ⟨1480886, by decide⟩ ⟨11, 2, 0, 1480886, 280902, 2521, 262144⟩
    (by decide) selected_cut_51372

theorem selected_cut_51373 : selected 10 ⟨1480939, by decide⟩
    (prefixPartial 11 280903) = some ⟨11, 2, 0, 1480939, 280903, 1797, 262144⟩ := by
  decide +kernel

theorem context_11_280903_1480939 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280903 ⟨1480939, by decide⟩ :=
  accepted_of_selected 11 280903 ⟨1480939, by decide⟩ ⟨11, 2, 0, 1480939, 280903, 1797, 262144⟩
    (by decide) selected_cut_51373

theorem unmarked_context_10_70225_1480940 : frontier 11 ⟨1480940, by decide⟩
    (prefixCache 10 70225) (prefixPartial 10 70225) = false := by
  decide +kernel

theorem node_context_10_70225_1480940 : EJMOriginalGlobalDAGData.nodes 11 ⟨1480940, by decide⟩ =
    .split (coordinate 10) (![⟨1480817, by decide⟩,⟨1468419, by decide⟩,⟨1480886, by decide⟩,⟨1480939, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_70225_1480940 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70225 ⟨1480940, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 70225
    ⟨1480940, by decide⟩ (by decide) (![⟨1480817, by decide⟩,⟨1468419, by decide⟩,⟨1480886, by decide⟩,⟨1480939, by decide⟩]) unmarked_context_10_70225_1480940 node_context_10_70225_1480940
  intro a
  fin_cases a
  · exact context_11_280900_1480817
  · exact context_11_280901_1468419
  · exact context_11_280902_1480886
  · exact context_11_280903_1480939

theorem selected_cut_51374 : selected 11 ⟨1481054, by decide⟩
    (prefixPartial 10 70226) = some ⟨10, 2, 0, 1481054, 70226, 4005, 1048576⟩ := by
  decide +kernel

theorem context_10_70226_1481054 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70226 ⟨1481054, by decide⟩ :=
  accepted_of_selected 10 70226 ⟨1481054, by decide⟩ ⟨10, 2, 0, 1481054, 70226, 4005, 1048576⟩
    (by decide) selected_cut_51374

theorem selected_cut_51375 : selected 11 ⟨1481134, by decide⟩
    (prefixPartial 10 70227) = some ⟨10, 2, 0, 1481134, 70227, 1969, 1048576⟩ := by
  decide +kernel

theorem context_10_70227_1481134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70227 ⟨1481134, by decide⟩ :=
  accepted_of_selected 10 70227 ⟨1481134, by decide⟩ ⟨10, 2, 0, 1481134, 70227, 1969, 1048576⟩
    (by decide) selected_cut_51375

theorem unmarked_context_9_17556_1481135 : frontier 12 ⟨1481135, by decide⟩
    (prefixCache 9 17556) (prefixPartial 9 17556) = false := by
  decide +kernel

theorem node_context_9_17556_1481135 : EJMOriginalGlobalDAGData.nodes 12 ⟨1481135, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1480940, by decide⟩,⟨1481054, by decide⟩,⟨1481134, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17556_1481135 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17556 ⟨1481135, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17556
    ⟨1481135, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1480940, by decide⟩,⟨1481054, by decide⟩,⟨1481134, by decide⟩]) unmarked_context_9_17556_1481135 node_context_9_17556_1481135
  intro a
  fin_cases a
  · exact context_10_70224_1468246
  · exact context_10_70225_1480940
  · exact context_10_70226_1481054
  · exact context_10_70227_1481134

theorem selected_cut_51376 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 280912) = some ⟨11, 1, 0, 434745, 280912, 1, 262144⟩ := by
  decide +kernel

theorem context_11_280912_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280912 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 280912 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 280912, 1, 262144⟩
    (by decide) selected_cut_51376

theorem selected_cut_51377 : selected 10 ⟨1481169, by decide⟩
    (prefixPartial 11 280913) = some ⟨11, 2, 0, 1481169, 280913, 1433, 262144⟩ := by
  decide +kernel

theorem context_11_280913_1481169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280913 ⟨1481169, by decide⟩ :=
  accepted_of_selected 11 280913 ⟨1481169, by decide⟩ ⟨11, 2, 0, 1481169, 280913, 1433, 262144⟩
    (by decide) selected_cut_51377

theorem selected_cut_51378 : selected 10 ⟨1481209, by decide⟩
    (prefixPartial 11 280914) = some ⟨11, 2, 0, 1481209, 280914, 1585, 262144⟩ := by
  decide +kernel

theorem context_11_280914_1481209 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280914 ⟨1481209, by decide⟩ :=
  accepted_of_selected 11 280914 ⟨1481209, by decide⟩ ⟨11, 2, 0, 1481209, 280914, 1585, 262144⟩
    (by decide) selected_cut_51378

theorem selected_cut_51379 : selected 10 ⟨1481250, by decide⟩
    (prefixPartial 11 280915) = some ⟨11, 2, 0, 1481250, 280915, 1569, 262144⟩ := by
  decide +kernel

theorem context_11_280915_1481250 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280915 ⟨1481250, by decide⟩ :=
  accepted_of_selected 11 280915 ⟨1481250, by decide⟩ ⟨11, 2, 0, 1481250, 280915, 1569, 262144⟩
    (by decide) selected_cut_51379

theorem unmarked_context_10_70228_1481251 : frontier 11 ⟨1481251, by decide⟩
    (prefixCache 10 70228) (prefixPartial 10 70228) = false := by
  decide +kernel

theorem node_context_10_70228_1481251 : EJMOriginalGlobalDAGData.nodes 11 ⟨1481251, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨1481169, by decide⟩,⟨1481209, by decide⟩,⟨1481250, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_70228_1481251 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70228 ⟨1481251, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 70228
    ⟨1481251, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨1481169, by decide⟩,⟨1481209, by decide⟩,⟨1481250, by decide⟩]) unmarked_context_10_70228_1481251 node_context_10_70228_1481251
  intro a
  fin_cases a
  · exact context_11_280912_434745
  · exact context_11_280913_1481169
  · exact context_11_280914_1481209
  · exact context_11_280915_1481250

theorem selected_cut_51380 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 70229) = some ⟨10, 1, 0, 1468874, 70229, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_70229_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70229 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 70229 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 70229, 1, 1048576⟩
    (by decide) selected_cut_51380

theorem selected_cut_51381 : selected 11 ⟨1481347, by decide⟩
    (prefixPartial 10 70230) = some ⟨10, 2, 0, 1481347, 70230, 2913, 1048576⟩ := by
  decide +kernel

theorem context_10_70230_1481347 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70230 ⟨1481347, by decide⟩ :=
  accepted_of_selected 10 70230 ⟨1481347, by decide⟩ ⟨10, 2, 0, 1481347, 70230, 2913, 1048576⟩
    (by decide) selected_cut_51381

theorem selected_cut_51382 : selected 11 ⟨1481394, by decide⟩
    (prefixPartial 10 70231) = some ⟨10, 2, 0, 1481394, 70231, 1245, 1048576⟩ := by
  decide +kernel

theorem context_10_70231_1481394 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70231 ⟨1481394, by decide⟩ :=
  accepted_of_selected 10 70231 ⟨1481394, by decide⟩ ⟨10, 2, 0, 1481394, 70231, 1245, 1048576⟩
    (by decide) selected_cut_51382

theorem unmarked_context_9_17557_1481395 : frontier 12 ⟨1481395, by decide⟩
    (prefixCache 9 17557) (prefixPartial 9 17557) = false := by
  decide +kernel

theorem node_context_9_17557_1481395 : EJMOriginalGlobalDAGData.nodes 12 ⟨1481395, by decide⟩ =
    .split (coordinate 9) (![⟨1481251, by decide⟩,⟨1468874, by decide⟩,⟨1481347, by decide⟩,⟨1481394, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17557_1481395 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17557 ⟨1481395, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17557
    ⟨1481395, by decide⟩ (by decide) (![⟨1481251, by decide⟩,⟨1468874, by decide⟩,⟨1481347, by decide⟩,⟨1481394, by decide⟩]) unmarked_context_9_17557_1481395 node_context_9_17557_1481395
  intro a
  fin_cases a
  · exact context_10_70228_1481251
  · exact context_10_70229_1468874
  · exact context_10_70230_1481347
  · exact context_10_70231_1481394

theorem selected_cut_51383 : selected 11 ⟨1481477, by decide⟩
    (prefixPartial 10 70232) = some ⟨10, 2, 0, 1481477, 70232, 3393, 1048576⟩ := by
  decide +kernel

theorem context_10_70232_1481477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70232 ⟨1481477, by decide⟩ :=
  accepted_of_selected 10 70232 ⟨1481477, by decide⟩ ⟨10, 2, 0, 1481477, 70232, 3393, 1048576⟩
    (by decide) selected_cut_51383

theorem selected_cut_51384 : selected 11 ⟨1481528, by decide⟩
    (prefixPartial 10 70233) = some ⟨10, 2, 0, 1481528, 70233, 1729, 1048576⟩ := by
  decide +kernel

theorem context_10_70233_1481528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70233 ⟨1481528, by decide⟩ :=
  accepted_of_selected 10 70233 ⟨1481528, by decide⟩ ⟨10, 2, 0, 1481528, 70233, 1729, 1048576⟩
    (by decide) selected_cut_51384

theorem selected_cut_51385 : selected 11 ⟨1469103, by decide⟩
    (prefixPartial 10 70234) = some ⟨10, 1, 0, 1469103, 70234, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_70234_1469103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70234 ⟨1469103, by decide⟩ :=
  accepted_of_selected 10 70234 ⟨1469103, by decide⟩ ⟨10, 1, 0, 1469103, 70234, 1, 1048576⟩
    (by decide) selected_cut_51385

theorem selected_cut_51386 : selected 11 ⟨1481560, by decide⟩
    (prefixPartial 10 70235) = some ⟨10, 2, 0, 1481560, 70235, 853, 1048576⟩ := by
  decide +kernel

theorem context_10_70235_1481560 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70235 ⟨1481560, by decide⟩ :=
  accepted_of_selected 10 70235 ⟨1481560, by decide⟩ ⟨10, 2, 0, 1481560, 70235, 853, 1048576⟩
    (by decide) selected_cut_51386

theorem unmarked_context_9_17558_1481561 : frontier 12 ⟨1481561, by decide⟩
    (prefixCache 9 17558) (prefixPartial 9 17558) = false := by
  decide +kernel

theorem node_context_9_17558_1481561 : EJMOriginalGlobalDAGData.nodes 12 ⟨1481561, by decide⟩ =
    .split (coordinate 9) (![⟨1481477, by decide⟩,⟨1481528, by decide⟩,⟨1469103, by decide⟩,⟨1481560, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17558_1481561 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17558 ⟨1481561, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17558
    ⟨1481561, by decide⟩ (by decide) (![⟨1481477, by decide⟩,⟨1481528, by decide⟩,⟨1469103, by decide⟩,⟨1481560, by decide⟩]) unmarked_context_9_17558_1481561 node_context_9_17558_1481561
  intro a
  fin_cases a
  · exact context_10_70232_1481477
  · exact context_10_70233_1481528
  · exact context_10_70234_1469103
  · exact context_10_70235_1481560

theorem selected_cut_51387 : selected 12 ⟨1481636, by decide⟩
    (prefixPartial 9 17559) = some ⟨9, 2, 0, 1481636, 17559, 1853, 4194304⟩ := by
  decide +kernel

theorem context_9_17559_1481636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17559 ⟨1481636, by decide⟩ :=
  accepted_of_selected 9 17559 ⟨1481636, by decide⟩ ⟨9, 2, 0, 1481636, 17559, 1853, 4194304⟩
    (by decide) selected_cut_51387

theorem unmarked_context_8_4389_1481637 : frontier 13 ⟨1481637, by decide⟩
    (prefixCache 8 4389) (prefixPartial 8 4389) = false := by
  decide +kernel

theorem node_context_8_4389_1481637 : EJMOriginalGlobalDAGData.nodes 13 ⟨1481637, by decide⟩ =
    .split (coordinate 8) (![⟨1481135, by decide⟩,⟨1481395, by decide⟩,⟨1481561, by decide⟩,⟨1481636, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4389_1481637 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4389 ⟨1481637, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4389
    ⟨1481637, by decide⟩ (by decide) (![⟨1481135, by decide⟩,⟨1481395, by decide⟩,⟨1481561, by decide⟩,⟨1481636, by decide⟩]) unmarked_context_8_4389_1481637 node_context_8_4389_1481637
  intro a
  fin_cases a
  · exact context_9_17556_1481135
  · exact context_9_17557_1481395
  · exact context_9_17558_1481561
  · exact context_9_17559_1481636

theorem selected_cut_51388 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 70240) = some ⟨10, 1, 0, 1468246, 70240, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_70240_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70240 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 70240 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 70240, 1, 1048576⟩
    (by decide) selected_cut_51388

theorem selected_cut_51389 : selected 10 ⟨1481689, by decide⟩
    (prefixPartial 11 280964) = some ⟨11, 2, 0, 1481689, 280964, 2921, 262144⟩ := by
  decide +kernel

theorem context_11_280964_1481689 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280964 ⟨1481689, by decide⟩ :=
  accepted_of_selected 11 280964 ⟨1481689, by decide⟩ ⟨11, 2, 0, 1481689, 280964, 2921, 262144⟩
    (by decide) selected_cut_51389

theorem selected_cut_51390 : selected 10 ⟨1468419, by decide⟩
    (prefixPartial 11 280965) = some ⟨11, 1, 0, 1468419, 280965, 1, 262144⟩ := by
  decide +kernel

theorem context_11_280965_1468419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280965 ⟨1468419, by decide⟩ :=
  accepted_of_selected 11 280965 ⟨1468419, by decide⟩ ⟨11, 1, 0, 1468419, 280965, 1, 262144⟩
    (by decide) selected_cut_51390

theorem selected_cut_51391 : selected 10 ⟨1481768, by decide⟩
    (prefixPartial 11 280966) = some ⟨11, 2, 0, 1481768, 280966, 3237, 262144⟩ := by
  decide +kernel

theorem context_11_280966_1481768 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280966 ⟨1481768, by decide⟩ :=
  accepted_of_selected 11 280966 ⟨1481768, by decide⟩ ⟨11, 2, 0, 1481768, 280966, 3237, 262144⟩
    (by decide) selected_cut_51391

theorem selected_cut_51392 : selected 10 ⟨1481817, by decide⟩
    (prefixPartial 11 280967) = some ⟨11, 2, 0, 1481817, 280967, 2893, 262144⟩ := by
  decide +kernel

theorem context_11_280967_1481817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280967 ⟨1481817, by decide⟩ :=
  accepted_of_selected 11 280967 ⟨1481817, by decide⟩ ⟨11, 2, 0, 1481817, 280967, 2893, 262144⟩
    (by decide) selected_cut_51392

theorem unmarked_context_10_70241_1481818 : frontier 11 ⟨1481818, by decide⟩
    (prefixCache 10 70241) (prefixPartial 10 70241) = false := by
  decide +kernel

theorem node_context_10_70241_1481818 : EJMOriginalGlobalDAGData.nodes 11 ⟨1481818, by decide⟩ =
    .split (coordinate 10) (![⟨1481689, by decide⟩,⟨1468419, by decide⟩,⟨1481768, by decide⟩,⟨1481817, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_70241_1481818 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70241 ⟨1481818, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 70241
    ⟨1481818, by decide⟩ (by decide) (![⟨1481689, by decide⟩,⟨1468419, by decide⟩,⟨1481768, by decide⟩,⟨1481817, by decide⟩]) unmarked_context_10_70241_1481818 node_context_10_70241_1481818
  intro a
  fin_cases a
  · exact context_11_280964_1481689
  · exact context_11_280965_1468419
  · exact context_11_280966_1481768
  · exact context_11_280967_1481817

theorem selected_cut_51393 : selected 10 ⟨1481877, by decide⟩
    (prefixPartial 11 280968) = some ⟨11, 2, 0, 1481877, 280968, 2861, 262144⟩ := by
  decide +kernel

theorem context_11_280968_1481877 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280968 ⟨1481877, by decide⟩ :=
  accepted_of_selected 11 280968 ⟨1481877, by decide⟩ ⟨11, 2, 0, 1481877, 280968, 2861, 262144⟩
    (by decide) selected_cut_51393

theorem selected_cut_51394 : selected 10 ⟨1481927, by decide⟩
    (prefixPartial 11 280969) = some ⟨11, 2, 0, 1481927, 280969, 1825, 262144⟩ := by
  decide +kernel

theorem context_11_280969_1481927 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280969 ⟨1481927, by decide⟩ :=
  accepted_of_selected 11 280969 ⟨1481927, by decide⟩ ⟨11, 2, 0, 1481927, 280969, 1825, 262144⟩
    (by decide) selected_cut_51394

theorem selected_cut_51395 : selected 10 ⟨1468743, by decide⟩
    (prefixPartial 11 280970) = some ⟨11, 1, 0, 1468743, 280970, 1, 262144⟩ := by
  decide +kernel

theorem context_11_280970_1468743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280970 ⟨1468743, by decide⟩ :=
  accepted_of_selected 11 280970 ⟨1468743, by decide⟩ ⟨11, 1, 0, 1468743, 280970, 1, 262144⟩
    (by decide) selected_cut_51395

theorem selected_cut_51396 : selected 10 ⟨1481979, by decide⟩
    (prefixPartial 11 280971) = some ⟨11, 2, 0, 1481979, 280971, 2653, 262144⟩ := by
  decide +kernel

theorem context_11_280971_1481979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280971 ⟨1481979, by decide⟩ :=
  accepted_of_selected 11 280971 ⟨1481979, by decide⟩ ⟨11, 2, 0, 1481979, 280971, 2653, 262144⟩
    (by decide) selected_cut_51396

theorem unmarked_context_10_70242_1481980 : frontier 11 ⟨1481980, by decide⟩
    (prefixCache 10 70242) (prefixPartial 10 70242) = false := by
  decide +kernel

theorem node_context_10_70242_1481980 : EJMOriginalGlobalDAGData.nodes 11 ⟨1481980, by decide⟩ =
    .split (coordinate 10) (![⟨1481877, by decide⟩,⟨1481927, by decide⟩,⟨1468743, by decide⟩,⟨1481979, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_70242_1481980 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70242 ⟨1481980, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 70242
    ⟨1481980, by decide⟩ (by decide) (![⟨1481877, by decide⟩,⟨1481927, by decide⟩,⟨1468743, by decide⟩,⟨1481979, by decide⟩]) unmarked_context_10_70242_1481980 node_context_10_70242_1481980
  intro a
  fin_cases a
  · exact context_11_280968_1481877
  · exact context_11_280969_1481927
  · exact context_11_280970_1468743
  · exact context_11_280971_1481979

theorem selected_cut_51397 : selected 10 ⟨1482023, by decide⟩
    (prefixPartial 11 280972) = some ⟨11, 2, 0, 1482023, 280972, 2313, 262144⟩ := by
  decide +kernel

theorem context_11_280972_1482023 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280972 ⟨1482023, by decide⟩ :=
  accepted_of_selected 11 280972 ⟨1482023, by decide⟩ ⟨11, 2, 0, 1482023, 280972, 2313, 262144⟩
    (by decide) selected_cut_51397

theorem selected_cut_51398 : selected 10 ⟨1482066, by decide⟩
    (prefixPartial 11 280973) = some ⟨11, 2, 0, 1482066, 280973, 2225, 262144⟩ := by
  decide +kernel

theorem context_11_280973_1482066 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280973 ⟨1482066, by decide⟩ :=
  accepted_of_selected 11 280973 ⟨1482066, by decide⟩ ⟨11, 2, 0, 1482066, 280973, 2225, 262144⟩
    (by decide) selected_cut_51398

theorem selected_cut_51399 : selected 10 ⟨1482119, by decide⟩
    (prefixPartial 11 280974) = some ⟨11, 2, 0, 1482119, 280974, 2421, 262144⟩ := by
  decide +kernel

theorem context_11_280974_1482119 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280974 ⟨1482119, by decide⟩ :=
  accepted_of_selected 11 280974 ⟨1482119, by decide⟩ ⟨11, 2, 0, 1482119, 280974, 2421, 262144⟩
    (by decide) selected_cut_51399

theorem selected_cut_51400 : selected 10 ⟨1470044, by decide⟩
    (prefixPartial 11 280975) = some ⟨11, 1, 0, 1470044, 280975, 1, 262144⟩ := by
  decide +kernel

theorem context_11_280975_1470044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280975 ⟨1470044, by decide⟩ :=
  accepted_of_selected 11 280975 ⟨1470044, by decide⟩ ⟨11, 1, 0, 1470044, 280975, 1, 262144⟩
    (by decide) selected_cut_51400

theorem unmarked_context_10_70243_1482120 : frontier 11 ⟨1482120, by decide⟩
    (prefixCache 10 70243) (prefixPartial 10 70243) = false := by
  decide +kernel

theorem node_context_10_70243_1482120 : EJMOriginalGlobalDAGData.nodes 11 ⟨1482120, by decide⟩ =
    .split (coordinate 10) (![⟨1482023, by decide⟩,⟨1482066, by decide⟩,⟨1482119, by decide⟩,⟨1470044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_70243_1482120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70243 ⟨1482120, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 70243
    ⟨1482120, by decide⟩ (by decide) (![⟨1482023, by decide⟩,⟨1482066, by decide⟩,⟨1482119, by decide⟩,⟨1470044, by decide⟩]) unmarked_context_10_70243_1482120 node_context_10_70243_1482120
  intro a
  fin_cases a
  · exact context_11_280972_1482023
  · exact context_11_280973_1482066
  · exact context_11_280974_1482119
  · exact context_11_280975_1470044

theorem unmarked_context_9_17560_1482121 : frontier 12 ⟨1482121, by decide⟩
    (prefixCache 9 17560) (prefixPartial 9 17560) = false := by
  decide +kernel

theorem node_context_9_17560_1482121 : EJMOriginalGlobalDAGData.nodes 12 ⟨1482121, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1481818, by decide⟩,⟨1481980, by decide⟩,⟨1482120, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17560_1482121 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17560 ⟨1482121, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17560
    ⟨1482121, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1481818, by decide⟩,⟨1481980, by decide⟩,⟨1482120, by decide⟩]) unmarked_context_9_17560_1482121 node_context_9_17560_1482121
  intro a
  fin_cases a
  · exact context_10_70240_1468246
  · exact context_10_70241_1481818
  · exact context_10_70242_1481980
  · exact context_10_70243_1482120

theorem selected_cut_51401 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 280976) = some ⟨11, 1, 0, 434745, 280976, 1, 262144⟩ := by
  decide +kernel

theorem context_11_280976_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280976 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 280976 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 280976, 1, 262144⟩
    (by decide) selected_cut_51401

theorem selected_cut_51402 : selected 10 ⟨1482170, by decide⟩
    (prefixPartial 11 280977) = some ⟨11, 2, 0, 1482170, 280977, 2653, 262144⟩ := by
  decide +kernel

theorem context_11_280977_1482170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280977 ⟨1482170, by decide⟩ :=
  accepted_of_selected 11 280977 ⟨1482170, by decide⟩ ⟨11, 2, 0, 1482170, 280977, 2653, 262144⟩
    (by decide) selected_cut_51402

theorem selected_cut_51403 : selected 10 ⟨1482204, by decide⟩
    (prefixPartial 11 280978) = some ⟨11, 2, 0, 1482204, 280978, 2057, 262144⟩ := by
  decide +kernel

theorem context_11_280978_1482204 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280978 ⟨1482204, by decide⟩ :=
  accepted_of_selected 11 280978 ⟨1482204, by decide⟩ ⟨11, 2, 0, 1482204, 280978, 2057, 262144⟩
    (by decide) selected_cut_51403

theorem selected_cut_51404 : selected 10 ⟨1482242, by decide⟩
    (prefixPartial 11 280979) = some ⟨11, 2, 0, 1482242, 280979, 1949, 262144⟩ := by
  decide +kernel

theorem context_11_280979_1482242 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280979 ⟨1482242, by decide⟩ :=
  accepted_of_selected 11 280979 ⟨1482242, by decide⟩ ⟨11, 2, 0, 1482242, 280979, 1949, 262144⟩
    (by decide) selected_cut_51404

theorem unmarked_context_10_70244_1482243 : frontier 11 ⟨1482243, by decide⟩
    (prefixCache 10 70244) (prefixPartial 10 70244) = false := by
  decide +kernel

theorem node_context_10_70244_1482243 : EJMOriginalGlobalDAGData.nodes 11 ⟨1482243, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨1482170, by decide⟩,⟨1482204, by decide⟩,⟨1482242, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_70244_1482243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70244 ⟨1482243, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 70244
    ⟨1482243, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨1482170, by decide⟩,⟨1482204, by decide⟩,⟨1482242, by decide⟩]) unmarked_context_10_70244_1482243 node_context_10_70244_1482243
  intro a
  fin_cases a
  · exact context_11_280976_434745
  · exact context_11_280977_1482170
  · exact context_11_280978_1482204
  · exact context_11_280979_1482242

theorem selected_cut_51405 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 70245) = some ⟨10, 1, 0, 1468874, 70245, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_70245_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70245 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 70245 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 70245, 1, 1048576⟩
    (by decide) selected_cut_51405

theorem selected_cut_51406 : selected 10 ⟨1482287, by decide⟩
    (prefixPartial 11 280984) = some ⟨11, 2, 0, 1482287, 280984, 2093, 262144⟩ := by
  decide +kernel

theorem context_11_280984_1482287 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280984 ⟨1482287, by decide⟩ :=
  accepted_of_selected 11 280984 ⟨1482287, by decide⟩ ⟨11, 2, 0, 1482287, 280984, 2093, 262144⟩
    (by decide) selected_cut_51406

theorem selected_cut_51407 : selected 10 ⟨1482334, by decide⟩
    (prefixPartial 11 280985) = some ⟨11, 2, 0, 1482334, 280985, 2349, 262144⟩ := by
  decide +kernel

theorem context_11_280985_1482334 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280985 ⟨1482334, by decide⟩ :=
  accepted_of_selected 11 280985 ⟨1482334, by decide⟩ ⟨11, 2, 0, 1482334, 280985, 2349, 262144⟩
    (by decide) selected_cut_51407

theorem selected_cut_51408 : selected 10 ⟨1468743, by decide⟩
    (prefixPartial 11 280986) = some ⟨11, 1, 0, 1468743, 280986, 1, 262144⟩ := by
  decide +kernel

theorem context_11_280986_1468743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280986 ⟨1468743, by decide⟩ :=
  accepted_of_selected 11 280986 ⟨1468743, by decide⟩ ⟨11, 1, 0, 1468743, 280986, 1, 262144⟩
    (by decide) selected_cut_51408

theorem selected_cut_51409 : selected 10 ⟨1482371, by decide⟩
    (prefixPartial 11 280987) = some ⟨11, 2, 0, 1482371, 280987, 1801, 262144⟩ := by
  decide +kernel

theorem context_11_280987_1482371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280987 ⟨1482371, by decide⟩ :=
  accepted_of_selected 11 280987 ⟨1482371, by decide⟩ ⟨11, 2, 0, 1482371, 280987, 1801, 262144⟩
    (by decide) selected_cut_51409

theorem unmarked_context_10_70246_1482372 : frontier 11 ⟨1482372, by decide⟩
    (prefixCache 10 70246) (prefixPartial 10 70246) = false := by
  decide +kernel

theorem node_context_10_70246_1482372 : EJMOriginalGlobalDAGData.nodes 11 ⟨1482372, by decide⟩ =
    .split (coordinate 10) (![⟨1482287, by decide⟩,⟨1482334, by decide⟩,⟨1468743, by decide⟩,⟨1482371, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_70246_1482372 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70246 ⟨1482372, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 70246
    ⟨1482372, by decide⟩ (by decide) (![⟨1482287, by decide⟩,⟨1482334, by decide⟩,⟨1468743, by decide⟩,⟨1482371, by decide⟩]) unmarked_context_10_70246_1482372 node_context_10_70246_1482372
  intro a
  fin_cases a
  · exact context_11_280984_1482287
  · exact context_11_280985_1482334
  · exact context_11_280986_1468743
  · exact context_11_280987_1482371

theorem selected_cut_51410 : selected 10 ⟨1482400, by decide⟩
    (prefixPartial 11 280988) = some ⟨11, 2, 0, 1482400, 280988, 1613, 262144⟩ := by
  decide +kernel

theorem context_11_280988_1482400 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280988 ⟨1482400, by decide⟩ :=
  accepted_of_selected 11 280988 ⟨1482400, by decide⟩ ⟨11, 2, 0, 1482400, 280988, 1613, 262144⟩
    (by decide) selected_cut_51410

theorem selected_cut_51411 : selected 10 ⟨1482431, by decide⟩
    (prefixPartial 11 280989) = some ⟨11, 2, 0, 1482431, 280989, 1829, 262144⟩ := by
  decide +kernel

theorem context_11_280989_1482431 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280989 ⟨1482431, by decide⟩ :=
  accepted_of_selected 11 280989 ⟨1482431, by decide⟩ ⟨11, 2, 0, 1482431, 280989, 1829, 262144⟩
    (by decide) selected_cut_51411

theorem selected_cut_51412 : selected 10 ⟨1482463, by decide⟩
    (prefixPartial 11 280990) = some ⟨11, 2, 0, 1482463, 280990, 1369, 262144⟩ := by
  decide +kernel

theorem context_11_280990_1482463 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280990 ⟨1482463, by decide⟩ :=
  accepted_of_selected 11 280990 ⟨1482463, by decide⟩ ⟨11, 2, 0, 1482463, 280990, 1369, 262144⟩
    (by decide) selected_cut_51412

theorem selected_cut_51413 : selected 10 ⟨1470044, by decide⟩
    (prefixPartial 11 280991) = some ⟨11, 1, 0, 1470044, 280991, 1, 262144⟩ := by
  decide +kernel

theorem context_11_280991_1470044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 280991 ⟨1470044, by decide⟩ :=
  accepted_of_selected 11 280991 ⟨1470044, by decide⟩ ⟨11, 1, 0, 1470044, 280991, 1, 262144⟩
    (by decide) selected_cut_51413

theorem unmarked_context_10_70247_1482464 : frontier 11 ⟨1482464, by decide⟩
    (prefixCache 10 70247) (prefixPartial 10 70247) = false := by
  decide +kernel

theorem node_context_10_70247_1482464 : EJMOriginalGlobalDAGData.nodes 11 ⟨1482464, by decide⟩ =
    .split (coordinate 10) (![⟨1482400, by decide⟩,⟨1482431, by decide⟩,⟨1482463, by decide⟩,⟨1470044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_70247_1482464 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70247 ⟨1482464, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 70247
    ⟨1482464, by decide⟩ (by decide) (![⟨1482400, by decide⟩,⟨1482431, by decide⟩,⟨1482463, by decide⟩,⟨1470044, by decide⟩]) unmarked_context_10_70247_1482464 node_context_10_70247_1482464
  intro a
  fin_cases a
  · exact context_11_280988_1482400
  · exact context_11_280989_1482431
  · exact context_11_280990_1482463
  · exact context_11_280991_1470044

theorem unmarked_context_9_17561_1482465 : frontier 12 ⟨1482465, by decide⟩
    (prefixCache 9 17561) (prefixPartial 9 17561) = false := by
  decide +kernel

theorem node_context_9_17561_1482465 : EJMOriginalGlobalDAGData.nodes 12 ⟨1482465, by decide⟩ =
    .split (coordinate 9) (![⟨1482243, by decide⟩,⟨1468874, by decide⟩,⟨1482372, by decide⟩,⟨1482464, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17561_1482465 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17561 ⟨1482465, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17561
    ⟨1482465, by decide⟩ (by decide) (![⟨1482243, by decide⟩,⟨1468874, by decide⟩,⟨1482372, by decide⟩,⟨1482464, by decide⟩]) unmarked_context_9_17561_1482465 node_context_9_17561_1482465
  intro a
  fin_cases a
  · exact context_10_70244_1482243
  · exact context_10_70245_1468874
  · exact context_10_70246_1482372
  · exact context_10_70247_1482464

theorem selected_cut_51414 : selected 11 ⟨1482538, by decide⟩
    (prefixPartial 10 70248) = some ⟨10, 2, 0, 1482538, 70248, 4041, 1048576⟩ := by
  decide +kernel

theorem context_10_70248_1482538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70248 ⟨1482538, by decide⟩ :=
  accepted_of_selected 10 70248 ⟨1482538, by decide⟩ ⟨10, 2, 0, 1482538, 70248, 4041, 1048576⟩
    (by decide) selected_cut_51414

theorem selected_cut_51415 : selected 11 ⟨1482603, by decide⟩
    (prefixPartial 10 70249) = some ⟨10, 2, 0, 1482603, 70249, 3573, 1048576⟩ := by
  decide +kernel

theorem context_10_70249_1482603 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70249 ⟨1482603, by decide⟩ :=
  accepted_of_selected 10 70249 ⟨1482603, by decide⟩ ⟨10, 2, 0, 1482603, 70249, 3573, 1048576⟩
    (by decide) selected_cut_51415

theorem selected_cut_51416 : selected 11 ⟨1469103, by decide⟩
    (prefixPartial 10 70250) = some ⟨10, 1, 0, 1469103, 70250, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_70250_1469103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70250 ⟨1469103, by decide⟩ :=
  accepted_of_selected 10 70250 ⟨1469103, by decide⟩ ⟨10, 1, 0, 1469103, 70250, 1, 1048576⟩
    (by decide) selected_cut_51416

theorem selected_cut_51417 : selected 11 ⟨1482648, by decide⟩
    (prefixPartial 10 70251) = some ⟨10, 2, 0, 1482648, 70251, 2321, 1048576⟩ := by
  decide +kernel

theorem context_10_70251_1482648 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70251 ⟨1482648, by decide⟩ :=
  accepted_of_selected 10 70251 ⟨1482648, by decide⟩ ⟨10, 2, 0, 1482648, 70251, 2321, 1048576⟩
    (by decide) selected_cut_51417

theorem unmarked_context_9_17562_1482649 : frontier 12 ⟨1482649, by decide⟩
    (prefixCache 9 17562) (prefixPartial 9 17562) = false := by
  decide +kernel

theorem node_context_9_17562_1482649 : EJMOriginalGlobalDAGData.nodes 12 ⟨1482649, by decide⟩ =
    .split (coordinate 9) (![⟨1482538, by decide⟩,⟨1482603, by decide⟩,⟨1469103, by decide⟩,⟨1482648, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17562_1482649 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17562 ⟨1482649, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17562
    ⟨1482649, by decide⟩ (by decide) (![⟨1482538, by decide⟩,⟨1482603, by decide⟩,⟨1469103, by decide⟩,⟨1482648, by decide⟩]) unmarked_context_9_17562_1482649 node_context_9_17562_1482649
  intro a
  fin_cases a
  · exact context_10_70248_1482538
  · exact context_10_70249_1482603
  · exact context_10_70250_1469103
  · exact context_10_70251_1482648

theorem selected_cut_51418 : selected 12 ⟨1482703, by decide⟩
    (prefixPartial 9 17563) = some ⟨9, 2, 0, 1482703, 17563, 3049, 4194304⟩ := by
  decide +kernel

theorem context_9_17563_1482703 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17563 ⟨1482703, by decide⟩ :=
  accepted_of_selected 9 17563 ⟨1482703, by decide⟩ ⟨9, 2, 0, 1482703, 17563, 3049, 4194304⟩
    (by decide) selected_cut_51418

theorem unmarked_context_8_4390_1482704 : frontier 13 ⟨1482704, by decide⟩
    (prefixCache 8 4390) (prefixPartial 8 4390) = false := by
  decide +kernel

theorem node_context_8_4390_1482704 : EJMOriginalGlobalDAGData.nodes 13 ⟨1482704, by decide⟩ =
    .split (coordinate 8) (![⟨1482121, by decide⟩,⟨1482465, by decide⟩,⟨1482649, by decide⟩,⟨1482703, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4390_1482704 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4390 ⟨1482704, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4390
    ⟨1482704, by decide⟩ (by decide) (![⟨1482121, by decide⟩,⟨1482465, by decide⟩,⟨1482649, by decide⟩,⟨1482703, by decide⟩]) unmarked_context_8_4390_1482704 node_context_8_4390_1482704
  intro a
  fin_cases a
  · exact context_9_17560_1482121
  · exact context_9_17561_1482465
  · exact context_9_17562_1482649
  · exact context_9_17563_1482703

theorem selected_cut_51419 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 70256) = some ⟨10, 1, 0, 1468246, 70256, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_70256_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70256 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 70256 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 70256, 1, 1048576⟩
    (by decide) selected_cut_51419

theorem selected_cut_51420 : selected 10 ⟨1482768, by decide⟩
    (prefixPartial 11 281028) = some ⟨11, 2, 0, 1482768, 281028, 3037, 262144⟩ := by
  decide +kernel

theorem context_11_281028_1482768 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 281028 ⟨1482768, by decide⟩ :=
  accepted_of_selected 11 281028 ⟨1482768, by decide⟩ ⟨11, 2, 0, 1482768, 281028, 3037, 262144⟩
    (by decide) selected_cut_51420

theorem selected_cut_51421 : selected 10 ⟨1468419, by decide⟩
    (prefixPartial 11 281029) = some ⟨11, 1, 0, 1468419, 281029, 1, 262144⟩ := by
  decide +kernel

theorem context_11_281029_1468419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 281029 ⟨1468419, by decide⟩ :=
  accepted_of_selected 11 281029 ⟨1468419, by decide⟩ ⟨11, 1, 0, 1468419, 281029, 1, 262144⟩
    (by decide) selected_cut_51421

theorem selected_cut_51422 : selected 10 ⟨1482851, by decide⟩
    (prefixPartial 11 281030) = some ⟨11, 2, 0, 1482851, 281030, 3341, 262144⟩ := by
  decide +kernel

theorem context_11_281030_1482851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 281030 ⟨1482851, by decide⟩ :=
  accepted_of_selected 11 281030 ⟨1482851, by decide⟩ ⟨11, 2, 0, 1482851, 281030, 3341, 262144⟩
    (by decide) selected_cut_51422

theorem selected_cut_51423 : selected 10 ⟨1482881, by decide⟩
    (prefixPartial 11 281031) = some ⟨11, 2, 0, 1482881, 281031, 1453, 262144⟩ := by
  decide +kernel

theorem context_11_281031_1482881 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 281031 ⟨1482881, by decide⟩ :=
  accepted_of_selected 11 281031 ⟨1482881, by decide⟩ ⟨11, 2, 0, 1482881, 281031, 1453, 262144⟩
    (by decide) selected_cut_51423

theorem unmarked_context_10_70257_1482882 : frontier 11 ⟨1482882, by decide⟩
    (prefixCache 10 70257) (prefixPartial 10 70257) = false := by
  decide +kernel

theorem node_context_10_70257_1482882 : EJMOriginalGlobalDAGData.nodes 11 ⟨1482882, by decide⟩ =
    .split (coordinate 10) (![⟨1482768, by decide⟩,⟨1468419, by decide⟩,⟨1482851, by decide⟩,⟨1482881, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_70257_1482882 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70257 ⟨1482882, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 70257
    ⟨1482882, by decide⟩ (by decide) (![⟨1482768, by decide⟩,⟨1468419, by decide⟩,⟨1482851, by decide⟩,⟨1482881, by decide⟩]) unmarked_context_10_70257_1482882 node_context_10_70257_1482882
  intro a
  fin_cases a
  · exact context_11_281028_1482768
  · exact context_11_281029_1468419
  · exact context_11_281030_1482851
  · exact context_11_281031_1482881

theorem selected_cut_51424 : selected 10 ⟨1482944, by decide⟩
    (prefixPartial 11 281032) = some ⟨11, 2, 0, 1482944, 281032, 2797, 262144⟩ := by
  decide +kernel

theorem context_11_281032_1482944 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 281032 ⟨1482944, by decide⟩ :=
  accepted_of_selected 11 281032 ⟨1482944, by decide⟩ ⟨11, 2, 0, 1482944, 281032, 2797, 262144⟩
    (by decide) selected_cut_51424

theorem selected_cut_51425 : selected 10 ⟨1482997, by decide⟩
    (prefixPartial 11 281033) = some ⟨11, 2, 0, 1482997, 281033, 2549, 262144⟩ := by
  decide +kernel

theorem context_11_281033_1482997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 281033 ⟨1482997, by decide⟩ :=
  accepted_of_selected 11 281033 ⟨1482997, by decide⟩ ⟨11, 2, 0, 1482997, 281033, 2549, 262144⟩
    (by decide) selected_cut_51425

theorem selected_cut_51426 : selected 10 ⟨1468743, by decide⟩
    (prefixPartial 11 281034) = some ⟨11, 1, 0, 1468743, 281034, 1, 262144⟩ := by
  decide +kernel

theorem context_11_281034_1468743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 281034 ⟨1468743, by decide⟩ :=
  accepted_of_selected 11 281034 ⟨1468743, by decide⟩ ⟨11, 1, 0, 1468743, 281034, 1, 262144⟩
    (by decide) selected_cut_51426

theorem selected_cut_51427 : selected 10 ⟨1483044, by decide⟩
    (prefixPartial 11 281035) = some ⟨11, 2, 0, 1483044, 281035, 2561, 262144⟩ := by
  decide +kernel

theorem context_11_281035_1483044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 281035 ⟨1483044, by decide⟩ :=
  accepted_of_selected 11 281035 ⟨1483044, by decide⟩ ⟨11, 2, 0, 1483044, 281035, 2561, 262144⟩
    (by decide) selected_cut_51427

theorem unmarked_context_10_70258_1483045 : frontier 11 ⟨1483045, by decide⟩
    (prefixCache 10 70258) (prefixPartial 10 70258) = false := by
  decide +kernel

theorem node_context_10_70258_1483045 : EJMOriginalGlobalDAGData.nodes 11 ⟨1483045, by decide⟩ =
    .split (coordinate 10) (![⟨1482944, by decide⟩,⟨1482997, by decide⟩,⟨1468743, by decide⟩,⟨1483044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_70258_1483045 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70258 ⟨1483045, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 70258
    ⟨1483045, by decide⟩ (by decide) (![⟨1482944, by decide⟩,⟨1482997, by decide⟩,⟨1468743, by decide⟩,⟨1483044, by decide⟩]) unmarked_context_10_70258_1483045 node_context_10_70258_1483045
  intro a
  fin_cases a
  · exact context_11_281032_1482944
  · exact context_11_281033_1482997
  · exact context_11_281034_1468743
  · exact context_11_281035_1483044

theorem selected_cut_51428 : selected 10 ⟨1483114, by decide⟩
    (prefixPartial 11 281036) = some ⟨11, 2, 0, 1483114, 281036, 2733, 262144⟩ := by
  decide +kernel

theorem context_11_281036_1483114 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 281036 ⟨1483114, by decide⟩ :=
  accepted_of_selected 11 281036 ⟨1483114, by decide⟩ ⟨11, 2, 0, 1483114, 281036, 2733, 262144⟩
    (by decide) selected_cut_51428

theorem selected_cut_51429 : selected 10 ⟨1483138, by decide⟩
    (prefixPartial 11 281037) = some ⟨11, 2, 0, 1483138, 281037, 1145, 262144⟩ := by
  decide +kernel

theorem context_11_281037_1483138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 281037 ⟨1483138, by decide⟩ :=
  accepted_of_selected 11 281037 ⟨1483138, by decide⟩ ⟨11, 2, 0, 1483138, 281037, 1145, 262144⟩
    (by decide) selected_cut_51429

theorem selected_cut_51430 : selected 10 ⟨1483217, by decide⟩
    (prefixPartial 11 281038) = some ⟨11, 2, 0, 1483217, 281038, 2189, 262144⟩ := by
  decide +kernel

theorem context_11_281038_1483217 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 281038 ⟨1483217, by decide⟩ :=
  accepted_of_selected 11 281038 ⟨1483217, by decide⟩ ⟨11, 2, 0, 1483217, 281038, 2189, 262144⟩
    (by decide) selected_cut_51430

theorem selected_cut_51431 : selected 10 ⟨1470044, by decide⟩
    (prefixPartial 11 281039) = some ⟨11, 1, 0, 1470044, 281039, 1, 262144⟩ := by
  decide +kernel

theorem context_11_281039_1470044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 281039 ⟨1470044, by decide⟩ :=
  accepted_of_selected 11 281039 ⟨1470044, by decide⟩ ⟨11, 1, 0, 1470044, 281039, 1, 262144⟩
    (by decide) selected_cut_51431

theorem unmarked_context_10_70259_1483218 : frontier 11 ⟨1483218, by decide⟩
    (prefixCache 10 70259) (prefixPartial 10 70259) = false := by
  decide +kernel

theorem node_context_10_70259_1483218 : EJMOriginalGlobalDAGData.nodes 11 ⟨1483218, by decide⟩ =
    .split (coordinate 10) (![⟨1483114, by decide⟩,⟨1483138, by decide⟩,⟨1483217, by decide⟩,⟨1470044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_70259_1483218 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70259 ⟨1483218, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 70259
    ⟨1483218, by decide⟩ (by decide) (![⟨1483114, by decide⟩,⟨1483138, by decide⟩,⟨1483217, by decide⟩,⟨1470044, by decide⟩]) unmarked_context_10_70259_1483218 node_context_10_70259_1483218
  intro a
  fin_cases a
  · exact context_11_281036_1483114
  · exact context_11_281037_1483138
  · exact context_11_281038_1483217
  · exact context_11_281039_1470044

theorem unmarked_context_9_17564_1483219 : frontier 12 ⟨1483219, by decide⟩
    (prefixCache 9 17564) (prefixPartial 9 17564) = false := by
  decide +kernel

theorem node_context_9_17564_1483219 : EJMOriginalGlobalDAGData.nodes 12 ⟨1483219, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1482882, by decide⟩,⟨1483045, by decide⟩,⟨1483218, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17564_1483219 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17564 ⟨1483219, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17564
    ⟨1483219, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1482882, by decide⟩,⟨1483045, by decide⟩,⟨1483218, by decide⟩]) unmarked_context_9_17564_1483219 node_context_9_17564_1483219
  intro a
  fin_cases a
  · exact context_10_70256_1468246
  · exact context_10_70257_1482882
  · exact context_10_70258_1483045
  · exact context_10_70259_1483218

theorem selected_cut_51432 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 281040) = some ⟨11, 1, 0, 434745, 281040, 1, 262144⟩ := by
  decide +kernel

theorem context_11_281040_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 281040 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 281040 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 281040, 1, 262144⟩
    (by decide) selected_cut_51432

theorem selected_cut_51433 : selected 10 ⟨1483266, by decide⟩
    (prefixPartial 11 281041) = some ⟨11, 2, 0, 1483266, 281041, 2781, 262144⟩ := by
  decide +kernel

theorem context_11_281041_1483266 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 281041 ⟨1483266, by decide⟩ :=
  accepted_of_selected 11 281041 ⟨1483266, by decide⟩ ⟨11, 2, 0, 1483266, 281041, 2781, 262144⟩
    (by decide) selected_cut_51433

theorem selected_cut_51434 : selected 10 ⟨1483307, by decide⟩
    (prefixPartial 11 281042) = some ⟨11, 2, 0, 1483307, 281042, 2101, 262144⟩ := by
  decide +kernel

theorem context_11_281042_1483307 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 281042 ⟨1483307, by decide⟩ :=
  accepted_of_selected 11 281042 ⟨1483307, by decide⟩ ⟨11, 2, 0, 1483307, 281042, 2101, 262144⟩
    (by decide) selected_cut_51434

theorem selected_cut_51435 : selected 10 ⟨1483344, by decide⟩
    (prefixPartial 11 281043) = some ⟨11, 2, 0, 1483344, 281043, 1985, 262144⟩ := by
  decide +kernel

theorem context_11_281043_1483344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 281043 ⟨1483344, by decide⟩ :=
  accepted_of_selected 11 281043 ⟨1483344, by decide⟩ ⟨11, 2, 0, 1483344, 281043, 1985, 262144⟩
    (by decide) selected_cut_51435

theorem unmarked_context_10_70260_1483345 : frontier 11 ⟨1483345, by decide⟩
    (prefixCache 10 70260) (prefixPartial 10 70260) = false := by
  decide +kernel

theorem node_context_10_70260_1483345 : EJMOriginalGlobalDAGData.nodes 11 ⟨1483345, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨1483266, by decide⟩,⟨1483307, by decide⟩,⟨1483344, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_70260_1483345 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70260 ⟨1483345, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 70260
    ⟨1483345, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨1483266, by decide⟩,⟨1483307, by decide⟩,⟨1483344, by decide⟩]) unmarked_context_10_70260_1483345 node_context_10_70260_1483345
  intro a
  fin_cases a
  · exact context_11_281040_434745
  · exact context_11_281041_1483266
  · exact context_11_281042_1483307
  · exact context_11_281043_1483344

theorem selected_cut_51436 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 70261) = some ⟨10, 1, 0, 1468874, 70261, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_70261_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70261 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 70261 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 70261, 1, 1048576⟩
    (by decide) selected_cut_51436

theorem selected_cut_51437 : selected 10 ⟨1483387, by decide⟩
    (prefixPartial 11 281048) = some ⟨11, 2, 0, 1483387, 281048, 2157, 262144⟩ := by
  decide +kernel

theorem context_11_281048_1483387 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 281048 ⟨1483387, by decide⟩ :=
  accepted_of_selected 11 281048 ⟨1483387, by decide⟩ ⟨11, 2, 0, 1483387, 281048, 2157, 262144⟩
    (by decide) selected_cut_51437

theorem selected_cut_51438 : selected 10 ⟨1483431, by decide⟩
    (prefixPartial 11 281049) = some ⟨11, 2, 0, 1483431, 281049, 2457, 262144⟩ := by
  decide +kernel

theorem context_11_281049_1483431 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 281049 ⟨1483431, by decide⟩ :=
  accepted_of_selected 11 281049 ⟨1483431, by decide⟩ ⟨11, 2, 0, 1483431, 281049, 2457, 262144⟩
    (by decide) selected_cut_51438

theorem selected_cut_51439 : selected 10 ⟨1468743, by decide⟩
    (prefixPartial 11 281050) = some ⟨11, 1, 0, 1468743, 281050, 1, 262144⟩ := by
  decide +kernel

theorem context_11_281050_1468743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 281050 ⟨1468743, by decide⟩ :=
  accepted_of_selected 11 281050 ⟨1468743, by decide⟩ ⟨11, 1, 0, 1468743, 281050, 1, 262144⟩
    (by decide) selected_cut_51439

theorem selected_cut_51440 : selected 10 ⟨1483463, by decide⟩
    (prefixPartial 11 281051) = some ⟨11, 2, 0, 1483463, 281051, 1781, 262144⟩ := by
  decide +kernel

theorem context_11_281051_1483463 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 281051 ⟨1483463, by decide⟩ :=
  accepted_of_selected 11 281051 ⟨1483463, by decide⟩ ⟨11, 2, 0, 1483463, 281051, 1781, 262144⟩
    (by decide) selected_cut_51440

theorem unmarked_context_10_70262_1483464 : frontier 11 ⟨1483464, by decide⟩
    (prefixCache 10 70262) (prefixPartial 10 70262) = false := by
  decide +kernel

theorem node_context_10_70262_1483464 : EJMOriginalGlobalDAGData.nodes 11 ⟨1483464, by decide⟩ =
    .split (coordinate 10) (![⟨1483387, by decide⟩,⟨1483431, by decide⟩,⟨1468743, by decide⟩,⟨1483463, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_70262_1483464 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70262 ⟨1483464, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 70262
    ⟨1483464, by decide⟩ (by decide) (![⟨1483387, by decide⟩,⟨1483431, by decide⟩,⟨1468743, by decide⟩,⟨1483463, by decide⟩]) unmarked_context_10_70262_1483464 node_context_10_70262_1483464
  intro a
  fin_cases a
  · exact context_11_281048_1483387
  · exact context_11_281049_1483431
  · exact context_11_281050_1468743
  · exact context_11_281051_1483463

theorem selected_cut_51441 : selected 10 ⟨1483503, by decide⟩
    (prefixPartial 11 281052) = some ⟨11, 2, 0, 1483503, 281052, 1873, 262144⟩ := by
  decide +kernel

theorem context_11_281052_1483503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 281052 ⟨1483503, by decide⟩ :=
  accepted_of_selected 11 281052 ⟨1483503, by decide⟩ ⟨11, 2, 0, 1483503, 281052, 1873, 262144⟩
    (by decide) selected_cut_51441

theorem selected_cut_51442 : selected 10 ⟨1483553, by decide⟩
    (prefixPartial 11 281053) = some ⟨11, 2, 0, 1483553, 281053, 2261, 262144⟩ := by
  decide +kernel

theorem context_11_281053_1483553 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 281053 ⟨1483553, by decide⟩ :=
  accepted_of_selected 11 281053 ⟨1483553, by decide⟩ ⟨11, 2, 0, 1483553, 281053, 2261, 262144⟩
    (by decide) selected_cut_51442

theorem selected_cut_51443 : selected 10 ⟨1483590, by decide⟩
    (prefixPartial 11 281054) = some ⟨11, 2, 0, 1483590, 281054, 1577, 262144⟩ := by
  decide +kernel

theorem context_11_281054_1483590 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 281054 ⟨1483590, by decide⟩ :=
  accepted_of_selected 11 281054 ⟨1483590, by decide⟩ ⟨11, 2, 0, 1483590, 281054, 1577, 262144⟩
    (by decide) selected_cut_51443

theorem selected_cut_51444 : selected 10 ⟨1470044, by decide⟩
    (prefixPartial 11 281055) = some ⟨11, 1, 0, 1470044, 281055, 1, 262144⟩ := by
  decide +kernel

theorem context_11_281055_1470044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 281055 ⟨1470044, by decide⟩ :=
  accepted_of_selected 11 281055 ⟨1470044, by decide⟩ ⟨11, 1, 0, 1470044, 281055, 1, 262144⟩
    (by decide) selected_cut_51444

theorem unmarked_context_10_70263_1483591 : frontier 11 ⟨1483591, by decide⟩
    (prefixCache 10 70263) (prefixPartial 10 70263) = false := by
  decide +kernel

theorem node_context_10_70263_1483591 : EJMOriginalGlobalDAGData.nodes 11 ⟨1483591, by decide⟩ =
    .split (coordinate 10) (![⟨1483503, by decide⟩,⟨1483553, by decide⟩,⟨1483590, by decide⟩,⟨1470044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_70263_1483591 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70263 ⟨1483591, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 70263
    ⟨1483591, by decide⟩ (by decide) (![⟨1483503, by decide⟩,⟨1483553, by decide⟩,⟨1483590, by decide⟩,⟨1470044, by decide⟩]) unmarked_context_10_70263_1483591 node_context_10_70263_1483591
  intro a
  fin_cases a
  · exact context_11_281052_1483503
  · exact context_11_281053_1483553
  · exact context_11_281054_1483590
  · exact context_11_281055_1470044

theorem unmarked_context_9_17565_1483592 : frontier 12 ⟨1483592, by decide⟩
    (prefixCache 9 17565) (prefixPartial 9 17565) = false := by
  decide +kernel

theorem node_context_9_17565_1483592 : EJMOriginalGlobalDAGData.nodes 12 ⟨1483592, by decide⟩ =
    .split (coordinate 9) (![⟨1483345, by decide⟩,⟨1468874, by decide⟩,⟨1483464, by decide⟩,⟨1483591, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17565_1483592 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17565 ⟨1483592, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17565
    ⟨1483592, by decide⟩ (by decide) (![⟨1483345, by decide⟩,⟨1468874, by decide⟩,⟨1483464, by decide⟩,⟨1483591, by decide⟩]) unmarked_context_9_17565_1483592 node_context_9_17565_1483592
  intro a
  fin_cases a
  · exact context_10_70260_1483345
  · exact context_10_70261_1468874
  · exact context_10_70262_1483464
  · exact context_10_70263_1483591

theorem selected_cut_51445 : selected 10 ⟨1469810, by decide⟩
    (prefixPartial 11 281056) = some ⟨11, 1, 0, 1469810, 281056, 1, 262144⟩ := by
  decide +kernel

theorem context_11_281056_1469810 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 281056 ⟨1469810, by decide⟩ :=
  accepted_of_selected 11 281056 ⟨1469810, by decide⟩ ⟨11, 1, 0, 1469810, 281056, 1, 262144⟩
    (by decide) selected_cut_51445

theorem selected_cut_51446 : selected 10 ⟨1483610, by decide⟩
    (prefixPartial 11 281057) = some ⟨11, 2, 0, 1483610, 281057, 1089, 262144⟩ := by
  decide +kernel

theorem context_11_281057_1483610 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 281057 ⟨1483610, by decide⟩ :=
  accepted_of_selected 11 281057 ⟨1483610, by decide⟩ ⟨11, 2, 0, 1483610, 281057, 1089, 262144⟩
    (by decide) selected_cut_51446

theorem selected_cut_51447 : selected 10 ⟨1483639, by decide⟩
    (prefixPartial 11 281058) = some ⟨11, 2, 0, 1483639, 281058, 1953, 262144⟩ := by
  decide +kernel

theorem context_11_281058_1483639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 281058 ⟨1483639, by decide⟩ :=
  accepted_of_selected 11 281058 ⟨1483639, by decide⟩ ⟨11, 2, 0, 1483639, 281058, 1953, 262144⟩
    (by decide) selected_cut_51447

theorem selected_cut_51448 : selected 10 ⟨1483653, by decide⟩
    (prefixPartial 11 281059) = some ⟨11, 2, 0, 1483653, 281059, 1061, 262144⟩ := by
  decide +kernel

theorem context_11_281059_1483653 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 281059 ⟨1483653, by decide⟩ :=
  accepted_of_selected 11 281059 ⟨1483653, by decide⟩ ⟨11, 2, 0, 1483653, 281059, 1061, 262144⟩
    (by decide) selected_cut_51448

theorem unmarked_context_10_70264_1483654 : frontier 11 ⟨1483654, by decide⟩
    (prefixCache 10 70264) (prefixPartial 10 70264) = false := by
  decide +kernel

theorem node_context_10_70264_1483654 : EJMOriginalGlobalDAGData.nodes 11 ⟨1483654, by decide⟩ =
    .split (coordinate 10) (![⟨1469810, by decide⟩,⟨1483610, by decide⟩,⟨1483639, by decide⟩,⟨1483653, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_70264_1483654 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70264 ⟨1483654, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 70264
    ⟨1483654, by decide⟩ (by decide) (![⟨1469810, by decide⟩,⟨1483610, by decide⟩,⟨1483639, by decide⟩,⟨1483653, by decide⟩]) unmarked_context_10_70264_1483654 node_context_10_70264_1483654
  intro a
  fin_cases a
  · exact context_11_281056_1469810
  · exact context_11_281057_1483610
  · exact context_11_281058_1483639
  · exact context_11_281059_1483653

theorem selected_cut_51449 : selected 11 ⟨1483709, by decide⟩
    (prefixPartial 10 70265) = some ⟨10, 2, 0, 1483709, 70265, 3729, 1048576⟩ := by
  decide +kernel

theorem context_10_70265_1483709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70265 ⟨1483709, by decide⟩ :=
  accepted_of_selected 10 70265 ⟨1483709, by decide⟩ ⟨10, 2, 0, 1483709, 70265, 3729, 1048576⟩
    (by decide) selected_cut_51449

theorem selected_cut_51450 : selected 11 ⟨1469103, by decide⟩
    (prefixPartial 10 70266) = some ⟨10, 1, 0, 1469103, 70266, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_70266_1469103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70266 ⟨1469103, by decide⟩ :=
  accepted_of_selected 10 70266 ⟨1469103, by decide⟩ ⟨10, 1, 0, 1469103, 70266, 1, 1048576⟩
    (by decide) selected_cut_51450

theorem selected_cut_51451 : selected 11 ⟨1483765, by decide⟩
    (prefixPartial 10 70267) = some ⟨10, 2, 0, 1483765, 70267, 2821, 1048576⟩ := by
  decide +kernel

theorem context_10_70267_1483765 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70267 ⟨1483765, by decide⟩ :=
  accepted_of_selected 10 70267 ⟨1483765, by decide⟩ ⟨10, 2, 0, 1483765, 70267, 2821, 1048576⟩
    (by decide) selected_cut_51451

theorem unmarked_context_9_17566_1483766 : frontier 12 ⟨1483766, by decide⟩
    (prefixCache 9 17566) (prefixPartial 9 17566) = false := by
  decide +kernel

theorem node_context_9_17566_1483766 : EJMOriginalGlobalDAGData.nodes 12 ⟨1483766, by decide⟩ =
    .split (coordinate 9) (![⟨1483654, by decide⟩,⟨1483709, by decide⟩,⟨1469103, by decide⟩,⟨1483765, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17566_1483766 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17566 ⟨1483766, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17566
    ⟨1483766, by decide⟩ (by decide) (![⟨1483654, by decide⟩,⟨1483709, by decide⟩,⟨1469103, by decide⟩,⟨1483765, by decide⟩]) unmarked_context_9_17566_1483766 node_context_9_17566_1483766
  intro a
  fin_cases a
  · exact context_10_70264_1483654
  · exact context_10_70265_1483709
  · exact context_10_70266_1469103
  · exact context_10_70267_1483765

theorem selected_cut_51452 : selected 12 ⟨1483831, by decide⟩
    (prefixPartial 9 17567) = some ⟨9, 2, 0, 1483831, 17567, 2945, 4194304⟩ := by
  decide +kernel

theorem context_9_17567_1483831 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17567 ⟨1483831, by decide⟩ :=
  accepted_of_selected 9 17567 ⟨1483831, by decide⟩ ⟨9, 2, 0, 1483831, 17567, 2945, 4194304⟩
    (by decide) selected_cut_51452

theorem unmarked_context_8_4391_1483832 : frontier 13 ⟨1483832, by decide⟩
    (prefixCache 8 4391) (prefixPartial 8 4391) = false := by
  decide +kernel

theorem node_context_8_4391_1483832 : EJMOriginalGlobalDAGData.nodes 13 ⟨1483832, by decide⟩ =
    .split (coordinate 8) (![⟨1483219, by decide⟩,⟨1483592, by decide⟩,⟨1483766, by decide⟩,⟨1483831, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4391_1483832 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4391 ⟨1483832, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4391
    ⟨1483832, by decide⟩ (by decide) (![⟨1483219, by decide⟩,⟨1483592, by decide⟩,⟨1483766, by decide⟩,⟨1483831, by decide⟩]) unmarked_context_8_4391_1483832 node_context_8_4391_1483832
  intro a
  fin_cases a
  · exact context_9_17564_1483219
  · exact context_9_17565_1483592
  · exact context_9_17566_1483766
  · exact context_9_17567_1483831

theorem unmarked_context_7_1097_1483833 : frontier 14 ⟨1483833, by decide⟩
    (prefixCache 7 1097) (prefixPartial 7 1097) = false := by
  decide +kernel

theorem node_context_7_1097_1483833 : EJMOriginalGlobalDAGData.nodes 14 ⟨1483833, by decide⟩ =
    .split (coordinate 7) (![⟨14300, by decide⟩,⟨1481637, by decide⟩,⟨1482704, by decide⟩,⟨1483832, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_1097_1483833 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 1097 ⟨1483833, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 1097
    ⟨1483833, by decide⟩ (by decide) (![⟨14300, by decide⟩,⟨1481637, by decide⟩,⟨1482704, by decide⟩,⟨1483832, by decide⟩]) unmarked_context_7_1097_1483833 node_context_7_1097_1483833
  intro a
  fin_cases a
  · exact context_8_4388_14300
  · exact context_8_4389_1481637
  · exact context_8_4390_1482704
  · exact context_8_4391_1483832

theorem selected_cut_51453 : selected 13 ⟨14300, by decide⟩
    (prefixPartial 8 4392) = some ⟨8, 1, 0, 14300, 4392, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_4392_14300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4392 ⟨14300, by decide⟩ :=
  accepted_of_selected 8 4392 ⟨14300, by decide⟩ ⟨8, 1, 0, 14300, 4392, 1, 16777216⟩
    (by decide) selected_cut_51453

theorem selected_cut_51454 : selected 13 ⟨14300, by decide⟩
    (prefixPartial 8 4393) = some ⟨8, 1, 0, 14300, 4393, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_4393_14300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4393 ⟨14300, by decide⟩ :=
  accepted_of_selected 8 4393 ⟨14300, by decide⟩ ⟨8, 1, 0, 14300, 4393, 1, 16777216⟩
    (by decide) selected_cut_51454

theorem selected_cut_51455 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 70304) = some ⟨10, 1, 0, 1468246, 70304, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_70304_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 70304 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 70304 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 70304, 1, 1048576⟩
    (by decide) selected_cut_51455

theorem selected_cut_51456 : selected 10 ⟨1483983, by decide⟩
    (prefixPartial 11 281220) = some ⟨11, 2, 0, 1483983, 281220, 2853, 262144⟩ := by
  decide +kernel

theorem context_11_281220_1483983 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 281220 ⟨1483983, by decide⟩ :=
  accepted_of_selected 11 281220 ⟨1483983, by decide⟩ ⟨11, 2, 0, 1483983, 281220, 2853, 262144⟩
    (by decide) selected_cut_51456

theorem selected_cut_51457 : selected 10 ⟨1468419, by decide⟩
    (prefixPartial 11 281221) = some ⟨11, 1, 0, 1468419, 281221, 1, 262144⟩ := by
  decide +kernel

theorem context_11_281221_1468419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 281221 ⟨1468419, by decide⟩ :=
  accepted_of_selected 11 281221 ⟨1468419, by decide⟩ ⟨11, 1, 0, 1468419, 281221, 1, 262144⟩
    (by decide) selected_cut_51457

theorem selected_cut_51458 : selected 10 ⟨1484175, by decide⟩
    (prefixPartial 11 281222) = some ⟨11, 2, 0, 1484175, 281222, 1753, 262144⟩ := by
  decide +kernel

theorem context_11_281222_1484175 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 281222 ⟨1484175, by decide⟩ :=
  accepted_of_selected 11 281222 ⟨1484175, by decide⟩ ⟨11, 2, 0, 1484175, 281222, 1753, 262144⟩
    (by decide) selected_cut_51458

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
