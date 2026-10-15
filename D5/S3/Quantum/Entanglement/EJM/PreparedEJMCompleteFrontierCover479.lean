/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover478
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_45987 : selected 9 ⟨1279771, by decide⟩
    (prefixPartial 12 369504) = some ⟨12, 2, 0, 1279771, 369504, 1485, 65536⟩ := by
  decide +kernel

theorem context_12_369504_1279771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369504 ⟨1279771, by decide⟩ :=
  accepted_of_selected 12 369504 ⟨1279771, by decide⟩ ⟨12, 2, 0, 1279771, 369504, 1485, 65536⟩
    (by decide) selected_cut_45987

theorem selected_cut_45988 : selected 9 ⟨1256866, by decide⟩
    (prefixPartial 12 369505) = some ⟨12, 1, 0, 1256866, 369505, 1, 65536⟩ := by
  decide +kernel

theorem context_12_369505_1256866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369505 ⟨1256866, by decide⟩ :=
  accepted_of_selected 12 369505 ⟨1256866, by decide⟩ ⟨12, 1, 0, 1256866, 369505, 1, 65536⟩
    (by decide) selected_cut_45988

theorem selected_cut_45989 : selected 9 ⟨1279798, by decide⟩
    (prefixPartial 12 369506) = some ⟨12, 2, 0, 1279798, 369506, 1433, 65536⟩ := by
  decide +kernel

theorem context_12_369506_1279798 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369506 ⟨1279798, by decide⟩ :=
  accepted_of_selected 12 369506 ⟨1279798, by decide⟩ ⟨12, 2, 0, 1279798, 369506, 1433, 65536⟩
    (by decide) selected_cut_45989

theorem selected_cut_45990 : selected 9 ⟨1279820, by decide⟩
    (prefixPartial 12 369507) = some ⟨12, 2, 0, 1279820, 369507, 1481, 65536⟩ := by
  decide +kernel

theorem context_12_369507_1279820 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369507 ⟨1279820, by decide⟩ :=
  accepted_of_selected 12 369507 ⟨1279820, by decide⟩ ⟨12, 2, 0, 1279820, 369507, 1481, 65536⟩
    (by decide) selected_cut_45990

theorem unmarked_context_11_92376_1279821 : frontier 10 ⟨1279821, by decide⟩
    (prefixCache 11 92376) (prefixPartial 11 92376) = false := by
  decide +kernel

theorem node_context_11_92376_1279821 : EJMOriginalGlobalDAGData.nodes 10 ⟨1279821, by decide⟩ =
    .split (coordinate 11) (![⟨1279771, by decide⟩,⟨1256866, by decide⟩,⟨1279798, by decide⟩,⟨1279820, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92376_1279821 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92376 ⟨1279821, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92376
    ⟨1279821, by decide⟩ (by decide) (![⟨1279771, by decide⟩,⟨1256866, by decide⟩,⟨1279798, by decide⟩,⟨1279820, by decide⟩]) unmarked_context_11_92376_1279821 node_context_11_92376_1279821
  intro a
  fin_cases a
  · exact context_12_369504_1279771
  · exact context_12_369505_1256866
  · exact context_12_369506_1279798
  · exact context_12_369507_1279820

theorem selected_cut_45991 : selected 9 ⟨1279858, by decide⟩
    (prefixPartial 12 369508) = some ⟨12, 2, 0, 1279858, 369508, 1861, 65536⟩ := by
  decide +kernel

theorem context_12_369508_1279858 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369508 ⟨1279858, by decide⟩ :=
  accepted_of_selected 12 369508 ⟨1279858, by decide⟩ ⟨12, 2, 0, 1279858, 369508, 1861, 65536⟩
    (by decide) selected_cut_45991

theorem selected_cut_45992 : selected 9 ⟨1256866, by decide⟩
    (prefixPartial 12 369509) = some ⟨12, 1, 0, 1256866, 369509, 1, 65536⟩ := by
  decide +kernel

theorem context_12_369509_1256866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369509 ⟨1256866, by decide⟩ :=
  accepted_of_selected 12 369509 ⟨1256866, by decide⟩ ⟨12, 1, 0, 1256866, 369509, 1, 65536⟩
    (by decide) selected_cut_45992

theorem selected_cut_45993 : selected 9 ⟨1279885, by decide⟩
    (prefixPartial 12 369510) = some ⟨12, 2, 0, 1279885, 369510, 1605, 65536⟩ := by
  decide +kernel

theorem context_12_369510_1279885 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369510 ⟨1279885, by decide⟩ :=
  accepted_of_selected 12 369510 ⟨1279885, by decide⟩ ⟨12, 2, 0, 1279885, 369510, 1605, 65536⟩
    (by decide) selected_cut_45993

theorem selected_cut_45994 : selected 9 ⟨1279918, by decide⟩
    (prefixPartial 12 369511) = some ⟨12, 2, 0, 1279918, 369511, 1893, 65536⟩ := by
  decide +kernel

theorem context_12_369511_1279918 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369511 ⟨1279918, by decide⟩ :=
  accepted_of_selected 12 369511 ⟨1279918, by decide⟩ ⟨12, 2, 0, 1279918, 369511, 1893, 65536⟩
    (by decide) selected_cut_45994

theorem unmarked_context_11_92377_1279919 : frontier 10 ⟨1279919, by decide⟩
    (prefixCache 11 92377) (prefixPartial 11 92377) = false := by
  decide +kernel

theorem node_context_11_92377_1279919 : EJMOriginalGlobalDAGData.nodes 10 ⟨1279919, by decide⟩ =
    .split (coordinate 11) (![⟨1279858, by decide⟩,⟨1256866, by decide⟩,⟨1279885, by decide⟩,⟨1279918, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92377_1279919 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92377 ⟨1279919, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92377
    ⟨1279919, by decide⟩ (by decide) (![⟨1279858, by decide⟩,⟨1256866, by decide⟩,⟨1279885, by decide⟩,⟨1279918, by decide⟩]) unmarked_context_11_92377_1279919 node_context_11_92377_1279919
  intro a
  fin_cases a
  · exact context_12_369508_1279858
  · exact context_12_369509_1256866
  · exact context_12_369510_1279885
  · exact context_12_369511_1279918

theorem selected_cut_45995 : selected 10 ⟨1279978, by decide⟩
    (prefixPartial 11 92378) = some ⟨11, 2, 0, 1279978, 92378, 3073, 262144⟩ := by
  decide +kernel

theorem context_11_92378_1279978 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92378 ⟨1279978, by decide⟩ :=
  accepted_of_selected 11 92378 ⟨1279978, by decide⟩ ⟨11, 2, 0, 1279978, 92378, 3073, 262144⟩
    (by decide) selected_cut_45995

theorem selected_cut_45996 : selected 10 ⟨1280049, by decide⟩
    (prefixPartial 11 92379) = some ⟨11, 2, 0, 1280049, 92379, 3157, 262144⟩ := by
  decide +kernel

theorem context_11_92379_1280049 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92379 ⟨1280049, by decide⟩ :=
  accepted_of_selected 11 92379 ⟨1280049, by decide⟩ ⟨11, 2, 0, 1280049, 92379, 3157, 262144⟩
    (by decide) selected_cut_45996

theorem unmarked_context_10_23094_1280050 : frontier 11 ⟨1280050, by decide⟩
    (prefixCache 10 23094) (prefixPartial 10 23094) = false := by
  decide +kernel

theorem node_context_10_23094_1280050 : EJMOriginalGlobalDAGData.nodes 11 ⟨1280050, by decide⟩ =
    .split (coordinate 10) (![⟨1279821, by decide⟩,⟨1279919, by decide⟩,⟨1279978, by decide⟩,⟨1280049, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23094_1280050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23094 ⟨1280050, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23094
    ⟨1280050, by decide⟩ (by decide) (![⟨1279821, by decide⟩,⟨1279919, by decide⟩,⟨1279978, by decide⟩,⟨1280049, by decide⟩]) unmarked_context_10_23094_1280050 node_context_10_23094_1280050
  intro a
  fin_cases a
  · exact context_11_92376_1279821
  · exact context_11_92377_1279919
  · exact context_11_92378_1279978
  · exact context_11_92379_1280049

theorem selected_cut_45997 : selected 9 ⟨792260, by decide⟩
    (prefixPartial 12 369520) = some ⟨12, 1, 0, 792260, 369520, 1, 65536⟩ := by
  decide +kernel

theorem context_12_369520_792260 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369520 ⟨792260, by decide⟩ :=
  accepted_of_selected 12 369520 ⟨792260, by decide⟩ ⟨12, 1, 0, 792260, 369520, 1, 65536⟩
    (by decide) selected_cut_45997

theorem selected_cut_45998 : selected 9 ⟨1280071, by decide⟩
    (prefixPartial 12 369521) = some ⟨12, 2, 0, 1280071, 369521, 1401, 65536⟩ := by
  decide +kernel

theorem context_12_369521_1280071 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369521 ⟨1280071, by decide⟩ :=
  accepted_of_selected 12 369521 ⟨1280071, by decide⟩ ⟨12, 2, 0, 1280071, 369521, 1401, 65536⟩
    (by decide) selected_cut_45998

theorem selected_cut_45999 : selected 9 ⟨1280091, by decide⟩
    (prefixPartial 12 369522) = some ⟨12, 2, 0, 1280091, 369522, 1333, 65536⟩ := by
  decide +kernel

theorem context_12_369522_1280091 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369522 ⟨1280091, by decide⟩ :=
  accepted_of_selected 12 369522 ⟨1280091, by decide⟩ ⟨12, 2, 0, 1280091, 369522, 1333, 65536⟩
    (by decide) selected_cut_45999

theorem selected_cut_46000 : selected 9 ⟨1280112, by decide⟩
    (prefixPartial 12 369523) = some ⟨12, 2, 0, 1280112, 369523, 1397, 65536⟩ := by
  decide +kernel

theorem context_12_369523_1280112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369523 ⟨1280112, by decide⟩ :=
  accepted_of_selected 12 369523 ⟨1280112, by decide⟩ ⟨12, 2, 0, 1280112, 369523, 1397, 65536⟩
    (by decide) selected_cut_46000

theorem unmarked_context_11_92380_1280113 : frontier 10 ⟨1280113, by decide⟩
    (prefixCache 11 92380) (prefixPartial 11 92380) = false := by
  decide +kernel

theorem node_context_11_92380_1280113 : EJMOriginalGlobalDAGData.nodes 10 ⟨1280113, by decide⟩ =
    .split (coordinate 11) (![⟨792260, by decide⟩,⟨1280071, by decide⟩,⟨1280091, by decide⟩,⟨1280112, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92380_1280113 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92380 ⟨1280113, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92380
    ⟨1280113, by decide⟩ (by decide) (![⟨792260, by decide⟩,⟨1280071, by decide⟩,⟨1280091, by decide⟩,⟨1280112, by decide⟩]) unmarked_context_11_92380_1280113 node_context_11_92380_1280113
  intro a
  fin_cases a
  · exact context_12_369520_792260
  · exact context_12_369521_1280071
  · exact context_12_369522_1280091
  · exact context_12_369523_1280112

theorem selected_cut_46001 : selected 9 ⟨1280137, by decide⟩
    (prefixPartial 12 369524) = some ⟨12, 2, 0, 1280137, 369524, 1533, 65536⟩ := by
  decide +kernel

theorem context_12_369524_1280137 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369524 ⟨1280137, by decide⟩ :=
  accepted_of_selected 12 369524 ⟨1280137, by decide⟩ ⟨12, 2, 0, 1280137, 369524, 1533, 65536⟩
    (by decide) selected_cut_46001

theorem selected_cut_46002 : selected 9 ⟨410616, by decide⟩
    (prefixPartial 12 369525) = some ⟨12, 1, 0, 410616, 369525, 1, 65536⟩ := by
  decide +kernel

theorem context_12_369525_410616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369525 ⟨410616, by decide⟩ :=
  accepted_of_selected 12 369525 ⟨410616, by decide⟩ ⟨12, 1, 0, 410616, 369525, 1, 65536⟩
    (by decide) selected_cut_46002

theorem selected_cut_46003 : selected 9 ⟨1280162, by decide⟩
    (prefixPartial 12 369526) = some ⟨12, 2, 0, 1280162, 369526, 1389, 65536⟩ := by
  decide +kernel

theorem context_12_369526_1280162 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369526 ⟨1280162, by decide⟩ :=
  accepted_of_selected 12 369526 ⟨1280162, by decide⟩ ⟨12, 2, 0, 1280162, 369526, 1389, 65536⟩
    (by decide) selected_cut_46003

theorem selected_cut_46004 : selected 9 ⟨1280214, by decide⟩
    (prefixPartial 12 369527) = some ⟨12, 2, 0, 1280214, 369527, 1653, 65536⟩ := by
  decide +kernel

theorem context_12_369527_1280214 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369527 ⟨1280214, by decide⟩ :=
  accepted_of_selected 12 369527 ⟨1280214, by decide⟩ ⟨12, 2, 0, 1280214, 369527, 1653, 65536⟩
    (by decide) selected_cut_46004

theorem unmarked_context_11_92381_1280215 : frontier 10 ⟨1280215, by decide⟩
    (prefixCache 11 92381) (prefixPartial 11 92381) = false := by
  decide +kernel

theorem node_context_11_92381_1280215 : EJMOriginalGlobalDAGData.nodes 10 ⟨1280215, by decide⟩ =
    .split (coordinate 11) (![⟨1280137, by decide⟩,⟨410616, by decide⟩,⟨1280162, by decide⟩,⟨1280214, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92381_1280215 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92381 ⟨1280215, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92381
    ⟨1280215, by decide⟩ (by decide) (![⟨1280137, by decide⟩,⟨410616, by decide⟩,⟨1280162, by decide⟩,⟨1280214, by decide⟩]) unmarked_context_11_92381_1280215 node_context_11_92381_1280215
  intro a
  fin_cases a
  · exact context_12_369524_1280137
  · exact context_12_369525_410616
  · exact context_12_369526_1280162
  · exact context_12_369527_1280214

theorem selected_cut_46005 : selected 9 ⟨1280253, by decide⟩
    (prefixPartial 12 369528) = some ⟨12, 2, 0, 1280253, 369528, 1397, 65536⟩ := by
  decide +kernel

theorem context_12_369528_1280253 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369528 ⟨1280253, by decide⟩ :=
  accepted_of_selected 12 369528 ⟨1280253, by decide⟩ ⟨12, 2, 0, 1280253, 369528, 1397, 65536⟩
    (by decide) selected_cut_46005

theorem selected_cut_46006 : selected 9 ⟨753187, by decide⟩
    (prefixPartial 12 369529) = some ⟨12, 1, 0, 753187, 369529, 1, 65536⟩ := by
  decide +kernel

theorem context_12_369529_753187 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369529 ⟨753187, by decide⟩ :=
  accepted_of_selected 12 369529 ⟨753187, by decide⟩ ⟨12, 1, 0, 753187, 369529, 1, 65536⟩
    (by decide) selected_cut_46006

theorem selected_cut_46007 : selected 9 ⟨1280277, by decide⟩
    (prefixPartial 12 369530) = some ⟨12, 2, 0, 1280277, 369530, 1297, 65536⟩ := by
  decide +kernel

theorem context_12_369530_1280277 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369530 ⟨1280277, by decide⟩ :=
  accepted_of_selected 12 369530 ⟨1280277, by decide⟩ ⟨12, 2, 0, 1280277, 369530, 1297, 65536⟩
    (by decide) selected_cut_46007

theorem selected_cut_46008 : selected 9 ⟨1280302, by decide⟩
    (prefixPartial 12 369531) = some ⟨12, 2, 0, 1280302, 369531, 1413, 65536⟩ := by
  decide +kernel

theorem context_12_369531_1280302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369531 ⟨1280302, by decide⟩ :=
  accepted_of_selected 12 369531 ⟨1280302, by decide⟩ ⟨12, 2, 0, 1280302, 369531, 1413, 65536⟩
    (by decide) selected_cut_46008

theorem unmarked_context_11_92382_1280303 : frontier 10 ⟨1280303, by decide⟩
    (prefixCache 11 92382) (prefixPartial 11 92382) = false := by
  decide +kernel

theorem node_context_11_92382_1280303 : EJMOriginalGlobalDAGData.nodes 10 ⟨1280303, by decide⟩ =
    .split (coordinate 11) (![⟨1280253, by decide⟩,⟨753187, by decide⟩,⟨1280277, by decide⟩,⟨1280302, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92382_1280303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92382 ⟨1280303, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92382
    ⟨1280303, by decide⟩ (by decide) (![⟨1280253, by decide⟩,⟨753187, by decide⟩,⟨1280277, by decide⟩,⟨1280302, by decide⟩]) unmarked_context_11_92382_1280303 node_context_11_92382_1280303
  intro a
  fin_cases a
  · exact context_12_369528_1280253
  · exact context_12_369529_753187
  · exact context_12_369530_1280277
  · exact context_12_369531_1280302

theorem selected_cut_46009 : selected 10 ⟨1280360, by decide⟩
    (prefixPartial 11 92383) = some ⟨11, 2, 0, 1280360, 92383, 2461, 262144⟩ := by
  decide +kernel

theorem context_11_92383_1280360 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92383 ⟨1280360, by decide⟩ :=
  accepted_of_selected 11 92383 ⟨1280360, by decide⟩ ⟨11, 2, 0, 1280360, 92383, 2461, 262144⟩
    (by decide) selected_cut_46009

theorem unmarked_context_10_23095_1280361 : frontier 11 ⟨1280361, by decide⟩
    (prefixCache 10 23095) (prefixPartial 10 23095) = false := by
  decide +kernel

theorem node_context_10_23095_1280361 : EJMOriginalGlobalDAGData.nodes 11 ⟨1280361, by decide⟩ =
    .split (coordinate 10) (![⟨1280113, by decide⟩,⟨1280215, by decide⟩,⟨1280303, by decide⟩,⟨1280360, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23095_1280361 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23095 ⟨1280361, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23095
    ⟨1280361, by decide⟩ (by decide) (![⟨1280113, by decide⟩,⟨1280215, by decide⟩,⟨1280303, by decide⟩,⟨1280360, by decide⟩]) unmarked_context_10_23095_1280361 node_context_10_23095_1280361
  intro a
  fin_cases a
  · exact context_11_92380_1280113
  · exact context_11_92381_1280215
  · exact context_11_92382_1280303
  · exact context_11_92383_1280360

theorem unmarked_context_9_5773_1280362 : frontier 12 ⟨1280362, by decide⟩
    (prefixCache 9 5773) (prefixPartial 9 5773) = false := by
  decide +kernel

theorem node_context_9_5773_1280362 : EJMOriginalGlobalDAGData.nodes 12 ⟨1280362, by decide⟩ =
    .split (coordinate 9) (![⟨1279745, by decide⟩,⟨893098, by decide⟩,⟨1280050, by decide⟩,⟨1280361, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5773_1280362 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5773 ⟨1280362, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5773
    ⟨1280362, by decide⟩ (by decide) (![⟨1279745, by decide⟩,⟨893098, by decide⟩,⟨1280050, by decide⟩,⟨1280361, by decide⟩]) unmarked_context_9_5773_1280362 node_context_9_5773_1280362
  intro a
  fin_cases a
  · exact context_10_23092_1279745
  · exact context_10_23093_893098
  · exact context_10_23094_1280050
  · exact context_10_23095_1280361

theorem selected_cut_46010 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 92384) = some ⟨11, 1, 0, 907917, 92384, 1, 262144⟩ := by
  decide +kernel

theorem context_11_92384_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92384 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 92384 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 92384, 1, 262144⟩
    (by decide) selected_cut_46010

theorem selected_cut_46011 : selected 10 ⟨1280418, by decide⟩
    (prefixPartial 11 92385) = some ⟨11, 2, 0, 1280418, 92385, 3209, 262144⟩ := by
  decide +kernel

theorem context_11_92385_1280418 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92385 ⟨1280418, by decide⟩ :=
  accepted_of_selected 11 92385 ⟨1280418, by decide⟩ ⟨11, 2, 0, 1280418, 92385, 3209, 262144⟩
    (by decide) selected_cut_46011

theorem selected_cut_46012 : selected 10 ⟨1280465, by decide⟩
    (prefixPartial 11 92386) = some ⟨11, 2, 0, 1280465, 92386, 2857, 262144⟩ := by
  decide +kernel

theorem context_11_92386_1280465 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92386 ⟨1280465, by decide⟩ :=
  accepted_of_selected 11 92386 ⟨1280465, by decide⟩ ⟨11, 2, 0, 1280465, 92386, 2857, 262144⟩
    (by decide) selected_cut_46012

theorem selected_cut_46013 : selected 10 ⟨1280491, by decide⟩
    (prefixPartial 11 92387) = some ⟨11, 2, 0, 1280491, 92387, 1669, 262144⟩ := by
  decide +kernel

theorem context_11_92387_1280491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92387 ⟨1280491, by decide⟩ :=
  accepted_of_selected 11 92387 ⟨1280491, by decide⟩ ⟨11, 2, 0, 1280491, 92387, 1669, 262144⟩
    (by decide) selected_cut_46013

theorem unmarked_context_10_23096_1280492 : frontier 11 ⟨1280492, by decide⟩
    (prefixCache 10 23096) (prefixPartial 10 23096) = false := by
  decide +kernel

theorem node_context_10_23096_1280492 : EJMOriginalGlobalDAGData.nodes 11 ⟨1280492, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨1280418, by decide⟩,⟨1280465, by decide⟩,⟨1280491, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23096_1280492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23096 ⟨1280492, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23096
    ⟨1280492, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨1280418, by decide⟩,⟨1280465, by decide⟩,⟨1280491, by decide⟩]) unmarked_context_10_23096_1280492 node_context_10_23096_1280492
  intro a
  fin_cases a
  · exact context_11_92384_907917
  · exact context_11_92385_1280418
  · exact context_11_92386_1280465
  · exact context_11_92387_1280491

theorem selected_cut_46014 : selected 10 ⟨1280536, by decide⟩
    (prefixPartial 11 92388) = some ⟨11, 2, 0, 1280536, 92388, 2689, 262144⟩ := by
  decide +kernel

theorem context_11_92388_1280536 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92388 ⟨1280536, by decide⟩ :=
  accepted_of_selected 11 92388 ⟨1280536, by decide⟩ ⟨11, 2, 0, 1280536, 92388, 2689, 262144⟩
    (by decide) selected_cut_46014

theorem selected_cut_46015 : selected 10 ⟨1280573, by decide⟩
    (prefixPartial 11 92389) = some ⟨11, 2, 0, 1280573, 92389, 1953, 262144⟩ := by
  decide +kernel

theorem context_11_92389_1280573 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92389 ⟨1280573, by decide⟩ :=
  accepted_of_selected 11 92389 ⟨1280573, by decide⟩ ⟨11, 2, 0, 1280573, 92389, 1953, 262144⟩
    (by decide) selected_cut_46015

theorem selected_cut_46016 : selected 10 ⟨1280620, by decide⟩
    (prefixPartial 11 92390) = some ⟨11, 2, 0, 1280620, 92390, 2629, 262144⟩ := by
  decide +kernel

theorem context_11_92390_1280620 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92390 ⟨1280620, by decide⟩ :=
  accepted_of_selected 11 92390 ⟨1280620, by decide⟩ ⟨11, 2, 0, 1280620, 92390, 2629, 262144⟩
    (by decide) selected_cut_46016

theorem selected_cut_46017 : selected 10 ⟨1280650, by decide⟩
    (prefixPartial 11 92391) = some ⟨11, 2, 0, 1280650, 92391, 1481, 262144⟩ := by
  decide +kernel

theorem context_11_92391_1280650 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92391 ⟨1280650, by decide⟩ :=
  accepted_of_selected 11 92391 ⟨1280650, by decide⟩ ⟨11, 2, 0, 1280650, 92391, 1481, 262144⟩
    (by decide) selected_cut_46017

theorem unmarked_context_10_23097_1280651 : frontier 11 ⟨1280651, by decide⟩
    (prefixCache 10 23097) (prefixPartial 10 23097) = false := by
  decide +kernel

theorem node_context_10_23097_1280651 : EJMOriginalGlobalDAGData.nodes 11 ⟨1280651, by decide⟩ =
    .split (coordinate 10) (![⟨1280536, by decide⟩,⟨1280573, by decide⟩,⟨1280620, by decide⟩,⟨1280650, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23097_1280651 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23097 ⟨1280651, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23097
    ⟨1280651, by decide⟩ (by decide) (![⟨1280536, by decide⟩,⟨1280573, by decide⟩,⟨1280620, by decide⟩,⟨1280650, by decide⟩]) unmarked_context_10_23097_1280651 node_context_10_23097_1280651
  intro a
  fin_cases a
  · exact context_11_92388_1280536
  · exact context_11_92389_1280573
  · exact context_11_92390_1280620
  · exact context_11_92391_1280650

theorem selected_cut_46018 : selected 11 ⟨1280702, by decide⟩
    (prefixPartial 10 23098) = some ⟨10, 2, 0, 1280702, 23098, 2913, 1048576⟩ := by
  decide +kernel

theorem context_10_23098_1280702 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23098 ⟨1280702, by decide⟩ :=
  accepted_of_selected 10 23098 ⟨1280702, by decide⟩ ⟨10, 2, 0, 1280702, 23098, 2913, 1048576⟩
    (by decide) selected_cut_46018

theorem selected_cut_46019 : selected 10 ⟨1280728, by decide⟩
    (prefixPartial 11 92396) = some ⟨11, 2, 0, 1280728, 92396, 1257, 262144⟩ := by
  decide +kernel

theorem context_11_92396_1280728 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92396 ⟨1280728, by decide⟩ :=
  accepted_of_selected 11 92396 ⟨1280728, by decide⟩ ⟨11, 2, 0, 1280728, 92396, 1257, 262144⟩
    (by decide) selected_cut_46019

theorem selected_cut_46020 : selected 10 ⟨1280761, by decide⟩
    (prefixPartial 11 92397) = some ⟨11, 2, 0, 1280761, 92397, 1965, 262144⟩ := by
  decide +kernel

theorem context_11_92397_1280761 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92397 ⟨1280761, by decide⟩ :=
  accepted_of_selected 11 92397 ⟨1280761, by decide⟩ ⟨11, 2, 0, 1280761, 92397, 1965, 262144⟩
    (by decide) selected_cut_46020

theorem selected_cut_46021 : selected 10 ⟨1280801, by decide⟩
    (prefixPartial 11 92398) = some ⟨11, 2, 0, 1280801, 92398, 1709, 262144⟩ := by
  decide +kernel

theorem context_11_92398_1280801 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92398 ⟨1280801, by decide⟩ :=
  accepted_of_selected 11 92398 ⟨1280801, by decide⟩ ⟨11, 2, 0, 1280801, 92398, 1709, 262144⟩
    (by decide) selected_cut_46021

theorem selected_cut_46022 : selected 10 ⟨1280814, by decide⟩
    (prefixPartial 11 92399) = some ⟨11, 2, 0, 1280814, 92399, 569, 262144⟩ := by
  decide +kernel

theorem context_11_92399_1280814 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92399 ⟨1280814, by decide⟩ :=
  accepted_of_selected 11 92399 ⟨1280814, by decide⟩ ⟨11, 2, 0, 1280814, 92399, 569, 262144⟩
    (by decide) selected_cut_46022

theorem unmarked_context_10_23099_1280815 : frontier 11 ⟨1280815, by decide⟩
    (prefixCache 10 23099) (prefixPartial 10 23099) = false := by
  decide +kernel

theorem node_context_10_23099_1280815 : EJMOriginalGlobalDAGData.nodes 11 ⟨1280815, by decide⟩ =
    .split (coordinate 10) (![⟨1280728, by decide⟩,⟨1280761, by decide⟩,⟨1280801, by decide⟩,⟨1280814, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23099_1280815 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23099 ⟨1280815, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23099
    ⟨1280815, by decide⟩ (by decide) (![⟨1280728, by decide⟩,⟨1280761, by decide⟩,⟨1280801, by decide⟩,⟨1280814, by decide⟩]) unmarked_context_10_23099_1280815 node_context_10_23099_1280815
  intro a
  fin_cases a
  · exact context_11_92396_1280728
  · exact context_11_92397_1280761
  · exact context_11_92398_1280801
  · exact context_11_92399_1280814

theorem unmarked_context_9_5774_1280816 : frontier 12 ⟨1280816, by decide⟩
    (prefixCache 9 5774) (prefixPartial 9 5774) = false := by
  decide +kernel

theorem node_context_9_5774_1280816 : EJMOriginalGlobalDAGData.nodes 12 ⟨1280816, by decide⟩ =
    .split (coordinate 9) (![⟨1280492, by decide⟩,⟨1280651, by decide⟩,⟨1280702, by decide⟩,⟨1280815, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5774_1280816 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5774 ⟨1280816, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5774
    ⟨1280816, by decide⟩ (by decide) (![⟨1280492, by decide⟩,⟨1280651, by decide⟩,⟨1280702, by decide⟩,⟨1280815, by decide⟩]) unmarked_context_9_5774_1280816 node_context_9_5774_1280816
  intro a
  fin_cases a
  · exact context_10_23096_1280492
  · exact context_10_23097_1280651
  · exact context_10_23098_1280702
  · exact context_10_23099_1280815

theorem selected_cut_46023 : selected 11 ⟨1280881, by decide⟩
    (prefixPartial 10 23100) = some ⟨10, 2, 0, 1280881, 23100, 3817, 1048576⟩ := by
  decide +kernel

theorem context_10_23100_1280881 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23100 ⟨1280881, by decide⟩ :=
  accepted_of_selected 10 23100 ⟨1280881, by decide⟩ ⟨10, 2, 0, 1280881, 23100, 3817, 1048576⟩
    (by decide) selected_cut_46023

theorem selected_cut_46024 : selected 11 ⟨1280939, by decide⟩
    (prefixPartial 10 23101) = some ⟨10, 2, 0, 1280939, 23101, 3317, 1048576⟩ := by
  decide +kernel

theorem context_10_23101_1280939 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23101 ⟨1280939, by decide⟩ :=
  accepted_of_selected 10 23101 ⟨1280939, by decide⟩ ⟨10, 2, 0, 1280939, 23101, 3317, 1048576⟩
    (by decide) selected_cut_46024

theorem selected_cut_46025 : selected 11 ⟨1281001, by decide⟩
    (prefixPartial 10 23102) = some ⟨10, 2, 0, 1281001, 23102, 2029, 1048576⟩ := by
  decide +kernel

theorem context_10_23102_1281001 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23102 ⟨1281001, by decide⟩ :=
  accepted_of_selected 10 23102 ⟨1281001, by decide⟩ ⟨10, 2, 0, 1281001, 23102, 2029, 1048576⟩
    (by decide) selected_cut_46025

theorem selected_cut_46026 : selected 11 ⟨1281016, by decide⟩
    (prefixPartial 10 23103) = some ⟨10, 2, 0, 1281016, 23103, 325, 1048576⟩ := by
  decide +kernel

theorem context_10_23103_1281016 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23103 ⟨1281016, by decide⟩ :=
  accepted_of_selected 10 23103 ⟨1281016, by decide⟩ ⟨10, 2, 0, 1281016, 23103, 325, 1048576⟩
    (by decide) selected_cut_46026

theorem unmarked_context_9_5775_1281017 : frontier 12 ⟨1281017, by decide⟩
    (prefixCache 9 5775) (prefixPartial 9 5775) = false := by
  decide +kernel

theorem node_context_9_5775_1281017 : EJMOriginalGlobalDAGData.nodes 12 ⟨1281017, by decide⟩ =
    .split (coordinate 9) (![⟨1280881, by decide⟩,⟨1280939, by decide⟩,⟨1281001, by decide⟩,⟨1281016, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5775_1281017 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5775 ⟨1281017, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5775
    ⟨1281017, by decide⟩ (by decide) (![⟨1280881, by decide⟩,⟨1280939, by decide⟩,⟨1281001, by decide⟩,⟨1281016, by decide⟩]) unmarked_context_9_5775_1281017 node_context_9_5775_1281017
  intro a
  fin_cases a
  · exact context_10_23100_1280881
  · exact context_10_23101_1280939
  · exact context_10_23102_1281001
  · exact context_10_23103_1281016

theorem unmarked_context_8_1443_1281018 : frontier 13 ⟨1281018, by decide⟩
    (prefixCache 8 1443) (prefixPartial 8 1443) = false := by
  decide +kernel

theorem node_context_8_1443_1281018 : EJMOriginalGlobalDAGData.nodes 13 ⟨1281018, by decide⟩ =
    .split (coordinate 8) (![⟨1279417, by decide⟩,⟨1280362, by decide⟩,⟨1280816, by decide⟩,⟨1281017, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1443_1281018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1443 ⟨1281018, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1443
    ⟨1281018, by decide⟩ (by decide) (![⟨1279417, by decide⟩,⟨1280362, by decide⟩,⟨1280816, by decide⟩,⟨1281017, by decide⟩]) unmarked_context_8_1443_1281018 node_context_8_1443_1281018
  intro a
  fin_cases a
  · exact context_9_5772_1279417
  · exact context_9_5773_1280362
  · exact context_9_5774_1280816
  · exact context_9_5775_1281017

theorem unmarked_context_7_360_1281019 : frontier 14 ⟨1281019, by decide⟩
    (prefixCache 7 360) (prefixPartial 7 360) = false := by
  decide +kernel

theorem node_context_7_360_1281019 : EJMOriginalGlobalDAGData.nodes 14 ⟨1281019, by decide⟩ =
    .split (coordinate 7) (![⟨1270133, by decide⟩,⟨1273470, by decide⟩,⟨1276986, by decide⟩,⟨1281018, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_360_1281019 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 360 ⟨1281019, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 360
    ⟨1281019, by decide⟩ (by decide) (![⟨1270133, by decide⟩,⟨1273470, by decide⟩,⟨1276986, by decide⟩,⟨1281018, by decide⟩]) unmarked_context_7_360_1281019 node_context_7_360_1281019
  intro a
  fin_cases a
  · exact context_8_1440_1270133
  · exact context_8_1441_1273470
  · exact context_8_1442_1276986
  · exact context_8_1443_1281018

theorem selected_cut_46027 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 92416) = some ⟨11, 1, 0, 434745, 92416, 1, 262144⟩ := by
  decide +kernel

theorem context_11_92416_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92416 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 92416 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 92416, 1, 262144⟩
    (by decide) selected_cut_46027

theorem selected_cut_46028 : selected 10 ⟨167448, by decide⟩
    (prefixPartial 11 92417) = some ⟨11, 1, 0, 167448, 92417, 1, 262144⟩ := by
  decide +kernel

theorem context_11_92417_167448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92417 ⟨167448, by decide⟩ :=
  accepted_of_selected 11 92417 ⟨167448, by decide⟩ ⟨11, 1, 0, 167448, 92417, 1, 262144⟩
    (by decide) selected_cut_46028

theorem selected_cut_46029 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 369672) = some ⟨12, 1, 0, 448748, 369672, 1, 65536⟩ := by
  decide +kernel

theorem context_12_369672_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369672 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 369672 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 369672, 1, 65536⟩
    (by decide) selected_cut_46029

theorem selected_cut_46030 : selected 9 ⟨1281112, by decide⟩
    (prefixPartial 12 369673) = some ⟨12, 2, 0, 1281112, 369673, 2825, 65536⟩ := by
  decide +kernel

theorem context_12_369673_1281112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369673 ⟨1281112, by decide⟩ :=
  accepted_of_selected 12 369673 ⟨1281112, by decide⟩ ⟨12, 2, 0, 1281112, 369673, 2825, 65536⟩
    (by decide) selected_cut_46030

theorem selected_cut_46031 : selected 9 ⟨188189, by decide⟩
    (prefixPartial 12 369674) = some ⟨12, 1, 0, 188189, 369674, 1, 65536⟩ := by
  decide +kernel

theorem context_12_369674_188189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369674 ⟨188189, by decide⟩ :=
  accepted_of_selected 12 369674 ⟨188189, by decide⟩ ⟨12, 1, 0, 188189, 369674, 1, 65536⟩
    (by decide) selected_cut_46031

theorem selected_cut_46032 : selected 9 ⟨1281242, by decide⟩
    (prefixPartial 12 369675) = some ⟨12, 2, 0, 1281242, 369675, 3877, 65536⟩ := by
  decide +kernel

theorem context_12_369675_1281242 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369675 ⟨1281242, by decide⟩ :=
  accepted_of_selected 12 369675 ⟨1281242, by decide⟩ ⟨12, 2, 0, 1281242, 369675, 3877, 65536⟩
    (by decide) selected_cut_46032

theorem unmarked_context_11_92418_1281243 : frontier 10 ⟨1281243, by decide⟩
    (prefixCache 11 92418) (prefixPartial 11 92418) = false := by
  decide +kernel

theorem node_context_11_92418_1281243 : EJMOriginalGlobalDAGData.nodes 10 ⟨1281243, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1281112, by decide⟩,⟨188189, by decide⟩,⟨1281242, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92418_1281243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92418 ⟨1281243, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92418
    ⟨1281243, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1281112, by decide⟩,⟨188189, by decide⟩,⟨1281242, by decide⟩]) unmarked_context_11_92418_1281243 node_context_11_92418_1281243
  intro a
  fin_cases a
  · exact context_12_369672_448748
  · exact context_12_369673_1281112
  · exact context_12_369674_188189
  · exact context_12_369675_1281242

theorem selected_cut_46033 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 369676) = some ⟨12, 1, 0, 448748, 369676, 1, 65536⟩ := by
  decide +kernel

theorem context_12_369676_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369676 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 369676 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 369676, 1, 65536⟩
    (by decide) selected_cut_46033

theorem selected_cut_46034 : selected 9 ⟨1281306, by decide⟩
    (prefixPartial 12 369677) = some ⟨12, 2, 0, 1281306, 369677, 2729, 65536⟩ := by
  decide +kernel

theorem context_12_369677_1281306 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369677 ⟨1281306, by decide⟩ :=
  accepted_of_selected 12 369677 ⟨1281306, by decide⟩ ⟨12, 2, 0, 1281306, 369677, 2729, 65536⟩
    (by decide) selected_cut_46034

theorem selected_cut_46035 : selected 9 ⟨1281378, by decide⟩
    (prefixPartial 12 369678) = some ⟨12, 2, 0, 1281378, 369678, 3065, 65536⟩ := by
  decide +kernel

theorem context_12_369678_1281378 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369678 ⟨1281378, by decide⟩ :=
  accepted_of_selected 12 369678 ⟨1281378, by decide⟩ ⟨12, 2, 0, 1281378, 369678, 3065, 65536⟩
    (by decide) selected_cut_46035

theorem selected_cut_46036 : selected 9 ⟨296530, by decide⟩
    (prefixPartial 12 369679) = some ⟨12, 1, 0, 296530, 369679, 1, 65536⟩ := by
  decide +kernel

theorem context_12_369679_296530 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369679 ⟨296530, by decide⟩ :=
  accepted_of_selected 12 369679 ⟨296530, by decide⟩ ⟨12, 1, 0, 296530, 369679, 1, 65536⟩
    (by decide) selected_cut_46036

theorem unmarked_context_11_92419_1281379 : frontier 10 ⟨1281379, by decide⟩
    (prefixCache 11 92419) (prefixPartial 11 92419) = false := by
  decide +kernel

theorem node_context_11_92419_1281379 : EJMOriginalGlobalDAGData.nodes 10 ⟨1281379, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1281306, by decide⟩,⟨1281378, by decide⟩,⟨296530, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92419_1281379 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92419 ⟨1281379, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92419
    ⟨1281379, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1281306, by decide⟩,⟨1281378, by decide⟩,⟨296530, by decide⟩]) unmarked_context_11_92419_1281379 node_context_11_92419_1281379
  intro a
  fin_cases a
  · exact context_12_369676_448748
  · exact context_12_369677_1281306
  · exact context_12_369678_1281378
  · exact context_12_369679_296530

theorem unmarked_context_10_23104_1281380 : frontier 11 ⟨1281380, by decide⟩
    (prefixCache 10 23104) (prefixPartial 10 23104) = false := by
  decide +kernel

theorem node_context_10_23104_1281380 : EJMOriginalGlobalDAGData.nodes 11 ⟨1281380, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨167448, by decide⟩,⟨1281243, by decide⟩,⟨1281379, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23104_1281380 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23104 ⟨1281380, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23104
    ⟨1281380, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨167448, by decide⟩,⟨1281243, by decide⟩,⟨1281379, by decide⟩]) unmarked_context_10_23104_1281380 node_context_10_23104_1281380
  intro a
  fin_cases a
  · exact context_11_92416_434745
  · exact context_11_92417_167448
  · exact context_11_92418_1281243
  · exact context_11_92419_1281379

theorem selected_cut_46037 : selected 9 ⟨985390, by decide⟩
    (prefixPartial 12 369680) = some ⟨12, 1, 0, 985390, 369680, 1, 65536⟩ := by
  decide +kernel

theorem context_12_369680_985390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369680 ⟨985390, by decide⟩ :=
  accepted_of_selected 12 369680 ⟨985390, by decide⟩ ⟨12, 1, 0, 985390, 369680, 1, 65536⟩
    (by decide) selected_cut_46037

theorem selected_cut_46038 : selected 9 ⟨1281424, by decide⟩
    (prefixPartial 12 369681) = some ⟨12, 2, 0, 1281424, 369681, 2181, 65536⟩ := by
  decide +kernel

theorem context_12_369681_1281424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369681 ⟨1281424, by decide⟩ :=
  accepted_of_selected 12 369681 ⟨1281424, by decide⟩ ⟨12, 2, 0, 1281424, 369681, 2181, 65536⟩
    (by decide) selected_cut_46038

theorem selected_cut_46039 : selected 9 ⟨1281476, by decide⟩
    (prefixPartial 12 369682) = some ⟨12, 2, 0, 1281476, 369682, 2465, 65536⟩ := by
  decide +kernel

theorem context_12_369682_1281476 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369682 ⟨1281476, by decide⟩ :=
  accepted_of_selected 12 369682 ⟨1281476, by decide⟩ ⟨12, 2, 0, 1281476, 369682, 2465, 65536⟩
    (by decide) selected_cut_46039

theorem selected_cut_46040 : selected 9 ⟨1281556, by decide⟩
    (prefixPartial 12 369683) = some ⟨12, 2, 0, 1281556, 369683, 3085, 65536⟩ := by
  decide +kernel

theorem context_12_369683_1281556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369683 ⟨1281556, by decide⟩ :=
  accepted_of_selected 12 369683 ⟨1281556, by decide⟩ ⟨12, 2, 0, 1281556, 369683, 3085, 65536⟩
    (by decide) selected_cut_46040

theorem unmarked_context_11_92420_1281557 : frontier 10 ⟨1281557, by decide⟩
    (prefixCache 11 92420) (prefixPartial 11 92420) = false := by
  decide +kernel

theorem node_context_11_92420_1281557 : EJMOriginalGlobalDAGData.nodes 10 ⟨1281557, by decide⟩ =
    .split (coordinate 11) (![⟨985390, by decide⟩,⟨1281424, by decide⟩,⟨1281476, by decide⟩,⟨1281556, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92420_1281557 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92420 ⟨1281557, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92420
    ⟨1281557, by decide⟩ (by decide) (![⟨985390, by decide⟩,⟨1281424, by decide⟩,⟨1281476, by decide⟩,⟨1281556, by decide⟩]) unmarked_context_11_92420_1281557 node_context_11_92420_1281557
  intro a
  fin_cases a
  · exact context_12_369680_985390
  · exact context_12_369681_1281424
  · exact context_12_369682_1281476
  · exact context_12_369683_1281556

theorem selected_cut_46041 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 92421) = some ⟨11, 1, 0, 892405, 92421, 1, 262144⟩ := by
  decide +kernel

theorem context_11_92421_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92421 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 92421 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 92421, 1, 262144⟩
    (by decide) selected_cut_46041

theorem selected_cut_46042 : selected 9 ⟨994572, by decide⟩
    (prefixPartial 12 369688) = some ⟨12, 1, 0, 994572, 369688, 1, 65536⟩ := by
  decide +kernel

theorem context_12_369688_994572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369688 ⟨994572, by decide⟩ :=
  accepted_of_selected 12 369688 ⟨994572, by decide⟩ ⟨12, 1, 0, 994572, 369688, 1, 65536⟩
    (by decide) selected_cut_46042

theorem selected_cut_46043 : selected 9 ⟨1281597, by decide⟩
    (prefixPartial 12 369689) = some ⟨12, 2, 0, 1281597, 369689, 2261, 65536⟩ := by
  decide +kernel

theorem context_12_369689_1281597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369689 ⟨1281597, by decide⟩ :=
  accepted_of_selected 12 369689 ⟨1281597, by decide⟩ ⟨12, 2, 0, 1281597, 369689, 2261, 65536⟩
    (by decide) selected_cut_46043

theorem selected_cut_46044 : selected 9 ⟨806997, by decide⟩
    (prefixPartial 12 369690) = some ⟨12, 1, 0, 806997, 369690, 1, 65536⟩ := by
  decide +kernel

theorem context_12_369690_806997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369690 ⟨806997, by decide⟩ :=
  accepted_of_selected 12 369690 ⟨806997, by decide⟩ ⟨12, 1, 0, 806997, 369690, 1, 65536⟩
    (by decide) selected_cut_46044

theorem selected_cut_46045 : selected 9 ⟨1281678, by decide⟩
    (prefixPartial 12 369691) = some ⟨12, 2, 0, 1281678, 369691, 3265, 65536⟩ := by
  decide +kernel

theorem context_12_369691_1281678 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369691 ⟨1281678, by decide⟩ :=
  accepted_of_selected 12 369691 ⟨1281678, by decide⟩ ⟨12, 2, 0, 1281678, 369691, 3265, 65536⟩
    (by decide) selected_cut_46045

theorem unmarked_context_11_92422_1281679 : frontier 10 ⟨1281679, by decide⟩
    (prefixCache 11 92422) (prefixPartial 11 92422) = false := by
  decide +kernel

theorem node_context_11_92422_1281679 : EJMOriginalGlobalDAGData.nodes 10 ⟨1281679, by decide⟩ =
    .split (coordinate 11) (![⟨994572, by decide⟩,⟨1281597, by decide⟩,⟨806997, by decide⟩,⟨1281678, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92422_1281679 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92422 ⟨1281679, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92422
    ⟨1281679, by decide⟩ (by decide) (![⟨994572, by decide⟩,⟨1281597, by decide⟩,⟨806997, by decide⟩,⟨1281678, by decide⟩]) unmarked_context_11_92422_1281679 node_context_11_92422_1281679
  intro a
  fin_cases a
  · exact context_12_369688_994572
  · exact context_12_369689_1281597
  · exact context_12_369690_806997
  · exact context_12_369691_1281678

theorem selected_cut_46046 : selected 9 ⟨1281738, by decide⟩
    (prefixPartial 12 369692) = some ⟨12, 2, 0, 1281738, 369692, 2737, 65536⟩ := by
  decide +kernel

theorem context_12_369692_1281738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369692 ⟨1281738, by decide⟩ :=
  accepted_of_selected 12 369692 ⟨1281738, by decide⟩ ⟨12, 2, 0, 1281738, 369692, 2737, 65536⟩
    (by decide) selected_cut_46046

theorem selected_cut_46047 : selected 9 ⟨1281777, by decide⟩
    (prefixPartial 12 369693) = some ⟨12, 2, 0, 1281777, 369693, 2333, 65536⟩ := by
  decide +kernel

theorem context_12_369693_1281777 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369693 ⟨1281777, by decide⟩ :=
  accepted_of_selected 12 369693 ⟨1281777, by decide⟩ ⟨12, 2, 0, 1281777, 369693, 2333, 65536⟩
    (by decide) selected_cut_46047

theorem selected_cut_46048 : selected 9 ⟨1281842, by decide⟩
    (prefixPartial 12 369694) = some ⟨12, 2, 0, 1281842, 369694, 2833, 65536⟩ := by
  decide +kernel

theorem context_12_369694_1281842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369694 ⟨1281842, by decide⟩ :=
  accepted_of_selected 12 369694 ⟨1281842, by decide⟩ ⟨12, 2, 0, 1281842, 369694, 2833, 65536⟩
    (by decide) selected_cut_46048

theorem selected_cut_46049 : selected 9 ⟨1281916, by decide⟩
    (prefixPartial 12 369695) = some ⟨12, 2, 0, 1281916, 369695, 3157, 65536⟩ := by
  decide +kernel

theorem context_12_369695_1281916 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369695 ⟨1281916, by decide⟩ :=
  accepted_of_selected 12 369695 ⟨1281916, by decide⟩ ⟨12, 2, 0, 1281916, 369695, 3157, 65536⟩
    (by decide) selected_cut_46049

theorem unmarked_context_11_92423_1281917 : frontier 10 ⟨1281917, by decide⟩
    (prefixCache 11 92423) (prefixPartial 11 92423) = false := by
  decide +kernel

theorem node_context_11_92423_1281917 : EJMOriginalGlobalDAGData.nodes 10 ⟨1281917, by decide⟩ =
    .split (coordinate 11) (![⟨1281738, by decide⟩,⟨1281777, by decide⟩,⟨1281842, by decide⟩,⟨1281916, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92423_1281917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92423 ⟨1281917, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92423
    ⟨1281917, by decide⟩ (by decide) (![⟨1281738, by decide⟩,⟨1281777, by decide⟩,⟨1281842, by decide⟩,⟨1281916, by decide⟩]) unmarked_context_11_92423_1281917 node_context_11_92423_1281917
  intro a
  fin_cases a
  · exact context_12_369692_1281738
  · exact context_12_369693_1281777
  · exact context_12_369694_1281842
  · exact context_12_369695_1281916

theorem unmarked_context_10_23105_1281918 : frontier 11 ⟨1281918, by decide⟩
    (prefixCache 10 23105) (prefixPartial 10 23105) = false := by
  decide +kernel

theorem node_context_10_23105_1281918 : EJMOriginalGlobalDAGData.nodes 11 ⟨1281918, by decide⟩ =
    .split (coordinate 10) (![⟨1281557, by decide⟩,⟨892405, by decide⟩,⟨1281679, by decide⟩,⟨1281917, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23105_1281918 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23105 ⟨1281918, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23105
    ⟨1281918, by decide⟩ (by decide) (![⟨1281557, by decide⟩,⟨892405, by decide⟩,⟨1281679, by decide⟩,⟨1281917, by decide⟩]) unmarked_context_10_23105_1281918 node_context_10_23105_1281918
  intro a
  fin_cases a
  · exact context_11_92420_1281557
  · exact context_11_92421_892405
  · exact context_11_92422_1281679
  · exact context_11_92423_1281917

theorem selected_cut_46050 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 369696) = some ⟨12, 1, 0, 435790, 369696, 1, 65536⟩ := by
  decide +kernel

theorem context_12_369696_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369696 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 369696 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 369696, 1, 65536⟩
    (by decide) selected_cut_46050

theorem selected_cut_46051 : selected 9 ⟨1281968, by decide⟩
    (prefixPartial 12 369697) = some ⟨12, 2, 0, 1281968, 369697, 2297, 65536⟩ := by
  decide +kernel

theorem context_12_369697_1281968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369697 ⟨1281968, by decide⟩ :=
  accepted_of_selected 12 369697 ⟨1281968, by decide⟩ ⟨12, 2, 0, 1281968, 369697, 2297, 65536⟩
    (by decide) selected_cut_46051

theorem selected_cut_46052 : selected 9 ⟨1282024, by decide⟩
    (prefixPartial 12 369698) = some ⟨12, 2, 0, 1282024, 369698, 2533, 65536⟩ := by
  decide +kernel

theorem context_12_369698_1282024 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369698 ⟨1282024, by decide⟩ :=
  accepted_of_selected 12 369698 ⟨1282024, by decide⟩ ⟨12, 2, 0, 1282024, 369698, 2533, 65536⟩
    (by decide) selected_cut_46052

theorem selected_cut_46053 : selected 9 ⟨1282083, by decide⟩
    (prefixPartial 12 369699) = some ⟨12, 2, 0, 1282083, 369699, 2889, 65536⟩ := by
  decide +kernel

theorem context_12_369699_1282083 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369699 ⟨1282083, by decide⟩ :=
  accepted_of_selected 12 369699 ⟨1282083, by decide⟩ ⟨12, 2, 0, 1282083, 369699, 2889, 65536⟩
    (by decide) selected_cut_46053

theorem unmarked_context_11_92424_1282084 : frontier 10 ⟨1282084, by decide⟩
    (prefixCache 11 92424) (prefixPartial 11 92424) = false := by
  decide +kernel

theorem node_context_11_92424_1282084 : EJMOriginalGlobalDAGData.nodes 10 ⟨1282084, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨1281968, by decide⟩,⟨1282024, by decide⟩,⟨1282083, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92424_1282084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92424 ⟨1282084, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92424
    ⟨1282084, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨1281968, by decide⟩,⟨1282024, by decide⟩,⟨1282083, by decide⟩]) unmarked_context_11_92424_1282084 node_context_11_92424_1282084
  intro a
  fin_cases a
  · exact context_12_369696_435790
  · exact context_12_369697_1281968
  · exact context_12_369698_1282024
  · exact context_12_369699_1282083

theorem selected_cut_46054 : selected 9 ⟨450498, by decide⟩
    (prefixPartial 12 369700) = some ⟨12, 1, 0, 450498, 369700, 1, 65536⟩ := by
  decide +kernel

theorem context_12_369700_450498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369700 ⟨450498, by decide⟩ :=
  accepted_of_selected 12 369700 ⟨450498, by decide⟩ ⟨12, 1, 0, 450498, 369700, 1, 65536⟩
    (by decide) selected_cut_46054

theorem selected_cut_46055 : selected 9 ⟨1008220, by decide⟩
    (prefixPartial 12 369701) = some ⟨12, 1, 0, 1008220, 369701, 1, 65536⟩ := by
  decide +kernel

theorem context_12_369701_1008220 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369701 ⟨1008220, by decide⟩ :=
  accepted_of_selected 12 369701 ⟨1008220, by decide⟩ ⟨12, 1, 0, 1008220, 369701, 1, 65536⟩
    (by decide) selected_cut_46055

theorem selected_cut_46056 : selected 9 ⟨1282164, by decide⟩
    (prefixPartial 12 369702) = some ⟨12, 2, 0, 1282164, 369702, 2881, 65536⟩ := by
  decide +kernel

theorem context_12_369702_1282164 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369702 ⟨1282164, by decide⟩ :=
  accepted_of_selected 12 369702 ⟨1282164, by decide⟩ ⟨12, 2, 0, 1282164, 369702, 2881, 65536⟩
    (by decide) selected_cut_46056

theorem selected_cut_46057 : selected 9 ⟨1282255, by decide⟩
    (prefixPartial 12 369703) = some ⟨12, 2, 0, 1282255, 369703, 3449, 65536⟩ := by
  decide +kernel

theorem context_12_369703_1282255 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369703 ⟨1282255, by decide⟩ :=
  accepted_of_selected 12 369703 ⟨1282255, by decide⟩ ⟨12, 2, 0, 1282255, 369703, 3449, 65536⟩
    (by decide) selected_cut_46057

theorem unmarked_context_11_92425_1282256 : frontier 10 ⟨1282256, by decide⟩
    (prefixCache 11 92425) (prefixPartial 11 92425) = false := by
  decide +kernel

theorem node_context_11_92425_1282256 : EJMOriginalGlobalDAGData.nodes 10 ⟨1282256, by decide⟩ =
    .split (coordinate 11) (![⟨450498, by decide⟩,⟨1008220, by decide⟩,⟨1282164, by decide⟩,⟨1282255, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92425_1282256 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92425 ⟨1282256, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92425
    ⟨1282256, by decide⟩ (by decide) (![⟨450498, by decide⟩,⟨1008220, by decide⟩,⟨1282164, by decide⟩,⟨1282255, by decide⟩]) unmarked_context_11_92425_1282256 node_context_11_92425_1282256
  intro a
  fin_cases a
  · exact context_12_369700_450498
  · exact context_12_369701_1008220
  · exact context_12_369702_1282164
  · exact context_12_369703_1282255

theorem selected_cut_46058 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 369704) = some ⟨12, 1, 0, 435790, 369704, 1, 65536⟩ := by
  decide +kernel

theorem context_12_369704_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369704 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 369704 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 369704, 1, 65536⟩
    (by decide) selected_cut_46058

theorem selected_cut_46059 : selected 9 ⟨1282317, by decide⟩
    (prefixPartial 12 369705) = some ⟨12, 2, 0, 1282317, 369705, 1241, 65536⟩ := by
  decide +kernel

theorem context_12_369705_1282317 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369705 ⟨1282317, by decide⟩ :=
  accepted_of_selected 12 369705 ⟨1282317, by decide⟩ ⟨12, 2, 0, 1282317, 369705, 1241, 65536⟩
    (by decide) selected_cut_46059

theorem selected_cut_46060 : selected 9 ⟨1113261, by decide⟩
    (prefixPartial 12 369706) = some ⟨12, 1, 0, 1113261, 369706, 1, 65536⟩ := by
  decide +kernel

theorem context_12_369706_1113261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369706 ⟨1113261, by decide⟩ :=
  accepted_of_selected 12 369706 ⟨1113261, by decide⟩ ⟨12, 1, 0, 1113261, 369706, 1, 65536⟩
    (by decide) selected_cut_46060

theorem selected_cut_46061 : selected 9 ⟨1282389, by decide⟩
    (prefixPartial 12 369707) = some ⟨12, 2, 0, 1282389, 369707, 3145, 65536⟩ := by
  decide +kernel

theorem context_12_369707_1282389 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369707 ⟨1282389, by decide⟩ :=
  accepted_of_selected 12 369707 ⟨1282389, by decide⟩ ⟨12, 2, 0, 1282389, 369707, 3145, 65536⟩
    (by decide) selected_cut_46061

theorem unmarked_context_11_92426_1282390 : frontier 10 ⟨1282390, by decide⟩
    (prefixCache 11 92426) (prefixPartial 11 92426) = false := by
  decide +kernel

theorem node_context_11_92426_1282390 : EJMOriginalGlobalDAGData.nodes 10 ⟨1282390, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨1282317, by decide⟩,⟨1113261, by decide⟩,⟨1282389, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92426_1282390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92426 ⟨1282390, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92426
    ⟨1282390, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨1282317, by decide⟩,⟨1113261, by decide⟩,⟨1282389, by decide⟩]) unmarked_context_11_92426_1282390 node_context_11_92426_1282390
  intro a
  fin_cases a
  · exact context_12_369704_435790
  · exact context_12_369705_1282317
  · exact context_12_369706_1113261
  · exact context_12_369707_1282389

theorem selected_cut_46062 : selected 9 ⟨1282469, by decide⟩
    (prefixPartial 12 369708) = some ⟨12, 2, 0, 1282469, 369708, 2985, 65536⟩ := by
  decide +kernel

theorem context_12_369708_1282469 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369708 ⟨1282469, by decide⟩ :=
  accepted_of_selected 12 369708 ⟨1282469, by decide⟩ ⟨12, 2, 0, 1282469, 369708, 2985, 65536⟩
    (by decide) selected_cut_46062

theorem selected_cut_46063 : selected 9 ⟨1282507, by decide⟩
    (prefixPartial 12 369709) = some ⟨12, 2, 0, 1282507, 369709, 2281, 65536⟩ := by
  decide +kernel

theorem context_12_369709_1282507 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369709 ⟨1282507, by decide⟩ :=
  accepted_of_selected 12 369709 ⟨1282507, by decide⟩ ⟨12, 2, 0, 1282507, 369709, 2281, 65536⟩
    (by decide) selected_cut_46063

theorem selected_cut_46064 : selected 9 ⟨1282559, by decide⟩
    (prefixPartial 12 369710) = some ⟨12, 2, 0, 1282559, 369710, 2713, 65536⟩ := by
  decide +kernel

theorem context_12_369710_1282559 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369710 ⟨1282559, by decide⟩ :=
  accepted_of_selected 12 369710 ⟨1282559, by decide⟩ ⟨12, 2, 0, 1282559, 369710, 2713, 65536⟩
    (by decide) selected_cut_46064

theorem selected_cut_46065 : selected 9 ⟨1282622, by decide⟩
    (prefixPartial 12 369711) = some ⟨12, 2, 0, 1282622, 369711, 3009, 65536⟩ := by
  decide +kernel

theorem context_12_369711_1282622 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369711 ⟨1282622, by decide⟩ :=
  accepted_of_selected 12 369711 ⟨1282622, by decide⟩ ⟨12, 2, 0, 1282622, 369711, 3009, 65536⟩
    (by decide) selected_cut_46065

theorem unmarked_context_11_92427_1282623 : frontier 10 ⟨1282623, by decide⟩
    (prefixCache 11 92427) (prefixPartial 11 92427) = false := by
  decide +kernel

theorem node_context_11_92427_1282623 : EJMOriginalGlobalDAGData.nodes 10 ⟨1282623, by decide⟩ =
    .split (coordinate 11) (![⟨1282469, by decide⟩,⟨1282507, by decide⟩,⟨1282559, by decide⟩,⟨1282622, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92427_1282623 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92427 ⟨1282623, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92427
    ⟨1282623, by decide⟩ (by decide) (![⟨1282469, by decide⟩,⟨1282507, by decide⟩,⟨1282559, by decide⟩,⟨1282622, by decide⟩]) unmarked_context_11_92427_1282623 node_context_11_92427_1282623
  intro a
  fin_cases a
  · exact context_12_369708_1282469
  · exact context_12_369709_1282507
  · exact context_12_369710_1282559
  · exact context_12_369711_1282622

theorem unmarked_context_10_23106_1282624 : frontier 11 ⟨1282624, by decide⟩
    (prefixCache 10 23106) (prefixPartial 10 23106) = false := by
  decide +kernel

theorem node_context_10_23106_1282624 : EJMOriginalGlobalDAGData.nodes 11 ⟨1282624, by decide⟩ =
    .split (coordinate 10) (![⟨1282084, by decide⟩,⟨1282256, by decide⟩,⟨1282390, by decide⟩,⟨1282623, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23106_1282624 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23106 ⟨1282624, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23106
    ⟨1282624, by decide⟩ (by decide) (![⟨1282084, by decide⟩,⟨1282256, by decide⟩,⟨1282390, by decide⟩,⟨1282623, by decide⟩]) unmarked_context_10_23106_1282624 node_context_10_23106_1282624
  intro a
  fin_cases a
  · exact context_11_92424_1282084
  · exact context_11_92425_1282256
  · exact context_11_92426_1282390
  · exact context_11_92427_1282623

theorem selected_cut_46066 : selected 9 ⟨985390, by decide⟩
    (prefixPartial 12 369712) = some ⟨12, 1, 0, 985390, 369712, 1, 65536⟩ := by
  decide +kernel

theorem context_12_369712_985390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369712 ⟨985390, by decide⟩ :=
  accepted_of_selected 12 369712 ⟨985390, by decide⟩ ⟨12, 1, 0, 985390, 369712, 1, 65536⟩
    (by decide) selected_cut_46066

theorem selected_cut_46067 : selected 9 ⟨1282655, by decide⟩
    (prefixPartial 12 369713) = some ⟨12, 2, 0, 1282655, 369713, 1925, 65536⟩ := by
  decide +kernel

theorem context_12_369713_1282655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369713 ⟨1282655, by decide⟩ :=
  accepted_of_selected 12 369713 ⟨1282655, by decide⟩ ⟨12, 2, 0, 1282655, 369713, 1925, 65536⟩
    (by decide) selected_cut_46067

theorem selected_cut_46068 : selected 9 ⟨1282697, by decide⟩
    (prefixPartial 12 369714) = some ⟨12, 2, 0, 1282697, 369714, 2169, 65536⟩ := by
  decide +kernel

theorem context_12_369714_1282697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369714 ⟨1282697, by decide⟩ :=
  accepted_of_selected 12 369714 ⟨1282697, by decide⟩ ⟨12, 2, 0, 1282697, 369714, 2169, 65536⟩
    (by decide) selected_cut_46068

theorem selected_cut_46069 : selected 9 ⟨1282745, by decide⟩
    (prefixPartial 12 369715) = some ⟨12, 2, 0, 1282745, 369715, 2637, 65536⟩ := by
  decide +kernel

theorem context_12_369715_1282745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369715 ⟨1282745, by decide⟩ :=
  accepted_of_selected 12 369715 ⟨1282745, by decide⟩ ⟨12, 2, 0, 1282745, 369715, 2637, 65536⟩
    (by decide) selected_cut_46069

theorem unmarked_context_11_92428_1282746 : frontier 10 ⟨1282746, by decide⟩
    (prefixCache 11 92428) (prefixPartial 11 92428) = false := by
  decide +kernel

theorem node_context_11_92428_1282746 : EJMOriginalGlobalDAGData.nodes 10 ⟨1282746, by decide⟩ =
    .split (coordinate 11) (![⟨985390, by decide⟩,⟨1282655, by decide⟩,⟨1282697, by decide⟩,⟨1282745, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92428_1282746 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92428 ⟨1282746, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92428
    ⟨1282746, by decide⟩ (by decide) (![⟨985390, by decide⟩,⟨1282655, by decide⟩,⟨1282697, by decide⟩,⟨1282745, by decide⟩]) unmarked_context_11_92428_1282746 node_context_11_92428_1282746
  intro a
  fin_cases a
  · exact context_12_369712_985390
  · exact context_12_369713_1282655
  · exact context_12_369714_1282697
  · exact context_12_369715_1282745

theorem selected_cut_46070 : selected 9 ⟨1282809, by decide⟩
    (prefixPartial 12 369716) = some ⟨12, 2, 0, 1282809, 369716, 2665, 65536⟩ := by
  decide +kernel

theorem context_12_369716_1282809 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369716 ⟨1282809, by decide⟩ :=
  accepted_of_selected 12 369716 ⟨1282809, by decide⟩ ⟨12, 2, 0, 1282809, 369716, 2665, 65536⟩
    (by decide) selected_cut_46070

theorem selected_cut_46071 : selected 9 ⟨1282850, by decide⟩
    (prefixPartial 12 369717) = some ⟨12, 2, 0, 1282850, 369717, 1945, 65536⟩ := by
  decide +kernel

theorem context_12_369717_1282850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369717 ⟨1282850, by decide⟩ :=
  accepted_of_selected 12 369717 ⟨1282850, by decide⟩ ⟨12, 2, 0, 1282850, 369717, 1945, 65536⟩
    (by decide) selected_cut_46071

theorem selected_cut_46072 : selected 9 ⟨1282901, by decide⟩
    (prefixPartial 12 369718) = some ⟨12, 2, 0, 1282901, 369718, 2281, 65536⟩ := by
  decide +kernel

theorem context_12_369718_1282901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369718 ⟨1282901, by decide⟩ :=
  accepted_of_selected 12 369718 ⟨1282901, by decide⟩ ⟨12, 2, 0, 1282901, 369718, 2281, 65536⟩
    (by decide) selected_cut_46072

theorem selected_cut_46073 : selected 9 ⟨1282958, by decide⟩
    (prefixPartial 12 369719) = some ⟨12, 2, 0, 1282958, 369719, 2709, 65536⟩ := by
  decide +kernel

theorem context_12_369719_1282958 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369719 ⟨1282958, by decide⟩ :=
  accepted_of_selected 12 369719 ⟨1282958, by decide⟩ ⟨12, 2, 0, 1282958, 369719, 2709, 65536⟩
    (by decide) selected_cut_46073

theorem unmarked_context_11_92429_1282959 : frontier 10 ⟨1282959, by decide⟩
    (prefixCache 11 92429) (prefixPartial 11 92429) = false := by
  decide +kernel

theorem node_context_11_92429_1282959 : EJMOriginalGlobalDAGData.nodes 10 ⟨1282959, by decide⟩ =
    .split (coordinate 11) (![⟨1282809, by decide⟩,⟨1282850, by decide⟩,⟨1282901, by decide⟩,⟨1282958, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92429_1282959 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92429 ⟨1282959, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92429
    ⟨1282959, by decide⟩ (by decide) (![⟨1282809, by decide⟩,⟨1282850, by decide⟩,⟨1282901, by decide⟩,⟨1282958, by decide⟩]) unmarked_context_11_92429_1282959 node_context_11_92429_1282959
  intro a
  fin_cases a
  · exact context_12_369716_1282809
  · exact context_12_369717_1282850
  · exact context_12_369718_1282901
  · exact context_12_369719_1282958

theorem selected_cut_46074 : selected 9 ⟨994572, by decide⟩
    (prefixPartial 12 369720) = some ⟨12, 1, 0, 994572, 369720, 1, 65536⟩ := by
  decide +kernel

theorem context_12_369720_994572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369720 ⟨994572, by decide⟩ :=
  accepted_of_selected 12 369720 ⟨994572, by decide⟩ ⟨12, 1, 0, 994572, 369720, 1, 65536⟩
    (by decide) selected_cut_46074

theorem selected_cut_46075 : selected 9 ⟨1282991, by decide⟩
    (prefixPartial 12 369721) = some ⟨12, 2, 0, 1282991, 369721, 1885, 65536⟩ := by
  decide +kernel

theorem context_12_369721_1282991 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369721 ⟨1282991, by decide⟩ :=
  accepted_of_selected 12 369721 ⟨1282991, by decide⟩ ⟨12, 2, 0, 1282991, 369721, 1885, 65536⟩
    (by decide) selected_cut_46075

theorem selected_cut_46076 : selected 9 ⟨806997, by decide⟩
    (prefixPartial 12 369722) = some ⟨12, 1, 0, 806997, 369722, 1, 65536⟩ := by
  decide +kernel

theorem context_12_369722_806997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369722 ⟨806997, by decide⟩ :=
  accepted_of_selected 12 369722 ⟨806997, by decide⟩ ⟨12, 1, 0, 806997, 369722, 1, 65536⟩
    (by decide) selected_cut_46076

theorem selected_cut_46077 : selected 9 ⟨1283041, by decide⟩
    (prefixPartial 12 369723) = some ⟨12, 2, 0, 1283041, 369723, 2673, 65536⟩ := by
  decide +kernel

theorem context_12_369723_1283041 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369723 ⟨1283041, by decide⟩ :=
  accepted_of_selected 12 369723 ⟨1283041, by decide⟩ ⟨12, 2, 0, 1283041, 369723, 2673, 65536⟩
    (by decide) selected_cut_46077

theorem unmarked_context_11_92430_1283042 : frontier 10 ⟨1283042, by decide⟩
    (prefixCache 11 92430) (prefixPartial 11 92430) = false := by
  decide +kernel

theorem node_context_11_92430_1283042 : EJMOriginalGlobalDAGData.nodes 10 ⟨1283042, by decide⟩ =
    .split (coordinate 11) (![⟨994572, by decide⟩,⟨1282991, by decide⟩,⟨806997, by decide⟩,⟨1283041, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92430_1283042 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92430 ⟨1283042, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92430
    ⟨1283042, by decide⟩ (by decide) (![⟨994572, by decide⟩,⟨1282991, by decide⟩,⟨806997, by decide⟩,⟨1283041, by decide⟩]) unmarked_context_11_92430_1283042 node_context_11_92430_1283042
  intro a
  fin_cases a
  · exact context_12_369720_994572
  · exact context_12_369721_1282991
  · exact context_12_369722_806997
  · exact context_12_369723_1283041

theorem selected_cut_46078 : selected 9 ⟨1283091, by decide⟩
    (prefixPartial 12 369724) = some ⟨12, 2, 0, 1283091, 369724, 2233, 65536⟩ := by
  decide +kernel

theorem context_12_369724_1283091 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369724 ⟨1283091, by decide⟩ :=
  accepted_of_selected 12 369724 ⟨1283091, by decide⟩ ⟨12, 2, 0, 1283091, 369724, 2233, 65536⟩
    (by decide) selected_cut_46078

theorem selected_cut_46079 : selected 9 ⟨1283121, by decide⟩
    (prefixPartial 12 369725) = some ⟨12, 2, 0, 1283121, 369725, 1697, 65536⟩ := by
  decide +kernel

theorem context_12_369725_1283121 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369725 ⟨1283121, by decide⟩ :=
  accepted_of_selected 12 369725 ⟨1283121, by decide⟩ ⟨12, 2, 0, 1283121, 369725, 1697, 65536⟩
    (by decide) selected_cut_46079

theorem selected_cut_46080 : selected 9 ⟨1283164, by decide⟩
    (prefixPartial 12 369726) = some ⟨12, 2, 0, 1283164, 369726, 2049, 65536⟩ := by
  decide +kernel

theorem context_12_369726_1283164 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369726 ⟨1283164, by decide⟩ :=
  accepted_of_selected 12 369726 ⟨1283164, by decide⟩ ⟨12, 2, 0, 1283164, 369726, 2049, 65536⟩
    (by decide) selected_cut_46080

theorem selected_cut_46081 : selected 9 ⟨1116246, by decide⟩
    (prefixPartial 12 369727) = some ⟨12, 1, 0, 1116246, 369727, 1, 65536⟩ := by
  decide +kernel

theorem context_12_369727_1116246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369727 ⟨1116246, by decide⟩ :=
  accepted_of_selected 12 369727 ⟨1116246, by decide⟩ ⟨12, 1, 0, 1116246, 369727, 1, 65536⟩
    (by decide) selected_cut_46081

theorem unmarked_context_11_92431_1283165 : frontier 10 ⟨1283165, by decide⟩
    (prefixCache 11 92431) (prefixPartial 11 92431) = false := by
  decide +kernel

theorem node_context_11_92431_1283165 : EJMOriginalGlobalDAGData.nodes 10 ⟨1283165, by decide⟩ =
    .split (coordinate 11) (![⟨1283091, by decide⟩,⟨1283121, by decide⟩,⟨1283164, by decide⟩,⟨1116246, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92431_1283165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92431 ⟨1283165, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92431
    ⟨1283165, by decide⟩ (by decide) (![⟨1283091, by decide⟩,⟨1283121, by decide⟩,⟨1283164, by decide⟩,⟨1116246, by decide⟩]) unmarked_context_11_92431_1283165 node_context_11_92431_1283165
  intro a
  fin_cases a
  · exact context_12_369724_1283091
  · exact context_12_369725_1283121
  · exact context_12_369726_1283164
  · exact context_12_369727_1116246

theorem unmarked_context_10_23107_1283166 : frontier 11 ⟨1283166, by decide⟩
    (prefixCache 10 23107) (prefixPartial 10 23107) = false := by
  decide +kernel

theorem node_context_10_23107_1283166 : EJMOriginalGlobalDAGData.nodes 11 ⟨1283166, by decide⟩ =
    .split (coordinate 10) (![⟨1282746, by decide⟩,⟨1282959, by decide⟩,⟨1283042, by decide⟩,⟨1283165, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23107_1283166 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23107 ⟨1283166, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23107
    ⟨1283166, by decide⟩ (by decide) (![⟨1282746, by decide⟩,⟨1282959, by decide⟩,⟨1283042, by decide⟩,⟨1283165, by decide⟩]) unmarked_context_10_23107_1283166 node_context_10_23107_1283166
  intro a
  fin_cases a
  · exact context_11_92428_1282746
  · exact context_11_92429_1282959
  · exact context_11_92430_1283042
  · exact context_11_92431_1283165

theorem unmarked_context_9_5776_1283167 : frontier 12 ⟨1283167, by decide⟩
    (prefixCache 9 5776) (prefixPartial 9 5776) = false := by
  decide +kernel

theorem node_context_9_5776_1283167 : EJMOriginalGlobalDAGData.nodes 12 ⟨1283167, by decide⟩ =
    .split (coordinate 9) (![⟨1281380, by decide⟩,⟨1281918, by decide⟩,⟨1282624, by decide⟩,⟨1283166, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5776_1283167 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5776 ⟨1283167, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5776
    ⟨1283167, by decide⟩ (by decide) (![⟨1281380, by decide⟩,⟨1281918, by decide⟩,⟨1282624, by decide⟩,⟨1283166, by decide⟩]) unmarked_context_9_5776_1283167 node_context_9_5776_1283167
  intro a
  fin_cases a
  · exact context_10_23104_1281380
  · exact context_10_23105_1281918
  · exact context_10_23106_1282624
  · exact context_10_23107_1283166

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
