/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover416
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_40036 : selected 9 ⟨1087083, by decide⟩
    (prefixPartial 12 308527) = some ⟨12, 2, 0, 1087083, 308527, 3477, 65536⟩ := by
  decide +kernel

theorem context_12_308527_1087083 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308527 ⟨1087083, by decide⟩ :=
  accepted_of_selected 12 308527 ⟨1087083, by decide⟩ ⟨12, 2, 0, 1087083, 308527, 3477, 65536⟩
    (by decide) selected_cut_40036

theorem unmarked_context_11_77131_1087084 : frontier 10 ⟨1087084, by decide⟩
    (prefixCache 11 77131) (prefixPartial 11 77131) = false := by
  decide +kernel

theorem node_context_11_77131_1087084 : EJMOriginalGlobalDAGData.nodes 10 ⟨1087084, by decide⟩ =
    .split (coordinate 11) (![⟨1086931, by decide⟩,⟨1086971, by decide⟩,⟨1087027, by decide⟩,⟨1087083, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77131_1087084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77131 ⟨1087084, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77131
    ⟨1087084, by decide⟩ (by decide) (![⟨1086931, by decide⟩,⟨1086971, by decide⟩,⟨1087027, by decide⟩,⟨1087083, by decide⟩]) unmarked_context_11_77131_1087084 node_context_11_77131_1087084
  intro a
  fin_cases a
  · exact context_12_308524_1086931
  · exact context_12_308525_1086971
  · exact context_12_308526_1087027
  · exact context_12_308527_1087083

theorem unmarked_context_10_19282_1087085 : frontier 11 ⟨1087085, by decide⟩
    (prefixCache 10 19282) (prefixPartial 10 19282) = false := by
  decide +kernel

theorem node_context_10_19282_1087085 : EJMOriginalGlobalDAGData.nodes 11 ⟨1087085, by decide⟩ =
    .split (coordinate 10) (![⟨1086519, by decide⟩,⟨1086686, by decide⟩,⟨1086872, by decide⟩,⟨1087084, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19282_1087085 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19282 ⟨1087085, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19282
    ⟨1087085, by decide⟩ (by decide) (![⟨1086519, by decide⟩,⟨1086686, by decide⟩,⟨1086872, by decide⟩,⟨1087084, by decide⟩]) unmarked_context_10_19282_1087085 node_context_10_19282_1087085
  intro a
  fin_cases a
  · exact context_11_77128_1086519
  · exact context_11_77129_1086686
  · exact context_11_77130_1086872
  · exact context_11_77131_1087084

theorem selected_cut_40037 : selected 9 ⟨1087125, by decide⟩
    (prefixPartial 12 308528) = some ⟨12, 2, 0, 1087125, 308528, 1557, 65536⟩ := by
  decide +kernel

theorem context_12_308528_1087125 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308528 ⟨1087125, by decide⟩ :=
  accepted_of_selected 12 308528 ⟨1087125, by decide⟩ ⟨12, 2, 0, 1087125, 308528, 1557, 65536⟩
    (by decide) selected_cut_40037

theorem selected_cut_40038 : selected 9 ⟨1087166, by decide⟩
    (prefixPartial 12 308529) = some ⟨12, 2, 0, 1087166, 308529, 2517, 65536⟩ := by
  decide +kernel

theorem context_12_308529_1087166 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308529 ⟨1087166, by decide⟩ :=
  accepted_of_selected 12 308529 ⟨1087166, by decide⟩ ⟨12, 2, 0, 1087166, 308529, 2517, 65536⟩
    (by decide) selected_cut_40038

theorem selected_cut_40039 : selected 9 ⟨1087201, by decide⟩
    (prefixPartial 12 308530) = some ⟨12, 2, 0, 1087201, 308530, 2705, 65536⟩ := by
  decide +kernel

theorem context_12_308530_1087201 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308530 ⟨1087201, by decide⟩ :=
  accepted_of_selected 12 308530 ⟨1087201, by decide⟩ ⟨12, 2, 0, 1087201, 308530, 2705, 65536⟩
    (by decide) selected_cut_40039

theorem selected_cut_40040 : selected 9 ⟨1087238, by decide⟩
    (prefixPartial 12 308531) = some ⟨12, 2, 0, 1087238, 308531, 2673, 65536⟩ := by
  decide +kernel

theorem context_12_308531_1087238 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308531 ⟨1087238, by decide⟩ :=
  accepted_of_selected 12 308531 ⟨1087238, by decide⟩ ⟨12, 2, 0, 1087238, 308531, 2673, 65536⟩
    (by decide) selected_cut_40040

theorem unmarked_context_11_77132_1087239 : frontier 10 ⟨1087239, by decide⟩
    (prefixCache 11 77132) (prefixPartial 11 77132) = false := by
  decide +kernel

theorem node_context_11_77132_1087239 : EJMOriginalGlobalDAGData.nodes 10 ⟨1087239, by decide⟩ =
    .split (coordinate 11) (![⟨1087125, by decide⟩,⟨1087166, by decide⟩,⟨1087201, by decide⟩,⟨1087238, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77132_1087239 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77132 ⟨1087239, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77132
    ⟨1087239, by decide⟩ (by decide) (![⟨1087125, by decide⟩,⟨1087166, by decide⟩,⟨1087201, by decide⟩,⟨1087238, by decide⟩]) unmarked_context_11_77132_1087239 node_context_11_77132_1087239
  intro a
  fin_cases a
  · exact context_12_308528_1087125
  · exact context_12_308529_1087166
  · exact context_12_308530_1087201
  · exact context_12_308531_1087238

theorem selected_cut_40041 : selected 9 ⟨1087287, by decide⟩
    (prefixPartial 12 308532) = some ⟨12, 2, 0, 1087287, 308532, 2881, 65536⟩ := by
  decide +kernel

theorem context_12_308532_1087287 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308532 ⟨1087287, by decide⟩ :=
  accepted_of_selected 12 308532 ⟨1087287, by decide⟩ ⟨12, 2, 0, 1087287, 308532, 2881, 65536⟩
    (by decide) selected_cut_40041

theorem selected_cut_40042 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 308533) = some ⟨12, 1, 0, 891951, 308533, 1, 65536⟩ := by
  decide +kernel

theorem context_12_308533_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308533 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 308533 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 308533, 1, 65536⟩
    (by decide) selected_cut_40042

theorem selected_cut_40043 : selected 9 ⟨1087333, by decide⟩
    (prefixPartial 12 308534) = some ⟨12, 2, 0, 1087333, 308534, 2773, 65536⟩ := by
  decide +kernel

theorem context_12_308534_1087333 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308534 ⟨1087333, by decide⟩ :=
  accepted_of_selected 12 308534 ⟨1087333, by decide⟩ ⟨12, 2, 0, 1087333, 308534, 2773, 65536⟩
    (by decide) selected_cut_40043

theorem selected_cut_40044 : selected 9 ⟨1087370, by decide⟩
    (prefixPartial 12 308535) = some ⟨12, 2, 0, 1087370, 308535, 2621, 65536⟩ := by
  decide +kernel

theorem context_12_308535_1087370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308535 ⟨1087370, by decide⟩ :=
  accepted_of_selected 12 308535 ⟨1087370, by decide⟩ ⟨12, 2, 0, 1087370, 308535, 2621, 65536⟩
    (by decide) selected_cut_40044

theorem unmarked_context_11_77133_1087371 : frontier 10 ⟨1087371, by decide⟩
    (prefixCache 11 77133) (prefixPartial 11 77133) = false := by
  decide +kernel

theorem node_context_11_77133_1087371 : EJMOriginalGlobalDAGData.nodes 10 ⟨1087371, by decide⟩ =
    .split (coordinate 11) (![⟨1087287, by decide⟩,⟨891951, by decide⟩,⟨1087333, by decide⟩,⟨1087370, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77133_1087371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77133 ⟨1087371, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77133
    ⟨1087371, by decide⟩ (by decide) (![⟨1087287, by decide⟩,⟨891951, by decide⟩,⟨1087333, by decide⟩,⟨1087370, by decide⟩]) unmarked_context_11_77133_1087371 node_context_11_77133_1087371
  intro a
  fin_cases a
  · exact context_12_308532_1087287
  · exact context_12_308533_891951
  · exact context_12_308534_1087333
  · exact context_12_308535_1087370

theorem selected_cut_40045 : selected 9 ⟨1087410, by decide⟩
    (prefixPartial 12 308536) = some ⟨12, 2, 0, 1087410, 308536, 2677, 65536⟩ := by
  decide +kernel

theorem context_12_308536_1087410 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308536 ⟨1087410, by decide⟩ :=
  accepted_of_selected 12 308536 ⟨1087410, by decide⟩ ⟨12, 2, 0, 1087410, 308536, 2677, 65536⟩
    (by decide) selected_cut_40045

theorem selected_cut_40046 : selected 9 ⟨1087447, by decide⟩
    (prefixPartial 12 308537) = some ⟨12, 2, 0, 1087447, 308537, 2421, 65536⟩ := by
  decide +kernel

theorem context_12_308537_1087447 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308537 ⟨1087447, by decide⟩ :=
  accepted_of_selected 12 308537 ⟨1087447, by decide⟩ ⟨12, 2, 0, 1087447, 308537, 2421, 65536⟩
    (by decide) selected_cut_40046

theorem selected_cut_40047 : selected 9 ⟨1087488, by decide⟩
    (prefixPartial 12 308538) = some ⟨12, 2, 0, 1087488, 308538, 2737, 65536⟩ := by
  decide +kernel

theorem context_12_308538_1087488 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308538 ⟨1087488, by decide⟩ :=
  accepted_of_selected 12 308538 ⟨1087488, by decide⟩ ⟨12, 2, 0, 1087488, 308538, 2737, 65536⟩
    (by decide) selected_cut_40047

theorem selected_cut_40048 : selected 9 ⟨1087524, by decide⟩
    (prefixPartial 12 308539) = some ⟨12, 2, 0, 1087524, 308539, 2541, 65536⟩ := by
  decide +kernel

theorem context_12_308539_1087524 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308539 ⟨1087524, by decide⟩ :=
  accepted_of_selected 12 308539 ⟨1087524, by decide⟩ ⟨12, 2, 0, 1087524, 308539, 2541, 65536⟩
    (by decide) selected_cut_40048

theorem unmarked_context_11_77134_1087525 : frontier 10 ⟨1087525, by decide⟩
    (prefixCache 11 77134) (prefixPartial 11 77134) = false := by
  decide +kernel

theorem node_context_11_77134_1087525 : EJMOriginalGlobalDAGData.nodes 10 ⟨1087525, by decide⟩ =
    .split (coordinate 11) (![⟨1087410, by decide⟩,⟨1087447, by decide⟩,⟨1087488, by decide⟩,⟨1087524, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77134_1087525 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77134 ⟨1087525, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77134
    ⟨1087525, by decide⟩ (by decide) (![⟨1087410, by decide⟩,⟨1087447, by decide⟩,⟨1087488, by decide⟩,⟨1087524, by decide⟩]) unmarked_context_11_77134_1087525 node_context_11_77134_1087525
  intro a
  fin_cases a
  · exact context_12_308536_1087410
  · exact context_12_308537_1087447
  · exact context_12_308538_1087488
  · exact context_12_308539_1087524

theorem selected_cut_40049 : selected 9 ⟨1087560, by decide⟩
    (prefixPartial 12 308540) = some ⟨12, 2, 0, 1087560, 308540, 2601, 65536⟩ := by
  decide +kernel

theorem context_12_308540_1087560 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308540 ⟨1087560, by decide⟩ :=
  accepted_of_selected 12 308540 ⟨1087560, by decide⟩ ⟨12, 2, 0, 1087560, 308540, 2601, 65536⟩
    (by decide) selected_cut_40049

theorem selected_cut_40050 : selected 9 ⟨1087591, by decide⟩
    (prefixPartial 12 308541) = some ⟨12, 2, 0, 1087591, 308541, 2277, 65536⟩ := by
  decide +kernel

theorem context_12_308541_1087591 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308541 ⟨1087591, by decide⟩ :=
  accepted_of_selected 12 308541 ⟨1087591, by decide⟩ ⟨12, 2, 0, 1087591, 308541, 2277, 65536⟩
    (by decide) selected_cut_40050

theorem selected_cut_40051 : selected 9 ⟨1087631, by decide⟩
    (prefixPartial 12 308542) = some ⟨12, 2, 0, 1087631, 308542, 2501, 65536⟩ := by
  decide +kernel

theorem context_12_308542_1087631 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308542 ⟨1087631, by decide⟩ :=
  accepted_of_selected 12 308542 ⟨1087631, by decide⟩ ⟨12, 2, 0, 1087631, 308542, 2501, 65536⟩
    (by decide) selected_cut_40051

theorem selected_cut_40052 : selected 9 ⟨762108, by decide⟩
    (prefixPartial 12 308543) = some ⟨12, 1, 0, 762108, 308543, 1, 65536⟩ := by
  decide +kernel

theorem context_12_308543_762108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308543 ⟨762108, by decide⟩ :=
  accepted_of_selected 12 308543 ⟨762108, by decide⟩ ⟨12, 1, 0, 762108, 308543, 1, 65536⟩
    (by decide) selected_cut_40052

theorem unmarked_context_11_77135_1087632 : frontier 10 ⟨1087632, by decide⟩
    (prefixCache 11 77135) (prefixPartial 11 77135) = false := by
  decide +kernel

theorem node_context_11_77135_1087632 : EJMOriginalGlobalDAGData.nodes 10 ⟨1087632, by decide⟩ =
    .split (coordinate 11) (![⟨1087560, by decide⟩,⟨1087591, by decide⟩,⟨1087631, by decide⟩,⟨762108, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77135_1087632 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77135 ⟨1087632, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77135
    ⟨1087632, by decide⟩ (by decide) (![⟨1087560, by decide⟩,⟨1087591, by decide⟩,⟨1087631, by decide⟩,⟨762108, by decide⟩]) unmarked_context_11_77135_1087632 node_context_11_77135_1087632
  intro a
  fin_cases a
  · exact context_12_308540_1087560
  · exact context_12_308541_1087591
  · exact context_12_308542_1087631
  · exact context_12_308543_762108

theorem unmarked_context_10_19283_1087633 : frontier 11 ⟨1087633, by decide⟩
    (prefixCache 10 19283) (prefixPartial 10 19283) = false := by
  decide +kernel

theorem node_context_10_19283_1087633 : EJMOriginalGlobalDAGData.nodes 11 ⟨1087633, by decide⟩ =
    .split (coordinate 10) (![⟨1087239, by decide⟩,⟨1087371, by decide⟩,⟨1087525, by decide⟩,⟨1087632, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19283_1087633 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19283 ⟨1087633, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19283
    ⟨1087633, by decide⟩ (by decide) (![⟨1087239, by decide⟩,⟨1087371, by decide⟩,⟨1087525, by decide⟩,⟨1087632, by decide⟩]) unmarked_context_10_19283_1087633 node_context_10_19283_1087633
  intro a
  fin_cases a
  · exact context_11_77132_1087239
  · exact context_11_77133_1087371
  · exact context_11_77134_1087525
  · exact context_11_77135_1087632

theorem unmarked_context_9_4820_1087634 : frontier 12 ⟨1087634, by decide⟩
    (prefixCache 9 4820) (prefixPartial 9 4820) = false := by
  decide +kernel

theorem node_context_9_4820_1087634 : EJMOriginalGlobalDAGData.nodes 12 ⟨1087634, by decide⟩ =
    .split (coordinate 9) (![⟨1085813, by decide⟩,⟨1086346, by decide⟩,⟨1087085, by decide⟩,⟨1087633, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4820_1087634 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4820 ⟨1087634, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4820
    ⟨1087634, by decide⟩ (by decide) (![⟨1085813, by decide⟩,⟨1086346, by decide⟩,⟨1087085, by decide⟩,⟨1087633, by decide⟩]) unmarked_context_9_4820_1087634 node_context_9_4820_1087634
  intro a
  fin_cases a
  · exact context_10_19280_1085813
  · exact context_10_19281_1086346
  · exact context_10_19282_1087085
  · exact context_10_19283_1087633

theorem selected_cut_40053 : selected 9 ⟨169790, by decide⟩
    (prefixPartial 12 308544) = some ⟨12, 1, 0, 169790, 308544, 1, 65536⟩ := by
  decide +kernel

theorem context_12_308544_169790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308544 ⟨169790, by decide⟩ :=
  accepted_of_selected 12 308544 ⟨169790, by decide⟩ ⟨12, 1, 0, 169790, 308544, 1, 65536⟩
    (by decide) selected_cut_40053

theorem selected_cut_40054 : selected 9 ⟨1087666, by decide⟩
    (prefixPartial 12 308545) = some ⟨12, 2, 0, 1087666, 308545, 2049, 65536⟩ := by
  decide +kernel

theorem context_12_308545_1087666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308545 ⟨1087666, by decide⟩ :=
  accepted_of_selected 12 308545 ⟨1087666, by decide⟩ ⟨12, 2, 0, 1087666, 308545, 2049, 65536⟩
    (by decide) selected_cut_40054

theorem selected_cut_40055 : selected 9 ⟨1087706, by decide⟩
    (prefixPartial 12 308546) = some ⟨12, 2, 0, 1087706, 308546, 2357, 65536⟩ := by
  decide +kernel

theorem context_12_308546_1087706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308546 ⟨1087706, by decide⟩ :=
  accepted_of_selected 12 308546 ⟨1087706, by decide⟩ ⟨12, 2, 0, 1087706, 308546, 2357, 65536⟩
    (by decide) selected_cut_40055

theorem selected_cut_40056 : selected 9 ⟨1087736, by decide⟩
    (prefixPartial 12 308547) = some ⟨12, 2, 0, 1087736, 308547, 2349, 65536⟩ := by
  decide +kernel

theorem context_12_308547_1087736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308547 ⟨1087736, by decide⟩ :=
  accepted_of_selected 12 308547 ⟨1087736, by decide⟩ ⟨12, 2, 0, 1087736, 308547, 2349, 65536⟩
    (by decide) selected_cut_40056

theorem unmarked_context_11_77136_1087737 : frontier 10 ⟨1087737, by decide⟩
    (prefixCache 11 77136) (prefixPartial 11 77136) = false := by
  decide +kernel

theorem node_context_11_77136_1087737 : EJMOriginalGlobalDAGData.nodes 10 ⟨1087737, by decide⟩ =
    .split (coordinate 11) (![⟨169790, by decide⟩,⟨1087666, by decide⟩,⟨1087706, by decide⟩,⟨1087736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77136_1087737 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77136 ⟨1087737, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77136
    ⟨1087737, by decide⟩ (by decide) (![⟨169790, by decide⟩,⟨1087666, by decide⟩,⟨1087706, by decide⟩,⟨1087736, by decide⟩]) unmarked_context_11_77136_1087737 node_context_11_77136_1087737
  intro a
  fin_cases a
  · exact context_12_308544_169790
  · exact context_12_308545_1087666
  · exact context_12_308546_1087706
  · exact context_12_308547_1087736

theorem selected_cut_40057 : selected 9 ⟨1087777, by decide⟩
    (prefixPartial 12 308548) = some ⟨12, 2, 0, 1087777, 308548, 2837, 65536⟩ := by
  decide +kernel

theorem context_12_308548_1087777 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308548 ⟨1087777, by decide⟩ :=
  accepted_of_selected 12 308548 ⟨1087777, by decide⟩ ⟨12, 2, 0, 1087777, 308548, 2837, 65536⟩
    (by decide) selected_cut_40057

theorem selected_cut_40058 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 308549) = some ⟨12, 1, 0, 891951, 308549, 1, 65536⟩ := by
  decide +kernel

theorem context_12_308549_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308549 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 308549 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 308549, 1, 65536⟩
    (by decide) selected_cut_40058

theorem selected_cut_40059 : selected 9 ⟨1087804, by decide⟩
    (prefixPartial 12 308550) = some ⟨12, 2, 0, 1087804, 308550, 2033, 65536⟩ := by
  decide +kernel

theorem context_12_308550_1087804 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308550 ⟨1087804, by decide⟩ :=
  accepted_of_selected 12 308550 ⟨1087804, by decide⟩ ⟨12, 2, 0, 1087804, 308550, 2033, 65536⟩
    (by decide) selected_cut_40059

theorem selected_cut_40060 : selected 9 ⟨1087833, by decide⟩
    (prefixPartial 12 308551) = some ⟨12, 2, 0, 1087833, 308551, 2149, 65536⟩ := by
  decide +kernel

theorem context_12_308551_1087833 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308551 ⟨1087833, by decide⟩ :=
  accepted_of_selected 12 308551 ⟨1087833, by decide⟩ ⟨12, 2, 0, 1087833, 308551, 2149, 65536⟩
    (by decide) selected_cut_40060

theorem unmarked_context_11_77137_1087834 : frontier 10 ⟨1087834, by decide⟩
    (prefixCache 11 77137) (prefixPartial 11 77137) = false := by
  decide +kernel

theorem node_context_11_77137_1087834 : EJMOriginalGlobalDAGData.nodes 10 ⟨1087834, by decide⟩ =
    .split (coordinate 11) (![⟨1087777, by decide⟩,⟨891951, by decide⟩,⟨1087804, by decide⟩,⟨1087833, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77137_1087834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77137 ⟨1087834, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77137
    ⟨1087834, by decide⟩ (by decide) (![⟨1087777, by decide⟩,⟨891951, by decide⟩,⟨1087804, by decide⟩,⟨1087833, by decide⟩]) unmarked_context_11_77137_1087834 node_context_11_77137_1087834
  intro a
  fin_cases a
  · exact context_12_308548_1087777
  · exact context_12_308549_891951
  · exact context_12_308550_1087804
  · exact context_12_308551_1087833

theorem selected_cut_40061 : selected 9 ⟨1087894, by decide⟩
    (prefixPartial 12 308552) = some ⟨12, 2, 0, 1087894, 308552, 3065, 65536⟩ := by
  decide +kernel

theorem context_12_308552_1087894 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308552 ⟨1087894, by decide⟩ :=
  accepted_of_selected 12 308552 ⟨1087894, by decide⟩ ⟨12, 2, 0, 1087894, 308552, 3065, 65536⟩
    (by decide) selected_cut_40061

theorem selected_cut_40062 : selected 9 ⟨1087925, by decide⟩
    (prefixPartial 12 308553) = some ⟨12, 2, 0, 1087925, 308553, 2105, 65536⟩ := by
  decide +kernel

theorem context_12_308553_1087925 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308553 ⟨1087925, by decide⟩ :=
  accepted_of_selected 12 308553 ⟨1087925, by decide⟩ ⟨12, 2, 0, 1087925, 308553, 2105, 65536⟩
    (by decide) selected_cut_40062

theorem selected_cut_40063 : selected 9 ⟨1087958, by decide⟩
    (prefixPartial 12 308554) = some ⟨12, 2, 0, 1087958, 308554, 2513, 65536⟩ := by
  decide +kernel

theorem context_12_308554_1087958 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308554 ⟨1087958, by decide⟩ :=
  accepted_of_selected 12 308554 ⟨1087958, by decide⟩ ⟨12, 2, 0, 1087958, 308554, 2513, 65536⟩
    (by decide) selected_cut_40063

theorem selected_cut_40064 : selected 9 ⟨1088001, by decide⟩
    (prefixPartial 12 308555) = some ⟨12, 2, 0, 1088001, 308555, 2493, 65536⟩ := by
  decide +kernel

theorem context_12_308555_1088001 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308555 ⟨1088001, by decide⟩ :=
  accepted_of_selected 12 308555 ⟨1088001, by decide⟩ ⟨12, 2, 0, 1088001, 308555, 2493, 65536⟩
    (by decide) selected_cut_40064

theorem unmarked_context_11_77138_1088002 : frontier 10 ⟨1088002, by decide⟩
    (prefixCache 11 77138) (prefixPartial 11 77138) = false := by
  decide +kernel

theorem node_context_11_77138_1088002 : EJMOriginalGlobalDAGData.nodes 10 ⟨1088002, by decide⟩ =
    .split (coordinate 11) (![⟨1087894, by decide⟩,⟨1087925, by decide⟩,⟨1087958, by decide⟩,⟨1088001, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77138_1088002 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77138 ⟨1088002, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77138
    ⟨1088002, by decide⟩ (by decide) (![⟨1087894, by decide⟩,⟨1087925, by decide⟩,⟨1087958, by decide⟩,⟨1088001, by decide⟩]) unmarked_context_11_77138_1088002 node_context_11_77138_1088002
  intro a
  fin_cases a
  · exact context_12_308552_1087894
  · exact context_12_308553_1087925
  · exact context_12_308554_1087958
  · exact context_12_308555_1088001

theorem selected_cut_40065 : selected 9 ⟨1088057, by decide⟩
    (prefixPartial 12 308556) = some ⟨12, 2, 0, 1088057, 308556, 3021, 65536⟩ := by
  decide +kernel

theorem context_12_308556_1088057 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308556 ⟨1088057, by decide⟩ :=
  accepted_of_selected 12 308556 ⟨1088057, by decide⟩ ⟨12, 2, 0, 1088057, 308556, 3021, 65536⟩
    (by decide) selected_cut_40065

theorem selected_cut_40066 : selected 9 ⟨1088082, by decide⟩
    (prefixPartial 12 308557) = some ⟨12, 2, 0, 1088082, 308557, 1941, 65536⟩ := by
  decide +kernel

theorem context_12_308557_1088082 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308557 ⟨1088082, by decide⟩ :=
  accepted_of_selected 12 308557 ⟨1088082, by decide⟩ ⟨12, 2, 0, 1088082, 308557, 1941, 65536⟩
    (by decide) selected_cut_40066

theorem selected_cut_40067 : selected 9 ⟨1088119, by decide⟩
    (prefixPartial 12 308558) = some ⟨12, 2, 0, 1088119, 308558, 2337, 65536⟩ := by
  decide +kernel

theorem context_12_308558_1088119 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308558 ⟨1088119, by decide⟩ :=
  accepted_of_selected 12 308558 ⟨1088119, by decide⟩ ⟨12, 2, 0, 1088119, 308558, 2337, 65536⟩
    (by decide) selected_cut_40067

theorem selected_cut_40068 : selected 9 ⟨1088158, by decide⟩
    (prefixPartial 12 308559) = some ⟨12, 2, 0, 1088158, 308559, 2393, 65536⟩ := by
  decide +kernel

theorem context_12_308559_1088158 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308559 ⟨1088158, by decide⟩ :=
  accepted_of_selected 12 308559 ⟨1088158, by decide⟩ ⟨12, 2, 0, 1088158, 308559, 2393, 65536⟩
    (by decide) selected_cut_40068

theorem unmarked_context_11_77139_1088159 : frontier 10 ⟨1088159, by decide⟩
    (prefixCache 11 77139) (prefixPartial 11 77139) = false := by
  decide +kernel

theorem node_context_11_77139_1088159 : EJMOriginalGlobalDAGData.nodes 10 ⟨1088159, by decide⟩ =
    .split (coordinate 11) (![⟨1088057, by decide⟩,⟨1088082, by decide⟩,⟨1088119, by decide⟩,⟨1088158, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77139_1088159 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77139 ⟨1088159, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77139
    ⟨1088159, by decide⟩ (by decide) (![⟨1088057, by decide⟩,⟨1088082, by decide⟩,⟨1088119, by decide⟩,⟨1088158, by decide⟩]) unmarked_context_11_77139_1088159 node_context_11_77139_1088159
  intro a
  fin_cases a
  · exact context_12_308556_1088057
  · exact context_12_308557_1088082
  · exact context_12_308558_1088119
  · exact context_12_308559_1088158

theorem unmarked_context_10_19284_1088160 : frontier 11 ⟨1088160, by decide⟩
    (prefixCache 10 19284) (prefixPartial 10 19284) = false := by
  decide +kernel

theorem node_context_10_19284_1088160 : EJMOriginalGlobalDAGData.nodes 11 ⟨1088160, by decide⟩ =
    .split (coordinate 10) (![⟨1087737, by decide⟩,⟨1087834, by decide⟩,⟨1088002, by decide⟩,⟨1088159, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19284_1088160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19284 ⟨1088160, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19284
    ⟨1088160, by decide⟩ (by decide) (![⟨1087737, by decide⟩,⟨1087834, by decide⟩,⟨1088002, by decide⟩,⟨1088159, by decide⟩]) unmarked_context_10_19284_1088160 node_context_10_19284_1088160
  intro a
  fin_cases a
  · exact context_11_77136_1087737
  · exact context_11_77137_1087834
  · exact context_11_77138_1088002
  · exact context_11_77139_1088159

theorem selected_cut_40069 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 19285) = some ⟨10, 1, 0, 893098, 19285, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_19285_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19285 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 19285 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 19285, 1, 1048576⟩
    (by decide) selected_cut_40069

theorem selected_cut_40070 : selected 9 ⟨1088194, by decide⟩
    (prefixPartial 12 308576) = some ⟨12, 2, 0, 1088194, 308576, 2337, 65536⟩ := by
  decide +kernel

theorem context_12_308576_1088194 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308576 ⟨1088194, by decide⟩ :=
  accepted_of_selected 12 308576 ⟨1088194, by decide⟩ ⟨12, 2, 0, 1088194, 308576, 2337, 65536⟩
    (by decide) selected_cut_40070

theorem selected_cut_40071 : selected 9 ⟨1088216, by decide⟩
    (prefixPartial 12 308577) = some ⟨12, 2, 0, 1088216, 308577, 1929, 65536⟩ := by
  decide +kernel

theorem context_12_308577_1088216 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308577 ⟨1088216, by decide⟩ :=
  accepted_of_selected 12 308577 ⟨1088216, by decide⟩ ⟨12, 2, 0, 1088216, 308577, 1929, 65536⟩
    (by decide) selected_cut_40071

theorem selected_cut_40072 : selected 9 ⟨1088254, by decide⟩
    (prefixPartial 12 308578) = some ⟨12, 2, 0, 1088254, 308578, 2105, 65536⟩ := by
  decide +kernel

theorem context_12_308578_1088254 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308578 ⟨1088254, by decide⟩ :=
  accepted_of_selected 12 308578 ⟨1088254, by decide⟩ ⟨12, 2, 0, 1088254, 308578, 2105, 65536⟩
    (by decide) selected_cut_40072

theorem selected_cut_40073 : selected 9 ⟨1088285, by decide⟩
    (prefixPartial 12 308579) = some ⟨12, 2, 0, 1088285, 308579, 2121, 65536⟩ := by
  decide +kernel

theorem context_12_308579_1088285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308579 ⟨1088285, by decide⟩ :=
  accepted_of_selected 12 308579 ⟨1088285, by decide⟩ ⟨12, 2, 0, 1088285, 308579, 2121, 65536⟩
    (by decide) selected_cut_40073

theorem unmarked_context_11_77144_1088286 : frontier 10 ⟨1088286, by decide⟩
    (prefixCache 11 77144) (prefixPartial 11 77144) = false := by
  decide +kernel

theorem node_context_11_77144_1088286 : EJMOriginalGlobalDAGData.nodes 10 ⟨1088286, by decide⟩ =
    .split (coordinate 11) (![⟨1088194, by decide⟩,⟨1088216, by decide⟩,⟨1088254, by decide⟩,⟨1088285, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77144_1088286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77144 ⟨1088286, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77144
    ⟨1088286, by decide⟩ (by decide) (![⟨1088194, by decide⟩,⟨1088216, by decide⟩,⟨1088254, by decide⟩,⟨1088285, by decide⟩]) unmarked_context_11_77144_1088286 node_context_11_77144_1088286
  intro a
  fin_cases a
  · exact context_12_308576_1088194
  · exact context_12_308577_1088216
  · exact context_12_308578_1088254
  · exact context_12_308579_1088285

theorem selected_cut_40074 : selected 9 ⟨1088317, by decide⟩
    (prefixPartial 12 308580) = some ⟨12, 2, 0, 1088317, 308580, 1973, 65536⟩ := by
  decide +kernel

theorem context_12_308580_1088317 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308580 ⟨1088317, by decide⟩ :=
  accepted_of_selected 12 308580 ⟨1088317, by decide⟩ ⟨12, 2, 0, 1088317, 308580, 1973, 65536⟩
    (by decide) selected_cut_40074

theorem selected_cut_40075 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 308581) = some ⟨12, 1, 0, 891951, 308581, 1, 65536⟩ := by
  decide +kernel

theorem context_12_308581_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308581 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 308581 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 308581, 1, 65536⟩
    (by decide) selected_cut_40075

theorem selected_cut_40076 : selected 9 ⟨1088343, by decide⟩
    (prefixPartial 12 308582) = some ⟨12, 2, 0, 1088343, 308582, 1685, 65536⟩ := by
  decide +kernel

theorem context_12_308582_1088343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308582 ⟨1088343, by decide⟩ :=
  accepted_of_selected 12 308582 ⟨1088343, by decide⟩ ⟨12, 2, 0, 1088343, 308582, 1685, 65536⟩
    (by decide) selected_cut_40076

theorem selected_cut_40077 : selected 9 ⟨1088367, by decide⟩
    (prefixPartial 12 308583) = some ⟨12, 2, 0, 1088367, 308583, 1817, 65536⟩ := by
  decide +kernel

theorem context_12_308583_1088367 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308583 ⟨1088367, by decide⟩ :=
  accepted_of_selected 12 308583 ⟨1088367, by decide⟩ ⟨12, 2, 0, 1088367, 308583, 1817, 65536⟩
    (by decide) selected_cut_40077

theorem unmarked_context_11_77145_1088368 : frontier 10 ⟨1088368, by decide⟩
    (prefixCache 11 77145) (prefixPartial 11 77145) = false := by
  decide +kernel

theorem node_context_11_77145_1088368 : EJMOriginalGlobalDAGData.nodes 10 ⟨1088368, by decide⟩ =
    .split (coordinate 11) (![⟨1088317, by decide⟩,⟨891951, by decide⟩,⟨1088343, by decide⟩,⟨1088367, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77145_1088368 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77145 ⟨1088368, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77145
    ⟨1088368, by decide⟩ (by decide) (![⟨1088317, by decide⟩,⟨891951, by decide⟩,⟨1088343, by decide⟩,⟨1088367, by decide⟩]) unmarked_context_11_77145_1088368 node_context_11_77145_1088368
  intro a
  fin_cases a
  · exact context_12_308580_1088317
  · exact context_12_308581_891951
  · exact context_12_308582_1088343
  · exact context_12_308583_1088367

theorem selected_cut_40078 : selected 9 ⟨1088400, by decide⟩
    (prefixPartial 12 308584) = some ⟨12, 2, 0, 1088400, 308584, 2277, 65536⟩ := by
  decide +kernel

theorem context_12_308584_1088400 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308584 ⟨1088400, by decide⟩ :=
  accepted_of_selected 12 308584 ⟨1088400, by decide⟩ ⟨12, 2, 0, 1088400, 308584, 2277, 65536⟩
    (by decide) selected_cut_40078

theorem selected_cut_40079 : selected 9 ⟨1088436, by decide⟩
    (prefixPartial 12 308585) = some ⟨12, 2, 0, 1088436, 308585, 1993, 65536⟩ := by
  decide +kernel

theorem context_12_308585_1088436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308585 ⟨1088436, by decide⟩ :=
  accepted_of_selected 12 308585 ⟨1088436, by decide⟩ ⟨12, 2, 0, 1088436, 308585, 1993, 65536⟩
    (by decide) selected_cut_40079

theorem selected_cut_40080 : selected 9 ⟨661671, by decide⟩
    (prefixPartial 12 308586) = some ⟨12, 1, 0, 661671, 308586, 1, 65536⟩ := by
  decide +kernel

theorem context_12_308586_661671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308586 ⟨661671, by decide⟩ :=
  accepted_of_selected 12 308586 ⟨661671, by decide⟩ ⟨12, 1, 0, 661671, 308586, 1, 65536⟩
    (by decide) selected_cut_40080

theorem selected_cut_40081 : selected 9 ⟨1088474, by decide⟩
    (prefixPartial 12 308587) = some ⟨12, 2, 0, 1088474, 308587, 2253, 65536⟩ := by
  decide +kernel

theorem context_12_308587_1088474 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308587 ⟨1088474, by decide⟩ :=
  accepted_of_selected 12 308587 ⟨1088474, by decide⟩ ⟨12, 2, 0, 1088474, 308587, 2253, 65536⟩
    (by decide) selected_cut_40081

theorem unmarked_context_11_77146_1088475 : frontier 10 ⟨1088475, by decide⟩
    (prefixCache 11 77146) (prefixPartial 11 77146) = false := by
  decide +kernel

theorem node_context_11_77146_1088475 : EJMOriginalGlobalDAGData.nodes 10 ⟨1088475, by decide⟩ =
    .split (coordinate 11) (![⟨1088400, by decide⟩,⟨1088436, by decide⟩,⟨661671, by decide⟩,⟨1088474, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77146_1088475 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77146 ⟨1088475, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77146
    ⟨1088475, by decide⟩ (by decide) (![⟨1088400, by decide⟩,⟨1088436, by decide⟩,⟨661671, by decide⟩,⟨1088474, by decide⟩]) unmarked_context_11_77146_1088475 node_context_11_77146_1088475
  intro a
  fin_cases a
  · exact context_12_308584_1088400
  · exact context_12_308585_1088436
  · exact context_12_308586_661671
  · exact context_12_308587_1088474

theorem selected_cut_40082 : selected 9 ⟨1088505, by decide⟩
    (prefixPartial 12 308588) = some ⟨12, 2, 0, 1088505, 308588, 2153, 65536⟩ := by
  decide +kernel

theorem context_12_308588_1088505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308588 ⟨1088505, by decide⟩ :=
  accepted_of_selected 12 308588 ⟨1088505, by decide⟩ ⟨12, 2, 0, 1088505, 308588, 2153, 65536⟩
    (by decide) selected_cut_40082

theorem selected_cut_40083 : selected 9 ⟨1088529, by decide⟩
    (prefixPartial 12 308589) = some ⟨12, 2, 0, 1088529, 308589, 1765, 65536⟩ := by
  decide +kernel

theorem context_12_308589_1088529 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308589 ⟨1088529, by decide⟩ :=
  accepted_of_selected 12 308589 ⟨1088529, by decide⟩ ⟨12, 2, 0, 1088529, 308589, 1765, 65536⟩
    (by decide) selected_cut_40083

theorem selected_cut_40084 : selected 9 ⟨1088561, by decide⟩
    (prefixPartial 12 308590) = some ⟨12, 2, 0, 1088561, 308590, 1945, 65536⟩ := by
  decide +kernel

theorem context_12_308590_1088561 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308590 ⟨1088561, by decide⟩ :=
  accepted_of_selected 12 308590 ⟨1088561, by decide⟩ ⟨12, 2, 0, 1088561, 308590, 1945, 65536⟩
    (by decide) selected_cut_40084

theorem selected_cut_40085 : selected 9 ⟨1088594, by decide⟩
    (prefixPartial 12 308591) = some ⟨12, 2, 0, 1088594, 308591, 1989, 65536⟩ := by
  decide +kernel

theorem context_12_308591_1088594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308591 ⟨1088594, by decide⟩ :=
  accepted_of_selected 12 308591 ⟨1088594, by decide⟩ ⟨12, 2, 0, 1088594, 308591, 1989, 65536⟩
    (by decide) selected_cut_40085

theorem unmarked_context_11_77147_1088595 : frontier 10 ⟨1088595, by decide⟩
    (prefixCache 11 77147) (prefixPartial 11 77147) = false := by
  decide +kernel

theorem node_context_11_77147_1088595 : EJMOriginalGlobalDAGData.nodes 10 ⟨1088595, by decide⟩ =
    .split (coordinate 11) (![⟨1088505, by decide⟩,⟨1088529, by decide⟩,⟨1088561, by decide⟩,⟨1088594, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77147_1088595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77147 ⟨1088595, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77147
    ⟨1088595, by decide⟩ (by decide) (![⟨1088505, by decide⟩,⟨1088529, by decide⟩,⟨1088561, by decide⟩,⟨1088594, by decide⟩]) unmarked_context_11_77147_1088595 node_context_11_77147_1088595
  intro a
  fin_cases a
  · exact context_12_308588_1088505
  · exact context_12_308589_1088529
  · exact context_12_308590_1088561
  · exact context_12_308591_1088594

theorem unmarked_context_10_19286_1088596 : frontier 11 ⟨1088596, by decide⟩
    (prefixCache 10 19286) (prefixPartial 10 19286) = false := by
  decide +kernel

theorem node_context_10_19286_1088596 : EJMOriginalGlobalDAGData.nodes 11 ⟨1088596, by decide⟩ =
    .split (coordinate 10) (![⟨1088286, by decide⟩,⟨1088368, by decide⟩,⟨1088475, by decide⟩,⟨1088595, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19286_1088596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19286 ⟨1088596, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19286
    ⟨1088596, by decide⟩ (by decide) (![⟨1088286, by decide⟩,⟨1088368, by decide⟩,⟨1088475, by decide⟩,⟨1088595, by decide⟩]) unmarked_context_10_19286_1088596 node_context_10_19286_1088596
  intro a
  fin_cases a
  · exact context_11_77144_1088286
  · exact context_11_77145_1088368
  · exact context_11_77146_1088475
  · exact context_11_77147_1088595

theorem selected_cut_40086 : selected 9 ⟨1088624, by decide⟩
    (prefixPartial 12 308592) = some ⟨12, 2, 0, 1088624, 308592, 1877, 65536⟩ := by
  decide +kernel

theorem context_12_308592_1088624 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308592 ⟨1088624, by decide⟩ :=
  accepted_of_selected 12 308592 ⟨1088624, by decide⟩ ⟨12, 2, 0, 1088624, 308592, 1877, 65536⟩
    (by decide) selected_cut_40086

theorem selected_cut_40087 : selected 9 ⟨1088648, by decide⟩
    (prefixPartial 12 308593) = some ⟨12, 2, 0, 1088648, 308593, 1489, 65536⟩ := by
  decide +kernel

theorem context_12_308593_1088648 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308593 ⟨1088648, by decide⟩ :=
  accepted_of_selected 12 308593 ⟨1088648, by decide⟩ ⟨12, 2, 0, 1088648, 308593, 1489, 65536⟩
    (by decide) selected_cut_40087

theorem selected_cut_40088 : selected 9 ⟨1088671, by decide⟩
    (prefixPartial 12 308594) = some ⟨12, 2, 0, 1088671, 308594, 1641, 65536⟩ := by
  decide +kernel

theorem context_12_308594_1088671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308594 ⟨1088671, by decide⟩ :=
  accepted_of_selected 12 308594 ⟨1088671, by decide⟩ ⟨12, 2, 0, 1088671, 308594, 1641, 65536⟩
    (by decide) selected_cut_40088

theorem selected_cut_40089 : selected 9 ⟨1088691, by decide⟩
    (prefixPartial 12 308595) = some ⟨12, 2, 0, 1088691, 308595, 1549, 65536⟩ := by
  decide +kernel

theorem context_12_308595_1088691 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308595 ⟨1088691, by decide⟩ :=
  accepted_of_selected 12 308595 ⟨1088691, by decide⟩ ⟨12, 2, 0, 1088691, 308595, 1549, 65536⟩
    (by decide) selected_cut_40089

theorem unmarked_context_11_77148_1088692 : frontier 10 ⟨1088692, by decide⟩
    (prefixCache 11 77148) (prefixPartial 11 77148) = false := by
  decide +kernel

theorem node_context_11_77148_1088692 : EJMOriginalGlobalDAGData.nodes 10 ⟨1088692, by decide⟩ =
    .split (coordinate 11) (![⟨1088624, by decide⟩,⟨1088648, by decide⟩,⟨1088671, by decide⟩,⟨1088691, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77148_1088692 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77148 ⟨1088692, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77148
    ⟨1088692, by decide⟩ (by decide) (![⟨1088624, by decide⟩,⟨1088648, by decide⟩,⟨1088671, by decide⟩,⟨1088691, by decide⟩]) unmarked_context_11_77148_1088692 node_context_11_77148_1088692
  intro a
  fin_cases a
  · exact context_12_308592_1088624
  · exact context_12_308593_1088648
  · exact context_12_308594_1088671
  · exact context_12_308595_1088691

theorem selected_cut_40090 : selected 9 ⟨1088717, by decide⟩
    (prefixPartial 12 308596) = some ⟨12, 2, 0, 1088717, 308596, 1637, 65536⟩ := by
  decide +kernel

theorem context_12_308596_1088717 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308596 ⟨1088717, by decide⟩ :=
  accepted_of_selected 12 308596 ⟨1088717, by decide⟩ ⟨12, 2, 0, 1088717, 308596, 1637, 65536⟩
    (by decide) selected_cut_40090

theorem selected_cut_40091 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 308597) = some ⟨12, 1, 0, 891951, 308597, 1, 65536⟩ := by
  decide +kernel

theorem context_12_308597_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308597 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 308597 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 308597, 1, 65536⟩
    (by decide) selected_cut_40091

theorem selected_cut_40092 : selected 9 ⟨1088734, by decide⟩
    (prefixPartial 12 308598) = some ⟨12, 2, 0, 1088734, 308598, 1445, 65536⟩ := by
  decide +kernel

theorem context_12_308598_1088734 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308598 ⟨1088734, by decide⟩ :=
  accepted_of_selected 12 308598 ⟨1088734, by decide⟩ ⟨12, 2, 0, 1088734, 308598, 1445, 65536⟩
    (by decide) selected_cut_40092

theorem selected_cut_40093 : selected 9 ⟨1088752, by decide⟩
    (prefixPartial 12 308599) = some ⟨12, 2, 0, 1088752, 308599, 1405, 65536⟩ := by
  decide +kernel

theorem context_12_308599_1088752 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308599 ⟨1088752, by decide⟩ :=
  accepted_of_selected 12 308599 ⟨1088752, by decide⟩ ⟨12, 2, 0, 1088752, 308599, 1405, 65536⟩
    (by decide) selected_cut_40093

theorem unmarked_context_11_77149_1088753 : frontier 10 ⟨1088753, by decide⟩
    (prefixCache 11 77149) (prefixPartial 11 77149) = false := by
  decide +kernel

theorem node_context_11_77149_1088753 : EJMOriginalGlobalDAGData.nodes 10 ⟨1088753, by decide⟩ =
    .split (coordinate 11) (![⟨1088717, by decide⟩,⟨891951, by decide⟩,⟨1088734, by decide⟩,⟨1088752, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77149_1088753 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77149 ⟨1088753, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77149
    ⟨1088753, by decide⟩ (by decide) (![⟨1088717, by decide⟩,⟨891951, by decide⟩,⟨1088734, by decide⟩,⟨1088752, by decide⟩]) unmarked_context_11_77149_1088753 node_context_11_77149_1088753
  intro a
  fin_cases a
  · exact context_12_308596_1088717
  · exact context_12_308597_891951
  · exact context_12_308598_1088734
  · exact context_12_308599_1088752

theorem selected_cut_40094 : selected 9 ⟨1088780, by decide⟩
    (prefixPartial 12 308600) = some ⟨12, 2, 0, 1088780, 308600, 1657, 65536⟩ := by
  decide +kernel

theorem context_12_308600_1088780 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308600 ⟨1088780, by decide⟩ :=
  accepted_of_selected 12 308600 ⟨1088780, by decide⟩ ⟨12, 2, 0, 1088780, 308600, 1657, 65536⟩
    (by decide) selected_cut_40094

theorem selected_cut_40095 : selected 9 ⟨1088801, by decide⟩
    (prefixPartial 12 308601) = some ⟨12, 2, 0, 1088801, 308601, 1365, 65536⟩ := by
  decide +kernel

theorem context_12_308601_1088801 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308601 ⟨1088801, by decide⟩ :=
  accepted_of_selected 12 308601 ⟨1088801, by decide⟩ ⟨12, 2, 0, 1088801, 308601, 1365, 65536⟩
    (by decide) selected_cut_40095

theorem selected_cut_40096 : selected 9 ⟨1088825, by decide⟩
    (prefixPartial 12 308602) = some ⟨12, 2, 0, 1088825, 308602, 1533, 65536⟩ := by
  decide +kernel

theorem context_12_308602_1088825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308602 ⟨1088825, by decide⟩ :=
  accepted_of_selected 12 308602 ⟨1088825, by decide⟩ ⟨12, 2, 0, 1088825, 308602, 1533, 65536⟩
    (by decide) selected_cut_40096

theorem selected_cut_40097 : selected 9 ⟨1088849, by decide⟩
    (prefixPartial 12 308603) = some ⟨12, 2, 0, 1088849, 308603, 1485, 65536⟩ := by
  decide +kernel

theorem context_12_308603_1088849 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308603 ⟨1088849, by decide⟩ :=
  accepted_of_selected 12 308603 ⟨1088849, by decide⟩ ⟨12, 2, 0, 1088849, 308603, 1485, 65536⟩
    (by decide) selected_cut_40097

theorem unmarked_context_11_77150_1088850 : frontier 10 ⟨1088850, by decide⟩
    (prefixCache 11 77150) (prefixPartial 11 77150) = false := by
  decide +kernel

theorem node_context_11_77150_1088850 : EJMOriginalGlobalDAGData.nodes 10 ⟨1088850, by decide⟩ =
    .split (coordinate 11) (![⟨1088780, by decide⟩,⟨1088801, by decide⟩,⟨1088825, by decide⟩,⟨1088849, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77150_1088850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77150 ⟨1088850, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77150
    ⟨1088850, by decide⟩ (by decide) (![⟨1088780, by decide⟩,⟨1088801, by decide⟩,⟨1088825, by decide⟩,⟨1088849, by decide⟩]) unmarked_context_11_77150_1088850 node_context_11_77150_1088850
  intro a
  fin_cases a
  · exact context_12_308600_1088780
  · exact context_12_308601_1088801
  · exact context_12_308602_1088825
  · exact context_12_308603_1088849

theorem selected_cut_40098 : selected 9 ⟨1088872, by decide⟩
    (prefixPartial 12 308604) = some ⟨12, 2, 0, 1088872, 308604, 1557, 65536⟩ := by
  decide +kernel

theorem context_12_308604_1088872 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308604 ⟨1088872, by decide⟩ :=
  accepted_of_selected 12 308604 ⟨1088872, by decide⟩ ⟨12, 2, 0, 1088872, 308604, 1557, 65536⟩
    (by decide) selected_cut_40098

theorem selected_cut_40099 : selected 9 ⟨1088891, by decide⟩
    (prefixPartial 12 308605) = some ⟨12, 2, 0, 1088891, 308605, 1321, 65536⟩ := by
  decide +kernel

theorem context_12_308605_1088891 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308605 ⟨1088891, by decide⟩ :=
  accepted_of_selected 12 308605 ⟨1088891, by decide⟩ ⟨12, 2, 0, 1088891, 308605, 1321, 65536⟩
    (by decide) selected_cut_40099

theorem selected_cut_40100 : selected 9 ⟨1088914, by decide⟩
    (prefixPartial 12 308606) = some ⟨12, 2, 0, 1088914, 308606, 1453, 65536⟩ := by
  decide +kernel

theorem context_12_308606_1088914 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308606 ⟨1088914, by decide⟩ :=
  accepted_of_selected 12 308606 ⟨1088914, by decide⟩ ⟨12, 2, 0, 1088914, 308606, 1453, 65536⟩
    (by decide) selected_cut_40100

theorem selected_cut_40101 : selected 9 ⟨762108, by decide⟩
    (prefixPartial 12 308607) = some ⟨12, 1, 0, 762108, 308607, 1, 65536⟩ := by
  decide +kernel

theorem context_12_308607_762108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308607 ⟨762108, by decide⟩ :=
  accepted_of_selected 12 308607 ⟨762108, by decide⟩ ⟨12, 1, 0, 762108, 308607, 1, 65536⟩
    (by decide) selected_cut_40101

theorem unmarked_context_11_77151_1088915 : frontier 10 ⟨1088915, by decide⟩
    (prefixCache 11 77151) (prefixPartial 11 77151) = false := by
  decide +kernel

theorem node_context_11_77151_1088915 : EJMOriginalGlobalDAGData.nodes 10 ⟨1088915, by decide⟩ =
    .split (coordinate 11) (![⟨1088872, by decide⟩,⟨1088891, by decide⟩,⟨1088914, by decide⟩,⟨762108, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77151_1088915 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77151 ⟨1088915, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77151
    ⟨1088915, by decide⟩ (by decide) (![⟨1088872, by decide⟩,⟨1088891, by decide⟩,⟨1088914, by decide⟩,⟨762108, by decide⟩]) unmarked_context_11_77151_1088915 node_context_11_77151_1088915
  intro a
  fin_cases a
  · exact context_12_308604_1088872
  · exact context_12_308605_1088891
  · exact context_12_308606_1088914
  · exact context_12_308607_762108

theorem unmarked_context_10_19287_1088916 : frontier 11 ⟨1088916, by decide⟩
    (prefixCache 10 19287) (prefixPartial 10 19287) = false := by
  decide +kernel

theorem node_context_10_19287_1088916 : EJMOriginalGlobalDAGData.nodes 11 ⟨1088916, by decide⟩ =
    .split (coordinate 10) (![⟨1088692, by decide⟩,⟨1088753, by decide⟩,⟨1088850, by decide⟩,⟨1088915, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19287_1088916 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19287 ⟨1088916, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19287
    ⟨1088916, by decide⟩ (by decide) (![⟨1088692, by decide⟩,⟨1088753, by decide⟩,⟨1088850, by decide⟩,⟨1088915, by decide⟩]) unmarked_context_10_19287_1088916 node_context_10_19287_1088916
  intro a
  fin_cases a
  · exact context_11_77148_1088692
  · exact context_11_77149_1088753
  · exact context_11_77150_1088850
  · exact context_11_77151_1088915

theorem unmarked_context_9_4821_1088917 : frontier 12 ⟨1088917, by decide⟩
    (prefixCache 9 4821) (prefixPartial 9 4821) = false := by
  decide +kernel

theorem node_context_9_4821_1088917 : EJMOriginalGlobalDAGData.nodes 12 ⟨1088917, by decide⟩ =
    .split (coordinate 9) (![⟨1088160, by decide⟩,⟨893098, by decide⟩,⟨1088596, by decide⟩,⟨1088916, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4821_1088917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4821 ⟨1088917, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4821
    ⟨1088917, by decide⟩ (by decide) (![⟨1088160, by decide⟩,⟨893098, by decide⟩,⟨1088596, by decide⟩,⟨1088916, by decide⟩]) unmarked_context_9_4821_1088917 node_context_9_4821_1088917
  intro a
  fin_cases a
  · exact context_10_19284_1088160
  · exact context_10_19285_893098
  · exact context_10_19286_1088596
  · exact context_10_19287_1088916

theorem selected_cut_40102 : selected 10 ⟨1088959, by decide⟩
    (prefixPartial 11 77152) = some ⟨11, 2, 0, 1088959, 77152, 2761, 262144⟩ := by
  decide +kernel

theorem context_11_77152_1088959 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77152 ⟨1088959, by decide⟩ :=
  accepted_of_selected 11 77152 ⟨1088959, by decide⟩ ⟨11, 2, 0, 1088959, 77152, 2761, 262144⟩
    (by decide) selected_cut_40102

theorem selected_cut_40103 : selected 10 ⟨1089004, by decide⟩
    (prefixPartial 11 77153) = some ⟨11, 2, 0, 1089004, 77153, 2941, 262144⟩ := by
  decide +kernel

theorem context_11_77153_1089004 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77153 ⟨1089004, by decide⟩ :=
  accepted_of_selected 11 77153 ⟨1089004, by decide⟩ ⟨11, 2, 0, 1089004, 77153, 2941, 262144⟩
    (by decide) selected_cut_40103

theorem selected_cut_40104 : selected 9 ⟨1089037, by decide⟩
    (prefixPartial 12 308616) = some ⟨12, 2, 0, 1089037, 308616, 1721, 65536⟩ := by
  decide +kernel

theorem context_12_308616_1089037 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308616 ⟨1089037, by decide⟩ :=
  accepted_of_selected 12 308616 ⟨1089037, by decide⟩ ⟨12, 2, 0, 1089037, 308616, 1721, 65536⟩
    (by decide) selected_cut_40104

theorem selected_cut_40105 : selected 9 ⟨1089060, by decide⟩
    (prefixPartial 12 308617) = some ⟨12, 2, 0, 1089060, 308617, 1281, 65536⟩ := by
  decide +kernel

theorem context_12_308617_1089060 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308617 ⟨1089060, by decide⟩ :=
  accepted_of_selected 12 308617 ⟨1089060, by decide⟩ ⟨12, 2, 0, 1089060, 308617, 1281, 65536⟩
    (by decide) selected_cut_40105

theorem selected_cut_40106 : selected 9 ⟨984676, by decide⟩
    (prefixPartial 12 308618) = some ⟨12, 1, 0, 984676, 308618, 1, 65536⟩ := by
  decide +kernel

theorem context_12_308618_984676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308618 ⟨984676, by decide⟩ :=
  accepted_of_selected 12 308618 ⟨984676, by decide⟩ ⟨12, 1, 0, 984676, 308618, 1, 65536⟩
    (by decide) selected_cut_40106

theorem selected_cut_40107 : selected 9 ⟨1089083, by decide⟩
    (prefixPartial 12 308619) = some ⟨12, 2, 0, 1089083, 308619, 1325, 65536⟩ := by
  decide +kernel

theorem context_12_308619_1089083 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308619 ⟨1089083, by decide⟩ :=
  accepted_of_selected 12 308619 ⟨1089083, by decide⟩ ⟨12, 2, 0, 1089083, 308619, 1325, 65536⟩
    (by decide) selected_cut_40107

theorem unmarked_context_11_77154_1089084 : frontier 10 ⟨1089084, by decide⟩
    (prefixCache 11 77154) (prefixPartial 11 77154) = false := by
  decide +kernel

theorem node_context_11_77154_1089084 : EJMOriginalGlobalDAGData.nodes 10 ⟨1089084, by decide⟩ =
    .split (coordinate 11) (![⟨1089037, by decide⟩,⟨1089060, by decide⟩,⟨984676, by decide⟩,⟨1089083, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77154_1089084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77154 ⟨1089084, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77154
    ⟨1089084, by decide⟩ (by decide) (![⟨1089037, by decide⟩,⟨1089060, by decide⟩,⟨984676, by decide⟩,⟨1089083, by decide⟩]) unmarked_context_11_77154_1089084 node_context_11_77154_1089084
  intro a
  fin_cases a
  · exact context_12_308616_1089037
  · exact context_12_308617_1089060
  · exact context_12_308618_984676
  · exact context_12_308619_1089083

theorem selected_cut_40108 : selected 10 ⟨1089156, by decide⟩
    (prefixPartial 11 77155) = some ⟨11, 2, 0, 1089156, 77155, 3897, 262144⟩ := by
  decide +kernel

theorem context_11_77155_1089156 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77155 ⟨1089156, by decide⟩ :=
  accepted_of_selected 11 77155 ⟨1089156, by decide⟩ ⟨11, 2, 0, 1089156, 77155, 3897, 262144⟩
    (by decide) selected_cut_40108

theorem unmarked_context_10_19288_1089157 : frontier 11 ⟨1089157, by decide⟩
    (prefixCache 10 19288) (prefixPartial 10 19288) = false := by
  decide +kernel

theorem node_context_10_19288_1089157 : EJMOriginalGlobalDAGData.nodes 11 ⟨1089157, by decide⟩ =
    .split (coordinate 10) (![⟨1088959, by decide⟩,⟨1089004, by decide⟩,⟨1089084, by decide⟩,⟨1089156, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19288_1089157 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19288 ⟨1089157, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19288
    ⟨1089157, by decide⟩ (by decide) (![⟨1088959, by decide⟩,⟨1089004, by decide⟩,⟨1089084, by decide⟩,⟨1089156, by decide⟩]) unmarked_context_10_19288_1089157 node_context_10_19288_1089157
  intro a
  fin_cases a
  · exact context_11_77152_1088959
  · exact context_11_77153_1089004
  · exact context_11_77154_1089084
  · exact context_11_77155_1089156

theorem selected_cut_40109 : selected 10 ⟨1089213, by decide⟩
    (prefixPartial 11 77156) = some ⟨11, 2, 0, 1089213, 77156, 3413, 262144⟩ := by
  decide +kernel

theorem context_11_77156_1089213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77156 ⟨1089213, by decide⟩ :=
  accepted_of_selected 11 77156 ⟨1089213, by decide⟩ ⟨11, 2, 0, 1089213, 77156, 3413, 262144⟩
    (by decide) selected_cut_40109

theorem selected_cut_40110 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 77157) = some ⟨11, 1, 0, 892405, 77157, 1, 262144⟩ := by
  decide +kernel

theorem context_11_77157_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77157 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 77157 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 77157, 1, 262144⟩
    (by decide) selected_cut_40110

theorem selected_cut_40111 : selected 10 ⟨1089256, by decide⟩
    (prefixPartial 11 77158) = some ⟨11, 2, 0, 1089256, 77158, 2917, 262144⟩ := by
  decide +kernel

theorem context_11_77158_1089256 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77158 ⟨1089256, by decide⟩ :=
  accepted_of_selected 11 77158 ⟨1089256, by decide⟩ ⟨11, 2, 0, 1089256, 77158, 2917, 262144⟩
    (by decide) selected_cut_40111

theorem selected_cut_40112 : selected 10 ⟨1089300, by decide⟩
    (prefixPartial 11 77159) = some ⟨11, 2, 0, 1089300, 77159, 2809, 262144⟩ := by
  decide +kernel

theorem context_11_77159_1089300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77159 ⟨1089300, by decide⟩ :=
  accepted_of_selected 11 77159 ⟨1089300, by decide⟩ ⟨11, 2, 0, 1089300, 77159, 2809, 262144⟩
    (by decide) selected_cut_40112

theorem unmarked_context_10_19289_1089301 : frontier 11 ⟨1089301, by decide⟩
    (prefixCache 10 19289) (prefixPartial 10 19289) = false := by
  decide +kernel

theorem node_context_10_19289_1089301 : EJMOriginalGlobalDAGData.nodes 11 ⟨1089301, by decide⟩ =
    .split (coordinate 10) (![⟨1089213, by decide⟩,⟨892405, by decide⟩,⟨1089256, by decide⟩,⟨1089300, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19289_1089301 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19289 ⟨1089301, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19289
    ⟨1089301, by decide⟩ (by decide) (![⟨1089213, by decide⟩,⟨892405, by decide⟩,⟨1089256, by decide⟩,⟨1089300, by decide⟩]) unmarked_context_10_19289_1089301 node_context_10_19289_1089301
  intro a
  fin_cases a
  · exact context_11_77156_1089213
  · exact context_11_77157_892405
  · exact context_11_77158_1089256
  · exact context_11_77159_1089300

theorem selected_cut_40113 : selected 10 ⟨1089334, by decide⟩
    (prefixPartial 11 77160) = some ⟨11, 2, 0, 1089334, 77160, 2513, 262144⟩ := by
  decide +kernel

theorem context_11_77160_1089334 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77160 ⟨1089334, by decide⟩ :=
  accepted_of_selected 11 77160 ⟨1089334, by decide⟩ ⟨11, 2, 0, 1089334, 77160, 2513, 262144⟩
    (by decide) selected_cut_40113

theorem selected_cut_40114 : selected 10 ⟨1089356, by decide⟩
    (prefixPartial 11 77161) = some ⟨11, 2, 0, 1089356, 77161, 1625, 262144⟩ := by
  decide +kernel

theorem context_11_77161_1089356 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77161 ⟨1089356, by decide⟩ :=
  accepted_of_selected 11 77161 ⟨1089356, by decide⟩ ⟨11, 2, 0, 1089356, 77161, 1625, 262144⟩
    (by decide) selected_cut_40114

theorem selected_cut_40115 : selected 10 ⟨906566, by decide⟩
    (prefixPartial 11 77162) = some ⟨11, 1, 0, 906566, 77162, 1, 262144⟩ := by
  decide +kernel

theorem context_11_77162_906566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77162 ⟨906566, by decide⟩ :=
  accepted_of_selected 11 77162 ⟨906566, by decide⟩ ⟨11, 1, 0, 906566, 77162, 1, 262144⟩
    (by decide) selected_cut_40115

theorem selected_cut_40116 : selected 10 ⟨1089388, by decide⟩
    (prefixPartial 11 77163) = some ⟨11, 2, 0, 1089388, 77163, 2349, 262144⟩ := by
  decide +kernel

theorem context_11_77163_1089388 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77163 ⟨1089388, by decide⟩ :=
  accepted_of_selected 11 77163 ⟨1089388, by decide⟩ ⟨11, 2, 0, 1089388, 77163, 2349, 262144⟩
    (by decide) selected_cut_40116

theorem unmarked_context_10_19290_1089389 : frontier 11 ⟨1089389, by decide⟩
    (prefixCache 10 19290) (prefixPartial 10 19290) = false := by
  decide +kernel

theorem node_context_10_19290_1089389 : EJMOriginalGlobalDAGData.nodes 11 ⟨1089389, by decide⟩ =
    .split (coordinate 10) (![⟨1089334, by decide⟩,⟨1089356, by decide⟩,⟨906566, by decide⟩,⟨1089388, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19290_1089389 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19290 ⟨1089389, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19290
    ⟨1089389, by decide⟩ (by decide) (![⟨1089334, by decide⟩,⟨1089356, by decide⟩,⟨906566, by decide⟩,⟨1089388, by decide⟩]) unmarked_context_10_19290_1089389 node_context_10_19290_1089389
  intro a
  fin_cases a
  · exact context_11_77160_1089334
  · exact context_11_77161_1089356
  · exact context_11_77162_906566
  · exact context_11_77163_1089388

theorem selected_cut_40117 : selected 10 ⟨1089417, by decide⟩
    (prefixPartial 11 77164) = some ⟨11, 2, 0, 1089417, 77164, 2041, 262144⟩ := by
  decide +kernel

theorem context_11_77164_1089417 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77164 ⟨1089417, by decide⟩ :=
  accepted_of_selected 11 77164 ⟨1089417, by decide⟩ ⟨11, 2, 0, 1089417, 77164, 2041, 262144⟩
    (by decide) selected_cut_40117

theorem selected_cut_40118 : selected 10 ⟨1089442, by decide⟩
    (prefixPartial 11 77165) = some ⟨11, 2, 0, 1089442, 77165, 1385, 262144⟩ := by
  decide +kernel

theorem context_11_77165_1089442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77165 ⟨1089442, by decide⟩ :=
  accepted_of_selected 11 77165 ⟨1089442, by decide⟩ ⟨11, 2, 0, 1089442, 77165, 1385, 262144⟩
    (by decide) selected_cut_40118

theorem selected_cut_40119 : selected 10 ⟨1089468, by decide⟩
    (prefixPartial 11 77166) = some ⟨11, 2, 0, 1089468, 77166, 1793, 262144⟩ := by
  decide +kernel

theorem context_11_77166_1089468 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77166 ⟨1089468, by decide⟩ :=
  accepted_of_selected 11 77166 ⟨1089468, by decide⟩ ⟨11, 2, 0, 1089468, 77166, 1793, 262144⟩
    (by decide) selected_cut_40119

theorem selected_cut_40120 : selected 10 ⟨1089489, by decide⟩
    (prefixPartial 11 77167) = some ⟨11, 2, 0, 1089489, 77167, 1169, 262144⟩ := by
  decide +kernel

theorem context_11_77167_1089489 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77167 ⟨1089489, by decide⟩ :=
  accepted_of_selected 11 77167 ⟨1089489, by decide⟩ ⟨11, 2, 0, 1089489, 77167, 1169, 262144⟩
    (by decide) selected_cut_40120

theorem unmarked_context_10_19291_1089490 : frontier 11 ⟨1089490, by decide⟩
    (prefixCache 10 19291) (prefixPartial 10 19291) = false := by
  decide +kernel

theorem node_context_10_19291_1089490 : EJMOriginalGlobalDAGData.nodes 11 ⟨1089490, by decide⟩ =
    .split (coordinate 10) (![⟨1089417, by decide⟩,⟨1089442, by decide⟩,⟨1089468, by decide⟩,⟨1089489, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19291_1089490 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19291 ⟨1089490, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19291
    ⟨1089490, by decide⟩ (by decide) (![⟨1089417, by decide⟩,⟨1089442, by decide⟩,⟨1089468, by decide⟩,⟨1089489, by decide⟩]) unmarked_context_10_19291_1089490 node_context_10_19291_1089490
  intro a
  fin_cases a
  · exact context_11_77164_1089417
  · exact context_11_77165_1089442
  · exact context_11_77166_1089468
  · exact context_11_77167_1089489

theorem unmarked_context_9_4822_1089491 : frontier 12 ⟨1089491, by decide⟩
    (prefixCache 9 4822) (prefixPartial 9 4822) = false := by
  decide +kernel

theorem node_context_9_4822_1089491 : EJMOriginalGlobalDAGData.nodes 12 ⟨1089491, by decide⟩ =
    .split (coordinate 9) (![⟨1089157, by decide⟩,⟨1089301, by decide⟩,⟨1089389, by decide⟩,⟨1089490, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4822_1089491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4822 ⟨1089491, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4822
    ⟨1089491, by decide⟩ (by decide) (![⟨1089157, by decide⟩,⟨1089301, by decide⟩,⟨1089389, by decide⟩,⟨1089490, by decide⟩]) unmarked_context_9_4822_1089491 node_context_9_4822_1089491
  intro a
  fin_cases a
  · exact context_10_19288_1089157
  · exact context_10_19289_1089301
  · exact context_10_19290_1089389
  · exact context_10_19291_1089490

theorem selected_cut_40121 : selected 10 ⟨1089519, by decide⟩
    (prefixPartial 11 77168) = some ⟨11, 2, 0, 1089519, 77168, 1813, 262144⟩ := by
  decide +kernel

theorem context_11_77168_1089519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77168 ⟨1089519, by decide⟩ :=
  accepted_of_selected 11 77168 ⟨1089519, by decide⟩ ⟨11, 2, 0, 1089519, 77168, 1813, 262144⟩
    (by decide) selected_cut_40121

theorem selected_cut_40122 : selected 10 ⟨1089551, by decide⟩
    (prefixPartial 11 77169) = some ⟨11, 2, 0, 1089551, 77169, 1869, 262144⟩ := by
  decide +kernel

theorem context_11_77169_1089551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77169 ⟨1089551, by decide⟩ :=
  accepted_of_selected 11 77169 ⟨1089551, by decide⟩ ⟨11, 2, 0, 1089551, 77169, 1869, 262144⟩
    (by decide) selected_cut_40122

theorem selected_cut_40123 : selected 10 ⟨1089586, by decide⟩
    (prefixPartial 11 77170) = some ⟨11, 2, 0, 1089586, 77170, 2077, 262144⟩ := by
  decide +kernel

theorem context_11_77170_1089586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77170 ⟨1089586, by decide⟩ :=
  accepted_of_selected 11 77170 ⟨1089586, by decide⟩ ⟨11, 2, 0, 1089586, 77170, 2077, 262144⟩
    (by decide) selected_cut_40123

theorem selected_cut_40124 : selected 10 ⟨1089641, by decide⟩
    (prefixPartial 11 77171) = some ⟨11, 2, 0, 1089641, 77171, 1821, 262144⟩ := by
  decide +kernel

theorem context_11_77171_1089641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77171 ⟨1089641, by decide⟩ :=
  accepted_of_selected 11 77171 ⟨1089641, by decide⟩ ⟨11, 2, 0, 1089641, 77171, 1821, 262144⟩
    (by decide) selected_cut_40124

theorem unmarked_context_10_19292_1089642 : frontier 11 ⟨1089642, by decide⟩
    (prefixCache 10 19292) (prefixPartial 10 19292) = false := by
  decide +kernel

theorem node_context_10_19292_1089642 : EJMOriginalGlobalDAGData.nodes 11 ⟨1089642, by decide⟩ =
    .split (coordinate 10) (![⟨1089519, by decide⟩,⟨1089551, by decide⟩,⟨1089586, by decide⟩,⟨1089641, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19292_1089642 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19292 ⟨1089642, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19292
    ⟨1089642, by decide⟩ (by decide) (![⟨1089519, by decide⟩,⟨1089551, by decide⟩,⟨1089586, by decide⟩,⟨1089641, by decide⟩]) unmarked_context_10_19292_1089642 node_context_10_19292_1089642
  intro a
  fin_cases a
  · exact context_11_77168_1089519
  · exact context_11_77169_1089551
  · exact context_11_77170_1089586
  · exact context_11_77171_1089641

theorem selected_cut_40125 : selected 11 ⟨1089709, by decide⟩
    (prefixPartial 10 19293) = some ⟨10, 2, 0, 1089709, 19293, 3805, 1048576⟩ := by
  decide +kernel

theorem context_10_19293_1089709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19293 ⟨1089709, by decide⟩ :=
  accepted_of_selected 10 19293 ⟨1089709, by decide⟩ ⟨10, 2, 0, 1089709, 19293, 3805, 1048576⟩
    (by decide) selected_cut_40125

theorem selected_cut_40126 : selected 11 ⟨1089761, by decide⟩
    (prefixPartial 10 19294) = some ⟨10, 2, 0, 1089761, 19294, 2457, 1048576⟩ := by
  decide +kernel

theorem context_10_19294_1089761 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19294 ⟨1089761, by decide⟩ :=
  accepted_of_selected 10 19294 ⟨1089761, by decide⟩ ⟨10, 2, 0, 1089761, 19294, 2457, 1048576⟩
    (by decide) selected_cut_40126

theorem selected_cut_40127 : selected 11 ⟨1089788, by decide⟩
    (prefixPartial 10 19295) = some ⟨10, 2, 0, 1089788, 19295, 473, 1048576⟩ := by
  decide +kernel

theorem context_10_19295_1089788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19295 ⟨1089788, by decide⟩ :=
  accepted_of_selected 10 19295 ⟨1089788, by decide⟩ ⟨10, 2, 0, 1089788, 19295, 473, 1048576⟩
    (by decide) selected_cut_40127

theorem unmarked_context_9_4823_1089789 : frontier 12 ⟨1089789, by decide⟩
    (prefixCache 9 4823) (prefixPartial 9 4823) = false := by
  decide +kernel

theorem node_context_9_4823_1089789 : EJMOriginalGlobalDAGData.nodes 12 ⟨1089789, by decide⟩ =
    .split (coordinate 9) (![⟨1089642, by decide⟩,⟨1089709, by decide⟩,⟨1089761, by decide⟩,⟨1089788, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4823_1089789 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4823 ⟨1089789, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4823
    ⟨1089789, by decide⟩ (by decide) (![⟨1089642, by decide⟩,⟨1089709, by decide⟩,⟨1089761, by decide⟩,⟨1089788, by decide⟩]) unmarked_context_9_4823_1089789 node_context_9_4823_1089789
  intro a
  fin_cases a
  · exact context_10_19292_1089642
  · exact context_10_19293_1089709
  · exact context_10_19294_1089761
  · exact context_10_19295_1089788

theorem unmarked_context_8_1205_1089790 : frontier 13 ⟨1089790, by decide⟩
    (prefixCache 8 1205) (prefixPartial 8 1205) = false := by
  decide +kernel

theorem node_context_8_1205_1089790 : EJMOriginalGlobalDAGData.nodes 13 ⟨1089790, by decide⟩ =
    .split (coordinate 8) (![⟨1087634, by decide⟩,⟨1088917, by decide⟩,⟨1089491, by decide⟩,⟨1089789, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1205_1089790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1205 ⟨1089790, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1205
    ⟨1089790, by decide⟩ (by decide) (![⟨1087634, by decide⟩,⟨1088917, by decide⟩,⟨1089491, by decide⟩,⟨1089789, by decide⟩]) unmarked_context_8_1205_1089790 node_context_8_1205_1089790
  intro a
  fin_cases a
  · exact context_9_4820_1087634
  · exact context_9_4821_1088917
  · exact context_9_4822_1089491
  · exact context_9_4823_1089789

theorem selected_cut_40128 : selected 10 ⟨167448, by decide⟩
    (prefixPartial 11 77184) = some ⟨11, 1, 0, 167448, 77184, 1, 262144⟩ := by
  decide +kernel

theorem context_11_77184_167448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77184 ⟨167448, by decide⟩ :=
  accepted_of_selected 11 77184 ⟨167448, by decide⟩ ⟨11, 1, 0, 167448, 77184, 1, 262144⟩
    (by decide) selected_cut_40128

theorem selected_cut_40129 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 308740) = some ⟨12, 1, 0, 34034, 308740, 1, 65536⟩ := by
  decide +kernel

theorem context_12_308740_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308740 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 308740 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 308740, 1, 65536⟩
    (by decide) selected_cut_40129

theorem selected_cut_40130 : selected 8 ⟨1089828, by decide⟩
    (prefixPartial 13 1234964) = some ⟨13, 2, 0, 1089828, 1234964, 1833, 16384⟩ := by
  decide +kernel

theorem context_13_1234964_1089828 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1234964 ⟨1089828, by decide⟩ :=
  accepted_of_selected 13 1234964 ⟨1089828, by decide⟩ ⟨13, 2, 0, 1089828, 1234964, 1833, 16384⟩
    (by decide) selected_cut_40130

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
