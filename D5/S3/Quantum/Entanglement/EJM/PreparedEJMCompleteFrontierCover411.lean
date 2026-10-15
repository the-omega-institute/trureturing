/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover410
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_39458 : selected 9 ⟨26677, by decide⟩
    (prefixPartial 12 307220) = some ⟨12, 1, 0, 26677, 307220, 1, 65536⟩ := by
  decide +kernel

theorem context_12_307220_26677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307220 ⟨26677, by decide⟩ :=
  accepted_of_selected 12 307220 ⟨26677, by decide⟩ ⟨12, 1, 0, 26677, 307220, 1, 65536⟩
    (by decide) selected_cut_39458

theorem selected_cut_39459 : selected 9 ⟨124308, by decide⟩
    (prefixPartial 12 307221) = some ⟨12, 1, 0, 124308, 307221, 1, 65536⟩ := by
  decide +kernel

theorem context_12_307221_124308 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307221 ⟨124308, by decide⟩ :=
  accepted_of_selected 12 307221 ⟨124308, by decide⟩ ⟨12, 1, 0, 124308, 307221, 1, 65536⟩
    (by decide) selected_cut_39459

theorem selected_cut_39460 : selected 9 ⟨1070733, by decide⟩
    (prefixPartial 12 307222) = some ⟨12, 2, 0, 1070733, 307222, 2397, 65536⟩ := by
  decide +kernel

theorem context_12_307222_1070733 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307222 ⟨1070733, by decide⟩ :=
  accepted_of_selected 12 307222 ⟨1070733, by decide⟩ ⟨12, 2, 0, 1070733, 307222, 2397, 65536⟩
    (by decide) selected_cut_39460

theorem selected_cut_39461 : selected 9 ⟨1070769, by decide⟩
    (prefixPartial 12 307223) = some ⟨12, 2, 0, 1070769, 307223, 2477, 65536⟩ := by
  decide +kernel

theorem context_12_307223_1070769 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307223 ⟨1070769, by decide⟩ :=
  accepted_of_selected 12 307223 ⟨1070769, by decide⟩ ⟨12, 2, 0, 1070769, 307223, 2477, 65536⟩
    (by decide) selected_cut_39461

theorem unmarked_context_11_76805_1070770 : frontier 10 ⟨1070770, by decide⟩
    (prefixCache 11 76805) (prefixPartial 11 76805) = false := by
  decide +kernel

theorem node_context_11_76805_1070770 : EJMOriginalGlobalDAGData.nodes 10 ⟨1070770, by decide⟩ =
    .split (coordinate 11) (![⟨26677, by decide⟩,⟨124308, by decide⟩,⟨1070733, by decide⟩,⟨1070769, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76805_1070770 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76805 ⟨1070770, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76805
    ⟨1070770, by decide⟩ (by decide) (![⟨26677, by decide⟩,⟨124308, by decide⟩,⟨1070733, by decide⟩,⟨1070769, by decide⟩]) unmarked_context_11_76805_1070770 node_context_11_76805_1070770
  intro a
  fin_cases a
  · exact context_12_307220_26677
  · exact context_12_307221_124308
  · exact context_12_307222_1070733
  · exact context_12_307223_1070769

theorem selected_cut_39462 : selected 9 ⟨26677, by decide⟩
    (prefixPartial 12 307224) = some ⟨12, 1, 0, 26677, 307224, 1, 65536⟩ := by
  decide +kernel

theorem context_12_307224_26677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307224 ⟨26677, by decide⟩ :=
  accepted_of_selected 12 307224 ⟨26677, by decide⟩ ⟨12, 1, 0, 26677, 307224, 1, 65536⟩
    (by decide) selected_cut_39462

theorem selected_cut_39463 : selected 9 ⟨1070802, by decide⟩
    (prefixPartial 12 307225) = some ⟨12, 2, 0, 1070802, 307225, 2301, 65536⟩ := by
  decide +kernel

theorem context_12_307225_1070802 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307225 ⟨1070802, by decide⟩ :=
  accepted_of_selected 12 307225 ⟨1070802, by decide⟩ ⟨12, 2, 0, 1070802, 307225, 2301, 65536⟩
    (by decide) selected_cut_39463

theorem selected_cut_39464 : selected 9 ⟨3161, by decide⟩
    (prefixPartial 12 307226) = some ⟨12, 1, 0, 3161, 307226, 1, 65536⟩ := by
  decide +kernel

theorem context_12_307226_3161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307226 ⟨3161, by decide⟩ :=
  accepted_of_selected 12 307226 ⟨3161, by decide⟩ ⟨12, 1, 0, 3161, 307226, 1, 65536⟩
    (by decide) selected_cut_39464

theorem selected_cut_39465 : selected 9 ⟨1070836, by decide⟩
    (prefixPartial 12 307227) = some ⟨12, 2, 0, 1070836, 307227, 2449, 65536⟩ := by
  decide +kernel

theorem context_12_307227_1070836 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307227 ⟨1070836, by decide⟩ :=
  accepted_of_selected 12 307227 ⟨1070836, by decide⟩ ⟨12, 2, 0, 1070836, 307227, 2449, 65536⟩
    (by decide) selected_cut_39465

theorem unmarked_context_11_76806_1070837 : frontier 10 ⟨1070837, by decide⟩
    (prefixCache 11 76806) (prefixPartial 11 76806) = false := by
  decide +kernel

theorem node_context_11_76806_1070837 : EJMOriginalGlobalDAGData.nodes 10 ⟨1070837, by decide⟩ =
    .split (coordinate 11) (![⟨26677, by decide⟩,⟨1070802, by decide⟩,⟨3161, by decide⟩,⟨1070836, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76806_1070837 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76806 ⟨1070837, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76806
    ⟨1070837, by decide⟩ (by decide) (![⟨26677, by decide⟩,⟨1070802, by decide⟩,⟨3161, by decide⟩,⟨1070836, by decide⟩]) unmarked_context_11_76806_1070837 node_context_11_76806_1070837
  intro a
  fin_cases a
  · exact context_12_307224_26677
  · exact context_12_307225_1070802
  · exact context_12_307226_3161
  · exact context_12_307227_1070836

theorem selected_cut_39466 : selected 9 ⟨26677, by decide⟩
    (prefixPartial 12 307228) = some ⟨12, 1, 0, 26677, 307228, 1, 65536⟩ := by
  decide +kernel

theorem context_12_307228_26677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307228 ⟨26677, by decide⟩ :=
  accepted_of_selected 12 307228 ⟨26677, by decide⟩ ⟨12, 1, 0, 26677, 307228, 1, 65536⟩
    (by decide) selected_cut_39466

theorem selected_cut_39467 : selected 9 ⟨1070879, by decide⟩
    (prefixPartial 12 307229) = some ⟨12, 2, 0, 1070879, 307229, 2561, 65536⟩ := by
  decide +kernel

theorem context_12_307229_1070879 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307229 ⟨1070879, by decide⟩ :=
  accepted_of_selected 12 307229 ⟨1070879, by decide⟩ ⟨12, 2, 0, 1070879, 307229, 2561, 65536⟩
    (by decide) selected_cut_39467

theorem selected_cut_39468 : selected 9 ⟨1070911, by decide⟩
    (prefixPartial 12 307230) = some ⟨12, 2, 0, 1070911, 307230, 1601, 65536⟩ := by
  decide +kernel

theorem context_12_307230_1070911 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307230 ⟨1070911, by decide⟩ :=
  accepted_of_selected 12 307230 ⟨1070911, by decide⟩ ⟨12, 2, 0, 1070911, 307230, 1601, 65536⟩
    (by decide) selected_cut_39468

theorem selected_cut_39469 : selected 9 ⟨1070950, by decide⟩
    (prefixPartial 12 307231) = some ⟨12, 2, 0, 1070950, 307231, 2457, 65536⟩ := by
  decide +kernel

theorem context_12_307231_1070950 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307231 ⟨1070950, by decide⟩ :=
  accepted_of_selected 12 307231 ⟨1070950, by decide⟩ ⟨12, 2, 0, 1070950, 307231, 2457, 65536⟩
    (by decide) selected_cut_39469

theorem unmarked_context_11_76807_1070951 : frontier 10 ⟨1070951, by decide⟩
    (prefixCache 11 76807) (prefixPartial 11 76807) = false := by
  decide +kernel

theorem node_context_11_76807_1070951 : EJMOriginalGlobalDAGData.nodes 10 ⟨1070951, by decide⟩ =
    .split (coordinate 11) (![⟨26677, by decide⟩,⟨1070879, by decide⟩,⟨1070911, by decide⟩,⟨1070950, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76807_1070951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76807 ⟨1070951, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76807
    ⟨1070951, by decide⟩ (by decide) (![⟨26677, by decide⟩,⟨1070879, by decide⟩,⟨1070911, by decide⟩,⟨1070950, by decide⟩]) unmarked_context_11_76807_1070951 node_context_11_76807_1070951
  intro a
  fin_cases a
  · exact context_12_307228_26677
  · exact context_12_307229_1070879
  · exact context_12_307230_1070911
  · exact context_12_307231_1070950

theorem unmarked_context_10_19201_1070952 : frontier 11 ⟨1070952, by decide⟩
    (prefixCache 10 19201) (prefixPartial 10 19201) = false := by
  decide +kernel

theorem node_context_10_19201_1070952 : EJMOriginalGlobalDAGData.nodes 11 ⟨1070952, by decide⟩ =
    .split (coordinate 10) (![⟨1070700, by decide⟩,⟨1070770, by decide⟩,⟨1070837, by decide⟩,⟨1070951, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19201_1070952 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19201 ⟨1070952, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19201
    ⟨1070952, by decide⟩ (by decide) (![⟨1070700, by decide⟩,⟨1070770, by decide⟩,⟨1070837, by decide⟩,⟨1070951, by decide⟩]) unmarked_context_10_19201_1070952 node_context_10_19201_1070952
  intro a
  fin_cases a
  · exact context_11_76804_1070700
  · exact context_11_76805_1070770
  · exact context_11_76806_1070837
  · exact context_11_76807_1070951

theorem selected_cut_39470 : selected 10 ⟨1071006, by decide⟩
    (prefixPartial 11 76808) = some ⟨11, 2, 0, 1071006, 76808, 2953, 262144⟩ := by
  decide +kernel

theorem context_11_76808_1071006 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76808 ⟨1071006, by decide⟩ :=
  accepted_of_selected 11 76808 ⟨1071006, by decide⟩ ⟨11, 2, 0, 1071006, 76808, 2953, 262144⟩
    (by decide) selected_cut_39470

theorem selected_cut_39471 : selected 9 ⟨26677, by decide⟩
    (prefixPartial 12 307236) = some ⟨12, 1, 0, 26677, 307236, 1, 65536⟩ := by
  decide +kernel

theorem context_12_307236_26677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307236 ⟨26677, by decide⟩ :=
  accepted_of_selected 12 307236 ⟨26677, by decide⟩ ⟨12, 1, 0, 26677, 307236, 1, 65536⟩
    (by decide) selected_cut_39471

theorem selected_cut_39472 : selected 9 ⟨1071033, by decide⟩
    (prefixPartial 12 307237) = some ⟨12, 2, 0, 1071033, 307237, 2089, 65536⟩ := by
  decide +kernel

theorem context_12_307237_1071033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307237 ⟨1071033, by decide⟩ :=
  accepted_of_selected 12 307237 ⟨1071033, by decide⟩ ⟨12, 2, 0, 1071033, 307237, 2089, 65536⟩
    (by decide) selected_cut_39472

theorem selected_cut_39473 : selected 9 ⟨26677, by decide⟩
    (prefixPartial 12 307238) = some ⟨12, 1, 0, 26677, 307238, 1, 65536⟩ := by
  decide +kernel

theorem context_12_307238_26677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307238 ⟨26677, by decide⟩ :=
  accepted_of_selected 12 307238 ⟨26677, by decide⟩ ⟨12, 1, 0, 26677, 307238, 1, 65536⟩
    (by decide) selected_cut_39473

theorem selected_cut_39474 : selected 9 ⟨1071067, by decide⟩
    (prefixPartial 12 307239) = some ⟨12, 2, 0, 1071067, 307239, 2265, 65536⟩ := by
  decide +kernel

theorem context_12_307239_1071067 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307239 ⟨1071067, by decide⟩ :=
  accepted_of_selected 12 307239 ⟨1071067, by decide⟩ ⟨12, 2, 0, 1071067, 307239, 2265, 65536⟩
    (by decide) selected_cut_39474

theorem unmarked_context_11_76809_1071068 : frontier 10 ⟨1071068, by decide⟩
    (prefixCache 11 76809) (prefixPartial 11 76809) = false := by
  decide +kernel

theorem node_context_11_76809_1071068 : EJMOriginalGlobalDAGData.nodes 10 ⟨1071068, by decide⟩ =
    .split (coordinate 11) (![⟨26677, by decide⟩,⟨1071033, by decide⟩,⟨26677, by decide⟩,⟨1071067, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76809_1071068 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76809 ⟨1071068, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76809
    ⟨1071068, by decide⟩ (by decide) (![⟨26677, by decide⟩,⟨1071033, by decide⟩,⟨26677, by decide⟩,⟨1071067, by decide⟩]) unmarked_context_11_76809_1071068 node_context_11_76809_1071068
  intro a
  fin_cases a
  · exact context_12_307236_26677
  · exact context_12_307237_1071033
  · exact context_12_307238_26677
  · exact context_12_307239_1071067

theorem selected_cut_39475 : selected 10 ⟨1071102, by decide⟩
    (prefixPartial 11 76810) = some ⟨11, 2, 0, 1071102, 76810, 2241, 262144⟩ := by
  decide +kernel

theorem context_11_76810_1071102 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76810 ⟨1071102, by decide⟩ :=
  accepted_of_selected 11 76810 ⟨1071102, by decide⟩ ⟨11, 2, 0, 1071102, 76810, 2241, 262144⟩
    (by decide) selected_cut_39475

theorem selected_cut_39476 : selected 10 ⟨1071155, by decide⟩
    (prefixPartial 11 76811) = some ⟨11, 2, 0, 1071155, 76811, 3505, 262144⟩ := by
  decide +kernel

theorem context_11_76811_1071155 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76811 ⟨1071155, by decide⟩ :=
  accepted_of_selected 11 76811 ⟨1071155, by decide⟩ ⟨11, 2, 0, 1071155, 76811, 3505, 262144⟩
    (by decide) selected_cut_39476

theorem unmarked_context_10_19202_1071156 : frontier 11 ⟨1071156, by decide⟩
    (prefixCache 10 19202) (prefixPartial 10 19202) = false := by
  decide +kernel

theorem node_context_10_19202_1071156 : EJMOriginalGlobalDAGData.nodes 11 ⟨1071156, by decide⟩ =
    .split (coordinate 10) (![⟨1071006, by decide⟩,⟨1071068, by decide⟩,⟨1071102, by decide⟩,⟨1071155, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19202_1071156 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19202 ⟨1071156, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19202
    ⟨1071156, by decide⟩ (by decide) (![⟨1071006, by decide⟩,⟨1071068, by decide⟩,⟨1071102, by decide⟩,⟨1071155, by decide⟩]) unmarked_context_10_19202_1071156 node_context_10_19202_1071156
  intro a
  fin_cases a
  · exact context_11_76808_1071006
  · exact context_11_76809_1071068
  · exact context_11_76810_1071102
  · exact context_11_76811_1071155

theorem selected_cut_39477 : selected 11 ⟨1071221, by decide⟩
    (prefixPartial 10 19203) = some ⟨10, 2, 0, 1071221, 19203, 3429, 1048576⟩ := by
  decide +kernel

theorem context_10_19203_1071221 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19203 ⟨1071221, by decide⟩ :=
  accepted_of_selected 10 19203 ⟨1071221, by decide⟩ ⟨10, 2, 0, 1071221, 19203, 3429, 1048576⟩
    (by decide) selected_cut_39477

theorem unmarked_context_9_4800_1071222 : frontier 12 ⟨1071222, by decide⟩
    (prefixCache 9 4800) (prefixPartial 9 4800) = false := by
  decide +kernel

theorem node_context_9_4800_1071222 : EJMOriginalGlobalDAGData.nodes 12 ⟨1071222, by decide⟩ =
    .split (coordinate 9) (![⟨1070604, by decide⟩,⟨1070952, by decide⟩,⟨1071156, by decide⟩,⟨1071221, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4800_1071222 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4800 ⟨1071222, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4800
    ⟨1071222, by decide⟩ (by decide) (![⟨1070604, by decide⟩,⟨1070952, by decide⟩,⟨1071156, by decide⟩,⟨1071221, by decide⟩]) unmarked_context_9_4800_1071222 node_context_9_4800_1071222
  intro a
  fin_cases a
  · exact context_10_19200_1070604
  · exact context_10_19201_1070952
  · exact context_10_19202_1071156
  · exact context_10_19203_1071221

theorem selected_cut_39478 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 76816) = some ⟨11, 1, 0, 907917, 76816, 1, 262144⟩ := by
  decide +kernel

theorem context_11_76816_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76816 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 76816 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 76816, 1, 262144⟩
    (by decide) selected_cut_39478

theorem selected_cut_39479 : selected 9 ⟨1071255, by decide⟩
    (prefixPartial 12 307268) = some ⟨12, 2, 0, 1071255, 307268, 2181, 65536⟩ := by
  decide +kernel

theorem context_12_307268_1071255 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307268 ⟨1071255, by decide⟩ :=
  accepted_of_selected 12 307268 ⟨1071255, by decide⟩ ⟨12, 2, 0, 1071255, 307268, 2181, 65536⟩
    (by decide) selected_cut_39479

theorem selected_cut_39480 : selected 9 ⟨289098, by decide⟩
    (prefixPartial 12 307269) = some ⟨12, 1, 0, 289098, 307269, 1, 65536⟩ := by
  decide +kernel

theorem context_12_307269_289098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307269 ⟨289098, by decide⟩ :=
  accepted_of_selected 12 307269 ⟨289098, by decide⟩ ⟨12, 1, 0, 289098, 307269, 1, 65536⟩
    (by decide) selected_cut_39480

theorem selected_cut_39481 : selected 9 ⟨1071290, by decide⟩
    (prefixPartial 12 307270) = some ⟨12, 2, 0, 1071290, 307270, 2341, 65536⟩ := by
  decide +kernel

theorem context_12_307270_1071290 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307270 ⟨1071290, by decide⟩ :=
  accepted_of_selected 12 307270 ⟨1071290, by decide⟩ ⟨12, 2, 0, 1071290, 307270, 2341, 65536⟩
    (by decide) selected_cut_39481

theorem selected_cut_39482 : selected 9 ⟨1071332, by decide⟩
    (prefixPartial 12 307271) = some ⟨12, 2, 0, 1071332, 307271, 2337, 65536⟩ := by
  decide +kernel

theorem context_12_307271_1071332 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307271 ⟨1071332, by decide⟩ :=
  accepted_of_selected 12 307271 ⟨1071332, by decide⟩ ⟨12, 2, 0, 1071332, 307271, 2337, 65536⟩
    (by decide) selected_cut_39482

theorem unmarked_context_11_76817_1071333 : frontier 10 ⟨1071333, by decide⟩
    (prefixCache 11 76817) (prefixPartial 11 76817) = false := by
  decide +kernel

theorem node_context_11_76817_1071333 : EJMOriginalGlobalDAGData.nodes 10 ⟨1071333, by decide⟩ =
    .split (coordinate 11) (![⟨1071255, by decide⟩,⟨289098, by decide⟩,⟨1071290, by decide⟩,⟨1071332, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76817_1071333 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76817 ⟨1071333, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76817
    ⟨1071333, by decide⟩ (by decide) (![⟨1071255, by decide⟩,⟨289098, by decide⟩,⟨1071290, by decide⟩,⟨1071332, by decide⟩]) unmarked_context_11_76817_1071333 node_context_11_76817_1071333
  intro a
  fin_cases a
  · exact context_12_307268_1071255
  · exact context_12_307269_289098
  · exact context_12_307270_1071290
  · exact context_12_307271_1071332

theorem selected_cut_39483 : selected 9 ⟨1071365, by decide⟩
    (prefixPartial 12 307272) = some ⟨12, 2, 0, 1071365, 307272, 2013, 65536⟩ := by
  decide +kernel

theorem context_12_307272_1071365 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307272 ⟨1071365, by decide⟩ :=
  accepted_of_selected 12 307272 ⟨1071365, by decide⟩ ⟨12, 2, 0, 1071365, 307272, 2013, 65536⟩
    (by decide) selected_cut_39483

theorem selected_cut_39484 : selected 9 ⟨1071400, by decide⟩
    (prefixPartial 12 307273) = some ⟨12, 2, 0, 1071400, 307273, 1993, 65536⟩ := by
  decide +kernel

theorem context_12_307273_1071400 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307273 ⟨1071400, by decide⟩ :=
  accepted_of_selected 12 307273 ⟨1071400, by decide⟩ ⟨12, 2, 0, 1071400, 307273, 1993, 65536⟩
    (by decide) selected_cut_39484

theorem selected_cut_39485 : selected 9 ⟨1071438, by decide⟩
    (prefixPartial 12 307274) = some ⟨12, 2, 0, 1071438, 307274, 2149, 65536⟩ := by
  decide +kernel

theorem context_12_307274_1071438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307274 ⟨1071438, by decide⟩ :=
  accepted_of_selected 12 307274 ⟨1071438, by decide⟩ ⟨12, 2, 0, 1071438, 307274, 2149, 65536⟩
    (by decide) selected_cut_39485

theorem selected_cut_39486 : selected 9 ⟨1071471, by decide⟩
    (prefixPartial 12 307275) = some ⟨12, 2, 0, 1071471, 307275, 2185, 65536⟩ := by
  decide +kernel

theorem context_12_307275_1071471 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307275 ⟨1071471, by decide⟩ :=
  accepted_of_selected 12 307275 ⟨1071471, by decide⟩ ⟨12, 2, 0, 1071471, 307275, 2185, 65536⟩
    (by decide) selected_cut_39486

theorem unmarked_context_11_76818_1071472 : frontier 10 ⟨1071472, by decide⟩
    (prefixCache 11 76818) (prefixPartial 11 76818) = false := by
  decide +kernel

theorem node_context_11_76818_1071472 : EJMOriginalGlobalDAGData.nodes 10 ⟨1071472, by decide⟩ =
    .split (coordinate 11) (![⟨1071365, by decide⟩,⟨1071400, by decide⟩,⟨1071438, by decide⟩,⟨1071471, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76818_1071472 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76818 ⟨1071472, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76818
    ⟨1071472, by decide⟩ (by decide) (![⟨1071365, by decide⟩,⟨1071400, by decide⟩,⟨1071438, by decide⟩,⟨1071471, by decide⟩]) unmarked_context_11_76818_1071472 node_context_11_76818_1071472
  intro a
  fin_cases a
  · exact context_12_307272_1071365
  · exact context_12_307273_1071400
  · exact context_12_307274_1071438
  · exact context_12_307275_1071471

theorem selected_cut_39487 : selected 9 ⟨1071510, by decide⟩
    (prefixPartial 12 307276) = some ⟨12, 2, 0, 1071510, 307276, 2065, 65536⟩ := by
  decide +kernel

theorem context_12_307276_1071510 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307276 ⟨1071510, by decide⟩ :=
  accepted_of_selected 12 307276 ⟨1071510, by decide⟩ ⟨12, 2, 0, 1071510, 307276, 2065, 65536⟩
    (by decide) selected_cut_39487

theorem selected_cut_39488 : selected 9 ⟨1071548, by decide⟩
    (prefixPartial 12 307277) = some ⟨12, 2, 0, 1071548, 307277, 2029, 65536⟩ := by
  decide +kernel

theorem context_12_307277_1071548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307277 ⟨1071548, by decide⟩ :=
  accepted_of_selected 12 307277 ⟨1071548, by decide⟩ ⟨12, 2, 0, 1071548, 307277, 2029, 65536⟩
    (by decide) selected_cut_39488

theorem selected_cut_39489 : selected 9 ⟨1071591, by decide⟩
    (prefixPartial 12 307278) = some ⟨12, 2, 0, 1071591, 307278, 2249, 65536⟩ := by
  decide +kernel

theorem context_12_307278_1071591 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307278 ⟨1071591, by decide⟩ :=
  accepted_of_selected 12 307278 ⟨1071591, by decide⟩ ⟨12, 2, 0, 1071591, 307278, 2249, 65536⟩
    (by decide) selected_cut_39489

theorem selected_cut_39490 : selected 9 ⟨1071625, by decide⟩
    (prefixPartial 12 307279) = some ⟨12, 2, 0, 1071625, 307279, 2025, 65536⟩ := by
  decide +kernel

theorem context_12_307279_1071625 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307279 ⟨1071625, by decide⟩ :=
  accepted_of_selected 12 307279 ⟨1071625, by decide⟩ ⟨12, 2, 0, 1071625, 307279, 2025, 65536⟩
    (by decide) selected_cut_39490

theorem unmarked_context_11_76819_1071626 : frontier 10 ⟨1071626, by decide⟩
    (prefixCache 11 76819) (prefixPartial 11 76819) = false := by
  decide +kernel

theorem node_context_11_76819_1071626 : EJMOriginalGlobalDAGData.nodes 10 ⟨1071626, by decide⟩ =
    .split (coordinate 11) (![⟨1071510, by decide⟩,⟨1071548, by decide⟩,⟨1071591, by decide⟩,⟨1071625, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76819_1071626 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76819 ⟨1071626, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76819
    ⟨1071626, by decide⟩ (by decide) (![⟨1071510, by decide⟩,⟨1071548, by decide⟩,⟨1071591, by decide⟩,⟨1071625, by decide⟩]) unmarked_context_11_76819_1071626 node_context_11_76819_1071626
  intro a
  fin_cases a
  · exact context_12_307276_1071510
  · exact context_12_307277_1071548
  · exact context_12_307278_1071591
  · exact context_12_307279_1071625

theorem unmarked_context_10_19204_1071627 : frontier 11 ⟨1071627, by decide⟩
    (prefixCache 10 19204) (prefixPartial 10 19204) = false := by
  decide +kernel

theorem node_context_10_19204_1071627 : EJMOriginalGlobalDAGData.nodes 11 ⟨1071627, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨1071333, by decide⟩,⟨1071472, by decide⟩,⟨1071626, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19204_1071627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19204 ⟨1071627, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19204
    ⟨1071627, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨1071333, by decide⟩,⟨1071472, by decide⟩,⟨1071626, by decide⟩]) unmarked_context_10_19204_1071627 node_context_10_19204_1071627
  intro a
  fin_cases a
  · exact context_11_76816_907917
  · exact context_11_76817_1071333
  · exact context_11_76818_1071472
  · exact context_11_76819_1071626

theorem selected_cut_39491 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 19205) = some ⟨10, 1, 0, 893098, 19205, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_19205_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19205 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 19205 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 19205, 1, 1048576⟩
    (by decide) selected_cut_39491

theorem selected_cut_39492 : selected 9 ⟨985390, by decide⟩
    (prefixPartial 12 307296) = some ⟨12, 1, 0, 985390, 307296, 1, 65536⟩ := by
  decide +kernel

theorem context_12_307296_985390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307296 ⟨985390, by decide⟩ :=
  accepted_of_selected 12 307296 ⟨985390, by decide⟩ ⟨12, 1, 0, 985390, 307296, 1, 65536⟩
    (by decide) selected_cut_39492

theorem selected_cut_39493 : selected 9 ⟨1071655, by decide⟩
    (prefixPartial 12 307297) = some ⟨12, 2, 0, 1071655, 307297, 1457, 65536⟩ := by
  decide +kernel

theorem context_12_307297_1071655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307297 ⟨1071655, by decide⟩ :=
  accepted_of_selected 12 307297 ⟨1071655, by decide⟩ ⟨12, 2, 0, 1071655, 307297, 1457, 65536⟩
    (by decide) selected_cut_39493

theorem selected_cut_39494 : selected 9 ⟨1071679, by decide⟩
    (prefixPartial 12 307298) = some ⟨12, 2, 0, 1071679, 307298, 1385, 65536⟩ := by
  decide +kernel

theorem context_12_307298_1071679 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307298 ⟨1071679, by decide⟩ :=
  accepted_of_selected 12 307298 ⟨1071679, by decide⟩ ⟨12, 2, 0, 1071679, 307298, 1385, 65536⟩
    (by decide) selected_cut_39494

theorem selected_cut_39495 : selected 9 ⟨1071702, by decide⟩
    (prefixPartial 12 307299) = some ⟨12, 2, 0, 1071702, 307299, 1397, 65536⟩ := by
  decide +kernel

theorem context_12_307299_1071702 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307299 ⟨1071702, by decide⟩ :=
  accepted_of_selected 12 307299 ⟨1071702, by decide⟩ ⟨12, 2, 0, 1071702, 307299, 1397, 65536⟩
    (by decide) selected_cut_39495

theorem unmarked_context_11_76824_1071703 : frontier 10 ⟨1071703, by decide⟩
    (prefixCache 11 76824) (prefixPartial 11 76824) = false := by
  decide +kernel

theorem node_context_11_76824_1071703 : EJMOriginalGlobalDAGData.nodes 10 ⟨1071703, by decide⟩ =
    .split (coordinate 11) (![⟨985390, by decide⟩,⟨1071655, by decide⟩,⟨1071679, by decide⟩,⟨1071702, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76824_1071703 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76824 ⟨1071703, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76824
    ⟨1071703, by decide⟩ (by decide) (![⟨985390, by decide⟩,⟨1071655, by decide⟩,⟨1071679, by decide⟩,⟨1071702, by decide⟩]) unmarked_context_11_76824_1071703 node_context_11_76824_1071703
  intro a
  fin_cases a
  · exact context_12_307296_985390
  · exact context_12_307297_1071655
  · exact context_12_307298_1071679
  · exact context_12_307299_1071702

theorem selected_cut_39496 : selected 9 ⟨1071732, by decide⟩
    (prefixPartial 12 307300) = some ⟨12, 2, 0, 1071732, 307300, 1585, 65536⟩ := by
  decide +kernel

theorem context_12_307300_1071732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307300 ⟨1071732, by decide⟩ :=
  accepted_of_selected 12 307300 ⟨1071732, by decide⟩ ⟨12, 2, 0, 1071732, 307300, 1585, 65536⟩
    (by decide) selected_cut_39496

theorem selected_cut_39497 : selected 9 ⟨289098, by decide⟩
    (prefixPartial 12 307301) = some ⟨12, 1, 0, 289098, 307301, 1, 65536⟩ := by
  decide +kernel

theorem context_12_307301_289098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307301 ⟨289098, by decide⟩ :=
  accepted_of_selected 12 307301 ⟨289098, by decide⟩ ⟨12, 1, 0, 289098, 307301, 1, 65536⟩
    (by decide) selected_cut_39497

theorem selected_cut_39498 : selected 9 ⟨1071762, by decide⟩
    (prefixPartial 12 307302) = some ⟨12, 2, 0, 1071762, 307302, 1633, 65536⟩ := by
  decide +kernel

theorem context_12_307302_1071762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307302 ⟨1071762, by decide⟩ :=
  accepted_of_selected 12 307302 ⟨1071762, by decide⟩ ⟨12, 2, 0, 1071762, 307302, 1633, 65536⟩
    (by decide) selected_cut_39498

theorem selected_cut_39499 : selected 9 ⟨1071793, by decide⟩
    (prefixPartial 12 307303) = some ⟨12, 2, 0, 1071793, 307303, 1609, 65536⟩ := by
  decide +kernel

theorem context_12_307303_1071793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307303 ⟨1071793, by decide⟩ :=
  accepted_of_selected 12 307303 ⟨1071793, by decide⟩ ⟨12, 2, 0, 1071793, 307303, 1609, 65536⟩
    (by decide) selected_cut_39499

theorem unmarked_context_11_76825_1071794 : frontier 10 ⟨1071794, by decide⟩
    (prefixCache 11 76825) (prefixPartial 11 76825) = false := by
  decide +kernel

theorem node_context_11_76825_1071794 : EJMOriginalGlobalDAGData.nodes 10 ⟨1071794, by decide⟩ =
    .split (coordinate 11) (![⟨1071732, by decide⟩,⟨289098, by decide⟩,⟨1071762, by decide⟩,⟨1071793, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76825_1071794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76825 ⟨1071794, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76825
    ⟨1071794, by decide⟩ (by decide) (![⟨1071732, by decide⟩,⟨289098, by decide⟩,⟨1071762, by decide⟩,⟨1071793, by decide⟩]) unmarked_context_11_76825_1071794 node_context_11_76825_1071794
  intro a
  fin_cases a
  · exact context_12_307300_1071732
  · exact context_12_307301_289098
  · exact context_12_307302_1071762
  · exact context_12_307303_1071793

theorem selected_cut_39500 : selected 9 ⟨1071823, by decide⟩
    (prefixPartial 12 307304) = some ⟨12, 2, 0, 1071823, 307304, 1393, 65536⟩ := by
  decide +kernel

theorem context_12_307304_1071823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307304 ⟨1071823, by decide⟩ :=
  accepted_of_selected 12 307304 ⟨1071823, by decide⟩ ⟨12, 2, 0, 1071823, 307304, 1393, 65536⟩
    (by decide) selected_cut_39500

theorem selected_cut_39501 : selected 9 ⟨1071849, by decide⟩
    (prefixPartial 12 307305) = some ⟨12, 2, 0, 1071849, 307305, 1421, 65536⟩ := by
  decide +kernel

theorem context_12_307305_1071849 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307305 ⟨1071849, by decide⟩ :=
  accepted_of_selected 12 307305 ⟨1071849, by decide⟩ ⟨12, 2, 0, 1071849, 307305, 1421, 65536⟩
    (by decide) selected_cut_39501

theorem selected_cut_39502 : selected 9 ⟨242157, by decide⟩
    (prefixPartial 12 307306) = some ⟨12, 1, 0, 242157, 307306, 1, 65536⟩ := by
  decide +kernel

theorem context_12_307306_242157 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307306 ⟨242157, by decide⟩ :=
  accepted_of_selected 12 307306 ⟨242157, by decide⟩ ⟨12, 1, 0, 242157, 307306, 1, 65536⟩
    (by decide) selected_cut_39502

theorem selected_cut_39503 : selected 9 ⟨1071880, by decide⟩
    (prefixPartial 12 307307) = some ⟨12, 2, 0, 1071880, 307307, 1549, 65536⟩ := by
  decide +kernel

theorem context_12_307307_1071880 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307307 ⟨1071880, by decide⟩ :=
  accepted_of_selected 12 307307 ⟨1071880, by decide⟩ ⟨12, 2, 0, 1071880, 307307, 1549, 65536⟩
    (by decide) selected_cut_39503

theorem unmarked_context_11_76826_1071881 : frontier 10 ⟨1071881, by decide⟩
    (prefixCache 11 76826) (prefixPartial 11 76826) = false := by
  decide +kernel

theorem node_context_11_76826_1071881 : EJMOriginalGlobalDAGData.nodes 10 ⟨1071881, by decide⟩ =
    .split (coordinate 11) (![⟨1071823, by decide⟩,⟨1071849, by decide⟩,⟨242157, by decide⟩,⟨1071880, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76826_1071881 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76826 ⟨1071881, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76826
    ⟨1071881, by decide⟩ (by decide) (![⟨1071823, by decide⟩,⟨1071849, by decide⟩,⟨242157, by decide⟩,⟨1071880, by decide⟩]) unmarked_context_11_76826_1071881 node_context_11_76826_1071881
  intro a
  fin_cases a
  · exact context_12_307304_1071823
  · exact context_12_307305_1071849
  · exact context_12_307306_242157
  · exact context_12_307307_1071880

theorem selected_cut_39504 : selected 9 ⟨1071908, by decide⟩
    (prefixPartial 12 307308) = some ⟨12, 2, 0, 1071908, 307308, 1441, 65536⟩ := by
  decide +kernel

theorem context_12_307308_1071908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307308 ⟨1071908, by decide⟩ :=
  accepted_of_selected 12 307308 ⟨1071908, by decide⟩ ⟨12, 2, 0, 1071908, 307308, 1441, 65536⟩
    (by decide) selected_cut_39504

theorem selected_cut_39505 : selected 9 ⟨1071935, by decide⟩
    (prefixPartial 12 307309) = some ⟨12, 2, 0, 1071935, 307309, 1329, 65536⟩ := by
  decide +kernel

theorem context_12_307309_1071935 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307309 ⟨1071935, by decide⟩ :=
  accepted_of_selected 12 307309 ⟨1071935, by decide⟩ ⟨12, 2, 0, 1071935, 307309, 1329, 65536⟩
    (by decide) selected_cut_39505

theorem selected_cut_39506 : selected 9 ⟨1071968, by decide⟩
    (prefixPartial 12 307310) = some ⟨12, 2, 0, 1071968, 307310, 1457, 65536⟩ := by
  decide +kernel

theorem context_12_307310_1071968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307310 ⟨1071968, by decide⟩ :=
  accepted_of_selected 12 307310 ⟨1071968, by decide⟩ ⟨12, 2, 0, 1071968, 307310, 1457, 65536⟩
    (by decide) selected_cut_39506

theorem selected_cut_39507 : selected 9 ⟨1071991, by decide⟩
    (prefixPartial 12 307311) = some ⟨12, 2, 0, 1071991, 307311, 1321, 65536⟩ := by
  decide +kernel

theorem context_12_307311_1071991 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307311 ⟨1071991, by decide⟩ :=
  accepted_of_selected 12 307311 ⟨1071991, by decide⟩ ⟨12, 2, 0, 1071991, 307311, 1321, 65536⟩
    (by decide) selected_cut_39507

theorem unmarked_context_11_76827_1071992 : frontier 10 ⟨1071992, by decide⟩
    (prefixCache 11 76827) (prefixPartial 11 76827) = false := by
  decide +kernel

theorem node_context_11_76827_1071992 : EJMOriginalGlobalDAGData.nodes 10 ⟨1071992, by decide⟩ =
    .split (coordinate 11) (![⟨1071908, by decide⟩,⟨1071935, by decide⟩,⟨1071968, by decide⟩,⟨1071991, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76827_1071992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76827 ⟨1071992, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76827
    ⟨1071992, by decide⟩ (by decide) (![⟨1071908, by decide⟩,⟨1071935, by decide⟩,⟨1071968, by decide⟩,⟨1071991, by decide⟩]) unmarked_context_11_76827_1071992 node_context_11_76827_1071992
  intro a
  fin_cases a
  · exact context_12_307308_1071908
  · exact context_12_307309_1071935
  · exact context_12_307310_1071968
  · exact context_12_307311_1071991

theorem unmarked_context_10_19206_1071993 : frontier 11 ⟨1071993, by decide⟩
    (prefixCache 10 19206) (prefixPartial 10 19206) = false := by
  decide +kernel

theorem node_context_10_19206_1071993 : EJMOriginalGlobalDAGData.nodes 11 ⟨1071993, by decide⟩ =
    .split (coordinate 10) (![⟨1071703, by decide⟩,⟨1071794, by decide⟩,⟨1071881, by decide⟩,⟨1071992, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19206_1071993 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19206 ⟨1071993, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19206
    ⟨1071993, by decide⟩ (by decide) (![⟨1071703, by decide⟩,⟨1071794, by decide⟩,⟨1071881, by decide⟩,⟨1071992, by decide⟩]) unmarked_context_10_19206_1071993 node_context_10_19206_1071993
  intro a
  fin_cases a
  · exact context_11_76824_1071703
  · exact context_11_76825_1071794
  · exact context_11_76826_1071881
  · exact context_11_76827_1071992

theorem selected_cut_39508 : selected 10 ⟨1072054, by decide⟩
    (prefixPartial 11 76828) = some ⟨11, 2, 0, 1072054, 76828, 3049, 262144⟩ := by
  decide +kernel

theorem context_11_76828_1072054 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76828 ⟨1072054, by decide⟩ :=
  accepted_of_selected 11 76828 ⟨1072054, by decide⟩ ⟨11, 2, 0, 1072054, 76828, 3049, 262144⟩
    (by decide) selected_cut_39508

theorem selected_cut_39509 : selected 9 ⟨1072073, by decide⟩
    (prefixPartial 12 307316) = some ⟨12, 2, 0, 1072073, 307316, 1133, 65536⟩ := by
  decide +kernel

theorem context_12_307316_1072073 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307316 ⟨1072073, by decide⟩ :=
  accepted_of_selected 12 307316 ⟨1072073, by decide⟩ ⟨12, 2, 0, 1072073, 307316, 1133, 65536⟩
    (by decide) selected_cut_39509

theorem selected_cut_39510 : selected 9 ⟨1072091, by decide⟩
    (prefixPartial 12 307317) = some ⟨12, 2, 0, 1072091, 307317, 1025, 65536⟩ := by
  decide +kernel

theorem context_12_307317_1072091 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307317 ⟨1072091, by decide⟩ :=
  accepted_of_selected 12 307317 ⟨1072091, by decide⟩ ⟨12, 2, 0, 1072091, 307317, 1025, 65536⟩
    (by decide) selected_cut_39510

theorem selected_cut_39511 : selected 9 ⟨1072110, by decide⟩
    (prefixPartial 12 307318) = some ⟨12, 2, 0, 1072110, 307318, 1033, 65536⟩ := by
  decide +kernel

theorem context_12_307318_1072110 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307318 ⟨1072110, by decide⟩ :=
  accepted_of_selected 12 307318 ⟨1072110, by decide⟩ ⟨12, 2, 0, 1072110, 307318, 1033, 65536⟩
    (by decide) selected_cut_39511

theorem selected_cut_39512 : selected 9 ⟨1072128, by decide⟩
    (prefixPartial 12 307319) = some ⟨12, 2, 0, 1072128, 307319, 997, 65536⟩ := by
  decide +kernel

theorem context_12_307319_1072128 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307319 ⟨1072128, by decide⟩ :=
  accepted_of_selected 12 307319 ⟨1072128, by decide⟩ ⟨12, 2, 0, 1072128, 307319, 997, 65536⟩
    (by decide) selected_cut_39512

theorem unmarked_context_11_76829_1072129 : frontier 10 ⟨1072129, by decide⟩
    (prefixCache 11 76829) (prefixPartial 11 76829) = false := by
  decide +kernel

theorem node_context_11_76829_1072129 : EJMOriginalGlobalDAGData.nodes 10 ⟨1072129, by decide⟩ =
    .split (coordinate 11) (![⟨1072073, by decide⟩,⟨1072091, by decide⟩,⟨1072110, by decide⟩,⟨1072128, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76829_1072129 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76829 ⟨1072129, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76829
    ⟨1072129, by decide⟩ (by decide) (![⟨1072073, by decide⟩,⟨1072091, by decide⟩,⟨1072110, by decide⟩,⟨1072128, by decide⟩]) unmarked_context_11_76829_1072129 node_context_11_76829_1072129
  intro a
  fin_cases a
  · exact context_12_307316_1072073
  · exact context_12_307317_1072091
  · exact context_12_307318_1072110
  · exact context_12_307319_1072128

theorem selected_cut_39513 : selected 10 ⟨1072194, by decide⟩
    (prefixPartial 11 76830) = some ⟨11, 2, 0, 1072194, 76830, 3361, 262144⟩ := by
  decide +kernel

theorem context_11_76830_1072194 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76830 ⟨1072194, by decide⟩ :=
  accepted_of_selected 11 76830 ⟨1072194, by decide⟩ ⟨11, 2, 0, 1072194, 76830, 3361, 262144⟩
    (by decide) selected_cut_39513

theorem selected_cut_39514 : selected 10 ⟨1072234, by decide⟩
    (prefixPartial 11 76831) = some ⟨11, 2, 0, 1072234, 76831, 2153, 262144⟩ := by
  decide +kernel

theorem context_11_76831_1072234 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76831 ⟨1072234, by decide⟩ :=
  accepted_of_selected 11 76831 ⟨1072234, by decide⟩ ⟨11, 2, 0, 1072234, 76831, 2153, 262144⟩
    (by decide) selected_cut_39514

theorem unmarked_context_10_19207_1072235 : frontier 11 ⟨1072235, by decide⟩
    (prefixCache 10 19207) (prefixPartial 10 19207) = false := by
  decide +kernel

theorem node_context_10_19207_1072235 : EJMOriginalGlobalDAGData.nodes 11 ⟨1072235, by decide⟩ =
    .split (coordinate 10) (![⟨1072054, by decide⟩,⟨1072129, by decide⟩,⟨1072194, by decide⟩,⟨1072234, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19207_1072235 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19207 ⟨1072235, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19207
    ⟨1072235, by decide⟩ (by decide) (![⟨1072054, by decide⟩,⟨1072129, by decide⟩,⟨1072194, by decide⟩,⟨1072234, by decide⟩]) unmarked_context_10_19207_1072235 node_context_10_19207_1072235
  intro a
  fin_cases a
  · exact context_11_76828_1072054
  · exact context_11_76829_1072129
  · exact context_11_76830_1072194
  · exact context_11_76831_1072234

theorem unmarked_context_9_4801_1072236 : frontier 12 ⟨1072236, by decide⟩
    (prefixCache 9 4801) (prefixPartial 9 4801) = false := by
  decide +kernel

theorem node_context_9_4801_1072236 : EJMOriginalGlobalDAGData.nodes 12 ⟨1072236, by decide⟩ =
    .split (coordinate 9) (![⟨1071627, by decide⟩,⟨893098, by decide⟩,⟨1071993, by decide⟩,⟨1072235, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4801_1072236 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4801 ⟨1072236, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4801
    ⟨1072236, by decide⟩ (by decide) (![⟨1071627, by decide⟩,⟨893098, by decide⟩,⟨1071993, by decide⟩,⟨1072235, by decide⟩]) unmarked_context_9_4801_1072236 node_context_9_4801_1072236
  intro a
  fin_cases a
  · exact context_10_19204_1071627
  · exact context_10_19205_893098
  · exact context_10_19206_1071993
  · exact context_10_19207_1072235

theorem selected_cut_39515 : selected 12 ⟨33466, by decide⟩
    (prefixPartial 9 4802) = some ⟨9, 1, 0, 33466, 4802, 1, 4194304⟩ := by
  decide +kernel

theorem context_9_4802_33466 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4802 ⟨33466, by decide⟩ :=
  accepted_of_selected 9 4802 ⟨33466, by decide⟩ ⟨9, 1, 0, 33466, 4802, 1, 4194304⟩
    (by decide) selected_cut_39515

theorem selected_cut_39516 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 76848) = some ⟨11, 1, 0, 907917, 76848, 1, 262144⟩ := by
  decide +kernel

theorem context_11_76848_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76848 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 76848 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 76848, 1, 262144⟩
    (by decide) selected_cut_39516

theorem selected_cut_39517 : selected 10 ⟨1072270, by decide⟩
    (prefixPartial 11 76849) = some ⟨11, 2, 0, 1072270, 76849, 1825, 262144⟩ := by
  decide +kernel

theorem context_11_76849_1072270 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76849 ⟨1072270, by decide⟩ :=
  accepted_of_selected 11 76849 ⟨1072270, by decide⟩ ⟨11, 2, 0, 1072270, 76849, 1825, 262144⟩
    (by decide) selected_cut_39517

theorem selected_cut_39518 : selected 10 ⟨1072295, by decide⟩
    (prefixPartial 11 76850) = some ⟨11, 2, 0, 1072295, 76850, 1165, 262144⟩ := by
  decide +kernel

theorem context_11_76850_1072295 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76850 ⟨1072295, by decide⟩ :=
  accepted_of_selected 11 76850 ⟨1072295, by decide⟩ ⟨11, 2, 0, 1072295, 76850, 1165, 262144⟩
    (by decide) selected_cut_39518

theorem selected_cut_39519 : selected 10 ⟨1072327, by decide⟩
    (prefixPartial 11 76851) = some ⟨11, 2, 0, 1072327, 76851, 1117, 262144⟩ := by
  decide +kernel

theorem context_11_76851_1072327 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76851 ⟨1072327, by decide⟩ :=
  accepted_of_selected 11 76851 ⟨1072327, by decide⟩ ⟨11, 2, 0, 1072327, 76851, 1117, 262144⟩
    (by decide) selected_cut_39519

theorem unmarked_context_10_19212_1072328 : frontier 11 ⟨1072328, by decide⟩
    (prefixCache 10 19212) (prefixPartial 10 19212) = false := by
  decide +kernel

theorem node_context_10_19212_1072328 : EJMOriginalGlobalDAGData.nodes 11 ⟨1072328, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨1072270, by decide⟩,⟨1072295, by decide⟩,⟨1072327, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19212_1072328 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19212 ⟨1072328, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19212
    ⟨1072328, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨1072270, by decide⟩,⟨1072295, by decide⟩,⟨1072327, by decide⟩]) unmarked_context_10_19212_1072328 node_context_10_19212_1072328
  intro a
  fin_cases a
  · exact context_11_76848_907917
  · exact context_11_76849_1072270
  · exact context_11_76850_1072295
  · exact context_11_76851_1072327

theorem selected_cut_39520 : selected 11 ⟨1072399, by decide⟩
    (prefixPartial 10 19213) = some ⟨10, 2, 0, 1072399, 19213, 2281, 1048576⟩ := by
  decide +kernel

theorem context_10_19213_1072399 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19213 ⟨1072399, by decide⟩ :=
  accepted_of_selected 10 19213 ⟨1072399, by decide⟩ ⟨10, 2, 0, 1072399, 19213, 2281, 1048576⟩
    (by decide) selected_cut_39520

theorem selected_cut_39521 : selected 11 ⟨1072434, by decide⟩
    (prefixPartial 10 19214) = some ⟨10, 2, 0, 1072434, 19214, 577, 1048576⟩ := by
  decide +kernel

theorem context_10_19214_1072434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19214 ⟨1072434, by decide⟩ :=
  accepted_of_selected 10 19214 ⟨1072434, by decide⟩ ⟨10, 2, 0, 1072434, 19214, 577, 1048576⟩
    (by decide) selected_cut_39521

theorem selected_cut_39522 : selected 11 ⟨1072440, by decide⟩
    (prefixPartial 10 19215) = some ⟨10, 2, 0, 1072440, 19215, 57, 1048576⟩ := by
  decide +kernel

theorem context_10_19215_1072440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19215 ⟨1072440, by decide⟩ :=
  accepted_of_selected 10 19215 ⟨1072440, by decide⟩ ⟨10, 2, 0, 1072440, 19215, 57, 1048576⟩
    (by decide) selected_cut_39522

theorem unmarked_context_9_4803_1072441 : frontier 12 ⟨1072441, by decide⟩
    (prefixCache 9 4803) (prefixPartial 9 4803) = false := by
  decide +kernel

theorem node_context_9_4803_1072441 : EJMOriginalGlobalDAGData.nodes 12 ⟨1072441, by decide⟩ =
    .split (coordinate 9) (![⟨1072328, by decide⟩,⟨1072399, by decide⟩,⟨1072434, by decide⟩,⟨1072440, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4803_1072441 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4803 ⟨1072441, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4803
    ⟨1072441, by decide⟩ (by decide) (![⟨1072328, by decide⟩,⟨1072399, by decide⟩,⟨1072434, by decide⟩,⟨1072440, by decide⟩]) unmarked_context_9_4803_1072441 node_context_9_4803_1072441
  intro a
  fin_cases a
  · exact context_10_19212_1072328
  · exact context_10_19213_1072399
  · exact context_10_19214_1072434
  · exact context_10_19215_1072440

theorem unmarked_context_8_1200_1072442 : frontier 13 ⟨1072442, by decide⟩
    (prefixCache 8 1200) (prefixPartial 8 1200) = false := by
  decide +kernel

theorem node_context_8_1200_1072442 : EJMOriginalGlobalDAGData.nodes 13 ⟨1072442, by decide⟩ =
    .split (coordinate 8) (![⟨1071222, by decide⟩,⟨1072236, by decide⟩,⟨33466, by decide⟩,⟨1072441, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1200_1072442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1200 ⟨1072442, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1200
    ⟨1072442, by decide⟩ (by decide) (![⟨1071222, by decide⟩,⟨1072236, by decide⟩,⟨33466, by decide⟩,⟨1072441, by decide⟩]) unmarked_context_8_1200_1072442 node_context_8_1200_1072442
  intro a
  fin_cases a
  · exact context_9_4800_1071222
  · exact context_9_4801_1072236
  · exact context_9_4802_33466
  · exact context_9_4803_1072441

theorem selected_cut_39523 : selected 10 ⟨167448, by decide⟩
    (prefixPartial 11 76864) = some ⟨11, 1, 0, 167448, 76864, 1, 262144⟩ := by
  decide +kernel

theorem context_11_76864_167448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76864 ⟨167448, by decide⟩ :=
  accepted_of_selected 11 76864 ⟨167448, by decide⟩ ⟨11, 1, 0, 167448, 76864, 1, 262144⟩
    (by decide) selected_cut_39523

theorem selected_cut_39524 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 307460) = some ⟨12, 1, 0, 34034, 307460, 1, 65536⟩ := by
  decide +kernel

theorem context_12_307460_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307460 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 307460 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 307460, 1, 65536⟩
    (by decide) selected_cut_39524

theorem selected_cut_39525 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 307461) = some ⟨12, 1, 0, 891951, 307461, 1, 65536⟩ := by
  decide +kernel

theorem context_12_307461_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307461 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 307461 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 307461, 1, 65536⟩
    (by decide) selected_cut_39525

theorem selected_cut_39526 : selected 9 ⟨1072494, by decide⟩
    (prefixPartial 12 307462) = some ⟨12, 2, 0, 1072494, 307462, 3109, 65536⟩ := by
  decide +kernel

theorem context_12_307462_1072494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307462 ⟨1072494, by decide⟩ :=
  accepted_of_selected 12 307462 ⟨1072494, by decide⟩ ⟨12, 2, 0, 1072494, 307462, 3109, 65536⟩
    (by decide) selected_cut_39526

theorem selected_cut_39527 : selected 9 ⟨1072538, by decide⟩
    (prefixPartial 12 307463) = some ⟨12, 2, 0, 1072538, 307463, 3081, 65536⟩ := by
  decide +kernel

theorem context_12_307463_1072538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307463 ⟨1072538, by decide⟩ :=
  accepted_of_selected 12 307463 ⟨1072538, by decide⟩ ⟨12, 2, 0, 1072538, 307463, 3081, 65536⟩
    (by decide) selected_cut_39527

theorem unmarked_context_11_76865_1072539 : frontier 10 ⟨1072539, by decide⟩
    (prefixCache 11 76865) (prefixPartial 11 76865) = false := by
  decide +kernel

theorem node_context_11_76865_1072539 : EJMOriginalGlobalDAGData.nodes 10 ⟨1072539, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨891951, by decide⟩,⟨1072494, by decide⟩,⟨1072538, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76865_1072539 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76865 ⟨1072539, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76865
    ⟨1072539, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨891951, by decide⟩,⟨1072494, by decide⟩,⟨1072538, by decide⟩]) unmarked_context_11_76865_1072539 node_context_11_76865_1072539
  intro a
  fin_cases a
  · exact context_12_307460_34034
  · exact context_12_307461_891951
  · exact context_12_307462_1072494
  · exact context_12_307463_1072538

theorem selected_cut_39528 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 307464) = some ⟨12, 1, 0, 34034, 307464, 1, 65536⟩ := by
  decide +kernel

theorem context_12_307464_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307464 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 307464 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 307464, 1, 65536⟩
    (by decide) selected_cut_39528

theorem selected_cut_39529 : selected 9 ⟨1072588, by decide⟩
    (prefixPartial 12 307465) = some ⟨12, 2, 0, 1072588, 307465, 3097, 65536⟩ := by
  decide +kernel

theorem context_12_307465_1072588 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307465 ⟨1072588, by decide⟩ :=
  accepted_of_selected 12 307465 ⟨1072588, by decide⟩ ⟨12, 2, 0, 1072588, 307465, 3097, 65536⟩
    (by decide) selected_cut_39529

theorem selected_cut_39530 : selected 9 ⟨1072637, by decide⟩
    (prefixPartial 12 307466) = some ⟨12, 2, 0, 1072637, 307466, 3169, 65536⟩ := by
  decide +kernel

theorem context_12_307466_1072637 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307466 ⟨1072637, by decide⟩ :=
  accepted_of_selected 12 307466 ⟨1072637, by decide⟩ ⟨12, 2, 0, 1072637, 307466, 3169, 65536⟩
    (by decide) selected_cut_39530

theorem selected_cut_39531 : selected 9 ⟨1072685, by decide⟩
    (prefixPartial 12 307467) = some ⟨12, 2, 0, 1072685, 307467, 2997, 65536⟩ := by
  decide +kernel

theorem context_12_307467_1072685 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307467 ⟨1072685, by decide⟩ :=
  accepted_of_selected 12 307467 ⟨1072685, by decide⟩ ⟨12, 2, 0, 1072685, 307467, 2997, 65536⟩
    (by decide) selected_cut_39531

theorem unmarked_context_11_76866_1072686 : frontier 10 ⟨1072686, by decide⟩
    (prefixCache 11 76866) (prefixPartial 11 76866) = false := by
  decide +kernel

theorem node_context_11_76866_1072686 : EJMOriginalGlobalDAGData.nodes 10 ⟨1072686, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨1072588, by decide⟩,⟨1072637, by decide⟩,⟨1072685, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76866_1072686 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76866 ⟨1072686, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76866
    ⟨1072686, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨1072588, by decide⟩,⟨1072637, by decide⟩,⟨1072685, by decide⟩]) unmarked_context_11_76866_1072686 node_context_11_76866_1072686
  intro a
  fin_cases a
  · exact context_12_307464_34034
  · exact context_12_307465_1072588
  · exact context_12_307466_1072637
  · exact context_12_307467_1072685

theorem selected_cut_39532 : selected 8 ⟨1072726, by decide⟩
    (prefixPartial 13 1229872) = some ⟨13, 2, 0, 1072726, 1229872, 1497, 16384⟩ := by
  decide +kernel

theorem context_13_1229872_1072726 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1229872 ⟨1072726, by decide⟩ :=
  accepted_of_selected 13 1229872 ⟨1072726, by decide⟩ ⟨13, 2, 0, 1072726, 1229872, 1497, 16384⟩
    (by decide) selected_cut_39532

theorem selected_cut_39533 : selected 8 ⟨1072759, by decide⟩
    (prefixPartial 13 1229873) = some ⟨13, 2, 0, 1072759, 1229873, 1597, 16384⟩ := by
  decide +kernel

theorem context_13_1229873_1072759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1229873 ⟨1072759, by decide⟩ :=
  accepted_of_selected 13 1229873 ⟨1072759, by decide⟩ ⟨13, 2, 0, 1072759, 1229873, 1597, 16384⟩
    (by decide) selected_cut_39533

theorem selected_cut_39534 : selected 8 ⟨1072772, by decide⟩
    (prefixPartial 13 1229874) = some ⟨13, 2, 0, 1072772, 1229874, 865, 16384⟩ := by
  decide +kernel

theorem context_13_1229874_1072772 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1229874 ⟨1072772, by decide⟩ :=
  accepted_of_selected 13 1229874 ⟨1072772, by decide⟩ ⟨13, 2, 0, 1072772, 1229874, 865, 16384⟩
    (by decide) selected_cut_39534

theorem selected_cut_39535 : selected 8 ⟨1072789, by decide⟩
    (prefixPartial 13 1229875) = some ⟨13, 2, 0, 1072789, 1229875, 593, 16384⟩ := by
  decide +kernel

theorem context_13_1229875_1072789 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1229875 ⟨1072789, by decide⟩ :=
  accepted_of_selected 13 1229875 ⟨1072789, by decide⟩ ⟨13, 2, 0, 1072789, 1229875, 593, 16384⟩
    (by decide) selected_cut_39535

theorem unmarked_context_12_307468_1072790 : frontier 9 ⟨1072790, by decide⟩
    (prefixCache 12 307468) (prefixPartial 12 307468) = false := by
  decide +kernel

theorem node_context_12_307468_1072790 : EJMOriginalGlobalDAGData.nodes 9 ⟨1072790, by decide⟩ =
    .split (coordinate 12) (![⟨1072726, by decide⟩,⟨1072759, by decide⟩,⟨1072772, by decide⟩,⟨1072789, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_307468_1072790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307468 ⟨1072790, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 307468
    ⟨1072790, by decide⟩ (by decide) (![⟨1072726, by decide⟩,⟨1072759, by decide⟩,⟨1072772, by decide⟩,⟨1072789, by decide⟩]) unmarked_context_12_307468_1072790 node_context_12_307468_1072790
  intro a
  fin_cases a
  · exact context_13_1229872_1072726
  · exact context_13_1229873_1072759
  · exact context_13_1229874_1072772
  · exact context_13_1229875_1072789

theorem selected_cut_39536 : selected 9 ⟨1072847, by decide⟩
    (prefixPartial 12 307469) = some ⟨12, 2, 0, 1072847, 307469, 3569, 65536⟩ := by
  decide +kernel

theorem context_12_307469_1072847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307469 ⟨1072847, by decide⟩ :=
  accepted_of_selected 12 307469 ⟨1072847, by decide⟩ ⟨12, 2, 0, 1072847, 307469, 3569, 65536⟩
    (by decide) selected_cut_39536

theorem selected_cut_39537 : selected 9 ⟨1072907, by decide⟩
    (prefixPartial 12 307470) = some ⟨12, 2, 0, 1072907, 307470, 3521, 65536⟩ := by
  decide +kernel

theorem context_12_307470_1072907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307470 ⟨1072907, by decide⟩ :=
  accepted_of_selected 12 307470 ⟨1072907, by decide⟩ ⟨12, 2, 0, 1072907, 307470, 3521, 65536⟩
    (by decide) selected_cut_39537

theorem selected_cut_39538 : selected 9 ⟨1072952, by decide⟩
    (prefixPartial 12 307471) = some ⟨12, 2, 0, 1072952, 307471, 3241, 65536⟩ := by
  decide +kernel

theorem context_12_307471_1072952 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307471 ⟨1072952, by decide⟩ :=
  accepted_of_selected 12 307471 ⟨1072952, by decide⟩ ⟨12, 2, 0, 1072952, 307471, 3241, 65536⟩
    (by decide) selected_cut_39538

theorem unmarked_context_11_76867_1072953 : frontier 10 ⟨1072953, by decide⟩
    (prefixCache 11 76867) (prefixPartial 11 76867) = false := by
  decide +kernel

theorem node_context_11_76867_1072953 : EJMOriginalGlobalDAGData.nodes 10 ⟨1072953, by decide⟩ =
    .split (coordinate 11) (![⟨1072790, by decide⟩,⟨1072847, by decide⟩,⟨1072907, by decide⟩,⟨1072952, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76867_1072953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76867 ⟨1072953, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76867
    ⟨1072953, by decide⟩ (by decide) (![⟨1072790, by decide⟩,⟨1072847, by decide⟩,⟨1072907, by decide⟩,⟨1072952, by decide⟩]) unmarked_context_11_76867_1072953 node_context_11_76867_1072953
  intro a
  fin_cases a
  · exact context_12_307468_1072790
  · exact context_12_307469_1072847
  · exact context_12_307470_1072907
  · exact context_12_307471_1072952

theorem unmarked_context_10_19216_1072954 : frontier 11 ⟨1072954, by decide⟩
    (prefixCache 10 19216) (prefixPartial 10 19216) = false := by
  decide +kernel

theorem node_context_10_19216_1072954 : EJMOriginalGlobalDAGData.nodes 11 ⟨1072954, by decide⟩ =
    .split (coordinate 10) (![⟨167448, by decide⟩,⟨1072539, by decide⟩,⟨1072686, by decide⟩,⟨1072953, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19216_1072954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19216 ⟨1072954, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19216
    ⟨1072954, by decide⟩ (by decide) (![⟨167448, by decide⟩,⟨1072539, by decide⟩,⟨1072686, by decide⟩,⟨1072953, by decide⟩]) unmarked_context_10_19216_1072954 node_context_10_19216_1072954
  intro a
  fin_cases a
  · exact context_11_76864_167448
  · exact context_11_76865_1072539
  · exact context_11_76866_1072686
  · exact context_11_76867_1072953

theorem selected_cut_39539 : selected 9 ⟨1072955, by decide⟩
    (prefixPartial 12 307472) = some ⟨12, 1, 0, 1072955, 307472, 1, 65536⟩ := by
  decide +kernel

theorem context_12_307472_1072955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307472 ⟨1072955, by decide⟩ :=
  accepted_of_selected 12 307472 ⟨1072955, by decide⟩ ⟨12, 1, 0, 1072955, 307472, 1, 65536⟩
    (by decide) selected_cut_39539

theorem selected_cut_39540 : selected 9 ⟨1072990, by decide⟩
    (prefixPartial 12 307473) = some ⟨12, 2, 0, 1072990, 307473, 2533, 65536⟩ := by
  decide +kernel

theorem context_12_307473_1072990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307473 ⟨1072990, by decide⟩ :=
  accepted_of_selected 12 307473 ⟨1072990, by decide⟩ ⟨12, 2, 0, 1072990, 307473, 2533, 65536⟩
    (by decide) selected_cut_39540

theorem selected_cut_39541 : selected 9 ⟨1073019, by decide⟩
    (prefixPartial 12 307474) = some ⟨12, 2, 0, 1073019, 307474, 2437, 65536⟩ := by
  decide +kernel

theorem context_12_307474_1073019 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307474 ⟨1073019, by decide⟩ :=
  accepted_of_selected 12 307474 ⟨1073019, by decide⟩ ⟨12, 2, 0, 1073019, 307474, 2437, 65536⟩
    (by decide) selected_cut_39541

theorem selected_cut_39542 : selected 9 ⟨1073054, by decide⟩
    (prefixPartial 12 307475) = some ⟨12, 2, 0, 1073054, 307475, 2613, 65536⟩ := by
  decide +kernel

theorem context_12_307475_1073054 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307475 ⟨1073054, by decide⟩ :=
  accepted_of_selected 12 307475 ⟨1073054, by decide⟩ ⟨12, 2, 0, 1073054, 307475, 2613, 65536⟩
    (by decide) selected_cut_39542

theorem unmarked_context_11_76868_1073055 : frontier 10 ⟨1073055, by decide⟩
    (prefixCache 11 76868) (prefixPartial 11 76868) = false := by
  decide +kernel

theorem node_context_11_76868_1073055 : EJMOriginalGlobalDAGData.nodes 10 ⟨1073055, by decide⟩ =
    .split (coordinate 11) (![⟨1072955, by decide⟩,⟨1072990, by decide⟩,⟨1073019, by decide⟩,⟨1073054, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76868_1073055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76868 ⟨1073055, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76868
    ⟨1073055, by decide⟩ (by decide) (![⟨1072955, by decide⟩,⟨1072990, by decide⟩,⟨1073019, by decide⟩,⟨1073054, by decide⟩]) unmarked_context_11_76868_1073055 node_context_11_76868_1073055
  intro a
  fin_cases a
  · exact context_12_307472_1072955
  · exact context_12_307473_1072990
  · exact context_12_307474_1073019
  · exact context_12_307475_1073054

theorem selected_cut_39543 : selected 9 ⟨1073106, by decide⟩
    (prefixPartial 12 307476) = some ⟨12, 2, 0, 1073106, 307476, 3537, 65536⟩ := by
  decide +kernel

theorem context_12_307476_1073106 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307476 ⟨1073106, by decide⟩ :=
  accepted_of_selected 12 307476 ⟨1073106, by decide⟩ ⟨12, 2, 0, 1073106, 307476, 3537, 65536⟩
    (by decide) selected_cut_39543

theorem selected_cut_39544 : selected 9 ⟨124308, by decide⟩
    (prefixPartial 12 307477) = some ⟨12, 1, 0, 124308, 307477, 1, 65536⟩ := by
  decide +kernel

theorem context_12_307477_124308 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307477 ⟨124308, by decide⟩ :=
  accepted_of_selected 12 307477 ⟨124308, by decide⟩ ⟨12, 1, 0, 124308, 307477, 1, 65536⟩
    (by decide) selected_cut_39544

theorem selected_cut_39545 : selected 9 ⟨1073148, by decide⟩
    (prefixPartial 12 307478) = some ⟨12, 2, 0, 1073148, 307478, 2821, 65536⟩ := by
  decide +kernel

theorem context_12_307478_1073148 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307478 ⟨1073148, by decide⟩ :=
  accepted_of_selected 12 307478 ⟨1073148, by decide⟩ ⟨12, 2, 0, 1073148, 307478, 2821, 65536⟩
    (by decide) selected_cut_39545

theorem selected_cut_39546 : selected 9 ⟨1073185, by decide⟩
    (prefixPartial 12 307479) = some ⟨12, 2, 0, 1073185, 307479, 2905, 65536⟩ := by
  decide +kernel

theorem context_12_307479_1073185 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307479 ⟨1073185, by decide⟩ :=
  accepted_of_selected 12 307479 ⟨1073185, by decide⟩ ⟨12, 2, 0, 1073185, 307479, 2905, 65536⟩
    (by decide) selected_cut_39546

theorem unmarked_context_11_76869_1073186 : frontier 10 ⟨1073186, by decide⟩
    (prefixCache 11 76869) (prefixPartial 11 76869) = false := by
  decide +kernel

theorem node_context_11_76869_1073186 : EJMOriginalGlobalDAGData.nodes 10 ⟨1073186, by decide⟩ =
    .split (coordinate 11) (![⟨1073106, by decide⟩,⟨124308, by decide⟩,⟨1073148, by decide⟩,⟨1073185, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76869_1073186 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76869 ⟨1073186, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76869
    ⟨1073186, by decide⟩ (by decide) (![⟨1073106, by decide⟩,⟨124308, by decide⟩,⟨1073148, by decide⟩,⟨1073185, by decide⟩]) unmarked_context_11_76869_1073186 node_context_11_76869_1073186
  intro a
  fin_cases a
  · exact context_12_307476_1073106
  · exact context_12_307477_124308
  · exact context_12_307478_1073148
  · exact context_12_307479_1073185

theorem selected_cut_39547 : selected 9 ⟨1073239, by decide⟩
    (prefixPartial 12 307480) = some ⟨12, 2, 0, 1073239, 307480, 3253, 65536⟩ := by
  decide +kernel

theorem context_12_307480_1073239 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307480 ⟨1073239, by decide⟩ :=
  accepted_of_selected 12 307480 ⟨1073239, by decide⟩ ⟨12, 2, 0, 1073239, 307480, 3253, 65536⟩
    (by decide) selected_cut_39547

theorem selected_cut_39548 : selected 9 ⟨1073270, by decide⟩
    (prefixPartial 12 307481) = some ⟨12, 2, 0, 1073270, 307481, 2725, 65536⟩ := by
  decide +kernel

theorem context_12_307481_1073270 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307481 ⟨1073270, by decide⟩ :=
  accepted_of_selected 12 307481 ⟨1073270, by decide⟩ ⟨12, 2, 0, 1073270, 307481, 2725, 65536⟩
    (by decide) selected_cut_39548

theorem selected_cut_39549 : selected 9 ⟨1073308, by decide⟩
    (prefixPartial 12 307482) = some ⟨12, 2, 0, 1073308, 307482, 2673, 65536⟩ := by
  decide +kernel

theorem context_12_307482_1073308 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307482 ⟨1073308, by decide⟩ :=
  accepted_of_selected 12 307482 ⟨1073308, by decide⟩ ⟨12, 2, 0, 1073308, 307482, 2673, 65536⟩
    (by decide) selected_cut_39549

theorem selected_cut_39550 : selected 9 ⟨1073344, by decide⟩
    (prefixPartial 12 307483) = some ⟨12, 2, 0, 1073344, 307483, 2865, 65536⟩ := by
  decide +kernel

theorem context_12_307483_1073344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307483 ⟨1073344, by decide⟩ :=
  accepted_of_selected 12 307483 ⟨1073344, by decide⟩ ⟨12, 2, 0, 1073344, 307483, 2865, 65536⟩
    (by decide) selected_cut_39550

theorem unmarked_context_11_76870_1073345 : frontier 10 ⟨1073345, by decide⟩
    (prefixCache 11 76870) (prefixPartial 11 76870) = false := by
  decide +kernel

theorem node_context_11_76870_1073345 : EJMOriginalGlobalDAGData.nodes 10 ⟨1073345, by decide⟩ =
    .split (coordinate 11) (![⟨1073239, by decide⟩,⟨1073270, by decide⟩,⟨1073308, by decide⟩,⟨1073344, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76870_1073345 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76870 ⟨1073345, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76870
    ⟨1073345, by decide⟩ (by decide) (![⟨1073239, by decide⟩,⟨1073270, by decide⟩,⟨1073308, by decide⟩,⟨1073344, by decide⟩]) unmarked_context_11_76870_1073345 node_context_11_76870_1073345
  intro a
  fin_cases a
  · exact context_12_307480_1073239
  · exact context_12_307481_1073270
  · exact context_12_307482_1073308
  · exact context_12_307483_1073344

theorem selected_cut_39551 : selected 9 ⟨1073416, by decide⟩
    (prefixPartial 12 307484) = some ⟨12, 2, 0, 1073416, 307484, 3881, 65536⟩ := by
  decide +kernel

theorem context_12_307484_1073416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307484 ⟨1073416, by decide⟩ :=
  accepted_of_selected 12 307484 ⟨1073416, by decide⟩ ⟨12, 2, 0, 1073416, 307484, 3881, 65536⟩
    (by decide) selected_cut_39551

theorem selected_cut_39552 : selected 9 ⟨1073455, by decide⟩
    (prefixPartial 12 307485) = some ⟨12, 2, 0, 1073455, 307485, 3073, 65536⟩ := by
  decide +kernel

theorem context_12_307485_1073455 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307485 ⟨1073455, by decide⟩ :=
  accepted_of_selected 12 307485 ⟨1073455, by decide⟩ ⟨12, 2, 0, 1073455, 307485, 3073, 65536⟩
    (by decide) selected_cut_39552

theorem selected_cut_39553 : selected 9 ⟨1073503, by decide⟩
    (prefixPartial 12 307486) = some ⟨12, 2, 0, 1073503, 307486, 3157, 65536⟩ := by
  decide +kernel

theorem context_12_307486_1073503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307486 ⟨1073503, by decide⟩ :=
  accepted_of_selected 12 307486 ⟨1073503, by decide⟩ ⟨12, 2, 0, 1073503, 307486, 3157, 65536⟩
    (by decide) selected_cut_39553

theorem selected_cut_39554 : selected 9 ⟨1073546, by decide⟩
    (prefixPartial 12 307487) = some ⟨12, 2, 0, 1073546, 307487, 3057, 65536⟩ := by
  decide +kernel

theorem context_12_307487_1073546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307487 ⟨1073546, by decide⟩ :=
  accepted_of_selected 12 307487 ⟨1073546, by decide⟩ ⟨12, 2, 0, 1073546, 307487, 3057, 65536⟩
    (by decide) selected_cut_39554

theorem unmarked_context_11_76871_1073547 : frontier 10 ⟨1073547, by decide⟩
    (prefixCache 11 76871) (prefixPartial 11 76871) = false := by
  decide +kernel

theorem node_context_11_76871_1073547 : EJMOriginalGlobalDAGData.nodes 10 ⟨1073547, by decide⟩ =
    .split (coordinate 11) (![⟨1073416, by decide⟩,⟨1073455, by decide⟩,⟨1073503, by decide⟩,⟨1073546, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76871_1073547 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76871 ⟨1073547, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76871
    ⟨1073547, by decide⟩ (by decide) (![⟨1073416, by decide⟩,⟨1073455, by decide⟩,⟨1073503, by decide⟩,⟨1073546, by decide⟩]) unmarked_context_11_76871_1073547 node_context_11_76871_1073547
  intro a
  fin_cases a
  · exact context_12_307484_1073416
  · exact context_12_307485_1073455
  · exact context_12_307486_1073503
  · exact context_12_307487_1073546

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
