/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover442
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_42531 : selected 9 ⟨1162288, by decide⟩
    (prefixPartial 12 338211) = some ⟨12, 2, 0, 1162288, 338211, 2129, 65536⟩ := by
  decide +kernel

theorem context_12_338211_1162288 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338211 ⟨1162288, by decide⟩ :=
  accepted_of_selected 12 338211 ⟨1162288, by decide⟩ ⟨12, 2, 0, 1162288, 338211, 2129, 65536⟩
    (by decide) selected_cut_42531

theorem unmarked_context_11_84552_1162289 : frontier 10 ⟨1162289, by decide⟩
    (prefixCache 11 84552) (prefixPartial 11 84552) = false := by
  decide +kernel

theorem node_context_11_84552_1162289 : EJMOriginalGlobalDAGData.nodes 10 ⟨1162289, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1162226, by decide⟩,⟨1162257, by decide⟩,⟨1162288, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84552_1162289 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84552 ⟨1162289, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84552
    ⟨1162289, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1162226, by decide⟩,⟨1162257, by decide⟩,⟨1162288, by decide⟩]) unmarked_context_11_84552_1162289 node_context_11_84552_1162289
  intro a
  fin_cases a
  · exact context_12_338208_1108174
  · exact context_12_338209_1162226
  · exact context_12_338210_1162257
  · exact context_12_338211_1162288

theorem selected_cut_42532 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 338212) = some ⟨12, 1, 0, 1108174, 338212, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338212_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338212 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 338212 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 338212, 1, 65536⟩
    (by decide) selected_cut_42532

theorem selected_cut_42533 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 338213) = some ⟨12, 1, 0, 891951, 338213, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338213_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338213 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 338213 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 338213, 1, 65536⟩
    (by decide) selected_cut_42533

theorem selected_cut_42534 : selected 9 ⟨1162322, by decide⟩
    (prefixPartial 12 338214) = some ⟨12, 2, 0, 1162322, 338214, 2133, 65536⟩ := by
  decide +kernel

theorem context_12_338214_1162322 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338214 ⟨1162322, by decide⟩ :=
  accepted_of_selected 12 338214 ⟨1162322, by decide⟩ ⟨12, 2, 0, 1162322, 338214, 2133, 65536⟩
    (by decide) selected_cut_42534

theorem selected_cut_42535 : selected 9 ⟨1162359, by decide⟩
    (prefixPartial 12 338215) = some ⟨12, 2, 0, 1162359, 338215, 2185, 65536⟩ := by
  decide +kernel

theorem context_12_338215_1162359 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338215 ⟨1162359, by decide⟩ :=
  accepted_of_selected 12 338215 ⟨1162359, by decide⟩ ⟨12, 2, 0, 1162359, 338215, 2185, 65536⟩
    (by decide) selected_cut_42535

theorem unmarked_context_11_84553_1162360 : frontier 10 ⟨1162360, by decide⟩
    (prefixCache 11 84553) (prefixPartial 11 84553) = false := by
  decide +kernel

theorem node_context_11_84553_1162360 : EJMOriginalGlobalDAGData.nodes 10 ⟨1162360, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨891951, by decide⟩,⟨1162322, by decide⟩,⟨1162359, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84553_1162360 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84553 ⟨1162360, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84553
    ⟨1162360, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨891951, by decide⟩,⟨1162322, by decide⟩,⟨1162359, by decide⟩]) unmarked_context_11_84553_1162360 node_context_11_84553_1162360
  intro a
  fin_cases a
  · exact context_12_338212_1108174
  · exact context_12_338213_891951
  · exact context_12_338214_1162322
  · exact context_12_338215_1162359

theorem selected_cut_42536 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 84554) = some ⟨11, 1, 0, 900587, 84554, 1, 262144⟩ := by
  decide +kernel

theorem context_11_84554_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84554 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 84554 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 84554, 1, 262144⟩
    (by decide) selected_cut_42536

theorem selected_cut_42537 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 338220) = some ⟨12, 1, 0, 1108174, 338220, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338220_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338220 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 338220 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 338220, 1, 65536⟩
    (by decide) selected_cut_42537

theorem selected_cut_42538 : selected 9 ⟨1162387, by decide⟩
    (prefixPartial 12 338221) = some ⟨12, 2, 0, 1162387, 338221, 2021, 65536⟩ := by
  decide +kernel

theorem context_12_338221_1162387 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338221 ⟨1162387, by decide⟩ :=
  accepted_of_selected 12 338221 ⟨1162387, by decide⟩ ⟨12, 2, 0, 1162387, 338221, 2021, 65536⟩
    (by decide) selected_cut_42538

theorem selected_cut_42539 : selected 9 ⟨1162421, by decide⟩
    (prefixPartial 12 338222) = some ⟨12, 2, 0, 1162421, 338222, 1873, 65536⟩ := by
  decide +kernel

theorem context_12_338222_1162421 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338222 ⟨1162421, by decide⟩ :=
  accepted_of_selected 12 338222 ⟨1162421, by decide⟩ ⟨12, 2, 0, 1162421, 338222, 1873, 65536⟩
    (by decide) selected_cut_42539

theorem selected_cut_42540 : selected 9 ⟨1162451, by decide⟩
    (prefixPartial 12 338223) = some ⟨12, 2, 0, 1162451, 338223, 2057, 65536⟩ := by
  decide +kernel

theorem context_12_338223_1162451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338223 ⟨1162451, by decide⟩ :=
  accepted_of_selected 12 338223 ⟨1162451, by decide⟩ ⟨12, 2, 0, 1162451, 338223, 2057, 65536⟩
    (by decide) selected_cut_42540

theorem unmarked_context_11_84555_1162452 : frontier 10 ⟨1162452, by decide⟩
    (prefixCache 11 84555) (prefixPartial 11 84555) = false := by
  decide +kernel

theorem node_context_11_84555_1162452 : EJMOriginalGlobalDAGData.nodes 10 ⟨1162452, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1162387, by decide⟩,⟨1162421, by decide⟩,⟨1162451, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84555_1162452 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84555 ⟨1162452, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84555
    ⟨1162452, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1162387, by decide⟩,⟨1162421, by decide⟩,⟨1162451, by decide⟩]) unmarked_context_11_84555_1162452 node_context_11_84555_1162452
  intro a
  fin_cases a
  · exact context_12_338220_1108174
  · exact context_12_338221_1162387
  · exact context_12_338222_1162421
  · exact context_12_338223_1162451

theorem unmarked_context_10_21138_1162453 : frontier 11 ⟨1162453, by decide⟩
    (prefixCache 10 21138) (prefixPartial 10 21138) = false := by
  decide +kernel

theorem node_context_10_21138_1162453 : EJMOriginalGlobalDAGData.nodes 11 ⟨1162453, by decide⟩ =
    .split (coordinate 10) (![⟨1162289, by decide⟩,⟨1162360, by decide⟩,⟨900587, by decide⟩,⟨1162452, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21138_1162453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21138 ⟨1162453, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21138
    ⟨1162453, by decide⟩ (by decide) (![⟨1162289, by decide⟩,⟨1162360, by decide⟩,⟨900587, by decide⟩,⟨1162452, by decide⟩]) unmarked_context_10_21138_1162453 node_context_10_21138_1162453
  intro a
  fin_cases a
  · exact context_11_84552_1162289
  · exact context_11_84553_1162360
  · exact context_11_84554_900587
  · exact context_11_84555_1162452

theorem selected_cut_42541 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 338224) = some ⟨12, 1, 0, 1108174, 338224, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338224_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338224 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 338224 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 338224, 1, 65536⟩
    (by decide) selected_cut_42541

theorem selected_cut_42542 : selected 9 ⟨1162497, by decide⟩
    (prefixPartial 12 338225) = some ⟨12, 2, 0, 1162497, 338225, 2601, 65536⟩ := by
  decide +kernel

theorem context_12_338225_1162497 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338225 ⟨1162497, by decide⟩ :=
  accepted_of_selected 12 338225 ⟨1162497, by decide⟩ ⟨12, 2, 0, 1162497, 338225, 2601, 65536⟩
    (by decide) selected_cut_42542

theorem selected_cut_42543 : selected 9 ⟨1162537, by decide⟩
    (prefixPartial 12 338226) = some ⟨12, 2, 0, 1162537, 338226, 2421, 65536⟩ := by
  decide +kernel

theorem context_12_338226_1162537 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338226 ⟨1162537, by decide⟩ :=
  accepted_of_selected 12 338226 ⟨1162537, by decide⟩ ⟨12, 2, 0, 1162537, 338226, 2421, 65536⟩
    (by decide) selected_cut_42543

theorem selected_cut_42544 : selected 9 ⟨1162588, by decide⟩
    (prefixPartial 12 338227) = some ⟨12, 2, 0, 1162588, 338227, 2601, 65536⟩ := by
  decide +kernel

theorem context_12_338227_1162588 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338227 ⟨1162588, by decide⟩ :=
  accepted_of_selected 12 338227 ⟨1162588, by decide⟩ ⟨12, 2, 0, 1162588, 338227, 2601, 65536⟩
    (by decide) selected_cut_42544

theorem unmarked_context_11_84556_1162589 : frontier 10 ⟨1162589, by decide⟩
    (prefixCache 11 84556) (prefixPartial 11 84556) = false := by
  decide +kernel

theorem node_context_11_84556_1162589 : EJMOriginalGlobalDAGData.nodes 10 ⟨1162589, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1162497, by decide⟩,⟨1162537, by decide⟩,⟨1162588, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84556_1162589 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84556 ⟨1162589, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84556
    ⟨1162589, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1162497, by decide⟩,⟨1162537, by decide⟩,⟨1162588, by decide⟩]) unmarked_context_11_84556_1162589 node_context_11_84556_1162589
  intro a
  fin_cases a
  · exact context_12_338224_1108174
  · exact context_12_338225_1162497
  · exact context_12_338226_1162537
  · exact context_12_338227_1162588

theorem selected_cut_42545 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 338228) = some ⟨12, 1, 0, 1108174, 338228, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338228_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338228 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 338228 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 338228, 1, 65536⟩
    (by decide) selected_cut_42545

theorem selected_cut_42546 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 338229) = some ⟨12, 1, 0, 891951, 338229, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338229_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338229 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 338229 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 338229, 1, 65536⟩
    (by decide) selected_cut_42546

theorem selected_cut_42547 : selected 9 ⟨1162629, by decide⟩
    (prefixPartial 12 338230) = some ⟨12, 2, 0, 1162629, 338230, 2321, 65536⟩ := by
  decide +kernel

theorem context_12_338230_1162629 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338230 ⟨1162629, by decide⟩ :=
  accepted_of_selected 12 338230 ⟨1162629, by decide⟩ ⟨12, 2, 0, 1162629, 338230, 2321, 65536⟩
    (by decide) selected_cut_42547

theorem selected_cut_42548 : selected 9 ⟨1162669, by decide⟩
    (prefixPartial 12 338231) = some ⟨12, 2, 0, 1162669, 338231, 2417, 65536⟩ := by
  decide +kernel

theorem context_12_338231_1162669 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338231 ⟨1162669, by decide⟩ :=
  accepted_of_selected 12 338231 ⟨1162669, by decide⟩ ⟨12, 2, 0, 1162669, 338231, 2417, 65536⟩
    (by decide) selected_cut_42548

theorem unmarked_context_11_84557_1162670 : frontier 10 ⟨1162670, by decide⟩
    (prefixCache 11 84557) (prefixPartial 11 84557) = false := by
  decide +kernel

theorem node_context_11_84557_1162670 : EJMOriginalGlobalDAGData.nodes 10 ⟨1162670, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨891951, by decide⟩,⟨1162629, by decide⟩,⟨1162669, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84557_1162670 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84557 ⟨1162670, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84557
    ⟨1162670, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨891951, by decide⟩,⟨1162629, by decide⟩,⟨1162669, by decide⟩]) unmarked_context_11_84557_1162670 node_context_11_84557_1162670
  intro a
  fin_cases a
  · exact context_12_338228_1108174
  · exact context_12_338229_891951
  · exact context_12_338230_1162629
  · exact context_12_338231_1162669

theorem selected_cut_42549 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 338232) = some ⟨12, 1, 0, 1108174, 338232, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338232_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338232 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 338232 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 338232, 1, 65536⟩
    (by decide) selected_cut_42549

theorem selected_cut_42550 : selected 9 ⟨1162707, by decide⟩
    (prefixPartial 12 338233) = some ⟨12, 2, 0, 1162707, 338233, 2233, 65536⟩ := by
  decide +kernel

theorem context_12_338233_1162707 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338233 ⟨1162707, by decide⟩ :=
  accepted_of_selected 12 338233 ⟨1162707, by decide⟩ ⟨12, 2, 0, 1162707, 338233, 2233, 65536⟩
    (by decide) selected_cut_42550

theorem selected_cut_42551 : selected 9 ⟨1162733, by decide⟩
    (prefixPartial 12 338234) = some ⟨12, 2, 0, 1162733, 338234, 2001, 65536⟩ := by
  decide +kernel

theorem context_12_338234_1162733 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338234 ⟨1162733, by decide⟩ :=
  accepted_of_selected 12 338234 ⟨1162733, by decide⟩ ⟨12, 2, 0, 1162733, 338234, 2001, 65536⟩
    (by decide) selected_cut_42551

theorem selected_cut_42552 : selected 9 ⟨1162759, by decide⟩
    (prefixPartial 12 338235) = some ⟨12, 2, 0, 1162759, 338235, 2033, 65536⟩ := by
  decide +kernel

theorem context_12_338235_1162759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338235 ⟨1162759, by decide⟩ :=
  accepted_of_selected 12 338235 ⟨1162759, by decide⟩ ⟨12, 2, 0, 1162759, 338235, 2033, 65536⟩
    (by decide) selected_cut_42552

theorem unmarked_context_11_84558_1162760 : frontier 10 ⟨1162760, by decide⟩
    (prefixCache 11 84558) (prefixPartial 11 84558) = false := by
  decide +kernel

theorem node_context_11_84558_1162760 : EJMOriginalGlobalDAGData.nodes 10 ⟨1162760, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1162707, by decide⟩,⟨1162733, by decide⟩,⟨1162759, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84558_1162760 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84558 ⟨1162760, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84558
    ⟨1162760, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1162707, by decide⟩,⟨1162733, by decide⟩,⟨1162759, by decide⟩]) unmarked_context_11_84558_1162760 node_context_11_84558_1162760
  intro a
  fin_cases a
  · exact context_12_338232_1108174
  · exact context_12_338233_1162707
  · exact context_12_338234_1162733
  · exact context_12_338235_1162759

theorem selected_cut_42553 : selected 10 ⟨1162806, by decide⟩
    (prefixPartial 11 84559) = some ⟨11, 2, 0, 1162806, 84559, 3777, 262144⟩ := by
  decide +kernel

theorem context_11_84559_1162806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84559 ⟨1162806, by decide⟩ :=
  accepted_of_selected 11 84559 ⟨1162806, by decide⟩ ⟨11, 2, 0, 1162806, 84559, 3777, 262144⟩
    (by decide) selected_cut_42553

theorem unmarked_context_10_21139_1162807 : frontier 11 ⟨1162807, by decide⟩
    (prefixCache 10 21139) (prefixPartial 10 21139) = false := by
  decide +kernel

theorem node_context_10_21139_1162807 : EJMOriginalGlobalDAGData.nodes 11 ⟨1162807, by decide⟩ =
    .split (coordinate 10) (![⟨1162589, by decide⟩,⟨1162670, by decide⟩,⟨1162760, by decide⟩,⟨1162806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21139_1162807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21139 ⟨1162807, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21139
    ⟨1162807, by decide⟩ (by decide) (![⟨1162589, by decide⟩,⟨1162670, by decide⟩,⟨1162760, by decide⟩,⟨1162806, by decide⟩]) unmarked_context_10_21139_1162807 node_context_10_21139_1162807
  intro a
  fin_cases a
  · exact context_11_84556_1162589
  · exact context_11_84557_1162670
  · exact context_11_84558_1162760
  · exact context_11_84559_1162806

theorem unmarked_context_9_5284_1162808 : frontier 12 ⟨1162808, by decide⟩
    (prefixCache 9 5284) (prefixPartial 9 5284) = false := by
  decide +kernel

theorem node_context_9_5284_1162808 : EJMOriginalGlobalDAGData.nodes 12 ⟨1162808, by decide⟩ =
    .split (coordinate 9) (![⟨1161766, by decide⟩,⟨1162183, by decide⟩,⟨1162453, by decide⟩,⟨1162807, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5284_1162808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5284 ⟨1162808, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5284
    ⟨1162808, by decide⟩ (by decide) (![⟨1161766, by decide⟩,⟨1162183, by decide⟩,⟨1162453, by decide⟩,⟨1162807, by decide⟩]) unmarked_context_9_5284_1162808 node_context_9_5284_1162808
  intro a
  fin_cases a
  · exact context_10_21136_1161766
  · exact context_10_21137_1162183
  · exact context_10_21138_1162453
  · exact context_10_21139_1162807

theorem selected_cut_42554 : selected 10 ⟨1162866, by decide⟩
    (prefixPartial 11 84560) = some ⟨11, 2, 0, 1162866, 84560, 3729, 262144⟩ := by
  decide +kernel

theorem context_11_84560_1162866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84560 ⟨1162866, by decide⟩ :=
  accepted_of_selected 11 84560 ⟨1162866, by decide⟩ ⟨11, 2, 0, 1162866, 84560, 3729, 262144⟩
    (by decide) selected_cut_42554

theorem selected_cut_42555 : selected 9 ⟨1162887, by decide⟩
    (prefixPartial 12 338244) = some ⟨12, 2, 0, 1162887, 338244, 1521, 65536⟩ := by
  decide +kernel

theorem context_12_338244_1162887 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338244 ⟨1162887, by decide⟩ :=
  accepted_of_selected 12 338244 ⟨1162887, by decide⟩ ⟨12, 2, 0, 1162887, 338244, 1521, 65536⟩
    (by decide) selected_cut_42555

theorem selected_cut_42556 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 338245) = some ⟨12, 1, 0, 170504, 338245, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338245_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338245 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 338245 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 338245, 1, 65536⟩
    (by decide) selected_cut_42556

theorem selected_cut_42557 : selected 9 ⟨1162911, by decide⟩
    (prefixPartial 12 338246) = some ⟨12, 2, 0, 1162911, 338246, 1669, 65536⟩ := by
  decide +kernel

theorem context_12_338246_1162911 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338246 ⟨1162911, by decide⟩ :=
  accepted_of_selected 12 338246 ⟨1162911, by decide⟩ ⟨12, 2, 0, 1162911, 338246, 1669, 65536⟩
    (by decide) selected_cut_42557

theorem selected_cut_42558 : selected 9 ⟨1162942, by decide⟩
    (prefixPartial 12 338247) = some ⟨12, 2, 0, 1162942, 338247, 1701, 65536⟩ := by
  decide +kernel

theorem context_12_338247_1162942 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338247 ⟨1162942, by decide⟩ :=
  accepted_of_selected 12 338247 ⟨1162942, by decide⟩ ⟨12, 2, 0, 1162942, 338247, 1701, 65536⟩
    (by decide) selected_cut_42558

theorem unmarked_context_11_84561_1162943 : frontier 10 ⟨1162943, by decide⟩
    (prefixCache 11 84561) (prefixPartial 11 84561) = false := by
  decide +kernel

theorem node_context_11_84561_1162943 : EJMOriginalGlobalDAGData.nodes 10 ⟨1162943, by decide⟩ =
    .split (coordinate 11) (![⟨1162887, by decide⟩,⟨170504, by decide⟩,⟨1162911, by decide⟩,⟨1162942, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84561_1162943 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84561 ⟨1162943, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84561
    ⟨1162943, by decide⟩ (by decide) (![⟨1162887, by decide⟩,⟨170504, by decide⟩,⟨1162911, by decide⟩,⟨1162942, by decide⟩]) unmarked_context_11_84561_1162943 node_context_11_84561_1162943
  intro a
  fin_cases a
  · exact context_12_338244_1162887
  · exact context_12_338245_170504
  · exact context_12_338246_1162911
  · exact context_12_338247_1162942

theorem selected_cut_42559 : selected 9 ⟨1162961, by decide⟩
    (prefixPartial 12 338248) = some ⟨12, 2, 0, 1162961, 338248, 1325, 65536⟩ := by
  decide +kernel

theorem context_12_338248_1162961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338248 ⟨1162961, by decide⟩ :=
  accepted_of_selected 12 338248 ⟨1162961, by decide⟩ ⟨12, 2, 0, 1162961, 338248, 1325, 65536⟩
    (by decide) selected_cut_42559

theorem selected_cut_42560 : selected 9 ⟨126371, by decide⟩
    (prefixPartial 12 338249) = some ⟨12, 1, 0, 126371, 338249, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338249_126371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338249 ⟨126371, by decide⟩ :=
  accepted_of_selected 12 338249 ⟨126371, by decide⟩ ⟨12, 1, 0, 126371, 338249, 1, 65536⟩
    (by decide) selected_cut_42560

theorem selected_cut_42561 : selected 9 ⟨1162987, by decide⟩
    (prefixPartial 12 338250) = some ⟨12, 2, 0, 1162987, 338250, 1609, 65536⟩ := by
  decide +kernel

theorem context_12_338250_1162987 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338250 ⟨1162987, by decide⟩ :=
  accepted_of_selected 12 338250 ⟨1162987, by decide⟩ ⟨12, 2, 0, 1162987, 338250, 1609, 65536⟩
    (by decide) selected_cut_42561

theorem selected_cut_42562 : selected 9 ⟨1163015, by decide⟩
    (prefixPartial 12 338251) = some ⟨12, 2, 0, 1163015, 338251, 1589, 65536⟩ := by
  decide +kernel

theorem context_12_338251_1163015 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338251 ⟨1163015, by decide⟩ :=
  accepted_of_selected 12 338251 ⟨1163015, by decide⟩ ⟨12, 2, 0, 1163015, 338251, 1589, 65536⟩
    (by decide) selected_cut_42562

theorem unmarked_context_11_84562_1163016 : frontier 10 ⟨1163016, by decide⟩
    (prefixCache 11 84562) (prefixPartial 11 84562) = false := by
  decide +kernel

theorem node_context_11_84562_1163016 : EJMOriginalGlobalDAGData.nodes 10 ⟨1163016, by decide⟩ =
    .split (coordinate 11) (![⟨1162961, by decide⟩,⟨126371, by decide⟩,⟨1162987, by decide⟩,⟨1163015, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84562_1163016 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84562 ⟨1163016, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84562
    ⟨1163016, by decide⟩ (by decide) (![⟨1162961, by decide⟩,⟨126371, by decide⟩,⟨1162987, by decide⟩,⟨1163015, by decide⟩]) unmarked_context_11_84562_1163016 node_context_11_84562_1163016
  intro a
  fin_cases a
  · exact context_12_338248_1162961
  · exact context_12_338249_126371
  · exact context_12_338250_1162987
  · exact context_12_338251_1163015

theorem selected_cut_42563 : selected 9 ⟨1163038, by decide⟩
    (prefixPartial 12 338252) = some ⟨12, 2, 0, 1163038, 338252, 1353, 65536⟩ := by
  decide +kernel

theorem context_12_338252_1163038 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338252 ⟨1163038, by decide⟩ :=
  accepted_of_selected 12 338252 ⟨1163038, by decide⟩ ⟨12, 2, 0, 1163038, 338252, 1353, 65536⟩
    (by decide) selected_cut_42563

theorem selected_cut_42564 : selected 9 ⟨320864, by decide⟩
    (prefixPartial 12 338253) = some ⟨12, 1, 0, 320864, 338253, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338253_320864 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338253 ⟨320864, by decide⟩ :=
  accepted_of_selected 12 338253 ⟨320864, by decide⟩ ⟨12, 1, 0, 320864, 338253, 1, 65536⟩
    (by decide) selected_cut_42564

theorem selected_cut_42565 : selected 9 ⟨1163059, by decide⟩
    (prefixPartial 12 338254) = some ⟨12, 2, 0, 1163059, 338254, 1561, 65536⟩ := by
  decide +kernel

theorem context_12_338254_1163059 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338254 ⟨1163059, by decide⟩ :=
  accepted_of_selected 12 338254 ⟨1163059, by decide⟩ ⟨12, 2, 0, 1163059, 338254, 1561, 65536⟩
    (by decide) selected_cut_42565

theorem selected_cut_42566 : selected 9 ⟨1163079, by decide⟩
    (prefixPartial 12 338255) = some ⟨12, 2, 0, 1163079, 338255, 1621, 65536⟩ := by
  decide +kernel

theorem context_12_338255_1163079 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338255 ⟨1163079, by decide⟩ :=
  accepted_of_selected 12 338255 ⟨1163079, by decide⟩ ⟨12, 2, 0, 1163079, 338255, 1621, 65536⟩
    (by decide) selected_cut_42566

theorem unmarked_context_11_84563_1163080 : frontier 10 ⟨1163080, by decide⟩
    (prefixCache 11 84563) (prefixPartial 11 84563) = false := by
  decide +kernel

theorem node_context_11_84563_1163080 : EJMOriginalGlobalDAGData.nodes 10 ⟨1163080, by decide⟩ =
    .split (coordinate 11) (![⟨1163038, by decide⟩,⟨320864, by decide⟩,⟨1163059, by decide⟩,⟨1163079, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84563_1163080 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84563 ⟨1163080, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84563
    ⟨1163080, by decide⟩ (by decide) (![⟨1163038, by decide⟩,⟨320864, by decide⟩,⟨1163059, by decide⟩,⟨1163079, by decide⟩]) unmarked_context_11_84563_1163080 node_context_11_84563_1163080
  intro a
  fin_cases a
  · exact context_12_338252_1163038
  · exact context_12_338253_320864
  · exact context_12_338254_1163059
  · exact context_12_338255_1163079

theorem unmarked_context_10_21140_1163081 : frontier 11 ⟨1163081, by decide⟩
    (prefixCache 10 21140) (prefixPartial 10 21140) = false := by
  decide +kernel

theorem node_context_10_21140_1163081 : EJMOriginalGlobalDAGData.nodes 11 ⟨1163081, by decide⟩ =
    .split (coordinate 10) (![⟨1162866, by decide⟩,⟨1162943, by decide⟩,⟨1163016, by decide⟩,⟨1163080, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21140_1163081 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21140 ⟨1163081, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21140
    ⟨1163081, by decide⟩ (by decide) (![⟨1162866, by decide⟩,⟨1162943, by decide⟩,⟨1163016, by decide⟩,⟨1163080, by decide⟩]) unmarked_context_10_21140_1163081 node_context_10_21140_1163081
  intro a
  fin_cases a
  · exact context_11_84560_1162866
  · exact context_11_84561_1162943
  · exact context_11_84562_1163016
  · exact context_11_84563_1163080

theorem selected_cut_42567 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 21141) = some ⟨10, 1, 0, 893098, 21141, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_21141_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21141 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 21141 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 21141, 1, 1048576⟩
    (by decide) selected_cut_42567

theorem selected_cut_42568 : selected 10 ⟨1163143, by decide⟩
    (prefixPartial 11 84568) = some ⟨11, 2, 0, 1163143, 84568, 3685, 262144⟩ := by
  decide +kernel

theorem context_11_84568_1163143 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84568 ⟨1163143, by decide⟩ :=
  accepted_of_selected 11 84568 ⟨1163143, by decide⟩ ⟨11, 2, 0, 1163143, 84568, 3685, 262144⟩
    (by decide) selected_cut_42568

theorem selected_cut_42569 : selected 10 ⟨1163197, by decide⟩
    (prefixPartial 11 84569) = some ⟨11, 2, 0, 1163197, 84569, 4049, 262144⟩ := by
  decide +kernel

theorem context_11_84569_1163197 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84569 ⟨1163197, by decide⟩ :=
  accepted_of_selected 11 84569 ⟨1163197, by decide⟩ ⟨11, 2, 0, 1163197, 84569, 4049, 262144⟩
    (by decide) selected_cut_42569

theorem selected_cut_42570 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 84570) = some ⟨11, 1, 0, 900587, 84570, 1, 262144⟩ := by
  decide +kernel

theorem context_11_84570_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84570 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 84570 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 84570, 1, 262144⟩
    (by decide) selected_cut_42570

theorem selected_cut_42571 : selected 9 ⟨1163214, by decide⟩
    (prefixPartial 12 338284) = some ⟨12, 2, 0, 1163214, 338284, 1193, 65536⟩ := by
  decide +kernel

theorem context_12_338284_1163214 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338284 ⟨1163214, by decide⟩ :=
  accepted_of_selected 12 338284 ⟨1163214, by decide⟩ ⟨12, 2, 0, 1163214, 338284, 1193, 65536⟩
    (by decide) selected_cut_42571

theorem selected_cut_42572 : selected 9 ⟨1163229, by decide⟩
    (prefixPartial 12 338285) = some ⟨12, 2, 0, 1163229, 338285, 1229, 65536⟩ := by
  decide +kernel

theorem context_12_338285_1163229 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338285 ⟨1163229, by decide⟩ :=
  accepted_of_selected 12 338285 ⟨1163229, by decide⟩ ⟨12, 2, 0, 1163229, 338285, 1229, 65536⟩
    (by decide) selected_cut_42572

theorem selected_cut_42573 : selected 9 ⟨1163244, by decide⟩
    (prefixPartial 12 338286) = some ⟨12, 2, 0, 1163244, 338286, 1281, 65536⟩ := by
  decide +kernel

theorem context_12_338286_1163244 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338286 ⟨1163244, by decide⟩ :=
  accepted_of_selected 12 338286 ⟨1163244, by decide⟩ ⟨12, 2, 0, 1163244, 338286, 1281, 65536⟩
    (by decide) selected_cut_42573

theorem selected_cut_42574 : selected 9 ⟨1163259, by decide⟩
    (prefixPartial 12 338287) = some ⟨12, 2, 0, 1163259, 338287, 1321, 65536⟩ := by
  decide +kernel

theorem context_12_338287_1163259 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338287 ⟨1163259, by decide⟩ :=
  accepted_of_selected 12 338287 ⟨1163259, by decide⟩ ⟨12, 2, 0, 1163259, 338287, 1321, 65536⟩
    (by decide) selected_cut_42574

theorem unmarked_context_11_84571_1163260 : frontier 10 ⟨1163260, by decide⟩
    (prefixCache 11 84571) (prefixPartial 11 84571) = false := by
  decide +kernel

theorem node_context_11_84571_1163260 : EJMOriginalGlobalDAGData.nodes 10 ⟨1163260, by decide⟩ =
    .split (coordinate 11) (![⟨1163214, by decide⟩,⟨1163229, by decide⟩,⟨1163244, by decide⟩,⟨1163259, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84571_1163260 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84571 ⟨1163260, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84571
    ⟨1163260, by decide⟩ (by decide) (![⟨1163214, by decide⟩,⟨1163229, by decide⟩,⟨1163244, by decide⟩,⟨1163259, by decide⟩]) unmarked_context_11_84571_1163260 node_context_11_84571_1163260
  intro a
  fin_cases a
  · exact context_12_338284_1163214
  · exact context_12_338285_1163229
  · exact context_12_338286_1163244
  · exact context_12_338287_1163259

theorem unmarked_context_10_21142_1163261 : frontier 11 ⟨1163261, by decide⟩
    (prefixCache 10 21142) (prefixPartial 10 21142) = false := by
  decide +kernel

theorem node_context_10_21142_1163261 : EJMOriginalGlobalDAGData.nodes 11 ⟨1163261, by decide⟩ =
    .split (coordinate 10) (![⟨1163143, by decide⟩,⟨1163197, by decide⟩,⟨900587, by decide⟩,⟨1163260, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21142_1163261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21142 ⟨1163261, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21142
    ⟨1163261, by decide⟩ (by decide) (![⟨1163143, by decide⟩,⟨1163197, by decide⟩,⟨900587, by decide⟩,⟨1163260, by decide⟩]) unmarked_context_10_21142_1163261 node_context_10_21142_1163261
  intro a
  fin_cases a
  · exact context_11_84568_1163143
  · exact context_11_84569_1163197
  · exact context_11_84570_900587
  · exact context_11_84571_1163260

theorem selected_cut_42575 : selected 9 ⟨1163289, by decide⟩
    (prefixPartial 12 338288) = some ⟨12, 2, 0, 1163289, 338288, 1645, 65536⟩ := by
  decide +kernel

theorem context_12_338288_1163289 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338288 ⟨1163289, by decide⟩ :=
  accepted_of_selected 12 338288 ⟨1163289, by decide⟩ ⟨12, 2, 0, 1163289, 338288, 1645, 65536⟩
    (by decide) selected_cut_42575

theorem selected_cut_42576 : selected 9 ⟨355230, by decide⟩
    (prefixPartial 12 338289) = some ⟨12, 1, 0, 355230, 338289, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338289_355230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338289 ⟨355230, by decide⟩ :=
  accepted_of_selected 12 338289 ⟨355230, by decide⟩ ⟨12, 1, 0, 355230, 338289, 1, 65536⟩
    (by decide) selected_cut_42576

theorem selected_cut_42577 : selected 9 ⟨1163317, by decide⟩
    (prefixPartial 12 338290) = some ⟨12, 2, 0, 1163317, 338290, 1625, 65536⟩ := by
  decide +kernel

theorem context_12_338290_1163317 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338290 ⟨1163317, by decide⟩ :=
  accepted_of_selected 12 338290 ⟨1163317, by decide⟩ ⟨12, 2, 0, 1163317, 338290, 1625, 65536⟩
    (by decide) selected_cut_42577

theorem selected_cut_42578 : selected 9 ⟨1163349, by decide⟩
    (prefixPartial 12 338291) = some ⟨12, 2, 0, 1163349, 338291, 1809, 65536⟩ := by
  decide +kernel

theorem context_12_338291_1163349 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338291 ⟨1163349, by decide⟩ :=
  accepted_of_selected 12 338291 ⟨1163349, by decide⟩ ⟨12, 2, 0, 1163349, 338291, 1809, 65536⟩
    (by decide) selected_cut_42578

theorem unmarked_context_11_84572_1163350 : frontier 10 ⟨1163350, by decide⟩
    (prefixCache 11 84572) (prefixPartial 11 84572) = false := by
  decide +kernel

theorem node_context_11_84572_1163350 : EJMOriginalGlobalDAGData.nodes 10 ⟨1163350, by decide⟩ =
    .split (coordinate 11) (![⟨1163289, by decide⟩,⟨355230, by decide⟩,⟨1163317, by decide⟩,⟨1163349, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84572_1163350 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84572 ⟨1163350, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84572
    ⟨1163350, by decide⟩ (by decide) (![⟨1163289, by decide⟩,⟨355230, by decide⟩,⟨1163317, by decide⟩,⟨1163349, by decide⟩]) unmarked_context_11_84572_1163350 node_context_11_84572_1163350
  intro a
  fin_cases a
  · exact context_12_338288_1163289
  · exact context_12_338289_355230
  · exact context_12_338290_1163317
  · exact context_12_338291_1163349

theorem selected_cut_42579 : selected 9 ⟨1163372, by decide⟩
    (prefixPartial 12 338292) = some ⟨12, 2, 0, 1163372, 338292, 1425, 65536⟩ := by
  decide +kernel

theorem context_12_338292_1163372 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338292 ⟨1163372, by decide⟩ :=
  accepted_of_selected 12 338292 ⟨1163372, by decide⟩ ⟨12, 2, 0, 1163372, 338292, 1425, 65536⟩
    (by decide) selected_cut_42579

theorem selected_cut_42580 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 338293) = some ⟨12, 1, 0, 891951, 338293, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338293_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338293 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 338293 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 338293, 1, 65536⟩
    (by decide) selected_cut_42580

theorem selected_cut_42581 : selected 9 ⟨1163390, by decide⟩
    (prefixPartial 12 338294) = some ⟨12, 2, 0, 1163390, 338294, 1457, 65536⟩ := by
  decide +kernel

theorem context_12_338294_1163390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338294 ⟨1163390, by decide⟩ :=
  accepted_of_selected 12 338294 ⟨1163390, by decide⟩ ⟨12, 2, 0, 1163390, 338294, 1457, 65536⟩
    (by decide) selected_cut_42581

theorem selected_cut_42582 : selected 9 ⟨1163417, by decide⟩
    (prefixPartial 12 338295) = some ⟨12, 2, 0, 1163417, 338295, 1513, 65536⟩ := by
  decide +kernel

theorem context_12_338295_1163417 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338295 ⟨1163417, by decide⟩ :=
  accepted_of_selected 12 338295 ⟨1163417, by decide⟩ ⟨12, 2, 0, 1163417, 338295, 1513, 65536⟩
    (by decide) selected_cut_42582

theorem unmarked_context_11_84573_1163418 : frontier 10 ⟨1163418, by decide⟩
    (prefixCache 11 84573) (prefixPartial 11 84573) = false := by
  decide +kernel

theorem node_context_11_84573_1163418 : EJMOriginalGlobalDAGData.nodes 10 ⟨1163418, by decide⟩ =
    .split (coordinate 11) (![⟨1163372, by decide⟩,⟨891951, by decide⟩,⟨1163390, by decide⟩,⟨1163417, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84573_1163418 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84573 ⟨1163418, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84573
    ⟨1163418, by decide⟩ (by decide) (![⟨1163372, by decide⟩,⟨891951, by decide⟩,⟨1163390, by decide⟩,⟨1163417, by decide⟩]) unmarked_context_11_84573_1163418 node_context_11_84573_1163418
  intro a
  fin_cases a
  · exact context_12_338292_1163372
  · exact context_12_338293_891951
  · exact context_12_338294_1163390
  · exact context_12_338295_1163417

theorem selected_cut_42583 : selected 9 ⟨1163428, by decide⟩
    (prefixPartial 12 338296) = some ⟨12, 2, 0, 1163428, 338296, 1189, 65536⟩ := by
  decide +kernel

theorem context_12_338296_1163428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338296 ⟨1163428, by decide⟩ :=
  accepted_of_selected 12 338296 ⟨1163428, by decide⟩ ⟨12, 2, 0, 1163428, 338296, 1189, 65536⟩
    (by decide) selected_cut_42583

theorem selected_cut_42584 : selected 9 ⟨1163446, by decide⟩
    (prefixPartial 12 338297) = some ⟨12, 2, 0, 1163446, 338297, 1353, 65536⟩ := by
  decide +kernel

theorem context_12_338297_1163446 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338297 ⟨1163446, by decide⟩ :=
  accepted_of_selected 12 338297 ⟨1163446, by decide⟩ ⟨12, 2, 0, 1163446, 338297, 1353, 65536⟩
    (by decide) selected_cut_42584

theorem selected_cut_42585 : selected 9 ⟨1163462, by decide⟩
    (prefixPartial 12 338298) = some ⟨12, 2, 0, 1163462, 338298, 1305, 65536⟩ := by
  decide +kernel

theorem context_12_338298_1163462 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338298 ⟨1163462, by decide⟩ :=
  accepted_of_selected 12 338298 ⟨1163462, by decide⟩ ⟨12, 2, 0, 1163462, 338298, 1305, 65536⟩
    (by decide) selected_cut_42585

theorem selected_cut_42586 : selected 9 ⟨1163481, by decide⟩
    (prefixPartial 12 338299) = some ⟨12, 2, 0, 1163481, 338299, 1361, 65536⟩ := by
  decide +kernel

theorem context_12_338299_1163481 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338299 ⟨1163481, by decide⟩ :=
  accepted_of_selected 12 338299 ⟨1163481, by decide⟩ ⟨12, 2, 0, 1163481, 338299, 1361, 65536⟩
    (by decide) selected_cut_42586

theorem unmarked_context_11_84574_1163482 : frontier 10 ⟨1163482, by decide⟩
    (prefixCache 11 84574) (prefixPartial 11 84574) = false := by
  decide +kernel

theorem node_context_11_84574_1163482 : EJMOriginalGlobalDAGData.nodes 10 ⟨1163482, by decide⟩ =
    .split (coordinate 11) (![⟨1163428, by decide⟩,⟨1163446, by decide⟩,⟨1163462, by decide⟩,⟨1163481, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84574_1163482 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84574 ⟨1163482, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84574
    ⟨1163482, by decide⟩ (by decide) (![⟨1163428, by decide⟩,⟨1163446, by decide⟩,⟨1163462, by decide⟩,⟨1163481, by decide⟩]) unmarked_context_11_84574_1163482 node_context_11_84574_1163482
  intro a
  fin_cases a
  · exact context_12_338296_1163428
  · exact context_12_338297_1163446
  · exact context_12_338298_1163462
  · exact context_12_338299_1163481

theorem selected_cut_42587 : selected 10 ⟨1163527, by decide⟩
    (prefixPartial 11 84575) = some ⟨11, 2, 0, 1163527, 84575, 3409, 262144⟩ := by
  decide +kernel

theorem context_11_84575_1163527 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84575 ⟨1163527, by decide⟩ :=
  accepted_of_selected 11 84575 ⟨1163527, by decide⟩ ⟨11, 2, 0, 1163527, 84575, 3409, 262144⟩
    (by decide) selected_cut_42587

theorem unmarked_context_10_21143_1163528 : frontier 11 ⟨1163528, by decide⟩
    (prefixCache 10 21143) (prefixPartial 10 21143) = false := by
  decide +kernel

theorem node_context_10_21143_1163528 : EJMOriginalGlobalDAGData.nodes 11 ⟨1163528, by decide⟩ =
    .split (coordinate 10) (![⟨1163350, by decide⟩,⟨1163418, by decide⟩,⟨1163482, by decide⟩,⟨1163527, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21143_1163528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21143 ⟨1163528, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21143
    ⟨1163528, by decide⟩ (by decide) (![⟨1163350, by decide⟩,⟨1163418, by decide⟩,⟨1163482, by decide⟩,⟨1163527, by decide⟩]) unmarked_context_10_21143_1163528 node_context_10_21143_1163528
  intro a
  fin_cases a
  · exact context_11_84572_1163350
  · exact context_11_84573_1163418
  · exact context_11_84574_1163482
  · exact context_11_84575_1163527

theorem unmarked_context_9_5285_1163529 : frontier 12 ⟨1163529, by decide⟩
    (prefixCache 9 5285) (prefixPartial 9 5285) = false := by
  decide +kernel

theorem node_context_9_5285_1163529 : EJMOriginalGlobalDAGData.nodes 12 ⟨1163529, by decide⟩ =
    .split (coordinate 9) (![⟨1163081, by decide⟩,⟨893098, by decide⟩,⟨1163261, by decide⟩,⟨1163528, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5285_1163529 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5285 ⟨1163529, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5285
    ⟨1163529, by decide⟩ (by decide) (![⟨1163081, by decide⟩,⟨893098, by decide⟩,⟨1163261, by decide⟩,⟨1163528, by decide⟩]) unmarked_context_9_5285_1163529 node_context_9_5285_1163529
  intro a
  fin_cases a
  · exact context_10_21140_1163081
  · exact context_10_21141_893098
  · exact context_10_21142_1163261
  · exact context_10_21143_1163528

theorem selected_cut_42588 : selected 10 ⟨1163595, by decide⟩
    (prefixPartial 11 84576) = some ⟨11, 2, 0, 1163595, 84576, 3917, 262144⟩ := by
  decide +kernel

theorem context_11_84576_1163595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84576 ⟨1163595, by decide⟩ :=
  accepted_of_selected 11 84576 ⟨1163595, by decide⟩ ⟨11, 2, 0, 1163595, 84576, 3917, 262144⟩
    (by decide) selected_cut_42588

theorem selected_cut_42589 : selected 10 ⟨1163648, by decide⟩
    (prefixPartial 11 84577) = some ⟨11, 2, 0, 1163648, 84577, 3397, 262144⟩ := by
  decide +kernel

theorem context_11_84577_1163648 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84577 ⟨1163648, by decide⟩ :=
  accepted_of_selected 11 84577 ⟨1163648, by decide⟩ ⟨11, 2, 0, 1163648, 84577, 3397, 262144⟩
    (by decide) selected_cut_42589

theorem selected_cut_42590 : selected 10 ⟨1163697, by decide⟩
    (prefixPartial 11 84578) = some ⟨11, 2, 0, 1163697, 84578, 3205, 262144⟩ := by
  decide +kernel

theorem context_11_84578_1163697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84578 ⟨1163697, by decide⟩ :=
  accepted_of_selected 11 84578 ⟨1163697, by decide⟩ ⟨11, 2, 0, 1163697, 84578, 3205, 262144⟩
    (by decide) selected_cut_42590

theorem selected_cut_42591 : selected 9 ⟨1163709, by decide⟩
    (prefixPartial 12 338316) = some ⟨12, 2, 0, 1163709, 338316, 925, 65536⟩ := by
  decide +kernel

theorem context_12_338316_1163709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338316 ⟨1163709, by decide⟩ :=
  accepted_of_selected 12 338316 ⟨1163709, by decide⟩ ⟨12, 2, 0, 1163709, 338316, 925, 65536⟩
    (by decide) selected_cut_42591

theorem selected_cut_42592 : selected 9 ⟨1163727, by decide⟩
    (prefixPartial 12 338317) = some ⟨12, 2, 0, 1163727, 338317, 1125, 65536⟩ := by
  decide +kernel

theorem context_12_338317_1163727 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338317 ⟨1163727, by decide⟩ :=
  accepted_of_selected 12 338317 ⟨1163727, by decide⟩ ⟨12, 2, 0, 1163727, 338317, 1125, 65536⟩
    (by decide) selected_cut_42592

theorem selected_cut_42593 : selected 9 ⟨1163743, by decide⟩
    (prefixPartial 12 338318) = some ⟨12, 2, 0, 1163743, 338318, 1081, 65536⟩ := by
  decide +kernel

theorem context_12_338318_1163743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338318 ⟨1163743, by decide⟩ :=
  accepted_of_selected 12 338318 ⟨1163743, by decide⟩ ⟨12, 2, 0, 1163743, 338318, 1081, 65536⟩
    (by decide) selected_cut_42593

theorem selected_cut_42594 : selected 9 ⟨1163760, by decide⟩
    (prefixPartial 12 338319) = some ⟨12, 2, 0, 1163760, 338319, 1141, 65536⟩ := by
  decide +kernel

theorem context_12_338319_1163760 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338319 ⟨1163760, by decide⟩ :=
  accepted_of_selected 12 338319 ⟨1163760, by decide⟩ ⟨12, 2, 0, 1163760, 338319, 1141, 65536⟩
    (by decide) selected_cut_42594

theorem unmarked_context_11_84579_1163761 : frontier 10 ⟨1163761, by decide⟩
    (prefixCache 11 84579) (prefixPartial 11 84579) = false := by
  decide +kernel

theorem node_context_11_84579_1163761 : EJMOriginalGlobalDAGData.nodes 10 ⟨1163761, by decide⟩ =
    .split (coordinate 11) (![⟨1163709, by decide⟩,⟨1163727, by decide⟩,⟨1163743, by decide⟩,⟨1163760, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84579_1163761 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84579 ⟨1163761, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84579
    ⟨1163761, by decide⟩ (by decide) (![⟨1163709, by decide⟩,⟨1163727, by decide⟩,⟨1163743, by decide⟩,⟨1163760, by decide⟩]) unmarked_context_11_84579_1163761 node_context_11_84579_1163761
  intro a
  fin_cases a
  · exact context_12_338316_1163709
  · exact context_12_338317_1163727
  · exact context_12_338318_1163743
  · exact context_12_338319_1163760

theorem unmarked_context_10_21144_1163762 : frontier 11 ⟨1163762, by decide⟩
    (prefixCache 10 21144) (prefixPartial 10 21144) = false := by
  decide +kernel

theorem node_context_10_21144_1163762 : EJMOriginalGlobalDAGData.nodes 11 ⟨1163762, by decide⟩ =
    .split (coordinate 10) (![⟨1163595, by decide⟩,⟨1163648, by decide⟩,⟨1163697, by decide⟩,⟨1163761, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21144_1163762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21144 ⟨1163762, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21144
    ⟨1163762, by decide⟩ (by decide) (![⟨1163595, by decide⟩,⟨1163648, by decide⟩,⟨1163697, by decide⟩,⟨1163761, by decide⟩]) unmarked_context_10_21144_1163762 node_context_10_21144_1163762
  intro a
  fin_cases a
  · exact context_11_84576_1163595
  · exact context_11_84577_1163648
  · exact context_11_84578_1163697
  · exact context_11_84579_1163761

theorem selected_cut_42595 : selected 9 ⟨1163775, by decide⟩
    (prefixPartial 12 338320) = some ⟨12, 2, 0, 1163775, 338320, 949, 65536⟩ := by
  decide +kernel

theorem context_12_338320_1163775 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338320 ⟨1163775, by decide⟩ :=
  accepted_of_selected 12 338320 ⟨1163775, by decide⟩ ⟨12, 2, 0, 1163775, 338320, 949, 65536⟩
    (by decide) selected_cut_42595

theorem selected_cut_42596 : selected 9 ⟨1163793, by decide⟩
    (prefixPartial 12 338321) = some ⟨12, 2, 0, 1163793, 338321, 1145, 65536⟩ := by
  decide +kernel

theorem context_12_338321_1163793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338321 ⟨1163793, by decide⟩ :=
  accepted_of_selected 12 338321 ⟨1163793, by decide⟩ ⟨12, 2, 0, 1163793, 338321, 1145, 65536⟩
    (by decide) selected_cut_42596

theorem selected_cut_42597 : selected 9 ⟨1163807, by decide⟩
    (prefixPartial 12 338322) = some ⟨12, 2, 0, 1163807, 338322, 1121, 65536⟩ := by
  decide +kernel

theorem context_12_338322_1163807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338322 ⟨1163807, by decide⟩ :=
  accepted_of_selected 12 338322 ⟨1163807, by decide⟩ ⟨12, 2, 0, 1163807, 338322, 1121, 65536⟩
    (by decide) selected_cut_42597

theorem selected_cut_42598 : selected 9 ⟨1163819, by decide⟩
    (prefixPartial 12 338323) = some ⟨12, 2, 0, 1163819, 338323, 1061, 65536⟩ := by
  decide +kernel

theorem context_12_338323_1163819 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338323 ⟨1163819, by decide⟩ :=
  accepted_of_selected 12 338323 ⟨1163819, by decide⟩ ⟨12, 2, 0, 1163819, 338323, 1061, 65536⟩
    (by decide) selected_cut_42598

theorem unmarked_context_11_84580_1163820 : frontier 10 ⟨1163820, by decide⟩
    (prefixCache 11 84580) (prefixPartial 11 84580) = false := by
  decide +kernel

theorem node_context_11_84580_1163820 : EJMOriginalGlobalDAGData.nodes 10 ⟨1163820, by decide⟩ =
    .split (coordinate 11) (![⟨1163775, by decide⟩,⟨1163793, by decide⟩,⟨1163807, by decide⟩,⟨1163819, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84580_1163820 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84580 ⟨1163820, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84580
    ⟨1163820, by decide⟩ (by decide) (![⟨1163775, by decide⟩,⟨1163793, by decide⟩,⟨1163807, by decide⟩,⟨1163819, by decide⟩]) unmarked_context_11_84580_1163820 node_context_11_84580_1163820
  intro a
  fin_cases a
  · exact context_12_338320_1163775
  · exact context_12_338321_1163793
  · exact context_12_338322_1163807
  · exact context_12_338323_1163819

theorem selected_cut_42599 : selected 10 ⟨1163822, by decide⟩
    (prefixPartial 11 84581) = some ⟨11, 2, 0, 1163822, 84581, 5, 262144⟩ := by
  decide +kernel

theorem context_11_84581_1163822 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84581 ⟨1163822, by decide⟩ :=
  accepted_of_selected 11 84581 ⟨1163822, by decide⟩ ⟨11, 2, 0, 1163822, 84581, 5, 262144⟩
    (by decide) selected_cut_42599

theorem selected_cut_42600 : selected 10 ⟨1163858, by decide⟩
    (prefixPartial 11 84582) = some ⟨11, 2, 0, 1163858, 84582, 2733, 262144⟩ := by
  decide +kernel

theorem context_11_84582_1163858 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84582 ⟨1163858, by decide⟩ :=
  accepted_of_selected 11 84582 ⟨1163858, by decide⟩ ⟨11, 2, 0, 1163858, 84582, 2733, 262144⟩
    (by decide) selected_cut_42600

theorem selected_cut_42601 : selected 10 ⟨1163904, by decide⟩
    (prefixPartial 11 84583) = some ⟨11, 2, 0, 1163904, 84583, 3537, 262144⟩ := by
  decide +kernel

theorem context_11_84583_1163904 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84583 ⟨1163904, by decide⟩ :=
  accepted_of_selected 11 84583 ⟨1163904, by decide⟩ ⟨11, 2, 0, 1163904, 84583, 3537, 262144⟩
    (by decide) selected_cut_42601

theorem unmarked_context_10_21145_1163905 : frontier 11 ⟨1163905, by decide⟩
    (prefixCache 10 21145) (prefixPartial 10 21145) = false := by
  decide +kernel

theorem node_context_10_21145_1163905 : EJMOriginalGlobalDAGData.nodes 11 ⟨1163905, by decide⟩ =
    .split (coordinate 10) (![⟨1163820, by decide⟩,⟨1163822, by decide⟩,⟨1163858, by decide⟩,⟨1163904, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21145_1163905 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21145 ⟨1163905, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21145
    ⟨1163905, by decide⟩ (by decide) (![⟨1163820, by decide⟩,⟨1163822, by decide⟩,⟨1163858, by decide⟩,⟨1163904, by decide⟩]) unmarked_context_10_21145_1163905 node_context_10_21145_1163905
  intro a
  fin_cases a
  · exact context_11_84580_1163820
  · exact context_11_84581_1163822
  · exact context_11_84582_1163858
  · exact context_11_84583_1163904

theorem selected_cut_42602 : selected 10 ⟨1163935, by decide⟩
    (prefixPartial 11 84584) = some ⟨11, 2, 0, 1163935, 84584, 2221, 262144⟩ := by
  decide +kernel

theorem context_11_84584_1163935 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84584 ⟨1163935, by decide⟩ :=
  accepted_of_selected 11 84584 ⟨1163935, by decide⟩ ⟨11, 2, 0, 1163935, 84584, 2221, 262144⟩
    (by decide) selected_cut_42602

theorem selected_cut_42603 : selected 10 ⟨1163960, by decide⟩
    (prefixPartial 11 84585) = some ⟨11, 2, 0, 1163960, 84585, 925, 262144⟩ := by
  decide +kernel

theorem context_11_84585_1163960 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84585 ⟨1163960, by decide⟩ :=
  accepted_of_selected 11 84585 ⟨1163960, by decide⟩ ⟨11, 2, 0, 1163960, 84585, 925, 262144⟩
    (by decide) selected_cut_42603

theorem selected_cut_42604 : selected 10 ⟨1109453, by decide⟩
    (prefixPartial 11 84586) = some ⟨11, 1, 0, 1109453, 84586, 1, 262144⟩ := by
  decide +kernel

theorem context_11_84586_1109453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84586 ⟨1109453, by decide⟩ :=
  accepted_of_selected 11 84586 ⟨1109453, by decide⟩ ⟨11, 1, 0, 1109453, 84586, 1, 262144⟩
    (by decide) selected_cut_42604

theorem selected_cut_42605 : selected 10 ⟨1163984, by decide⟩
    (prefixPartial 11 84587) = some ⟨11, 2, 0, 1163984, 84587, 2045, 262144⟩ := by
  decide +kernel

theorem context_11_84587_1163984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84587 ⟨1163984, by decide⟩ :=
  accepted_of_selected 11 84587 ⟨1163984, by decide⟩ ⟨11, 2, 0, 1163984, 84587, 2045, 262144⟩
    (by decide) selected_cut_42605

theorem unmarked_context_10_21146_1163985 : frontier 11 ⟨1163985, by decide⟩
    (prefixCache 10 21146) (prefixPartial 10 21146) = false := by
  decide +kernel

theorem node_context_10_21146_1163985 : EJMOriginalGlobalDAGData.nodes 11 ⟨1163985, by decide⟩ =
    .split (coordinate 10) (![⟨1163935, by decide⟩,⟨1163960, by decide⟩,⟨1109453, by decide⟩,⟨1163984, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21146_1163985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21146 ⟨1163985, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21146
    ⟨1163985, by decide⟩ (by decide) (![⟨1163935, by decide⟩,⟨1163960, by decide⟩,⟨1109453, by decide⟩,⟨1163984, by decide⟩]) unmarked_context_10_21146_1163985 node_context_10_21146_1163985
  intro a
  fin_cases a
  · exact context_11_84584_1163935
  · exact context_11_84585_1163960
  · exact context_11_84586_1109453
  · exact context_11_84587_1163984

theorem selected_cut_42606 : selected 10 ⟨1164035, by decide⟩
    (prefixPartial 11 84588) = some ⟨11, 2, 0, 1164035, 84588, 3005, 262144⟩ := by
  decide +kernel

theorem context_11_84588_1164035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84588 ⟨1164035, by decide⟩ :=
  accepted_of_selected 11 84588 ⟨1164035, by decide⟩ ⟨11, 2, 0, 1164035, 84588, 3005, 262144⟩
    (by decide) selected_cut_42606

theorem selected_cut_42607 : selected 10 ⟨1164063, by decide⟩
    (prefixPartial 11 84589) = some ⟨11, 2, 0, 1164063, 84589, 1933, 262144⟩ := by
  decide +kernel

theorem context_11_84589_1164063 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84589 ⟨1164063, by decide⟩ :=
  accepted_of_selected 11 84589 ⟨1164063, by decide⟩ ⟨11, 2, 0, 1164063, 84589, 1933, 262144⟩
    (by decide) selected_cut_42607

theorem selected_cut_42608 : selected 10 ⟨1164092, by decide⟩
    (prefixPartial 11 84590) = some ⟨11, 2, 0, 1164092, 84590, 1757, 262144⟩ := by
  decide +kernel

theorem context_11_84590_1164092 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84590 ⟨1164092, by decide⟩ :=
  accepted_of_selected 11 84590 ⟨1164092, by decide⟩ ⟨11, 2, 0, 1164092, 84590, 1757, 262144⟩
    (by decide) selected_cut_42608

theorem selected_cut_42609 : selected 10 ⟨1164114, by decide⟩
    (prefixPartial 11 84591) = some ⟨11, 2, 0, 1164114, 84591, 1589, 262144⟩ := by
  decide +kernel

theorem context_11_84591_1164114 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84591 ⟨1164114, by decide⟩ :=
  accepted_of_selected 11 84591 ⟨1164114, by decide⟩ ⟨11, 2, 0, 1164114, 84591, 1589, 262144⟩
    (by decide) selected_cut_42609

theorem unmarked_context_10_21147_1164115 : frontier 11 ⟨1164115, by decide⟩
    (prefixCache 10 21147) (prefixPartial 10 21147) = false := by
  decide +kernel

theorem node_context_10_21147_1164115 : EJMOriginalGlobalDAGData.nodes 11 ⟨1164115, by decide⟩ =
    .split (coordinate 10) (![⟨1164035, by decide⟩,⟨1164063, by decide⟩,⟨1164092, by decide⟩,⟨1164114, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21147_1164115 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21147 ⟨1164115, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21147
    ⟨1164115, by decide⟩ (by decide) (![⟨1164035, by decide⟩,⟨1164063, by decide⟩,⟨1164092, by decide⟩,⟨1164114, by decide⟩]) unmarked_context_10_21147_1164115 node_context_10_21147_1164115
  intro a
  fin_cases a
  · exact context_11_84588_1164035
  · exact context_11_84589_1164063
  · exact context_11_84590_1164092
  · exact context_11_84591_1164114

theorem unmarked_context_9_5286_1164116 : frontier 12 ⟨1164116, by decide⟩
    (prefixCache 9 5286) (prefixPartial 9 5286) = false := by
  decide +kernel

theorem node_context_9_5286_1164116 : EJMOriginalGlobalDAGData.nodes 12 ⟨1164116, by decide⟩ =
    .split (coordinate 9) (![⟨1163762, by decide⟩,⟨1163905, by decide⟩,⟨1163985, by decide⟩,⟨1164115, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5286_1164116 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5286 ⟨1164116, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5286
    ⟨1164116, by decide⟩ (by decide) (![⟨1163762, by decide⟩,⟨1163905, by decide⟩,⟨1163985, by decide⟩,⟨1164115, by decide⟩]) unmarked_context_9_5286_1164116 node_context_9_5286_1164116
  intro a
  fin_cases a
  · exact context_10_21144_1163762
  · exact context_10_21145_1163905
  · exact context_10_21146_1163985
  · exact context_10_21147_1164115

theorem selected_cut_42610 : selected 10 ⟨1164144, by decide⟩
    (prefixPartial 11 84592) = some ⟨11, 2, 0, 1164144, 84592, 1845, 262144⟩ := by
  decide +kernel

theorem context_11_84592_1164144 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84592 ⟨1164144, by decide⟩ :=
  accepted_of_selected 11 84592 ⟨1164144, by decide⟩ ⟨11, 2, 0, 1164144, 84592, 1845, 262144⟩
    (by decide) selected_cut_42610

theorem selected_cut_42611 : selected 10 ⟨1164164, by decide⟩
    (prefixPartial 11 84593) = some ⟨11, 2, 0, 1164164, 84593, 1389, 262144⟩ := by
  decide +kernel

theorem context_11_84593_1164164 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84593 ⟨1164164, by decide⟩ :=
  accepted_of_selected 11 84593 ⟨1164164, by decide⟩ ⟨11, 2, 0, 1164164, 84593, 1389, 262144⟩
    (by decide) selected_cut_42611

theorem selected_cut_42612 : selected 10 ⟨1164185, by decide⟩
    (prefixPartial 11 84594) = some ⟨11, 2, 0, 1164185, 84594, 1597, 262144⟩ := by
  decide +kernel

theorem context_11_84594_1164185 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84594 ⟨1164185, by decide⟩ :=
  accepted_of_selected 11 84594 ⟨1164185, by decide⟩ ⟨11, 2, 0, 1164185, 84594, 1597, 262144⟩
    (by decide) selected_cut_42612

theorem selected_cut_42613 : selected 10 ⟨1164203, by decide⟩
    (prefixPartial 11 84595) = some ⟨11, 2, 0, 1164203, 84595, 1289, 262144⟩ := by
  decide +kernel

theorem context_11_84595_1164203 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84595 ⟨1164203, by decide⟩ :=
  accepted_of_selected 11 84595 ⟨1164203, by decide⟩ ⟨11, 2, 0, 1164203, 84595, 1289, 262144⟩
    (by decide) selected_cut_42613

theorem unmarked_context_10_21148_1164204 : frontier 11 ⟨1164204, by decide⟩
    (prefixCache 10 21148) (prefixPartial 10 21148) = false := by
  decide +kernel

theorem node_context_10_21148_1164204 : EJMOriginalGlobalDAGData.nodes 11 ⟨1164204, by decide⟩ =
    .split (coordinate 10) (![⟨1164144, by decide⟩,⟨1164164, by decide⟩,⟨1164185, by decide⟩,⟨1164203, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21148_1164204 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21148 ⟨1164204, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21148
    ⟨1164204, by decide⟩ (by decide) (![⟨1164144, by decide⟩,⟨1164164, by decide⟩,⟨1164185, by decide⟩,⟨1164203, by decide⟩]) unmarked_context_10_21148_1164204 node_context_10_21148_1164204
  intro a
  fin_cases a
  · exact context_11_84592_1164144
  · exact context_11_84593_1164164
  · exact context_11_84594_1164185
  · exact context_11_84595_1164203

theorem selected_cut_42614 : selected 11 ⟨1164261, by decide⟩
    (prefixPartial 10 21149) = some ⟨10, 2, 0, 1164261, 21149, 3829, 1048576⟩ := by
  decide +kernel

theorem context_10_21149_1164261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21149 ⟨1164261, by decide⟩ :=
  accepted_of_selected 10 21149 ⟨1164261, by decide⟩ ⟨10, 2, 0, 1164261, 21149, 3829, 1048576⟩
    (by decide) selected_cut_42614

theorem selected_cut_42615 : selected 11 ⟨1164287, by decide⟩
    (prefixPartial 10 21150) = some ⟨10, 2, 0, 1164287, 21150, 1601, 1048576⟩ := by
  decide +kernel

theorem context_10_21150_1164287 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21150 ⟨1164287, by decide⟩ :=
  accepted_of_selected 10 21150 ⟨1164287, by decide⟩ ⟨10, 2, 0, 1164287, 21150, 1601, 1048576⟩
    (by decide) selected_cut_42615

theorem selected_cut_42616 : selected 11 ⟨1164294, by decide⟩
    (prefixPartial 10 21151) = some ⟨10, 2, 0, 1164294, 21151, 473, 1048576⟩ := by
  decide +kernel

theorem context_10_21151_1164294 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21151 ⟨1164294, by decide⟩ :=
  accepted_of_selected 10 21151 ⟨1164294, by decide⟩ ⟨10, 2, 0, 1164294, 21151, 473, 1048576⟩
    (by decide) selected_cut_42616

theorem unmarked_context_9_5287_1164295 : frontier 12 ⟨1164295, by decide⟩
    (prefixCache 9 5287) (prefixPartial 9 5287) = false := by
  decide +kernel

theorem node_context_9_5287_1164295 : EJMOriginalGlobalDAGData.nodes 12 ⟨1164295, by decide⟩ =
    .split (coordinate 9) (![⟨1164204, by decide⟩,⟨1164261, by decide⟩,⟨1164287, by decide⟩,⟨1164294, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5287_1164295 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5287 ⟨1164295, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5287
    ⟨1164295, by decide⟩ (by decide) (![⟨1164204, by decide⟩,⟨1164261, by decide⟩,⟨1164287, by decide⟩,⟨1164294, by decide⟩]) unmarked_context_9_5287_1164295 node_context_9_5287_1164295
  intro a
  fin_cases a
  · exact context_10_21148_1164204
  · exact context_10_21149_1164261
  · exact context_10_21150_1164287
  · exact context_10_21151_1164294

theorem unmarked_context_8_1321_1164296 : frontier 13 ⟨1164296, by decide⟩
    (prefixCache 8 1321) (prefixPartial 8 1321) = false := by
  decide +kernel

theorem node_context_8_1321_1164296 : EJMOriginalGlobalDAGData.nodes 13 ⟨1164296, by decide⟩ =
    .split (coordinate 8) (![⟨1162808, by decide⟩,⟨1163529, by decide⟩,⟨1164116, by decide⟩,⟨1164295, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1321_1164296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1321 ⟨1164296, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1321
    ⟨1164296, by decide⟩ (by decide) (![⟨1162808, by decide⟩,⟨1163529, by decide⟩,⟨1164116, by decide⟩,⟨1164295, by decide⟩]) unmarked_context_8_1321_1164296 node_context_8_1321_1164296
  intro a
  fin_cases a
  · exact context_9_5284_1162808
  · exact context_9_5285_1163529
  · exact context_9_5286_1164116
  · exact context_9_5287_1164295

theorem selected_cut_42617 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 84608) = some ⟨11, 1, 0, 434745, 84608, 1, 262144⟩ := by
  decide +kernel

theorem context_11_84608_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84608 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 84608 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 84608, 1, 262144⟩
    (by decide) selected_cut_42617

theorem selected_cut_42618 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 338436) = some ⟨12, 1, 0, 448748, 338436, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338436_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338436 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 338436 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 338436, 1, 65536⟩
    (by decide) selected_cut_42618

theorem selected_cut_42619 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 338437) = some ⟨12, 1, 0, 34034, 338437, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338437_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338437 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 338437 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 338437, 1, 65536⟩
    (by decide) selected_cut_42619

theorem selected_cut_42620 : selected 9 ⟨1164353, by decide⟩
    (prefixPartial 12 338438) = some ⟨12, 2, 0, 1164353, 338438, 3189, 65536⟩ := by
  decide +kernel

theorem context_12_338438_1164353 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338438 ⟨1164353, by decide⟩ :=
  accepted_of_selected 12 338438 ⟨1164353, by decide⟩ ⟨12, 2, 0, 1164353, 338438, 3189, 65536⟩
    (by decide) selected_cut_42620

theorem selected_cut_42621 : selected 9 ⟨1164422, by decide⟩
    (prefixPartial 12 338439) = some ⟨12, 2, 0, 1164422, 338439, 3485, 65536⟩ := by
  decide +kernel

theorem context_12_338439_1164422 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338439 ⟨1164422, by decide⟩ :=
  accepted_of_selected 12 338439 ⟨1164422, by decide⟩ ⟨12, 2, 0, 1164422, 338439, 3485, 65536⟩
    (by decide) selected_cut_42621

theorem unmarked_context_11_84609_1164423 : frontier 10 ⟨1164423, by decide⟩
    (prefixCache 11 84609) (prefixPartial 11 84609) = false := by
  decide +kernel

theorem node_context_11_84609_1164423 : EJMOriginalGlobalDAGData.nodes 10 ⟨1164423, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1164353, by decide⟩,⟨1164422, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84609_1164423 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84609 ⟨1164423, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84609
    ⟨1164423, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1164353, by decide⟩,⟨1164422, by decide⟩]) unmarked_context_11_84609_1164423 node_context_11_84609_1164423
  intro a
  fin_cases a
  · exact context_12_338436_448748
  · exact context_12_338437_34034
  · exact context_12_338438_1164353
  · exact context_12_338439_1164422

theorem selected_cut_42622 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 338440) = some ⟨12, 1, 0, 448748, 338440, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338440_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338440 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 338440 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 338440, 1, 65536⟩
    (by decide) selected_cut_42622

theorem selected_cut_42623 : selected 9 ⟨1164491, by decide⟩
    (prefixPartial 12 338441) = some ⟨12, 2, 0, 1164491, 338441, 3021, 65536⟩ := by
  decide +kernel

theorem context_12_338441_1164491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338441 ⟨1164491, by decide⟩ :=
  accepted_of_selected 12 338441 ⟨1164491, by decide⟩ ⟨12, 2, 0, 1164491, 338441, 3021, 65536⟩
    (by decide) selected_cut_42623

theorem selected_cut_42624 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 338442) = some ⟨12, 1, 0, 893903, 338442, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338442_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338442 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 338442 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 338442, 1, 65536⟩
    (by decide) selected_cut_42624

theorem selected_cut_42625 : selected 9 ⟨1164556, by decide⟩
    (prefixPartial 12 338443) = some ⟨12, 2, 0, 1164556, 338443, 2985, 65536⟩ := by
  decide +kernel

theorem context_12_338443_1164556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338443 ⟨1164556, by decide⟩ :=
  accepted_of_selected 12 338443 ⟨1164556, by decide⟩ ⟨12, 2, 0, 1164556, 338443, 2985, 65536⟩
    (by decide) selected_cut_42625

theorem unmarked_context_11_84610_1164557 : frontier 10 ⟨1164557, by decide⟩
    (prefixCache 11 84610) (prefixPartial 11 84610) = false := by
  decide +kernel

theorem node_context_11_84610_1164557 : EJMOriginalGlobalDAGData.nodes 10 ⟨1164557, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1164491, by decide⟩,⟨893903, by decide⟩,⟨1164556, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84610_1164557 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84610 ⟨1164557, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84610
    ⟨1164557, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1164491, by decide⟩,⟨893903, by decide⟩,⟨1164556, by decide⟩]) unmarked_context_11_84610_1164557 node_context_11_84610_1164557
  intro a
  fin_cases a
  · exact context_12_338440_448748
  · exact context_12_338441_1164491
  · exact context_12_338442_893903
  · exact context_12_338443_1164556

theorem selected_cut_42626 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 338444) = some ⟨12, 1, 0, 448748, 338444, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338444_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338444 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 338444 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 338444, 1, 65536⟩
    (by decide) selected_cut_42626

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
