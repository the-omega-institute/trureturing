/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover088
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_08546 : selected 8 ⟨239419, by decide⟩
    (prefixPartial 13 92225) = some ⟨13, 2, 0, 239419, 92225, 2681, 16384⟩ := by
  decide +kernel

theorem context_13_92225_239419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92225 ⟨239419, by decide⟩ :=
  accepted_of_selected 13 92225 ⟨239419, by decide⟩ ⟨13, 2, 0, 239419, 92225, 2681, 16384⟩
    (by decide) selected_cut_08546

theorem selected_cut_08547 : selected 8 ⟨239438, by decide⟩
    (prefixPartial 13 92226) = some ⟨13, 2, 0, 239438, 92226, 1501, 16384⟩ := by
  decide +kernel

theorem context_13_92226_239438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92226 ⟨239438, by decide⟩ :=
  accepted_of_selected 13 92226 ⟨239438, by decide⟩ ⟨13, 2, 0, 239438, 92226, 1501, 16384⟩
    (by decide) selected_cut_08547

theorem selected_cut_08548 : selected 8 ⟨239448, by decide⟩
    (prefixPartial 13 92227) = some ⟨13, 2, 0, 239448, 92227, 981, 16384⟩ := by
  decide +kernel

theorem context_13_92227_239448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92227 ⟨239448, by decide⟩ :=
  accepted_of_selected 13 92227 ⟨239448, by decide⟩ ⟨13, 2, 0, 239448, 92227, 981, 16384⟩
    (by decide) selected_cut_08548

theorem unmarked_context_12_23056_239449 : frontier 9 ⟨239449, by decide⟩
    (prefixCache 12 23056) (prefixPartial 12 23056) = false := by
  decide +kernel

theorem node_context_12_23056_239449 : EJMOriginalGlobalDAGData.nodes 9 ⟨239449, by decide⟩ =
    .split (coordinate 12) (![⟨239383, by decide⟩,⟨239419, by decide⟩,⟨239438, by decide⟩,⟨239448, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23056_239449 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23056 ⟨239449, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23056
    ⟨239449, by decide⟩ (by decide) (![⟨239383, by decide⟩,⟨239419, by decide⟩,⟨239438, by decide⟩,⟨239448, by decide⟩]) unmarked_context_12_23056_239449 node_context_12_23056_239449
  intro a
  fin_cases a
  · exact context_13_92224_239383
  · exact context_13_92225_239419
  · exact context_13_92226_239438
  · exact context_13_92227_239448

theorem selected_cut_08549 : selected 8 ⟨239486, by decide⟩
    (prefixPartial 13 92228) = some ⟨13, 2, 0, 239486, 92228, 2373, 16384⟩ := by
  decide +kernel

theorem context_13_92228_239486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92228 ⟨239486, by decide⟩ :=
  accepted_of_selected 13 92228 ⟨239486, by decide⟩ ⟨13, 2, 0, 239486, 92228, 2373, 16384⟩
    (by decide) selected_cut_08549

theorem selected_cut_08550 : selected 8 ⟨239534, by decide⟩
    (prefixPartial 13 92229) = some ⟨13, 2, 0, 239534, 92229, 2549, 16384⟩ := by
  decide +kernel

theorem context_13_92229_239534 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92229 ⟨239534, by decide⟩ :=
  accepted_of_selected 13 92229 ⟨239534, by decide⟩ ⟨13, 2, 0, 239534, 92229, 2549, 16384⟩
    (by decide) selected_cut_08550

theorem selected_cut_08551 : selected 8 ⟨239558, by decide⟩
    (prefixPartial 13 92230) = some ⟨13, 2, 0, 239558, 92230, 1489, 16384⟩ := by
  decide +kernel

theorem context_13_92230_239558 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92230 ⟨239558, by decide⟩ :=
  accepted_of_selected 13 92230 ⟨239558, by decide⟩ ⟨13, 2, 0, 239558, 92230, 1489, 16384⟩
    (by decide) selected_cut_08551

theorem selected_cut_08552 : selected 8 ⟨239567, by decide⟩
    (prefixPartial 13 92231) = some ⟨13, 2, 0, 239567, 92231, 1029, 16384⟩ := by
  decide +kernel

theorem context_13_92231_239567 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92231 ⟨239567, by decide⟩ :=
  accepted_of_selected 13 92231 ⟨239567, by decide⟩ ⟨13, 2, 0, 239567, 92231, 1029, 16384⟩
    (by decide) selected_cut_08552

theorem unmarked_context_12_23057_239568 : frontier 9 ⟨239568, by decide⟩
    (prefixCache 12 23057) (prefixPartial 12 23057) = false := by
  decide +kernel

theorem node_context_12_23057_239568 : EJMOriginalGlobalDAGData.nodes 9 ⟨239568, by decide⟩ =
    .split (coordinate 12) (![⟨239486, by decide⟩,⟨239534, by decide⟩,⟨239558, by decide⟩,⟨239567, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23057_239568 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23057 ⟨239568, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23057
    ⟨239568, by decide⟩ (by decide) (![⟨239486, by decide⟩,⟨239534, by decide⟩,⟨239558, by decide⟩,⟨239567, by decide⟩]) unmarked_context_12_23057_239568 node_context_12_23057_239568
  intro a
  fin_cases a
  · exact context_13_92228_239486
  · exact context_13_92229_239534
  · exact context_13_92230_239558
  · exact context_13_92231_239567

theorem selected_cut_08553 : selected 8 ⟨239599, by decide⟩
    (prefixPartial 13 92232) = some ⟨13, 2, 0, 239599, 92232, 2533, 16384⟩ := by
  decide +kernel

theorem context_13_92232_239599 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92232 ⟨239599, by decide⟩ :=
  accepted_of_selected 13 92232 ⟨239599, by decide⟩ ⟨13, 2, 0, 239599, 92232, 2533, 16384⟩
    (by decide) selected_cut_08553

theorem selected_cut_08554 : selected 8 ⟨239641, by decide⟩
    (prefixPartial 13 92233) = some ⟨13, 2, 0, 239641, 92233, 3041, 16384⟩ := by
  decide +kernel

theorem context_13_92233_239641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92233 ⟨239641, by decide⟩ :=
  accepted_of_selected 13 92233 ⟨239641, by decide⟩ ⟨13, 2, 0, 239641, 92233, 3041, 16384⟩
    (by decide) selected_cut_08554

theorem selected_cut_08555 : selected 8 ⟨239663, by decide⟩
    (prefixPartial 13 92234) = some ⟨13, 2, 0, 239663, 92234, 1793, 16384⟩ := by
  decide +kernel

theorem context_13_92234_239663 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92234 ⟨239663, by decide⟩ :=
  accepted_of_selected 13 92234 ⟨239663, by decide⟩ ⟨13, 2, 0, 239663, 92234, 1793, 16384⟩
    (by decide) selected_cut_08555

theorem selected_cut_08556 : selected 8 ⟨239672, by decide⟩
    (prefixPartial 13 92235) = some ⟨13, 2, 0, 239672, 92235, 1097, 16384⟩ := by
  decide +kernel

theorem context_13_92235_239672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92235 ⟨239672, by decide⟩ :=
  accepted_of_selected 13 92235 ⟨239672, by decide⟩ ⟨13, 2, 0, 239672, 92235, 1097, 16384⟩
    (by decide) selected_cut_08556

theorem unmarked_context_12_23058_239673 : frontier 9 ⟨239673, by decide⟩
    (prefixCache 12 23058) (prefixPartial 12 23058) = false := by
  decide +kernel

theorem node_context_12_23058_239673 : EJMOriginalGlobalDAGData.nodes 9 ⟨239673, by decide⟩ =
    .split (coordinate 12) (![⟨239599, by decide⟩,⟨239641, by decide⟩,⟨239663, by decide⟩,⟨239672, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23058_239673 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23058 ⟨239673, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23058
    ⟨239673, by decide⟩ (by decide) (![⟨239599, by decide⟩,⟨239641, by decide⟩,⟨239663, by decide⟩,⟨239672, by decide⟩]) unmarked_context_12_23058_239673 node_context_12_23058_239673
  intro a
  fin_cases a
  · exact context_13_92232_239599
  · exact context_13_92233_239641
  · exact context_13_92234_239663
  · exact context_13_92235_239672

theorem selected_cut_08557 : selected 8 ⟨239719, by decide⟩
    (prefixPartial 13 92236) = some ⟨13, 2, 0, 239719, 92236, 3029, 16384⟩ := by
  decide +kernel

theorem context_13_92236_239719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92236 ⟨239719, by decide⟩ :=
  accepted_of_selected 13 92236 ⟨239719, by decide⟩ ⟨13, 2, 0, 239719, 92236, 3029, 16384⟩
    (by decide) selected_cut_08557

theorem selected_cut_08558 : selected 8 ⟨239769, by decide⟩
    (prefixPartial 13 92237) = some ⟨13, 2, 0, 239769, 92237, 3313, 16384⟩ := by
  decide +kernel

theorem context_13_92237_239769 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92237 ⟨239769, by decide⟩ :=
  accepted_of_selected 13 92237 ⟨239769, by decide⟩ ⟨13, 2, 0, 239769, 92237, 3313, 16384⟩
    (by decide) selected_cut_08558

theorem selected_cut_08559 : selected 8 ⟨239791, by decide⟩
    (prefixPartial 13 92238) = some ⟨13, 2, 0, 239791, 92238, 1793, 16384⟩ := by
  decide +kernel

theorem context_13_92238_239791 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92238 ⟨239791, by decide⟩ :=
  accepted_of_selected 13 92238 ⟨239791, by decide⟩ ⟨13, 2, 0, 239791, 92238, 1793, 16384⟩
    (by decide) selected_cut_08559

theorem selected_cut_08560 : selected 8 ⟨239802, by decide⟩
    (prefixPartial 13 92239) = some ⟨13, 2, 0, 239802, 92239, 1125, 16384⟩ := by
  decide +kernel

theorem context_13_92239_239802 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92239 ⟨239802, by decide⟩ :=
  accepted_of_selected 13 92239 ⟨239802, by decide⟩ ⟨13, 2, 0, 239802, 92239, 1125, 16384⟩
    (by decide) selected_cut_08560

theorem unmarked_context_12_23059_239803 : frontier 9 ⟨239803, by decide⟩
    (prefixCache 12 23059) (prefixPartial 12 23059) = false := by
  decide +kernel

theorem node_context_12_23059_239803 : EJMOriginalGlobalDAGData.nodes 9 ⟨239803, by decide⟩ =
    .split (coordinate 12) (![⟨239719, by decide⟩,⟨239769, by decide⟩,⟨239791, by decide⟩,⟨239802, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23059_239803 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23059 ⟨239803, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23059
    ⟨239803, by decide⟩ (by decide) (![⟨239719, by decide⟩,⟨239769, by decide⟩,⟨239791, by decide⟩,⟨239802, by decide⟩]) unmarked_context_12_23059_239803 node_context_12_23059_239803
  intro a
  fin_cases a
  · exact context_13_92236_239719
  · exact context_13_92237_239769
  · exact context_13_92238_239791
  · exact context_13_92239_239802

theorem unmarked_context_11_5764_239804 : frontier 10 ⟨239804, by decide⟩
    (prefixCache 11 5764) (prefixPartial 11 5764) = false := by
  decide +kernel

theorem node_context_11_5764_239804 : EJMOriginalGlobalDAGData.nodes 10 ⟨239804, by decide⟩ =
    .split (coordinate 11) (![⟨239449, by decide⟩,⟨239568, by decide⟩,⟨239673, by decide⟩,⟨239803, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5764_239804 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5764 ⟨239804, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5764
    ⟨239804, by decide⟩ (by decide) (![⟨239449, by decide⟩,⟨239568, by decide⟩,⟨239673, by decide⟩,⟨239803, by decide⟩]) unmarked_context_11_5764_239804 node_context_11_5764_239804
  intro a
  fin_cases a
  · exact context_12_23056_239449
  · exact context_12_23057_239568
  · exact context_12_23058_239673
  · exact context_12_23059_239803

theorem selected_cut_08561 : selected 8 ⟨239842, by decide⟩
    (prefixPartial 13 92240) = some ⟨13, 2, 0, 239842, 92240, 2013, 16384⟩ := by
  decide +kernel

theorem context_13_92240_239842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92240 ⟨239842, by decide⟩ :=
  accepted_of_selected 13 92240 ⟨239842, by decide⟩ ⟨13, 2, 0, 239842, 92240, 2013, 16384⟩
    (by decide) selected_cut_08561

theorem selected_cut_08562 : selected 8 ⟨239886, by decide⟩
    (prefixPartial 13 92241) = some ⟨13, 2, 0, 239886, 92241, 2865, 16384⟩ := by
  decide +kernel

theorem context_13_92241_239886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92241 ⟨239886, by decide⟩ :=
  accepted_of_selected 13 92241 ⟨239886, by decide⟩ ⟨13, 2, 0, 239886, 92241, 2865, 16384⟩
    (by decide) selected_cut_08562

theorem selected_cut_08563 : selected 8 ⟨239905, by decide⟩
    (prefixPartial 13 92242) = some ⟨13, 2, 0, 239905, 92242, 1221, 16384⟩ := by
  decide +kernel

theorem context_13_92242_239905 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92242 ⟨239905, by decide⟩ :=
  accepted_of_selected 13 92242 ⟨239905, by decide⟩ ⟨13, 2, 0, 239905, 92242, 1221, 16384⟩
    (by decide) selected_cut_08563

theorem selected_cut_08564 : selected 8 ⟨239918, by decide⟩
    (prefixPartial 13 92243) = some ⟨13, 2, 0, 239918, 92243, 1117, 16384⟩ := by
  decide +kernel

theorem context_13_92243_239918 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92243 ⟨239918, by decide⟩ :=
  accepted_of_selected 13 92243 ⟨239918, by decide⟩ ⟨13, 2, 0, 239918, 92243, 1117, 16384⟩
    (by decide) selected_cut_08564

theorem unmarked_context_12_23060_239919 : frontier 9 ⟨239919, by decide⟩
    (prefixCache 12 23060) (prefixPartial 12 23060) = false := by
  decide +kernel

theorem node_context_12_23060_239919 : EJMOriginalGlobalDAGData.nodes 9 ⟨239919, by decide⟩ =
    .split (coordinate 12) (![⟨239842, by decide⟩,⟨239886, by decide⟩,⟨239905, by decide⟩,⟨239918, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23060_239919 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23060 ⟨239919, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23060
    ⟨239919, by decide⟩ (by decide) (![⟨239842, by decide⟩,⟨239886, by decide⟩,⟨239905, by decide⟩,⟨239918, by decide⟩]) unmarked_context_12_23060_239919 node_context_12_23060_239919
  intro a
  fin_cases a
  · exact context_13_92240_239842
  · exact context_13_92241_239886
  · exact context_13_92242_239905
  · exact context_13_92243_239918

theorem selected_cut_08565 : selected 8 ⟨239948, by decide⟩
    (prefixPartial 13 92244) = some ⟨13, 2, 0, 239948, 92244, 1981, 16384⟩ := by
  decide +kernel

theorem context_13_92244_239948 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92244 ⟨239948, by decide⟩ :=
  accepted_of_selected 13 92244 ⟨239948, by decide⟩ ⟨13, 2, 0, 239948, 92244, 1981, 16384⟩
    (by decide) selected_cut_08565

theorem selected_cut_08566 : selected 8 ⟨239988, by decide⟩
    (prefixPartial 13 92245) = some ⟨13, 2, 0, 239988, 92245, 2329, 16384⟩ := by
  decide +kernel

theorem context_13_92245_239988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92245 ⟨239988, by decide⟩ :=
  accepted_of_selected 13 92245 ⟨239988, by decide⟩ ⟨13, 2, 0, 239988, 92245, 2329, 16384⟩
    (by decide) selected_cut_08566

theorem selected_cut_08567 : selected 8 ⟨240008, by decide⟩
    (prefixPartial 13 92246) = some ⟨13, 2, 0, 240008, 92246, 1201, 16384⟩ := by
  decide +kernel

theorem context_13_92246_240008 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92246 ⟨240008, by decide⟩ :=
  accepted_of_selected 13 92246 ⟨240008, by decide⟩ ⟨13, 2, 0, 240008, 92246, 1201, 16384⟩
    (by decide) selected_cut_08567

theorem selected_cut_08568 : selected 8 ⟨240015, by decide⟩
    (prefixPartial 13 92247) = some ⟨13, 2, 0, 240015, 92247, 1093, 16384⟩ := by
  decide +kernel

theorem context_13_92247_240015 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92247 ⟨240015, by decide⟩ :=
  accepted_of_selected 13 92247 ⟨240015, by decide⟩ ⟨13, 2, 0, 240015, 92247, 1093, 16384⟩
    (by decide) selected_cut_08568

theorem unmarked_context_12_23061_240016 : frontier 9 ⟨240016, by decide⟩
    (prefixCache 12 23061) (prefixPartial 12 23061) = false := by
  decide +kernel

theorem node_context_12_23061_240016 : EJMOriginalGlobalDAGData.nodes 9 ⟨240016, by decide⟩ =
    .split (coordinate 12) (![⟨239948, by decide⟩,⟨239988, by decide⟩,⟨240008, by decide⟩,⟨240015, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23061_240016 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23061 ⟨240016, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23061
    ⟨240016, by decide⟩ (by decide) (![⟨239948, by decide⟩,⟨239988, by decide⟩,⟨240008, by decide⟩,⟨240015, by decide⟩]) unmarked_context_12_23061_240016 node_context_12_23061_240016
  intro a
  fin_cases a
  · exact context_13_92244_239948
  · exact context_13_92245_239988
  · exact context_13_92246_240008
  · exact context_13_92247_240015

theorem selected_cut_08569 : selected 8 ⟨240049, by decide⟩
    (prefixPartial 13 92248) = some ⟨13, 2, 0, 240049, 92248, 2245, 16384⟩ := by
  decide +kernel

theorem context_13_92248_240049 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92248 ⟨240049, by decide⟩ :=
  accepted_of_selected 13 92248 ⟨240049, by decide⟩ ⟨13, 2, 0, 240049, 92248, 2245, 16384⟩
    (by decide) selected_cut_08569

theorem selected_cut_08570 : selected 8 ⟨240089, by decide⟩
    (prefixPartial 13 92249) = some ⟨13, 2, 0, 240089, 92249, 2721, 16384⟩ := by
  decide +kernel

theorem context_13_92249_240089 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92249 ⟨240089, by decide⟩ :=
  accepted_of_selected 13 92249 ⟨240089, by decide⟩ ⟨13, 2, 0, 240089, 92249, 2721, 16384⟩
    (by decide) selected_cut_08570

theorem selected_cut_08571 : selected 8 ⟨240107, by decide⟩
    (prefixPartial 13 92250) = some ⟨13, 2, 0, 240107, 92250, 1477, 16384⟩ := by
  decide +kernel

theorem context_13_92250_240107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92250 ⟨240107, by decide⟩ :=
  accepted_of_selected 13 92250 ⟨240107, by decide⟩ ⟨13, 2, 0, 240107, 92250, 1477, 16384⟩
    (by decide) selected_cut_08571

theorem selected_cut_08572 : selected 8 ⟨240113, by decide⟩
    (prefixPartial 13 92251) = some ⟨13, 2, 0, 240113, 92251, 1189, 16384⟩ := by
  decide +kernel

theorem context_13_92251_240113 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92251 ⟨240113, by decide⟩ :=
  accepted_of_selected 13 92251 ⟨240113, by decide⟩ ⟨13, 2, 0, 240113, 92251, 1189, 16384⟩
    (by decide) selected_cut_08572

theorem unmarked_context_12_23062_240114 : frontier 9 ⟨240114, by decide⟩
    (prefixCache 12 23062) (prefixPartial 12 23062) = false := by
  decide +kernel

theorem node_context_12_23062_240114 : EJMOriginalGlobalDAGData.nodes 9 ⟨240114, by decide⟩ =
    .split (coordinate 12) (![⟨240049, by decide⟩,⟨240089, by decide⟩,⟨240107, by decide⟩,⟨240113, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23062_240114 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23062 ⟨240114, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23062
    ⟨240114, by decide⟩ (by decide) (![⟨240049, by decide⟩,⟨240089, by decide⟩,⟨240107, by decide⟩,⟨240113, by decide⟩]) unmarked_context_12_23062_240114 node_context_12_23062_240114
  intro a
  fin_cases a
  · exact context_13_92248_240049
  · exact context_13_92249_240089
  · exact context_13_92250_240107
  · exact context_13_92251_240113

theorem selected_cut_08573 : selected 8 ⟨240152, by decide⟩
    (prefixPartial 13 92252) = some ⟨13, 2, 0, 240152, 92252, 2661, 16384⟩ := by
  decide +kernel

theorem context_13_92252_240152 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92252 ⟨240152, by decide⟩ :=
  accepted_of_selected 13 92252 ⟨240152, by decide⟩ ⟨13, 2, 0, 240152, 92252, 2661, 16384⟩
    (by decide) selected_cut_08573

theorem selected_cut_08574 : selected 8 ⟨240195, by decide⟩
    (prefixPartial 13 92253) = some ⟨13, 2, 0, 240195, 92253, 2953, 16384⟩ := by
  decide +kernel

theorem context_13_92253_240195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92253 ⟨240195, by decide⟩ :=
  accepted_of_selected 13 92253 ⟨240195, by decide⟩ ⟨13, 2, 0, 240195, 92253, 2953, 16384⟩
    (by decide) selected_cut_08574

theorem selected_cut_08575 : selected 8 ⟨240217, by decide⟩
    (prefixPartial 13 92254) = some ⟨13, 2, 0, 240217, 92254, 1657, 16384⟩ := by
  decide +kernel

theorem context_13_92254_240217 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92254 ⟨240217, by decide⟩ :=
  accepted_of_selected 13 92254 ⟨240217, by decide⟩ ⟨13, 2, 0, 240217, 92254, 1657, 16384⟩
    (by decide) selected_cut_08575

theorem selected_cut_08576 : selected 8 ⟨240229, by decide⟩
    (prefixPartial 13 92255) = some ⟨13, 2, 0, 240229, 92255, 1181, 16384⟩ := by
  decide +kernel

theorem context_13_92255_240229 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92255 ⟨240229, by decide⟩ :=
  accepted_of_selected 13 92255 ⟨240229, by decide⟩ ⟨13, 2, 0, 240229, 92255, 1181, 16384⟩
    (by decide) selected_cut_08576

theorem unmarked_context_12_23063_240230 : frontier 9 ⟨240230, by decide⟩
    (prefixCache 12 23063) (prefixPartial 12 23063) = false := by
  decide +kernel

theorem node_context_12_23063_240230 : EJMOriginalGlobalDAGData.nodes 9 ⟨240230, by decide⟩ =
    .split (coordinate 12) (![⟨240152, by decide⟩,⟨240195, by decide⟩,⟨240217, by decide⟩,⟨240229, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23063_240230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23063 ⟨240230, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23063
    ⟨240230, by decide⟩ (by decide) (![⟨240152, by decide⟩,⟨240195, by decide⟩,⟨240217, by decide⟩,⟨240229, by decide⟩]) unmarked_context_12_23063_240230 node_context_12_23063_240230
  intro a
  fin_cases a
  · exact context_13_92252_240152
  · exact context_13_92253_240195
  · exact context_13_92254_240217
  · exact context_13_92255_240229

theorem unmarked_context_11_5765_240231 : frontier 10 ⟨240231, by decide⟩
    (prefixCache 11 5765) (prefixPartial 11 5765) = false := by
  decide +kernel

theorem node_context_11_5765_240231 : EJMOriginalGlobalDAGData.nodes 10 ⟨240231, by decide⟩ =
    .split (coordinate 11) (![⟨239919, by decide⟩,⟨240016, by decide⟩,⟨240114, by decide⟩,⟨240230, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5765_240231 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5765 ⟨240231, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5765
    ⟨240231, by decide⟩ (by decide) (![⟨239919, by decide⟩,⟨240016, by decide⟩,⟨240114, by decide⟩,⟨240230, by decide⟩]) unmarked_context_11_5765_240231 node_context_11_5765_240231
  intro a
  fin_cases a
  · exact context_12_23060_239919
  · exact context_12_23061_240016
  · exact context_12_23062_240114
  · exact context_12_23063_240230

theorem selected_cut_08577 : selected 8 ⟨240250, by decide⟩
    (prefixPartial 13 92256) = some ⟨13, 2, 0, 240250, 92256, 1617, 16384⟩ := by
  decide +kernel

theorem context_13_92256_240250 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92256 ⟨240250, by decide⟩ :=
  accepted_of_selected 13 92256 ⟨240250, by decide⟩ ⟨13, 2, 0, 240250, 92256, 1617, 16384⟩
    (by decide) selected_cut_08577

theorem selected_cut_08578 : selected 8 ⟨240286, by decide⟩
    (prefixPartial 13 92257) = some ⟨13, 2, 0, 240286, 92257, 2529, 16384⟩ := by
  decide +kernel

theorem context_13_92257_240286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92257 ⟨240286, by decide⟩ :=
  accepted_of_selected 13 92257 ⟨240286, by decide⟩ ⟨13, 2, 0, 240286, 92257, 2529, 16384⟩
    (by decide) selected_cut_08578

theorem selected_cut_08579 : selected 8 ⟨240307, by decide⟩
    (prefixPartial 13 92258) = some ⟨13, 2, 0, 240307, 92258, 1517, 16384⟩ := by
  decide +kernel

theorem context_13_92258_240307 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92258 ⟨240307, by decide⟩ :=
  accepted_of_selected 13 92258 ⟨240307, by decide⟩ ⟨13, 2, 0, 240307, 92258, 1517, 16384⟩
    (by decide) selected_cut_08579

theorem selected_cut_08580 : selected 8 ⟨240317, by decide⟩
    (prefixPartial 13 92259) = some ⟨13, 2, 0, 240317, 92259, 901, 16384⟩ := by
  decide +kernel

theorem context_13_92259_240317 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92259 ⟨240317, by decide⟩ :=
  accepted_of_selected 13 92259 ⟨240317, by decide⟩ ⟨13, 2, 0, 240317, 92259, 901, 16384⟩
    (by decide) selected_cut_08580

theorem unmarked_context_12_23064_240318 : frontier 9 ⟨240318, by decide⟩
    (prefixCache 12 23064) (prefixPartial 12 23064) = false := by
  decide +kernel

theorem node_context_12_23064_240318 : EJMOriginalGlobalDAGData.nodes 9 ⟨240318, by decide⟩ =
    .split (coordinate 12) (![⟨240250, by decide⟩,⟨240286, by decide⟩,⟨240307, by decide⟩,⟨240317, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23064_240318 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23064 ⟨240318, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23064
    ⟨240318, by decide⟩ (by decide) (![⟨240250, by decide⟩,⟨240286, by decide⟩,⟨240307, by decide⟩,⟨240317, by decide⟩]) unmarked_context_12_23064_240318 node_context_12_23064_240318
  intro a
  fin_cases a
  · exact context_13_92256_240250
  · exact context_13_92257_240286
  · exact context_13_92258_240307
  · exact context_13_92259_240317

theorem selected_cut_08581 : selected 8 ⟨240354, by decide⟩
    (prefixPartial 13 92260) = some ⟨13, 2, 0, 240354, 92260, 1917, 16384⟩ := by
  decide +kernel

theorem context_13_92260_240354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92260 ⟨240354, by decide⟩ :=
  accepted_of_selected 13 92260 ⟨240354, by decide⟩ ⟨13, 2, 0, 240354, 92260, 1917, 16384⟩
    (by decide) selected_cut_08581

theorem selected_cut_08582 : selected 8 ⟨240388, by decide⟩
    (prefixPartial 13 92261) = some ⟨13, 2, 0, 240388, 92261, 2165, 16384⟩ := by
  decide +kernel

theorem context_13_92261_240388 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92261 ⟨240388, by decide⟩ :=
  accepted_of_selected 13 92261 ⟨240388, by decide⟩ ⟨13, 2, 0, 240388, 92261, 2165, 16384⟩
    (by decide) selected_cut_08582

theorem selected_cut_08583 : selected 8 ⟨240413, by decide⟩
    (prefixPartial 13 92262) = some ⟨13, 2, 0, 240413, 92262, 1581, 16384⟩ := by
  decide +kernel

theorem context_13_92262_240413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92262 ⟨240413, by decide⟩ :=
  accepted_of_selected 13 92262 ⟨240413, by decide⟩ ⟨13, 2, 0, 240413, 92262, 1581, 16384⟩
    (by decide) selected_cut_08583

theorem selected_cut_08584 : selected 8 ⟨240422, by decide⟩
    (prefixPartial 13 92263) = some ⟨13, 2, 0, 240422, 92263, 953, 16384⟩ := by
  decide +kernel

theorem context_13_92263_240422 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92263 ⟨240422, by decide⟩ :=
  accepted_of_selected 13 92263 ⟨240422, by decide⟩ ⟨13, 2, 0, 240422, 92263, 953, 16384⟩
    (by decide) selected_cut_08584

theorem unmarked_context_12_23065_240423 : frontier 9 ⟨240423, by decide⟩
    (prefixCache 12 23065) (prefixPartial 12 23065) = false := by
  decide +kernel

theorem node_context_12_23065_240423 : EJMOriginalGlobalDAGData.nodes 9 ⟨240423, by decide⟩ =
    .split (coordinate 12) (![⟨240354, by decide⟩,⟨240388, by decide⟩,⟨240413, by decide⟩,⟨240422, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23065_240423 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23065 ⟨240423, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23065
    ⟨240423, by decide⟩ (by decide) (![⟨240354, by decide⟩,⟨240388, by decide⟩,⟨240413, by decide⟩,⟨240422, by decide⟩]) unmarked_context_12_23065_240423 node_context_12_23065_240423
  intro a
  fin_cases a
  · exact context_13_92260_240354
  · exact context_13_92261_240388
  · exact context_13_92262_240413
  · exact context_13_92263_240422

theorem selected_cut_08585 : selected 8 ⟨240471, by decide⟩
    (prefixPartial 13 92264) = some ⟨13, 2, 0, 240471, 92264, 3209, 16384⟩ := by
  decide +kernel

theorem context_13_92264_240471 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92264 ⟨240471, by decide⟩ :=
  accepted_of_selected 13 92264 ⟨240471, by decide⟩ ⟨13, 2, 0, 240471, 92264, 3209, 16384⟩
    (by decide) selected_cut_08585

theorem selected_cut_08586 : selected 7 ⟨240496, by decide⟩
    (prefixPartial 14 369060) = some ⟨14, 2, 0, 240496, 369060, 1289, 4096⟩ := by
  decide +kernel

theorem context_14_369060_240496 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 369060 ⟨240496, by decide⟩ :=
  accepted_of_selected 14 369060 ⟨240496, by decide⟩ ⟨14, 2, 0, 240496, 369060, 1289, 4096⟩
    (by decide) selected_cut_08586

theorem selected_cut_08587 : selected 7 ⟨240522, by decide⟩
    (prefixPartial 14 369061) = some ⟨14, 2, 0, 240522, 369061, 1105, 4096⟩ := by
  decide +kernel

theorem context_14_369061_240522 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 369061 ⟨240522, by decide⟩ :=
  accepted_of_selected 14 369061 ⟨240522, by decide⟩ ⟨14, 2, 0, 240522, 369061, 1105, 4096⟩
    (by decide) selected_cut_08587

theorem selected_cut_08588 : selected 7 ⟨240538, by decide⟩
    (prefixPartial 14 369062) = some ⟨14, 2, 0, 240538, 369062, 1013, 4096⟩ := by
  decide +kernel

theorem context_14_369062_240538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 369062 ⟨240538, by decide⟩ :=
  accepted_of_selected 14 369062 ⟨240538, by decide⟩ ⟨14, 2, 0, 240538, 369062, 1013, 4096⟩
    (by decide) selected_cut_08588

theorem selected_cut_08589 : selected 7 ⟨240556, by decide⟩
    (prefixPartial 14 369063) = some ⟨14, 2, 0, 240556, 369063, 1073, 4096⟩ := by
  decide +kernel

theorem context_14_369063_240556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 369063 ⟨240556, by decide⟩ :=
  accepted_of_selected 14 369063 ⟨240556, by decide⟩ ⟨14, 2, 0, 240556, 369063, 1073, 4096⟩
    (by decide) selected_cut_08589

theorem unmarked_context_13_92265_240557 : frontier 8 ⟨240557, by decide⟩
    (prefixCache 13 92265) (prefixPartial 13 92265) = false := by
  decide +kernel

theorem node_context_13_92265_240557 : EJMOriginalGlobalDAGData.nodes 8 ⟨240557, by decide⟩ =
    .split (coordinate 13) (![⟨240496, by decide⟩,⟨240522, by decide⟩,⟨240538, by decide⟩,⟨240556, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_92265_240557 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92265 ⟨240557, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 92265
    ⟨240557, by decide⟩ (by decide) (![⟨240496, by decide⟩,⟨240522, by decide⟩,⟨240538, by decide⟩,⟨240556, by decide⟩]) unmarked_context_13_92265_240557 node_context_13_92265_240557
  intro a
  fin_cases a
  · exact context_14_369060_240496
  · exact context_14_369061_240522
  · exact context_14_369062_240538
  · exact context_14_369063_240556

theorem selected_cut_08590 : selected 8 ⟨240636, by decide⟩
    (prefixPartial 13 92266) = some ⟨13, 2, 0, 240636, 92266, 3041, 16384⟩ := by
  decide +kernel

theorem context_13_92266_240636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92266 ⟨240636, by decide⟩ :=
  accepted_of_selected 13 92266 ⟨240636, by decide⟩ ⟨13, 2, 0, 240636, 92266, 3041, 16384⟩
    (by decide) selected_cut_08590

theorem selected_cut_08591 : selected 8 ⟨240653, by decide⟩
    (prefixPartial 13 92267) = some ⟨13, 2, 0, 240653, 92267, 1321, 16384⟩ := by
  decide +kernel

theorem context_13_92267_240653 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92267 ⟨240653, by decide⟩ :=
  accepted_of_selected 13 92267 ⟨240653, by decide⟩ ⟨13, 2, 0, 240653, 92267, 1321, 16384⟩
    (by decide) selected_cut_08591

theorem unmarked_context_12_23066_240654 : frontier 9 ⟨240654, by decide⟩
    (prefixCache 12 23066) (prefixPartial 12 23066) = false := by
  decide +kernel

theorem node_context_12_23066_240654 : EJMOriginalGlobalDAGData.nodes 9 ⟨240654, by decide⟩ =
    .split (coordinate 12) (![⟨240471, by decide⟩,⟨240557, by decide⟩,⟨240636, by decide⟩,⟨240653, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23066_240654 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23066 ⟨240654, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23066
    ⟨240654, by decide⟩ (by decide) (![⟨240471, by decide⟩,⟨240557, by decide⟩,⟨240636, by decide⟩,⟨240653, by decide⟩]) unmarked_context_12_23066_240654 node_context_12_23066_240654
  intro a
  fin_cases a
  · exact context_13_92264_240471
  · exact context_13_92265_240557
  · exact context_13_92266_240636
  · exact context_13_92267_240653

theorem selected_cut_08592 : selected 8 ⟨240690, by decide⟩
    (prefixPartial 13 92268) = some ⟨13, 2, 0, 240690, 92268, 2277, 16384⟩ := by
  decide +kernel

theorem context_13_92268_240690 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92268 ⟨240690, by decide⟩ :=
  accepted_of_selected 13 92268 ⟨240690, by decide⟩ ⟨13, 2, 0, 240690, 92268, 2277, 16384⟩
    (by decide) selected_cut_08592

theorem selected_cut_08593 : selected 8 ⟨240739, by decide⟩
    (prefixPartial 13 92269) = some ⟨13, 2, 0, 240739, 92269, 3137, 16384⟩ := by
  decide +kernel

theorem context_13_92269_240739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92269 ⟨240739, by decide⟩ :=
  accepted_of_selected 13 92269 ⟨240739, by decide⟩ ⟨13, 2, 0, 240739, 92269, 3137, 16384⟩
    (by decide) selected_cut_08593

theorem selected_cut_08594 : selected 8 ⟨240763, by decide⟩
    (prefixPartial 13 92270) = some ⟨13, 2, 0, 240763, 92270, 1861, 16384⟩ := by
  decide +kernel

theorem context_13_92270_240763 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92270 ⟨240763, by decide⟩ :=
  accepted_of_selected 13 92270 ⟨240763, by decide⟩ ⟨13, 2, 0, 240763, 92270, 1861, 16384⟩
    (by decide) selected_cut_08594

theorem selected_cut_08595 : selected 8 ⟨240774, by decide⟩
    (prefixPartial 13 92271) = some ⟨13, 2, 0, 240774, 92271, 1005, 16384⟩ := by
  decide +kernel

theorem context_13_92271_240774 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92271 ⟨240774, by decide⟩ :=
  accepted_of_selected 13 92271 ⟨240774, by decide⟩ ⟨13, 2, 0, 240774, 92271, 1005, 16384⟩
    (by decide) selected_cut_08595

theorem unmarked_context_12_23067_240775 : frontier 9 ⟨240775, by decide⟩
    (prefixCache 12 23067) (prefixPartial 12 23067) = false := by
  decide +kernel

theorem node_context_12_23067_240775 : EJMOriginalGlobalDAGData.nodes 9 ⟨240775, by decide⟩ =
    .split (coordinate 12) (![⟨240690, by decide⟩,⟨240739, by decide⟩,⟨240763, by decide⟩,⟨240774, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23067_240775 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23067 ⟨240775, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23067
    ⟨240775, by decide⟩ (by decide) (![⟨240690, by decide⟩,⟨240739, by decide⟩,⟨240763, by decide⟩,⟨240774, by decide⟩]) unmarked_context_12_23067_240775 node_context_12_23067_240775
  intro a
  fin_cases a
  · exact context_13_92268_240690
  · exact context_13_92269_240739
  · exact context_13_92270_240763
  · exact context_13_92271_240774

theorem unmarked_context_11_5766_240776 : frontier 10 ⟨240776, by decide⟩
    (prefixCache 11 5766) (prefixPartial 11 5766) = false := by
  decide +kernel

theorem node_context_11_5766_240776 : EJMOriginalGlobalDAGData.nodes 10 ⟨240776, by decide⟩ =
    .split (coordinate 11) (![⟨240318, by decide⟩,⟨240423, by decide⟩,⟨240654, by decide⟩,⟨240775, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5766_240776 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5766 ⟨240776, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5766
    ⟨240776, by decide⟩ (by decide) (![⟨240318, by decide⟩,⟨240423, by decide⟩,⟨240654, by decide⟩,⟨240775, by decide⟩]) unmarked_context_11_5766_240776 node_context_11_5766_240776
  intro a
  fin_cases a
  · exact context_12_23064_240318
  · exact context_12_23065_240423
  · exact context_12_23066_240654
  · exact context_12_23067_240775

theorem selected_cut_08596 : selected 8 ⟨240801, by decide⟩
    (prefixPartial 13 92272) = some ⟨13, 2, 0, 240801, 92272, 1565, 16384⟩ := by
  decide +kernel

theorem context_13_92272_240801 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92272 ⟨240801, by decide⟩ :=
  accepted_of_selected 13 92272 ⟨240801, by decide⟩ ⟨13, 2, 0, 240801, 92272, 1565, 16384⟩
    (by decide) selected_cut_08596

theorem selected_cut_08597 : selected 8 ⟨240846, by decide⟩
    (prefixPartial 13 92273) = some ⟨13, 2, 0, 240846, 92273, 2913, 16384⟩ := by
  decide +kernel

theorem context_13_92273_240846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92273 ⟨240846, by decide⟩ :=
  accepted_of_selected 13 92273 ⟨240846, by decide⟩ ⟨13, 2, 0, 240846, 92273, 2913, 16384⟩
    (by decide) selected_cut_08597

theorem selected_cut_08598 : selected 8 ⟨240868, by decide⟩
    (prefixPartial 13 92274) = some ⟨13, 2, 0, 240868, 92274, 1473, 16384⟩ := by
  decide +kernel

theorem context_13_92274_240868 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92274 ⟨240868, by decide⟩ :=
  accepted_of_selected 13 92274 ⟨240868, by decide⟩ ⟨13, 2, 0, 240868, 92274, 1473, 16384⟩
    (by decide) selected_cut_08598

theorem selected_cut_08599 : selected 8 ⟨240883, by decide⟩
    (prefixPartial 13 92275) = some ⟨13, 2, 0, 240883, 92275, 973, 16384⟩ := by
  decide +kernel

theorem context_13_92275_240883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92275 ⟨240883, by decide⟩ :=
  accepted_of_selected 13 92275 ⟨240883, by decide⟩ ⟨13, 2, 0, 240883, 92275, 973, 16384⟩
    (by decide) selected_cut_08599

theorem unmarked_context_12_23068_240884 : frontier 9 ⟨240884, by decide⟩
    (prefixCache 12 23068) (prefixPartial 12 23068) = false := by
  decide +kernel

theorem node_context_12_23068_240884 : EJMOriginalGlobalDAGData.nodes 9 ⟨240884, by decide⟩ =
    .split (coordinate 12) (![⟨240801, by decide⟩,⟨240846, by decide⟩,⟨240868, by decide⟩,⟨240883, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23068_240884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23068 ⟨240884, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23068
    ⟨240884, by decide⟩ (by decide) (![⟨240801, by decide⟩,⟨240846, by decide⟩,⟨240868, by decide⟩,⟨240883, by decide⟩]) unmarked_context_12_23068_240884 node_context_12_23068_240884
  intro a
  fin_cases a
  · exact context_13_92272_240801
  · exact context_13_92273_240846
  · exact context_13_92274_240868
  · exact context_13_92275_240883

theorem selected_cut_08600 : selected 8 ⟨240918, by decide⟩
    (prefixPartial 13 92276) = some ⟨13, 2, 0, 240918, 92276, 1741, 16384⟩ := by
  decide +kernel

theorem context_13_92276_240918 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92276 ⟨240918, by decide⟩ :=
  accepted_of_selected 13 92276 ⟨240918, by decide⟩ ⟨13, 2, 0, 240918, 92276, 1741, 16384⟩
    (by decide) selected_cut_08600

theorem selected_cut_08601 : selected 8 ⟨240964, by decide⟩
    (prefixPartial 13 92277) = some ⟨13, 2, 0, 240964, 92277, 2537, 16384⟩ := by
  decide +kernel

theorem context_13_92277_240964 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92277 ⟨240964, by decide⟩ :=
  accepted_of_selected 13 92277 ⟨240964, by decide⟩ ⟨13, 2, 0, 240964, 92277, 2537, 16384⟩
    (by decide) selected_cut_08601

theorem selected_cut_08602 : selected 8 ⟨240987, by decide⟩
    (prefixPartial 13 92278) = some ⟨13, 2, 0, 240987, 92278, 1557, 16384⟩ := by
  decide +kernel

theorem context_13_92278_240987 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92278 ⟨240987, by decide⟩ :=
  accepted_of_selected 13 92278 ⟨240987, by decide⟩ ⟨13, 2, 0, 240987, 92278, 1557, 16384⟩
    (by decide) selected_cut_08602

theorem selected_cut_08603 : selected 8 ⟨240998, by decide⟩
    (prefixPartial 13 92279) = some ⟨13, 2, 0, 240998, 92279, 877, 16384⟩ := by
  decide +kernel

theorem context_13_92279_240998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92279 ⟨240998, by decide⟩ :=
  accepted_of_selected 13 92279 ⟨240998, by decide⟩ ⟨13, 2, 0, 240998, 92279, 877, 16384⟩
    (by decide) selected_cut_08603

theorem unmarked_context_12_23069_240999 : frontier 9 ⟨240999, by decide⟩
    (prefixCache 12 23069) (prefixPartial 12 23069) = false := by
  decide +kernel

theorem node_context_12_23069_240999 : EJMOriginalGlobalDAGData.nodes 9 ⟨240999, by decide⟩ =
    .split (coordinate 12) (![⟨240918, by decide⟩,⟨240964, by decide⟩,⟨240987, by decide⟩,⟨240998, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23069_240999 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23069 ⟨240999, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23069
    ⟨240999, by decide⟩ (by decide) (![⟨240918, by decide⟩,⟨240964, by decide⟩,⟨240987, by decide⟩,⟨240998, by decide⟩]) unmarked_context_12_23069_240999 node_context_12_23069_240999
  intro a
  fin_cases a
  · exact context_13_92276_240918
  · exact context_13_92277_240964
  · exact context_13_92278_240987
  · exact context_13_92279_240998

theorem selected_cut_08604 : selected 8 ⟨241031, by decide⟩
    (prefixPartial 13 92280) = some ⟨13, 2, 0, 241031, 92280, 1857, 16384⟩ := by
  decide +kernel

theorem context_13_92280_241031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92280 ⟨241031, by decide⟩ :=
  accepted_of_selected 13 92280 ⟨241031, by decide⟩ ⟨13, 2, 0, 241031, 92280, 1857, 16384⟩
    (by decide) selected_cut_08604

theorem selected_cut_08605 : selected 8 ⟨241084, by decide⟩
    (prefixPartial 13 92281) = some ⟨13, 2, 0, 241084, 92281, 3101, 16384⟩ := by
  decide +kernel

theorem context_13_92281_241084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92281 ⟨241084, by decide⟩ :=
  accepted_of_selected 13 92281 ⟨241084, by decide⟩ ⟨13, 2, 0, 241084, 92281, 3101, 16384⟩
    (by decide) selected_cut_08605

theorem selected_cut_08606 : selected 8 ⟨241110, by decide⟩
    (prefixPartial 13 92282) = some ⟨13, 2, 0, 241110, 92282, 1757, 16384⟩ := by
  decide +kernel

theorem context_13_92282_241110 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92282 ⟨241110, by decide⟩ :=
  accepted_of_selected 13 92282 ⟨241110, by decide⟩ ⟨13, 2, 0, 241110, 92282, 1757, 16384⟩
    (by decide) selected_cut_08606

theorem selected_cut_08607 : selected 8 ⟨241122, by decide⟩
    (prefixPartial 13 92283) = some ⟨13, 2, 0, 241122, 92283, 897, 16384⟩ := by
  decide +kernel

theorem context_13_92283_241122 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92283 ⟨241122, by decide⟩ :=
  accepted_of_selected 13 92283 ⟨241122, by decide⟩ ⟨13, 2, 0, 241122, 92283, 897, 16384⟩
    (by decide) selected_cut_08607

theorem unmarked_context_12_23070_241123 : frontier 9 ⟨241123, by decide⟩
    (prefixCache 12 23070) (prefixPartial 12 23070) = false := by
  decide +kernel

theorem node_context_12_23070_241123 : EJMOriginalGlobalDAGData.nodes 9 ⟨241123, by decide⟩ =
    .split (coordinate 12) (![⟨241031, by decide⟩,⟨241084, by decide⟩,⟨241110, by decide⟩,⟨241122, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23070_241123 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23070 ⟨241123, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23070
    ⟨241123, by decide⟩ (by decide) (![⟨241031, by decide⟩,⟨241084, by decide⟩,⟨241110, by decide⟩,⟨241122, by decide⟩]) unmarked_context_12_23070_241123 node_context_12_23070_241123
  intro a
  fin_cases a
  · exact context_13_92280_241031
  · exact context_13_92281_241084
  · exact context_13_92282_241110
  · exact context_13_92283_241122

theorem selected_cut_08608 : selected 8 ⟨241160, by decide⟩
    (prefixPartial 13 92284) = some ⟨13, 2, 0, 241160, 92284, 2077, 16384⟩ := by
  decide +kernel

theorem context_13_92284_241160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92284 ⟨241160, by decide⟩ :=
  accepted_of_selected 13 92284 ⟨241160, by decide⟩ ⟨13, 2, 0, 241160, 92284, 2077, 16384⟩
    (by decide) selected_cut_08608

theorem selected_cut_08609 : selected 8 ⟨241218, by decide⟩
    (prefixPartial 13 92285) = some ⟨13, 2, 0, 241218, 92285, 3165, 16384⟩ := by
  decide +kernel

theorem context_13_92285_241218 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92285 ⟨241218, by decide⟩ :=
  accepted_of_selected 13 92285 ⟨241218, by decide⟩ ⟨13, 2, 0, 241218, 92285, 3165, 16384⟩
    (by decide) selected_cut_08609

theorem selected_cut_08610 : selected 8 ⟨241241, by decide⟩
    (prefixPartial 13 92286) = some ⟨13, 2, 0, 241241, 92286, 1721, 16384⟩ := by
  decide +kernel

theorem context_13_92286_241241 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92286 ⟨241241, by decide⟩ :=
  accepted_of_selected 13 92286 ⟨241241, by decide⟩ ⟨13, 2, 0, 241241, 92286, 1721, 16384⟩
    (by decide) selected_cut_08610

theorem selected_cut_08611 : selected 8 ⟨241251, by decide⟩
    (prefixPartial 13 92287) = some ⟨13, 2, 0, 241251, 92287, 1053, 16384⟩ := by
  decide +kernel

theorem context_13_92287_241251 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92287 ⟨241251, by decide⟩ :=
  accepted_of_selected 13 92287 ⟨241251, by decide⟩ ⟨13, 2, 0, 241251, 92287, 1053, 16384⟩
    (by decide) selected_cut_08611

theorem unmarked_context_12_23071_241252 : frontier 9 ⟨241252, by decide⟩
    (prefixCache 12 23071) (prefixPartial 12 23071) = false := by
  decide +kernel

theorem node_context_12_23071_241252 : EJMOriginalGlobalDAGData.nodes 9 ⟨241252, by decide⟩ =
    .split (coordinate 12) (![⟨241160, by decide⟩,⟨241218, by decide⟩,⟨241241, by decide⟩,⟨241251, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23071_241252 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23071 ⟨241252, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23071
    ⟨241252, by decide⟩ (by decide) (![⟨241160, by decide⟩,⟨241218, by decide⟩,⟨241241, by decide⟩,⟨241251, by decide⟩]) unmarked_context_12_23071_241252 node_context_12_23071_241252
  intro a
  fin_cases a
  · exact context_13_92284_241160
  · exact context_13_92285_241218
  · exact context_13_92286_241241
  · exact context_13_92287_241251

theorem unmarked_context_11_5767_241253 : frontier 10 ⟨241253, by decide⟩
    (prefixCache 11 5767) (prefixPartial 11 5767) = false := by
  decide +kernel

theorem node_context_11_5767_241253 : EJMOriginalGlobalDAGData.nodes 10 ⟨241253, by decide⟩ =
    .split (coordinate 11) (![⟨240884, by decide⟩,⟨240999, by decide⟩,⟨241123, by decide⟩,⟨241252, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5767_241253 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5767 ⟨241253, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5767
    ⟨241253, by decide⟩ (by decide) (![⟨240884, by decide⟩,⟨240999, by decide⟩,⟨241123, by decide⟩,⟨241252, by decide⟩]) unmarked_context_11_5767_241253 node_context_11_5767_241253
  intro a
  fin_cases a
  · exact context_12_23068_240884
  · exact context_12_23069_240999
  · exact context_12_23070_241123
  · exact context_12_23071_241252

theorem unmarked_context_10_1441_241254 : frontier 11 ⟨241254, by decide⟩
    (prefixCache 10 1441) (prefixPartial 10 1441) = false := by
  decide +kernel

theorem node_context_10_1441_241254 : EJMOriginalGlobalDAGData.nodes 11 ⟨241254, by decide⟩ =
    .split (coordinate 10) (![⟨239804, by decide⟩,⟨240231, by decide⟩,⟨240776, by decide⟩,⟨241253, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1441_241254 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1441 ⟨241254, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1441
    ⟨241254, by decide⟩ (by decide) (![⟨239804, by decide⟩,⟨240231, by decide⟩,⟨240776, by decide⟩,⟨241253, by decide⟩]) unmarked_context_10_1441_241254 node_context_10_1441_241254
  intro a
  fin_cases a
  · exact context_11_5764_239804
  · exact context_11_5765_240231
  · exact context_11_5766_240776
  · exact context_11_5767_241253

theorem selected_cut_08612 : selected 8 ⟨241272, by decide⟩
    (prefixPartial 13 92288) = some ⟨13, 2, 0, 241272, 92288, 1345, 16384⟩ := by
  decide +kernel

theorem context_13_92288_241272 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92288 ⟨241272, by decide⟩ :=
  accepted_of_selected 13 92288 ⟨241272, by decide⟩ ⟨13, 2, 0, 241272, 92288, 1345, 16384⟩
    (by decide) selected_cut_08612

theorem selected_cut_08613 : selected 8 ⟨241301, by decide⟩
    (prefixPartial 13 92289) = some ⟨13, 2, 0, 241301, 92289, 2533, 16384⟩ := by
  decide +kernel

theorem context_13_92289_241301 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92289 ⟨241301, by decide⟩ :=
  accepted_of_selected 13 92289 ⟨241301, by decide⟩ ⟨13, 2, 0, 241301, 92289, 2533, 16384⟩
    (by decide) selected_cut_08613

theorem selected_cut_08614 : selected 8 ⟨241321, by decide⟩
    (prefixPartial 13 92290) = some ⟨13, 2, 0, 241321, 92290, 1529, 16384⟩ := by
  decide +kernel

theorem context_13_92290_241321 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92290 ⟨241321, by decide⟩ :=
  accepted_of_selected 13 92290 ⟨241321, by decide⟩ ⟨13, 2, 0, 241321, 92290, 1529, 16384⟩
    (by decide) selected_cut_08614

theorem selected_cut_08615 : selected 8 ⟨241330, by decide⟩
    (prefixPartial 13 92291) = some ⟨13, 2, 0, 241330, 92291, 797, 16384⟩ := by
  decide +kernel

theorem context_13_92291_241330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92291 ⟨241330, by decide⟩ :=
  accepted_of_selected 13 92291 ⟨241330, by decide⟩ ⟨13, 2, 0, 241330, 92291, 797, 16384⟩
    (by decide) selected_cut_08615

theorem unmarked_context_12_23072_241331 : frontier 9 ⟨241331, by decide⟩
    (prefixCache 12 23072) (prefixPartial 12 23072) = false := by
  decide +kernel

theorem node_context_12_23072_241331 : EJMOriginalGlobalDAGData.nodes 9 ⟨241331, by decide⟩ =
    .split (coordinate 12) (![⟨241272, by decide⟩,⟨241301, by decide⟩,⟨241321, by decide⟩,⟨241330, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23072_241331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23072 ⟨241331, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23072
    ⟨241331, by decide⟩ (by decide) (![⟨241272, by decide⟩,⟨241301, by decide⟩,⟨241321, by decide⟩,⟨241330, by decide⟩]) unmarked_context_12_23072_241331 node_context_12_23072_241331
  intro a
  fin_cases a
  · exact context_13_92288_241272
  · exact context_13_92289_241301
  · exact context_13_92290_241321
  · exact context_13_92291_241330

theorem selected_cut_08616 : selected 8 ⟨241346, by decide⟩
    (prefixPartial 13 92292) = some ⟨13, 2, 0, 241346, 92292, 1393, 16384⟩ := by
  decide +kernel

theorem context_13_92292_241346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92292 ⟨241346, by decide⟩ :=
  accepted_of_selected 13 92292 ⟨241346, by decide⟩ ⟨13, 2, 0, 241346, 92292, 1393, 16384⟩
    (by decide) selected_cut_08616

theorem selected_cut_08617 : selected 8 ⟨241377, by decide⟩
    (prefixPartial 13 92293) = some ⟨13, 2, 0, 241377, 92293, 2373, 16384⟩ := by
  decide +kernel

theorem context_13_92293_241377 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92293 ⟨241377, by decide⟩ :=
  accepted_of_selected 13 92293 ⟨241377, by decide⟩ ⟨13, 2, 0, 241377, 92293, 2373, 16384⟩
    (by decide) selected_cut_08617

theorem selected_cut_08618 : selected 8 ⟨241395, by decide⟩
    (prefixPartial 13 92294) = some ⟨13, 2, 0, 241395, 92294, 1429, 16384⟩ := by
  decide +kernel

theorem context_13_92294_241395 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92294 ⟨241395, by decide⟩ :=
  accepted_of_selected 13 92294 ⟨241395, by decide⟩ ⟨13, 2, 0, 241395, 92294, 1429, 16384⟩
    (by decide) selected_cut_08618

theorem selected_cut_08619 : selected 8 ⟨241403, by decide⟩
    (prefixPartial 13 92295) = some ⟨13, 2, 0, 241403, 92295, 849, 16384⟩ := by
  decide +kernel

theorem context_13_92295_241403 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92295 ⟨241403, by decide⟩ :=
  accepted_of_selected 13 92295 ⟨241403, by decide⟩ ⟨13, 2, 0, 241403, 92295, 849, 16384⟩
    (by decide) selected_cut_08619

theorem unmarked_context_12_23073_241404 : frontier 9 ⟨241404, by decide⟩
    (prefixCache 12 23073) (prefixPartial 12 23073) = false := by
  decide +kernel

theorem node_context_12_23073_241404 : EJMOriginalGlobalDAGData.nodes 9 ⟨241404, by decide⟩ =
    .split (coordinate 12) (![⟨241346, by decide⟩,⟨241377, by decide⟩,⟨241395, by decide⟩,⟨241403, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23073_241404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23073 ⟨241404, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23073
    ⟨241404, by decide⟩ (by decide) (![⟨241346, by decide⟩,⟨241377, by decide⟩,⟨241395, by decide⟩,⟨241403, by decide⟩]) unmarked_context_12_23073_241404 node_context_12_23073_241404
  intro a
  fin_cases a
  · exact context_13_92292_241346
  · exact context_13_92293_241377
  · exact context_13_92294_241395
  · exact context_13_92295_241403

theorem selected_cut_08620 : selected 8 ⟨241416, by decide⟩
    (prefixPartial 13 92296) = some ⟨13, 2, 0, 241416, 92296, 1585, 16384⟩ := by
  decide +kernel

theorem context_13_92296_241416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92296 ⟨241416, by decide⟩ :=
  accepted_of_selected 13 92296 ⟨241416, by decide⟩ ⟨13, 2, 0, 241416, 92296, 1585, 16384⟩
    (by decide) selected_cut_08620

theorem selected_cut_08621 : selected 8 ⟨241446, by decide⟩
    (prefixPartial 13 92297) = some ⟨13, 2, 0, 241446, 92297, 2685, 16384⟩ := by
  decide +kernel

theorem context_13_92297_241446 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92297 ⟨241446, by decide⟩ :=
  accepted_of_selected 13 92297 ⟨241446, by decide⟩ ⟨13, 2, 0, 241446, 92297, 2685, 16384⟩
    (by decide) selected_cut_08621

theorem selected_cut_08622 : selected 8 ⟨241465, by decide⟩
    (prefixPartial 13 92298) = some ⟨13, 2, 0, 241465, 92298, 1429, 16384⟩ := by
  decide +kernel

theorem context_13_92298_241465 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92298 ⟨241465, by decide⟩ :=
  accepted_of_selected 13 92298 ⟨241465, by decide⟩ ⟨13, 2, 0, 241465, 92298, 1429, 16384⟩
    (by decide) selected_cut_08622

theorem selected_cut_08623 : selected 8 ⟨241474, by decide⟩
    (prefixPartial 13 92299) = some ⟨13, 2, 0, 241474, 92299, 921, 16384⟩ := by
  decide +kernel

theorem context_13_92299_241474 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92299 ⟨241474, by decide⟩ :=
  accepted_of_selected 13 92299 ⟨241474, by decide⟩ ⟨13, 2, 0, 241474, 92299, 921, 16384⟩
    (by decide) selected_cut_08623

theorem unmarked_context_12_23074_241475 : frontier 9 ⟨241475, by decide⟩
    (prefixCache 12 23074) (prefixPartial 12 23074) = false := by
  decide +kernel

theorem node_context_12_23074_241475 : EJMOriginalGlobalDAGData.nodes 9 ⟨241475, by decide⟩ =
    .split (coordinate 12) (![⟨241416, by decide⟩,⟨241446, by decide⟩,⟨241465, by decide⟩,⟨241474, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23074_241475 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23074 ⟨241475, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23074
    ⟨241475, by decide⟩ (by decide) (![⟨241416, by decide⟩,⟨241446, by decide⟩,⟨241465, by decide⟩,⟨241474, by decide⟩]) unmarked_context_12_23074_241475 node_context_12_23074_241475
  intro a
  fin_cases a
  · exact context_13_92296_241416
  · exact context_13_92297_241446
  · exact context_13_92298_241465
  · exact context_13_92299_241474

theorem selected_cut_08624 : selected 8 ⟨241492, by decide⟩
    (prefixPartial 13 92300) = some ⟨13, 2, 0, 241492, 92300, 1657, 16384⟩ := by
  decide +kernel

theorem context_13_92300_241492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92300 ⟨241492, by decide⟩ :=
  accepted_of_selected 13 92300 ⟨241492, by decide⟩ ⟨13, 2, 0, 241492, 92300, 1657, 16384⟩
    (by decide) selected_cut_08624

theorem selected_cut_08625 : selected 8 ⟨241536, by decide⟩
    (prefixPartial 13 92301) = some ⟨13, 2, 0, 241536, 92301, 2921, 16384⟩ := by
  decide +kernel

theorem context_13_92301_241536 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92301 ⟨241536, by decide⟩ :=
  accepted_of_selected 13 92301 ⟨241536, by decide⟩ ⟨13, 2, 0, 241536, 92301, 2921, 16384⟩
    (by decide) selected_cut_08625

theorem selected_cut_08626 : selected 8 ⟨241556, by decide⟩
    (prefixPartial 13 92302) = some ⟨13, 2, 0, 241556, 92302, 1617, 16384⟩ := by
  decide +kernel

theorem context_13_92302_241556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92302 ⟨241556, by decide⟩ :=
  accepted_of_selected 13 92302 ⟨241556, by decide⟩ ⟨13, 2, 0, 241556, 92302, 1617, 16384⟩
    (by decide) selected_cut_08626

theorem selected_cut_08627 : selected 8 ⟨241562, by decide⟩
    (prefixPartial 13 92303) = some ⟨13, 2, 0, 241562, 92303, 1013, 16384⟩ := by
  decide +kernel

theorem context_13_92303_241562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92303 ⟨241562, by decide⟩ :=
  accepted_of_selected 13 92303 ⟨241562, by decide⟩ ⟨13, 2, 0, 241562, 92303, 1013, 16384⟩
    (by decide) selected_cut_08627

theorem unmarked_context_12_23075_241563 : frontier 9 ⟨241563, by decide⟩
    (prefixCache 12 23075) (prefixPartial 12 23075) = false := by
  decide +kernel

theorem node_context_12_23075_241563 : EJMOriginalGlobalDAGData.nodes 9 ⟨241563, by decide⟩ =
    .split (coordinate 12) (![⟨241492, by decide⟩,⟨241536, by decide⟩,⟨241556, by decide⟩,⟨241562, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23075_241563 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23075 ⟨241563, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23075
    ⟨241563, by decide⟩ (by decide) (![⟨241492, by decide⟩,⟨241536, by decide⟩,⟨241556, by decide⟩,⟨241562, by decide⟩]) unmarked_context_12_23075_241563 node_context_12_23075_241563
  intro a
  fin_cases a
  · exact context_13_92300_241492
  · exact context_13_92301_241536
  · exact context_13_92302_241556
  · exact context_13_92303_241562

theorem unmarked_context_11_5768_241564 : frontier 10 ⟨241564, by decide⟩
    (prefixCache 11 5768) (prefixPartial 11 5768) = false := by
  decide +kernel

theorem node_context_11_5768_241564 : EJMOriginalGlobalDAGData.nodes 10 ⟨241564, by decide⟩ =
    .split (coordinate 11) (![⟨241331, by decide⟩,⟨241404, by decide⟩,⟨241475, by decide⟩,⟨241563, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5768_241564 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5768 ⟨241564, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5768
    ⟨241564, by decide⟩ (by decide) (![⟨241331, by decide⟩,⟨241404, by decide⟩,⟨241475, by decide⟩,⟨241563, by decide⟩]) unmarked_context_11_5768_241564 node_context_11_5768_241564
  intro a
  fin_cases a
  · exact context_12_23072_241331
  · exact context_12_23073_241404
  · exact context_12_23074_241475
  · exact context_12_23075_241563

theorem selected_cut_08628 : selected 8 ⟨241579, by decide⟩
    (prefixPartial 13 92304) = some ⟨13, 2, 0, 241579, 92304, 1041, 16384⟩ := by
  decide +kernel

theorem context_13_92304_241579 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92304 ⟨241579, by decide⟩ :=
  accepted_of_selected 13 92304 ⟨241579, by decide⟩ ⟨13, 2, 0, 241579, 92304, 1041, 16384⟩
    (by decide) selected_cut_08628

theorem selected_cut_08629 : selected 8 ⟨241626, by decide⟩
    (prefixPartial 13 92305) = some ⟨13, 2, 0, 241626, 92305, 2969, 16384⟩ := by
  decide +kernel

theorem context_13_92305_241626 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92305 ⟨241626, by decide⟩ :=
  accepted_of_selected 13 92305 ⟨241626, by decide⟩ ⟨13, 2, 0, 241626, 92305, 2969, 16384⟩
    (by decide) selected_cut_08629

theorem selected_cut_08630 : selected 8 ⟨241645, by decide⟩
    (prefixPartial 13 92306) = some ⟨13, 2, 0, 241645, 92306, 1353, 16384⟩ := by
  decide +kernel

theorem context_13_92306_241645 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92306 ⟨241645, by decide⟩ :=
  accepted_of_selected 13 92306 ⟨241645, by decide⟩ ⟨13, 2, 0, 241645, 92306, 1353, 16384⟩
    (by decide) selected_cut_08630

theorem selected_cut_08631 : selected 8 ⟨241656, by decide⟩
    (prefixPartial 13 92307) = some ⟨13, 2, 0, 241656, 92307, 909, 16384⟩ := by
  decide +kernel

theorem context_13_92307_241656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92307 ⟨241656, by decide⟩ :=
  accepted_of_selected 13 92307 ⟨241656, by decide⟩ ⟨13, 2, 0, 241656, 92307, 909, 16384⟩
    (by decide) selected_cut_08631

theorem unmarked_context_12_23076_241657 : frontier 9 ⟨241657, by decide⟩
    (prefixCache 12 23076) (prefixPartial 12 23076) = false := by
  decide +kernel

theorem node_context_12_23076_241657 : EJMOriginalGlobalDAGData.nodes 9 ⟨241657, by decide⟩ =
    .split (coordinate 12) (![⟨241579, by decide⟩,⟨241626, by decide⟩,⟨241645, by decide⟩,⟨241656, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23076_241657 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23076 ⟨241657, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23076
    ⟨241657, by decide⟩ (by decide) (![⟨241579, by decide⟩,⟨241626, by decide⟩,⟨241645, by decide⟩,⟨241656, by decide⟩]) unmarked_context_12_23076_241657 node_context_12_23076_241657
  intro a
  fin_cases a
  · exact context_13_92304_241579
  · exact context_13_92305_241626
  · exact context_13_92306_241645
  · exact context_13_92307_241656

theorem selected_cut_08632 : selected 8 ⟨241670, by decide⟩
    (prefixPartial 13 92308) = some ⟨13, 2, 0, 241670, 92308, 973, 16384⟩ := by
  decide +kernel

theorem context_13_92308_241670 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92308 ⟨241670, by decide⟩ :=
  accepted_of_selected 13 92308 ⟨241670, by decide⟩ ⟨13, 2, 0, 241670, 92308, 973, 16384⟩
    (by decide) selected_cut_08632

theorem selected_cut_08633 : selected 8 ⟨241709, by decide⟩
    (prefixPartial 13 92309) = some ⟨13, 2, 0, 241709, 92309, 2405, 16384⟩ := by
  decide +kernel

theorem context_13_92309_241709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92309 ⟨241709, by decide⟩ :=
  accepted_of_selected 13 92309 ⟨241709, by decide⟩ ⟨13, 2, 0, 241709, 92309, 2405, 16384⟩
    (by decide) selected_cut_08633

theorem selected_cut_08634 : selected 8 ⟨241728, by decide⟩
    (prefixPartial 13 92310) = some ⟨13, 2, 0, 241728, 92310, 1229, 16384⟩ := by
  decide +kernel

theorem context_13_92310_241728 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92310 ⟨241728, by decide⟩ :=
  accepted_of_selected 13 92310 ⟨241728, by decide⟩ ⟨13, 2, 0, 241728, 92310, 1229, 16384⟩
    (by decide) selected_cut_08634

theorem selected_cut_08635 : selected 8 ⟨241739, by decide⟩
    (prefixPartial 13 92311) = some ⟨13, 2, 0, 241739, 92311, 861, 16384⟩ := by
  decide +kernel

theorem context_13_92311_241739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92311 ⟨241739, by decide⟩ :=
  accepted_of_selected 13 92311 ⟨241739, by decide⟩ ⟨13, 2, 0, 241739, 92311, 861, 16384⟩
    (by decide) selected_cut_08635

theorem unmarked_context_12_23077_241740 : frontier 9 ⟨241740, by decide⟩
    (prefixCache 12 23077) (prefixPartial 12 23077) = false := by
  decide +kernel

theorem node_context_12_23077_241740 : EJMOriginalGlobalDAGData.nodes 9 ⟨241740, by decide⟩ =
    .split (coordinate 12) (![⟨241670, by decide⟩,⟨241709, by decide⟩,⟨241728, by decide⟩,⟨241739, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23077_241740 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23077 ⟨241740, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23077
    ⟨241740, by decide⟩ (by decide) (![⟨241670, by decide⟩,⟨241709, by decide⟩,⟨241728, by decide⟩,⟨241739, by decide⟩]) unmarked_context_12_23077_241740 node_context_12_23077_241740
  intro a
  fin_cases a
  · exact context_13_92308_241670
  · exact context_13_92309_241709
  · exact context_13_92310_241728
  · exact context_13_92311_241739

theorem selected_cut_08636 : selected 8 ⟨241752, by decide⟩
    (prefixPartial 13 92312) = some ⟨13, 2, 0, 241752, 92312, 1137, 16384⟩ := by
  decide +kernel

theorem context_13_92312_241752 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92312 ⟨241752, by decide⟩ :=
  accepted_of_selected 13 92312 ⟨241752, by decide⟩ ⟨13, 2, 0, 241752, 92312, 1137, 16384⟩
    (by decide) selected_cut_08636

theorem selected_cut_08637 : selected 8 ⟨241791, by decide⟩
    (prefixPartial 13 92313) = some ⟨13, 2, 0, 241791, 92313, 2577, 16384⟩ := by
  decide +kernel

theorem context_13_92313_241791 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92313 ⟨241791, by decide⟩ :=
  accepted_of_selected 13 92313 ⟨241791, by decide⟩ ⟨13, 2, 0, 241791, 92313, 2577, 16384⟩
    (by decide) selected_cut_08637

theorem selected_cut_08638 : selected 8 ⟨241808, by decide⟩
    (prefixPartial 13 92314) = some ⟨13, 2, 0, 241808, 92314, 1173, 16384⟩ := by
  decide +kernel

theorem context_13_92314_241808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92314 ⟨241808, by decide⟩ :=
  accepted_of_selected 13 92314 ⟨241808, by decide⟩ ⟨13, 2, 0, 241808, 92314, 1173, 16384⟩
    (by decide) selected_cut_08638

theorem selected_cut_08639 : selected 8 ⟨241815, by decide⟩
    (prefixPartial 13 92315) = some ⟨13, 2, 0, 241815, 92315, 965, 16384⟩ := by
  decide +kernel

theorem context_13_92315_241815 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92315 ⟨241815, by decide⟩ :=
  accepted_of_selected 13 92315 ⟨241815, by decide⟩ ⟨13, 2, 0, 241815, 92315, 965, 16384⟩
    (by decide) selected_cut_08639

theorem unmarked_context_12_23078_241816 : frontier 9 ⟨241816, by decide⟩
    (prefixCache 12 23078) (prefixPartial 12 23078) = false := by
  decide +kernel

theorem node_context_12_23078_241816 : EJMOriginalGlobalDAGData.nodes 9 ⟨241816, by decide⟩ =
    .split (coordinate 12) (![⟨241752, by decide⟩,⟨241791, by decide⟩,⟨241808, by decide⟩,⟨241815, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23078_241816 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23078 ⟨241816, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23078
    ⟨241816, by decide⟩ (by decide) (![⟨241752, by decide⟩,⟨241791, by decide⟩,⟨241808, by decide⟩,⟨241815, by decide⟩]) unmarked_context_12_23078_241816 node_context_12_23078_241816
  intro a
  fin_cases a
  · exact context_13_92312_241752
  · exact context_13_92313_241791
  · exact context_13_92314_241808
  · exact context_13_92315_241815

theorem selected_cut_08640 : selected 8 ⟨241834, by decide⟩
    (prefixPartial 13 92316) = some ⟨13, 2, 0, 241834, 92316, 1249, 16384⟩ := by
  decide +kernel

theorem context_13_92316_241834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92316 ⟨241834, by decide⟩ :=
  accepted_of_selected 13 92316 ⟨241834, by decide⟩ ⟨13, 2, 0, 241834, 92316, 1249, 16384⟩
    (by decide) selected_cut_08640

theorem selected_cut_08641 : selected 8 ⟨241879, by decide⟩
    (prefixPartial 13 92317) = some ⟨13, 2, 0, 241879, 92317, 2745, 16384⟩ := by
  decide +kernel

theorem context_13_92317_241879 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92317 ⟨241879, by decide⟩ :=
  accepted_of_selected 13 92317 ⟨241879, by decide⟩ ⟨13, 2, 0, 241879, 92317, 2745, 16384⟩
    (by decide) selected_cut_08641

theorem selected_cut_08642 : selected 8 ⟨241900, by decide⟩
    (prefixPartial 13 92318) = some ⟨13, 2, 0, 241900, 92318, 1569, 16384⟩ := by
  decide +kernel

theorem context_13_92318_241900 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92318 ⟨241900, by decide⟩ :=
  accepted_of_selected 13 92318 ⟨241900, by decide⟩ ⟨13, 2, 0, 241900, 92318, 1569, 16384⟩
    (by decide) selected_cut_08642

theorem selected_cut_08643 : selected 8 ⟨241908, by decide⟩
    (prefixPartial 13 92319) = some ⟨13, 2, 0, 241908, 92319, 985, 16384⟩ := by
  decide +kernel

theorem context_13_92319_241908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92319 ⟨241908, by decide⟩ :=
  accepted_of_selected 13 92319 ⟨241908, by decide⟩ ⟨13, 2, 0, 241908, 92319, 985, 16384⟩
    (by decide) selected_cut_08643

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
