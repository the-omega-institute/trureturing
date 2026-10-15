/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover181
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_17474 : selected 9 ⟨444699, by decide⟩
    (prefixPartial 12 70178) = some ⟨12, 2, 0, 444699, 70178, 3569, 65536⟩ := by
  decide +kernel

theorem context_12_70178_444699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70178 ⟨444699, by decide⟩ :=
  accepted_of_selected 12 70178 ⟨444699, by decide⟩ ⟨12, 2, 0, 444699, 70178, 3569, 65536⟩
    (by decide) selected_cut_17474

theorem selected_cut_17475 : selected 8 ⟨444720, by decide⟩
    (prefixPartial 13 280716) = some ⟨13, 2, 0, 444720, 280716, 917, 16384⟩ := by
  decide +kernel

theorem context_13_280716_444720 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280716 ⟨444720, by decide⟩ :=
  accepted_of_selected 13 280716 ⟨444720, by decide⟩ ⟨13, 2, 0, 444720, 280716, 917, 16384⟩
    (by decide) selected_cut_17475

theorem selected_cut_17476 : selected 8 ⟨444737, by decide⟩
    (prefixPartial 13 280717) = some ⟨13, 2, 0, 444737, 280717, 1533, 16384⟩ := by
  decide +kernel

theorem context_13_280717_444737 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280717 ⟨444737, by decide⟩ :=
  accepted_of_selected 13 280717 ⟨444737, by decide⟩ ⟨13, 2, 0, 444737, 280717, 1533, 16384⟩
    (by decide) selected_cut_17476

theorem selected_cut_17477 : selected 8 ⟨444757, by decide⟩
    (prefixPartial 13 280718) = some ⟨13, 2, 0, 444757, 280718, 1253, 16384⟩ := by
  decide +kernel

theorem context_13_280718_444757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280718 ⟨444757, by decide⟩ :=
  accepted_of_selected 13 280718 ⟨444757, by decide⟩ ⟨13, 2, 0, 444757, 280718, 1253, 16384⟩
    (by decide) selected_cut_17477

theorem selected_cut_17478 : selected 8 ⟨444766, by decide⟩
    (prefixPartial 13 280719) = some ⟨13, 2, 0, 444766, 280719, 661, 16384⟩ := by
  decide +kernel

theorem context_13_280719_444766 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280719 ⟨444766, by decide⟩ :=
  accepted_of_selected 13 280719 ⟨444766, by decide⟩ ⟨13, 2, 0, 444766, 280719, 661, 16384⟩
    (by decide) selected_cut_17478

theorem unmarked_context_12_70179_444767 : frontier 9 ⟨444767, by decide⟩
    (prefixCache 12 70179) (prefixPartial 12 70179) = false := by
  decide +kernel

theorem node_context_12_70179_444767 : EJMOriginalGlobalDAGData.nodes 9 ⟨444767, by decide⟩ =
    .split (coordinate 12) (![⟨444720, by decide⟩,⟨444737, by decide⟩,⟨444757, by decide⟩,⟨444766, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70179_444767 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70179 ⟨444767, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70179
    ⟨444767, by decide⟩ (by decide) (![⟨444720, by decide⟩,⟨444737, by decide⟩,⟨444757, by decide⟩,⟨444766, by decide⟩]) unmarked_context_12_70179_444767 node_context_12_70179_444767
  intro a
  fin_cases a
  · exact context_13_280716_444720
  · exact context_13_280717_444737
  · exact context_13_280718_444757
  · exact context_13_280719_444766

theorem unmarked_context_11_17544_444768 : frontier 10 ⟨444768, by decide⟩
    (prefixCache 11 17544) (prefixPartial 11 17544) = false := by
  decide +kernel

theorem node_context_11_17544_444768 : EJMOriginalGlobalDAGData.nodes 10 ⟨444768, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨444644, by decide⟩,⟨444699, by decide⟩,⟨444767, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17544_444768 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17544 ⟨444768, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17544
    ⟨444768, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨444644, by decide⟩,⟨444699, by decide⟩,⟨444767, by decide⟩]) unmarked_context_11_17544_444768 node_context_11_17544_444768
  intro a
  fin_cases a
  · exact context_12_70176_435790
  · exact context_12_70177_444644
  · exact context_12_70178_444699
  · exact context_12_70179_444767

theorem selected_cut_17479 : selected 8 ⟨444802, by decide⟩
    (prefixPartial 13 280720) = some ⟨13, 2, 0, 444802, 280720, 1293, 16384⟩ := by
  decide +kernel

theorem context_13_280720_444802 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280720 ⟨444802, by decide⟩ :=
  accepted_of_selected 13 280720 ⟨444802, by decide⟩ ⟨13, 2, 0, 444802, 280720, 1293, 16384⟩
    (by decide) selected_cut_17479

theorem selected_cut_17480 : selected 8 ⟨444845, by decide⟩
    (prefixPartial 13 280721) = some ⟨13, 2, 0, 444845, 280721, 2365, 16384⟩ := by
  decide +kernel

theorem context_13_280721_444845 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280721 ⟨444845, by decide⟩ :=
  accepted_of_selected 13 280721 ⟨444845, by decide⟩ ⟨13, 2, 0, 444845, 280721, 2365, 16384⟩
    (by decide) selected_cut_17480

theorem selected_cut_17481 : selected 8 ⟨444877, by decide⟩
    (prefixPartial 13 280722) = some ⟨13, 2, 0, 444877, 280722, 2025, 16384⟩ := by
  decide +kernel

theorem context_13_280722_444877 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280722 ⟨444877, by decide⟩ :=
  accepted_of_selected 13 280722 ⟨444877, by decide⟩ ⟨13, 2, 0, 444877, 280722, 2025, 16384⟩
    (by decide) selected_cut_17481

theorem selected_cut_17482 : selected 8 ⟨444888, by decide⟩
    (prefixPartial 13 280723) = some ⟨13, 2, 0, 444888, 280723, 977, 16384⟩ := by
  decide +kernel

theorem context_13_280723_444888 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280723 ⟨444888, by decide⟩ :=
  accepted_of_selected 13 280723 ⟨444888, by decide⟩ ⟨13, 2, 0, 444888, 280723, 977, 16384⟩
    (by decide) selected_cut_17482

theorem unmarked_context_12_70180_444889 : frontier 9 ⟨444889, by decide⟩
    (prefixCache 12 70180) (prefixPartial 12 70180) = false := by
  decide +kernel

theorem node_context_12_70180_444889 : EJMOriginalGlobalDAGData.nodes 9 ⟨444889, by decide⟩ =
    .split (coordinate 12) (![⟨444802, by decide⟩,⟨444845, by decide⟩,⟨444877, by decide⟩,⟨444888, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70180_444889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70180 ⟨444889, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70180
    ⟨444889, by decide⟩ (by decide) (![⟨444802, by decide⟩,⟨444845, by decide⟩,⟨444877, by decide⟩,⟨444888, by decide⟩]) unmarked_context_12_70180_444889 node_context_12_70180_444889
  intro a
  fin_cases a
  · exact context_13_280720_444802
  · exact context_13_280721_444845
  · exact context_13_280722_444877
  · exact context_13_280723_444888

theorem selected_cut_17483 : selected 8 ⟨444915, by decide⟩
    (prefixPartial 13 280724) = some ⟨13, 2, 0, 444915, 280724, 1109, 16384⟩ := by
  decide +kernel

theorem context_13_280724_444915 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280724 ⟨444915, by decide⟩ :=
  accepted_of_selected 13 280724 ⟨444915, by decide⟩ ⟨13, 2, 0, 444915, 280724, 1109, 16384⟩
    (by decide) selected_cut_17483

theorem selected_cut_17484 : selected 8 ⟨444929, by decide⟩
    (prefixPartial 13 280725) = some ⟨13, 2, 0, 444929, 280725, 1113, 16384⟩ := by
  decide +kernel

theorem context_13_280725_444929 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280725 ⟨444929, by decide⟩ :=
  accepted_of_selected 13 280725 ⟨444929, by decide⟩ ⟨13, 2, 0, 444929, 280725, 1113, 16384⟩
    (by decide) selected_cut_17484

theorem selected_cut_17485 : selected 8 ⟨444948, by decide⟩
    (prefixPartial 13 280726) = some ⟨13, 2, 0, 444948, 280726, 1689, 16384⟩ := by
  decide +kernel

theorem context_13_280726_444948 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280726 ⟨444948, by decide⟩ :=
  accepted_of_selected 13 280726 ⟨444948, by decide⟩ ⟨13, 2, 0, 444948, 280726, 1689, 16384⟩
    (by decide) selected_cut_17485

theorem selected_cut_17486 : selected 8 ⟨444957, by decide⟩
    (prefixPartial 13 280727) = some ⟨13, 2, 0, 444957, 280727, 765, 16384⟩ := by
  decide +kernel

theorem context_13_280727_444957 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280727 ⟨444957, by decide⟩ :=
  accepted_of_selected 13 280727 ⟨444957, by decide⟩ ⟨13, 2, 0, 444957, 280727, 765, 16384⟩
    (by decide) selected_cut_17486

theorem unmarked_context_12_70181_444958 : frontier 9 ⟨444958, by decide⟩
    (prefixCache 12 70181) (prefixPartial 12 70181) = false := by
  decide +kernel

theorem node_context_12_70181_444958 : EJMOriginalGlobalDAGData.nodes 9 ⟨444958, by decide⟩ =
    .split (coordinate 12) (![⟨444915, by decide⟩,⟨444929, by decide⟩,⟨444948, by decide⟩,⟨444957, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70181_444958 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70181 ⟨444958, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70181
    ⟨444958, by decide⟩ (by decide) (![⟨444915, by decide⟩,⟨444929, by decide⟩,⟨444948, by decide⟩,⟨444957, by decide⟩]) unmarked_context_12_70181_444958 node_context_12_70181_444958
  intro a
  fin_cases a
  · exact context_13_280724_444915
  · exact context_13_280725_444929
  · exact context_13_280726_444948
  · exact context_13_280727_444957

theorem selected_cut_17487 : selected 9 ⟨445023, by decide⟩
    (prefixPartial 12 70182) = some ⟨12, 2, 0, 445023, 70182, 4041, 65536⟩ := by
  decide +kernel

theorem context_12_70182_445023 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70182 ⟨445023, by decide⟩ :=
  accepted_of_selected 12 70182 ⟨445023, by decide⟩ ⟨12, 2, 0, 445023, 70182, 4041, 65536⟩
    (by decide) selected_cut_17487

theorem selected_cut_17488 : selected 8 ⟨445044, by decide⟩
    (prefixPartial 13 280732) = some ⟨13, 2, 0, 445044, 280732, 949, 16384⟩ := by
  decide +kernel

theorem context_13_280732_445044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280732 ⟨445044, by decide⟩ :=
  accepted_of_selected 13 280732 ⟨445044, by decide⟩ ⟨13, 2, 0, 445044, 280732, 949, 16384⟩
    (by decide) selected_cut_17488

theorem selected_cut_17489 : selected 8 ⟨445062, by decide⟩
    (prefixPartial 13 280733) = some ⟨13, 2, 0, 445062, 280733, 1565, 16384⟩ := by
  decide +kernel

theorem context_13_280733_445062 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280733 ⟨445062, by decide⟩ :=
  accepted_of_selected 13 280733 ⟨445062, by decide⟩ ⟨13, 2, 0, 445062, 280733, 1565, 16384⟩
    (by decide) selected_cut_17489

theorem selected_cut_17490 : selected 8 ⟨445083, by decide⟩
    (prefixPartial 13 280734) = some ⟨13, 2, 0, 445083, 280734, 1513, 16384⟩ := by
  decide +kernel

theorem context_13_280734_445083 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280734 ⟨445083, by decide⟩ :=
  accepted_of_selected 13 280734 ⟨445083, by decide⟩ ⟨13, 2, 0, 445083, 280734, 1513, 16384⟩
    (by decide) selected_cut_17490

theorem selected_cut_17491 : selected 8 ⟨445089, by decide⟩
    (prefixPartial 13 280735) = some ⟨13, 2, 0, 445089, 280735, 677, 16384⟩ := by
  decide +kernel

theorem context_13_280735_445089 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280735 ⟨445089, by decide⟩ :=
  accepted_of_selected 13 280735 ⟨445089, by decide⟩ ⟨13, 2, 0, 445089, 280735, 677, 16384⟩
    (by decide) selected_cut_17491

theorem unmarked_context_12_70183_445090 : frontier 9 ⟨445090, by decide⟩
    (prefixCache 12 70183) (prefixPartial 12 70183) = false := by
  decide +kernel

theorem node_context_12_70183_445090 : EJMOriginalGlobalDAGData.nodes 9 ⟨445090, by decide⟩ =
    .split (coordinate 12) (![⟨445044, by decide⟩,⟨445062, by decide⟩,⟨445083, by decide⟩,⟨445089, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70183_445090 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70183 ⟨445090, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70183
    ⟨445090, by decide⟩ (by decide) (![⟨445044, by decide⟩,⟨445062, by decide⟩,⟨445083, by decide⟩,⟨445089, by decide⟩]) unmarked_context_12_70183_445090 node_context_12_70183_445090
  intro a
  fin_cases a
  · exact context_13_280732_445044
  · exact context_13_280733_445062
  · exact context_13_280734_445083
  · exact context_13_280735_445089

theorem unmarked_context_11_17545_445091 : frontier 10 ⟨445091, by decide⟩
    (prefixCache 11 17545) (prefixPartial 11 17545) = false := by
  decide +kernel

theorem node_context_11_17545_445091 : EJMOriginalGlobalDAGData.nodes 10 ⟨445091, by decide⟩ =
    .split (coordinate 11) (![⟨444889, by decide⟩,⟨444958, by decide⟩,⟨445023, by decide⟩,⟨445090, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17545_445091 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17545 ⟨445091, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17545
    ⟨445091, by decide⟩ (by decide) (![⟨444889, by decide⟩,⟨444958, by decide⟩,⟨445023, by decide⟩,⟨445090, by decide⟩]) unmarked_context_11_17545_445091 node_context_11_17545_445091
  intro a
  fin_cases a
  · exact context_12_70180_444889
  · exact context_12_70181_444958
  · exact context_12_70182_445023
  · exact context_12_70183_445090

theorem selected_cut_17492 : selected 8 ⟨445113, by decide⟩
    (prefixPartial 13 280736) = some ⟨13, 2, 0, 445113, 280736, 1009, 16384⟩ := by
  decide +kernel

theorem context_13_280736_445113 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280736 ⟨445113, by decide⟩ :=
  accepted_of_selected 13 280736 ⟨445113, by decide⟩ ⟨13, 2, 0, 445113, 280736, 1009, 16384⟩
    (by decide) selected_cut_17492

theorem selected_cut_17493 : selected 8 ⟨445138, by decide⟩
    (prefixPartial 13 280737) = some ⟨13, 2, 0, 445138, 280737, 2197, 16384⟩ := by
  decide +kernel

theorem context_13_280737_445138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280737 ⟨445138, by decide⟩ :=
  accepted_of_selected 13 280737 ⟨445138, by decide⟩ ⟨13, 2, 0, 445138, 280737, 2197, 16384⟩
    (by decide) selected_cut_17493

theorem selected_cut_17494 : selected 8 ⟨445180, by decide⟩
    (prefixPartial 13 280738) = some ⟨13, 2, 0, 445180, 280738, 1889, 16384⟩ := by
  decide +kernel

theorem context_13_280738_445180 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280738 ⟨445180, by decide⟩ :=
  accepted_of_selected 13 280738 ⟨445180, by decide⟩ ⟨13, 2, 0, 445180, 280738, 1889, 16384⟩
    (by decide) selected_cut_17494

theorem selected_cut_17495 : selected 8 ⟨445184, by decide⟩
    (prefixPartial 13 280739) = some ⟨13, 2, 0, 445184, 280739, 937, 16384⟩ := by
  decide +kernel

theorem context_13_280739_445184 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280739 ⟨445184, by decide⟩ :=
  accepted_of_selected 13 280739 ⟨445184, by decide⟩ ⟨13, 2, 0, 445184, 280739, 937, 16384⟩
    (by decide) selected_cut_17495

theorem unmarked_context_12_70184_445185 : frontier 9 ⟨445185, by decide⟩
    (prefixCache 12 70184) (prefixPartial 12 70184) = false := by
  decide +kernel

theorem node_context_12_70184_445185 : EJMOriginalGlobalDAGData.nodes 9 ⟨445185, by decide⟩ =
    .split (coordinate 12) (![⟨445113, by decide⟩,⟨445138, by decide⟩,⟨445180, by decide⟩,⟨445184, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70184_445185 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70184 ⟨445185, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70184
    ⟨445185, by decide⟩ (by decide) (![⟨445113, by decide⟩,⟨445138, by decide⟩,⟨445180, by decide⟩,⟨445184, by decide⟩]) unmarked_context_12_70184_445185 node_context_12_70184_445185
  intro a
  fin_cases a
  · exact context_13_280736_445113
  · exact context_13_280737_445138
  · exact context_13_280738_445180
  · exact context_13_280739_445184

theorem selected_cut_17496 : selected 8 ⟨445203, by decide⟩
    (prefixPartial 13 280740) = some ⟨13, 2, 0, 445203, 280740, 889, 16384⟩ := by
  decide +kernel

theorem context_13_280740_445203 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280740 ⟨445203, by decide⟩ :=
  accepted_of_selected 13 280740 ⟨445203, by decide⟩ ⟨13, 2, 0, 445203, 280740, 889, 16384⟩
    (by decide) selected_cut_17496

theorem selected_cut_17497 : selected 8 ⟨445219, by decide⟩
    (prefixPartial 13 280741) = some ⟨13, 2, 0, 445219, 280741, 1185, 16384⟩ := by
  decide +kernel

theorem context_13_280741_445219 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280741 ⟨445219, by decide⟩ :=
  accepted_of_selected 13 280741 ⟨445219, by decide⟩ ⟨13, 2, 0, 445219, 280741, 1185, 16384⟩
    (by decide) selected_cut_17497

theorem selected_cut_17498 : selected 8 ⟨445239, by decide⟩
    (prefixPartial 13 280742) = some ⟨13, 2, 0, 445239, 280742, 1713, 16384⟩ := by
  decide +kernel

theorem context_13_280742_445239 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280742 ⟨445239, by decide⟩ :=
  accepted_of_selected 13 280742 ⟨445239, by decide⟩ ⟨13, 2, 0, 445239, 280742, 1713, 16384⟩
    (by decide) selected_cut_17498

theorem selected_cut_17499 : selected 8 ⟨445246, by decide⟩
    (prefixPartial 13 280743) = some ⟨13, 2, 0, 445246, 280743, 893, 16384⟩ := by
  decide +kernel

theorem context_13_280743_445246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280743 ⟨445246, by decide⟩ :=
  accepted_of_selected 13 280743 ⟨445246, by decide⟩ ⟨13, 2, 0, 445246, 280743, 893, 16384⟩
    (by decide) selected_cut_17499

theorem unmarked_context_12_70185_445247 : frontier 9 ⟨445247, by decide⟩
    (prefixCache 12 70185) (prefixPartial 12 70185) = false := by
  decide +kernel

theorem node_context_12_70185_445247 : EJMOriginalGlobalDAGData.nodes 9 ⟨445247, by decide⟩ =
    .split (coordinate 12) (![⟨445203, by decide⟩,⟨445219, by decide⟩,⟨445239, by decide⟩,⟨445246, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70185_445247 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70185 ⟨445247, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70185
    ⟨445247, by decide⟩ (by decide) (![⟨445203, by decide⟩,⟨445219, by decide⟩,⟨445239, by decide⟩,⟨445246, by decide⟩]) unmarked_context_12_70185_445247 node_context_12_70185_445247
  intro a
  fin_cases a
  · exact context_13_280740_445203
  · exact context_13_280741_445219
  · exact context_13_280742_445239
  · exact context_13_280743_445246

theorem selected_cut_17500 : selected 9 ⟨445248, by decide⟩
    (prefixPartial 12 70186) = some ⟨12, 1, 0, 445248, 70186, 1, 65536⟩ := by
  decide +kernel

theorem context_12_70186_445248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70186 ⟨445248, by decide⟩ :=
  accepted_of_selected 12 70186 ⟨445248, by decide⟩ ⟨12, 1, 0, 445248, 70186, 1, 65536⟩
    (by decide) selected_cut_17500

theorem selected_cut_17501 : selected 8 ⟨445266, by decide⟩
    (prefixPartial 13 280748) = some ⟨13, 2, 0, 445266, 280748, 765, 16384⟩ := by
  decide +kernel

theorem context_13_280748_445266 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280748 ⟨445266, by decide⟩ :=
  accepted_of_selected 13 280748 ⟨445266, by decide⟩ ⟨13, 2, 0, 445266, 280748, 765, 16384⟩
    (by decide) selected_cut_17501

theorem selected_cut_17502 : selected 8 ⟨445283, by decide⟩
    (prefixPartial 13 280749) = some ⟨13, 2, 0, 445283, 280749, 1785, 16384⟩ := by
  decide +kernel

theorem context_13_280749_445283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280749 ⟨445283, by decide⟩ :=
  accepted_of_selected 13 280749 ⟨445283, by decide⟩ ⟨13, 2, 0, 445283, 280749, 1785, 16384⟩
    (by decide) selected_cut_17502

theorem selected_cut_17503 : selected 8 ⟨445300, by decide⟩
    (prefixPartial 13 280750) = some ⟨13, 2, 0, 445300, 280750, 1501, 16384⟩ := by
  decide +kernel

theorem context_13_280750_445300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280750 ⟨445300, by decide⟩ :=
  accepted_of_selected 13 280750 ⟨445300, by decide⟩ ⟨13, 2, 0, 445300, 280750, 1501, 16384⟩
    (by decide) selected_cut_17503

theorem selected_cut_17504 : selected 8 ⟨445306, by decide⟩
    (prefixPartial 13 280751) = some ⟨13, 2, 0, 445306, 280751, 709, 16384⟩ := by
  decide +kernel

theorem context_13_280751_445306 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280751 ⟨445306, by decide⟩ :=
  accepted_of_selected 13 280751 ⟨445306, by decide⟩ ⟨13, 2, 0, 445306, 280751, 709, 16384⟩
    (by decide) selected_cut_17504

theorem unmarked_context_12_70187_445307 : frontier 9 ⟨445307, by decide⟩
    (prefixCache 12 70187) (prefixPartial 12 70187) = false := by
  decide +kernel

theorem node_context_12_70187_445307 : EJMOriginalGlobalDAGData.nodes 9 ⟨445307, by decide⟩ =
    .split (coordinate 12) (![⟨445266, by decide⟩,⟨445283, by decide⟩,⟨445300, by decide⟩,⟨445306, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70187_445307 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70187 ⟨445307, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70187
    ⟨445307, by decide⟩ (by decide) (![⟨445266, by decide⟩,⟨445283, by decide⟩,⟨445300, by decide⟩,⟨445306, by decide⟩]) unmarked_context_12_70187_445307 node_context_12_70187_445307
  intro a
  fin_cases a
  · exact context_13_280748_445266
  · exact context_13_280749_445283
  · exact context_13_280750_445300
  · exact context_13_280751_445306

theorem unmarked_context_11_17546_445308 : frontier 10 ⟨445308, by decide⟩
    (prefixCache 11 17546) (prefixPartial 11 17546) = false := by
  decide +kernel

theorem node_context_11_17546_445308 : EJMOriginalGlobalDAGData.nodes 10 ⟨445308, by decide⟩ =
    .split (coordinate 11) (![⟨445185, by decide⟩,⟨445247, by decide⟩,⟨445248, by decide⟩,⟨445307, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17546_445308 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17546 ⟨445308, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17546
    ⟨445308, by decide⟩ (by decide) (![⟨445185, by decide⟩,⟨445247, by decide⟩,⟨445248, by decide⟩,⟨445307, by decide⟩]) unmarked_context_11_17546_445308 node_context_11_17546_445308
  intro a
  fin_cases a
  · exact context_12_70184_445185
  · exact context_12_70185_445247
  · exact context_12_70186_445248
  · exact context_12_70187_445307

theorem selected_cut_17505 : selected 8 ⟨445327, by decide⟩
    (prefixPartial 13 280752) = some ⟨13, 2, 0, 445327, 280752, 877, 16384⟩ := by
  decide +kernel

theorem context_13_280752_445327 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280752 ⟨445327, by decide⟩ :=
  accepted_of_selected 13 280752 ⟨445327, by decide⟩ ⟨13, 2, 0, 445327, 280752, 877, 16384⟩
    (by decide) selected_cut_17505

theorem selected_cut_17506 : selected 8 ⟨445354, by decide⟩
    (prefixPartial 13 280753) = some ⟨13, 2, 0, 445354, 280753, 2417, 16384⟩ := by
  decide +kernel

theorem context_13_280753_445354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280753 ⟨445354, by decide⟩ :=
  accepted_of_selected 13 280753 ⟨445354, by decide⟩ ⟨13, 2, 0, 445354, 280753, 2417, 16384⟩
    (by decide) selected_cut_17506

theorem selected_cut_17507 : selected 8 ⟨445379, by decide⟩
    (prefixPartial 13 280754) = some ⟨13, 2, 0, 445379, 280754, 1793, 16384⟩ := by
  decide +kernel

theorem context_13_280754_445379 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280754 ⟨445379, by decide⟩ :=
  accepted_of_selected 13 280754 ⟨445379, by decide⟩ ⟨13, 2, 0, 445379, 280754, 1793, 16384⟩
    (by decide) selected_cut_17507

theorem selected_cut_17508 : selected 8 ⟨445390, by decide⟩
    (prefixPartial 13 280755) = some ⟨13, 2, 0, 445390, 280755, 1049, 16384⟩ := by
  decide +kernel

theorem context_13_280755_445390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280755 ⟨445390, by decide⟩ :=
  accepted_of_selected 13 280755 ⟨445390, by decide⟩ ⟨13, 2, 0, 445390, 280755, 1049, 16384⟩
    (by decide) selected_cut_17508

theorem unmarked_context_12_70188_445391 : frontier 9 ⟨445391, by decide⟩
    (prefixCache 12 70188) (prefixPartial 12 70188) = false := by
  decide +kernel

theorem node_context_12_70188_445391 : EJMOriginalGlobalDAGData.nodes 9 ⟨445391, by decide⟩ =
    .split (coordinate 12) (![⟨445327, by decide⟩,⟨445354, by decide⟩,⟨445379, by decide⟩,⟨445390, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70188_445391 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70188 ⟨445391, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70188
    ⟨445391, by decide⟩ (by decide) (![⟨445327, by decide⟩,⟨445354, by decide⟩,⟨445379, by decide⟩,⟨445390, by decide⟩]) unmarked_context_12_70188_445391 node_context_12_70188_445391
  intro a
  fin_cases a
  · exact context_13_280752_445327
  · exact context_13_280753_445354
  · exact context_13_280754_445379
  · exact context_13_280755_445390

theorem selected_cut_17509 : selected 8 ⟨445409, by decide⟩
    (prefixPartial 13 280756) = some ⟨13, 2, 0, 445409, 280756, 873, 16384⟩ := by
  decide +kernel

theorem context_13_280756_445409 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280756 ⟨445409, by decide⟩ :=
  accepted_of_selected 13 280756 ⟨445409, by decide⟩ ⟨13, 2, 0, 445409, 280756, 873, 16384⟩
    (by decide) selected_cut_17509

theorem selected_cut_17510 : selected 8 ⟨445427, by decide⟩
    (prefixPartial 13 280757) = some ⟨13, 2, 0, 445427, 280757, 1341, 16384⟩ := by
  decide +kernel

theorem context_13_280757_445427 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280757 ⟨445427, by decide⟩ :=
  accepted_of_selected 13 280757 ⟨445427, by decide⟩ ⟨13, 2, 0, 445427, 280757, 1341, 16384⟩
    (by decide) selected_cut_17510

theorem selected_cut_17511 : selected 8 ⟨445442, by decide⟩
    (prefixPartial 13 280758) = some ⟨13, 2, 0, 445442, 280758, 1669, 16384⟩ := by
  decide +kernel

theorem context_13_280758_445442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280758 ⟨445442, by decide⟩ :=
  accepted_of_selected 13 280758 ⟨445442, by decide⟩ ⟨13, 2, 0, 445442, 280758, 1669, 16384⟩
    (by decide) selected_cut_17511

theorem selected_cut_17512 : selected 8 ⟨445450, by decide⟩
    (prefixPartial 13 280759) = some ⟨13, 2, 0, 445450, 280759, 905, 16384⟩ := by
  decide +kernel

theorem context_13_280759_445450 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280759 ⟨445450, by decide⟩ :=
  accepted_of_selected 13 280759 ⟨445450, by decide⟩ ⟨13, 2, 0, 445450, 280759, 905, 16384⟩
    (by decide) selected_cut_17512

theorem unmarked_context_12_70189_445451 : frontier 9 ⟨445451, by decide⟩
    (prefixCache 12 70189) (prefixPartial 12 70189) = false := by
  decide +kernel

theorem node_context_12_70189_445451 : EJMOriginalGlobalDAGData.nodes 9 ⟨445451, by decide⟩ =
    .split (coordinate 12) (![⟨445409, by decide⟩,⟨445427, by decide⟩,⟨445442, by decide⟩,⟨445450, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70189_445451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70189 ⟨445451, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70189
    ⟨445451, by decide⟩ (by decide) (![⟨445409, by decide⟩,⟨445427, by decide⟩,⟨445442, by decide⟩,⟨445450, by decide⟩]) unmarked_context_12_70189_445451 node_context_12_70189_445451
  intro a
  fin_cases a
  · exact context_13_280756_445409
  · exact context_13_280757_445427
  · exact context_13_280758_445442
  · exact context_13_280759_445450

theorem selected_cut_17513 : selected 9 ⟨445508, by decide⟩
    (prefixPartial 12 70190) = some ⟨12, 2, 0, 445508, 70190, 4093, 65536⟩ := by
  decide +kernel

theorem context_12_70190_445508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70190 ⟨445508, by decide⟩ :=
  accepted_of_selected 12 70190 ⟨445508, by decide⟩ ⟨12, 2, 0, 445508, 70190, 4093, 65536⟩
    (by decide) selected_cut_17513

theorem selected_cut_17514 : selected 8 ⟨445522, by decide⟩
    (prefixPartial 13 280764) = some ⟨13, 2, 0, 445522, 280764, 657, 16384⟩ := by
  decide +kernel

theorem context_13_280764_445522 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280764 ⟨445522, by decide⟩ :=
  accepted_of_selected 13 280764 ⟨445522, by decide⟩ ⟨13, 2, 0, 445522, 280764, 657, 16384⟩
    (by decide) selected_cut_17514

theorem selected_cut_17515 : selected 8 ⟨445539, by decide⟩
    (prefixPartial 13 280765) = some ⟨13, 2, 0, 445539, 280765, 1833, 16384⟩ := by
  decide +kernel

theorem context_13_280765_445539 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280765 ⟨445539, by decide⟩ :=
  accepted_of_selected 13 280765 ⟨445539, by decide⟩ ⟨13, 2, 0, 445539, 280765, 1833, 16384⟩
    (by decide) selected_cut_17515

theorem selected_cut_17516 : selected 8 ⟨445550, by decide⟩
    (prefixPartial 13 280766) = some ⟨13, 2, 0, 445550, 280766, 1469, 16384⟩ := by
  decide +kernel

theorem context_13_280766_445550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280766 ⟨445550, by decide⟩ :=
  accepted_of_selected 13 280766 ⟨445550, by decide⟩ ⟨13, 2, 0, 445550, 280766, 1469, 16384⟩
    (by decide) selected_cut_17516

theorem selected_cut_17517 : selected 8 ⟨445558, by decide⟩
    (prefixPartial 13 280767) = some ⟨13, 2, 0, 445558, 280767, 717, 16384⟩ := by
  decide +kernel

theorem context_13_280767_445558 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280767 ⟨445558, by decide⟩ :=
  accepted_of_selected 13 280767 ⟨445558, by decide⟩ ⟨13, 2, 0, 445558, 280767, 717, 16384⟩
    (by decide) selected_cut_17517

theorem unmarked_context_12_70191_445559 : frontier 9 ⟨445559, by decide⟩
    (prefixCache 12 70191) (prefixPartial 12 70191) = false := by
  decide +kernel

theorem node_context_12_70191_445559 : EJMOriginalGlobalDAGData.nodes 9 ⟨445559, by decide⟩ =
    .split (coordinate 12) (![⟨445522, by decide⟩,⟨445539, by decide⟩,⟨445550, by decide⟩,⟨445558, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70191_445559 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70191 ⟨445559, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70191
    ⟨445559, by decide⟩ (by decide) (![⟨445522, by decide⟩,⟨445539, by decide⟩,⟨445550, by decide⟩,⟨445558, by decide⟩]) unmarked_context_12_70191_445559 node_context_12_70191_445559
  intro a
  fin_cases a
  · exact context_13_280764_445522
  · exact context_13_280765_445539
  · exact context_13_280766_445550
  · exact context_13_280767_445558

theorem unmarked_context_11_17547_445560 : frontier 10 ⟨445560, by decide⟩
    (prefixCache 11 17547) (prefixPartial 11 17547) = false := by
  decide +kernel

theorem node_context_11_17547_445560 : EJMOriginalGlobalDAGData.nodes 10 ⟨445560, by decide⟩ =
    .split (coordinate 11) (![⟨445391, by decide⟩,⟨445451, by decide⟩,⟨445508, by decide⟩,⟨445559, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17547_445560 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17547 ⟨445560, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17547
    ⟨445560, by decide⟩ (by decide) (![⟨445391, by decide⟩,⟨445451, by decide⟩,⟨445508, by decide⟩,⟨445559, by decide⟩]) unmarked_context_11_17547_445560 node_context_11_17547_445560
  intro a
  fin_cases a
  · exact context_12_70188_445391
  · exact context_12_70189_445451
  · exact context_12_70190_445508
  · exact context_12_70191_445559

theorem unmarked_context_10_4386_445561 : frontier 11 ⟨445561, by decide⟩
    (prefixCache 10 4386) (prefixPartial 10 4386) = false := by
  decide +kernel

theorem node_context_10_4386_445561 : EJMOriginalGlobalDAGData.nodes 11 ⟨445561, by decide⟩ =
    .split (coordinate 10) (![⟨444768, by decide⟩,⟨445091, by decide⟩,⟨445308, by decide⟩,⟨445560, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4386_445561 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4386 ⟨445561, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4386
    ⟨445561, by decide⟩ (by decide) (![⟨444768, by decide⟩,⟨445091, by decide⟩,⟨445308, by decide⟩,⟨445560, by decide⟩]) unmarked_context_10_4386_445561 node_context_10_4386_445561
  intro a
  fin_cases a
  · exact context_11_17544_444768
  · exact context_11_17545_445091
  · exact context_11_17546_445308
  · exact context_11_17547_445560

theorem selected_cut_17518 : selected 9 ⟨445562, by decide⟩
    (prefixPartial 12 70192) = some ⟨12, 1, 0, 445562, 70192, 1, 65536⟩ := by
  decide +kernel

theorem context_12_70192_445562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70192 ⟨445562, by decide⟩ :=
  accepted_of_selected 12 70192 ⟨445562, by decide⟩ ⟨12, 1, 0, 445562, 70192, 1, 65536⟩
    (by decide) selected_cut_17518

theorem selected_cut_17519 : selected 9 ⟨445640, by decide⟩
    (prefixPartial 12 70193) = some ⟨12, 2, 0, 445640, 70193, 3873, 65536⟩ := by
  decide +kernel

theorem context_12_70193_445640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70193 ⟨445640, by decide⟩ :=
  accepted_of_selected 12 70193 ⟨445640, by decide⟩ ⟨12, 2, 0, 445640, 70193, 3873, 65536⟩
    (by decide) selected_cut_17519

theorem selected_cut_17520 : selected 9 ⟨445715, by decide⟩
    (prefixPartial 12 70194) = some ⟨12, 2, 0, 445715, 70194, 3165, 65536⟩ := by
  decide +kernel

theorem context_12_70194_445715 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70194 ⟨445715, by decide⟩ :=
  accepted_of_selected 12 70194 ⟨445715, by decide⟩ ⟨12, 2, 0, 445715, 70194, 3165, 65536⟩
    (by decide) selected_cut_17520

theorem selected_cut_17521 : selected 9 ⟨445792, by decide⟩
    (prefixPartial 12 70195) = some ⟨12, 2, 0, 445792, 70195, 3585, 65536⟩ := by
  decide +kernel

theorem context_12_70195_445792 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70195 ⟨445792, by decide⟩ :=
  accepted_of_selected 12 70195 ⟨445792, by decide⟩ ⟨12, 2, 0, 445792, 70195, 3585, 65536⟩
    (by decide) selected_cut_17521

theorem unmarked_context_11_17548_445793 : frontier 10 ⟨445793, by decide⟩
    (prefixCache 11 17548) (prefixPartial 11 17548) = false := by
  decide +kernel

theorem node_context_11_17548_445793 : EJMOriginalGlobalDAGData.nodes 10 ⟨445793, by decide⟩ =
    .split (coordinate 11) (![⟨445562, by decide⟩,⟨445640, by decide⟩,⟨445715, by decide⟩,⟨445792, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17548_445793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17548 ⟨445793, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17548
    ⟨445793, by decide⟩ (by decide) (![⟨445562, by decide⟩,⟨445640, by decide⟩,⟨445715, by decide⟩,⟨445792, by decide⟩]) unmarked_context_11_17548_445793 node_context_11_17548_445793
  intro a
  fin_cases a
  · exact context_12_70192_445562
  · exact context_12_70193_445640
  · exact context_12_70194_445715
  · exact context_12_70195_445792

theorem selected_cut_17522 : selected 8 ⟨445813, by decide⟩
    (prefixPartial 13 280784) = some ⟨13, 2, 0, 445813, 280784, 753, 16384⟩ := by
  decide +kernel

theorem context_13_280784_445813 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280784 ⟨445813, by decide⟩ :=
  accepted_of_selected 13 280784 ⟨445813, by decide⟩ ⟨13, 2, 0, 445813, 280784, 753, 16384⟩
    (by decide) selected_cut_17522

theorem selected_cut_17523 : selected 8 ⟨445862, by decide⟩
    (prefixPartial 13 280785) = some ⟨13, 2, 0, 445862, 280785, 2325, 16384⟩ := by
  decide +kernel

theorem context_13_280785_445862 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280785 ⟨445862, by decide⟩ :=
  accepted_of_selected 13 280785 ⟨445862, by decide⟩ ⟨13, 2, 0, 445862, 280785, 2325, 16384⟩
    (by decide) selected_cut_17523

theorem selected_cut_17524 : selected 8 ⟨445883, by decide⟩
    (prefixPartial 13 280786) = some ⟨13, 2, 0, 445883, 280786, 1581, 16384⟩ := by
  decide +kernel

theorem context_13_280786_445883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280786 ⟨445883, by decide⟩ :=
  accepted_of_selected 13 280786 ⟨445883, by decide⟩ ⟨13, 2, 0, 445883, 280786, 1581, 16384⟩
    (by decide) selected_cut_17524

theorem selected_cut_17525 : selected 8 ⟨445894, by decide⟩
    (prefixPartial 13 280787) = some ⟨13, 2, 0, 445894, 280787, 901, 16384⟩ := by
  decide +kernel

theorem context_13_280787_445894 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280787 ⟨445894, by decide⟩ :=
  accepted_of_selected 13 280787 ⟨445894, by decide⟩ ⟨13, 2, 0, 445894, 280787, 901, 16384⟩
    (by decide) selected_cut_17525

theorem unmarked_context_12_70196_445895 : frontier 9 ⟨445895, by decide⟩
    (prefixCache 12 70196) (prefixPartial 12 70196) = false := by
  decide +kernel

theorem node_context_12_70196_445895 : EJMOriginalGlobalDAGData.nodes 9 ⟨445895, by decide⟩ =
    .split (coordinate 12) (![⟨445813, by decide⟩,⟨445862, by decide⟩,⟨445883, by decide⟩,⟨445894, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70196_445895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70196 ⟨445895, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70196
    ⟨445895, by decide⟩ (by decide) (![⟨445813, by decide⟩,⟨445862, by decide⟩,⟨445883, by decide⟩,⟨445894, by decide⟩]) unmarked_context_12_70196_445895 node_context_12_70196_445895
  intro a
  fin_cases a
  · exact context_13_280784_445813
  · exact context_13_280785_445862
  · exact context_13_280786_445883
  · exact context_13_280787_445894

theorem selected_cut_17526 : selected 9 ⟨445970, by decide⟩
    (prefixPartial 12 70197) = some ⟨12, 2, 0, 445970, 70197, 3737, 65536⟩ := by
  decide +kernel

theorem context_12_70197_445970 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70197 ⟨445970, by decide⟩ :=
  accepted_of_selected 12 70197 ⟨445970, by decide⟩ ⟨12, 2, 0, 445970, 70197, 3737, 65536⟩
    (by decide) selected_cut_17526

theorem selected_cut_17527 : selected 9 ⟨446049, by decide⟩
    (prefixPartial 12 70198) = some ⟨12, 2, 0, 446049, 70198, 3633, 65536⟩ := by
  decide +kernel

theorem context_12_70198_446049 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70198 ⟨446049, by decide⟩ :=
  accepted_of_selected 12 70198 ⟨446049, by decide⟩ ⟨12, 2, 0, 446049, 70198, 3633, 65536⟩
    (by decide) selected_cut_17527

theorem selected_cut_17528 : selected 9 ⟨446119, by decide⟩
    (prefixPartial 12 70199) = some ⟨12, 2, 0, 446119, 70199, 3689, 65536⟩ := by
  decide +kernel

theorem context_12_70199_446119 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70199 ⟨446119, by decide⟩ :=
  accepted_of_selected 12 70199 ⟨446119, by decide⟩ ⟨12, 2, 0, 446119, 70199, 3689, 65536⟩
    (by decide) selected_cut_17528

theorem unmarked_context_11_17549_446120 : frontier 10 ⟨446120, by decide⟩
    (prefixCache 11 17549) (prefixPartial 11 17549) = false := by
  decide +kernel

theorem node_context_11_17549_446120 : EJMOriginalGlobalDAGData.nodes 10 ⟨446120, by decide⟩ =
    .split (coordinate 11) (![⟨445895, by decide⟩,⟨445970, by decide⟩,⟨446049, by decide⟩,⟨446119, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17549_446120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17549 ⟨446120, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17549
    ⟨446120, by decide⟩ (by decide) (![⟨445895, by decide⟩,⟨445970, by decide⟩,⟨446049, by decide⟩,⟨446119, by decide⟩]) unmarked_context_11_17549_446120 node_context_11_17549_446120
  intro a
  fin_cases a
  · exact context_12_70196_445895
  · exact context_12_70197_445970
  · exact context_12_70198_446049
  · exact context_12_70199_446119

theorem selected_cut_17529 : selected 8 ⟨446130, by decide⟩
    (prefixPartial 13 280800) = some ⟨13, 2, 0, 446130, 280800, 453, 16384⟩ := by
  decide +kernel

theorem context_13_280800_446130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280800 ⟨446130, by decide⟩ :=
  accepted_of_selected 13 280800 ⟨446130, by decide⟩ ⟨13, 2, 0, 446130, 280800, 453, 16384⟩
    (by decide) selected_cut_17529

theorem selected_cut_17530 : selected 8 ⟨446177, by decide⟩
    (prefixPartial 13 280801) = some ⟨13, 2, 0, 446177, 280801, 2297, 16384⟩ := by
  decide +kernel

theorem context_13_280801_446177 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280801 ⟨446177, by decide⟩ :=
  accepted_of_selected 13 280801 ⟨446177, by decide⟩ ⟨13, 2, 0, 446177, 280801, 2297, 16384⟩
    (by decide) selected_cut_17530

theorem selected_cut_17531 : selected 8 ⟨446200, by decide⟩
    (prefixPartial 13 280802) = some ⟨13, 2, 0, 446200, 280802, 1593, 16384⟩ := by
  decide +kernel

theorem context_13_280802_446200 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280802 ⟨446200, by decide⟩ :=
  accepted_of_selected 13 280802 ⟨446200, by decide⟩ ⟨13, 2, 0, 446200, 280802, 1593, 16384⟩
    (by decide) selected_cut_17531

theorem selected_cut_17532 : selected 8 ⟨446210, by decide⟩
    (prefixPartial 13 280803) = some ⟨13, 2, 0, 446210, 280803, 841, 16384⟩ := by
  decide +kernel

theorem context_13_280803_446210 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280803 ⟨446210, by decide⟩ :=
  accepted_of_selected 13 280803 ⟨446210, by decide⟩ ⟨13, 2, 0, 446210, 280803, 841, 16384⟩
    (by decide) selected_cut_17532

theorem unmarked_context_12_70200_446211 : frontier 9 ⟨446211, by decide⟩
    (prefixCache 12 70200) (prefixPartial 12 70200) = false := by
  decide +kernel

theorem node_context_12_70200_446211 : EJMOriginalGlobalDAGData.nodes 9 ⟨446211, by decide⟩ =
    .split (coordinate 12) (![⟨446130, by decide⟩,⟨446177, by decide⟩,⟨446200, by decide⟩,⟨446210, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70200_446211 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70200 ⟨446211, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70200
    ⟨446211, by decide⟩ (by decide) (![⟨446130, by decide⟩,⟨446177, by decide⟩,⟨446200, by decide⟩,⟨446210, by decide⟩]) unmarked_context_12_70200_446211 node_context_12_70200_446211
  intro a
  fin_cases a
  · exact context_13_280800_446130
  · exact context_13_280801_446177
  · exact context_13_280802_446200
  · exact context_13_280803_446210

theorem selected_cut_17533 : selected 9 ⟨446273, by decide⟩
    (prefixPartial 12 70201) = some ⟨12, 2, 0, 446273, 70201, 3897, 65536⟩ := by
  decide +kernel

theorem context_12_70201_446273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70201 ⟨446273, by decide⟩ :=
  accepted_of_selected 12 70201 ⟨446273, by decide⟩ ⟨12, 2, 0, 446273, 70201, 3897, 65536⟩
    (by decide) selected_cut_17533

theorem selected_cut_17534 : selected 8 ⟨446284, by decide⟩
    (prefixPartial 13 280808) = some ⟨13, 2, 0, 446284, 280808, 409, 16384⟩ := by
  decide +kernel

theorem context_13_280808_446284 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280808 ⟨446284, by decide⟩ :=
  accepted_of_selected 13 280808 ⟨446284, by decide⟩ ⟨13, 2, 0, 446284, 280808, 409, 16384⟩
    (by decide) selected_cut_17534

theorem selected_cut_17535 : selected 8 ⟨446323, by decide⟩
    (prefixPartial 13 280809) = some ⟨13, 2, 0, 446323, 280809, 2513, 16384⟩ := by
  decide +kernel

theorem context_13_280809_446323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280809 ⟨446323, by decide⟩ :=
  accepted_of_selected 13 280809 ⟨446323, by decide⟩ ⟨13, 2, 0, 446323, 280809, 2513, 16384⟩
    (by decide) selected_cut_17535

theorem selected_cut_17536 : selected 8 ⟨446354, by decide⟩
    (prefixPartial 13 280810) = some ⟨13, 2, 0, 446354, 280810, 1733, 16384⟩ := by
  decide +kernel

theorem context_13_280810_446354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280810 ⟨446354, by decide⟩ :=
  accepted_of_selected 13 280810 ⟨446354, by decide⟩ ⟨13, 2, 0, 446354, 280810, 1733, 16384⟩
    (by decide) selected_cut_17536

theorem selected_cut_17537 : selected 8 ⟨446375, by decide⟩
    (prefixPartial 13 280811) = some ⟨13, 2, 0, 446375, 280811, 1061, 16384⟩ := by
  decide +kernel

theorem context_13_280811_446375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280811 ⟨446375, by decide⟩ :=
  accepted_of_selected 13 280811 ⟨446375, by decide⟩ ⟨13, 2, 0, 446375, 280811, 1061, 16384⟩
    (by decide) selected_cut_17537

theorem unmarked_context_12_70202_446376 : frontier 9 ⟨446376, by decide⟩
    (prefixCache 12 70202) (prefixPartial 12 70202) = false := by
  decide +kernel

theorem node_context_12_70202_446376 : EJMOriginalGlobalDAGData.nodes 9 ⟨446376, by decide⟩ =
    .split (coordinate 12) (![⟨446284, by decide⟩,⟨446323, by decide⟩,⟨446354, by decide⟩,⟨446375, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70202_446376 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70202 ⟨446376, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70202
    ⟨446376, by decide⟩ (by decide) (![⟨446284, by decide⟩,⟨446323, by decide⟩,⟨446354, by decide⟩,⟨446375, by decide⟩]) unmarked_context_12_70202_446376 node_context_12_70202_446376
  intro a
  fin_cases a
  · exact context_13_280808_446284
  · exact context_13_280809_446323
  · exact context_13_280810_446354
  · exact context_13_280811_446375

theorem selected_cut_17538 : selected 9 ⟨446446, by decide⟩
    (prefixPartial 12 70203) = some ⟨12, 2, 0, 446446, 70203, 3745, 65536⟩ := by
  decide +kernel

theorem context_12_70203_446446 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70203 ⟨446446, by decide⟩ :=
  accepted_of_selected 12 70203 ⟨446446, by decide⟩ ⟨12, 2, 0, 446446, 70203, 3745, 65536⟩
    (by decide) selected_cut_17538

theorem unmarked_context_11_17550_446447 : frontier 10 ⟨446447, by decide⟩
    (prefixCache 11 17550) (prefixPartial 11 17550) = false := by
  decide +kernel

theorem node_context_11_17550_446447 : EJMOriginalGlobalDAGData.nodes 10 ⟨446447, by decide⟩ =
    .split (coordinate 11) (![⟨446211, by decide⟩,⟨446273, by decide⟩,⟨446376, by decide⟩,⟨446446, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17550_446447 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17550 ⟨446447, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17550
    ⟨446447, by decide⟩ (by decide) (![⟨446211, by decide⟩,⟨446273, by decide⟩,⟨446376, by decide⟩,⟨446446, by decide⟩]) unmarked_context_11_17550_446447 node_context_11_17550_446447
  intro a
  fin_cases a
  · exact context_12_70200_446211
  · exact context_12_70201_446273
  · exact context_12_70202_446376
  · exact context_12_70203_446446

theorem selected_cut_17539 : selected 8 ⟨446454, by decide⟩
    (prefixPartial 13 280816) = some ⟨13, 2, 0, 446454, 280816, 177, 16384⟩ := by
  decide +kernel

theorem context_13_280816_446454 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280816 ⟨446454, by decide⟩ :=
  accepted_of_selected 13 280816 ⟨446454, by decide⟩ ⟨13, 2, 0, 446454, 280816, 177, 16384⟩
    (by decide) selected_cut_17539

theorem selected_cut_17540 : selected 8 ⟨446498, by decide⟩
    (prefixPartial 13 280817) = some ⟨13, 2, 0, 446498, 280817, 2385, 16384⟩ := by
  decide +kernel

theorem context_13_280817_446498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280817 ⟨446498, by decide⟩ :=
  accepted_of_selected 13 280817 ⟨446498, by decide⟩ ⟨13, 2, 0, 446498, 280817, 2385, 16384⟩
    (by decide) selected_cut_17540

theorem selected_cut_17541 : selected 8 ⟨446513, by decide⟩
    (prefixPartial 13 280818) = some ⟨13, 2, 0, 446513, 280818, 1565, 16384⟩ := by
  decide +kernel

theorem context_13_280818_446513 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280818 ⟨446513, by decide⟩ :=
  accepted_of_selected 13 280818 ⟨446513, by decide⟩ ⟨13, 2, 0, 446513, 280818, 1565, 16384⟩
    (by decide) selected_cut_17541

theorem selected_cut_17542 : selected 8 ⟨446523, by decide⟩
    (prefixPartial 13 280819) = some ⟨13, 2, 0, 446523, 280819, 781, 16384⟩ := by
  decide +kernel

theorem context_13_280819_446523 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 280819 ⟨446523, by decide⟩ :=
  accepted_of_selected 13 280819 ⟨446523, by decide⟩ ⟨13, 2, 0, 446523, 280819, 781, 16384⟩
    (by decide) selected_cut_17542

theorem unmarked_context_12_70204_446524 : frontier 9 ⟨446524, by decide⟩
    (prefixCache 12 70204) (prefixPartial 12 70204) = false := by
  decide +kernel

theorem node_context_12_70204_446524 : EJMOriginalGlobalDAGData.nodes 9 ⟨446524, by decide⟩ =
    .split (coordinate 12) (![⟨446454, by decide⟩,⟨446498, by decide⟩,⟨446513, by decide⟩,⟨446523, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_70204_446524 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70204 ⟨446524, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 70204
    ⟨446524, by decide⟩ (by decide) (![⟨446454, by decide⟩,⟨446498, by decide⟩,⟨446513, by decide⟩,⟨446523, by decide⟩]) unmarked_context_12_70204_446524 node_context_12_70204_446524
  intro a
  fin_cases a
  · exact context_13_280816_446454
  · exact context_13_280817_446498
  · exact context_13_280818_446513
  · exact context_13_280819_446523

theorem selected_cut_17543 : selected 9 ⟨446574, by decide⟩
    (prefixPartial 12 70205) = some ⟨12, 2, 0, 446574, 70205, 3709, 65536⟩ := by
  decide +kernel

theorem context_12_70205_446574 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70205 ⟨446574, by decide⟩ :=
  accepted_of_selected 12 70205 ⟨446574, by decide⟩ ⟨12, 2, 0, 446574, 70205, 3709, 65536⟩
    (by decide) selected_cut_17543

theorem selected_cut_17544 : selected 9 ⟨446628, by decide⟩
    (prefixPartial 12 70206) = some ⟨12, 2, 0, 446628, 70206, 3501, 65536⟩ := by
  decide +kernel

theorem context_12_70206_446628 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70206 ⟨446628, by decide⟩ :=
  accepted_of_selected 12 70206 ⟨446628, by decide⟩ ⟨12, 2, 0, 446628, 70206, 3501, 65536⟩
    (by decide) selected_cut_17544

theorem selected_cut_17545 : selected 9 ⟨446681, by decide⟩
    (prefixPartial 12 70207) = some ⟨12, 2, 0, 446681, 70207, 3629, 65536⟩ := by
  decide +kernel

theorem context_12_70207_446681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70207 ⟨446681, by decide⟩ :=
  accepted_of_selected 12 70207 ⟨446681, by decide⟩ ⟨12, 2, 0, 446681, 70207, 3629, 65536⟩
    (by decide) selected_cut_17545

theorem unmarked_context_11_17551_446682 : frontier 10 ⟨446682, by decide⟩
    (prefixCache 11 17551) (prefixPartial 11 17551) = false := by
  decide +kernel

theorem node_context_11_17551_446682 : EJMOriginalGlobalDAGData.nodes 10 ⟨446682, by decide⟩ =
    .split (coordinate 11) (![⟨446524, by decide⟩,⟨446574, by decide⟩,⟨446628, by decide⟩,⟨446681, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17551_446682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17551 ⟨446682, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17551
    ⟨446682, by decide⟩ (by decide) (![⟨446524, by decide⟩,⟨446574, by decide⟩,⟨446628, by decide⟩,⟨446681, by decide⟩]) unmarked_context_11_17551_446682 node_context_11_17551_446682
  intro a
  fin_cases a
  · exact context_12_70204_446524
  · exact context_12_70205_446574
  · exact context_12_70206_446628
  · exact context_12_70207_446681

theorem unmarked_context_10_4387_446683 : frontier 11 ⟨446683, by decide⟩
    (prefixCache 10 4387) (prefixPartial 10 4387) = false := by
  decide +kernel

theorem node_context_10_4387_446683 : EJMOriginalGlobalDAGData.nodes 11 ⟨446683, by decide⟩ =
    .split (coordinate 10) (![⟨445793, by decide⟩,⟨446120, by decide⟩,⟨446447, by decide⟩,⟨446682, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4387_446683 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4387 ⟨446683, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4387
    ⟨446683, by decide⟩ (by decide) (![⟨445793, by decide⟩,⟨446120, by decide⟩,⟨446447, by decide⟩,⟨446682, by decide⟩]) unmarked_context_10_4387_446683 node_context_10_4387_446683
  intro a
  fin_cases a
  · exact context_11_17548_445793
  · exact context_11_17549_446120
  · exact context_11_17550_446447
  · exact context_11_17551_446682

theorem unmarked_context_9_1096_446684 : frontier 12 ⟨446684, by decide⟩
    (prefixCache 9 1096) (prefixPartial 9 1096) = false := by
  decide +kernel

theorem node_context_9_1096_446684 : EJMOriginalGlobalDAGData.nodes 12 ⟨446684, by decide⟩ =
    .split (coordinate 9) (![⟨443185, by decide⟩,⟨444572, by decide⟩,⟨445561, by decide⟩,⟨446683, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1096_446684 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1096 ⟨446684, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1096
    ⟨446684, by decide⟩ (by decide) (![⟨443185, by decide⟩,⟨444572, by decide⟩,⟨445561, by decide⟩,⟨446683, by decide⟩]) unmarked_context_9_1096_446684 node_context_9_1096_446684
  intro a
  fin_cases a
  · exact context_10_4384_443185
  · exact context_10_4385_444572
  · exact context_10_4386_445561
  · exact context_10_4387_446683

theorem selected_cut_17546 : selected 11 ⟨3442, by decide⟩
    (prefixPartial 10 4388) = some ⟨10, 1, 0, 3442, 4388, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_4388_3442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4388 ⟨3442, by decide⟩ :=
  accepted_of_selected 10 4388 ⟨3442, by decide⟩ ⟨10, 1, 0, 3442, 4388, 1, 1048576⟩
    (by decide) selected_cut_17546

theorem selected_cut_17547 : selected 9 ⟨446719, by decide⟩
    (prefixPartial 12 70224) = some ⟨12, 2, 0, 446719, 70224, 1473, 65536⟩ := by
  decide +kernel

theorem context_12_70224_446719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70224 ⟨446719, by decide⟩ :=
  accepted_of_selected 12 70224 ⟨446719, by decide⟩ ⟨12, 2, 0, 446719, 70224, 1473, 65536⟩
    (by decide) selected_cut_17547

theorem selected_cut_17548 : selected 9 ⟨446787, by decide⟩
    (prefixPartial 12 70225) = some ⟨12, 2, 0, 446787, 70225, 3205, 65536⟩ := by
  decide +kernel

theorem context_12_70225_446787 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70225 ⟨446787, by decide⟩ :=
  accepted_of_selected 12 70225 ⟨446787, by decide⟩ ⟨12, 2, 0, 446787, 70225, 3205, 65536⟩
    (by decide) selected_cut_17548

theorem selected_cut_17549 : selected 9 ⟨446839, by decide⟩
    (prefixPartial 12 70226) = some ⟨12, 2, 0, 446839, 70226, 3021, 65536⟩ := by
  decide +kernel

theorem context_12_70226_446839 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70226 ⟨446839, by decide⟩ :=
  accepted_of_selected 12 70226 ⟨446839, by decide⟩ ⟨12, 2, 0, 446839, 70226, 3021, 65536⟩
    (by decide) selected_cut_17549

theorem selected_cut_17550 : selected 9 ⟨446901, by decide⟩
    (prefixPartial 12 70227) = some ⟨12, 2, 0, 446901, 70227, 3409, 65536⟩ := by
  decide +kernel

theorem context_12_70227_446901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70227 ⟨446901, by decide⟩ :=
  accepted_of_selected 12 70227 ⟨446901, by decide⟩ ⟨12, 2, 0, 446901, 70227, 3409, 65536⟩
    (by decide) selected_cut_17550

theorem unmarked_context_11_17556_446902 : frontier 10 ⟨446902, by decide⟩
    (prefixCache 11 17556) (prefixPartial 11 17556) = false := by
  decide +kernel

theorem node_context_11_17556_446902 : EJMOriginalGlobalDAGData.nodes 10 ⟨446902, by decide⟩ =
    .split (coordinate 11) (![⟨446719, by decide⟩,⟨446787, by decide⟩,⟨446839, by decide⟩,⟨446901, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17556_446902 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17556 ⟨446902, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17556
    ⟨446902, by decide⟩ (by decide) (![⟨446719, by decide⟩,⟨446787, by decide⟩,⟨446839, by decide⟩,⟨446901, by decide⟩]) unmarked_context_11_17556_446902 node_context_11_17556_446902
  intro a
  fin_cases a
  · exact context_12_70224_446719
  · exact context_12_70225_446787
  · exact context_12_70226_446839
  · exact context_12_70227_446901

theorem selected_cut_17551 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 70228) = some ⟨12, 1, 0, 895, 70228, 1, 65536⟩ := by
  decide +kernel

theorem context_12_70228_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70228 ⟨895, by decide⟩ :=
  accepted_of_selected 12 70228 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 70228, 1, 65536⟩
    (by decide) selected_cut_17551

theorem selected_cut_17552 : selected 9 ⟨446939, by decide⟩
    (prefixPartial 12 70229) = some ⟨12, 2, 0, 446939, 70229, 1813, 65536⟩ := by
  decide +kernel

theorem context_12_70229_446939 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70229 ⟨446939, by decide⟩ :=
  accepted_of_selected 12 70229 ⟨446939, by decide⟩ ⟨12, 2, 0, 446939, 70229, 1813, 65536⟩
    (by decide) selected_cut_17552

theorem selected_cut_17553 : selected 9 ⟨446990, by decide⟩
    (prefixPartial 12 70230) = some ⟨12, 2, 0, 446990, 70230, 3293, 65536⟩ := by
  decide +kernel

theorem context_12_70230_446990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70230 ⟨446990, by decide⟩ :=
  accepted_of_selected 12 70230 ⟨446990, by decide⟩ ⟨12, 2, 0, 446990, 70230, 3293, 65536⟩
    (by decide) selected_cut_17553

theorem selected_cut_17554 : selected 9 ⟨447066, by decide⟩
    (prefixPartial 12 70231) = some ⟨12, 2, 0, 447066, 70231, 3641, 65536⟩ := by
  decide +kernel

theorem context_12_70231_447066 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70231 ⟨447066, by decide⟩ :=
  accepted_of_selected 12 70231 ⟨447066, by decide⟩ ⟨12, 2, 0, 447066, 70231, 3641, 65536⟩
    (by decide) selected_cut_17554

theorem unmarked_context_11_17557_447067 : frontier 10 ⟨447067, by decide⟩
    (prefixCache 11 17557) (prefixPartial 11 17557) = false := by
  decide +kernel

theorem node_context_11_17557_447067 : EJMOriginalGlobalDAGData.nodes 10 ⟨447067, by decide⟩ =
    .split (coordinate 11) (![⟨895, by decide⟩,⟨446939, by decide⟩,⟨446990, by decide⟩,⟨447066, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17557_447067 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17557 ⟨447067, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17557
    ⟨447067, by decide⟩ (by decide) (![⟨895, by decide⟩,⟨446939, by decide⟩,⟨446990, by decide⟩,⟨447066, by decide⟩]) unmarked_context_11_17557_447067 node_context_11_17557_447067
  intro a
  fin_cases a
  · exact context_12_70228_895
  · exact context_12_70229_446939
  · exact context_12_70230_446990
  · exact context_12_70231_447066

theorem selected_cut_17555 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 70232) = some ⟨12, 1, 0, 895, 70232, 1, 65536⟩ := by
  decide +kernel

theorem context_12_70232_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70232 ⟨895, by decide⟩ :=
  accepted_of_selected 12 70232 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 70232, 1, 65536⟩
    (by decide) selected_cut_17555

theorem selected_cut_17556 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 70233) = some ⟨12, 1, 0, 895, 70233, 1, 65536⟩ := by
  decide +kernel

theorem context_12_70233_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70233 ⟨895, by decide⟩ :=
  accepted_of_selected 12 70233 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 70233, 1, 65536⟩
    (by decide) selected_cut_17556

theorem selected_cut_17557 : selected 9 ⟨447157, by decide⟩
    (prefixPartial 12 70234) = some ⟨12, 2, 0, 447157, 70234, 2721, 65536⟩ := by
  decide +kernel

theorem context_12_70234_447157 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70234 ⟨447157, by decide⟩ :=
  accepted_of_selected 12 70234 ⟨447157, by decide⟩ ⟨12, 2, 0, 447157, 70234, 2721, 65536⟩
    (by decide) selected_cut_17557

theorem selected_cut_17558 : selected 9 ⟨447203, by decide⟩
    (prefixPartial 12 70235) = some ⟨12, 2, 0, 447203, 70235, 3529, 65536⟩ := by
  decide +kernel

theorem context_12_70235_447203 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70235 ⟨447203, by decide⟩ :=
  accepted_of_selected 12 70235 ⟨447203, by decide⟩ ⟨12, 2, 0, 447203, 70235, 3529, 65536⟩
    (by decide) selected_cut_17558

theorem unmarked_context_11_17558_447204 : frontier 10 ⟨447204, by decide⟩
    (prefixCache 11 17558) (prefixPartial 11 17558) = false := by
  decide +kernel

theorem node_context_11_17558_447204 : EJMOriginalGlobalDAGData.nodes 10 ⟨447204, by decide⟩ =
    .split (coordinate 11) (![⟨895, by decide⟩,⟨895, by decide⟩,⟨447157, by decide⟩,⟨447203, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17558_447204 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17558 ⟨447204, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17558
    ⟨447204, by decide⟩ (by decide) (![⟨895, by decide⟩,⟨895, by decide⟩,⟨447157, by decide⟩,⟨447203, by decide⟩]) unmarked_context_11_17558_447204 node_context_11_17558_447204
  intro a
  fin_cases a
  · exact context_12_70232_895
  · exact context_12_70233_895
  · exact context_12_70234_447157
  · exact context_12_70235_447203

theorem selected_cut_17559 : selected 10 ⟨447259, by decide⟩
    (prefixPartial 11 17559) = some ⟨11, 2, 0, 447259, 17559, 2189, 262144⟩ := by
  decide +kernel

theorem context_11_17559_447259 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17559 ⟨447259, by decide⟩ :=
  accepted_of_selected 11 17559 ⟨447259, by decide⟩ ⟨11, 2, 0, 447259, 17559, 2189, 262144⟩
    (by decide) selected_cut_17559

theorem unmarked_context_10_4389_447260 : frontier 11 ⟨447260, by decide⟩
    (prefixCache 10 4389) (prefixPartial 10 4389) = false := by
  decide +kernel

theorem node_context_10_4389_447260 : EJMOriginalGlobalDAGData.nodes 11 ⟨447260, by decide⟩ =
    .split (coordinate 10) (![⟨446902, by decide⟩,⟨447067, by decide⟩,⟨447204, by decide⟩,⟨447259, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4389_447260 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4389 ⟨447260, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4389
    ⟨447260, by decide⟩ (by decide) (![⟨446902, by decide⟩,⟨447067, by decide⟩,⟨447204, by decide⟩,⟨447259, by decide⟩]) unmarked_context_10_4389_447260 node_context_10_4389_447260
  intro a
  fin_cases a
  · exact context_11_17556_446902
  · exact context_11_17557_447067
  · exact context_11_17558_447204
  · exact context_11_17559_447259

theorem selected_cut_17560 : selected 9 ⟨447306, by decide⟩
    (prefixPartial 12 70240) = some ⟨12, 2, 0, 447306, 70240, 2449, 65536⟩ := by
  decide +kernel

theorem context_12_70240_447306 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70240 ⟨447306, by decide⟩ :=
  accepted_of_selected 12 70240 ⟨447306, by decide⟩ ⟨12, 2, 0, 447306, 70240, 2449, 65536⟩
    (by decide) selected_cut_17560

theorem selected_cut_17561 : selected 9 ⟨447367, by decide⟩
    (prefixPartial 12 70241) = some ⟨12, 2, 0, 447367, 70241, 3125, 65536⟩ := by
  decide +kernel

theorem context_12_70241_447367 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70241 ⟨447367, by decide⟩ :=
  accepted_of_selected 12 70241 ⟨447367, by decide⟩ ⟨12, 2, 0, 447367, 70241, 3125, 65536⟩
    (by decide) selected_cut_17561

theorem selected_cut_17562 : selected 9 ⟨447406, by decide⟩
    (prefixPartial 12 70242) = some ⟨12, 2, 0, 447406, 70242, 2497, 65536⟩ := by
  decide +kernel

theorem context_12_70242_447406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70242 ⟨447406, by decide⟩ :=
  accepted_of_selected 12 70242 ⟨447406, by decide⟩ ⟨12, 2, 0, 447406, 70242, 2497, 65536⟩
    (by decide) selected_cut_17562

theorem selected_cut_17563 : selected 9 ⟨447460, by decide⟩
    (prefixPartial 12 70243) = some ⟨12, 2, 0, 447460, 70243, 3001, 65536⟩ := by
  decide +kernel

theorem context_12_70243_447460 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70243 ⟨447460, by decide⟩ :=
  accepted_of_selected 12 70243 ⟨447460, by decide⟩ ⟨12, 2, 0, 447460, 70243, 3001, 65536⟩
    (by decide) selected_cut_17563

theorem unmarked_context_11_17560_447461 : frontier 10 ⟨447461, by decide⟩
    (prefixCache 11 17560) (prefixPartial 11 17560) = false := by
  decide +kernel

theorem node_context_11_17560_447461 : EJMOriginalGlobalDAGData.nodes 10 ⟨447461, by decide⟩ =
    .split (coordinate 11) (![⟨447306, by decide⟩,⟨447367, by decide⟩,⟨447406, by decide⟩,⟨447460, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17560_447461 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17560 ⟨447461, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17560
    ⟨447461, by decide⟩ (by decide) (![⟨447306, by decide⟩,⟨447367, by decide⟩,⟨447406, by decide⟩,⟨447460, by decide⟩]) unmarked_context_11_17560_447461 node_context_11_17560_447461
  intro a
  fin_cases a
  · exact context_12_70240_447306
  · exact context_12_70241_447367
  · exact context_12_70242_447406
  · exact context_12_70243_447460

theorem selected_cut_17564 : selected 9 ⟨447506, by decide⟩
    (prefixPartial 12 70244) = some ⟨12, 2, 0, 447506, 70244, 2785, 65536⟩ := by
  decide +kernel

theorem context_12_70244_447506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70244 ⟨447506, by decide⟩ :=
  accepted_of_selected 12 70244 ⟨447506, by decide⟩ ⟨12, 2, 0, 447506, 70244, 2785, 65536⟩
    (by decide) selected_cut_17564

theorem selected_cut_17565 : selected 9 ⟨447544, by decide⟩
    (prefixPartial 12 70245) = some ⟨12, 2, 0, 447544, 70245, 2737, 65536⟩ := by
  decide +kernel

theorem context_12_70245_447544 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70245 ⟨447544, by decide⟩ :=
  accepted_of_selected 12 70245 ⟨447544, by decide⟩ ⟨12, 2, 0, 447544, 70245, 2737, 65536⟩
    (by decide) selected_cut_17565

theorem selected_cut_17566 : selected 9 ⟨447576, by decide⟩
    (prefixPartial 12 70246) = some ⟨12, 2, 0, 447576, 70246, 2585, 65536⟩ := by
  decide +kernel

theorem context_12_70246_447576 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70246 ⟨447576, by decide⟩ :=
  accepted_of_selected 12 70246 ⟨447576, by decide⟩ ⟨12, 2, 0, 447576, 70246, 2585, 65536⟩
    (by decide) selected_cut_17566

theorem selected_cut_17567 : selected 9 ⟨447616, by decide⟩
    (prefixPartial 12 70247) = some ⟨12, 2, 0, 447616, 70247, 2789, 65536⟩ := by
  decide +kernel

theorem context_12_70247_447616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70247 ⟨447616, by decide⟩ :=
  accepted_of_selected 12 70247 ⟨447616, by decide⟩ ⟨12, 2, 0, 447616, 70247, 2789, 65536⟩
    (by decide) selected_cut_17567

theorem unmarked_context_11_17561_447617 : frontier 10 ⟨447617, by decide⟩
    (prefixCache 11 17561) (prefixPartial 11 17561) = false := by
  decide +kernel

theorem node_context_11_17561_447617 : EJMOriginalGlobalDAGData.nodes 10 ⟨447617, by decide⟩ =
    .split (coordinate 11) (![⟨447506, by decide⟩,⟨447544, by decide⟩,⟨447576, by decide⟩,⟨447616, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17561_447617 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17561 ⟨447617, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17561
    ⟨447617, by decide⟩ (by decide) (![⟨447506, by decide⟩,⟨447544, by decide⟩,⟨447576, by decide⟩,⟨447616, by decide⟩]) unmarked_context_11_17561_447617 node_context_11_17561_447617
  intro a
  fin_cases a
  · exact context_12_70244_447506
  · exact context_12_70245_447544
  · exact context_12_70246_447576
  · exact context_12_70247_447616

theorem selected_cut_17568 : selected 9 ⟨447654, by decide⟩
    (prefixPartial 12 70248) = some ⟨12, 2, 0, 447654, 70248, 2497, 65536⟩ := by
  decide +kernel

theorem context_12_70248_447654 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70248 ⟨447654, by decide⟩ :=
  accepted_of_selected 12 70248 ⟨447654, by decide⟩ ⟨12, 2, 0, 447654, 70248, 2497, 65536⟩
    (by decide) selected_cut_17568

theorem selected_cut_17569 : selected 9 ⟨447693, by decide⟩
    (prefixPartial 12 70249) = some ⟨12, 2, 0, 447693, 70249, 2757, 65536⟩ := by
  decide +kernel

theorem context_12_70249_447693 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70249 ⟨447693, by decide⟩ :=
  accepted_of_selected 12 70249 ⟨447693, by decide⟩ ⟨12, 2, 0, 447693, 70249, 2757, 65536⟩
    (by decide) selected_cut_17569

theorem selected_cut_17570 : selected 9 ⟨445248, by decide⟩
    (prefixPartial 12 70250) = some ⟨12, 1, 0, 445248, 70250, 1, 65536⟩ := by
  decide +kernel

theorem context_12_70250_445248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 70250 ⟨445248, by decide⟩ :=
  accepted_of_selected 12 70250 ⟨445248, by decide⟩ ⟨12, 1, 0, 445248, 70250, 1, 65536⟩
    (by decide) selected_cut_17570

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
