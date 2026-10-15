/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover130
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_12_26211_331811 : frontier 9 ⟨331811, by decide⟩
    (prefixCache 12 26211) (prefixPartial 12 26211) = false := by
  decide +kernel

theorem node_context_12_26211_331811 : EJMOriginalGlobalDAGData.nodes 9 ⟨331811, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨331781, by decide⟩,⟨331805, by decide⟩,⟨331810, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26211_331811 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26211 ⟨331811, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26211
    ⟨331811, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨331781, by decide⟩,⟨331805, by decide⟩,⟨331810, by decide⟩]) unmarked_context_12_26211_331811 node_context_12_26211_331811
  intro a
  fin_cases a
  · exact context_13_104844_3444
  · exact context_13_104845_331781
  · exact context_13_104846_331805
  · exact context_13_104847_331810

theorem unmarked_context_11_6552_331812 : frontier 10 ⟨331812, by decide⟩
    (prefixCache 11 6552) (prefixPartial 11 6552) = false := by
  decide +kernel

theorem node_context_11_6552_331812 : EJMOriginalGlobalDAGData.nodes 10 ⟨331812, by decide⟩ =
    .split (coordinate 11) (![⟨331613, by decide⟩,⟨331715, by decide⟩,⟨331751, by decide⟩,⟨331811, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6552_331812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6552 ⟨331812, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6552
    ⟨331812, by decide⟩ (by decide) (![⟨331613, by decide⟩,⟨331715, by decide⟩,⟨331751, by decide⟩,⟨331811, by decide⟩]) unmarked_context_11_6552_331812 node_context_11_6552_331812
  intro a
  fin_cases a
  · exact context_12_26208_331613
  · exact context_12_26209_331715
  · exact context_12_26210_331751
  · exact context_12_26211_331811

theorem selected_cut_12580 : selected 9 ⟨331852, by decide⟩
    (prefixPartial 12 26212) = some ⟨12, 2, 0, 331852, 26212, 3201, 65536⟩ := by
  decide +kernel

theorem context_12_26212_331852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26212 ⟨331852, by decide⟩ :=
  accepted_of_selected 12 26212 ⟨331852, by decide⟩ ⟨12, 2, 0, 331852, 26212, 3201, 65536⟩
    (by decide) selected_cut_12580

theorem selected_cut_12581 : selected 9 ⟨289098, by decide⟩
    (prefixPartial 12 26213) = some ⟨12, 1, 0, 289098, 26213, 1, 65536⟩ := by
  decide +kernel

theorem context_12_26213_289098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26213 ⟨289098, by decide⟩ :=
  accepted_of_selected 12 26213 ⟨289098, by decide⟩ ⟨12, 1, 0, 289098, 26213, 1, 65536⟩
    (by decide) selected_cut_12581

theorem selected_cut_12582 : selected 9 ⟨331889, by decide⟩
    (prefixPartial 12 26214) = some ⟨12, 2, 0, 331889, 26214, 3173, 65536⟩ := by
  decide +kernel

theorem context_12_26214_331889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26214 ⟨331889, by decide⟩ :=
  accepted_of_selected 12 26214 ⟨331889, by decide⟩ ⟨12, 2, 0, 331889, 26214, 3173, 65536⟩
    (by decide) selected_cut_12582

theorem selected_cut_12583 : selected 9 ⟨331936, by decide⟩
    (prefixPartial 12 26215) = some ⟨12, 2, 0, 331936, 26215, 3965, 65536⟩ := by
  decide +kernel

theorem context_12_26215_331936 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26215 ⟨331936, by decide⟩ :=
  accepted_of_selected 12 26215 ⟨331936, by decide⟩ ⟨12, 2, 0, 331936, 26215, 3965, 65536⟩
    (by decide) selected_cut_12583

theorem unmarked_context_11_6553_331937 : frontier 10 ⟨331937, by decide⟩
    (prefixCache 11 6553) (prefixPartial 11 6553) = false := by
  decide +kernel

theorem node_context_11_6553_331937 : EJMOriginalGlobalDAGData.nodes 10 ⟨331937, by decide⟩ =
    .split (coordinate 11) (![⟨331852, by decide⟩,⟨289098, by decide⟩,⟨331889, by decide⟩,⟨331936, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6553_331937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6553 ⟨331937, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6553
    ⟨331937, by decide⟩ (by decide) (![⟨331852, by decide⟩,⟨289098, by decide⟩,⟨331889, by decide⟩,⟨331936, by decide⟩]) unmarked_context_11_6553_331937 node_context_11_6553_331937
  intro a
  fin_cases a
  · exact context_12_26212_331852
  · exact context_12_26213_289098
  · exact context_12_26214_331889
  · exact context_12_26215_331936

theorem selected_cut_12584 : selected 9 ⟨331974, by decide⟩
    (prefixPartial 12 26216) = some ⟨12, 2, 0, 331974, 26216, 2981, 65536⟩ := by
  decide +kernel

theorem context_12_26216_331974 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26216 ⟨331974, by decide⟩ :=
  accepted_of_selected 12 26216 ⟨331974, by decide⟩ ⟨12, 2, 0, 331974, 26216, 2981, 65536⟩
    (by decide) selected_cut_12584

theorem selected_cut_12585 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 104868) = some ⟨13, 1, 0, 3444, 104868, 1, 16384⟩ := by
  decide +kernel

theorem context_13_104868_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104868 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 104868 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 104868, 1, 16384⟩
    (by decide) selected_cut_12585

theorem selected_cut_12586 : selected 8 ⟨331996, by decide⟩
    (prefixPartial 13 104869) = some ⟨13, 2, 0, 331996, 104869, 1385, 16384⟩ := by
  decide +kernel

theorem context_13_104869_331996 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104869 ⟨331996, by decide⟩ :=
  accepted_of_selected 13 104869 ⟨331996, by decide⟩ ⟨13, 2, 0, 331996, 104869, 1385, 16384⟩
    (by decide) selected_cut_12586

theorem selected_cut_12587 : selected 8 ⟨332023, by decide⟩
    (prefixPartial 13 104870) = some ⟨13, 2, 0, 332023, 104870, 2397, 16384⟩ := by
  decide +kernel

theorem context_13_104870_332023 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104870 ⟨332023, by decide⟩ :=
  accepted_of_selected 13 104870 ⟨332023, by decide⟩ ⟨13, 2, 0, 332023, 104870, 2397, 16384⟩
    (by decide) selected_cut_12587

theorem selected_cut_12588 : selected 8 ⟨332039, by decide⟩
    (prefixPartial 13 104871) = some ⟨13, 2, 0, 332039, 104871, 1301, 16384⟩ := by
  decide +kernel

theorem context_13_104871_332039 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104871 ⟨332039, by decide⟩ :=
  accepted_of_selected 13 104871 ⟨332039, by decide⟩ ⟨13, 2, 0, 332039, 104871, 1301, 16384⟩
    (by decide) selected_cut_12588

theorem unmarked_context_12_26217_332040 : frontier 9 ⟨332040, by decide⟩
    (prefixCache 12 26217) (prefixPartial 12 26217) = false := by
  decide +kernel

theorem node_context_12_26217_332040 : EJMOriginalGlobalDAGData.nodes 9 ⟨332040, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨331996, by decide⟩,⟨332023, by decide⟩,⟨332039, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26217_332040 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26217 ⟨332040, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26217
    ⟨332040, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨331996, by decide⟩,⟨332023, by decide⟩,⟨332039, by decide⟩]) unmarked_context_12_26217_332040 node_context_12_26217_332040
  intro a
  fin_cases a
  · exact context_13_104868_3444
  · exact context_13_104869_331996
  · exact context_13_104870_332023
  · exact context_13_104871_332039

theorem selected_cut_12589 : selected 9 ⟨212113, by decide⟩
    (prefixPartial 12 26218) = some ⟨12, 1, 0, 212113, 26218, 1, 65536⟩ := by
  decide +kernel

theorem context_12_26218_212113 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26218 ⟨212113, by decide⟩ :=
  accepted_of_selected 12 26218 ⟨212113, by decide⟩ ⟨12, 1, 0, 212113, 26218, 1, 65536⟩
    (by decide) selected_cut_12589

theorem selected_cut_12590 : selected 9 ⟨332084, by decide⟩
    (prefixPartial 12 26219) = some ⟨12, 2, 0, 332084, 26219, 3573, 65536⟩ := by
  decide +kernel

theorem context_12_26219_332084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26219 ⟨332084, by decide⟩ :=
  accepted_of_selected 12 26219 ⟨332084, by decide⟩ ⟨12, 2, 0, 332084, 26219, 3573, 65536⟩
    (by decide) selected_cut_12590

theorem unmarked_context_11_6554_332085 : frontier 10 ⟨332085, by decide⟩
    (prefixCache 11 6554) (prefixPartial 11 6554) = false := by
  decide +kernel

theorem node_context_11_6554_332085 : EJMOriginalGlobalDAGData.nodes 10 ⟨332085, by decide⟩ =
    .split (coordinate 11) (![⟨331974, by decide⟩,⟨332040, by decide⟩,⟨212113, by decide⟩,⟨332084, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6554_332085 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6554 ⟨332085, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6554
    ⟨332085, by decide⟩ (by decide) (![⟨331974, by decide⟩,⟨332040, by decide⟩,⟨212113, by decide⟩,⟨332084, by decide⟩]) unmarked_context_11_6554_332085 node_context_11_6554_332085
  intro a
  fin_cases a
  · exact context_12_26216_331974
  · exact context_12_26217_332040
  · exact context_12_26218_212113
  · exact context_12_26219_332084

theorem selected_cut_12591 : selected 9 ⟨332122, by decide⟩
    (prefixPartial 12 26220) = some ⟨12, 2, 0, 332122, 26220, 3401, 65536⟩ := by
  decide +kernel

theorem context_12_26220_332122 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26220 ⟨332122, by decide⟩ :=
  accepted_of_selected 12 26220 ⟨332122, by decide⟩ ⟨12, 2, 0, 332122, 26220, 3401, 65536⟩
    (by decide) selected_cut_12591

theorem selected_cut_12592 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 104884) = some ⟨13, 1, 0, 3444, 104884, 1, 16384⟩ := by
  decide +kernel

theorem context_13_104884_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104884 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 104884 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 104884, 1, 16384⟩
    (by decide) selected_cut_12592

theorem selected_cut_12593 : selected 8 ⟨332147, by decide⟩
    (prefixPartial 13 104885) = some ⟨13, 2, 0, 332147, 104885, 1341, 16384⟩ := by
  decide +kernel

theorem context_13_104885_332147 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104885 ⟨332147, by decide⟩ :=
  accepted_of_selected 13 104885 ⟨332147, by decide⟩ ⟨13, 2, 0, 332147, 104885, 1341, 16384⟩
    (by decide) selected_cut_12593

theorem selected_cut_12594 : selected 8 ⟨332192, by decide⟩
    (prefixPartial 13 104886) = some ⟨13, 2, 0, 332192, 104886, 2773, 16384⟩ := by
  decide +kernel

theorem context_13_104886_332192 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104886 ⟨332192, by decide⟩ :=
  accepted_of_selected 13 104886 ⟨332192, by decide⟩ ⟨13, 2, 0, 332192, 104886, 2773, 16384⟩
    (by decide) selected_cut_12594

theorem selected_cut_12595 : selected 8 ⟨332216, by decide⟩
    (prefixPartial 13 104887) = some ⟨13, 2, 0, 332216, 104887, 1429, 16384⟩ := by
  decide +kernel

theorem context_13_104887_332216 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104887 ⟨332216, by decide⟩ :=
  accepted_of_selected 13 104887 ⟨332216, by decide⟩ ⟨13, 2, 0, 332216, 104887, 1429, 16384⟩
    (by decide) selected_cut_12595

theorem unmarked_context_12_26221_332217 : frontier 9 ⟨332217, by decide⟩
    (prefixCache 12 26221) (prefixPartial 12 26221) = false := by
  decide +kernel

theorem node_context_12_26221_332217 : EJMOriginalGlobalDAGData.nodes 9 ⟨332217, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨332147, by decide⟩,⟨332192, by decide⟩,⟨332216, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26221_332217 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26221 ⟨332217, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26221
    ⟨332217, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨332147, by decide⟩,⟨332192, by decide⟩,⟨332216, by decide⟩]) unmarked_context_12_26221_332217 node_context_12_26221_332217
  intro a
  fin_cases a
  · exact context_13_104884_3444
  · exact context_13_104885_332147
  · exact context_13_104886_332192
  · exact context_13_104887_332216

theorem selected_cut_12596 : selected 9 ⟨332255, by decide⟩
    (prefixPartial 12 26222) = some ⟨12, 2, 0, 332255, 26222, 2877, 65536⟩ := by
  decide +kernel

theorem context_12_26222_332255 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26222 ⟨332255, by decide⟩ :=
  accepted_of_selected 12 26222 ⟨332255, by decide⟩ ⟨12, 2, 0, 332255, 26222, 2877, 65536⟩
    (by decide) selected_cut_12596

theorem selected_cut_12597 : selected 9 ⟨332299, by decide⟩
    (prefixPartial 12 26223) = some ⟨12, 2, 0, 332299, 26223, 3745, 65536⟩ := by
  decide +kernel

theorem context_12_26223_332299 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26223 ⟨332299, by decide⟩ :=
  accepted_of_selected 12 26223 ⟨332299, by decide⟩ ⟨12, 2, 0, 332299, 26223, 3745, 65536⟩
    (by decide) selected_cut_12597

theorem unmarked_context_11_6555_332300 : frontier 10 ⟨332300, by decide⟩
    (prefixCache 11 6555) (prefixPartial 11 6555) = false := by
  decide +kernel

theorem node_context_11_6555_332300 : EJMOriginalGlobalDAGData.nodes 10 ⟨332300, by decide⟩ =
    .split (coordinate 11) (![⟨332122, by decide⟩,⟨332217, by decide⟩,⟨332255, by decide⟩,⟨332299, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6555_332300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6555 ⟨332300, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6555
    ⟨332300, by decide⟩ (by decide) (![⟨332122, by decide⟩,⟨332217, by decide⟩,⟨332255, by decide⟩,⟨332299, by decide⟩]) unmarked_context_11_6555_332300 node_context_11_6555_332300
  intro a
  fin_cases a
  · exact context_12_26220_332122
  · exact context_12_26221_332217
  · exact context_12_26222_332255
  · exact context_12_26223_332299

theorem unmarked_context_10_1638_332301 : frontier 11 ⟨332301, by decide⟩
    (prefixCache 10 1638) (prefixPartial 10 1638) = false := by
  decide +kernel

theorem node_context_10_1638_332301 : EJMOriginalGlobalDAGData.nodes 11 ⟨332301, by decide⟩ =
    .split (coordinate 10) (![⟨331812, by decide⟩,⟨331937, by decide⟩,⟨332085, by decide⟩,⟨332300, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1638_332301 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1638 ⟨332301, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1638
    ⟨332301, by decide⟩ (by decide) (![⟨331812, by decide⟩,⟨331937, by decide⟩,⟨332085, by decide⟩,⟨332300, by decide⟩]) unmarked_context_10_1638_332301 node_context_10_1638_332301
  intro a
  fin_cases a
  · exact context_11_6552_331812
  · exact context_11_6553_331937
  · exact context_11_6554_332085
  · exact context_11_6555_332300

theorem selected_cut_12598 : selected 9 ⟨332337, by decide⟩
    (prefixPartial 12 26224) = some ⟨12, 2, 0, 332337, 26224, 3105, 65536⟩ := by
  decide +kernel

theorem context_12_26224_332337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26224 ⟨332337, by decide⟩ :=
  accepted_of_selected 12 26224 ⟨332337, by decide⟩ ⟨12, 2, 0, 332337, 26224, 3105, 65536⟩
    (by decide) selected_cut_12598

theorem selected_cut_12599 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 104900) = some ⟨13, 1, 0, 3444, 104900, 1, 16384⟩ := by
  decide +kernel

theorem context_13_104900_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104900 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 104900 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 104900, 1, 16384⟩
    (by decide) selected_cut_12599

theorem selected_cut_12600 : selected 8 ⟨332365, by decide⟩
    (prefixPartial 13 104901) = some ⟨13, 2, 0, 332365, 104901, 1341, 16384⟩ := by
  decide +kernel

theorem context_13_104901_332365 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104901 ⟨332365, by decide⟩ :=
  accepted_of_selected 13 104901 ⟨332365, by decide⟩ ⟨13, 2, 0, 332365, 104901, 1341, 16384⟩
    (by decide) selected_cut_12600

theorem selected_cut_12601 : selected 8 ⟨332415, by decide⟩
    (prefixPartial 13 104902) = some ⟨13, 2, 0, 332415, 104902, 2809, 16384⟩ := by
  decide +kernel

theorem context_13_104902_332415 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104902 ⟨332415, by decide⟩ :=
  accepted_of_selected 13 104902 ⟨332415, by decide⟩ ⟨13, 2, 0, 332415, 104902, 2809, 16384⟩
    (by decide) selected_cut_12601

theorem selected_cut_12602 : selected 8 ⟨332426, by decide⟩
    (prefixPartial 13 104903) = some ⟨13, 2, 0, 332426, 104903, 1305, 16384⟩ := by
  decide +kernel

theorem context_13_104903_332426 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104903 ⟨332426, by decide⟩ :=
  accepted_of_selected 13 104903 ⟨332426, by decide⟩ ⟨13, 2, 0, 332426, 104903, 1305, 16384⟩
    (by decide) selected_cut_12602

theorem unmarked_context_12_26225_332427 : frontier 9 ⟨332427, by decide⟩
    (prefixCache 12 26225) (prefixPartial 12 26225) = false := by
  decide +kernel

theorem node_context_12_26225_332427 : EJMOriginalGlobalDAGData.nodes 9 ⟨332427, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨332365, by decide⟩,⟨332415, by decide⟩,⟨332426, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26225_332427 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26225 ⟨332427, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26225
    ⟨332427, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨332365, by decide⟩,⟨332415, by decide⟩,⟨332426, by decide⟩]) unmarked_context_12_26225_332427 node_context_12_26225_332427
  intro a
  fin_cases a
  · exact context_13_104900_3444
  · exact context_13_104901_332365
  · exact context_13_104902_332415
  · exact context_13_104903_332426

theorem selected_cut_12603 : selected 9 ⟨332462, by decide⟩
    (prefixPartial 12 26226) = some ⟨12, 2, 0, 332462, 26226, 3065, 65536⟩ := by
  decide +kernel

theorem context_12_26226_332462 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26226 ⟨332462, by decide⟩ :=
  accepted_of_selected 12 26226 ⟨332462, by decide⟩ ⟨12, 2, 0, 332462, 26226, 3065, 65536⟩
    (by decide) selected_cut_12603

theorem selected_cut_12604 : selected 9 ⟨332519, by decide⟩
    (prefixPartial 12 26227) = some ⟨12, 2, 0, 332519, 26227, 3881, 65536⟩ := by
  decide +kernel

theorem context_12_26227_332519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26227 ⟨332519, by decide⟩ :=
  accepted_of_selected 12 26227 ⟨332519, by decide⟩ ⟨12, 2, 0, 332519, 26227, 3881, 65536⟩
    (by decide) selected_cut_12604

theorem unmarked_context_11_6556_332520 : frontier 10 ⟨332520, by decide⟩
    (prefixCache 11 6556) (prefixPartial 11 6556) = false := by
  decide +kernel

theorem node_context_11_6556_332520 : EJMOriginalGlobalDAGData.nodes 10 ⟨332520, by decide⟩ =
    .split (coordinate 11) (![⟨332337, by decide⟩,⟨332427, by decide⟩,⟨332462, by decide⟩,⟨332519, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6556_332520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6556 ⟨332520, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6556
    ⟨332520, by decide⟩ (by decide) (![⟨332337, by decide⟩,⟨332427, by decide⟩,⟨332462, by decide⟩,⟨332519, by decide⟩]) unmarked_context_11_6556_332520 node_context_11_6556_332520
  intro a
  fin_cases a
  · exact context_12_26224_332337
  · exact context_12_26225_332427
  · exact context_12_26226_332462
  · exact context_12_26227_332519

theorem selected_cut_12605 : selected 9 ⟨332554, by decide⟩
    (prefixPartial 12 26228) = some ⟨12, 2, 0, 332554, 26228, 2785, 65536⟩ := by
  decide +kernel

theorem context_12_26228_332554 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26228 ⟨332554, by decide⟩ :=
  accepted_of_selected 12 26228 ⟨332554, by decide⟩ ⟨12, 2, 0, 332554, 26228, 2785, 65536⟩
    (by decide) selected_cut_12605

theorem selected_cut_12606 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 104916) = some ⟨13, 1, 0, 3444, 104916, 1, 16384⟩ := by
  decide +kernel

theorem context_13_104916_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104916 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 104916 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 104916, 1, 16384⟩
    (by decide) selected_cut_12606

theorem selected_cut_12607 : selected 8 ⟨332569, by decide⟩
    (prefixPartial 13 104917) = some ⟨13, 2, 0, 332569, 104917, 809, 16384⟩ := by
  decide +kernel

theorem context_13_104917_332569 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104917 ⟨332569, by decide⟩ :=
  accepted_of_selected 13 104917 ⟨332569, by decide⟩ ⟨13, 2, 0, 332569, 104917, 809, 16384⟩
    (by decide) selected_cut_12607

theorem selected_cut_12608 : selected 8 ⟨332602, by decide⟩
    (prefixPartial 13 104918) = some ⟨13, 2, 0, 332602, 104918, 2521, 16384⟩ := by
  decide +kernel

theorem context_13_104918_332602 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104918 ⟨332602, by decide⟩ :=
  accepted_of_selected 13 104918 ⟨332602, by decide⟩ ⟨13, 2, 0, 332602, 104918, 2521, 16384⟩
    (by decide) selected_cut_12608

theorem selected_cut_12609 : selected 8 ⟨332614, by decide⟩
    (prefixPartial 13 104919) = some ⟨13, 2, 0, 332614, 104919, 1225, 16384⟩ := by
  decide +kernel

theorem context_13_104919_332614 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104919 ⟨332614, by decide⟩ :=
  accepted_of_selected 13 104919 ⟨332614, by decide⟩ ⟨13, 2, 0, 332614, 104919, 1225, 16384⟩
    (by decide) selected_cut_12609

theorem unmarked_context_12_26229_332615 : frontier 9 ⟨332615, by decide⟩
    (prefixCache 12 26229) (prefixPartial 12 26229) = false := by
  decide +kernel

theorem node_context_12_26229_332615 : EJMOriginalGlobalDAGData.nodes 9 ⟨332615, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨332569, by decide⟩,⟨332602, by decide⟩,⟨332614, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26229_332615 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26229 ⟨332615, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26229
    ⟨332615, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨332569, by decide⟩,⟨332602, by decide⟩,⟨332614, by decide⟩]) unmarked_context_12_26229_332615 node_context_12_26229_332615
  intro a
  fin_cases a
  · exact context_13_104916_3444
  · exact context_13_104917_332569
  · exact context_13_104918_332602
  · exact context_13_104919_332614

theorem selected_cut_12610 : selected 9 ⟨332645, by decide⟩
    (prefixPartial 12 26230) = some ⟨12, 2, 0, 332645, 26230, 2781, 65536⟩ := by
  decide +kernel

theorem context_12_26230_332645 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26230 ⟨332645, by decide⟩ :=
  accepted_of_selected 12 26230 ⟨332645, by decide⟩ ⟨12, 2, 0, 332645, 26230, 2781, 65536⟩
    (by decide) selected_cut_12610

theorem selected_cut_12611 : selected 9 ⟨332688, by decide⟩
    (prefixPartial 12 26231) = some ⟨12, 2, 0, 332688, 26231, 3241, 65536⟩ := by
  decide +kernel

theorem context_12_26231_332688 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26231 ⟨332688, by decide⟩ :=
  accepted_of_selected 12 26231 ⟨332688, by decide⟩ ⟨12, 2, 0, 332688, 26231, 3241, 65536⟩
    (by decide) selected_cut_12611

theorem unmarked_context_11_6557_332689 : frontier 10 ⟨332689, by decide⟩
    (prefixCache 11 6557) (prefixPartial 11 6557) = false := by
  decide +kernel

theorem node_context_11_6557_332689 : EJMOriginalGlobalDAGData.nodes 10 ⟨332689, by decide⟩ =
    .split (coordinate 11) (![⟨332554, by decide⟩,⟨332615, by decide⟩,⟨332645, by decide⟩,⟨332688, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6557_332689 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6557 ⟨332689, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6557
    ⟨332689, by decide⟩ (by decide) (![⟨332554, by decide⟩,⟨332615, by decide⟩,⟨332645, by decide⟩,⟨332688, by decide⟩]) unmarked_context_11_6557_332689 node_context_11_6557_332689
  intro a
  fin_cases a
  · exact context_12_26228_332554
  · exact context_12_26229_332615
  · exact context_12_26230_332645
  · exact context_12_26231_332688

theorem selected_cut_12612 : selected 9 ⟨332721, by decide⟩
    (prefixPartial 12 26232) = some ⟨12, 2, 0, 332721, 26232, 2537, 65536⟩ := by
  decide +kernel

theorem context_12_26232_332721 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26232 ⟨332721, by decide⟩ :=
  accepted_of_selected 12 26232 ⟨332721, by decide⟩ ⟨12, 2, 0, 332721, 26232, 2537, 65536⟩
    (by decide) selected_cut_12612

theorem selected_cut_12613 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 104932) = some ⟨13, 1, 0, 3444, 104932, 1, 16384⟩ := by
  decide +kernel

theorem context_13_104932_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104932 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 104932 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 104932, 1, 16384⟩
    (by decide) selected_cut_12613

theorem selected_cut_12614 : selected 8 ⟨332732, by decide⟩
    (prefixPartial 13 104933) = some ⟨13, 2, 0, 332732, 104933, 505, 16384⟩ := by
  decide +kernel

theorem context_13_104933_332732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104933 ⟨332732, by decide⟩ :=
  accepted_of_selected 13 104933 ⟨332732, by decide⟩ ⟨13, 2, 0, 332732, 104933, 505, 16384⟩
    (by decide) selected_cut_12614

theorem selected_cut_12615 : selected 8 ⟨332764, by decide⟩
    (prefixPartial 13 104934) = some ⟨13, 2, 0, 332764, 104934, 2549, 16384⟩ := by
  decide +kernel

theorem context_13_104934_332764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104934 ⟨332764, by decide⟩ :=
  accepted_of_selected 13 104934 ⟨332764, by decide⟩ ⟨13, 2, 0, 332764, 104934, 2549, 16384⟩
    (by decide) selected_cut_12615

theorem selected_cut_12616 : selected 8 ⟨332775, by decide⟩
    (prefixPartial 13 104935) = some ⟨13, 2, 0, 332775, 104935, 1329, 16384⟩ := by
  decide +kernel

theorem context_13_104935_332775 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104935 ⟨332775, by decide⟩ :=
  accepted_of_selected 13 104935 ⟨332775, by decide⟩ ⟨13, 2, 0, 332775, 104935, 1329, 16384⟩
    (by decide) selected_cut_12616

theorem unmarked_context_12_26233_332776 : frontier 9 ⟨332776, by decide⟩
    (prefixCache 12 26233) (prefixPartial 12 26233) = false := by
  decide +kernel

theorem node_context_12_26233_332776 : EJMOriginalGlobalDAGData.nodes 9 ⟨332776, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨332732, by decide⟩,⟨332764, by decide⟩,⟨332775, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26233_332776 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26233 ⟨332776, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26233
    ⟨332776, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨332732, by decide⟩,⟨332764, by decide⟩,⟨332775, by decide⟩]) unmarked_context_12_26233_332776 node_context_12_26233_332776
  intro a
  fin_cases a
  · exact context_13_104932_3444
  · exact context_13_104933_332732
  · exact context_13_104934_332764
  · exact context_13_104935_332775

theorem selected_cut_12617 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 104936) = some ⟨13, 1, 0, 3444, 104936, 1, 16384⟩ := by
  decide +kernel

theorem context_13_104936_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104936 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 104936 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 104936, 1, 16384⟩
    (by decide) selected_cut_12617

theorem selected_cut_12618 : selected 8 ⟨332785, by decide⟩
    (prefixPartial 13 104937) = some ⟨13, 2, 0, 332785, 104937, 417, 16384⟩ := by
  decide +kernel

theorem context_13_104937_332785 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104937 ⟨332785, by decide⟩ :=
  accepted_of_selected 13 104937 ⟨332785, by decide⟩ ⟨13, 2, 0, 332785, 104937, 417, 16384⟩
    (by decide) selected_cut_12618

theorem selected_cut_12619 : selected 8 ⟨332819, by decide⟩
    (prefixPartial 13 104938) = some ⟨13, 2, 0, 332819, 104938, 2617, 16384⟩ := by
  decide +kernel

theorem context_13_104938_332819 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104938 ⟨332819, by decide⟩ :=
  accepted_of_selected 13 104938 ⟨332819, by decide⟩ ⟨13, 2, 0, 332819, 104938, 2617, 16384⟩
    (by decide) selected_cut_12619

theorem selected_cut_12620 : selected 8 ⟨332833, by decide⟩
    (prefixPartial 13 104939) = some ⟨13, 2, 0, 332833, 104939, 1229, 16384⟩ := by
  decide +kernel

theorem context_13_104939_332833 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104939 ⟨332833, by decide⟩ :=
  accepted_of_selected 13 104939 ⟨332833, by decide⟩ ⟨13, 2, 0, 332833, 104939, 1229, 16384⟩
    (by decide) selected_cut_12620

theorem unmarked_context_12_26234_332834 : frontier 9 ⟨332834, by decide⟩
    (prefixCache 12 26234) (prefixPartial 12 26234) = false := by
  decide +kernel

theorem node_context_12_26234_332834 : EJMOriginalGlobalDAGData.nodes 9 ⟨332834, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨332785, by decide⟩,⟨332819, by decide⟩,⟨332833, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26234_332834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26234 ⟨332834, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26234
    ⟨332834, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨332785, by decide⟩,⟨332819, by decide⟩,⟨332833, by decide⟩]) unmarked_context_12_26234_332834 node_context_12_26234_332834
  intro a
  fin_cases a
  · exact context_13_104936_3444
  · exact context_13_104937_332785
  · exact context_13_104938_332819
  · exact context_13_104939_332833

theorem selected_cut_12621 : selected 9 ⟨332870, by decide⟩
    (prefixPartial 12 26235) = some ⟨12, 2, 0, 332870, 26235, 2825, 65536⟩ := by
  decide +kernel

theorem context_12_26235_332870 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26235 ⟨332870, by decide⟩ :=
  accepted_of_selected 12 26235 ⟨332870, by decide⟩ ⟨12, 2, 0, 332870, 26235, 2825, 65536⟩
    (by decide) selected_cut_12621

theorem unmarked_context_11_6558_332871 : frontier 10 ⟨332871, by decide⟩
    (prefixCache 11 6558) (prefixPartial 11 6558) = false := by
  decide +kernel

theorem node_context_11_6558_332871 : EJMOriginalGlobalDAGData.nodes 10 ⟨332871, by decide⟩ =
    .split (coordinate 11) (![⟨332721, by decide⟩,⟨332776, by decide⟩,⟨332834, by decide⟩,⟨332870, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6558_332871 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6558 ⟨332871, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6558
    ⟨332871, by decide⟩ (by decide) (![⟨332721, by decide⟩,⟨332776, by decide⟩,⟨332834, by decide⟩,⟨332870, by decide⟩]) unmarked_context_11_6558_332871 node_context_11_6558_332871
  intro a
  fin_cases a
  · exact context_12_26232_332721
  · exact context_12_26233_332776
  · exact context_12_26234_332834
  · exact context_12_26235_332870

theorem selected_cut_12622 : selected 9 ⟨332899, by decide⟩
    (prefixPartial 12 26236) = some ⟨12, 2, 0, 332899, 26236, 2773, 65536⟩ := by
  decide +kernel

theorem context_12_26236_332899 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26236 ⟨332899, by decide⟩ :=
  accepted_of_selected 12 26236 ⟨332899, by decide⟩ ⟨12, 2, 0, 332899, 26236, 2773, 65536⟩
    (by decide) selected_cut_12622

theorem selected_cut_12623 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 104948) = some ⟨13, 1, 0, 3444, 104948, 1, 16384⟩ := by
  decide +kernel

theorem context_13_104948_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104948 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 104948 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 104948, 1, 16384⟩
    (by decide) selected_cut_12623

theorem selected_cut_12624 : selected 8 ⟨332905, by decide⟩
    (prefixPartial 13 104949) = some ⟨13, 2, 0, 332905, 104949, 213, 16384⟩ := by
  decide +kernel

theorem context_13_104949_332905 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104949 ⟨332905, by decide⟩ :=
  accepted_of_selected 13 104949 ⟨332905, by decide⟩ ⟨13, 2, 0, 332905, 104949, 213, 16384⟩
    (by decide) selected_cut_12624

theorem selected_cut_12625 : selected 8 ⟨332951, by decide⟩
    (prefixPartial 13 104950) = some ⟨13, 2, 0, 332951, 104950, 2913, 16384⟩ := by
  decide +kernel

theorem context_13_104950_332951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104950 ⟨332951, by decide⟩ :=
  accepted_of_selected 13 104950 ⟨332951, by decide⟩ ⟨13, 2, 0, 332951, 104950, 2913, 16384⟩
    (by decide) selected_cut_12625

theorem selected_cut_12626 : selected 8 ⟨332969, by decide⟩
    (prefixPartial 13 104951) = some ⟨13, 2, 0, 332969, 104951, 1313, 16384⟩ := by
  decide +kernel

theorem context_13_104951_332969 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104951 ⟨332969, by decide⟩ :=
  accepted_of_selected 13 104951 ⟨332969, by decide⟩ ⟨13, 2, 0, 332969, 104951, 1313, 16384⟩
    (by decide) selected_cut_12626

theorem unmarked_context_12_26237_332970 : frontier 9 ⟨332970, by decide⟩
    (prefixCache 12 26237) (prefixPartial 12 26237) = false := by
  decide +kernel

theorem node_context_12_26237_332970 : EJMOriginalGlobalDAGData.nodes 9 ⟨332970, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨332905, by decide⟩,⟨332951, by decide⟩,⟨332969, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26237_332970 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26237 ⟨332970, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26237
    ⟨332970, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨332905, by decide⟩,⟨332951, by decide⟩,⟨332969, by decide⟩]) unmarked_context_12_26237_332970 node_context_12_26237_332970
  intro a
  fin_cases a
  · exact context_13_104948_3444
  · exact context_13_104949_332905
  · exact context_13_104950_332951
  · exact context_13_104951_332969

theorem selected_cut_12627 : selected 9 ⟨333002, by decide⟩
    (prefixPartial 12 26238) = some ⟨12, 2, 0, 333002, 26238, 2457, 65536⟩ := by
  decide +kernel

theorem context_12_26238_333002 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26238 ⟨333002, by decide⟩ :=
  accepted_of_selected 12 26238 ⟨333002, by decide⟩ ⟨12, 2, 0, 333002, 26238, 2457, 65536⟩
    (by decide) selected_cut_12627

theorem selected_cut_12628 : selected 9 ⟨333038, by decide⟩
    (prefixPartial 12 26239) = some ⟨12, 2, 0, 333038, 26239, 3033, 65536⟩ := by
  decide +kernel

theorem context_12_26239_333038 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26239 ⟨333038, by decide⟩ :=
  accepted_of_selected 12 26239 ⟨333038, by decide⟩ ⟨12, 2, 0, 333038, 26239, 3033, 65536⟩
    (by decide) selected_cut_12628

theorem unmarked_context_11_6559_333039 : frontier 10 ⟨333039, by decide⟩
    (prefixCache 11 6559) (prefixPartial 11 6559) = false := by
  decide +kernel

theorem node_context_11_6559_333039 : EJMOriginalGlobalDAGData.nodes 10 ⟨333039, by decide⟩ =
    .split (coordinate 11) (![⟨332899, by decide⟩,⟨332970, by decide⟩,⟨333002, by decide⟩,⟨333038, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6559_333039 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6559 ⟨333039, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6559
    ⟨333039, by decide⟩ (by decide) (![⟨332899, by decide⟩,⟨332970, by decide⟩,⟨333002, by decide⟩,⟨333038, by decide⟩]) unmarked_context_11_6559_333039 node_context_11_6559_333039
  intro a
  fin_cases a
  · exact context_12_26236_332899
  · exact context_12_26237_332970
  · exact context_12_26238_333002
  · exact context_12_26239_333038

theorem unmarked_context_10_1639_333040 : frontier 11 ⟨333040, by decide⟩
    (prefixCache 10 1639) (prefixPartial 10 1639) = false := by
  decide +kernel

theorem node_context_10_1639_333040 : EJMOriginalGlobalDAGData.nodes 11 ⟨333040, by decide⟩ =
    .split (coordinate 10) (![⟨332520, by decide⟩,⟨332689, by decide⟩,⟨332871, by decide⟩,⟨333039, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1639_333040 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1639 ⟨333040, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1639
    ⟨333040, by decide⟩ (by decide) (![⟨332520, by decide⟩,⟨332689, by decide⟩,⟨332871, by decide⟩,⟨333039, by decide⟩]) unmarked_context_10_1639_333040 node_context_10_1639_333040
  intro a
  fin_cases a
  · exact context_11_6556_332520
  · exact context_11_6557_332689
  · exact context_11_6558_332871
  · exact context_11_6559_333039

theorem unmarked_context_9_409_333041 : frontier 12 ⟨333041, by decide⟩
    (prefixCache 9 409) (prefixPartial 9 409) = false := by
  decide +kernel

theorem node_context_9_409_333041 : EJMOriginalGlobalDAGData.nodes 12 ⟨333041, by decide⟩ =
    .split (coordinate 9) (![⟨330803, by decide⟩,⟨331575, by decide⟩,⟨332301, by decide⟩,⟨333040, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_409_333041 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 409 ⟨333041, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 409
    ⟨333041, by decide⟩ (by decide) (![⟨330803, by decide⟩,⟨331575, by decide⟩,⟨332301, by decide⟩,⟨333040, by decide⟩]) unmarked_context_9_409_333041 node_context_9_409_333041
  intro a
  fin_cases a
  · exact context_10_1636_330803
  · exact context_10_1637_331575
  · exact context_10_1638_332301
  · exact context_10_1639_333040

theorem selected_cut_12629 : selected 9 ⟨333066, by decide⟩
    (prefixPartial 12 26240) = some ⟨12, 2, 0, 333066, 26240, 2133, 65536⟩ := by
  decide +kernel

theorem context_12_26240_333066 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26240 ⟨333066, by decide⟩ :=
  accepted_of_selected 12 26240 ⟨333066, by decide⟩ ⟨12, 2, 0, 333066, 26240, 2133, 65536⟩
    (by decide) selected_cut_12629

theorem selected_cut_12630 : selected 9 ⟨333100, by decide⟩
    (prefixPartial 12 26241) = some ⟨12, 2, 0, 333100, 26241, 2385, 65536⟩ := by
  decide +kernel

theorem context_12_26241_333100 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26241 ⟨333100, by decide⟩ :=
  accepted_of_selected 12 26241 ⟨333100, by decide⟩ ⟨12, 2, 0, 333100, 26241, 2385, 65536⟩
    (by decide) selected_cut_12630

theorem selected_cut_12631 : selected 9 ⟨333131, by decide⟩
    (prefixPartial 12 26242) = some ⟨12, 2, 0, 333131, 26242, 1901, 65536⟩ := by
  decide +kernel

theorem context_12_26242_333131 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26242 ⟨333131, by decide⟩ :=
  accepted_of_selected 12 26242 ⟨333131, by decide⟩ ⟨12, 2, 0, 333131, 26242, 1901, 65536⟩
    (by decide) selected_cut_12631

theorem selected_cut_12632 : selected 9 ⟨333163, by decide⟩
    (prefixPartial 12 26243) = some ⟨12, 2, 0, 333163, 26243, 2537, 65536⟩ := by
  decide +kernel

theorem context_12_26243_333163 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26243 ⟨333163, by decide⟩ :=
  accepted_of_selected 12 26243 ⟨333163, by decide⟩ ⟨12, 2, 0, 333163, 26243, 2537, 65536⟩
    (by decide) selected_cut_12632

theorem unmarked_context_11_6560_333164 : frontier 10 ⟨333164, by decide⟩
    (prefixCache 11 6560) (prefixPartial 11 6560) = false := by
  decide +kernel

theorem node_context_11_6560_333164 : EJMOriginalGlobalDAGData.nodes 10 ⟨333164, by decide⟩ =
    .split (coordinate 11) (![⟨333066, by decide⟩,⟨333100, by decide⟩,⟨333131, by decide⟩,⟨333163, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6560_333164 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6560 ⟨333164, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6560
    ⟨333164, by decide⟩ (by decide) (![⟨333066, by decide⟩,⟨333100, by decide⟩,⟨333131, by decide⟩,⟨333163, by decide⟩]) unmarked_context_11_6560_333164 node_context_11_6560_333164
  intro a
  fin_cases a
  · exact context_12_26240_333066
  · exact context_12_26241_333100
  · exact context_12_26242_333131
  · exact context_12_26243_333163

theorem selected_cut_12633 : selected 9 ⟨333190, by decide⟩
    (prefixPartial 12 26244) = some ⟨12, 2, 0, 333190, 26244, 2205, 65536⟩ := by
  decide +kernel

theorem context_12_26244_333190 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26244 ⟨333190, by decide⟩ :=
  accepted_of_selected 12 26244 ⟨333190, by decide⟩ ⟨12, 2, 0, 333190, 26244, 2205, 65536⟩
    (by decide) selected_cut_12633

theorem selected_cut_12634 : selected 9 ⟨333220, by decide⟩
    (prefixPartial 12 26245) = some ⟨12, 2, 0, 333220, 26245, 2201, 65536⟩ := by
  decide +kernel

theorem context_12_26245_333220 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26245 ⟨333220, by decide⟩ :=
  accepted_of_selected 12 26245 ⟨333220, by decide⟩ ⟨12, 2, 0, 333220, 26245, 2201, 65536⟩
    (by decide) selected_cut_12634

theorem selected_cut_12635 : selected 9 ⟨333247, by decide⟩
    (prefixPartial 12 26246) = some ⟨12, 2, 0, 333247, 26246, 1953, 65536⟩ := by
  decide +kernel

theorem context_12_26246_333247 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26246 ⟨333247, by decide⟩ :=
  accepted_of_selected 12 26246 ⟨333247, by decide⟩ ⟨12, 2, 0, 333247, 26246, 1953, 65536⟩
    (by decide) selected_cut_12635

theorem selected_cut_12636 : selected 9 ⟨333276, by decide⟩
    (prefixPartial 12 26247) = some ⟨12, 2, 0, 333276, 26247, 2453, 65536⟩ := by
  decide +kernel

theorem context_12_26247_333276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26247 ⟨333276, by decide⟩ :=
  accepted_of_selected 12 26247 ⟨333276, by decide⟩ ⟨12, 2, 0, 333276, 26247, 2453, 65536⟩
    (by decide) selected_cut_12636

theorem unmarked_context_11_6561_333277 : frontier 10 ⟨333277, by decide⟩
    (prefixCache 11 6561) (prefixPartial 11 6561) = false := by
  decide +kernel

theorem node_context_11_6561_333277 : EJMOriginalGlobalDAGData.nodes 10 ⟨333277, by decide⟩ =
    .split (coordinate 11) (![⟨333190, by decide⟩,⟨333220, by decide⟩,⟨333247, by decide⟩,⟨333276, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6561_333277 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6561 ⟨333277, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6561
    ⟨333277, by decide⟩ (by decide) (![⟨333190, by decide⟩,⟨333220, by decide⟩,⟨333247, by decide⟩,⟨333276, by decide⟩]) unmarked_context_11_6561_333277 node_context_11_6561_333277
  intro a
  fin_cases a
  · exact context_12_26244_333190
  · exact context_12_26245_333220
  · exact context_12_26246_333247
  · exact context_12_26247_333276

theorem selected_cut_12637 : selected 9 ⟨333303, by decide⟩
    (prefixPartial 12 26248) = some ⟨12, 2, 0, 333303, 26248, 2001, 65536⟩ := by
  decide +kernel

theorem context_12_26248_333303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26248 ⟨333303, by decide⟩ :=
  accepted_of_selected 12 26248 ⟨333303, by decide⟩ ⟨12, 2, 0, 333303, 26248, 2001, 65536⟩
    (by decide) selected_cut_12637

theorem selected_cut_12638 : selected 9 ⟨333330, by decide⟩
    (prefixPartial 12 26249) = some ⟨12, 2, 0, 333330, 26249, 2193, 65536⟩ := by
  decide +kernel

theorem context_12_26249_333330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26249 ⟨333330, by decide⟩ :=
  accepted_of_selected 12 26249 ⟨333330, by decide⟩ ⟨12, 2, 0, 333330, 26249, 2193, 65536⟩
    (by decide) selected_cut_12638

theorem selected_cut_12639 : selected 9 ⟨333367, by decide⟩
    (prefixPartial 12 26250) = some ⟨12, 2, 0, 333367, 26250, 1145, 65536⟩ := by
  decide +kernel

theorem context_12_26250_333367 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26250 ⟨333367, by decide⟩ :=
  accepted_of_selected 12 26250 ⟨333367, by decide⟩ ⟨12, 2, 0, 333367, 26250, 1145, 65536⟩
    (by decide) selected_cut_12639

theorem selected_cut_12640 : selected 9 ⟨333397, by decide⟩
    (prefixPartial 12 26251) = some ⟨12, 2, 0, 333397, 26251, 2137, 65536⟩ := by
  decide +kernel

theorem context_12_26251_333397 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26251 ⟨333397, by decide⟩ :=
  accepted_of_selected 12 26251 ⟨333397, by decide⟩ ⟨12, 2, 0, 333397, 26251, 2137, 65536⟩
    (by decide) selected_cut_12640

theorem unmarked_context_11_6562_333398 : frontier 10 ⟨333398, by decide⟩
    (prefixCache 11 6562) (prefixPartial 11 6562) = false := by
  decide +kernel

theorem node_context_11_6562_333398 : EJMOriginalGlobalDAGData.nodes 10 ⟨333398, by decide⟩ =
    .split (coordinate 11) (![⟨333303, by decide⟩,⟨333330, by decide⟩,⟨333367, by decide⟩,⟨333397, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6562_333398 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6562 ⟨333398, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6562
    ⟨333398, by decide⟩ (by decide) (![⟨333303, by decide⟩,⟨333330, by decide⟩,⟨333367, by decide⟩,⟨333397, by decide⟩]) unmarked_context_11_6562_333398 node_context_11_6562_333398
  intro a
  fin_cases a
  · exact context_12_26248_333303
  · exact context_12_26249_333330
  · exact context_12_26250_333367
  · exact context_12_26251_333397

theorem selected_cut_12641 : selected 9 ⟨333424, by decide⟩
    (prefixPartial 12 26252) = some ⟨12, 2, 0, 333424, 26252, 2129, 65536⟩ := by
  decide +kernel

theorem context_12_26252_333424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26252 ⟨333424, by decide⟩ :=
  accepted_of_selected 12 26252 ⟨333424, by decide⟩ ⟨12, 2, 0, 333424, 26252, 2129, 65536⟩
    (by decide) selected_cut_12641

theorem selected_cut_12642 : selected 9 ⟨333454, by decide⟩
    (prefixPartial 12 26253) = some ⟨12, 2, 0, 333454, 26253, 2145, 65536⟩ := by
  decide +kernel

theorem context_12_26253_333454 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26253 ⟨333454, by decide⟩ :=
  accepted_of_selected 12 26253 ⟨333454, by decide⟩ ⟨12, 2, 0, 333454, 26253, 2145, 65536⟩
    (by decide) selected_cut_12642

theorem selected_cut_12643 : selected 9 ⟨333483, by decide⟩
    (prefixPartial 12 26254) = some ⟨12, 2, 0, 333483, 26254, 1757, 65536⟩ := by
  decide +kernel

theorem context_12_26254_333483 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26254 ⟨333483, by decide⟩ :=
  accepted_of_selected 12 26254 ⟨333483, by decide⟩ ⟨12, 2, 0, 333483, 26254, 1757, 65536⟩
    (by decide) selected_cut_12643

theorem selected_cut_12644 : selected 9 ⟨333502, by decide⟩
    (prefixPartial 12 26255) = some ⟨12, 2, 0, 333502, 26255, 2197, 65536⟩ := by
  decide +kernel

theorem context_12_26255_333502 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26255 ⟨333502, by decide⟩ :=
  accepted_of_selected 12 26255 ⟨333502, by decide⟩ ⟨12, 2, 0, 333502, 26255, 2197, 65536⟩
    (by decide) selected_cut_12644

theorem unmarked_context_11_6563_333503 : frontier 10 ⟨333503, by decide⟩
    (prefixCache 11 6563) (prefixPartial 11 6563) = false := by
  decide +kernel

theorem node_context_11_6563_333503 : EJMOriginalGlobalDAGData.nodes 10 ⟨333503, by decide⟩ =
    .split (coordinate 11) (![⟨333424, by decide⟩,⟨333454, by decide⟩,⟨333483, by decide⟩,⟨333502, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6563_333503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6563 ⟨333503, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6563
    ⟨333503, by decide⟩ (by decide) (![⟨333424, by decide⟩,⟨333454, by decide⟩,⟨333483, by decide⟩,⟨333502, by decide⟩]) unmarked_context_11_6563_333503 node_context_11_6563_333503
  intro a
  fin_cases a
  · exact context_12_26252_333424
  · exact context_12_26253_333454
  · exact context_12_26254_333483
  · exact context_12_26255_333502

theorem unmarked_context_10_1640_333504 : frontier 11 ⟨333504, by decide⟩
    (prefixCache 10 1640) (prefixPartial 10 1640) = false := by
  decide +kernel

theorem node_context_10_1640_333504 : EJMOriginalGlobalDAGData.nodes 11 ⟨333504, by decide⟩ =
    .split (coordinate 10) (![⟨333164, by decide⟩,⟨333277, by decide⟩,⟨333398, by decide⟩,⟨333503, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1640_333504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1640 ⟨333504, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1640
    ⟨333504, by decide⟩ (by decide) (![⟨333164, by decide⟩,⟨333277, by decide⟩,⟨333398, by decide⟩,⟨333503, by decide⟩]) unmarked_context_10_1640_333504 node_context_10_1640_333504
  intro a
  fin_cases a
  · exact context_11_6560_333164
  · exact context_11_6561_333277
  · exact context_11_6562_333398
  · exact context_11_6563_333503

theorem selected_cut_12645 : selected 9 ⟨333527, by decide⟩
    (prefixPartial 12 26256) = some ⟨12, 2, 0, 333527, 26256, 1981, 65536⟩ := by
  decide +kernel

theorem context_12_26256_333527 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26256 ⟨333527, by decide⟩ :=
  accepted_of_selected 12 26256 ⟨333527, by decide⟩ ⟨12, 2, 0, 333527, 26256, 1981, 65536⟩
    (by decide) selected_cut_12645

theorem selected_cut_12646 : selected 9 ⟨333555, by decide⟩
    (prefixPartial 12 26257) = some ⟨12, 2, 0, 333555, 26257, 2277, 65536⟩ := by
  decide +kernel

theorem context_12_26257_333555 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26257 ⟨333555, by decide⟩ :=
  accepted_of_selected 12 26257 ⟨333555, by decide⟩ ⟨12, 2, 0, 333555, 26257, 2277, 65536⟩
    (by decide) selected_cut_12646

theorem selected_cut_12647 : selected 9 ⟨333578, by decide⟩
    (prefixPartial 12 26258) = some ⟨12, 2, 0, 333578, 26258, 1825, 65536⟩ := by
  decide +kernel

theorem context_12_26258_333578 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26258 ⟨333578, by decide⟩ :=
  accepted_of_selected 12 26258 ⟨333578, by decide⟩ ⟨12, 2, 0, 333578, 26258, 1825, 65536⟩
    (by decide) selected_cut_12647

theorem selected_cut_12648 : selected 9 ⟨333605, by decide⟩
    (prefixPartial 12 26259) = some ⟨12, 2, 0, 333605, 26259, 2401, 65536⟩ := by
  decide +kernel

theorem context_12_26259_333605 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26259 ⟨333605, by decide⟩ :=
  accepted_of_selected 12 26259 ⟨333605, by decide⟩ ⟨12, 2, 0, 333605, 26259, 2401, 65536⟩
    (by decide) selected_cut_12648

theorem unmarked_context_11_6564_333606 : frontier 10 ⟨333606, by decide⟩
    (prefixCache 11 6564) (prefixPartial 11 6564) = false := by
  decide +kernel

theorem node_context_11_6564_333606 : EJMOriginalGlobalDAGData.nodes 10 ⟨333606, by decide⟩ =
    .split (coordinate 11) (![⟨333527, by decide⟩,⟨333555, by decide⟩,⟨333578, by decide⟩,⟨333605, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6564_333606 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6564 ⟨333606, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6564
    ⟨333606, by decide⟩ (by decide) (![⟨333527, by decide⟩,⟨333555, by decide⟩,⟨333578, by decide⟩,⟨333605, by decide⟩]) unmarked_context_11_6564_333606 node_context_11_6564_333606
  intro a
  fin_cases a
  · exact context_12_26256_333527
  · exact context_12_26257_333555
  · exact context_12_26258_333578
  · exact context_12_26259_333605

theorem selected_cut_12649 : selected 9 ⟨333637, by decide⟩
    (prefixPartial 12 26260) = some ⟨12, 2, 0, 333637, 26260, 2657, 65536⟩ := by
  decide +kernel

theorem context_12_26260_333637 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26260 ⟨333637, by decide⟩ :=
  accepted_of_selected 12 26260 ⟨333637, by decide⟩ ⟨12, 2, 0, 333637, 26260, 2657, 65536⟩
    (by decide) selected_cut_12649

theorem selected_cut_12650 : selected 9 ⟨333638, by decide⟩
    (prefixPartial 12 26261) = some ⟨12, 1, 0, 333638, 26261, 1, 65536⟩ := by
  decide +kernel

theorem context_12_26261_333638 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26261 ⟨333638, by decide⟩ :=
  accepted_of_selected 12 26261 ⟨333638, by decide⟩ ⟨12, 1, 0, 333638, 26261, 1, 65536⟩
    (by decide) selected_cut_12650

theorem selected_cut_12651 : selected 9 ⟨333659, by decide⟩
    (prefixPartial 12 26262) = some ⟨12, 2, 0, 333659, 26262, 2677, 65536⟩ := by
  decide +kernel

theorem context_12_26262_333659 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26262 ⟨333659, by decide⟩ :=
  accepted_of_selected 12 26262 ⟨333659, by decide⟩ ⟨12, 2, 0, 333659, 26262, 2677, 65536⟩
    (by decide) selected_cut_12651

theorem selected_cut_12652 : selected 9 ⟨333699, by decide⟩
    (prefixPartial 12 26263) = some ⟨12, 2, 0, 333699, 26263, 3125, 65536⟩ := by
  decide +kernel

theorem context_12_26263_333699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26263 ⟨333699, by decide⟩ :=
  accepted_of_selected 12 26263 ⟨333699, by decide⟩ ⟨12, 2, 0, 333699, 26263, 3125, 65536⟩
    (by decide) selected_cut_12652

theorem unmarked_context_11_6565_333700 : frontier 10 ⟨333700, by decide⟩
    (prefixCache 11 6565) (prefixPartial 11 6565) = false := by
  decide +kernel

theorem node_context_11_6565_333700 : EJMOriginalGlobalDAGData.nodes 10 ⟨333700, by decide⟩ =
    .split (coordinate 11) (![⟨333637, by decide⟩,⟨333638, by decide⟩,⟨333659, by decide⟩,⟨333699, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6565_333700 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6565 ⟨333700, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6565
    ⟨333700, by decide⟩ (by decide) (![⟨333637, by decide⟩,⟨333638, by decide⟩,⟨333659, by decide⟩,⟨333699, by decide⟩]) unmarked_context_11_6565_333700 node_context_11_6565_333700
  intro a
  fin_cases a
  · exact context_12_26260_333637
  · exact context_12_26261_333638
  · exact context_12_26262_333659
  · exact context_12_26263_333699

theorem selected_cut_12653 : selected 9 ⟨333721, by decide⟩
    (prefixPartial 12 26264) = some ⟨12, 2, 0, 333721, 26264, 1861, 65536⟩ := by
  decide +kernel

theorem context_12_26264_333721 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26264 ⟨333721, by decide⟩ :=
  accepted_of_selected 12 26264 ⟨333721, by decide⟩ ⟨12, 2, 0, 333721, 26264, 1861, 65536⟩
    (by decide) selected_cut_12653

theorem selected_cut_12654 : selected 9 ⟨333746, by decide⟩
    (prefixPartial 12 26265) = some ⟨12, 2, 0, 333746, 26265, 2165, 65536⟩ := by
  decide +kernel

theorem context_12_26265_333746 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26265 ⟨333746, by decide⟩ :=
  accepted_of_selected 12 26265 ⟨333746, by decide⟩ ⟨12, 2, 0, 333746, 26265, 2165, 65536⟩
    (by decide) selected_cut_12654

theorem selected_cut_12655 : selected 9 ⟨290673, by decide⟩
    (prefixPartial 12 26266) = some ⟨12, 1, 0, 290673, 26266, 1, 65536⟩ := by
  decide +kernel

theorem context_12_26266_290673 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26266 ⟨290673, by decide⟩ :=
  accepted_of_selected 12 26266 ⟨290673, by decide⟩ ⟨12, 1, 0, 290673, 26266, 1, 65536⟩
    (by decide) selected_cut_12655

theorem selected_cut_12656 : selected 9 ⟨333769, by decide⟩
    (prefixPartial 12 26267) = some ⟨12, 2, 0, 333769, 26267, 2097, 65536⟩ := by
  decide +kernel

theorem context_12_26267_333769 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26267 ⟨333769, by decide⟩ :=
  accepted_of_selected 12 26267 ⟨333769, by decide⟩ ⟨12, 2, 0, 333769, 26267, 2097, 65536⟩
    (by decide) selected_cut_12656

theorem unmarked_context_11_6566_333770 : frontier 10 ⟨333770, by decide⟩
    (prefixCache 11 6566) (prefixPartial 11 6566) = false := by
  decide +kernel

theorem node_context_11_6566_333770 : EJMOriginalGlobalDAGData.nodes 10 ⟨333770, by decide⟩ =
    .split (coordinate 11) (![⟨333721, by decide⟩,⟨333746, by decide⟩,⟨290673, by decide⟩,⟨333769, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6566_333770 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6566 ⟨333770, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6566
    ⟨333770, by decide⟩ (by decide) (![⟨333721, by decide⟩,⟨333746, by decide⟩,⟨290673, by decide⟩,⟨333769, by decide⟩]) unmarked_context_11_6566_333770 node_context_11_6566_333770
  intro a
  fin_cases a
  · exact context_12_26264_333721
  · exact context_12_26265_333746
  · exact context_12_26266_290673
  · exact context_12_26267_333769

theorem selected_cut_12657 : selected 9 ⟨333790, by decide⟩
    (prefixPartial 12 26268) = some ⟨12, 2, 0, 333790, 26268, 2013, 65536⟩ := by
  decide +kernel

theorem context_12_26268_333790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26268 ⟨333790, by decide⟩ :=
  accepted_of_selected 12 26268 ⟨333790, by decide⟩ ⟨12, 2, 0, 333790, 26268, 2013, 65536⟩
    (by decide) selected_cut_12657

theorem selected_cut_12658 : selected 9 ⟨333820, by decide⟩
    (prefixPartial 12 26269) = some ⟨12, 2, 0, 333820, 26269, 2069, 65536⟩ := by
  decide +kernel

theorem context_12_26269_333820 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26269 ⟨333820, by decide⟩ :=
  accepted_of_selected 12 26269 ⟨333820, by decide⟩ ⟨12, 2, 0, 333820, 26269, 2069, 65536⟩
    (by decide) selected_cut_12658

theorem selected_cut_12659 : selected 9 ⟨333846, by decide⟩
    (prefixPartial 12 26270) = some ⟨12, 2, 0, 333846, 26270, 1697, 65536⟩ := by
  decide +kernel

theorem context_12_26270_333846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26270 ⟨333846, by decide⟩ :=
  accepted_of_selected 12 26270 ⟨333846, by decide⟩ ⟨12, 2, 0, 333846, 26270, 1697, 65536⟩
    (by decide) selected_cut_12659

theorem selected_cut_12660 : selected 9 ⟨333868, by decide⟩
    (prefixPartial 12 26271) = some ⟨12, 2, 0, 333868, 26271, 2185, 65536⟩ := by
  decide +kernel

theorem context_12_26271_333868 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26271 ⟨333868, by decide⟩ :=
  accepted_of_selected 12 26271 ⟨333868, by decide⟩ ⟨12, 2, 0, 333868, 26271, 2185, 65536⟩
    (by decide) selected_cut_12660

theorem unmarked_context_11_6567_333869 : frontier 10 ⟨333869, by decide⟩
    (prefixCache 11 6567) (prefixPartial 11 6567) = false := by
  decide +kernel

theorem node_context_11_6567_333869 : EJMOriginalGlobalDAGData.nodes 10 ⟨333869, by decide⟩ =
    .split (coordinate 11) (![⟨333790, by decide⟩,⟨333820, by decide⟩,⟨333846, by decide⟩,⟨333868, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6567_333869 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6567 ⟨333869, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6567
    ⟨333869, by decide⟩ (by decide) (![⟨333790, by decide⟩,⟨333820, by decide⟩,⟨333846, by decide⟩,⟨333868, by decide⟩]) unmarked_context_11_6567_333869 node_context_11_6567_333869
  intro a
  fin_cases a
  · exact context_12_26268_333790
  · exact context_12_26269_333820
  · exact context_12_26270_333846
  · exact context_12_26271_333868

theorem unmarked_context_10_1641_333870 : frontier 11 ⟨333870, by decide⟩
    (prefixCache 10 1641) (prefixPartial 10 1641) = false := by
  decide +kernel

theorem node_context_10_1641_333870 : EJMOriginalGlobalDAGData.nodes 11 ⟨333870, by decide⟩ =
    .split (coordinate 10) (![⟨333606, by decide⟩,⟨333700, by decide⟩,⟨333770, by decide⟩,⟨333869, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1641_333870 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1641 ⟨333870, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1641
    ⟨333870, by decide⟩ (by decide) (![⟨333606, by decide⟩,⟨333700, by decide⟩,⟨333770, by decide⟩,⟨333869, by decide⟩]) unmarked_context_10_1641_333870 node_context_10_1641_333870
  intro a
  fin_cases a
  · exact context_11_6564_333606
  · exact context_11_6565_333700
  · exact context_11_6566_333770
  · exact context_11_6567_333869

theorem selected_cut_12661 : selected 9 ⟨333888, by decide⟩
    (prefixPartial 12 26272) = some ⟨12, 2, 0, 333888, 26272, 1449, 65536⟩ := by
  decide +kernel

theorem context_12_26272_333888 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26272 ⟨333888, by decide⟩ :=
  accepted_of_selected 12 26272 ⟨333888, by decide⟩ ⟨12, 2, 0, 333888, 26272, 1449, 65536⟩
    (by decide) selected_cut_12661

theorem selected_cut_12662 : selected 9 ⟨333911, by decide⟩
    (prefixPartial 12 26273) = some ⟨12, 2, 0, 333911, 26273, 1781, 65536⟩ := by
  decide +kernel

theorem context_12_26273_333911 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26273 ⟨333911, by decide⟩ :=
  accepted_of_selected 12 26273 ⟨333911, by decide⟩ ⟨12, 2, 0, 333911, 26273, 1781, 65536⟩
    (by decide) selected_cut_12662

theorem selected_cut_12663 : selected 9 ⟨333925, by decide⟩
    (prefixPartial 12 26274) = some ⟨12, 2, 0, 333925, 26274, 1345, 65536⟩ := by
  decide +kernel

theorem context_12_26274_333925 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26274 ⟨333925, by decide⟩ :=
  accepted_of_selected 12 26274 ⟨333925, by decide⟩ ⟨12, 2, 0, 333925, 26274, 1345, 65536⟩
    (by decide) selected_cut_12663

theorem selected_cut_12664 : selected 9 ⟨333945, by decide⟩
    (prefixPartial 12 26275) = some ⟨12, 2, 0, 333945, 26275, 1761, 65536⟩ := by
  decide +kernel

theorem context_12_26275_333945 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26275 ⟨333945, by decide⟩ :=
  accepted_of_selected 12 26275 ⟨333945, by decide⟩ ⟨12, 2, 0, 333945, 26275, 1761, 65536⟩
    (by decide) selected_cut_12664

theorem unmarked_context_11_6568_333946 : frontier 10 ⟨333946, by decide⟩
    (prefixCache 11 6568) (prefixPartial 11 6568) = false := by
  decide +kernel

theorem node_context_11_6568_333946 : EJMOriginalGlobalDAGData.nodes 10 ⟨333946, by decide⟩ =
    .split (coordinate 11) (![⟨333888, by decide⟩,⟨333911, by decide⟩,⟨333925, by decide⟩,⟨333945, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6568_333946 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6568 ⟨333946, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6568
    ⟨333946, by decide⟩ (by decide) (![⟨333888, by decide⟩,⟨333911, by decide⟩,⟨333925, by decide⟩,⟨333945, by decide⟩]) unmarked_context_11_6568_333946 node_context_11_6568_333946
  intro a
  fin_cases a
  · exact context_12_26272_333888
  · exact context_12_26273_333911
  · exact context_12_26274_333925
  · exact context_12_26275_333945

theorem selected_cut_12665 : selected 9 ⟨333961, by decide⟩
    (prefixPartial 12 26276) = some ⟨12, 2, 0, 333961, 26276, 1389, 65536⟩ := by
  decide +kernel

theorem context_12_26276_333961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26276 ⟨333961, by decide⟩ :=
  accepted_of_selected 12 26276 ⟨333961, by decide⟩ ⟨12, 2, 0, 333961, 26276, 1389, 65536⟩
    (by decide) selected_cut_12665

theorem selected_cut_12666 : selected 9 ⟨333979, by decide⟩
    (prefixPartial 12 26277) = some ⟨12, 2, 0, 333979, 26277, 1629, 65536⟩ := by
  decide +kernel

theorem context_12_26277_333979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26277 ⟨333979, by decide⟩ :=
  accepted_of_selected 12 26277 ⟨333979, by decide⟩ ⟨12, 2, 0, 333979, 26277, 1629, 65536⟩
    (by decide) selected_cut_12666

theorem selected_cut_12667 : selected 9 ⟨333996, by decide⟩
    (prefixPartial 12 26278) = some ⟨12, 2, 0, 333996, 26278, 1317, 65536⟩ := by
  decide +kernel

theorem context_12_26278_333996 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26278 ⟨333996, by decide⟩ :=
  accepted_of_selected 12 26278 ⟨333996, by decide⟩ ⟨12, 2, 0, 333996, 26278, 1317, 65536⟩
    (by decide) selected_cut_12667

theorem selected_cut_12668 : selected 9 ⟨334013, by decide⟩
    (prefixPartial 12 26279) = some ⟨12, 2, 0, 334013, 26279, 1661, 65536⟩ := by
  decide +kernel

theorem context_12_26279_334013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26279 ⟨334013, by decide⟩ :=
  accepted_of_selected 12 26279 ⟨334013, by decide⟩ ⟨12, 2, 0, 334013, 26279, 1661, 65536⟩
    (by decide) selected_cut_12668

theorem unmarked_context_11_6569_334014 : frontier 10 ⟨334014, by decide⟩
    (prefixCache 11 6569) (prefixPartial 11 6569) = false := by
  decide +kernel

theorem node_context_11_6569_334014 : EJMOriginalGlobalDAGData.nodes 10 ⟨334014, by decide⟩ =
    .split (coordinate 11) (![⟨333961, by decide⟩,⟨333979, by decide⟩,⟨333996, by decide⟩,⟨334013, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6569_334014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6569 ⟨334014, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6569
    ⟨334014, by decide⟩ (by decide) (![⟨333961, by decide⟩,⟨333979, by decide⟩,⟨333996, by decide⟩,⟨334013, by decide⟩]) unmarked_context_11_6569_334014 node_context_11_6569_334014
  intro a
  fin_cases a
  · exact context_12_26276_333961
  · exact context_12_26277_333979
  · exact context_12_26278_333996
  · exact context_12_26279_334013

theorem selected_cut_12669 : selected 9 ⟨334031, by decide⟩
    (prefixPartial 12 26280) = some ⟨12, 2, 0, 334031, 26280, 1389, 65536⟩ := by
  decide +kernel

theorem context_12_26280_334031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26280 ⟨334031, by decide⟩ :=
  accepted_of_selected 12 26280 ⟨334031, by decide⟩ ⟨12, 2, 0, 334031, 26280, 1389, 65536⟩
    (by decide) selected_cut_12669

theorem selected_cut_12670 : selected 9 ⟨334048, by decide⟩
    (prefixPartial 12 26281) = some ⟨12, 2, 0, 334048, 26281, 1641, 65536⟩ := by
  decide +kernel

theorem context_12_26281_334048 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26281 ⟨334048, by decide⟩ :=
  accepted_of_selected 12 26281 ⟨334048, by decide⟩ ⟨12, 2, 0, 334048, 26281, 1641, 65536⟩
    (by decide) selected_cut_12670

theorem selected_cut_12671 : selected 9 ⟨212113, by decide⟩
    (prefixPartial 12 26282) = some ⟨12, 1, 0, 212113, 26282, 1, 65536⟩ := by
  decide +kernel

theorem context_12_26282_212113 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26282 ⟨212113, by decide⟩ :=
  accepted_of_selected 12 26282 ⟨212113, by decide⟩ ⟨12, 1, 0, 212113, 26282, 1, 65536⟩
    (by decide) selected_cut_12671

theorem selected_cut_12672 : selected 9 ⟨334071, by decide⟩
    (prefixPartial 12 26283) = some ⟨12, 2, 0, 334071, 26283, 1501, 65536⟩ := by
  decide +kernel

theorem context_12_26283_334071 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26283 ⟨334071, by decide⟩ :=
  accepted_of_selected 12 26283 ⟨334071, by decide⟩ ⟨12, 2, 0, 334071, 26283, 1501, 65536⟩
    (by decide) selected_cut_12672

theorem unmarked_context_11_6570_334072 : frontier 10 ⟨334072, by decide⟩
    (prefixCache 11 6570) (prefixPartial 11 6570) = false := by
  decide +kernel

theorem node_context_11_6570_334072 : EJMOriginalGlobalDAGData.nodes 10 ⟨334072, by decide⟩ =
    .split (coordinate 11) (![⟨334031, by decide⟩,⟨334048, by decide⟩,⟨212113, by decide⟩,⟨334071, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6570_334072 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6570 ⟨334072, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6570
    ⟨334072, by decide⟩ (by decide) (![⟨334031, by decide⟩,⟨334048, by decide⟩,⟨212113, by decide⟩,⟨334071, by decide⟩]) unmarked_context_11_6570_334072 node_context_11_6570_334072
  intro a
  fin_cases a
  · exact context_12_26280_334031
  · exact context_12_26281_334048
  · exact context_12_26282_212113
  · exact context_12_26283_334071

theorem selected_cut_12673 : selected 9 ⟨334091, by decide⟩
    (prefixPartial 12 26284) = some ⟨12, 2, 0, 334091, 26284, 1577, 65536⟩ := by
  decide +kernel

theorem context_12_26284_334091 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26284 ⟨334091, by decide⟩ :=
  accepted_of_selected 12 26284 ⟨334091, by decide⟩ ⟨12, 2, 0, 334091, 26284, 1577, 65536⟩
    (by decide) selected_cut_12673

theorem selected_cut_12674 : selected 9 ⟨334109, by decide⟩
    (prefixPartial 12 26285) = some ⟨12, 2, 0, 334109, 26285, 1673, 65536⟩ := by
  decide +kernel

theorem context_12_26285_334109 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26285 ⟨334109, by decide⟩ :=
  accepted_of_selected 12 26285 ⟨334109, by decide⟩ ⟨12, 2, 0, 334109, 26285, 1673, 65536⟩
    (by decide) selected_cut_12674

theorem selected_cut_12675 : selected 9 ⟨334121, by decide⟩
    (prefixPartial 12 26286) = some ⟨12, 2, 0, 334121, 26286, 1281, 65536⟩ := by
  decide +kernel

theorem context_12_26286_334121 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26286 ⟨334121, by decide⟩ :=
  accepted_of_selected 12 26286 ⟨334121, by decide⟩ ⟨12, 2, 0, 334121, 26286, 1281, 65536⟩
    (by decide) selected_cut_12675

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
