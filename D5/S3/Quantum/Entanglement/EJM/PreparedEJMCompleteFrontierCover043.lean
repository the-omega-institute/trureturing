/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover042
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_04130 : selected 8 ⟨131056, by decide⟩
    (prefixPartial 13 71825) = some ⟨13, 2, 0, 131056, 71825, 1765, 16384⟩ := by
  decide +kernel

theorem context_13_71825_131056 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71825 ⟨131056, by decide⟩ :=
  accepted_of_selected 13 71825 ⟨131056, by decide⟩ ⟨13, 2, 0, 131056, 71825, 1765, 16384⟩
    (by decide) selected_cut_04130

theorem selected_cut_04131 : selected 8 ⟨131077, by decide⟩
    (prefixPartial 13 71826) = some ⟨13, 2, 0, 131077, 71826, 1373, 16384⟩ := by
  decide +kernel

theorem context_13_71826_131077 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71826 ⟨131077, by decide⟩ :=
  accepted_of_selected 13 71826 ⟨131077, by decide⟩ ⟨13, 2, 0, 131077, 71826, 1373, 16384⟩
    (by decide) selected_cut_04131

theorem selected_cut_04132 : selected 8 ⟨131090, by decide⟩
    (prefixPartial 13 71827) = some ⟨13, 2, 0, 131090, 71827, 841, 16384⟩ := by
  decide +kernel

theorem context_13_71827_131090 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71827 ⟨131090, by decide⟩ :=
  accepted_of_selected 13 71827 ⟨131090, by decide⟩ ⟨13, 2, 0, 131090, 71827, 841, 16384⟩
    (by decide) selected_cut_04132

theorem unmarked_context_12_17956_131091 : frontier 9 ⟨131091, by decide⟩
    (prefixCache 12 17956) (prefixPartial 12 17956) = false := by
  decide +kernel

theorem node_context_12_17956_131091 : EJMOriginalGlobalDAGData.nodes 9 ⟨131091, by decide⟩ =
    .split (coordinate 12) (![⟨131035, by decide⟩,⟨131056, by decide⟩,⟨131077, by decide⟩,⟨131090, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17956_131091 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17956 ⟨131091, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17956
    ⟨131091, by decide⟩ (by decide) (![⟨131035, by decide⟩,⟨131056, by decide⟩,⟨131077, by decide⟩,⟨131090, by decide⟩]) unmarked_context_12_17956_131091 node_context_12_17956_131091
  intro a
  fin_cases a
  · exact context_13_71824_131035
  · exact context_13_71825_131056
  · exact context_13_71826_131077
  · exact context_13_71827_131090

theorem selected_cut_04133 : selected 8 ⟨131109, by decide⟩
    (prefixPartial 13 71828) = some ⟨13, 2, 0, 131109, 71828, 1117, 16384⟩ := by
  decide +kernel

theorem context_13_71828_131109 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71828 ⟨131109, by decide⟩ :=
  accepted_of_selected 13 71828 ⟨131109, by decide⟩ ⟨13, 2, 0, 131109, 71828, 1117, 16384⟩
    (by decide) selected_cut_04133

theorem selected_cut_04134 : selected 8 ⟨131132, by decide⟩
    (prefixPartial 13 71829) = some ⟨13, 2, 0, 131132, 71829, 1869, 16384⟩ := by
  decide +kernel

theorem context_13_71829_131132 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71829 ⟨131132, by decide⟩ :=
  accepted_of_selected 13 71829 ⟨131132, by decide⟩ ⟨13, 2, 0, 131132, 71829, 1869, 16384⟩
    (by decide) selected_cut_04134

theorem selected_cut_04135 : selected 8 ⟨131152, by decide⟩
    (prefixPartial 13 71830) = some ⟨13, 2, 0, 131152, 71830, 1121, 16384⟩ := by
  decide +kernel

theorem context_13_71830_131152 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71830 ⟨131152, by decide⟩ :=
  accepted_of_selected 13 71830 ⟨131152, by decide⟩ ⟨13, 2, 0, 131152, 71830, 1121, 16384⟩
    (by decide) selected_cut_04135

theorem selected_cut_04136 : selected 8 ⟨131160, by decide⟩
    (prefixPartial 13 71831) = some ⟨13, 2, 0, 131160, 71831, 753, 16384⟩ := by
  decide +kernel

theorem context_13_71831_131160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71831 ⟨131160, by decide⟩ :=
  accepted_of_selected 13 71831 ⟨131160, by decide⟩ ⟨13, 2, 0, 131160, 71831, 753, 16384⟩
    (by decide) selected_cut_04136

theorem unmarked_context_12_17957_131161 : frontier 9 ⟨131161, by decide⟩
    (prefixCache 12 17957) (prefixPartial 12 17957) = false := by
  decide +kernel

theorem node_context_12_17957_131161 : EJMOriginalGlobalDAGData.nodes 9 ⟨131161, by decide⟩ =
    .split (coordinate 12) (![⟨131109, by decide⟩,⟨131132, by decide⟩,⟨131152, by decide⟩,⟨131160, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17957_131161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17957 ⟨131161, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17957
    ⟨131161, by decide⟩ (by decide) (![⟨131109, by decide⟩,⟨131132, by decide⟩,⟨131152, by decide⟩,⟨131160, by decide⟩]) unmarked_context_12_17957_131161 node_context_12_17957_131161
  intro a
  fin_cases a
  · exact context_13_71828_131109
  · exact context_13_71829_131132
  · exact context_13_71830_131152
  · exact context_13_71831_131160

theorem selected_cut_04137 : selected 8 ⟨131178, by decide⟩
    (prefixPartial 13 71832) = some ⟨13, 2, 0, 131178, 71832, 997, 16384⟩ := by
  decide +kernel

theorem context_13_71832_131178 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71832 ⟨131178, by decide⟩ :=
  accepted_of_selected 13 71832 ⟨131178, by decide⟩ ⟨13, 2, 0, 131178, 71832, 997, 16384⟩
    (by decide) selected_cut_04137

theorem selected_cut_04138 : selected 8 ⟨131203, by decide⟩
    (prefixPartial 13 71833) = some ⟨13, 2, 0, 131203, 71833, 1793, 16384⟩ := by
  decide +kernel

theorem context_13_71833_131203 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71833 ⟨131203, by decide⟩ :=
  accepted_of_selected 13 71833 ⟨131203, by decide⟩ ⟨13, 2, 0, 131203, 71833, 1793, 16384⟩
    (by decide) selected_cut_04138

theorem selected_cut_04139 : selected 8 ⟨131219, by decide⟩
    (prefixPartial 13 71834) = some ⟨13, 2, 0, 131219, 71834, 917, 16384⟩ := by
  decide +kernel

theorem context_13_71834_131219 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71834 ⟨131219, by decide⟩ :=
  accepted_of_selected 13 71834 ⟨131219, by decide⟩ ⟨13, 2, 0, 131219, 71834, 917, 16384⟩
    (by decide) selected_cut_04139

theorem selected_cut_04140 : selected 8 ⟨131230, by decide⟩
    (prefixPartial 13 71835) = some ⟨13, 2, 0, 131230, 71835, 829, 16384⟩ := by
  decide +kernel

theorem context_13_71835_131230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71835 ⟨131230, by decide⟩ :=
  accepted_of_selected 13 71835 ⟨131230, by decide⟩ ⟨13, 2, 0, 131230, 71835, 829, 16384⟩
    (by decide) selected_cut_04140

theorem unmarked_context_12_17958_131231 : frontier 9 ⟨131231, by decide⟩
    (prefixCache 12 17958) (prefixPartial 12 17958) = false := by
  decide +kernel

theorem node_context_12_17958_131231 : EJMOriginalGlobalDAGData.nodes 9 ⟨131231, by decide⟩ =
    .split (coordinate 12) (![⟨131178, by decide⟩,⟨131203, by decide⟩,⟨131219, by decide⟩,⟨131230, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17958_131231 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17958 ⟨131231, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17958
    ⟨131231, by decide⟩ (by decide) (![⟨131178, by decide⟩,⟨131203, by decide⟩,⟨131219, by decide⟩,⟨131230, by decide⟩]) unmarked_context_12_17958_131231 node_context_12_17958_131231
  intro a
  fin_cases a
  · exact context_13_71832_131178
  · exact context_13_71833_131203
  · exact context_13_71834_131219
  · exact context_13_71835_131230

theorem selected_cut_04141 : selected 8 ⟨131251, by decide⟩
    (prefixPartial 13 71836) = some ⟨13, 2, 0, 131251, 71836, 1121, 16384⟩ := by
  decide +kernel

theorem context_13_71836_131251 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71836 ⟨131251, by decide⟩ :=
  accepted_of_selected 13 71836 ⟨131251, by decide⟩ ⟨13, 2, 0, 131251, 71836, 1121, 16384⟩
    (by decide) selected_cut_04141

theorem selected_cut_04142 : selected 8 ⟨131283, by decide⟩
    (prefixPartial 13 71837) = some ⟨13, 2, 0, 131283, 71837, 2121, 16384⟩ := by
  decide +kernel

theorem context_13_71837_131283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71837 ⟨131283, by decide⟩ :=
  accepted_of_selected 13 71837 ⟨131283, by decide⟩ ⟨13, 2, 0, 131283, 71837, 2121, 16384⟩
    (by decide) selected_cut_04142

theorem selected_cut_04143 : selected 8 ⟨131304, by decide⟩
    (prefixPartial 13 71838) = some ⟨13, 2, 0, 131304, 71838, 1273, 16384⟩ := by
  decide +kernel

theorem context_13_71838_131304 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71838 ⟨131304, by decide⟩ :=
  accepted_of_selected 13 71838 ⟨131304, by decide⟩ ⟨13, 2, 0, 131304, 71838, 1273, 16384⟩
    (by decide) selected_cut_04143

theorem selected_cut_04144 : selected 8 ⟨131312, by decide⟩
    (prefixPartial 13 71839) = some ⟨13, 2, 0, 131312, 71839, 893, 16384⟩ := by
  decide +kernel

theorem context_13_71839_131312 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71839 ⟨131312, by decide⟩ :=
  accepted_of_selected 13 71839 ⟨131312, by decide⟩ ⟨13, 2, 0, 131312, 71839, 893, 16384⟩
    (by decide) selected_cut_04144

theorem unmarked_context_12_17959_131313 : frontier 9 ⟨131313, by decide⟩
    (prefixCache 12 17959) (prefixPartial 12 17959) = false := by
  decide +kernel

theorem node_context_12_17959_131313 : EJMOriginalGlobalDAGData.nodes 9 ⟨131313, by decide⟩ =
    .split (coordinate 12) (![⟨131251, by decide⟩,⟨131283, by decide⟩,⟨131304, by decide⟩,⟨131312, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17959_131313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17959 ⟨131313, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17959
    ⟨131313, by decide⟩ (by decide) (![⟨131251, by decide⟩,⟨131283, by decide⟩,⟨131304, by decide⟩,⟨131312, by decide⟩]) unmarked_context_12_17959_131313 node_context_12_17959_131313
  intro a
  fin_cases a
  · exact context_13_71836_131251
  · exact context_13_71837_131283
  · exact context_13_71838_131304
  · exact context_13_71839_131312

theorem unmarked_context_11_4489_131314 : frontier 10 ⟨131314, by decide⟩
    (prefixCache 11 4489) (prefixPartial 11 4489) = false := by
  decide +kernel

theorem node_context_11_4489_131314 : EJMOriginalGlobalDAGData.nodes 10 ⟨131314, by decide⟩ =
    .split (coordinate 11) (![⟨131091, by decide⟩,⟨131161, by decide⟩,⟨131231, by decide⟩,⟨131313, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4489_131314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4489 ⟨131314, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4489
    ⟨131314, by decide⟩ (by decide) (![⟨131091, by decide⟩,⟨131161, by decide⟩,⟨131231, by decide⟩,⟨131313, by decide⟩]) unmarked_context_11_4489_131314 node_context_11_4489_131314
  intro a
  fin_cases a
  · exact context_12_17956_131091
  · exact context_12_17957_131161
  · exact context_12_17958_131231
  · exact context_12_17959_131313

theorem selected_cut_04145 : selected 9 ⟨131376, by decide⟩
    (prefixPartial 12 17960) = some ⟨12, 2, 0, 131376, 17960, 4017, 65536⟩ := by
  decide +kernel

theorem context_12_17960_131376 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17960 ⟨131376, by decide⟩ :=
  accepted_of_selected 12 17960 ⟨131376, by decide⟩ ⟨12, 2, 0, 131376, 17960, 4017, 65536⟩
    (by decide) selected_cut_04145

theorem selected_cut_04146 : selected 8 ⟨131397, by decide⟩
    (prefixPartial 13 71844) = some ⟨13, 2, 0, 131397, 71844, 1045, 16384⟩ := by
  decide +kernel

theorem context_13_71844_131397 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71844 ⟨131397, by decide⟩ :=
  accepted_of_selected 13 71844 ⟨131397, by decide⟩ ⟨13, 2, 0, 131397, 71844, 1045, 16384⟩
    (by decide) selected_cut_04146

theorem selected_cut_04147 : selected 8 ⟨131423, by decide⟩
    (prefixPartial 13 71845) = some ⟨13, 2, 0, 131423, 71845, 1713, 16384⟩ := by
  decide +kernel

theorem context_13_71845_131423 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71845 ⟨131423, by decide⟩ :=
  accepted_of_selected 13 71845 ⟨131423, by decide⟩ ⟨13, 2, 0, 131423, 71845, 1713, 16384⟩
    (by decide) selected_cut_04147

theorem selected_cut_04148 : selected 8 ⟨131442, by decide⟩
    (prefixPartial 13 71846) = some ⟨13, 2, 0, 131442, 71846, 1101, 16384⟩ := by
  decide +kernel

theorem context_13_71846_131442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71846 ⟨131442, by decide⟩ :=
  accepted_of_selected 13 71846 ⟨131442, by decide⟩ ⟨13, 2, 0, 131442, 71846, 1101, 16384⟩
    (by decide) selected_cut_04148

theorem selected_cut_04149 : selected 8 ⟨131452, by decide⟩
    (prefixPartial 13 71847) = some ⟨13, 2, 0, 131452, 71847, 821, 16384⟩ := by
  decide +kernel

theorem context_13_71847_131452 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71847 ⟨131452, by decide⟩ :=
  accepted_of_selected 13 71847 ⟨131452, by decide⟩ ⟨13, 2, 0, 131452, 71847, 821, 16384⟩
    (by decide) selected_cut_04149

theorem unmarked_context_12_17961_131453 : frontier 9 ⟨131453, by decide⟩
    (prefixCache 12 17961) (prefixPartial 12 17961) = false := by
  decide +kernel

theorem node_context_12_17961_131453 : EJMOriginalGlobalDAGData.nodes 9 ⟨131453, by decide⟩ =
    .split (coordinate 12) (![⟨131397, by decide⟩,⟨131423, by decide⟩,⟨131442, by decide⟩,⟨131452, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17961_131453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17961 ⟨131453, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17961
    ⟨131453, by decide⟩ (by decide) (![⟨131397, by decide⟩,⟨131423, by decide⟩,⟨131442, by decide⟩,⟨131452, by decide⟩]) unmarked_context_12_17961_131453 node_context_12_17961_131453
  intro a
  fin_cases a
  · exact context_13_71844_131397
  · exact context_13_71845_131423
  · exact context_13_71846_131442
  · exact context_13_71847_131452

theorem selected_cut_04150 : selected 8 ⟨131476, by decide⟩
    (prefixPartial 13 71848) = some ⟨13, 2, 0, 131476, 71848, 1209, 16384⟩ := by
  decide +kernel

theorem context_13_71848_131476 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71848 ⟨131476, by decide⟩ :=
  accepted_of_selected 13 71848 ⟨131476, by decide⟩ ⟨13, 2, 0, 131476, 71848, 1209, 16384⟩
    (by decide) selected_cut_04150

theorem selected_cut_04151 : selected 8 ⟨131513, by decide⟩
    (prefixPartial 13 71849) = some ⟨13, 2, 0, 131513, 71849, 2509, 16384⟩ := by
  decide +kernel

theorem context_13_71849_131513 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71849 ⟨131513, by decide⟩ :=
  accepted_of_selected 13 71849 ⟨131513, by decide⟩ ⟨13, 2, 0, 131513, 71849, 2509, 16384⟩
    (by decide) selected_cut_04151

theorem selected_cut_04152 : selected 8 ⟨131532, by decide⟩
    (prefixPartial 13 71850) = some ⟨13, 2, 0, 131532, 71850, 1449, 16384⟩ := by
  decide +kernel

theorem context_13_71850_131532 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71850 ⟨131532, by decide⟩ :=
  accepted_of_selected 13 71850 ⟨131532, by decide⟩ ⟨13, 2, 0, 131532, 71850, 1449, 16384⟩
    (by decide) selected_cut_04152

theorem selected_cut_04153 : selected 8 ⟨131540, by decide⟩
    (prefixPartial 13 71851) = some ⟨13, 2, 0, 131540, 71851, 1073, 16384⟩ := by
  decide +kernel

theorem context_13_71851_131540 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71851 ⟨131540, by decide⟩ :=
  accepted_of_selected 13 71851 ⟨131540, by decide⟩ ⟨13, 2, 0, 131540, 71851, 1073, 16384⟩
    (by decide) selected_cut_04153

theorem unmarked_context_12_17962_131541 : frontier 9 ⟨131541, by decide⟩
    (prefixCache 12 17962) (prefixPartial 12 17962) = false := by
  decide +kernel

theorem node_context_12_17962_131541 : EJMOriginalGlobalDAGData.nodes 9 ⟨131541, by decide⟩ =
    .split (coordinate 12) (![⟨131476, by decide⟩,⟨131513, by decide⟩,⟨131532, by decide⟩,⟨131540, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17962_131541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17962 ⟨131541, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17962
    ⟨131541, by decide⟩ (by decide) (![⟨131476, by decide⟩,⟨131513, by decide⟩,⟨131532, by decide⟩,⟨131540, by decide⟩]) unmarked_context_12_17962_131541 node_context_12_17962_131541
  intro a
  fin_cases a
  · exact context_13_71848_131476
  · exact context_13_71849_131513
  · exact context_13_71850_131532
  · exact context_13_71851_131540

theorem selected_cut_04154 : selected 8 ⟨131557, by decide⟩
    (prefixPartial 13 71852) = some ⟨13, 2, 0, 131557, 71852, 865, 16384⟩ := by
  decide +kernel

theorem context_13_71852_131557 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71852 ⟨131557, by decide⟩ :=
  accepted_of_selected 13 71852 ⟨131557, by decide⟩ ⟨13, 2, 0, 131557, 71852, 865, 16384⟩
    (by decide) selected_cut_04154

theorem selected_cut_04155 : selected 8 ⟨131585, by decide⟩
    (prefixPartial 13 71853) = some ⟨13, 2, 0, 131585, 71853, 1749, 16384⟩ := by
  decide +kernel

theorem context_13_71853_131585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71853 ⟨131585, by decide⟩ :=
  accepted_of_selected 13 71853 ⟨131585, by decide⟩ ⟨13, 2, 0, 131585, 71853, 1749, 16384⟩
    (by decide) selected_cut_04155

theorem selected_cut_04156 : selected 8 ⟨131597, by decide⟩
    (prefixPartial 13 71854) = some ⟨13, 2, 0, 131597, 71854, 1049, 16384⟩ := by
  decide +kernel

theorem context_13_71854_131597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71854 ⟨131597, by decide⟩ :=
  accepted_of_selected 13 71854 ⟨131597, by decide⟩ ⟨13, 2, 0, 131597, 71854, 1049, 16384⟩
    (by decide) selected_cut_04156

theorem selected_cut_04157 : selected 8 ⟨131605, by decide⟩
    (prefixPartial 13 71855) = some ⟨13, 2, 0, 131605, 71855, 821, 16384⟩ := by
  decide +kernel

theorem context_13_71855_131605 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71855 ⟨131605, by decide⟩ :=
  accepted_of_selected 13 71855 ⟨131605, by decide⟩ ⟨13, 2, 0, 131605, 71855, 821, 16384⟩
    (by decide) selected_cut_04157

theorem unmarked_context_12_17963_131606 : frontier 9 ⟨131606, by decide⟩
    (prefixCache 12 17963) (prefixPartial 12 17963) = false := by
  decide +kernel

theorem node_context_12_17963_131606 : EJMOriginalGlobalDAGData.nodes 9 ⟨131606, by decide⟩ =
    .split (coordinate 12) (![⟨131557, by decide⟩,⟨131585, by decide⟩,⟨131597, by decide⟩,⟨131605, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17963_131606 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17963 ⟨131606, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17963
    ⟨131606, by decide⟩ (by decide) (![⟨131557, by decide⟩,⟨131585, by decide⟩,⟨131597, by decide⟩,⟨131605, by decide⟩]) unmarked_context_12_17963_131606 node_context_12_17963_131606
  intro a
  fin_cases a
  · exact context_13_71852_131557
  · exact context_13_71853_131585
  · exact context_13_71854_131597
  · exact context_13_71855_131605

theorem unmarked_context_11_4490_131607 : frontier 10 ⟨131607, by decide⟩
    (prefixCache 11 4490) (prefixPartial 11 4490) = false := by
  decide +kernel

theorem node_context_11_4490_131607 : EJMOriginalGlobalDAGData.nodes 10 ⟨131607, by decide⟩ =
    .split (coordinate 11) (![⟨131376, by decide⟩,⟨131453, by decide⟩,⟨131541, by decide⟩,⟨131606, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4490_131607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4490 ⟨131607, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4490
    ⟨131607, by decide⟩ (by decide) (![⟨131376, by decide⟩,⟨131453, by decide⟩,⟨131541, by decide⟩,⟨131606, by decide⟩]) unmarked_context_11_4490_131607 node_context_11_4490_131607
  intro a
  fin_cases a
  · exact context_12_17960_131376
  · exact context_12_17961_131453
  · exact context_12_17962_131541
  · exact context_12_17963_131606

theorem selected_cut_04158 : selected 8 ⟨131618, by decide⟩
    (prefixPartial 13 71856) = some ⟨13, 2, 0, 131618, 71856, 625, 16384⟩ := by
  decide +kernel

theorem context_13_71856_131618 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71856 ⟨131618, by decide⟩ :=
  accepted_of_selected 13 71856 ⟨131618, by decide⟩ ⟨13, 2, 0, 131618, 71856, 625, 16384⟩
    (by decide) selected_cut_04158

theorem selected_cut_04159 : selected 8 ⟨131639, by decide⟩
    (prefixPartial 13 71857) = some ⟨13, 2, 0, 131639, 71857, 1505, 16384⟩ := by
  decide +kernel

theorem context_13_71857_131639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71857 ⟨131639, by decide⟩ :=
  accepted_of_selected 13 71857 ⟨131639, by decide⟩ ⟨13, 2, 0, 131639, 71857, 1505, 16384⟩
    (by decide) selected_cut_04159

theorem selected_cut_04160 : selected 8 ⟨131657, by decide⟩
    (prefixPartial 13 71858) = some ⟨13, 2, 0, 131657, 71858, 1297, 16384⟩ := by
  decide +kernel

theorem context_13_71858_131657 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71858 ⟨131657, by decide⟩ :=
  accepted_of_selected 13 71858 ⟨131657, by decide⟩ ⟨13, 2, 0, 131657, 71858, 1297, 16384⟩
    (by decide) selected_cut_04160

theorem selected_cut_04161 : selected 8 ⟨131667, by decide⟩
    (prefixPartial 13 71859) = some ⟨13, 2, 0, 131667, 71859, 885, 16384⟩ := by
  decide +kernel

theorem context_13_71859_131667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71859 ⟨131667, by decide⟩ :=
  accepted_of_selected 13 71859 ⟨131667, by decide⟩ ⟨13, 2, 0, 131667, 71859, 885, 16384⟩
    (by decide) selected_cut_04161

theorem unmarked_context_12_17964_131668 : frontier 9 ⟨131668, by decide⟩
    (prefixCache 12 17964) (prefixPartial 12 17964) = false := by
  decide +kernel

theorem node_context_12_17964_131668 : EJMOriginalGlobalDAGData.nodes 9 ⟨131668, by decide⟩ =
    .split (coordinate 12) (![⟨131618, by decide⟩,⟨131639, by decide⟩,⟨131657, by decide⟩,⟨131667, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17964_131668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17964 ⟨131668, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17964
    ⟨131668, by decide⟩ (by decide) (![⟨131618, by decide⟩,⟨131639, by decide⟩,⟨131657, by decide⟩,⟨131667, by decide⟩]) unmarked_context_12_17964_131668 node_context_12_17964_131668
  intro a
  fin_cases a
  · exact context_13_71856_131618
  · exact context_13_71857_131639
  · exact context_13_71858_131657
  · exact context_13_71859_131667

theorem selected_cut_04162 : selected 8 ⟨131686, by decide⟩
    (prefixPartial 13 71860) = some ⟨13, 2, 0, 131686, 71860, 893, 16384⟩ := by
  decide +kernel

theorem context_13_71860_131686 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71860 ⟨131686, by decide⟩ :=
  accepted_of_selected 13 71860 ⟨131686, by decide⟩ ⟨13, 2, 0, 131686, 71860, 893, 16384⟩
    (by decide) selected_cut_04162

theorem selected_cut_04163 : selected 8 ⟨131714, by decide⟩
    (prefixPartial 13 71861) = some ⟨13, 2, 0, 131714, 71861, 1897, 16384⟩ := by
  decide +kernel

theorem context_13_71861_131714 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71861 ⟨131714, by decide⟩ :=
  accepted_of_selected 13 71861 ⟨131714, by decide⟩ ⟨13, 2, 0, 131714, 71861, 1897, 16384⟩
    (by decide) selected_cut_04163

theorem selected_cut_04164 : selected 8 ⟨131732, by decide⟩
    (prefixPartial 13 71862) = some ⟨13, 2, 0, 131732, 71862, 1225, 16384⟩ := by
  decide +kernel

theorem context_13_71862_131732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71862 ⟨131732, by decide⟩ :=
  accepted_of_selected 13 71862 ⟨131732, by decide⟩ ⟨13, 2, 0, 131732, 71862, 1225, 16384⟩
    (by decide) selected_cut_04164

theorem selected_cut_04165 : selected 8 ⟨131743, by decide⟩
    (prefixPartial 13 71863) = some ⟨13, 2, 0, 131743, 71863, 809, 16384⟩ := by
  decide +kernel

theorem context_13_71863_131743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71863 ⟨131743, by decide⟩ :=
  accepted_of_selected 13 71863 ⟨131743, by decide⟩ ⟨13, 2, 0, 131743, 71863, 809, 16384⟩
    (by decide) selected_cut_04165

theorem unmarked_context_12_17965_131744 : frontier 9 ⟨131744, by decide⟩
    (prefixCache 12 17965) (prefixPartial 12 17965) = false := by
  decide +kernel

theorem node_context_12_17965_131744 : EJMOriginalGlobalDAGData.nodes 9 ⟨131744, by decide⟩ =
    .split (coordinate 12) (![⟨131686, by decide⟩,⟨131714, by decide⟩,⟨131732, by decide⟩,⟨131743, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17965_131744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17965 ⟨131744, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17965
    ⟨131744, by decide⟩ (by decide) (![⟨131686, by decide⟩,⟨131714, by decide⟩,⟨131732, by decide⟩,⟨131743, by decide⟩]) unmarked_context_12_17965_131744 node_context_12_17965_131744
  intro a
  fin_cases a
  · exact context_13_71860_131686
  · exact context_13_71861_131714
  · exact context_13_71862_131732
  · exact context_13_71863_131743

theorem selected_cut_04166 : selected 9 ⟨131805, by decide⟩
    (prefixPartial 12 17966) = some ⟨12, 2, 0, 131805, 17966, 4085, 65536⟩ := by
  decide +kernel

theorem context_12_17966_131805 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17966 ⟨131805, by decide⟩ :=
  accepted_of_selected 12 17966 ⟨131805, by decide⟩ ⟨12, 2, 0, 131805, 17966, 4085, 65536⟩
    (by decide) selected_cut_04166

theorem selected_cut_04167 : selected 8 ⟨131817, by decide⟩
    (prefixPartial 13 71868) = some ⟨13, 2, 0, 131817, 71868, 677, 16384⟩ := by
  decide +kernel

theorem context_13_71868_131817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71868 ⟨131817, by decide⟩ :=
  accepted_of_selected 13 71868 ⟨131817, by decide⟩ ⟨13, 2, 0, 131817, 71868, 677, 16384⟩
    (by decide) selected_cut_04167

theorem selected_cut_04168 : selected 8 ⟨131851, by decide⟩
    (prefixPartial 13 71869) = some ⟨13, 2, 0, 131851, 71869, 1709, 16384⟩ := by
  decide +kernel

theorem context_13_71869_131851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71869 ⟨131851, by decide⟩ :=
  accepted_of_selected 13 71869 ⟨131851, by decide⟩ ⟨13, 2, 0, 131851, 71869, 1709, 16384⟩
    (by decide) selected_cut_04168

theorem selected_cut_04169 : selected 8 ⟨131865, by decide⟩
    (prefixPartial 13 71870) = some ⟨13, 2, 0, 131865, 71870, 973, 16384⟩ := by
  decide +kernel

theorem context_13_71870_131865 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71870 ⟨131865, by decide⟩ :=
  accepted_of_selected 13 71870 ⟨131865, by decide⟩ ⟨13, 2, 0, 131865, 71870, 973, 16384⟩
    (by decide) selected_cut_04169

theorem selected_cut_04170 : selected 8 ⟨131875, by decide⟩
    (prefixPartial 13 71871) = some ⟨13, 2, 0, 131875, 71871, 761, 16384⟩ := by
  decide +kernel

theorem context_13_71871_131875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71871 ⟨131875, by decide⟩ :=
  accepted_of_selected 13 71871 ⟨131875, by decide⟩ ⟨13, 2, 0, 131875, 71871, 761, 16384⟩
    (by decide) selected_cut_04170

theorem unmarked_context_12_17967_131876 : frontier 9 ⟨131876, by decide⟩
    (prefixCache 12 17967) (prefixPartial 12 17967) = false := by
  decide +kernel

theorem node_context_12_17967_131876 : EJMOriginalGlobalDAGData.nodes 9 ⟨131876, by decide⟩ =
    .split (coordinate 12) (![⟨131817, by decide⟩,⟨131851, by decide⟩,⟨131865, by decide⟩,⟨131875, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17967_131876 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17967 ⟨131876, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17967
    ⟨131876, by decide⟩ (by decide) (![⟨131817, by decide⟩,⟨131851, by decide⟩,⟨131865, by decide⟩,⟨131875, by decide⟩]) unmarked_context_12_17967_131876 node_context_12_17967_131876
  intro a
  fin_cases a
  · exact context_13_71868_131817
  · exact context_13_71869_131851
  · exact context_13_71870_131865
  · exact context_13_71871_131875

theorem unmarked_context_11_4491_131877 : frontier 10 ⟨131877, by decide⟩
    (prefixCache 11 4491) (prefixPartial 11 4491) = false := by
  decide +kernel

theorem node_context_11_4491_131877 : EJMOriginalGlobalDAGData.nodes 10 ⟨131877, by decide⟩ =
    .split (coordinate 11) (![⟨131668, by decide⟩,⟨131744, by decide⟩,⟨131805, by decide⟩,⟨131876, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4491_131877 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4491 ⟨131877, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4491
    ⟨131877, by decide⟩ (by decide) (![⟨131668, by decide⟩,⟨131744, by decide⟩,⟨131805, by decide⟩,⟨131876, by decide⟩]) unmarked_context_11_4491_131877 node_context_11_4491_131877
  intro a
  fin_cases a
  · exact context_12_17964_131668
  · exact context_12_17965_131744
  · exact context_12_17966_131805
  · exact context_12_17967_131876

theorem unmarked_context_10_1122_131878 : frontier 11 ⟨131878, by decide⟩
    (prefixCache 10 1122) (prefixPartial 10 1122) = false := by
  decide +kernel

theorem node_context_10_1122_131878 : EJMOriginalGlobalDAGData.nodes 11 ⟨131878, by decide⟩ =
    .split (coordinate 10) (![⟨131015, by decide⟩,⟨131314, by decide⟩,⟨131607, by decide⟩,⟨131877, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1122_131878 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1122 ⟨131878, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1122
    ⟨131878, by decide⟩ (by decide) (![⟨131015, by decide⟩,⟨131314, by decide⟩,⟨131607, by decide⟩,⟨131877, by decide⟩]) unmarked_context_10_1122_131878 node_context_10_1122_131878
  intro a
  fin_cases a
  · exact context_11_4488_131015
  · exact context_11_4489_131314
  · exact context_11_4490_131607
  · exact context_11_4491_131877

theorem selected_cut_04171 : selected 8 ⟨131898, by decide⟩
    (prefixPartial 13 71872) = some ⟨13, 2, 0, 131898, 71872, 781, 16384⟩ := by
  decide +kernel

theorem context_13_71872_131898 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71872 ⟨131898, by decide⟩ :=
  accepted_of_selected 13 71872 ⟨131898, by decide⟩ ⟨13, 2, 0, 131898, 71872, 781, 16384⟩
    (by decide) selected_cut_04171

theorem selected_cut_04172 : selected 8 ⟨131960, by decide⟩
    (prefixPartial 13 71873) = some ⟨13, 2, 0, 131960, 71873, 1885, 16384⟩ := by
  decide +kernel

theorem context_13_71873_131960 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71873 ⟨131960, by decide⟩ :=
  accepted_of_selected 13 71873 ⟨131960, by decide⟩ ⟨13, 2, 0, 131960, 71873, 1885, 16384⟩
    (by decide) selected_cut_04172

theorem selected_cut_04173 : selected 8 ⟨131978, by decide⟩
    (prefixPartial 13 71874) = some ⟨13, 2, 0, 131978, 71874, 1197, 16384⟩ := by
  decide +kernel

theorem context_13_71874_131978 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71874 ⟨131978, by decide⟩ :=
  accepted_of_selected 13 71874 ⟨131978, by decide⟩ ⟨13, 2, 0, 131978, 71874, 1197, 16384⟩
    (by decide) selected_cut_04173

theorem selected_cut_04174 : selected 8 ⟨131989, by decide⟩
    (prefixPartial 13 71875) = some ⟨13, 2, 0, 131989, 71875, 773, 16384⟩ := by
  decide +kernel

theorem context_13_71875_131989 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71875 ⟨131989, by decide⟩ :=
  accepted_of_selected 13 71875 ⟨131989, by decide⟩ ⟨13, 2, 0, 131989, 71875, 773, 16384⟩
    (by decide) selected_cut_04174

theorem unmarked_context_12_17968_131990 : frontier 9 ⟨131990, by decide⟩
    (prefixCache 12 17968) (prefixPartial 12 17968) = false := by
  decide +kernel

theorem node_context_12_17968_131990 : EJMOriginalGlobalDAGData.nodes 9 ⟨131990, by decide⟩ =
    .split (coordinate 12) (![⟨131898, by decide⟩,⟨131960, by decide⟩,⟨131978, by decide⟩,⟨131989, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17968_131990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17968 ⟨131990, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17968
    ⟨131990, by decide⟩ (by decide) (![⟨131898, by decide⟩,⟨131960, by decide⟩,⟨131978, by decide⟩,⟨131989, by decide⟩]) unmarked_context_12_17968_131990 node_context_12_17968_131990
  intro a
  fin_cases a
  · exact context_13_71872_131898
  · exact context_13_71873_131960
  · exact context_13_71874_131978
  · exact context_13_71875_131989

theorem selected_cut_04175 : selected 8 ⟨132007, by decide⟩
    (prefixPartial 13 71876) = some ⟨13, 2, 0, 132007, 71876, 793, 16384⟩ := by
  decide +kernel

theorem context_13_71876_132007 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71876 ⟨132007, by decide⟩ :=
  accepted_of_selected 13 71876 ⟨132007, by decide⟩ ⟨13, 2, 0, 132007, 71876, 793, 16384⟩
    (by decide) selected_cut_04175

theorem selected_cut_04176 : selected 8 ⟨132068, by decide⟩
    (prefixPartial 13 71877) = some ⟨13, 2, 0, 132068, 71877, 2229, 16384⟩ := by
  decide +kernel

theorem context_13_71877_132068 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71877 ⟨132068, by decide⟩ :=
  accepted_of_selected 13 71877 ⟨132068, by decide⟩ ⟨13, 2, 0, 132068, 71877, 2229, 16384⟩
    (by decide) selected_cut_04176

theorem selected_cut_04177 : selected 8 ⟨132083, by decide⟩
    (prefixPartial 13 71878) = some ⟨13, 2, 0, 132083, 71878, 921, 16384⟩ := by
  decide +kernel

theorem context_13_71878_132083 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71878 ⟨132083, by decide⟩ :=
  accepted_of_selected 13 71878 ⟨132083, by decide⟩ ⟨13, 2, 0, 132083, 71878, 921, 16384⟩
    (by decide) selected_cut_04177

theorem selected_cut_04178 : selected 8 ⟨132092, by decide⟩
    (prefixPartial 13 71879) = some ⟨13, 2, 0, 132092, 71879, 725, 16384⟩ := by
  decide +kernel

theorem context_13_71879_132092 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71879 ⟨132092, by decide⟩ :=
  accepted_of_selected 13 71879 ⟨132092, by decide⟩ ⟨13, 2, 0, 132092, 71879, 725, 16384⟩
    (by decide) selected_cut_04178

theorem unmarked_context_12_17969_132093 : frontier 9 ⟨132093, by decide⟩
    (prefixCache 12 17969) (prefixPartial 12 17969) = false := by
  decide +kernel

theorem node_context_12_17969_132093 : EJMOriginalGlobalDAGData.nodes 9 ⟨132093, by decide⟩ =
    .split (coordinate 12) (![⟨132007, by decide⟩,⟨132068, by decide⟩,⟨132083, by decide⟩,⟨132092, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17969_132093 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17969 ⟨132093, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17969
    ⟨132093, by decide⟩ (by decide) (![⟨132007, by decide⟩,⟨132068, by decide⟩,⟨132083, by decide⟩,⟨132092, by decide⟩]) unmarked_context_12_17969_132093 node_context_12_17969_132093
  intro a
  fin_cases a
  · exact context_13_71876_132007
  · exact context_13_71877_132068
  · exact context_13_71878_132083
  · exact context_13_71879_132092

theorem selected_cut_04179 : selected 9 ⟨132182, by decide⟩
    (prefixPartial 12 17970) = some ⟨12, 2, 0, 132182, 17970, 4053, 65536⟩ := by
  decide +kernel

theorem context_12_17970_132182 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17970 ⟨132182, by decide⟩ :=
  accepted_of_selected 12 17970 ⟨132182, by decide⟩ ⟨12, 2, 0, 132182, 17970, 4053, 65536⟩
    (by decide) selected_cut_04179

theorem selected_cut_04180 : selected 8 ⟨132200, by decide⟩
    (prefixPartial 13 71884) = some ⟨13, 2, 0, 132200, 71884, 757, 16384⟩ := by
  decide +kernel

theorem context_13_71884_132200 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71884 ⟨132200, by decide⟩ :=
  accepted_of_selected 13 71884 ⟨132200, by decide⟩ ⟨13, 2, 0, 132200, 71884, 757, 16384⟩
    (by decide) selected_cut_04180

theorem selected_cut_04181 : selected 8 ⟨132251, by decide⟩
    (prefixPartial 13 71885) = some ⟨13, 2, 0, 132251, 71885, 2205, 16384⟩ := by
  decide +kernel

theorem context_13_71885_132251 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71885 ⟨132251, by decide⟩ :=
  accepted_of_selected 13 71885 ⟨132251, by decide⟩ ⟨13, 2, 0, 132251, 71885, 2205, 16384⟩
    (by decide) selected_cut_04181

theorem selected_cut_04182 : selected 8 ⟨132263, by decide⟩
    (prefixPartial 13 71886) = some ⟨13, 2, 0, 132263, 71886, 885, 16384⟩ := by
  decide +kernel

theorem context_13_71886_132263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71886 ⟨132263, by decide⟩ :=
  accepted_of_selected 13 71886 ⟨132263, by decide⟩ ⟨13, 2, 0, 132263, 71886, 885, 16384⟩
    (by decide) selected_cut_04182

theorem selected_cut_04183 : selected 8 ⟨132273, by decide⟩
    (prefixPartial 13 71887) = some ⟨13, 2, 0, 132273, 71887, 741, 16384⟩ := by
  decide +kernel

theorem context_13_71887_132273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71887 ⟨132273, by decide⟩ :=
  accepted_of_selected 13 71887 ⟨132273, by decide⟩ ⟨13, 2, 0, 132273, 71887, 741, 16384⟩
    (by decide) selected_cut_04183

theorem unmarked_context_12_17971_132274 : frontier 9 ⟨132274, by decide⟩
    (prefixCache 12 17971) (prefixPartial 12 17971) = false := by
  decide +kernel

theorem node_context_12_17971_132274 : EJMOriginalGlobalDAGData.nodes 9 ⟨132274, by decide⟩ =
    .split (coordinate 12) (![⟨132200, by decide⟩,⟨132251, by decide⟩,⟨132263, by decide⟩,⟨132273, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17971_132274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17971 ⟨132274, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17971
    ⟨132274, by decide⟩ (by decide) (![⟨132200, by decide⟩,⟨132251, by decide⟩,⟨132263, by decide⟩,⟨132273, by decide⟩]) unmarked_context_12_17971_132274 node_context_12_17971_132274
  intro a
  fin_cases a
  · exact context_13_71884_132200
  · exact context_13_71885_132251
  · exact context_13_71886_132263
  · exact context_13_71887_132273

theorem unmarked_context_11_4492_132275 : frontier 10 ⟨132275, by decide⟩
    (prefixCache 11 4492) (prefixPartial 11 4492) = false := by
  decide +kernel

theorem node_context_11_4492_132275 : EJMOriginalGlobalDAGData.nodes 10 ⟨132275, by decide⟩ =
    .split (coordinate 11) (![⟨131990, by decide⟩,⟨132093, by decide⟩,⟨132182, by decide⟩,⟨132274, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4492_132275 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4492 ⟨132275, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4492
    ⟨132275, by decide⟩ (by decide) (![⟨131990, by decide⟩,⟨132093, by decide⟩,⟨132182, by decide⟩,⟨132274, by decide⟩]) unmarked_context_11_4492_132275 node_context_11_4492_132275
  intro a
  fin_cases a
  · exact context_12_17968_131990
  · exact context_12_17969_132093
  · exact context_12_17970_132182
  · exact context_12_17971_132274

theorem selected_cut_04184 : selected 8 ⟨132287, by decide⟩
    (prefixPartial 13 71888) = some ⟨13, 2, 0, 132287, 71888, 521, 16384⟩ := by
  decide +kernel

theorem context_13_71888_132287 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71888 ⟨132287, by decide⟩ :=
  accepted_of_selected 13 71888 ⟨132287, by decide⟩ ⟨13, 2, 0, 132287, 71888, 521, 16384⟩
    (by decide) selected_cut_04184

theorem selected_cut_04185 : selected 8 ⟨132335, by decide⟩
    (prefixPartial 13 71889) = some ⟨13, 2, 0, 132335, 71889, 1889, 16384⟩ := by
  decide +kernel

theorem context_13_71889_132335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71889 ⟨132335, by decide⟩ :=
  accepted_of_selected 13 71889 ⟨132335, by decide⟩ ⟨13, 2, 0, 132335, 71889, 1889, 16384⟩
    (by decide) selected_cut_04185

theorem selected_cut_04186 : selected 8 ⟨132351, by decide⟩
    (prefixPartial 13 71890) = some ⟨13, 2, 0, 132351, 71890, 1333, 16384⟩ := by
  decide +kernel

theorem context_13_71890_132351 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71890 ⟨132351, by decide⟩ :=
  accepted_of_selected 13 71890 ⟨132351, by decide⟩ ⟨13, 2, 0, 132351, 71890, 1333, 16384⟩
    (by decide) selected_cut_04186

theorem selected_cut_04187 : selected 8 ⟨132362, by decide⟩
    (prefixPartial 13 71891) = some ⟨13, 2, 0, 132362, 71891, 865, 16384⟩ := by
  decide +kernel

theorem context_13_71891_132362 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71891 ⟨132362, by decide⟩ :=
  accepted_of_selected 13 71891 ⟨132362, by decide⟩ ⟨13, 2, 0, 132362, 71891, 865, 16384⟩
    (by decide) selected_cut_04187

theorem unmarked_context_12_17972_132363 : frontier 9 ⟨132363, by decide⟩
    (prefixCache 12 17972) (prefixPartial 12 17972) = false := by
  decide +kernel

theorem node_context_12_17972_132363 : EJMOriginalGlobalDAGData.nodes 9 ⟨132363, by decide⟩ =
    .split (coordinate 12) (![⟨132287, by decide⟩,⟨132335, by decide⟩,⟨132351, by decide⟩,⟨132362, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17972_132363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17972 ⟨132363, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17972
    ⟨132363, by decide⟩ (by decide) (![⟨132287, by decide⟩,⟨132335, by decide⟩,⟨132351, by decide⟩,⟨132362, by decide⟩]) unmarked_context_12_17972_132363 node_context_12_17972_132363
  intro a
  fin_cases a
  · exact context_13_71888_132287
  · exact context_13_71889_132335
  · exact context_13_71890_132351
  · exact context_13_71891_132362

theorem selected_cut_04188 : selected 8 ⟨132378, by decide⟩
    (prefixPartial 13 71892) = some ⟨13, 2, 0, 132378, 71892, 505, 16384⟩ := by
  decide +kernel

theorem context_13_71892_132378 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71892 ⟨132378, by decide⟩ :=
  accepted_of_selected 13 71892 ⟨132378, by decide⟩ ⟨13, 2, 0, 132378, 71892, 505, 16384⟩
    (by decide) selected_cut_04188

theorem selected_cut_04189 : selected 8 ⟨132427, by decide⟩
    (prefixPartial 13 71893) = some ⟨13, 2, 0, 132427, 71893, 2041, 16384⟩ := by
  decide +kernel

theorem context_13_71893_132427 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71893 ⟨132427, by decide⟩ :=
  accepted_of_selected 13 71893 ⟨132427, by decide⟩ ⟨13, 2, 0, 132427, 71893, 2041, 16384⟩
    (by decide) selected_cut_04189

theorem selected_cut_04190 : selected 8 ⟨132446, by decide⟩
    (prefixPartial 13 71894) = some ⟨13, 2, 0, 132446, 71894, 1145, 16384⟩ := by
  decide +kernel

theorem context_13_71894_132446 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71894 ⟨132446, by decide⟩ :=
  accepted_of_selected 13 71894 ⟨132446, by decide⟩ ⟨13, 2, 0, 132446, 71894, 1145, 16384⟩
    (by decide) selected_cut_04190

theorem selected_cut_04191 : selected 8 ⟨132457, by decide⟩
    (prefixPartial 13 71895) = some ⟨13, 2, 0, 132457, 71895, 737, 16384⟩ := by
  decide +kernel

theorem context_13_71895_132457 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71895 ⟨132457, by decide⟩ :=
  accepted_of_selected 13 71895 ⟨132457, by decide⟩ ⟨13, 2, 0, 132457, 71895, 737, 16384⟩
    (by decide) selected_cut_04191

theorem unmarked_context_12_17973_132458 : frontier 9 ⟨132458, by decide⟩
    (prefixCache 12 17973) (prefixPartial 12 17973) = false := by
  decide +kernel

theorem node_context_12_17973_132458 : EJMOriginalGlobalDAGData.nodes 9 ⟨132458, by decide⟩ =
    .split (coordinate 12) (![⟨132378, by decide⟩,⟨132427, by decide⟩,⟨132446, by decide⟩,⟨132457, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17973_132458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17973 ⟨132458, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17973
    ⟨132458, by decide⟩ (by decide) (![⟨132378, by decide⟩,⟨132427, by decide⟩,⟨132446, by decide⟩,⟨132457, by decide⟩]) unmarked_context_12_17973_132458 node_context_12_17973_132458
  intro a
  fin_cases a
  · exact context_13_71892_132378
  · exact context_13_71893_132427
  · exact context_13_71894_132446
  · exact context_13_71895_132457

theorem selected_cut_04192 : selected 8 ⟨132469, by decide⟩
    (prefixPartial 13 71896) = some ⟨13, 2, 0, 132469, 71896, 401, 16384⟩ := by
  decide +kernel

theorem context_13_71896_132469 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71896 ⟨132469, by decide⟩ :=
  accepted_of_selected 13 71896 ⟨132469, by decide⟩ ⟨13, 2, 0, 132469, 71896, 401, 16384⟩
    (by decide) selected_cut_04192

theorem selected_cut_04193 : selected 8 ⟨132519, by decide⟩
    (prefixPartial 13 71897) = some ⟨13, 2, 0, 132519, 71897, 2053, 16384⟩ := by
  decide +kernel

theorem context_13_71897_132519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71897 ⟨132519, by decide⟩ :=
  accepted_of_selected 13 71897 ⟨132519, by decide⟩ ⟨13, 2, 0, 132519, 71897, 2053, 16384⟩
    (by decide) selected_cut_04193

theorem selected_cut_04194 : selected 8 ⟨132535, by decide⟩
    (prefixPartial 13 71898) = some ⟨13, 2, 0, 132535, 71898, 997, 16384⟩ := by
  decide +kernel

theorem context_13_71898_132535 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71898 ⟨132535, by decide⟩ :=
  accepted_of_selected 13 71898 ⟨132535, by decide⟩ ⟨13, 2, 0, 132535, 71898, 997, 16384⟩
    (by decide) selected_cut_04194

theorem selected_cut_04195 : selected 8 ⟨132549, by decide⟩
    (prefixPartial 13 71899) = some ⟨13, 2, 0, 132549, 71899, 797, 16384⟩ := by
  decide +kernel

theorem context_13_71899_132549 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71899 ⟨132549, by decide⟩ :=
  accepted_of_selected 13 71899 ⟨132549, by decide⟩ ⟨13, 2, 0, 132549, 71899, 797, 16384⟩
    (by decide) selected_cut_04195

theorem unmarked_context_12_17974_132550 : frontier 9 ⟨132550, by decide⟩
    (prefixCache 12 17974) (prefixPartial 12 17974) = false := by
  decide +kernel

theorem node_context_12_17974_132550 : EJMOriginalGlobalDAGData.nodes 9 ⟨132550, by decide⟩ =
    .split (coordinate 12) (![⟨132469, by decide⟩,⟨132519, by decide⟩,⟨132535, by decide⟩,⟨132549, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17974_132550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17974 ⟨132550, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17974
    ⟨132550, by decide⟩ (by decide) (![⟨132469, by decide⟩,⟨132519, by decide⟩,⟨132535, by decide⟩,⟨132549, by decide⟩]) unmarked_context_12_17974_132550 node_context_12_17974_132550
  intro a
  fin_cases a
  · exact context_13_71896_132469
  · exact context_13_71897_132519
  · exact context_13_71898_132535
  · exact context_13_71899_132549

theorem selected_cut_04196 : selected 8 ⟨132562, by decide⟩
    (prefixPartial 13 71900) = some ⟨13, 2, 0, 132562, 71900, 497, 16384⟩ := by
  decide +kernel

theorem context_13_71900_132562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71900 ⟨132562, by decide⟩ :=
  accepted_of_selected 13 71900 ⟨132562, by decide⟩ ⟨13, 2, 0, 132562, 71900, 497, 16384⟩
    (by decide) selected_cut_04196

theorem selected_cut_04197 : selected 8 ⟨132616, by decide⟩
    (prefixPartial 13 71901) = some ⟨13, 2, 0, 132616, 71901, 2245, 16384⟩ := by
  decide +kernel

theorem context_13_71901_132616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71901 ⟨132616, by decide⟩ :=
  accepted_of_selected 13 71901 ⟨132616, by decide⟩ ⟨13, 2, 0, 132616, 71901, 2245, 16384⟩
    (by decide) selected_cut_04197

theorem selected_cut_04198 : selected 8 ⟨132633, by decide⟩
    (prefixPartial 13 71902) = some ⟨13, 2, 0, 132633, 71902, 1229, 16384⟩ := by
  decide +kernel

theorem context_13_71902_132633 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71902 ⟨132633, by decide⟩ :=
  accepted_of_selected 13 71902 ⟨132633, by decide⟩ ⟨13, 2, 0, 132633, 71902, 1229, 16384⟩
    (by decide) selected_cut_04198

theorem selected_cut_04199 : selected 8 ⟨132646, by decide⟩
    (prefixPartial 13 71903) = some ⟨13, 2, 0, 132646, 71903, 821, 16384⟩ := by
  decide +kernel

theorem context_13_71903_132646 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71903 ⟨132646, by decide⟩ :=
  accepted_of_selected 13 71903 ⟨132646, by decide⟩ ⟨13, 2, 0, 132646, 71903, 821, 16384⟩
    (by decide) selected_cut_04199

theorem unmarked_context_12_17975_132647 : frontier 9 ⟨132647, by decide⟩
    (prefixCache 12 17975) (prefixPartial 12 17975) = false := by
  decide +kernel

theorem node_context_12_17975_132647 : EJMOriginalGlobalDAGData.nodes 9 ⟨132647, by decide⟩ =
    .split (coordinate 12) (![⟨132562, by decide⟩,⟨132616, by decide⟩,⟨132633, by decide⟩,⟨132646, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17975_132647 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17975 ⟨132647, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17975
    ⟨132647, by decide⟩ (by decide) (![⟨132562, by decide⟩,⟨132616, by decide⟩,⟨132633, by decide⟩,⟨132646, by decide⟩]) unmarked_context_12_17975_132647 node_context_12_17975_132647
  intro a
  fin_cases a
  · exact context_13_71900_132562
  · exact context_13_71901_132616
  · exact context_13_71902_132633
  · exact context_13_71903_132646

theorem unmarked_context_11_4493_132648 : frontier 10 ⟨132648, by decide⟩
    (prefixCache 11 4493) (prefixPartial 11 4493) = false := by
  decide +kernel

theorem node_context_11_4493_132648 : EJMOriginalGlobalDAGData.nodes 10 ⟨132648, by decide⟩ =
    .split (coordinate 11) (![⟨132363, by decide⟩,⟨132458, by decide⟩,⟨132550, by decide⟩,⟨132647, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4493_132648 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4493 ⟨132648, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4493
    ⟨132648, by decide⟩ (by decide) (![⟨132363, by decide⟩,⟨132458, by decide⟩,⟨132550, by decide⟩,⟨132647, by decide⟩]) unmarked_context_11_4493_132648 node_context_11_4493_132648
  intro a
  fin_cases a
  · exact context_12_17972_132363
  · exact context_12_17973_132458
  · exact context_12_17974_132550
  · exact context_12_17975_132647

theorem selected_cut_04200 : selected 9 ⟨132712, by decide⟩
    (prefixPartial 12 17976) = some ⟨12, 2, 0, 132712, 17976, 3681, 65536⟩ := by
  decide +kernel

theorem context_12_17976_132712 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17976 ⟨132712, by decide⟩ :=
  accepted_of_selected 12 17976 ⟨132712, by decide⟩ ⟨12, 2, 0, 132712, 17976, 3681, 65536⟩
    (by decide) selected_cut_04200

theorem selected_cut_04201 : selected 8 ⟨132720, by decide⟩
    (prefixPartial 13 71908) = some ⟨13, 2, 0, 132720, 71908, 373, 16384⟩ := by
  decide +kernel

theorem context_13_71908_132720 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71908 ⟨132720, by decide⟩ :=
  accepted_of_selected 13 71908 ⟨132720, by decide⟩ ⟨13, 2, 0, 132720, 71908, 373, 16384⟩
    (by decide) selected_cut_04201

theorem selected_cut_04202 : selected 8 ⟨132769, by decide⟩
    (prefixPartial 13 71909) = some ⟨13, 2, 0, 132769, 71909, 1945, 16384⟩ := by
  decide +kernel

theorem context_13_71909_132769 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71909 ⟨132769, by decide⟩ :=
  accepted_of_selected 13 71909 ⟨132769, by decide⟩ ⟨13, 2, 0, 132769, 71909, 1945, 16384⟩
    (by decide) selected_cut_04202

theorem selected_cut_04203 : selected 8 ⟨132785, by decide⟩
    (prefixPartial 13 71910) = some ⟨13, 2, 0, 132785, 71910, 1157, 16384⟩ := by
  decide +kernel

theorem context_13_71910_132785 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71910 ⟨132785, by decide⟩ :=
  accepted_of_selected 13 71910 ⟨132785, by decide⟩ ⟨13, 2, 0, 132785, 71910, 1157, 16384⟩
    (by decide) selected_cut_04203

theorem selected_cut_04204 : selected 8 ⟨132796, by decide⟩
    (prefixPartial 13 71911) = some ⟨13, 2, 0, 132796, 71911, 709, 16384⟩ := by
  decide +kernel

theorem context_13_71911_132796 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71911 ⟨132796, by decide⟩ :=
  accepted_of_selected 13 71911 ⟨132796, by decide⟩ ⟨13, 2, 0, 132796, 71911, 709, 16384⟩
    (by decide) selected_cut_04204

theorem unmarked_context_12_17977_132797 : frontier 9 ⟨132797, by decide⟩
    (prefixCache 12 17977) (prefixPartial 12 17977) = false := by
  decide +kernel

theorem node_context_12_17977_132797 : EJMOriginalGlobalDAGData.nodes 9 ⟨132797, by decide⟩ =
    .split (coordinate 12) (![⟨132720, by decide⟩,⟨132769, by decide⟩,⟨132785, by decide⟩,⟨132796, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17977_132797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17977 ⟨132797, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17977
    ⟨132797, by decide⟩ (by decide) (![⟨132720, by decide⟩,⟨132769, by decide⟩,⟨132785, by decide⟩,⟨132796, by decide⟩]) unmarked_context_12_17977_132797 node_context_12_17977_132797
  intro a
  fin_cases a
  · exact context_13_71908_132720
  · exact context_13_71909_132769
  · exact context_13_71910_132785
  · exact context_13_71911_132796

theorem selected_cut_04205 : selected 8 ⟨132804, by decide⟩
    (prefixPartial 13 71912) = some ⟨13, 2, 0, 132804, 71912, 349, 16384⟩ := by
  decide +kernel

theorem context_13_71912_132804 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71912 ⟨132804, by decide⟩ :=
  accepted_of_selected 13 71912 ⟨132804, by decide⟩ ⟨13, 2, 0, 132804, 71912, 349, 16384⟩
    (by decide) selected_cut_04205

theorem selected_cut_04206 : selected 8 ⟨132870, by decide⟩
    (prefixPartial 13 71913) = some ⟨13, 2, 0, 132870, 71913, 2857, 16384⟩ := by
  decide +kernel

theorem context_13_71913_132870 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71913 ⟨132870, by decide⟩ :=
  accepted_of_selected 13 71913 ⟨132870, by decide⟩ ⟨13, 2, 0, 132870, 71913, 2857, 16384⟩
    (by decide) selected_cut_04206

theorem selected_cut_04207 : selected 8 ⟨132891, by decide⟩
    (prefixPartial 13 71914) = some ⟨13, 2, 0, 132891, 71914, 1569, 16384⟩ := by
  decide +kernel

theorem context_13_71914_132891 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71914 ⟨132891, by decide⟩ :=
  accepted_of_selected 13 71914 ⟨132891, by decide⟩ ⟨13, 2, 0, 132891, 71914, 1569, 16384⟩
    (by decide) selected_cut_04207

theorem selected_cut_04208 : selected 8 ⟨132904, by decide⟩
    (prefixPartial 13 71915) = some ⟨13, 2, 0, 132904, 71915, 949, 16384⟩ := by
  decide +kernel

theorem context_13_71915_132904 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71915 ⟨132904, by decide⟩ :=
  accepted_of_selected 13 71915 ⟨132904, by decide⟩ ⟨13, 2, 0, 132904, 71915, 949, 16384⟩
    (by decide) selected_cut_04208

theorem unmarked_context_12_17978_132905 : frontier 9 ⟨132905, by decide⟩
    (prefixCache 12 17978) (prefixPartial 12 17978) = false := by
  decide +kernel

theorem node_context_12_17978_132905 : EJMOriginalGlobalDAGData.nodes 9 ⟨132905, by decide⟩ =
    .split (coordinate 12) (![⟨132804, by decide⟩,⟨132870, by decide⟩,⟨132891, by decide⟩,⟨132904, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17978_132905 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17978 ⟨132905, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17978
    ⟨132905, by decide⟩ (by decide) (![⟨132804, by decide⟩,⟨132870, by decide⟩,⟨132891, by decide⟩,⟨132904, by decide⟩]) unmarked_context_12_17978_132905 node_context_12_17978_132905
  intro a
  fin_cases a
  · exact context_13_71912_132804
  · exact context_13_71913_132870
  · exact context_13_71914_132891
  · exact context_13_71915_132904

theorem selected_cut_04209 : selected 9 ⟨132992, by decide⟩
    (prefixPartial 12 17979) = some ⟨12, 2, 0, 132992, 17979, 3993, 65536⟩ := by
  decide +kernel

theorem context_12_17979_132992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17979 ⟨132992, by decide⟩ :=
  accepted_of_selected 12 17979 ⟨132992, by decide⟩ ⟨12, 2, 0, 132992, 17979, 3993, 65536⟩
    (by decide) selected_cut_04209

theorem unmarked_context_11_4494_132993 : frontier 10 ⟨132993, by decide⟩
    (prefixCache 11 4494) (prefixPartial 11 4494) = false := by
  decide +kernel

theorem node_context_11_4494_132993 : EJMOriginalGlobalDAGData.nodes 10 ⟨132993, by decide⟩ =
    .split (coordinate 11) (![⟨132712, by decide⟩,⟨132797, by decide⟩,⟨132905, by decide⟩,⟨132992, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4494_132993 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4494 ⟨132993, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4494
    ⟨132993, by decide⟩ (by decide) (![⟨132712, by decide⟩,⟨132797, by decide⟩,⟨132905, by decide⟩,⟨132992, by decide⟩]) unmarked_context_11_4494_132993 node_context_11_4494_132993
  intro a
  fin_cases a
  · exact context_12_17976_132712
  · exact context_12_17977_132797
  · exact context_12_17978_132905
  · exact context_12_17979_132992

theorem selected_cut_04210 : selected 9 ⟨133056, by decide⟩
    (prefixPartial 12 17980) = some ⟨12, 2, 0, 133056, 17980, 3789, 65536⟩ := by
  decide +kernel

theorem context_12_17980_133056 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17980 ⟨133056, by decide⟩ :=
  accepted_of_selected 12 17980 ⟨133056, by decide⟩ ⟨12, 2, 0, 133056, 17980, 3789, 65536⟩
    (by decide) selected_cut_04210

theorem selected_cut_04211 : selected 8 ⟨133060, by decide⟩
    (prefixPartial 13 71924) = some ⟨13, 2, 0, 133060, 71924, 133, 16384⟩ := by
  decide +kernel

theorem context_13_71924_133060 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71924 ⟨133060, by decide⟩ :=
  accepted_of_selected 13 71924 ⟨133060, by decide⟩ ⟨13, 2, 0, 133060, 71924, 133, 16384⟩
    (by decide) selected_cut_04211

theorem selected_cut_04212 : selected 8 ⟨133113, by decide⟩
    (prefixPartial 13 71925) = some ⟨13, 2, 0, 133113, 71925, 2129, 16384⟩ := by
  decide +kernel

theorem context_13_71925_133113 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71925 ⟨133113, by decide⟩ :=
  accepted_of_selected 13 71925 ⟨133113, by decide⟩ ⟨13, 2, 0, 133113, 71925, 2129, 16384⟩
    (by decide) selected_cut_04212

theorem selected_cut_04213 : selected 8 ⟨133130, by decide⟩
    (prefixPartial 13 71926) = some ⟨13, 2, 0, 133130, 71926, 1321, 16384⟩ := by
  decide +kernel

theorem context_13_71926_133130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71926 ⟨133130, by decide⟩ :=
  accepted_of_selected 13 71926 ⟨133130, by decide⟩ ⟨13, 2, 0, 133130, 71926, 1321, 16384⟩
    (by decide) selected_cut_04213

theorem selected_cut_04214 : selected 8 ⟨133141, by decide⟩
    (prefixPartial 13 71927) = some ⟨13, 2, 0, 133141, 71927, 669, 16384⟩ := by
  decide +kernel

theorem context_13_71927_133141 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 71927 ⟨133141, by decide⟩ :=
  accepted_of_selected 13 71927 ⟨133141, by decide⟩ ⟨13, 2, 0, 133141, 71927, 669, 16384⟩
    (by decide) selected_cut_04214

theorem unmarked_context_12_17981_133142 : frontier 9 ⟨133142, by decide⟩
    (prefixCache 12 17981) (prefixPartial 12 17981) = false := by
  decide +kernel

theorem node_context_12_17981_133142 : EJMOriginalGlobalDAGData.nodes 9 ⟨133142, by decide⟩ =
    .split (coordinate 12) (![⟨133060, by decide⟩,⟨133113, by decide⟩,⟨133130, by decide⟩,⟨133141, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17981_133142 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17981 ⟨133142, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17981
    ⟨133142, by decide⟩ (by decide) (![⟨133060, by decide⟩,⟨133113, by decide⟩,⟨133130, by decide⟩,⟨133141, by decide⟩]) unmarked_context_12_17981_133142 node_context_12_17981_133142
  intro a
  fin_cases a
  · exact context_13_71924_133060
  · exact context_13_71925_133113
  · exact context_13_71926_133130
  · exact context_13_71927_133141

theorem selected_cut_04215 : selected 9 ⟨133210, by decide⟩
    (prefixPartial 12 17982) = some ⟨12, 2, 0, 133210, 17982, 3577, 65536⟩ := by
  decide +kernel

theorem context_12_17982_133210 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17982 ⟨133210, by decide⟩ :=
  accepted_of_selected 12 17982 ⟨133210, by decide⟩ ⟨12, 2, 0, 133210, 17982, 3577, 65536⟩
    (by decide) selected_cut_04215

theorem selected_cut_04216 : selected 9 ⟨133277, by decide⟩
    (prefixPartial 12 17983) = some ⟨12, 2, 0, 133277, 17983, 3549, 65536⟩ := by
  decide +kernel

theorem context_12_17983_133277 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17983 ⟨133277, by decide⟩ :=
  accepted_of_selected 12 17983 ⟨133277, by decide⟩ ⟨12, 2, 0, 133277, 17983, 3549, 65536⟩
    (by decide) selected_cut_04216

theorem unmarked_context_11_4495_133278 : frontier 10 ⟨133278, by decide⟩
    (prefixCache 11 4495) (prefixPartial 11 4495) = false := by
  decide +kernel

theorem node_context_11_4495_133278 : EJMOriginalGlobalDAGData.nodes 10 ⟨133278, by decide⟩ =
    .split (coordinate 11) (![⟨133056, by decide⟩,⟨133142, by decide⟩,⟨133210, by decide⟩,⟨133277, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4495_133278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4495 ⟨133278, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4495
    ⟨133278, by decide⟩ (by decide) (![⟨133056, by decide⟩,⟨133142, by decide⟩,⟨133210, by decide⟩,⟨133277, by decide⟩]) unmarked_context_11_4495_133278 node_context_11_4495_133278
  intro a
  fin_cases a
  · exact context_12_17980_133056
  · exact context_12_17981_133142
  · exact context_12_17982_133210
  · exact context_12_17983_133277

theorem unmarked_context_10_1123_133279 : frontier 11 ⟨133279, by decide⟩
    (prefixCache 10 1123) (prefixPartial 10 1123) = false := by
  decide +kernel

theorem node_context_10_1123_133279 : EJMOriginalGlobalDAGData.nodes 11 ⟨133279, by decide⟩ =
    .split (coordinate 10) (![⟨132275, by decide⟩,⟨132648, by decide⟩,⟨132993, by decide⟩,⟨133278, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1123_133279 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1123 ⟨133279, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1123
    ⟨133279, by decide⟩ (by decide) (![⟨132275, by decide⟩,⟨132648, by decide⟩,⟨132993, by decide⟩,⟨133278, by decide⟩]) unmarked_context_10_1123_133279 node_context_10_1123_133279
  intro a
  fin_cases a
  · exact context_11_4492_132275
  · exact context_11_4493_132648
  · exact context_11_4494_132993
  · exact context_11_4495_133278

theorem unmarked_context_9_280_133280 : frontier 12 ⟨133280, by decide⟩
    (prefixCache 9 280) (prefixPartial 9 280) = false := by
  decide +kernel

theorem node_context_9_280_133280 : EJMOriginalGlobalDAGData.nodes 12 ⟨133280, by decide⟩ =
    .split (coordinate 9) (![⟨129019, by decide⟩,⟨130661, by decide⟩,⟨131878, by decide⟩,⟨133279, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_280_133280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 280 ⟨133280, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 280
    ⟨133280, by decide⟩ (by decide) (![⟨129019, by decide⟩,⟨130661, by decide⟩,⟨131878, by decide⟩,⟨133279, by decide⟩]) unmarked_context_9_280_133280 node_context_9_280_133280
  intro a
  fin_cases a
  · exact context_10_1120_129019
  · exact context_10_1121_130661
  · exact context_10_1122_131878
  · exact context_10_1123_133279

theorem selected_cut_04217 : selected 11 ⟨3442, by decide⟩
    (prefixPartial 10 1124) = some ⟨10, 1, 0, 3442, 1124, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_1124_3442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1124 ⟨3442, by decide⟩ :=
  accepted_of_selected 10 1124 ⟨3442, by decide⟩ ⟨10, 1, 0, 3442, 1124, 1, 1048576⟩
    (by decide) selected_cut_04217

theorem selected_cut_04218 : selected 9 ⟨133339, by decide⟩
    (prefixPartial 12 18000) = some ⟨12, 2, 0, 133339, 18000, 2113, 65536⟩ := by
  decide +kernel

theorem context_12_18000_133339 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18000 ⟨133339, by decide⟩ :=
  accepted_of_selected 12 18000 ⟨133339, by decide⟩ ⟨12, 2, 0, 133339, 18000, 2113, 65536⟩
    (by decide) selected_cut_04218

theorem selected_cut_04219 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 72004) = some ⟨13, 1, 0, 3444, 72004, 1, 16384⟩ := by
  decide +kernel

theorem context_13_72004_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 72004 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 72004 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 72004, 1, 16384⟩
    (by decide) selected_cut_04219

theorem selected_cut_04220 : selected 8 ⟨133396, by decide⟩
    (prefixPartial 13 72005) = some ⟨13, 2, 0, 133396, 72005, 2245, 16384⟩ := by
  decide +kernel

theorem context_13_72005_133396 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 72005 ⟨133396, by decide⟩ :=
  accepted_of_selected 13 72005 ⟨133396, by decide⟩ ⟨13, 2, 0, 133396, 72005, 2245, 16384⟩
    (by decide) selected_cut_04220

theorem selected_cut_04221 : selected 8 ⟨133426, by decide⟩
    (prefixPartial 13 72006) = some ⟨13, 2, 0, 133426, 72006, 1361, 16384⟩ := by
  decide +kernel

theorem context_13_72006_133426 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 72006 ⟨133426, by decide⟩ :=
  accepted_of_selected 13 72006 ⟨133426, by decide⟩ ⟨13, 2, 0, 133426, 72006, 1361, 16384⟩
    (by decide) selected_cut_04221

theorem selected_cut_04222 : selected 8 ⟨133438, by decide⟩
    (prefixPartial 13 72007) = some ⟨13, 2, 0, 133438, 72007, 933, 16384⟩ := by
  decide +kernel

theorem context_13_72007_133438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 72007 ⟨133438, by decide⟩ :=
  accepted_of_selected 13 72007 ⟨133438, by decide⟩ ⟨13, 2, 0, 133438, 72007, 933, 16384⟩
    (by decide) selected_cut_04222

theorem unmarked_context_12_18001_133439 : frontier 9 ⟨133439, by decide⟩
    (prefixCache 12 18001) (prefixPartial 12 18001) = false := by
  decide +kernel

theorem node_context_12_18001_133439 : EJMOriginalGlobalDAGData.nodes 9 ⟨133439, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨133396, by decide⟩,⟨133426, by decide⟩,⟨133438, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18001_133439 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18001 ⟨133439, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18001
    ⟨133439, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨133396, by decide⟩,⟨133426, by decide⟩,⟨133438, by decide⟩]) unmarked_context_12_18001_133439 node_context_12_18001_133439
  intro a
  fin_cases a
  · exact context_13_72004_3444
  · exact context_13_72005_133396
  · exact context_13_72006_133426
  · exact context_13_72007_133438

theorem selected_cut_04223 : selected 9 ⟨133510, by decide⟩
    (prefixPartial 12 18002) = some ⟨12, 2, 0, 133510, 18002, 3317, 65536⟩ := by
  decide +kernel

theorem context_12_18002_133510 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18002 ⟨133510, by decide⟩ :=
  accepted_of_selected 12 18002 ⟨133510, by decide⟩ ⟨12, 2, 0, 133510, 18002, 3317, 65536⟩
    (by decide) selected_cut_04223

theorem selected_cut_04224 : selected 9 ⟨133576, by decide⟩
    (prefixPartial 12 18003) = some ⟨12, 2, 0, 133576, 18003, 3665, 65536⟩ := by
  decide +kernel

theorem context_12_18003_133576 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18003 ⟨133576, by decide⟩ :=
  accepted_of_selected 12 18003 ⟨133576, by decide⟩ ⟨12, 2, 0, 133576, 18003, 3665, 65536⟩
    (by decide) selected_cut_04224

theorem unmarked_context_11_4500_133577 : frontier 10 ⟨133577, by decide⟩
    (prefixCache 11 4500) (prefixPartial 11 4500) = false := by
  decide +kernel

theorem node_context_11_4500_133577 : EJMOriginalGlobalDAGData.nodes 10 ⟨133577, by decide⟩ =
    .split (coordinate 11) (![⟨133339, by decide⟩,⟨133439, by decide⟩,⟨133510, by decide⟩,⟨133576, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4500_133577 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4500 ⟨133577, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4500
    ⟨133577, by decide⟩ (by decide) (![⟨133339, by decide⟩,⟨133439, by decide⟩,⟨133510, by decide⟩,⟨133576, by decide⟩]) unmarked_context_11_4500_133577 node_context_11_4500_133577
  intro a
  fin_cases a
  · exact context_12_18000_133339
  · exact context_12_18001_133439
  · exact context_12_18002_133510
  · exact context_12_18003_133576

theorem selected_cut_04225 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 18004) = some ⟨12, 1, 0, 895, 18004, 1, 65536⟩ := by
  decide +kernel

theorem context_12_18004_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18004 ⟨895, by decide⟩ :=
  accepted_of_selected 12 18004 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 18004, 1, 65536⟩
    (by decide) selected_cut_04225

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
