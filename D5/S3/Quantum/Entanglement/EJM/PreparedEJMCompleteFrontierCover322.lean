/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover321
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_30916 : selected 9 ⟨786221, by decide⟩
    (prefixPartial 12 105271) = some ⟨12, 2, 0, 786221, 105271, 3489, 65536⟩ := by
  decide +kernel

theorem context_12_105271_786221 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105271 ⟨786221, by decide⟩ :=
  accepted_of_selected 12 105271 ⟨786221, by decide⟩ ⟨12, 2, 0, 786221, 105271, 3489, 65536⟩
    (by decide) selected_cut_30916

theorem unmarked_context_11_26317_786222 : frontier 10 ⟨786222, by decide⟩
    (prefixCache 11 26317) (prefixPartial 11 26317) = false := by
  decide +kernel

theorem node_context_11_26317_786222 : EJMOriginalGlobalDAGData.nodes 10 ⟨786222, by decide⟩ =
    .split (coordinate 11) (![⟨786007, by decide⟩,⟨786092, by decide⟩,⟨786161, by decide⟩,⟨786221, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26317_786222 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26317 ⟨786222, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26317
    ⟨786222, by decide⟩ (by decide) (![⟨786007, by decide⟩,⟨786092, by decide⟩,⟨786161, by decide⟩,⟨786221, by decide⟩]) unmarked_context_11_26317_786222 node_context_11_26317_786222
  intro a
  fin_cases a
  · exact context_12_105268_786007
  · exact context_12_105269_786092
  · exact context_12_105270_786161
  · exact context_12_105271_786221

theorem selected_cut_30917 : selected 9 ⟨786272, by decide⟩
    (prefixPartial 12 105272) = some ⟨12, 2, 0, 786272, 105272, 3309, 65536⟩ := by
  decide +kernel

theorem context_12_105272_786272 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105272 ⟨786272, by decide⟩ :=
  accepted_of_selected 12 105272 ⟨786272, by decide⟩ ⟨12, 2, 0, 786272, 105272, 3309, 65536⟩
    (by decide) selected_cut_30917

theorem selected_cut_30918 : selected 9 ⟨786334, by decide⟩
    (prefixPartial 12 105273) = some ⟨12, 2, 0, 786334, 105273, 3533, 65536⟩ := by
  decide +kernel

theorem context_12_105273_786334 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105273 ⟨786334, by decide⟩ :=
  accepted_of_selected 12 105273 ⟨786334, by decide⟩ ⟨12, 2, 0, 786334, 105273, 3533, 65536⟩
    (by decide) selected_cut_30918

theorem selected_cut_30919 : selected 9 ⟨786385, by decide⟩
    (prefixPartial 12 105274) = some ⟨12, 2, 0, 786385, 105274, 3365, 65536⟩ := by
  decide +kernel

theorem context_12_105274_786385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105274 ⟨786385, by decide⟩ :=
  accepted_of_selected 12 105274 ⟨786385, by decide⟩ ⟨12, 2, 0, 786385, 105274, 3365, 65536⟩
    (by decide) selected_cut_30919

theorem selected_cut_30920 : selected 9 ⟨786436, by decide⟩
    (prefixPartial 12 105275) = some ⟨12, 2, 0, 786436, 105275, 3353, 65536⟩ := by
  decide +kernel

theorem context_12_105275_786436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105275 ⟨786436, by decide⟩ :=
  accepted_of_selected 12 105275 ⟨786436, by decide⟩ ⟨12, 2, 0, 786436, 105275, 3353, 65536⟩
    (by decide) selected_cut_30920

theorem unmarked_context_11_26318_786437 : frontier 10 ⟨786437, by decide⟩
    (prefixCache 11 26318) (prefixPartial 11 26318) = false := by
  decide +kernel

theorem node_context_11_26318_786437 : EJMOriginalGlobalDAGData.nodes 10 ⟨786437, by decide⟩ =
    .split (coordinate 11) (![⟨786272, by decide⟩,⟨786334, by decide⟩,⟨786385, by decide⟩,⟨786436, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26318_786437 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26318 ⟨786437, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26318
    ⟨786437, by decide⟩ (by decide) (![⟨786272, by decide⟩,⟨786334, by decide⟩,⟨786385, by decide⟩,⟨786436, by decide⟩]) unmarked_context_11_26318_786437 node_context_11_26318_786437
  intro a
  fin_cases a
  · exact context_12_105272_786272
  · exact context_12_105273_786334
  · exact context_12_105274_786385
  · exact context_12_105275_786436

theorem selected_cut_30921 : selected 9 ⟨786498, by decide⟩
    (prefixPartial 12 105276) = some ⟨12, 2, 0, 786498, 105276, 3021, 65536⟩ := by
  decide +kernel

theorem context_12_105276_786498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105276 ⟨786498, by decide⟩ :=
  accepted_of_selected 12 105276 ⟨786498, by decide⟩ ⟨12, 2, 0, 786498, 105276, 3021, 65536⟩
    (by decide) selected_cut_30921

theorem selected_cut_30922 : selected 9 ⟨786552, by decide⟩
    (prefixPartial 12 105277) = some ⟨12, 2, 0, 786552, 105277, 3269, 65536⟩ := by
  decide +kernel

theorem context_12_105277_786552 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105277 ⟨786552, by decide⟩ :=
  accepted_of_selected 12 105277 ⟨786552, by decide⟩ ⟨12, 2, 0, 786552, 105277, 3269, 65536⟩
    (by decide) selected_cut_30922

theorem selected_cut_30923 : selected 9 ⟨786598, by decide⟩
    (prefixPartial 12 105278) = some ⟨12, 2, 0, 786598, 105278, 3077, 65536⟩ := by
  decide +kernel

theorem context_12_105278_786598 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105278 ⟨786598, by decide⟩ :=
  accepted_of_selected 12 105278 ⟨786598, by decide⟩ ⟨12, 2, 0, 786598, 105278, 3077, 65536⟩
    (by decide) selected_cut_30923

theorem selected_cut_30924 : selected 9 ⟨512556, by decide⟩
    (prefixPartial 12 105279) = some ⟨12, 1, 0, 512556, 105279, 1, 65536⟩ := by
  decide +kernel

theorem context_12_105279_512556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105279 ⟨512556, by decide⟩ :=
  accepted_of_selected 12 105279 ⟨512556, by decide⟩ ⟨12, 1, 0, 512556, 105279, 1, 65536⟩
    (by decide) selected_cut_30924

theorem unmarked_context_11_26319_786599 : frontier 10 ⟨786599, by decide⟩
    (prefixCache 11 26319) (prefixPartial 11 26319) = false := by
  decide +kernel

theorem node_context_11_26319_786599 : EJMOriginalGlobalDAGData.nodes 10 ⟨786599, by decide⟩ =
    .split (coordinate 11) (![⟨786498, by decide⟩,⟨786552, by decide⟩,⟨786598, by decide⟩,⟨512556, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26319_786599 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26319 ⟨786599, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26319
    ⟨786599, by decide⟩ (by decide) (![⟨786498, by decide⟩,⟨786552, by decide⟩,⟨786598, by decide⟩,⟨512556, by decide⟩]) unmarked_context_11_26319_786599 node_context_11_26319_786599
  intro a
  fin_cases a
  · exact context_12_105276_786498
  · exact context_12_105277_786552
  · exact context_12_105278_786598
  · exact context_12_105279_512556

theorem unmarked_context_10_6579_786600 : frontier 11 ⟨786600, by decide⟩
    (prefixCache 10 6579) (prefixPartial 10 6579) = false := by
  decide +kernel

theorem node_context_10_6579_786600 : EJMOriginalGlobalDAGData.nodes 11 ⟨786600, by decide⟩ =
    .split (coordinate 10) (![⟨785928, by decide⟩,⟨786222, by decide⟩,⟨786437, by decide⟩,⟨786599, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6579_786600 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6579 ⟨786600, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6579
    ⟨786600, by decide⟩ (by decide) (![⟨785928, by decide⟩,⟨786222, by decide⟩,⟨786437, by decide⟩,⟨786599, by decide⟩]) unmarked_context_10_6579_786600 node_context_10_6579_786600
  intro a
  fin_cases a
  · exact context_11_26316_785928
  · exact context_11_26317_786222
  · exact context_11_26318_786437
  · exact context_11_26319_786599

theorem unmarked_context_9_1644_786601 : frontier 12 ⟨786601, by decide⟩
    (prefixCache 9 1644) (prefixPartial 9 1644) = false := by
  decide +kernel

theorem node_context_9_1644_786601 : EJMOriginalGlobalDAGData.nodes 12 ⟨786601, by decide⟩ =
    .split (coordinate 9) (![⟨783309, by decide⟩,⟨784881, by decide⟩,⟨785640, by decide⟩,⟨786600, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1644_786601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1644 ⟨786601, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1644
    ⟨786601, by decide⟩ (by decide) (![⟨783309, by decide⟩,⟨784881, by decide⟩,⟨785640, by decide⟩,⟨786600, by decide⟩]) unmarked_context_9_1644_786601 node_context_9_1644_786601
  intro a
  fin_cases a
  · exact context_10_6576_783309
  · exact context_10_6577_784881
  · exact context_10_6578_785640
  · exact context_10_6579_786600

theorem selected_cut_30925 : selected 11 ⟨3442, by decide⟩
    (prefixPartial 10 6580) = some ⟨10, 1, 0, 3442, 6580, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_6580_3442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6580 ⟨3442, by decide⟩ :=
  accepted_of_selected 10 6580 ⟨3442, by decide⟩ ⟨10, 1, 0, 3442, 6580, 1, 1048576⟩
    (by decide) selected_cut_30925

theorem selected_cut_30926 : selected 9 ⟨786643, by decide⟩
    (prefixPartial 12 105296) = some ⟨12, 2, 0, 786643, 105296, 1569, 65536⟩ := by
  decide +kernel

theorem context_12_105296_786643 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105296 ⟨786643, by decide⟩ :=
  accepted_of_selected 12 105296 ⟨786643, by decide⟩ ⟨12, 2, 0, 786643, 105296, 1569, 65536⟩
    (by decide) selected_cut_30926

theorem selected_cut_30927 : selected 9 ⟨786699, by decide⟩
    (prefixPartial 12 105297) = some ⟨12, 2, 0, 786699, 105297, 2789, 65536⟩ := by
  decide +kernel

theorem context_12_105297_786699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105297 ⟨786699, by decide⟩ :=
  accepted_of_selected 12 105297 ⟨786699, by decide⟩ ⟨12, 2, 0, 786699, 105297, 2789, 65536⟩
    (by decide) selected_cut_30927

theorem selected_cut_30928 : selected 9 ⟨786751, by decide⟩
    (prefixPartial 12 105298) = some ⟨12, 2, 0, 786751, 105298, 2977, 65536⟩ := by
  decide +kernel

theorem context_12_105298_786751 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105298 ⟨786751, by decide⟩ :=
  accepted_of_selected 12 105298 ⟨786751, by decide⟩ ⟨12, 2, 0, 786751, 105298, 2977, 65536⟩
    (by decide) selected_cut_30928

theorem selected_cut_30929 : selected 9 ⟨786798, by decide⟩
    (prefixPartial 12 105299) = some ⟨12, 2, 0, 786798, 105299, 2577, 65536⟩ := by
  decide +kernel

theorem context_12_105299_786798 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105299 ⟨786798, by decide⟩ :=
  accepted_of_selected 12 105299 ⟨786798, by decide⟩ ⟨12, 2, 0, 786798, 105299, 2577, 65536⟩
    (by decide) selected_cut_30929

theorem unmarked_context_11_26324_786799 : frontier 10 ⟨786799, by decide⟩
    (prefixCache 11 26324) (prefixPartial 11 26324) = false := by
  decide +kernel

theorem node_context_11_26324_786799 : EJMOriginalGlobalDAGData.nodes 10 ⟨786799, by decide⟩ =
    .split (coordinate 11) (![⟨786643, by decide⟩,⟨786699, by decide⟩,⟨786751, by decide⟩,⟨786798, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26324_786799 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26324 ⟨786799, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26324
    ⟨786799, by decide⟩ (by decide) (![⟨786643, by decide⟩,⟨786699, by decide⟩,⟨786751, by decide⟩,⟨786798, by decide⟩]) unmarked_context_11_26324_786799 node_context_11_26324_786799
  intro a
  fin_cases a
  · exact context_12_105296_786643
  · exact context_12_105297_786699
  · exact context_12_105298_786751
  · exact context_12_105299_786798

theorem selected_cut_30930 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 105300) = some ⟨12, 1, 0, 895, 105300, 1, 65536⟩ := by
  decide +kernel

theorem context_12_105300_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105300 ⟨895, by decide⟩ :=
  accepted_of_selected 12 105300 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 105300, 1, 65536⟩
    (by decide) selected_cut_30930

theorem selected_cut_30931 : selected 9 ⟨786834, by decide⟩
    (prefixPartial 12 105301) = some ⟨12, 2, 0, 786834, 105301, 1393, 65536⟩ := by
  decide +kernel

theorem context_12_105301_786834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105301 ⟨786834, by decide⟩ :=
  accepted_of_selected 12 105301 ⟨786834, by decide⟩ ⟨12, 2, 0, 786834, 105301, 1393, 65536⟩
    (by decide) selected_cut_30931

theorem selected_cut_30932 : selected 9 ⟨786890, by decide⟩
    (prefixPartial 12 105302) = some ⟨12, 2, 0, 786890, 105302, 2617, 65536⟩ := by
  decide +kernel

theorem context_12_105302_786890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105302 ⟨786890, by decide⟩ :=
  accepted_of_selected 12 105302 ⟨786890, by decide⟩ ⟨12, 2, 0, 786890, 105302, 2617, 65536⟩
    (by decide) selected_cut_30932

theorem selected_cut_30933 : selected 9 ⟨786936, by decide⟩
    (prefixPartial 12 105303) = some ⟨12, 2, 0, 786936, 105303, 2321, 65536⟩ := by
  decide +kernel

theorem context_12_105303_786936 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105303 ⟨786936, by decide⟩ :=
  accepted_of_selected 12 105303 ⟨786936, by decide⟩ ⟨12, 2, 0, 786936, 105303, 2321, 65536⟩
    (by decide) selected_cut_30933

theorem unmarked_context_11_26325_786937 : frontier 10 ⟨786937, by decide⟩
    (prefixCache 11 26325) (prefixPartial 11 26325) = false := by
  decide +kernel

theorem node_context_11_26325_786937 : EJMOriginalGlobalDAGData.nodes 10 ⟨786937, by decide⟩ =
    .split (coordinate 11) (![⟨895, by decide⟩,⟨786834, by decide⟩,⟨786890, by decide⟩,⟨786936, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26325_786937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26325 ⟨786937, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26325
    ⟨786937, by decide⟩ (by decide) (![⟨895, by decide⟩,⟨786834, by decide⟩,⟨786890, by decide⟩,⟨786936, by decide⟩]) unmarked_context_11_26325_786937 node_context_11_26325_786937
  intro a
  fin_cases a
  · exact context_12_105300_895
  · exact context_12_105301_786834
  · exact context_12_105302_786890
  · exact context_12_105303_786936

theorem selected_cut_30934 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 105304) = some ⟨12, 1, 0, 895, 105304, 1, 65536⟩ := by
  decide +kernel

theorem context_12_105304_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105304 ⟨895, by decide⟩ :=
  accepted_of_selected 12 105304 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 105304, 1, 65536⟩
    (by decide) selected_cut_30934

theorem selected_cut_30935 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 105305) = some ⟨12, 1, 0, 895, 105305, 1, 65536⟩ := by
  decide +kernel

theorem context_12_105305_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105305 ⟨895, by decide⟩ :=
  accepted_of_selected 12 105305 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 105305, 1, 65536⟩
    (by decide) selected_cut_30935

theorem selected_cut_30936 : selected 9 ⟨786985, by decide⟩
    (prefixPartial 12 105306) = some ⟨12, 2, 0, 786985, 105306, 1725, 65536⟩ := by
  decide +kernel

theorem context_12_105306_786985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105306 ⟨786985, by decide⟩ :=
  accepted_of_selected 12 105306 ⟨786985, by decide⟩ ⟨12, 2, 0, 786985, 105306, 1725, 65536⟩
    (by decide) selected_cut_30936

theorem selected_cut_30937 : selected 9 ⟨787039, by decide⟩
    (prefixPartial 12 105307) = some ⟨12, 2, 0, 787039, 105307, 2597, 65536⟩ := by
  decide +kernel

theorem context_12_105307_787039 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105307 ⟨787039, by decide⟩ :=
  accepted_of_selected 12 105307 ⟨787039, by decide⟩ ⟨12, 2, 0, 787039, 105307, 2597, 65536⟩
    (by decide) selected_cut_30937

theorem unmarked_context_11_26326_787040 : frontier 10 ⟨787040, by decide⟩
    (prefixCache 11 26326) (prefixPartial 11 26326) = false := by
  decide +kernel

theorem node_context_11_26326_787040 : EJMOriginalGlobalDAGData.nodes 10 ⟨787040, by decide⟩ =
    .split (coordinate 11) (![⟨895, by decide⟩,⟨895, by decide⟩,⟨786985, by decide⟩,⟨787039, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26326_787040 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26326 ⟨787040, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26326
    ⟨787040, by decide⟩ (by decide) (![⟨895, by decide⟩,⟨895, by decide⟩,⟨786985, by decide⟩,⟨787039, by decide⟩]) unmarked_context_11_26326_787040 node_context_11_26326_787040
  intro a
  fin_cases a
  · exact context_12_105304_895
  · exact context_12_105305_895
  · exact context_12_105306_786985
  · exact context_12_105307_787039

theorem selected_cut_30938 : selected 10 ⟨787129, by decide⟩
    (prefixPartial 11 26327) = some ⟨11, 2, 0, 787129, 26327, 821, 262144⟩ := by
  decide +kernel

theorem context_11_26327_787129 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26327 ⟨787129, by decide⟩ :=
  accepted_of_selected 11 26327 ⟨787129, by decide⟩ ⟨11, 2, 0, 787129, 26327, 821, 262144⟩
    (by decide) selected_cut_30938

theorem unmarked_context_10_6581_787130 : frontier 11 ⟨787130, by decide⟩
    (prefixCache 10 6581) (prefixPartial 10 6581) = false := by
  decide +kernel

theorem node_context_10_6581_787130 : EJMOriginalGlobalDAGData.nodes 11 ⟨787130, by decide⟩ =
    .split (coordinate 10) (![⟨786799, by decide⟩,⟨786937, by decide⟩,⟨787040, by decide⟩,⟨787129, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6581_787130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6581 ⟨787130, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6581
    ⟨787130, by decide⟩ (by decide) (![⟨786799, by decide⟩,⟨786937, by decide⟩,⟨787040, by decide⟩,⟨787129, by decide⟩]) unmarked_context_10_6581_787130 node_context_10_6581_787130
  intro a
  fin_cases a
  · exact context_11_26324_786799
  · exact context_11_26325_786937
  · exact context_11_26326_787040
  · exact context_11_26327_787129

theorem selected_cut_30939 : selected 9 ⟨787172, by decide⟩
    (prefixPartial 12 105312) = some ⟨12, 2, 0, 787172, 105312, 1969, 65536⟩ := by
  decide +kernel

theorem context_12_105312_787172 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105312 ⟨787172, by decide⟩ :=
  accepted_of_selected 12 105312 ⟨787172, by decide⟩ ⟨12, 2, 0, 787172, 105312, 1969, 65536⟩
    (by decide) selected_cut_30939

theorem selected_cut_30940 : selected 9 ⟨787212, by decide⟩
    (prefixPartial 12 105313) = some ⟨12, 2, 0, 787212, 105313, 2065, 65536⟩ := by
  decide +kernel

theorem context_12_105313_787212 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105313 ⟨787212, by decide⟩ :=
  accepted_of_selected 12 105313 ⟨787212, by decide⟩ ⟨12, 2, 0, 787212, 105313, 2065, 65536⟩
    (by decide) selected_cut_30940

theorem selected_cut_30941 : selected 9 ⟨787250, by decide⟩
    (prefixPartial 12 105314) = some ⟨12, 2, 0, 787250, 105314, 2093, 65536⟩ := by
  decide +kernel

theorem context_12_105314_787250 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105314 ⟨787250, by decide⟩ :=
  accepted_of_selected 12 105314 ⟨787250, by decide⟩ ⟨12, 2, 0, 787250, 105314, 2093, 65536⟩
    (by decide) selected_cut_30941

theorem selected_cut_30942 : selected 9 ⟨787280, by decide⟩
    (prefixPartial 12 105315) = some ⟨12, 2, 0, 787280, 105315, 1985, 65536⟩ := by
  decide +kernel

theorem context_12_105315_787280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105315 ⟨787280, by decide⟩ :=
  accepted_of_selected 12 105315 ⟨787280, by decide⟩ ⟨12, 2, 0, 787280, 105315, 1985, 65536⟩
    (by decide) selected_cut_30942

theorem unmarked_context_11_26328_787281 : frontier 10 ⟨787281, by decide⟩
    (prefixCache 11 26328) (prefixPartial 11 26328) = false := by
  decide +kernel

theorem node_context_11_26328_787281 : EJMOriginalGlobalDAGData.nodes 10 ⟨787281, by decide⟩ =
    .split (coordinate 11) (![⟨787172, by decide⟩,⟨787212, by decide⟩,⟨787250, by decide⟩,⟨787280, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26328_787281 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26328 ⟨787281, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26328
    ⟨787281, by decide⟩ (by decide) (![⟨787172, by decide⟩,⟨787212, by decide⟩,⟨787250, by decide⟩,⟨787280, by decide⟩]) unmarked_context_11_26328_787281 node_context_11_26328_787281
  intro a
  fin_cases a
  · exact context_12_105312_787172
  · exact context_12_105313_787212
  · exact context_12_105314_787250
  · exact context_12_105315_787280

theorem selected_cut_30943 : selected 9 ⟨787324, by decide⟩
    (prefixPartial 12 105316) = some ⟨12, 2, 0, 787324, 105316, 2157, 65536⟩ := by
  decide +kernel

theorem context_12_105316_787324 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105316 ⟨787324, by decide⟩ :=
  accepted_of_selected 12 105316 ⟨787324, by decide⟩ ⟨12, 2, 0, 787324, 105316, 2157, 65536⟩
    (by decide) selected_cut_30943

theorem selected_cut_30944 : selected 9 ⟨787361, by decide⟩
    (prefixPartial 12 105317) = some ⟨12, 2, 0, 787361, 105317, 1869, 65536⟩ := by
  decide +kernel

theorem context_12_105317_787361 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105317 ⟨787361, by decide⟩ :=
  accepted_of_selected 12 105317 ⟨787361, by decide⟩ ⟨12, 2, 0, 787361, 105317, 1869, 65536⟩
    (by decide) selected_cut_30944

theorem selected_cut_30945 : selected 9 ⟨787407, by decide⟩
    (prefixPartial 12 105318) = some ⟨12, 2, 0, 787407, 105318, 2081, 65536⟩ := by
  decide +kernel

theorem context_12_105318_787407 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105318 ⟨787407, by decide⟩ :=
  accepted_of_selected 12 105318 ⟨787407, by decide⟩ ⟨12, 2, 0, 787407, 105318, 2081, 65536⟩
    (by decide) selected_cut_30945

theorem selected_cut_30946 : selected 9 ⟨787442, by decide⟩
    (prefixPartial 12 105319) = some ⟨12, 2, 0, 787442, 105319, 1925, 65536⟩ := by
  decide +kernel

theorem context_12_105319_787442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105319 ⟨787442, by decide⟩ :=
  accepted_of_selected 12 105319 ⟨787442, by decide⟩ ⟨12, 2, 0, 787442, 105319, 1925, 65536⟩
    (by decide) selected_cut_30946

theorem unmarked_context_11_26329_787443 : frontier 10 ⟨787443, by decide⟩
    (prefixCache 11 26329) (prefixPartial 11 26329) = false := by
  decide +kernel

theorem node_context_11_26329_787443 : EJMOriginalGlobalDAGData.nodes 10 ⟨787443, by decide⟩ =
    .split (coordinate 11) (![⟨787324, by decide⟩,⟨787361, by decide⟩,⟨787407, by decide⟩,⟨787442, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26329_787443 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26329 ⟨787443, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26329
    ⟨787443, by decide⟩ (by decide) (![⟨787324, by decide⟩,⟨787361, by decide⟩,⟨787407, by decide⟩,⟨787442, by decide⟩]) unmarked_context_11_26329_787443 node_context_11_26329_787443
  intro a
  fin_cases a
  · exact context_12_105316_787324
  · exact context_12_105317_787361
  · exact context_12_105318_787407
  · exact context_12_105319_787442

theorem selected_cut_30947 : selected 9 ⟨787553, by decide⟩
    (prefixPartial 12 105320) = some ⟨12, 2, 0, 787553, 105320, 2997, 65536⟩ := by
  decide +kernel

theorem context_12_105320_787553 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105320 ⟨787553, by decide⟩ :=
  accepted_of_selected 12 105320 ⟨787553, by decide⟩ ⟨12, 2, 0, 787553, 105320, 2997, 65536⟩
    (by decide) selected_cut_30947

theorem selected_cut_30948 : selected 9 ⟨787626, by decide⟩
    (prefixPartial 12 105321) = some ⟨12, 2, 0, 787626, 105321, 2733, 65536⟩ := by
  decide +kernel

theorem context_12_105321_787626 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105321 ⟨787626, by decide⟩ :=
  accepted_of_selected 12 105321 ⟨787626, by decide⟩ ⟨12, 2, 0, 787626, 105321, 2733, 65536⟩
    (by decide) selected_cut_30948

theorem selected_cut_30949 : selected 9 ⟨769104, by decide⟩
    (prefixPartial 12 105322) = some ⟨12, 1, 0, 769104, 105322, 1, 65536⟩ := by
  decide +kernel

theorem context_12_105322_769104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105322 ⟨769104, by decide⟩ :=
  accepted_of_selected 12 105322 ⟨769104, by decide⟩ ⟨12, 1, 0, 769104, 105322, 1, 65536⟩
    (by decide) selected_cut_30949

theorem selected_cut_30950 : selected 9 ⟨661672, by decide⟩
    (prefixPartial 12 105323) = some ⟨12, 1, 0, 661672, 105323, 1, 65536⟩ := by
  decide +kernel

theorem context_12_105323_661672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105323 ⟨661672, by decide⟩ :=
  accepted_of_selected 12 105323 ⟨661672, by decide⟩ ⟨12, 1, 0, 661672, 105323, 1, 65536⟩
    (by decide) selected_cut_30950

theorem unmarked_context_11_26330_787627 : frontier 10 ⟨787627, by decide⟩
    (prefixCache 11 26330) (prefixPartial 11 26330) = false := by
  decide +kernel

theorem node_context_11_26330_787627 : EJMOriginalGlobalDAGData.nodes 10 ⟨787627, by decide⟩ =
    .split (coordinate 11) (![⟨787553, by decide⟩,⟨787626, by decide⟩,⟨769104, by decide⟩,⟨661672, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26330_787627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26330 ⟨787627, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26330
    ⟨787627, by decide⟩ (by decide) (![⟨787553, by decide⟩,⟨787626, by decide⟩,⟨769104, by decide⟩,⟨661672, by decide⟩]) unmarked_context_11_26330_787627 node_context_11_26330_787627
  intro a
  fin_cases a
  · exact context_12_105320_787553
  · exact context_12_105321_787626
  · exact context_12_105322_769104
  · exact context_12_105323_661672

theorem selected_cut_30951 : selected 9 ⟨787661, by decide⟩
    (prefixPartial 12 105324) = some ⟨12, 2, 0, 787661, 105324, 1645, 65536⟩ := by
  decide +kernel

theorem context_12_105324_787661 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105324 ⟨787661, by decide⟩ :=
  accepted_of_selected 12 105324 ⟨787661, by decide⟩ ⟨12, 2, 0, 787661, 105324, 1645, 65536⟩
    (by decide) selected_cut_30951

theorem selected_cut_30952 : selected 9 ⟨787691, by decide⟩
    (prefixPartial 12 105325) = some ⟨12, 2, 0, 787691, 105325, 1541, 65536⟩ := by
  decide +kernel

theorem context_12_105325_787691 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105325 ⟨787691, by decide⟩ :=
  accepted_of_selected 12 105325 ⟨787691, by decide⟩ ⟨12, 2, 0, 787691, 105325, 1541, 65536⟩
    (by decide) selected_cut_30952

theorem selected_cut_30953 : selected 9 ⟨787715, by decide⟩
    (prefixPartial 12 105326) = some ⟨12, 2, 0, 787715, 105326, 1493, 65536⟩ := by
  decide +kernel

theorem context_12_105326_787715 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105326 ⟨787715, by decide⟩ :=
  accepted_of_selected 12 105326 ⟨787715, by decide⟩ ⟨12, 2, 0, 787715, 105326, 1493, 65536⟩
    (by decide) selected_cut_30953

theorem selected_cut_30954 : selected 9 ⟨758968, by decide⟩
    (prefixPartial 12 105327) = some ⟨12, 1, 0, 758968, 105327, 1, 65536⟩ := by
  decide +kernel

theorem context_12_105327_758968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105327 ⟨758968, by decide⟩ :=
  accepted_of_selected 12 105327 ⟨758968, by decide⟩ ⟨12, 1, 0, 758968, 105327, 1, 65536⟩
    (by decide) selected_cut_30954

theorem unmarked_context_11_26331_787716 : frontier 10 ⟨787716, by decide⟩
    (prefixCache 11 26331) (prefixPartial 11 26331) = false := by
  decide +kernel

theorem node_context_11_26331_787716 : EJMOriginalGlobalDAGData.nodes 10 ⟨787716, by decide⟩ =
    .split (coordinate 11) (![⟨787661, by decide⟩,⟨787691, by decide⟩,⟨787715, by decide⟩,⟨758968, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26331_787716 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26331 ⟨787716, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26331
    ⟨787716, by decide⟩ (by decide) (![⟨787661, by decide⟩,⟨787691, by decide⟩,⟨787715, by decide⟩,⟨758968, by decide⟩]) unmarked_context_11_26331_787716 node_context_11_26331_787716
  intro a
  fin_cases a
  · exact context_12_105324_787661
  · exact context_12_105325_787691
  · exact context_12_105326_787715
  · exact context_12_105327_758968

theorem unmarked_context_10_6582_787717 : frontier 11 ⟨787717, by decide⟩
    (prefixCache 10 6582) (prefixPartial 10 6582) = false := by
  decide +kernel

theorem node_context_10_6582_787717 : EJMOriginalGlobalDAGData.nodes 11 ⟨787717, by decide⟩ =
    .split (coordinate 10) (![⟨787281, by decide⟩,⟨787443, by decide⟩,⟨787627, by decide⟩,⟨787716, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6582_787717 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6582 ⟨787717, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6582
    ⟨787717, by decide⟩ (by decide) (![⟨787281, by decide⟩,⟨787443, by decide⟩,⟨787627, by decide⟩,⟨787716, by decide⟩]) unmarked_context_10_6582_787717 node_context_10_6582_787717
  intro a
  fin_cases a
  · exact context_11_26328_787281
  · exact context_11_26329_787443
  · exact context_11_26330_787627
  · exact context_11_26331_787716

theorem selected_cut_30955 : selected 9 ⟨787742, by decide⟩
    (prefixPartial 12 105328) = some ⟨12, 2, 0, 787742, 105328, 1577, 65536⟩ := by
  decide +kernel

theorem context_12_105328_787742 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105328 ⟨787742, by decide⟩ :=
  accepted_of_selected 12 105328 ⟨787742, by decide⟩ ⟨12, 2, 0, 787742, 105328, 1577, 65536⟩
    (by decide) selected_cut_30955

theorem selected_cut_30956 : selected 9 ⟨787776, by decide⟩
    (prefixPartial 12 105329) = some ⟨12, 2, 0, 787776, 105329, 1685, 65536⟩ := by
  decide +kernel

theorem context_12_105329_787776 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105329 ⟨787776, by decide⟩ :=
  accepted_of_selected 12 105329 ⟨787776, by decide⟩ ⟨12, 2, 0, 787776, 105329, 1685, 65536⟩
    (by decide) selected_cut_30956

theorem selected_cut_30957 : selected 9 ⟨787810, by decide⟩
    (prefixPartial 12 105330) = some ⟨12, 2, 0, 787810, 105330, 1693, 65536⟩ := by
  decide +kernel

theorem context_12_105330_787810 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105330 ⟨787810, by decide⟩ :=
  accepted_of_selected 12 105330 ⟨787810, by decide⟩ ⟨12, 2, 0, 787810, 105330, 1693, 65536⟩
    (by decide) selected_cut_30957

theorem selected_cut_30958 : selected 9 ⟨787840, by decide⟩
    (prefixPartial 12 105331) = some ⟨12, 2, 0, 787840, 105331, 1513, 65536⟩ := by
  decide +kernel

theorem context_12_105331_787840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105331 ⟨787840, by decide⟩ :=
  accepted_of_selected 12 105331 ⟨787840, by decide⟩ ⟨12, 2, 0, 787840, 105331, 1513, 65536⟩
    (by decide) selected_cut_30958

theorem unmarked_context_11_26332_787841 : frontier 10 ⟨787841, by decide⟩
    (prefixCache 11 26332) (prefixPartial 11 26332) = false := by
  decide +kernel

theorem node_context_11_26332_787841 : EJMOriginalGlobalDAGData.nodes 10 ⟨787841, by decide⟩ =
    .split (coordinate 11) (![⟨787742, by decide⟩,⟨787776, by decide⟩,⟨787810, by decide⟩,⟨787840, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26332_787841 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26332 ⟨787841, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26332
    ⟨787841, by decide⟩ (by decide) (![⟨787742, by decide⟩,⟨787776, by decide⟩,⟨787810, by decide⟩,⟨787840, by decide⟩]) unmarked_context_11_26332_787841 node_context_11_26332_787841
  intro a
  fin_cases a
  · exact context_12_105328_787742
  · exact context_12_105329_787776
  · exact context_12_105330_787810
  · exact context_12_105331_787840

theorem selected_cut_30959 : selected 9 ⟨787875, by decide⟩
    (prefixPartial 12 105332) = some ⟨12, 2, 0, 787875, 105332, 1469, 65536⟩ := by
  decide +kernel

theorem context_12_105332_787875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105332 ⟨787875, by decide⟩ :=
  accepted_of_selected 12 105332 ⟨787875, by decide⟩ ⟨12, 2, 0, 787875, 105332, 1469, 65536⟩
    (by decide) selected_cut_30959

theorem selected_cut_30960 : selected 9 ⟨787898, by decide⟩
    (prefixPartial 12 105333) = some ⟨12, 2, 0, 787898, 105333, 1401, 65536⟩ := by
  decide +kernel

theorem context_12_105333_787898 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105333 ⟨787898, by decide⟩ :=
  accepted_of_selected 12 105333 ⟨787898, by decide⟩ ⟨12, 2, 0, 787898, 105333, 1401, 65536⟩
    (by decide) selected_cut_30960

theorem selected_cut_30961 : selected 9 ⟨787930, by decide⟩
    (prefixPartial 12 105334) = some ⟨12, 2, 0, 787930, 105334, 1461, 65536⟩ := by
  decide +kernel

theorem context_12_105334_787930 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105334 ⟨787930, by decide⟩ :=
  accepted_of_selected 12 105334 ⟨787930, by decide⟩ ⟨12, 2, 0, 787930, 105334, 1461, 65536⟩
    (by decide) selected_cut_30961

theorem selected_cut_30962 : selected 9 ⟨787952, by decide⟩
    (prefixPartial 12 105335) = some ⟨12, 2, 0, 787952, 105335, 1365, 65536⟩ := by
  decide +kernel

theorem context_12_105335_787952 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105335 ⟨787952, by decide⟩ :=
  accepted_of_selected 12 105335 ⟨787952, by decide⟩ ⟨12, 2, 0, 787952, 105335, 1365, 65536⟩
    (by decide) selected_cut_30962

theorem unmarked_context_11_26333_787953 : frontier 10 ⟨787953, by decide⟩
    (prefixCache 11 26333) (prefixPartial 11 26333) = false := by
  decide +kernel

theorem node_context_11_26333_787953 : EJMOriginalGlobalDAGData.nodes 10 ⟨787953, by decide⟩ =
    .split (coordinate 11) (![⟨787875, by decide⟩,⟨787898, by decide⟩,⟨787930, by decide⟩,⟨787952, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26333_787953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26333 ⟨787953, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26333
    ⟨787953, by decide⟩ (by decide) (![⟨787875, by decide⟩,⟨787898, by decide⟩,⟨787930, by decide⟩,⟨787952, by decide⟩]) unmarked_context_11_26333_787953 node_context_11_26333_787953
  intro a
  fin_cases a
  · exact context_12_105332_787875
  · exact context_12_105333_787898
  · exact context_12_105334_787930
  · exact context_12_105335_787952

theorem selected_cut_30963 : selected 9 ⟨787978, by decide⟩
    (prefixPartial 12 105336) = some ⟨12, 2, 0, 787978, 105336, 1353, 65536⟩ := by
  decide +kernel

theorem context_12_105336_787978 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105336 ⟨787978, by decide⟩ :=
  accepted_of_selected 12 105336 ⟨787978, by decide⟩ ⟨12, 2, 0, 787978, 105336, 1353, 65536⟩
    (by decide) selected_cut_30963

theorem selected_cut_30964 : selected 9 ⟨788006, by decide⟩
    (prefixPartial 12 105337) = some ⟨12, 2, 0, 788006, 105337, 1349, 65536⟩ := by
  decide +kernel

theorem context_12_105337_788006 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105337 ⟨788006, by decide⟩ :=
  accepted_of_selected 12 105337 ⟨788006, by decide⟩ ⟨12, 2, 0, 788006, 105337, 1349, 65536⟩
    (by decide) selected_cut_30964

theorem selected_cut_30965 : selected 9 ⟨788036, by decide⟩
    (prefixPartial 12 105338) = some ⟨12, 2, 0, 788036, 105338, 1317, 65536⟩ := by
  decide +kernel

theorem context_12_105338_788036 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105338 ⟨788036, by decide⟩ :=
  accepted_of_selected 12 105338 ⟨788036, by decide⟩ ⟨12, 2, 0, 788036, 105338, 1317, 65536⟩
    (by decide) selected_cut_30965

theorem selected_cut_30966 : selected 9 ⟨788062, by decide⟩
    (prefixPartial 12 105339) = some ⟨12, 2, 0, 788062, 105339, 1193, 65536⟩ := by
  decide +kernel

theorem context_12_105339_788062 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105339 ⟨788062, by decide⟩ :=
  accepted_of_selected 12 105339 ⟨788062, by decide⟩ ⟨12, 2, 0, 788062, 105339, 1193, 65536⟩
    (by decide) selected_cut_30966

theorem unmarked_context_11_26334_788063 : frontier 10 ⟨788063, by decide⟩
    (prefixCache 11 26334) (prefixPartial 11 26334) = false := by
  decide +kernel

theorem node_context_11_26334_788063 : EJMOriginalGlobalDAGData.nodes 10 ⟨788063, by decide⟩ =
    .split (coordinate 11) (![⟨787978, by decide⟩,⟨788006, by decide⟩,⟨788036, by decide⟩,⟨788062, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26334_788063 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26334 ⟨788063, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26334
    ⟨788063, by decide⟩ (by decide) (![⟨787978, by decide⟩,⟨788006, by decide⟩,⟨788036, by decide⟩,⟨788062, by decide⟩]) unmarked_context_11_26334_788063 node_context_11_26334_788063
  intro a
  fin_cases a
  · exact context_12_105336_787978
  · exact context_12_105337_788006
  · exact context_12_105338_788036
  · exact context_12_105339_788062

theorem selected_cut_30967 : selected 10 ⟨788124, by decide⟩
    (prefixPartial 11 26335) = some ⟨11, 2, 0, 788124, 26335, 2913, 262144⟩ := by
  decide +kernel

theorem context_11_26335_788124 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26335 ⟨788124, by decide⟩ :=
  accepted_of_selected 11 26335 ⟨788124, by decide⟩ ⟨11, 2, 0, 788124, 26335, 2913, 262144⟩
    (by decide) selected_cut_30967

theorem unmarked_context_10_6583_788125 : frontier 11 ⟨788125, by decide⟩
    (prefixCache 10 6583) (prefixPartial 10 6583) = false := by
  decide +kernel

theorem node_context_10_6583_788125 : EJMOriginalGlobalDAGData.nodes 11 ⟨788125, by decide⟩ =
    .split (coordinate 10) (![⟨787841, by decide⟩,⟨787953, by decide⟩,⟨788063, by decide⟩,⟨788124, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6583_788125 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6583 ⟨788125, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6583
    ⟨788125, by decide⟩ (by decide) (![⟨787841, by decide⟩,⟨787953, by decide⟩,⟨788063, by decide⟩,⟨788124, by decide⟩]) unmarked_context_10_6583_788125 node_context_10_6583_788125
  intro a
  fin_cases a
  · exact context_11_26332_787841
  · exact context_11_26333_787953
  · exact context_11_26334_788063
  · exact context_11_26335_788124

theorem unmarked_context_9_1645_788126 : frontier 12 ⟨788126, by decide⟩
    (prefixCache 9 1645) (prefixPartial 9 1645) = false := by
  decide +kernel

theorem node_context_9_1645_788126 : EJMOriginalGlobalDAGData.nodes 12 ⟨788126, by decide⟩ =
    .split (coordinate 9) (![⟨3442, by decide⟩,⟨787130, by decide⟩,⟨787717, by decide⟩,⟨788125, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1645_788126 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1645 ⟨788126, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1645
    ⟨788126, by decide⟩ (by decide) (![⟨3442, by decide⟩,⟨787130, by decide⟩,⟨787717, by decide⟩,⟨788125, by decide⟩]) unmarked_context_9_1645_788126 node_context_9_1645_788126
  intro a
  fin_cases a
  · exact context_10_6580_3442
  · exact context_10_6581_787130
  · exact context_10_6582_787717
  · exact context_10_6583_788125

theorem selected_cut_30968 : selected 11 ⟨3442, by decide⟩
    (prefixPartial 10 6584) = some ⟨10, 1, 0, 3442, 6584, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_6584_3442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6584 ⟨3442, by decide⟩ :=
  accepted_of_selected 10 6584 ⟨3442, by decide⟩ ⟨10, 1, 0, 3442, 6584, 1, 1048576⟩
    (by decide) selected_cut_30968

theorem selected_cut_30969 : selected 11 ⟨3442, by decide⟩
    (prefixPartial 10 6585) = some ⟨10, 1, 0, 3442, 6585, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_6585_3442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6585 ⟨3442, by decide⟩ :=
  accepted_of_selected 10 6585 ⟨3442, by decide⟩ ⟨10, 1, 0, 3442, 6585, 1, 1048576⟩
    (by decide) selected_cut_30969

theorem selected_cut_30970 : selected 11 ⟨788189, by decide⟩
    (prefixPartial 10 6586) = some ⟨10, 2, 0, 788189, 6586, 2761, 1048576⟩ := by
  decide +kernel

theorem context_10_6586_788189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6586 ⟨788189, by decide⟩ :=
  accepted_of_selected 10 6586 ⟨788189, by decide⟩ ⟨10, 2, 0, 788189, 6586, 2761, 1048576⟩
    (by decide) selected_cut_30970

theorem selected_cut_30971 : selected 10 ⟨788247, by decide⟩
    (prefixPartial 11 26348) = some ⟨11, 2, 0, 788247, 26348, 2613, 262144⟩ := by
  decide +kernel

theorem context_11_26348_788247 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26348 ⟨788247, by decide⟩ :=
  accepted_of_selected 11 26348 ⟨788247, by decide⟩ ⟨11, 2, 0, 788247, 26348, 2613, 262144⟩
    (by decide) selected_cut_30971

theorem selected_cut_30972 : selected 10 ⟨788313, by decide⟩
    (prefixPartial 11 26349) = some ⟨11, 2, 0, 788313, 26349, 2089, 262144⟩ := by
  decide +kernel

theorem context_11_26349_788313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26349 ⟨788313, by decide⟩ :=
  accepted_of_selected 11 26349 ⟨788313, by decide⟩ ⟨11, 2, 0, 788313, 26349, 2089, 262144⟩
    (by decide) selected_cut_30972

theorem selected_cut_30973 : selected 10 ⟨788346, by decide⟩
    (prefixPartial 11 26350) = some ⟨11, 2, 0, 788346, 26350, 1041, 262144⟩ := by
  decide +kernel

theorem context_11_26350_788346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26350 ⟨788346, by decide⟩ :=
  accepted_of_selected 11 26350 ⟨788346, by decide⟩ ⟨11, 2, 0, 788346, 26350, 1041, 262144⟩
    (by decide) selected_cut_30973

theorem selected_cut_30974 : selected 10 ⟨788363, by decide⟩
    (prefixPartial 11 26351) = some ⟨11, 2, 0, 788363, 26351, 553, 262144⟩ := by
  decide +kernel

theorem context_11_26351_788363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26351 ⟨788363, by decide⟩ :=
  accepted_of_selected 11 26351 ⟨788363, by decide⟩ ⟨11, 2, 0, 788363, 26351, 553, 262144⟩
    (by decide) selected_cut_30974

theorem unmarked_context_10_6587_788364 : frontier 11 ⟨788364, by decide⟩
    (prefixCache 10 6587) (prefixPartial 10 6587) = false := by
  decide +kernel

theorem node_context_10_6587_788364 : EJMOriginalGlobalDAGData.nodes 11 ⟨788364, by decide⟩ =
    .split (coordinate 10) (![⟨788247, by decide⟩,⟨788313, by decide⟩,⟨788346, by decide⟩,⟨788363, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6587_788364 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6587 ⟨788364, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6587
    ⟨788364, by decide⟩ (by decide) (![⟨788247, by decide⟩,⟨788313, by decide⟩,⟨788346, by decide⟩,⟨788363, by decide⟩]) unmarked_context_10_6587_788364 node_context_10_6587_788364
  intro a
  fin_cases a
  · exact context_11_26348_788247
  · exact context_11_26349_788313
  · exact context_11_26350_788346
  · exact context_11_26351_788363

theorem unmarked_context_9_1646_788365 : frontier 12 ⟨788365, by decide⟩
    (prefixCache 9 1646) (prefixPartial 9 1646) = false := by
  decide +kernel

theorem node_context_9_1646_788365 : EJMOriginalGlobalDAGData.nodes 12 ⟨788365, by decide⟩ =
    .split (coordinate 9) (![⟨3442, by decide⟩,⟨3442, by decide⟩,⟨788189, by decide⟩,⟨788364, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1646_788365 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1646 ⟨788365, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1646
    ⟨788365, by decide⟩ (by decide) (![⟨3442, by decide⟩,⟨3442, by decide⟩,⟨788189, by decide⟩,⟨788364, by decide⟩]) unmarked_context_9_1646_788365 node_context_9_1646_788365
  intro a
  fin_cases a
  · exact context_10_6584_3442
  · exact context_10_6585_3442
  · exact context_10_6586_788189
  · exact context_10_6587_788364

theorem selected_cut_30975 : selected 12 ⟨788402, by decide⟩
    (prefixPartial 9 1647) = some ⟨9, 2, 0, 788402, 1647, 961, 4194304⟩ := by
  decide +kernel

theorem context_9_1647_788402 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1647 ⟨788402, by decide⟩ :=
  accepted_of_selected 9 1647 ⟨788402, by decide⟩ ⟨9, 2, 0, 788402, 1647, 961, 4194304⟩
    (by decide) selected_cut_30975

theorem unmarked_context_8_411_788403 : frontier 13 ⟨788403, by decide⟩
    (prefixCache 8 411) (prefixPartial 8 411) = false := by
  decide +kernel

theorem node_context_8_411_788403 : EJMOriginalGlobalDAGData.nodes 13 ⟨788403, by decide⟩ =
    .split (coordinate 8) (![⟨786601, by decide⟩,⟨788126, by decide⟩,⟨788365, by decide⟩,⟨788402, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_411_788403 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 411 ⟨788403, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 411
    ⟨788403, by decide⟩ (by decide) (![⟨786601, by decide⟩,⟨788126, by decide⟩,⟨788365, by decide⟩,⟨788402, by decide⟩]) unmarked_context_8_411_788403 node_context_8_411_788403
  intro a
  fin_cases a
  · exact context_9_1644_786601
  · exact context_9_1645_788126
  · exact context_9_1646_788365
  · exact context_9_1647_788402

theorem unmarked_context_7_102_788404 : frontier 14 ⟨788404, by decide⟩
    (prefixCache 7 102) (prefixPartial 7 102) = false := by
  decide +kernel

theorem node_context_7_102_788404 : EJMOriginalGlobalDAGData.nodes 14 ⟨788404, by decide⟩ =
    .split (coordinate 7) (![⟨770191, by decide⟩,⟨777085, by decide⟩,⟨782853, by decide⟩,⟨788403, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_102_788404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 102 ⟨788404, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 102
    ⟨788404, by decide⟩ (by decide) (![⟨770191, by decide⟩,⟨777085, by decide⟩,⟨782853, by decide⟩,⟨788403, by decide⟩]) unmarked_context_7_102_788404 node_context_7_102_788404
  intro a
  fin_cases a
  · exact context_8_408_770191
  · exact context_8_409_777085
  · exact context_8_410_782853
  · exact context_8_411_788403

theorem selected_cut_30976 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 26368) = some ⟨11, 1, 0, 434745, 26368, 1, 262144⟩ := by
  decide +kernel

theorem context_11_26368_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26368 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 26368 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 26368, 1, 262144⟩
    (by decide) selected_cut_30976

theorem selected_cut_30977 : selected 9 ⟨14169, by decide⟩
    (prefixPartial 12 105476) = some ⟨12, 1, 0, 14169, 105476, 1, 65536⟩ := by
  decide +kernel

theorem context_12_105476_14169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105476 ⟨14169, by decide⟩ :=
  accepted_of_selected 12 105476 ⟨14169, by decide⟩ ⟨12, 1, 0, 14169, 105476, 1, 65536⟩
    (by decide) selected_cut_30977

theorem selected_cut_30978 : selected 8 ⟨788577, by decide⟩
    (prefixPartial 13 421908) = some ⟨13, 2, 0, 788577, 421908, 2845, 16384⟩ := by
  decide +kernel

theorem context_13_421908_788577 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421908 ⟨788577, by decide⟩ :=
  accepted_of_selected 13 421908 ⟨788577, by decide⟩ ⟨13, 2, 0, 788577, 421908, 2845, 16384⟩
    (by decide) selected_cut_30978

theorem selected_cut_30979 : selected 8 ⟨788686, by decide⟩
    (prefixPartial 13 421909) = some ⟨13, 2, 0, 788686, 421909, 2065, 16384⟩ := by
  decide +kernel

theorem context_13_421909_788686 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421909 ⟨788686, by decide⟩ :=
  accepted_of_selected 13 421909 ⟨788686, by decide⟩ ⟨13, 2, 0, 788686, 421909, 2065, 16384⟩
    (by decide) selected_cut_30979

theorem selected_cut_30980 : selected 8 ⟨788725, by decide⟩
    (prefixPartial 13 421910) = some ⟨13, 2, 0, 788725, 421910, 581, 16384⟩ := by
  decide +kernel

theorem context_13_421910_788725 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421910 ⟨788725, by decide⟩ :=
  accepted_of_selected 13 421910 ⟨788725, by decide⟩ ⟨13, 2, 0, 788725, 421910, 581, 16384⟩
    (by decide) selected_cut_30980

theorem selected_cut_30981 : selected 8 ⟨788730, by decide⟩
    (prefixPartial 13 421911) = some ⟨13, 2, 0, 788730, 421911, 145, 16384⟩ := by
  decide +kernel

theorem context_13_421911_788730 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421911 ⟨788730, by decide⟩ :=
  accepted_of_selected 13 421911 ⟨788730, by decide⟩ ⟨13, 2, 0, 788730, 421911, 145, 16384⟩
    (by decide) selected_cut_30981

theorem unmarked_context_12_105477_788731 : frontier 9 ⟨788731, by decide⟩
    (prefixCache 12 105477) (prefixPartial 12 105477) = false := by
  decide +kernel

theorem node_context_12_105477_788731 : EJMOriginalGlobalDAGData.nodes 9 ⟨788731, by decide⟩ =
    .split (coordinate 12) (![⟨788577, by decide⟩,⟨788686, by decide⟩,⟨788725, by decide⟩,⟨788730, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105477_788731 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105477 ⟨788731, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105477
    ⟨788731, by decide⟩ (by decide) (![⟨788577, by decide⟩,⟨788686, by decide⟩,⟨788725, by decide⟩,⟨788730, by decide⟩]) unmarked_context_12_105477_788731 node_context_12_105477_788731
  intro a
  fin_cases a
  · exact context_13_421908_788577
  · exact context_13_421909_788686
  · exact context_13_421910_788725
  · exact context_13_421911_788730

theorem selected_cut_30982 : selected 9 ⟨763842, by decide⟩
    (prefixPartial 12 105478) = some ⟨12, 1, 0, 763842, 105478, 1, 65536⟩ := by
  decide +kernel

theorem context_12_105478_763842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105478 ⟨763842, by decide⟩ :=
  accepted_of_selected 12 105478 ⟨763842, by decide⟩ ⟨12, 1, 0, 763842, 105478, 1, 65536⟩
    (by decide) selected_cut_30982

theorem selected_cut_30983 : selected 8 ⟨788840, by decide⟩
    (prefixPartial 13 421916) = some ⟨13, 2, 0, 788840, 421916, 3485, 16384⟩ := by
  decide +kernel

theorem context_13_421916_788840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421916 ⟨788840, by decide⟩ :=
  accepted_of_selected 13 421916 ⟨788840, by decide⟩ ⟨13, 2, 0, 788840, 421916, 3485, 16384⟩
    (by decide) selected_cut_30983

theorem selected_cut_30984 : selected 8 ⟨788958, by decide⟩
    (prefixPartial 13 421917) = some ⟨13, 2, 0, 788958, 421917, 3893, 16384⟩ := by
  decide +kernel

theorem context_13_421917_788958 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421917 ⟨788958, by decide⟩ :=
  accepted_of_selected 13 421917 ⟨788958, by decide⟩ ⟨13, 2, 0, 788958, 421917, 3893, 16384⟩
    (by decide) selected_cut_30984

theorem selected_cut_30985 : selected 8 ⟨789071, by decide⟩
    (prefixPartial 13 421918) = some ⟨13, 2, 0, 789071, 421918, 2437, 16384⟩ := by
  decide +kernel

theorem context_13_421918_789071 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421918 ⟨789071, by decide⟩ :=
  accepted_of_selected 13 421918 ⟨789071, by decide⟩ ⟨13, 2, 0, 789071, 421918, 2437, 16384⟩
    (by decide) selected_cut_30985

theorem selected_cut_30986 : selected 8 ⟨789099, by decide⟩
    (prefixPartial 13 421919) = some ⟨13, 2, 0, 789099, 421919, 1229, 16384⟩ := by
  decide +kernel

theorem context_13_421919_789099 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421919 ⟨789099, by decide⟩ :=
  accepted_of_selected 13 421919 ⟨789099, by decide⟩ ⟨13, 2, 0, 789099, 421919, 1229, 16384⟩
    (by decide) selected_cut_30986

theorem unmarked_context_12_105479_789100 : frontier 9 ⟨789100, by decide⟩
    (prefixCache 12 105479) (prefixPartial 12 105479) = false := by
  decide +kernel

theorem node_context_12_105479_789100 : EJMOriginalGlobalDAGData.nodes 9 ⟨789100, by decide⟩ =
    .split (coordinate 12) (![⟨788840, by decide⟩,⟨788958, by decide⟩,⟨789071, by decide⟩,⟨789099, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105479_789100 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105479 ⟨789100, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105479
    ⟨789100, by decide⟩ (by decide) (![⟨788840, by decide⟩,⟨788958, by decide⟩,⟨789071, by decide⟩,⟨789099, by decide⟩]) unmarked_context_12_105479_789100 node_context_12_105479_789100
  intro a
  fin_cases a
  · exact context_13_421916_788840
  · exact context_13_421917_788958
  · exact context_13_421918_789071
  · exact context_13_421919_789099

theorem unmarked_context_11_26369_789101 : frontier 10 ⟨789101, by decide⟩
    (prefixCache 11 26369) (prefixPartial 11 26369) = false := by
  decide +kernel

theorem node_context_11_26369_789101 : EJMOriginalGlobalDAGData.nodes 10 ⟨789101, by decide⟩ =
    .split (coordinate 11) (![⟨14169, by decide⟩,⟨788731, by decide⟩,⟨763842, by decide⟩,⟨789100, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26369_789101 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26369 ⟨789101, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26369
    ⟨789101, by decide⟩ (by decide) (![⟨14169, by decide⟩,⟨788731, by decide⟩,⟨763842, by decide⟩,⟨789100, by decide⟩]) unmarked_context_11_26369_789101 node_context_11_26369_789101
  intro a
  fin_cases a
  · exact context_12_105476_14169
  · exact context_12_105477_788731
  · exact context_12_105478_763842
  · exact context_12_105479_789100

theorem selected_cut_30987 : selected 9 ⟨14169, by decide⟩
    (prefixPartial 12 105480) = some ⟨12, 1, 0, 14169, 105480, 1, 65536⟩ := by
  decide +kernel

theorem context_12_105480_14169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105480 ⟨14169, by decide⟩ :=
  accepted_of_selected 12 105480 ⟨14169, by decide⟩ ⟨12, 1, 0, 14169, 105480, 1, 65536⟩
    (by decide) selected_cut_30987

theorem selected_cut_30988 : selected 9 ⟨14169, by decide⟩
    (prefixPartial 12 105481) = some ⟨12, 1, 0, 14169, 105481, 1, 65536⟩ := by
  decide +kernel

theorem context_12_105481_14169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105481 ⟨14169, by decide⟩ :=
  accepted_of_selected 12 105481 ⟨14169, by decide⟩ ⟨12, 1, 0, 14169, 105481, 1, 65536⟩
    (by decide) selected_cut_30988

theorem selected_cut_30989 : selected 9 ⟨763842, by decide⟩
    (prefixPartial 12 105482) = some ⟨12, 1, 0, 763842, 105482, 1, 65536⟩ := by
  decide +kernel

theorem context_12_105482_763842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105482 ⟨763842, by decide⟩ :=
  accepted_of_selected 12 105482 ⟨763842, by decide⟩ ⟨12, 1, 0, 763842, 105482, 1, 65536⟩
    (by decide) selected_cut_30989

theorem selected_cut_30990 : selected 8 ⟨789201, by decide⟩
    (prefixPartial 13 421932) = some ⟨13, 2, 0, 789201, 421932, 3369, 16384⟩ := by
  decide +kernel

theorem context_13_421932_789201 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421932 ⟨789201, by decide⟩ :=
  accepted_of_selected 13 421932 ⟨789201, by decide⟩ ⟨13, 2, 0, 789201, 421932, 3369, 16384⟩
    (by decide) selected_cut_30990

theorem selected_cut_30991 : selected 8 ⟨789290, by decide⟩
    (prefixPartial 13 421933) = some ⟨13, 2, 0, 789290, 421933, 2317, 16384⟩ := by
  decide +kernel

theorem context_13_421933_789290 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421933 ⟨789290, by decide⟩ :=
  accepted_of_selected 13 421933 ⟨789290, by decide⟩ ⟨13, 2, 0, 789290, 421933, 2317, 16384⟩
    (by decide) selected_cut_30991

theorem selected_cut_30992 : selected 8 ⟨789336, by decide⟩
    (prefixPartial 13 421934) = some ⟨13, 2, 0, 789336, 421934, 661, 16384⟩ := by
  decide +kernel

theorem context_13_421934_789336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421934 ⟨789336, by decide⟩ :=
  accepted_of_selected 13 421934 ⟨789336, by decide⟩ ⟨13, 2, 0, 789336, 421934, 661, 16384⟩
    (by decide) selected_cut_30992

theorem selected_cut_30993 : selected 8 ⟨789338, by decide⟩
    (prefixPartial 13 421935) = some ⟨13, 2, 0, 789338, 421935, 137, 16384⟩ := by
  decide +kernel

theorem context_13_421935_789338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421935 ⟨789338, by decide⟩ :=
  accepted_of_selected 13 421935 ⟨789338, by decide⟩ ⟨13, 2, 0, 789338, 421935, 137, 16384⟩
    (by decide) selected_cut_30993

theorem unmarked_context_12_105483_789339 : frontier 9 ⟨789339, by decide⟩
    (prefixCache 12 105483) (prefixPartial 12 105483) = false := by
  decide +kernel

theorem node_context_12_105483_789339 : EJMOriginalGlobalDAGData.nodes 9 ⟨789339, by decide⟩ =
    .split (coordinate 12) (![⟨789201, by decide⟩,⟨789290, by decide⟩,⟨789336, by decide⟩,⟨789338, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105483_789339 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105483 ⟨789339, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105483
    ⟨789339, by decide⟩ (by decide) (![⟨789201, by decide⟩,⟨789290, by decide⟩,⟨789336, by decide⟩,⟨789338, by decide⟩]) unmarked_context_12_105483_789339 node_context_12_105483_789339
  intro a
  fin_cases a
  · exact context_13_421932_789201
  · exact context_13_421933_789290
  · exact context_13_421934_789336
  · exact context_13_421935_789338

theorem unmarked_context_11_26370_789340 : frontier 10 ⟨789340, by decide⟩
    (prefixCache 11 26370) (prefixPartial 11 26370) = false := by
  decide +kernel

theorem node_context_11_26370_789340 : EJMOriginalGlobalDAGData.nodes 10 ⟨789340, by decide⟩ =
    .split (coordinate 11) (![⟨14169, by decide⟩,⟨14169, by decide⟩,⟨763842, by decide⟩,⟨789339, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26370_789340 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26370 ⟨789340, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26370
    ⟨789340, by decide⟩ (by decide) (![⟨14169, by decide⟩,⟨14169, by decide⟩,⟨763842, by decide⟩,⟨789339, by decide⟩]) unmarked_context_11_26370_789340 node_context_11_26370_789340
  intro a
  fin_cases a
  · exact context_12_105480_14169
  · exact context_12_105481_14169
  · exact context_12_105482_763842
  · exact context_12_105483_789339

theorem selected_cut_30994 : selected 10 ⟨789341, by decide⟩
    (prefixPartial 11 26371) = some ⟨11, 1, 0, 789341, 26371, 1, 262144⟩ := by
  decide +kernel

theorem context_11_26371_789341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26371 ⟨789341, by decide⟩ :=
  accepted_of_selected 11 26371 ⟨789341, by decide⟩ ⟨11, 1, 0, 789341, 26371, 1, 262144⟩
    (by decide) selected_cut_30994

theorem unmarked_context_10_6592_789342 : frontier 11 ⟨789342, by decide⟩
    (prefixCache 10 6592) (prefixPartial 10 6592) = false := by
  decide +kernel

theorem node_context_10_6592_789342 : EJMOriginalGlobalDAGData.nodes 11 ⟨789342, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨789101, by decide⟩,⟨789340, by decide⟩,⟨789341, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6592_789342 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6592 ⟨789342, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6592
    ⟨789342, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨789101, by decide⟩,⟨789340, by decide⟩,⟨789341, by decide⟩]) unmarked_context_10_6592_789342 node_context_10_6592_789342
  intro a
  fin_cases a
  · exact context_11_26368_434745
  · exact context_11_26369_789101
  · exact context_11_26370_789340
  · exact context_11_26371_789341

theorem selected_cut_30995 : selected 9 ⟨789343, by decide⟩
    (prefixPartial 12 105488) = some ⟨12, 1, 0, 789343, 105488, 1, 65536⟩ := by
  decide +kernel

theorem context_12_105488_789343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105488 ⟨789343, by decide⟩ :=
  accepted_of_selected 12 105488 ⟨789343, by decide⟩ ⟨12, 1, 0, 789343, 105488, 1, 65536⟩
    (by decide) selected_cut_30995

theorem selected_cut_30996 : selected 8 ⟨789393, by decide⟩
    (prefixPartial 13 421956) = some ⟨13, 2, 0, 789393, 421956, 1917, 16384⟩ := by
  decide +kernel

theorem context_13_421956_789393 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421956 ⟨789393, by decide⟩ :=
  accepted_of_selected 13 421956 ⟨789393, by decide⟩ ⟨13, 2, 0, 789393, 421956, 1917, 16384⟩
    (by decide) selected_cut_30996

theorem selected_cut_30997 : selected 8 ⟨789446, by decide⟩
    (prefixPartial 13 421957) = some ⟨13, 2, 0, 789446, 421957, 2193, 16384⟩ := by
  decide +kernel

theorem context_13_421957_789446 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421957 ⟨789446, by decide⟩ :=
  accepted_of_selected 13 421957 ⟨789446, by decide⟩ ⟨13, 2, 0, 789446, 421957, 2193, 16384⟩
    (by decide) selected_cut_30997

theorem selected_cut_30998 : selected 8 ⟨789475, by decide⟩
    (prefixPartial 13 421958) = some ⟨13, 2, 0, 789475, 421958, 1397, 16384⟩ := by
  decide +kernel

theorem context_13_421958_789475 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421958 ⟨789475, by decide⟩ :=
  accepted_of_selected 13 421958 ⟨789475, by decide⟩ ⟨13, 2, 0, 789475, 421958, 1397, 16384⟩
    (by decide) selected_cut_30998

theorem selected_cut_30999 : selected 8 ⟨789482, by decide⟩
    (prefixPartial 13 421959) = some ⟨13, 2, 0, 789482, 421959, 909, 16384⟩ := by
  decide +kernel

theorem context_13_421959_789482 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421959 ⟨789482, by decide⟩ :=
  accepted_of_selected 13 421959 ⟨789482, by decide⟩ ⟨13, 2, 0, 789482, 421959, 909, 16384⟩
    (by decide) selected_cut_30999

theorem unmarked_context_12_105489_789483 : frontier 9 ⟨789483, by decide⟩
    (prefixCache 12 105489) (prefixPartial 12 105489) = false := by
  decide +kernel

theorem node_context_12_105489_789483 : EJMOriginalGlobalDAGData.nodes 9 ⟨789483, by decide⟩ =
    .split (coordinate 12) (![⟨789393, by decide⟩,⟨789446, by decide⟩,⟨789475, by decide⟩,⟨789482, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105489_789483 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105489 ⟨789483, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105489
    ⟨789483, by decide⟩ (by decide) (![⟨789393, by decide⟩,⟨789446, by decide⟩,⟨789475, by decide⟩,⟨789482, by decide⟩]) unmarked_context_12_105489_789483 node_context_12_105489_789483
  intro a
  fin_cases a
  · exact context_13_421956_789393
  · exact context_13_421957_789446
  · exact context_13_421958_789475
  · exact context_13_421959_789482

theorem selected_cut_31000 : selected 8 ⟨789519, by decide⟩
    (prefixPartial 13 421960) = some ⟨13, 2, 0, 789519, 421960, 1653, 16384⟩ := by
  decide +kernel

theorem context_13_421960_789519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421960 ⟨789519, by decide⟩ :=
  accepted_of_selected 13 421960 ⟨789519, by decide⟩ ⟨13, 2, 0, 789519, 421960, 1653, 16384⟩
    (by decide) selected_cut_31000

theorem selected_cut_31001 : selected 8 ⟨789553, by decide⟩
    (prefixPartial 13 421961) = some ⟨13, 2, 0, 789553, 421961, 2333, 16384⟩ := by
  decide +kernel

theorem context_13_421961_789553 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421961 ⟨789553, by decide⟩ :=
  accepted_of_selected 13 421961 ⟨789553, by decide⟩ ⟨13, 2, 0, 789553, 421961, 2333, 16384⟩
    (by decide) selected_cut_31001

theorem selected_cut_31002 : selected 8 ⟨789573, by decide⟩
    (prefixPartial 13 421962) = some ⟨13, 2, 0, 789573, 421962, 1077, 16384⟩ := by
  decide +kernel

theorem context_13_421962_789573 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421962 ⟨789573, by decide⟩ :=
  accepted_of_selected 13 421962 ⟨789573, by decide⟩ ⟨13, 2, 0, 789573, 421962, 1077, 16384⟩
    (by decide) selected_cut_31002

theorem selected_cut_31003 : selected 8 ⟨789584, by decide⟩
    (prefixPartial 13 421963) = some ⟨13, 2, 0, 789584, 421963, 1049, 16384⟩ := by
  decide +kernel

theorem context_13_421963_789584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421963 ⟨789584, by decide⟩ :=
  accepted_of_selected 13 421963 ⟨789584, by decide⟩ ⟨13, 2, 0, 789584, 421963, 1049, 16384⟩
    (by decide) selected_cut_31003

theorem unmarked_context_12_105490_789585 : frontier 9 ⟨789585, by decide⟩
    (prefixCache 12 105490) (prefixPartial 12 105490) = false := by
  decide +kernel

theorem node_context_12_105490_789585 : EJMOriginalGlobalDAGData.nodes 9 ⟨789585, by decide⟩ =
    .split (coordinate 12) (![⟨789519, by decide⟩,⟨789553, by decide⟩,⟨789573, by decide⟩,⟨789584, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105490_789585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105490 ⟨789585, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105490
    ⟨789585, by decide⟩ (by decide) (![⟨789519, by decide⟩,⟨789553, by decide⟩,⟨789573, by decide⟩,⟨789584, by decide⟩]) unmarked_context_12_105490_789585 node_context_12_105490_789585
  intro a
  fin_cases a
  · exact context_13_421960_789519
  · exact context_13_421961_789553
  · exact context_13_421962_789573
  · exact context_13_421963_789584

theorem selected_cut_31004 : selected 8 ⟨789631, by decide⟩
    (prefixPartial 13 421964) = some ⟨13, 2, 0, 789631, 421964, 1873, 16384⟩ := by
  decide +kernel

theorem context_13_421964_789631 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421964 ⟨789631, by decide⟩ :=
  accepted_of_selected 13 421964 ⟨789631, by decide⟩ ⟨13, 2, 0, 789631, 421964, 1873, 16384⟩
    (by decide) selected_cut_31004

theorem selected_cut_31005 : selected 8 ⟨789658, by decide⟩
    (prefixPartial 13 421965) = some ⟨13, 2, 0, 789658, 421965, 2229, 16384⟩ := by
  decide +kernel

theorem context_13_421965_789658 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421965 ⟨789658, by decide⟩ :=
  accepted_of_selected 13 421965 ⟨789658, by decide⟩ ⟨13, 2, 0, 789658, 421965, 2229, 16384⟩
    (by decide) selected_cut_31005

theorem selected_cut_31006 : selected 8 ⟨789684, by decide⟩
    (prefixPartial 13 421966) = some ⟨13, 2, 0, 789684, 421966, 1529, 16384⟩ := by
  decide +kernel

theorem context_13_421966_789684 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421966 ⟨789684, by decide⟩ :=
  accepted_of_selected 13 421966 ⟨789684, by decide⟩ ⟨13, 2, 0, 789684, 421966, 1529, 16384⟩
    (by decide) selected_cut_31006

theorem selected_cut_31007 : selected 8 ⟨789693, by decide⟩
    (prefixPartial 13 421967) = some ⟨13, 2, 0, 789693, 421967, 941, 16384⟩ := by
  decide +kernel

theorem context_13_421967_789693 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421967 ⟨789693, by decide⟩ :=
  accepted_of_selected 13 421967 ⟨789693, by decide⟩ ⟨13, 2, 0, 789693, 421967, 941, 16384⟩
    (by decide) selected_cut_31007

theorem unmarked_context_12_105491_789694 : frontier 9 ⟨789694, by decide⟩
    (prefixCache 12 105491) (prefixPartial 12 105491) = false := by
  decide +kernel

theorem node_context_12_105491_789694 : EJMOriginalGlobalDAGData.nodes 9 ⟨789694, by decide⟩ =
    .split (coordinate 12) (![⟨789631, by decide⟩,⟨789658, by decide⟩,⟨789684, by decide⟩,⟨789693, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105491_789694 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105491 ⟨789694, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105491
    ⟨789694, by decide⟩ (by decide) (![⟨789631, by decide⟩,⟨789658, by decide⟩,⟨789684, by decide⟩,⟨789693, by decide⟩]) unmarked_context_12_105491_789694 node_context_12_105491_789694
  intro a
  fin_cases a
  · exact context_13_421964_789631
  · exact context_13_421965_789658
  · exact context_13_421966_789684
  · exact context_13_421967_789693

theorem unmarked_context_11_26372_789695 : frontier 10 ⟨789695, by decide⟩
    (prefixCache 11 26372) (prefixPartial 11 26372) = false := by
  decide +kernel

theorem node_context_11_26372_789695 : EJMOriginalGlobalDAGData.nodes 10 ⟨789695, by decide⟩ =
    .split (coordinate 11) (![⟨789343, by decide⟩,⟨789483, by decide⟩,⟨789585, by decide⟩,⟨789694, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26372_789695 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26372 ⟨789695, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26372
    ⟨789695, by decide⟩ (by decide) (![⟨789343, by decide⟩,⟨789483, by decide⟩,⟨789585, by decide⟩,⟨789694, by decide⟩]) unmarked_context_11_26372_789695 node_context_11_26372_789695
  intro a
  fin_cases a
  · exact context_12_105488_789343
  · exact context_12_105489_789483
  · exact context_12_105490_789585
  · exact context_12_105491_789694

theorem selected_cut_31008 : selected 8 ⟨789718, by decide⟩
    (prefixPartial 13 421968) = some ⟨13, 2, 0, 789718, 421968, 1217, 16384⟩ := by
  decide +kernel

theorem context_13_421968_789718 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421968 ⟨789718, by decide⟩ :=
  accepted_of_selected 13 421968 ⟨789718, by decide⟩ ⟨13, 2, 0, 789718, 421968, 1217, 16384⟩
    (by decide) selected_cut_31008

theorem selected_cut_31009 : selected 8 ⟨789763, by decide⟩
    (prefixPartial 13 421969) = some ⟨13, 2, 0, 789763, 421969, 2253, 16384⟩ := by
  decide +kernel

theorem context_13_421969_789763 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421969 ⟨789763, by decide⟩ :=
  accepted_of_selected 13 421969 ⟨789763, by decide⟩ ⟨13, 2, 0, 789763, 421969, 2253, 16384⟩
    (by decide) selected_cut_31009

theorem selected_cut_31010 : selected 8 ⟨789794, by decide⟩
    (prefixPartial 13 421970) = some ⟨13, 2, 0, 789794, 421970, 1457, 16384⟩ := by
  decide +kernel

theorem context_13_421970_789794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 421970 ⟨789794, by decide⟩ :=
  accepted_of_selected 13 421970 ⟨789794, by decide⟩ ⟨13, 2, 0, 789794, 421970, 1457, 16384⟩
    (by decide) selected_cut_31010

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
