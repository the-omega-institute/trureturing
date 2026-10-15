/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover091
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_08835 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 92508) = some ⟨13, 1, 0, 3444, 92508, 1, 16384⟩ := by
  decide +kernel

theorem context_13_92508_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92508 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 92508 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 92508, 1, 16384⟩
    (by decide) selected_cut_08835

theorem selected_cut_08836 : selected 8 ⟨245939, by decide⟩
    (prefixPartial 13 92509) = some ⟨13, 2, 0, 245939, 92509, 1949, 16384⟩ := by
  decide +kernel

theorem context_13_92509_245939 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92509 ⟨245939, by decide⟩ :=
  accepted_of_selected 13 92509 ⟨245939, by decide⟩ ⟨13, 2, 0, 245939, 92509, 1949, 16384⟩
    (by decide) selected_cut_08836

theorem selected_cut_08837 : selected 8 ⟨245963, by decide⟩
    (prefixPartial 13 92510) = some ⟨13, 2, 0, 245963, 92510, 1873, 16384⟩ := by
  decide +kernel

theorem context_13_92510_245963 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92510 ⟨245963, by decide⟩ :=
  accepted_of_selected 13 92510 ⟨245963, by decide⟩ ⟨13, 2, 0, 245963, 92510, 1873, 16384⟩
    (by decide) selected_cut_08837

theorem selected_cut_08838 : selected 8 ⟨245976, by decide⟩
    (prefixPartial 13 92511) = some ⟨13, 2, 0, 245976, 92511, 1149, 16384⟩ := by
  decide +kernel

theorem context_13_92511_245976 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92511 ⟨245976, by decide⟩ :=
  accepted_of_selected 13 92511 ⟨245976, by decide⟩ ⟨13, 2, 0, 245976, 92511, 1149, 16384⟩
    (by decide) selected_cut_08838

theorem unmarked_context_12_23127_245977 : frontier 9 ⟨245977, by decide⟩
    (prefixCache 12 23127) (prefixPartial 12 23127) = false := by
  decide +kernel

theorem node_context_12_23127_245977 : EJMOriginalGlobalDAGData.nodes 9 ⟨245977, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨245939, by decide⟩,⟨245963, by decide⟩,⟨245976, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23127_245977 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23127 ⟨245977, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23127
    ⟨245977, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨245939, by decide⟩,⟨245963, by decide⟩,⟨245976, by decide⟩]) unmarked_context_12_23127_245977 node_context_12_23127_245977
  intro a
  fin_cases a
  · exact context_13_92508_3444
  · exact context_13_92509_245939
  · exact context_13_92510_245963
  · exact context_13_92511_245976

theorem unmarked_context_11_5781_245978 : frontier 10 ⟨245978, by decide⟩
    (prefixCache 11 5781) (prefixPartial 11 5781) = false := by
  decide +kernel

theorem node_context_11_5781_245978 : EJMOriginalGlobalDAGData.nodes 10 ⟨245978, by decide⟩ =
    .split (coordinate 11) (![⟨245864, by decide⟩,⟨170504, by decide⟩,⟨245916, by decide⟩,⟨245977, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5781_245978 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5781 ⟨245978, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5781
    ⟨245978, by decide⟩ (by decide) (![⟨245864, by decide⟩,⟨170504, by decide⟩,⟨245916, by decide⟩,⟨245977, by decide⟩]) unmarked_context_11_5781_245978 node_context_11_5781_245978
  intro a
  fin_cases a
  · exact context_12_23124_245864
  · exact context_12_23125_170504
  · exact context_12_23126_245916
  · exact context_12_23127_245977

theorem selected_cut_08839 : selected 9 ⟨246019, by decide⟩
    (prefixPartial 12 23128) = some ⟨12, 2, 0, 246019, 23128, 3713, 65536⟩ := by
  decide +kernel

theorem context_12_23128_246019 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23128 ⟨246019, by decide⟩ :=
  accepted_of_selected 12 23128 ⟨246019, by decide⟩ ⟨12, 2, 0, 246019, 23128, 3713, 65536⟩
    (by decide) selected_cut_08839

theorem selected_cut_08840 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 92516) = some ⟨13, 1, 0, 3444, 92516, 1, 16384⟩ := by
  decide +kernel

theorem context_13_92516_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92516 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 92516 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 92516, 1, 16384⟩
    (by decide) selected_cut_08840

theorem selected_cut_08841 : selected 8 ⟨246043, by decide⟩
    (prefixPartial 13 92517) = some ⟨13, 2, 0, 246043, 92517, 2197, 16384⟩ := by
  decide +kernel

theorem context_13_92517_246043 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92517 ⟨246043, by decide⟩ :=
  accepted_of_selected 13 92517 ⟨246043, by decide⟩ ⟨13, 2, 0, 246043, 92517, 2197, 16384⟩
    (by decide) selected_cut_08841

theorem selected_cut_08842 : selected 8 ⟨246070, by decide⟩
    (prefixPartial 13 92518) = some ⟨13, 2, 0, 246070, 92518, 2121, 16384⟩ := by
  decide +kernel

theorem context_13_92518_246070 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92518 ⟨246070, by decide⟩ :=
  accepted_of_selected 13 92518 ⟨246070, by decide⟩ ⟨13, 2, 0, 246070, 92518, 2121, 16384⟩
    (by decide) selected_cut_08842

theorem selected_cut_08843 : selected 8 ⟨246082, by decide⟩
    (prefixPartial 13 92519) = some ⟨13, 2, 0, 246082, 92519, 1177, 16384⟩ := by
  decide +kernel

theorem context_13_92519_246082 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92519 ⟨246082, by decide⟩ :=
  accepted_of_selected 13 92519 ⟨246082, by decide⟩ ⟨13, 2, 0, 246082, 92519, 1177, 16384⟩
    (by decide) selected_cut_08843

theorem unmarked_context_12_23129_246083 : frontier 9 ⟨246083, by decide⟩
    (prefixCache 12 23129) (prefixPartial 12 23129) = false := by
  decide +kernel

theorem node_context_12_23129_246083 : EJMOriginalGlobalDAGData.nodes 9 ⟨246083, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨246043, by decide⟩,⟨246070, by decide⟩,⟨246082, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23129_246083 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23129 ⟨246083, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23129
    ⟨246083, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨246043, by decide⟩,⟨246070, by decide⟩,⟨246082, by decide⟩]) unmarked_context_12_23129_246083 node_context_12_23129_246083
  intro a
  fin_cases a
  · exact context_13_92516_3444
  · exact context_13_92517_246043
  · exact context_13_92518_246070
  · exact context_13_92519_246082

theorem selected_cut_08844 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 92520) = some ⟨13, 1, 0, 3444, 92520, 1, 16384⟩ := by
  decide +kernel

theorem context_13_92520_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92520 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 92520 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 92520, 1, 16384⟩
    (by decide) selected_cut_08844

theorem selected_cut_08845 : selected 8 ⟨246120, by decide⟩
    (prefixPartial 13 92521) = some ⟨13, 2, 0, 246120, 92521, 2561, 16384⟩ := by
  decide +kernel

theorem context_13_92521_246120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92521 ⟨246120, by decide⟩ :=
  accepted_of_selected 13 92521 ⟨246120, by decide⟩ ⟨13, 2, 0, 246120, 92521, 2561, 16384⟩
    (by decide) selected_cut_08845

theorem selected_cut_08846 : selected 8 ⟨246190, by decide⟩
    (prefixPartial 13 92522) = some ⟨13, 2, 0, 246190, 92522, 3165, 16384⟩ := by
  decide +kernel

theorem context_13_92522_246190 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92522 ⟨246190, by decide⟩ :=
  accepted_of_selected 13 92522 ⟨246190, by decide⟩ ⟨13, 2, 0, 246190, 92522, 3165, 16384⟩
    (by decide) selected_cut_08846

theorem selected_cut_08847 : selected 8 ⟨246205, by decide⟩
    (prefixPartial 13 92523) = some ⟨13, 2, 0, 246205, 92523, 1285, 16384⟩ := by
  decide +kernel

theorem context_13_92523_246205 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92523 ⟨246205, by decide⟩ :=
  accepted_of_selected 13 92523 ⟨246205, by decide⟩ ⟨13, 2, 0, 246205, 92523, 1285, 16384⟩
    (by decide) selected_cut_08847

theorem unmarked_context_12_23130_246206 : frontier 9 ⟨246206, by decide⟩
    (prefixCache 12 23130) (prefixPartial 12 23130) = false := by
  decide +kernel

theorem node_context_12_23130_246206 : EJMOriginalGlobalDAGData.nodes 9 ⟨246206, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨246120, by decide⟩,⟨246190, by decide⟩,⟨246205, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23130_246206 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23130 ⟨246206, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23130
    ⟨246206, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨246120, by decide⟩,⟨246190, by decide⟩,⟨246205, by decide⟩]) unmarked_context_12_23130_246206 node_context_12_23130_246206
  intro a
  fin_cases a
  · exact context_13_92520_3444
  · exact context_13_92521_246120
  · exact context_13_92522_246190
  · exact context_13_92523_246205

theorem selected_cut_08848 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 92524) = some ⟨13, 1, 0, 3444, 92524, 1, 16384⟩ := by
  decide +kernel

theorem context_13_92524_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92524 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 92524 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 92524, 1, 16384⟩
    (by decide) selected_cut_08848

theorem selected_cut_08849 : selected 8 ⟨246229, by decide⟩
    (prefixPartial 13 92525) = some ⟨13, 2, 0, 246229, 92525, 1673, 16384⟩ := by
  decide +kernel

theorem context_13_92525_246229 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92525 ⟨246229, by decide⟩ :=
  accepted_of_selected 13 92525 ⟨246229, by decide⟩ ⟨13, 2, 0, 246229, 92525, 1673, 16384⟩
    (by decide) selected_cut_08849

theorem selected_cut_08850 : selected 8 ⟨246255, by decide⟩
    (prefixPartial 13 92526) = some ⟨13, 2, 0, 246255, 92526, 2021, 16384⟩ := by
  decide +kernel

theorem context_13_92526_246255 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92526 ⟨246255, by decide⟩ :=
  accepted_of_selected 13 92526 ⟨246255, by decide⟩ ⟨13, 2, 0, 246255, 92526, 2021, 16384⟩
    (by decide) selected_cut_08850

theorem selected_cut_08851 : selected 8 ⟨246265, by decide⟩
    (prefixPartial 13 92527) = some ⟨13, 2, 0, 246265, 92527, 953, 16384⟩ := by
  decide +kernel

theorem context_13_92527_246265 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92527 ⟨246265, by decide⟩ :=
  accepted_of_selected 13 92527 ⟨246265, by decide⟩ ⟨13, 2, 0, 246265, 92527, 953, 16384⟩
    (by decide) selected_cut_08851

theorem unmarked_context_12_23131_246266 : frontier 9 ⟨246266, by decide⟩
    (prefixCache 12 23131) (prefixPartial 12 23131) = false := by
  decide +kernel

theorem node_context_12_23131_246266 : EJMOriginalGlobalDAGData.nodes 9 ⟨246266, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨246229, by decide⟩,⟨246255, by decide⟩,⟨246265, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23131_246266 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23131 ⟨246266, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23131
    ⟨246266, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨246229, by decide⟩,⟨246255, by decide⟩,⟨246265, by decide⟩]) unmarked_context_12_23131_246266 node_context_12_23131_246266
  intro a
  fin_cases a
  · exact context_13_92524_3444
  · exact context_13_92525_246229
  · exact context_13_92526_246255
  · exact context_13_92527_246265

theorem unmarked_context_11_5782_246267 : frontier 10 ⟨246267, by decide⟩
    (prefixCache 11 5782) (prefixPartial 11 5782) = false := by
  decide +kernel

theorem node_context_11_5782_246267 : EJMOriginalGlobalDAGData.nodes 10 ⟨246267, by decide⟩ =
    .split (coordinate 11) (![⟨246019, by decide⟩,⟨246083, by decide⟩,⟨246206, by decide⟩,⟨246266, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5782_246267 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5782 ⟨246267, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5782
    ⟨246267, by decide⟩ (by decide) (![⟨246019, by decide⟩,⟨246083, by decide⟩,⟨246206, by decide⟩,⟨246266, by decide⟩]) unmarked_context_11_5782_246267 node_context_11_5782_246267
  intro a
  fin_cases a
  · exact context_12_23128_246019
  · exact context_12_23129_246083
  · exact context_12_23130_246206
  · exact context_12_23131_246266

theorem selected_cut_08852 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 92528) = some ⟨13, 1, 0, 3444, 92528, 1, 16384⟩ := by
  decide +kernel

theorem context_13_92528_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92528 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 92528 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 92528, 1, 16384⟩
    (by decide) selected_cut_08852

theorem selected_cut_08853 : selected 8 ⟨246287, by decide⟩
    (prefixPartial 13 92529) = some ⟨13, 2, 0, 246287, 92529, 1557, 16384⟩ := by
  decide +kernel

theorem context_13_92529_246287 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92529 ⟨246287, by decide⟩ :=
  accepted_of_selected 13 92529 ⟨246287, by decide⟩ ⟨13, 2, 0, 246287, 92529, 1557, 16384⟩
    (by decide) selected_cut_08853

theorem selected_cut_08854 : selected 8 ⟨246305, by decide⟩
    (prefixPartial 13 92530) = some ⟨13, 2, 0, 246305, 92530, 1669, 16384⟩ := by
  decide +kernel

theorem context_13_92530_246305 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92530 ⟨246305, by decide⟩ :=
  accepted_of_selected 13 92530 ⟨246305, by decide⟩ ⟨13, 2, 0, 246305, 92530, 1669, 16384⟩
    (by decide) selected_cut_08854

theorem selected_cut_08855 : selected 8 ⟨246314, by decide⟩
    (prefixPartial 13 92531) = some ⟨13, 2, 0, 246314, 92531, 1105, 16384⟩ := by
  decide +kernel

theorem context_13_92531_246314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92531 ⟨246314, by decide⟩ :=
  accepted_of_selected 13 92531 ⟨246314, by decide⟩ ⟨13, 2, 0, 246314, 92531, 1105, 16384⟩
    (by decide) selected_cut_08855

theorem unmarked_context_12_23132_246315 : frontier 9 ⟨246315, by decide⟩
    (prefixCache 12 23132) (prefixPartial 12 23132) = false := by
  decide +kernel

theorem node_context_12_23132_246315 : EJMOriginalGlobalDAGData.nodes 9 ⟨246315, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨246287, by decide⟩,⟨246305, by decide⟩,⟨246314, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23132_246315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23132 ⟨246315, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23132
    ⟨246315, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨246287, by decide⟩,⟨246305, by decide⟩,⟨246314, by decide⟩]) unmarked_context_12_23132_246315 node_context_12_23132_246315
  intro a
  fin_cases a
  · exact context_13_92528_3444
  · exact context_13_92529_246287
  · exact context_13_92530_246305
  · exact context_13_92531_246314

theorem selected_cut_08856 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 92532) = some ⟨13, 1, 0, 3444, 92532, 1, 16384⟩ := by
  decide +kernel

theorem context_13_92532_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92532 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 92532 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 92532, 1, 16384⟩
    (by decide) selected_cut_08856

theorem selected_cut_08857 : selected 8 ⟨246358, by decide⟩
    (prefixPartial 13 92533) = some ⟨13, 2, 0, 246358, 92533, 2273, 16384⟩ := by
  decide +kernel

theorem context_13_92533_246358 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92533 ⟨246358, by decide⟩ :=
  accepted_of_selected 13 92533 ⟨246358, by decide⟩ ⟨13, 2, 0, 246358, 92533, 2273, 16384⟩
    (by decide) selected_cut_08857

theorem selected_cut_08858 : selected 8 ⟨246390, by decide⟩
    (prefixPartial 13 92534) = some ⟨13, 2, 0, 246390, 92534, 2341, 16384⟩ := by
  decide +kernel

theorem context_13_92534_246390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92534 ⟨246390, by decide⟩ :=
  accepted_of_selected 13 92534 ⟨246390, by decide⟩ ⟨13, 2, 0, 246390, 92534, 2341, 16384⟩
    (by decide) selected_cut_08858

theorem selected_cut_08859 : selected 8 ⟨246410, by decide⟩
    (prefixPartial 13 92535) = some ⟨13, 2, 0, 246410, 92535, 1313, 16384⟩ := by
  decide +kernel

theorem context_13_92535_246410 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92535 ⟨246410, by decide⟩ :=
  accepted_of_selected 13 92535 ⟨246410, by decide⟩ ⟨13, 2, 0, 246410, 92535, 1313, 16384⟩
    (by decide) selected_cut_08859

theorem unmarked_context_12_23133_246411 : frontier 9 ⟨246411, by decide⟩
    (prefixCache 12 23133) (prefixPartial 12 23133) = false := by
  decide +kernel

theorem node_context_12_23133_246411 : EJMOriginalGlobalDAGData.nodes 9 ⟨246411, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨246358, by decide⟩,⟨246390, by decide⟩,⟨246410, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23133_246411 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23133 ⟨246411, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23133
    ⟨246411, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨246358, by decide⟩,⟨246390, by decide⟩,⟨246410, by decide⟩]) unmarked_context_12_23133_246411 node_context_12_23133_246411
  intro a
  fin_cases a
  · exact context_13_92532_3444
  · exact context_13_92533_246358
  · exact context_13_92534_246390
  · exact context_13_92535_246410

theorem selected_cut_08860 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 92536) = some ⟨13, 1, 0, 3444, 92536, 1, 16384⟩ := by
  decide +kernel

theorem context_13_92536_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92536 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 92536 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 92536, 1, 16384⟩
    (by decide) selected_cut_08860

theorem selected_cut_08861 : selected 8 ⟨246430, by decide⟩
    (prefixPartial 13 92537) = some ⟨13, 2, 0, 246430, 92537, 1637, 16384⟩ := by
  decide +kernel

theorem context_13_92537_246430 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92537 ⟨246430, by decide⟩ :=
  accepted_of_selected 13 92537 ⟨246430, by decide⟩ ⟨13, 2, 0, 246430, 92537, 1637, 16384⟩
    (by decide) selected_cut_08861

theorem selected_cut_08862 : selected 8 ⟨246451, by decide⟩
    (prefixPartial 13 92538) = some ⟨13, 2, 0, 246451, 92538, 1957, 16384⟩ := by
  decide +kernel

theorem context_13_92538_246451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92538 ⟨246451, by decide⟩ :=
  accepted_of_selected 13 92538 ⟨246451, by decide⟩ ⟨13, 2, 0, 246451, 92538, 1957, 16384⟩
    (by decide) selected_cut_08862

theorem selected_cut_08863 : selected 8 ⟨246461, by decide⟩
    (prefixPartial 13 92539) = some ⟨13, 2, 0, 246461, 92539, 977, 16384⟩ := by
  decide +kernel

theorem context_13_92539_246461 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92539 ⟨246461, by decide⟩ :=
  accepted_of_selected 13 92539 ⟨246461, by decide⟩ ⟨13, 2, 0, 246461, 92539, 977, 16384⟩
    (by decide) selected_cut_08863

theorem unmarked_context_12_23134_246462 : frontier 9 ⟨246462, by decide⟩
    (prefixCache 12 23134) (prefixPartial 12 23134) = false := by
  decide +kernel

theorem node_context_12_23134_246462 : EJMOriginalGlobalDAGData.nodes 9 ⟨246462, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨246430, by decide⟩,⟨246451, by decide⟩,⟨246461, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23134_246462 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23134 ⟨246462, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23134
    ⟨246462, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨246430, by decide⟩,⟨246451, by decide⟩,⟨246461, by decide⟩]) unmarked_context_12_23134_246462 node_context_12_23134_246462
  intro a
  fin_cases a
  · exact context_13_92536_3444
  · exact context_13_92537_246430
  · exact context_13_92538_246451
  · exact context_13_92539_246461

theorem selected_cut_08864 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 92540) = some ⟨13, 1, 0, 3444, 92540, 1, 16384⟩ := by
  decide +kernel

theorem context_13_92540_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92540 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 92540 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 92540, 1, 16384⟩
    (by decide) selected_cut_08864

theorem selected_cut_08865 : selected 8 ⟨246484, by decide⟩
    (prefixPartial 13 92541) = some ⟨13, 2, 0, 246484, 92541, 1569, 16384⟩ := by
  decide +kernel

theorem context_13_92541_246484 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92541 ⟨246484, by decide⟩ :=
  accepted_of_selected 13 92541 ⟨246484, by decide⟩ ⟨13, 2, 0, 246484, 92541, 1569, 16384⟩
    (by decide) selected_cut_08865

theorem selected_cut_08866 : selected 8 ⟨246503, by decide⟩
    (prefixPartial 13 92542) = some ⟨13, 2, 0, 246503, 92542, 2045, 16384⟩ := by
  decide +kernel

theorem context_13_92542_246503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92542 ⟨246503, by decide⟩ :=
  accepted_of_selected 13 92542 ⟨246503, by decide⟩ ⟨13, 2, 0, 246503, 92542, 2045, 16384⟩
    (by decide) selected_cut_08866

theorem selected_cut_08867 : selected 8 ⟨246517, by decide⟩
    (prefixPartial 13 92543) = some ⟨13, 2, 0, 246517, 92543, 1153, 16384⟩ := by
  decide +kernel

theorem context_13_92543_246517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92543 ⟨246517, by decide⟩ :=
  accepted_of_selected 13 92543 ⟨246517, by decide⟩ ⟨13, 2, 0, 246517, 92543, 1153, 16384⟩
    (by decide) selected_cut_08867

theorem unmarked_context_12_23135_246518 : frontier 9 ⟨246518, by decide⟩
    (prefixCache 12 23135) (prefixPartial 12 23135) = false := by
  decide +kernel

theorem node_context_12_23135_246518 : EJMOriginalGlobalDAGData.nodes 9 ⟨246518, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨246484, by decide⟩,⟨246503, by decide⟩,⟨246517, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23135_246518 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23135 ⟨246518, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23135
    ⟨246518, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨246484, by decide⟩,⟨246503, by decide⟩,⟨246517, by decide⟩]) unmarked_context_12_23135_246518 node_context_12_23135_246518
  intro a
  fin_cases a
  · exact context_13_92540_3444
  · exact context_13_92541_246484
  · exact context_13_92542_246503
  · exact context_13_92543_246517

theorem unmarked_context_11_5783_246519 : frontier 10 ⟨246519, by decide⟩
    (prefixCache 11 5783) (prefixPartial 11 5783) = false := by
  decide +kernel

theorem node_context_11_5783_246519 : EJMOriginalGlobalDAGData.nodes 10 ⟨246519, by decide⟩ =
    .split (coordinate 11) (![⟨246315, by decide⟩,⟨246411, by decide⟩,⟨246462, by decide⟩,⟨246518, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5783_246519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5783 ⟨246519, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5783
    ⟨246519, by decide⟩ (by decide) (![⟨246315, by decide⟩,⟨246411, by decide⟩,⟨246462, by decide⟩,⟨246518, by decide⟩]) unmarked_context_11_5783_246519 node_context_11_5783_246519
  intro a
  fin_cases a
  · exact context_12_23132_246315
  · exact context_12_23133_246411
  · exact context_12_23134_246462
  · exact context_12_23135_246518

theorem unmarked_context_10_1445_246520 : frontier 11 ⟨246520, by decide⟩
    (prefixCache 10 1445) (prefixPartial 10 1445) = false := by
  decide +kernel

theorem node_context_10_1445_246520 : EJMOriginalGlobalDAGData.nodes 11 ⟨246520, by decide⟩ =
    .split (coordinate 10) (![⟨245809, by decide⟩,⟨245978, by decide⟩,⟨246267, by decide⟩,⟨246519, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1445_246520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1445 ⟨246520, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1445
    ⟨246520, by decide⟩ (by decide) (![⟨245809, by decide⟩,⟨245978, by decide⟩,⟨246267, by decide⟩,⟨246519, by decide⟩]) unmarked_context_10_1445_246520 node_context_10_1445_246520
  intro a
  fin_cases a
  · exact context_11_5780_245809
  · exact context_11_5781_245978
  · exact context_11_5782_246267
  · exact context_11_5783_246519

theorem selected_cut_08868 : selected 9 ⟨246563, by decide⟩
    (prefixPartial 12 23136) = some ⟨12, 2, 0, 246563, 23136, 3861, 65536⟩ := by
  decide +kernel

theorem context_12_23136_246563 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23136 ⟨246563, by decide⟩ :=
  accepted_of_selected 12 23136 ⟨246563, by decide⟩ ⟨12, 2, 0, 246563, 23136, 3861, 65536⟩
    (by decide) selected_cut_08868

theorem selected_cut_08869 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 92548) = some ⟨13, 1, 0, 3444, 92548, 1, 16384⟩ := by
  decide +kernel

theorem context_13_92548_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92548 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 92548 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 92548, 1, 16384⟩
    (by decide) selected_cut_08869

theorem selected_cut_08870 : selected 8 ⟨246604, by decide⟩
    (prefixPartial 13 92549) = some ⟨13, 2, 0, 246604, 92549, 2061, 16384⟩ := by
  decide +kernel

theorem context_13_92549_246604 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92549 ⟨246604, by decide⟩ :=
  accepted_of_selected 13 92549 ⟨246604, by decide⟩ ⟨13, 2, 0, 246604, 92549, 2061, 16384⟩
    (by decide) selected_cut_08870

theorem selected_cut_08871 : selected 8 ⟨246623, by decide⟩
    (prefixPartial 13 92550) = some ⟨13, 2, 0, 246623, 92550, 1925, 16384⟩ := by
  decide +kernel

theorem context_13_92550_246623 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92550 ⟨246623, by decide⟩ :=
  accepted_of_selected 13 92550 ⟨246623, by decide⟩ ⟨13, 2, 0, 246623, 92550, 1925, 16384⟩
    (by decide) selected_cut_08871

theorem selected_cut_08872 : selected 8 ⟨246631, by decide⟩
    (prefixPartial 13 92551) = some ⟨13, 2, 0, 246631, 92551, 1073, 16384⟩ := by
  decide +kernel

theorem context_13_92551_246631 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92551 ⟨246631, by decide⟩ :=
  accepted_of_selected 13 92551 ⟨246631, by decide⟩ ⟨13, 2, 0, 246631, 92551, 1073, 16384⟩
    (by decide) selected_cut_08872

theorem unmarked_context_12_23137_246632 : frontier 9 ⟨246632, by decide⟩
    (prefixCache 12 23137) (prefixPartial 12 23137) = false := by
  decide +kernel

theorem node_context_12_23137_246632 : EJMOriginalGlobalDAGData.nodes 9 ⟨246632, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨246604, by decide⟩,⟨246623, by decide⟩,⟨246631, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23137_246632 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23137 ⟨246632, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23137
    ⟨246632, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨246604, by decide⟩,⟨246623, by decide⟩,⟨246631, by decide⟩]) unmarked_context_12_23137_246632 node_context_12_23137_246632
  intro a
  fin_cases a
  · exact context_13_92548_3444
  · exact context_13_92549_246604
  · exact context_13_92550_246623
  · exact context_13_92551_246631

theorem selected_cut_08873 : selected 9 ⟨246671, by decide⟩
    (prefixPartial 12 23138) = some ⟨12, 2, 0, 246671, 23138, 3717, 65536⟩ := by
  decide +kernel

theorem context_12_23138_246671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23138 ⟨246671, by decide⟩ :=
  accepted_of_selected 12 23138 ⟨246671, by decide⟩ ⟨12, 2, 0, 246671, 23138, 3717, 65536⟩
    (by decide) selected_cut_08873

theorem selected_cut_08874 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 92556) = some ⟨13, 1, 0, 3444, 92556, 1, 16384⟩ := by
  decide +kernel

theorem context_13_92556_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92556 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 92556 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 92556, 1, 16384⟩
    (by decide) selected_cut_08874

theorem selected_cut_08875 : selected 8 ⟨246691, by decide⟩
    (prefixPartial 13 92557) = some ⟨13, 2, 0, 246691, 92557, 1517, 16384⟩ := by
  decide +kernel

theorem context_13_92557_246691 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92557 ⟨246691, by decide⟩ :=
  accepted_of_selected 13 92557 ⟨246691, by decide⟩ ⟨13, 2, 0, 246691, 92557, 1517, 16384⟩
    (by decide) selected_cut_08875

theorem selected_cut_08876 : selected 8 ⟨246715, by decide⟩
    (prefixPartial 13 92558) = some ⟨13, 2, 0, 246715, 92558, 1865, 16384⟩ := by
  decide +kernel

theorem context_13_92558_246715 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92558 ⟨246715, by decide⟩ :=
  accepted_of_selected 13 92558 ⟨246715, by decide⟩ ⟨13, 2, 0, 246715, 92558, 1865, 16384⟩
    (by decide) selected_cut_08876

theorem selected_cut_08877 : selected 8 ⟨246725, by decide⟩
    (prefixPartial 13 92559) = some ⟨13, 2, 0, 246725, 92559, 957, 16384⟩ := by
  decide +kernel

theorem context_13_92559_246725 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92559 ⟨246725, by decide⟩ :=
  accepted_of_selected 13 92559 ⟨246725, by decide⟩ ⟨13, 2, 0, 246725, 92559, 957, 16384⟩
    (by decide) selected_cut_08877

theorem unmarked_context_12_23139_246726 : frontier 9 ⟨246726, by decide⟩
    (prefixCache 12 23139) (prefixPartial 12 23139) = false := by
  decide +kernel

theorem node_context_12_23139_246726 : EJMOriginalGlobalDAGData.nodes 9 ⟨246726, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨246691, by decide⟩,⟨246715, by decide⟩,⟨246725, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23139_246726 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23139 ⟨246726, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23139
    ⟨246726, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨246691, by decide⟩,⟨246715, by decide⟩,⟨246725, by decide⟩]) unmarked_context_12_23139_246726 node_context_12_23139_246726
  intro a
  fin_cases a
  · exact context_13_92556_3444
  · exact context_13_92557_246691
  · exact context_13_92558_246715
  · exact context_13_92559_246725

theorem unmarked_context_11_5784_246727 : frontier 10 ⟨246727, by decide⟩
    (prefixCache 11 5784) (prefixPartial 11 5784) = false := by
  decide +kernel

theorem node_context_11_5784_246727 : EJMOriginalGlobalDAGData.nodes 10 ⟨246727, by decide⟩ =
    .split (coordinate 11) (![⟨246563, by decide⟩,⟨246632, by decide⟩,⟨246671, by decide⟩,⟨246726, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5784_246727 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5784 ⟨246727, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5784
    ⟨246727, by decide⟩ (by decide) (![⟨246563, by decide⟩,⟨246632, by decide⟩,⟨246671, by decide⟩,⟨246726, by decide⟩]) unmarked_context_11_5784_246727 node_context_11_5784_246727
  intro a
  fin_cases a
  · exact context_12_23136_246563
  · exact context_12_23137_246632
  · exact context_12_23138_246671
  · exact context_12_23139_246726

theorem selected_cut_08878 : selected 9 ⟨246770, by decide⟩
    (prefixPartial 12 23140) = some ⟨12, 2, 0, 246770, 23140, 3813, 65536⟩ := by
  decide +kernel

theorem context_12_23140_246770 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23140 ⟨246770, by decide⟩ :=
  accepted_of_selected 12 23140 ⟨246770, by decide⟩ ⟨12, 2, 0, 246770, 23140, 3813, 65536⟩
    (by decide) selected_cut_08878

theorem selected_cut_08879 : selected 9 ⟨246771, by decide⟩
    (prefixPartial 12 23141) = some ⟨12, 1, 0, 246771, 23141, 1, 65536⟩ := by
  decide +kernel

theorem context_12_23141_246771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23141 ⟨246771, by decide⟩ :=
  accepted_of_selected 12 23141 ⟨246771, by decide⟩ ⟨12, 1, 0, 246771, 23141, 1, 65536⟩
    (by decide) selected_cut_08879

theorem selected_cut_08880 : selected 9 ⟨246813, by decide⟩
    (prefixPartial 12 23142) = some ⟨12, 2, 0, 246813, 23142, 3485, 65536⟩ := by
  decide +kernel

theorem context_12_23142_246813 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23142 ⟨246813, by decide⟩ :=
  accepted_of_selected 12 23142 ⟨246813, by decide⟩ ⟨12, 2, 0, 246813, 23142, 3485, 65536⟩
    (by decide) selected_cut_08880

theorem selected_cut_08881 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 92572) = some ⟨13, 1, 0, 3444, 92572, 1, 16384⟩ := by
  decide +kernel

theorem context_13_92572_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92572 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 92572 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 92572, 1, 16384⟩
    (by decide) selected_cut_08881

theorem selected_cut_08882 : selected 8 ⟨246831, by decide⟩
    (prefixPartial 13 92573) = some ⟨13, 2, 0, 246831, 92573, 1229, 16384⟩ := by
  decide +kernel

theorem context_13_92573_246831 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92573 ⟨246831, by decide⟩ :=
  accepted_of_selected 13 92573 ⟨246831, by decide⟩ ⟨13, 2, 0, 246831, 92573, 1229, 16384⟩
    (by decide) selected_cut_08882

theorem selected_cut_08883 : selected 8 ⟨246853, by decide⟩
    (prefixPartial 13 92574) = some ⟨13, 2, 0, 246853, 92574, 2093, 16384⟩ := by
  decide +kernel

theorem context_13_92574_246853 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92574 ⟨246853, by decide⟩ :=
  accepted_of_selected 13 92574 ⟨246853, by decide⟩ ⟨13, 2, 0, 246853, 92574, 2093, 16384⟩
    (by decide) selected_cut_08883

theorem selected_cut_08884 : selected 8 ⟨246864, by decide⟩
    (prefixPartial 13 92575) = some ⟨13, 2, 0, 246864, 92575, 957, 16384⟩ := by
  decide +kernel

theorem context_13_92575_246864 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92575 ⟨246864, by decide⟩ :=
  accepted_of_selected 13 92575 ⟨246864, by decide⟩ ⟨13, 2, 0, 246864, 92575, 957, 16384⟩
    (by decide) selected_cut_08884

theorem unmarked_context_12_23143_246865 : frontier 9 ⟨246865, by decide⟩
    (prefixCache 12 23143) (prefixPartial 12 23143) = false := by
  decide +kernel

theorem node_context_12_23143_246865 : EJMOriginalGlobalDAGData.nodes 9 ⟨246865, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨246831, by decide⟩,⟨246853, by decide⟩,⟨246864, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23143_246865 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23143 ⟨246865, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23143
    ⟨246865, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨246831, by decide⟩,⟨246853, by decide⟩,⟨246864, by decide⟩]) unmarked_context_12_23143_246865 node_context_12_23143_246865
  intro a
  fin_cases a
  · exact context_13_92572_3444
  · exact context_13_92573_246831
  · exact context_13_92574_246853
  · exact context_13_92575_246864

theorem unmarked_context_11_5785_246866 : frontier 10 ⟨246866, by decide⟩
    (prefixCache 11 5785) (prefixPartial 11 5785) = false := by
  decide +kernel

theorem node_context_11_5785_246866 : EJMOriginalGlobalDAGData.nodes 10 ⟨246866, by decide⟩ =
    .split (coordinate 11) (![⟨246770, by decide⟩,⟨246771, by decide⟩,⟨246813, by decide⟩,⟨246865, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5785_246866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5785 ⟨246866, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5785
    ⟨246866, by decide⟩ (by decide) (![⟨246770, by decide⟩,⟨246771, by decide⟩,⟨246813, by decide⟩,⟨246865, by decide⟩]) unmarked_context_11_5785_246866 node_context_11_5785_246866
  intro a
  fin_cases a
  · exact context_12_23140_246770
  · exact context_12_23141_246771
  · exact context_12_23142_246813
  · exact context_12_23143_246865

theorem selected_cut_08885 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 92576) = some ⟨13, 1, 0, 3444, 92576, 1, 16384⟩ := by
  decide +kernel

theorem context_13_92576_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92576 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 92576 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 92576, 1, 16384⟩
    (by decide) selected_cut_08885

theorem selected_cut_08886 : selected 8 ⟨246886, by decide⟩
    (prefixPartial 13 92577) = some ⟨13, 2, 0, 246886, 92577, 1317, 16384⟩ := by
  decide +kernel

theorem context_13_92577_246886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92577 ⟨246886, by decide⟩ :=
  accepted_of_selected 13 92577 ⟨246886, by decide⟩ ⟨13, 2, 0, 246886, 92577, 1317, 16384⟩
    (by decide) selected_cut_08886

theorem selected_cut_08887 : selected 8 ⟨246913, by decide⟩
    (prefixPartial 13 92578) = some ⟨13, 2, 0, 246913, 92578, 2137, 16384⟩ := by
  decide +kernel

theorem context_13_92578_246913 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92578 ⟨246913, by decide⟩ :=
  accepted_of_selected 13 92578 ⟨246913, by decide⟩ ⟨13, 2, 0, 246913, 92578, 2137, 16384⟩
    (by decide) selected_cut_08887

theorem selected_cut_08888 : selected 8 ⟨246923, by decide⟩
    (prefixPartial 13 92579) = some ⟨13, 2, 0, 246923, 92579, 977, 16384⟩ := by
  decide +kernel

theorem context_13_92579_246923 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92579 ⟨246923, by decide⟩ :=
  accepted_of_selected 13 92579 ⟨246923, by decide⟩ ⟨13, 2, 0, 246923, 92579, 977, 16384⟩
    (by decide) selected_cut_08888

theorem unmarked_context_12_23144_246924 : frontier 9 ⟨246924, by decide⟩
    (prefixCache 12 23144) (prefixPartial 12 23144) = false := by
  decide +kernel

theorem node_context_12_23144_246924 : EJMOriginalGlobalDAGData.nodes 9 ⟨246924, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨246886, by decide⟩,⟨246913, by decide⟩,⟨246923, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23144_246924 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23144 ⟨246924, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23144
    ⟨246924, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨246886, by decide⟩,⟨246913, by decide⟩,⟨246923, by decide⟩]) unmarked_context_12_23144_246924 node_context_12_23144_246924
  intro a
  fin_cases a
  · exact context_13_92576_3444
  · exact context_13_92577_246886
  · exact context_13_92578_246913
  · exact context_13_92579_246923

theorem selected_cut_08889 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 92580) = some ⟨13, 1, 0, 3444, 92580, 1, 16384⟩ := by
  decide +kernel

theorem context_13_92580_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92580 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 92580 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 92580, 1, 16384⟩
    (by decide) selected_cut_08889

theorem selected_cut_08890 : selected 8 ⟨246958, by decide⟩
    (prefixPartial 13 92581) = some ⟨13, 2, 0, 246958, 92581, 1937, 16384⟩ := by
  decide +kernel

theorem context_13_92581_246958 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92581 ⟨246958, by decide⟩ :=
  accepted_of_selected 13 92581 ⟨246958, by decide⟩ ⟨13, 2, 0, 246958, 92581, 1937, 16384⟩
    (by decide) selected_cut_08890

theorem selected_cut_08891 : selected 8 ⟨246996, by decide⟩
    (prefixPartial 13 92582) = some ⟨13, 2, 0, 246996, 92582, 2661, 16384⟩ := by
  decide +kernel

theorem context_13_92582_246996 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92582 ⟨246996, by decide⟩ :=
  accepted_of_selected 13 92582 ⟨246996, by decide⟩ ⟨13, 2, 0, 246996, 92582, 2661, 16384⟩
    (by decide) selected_cut_08891

theorem selected_cut_08892 : selected 8 ⟨247032, by decide⟩
    (prefixPartial 13 92583) = some ⟨13, 2, 0, 247032, 92583, 1377, 16384⟩ := by
  decide +kernel

theorem context_13_92583_247032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92583 ⟨247032, by decide⟩ :=
  accepted_of_selected 13 92583 ⟨247032, by decide⟩ ⟨13, 2, 0, 247032, 92583, 1377, 16384⟩
    (by decide) selected_cut_08892

theorem unmarked_context_12_23145_247033 : frontier 9 ⟨247033, by decide⟩
    (prefixCache 12 23145) (prefixPartial 12 23145) = false := by
  decide +kernel

theorem node_context_12_23145_247033 : EJMOriginalGlobalDAGData.nodes 9 ⟨247033, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨246958, by decide⟩,⟨246996, by decide⟩,⟨247032, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23145_247033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23145 ⟨247033, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23145
    ⟨247033, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨246958, by decide⟩,⟨246996, by decide⟩,⟨247032, by decide⟩]) unmarked_context_12_23145_247033 node_context_12_23145_247033
  intro a
  fin_cases a
  · exact context_13_92580_3444
  · exact context_13_92581_246958
  · exact context_13_92582_246996
  · exact context_13_92583_247032

theorem selected_cut_08893 : selected 9 ⟨242157, by decide⟩
    (prefixPartial 12 23146) = some ⟨12, 1, 0, 242157, 23146, 1, 65536⟩ := by
  decide +kernel

theorem context_12_23146_242157 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23146 ⟨242157, by decide⟩ :=
  accepted_of_selected 12 23146 ⟨242157, by decide⟩ ⟨12, 1, 0, 242157, 23146, 1, 65536⟩
    (by decide) selected_cut_08893

theorem selected_cut_08894 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 92588) = some ⟨13, 1, 0, 3444, 92588, 1, 16384⟩ := by
  decide +kernel

theorem context_13_92588_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92588 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 92588 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 92588, 1, 16384⟩
    (by decide) selected_cut_08894

theorem selected_cut_08895 : selected 8 ⟨247054, by decide⟩
    (prefixPartial 13 92589) = some ⟨13, 2, 0, 247054, 92589, 1305, 16384⟩ := by
  decide +kernel

theorem context_13_92589_247054 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92589 ⟨247054, by decide⟩ :=
  accepted_of_selected 13 92589 ⟨247054, by decide⟩ ⟨13, 2, 0, 247054, 92589, 1305, 16384⟩
    (by decide) selected_cut_08895

theorem selected_cut_08896 : selected 8 ⟨247078, by decide⟩
    (prefixPartial 13 92590) = some ⟨13, 2, 0, 247078, 92590, 2501, 16384⟩ := by
  decide +kernel

theorem context_13_92590_247078 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92590 ⟨247078, by decide⟩ :=
  accepted_of_selected 13 92590 ⟨247078, by decide⟩ ⟨13, 2, 0, 247078, 92590, 2501, 16384⟩
    (by decide) selected_cut_08896

theorem selected_cut_08897 : selected 8 ⟨247091, by decide⟩
    (prefixPartial 13 92591) = some ⟨13, 2, 0, 247091, 92591, 1105, 16384⟩ := by
  decide +kernel

theorem context_13_92591_247091 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92591 ⟨247091, by decide⟩ :=
  accepted_of_selected 13 92591 ⟨247091, by decide⟩ ⟨13, 2, 0, 247091, 92591, 1105, 16384⟩
    (by decide) selected_cut_08897

theorem unmarked_context_12_23147_247092 : frontier 9 ⟨247092, by decide⟩
    (prefixCache 12 23147) (prefixPartial 12 23147) = false := by
  decide +kernel

theorem node_context_12_23147_247092 : EJMOriginalGlobalDAGData.nodes 9 ⟨247092, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨247054, by decide⟩,⟨247078, by decide⟩,⟨247091, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23147_247092 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23147 ⟨247092, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23147
    ⟨247092, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨247054, by decide⟩,⟨247078, by decide⟩,⟨247091, by decide⟩]) unmarked_context_12_23147_247092 node_context_12_23147_247092
  intro a
  fin_cases a
  · exact context_13_92588_3444
  · exact context_13_92589_247054
  · exact context_13_92590_247078
  · exact context_13_92591_247091

theorem unmarked_context_11_5786_247093 : frontier 10 ⟨247093, by decide⟩
    (prefixCache 11 5786) (prefixPartial 11 5786) = false := by
  decide +kernel

theorem node_context_11_5786_247093 : EJMOriginalGlobalDAGData.nodes 10 ⟨247093, by decide⟩ =
    .split (coordinate 11) (![⟨246924, by decide⟩,⟨247033, by decide⟩,⟨242157, by decide⟩,⟨247092, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5786_247093 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5786 ⟨247093, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5786
    ⟨247093, by decide⟩ (by decide) (![⟨246924, by decide⟩,⟨247033, by decide⟩,⟨242157, by decide⟩,⟨247092, by decide⟩]) unmarked_context_11_5786_247093 node_context_11_5786_247093
  intro a
  fin_cases a
  · exact context_12_23144_246924
  · exact context_12_23145_247033
  · exact context_12_23146_242157
  · exact context_12_23147_247092

theorem selected_cut_08898 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 92592) = some ⟨13, 1, 0, 3444, 92592, 1, 16384⟩ := by
  decide +kernel

theorem context_13_92592_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92592 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 92592 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 92592, 1, 16384⟩
    (by decide) selected_cut_08898

theorem selected_cut_08899 : selected 8 ⟨247105, by decide⟩
    (prefixPartial 13 92593) = some ⟨13, 2, 0, 247105, 92593, 989, 16384⟩ := by
  decide +kernel

theorem context_13_92593_247105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92593 ⟨247105, by decide⟩ :=
  accepted_of_selected 13 92593 ⟨247105, by decide⟩ ⟨13, 2, 0, 247105, 92593, 989, 16384⟩
    (by decide) selected_cut_08899

theorem selected_cut_08900 : selected 8 ⟨247130, by decide⟩
    (prefixPartial 13 92594) = some ⟨13, 2, 0, 247130, 92594, 2105, 16384⟩ := by
  decide +kernel

theorem context_13_92594_247130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92594 ⟨247130, by decide⟩ :=
  accepted_of_selected 13 92594 ⟨247130, by decide⟩ ⟨13, 2, 0, 247130, 92594, 2105, 16384⟩
    (by decide) selected_cut_08900

theorem selected_cut_08901 : selected 8 ⟨247137, by decide⟩
    (prefixPartial 13 92595) = some ⟨13, 2, 0, 247137, 92595, 1041, 16384⟩ := by
  decide +kernel

theorem context_13_92595_247137 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92595 ⟨247137, by decide⟩ :=
  accepted_of_selected 13 92595 ⟨247137, by decide⟩ ⟨13, 2, 0, 247137, 92595, 1041, 16384⟩
    (by decide) selected_cut_08901

theorem unmarked_context_12_23148_247138 : frontier 9 ⟨247138, by decide⟩
    (prefixCache 12 23148) (prefixPartial 12 23148) = false := by
  decide +kernel

theorem node_context_12_23148_247138 : EJMOriginalGlobalDAGData.nodes 9 ⟨247138, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨247105, by decide⟩,⟨247130, by decide⟩,⟨247137, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23148_247138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23148 ⟨247138, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23148
    ⟨247138, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨247105, by decide⟩,⟨247130, by decide⟩,⟨247137, by decide⟩]) unmarked_context_12_23148_247138 node_context_12_23148_247138
  intro a
  fin_cases a
  · exact context_13_92592_3444
  · exact context_13_92593_247105
  · exact context_13_92594_247130
  · exact context_13_92595_247137

theorem selected_cut_08902 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 92596) = some ⟨13, 1, 0, 3444, 92596, 1, 16384⟩ := by
  decide +kernel

theorem context_13_92596_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92596 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 92596 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 92596, 1, 16384⟩
    (by decide) selected_cut_08902

theorem selected_cut_08903 : selected 8 ⟨247157, by decide⟩
    (prefixPartial 13 92597) = some ⟨13, 2, 0, 247157, 92597, 1317, 16384⟩ := by
  decide +kernel

theorem context_13_92597_247157 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92597 ⟨247157, by decide⟩ :=
  accepted_of_selected 13 92597 ⟨247157, by decide⟩ ⟨13, 2, 0, 247157, 92597, 1317, 16384⟩
    (by decide) selected_cut_08903

theorem selected_cut_08904 : selected 8 ⟨247193, by decide⟩
    (prefixPartial 13 92598) = some ⟨13, 2, 0, 247193, 92598, 2537, 16384⟩ := by
  decide +kernel

theorem context_13_92598_247193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92598 ⟨247193, by decide⟩ :=
  accepted_of_selected 13 92598 ⟨247193, by decide⟩ ⟨13, 2, 0, 247193, 92598, 2537, 16384⟩
    (by decide) selected_cut_08904

theorem selected_cut_08905 : selected 8 ⟨247204, by decide⟩
    (prefixPartial 13 92599) = some ⟨13, 2, 0, 247204, 92599, 1205, 16384⟩ := by
  decide +kernel

theorem context_13_92599_247204 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92599 ⟨247204, by decide⟩ :=
  accepted_of_selected 13 92599 ⟨247204, by decide⟩ ⟨13, 2, 0, 247204, 92599, 1205, 16384⟩
    (by decide) selected_cut_08905

theorem unmarked_context_12_23149_247205 : frontier 9 ⟨247205, by decide⟩
    (prefixCache 12 23149) (prefixPartial 12 23149) = false := by
  decide +kernel

theorem node_context_12_23149_247205 : EJMOriginalGlobalDAGData.nodes 9 ⟨247205, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨247157, by decide⟩,⟨247193, by decide⟩,⟨247204, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23149_247205 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23149 ⟨247205, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23149
    ⟨247205, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨247157, by decide⟩,⟨247193, by decide⟩,⟨247204, by decide⟩]) unmarked_context_12_23149_247205 node_context_12_23149_247205
  intro a
  fin_cases a
  · exact context_13_92596_3444
  · exact context_13_92597_247157
  · exact context_13_92598_247193
  · exact context_13_92599_247204

theorem selected_cut_08906 : selected 9 ⟨247240, by decide⟩
    (prefixPartial 12 23150) = some ⟨12, 2, 0, 247240, 23150, 3753, 65536⟩ := by
  decide +kernel

theorem context_12_23150_247240 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23150 ⟨247240, by decide⟩ :=
  accepted_of_selected 12 23150 ⟨247240, by decide⟩ ⟨12, 2, 0, 247240, 23150, 3753, 65536⟩
    (by decide) selected_cut_08906

theorem selected_cut_08907 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 92604) = some ⟨13, 1, 0, 3444, 92604, 1, 16384⟩ := by
  decide +kernel

theorem context_13_92604_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92604 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 92604 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 92604, 1, 16384⟩
    (by decide) selected_cut_08907

theorem selected_cut_08908 : selected 8 ⟨247251, by decide⟩
    (prefixPartial 13 92605) = some ⟨13, 2, 0, 247251, 92605, 853, 16384⟩ := by
  decide +kernel

theorem context_13_92605_247251 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92605 ⟨247251, by decide⟩ :=
  accepted_of_selected 13 92605 ⟨247251, by decide⟩ ⟨13, 2, 0, 247251, 92605, 853, 16384⟩
    (by decide) selected_cut_08908

theorem selected_cut_08909 : selected 8 ⟨247269, by decide⟩
    (prefixPartial 13 92606) = some ⟨13, 2, 0, 247269, 92606, 2329, 16384⟩ := by
  decide +kernel

theorem context_13_92606_247269 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92606 ⟨247269, by decide⟩ :=
  accepted_of_selected 13 92606 ⟨247269, by decide⟩ ⟨13, 2, 0, 247269, 92606, 2329, 16384⟩
    (by decide) selected_cut_08909

theorem selected_cut_08910 : selected 8 ⟨247279, by decide⟩
    (prefixPartial 13 92607) = some ⟨13, 2, 0, 247279, 92607, 1085, 16384⟩ := by
  decide +kernel

theorem context_13_92607_247279 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92607 ⟨247279, by decide⟩ :=
  accepted_of_selected 13 92607 ⟨247279, by decide⟩ ⟨13, 2, 0, 247279, 92607, 1085, 16384⟩
    (by decide) selected_cut_08910

theorem unmarked_context_12_23151_247280 : frontier 9 ⟨247280, by decide⟩
    (prefixCache 12 23151) (prefixPartial 12 23151) = false := by
  decide +kernel

theorem node_context_12_23151_247280 : EJMOriginalGlobalDAGData.nodes 9 ⟨247280, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨247251, by decide⟩,⟨247269, by decide⟩,⟨247279, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23151_247280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23151 ⟨247280, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23151
    ⟨247280, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨247251, by decide⟩,⟨247269, by decide⟩,⟨247279, by decide⟩]) unmarked_context_12_23151_247280 node_context_12_23151_247280
  intro a
  fin_cases a
  · exact context_13_92604_3444
  · exact context_13_92605_247251
  · exact context_13_92606_247269
  · exact context_13_92607_247279

theorem unmarked_context_11_5787_247281 : frontier 10 ⟨247281, by decide⟩
    (prefixCache 11 5787) (prefixPartial 11 5787) = false := by
  decide +kernel

theorem node_context_11_5787_247281 : EJMOriginalGlobalDAGData.nodes 10 ⟨247281, by decide⟩ =
    .split (coordinate 11) (![⟨247138, by decide⟩,⟨247205, by decide⟩,⟨247240, by decide⟩,⟨247280, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5787_247281 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5787 ⟨247281, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5787
    ⟨247281, by decide⟩ (by decide) (![⟨247138, by decide⟩,⟨247205, by decide⟩,⟨247240, by decide⟩,⟨247280, by decide⟩]) unmarked_context_11_5787_247281 node_context_11_5787_247281
  intro a
  fin_cases a
  · exact context_12_23148_247138
  · exact context_12_23149_247205
  · exact context_12_23150_247240
  · exact context_12_23151_247280

theorem unmarked_context_10_1446_247282 : frontier 11 ⟨247282, by decide⟩
    (prefixCache 10 1446) (prefixPartial 10 1446) = false := by
  decide +kernel

theorem node_context_10_1446_247282 : EJMOriginalGlobalDAGData.nodes 11 ⟨247282, by decide⟩ =
    .split (coordinate 10) (![⟨246727, by decide⟩,⟨246866, by decide⟩,⟨247093, by decide⟩,⟨247281, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1446_247282 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1446 ⟨247282, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1446
    ⟨247282, by decide⟩ (by decide) (![⟨246727, by decide⟩,⟨246866, by decide⟩,⟨247093, by decide⟩,⟨247281, by decide⟩]) unmarked_context_10_1446_247282 node_context_10_1446_247282
  intro a
  fin_cases a
  · exact context_11_5784_246727
  · exact context_11_5785_246866
  · exact context_11_5786_247093
  · exact context_11_5787_247281

theorem selected_cut_08911 : selected 9 ⟨247317, by decide⟩
    (prefixPartial 12 23152) = some ⟨12, 2, 0, 247317, 23152, 3209, 65536⟩ := by
  decide +kernel

theorem context_12_23152_247317 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23152 ⟨247317, by decide⟩ :=
  accepted_of_selected 12 23152 ⟨247317, by decide⟩ ⟨12, 2, 0, 247317, 23152, 3209, 65536⟩
    (by decide) selected_cut_08911

theorem selected_cut_08912 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 92612) = some ⟨13, 1, 0, 3444, 92612, 1, 16384⟩ := by
  decide +kernel

theorem context_13_92612_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92612 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 92612 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 92612, 1, 16384⟩
    (by decide) selected_cut_08912

theorem selected_cut_08913 : selected 8 ⟨247335, by decide⟩
    (prefixPartial 13 92613) = some ⟨13, 2, 0, 247335, 92613, 1077, 16384⟩ := by
  decide +kernel

theorem context_13_92613_247335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92613 ⟨247335, by decide⟩ :=
  accepted_of_selected 13 92613 ⟨247335, by decide⟩ ⟨13, 2, 0, 247335, 92613, 1077, 16384⟩
    (by decide) selected_cut_08913

theorem selected_cut_08914 : selected 8 ⟨247370, by decide⟩
    (prefixPartial 13 92614) = some ⟨13, 2, 0, 247370, 92614, 2157, 16384⟩ := by
  decide +kernel

theorem context_13_92614_247370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92614 ⟨247370, by decide⟩ :=
  accepted_of_selected 13 92614 ⟨247370, by decide⟩ ⟨13, 2, 0, 247370, 92614, 2157, 16384⟩
    (by decide) selected_cut_08914

theorem selected_cut_08915 : selected 8 ⟨247384, by decide⟩
    (prefixPartial 13 92615) = some ⟨13, 2, 0, 247384, 92615, 1173, 16384⟩ := by
  decide +kernel

theorem context_13_92615_247384 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92615 ⟨247384, by decide⟩ :=
  accepted_of_selected 13 92615 ⟨247384, by decide⟩ ⟨13, 2, 0, 247384, 92615, 1173, 16384⟩
    (by decide) selected_cut_08915

theorem unmarked_context_12_23153_247385 : frontier 9 ⟨247385, by decide⟩
    (prefixCache 12 23153) (prefixPartial 12 23153) = false := by
  decide +kernel

theorem node_context_12_23153_247385 : EJMOriginalGlobalDAGData.nodes 9 ⟨247385, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨247335, by decide⟩,⟨247370, by decide⟩,⟨247384, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23153_247385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23153 ⟨247385, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23153
    ⟨247385, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨247335, by decide⟩,⟨247370, by decide⟩,⟨247384, by decide⟩]) unmarked_context_12_23153_247385 node_context_12_23153_247385
  intro a
  fin_cases a
  · exact context_13_92612_3444
  · exact context_13_92613_247335
  · exact context_13_92614_247370
  · exact context_13_92615_247384

theorem selected_cut_08916 : selected 9 ⟨247417, by decide⟩
    (prefixPartial 12 23154) = some ⟨12, 2, 0, 247417, 23154, 3409, 65536⟩ := by
  decide +kernel

theorem context_12_23154_247417 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23154 ⟨247417, by decide⟩ :=
  accepted_of_selected 12 23154 ⟨247417, by decide⟩ ⟨12, 2, 0, 247417, 23154, 3409, 65536⟩
    (by decide) selected_cut_08916

theorem selected_cut_08917 : selected 9 ⟨247464, by decide⟩
    (prefixPartial 12 23155) = some ⟨12, 2, 0, 247464, 23155, 3825, 65536⟩ := by
  decide +kernel

theorem context_12_23155_247464 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23155 ⟨247464, by decide⟩ :=
  accepted_of_selected 12 23155 ⟨247464, by decide⟩ ⟨12, 2, 0, 247464, 23155, 3825, 65536⟩
    (by decide) selected_cut_08917

theorem unmarked_context_11_5788_247465 : frontier 10 ⟨247465, by decide⟩
    (prefixCache 11 5788) (prefixPartial 11 5788) = false := by
  decide +kernel

theorem node_context_11_5788_247465 : EJMOriginalGlobalDAGData.nodes 10 ⟨247465, by decide⟩ =
    .split (coordinate 11) (![⟨247317, by decide⟩,⟨247385, by decide⟩,⟨247417, by decide⟩,⟨247464, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5788_247465 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5788 ⟨247465, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5788
    ⟨247465, by decide⟩ (by decide) (![⟨247317, by decide⟩,⟨247385, by decide⟩,⟨247417, by decide⟩,⟨247464, by decide⟩]) unmarked_context_11_5788_247465 node_context_11_5788_247465
  intro a
  fin_cases a
  · exact context_12_23152_247317
  · exact context_12_23153_247385
  · exact context_12_23154_247417
  · exact context_12_23155_247464

theorem selected_cut_08918 : selected 9 ⟨247499, by decide⟩
    (prefixPartial 12 23156) = some ⟨12, 2, 0, 247499, 23156, 3081, 65536⟩ := by
  decide +kernel

theorem context_12_23156_247499 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23156 ⟨247499, by decide⟩ :=
  accepted_of_selected 12 23156 ⟨247499, by decide⟩ ⟨12, 2, 0, 247499, 23156, 3081, 65536⟩
    (by decide) selected_cut_08918

theorem selected_cut_08919 : selected 9 ⟨247550, by decide⟩
    (prefixPartial 12 23157) = some ⟨12, 2, 0, 247550, 23157, 3961, 65536⟩ := by
  decide +kernel

theorem context_12_23157_247550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23157 ⟨247550, by decide⟩ :=
  accepted_of_selected 12 23157 ⟨247550, by decide⟩ ⟨12, 2, 0, 247550, 23157, 3961, 65536⟩
    (by decide) selected_cut_08919

theorem selected_cut_08920 : selected 9 ⟨247587, by decide⟩
    (prefixPartial 12 23158) = some ⟨12, 2, 0, 247587, 23158, 3101, 65536⟩ := by
  decide +kernel

theorem context_12_23158_247587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23158 ⟨247587, by decide⟩ :=
  accepted_of_selected 12 23158 ⟨247587, by decide⟩ ⟨12, 2, 0, 247587, 23158, 3101, 65536⟩
    (by decide) selected_cut_08920

theorem selected_cut_08921 : selected 9 ⟨247634, by decide⟩
    (prefixPartial 12 23159) = some ⟨12, 2, 0, 247634, 23159, 3673, 65536⟩ := by
  decide +kernel

theorem context_12_23159_247634 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23159 ⟨247634, by decide⟩ :=
  accepted_of_selected 12 23159 ⟨247634, by decide⟩ ⟨12, 2, 0, 247634, 23159, 3673, 65536⟩
    (by decide) selected_cut_08921

theorem unmarked_context_11_5789_247635 : frontier 10 ⟨247635, by decide⟩
    (prefixCache 11 5789) (prefixPartial 11 5789) = false := by
  decide +kernel

theorem node_context_11_5789_247635 : EJMOriginalGlobalDAGData.nodes 10 ⟨247635, by decide⟩ =
    .split (coordinate 11) (![⟨247499, by decide⟩,⟨247550, by decide⟩,⟨247587, by decide⟩,⟨247634, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5789_247635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5789 ⟨247635, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5789
    ⟨247635, by decide⟩ (by decide) (![⟨247499, by decide⟩,⟨247550, by decide⟩,⟨247587, by decide⟩,⟨247634, by decide⟩]) unmarked_context_11_5789_247635 node_context_11_5789_247635
  intro a
  fin_cases a
  · exact context_12_23156_247499
  · exact context_12_23157_247550
  · exact context_12_23158_247587
  · exact context_12_23159_247634

theorem selected_cut_08922 : selected 9 ⟨247662, by decide⟩
    (prefixPartial 12 23160) = some ⟨12, 2, 0, 247662, 23160, 2793, 65536⟩ := by
  decide +kernel

theorem context_12_23160_247662 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23160 ⟨247662, by decide⟩ :=
  accepted_of_selected 12 23160 ⟨247662, by decide⟩ ⟨12, 2, 0, 247662, 23160, 2793, 65536⟩
    (by decide) selected_cut_08922

theorem selected_cut_08923 : selected 9 ⟨247705, by decide⟩
    (prefixPartial 12 23161) = some ⟨12, 2, 0, 247705, 23161, 3965, 65536⟩ := by
  decide +kernel

theorem context_12_23161_247705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23161 ⟨247705, by decide⟩ :=
  accepted_of_selected 12 23161 ⟨247705, by decide⟩ ⟨12, 2, 0, 247705, 23161, 3965, 65536⟩
    (by decide) selected_cut_08923

theorem selected_cut_08924 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 92648) = some ⟨13, 1, 0, 3444, 92648, 1, 16384⟩ := by
  decide +kernel

theorem context_13_92648_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92648 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 92648 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 92648, 1, 16384⟩
    (by decide) selected_cut_08924

theorem selected_cut_08925 : selected 8 ⟨247712, by decide⟩
    (prefixPartial 13 92649) = some ⟨13, 2, 0, 247712, 92649, 389, 16384⟩ := by
  decide +kernel

theorem context_13_92649_247712 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92649 ⟨247712, by decide⟩ :=
  accepted_of_selected 13 92649 ⟨247712, by decide⟩ ⟨13, 2, 0, 247712, 92649, 389, 16384⟩
    (by decide) selected_cut_08925

theorem selected_cut_08926 : selected 8 ⟨247793, by decide⟩
    (prefixPartial 13 92650) = some ⟨13, 2, 0, 247793, 92650, 3573, 16384⟩ := by
  decide +kernel

theorem context_13_92650_247793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92650 ⟨247793, by decide⟩ :=
  accepted_of_selected 13 92650 ⟨247793, by decide⟩ ⟨13, 2, 0, 247793, 92650, 3573, 16384⟩
    (by decide) selected_cut_08926

theorem selected_cut_08927 : selected 8 ⟨247816, by decide⟩
    (prefixPartial 13 92651) = some ⟨13, 2, 0, 247816, 92651, 1309, 16384⟩ := by
  decide +kernel

theorem context_13_92651_247816 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 92651 ⟨247816, by decide⟩ :=
  accepted_of_selected 13 92651 ⟨247816, by decide⟩ ⟨13, 2, 0, 247816, 92651, 1309, 16384⟩
    (by decide) selected_cut_08927

theorem unmarked_context_12_23162_247817 : frontier 9 ⟨247817, by decide⟩
    (prefixCache 12 23162) (prefixPartial 12 23162) = false := by
  decide +kernel

theorem node_context_12_23162_247817 : EJMOriginalGlobalDAGData.nodes 9 ⟨247817, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨247712, by decide⟩,⟨247793, by decide⟩,⟨247816, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23162_247817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23162 ⟨247817, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23162
    ⟨247817, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨247712, by decide⟩,⟨247793, by decide⟩,⟨247816, by decide⟩]) unmarked_context_12_23162_247817 node_context_12_23162_247817
  intro a
  fin_cases a
  · exact context_13_92648_3444
  · exact context_13_92649_247712
  · exact context_13_92650_247793
  · exact context_13_92651_247816

theorem selected_cut_08928 : selected 9 ⟨247862, by decide⟩
    (prefixPartial 12 23163) = some ⟨12, 2, 0, 247862, 23163, 3501, 65536⟩ := by
  decide +kernel

theorem context_12_23163_247862 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23163 ⟨247862, by decide⟩ :=
  accepted_of_selected 12 23163 ⟨247862, by decide⟩ ⟨12, 2, 0, 247862, 23163, 3501, 65536⟩
    (by decide) selected_cut_08928

theorem unmarked_context_11_5790_247863 : frontier 10 ⟨247863, by decide⟩
    (prefixCache 11 5790) (prefixPartial 11 5790) = false := by
  decide +kernel

theorem node_context_11_5790_247863 : EJMOriginalGlobalDAGData.nodes 10 ⟨247863, by decide⟩ =
    .split (coordinate 11) (![⟨247662, by decide⟩,⟨247705, by decide⟩,⟨247817, by decide⟩,⟨247862, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5790_247863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5790 ⟨247863, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5790
    ⟨247863, by decide⟩ (by decide) (![⟨247662, by decide⟩,⟨247705, by decide⟩,⟨247817, by decide⟩,⟨247862, by decide⟩]) unmarked_context_11_5790_247863 node_context_11_5790_247863
  intro a
  fin_cases a
  · exact context_12_23160_247662
  · exact context_12_23161_247705
  · exact context_12_23162_247817
  · exact context_12_23163_247862

theorem selected_cut_08929 : selected 9 ⟨247892, by decide⟩
    (prefixPartial 12 23164) = some ⟨12, 2, 0, 247892, 23164, 2949, 65536⟩ := by
  decide +kernel

theorem context_12_23164_247892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23164 ⟨247892, by decide⟩ :=
  accepted_of_selected 12 23164 ⟨247892, by decide⟩ ⟨12, 2, 0, 247892, 23164, 2949, 65536⟩
    (by decide) selected_cut_08929

theorem selected_cut_08930 : selected 9 ⟨247953, by decide⟩
    (prefixPartial 12 23165) = some ⟨12, 2, 0, 247953, 23165, 3901, 65536⟩ := by
  decide +kernel

theorem context_12_23165_247953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23165 ⟨247953, by decide⟩ :=
  accepted_of_selected 12 23165 ⟨247953, by decide⟩ ⟨12, 2, 0, 247953, 23165, 3901, 65536⟩
    (by decide) selected_cut_08930

theorem selected_cut_08931 : selected 9 ⟨247985, by decide⟩
    (prefixPartial 12 23166) = some ⟨12, 2, 0, 247985, 23166, 2901, 65536⟩ := by
  decide +kernel

theorem context_12_23166_247985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23166 ⟨247985, by decide⟩ :=
  accepted_of_selected 12 23166 ⟨247985, by decide⟩ ⟨12, 2, 0, 247985, 23166, 2901, 65536⟩
    (by decide) selected_cut_08931

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
