/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover406
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_10_18909_1058820 : frontier 11 ⟨1058820, by decide⟩
    (prefixCache 10 18909) (prefixPartial 10 18909) = false := by
  decide +kernel

theorem node_context_10_18909_1058820 : EJMOriginalGlobalDAGData.nodes 11 ⟨1058820, by decide⟩ =
    .split (coordinate 10) (![⟨1058762, by decide⟩,⟨1058781, by decide⟩,⟨1058802, by decide⟩,⟨1058819, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18909_1058820 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18909 ⟨1058820, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18909
    ⟨1058820, by decide⟩ (by decide) (![⟨1058762, by decide⟩,⟨1058781, by decide⟩,⟨1058802, by decide⟩,⟨1058819, by decide⟩]) unmarked_context_10_18909_1058820 node_context_10_18909_1058820
  intro a
  fin_cases a
  · exact context_11_75636_1058762
  · exact context_11_75637_1058781
  · exact context_11_75638_1058802
  · exact context_11_75639_1058819

theorem selected_cut_39076 : selected 11 ⟨1058875, by decide⟩
    (prefixPartial 10 18910) = some ⟨10, 2, 0, 1058875, 18910, 2657, 1048576⟩ := by
  decide +kernel

theorem context_10_18910_1058875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18910 ⟨1058875, by decide⟩ :=
  accepted_of_selected 10 18910 ⟨1058875, by decide⟩ ⟨10, 2, 0, 1058875, 18910, 2657, 1048576⟩
    (by decide) selected_cut_39076

theorem selected_cut_39077 : selected 11 ⟨1058903, by decide⟩
    (prefixPartial 10 18911) = some ⟨10, 2, 0, 1058903, 18911, 557, 1048576⟩ := by
  decide +kernel

theorem context_10_18911_1058903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18911 ⟨1058903, by decide⟩ :=
  accepted_of_selected 10 18911 ⟨1058903, by decide⟩ ⟨10, 2, 0, 1058903, 18911, 557, 1048576⟩
    (by decide) selected_cut_39077

theorem unmarked_context_9_4727_1058904 : frontier 12 ⟨1058904, by decide⟩
    (prefixCache 9 4727) (prefixPartial 9 4727) = false := by
  decide +kernel

theorem node_context_9_4727_1058904 : EJMOriginalGlobalDAGData.nodes 12 ⟨1058904, by decide⟩ =
    .split (coordinate 9) (![⟨1058739, by decide⟩,⟨1058820, by decide⟩,⟨1058875, by decide⟩,⟨1058903, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4727_1058904 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4727 ⟨1058904, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4727
    ⟨1058904, by decide⟩ (by decide) (![⟨1058739, by decide⟩,⟨1058820, by decide⟩,⟨1058875, by decide⟩,⟨1058903, by decide⟩]) unmarked_context_9_4727_1058904 node_context_9_4727_1058904
  intro a
  fin_cases a
  · exact context_10_18908_1058739
  · exact context_10_18909_1058820
  · exact context_10_18910_1058875
  · exact context_10_18911_1058903

theorem unmarked_context_8_1181_1058905 : frontier 13 ⟨1058905, by decide⟩
    (prefixCache 8 1181) (prefixPartial 8 1181) = false := by
  decide +kernel

theorem node_context_8_1181_1058905 : EJMOriginalGlobalDAGData.nodes 13 ⟨1058905, by decide⟩ =
    .split (coordinate 8) (![⟨1056723, by decide⟩,⟨1058029, by decide⟩,⟨1058617, by decide⟩,⟨1058904, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1181_1058905 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1181 ⟨1058905, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1181
    ⟨1058905, by decide⟩ (by decide) (![⟨1056723, by decide⟩,⟨1058029, by decide⟩,⟨1058617, by decide⟩,⟨1058904, by decide⟩]) unmarked_context_8_1181_1058905 node_context_8_1181_1058905
  intro a
  fin_cases a
  · exact context_9_4724_1056723
  · exact context_9_4725_1058029
  · exact context_9_4726_1058617
  · exact context_9_4727_1058904

theorem selected_cut_39078 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 302592) = some ⟨12, 1, 0, 34034, 302592, 1, 65536⟩ := by
  decide +kernel

theorem context_12_302592_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302592 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 302592 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 302592, 1, 65536⟩
    (by decide) selected_cut_39078

theorem selected_cut_39079 : selected 8 ⟨1058936, by decide⟩
    (prefixPartial 13 1210372) = some ⟨13, 2, 0, 1058936, 1210372, 1737, 16384⟩ := by
  decide +kernel

theorem context_13_1210372_1058936 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1210372 ⟨1058936, by decide⟩ :=
  accepted_of_selected 13 1210372 ⟨1058936, by decide⟩ ⟨13, 2, 0, 1058936, 1210372, 1737, 16384⟩
    (by decide) selected_cut_39079

theorem selected_cut_39080 : selected 8 ⟨1058956, by decide⟩
    (prefixPartial 13 1210373) = some ⟨13, 2, 0, 1058956, 1210373, 1193, 16384⟩ := by
  decide +kernel

theorem context_13_1210373_1058956 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1210373 ⟨1058956, by decide⟩ :=
  accepted_of_selected 13 1210373 ⟨1058956, by decide⟩ ⟨13, 2, 0, 1058956, 1210373, 1193, 16384⟩
    (by decide) selected_cut_39080

theorem selected_cut_39081 : selected 8 ⟨1058979, by decide⟩
    (prefixPartial 13 1210374) = some ⟨13, 2, 0, 1058979, 1210374, 1073, 16384⟩ := by
  decide +kernel

theorem context_13_1210374_1058979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1210374 ⟨1058979, by decide⟩ :=
  accepted_of_selected 13 1210374 ⟨1058979, by decide⟩ ⟨13, 2, 0, 1058979, 1210374, 1073, 16384⟩
    (by decide) selected_cut_39081

theorem selected_cut_39082 : selected 8 ⟨1058998, by decide⟩
    (prefixPartial 13 1210375) = some ⟨13, 2, 0, 1058998, 1210375, 653, 16384⟩ := by
  decide +kernel

theorem context_13_1210375_1058998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1210375 ⟨1058998, by decide⟩ :=
  accepted_of_selected 13 1210375 ⟨1058998, by decide⟩ ⟨13, 2, 0, 1058998, 1210375, 653, 16384⟩
    (by decide) selected_cut_39082

theorem unmarked_context_12_302593_1058999 : frontier 9 ⟨1058999, by decide⟩
    (prefixCache 12 302593) (prefixPartial 12 302593) = false := by
  decide +kernel

theorem node_context_12_302593_1058999 : EJMOriginalGlobalDAGData.nodes 9 ⟨1058999, by decide⟩ =
    .split (coordinate 12) (![⟨1058936, by decide⟩,⟨1058956, by decide⟩,⟨1058979, by decide⟩,⟨1058998, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_302593_1058999 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302593 ⟨1058999, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 302593
    ⟨1058999, by decide⟩ (by decide) (![⟨1058936, by decide⟩,⟨1058956, by decide⟩,⟨1058979, by decide⟩,⟨1058998, by decide⟩]) unmarked_context_12_302593_1058999 node_context_12_302593_1058999
  intro a
  fin_cases a
  · exact context_13_1210372_1058936
  · exact context_13_1210373_1058956
  · exact context_13_1210374_1058979
  · exact context_13_1210375_1058998

theorem selected_cut_39083 : selected 9 ⟨1059064, by decide⟩
    (prefixPartial 12 302594) = some ⟨12, 2, 0, 1059064, 302594, 3961, 65536⟩ := by
  decide +kernel

theorem context_12_302594_1059064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302594 ⟨1059064, by decide⟩ :=
  accepted_of_selected 12 302594 ⟨1059064, by decide⟩ ⟨12, 2, 0, 1059064, 302594, 3961, 65536⟩
    (by decide) selected_cut_39083

theorem selected_cut_39084 : selected 8 ⟨1059087, by decide⟩
    (prefixPartial 13 1210380) = some ⟨13, 2, 0, 1059087, 1210380, 1565, 16384⟩ := by
  decide +kernel

theorem context_13_1210380_1059087 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1210380 ⟨1059087, by decide⟩ :=
  accepted_of_selected 13 1210380 ⟨1059087, by decide⟩ ⟨13, 2, 0, 1059087, 1210380, 1565, 16384⟩
    (by decide) selected_cut_39084

theorem selected_cut_39085 : selected 8 ⟨1059106, by decide⟩
    (prefixPartial 13 1210381) = some ⟨13, 2, 0, 1059106, 1210381, 1241, 16384⟩ := by
  decide +kernel

theorem context_13_1210381_1059106 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1210381 ⟨1059106, by decide⟩ :=
  accepted_of_selected 13 1210381 ⟨1059106, by decide⟩ ⟨13, 2, 0, 1059106, 1210381, 1241, 16384⟩
    (by decide) selected_cut_39085

theorem selected_cut_39086 : selected 8 ⟨1059125, by decide⟩
    (prefixPartial 13 1210382) = some ⟨13, 2, 0, 1059125, 1210382, 949, 16384⟩ := by
  decide +kernel

theorem context_13_1210382_1059125 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1210382 ⟨1059125, by decide⟩ :=
  accepted_of_selected 13 1210382 ⟨1059125, by decide⟩ ⟨13, 2, 0, 1059125, 1210382, 949, 16384⟩
    (by decide) selected_cut_39086

theorem selected_cut_39087 : selected 8 ⟨1059137, by decide⟩
    (prefixPartial 13 1210383) = some ⟨13, 2, 0, 1059137, 1210383, 577, 16384⟩ := by
  decide +kernel

theorem context_13_1210383_1059137 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1210383 ⟨1059137, by decide⟩ :=
  accepted_of_selected 13 1210383 ⟨1059137, by decide⟩ ⟨13, 2, 0, 1059137, 1210383, 577, 16384⟩
    (by decide) selected_cut_39087

theorem unmarked_context_12_302595_1059138 : frontier 9 ⟨1059138, by decide⟩
    (prefixCache 12 302595) (prefixPartial 12 302595) = false := by
  decide +kernel

theorem node_context_12_302595_1059138 : EJMOriginalGlobalDAGData.nodes 9 ⟨1059138, by decide⟩ =
    .split (coordinate 12) (![⟨1059087, by decide⟩,⟨1059106, by decide⟩,⟨1059125, by decide⟩,⟨1059137, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_302595_1059138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302595 ⟨1059138, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 302595
    ⟨1059138, by decide⟩ (by decide) (![⟨1059087, by decide⟩,⟨1059106, by decide⟩,⟨1059125, by decide⟩,⟨1059137, by decide⟩]) unmarked_context_12_302595_1059138 node_context_12_302595_1059138
  intro a
  fin_cases a
  · exact context_13_1210380_1059087
  · exact context_13_1210381_1059106
  · exact context_13_1210382_1059125
  · exact context_13_1210383_1059137

theorem unmarked_context_11_75648_1059139 : frontier 10 ⟨1059139, by decide⟩
    (prefixCache 11 75648) (prefixPartial 11 75648) = false := by
  decide +kernel

theorem node_context_11_75648_1059139 : EJMOriginalGlobalDAGData.nodes 10 ⟨1059139, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨1058999, by decide⟩,⟨1059064, by decide⟩,⟨1059138, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75648_1059139 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75648 ⟨1059139, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75648
    ⟨1059139, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨1058999, by decide⟩,⟨1059064, by decide⟩,⟨1059138, by decide⟩]) unmarked_context_11_75648_1059139 node_context_11_75648_1059139
  intro a
  fin_cases a
  · exact context_12_302592_34034
  · exact context_12_302593_1058999
  · exact context_12_302594_1059064
  · exact context_12_302595_1059138

theorem selected_cut_39088 : selected 8 ⟨1059167, by decide⟩
    (prefixPartial 13 1210384) = some ⟨13, 2, 0, 1059167, 1210384, 1481, 16384⟩ := by
  decide +kernel

theorem context_13_1210384_1059167 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1210384 ⟨1059167, by decide⟩ :=
  accepted_of_selected 13 1210384 ⟨1059167, by decide⟩ ⟨13, 2, 0, 1059167, 1210384, 1481, 16384⟩
    (by decide) selected_cut_39088

theorem selected_cut_39089 : selected 8 ⟨1059199, by decide⟩
    (prefixPartial 13 1210385) = some ⟨13, 2, 0, 1059199, 1210385, 1369, 16384⟩ := by
  decide +kernel

theorem context_13_1210385_1059199 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1210385 ⟨1059199, by decide⟩ :=
  accepted_of_selected 13 1210385 ⟨1059199, by decide⟩ ⟨13, 2, 0, 1059199, 1210385, 1369, 16384⟩
    (by decide) selected_cut_39089

theorem selected_cut_39090 : selected 8 ⟨1059216, by decide⟩
    (prefixPartial 13 1210386) = some ⟨13, 2, 0, 1059216, 1210386, 1041, 16384⟩ := by
  decide +kernel

theorem context_13_1210386_1059216 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1210386 ⟨1059216, by decide⟩ :=
  accepted_of_selected 13 1210386 ⟨1059216, by decide⟩ ⟨13, 2, 0, 1059216, 1210386, 1041, 16384⟩
    (by decide) selected_cut_39090

theorem selected_cut_39091 : selected 8 ⟨1059230, by decide⟩
    (prefixPartial 13 1210387) = some ⟨13, 2, 0, 1059230, 1210387, 733, 16384⟩ := by
  decide +kernel

theorem context_13_1210387_1059230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1210387 ⟨1059230, by decide⟩ :=
  accepted_of_selected 13 1210387 ⟨1059230, by decide⟩ ⟨13, 2, 0, 1059230, 1210387, 733, 16384⟩
    (by decide) selected_cut_39091

theorem unmarked_context_12_302596_1059231 : frontier 9 ⟨1059231, by decide⟩
    (prefixCache 12 302596) (prefixPartial 12 302596) = false := by
  decide +kernel

theorem node_context_12_302596_1059231 : EJMOriginalGlobalDAGData.nodes 9 ⟨1059231, by decide⟩ =
    .split (coordinate 12) (![⟨1059167, by decide⟩,⟨1059199, by decide⟩,⟨1059216, by decide⟩,⟨1059230, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_302596_1059231 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302596 ⟨1059231, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 302596
    ⟨1059231, by decide⟩ (by decide) (![⟨1059167, by decide⟩,⟨1059199, by decide⟩,⟨1059216, by decide⟩,⟨1059230, by decide⟩]) unmarked_context_12_302596_1059231 node_context_12_302596_1059231
  intro a
  fin_cases a
  · exact context_13_1210384_1059167
  · exact context_13_1210385_1059199
  · exact context_13_1210386_1059216
  · exact context_13_1210387_1059230

theorem selected_cut_39092 : selected 8 ⟨1059270, by decide⟩
    (prefixPartial 13 1210388) = some ⟨13, 2, 0, 1059270, 1210388, 1945, 16384⟩ := by
  decide +kernel

theorem context_13_1210388_1059270 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1210388 ⟨1059270, by decide⟩ :=
  accepted_of_selected 13 1210388 ⟨1059270, by decide⟩ ⟨13, 2, 0, 1059270, 1210388, 1945, 16384⟩
    (by decide) selected_cut_39092

theorem selected_cut_39093 : selected 8 ⟨1059293, by decide⟩
    (prefixPartial 13 1210389) = some ⟨13, 2, 0, 1059293, 1210389, 1301, 16384⟩ := by
  decide +kernel

theorem context_13_1210389_1059293 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1210389 ⟨1059293, by decide⟩ :=
  accepted_of_selected 13 1210389 ⟨1059293, by decide⟩ ⟨13, 2, 0, 1059293, 1210389, 1301, 16384⟩
    (by decide) selected_cut_39093

theorem selected_cut_39094 : selected 8 ⟨1059310, by decide⟩
    (prefixPartial 13 1210390) = some ⟨13, 2, 0, 1059310, 1210390, 1069, 16384⟩ := by
  decide +kernel

theorem context_13_1210390_1059310 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1210390 ⟨1059310, by decide⟩ :=
  accepted_of_selected 13 1210390 ⟨1059310, by decide⟩ ⟨13, 2, 0, 1059310, 1210390, 1069, 16384⟩
    (by decide) selected_cut_39094

theorem selected_cut_39095 : selected 8 ⟨1059323, by decide⟩
    (prefixPartial 13 1210391) = some ⟨13, 2, 0, 1059323, 1210391, 789, 16384⟩ := by
  decide +kernel

theorem context_13_1210391_1059323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1210391 ⟨1059323, by decide⟩ :=
  accepted_of_selected 13 1210391 ⟨1059323, by decide⟩ ⟨13, 2, 0, 1059323, 1210391, 789, 16384⟩
    (by decide) selected_cut_39095

theorem unmarked_context_12_302597_1059324 : frontier 9 ⟨1059324, by decide⟩
    (prefixCache 12 302597) (prefixPartial 12 302597) = false := by
  decide +kernel

theorem node_context_12_302597_1059324 : EJMOriginalGlobalDAGData.nodes 9 ⟨1059324, by decide⟩ =
    .split (coordinate 12) (![⟨1059270, by decide⟩,⟨1059293, by decide⟩,⟨1059310, by decide⟩,⟨1059323, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_302597_1059324 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302597 ⟨1059324, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 302597
    ⟨1059324, by decide⟩ (by decide) (![⟨1059270, by decide⟩,⟨1059293, by decide⟩,⟨1059310, by decide⟩,⟨1059323, by decide⟩]) unmarked_context_12_302597_1059324 node_context_12_302597_1059324
  intro a
  fin_cases a
  · exact context_13_1210388_1059270
  · exact context_13_1210389_1059293
  · exact context_13_1210390_1059310
  · exact context_13_1210391_1059323

theorem selected_cut_39096 : selected 8 ⟨1059345, by decide⟩
    (prefixPartial 13 1210392) = some ⟨13, 2, 0, 1059345, 1210392, 1417, 16384⟩ := by
  decide +kernel

theorem context_13_1210392_1059345 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1210392 ⟨1059345, by decide⟩ :=
  accepted_of_selected 13 1210392 ⟨1059345, by decide⟩ ⟨13, 2, 0, 1059345, 1210392, 1417, 16384⟩
    (by decide) selected_cut_39096

theorem selected_cut_39097 : selected 8 ⟨1059369, by decide⟩
    (prefixPartial 13 1210393) = some ⟨13, 2, 0, 1059369, 1210393, 1125, 16384⟩ := by
  decide +kernel

theorem context_13_1210393_1059369 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1210393 ⟨1059369, by decide⟩ :=
  accepted_of_selected 13 1210393 ⟨1059369, by decide⟩ ⟨13, 2, 0, 1059369, 1210393, 1125, 16384⟩
    (by decide) selected_cut_39097

theorem selected_cut_39098 : selected 8 ⟨1059386, by decide⟩
    (prefixPartial 13 1210394) = some ⟨13, 2, 0, 1059386, 1210394, 901, 16384⟩ := by
  decide +kernel

theorem context_13_1210394_1059386 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1210394 ⟨1059386, by decide⟩ :=
  accepted_of_selected 13 1210394 ⟨1059386, by decide⟩ ⟨13, 2, 0, 1059386, 1210394, 901, 16384⟩
    (by decide) selected_cut_39098

theorem selected_cut_39099 : selected 8 ⟨1059398, by decide⟩
    (prefixPartial 13 1210395) = some ⟨13, 2, 0, 1059398, 1210395, 729, 16384⟩ := by
  decide +kernel

theorem context_13_1210395_1059398 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1210395 ⟨1059398, by decide⟩ :=
  accepted_of_selected 13 1210395 ⟨1059398, by decide⟩ ⟨13, 2, 0, 1059398, 1210395, 729, 16384⟩
    (by decide) selected_cut_39099

theorem unmarked_context_12_302598_1059399 : frontier 9 ⟨1059399, by decide⟩
    (prefixCache 12 302598) (prefixPartial 12 302598) = false := by
  decide +kernel

theorem node_context_12_302598_1059399 : EJMOriginalGlobalDAGData.nodes 9 ⟨1059399, by decide⟩ =
    .split (coordinate 12) (![⟨1059345, by decide⟩,⟨1059369, by decide⟩,⟨1059386, by decide⟩,⟨1059398, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_302598_1059399 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302598 ⟨1059399, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 302598
    ⟨1059399, by decide⟩ (by decide) (![⟨1059345, by decide⟩,⟨1059369, by decide⟩,⟨1059386, by decide⟩,⟨1059398, by decide⟩]) unmarked_context_12_302598_1059399 node_context_12_302598_1059399
  intro a
  fin_cases a
  · exact context_13_1210392_1059345
  · exact context_13_1210393_1059369
  · exact context_13_1210394_1059386
  · exact context_13_1210395_1059398

theorem selected_cut_39100 : selected 8 ⟨1059431, by decide⟩
    (prefixPartial 13 1210396) = some ⟨13, 2, 0, 1059431, 1210396, 1705, 16384⟩ := by
  decide +kernel

theorem context_13_1210396_1059431 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1210396 ⟨1059431, by decide⟩ :=
  accepted_of_selected 13 1210396 ⟨1059431, by decide⟩ ⟨13, 2, 0, 1059431, 1210396, 1705, 16384⟩
    (by decide) selected_cut_39100

theorem selected_cut_39101 : selected 8 ⟨1059457, by decide⟩
    (prefixPartial 13 1210397) = some ⟨13, 2, 0, 1059457, 1210397, 1305, 16384⟩ := by
  decide +kernel

theorem context_13_1210397_1059457 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1210397 ⟨1059457, by decide⟩ :=
  accepted_of_selected 13 1210397 ⟨1059457, by decide⟩ ⟨13, 2, 0, 1059457, 1210397, 1305, 16384⟩
    (by decide) selected_cut_39101

theorem selected_cut_39102 : selected 8 ⟨1059476, by decide⟩
    (prefixPartial 13 1210398) = some ⟨13, 2, 0, 1059476, 1210398, 977, 16384⟩ := by
  decide +kernel

theorem context_13_1210398_1059476 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1210398 ⟨1059476, by decide⟩ :=
  accepted_of_selected 13 1210398 ⟨1059476, by decide⟩ ⟨13, 2, 0, 1059476, 1210398, 977, 16384⟩
    (by decide) selected_cut_39102

theorem selected_cut_39103 : selected 8 ⟨1059486, by decide⟩
    (prefixPartial 13 1210399) = some ⟨13, 2, 0, 1059486, 1210399, 733, 16384⟩ := by
  decide +kernel

theorem context_13_1210399_1059486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1210399 ⟨1059486, by decide⟩ :=
  accepted_of_selected 13 1210399 ⟨1059486, by decide⟩ ⟨13, 2, 0, 1059486, 1210399, 733, 16384⟩
    (by decide) selected_cut_39103

theorem unmarked_context_12_302599_1059487 : frontier 9 ⟨1059487, by decide⟩
    (prefixCache 12 302599) (prefixPartial 12 302599) = false := by
  decide +kernel

theorem node_context_12_302599_1059487 : EJMOriginalGlobalDAGData.nodes 9 ⟨1059487, by decide⟩ =
    .split (coordinate 12) (![⟨1059431, by decide⟩,⟨1059457, by decide⟩,⟨1059476, by decide⟩,⟨1059486, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_302599_1059487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302599 ⟨1059487, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 302599
    ⟨1059487, by decide⟩ (by decide) (![⟨1059431, by decide⟩,⟨1059457, by decide⟩,⟨1059476, by decide⟩,⟨1059486, by decide⟩]) unmarked_context_12_302599_1059487 node_context_12_302599_1059487
  intro a
  fin_cases a
  · exact context_13_1210396_1059431
  · exact context_13_1210397_1059457
  · exact context_13_1210398_1059476
  · exact context_13_1210399_1059486

theorem unmarked_context_11_75649_1059488 : frontier 10 ⟨1059488, by decide⟩
    (prefixCache 11 75649) (prefixPartial 11 75649) = false := by
  decide +kernel

theorem node_context_11_75649_1059488 : EJMOriginalGlobalDAGData.nodes 10 ⟨1059488, by decide⟩ =
    .split (coordinate 11) (![⟨1059231, by decide⟩,⟨1059324, by decide⟩,⟨1059399, by decide⟩,⟨1059487, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75649_1059488 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75649 ⟨1059488, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75649
    ⟨1059488, by decide⟩ (by decide) (![⟨1059231, by decide⟩,⟨1059324, by decide⟩,⟨1059399, by decide⟩,⟨1059487, by decide⟩]) unmarked_context_11_75649_1059488 node_context_11_75649_1059488
  intro a
  fin_cases a
  · exact context_12_302596_1059231
  · exact context_12_302597_1059324
  · exact context_12_302598_1059399
  · exact context_12_302599_1059487

theorem selected_cut_39104 : selected 9 ⟨450498, by decide⟩
    (prefixPartial 12 302600) = some ⟨12, 1, 0, 450498, 302600, 1, 65536⟩ := by
  decide +kernel

theorem context_12_302600_450498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302600 ⟨450498, by decide⟩ :=
  accepted_of_selected 12 302600 ⟨450498, by decide⟩ ⟨12, 1, 0, 450498, 302600, 1, 65536⟩
    (by decide) selected_cut_39104

theorem selected_cut_39105 : selected 8 ⟨1059527, by decide⟩
    (prefixPartial 13 1210404) = some ⟨13, 2, 0, 1059527, 1210404, 1937, 16384⟩ := by
  decide +kernel

theorem context_13_1210404_1059527 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1210404 ⟨1059527, by decide⟩ :=
  accepted_of_selected 13 1210404 ⟨1059527, by decide⟩ ⟨13, 2, 0, 1059527, 1210404, 1937, 16384⟩
    (by decide) selected_cut_39105

theorem selected_cut_39106 : selected 8 ⟨1059546, by decide⟩
    (prefixPartial 13 1210405) = some ⟨13, 2, 0, 1059546, 1210405, 1345, 16384⟩ := by
  decide +kernel

theorem context_13_1210405_1059546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1210405 ⟨1059546, by decide⟩ :=
  accepted_of_selected 13 1210405 ⟨1059546, by decide⟩ ⟨13, 2, 0, 1059546, 1210405, 1345, 16384⟩
    (by decide) selected_cut_39106

theorem selected_cut_39107 : selected 8 ⟨1059572, by decide⟩
    (prefixPartial 13 1210406) = some ⟨13, 2, 0, 1059572, 1210406, 1241, 16384⟩ := by
  decide +kernel

theorem context_13_1210406_1059572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1210406 ⟨1059572, by decide⟩ :=
  accepted_of_selected 13 1210406 ⟨1059572, by decide⟩ ⟨13, 2, 0, 1059572, 1210406, 1241, 16384⟩
    (by decide) selected_cut_39107

theorem selected_cut_39108 : selected 8 ⟨1059581, by decide⟩
    (prefixPartial 13 1210407) = some ⟨13, 2, 0, 1059581, 1210407, 653, 16384⟩ := by
  decide +kernel

theorem context_13_1210407_1059581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1210407 ⟨1059581, by decide⟩ :=
  accepted_of_selected 13 1210407 ⟨1059581, by decide⟩ ⟨13, 2, 0, 1059581, 1210407, 653, 16384⟩
    (by decide) selected_cut_39108

theorem unmarked_context_12_302601_1059582 : frontier 9 ⟨1059582, by decide⟩
    (prefixCache 12 302601) (prefixPartial 12 302601) = false := by
  decide +kernel

theorem node_context_12_302601_1059582 : EJMOriginalGlobalDAGData.nodes 9 ⟨1059582, by decide⟩ =
    .split (coordinate 12) (![⟨1059527, by decide⟩,⟨1059546, by decide⟩,⟨1059572, by decide⟩,⟨1059581, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_302601_1059582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302601 ⟨1059582, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 302601
    ⟨1059582, by decide⟩ (by decide) (![⟨1059527, by decide⟩,⟨1059546, by decide⟩,⟨1059572, by decide⟩,⟨1059581, by decide⟩]) unmarked_context_12_302601_1059582 node_context_12_302601_1059582
  intro a
  fin_cases a
  · exact context_13_1210404_1059527
  · exact context_13_1210405_1059546
  · exact context_13_1210406_1059572
  · exact context_13_1210407_1059581

theorem selected_cut_39109 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 302602) = some ⟨12, 1, 0, 893903, 302602, 1, 65536⟩ := by
  decide +kernel

theorem context_12_302602_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302602 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 302602 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 302602, 1, 65536⟩
    (by decide) selected_cut_39109

theorem selected_cut_39110 : selected 8 ⟨1059616, by decide⟩
    (prefixPartial 13 1210412) = some ⟨13, 2, 0, 1059616, 1210412, 1685, 16384⟩ := by
  decide +kernel

theorem context_13_1210412_1059616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1210412 ⟨1059616, by decide⟩ :=
  accepted_of_selected 13 1210412 ⟨1059616, by decide⟩ ⟨13, 2, 0, 1059616, 1210412, 1685, 16384⟩
    (by decide) selected_cut_39110

theorem selected_cut_39111 : selected 8 ⟨1059641, by decide⟩
    (prefixPartial 13 1210413) = some ⟨13, 2, 0, 1059641, 1210413, 1425, 16384⟩ := by
  decide +kernel

theorem context_13_1210413_1059641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1210413 ⟨1059641, by decide⟩ :=
  accepted_of_selected 13 1210413 ⟨1059641, by decide⟩ ⟨13, 2, 0, 1059641, 1210413, 1425, 16384⟩
    (by decide) selected_cut_39111

theorem selected_cut_39112 : selected 8 ⟨1059663, by decide⟩
    (prefixPartial 13 1210414) = some ⟨13, 2, 0, 1059663, 1210414, 1141, 16384⟩ := by
  decide +kernel

theorem context_13_1210414_1059663 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1210414 ⟨1059663, by decide⟩ :=
  accepted_of_selected 13 1210414 ⟨1059663, by decide⟩ ⟨13, 2, 0, 1059663, 1210414, 1141, 16384⟩
    (by decide) selected_cut_39112

theorem selected_cut_39113 : selected 8 ⟨1059675, by decide⟩
    (prefixPartial 13 1210415) = some ⟨13, 2, 0, 1059675, 1210415, 709, 16384⟩ := by
  decide +kernel

theorem context_13_1210415_1059675 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1210415 ⟨1059675, by decide⟩ :=
  accepted_of_selected 13 1210415 ⟨1059675, by decide⟩ ⟨13, 2, 0, 1059675, 1210415, 709, 16384⟩
    (by decide) selected_cut_39113

theorem unmarked_context_12_302603_1059676 : frontier 9 ⟨1059676, by decide⟩
    (prefixCache 12 302603) (prefixPartial 12 302603) = false := by
  decide +kernel

theorem node_context_12_302603_1059676 : EJMOriginalGlobalDAGData.nodes 9 ⟨1059676, by decide⟩ =
    .split (coordinate 12) (![⟨1059616, by decide⟩,⟨1059641, by decide⟩,⟨1059663, by decide⟩,⟨1059675, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_302603_1059676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302603 ⟨1059676, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 302603
    ⟨1059676, by decide⟩ (by decide) (![⟨1059616, by decide⟩,⟨1059641, by decide⟩,⟨1059663, by decide⟩,⟨1059675, by decide⟩]) unmarked_context_12_302603_1059676 node_context_12_302603_1059676
  intro a
  fin_cases a
  · exact context_13_1210412_1059616
  · exact context_13_1210413_1059641
  · exact context_13_1210414_1059663
  · exact context_13_1210415_1059675

theorem unmarked_context_11_75650_1059677 : frontier 10 ⟨1059677, by decide⟩
    (prefixCache 11 75650) (prefixPartial 11 75650) = false := by
  decide +kernel

theorem node_context_11_75650_1059677 : EJMOriginalGlobalDAGData.nodes 10 ⟨1059677, by decide⟩ =
    .split (coordinate 11) (![⟨450498, by decide⟩,⟨1059582, by decide⟩,⟨893903, by decide⟩,⟨1059676, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75650_1059677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75650 ⟨1059677, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75650
    ⟨1059677, by decide⟩ (by decide) (![⟨450498, by decide⟩,⟨1059582, by decide⟩,⟨893903, by decide⟩,⟨1059676, by decide⟩]) unmarked_context_11_75650_1059677 node_context_11_75650_1059677
  intro a
  fin_cases a
  · exact context_12_302600_450498
  · exact context_12_302601_1059582
  · exact context_12_302602_893903
  · exact context_12_302603_1059676

theorem selected_cut_39114 : selected 8 ⟨1059700, by decide⟩
    (prefixPartial 13 1210416) = some ⟨13, 2, 0, 1059700, 1210416, 1337, 16384⟩ := by
  decide +kernel

theorem context_13_1210416_1059700 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1210416 ⟨1059700, by decide⟩ :=
  accepted_of_selected 13 1210416 ⟨1059700, by decide⟩ ⟨13, 2, 0, 1059700, 1210416, 1337, 16384⟩
    (by decide) selected_cut_39114

theorem selected_cut_39115 : selected 8 ⟨1059725, by decide⟩
    (prefixPartial 13 1210417) = some ⟨13, 2, 0, 1059725, 1210417, 1413, 16384⟩ := by
  decide +kernel

theorem context_13_1210417_1059725 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1210417 ⟨1059725, by decide⟩ :=
  accepted_of_selected 13 1210417 ⟨1059725, by decide⟩ ⟨13, 2, 0, 1059725, 1210417, 1413, 16384⟩
    (by decide) selected_cut_39115

theorem selected_cut_39116 : selected 8 ⟨1059741, by decide⟩
    (prefixPartial 13 1210418) = some ⟨13, 2, 0, 1059741, 1210418, 1121, 16384⟩ := by
  decide +kernel

theorem context_13_1210418_1059741 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1210418 ⟨1059741, by decide⟩ :=
  accepted_of_selected 13 1210418 ⟨1059741, by decide⟩ ⟨13, 2, 0, 1059741, 1210418, 1121, 16384⟩
    (by decide) selected_cut_39116

theorem selected_cut_39117 : selected 8 ⟨1059752, by decide⟩
    (prefixPartial 13 1210419) = some ⟨13, 2, 0, 1059752, 1210419, 781, 16384⟩ := by
  decide +kernel

theorem context_13_1210419_1059752 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1210419 ⟨1059752, by decide⟩ :=
  accepted_of_selected 13 1210419 ⟨1059752, by decide⟩ ⟨13, 2, 0, 1059752, 1210419, 781, 16384⟩
    (by decide) selected_cut_39117

theorem unmarked_context_12_302604_1059753 : frontier 9 ⟨1059753, by decide⟩
    (prefixCache 12 302604) (prefixPartial 12 302604) = false := by
  decide +kernel

theorem node_context_12_302604_1059753 : EJMOriginalGlobalDAGData.nodes 9 ⟨1059753, by decide⟩ =
    .split (coordinate 12) (![⟨1059700, by decide⟩,⟨1059725, by decide⟩,⟨1059741, by decide⟩,⟨1059752, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_302604_1059753 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302604 ⟨1059753, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 302604
    ⟨1059753, by decide⟩ (by decide) (![⟨1059700, by decide⟩,⟨1059725, by decide⟩,⟨1059741, by decide⟩,⟨1059752, by decide⟩]) unmarked_context_12_302604_1059753 node_context_12_302604_1059753
  intro a
  fin_cases a
  · exact context_13_1210416_1059700
  · exact context_13_1210417_1059725
  · exact context_13_1210418_1059741
  · exact context_13_1210419_1059752

theorem selected_cut_39118 : selected 8 ⟨1059791, by decide⟩
    (prefixPartial 13 1210420) = some ⟨13, 2, 0, 1059791, 1210420, 1785, 16384⟩ := by
  decide +kernel

theorem context_13_1210420_1059791 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1210420 ⟨1059791, by decide⟩ :=
  accepted_of_selected 13 1210420 ⟨1059791, by decide⟩ ⟨13, 2, 0, 1059791, 1210420, 1785, 16384⟩
    (by decide) selected_cut_39118

theorem selected_cut_39119 : selected 8 ⟨1059808, by decide⟩
    (prefixPartial 13 1210421) = some ⟨13, 2, 0, 1059808, 1210421, 1341, 16384⟩ := by
  decide +kernel

theorem context_13_1210421_1059808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1210421 ⟨1059808, by decide⟩ :=
  accepted_of_selected 13 1210421 ⟨1059808, by decide⟩ ⟨13, 2, 0, 1059808, 1210421, 1341, 16384⟩
    (by decide) selected_cut_39119

theorem selected_cut_39120 : selected 8 ⟨1059833, by decide⟩
    (prefixPartial 13 1210422) = some ⟨13, 2, 0, 1059833, 1210422, 1169, 16384⟩ := by
  decide +kernel

theorem context_13_1210422_1059833 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1210422 ⟨1059833, by decide⟩ :=
  accepted_of_selected 13 1210422 ⟨1059833, by decide⟩ ⟨13, 2, 0, 1059833, 1210422, 1169, 16384⟩
    (by decide) selected_cut_39120

theorem selected_cut_39121 : selected 8 ⟨1059844, by decide⟩
    (prefixPartial 13 1210423) = some ⟨13, 2, 0, 1059844, 1210423, 813, 16384⟩ := by
  decide +kernel

theorem context_13_1210423_1059844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1210423 ⟨1059844, by decide⟩ :=
  accepted_of_selected 13 1210423 ⟨1059844, by decide⟩ ⟨13, 2, 0, 1059844, 1210423, 813, 16384⟩
    (by decide) selected_cut_39121

theorem unmarked_context_12_302605_1059845 : frontier 9 ⟨1059845, by decide⟩
    (prefixCache 12 302605) (prefixPartial 12 302605) = false := by
  decide +kernel

theorem node_context_12_302605_1059845 : EJMOriginalGlobalDAGData.nodes 9 ⟨1059845, by decide⟩ =
    .split (coordinate 12) (![⟨1059791, by decide⟩,⟨1059808, by decide⟩,⟨1059833, by decide⟩,⟨1059844, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_302605_1059845 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302605 ⟨1059845, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 302605
    ⟨1059845, by decide⟩ (by decide) (![⟨1059791, by decide⟩,⟨1059808, by decide⟩,⟨1059833, by decide⟩,⟨1059844, by decide⟩]) unmarked_context_12_302605_1059845 node_context_12_302605_1059845
  intro a
  fin_cases a
  · exact context_13_1210420_1059791
  · exact context_13_1210421_1059808
  · exact context_13_1210422_1059833
  · exact context_13_1210423_1059844

theorem selected_cut_39122 : selected 8 ⟨1059869, by decide⟩
    (prefixPartial 13 1210424) = some ⟨13, 2, 0, 1059869, 1210424, 1513, 16384⟩ := by
  decide +kernel

theorem context_13_1210424_1059869 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1210424 ⟨1059869, by decide⟩ :=
  accepted_of_selected 13 1210424 ⟨1059869, by decide⟩ ⟨13, 2, 0, 1059869, 1210424, 1513, 16384⟩
    (by decide) selected_cut_39122

theorem selected_cut_39123 : selected 8 ⟨1059888, by decide⟩
    (prefixPartial 13 1210425) = some ⟨13, 2, 0, 1059888, 1210425, 1293, 16384⟩ := by
  decide +kernel

theorem context_13_1210425_1059888 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1210425 ⟨1059888, by decide⟩ :=
  accepted_of_selected 13 1210425 ⟨1059888, by decide⟩ ⟨13, 2, 0, 1059888, 1210425, 1293, 16384⟩
    (by decide) selected_cut_39123

theorem selected_cut_39124 : selected 8 ⟨1059903, by decide⟩
    (prefixPartial 13 1210426) = some ⟨13, 2, 0, 1059903, 1210426, 945, 16384⟩ := by
  decide +kernel

theorem context_13_1210426_1059903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1210426 ⟨1059903, by decide⟩ :=
  accepted_of_selected 13 1210426 ⟨1059903, by decide⟩ ⟨13, 2, 0, 1059903, 1210426, 945, 16384⟩
    (by decide) selected_cut_39124

theorem selected_cut_39125 : selected 8 ⟨1059913, by decide⟩
    (prefixPartial 13 1210427) = some ⟨13, 2, 0, 1059913, 1210427, 813, 16384⟩ := by
  decide +kernel

theorem context_13_1210427_1059913 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1210427 ⟨1059913, by decide⟩ :=
  accepted_of_selected 13 1210427 ⟨1059913, by decide⟩ ⟨13, 2, 0, 1059913, 1210427, 813, 16384⟩
    (by decide) selected_cut_39125

theorem unmarked_context_12_302606_1059914 : frontier 9 ⟨1059914, by decide⟩
    (prefixCache 12 302606) (prefixPartial 12 302606) = false := by
  decide +kernel

theorem node_context_12_302606_1059914 : EJMOriginalGlobalDAGData.nodes 9 ⟨1059914, by decide⟩ =
    .split (coordinate 12) (![⟨1059869, by decide⟩,⟨1059888, by decide⟩,⟨1059903, by decide⟩,⟨1059913, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_302606_1059914 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302606 ⟨1059914, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 302606
    ⟨1059914, by decide⟩ (by decide) (![⟨1059869, by decide⟩,⟨1059888, by decide⟩,⟨1059903, by decide⟩,⟨1059913, by decide⟩]) unmarked_context_12_302606_1059914 node_context_12_302606_1059914
  intro a
  fin_cases a
  · exact context_13_1210424_1059869
  · exact context_13_1210425_1059888
  · exact context_13_1210426_1059903
  · exact context_13_1210427_1059913

theorem selected_cut_39126 : selected 8 ⟨1059943, by decide⟩
    (prefixPartial 13 1210428) = some ⟨13, 2, 0, 1059943, 1210428, 1473, 16384⟩ := by
  decide +kernel

theorem context_13_1210428_1059943 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1210428 ⟨1059943, by decide⟩ :=
  accepted_of_selected 13 1210428 ⟨1059943, by decide⟩ ⟨13, 2, 0, 1059943, 1210428, 1473, 16384⟩
    (by decide) selected_cut_39126

theorem selected_cut_39127 : selected 8 ⟨1059973, by decide⟩
    (prefixPartial 13 1210429) = some ⟨13, 2, 0, 1059973, 1210429, 1401, 16384⟩ := by
  decide +kernel

theorem context_13_1210429_1059973 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1210429 ⟨1059973, by decide⟩ :=
  accepted_of_selected 13 1210429 ⟨1059973, by decide⟩ ⟨13, 2, 0, 1059973, 1210429, 1401, 16384⟩
    (by decide) selected_cut_39127

theorem selected_cut_39128 : selected 8 ⟨1059986, by decide⟩
    (prefixPartial 13 1210430) = some ⟨13, 2, 0, 1059986, 1210430, 961, 16384⟩ := by
  decide +kernel

theorem context_13_1210430_1059986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1210430 ⟨1059986, by decide⟩ :=
  accepted_of_selected 13 1210430 ⟨1059986, by decide⟩ ⟨13, 2, 0, 1059986, 1210430, 961, 16384⟩
    (by decide) selected_cut_39128

theorem selected_cut_39129 : selected 8 ⟨1060000, by decide⟩
    (prefixPartial 13 1210431) = some ⟨13, 2, 0, 1060000, 1210431, 813, 16384⟩ := by
  decide +kernel

theorem context_13_1210431_1060000 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1210431 ⟨1060000, by decide⟩ :=
  accepted_of_selected 13 1210431 ⟨1060000, by decide⟩ ⟨13, 2, 0, 1060000, 1210431, 813, 16384⟩
    (by decide) selected_cut_39129

theorem unmarked_context_12_302607_1060001 : frontier 9 ⟨1060001, by decide⟩
    (prefixCache 12 302607) (prefixPartial 12 302607) = false := by
  decide +kernel

theorem node_context_12_302607_1060001 : EJMOriginalGlobalDAGData.nodes 9 ⟨1060001, by decide⟩ =
    .split (coordinate 12) (![⟨1059943, by decide⟩,⟨1059973, by decide⟩,⟨1059986, by decide⟩,⟨1060000, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_302607_1060001 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302607 ⟨1060001, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 302607
    ⟨1060001, by decide⟩ (by decide) (![⟨1059943, by decide⟩,⟨1059973, by decide⟩,⟨1059986, by decide⟩,⟨1060000, by decide⟩]) unmarked_context_12_302607_1060001 node_context_12_302607_1060001
  intro a
  fin_cases a
  · exact context_13_1210428_1059943
  · exact context_13_1210429_1059973
  · exact context_13_1210430_1059986
  · exact context_13_1210431_1060000

theorem unmarked_context_11_75651_1060002 : frontier 10 ⟨1060002, by decide⟩
    (prefixCache 11 75651) (prefixPartial 11 75651) = false := by
  decide +kernel

theorem node_context_11_75651_1060002 : EJMOriginalGlobalDAGData.nodes 10 ⟨1060002, by decide⟩ =
    .split (coordinate 11) (![⟨1059753, by decide⟩,⟨1059845, by decide⟩,⟨1059914, by decide⟩,⟨1060001, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75651_1060002 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75651 ⟨1060002, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75651
    ⟨1060002, by decide⟩ (by decide) (![⟨1059753, by decide⟩,⟨1059845, by decide⟩,⟨1059914, by decide⟩,⟨1060001, by decide⟩]) unmarked_context_11_75651_1060002 node_context_11_75651_1060002
  intro a
  fin_cases a
  · exact context_12_302604_1059753
  · exact context_12_302605_1059845
  · exact context_12_302606_1059914
  · exact context_12_302607_1060001

theorem unmarked_context_10_18912_1060003 : frontier 11 ⟨1060003, by decide⟩
    (prefixCache 10 18912) (prefixPartial 10 18912) = false := by
  decide +kernel

theorem node_context_10_18912_1060003 : EJMOriginalGlobalDAGData.nodes 11 ⟨1060003, by decide⟩ =
    .split (coordinate 10) (![⟨1059139, by decide⟩,⟨1059488, by decide⟩,⟨1059677, by decide⟩,⟨1060002, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18912_1060003 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18912 ⟨1060003, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18912
    ⟨1060003, by decide⟩ (by decide) (![⟨1059139, by decide⟩,⟨1059488, by decide⟩,⟨1059677, by decide⟩,⟨1060002, by decide⟩]) unmarked_context_10_18912_1060003 node_context_10_18912_1060003
  intro a
  fin_cases a
  · exact context_11_75648_1059139
  · exact context_11_75649_1059488
  · exact context_11_75650_1059677
  · exact context_11_75651_1060002

theorem selected_cut_39130 : selected 9 ⟨994572, by decide⟩
    (prefixPartial 12 302608) = some ⟨12, 1, 0, 994572, 302608, 1, 65536⟩ := by
  decide +kernel

theorem context_12_302608_994572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302608 ⟨994572, by decide⟩ :=
  accepted_of_selected 12 302608 ⟨994572, by decide⟩ ⟨12, 1, 0, 994572, 302608, 1, 65536⟩
    (by decide) selected_cut_39130

theorem selected_cut_39131 : selected 9 ⟨1060070, by decide⟩
    (prefixPartial 12 302609) = some ⟨12, 2, 0, 1060070, 302609, 4021, 65536⟩ := by
  decide +kernel

theorem context_12_302609_1060070 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302609 ⟨1060070, by decide⟩ :=
  accepted_of_selected 12 302609 ⟨1060070, by decide⟩ ⟨12, 2, 0, 1060070, 302609, 4021, 65536⟩
    (by decide) selected_cut_39131

theorem selected_cut_39132 : selected 9 ⟨1060125, by decide⟩
    (prefixPartial 12 302610) = some ⟨12, 2, 0, 1060125, 302610, 3489, 65536⟩ := by
  decide +kernel

theorem context_12_302610_1060125 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302610 ⟨1060125, by decide⟩ :=
  accepted_of_selected 12 302610 ⟨1060125, by decide⟩ ⟨12, 2, 0, 1060125, 302610, 3489, 65536⟩
    (by decide) selected_cut_39132

theorem selected_cut_39133 : selected 9 ⟨1060193, by decide⟩
    (prefixPartial 12 302611) = some ⟨12, 2, 0, 1060193, 302611, 4001, 65536⟩ := by
  decide +kernel

theorem context_12_302611_1060193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302611 ⟨1060193, by decide⟩ :=
  accepted_of_selected 12 302611 ⟨1060193, by decide⟩ ⟨12, 2, 0, 1060193, 302611, 4001, 65536⟩
    (by decide) selected_cut_39133

theorem unmarked_context_11_75652_1060194 : frontier 10 ⟨1060194, by decide⟩
    (prefixCache 11 75652) (prefixPartial 11 75652) = false := by
  decide +kernel

theorem node_context_11_75652_1060194 : EJMOriginalGlobalDAGData.nodes 10 ⟨1060194, by decide⟩ =
    .split (coordinate 11) (![⟨994572, by decide⟩,⟨1060070, by decide⟩,⟨1060125, by decide⟩,⟨1060193, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75652_1060194 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75652 ⟨1060194, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75652
    ⟨1060194, by decide⟩ (by decide) (![⟨994572, by decide⟩,⟨1060070, by decide⟩,⟨1060125, by decide⟩,⟨1060193, by decide⟩]) unmarked_context_11_75652_1060194 node_context_11_75652_1060194
  intro a
  fin_cases a
  · exact context_12_302608_994572
  · exact context_12_302609_1060070
  · exact context_12_302610_1060125
  · exact context_12_302611_1060193

theorem selected_cut_39134 : selected 9 ⟨1060256, by decide⟩
    (prefixPartial 12 302612) = some ⟨12, 2, 0, 1060256, 302612, 3585, 65536⟩ := by
  decide +kernel

theorem context_12_302612_1060256 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302612 ⟨1060256, by decide⟩ :=
  accepted_of_selected 12 302612 ⟨1060256, by decide⟩ ⟨12, 2, 0, 1060256, 302612, 3585, 65536⟩
    (by decide) selected_cut_39134

theorem selected_cut_39135 : selected 9 ⟨1060322, by decide⟩
    (prefixPartial 12 302613) = some ⟨12, 2, 0, 1060322, 302613, 3905, 65536⟩ := by
  decide +kernel

theorem context_12_302613_1060322 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302613 ⟨1060322, by decide⟩ :=
  accepted_of_selected 12 302613 ⟨1060322, by decide⟩ ⟨12, 2, 0, 1060322, 302613, 3905, 65536⟩
    (by decide) selected_cut_39135

theorem selected_cut_39136 : selected 9 ⟨1060372, by decide⟩
    (prefixPartial 12 302614) = some ⟨12, 2, 0, 1060372, 302614, 3353, 65536⟩ := by
  decide +kernel

theorem context_12_302614_1060372 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302614 ⟨1060372, by decide⟩ :=
  accepted_of_selected 12 302614 ⟨1060372, by decide⟩ ⟨12, 2, 0, 1060372, 302614, 3353, 65536⟩
    (by decide) selected_cut_39136

theorem selected_cut_39137 : selected 9 ⟨1060441, by decide⟩
    (prefixPartial 12 302615) = some ⟨12, 2, 0, 1060441, 302615, 3897, 65536⟩ := by
  decide +kernel

theorem context_12_302615_1060441 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302615 ⟨1060441, by decide⟩ :=
  accepted_of_selected 12 302615 ⟨1060441, by decide⟩ ⟨12, 2, 0, 1060441, 302615, 3897, 65536⟩
    (by decide) selected_cut_39137

theorem unmarked_context_11_75653_1060442 : frontier 10 ⟨1060442, by decide⟩
    (prefixCache 11 75653) (prefixPartial 11 75653) = false := by
  decide +kernel

theorem node_context_11_75653_1060442 : EJMOriginalGlobalDAGData.nodes 10 ⟨1060442, by decide⟩ =
    .split (coordinate 11) (![⟨1060256, by decide⟩,⟨1060322, by decide⟩,⟨1060372, by decide⟩,⟨1060441, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75653_1060442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75653 ⟨1060442, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75653
    ⟨1060442, by decide⟩ (by decide) (![⟨1060256, by decide⟩,⟨1060322, by decide⟩,⟨1060372, by decide⟩,⟨1060441, by decide⟩]) unmarked_context_11_75653_1060442 node_context_11_75653_1060442
  intro a
  fin_cases a
  · exact context_12_302612_1060256
  · exact context_12_302613_1060322
  · exact context_12_302614_1060372
  · exact context_12_302615_1060441

theorem selected_cut_39138 : selected 9 ⟨1060498, by decide⟩
    (prefixPartial 12 302616) = some ⟨12, 2, 0, 1060498, 302616, 3629, 65536⟩ := by
  decide +kernel

theorem context_12_302616_1060498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302616 ⟨1060498, by decide⟩ :=
  accepted_of_selected 12 302616 ⟨1060498, by decide⟩ ⟨12, 2, 0, 1060498, 302616, 3629, 65536⟩
    (by decide) selected_cut_39138

theorem selected_cut_39139 : selected 8 ⟨1060522, by decide⟩
    (prefixPartial 13 1210468) = some ⟨13, 2, 0, 1060522, 1210468, 1365, 16384⟩ := by
  decide +kernel

theorem context_13_1210468_1060522 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1210468 ⟨1060522, by decide⟩ :=
  accepted_of_selected 13 1210468 ⟨1060522, by decide⟩ ⟨13, 2, 0, 1060522, 1210468, 1365, 16384⟩
    (by decide) selected_cut_39139

theorem selected_cut_39140 : selected 8 ⟨1060535, by decide⟩
    (prefixPartial 13 1210469) = some ⟨13, 2, 0, 1060535, 1210469, 1049, 16384⟩ := by
  decide +kernel

theorem context_13_1210469_1060535 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1210469 ⟨1060535, by decide⟩ :=
  accepted_of_selected 13 1210469 ⟨1060535, by decide⟩ ⟨13, 2, 0, 1060535, 1210469, 1049, 16384⟩
    (by decide) selected_cut_39140

theorem selected_cut_39141 : selected 8 ⟨1060554, by decide⟩
    (prefixPartial 13 1210470) = some ⟨13, 2, 0, 1060554, 1210470, 1129, 16384⟩ := by
  decide +kernel

theorem context_13_1210470_1060554 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1210470 ⟨1060554, by decide⟩ :=
  accepted_of_selected 13 1210470 ⟨1060554, by decide⟩ ⟨13, 2, 0, 1060554, 1210470, 1129, 16384⟩
    (by decide) selected_cut_39141

theorem selected_cut_39142 : selected 8 ⟨1060559, by decide⟩
    (prefixPartial 13 1210471) = some ⟨13, 2, 0, 1060559, 1210471, 633, 16384⟩ := by
  decide +kernel

theorem context_13_1210471_1060559 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1210471 ⟨1060559, by decide⟩ :=
  accepted_of_selected 13 1210471 ⟨1060559, by decide⟩ ⟨13, 2, 0, 1060559, 1210471, 633, 16384⟩
    (by decide) selected_cut_39142

theorem unmarked_context_12_302617_1060560 : frontier 9 ⟨1060560, by decide⟩
    (prefixCache 12 302617) (prefixPartial 12 302617) = false := by
  decide +kernel

theorem node_context_12_302617_1060560 : EJMOriginalGlobalDAGData.nodes 9 ⟨1060560, by decide⟩ =
    .split (coordinate 12) (![⟨1060522, by decide⟩,⟨1060535, by decide⟩,⟨1060554, by decide⟩,⟨1060559, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_302617_1060560 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302617 ⟨1060560, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 302617
    ⟨1060560, by decide⟩ (by decide) (![⟨1060522, by decide⟩,⟨1060535, by decide⟩,⟨1060554, by decide⟩,⟨1060559, by decide⟩]) unmarked_context_12_302617_1060560 node_context_12_302617_1060560
  intro a
  fin_cases a
  · exact context_13_1210468_1060522
  · exact context_13_1210469_1060535
  · exact context_13_1210470_1060554
  · exact context_13_1210471_1060559

theorem selected_cut_39143 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 302618) = some ⟨12, 1, 0, 893903, 302618, 1, 65536⟩ := by
  decide +kernel

theorem context_12_302618_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302618 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 302618 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 302618, 1, 65536⟩
    (by decide) selected_cut_39143

theorem selected_cut_39144 : selected 8 ⟨1060579, by decide⟩
    (prefixPartial 13 1210476) = some ⟨13, 2, 0, 1060579, 1210476, 1161, 16384⟩ := by
  decide +kernel

theorem context_13_1210476_1060579 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1210476 ⟨1060579, by decide⟩ :=
  accepted_of_selected 13 1210476 ⟨1060579, by decide⟩ ⟨13, 2, 0, 1060579, 1210476, 1161, 16384⟩
    (by decide) selected_cut_39144

theorem selected_cut_39145 : selected 8 ⟨1060598, by decide⟩
    (prefixPartial 13 1210477) = some ⟨13, 2, 0, 1060598, 1210477, 1233, 16384⟩ := by
  decide +kernel

theorem context_13_1210477_1060598 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1210477 ⟨1060598, by decide⟩ :=
  accepted_of_selected 13 1210477 ⟨1060598, by decide⟩ ⟨13, 2, 0, 1060598, 1210477, 1233, 16384⟩
    (by decide) selected_cut_39145

theorem selected_cut_39146 : selected 8 ⟨1060617, by decide⟩
    (prefixPartial 13 1210478) = some ⟨13, 2, 0, 1060617, 1210478, 1125, 16384⟩ := by
  decide +kernel

theorem context_13_1210478_1060617 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1210478 ⟨1060617, by decide⟩ :=
  accepted_of_selected 13 1210478 ⟨1060617, by decide⟩ ⟨13, 2, 0, 1060617, 1210478, 1125, 16384⟩
    (by decide) selected_cut_39146

theorem selected_cut_39147 : selected 8 ⟨1060627, by decide⟩
    (prefixPartial 13 1210479) = some ⟨13, 2, 0, 1060627, 1210479, 665, 16384⟩ := by
  decide +kernel

theorem context_13_1210479_1060627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1210479 ⟨1060627, by decide⟩ :=
  accepted_of_selected 13 1210479 ⟨1060627, by decide⟩ ⟨13, 2, 0, 1060627, 1210479, 665, 16384⟩
    (by decide) selected_cut_39147

theorem unmarked_context_12_302619_1060628 : frontier 9 ⟨1060628, by decide⟩
    (prefixCache 12 302619) (prefixPartial 12 302619) = false := by
  decide +kernel

theorem node_context_12_302619_1060628 : EJMOriginalGlobalDAGData.nodes 9 ⟨1060628, by decide⟩ =
    .split (coordinate 12) (![⟨1060579, by decide⟩,⟨1060598, by decide⟩,⟨1060617, by decide⟩,⟨1060627, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_302619_1060628 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302619 ⟨1060628, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 302619
    ⟨1060628, by decide⟩ (by decide) (![⟨1060579, by decide⟩,⟨1060598, by decide⟩,⟨1060617, by decide⟩,⟨1060627, by decide⟩]) unmarked_context_12_302619_1060628 node_context_12_302619_1060628
  intro a
  fin_cases a
  · exact context_13_1210476_1060579
  · exact context_13_1210477_1060598
  · exact context_13_1210478_1060617
  · exact context_13_1210479_1060627

theorem unmarked_context_11_75654_1060629 : frontier 10 ⟨1060629, by decide⟩
    (prefixCache 11 75654) (prefixPartial 11 75654) = false := by
  decide +kernel

theorem node_context_11_75654_1060629 : EJMOriginalGlobalDAGData.nodes 10 ⟨1060629, by decide⟩ =
    .split (coordinate 11) (![⟨1060498, by decide⟩,⟨1060560, by decide⟩,⟨893903, by decide⟩,⟨1060628, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75654_1060629 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75654 ⟨1060629, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75654
    ⟨1060629, by decide⟩ (by decide) (![⟨1060498, by decide⟩,⟨1060560, by decide⟩,⟨893903, by decide⟩,⟨1060628, by decide⟩]) unmarked_context_11_75654_1060629 node_context_11_75654_1060629
  intro a
  fin_cases a
  · exact context_12_302616_1060498
  · exact context_12_302617_1060560
  · exact context_12_302618_893903
  · exact context_12_302619_1060628

theorem selected_cut_39148 : selected 9 ⟨1060689, by decide⟩
    (prefixPartial 12 302620) = some ⟨12, 2, 0, 1060689, 302620, 3749, 65536⟩ := by
  decide +kernel

theorem context_12_302620_1060689 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302620 ⟨1060689, by decide⟩ :=
  accepted_of_selected 12 302620 ⟨1060689, by decide⟩ ⟨12, 2, 0, 1060689, 302620, 3749, 65536⟩
    (by decide) selected_cut_39148

theorem selected_cut_39149 : selected 8 ⟨1060709, by decide⟩
    (prefixPartial 13 1210484) = some ⟨13, 2, 0, 1060709, 1210484, 1165, 16384⟩ := by
  decide +kernel

theorem context_13_1210484_1060709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1210484 ⟨1060709, by decide⟩ :=
  accepted_of_selected 13 1210484 ⟨1060709, by decide⟩ ⟨13, 2, 0, 1060709, 1210484, 1165, 16384⟩
    (by decide) selected_cut_39149

theorem selected_cut_39150 : selected 8 ⟨1060724, by decide⟩
    (prefixPartial 13 1210485) = some ⟨13, 2, 0, 1060724, 1210485, 1061, 16384⟩ := by
  decide +kernel

theorem context_13_1210485_1060724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1210485 ⟨1060724, by decide⟩ :=
  accepted_of_selected 13 1210485 ⟨1060724, by decide⟩ ⟨13, 2, 0, 1060724, 1210485, 1061, 16384⟩
    (by decide) selected_cut_39150

theorem selected_cut_39151 : selected 8 ⟨1060744, by decide⟩
    (prefixPartial 13 1210486) = some ⟨13, 2, 0, 1060744, 1210486, 1197, 16384⟩ := by
  decide +kernel

theorem context_13_1210486_1060744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1210486 ⟨1060744, by decide⟩ :=
  accepted_of_selected 13 1210486 ⟨1060744, by decide⟩ ⟨13, 2, 0, 1060744, 1210486, 1197, 16384⟩
    (by decide) selected_cut_39151

theorem selected_cut_39152 : selected 8 ⟨1060752, by decide⟩
    (prefixPartial 13 1210487) = some ⟨13, 2, 0, 1060752, 1210487, 745, 16384⟩ := by
  decide +kernel

theorem context_13_1210487_1060752 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1210487 ⟨1060752, by decide⟩ :=
  accepted_of_selected 13 1210487 ⟨1060752, by decide⟩ ⟨13, 2, 0, 1060752, 1210487, 745, 16384⟩
    (by decide) selected_cut_39152

theorem unmarked_context_12_302621_1060753 : frontier 9 ⟨1060753, by decide⟩
    (prefixCache 12 302621) (prefixPartial 12 302621) = false := by
  decide +kernel

theorem node_context_12_302621_1060753 : EJMOriginalGlobalDAGData.nodes 9 ⟨1060753, by decide⟩ =
    .split (coordinate 12) (![⟨1060709, by decide⟩,⟨1060724, by decide⟩,⟨1060744, by decide⟩,⟨1060752, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_302621_1060753 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302621 ⟨1060753, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 302621
    ⟨1060753, by decide⟩ (by decide) (![⟨1060709, by decide⟩,⟨1060724, by decide⟩,⟨1060744, by decide⟩,⟨1060752, by decide⟩]) unmarked_context_12_302621_1060753 node_context_12_302621_1060753
  intro a
  fin_cases a
  · exact context_13_1210484_1060709
  · exact context_13_1210485_1060724
  · exact context_13_1210486_1060744
  · exact context_13_1210487_1060752

theorem selected_cut_39153 : selected 9 ⟨1060806, by decide⟩
    (prefixPartial 12 302622) = some ⟨12, 2, 0, 1060806, 302622, 3693, 65536⟩ := by
  decide +kernel

theorem context_12_302622_1060806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302622 ⟨1060806, by decide⟩ :=
  accepted_of_selected 12 302622 ⟨1060806, by decide⟩ ⟨12, 2, 0, 1060806, 302622, 3693, 65536⟩
    (by decide) selected_cut_39153

theorem selected_cut_39154 : selected 9 ⟨1060862, by decide⟩
    (prefixPartial 12 302623) = some ⟨12, 2, 0, 1060862, 302623, 4041, 65536⟩ := by
  decide +kernel

theorem context_12_302623_1060862 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302623 ⟨1060862, by decide⟩ :=
  accepted_of_selected 12 302623 ⟨1060862, by decide⟩ ⟨12, 2, 0, 1060862, 302623, 4041, 65536⟩
    (by decide) selected_cut_39154

theorem unmarked_context_11_75655_1060863 : frontier 10 ⟨1060863, by decide⟩
    (prefixCache 11 75655) (prefixPartial 11 75655) = false := by
  decide +kernel

theorem node_context_11_75655_1060863 : EJMOriginalGlobalDAGData.nodes 10 ⟨1060863, by decide⟩ =
    .split (coordinate 11) (![⟨1060689, by decide⟩,⟨1060753, by decide⟩,⟨1060806, by decide⟩,⟨1060862, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75655_1060863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75655 ⟨1060863, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75655
    ⟨1060863, by decide⟩ (by decide) (![⟨1060689, by decide⟩,⟨1060753, by decide⟩,⟨1060806, by decide⟩,⟨1060862, by decide⟩]) unmarked_context_11_75655_1060863 node_context_11_75655_1060863
  intro a
  fin_cases a
  · exact context_12_302620_1060689
  · exact context_12_302621_1060753
  · exact context_12_302622_1060806
  · exact context_12_302623_1060862

theorem unmarked_context_10_18913_1060864 : frontier 11 ⟨1060864, by decide⟩
    (prefixCache 10 18913) (prefixPartial 10 18913) = false := by
  decide +kernel

theorem node_context_10_18913_1060864 : EJMOriginalGlobalDAGData.nodes 11 ⟨1060864, by decide⟩ =
    .split (coordinate 10) (![⟨1060194, by decide⟩,⟨1060442, by decide⟩,⟨1060629, by decide⟩,⟨1060863, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18913_1060864 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18913 ⟨1060864, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18913
    ⟨1060864, by decide⟩ (by decide) (![⟨1060194, by decide⟩,⟨1060442, by decide⟩,⟨1060629, by decide⟩,⟨1060863, by decide⟩]) unmarked_context_10_18913_1060864 node_context_10_18913_1060864
  intro a
  fin_cases a
  · exact context_11_75652_1060194
  · exact context_11_75653_1060442
  · exact context_11_75654_1060629
  · exact context_11_75655_1060863

theorem selected_cut_39155 : selected 9 ⟨994572, by decide⟩
    (prefixPartial 12 302624) = some ⟨12, 1, 0, 994572, 302624, 1, 65536⟩ := by
  decide +kernel

theorem context_12_302624_994572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302624 ⟨994572, by decide⟩ :=
  accepted_of_selected 12 302624 ⟨994572, by decide⟩ ⟨12, 1, 0, 994572, 302624, 1, 65536⟩
    (by decide) selected_cut_39155

theorem selected_cut_39156 : selected 9 ⟨1060946, by decide⟩
    (prefixPartial 12 302625) = some ⟨12, 2, 0, 1060946, 302625, 4037, 65536⟩ := by
  decide +kernel

theorem context_12_302625_1060946 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302625 ⟨1060946, by decide⟩ :=
  accepted_of_selected 12 302625 ⟨1060946, by decide⟩ ⟨12, 2, 0, 1060946, 302625, 4037, 65536⟩
    (by decide) selected_cut_39156

theorem selected_cut_39157 : selected 9 ⟨1061001, by decide⟩
    (prefixPartial 12 302626) = some ⟨12, 2, 0, 1061001, 302626, 3109, 65536⟩ := by
  decide +kernel

theorem context_12_302626_1061001 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302626 ⟨1061001, by decide⟩ :=
  accepted_of_selected 12 302626 ⟨1061001, by decide⟩ ⟨12, 2, 0, 1061001, 302626, 3109, 65536⟩
    (by decide) selected_cut_39157

theorem selected_cut_39158 : selected 9 ⟨1061056, by decide⟩
    (prefixPartial 12 302627) = some ⟨12, 2, 0, 1061056, 302627, 3749, 65536⟩ := by
  decide +kernel

theorem context_12_302627_1061056 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302627 ⟨1061056, by decide⟩ :=
  accepted_of_selected 12 302627 ⟨1061056, by decide⟩ ⟨12, 2, 0, 1061056, 302627, 3749, 65536⟩
    (by decide) selected_cut_39158

theorem unmarked_context_11_75656_1061057 : frontier 10 ⟨1061057, by decide⟩
    (prefixCache 11 75656) (prefixPartial 11 75656) = false := by
  decide +kernel

theorem node_context_11_75656_1061057 : EJMOriginalGlobalDAGData.nodes 10 ⟨1061057, by decide⟩ =
    .split (coordinate 11) (![⟨994572, by decide⟩,⟨1060946, by decide⟩,⟨1061001, by decide⟩,⟨1061056, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75656_1061057 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75656 ⟨1061057, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75656
    ⟨1061057, by decide⟩ (by decide) (![⟨994572, by decide⟩,⟨1060946, by decide⟩,⟨1061001, by decide⟩,⟨1061056, by decide⟩]) unmarked_context_11_75656_1061057 node_context_11_75656_1061057
  intro a
  fin_cases a
  · exact context_12_302624_994572
  · exact context_12_302625_1060946
  · exact context_12_302626_1061001
  · exact context_12_302627_1061056

theorem selected_cut_39159 : selected 9 ⟨1061120, by decide⟩
    (prefixPartial 12 302628) = some ⟨12, 2, 0, 1061120, 302628, 3545, 65536⟩ := by
  decide +kernel

theorem context_12_302628_1061120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302628 ⟨1061120, by decide⟩ :=
  accepted_of_selected 12 302628 ⟨1061120, by decide⟩ ⟨12, 2, 0, 1061120, 302628, 3545, 65536⟩
    (by decide) selected_cut_39159

theorem selected_cut_39160 : selected 9 ⟨1061189, by decide⟩
    (prefixPartial 12 302629) = some ⟨12, 2, 0, 1061189, 302629, 4065, 65536⟩ := by
  decide +kernel

theorem context_12_302629_1061189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302629 ⟨1061189, by decide⟩ :=
  accepted_of_selected 12 302629 ⟨1061189, by decide⟩ ⟨12, 2, 0, 1061189, 302629, 4065, 65536⟩
    (by decide) selected_cut_39160

theorem selected_cut_39161 : selected 9 ⟨1061234, by decide⟩
    (prefixPartial 12 302630) = some ⟨12, 2, 0, 1061234, 302630, 3065, 65536⟩ := by
  decide +kernel

theorem context_12_302630_1061234 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302630 ⟨1061234, by decide⟩ :=
  accepted_of_selected 12 302630 ⟨1061234, by decide⟩ ⟨12, 2, 0, 1061234, 302630, 3065, 65536⟩
    (by decide) selected_cut_39161

theorem selected_cut_39162 : selected 9 ⟨1061297, by decide⟩
    (prefixPartial 12 302631) = some ⟨12, 2, 0, 1061297, 302631, 3801, 65536⟩ := by
  decide +kernel

theorem context_12_302631_1061297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302631 ⟨1061297, by decide⟩ :=
  accepted_of_selected 12 302631 ⟨1061297, by decide⟩ ⟨12, 2, 0, 1061297, 302631, 3801, 65536⟩
    (by decide) selected_cut_39162

theorem unmarked_context_11_75657_1061298 : frontier 10 ⟨1061298, by decide⟩
    (prefixCache 11 75657) (prefixPartial 11 75657) = false := by
  decide +kernel

theorem node_context_11_75657_1061298 : EJMOriginalGlobalDAGData.nodes 10 ⟨1061298, by decide⟩ =
    .split (coordinate 11) (![⟨1061120, by decide⟩,⟨1061189, by decide⟩,⟨1061234, by decide⟩,⟨1061297, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75657_1061298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75657 ⟨1061298, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75657
    ⟨1061298, by decide⟩ (by decide) (![⟨1061120, by decide⟩,⟨1061189, by decide⟩,⟨1061234, by decide⟩,⟨1061297, by decide⟩]) unmarked_context_11_75657_1061298 node_context_11_75657_1061298
  intro a
  fin_cases a
  · exact context_12_302628_1061120
  · exact context_12_302629_1061189
  · exact context_12_302630_1061234
  · exact context_12_302631_1061297

theorem selected_cut_39163 : selected 9 ⟨1061352, by decide⟩
    (prefixPartial 12 302632) = some ⟨12, 2, 0, 1061352, 302632, 3357, 65536⟩ := by
  decide +kernel

theorem context_12_302632_1061352 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302632 ⟨1061352, by decide⟩ :=
  accepted_of_selected 12 302632 ⟨1061352, by decide⟩ ⟨12, 2, 0, 1061352, 302632, 3357, 65536⟩
    (by decide) selected_cut_39163

theorem selected_cut_39164 : selected 9 ⟨1061418, by decide⟩
    (prefixPartial 12 302633) = some ⟨12, 2, 0, 1061418, 302633, 4053, 65536⟩ := by
  decide +kernel

theorem context_12_302633_1061418 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302633 ⟨1061418, by decide⟩ :=
  accepted_of_selected 12 302633 ⟨1061418, by decide⟩ ⟨12, 2, 0, 1061418, 302633, 4053, 65536⟩
    (by decide) selected_cut_39164

theorem selected_cut_39165 : selected 9 ⟨661672, by decide⟩
    (prefixPartial 12 302634) = some ⟨12, 1, 0, 661672, 302634, 1, 65536⟩ := by
  decide +kernel

theorem context_12_302634_661672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302634 ⟨661672, by decide⟩ :=
  accepted_of_selected 12 302634 ⟨661672, by decide⟩ ⟨12, 1, 0, 661672, 302634, 1, 65536⟩
    (by decide) selected_cut_39165

theorem selected_cut_39166 : selected 9 ⟨1061478, by decide⟩
    (prefixPartial 12 302635) = some ⟨12, 2, 0, 1061478, 302635, 3921, 65536⟩ := by
  decide +kernel

theorem context_12_302635_1061478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302635 ⟨1061478, by decide⟩ :=
  accepted_of_selected 12 302635 ⟨1061478, by decide⟩ ⟨12, 2, 0, 1061478, 302635, 3921, 65536⟩
    (by decide) selected_cut_39166

theorem unmarked_context_11_75658_1061479 : frontier 10 ⟨1061479, by decide⟩
    (prefixCache 11 75658) (prefixPartial 11 75658) = false := by
  decide +kernel

theorem node_context_11_75658_1061479 : EJMOriginalGlobalDAGData.nodes 10 ⟨1061479, by decide⟩ =
    .split (coordinate 11) (![⟨1061352, by decide⟩,⟨1061418, by decide⟩,⟨661672, by decide⟩,⟨1061478, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75658_1061479 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75658 ⟨1061479, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75658
    ⟨1061479, by decide⟩ (by decide) (![⟨1061352, by decide⟩,⟨1061418, by decide⟩,⟨661672, by decide⟩,⟨1061478, by decide⟩]) unmarked_context_11_75658_1061479 node_context_11_75658_1061479
  intro a
  fin_cases a
  · exact context_12_302632_1061352
  · exact context_12_302633_1061418
  · exact context_12_302634_661672
  · exact context_12_302635_1061478

theorem selected_cut_39167 : selected 9 ⟨1061533, by decide⟩
    (prefixPartial 12 302636) = some ⟨12, 2, 0, 1061533, 302636, 3337, 65536⟩ := by
  decide +kernel

theorem context_12_302636_1061533 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302636 ⟨1061533, by decide⟩ :=
  accepted_of_selected 12 302636 ⟨1061533, by decide⟩ ⟨12, 2, 0, 1061533, 302636, 3337, 65536⟩
    (by decide) selected_cut_39167

theorem selected_cut_39168 : selected 9 ⟨1061601, by decide⟩
    (prefixPartial 12 302637) = some ⟨12, 2, 0, 1061601, 302637, 3909, 65536⟩ := by
  decide +kernel

theorem context_12_302637_1061601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302637 ⟨1061601, by decide⟩ :=
  accepted_of_selected 12 302637 ⟨1061601, by decide⟩ ⟨12, 2, 0, 1061601, 302637, 3909, 65536⟩
    (by decide) selected_cut_39168

theorem selected_cut_39169 : selected 9 ⟨1061644, by decide⟩
    (prefixPartial 12 302638) = some ⟨12, 2, 0, 1061644, 302638, 3149, 65536⟩ := by
  decide +kernel

theorem context_12_302638_1061644 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302638 ⟨1061644, by decide⟩ :=
  accepted_of_selected 12 302638 ⟨1061644, by decide⟩ ⟨12, 2, 0, 1061644, 302638, 3149, 65536⟩
    (by decide) selected_cut_39169

theorem selected_cut_39170 : selected 9 ⟨1061703, by decide⟩
    (prefixPartial 12 302639) = some ⟨12, 2, 0, 1061703, 302639, 3637, 65536⟩ := by
  decide +kernel

theorem context_12_302639_1061703 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302639 ⟨1061703, by decide⟩ :=
  accepted_of_selected 12 302639 ⟨1061703, by decide⟩ ⟨12, 2, 0, 1061703, 302639, 3637, 65536⟩
    (by decide) selected_cut_39170

theorem unmarked_context_11_75659_1061704 : frontier 10 ⟨1061704, by decide⟩
    (prefixCache 11 75659) (prefixPartial 11 75659) = false := by
  decide +kernel

theorem node_context_11_75659_1061704 : EJMOriginalGlobalDAGData.nodes 10 ⟨1061704, by decide⟩ =
    .split (coordinate 11) (![⟨1061533, by decide⟩,⟨1061601, by decide⟩,⟨1061644, by decide⟩,⟨1061703, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75659_1061704 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75659 ⟨1061704, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75659
    ⟨1061704, by decide⟩ (by decide) (![⟨1061533, by decide⟩,⟨1061601, by decide⟩,⟨1061644, by decide⟩,⟨1061703, by decide⟩]) unmarked_context_11_75659_1061704 node_context_11_75659_1061704
  intro a
  fin_cases a
  · exact context_12_302636_1061533
  · exact context_12_302637_1061601
  · exact context_12_302638_1061644
  · exact context_12_302639_1061703

theorem unmarked_context_10_18914_1061705 : frontier 11 ⟨1061705, by decide⟩
    (prefixCache 10 18914) (prefixPartial 10 18914) = false := by
  decide +kernel

theorem node_context_10_18914_1061705 : EJMOriginalGlobalDAGData.nodes 11 ⟨1061705, by decide⟩ =
    .split (coordinate 10) (![⟨1061057, by decide⟩,⟨1061298, by decide⟩,⟨1061479, by decide⟩,⟨1061704, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18914_1061705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18914 ⟨1061705, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18914
    ⟨1061705, by decide⟩ (by decide) (![⟨1061057, by decide⟩,⟨1061298, by decide⟩,⟨1061479, by decide⟩,⟨1061704, by decide⟩]) unmarked_context_10_18914_1061705 node_context_10_18914_1061705
  intro a
  fin_cases a
  · exact context_11_75656_1061057
  · exact context_11_75657_1061298
  · exact context_11_75658_1061479
  · exact context_11_75659_1061704

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
