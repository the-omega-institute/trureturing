/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover209
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_20164 : selected 9 ⟨516119, by decide⟩
    (prefixPartial 12 72574) = some ⟨12, 2, 0, 516119, 72574, 3049, 65536⟩ := by
  decide +kernel

theorem context_12_72574_516119 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72574 ⟨516119, by decide⟩ :=
  accepted_of_selected 12 72574 ⟨516119, by decide⟩ ⟨12, 2, 0, 516119, 72574, 3049, 65536⟩
    (by decide) selected_cut_20164

theorem selected_cut_20165 : selected 9 ⟨512556, by decide⟩
    (prefixPartial 12 72575) = some ⟨12, 1, 0, 512556, 72575, 1, 65536⟩ := by
  decide +kernel

theorem context_12_72575_512556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72575 ⟨512556, by decide⟩ :=
  accepted_of_selected 12 72575 ⟨512556, by decide⟩ ⟨12, 1, 0, 512556, 72575, 1, 65536⟩
    (by decide) selected_cut_20165

theorem unmarked_context_11_18143_516120 : frontier 10 ⟨516120, by decide⟩
    (prefixCache 11 18143) (prefixPartial 11 18143) = false := by
  decide +kernel

theorem node_context_11_18143_516120 : EJMOriginalGlobalDAGData.nodes 10 ⟨516120, by decide⟩ =
    .split (coordinate 11) (![⟨516051, by decide⟩,⟨516084, by decide⟩,⟨516119, by decide⟩,⟨512556, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18143_516120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18143 ⟨516120, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18143
    ⟨516120, by decide⟩ (by decide) (![⟨516051, by decide⟩,⟨516084, by decide⟩,⟨516119, by decide⟩,⟨512556, by decide⟩]) unmarked_context_11_18143_516120 node_context_11_18143_516120
  intro a
  fin_cases a
  · exact context_12_72572_516051
  · exact context_12_72573_516084
  · exact context_12_72574_516119
  · exact context_12_72575_512556

theorem unmarked_context_10_4535_516121 : frontier 11 ⟨516121, by decide⟩
    (prefixCache 10 4535) (prefixPartial 10 4535) = false := by
  decide +kernel

theorem node_context_10_4535_516121 : EJMOriginalGlobalDAGData.nodes 11 ⟨516121, by decide⟩ =
    .split (coordinate 10) (![⟨515630, by decide⟩,⟨515836, by decide⟩,⟨516020, by decide⟩,⟨516120, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4535_516121 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4535 ⟨516121, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4535
    ⟨516121, by decide⟩ (by decide) (![⟨515630, by decide⟩,⟨515836, by decide⟩,⟨516020, by decide⟩,⟨516120, by decide⟩]) unmarked_context_10_4535_516121 node_context_10_4535_516121
  intro a
  fin_cases a
  · exact context_11_18140_515630
  · exact context_11_18141_515836
  · exact context_11_18142_516020
  · exact context_11_18143_516120

theorem unmarked_context_9_1133_516122 : frontier 12 ⟨516122, by decide⟩
    (prefixCache 9 1133) (prefixPartial 9 1133) = false := by
  decide +kernel

theorem node_context_9_1133_516122 : EJMOriginalGlobalDAGData.nodes 12 ⟨516122, by decide⟩ =
    .split (coordinate 9) (![⟨513580, by decide⟩,⟨514532, by decide⟩,⟨515463, by decide⟩,⟨516121, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1133_516122 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1133 ⟨516122, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1133
    ⟨516122, by decide⟩ (by decide) (![⟨513580, by decide⟩,⟨514532, by decide⟩,⟨515463, by decide⟩,⟨516121, by decide⟩]) unmarked_context_9_1133_516122 node_context_9_1133_516122
  intro a
  fin_cases a
  · exact context_10_4532_513580
  · exact context_10_4533_514532
  · exact context_10_4534_515463
  · exact context_10_4535_516121

theorem selected_cut_20166 : selected 9 ⟨516144, by decide⟩
    (prefixPartial 12 72576) = some ⟨12, 2, 0, 516144, 72576, 2125, 65536⟩ := by
  decide +kernel

theorem context_12_72576_516144 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72576 ⟨516144, by decide⟩ :=
  accepted_of_selected 12 72576 ⟨516144, by decide⟩ ⟨12, 2, 0, 516144, 72576, 2125, 65536⟩
    (by decide) selected_cut_20166

theorem selected_cut_20167 : selected 9 ⟨516177, by decide⟩
    (prefixPartial 12 72577) = some ⟨12, 2, 0, 516177, 72577, 2641, 65536⟩ := by
  decide +kernel

theorem context_12_72577_516177 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72577 ⟨516177, by decide⟩ :=
  accepted_of_selected 12 72577 ⟨516177, by decide⟩ ⟨12, 2, 0, 516177, 72577, 2641, 65536⟩
    (by decide) selected_cut_20167

theorem selected_cut_20168 : selected 9 ⟨516223, by decide⟩
    (prefixPartial 12 72578) = some ⟨12, 2, 0, 516223, 72578, 2905, 65536⟩ := by
  decide +kernel

theorem context_12_72578_516223 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72578 ⟨516223, by decide⟩ :=
  accepted_of_selected 12 72578 ⟨516223, by decide⟩ ⟨12, 2, 0, 516223, 72578, 2905, 65536⟩
    (by decide) selected_cut_20168

theorem selected_cut_20169 : selected 9 ⟨516246, by decide⟩
    (prefixPartial 12 72579) = some ⟨12, 2, 0, 516246, 72579, 2649, 65536⟩ := by
  decide +kernel

theorem context_12_72579_516246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72579 ⟨516246, by decide⟩ :=
  accepted_of_selected 12 72579 ⟨516246, by decide⟩ ⟨12, 2, 0, 516246, 72579, 2649, 65536⟩
    (by decide) selected_cut_20169

theorem unmarked_context_11_18144_516247 : frontier 10 ⟨516247, by decide⟩
    (prefixCache 11 18144) (prefixPartial 11 18144) = false := by
  decide +kernel

theorem node_context_11_18144_516247 : EJMOriginalGlobalDAGData.nodes 10 ⟨516247, by decide⟩ =
    .split (coordinate 11) (![⟨516144, by decide⟩,⟨516177, by decide⟩,⟨516223, by decide⟩,⟨516246, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18144_516247 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18144 ⟨516247, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18144
    ⟨516247, by decide⟩ (by decide) (![⟨516144, by decide⟩,⟨516177, by decide⟩,⟨516223, by decide⟩,⟨516246, by decide⟩]) unmarked_context_11_18144_516247 node_context_11_18144_516247
  intro a
  fin_cases a
  · exact context_12_72576_516144
  · exact context_12_72577_516177
  · exact context_12_72578_516223
  · exact context_12_72579_516246

theorem selected_cut_20170 : selected 9 ⟨516272, by decide⟩
    (prefixPartial 12 72580) = some ⟨12, 2, 0, 516272, 72580, 2229, 65536⟩ := by
  decide +kernel

theorem context_12_72580_516272 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72580 ⟨516272, by decide⟩ :=
  accepted_of_selected 12 72580 ⟨516272, by decide⟩ ⟨12, 2, 0, 516272, 72580, 2229, 65536⟩
    (by decide) selected_cut_20170

theorem selected_cut_20171 : selected 9 ⟨516299, by decide⟩
    (prefixPartial 12 72581) = some ⟨12, 2, 0, 516299, 72581, 2329, 65536⟩ := by
  decide +kernel

theorem context_12_72581_516299 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72581 ⟨516299, by decide⟩ :=
  accepted_of_selected 12 72581 ⟨516299, by decide⟩ ⟨12, 2, 0, 516299, 72581, 2329, 65536⟩
    (by decide) selected_cut_20171

theorem selected_cut_20172 : selected 9 ⟨516328, by decide⟩
    (prefixPartial 12 72582) = some ⟨12, 2, 0, 516328, 72582, 2697, 65536⟩ := by
  decide +kernel

theorem context_12_72582_516328 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72582 ⟨516328, by decide⟩ :=
  accepted_of_selected 12 72582 ⟨516328, by decide⟩ ⟨12, 2, 0, 516328, 72582, 2697, 65536⟩
    (by decide) selected_cut_20172

theorem selected_cut_20173 : selected 9 ⟨516352, by decide⟩
    (prefixPartial 12 72583) = some ⟨12, 2, 0, 516352, 72583, 2413, 65536⟩ := by
  decide +kernel

theorem context_12_72583_516352 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72583 ⟨516352, by decide⟩ :=
  accepted_of_selected 12 72583 ⟨516352, by decide⟩ ⟨12, 2, 0, 516352, 72583, 2413, 65536⟩
    (by decide) selected_cut_20173

theorem unmarked_context_11_18145_516353 : frontier 10 ⟨516353, by decide⟩
    (prefixCache 11 18145) (prefixPartial 11 18145) = false := by
  decide +kernel

theorem node_context_11_18145_516353 : EJMOriginalGlobalDAGData.nodes 10 ⟨516353, by decide⟩ =
    .split (coordinate 11) (![⟨516272, by decide⟩,⟨516299, by decide⟩,⟨516328, by decide⟩,⟨516352, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18145_516353 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18145 ⟨516353, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18145
    ⟨516353, by decide⟩ (by decide) (![⟨516272, by decide⟩,⟨516299, by decide⟩,⟨516328, by decide⟩,⟨516352, by decide⟩]) unmarked_context_11_18145_516353 node_context_11_18145_516353
  intro a
  fin_cases a
  · exact context_12_72580_516272
  · exact context_12_72581_516299
  · exact context_12_72582_516328
  · exact context_12_72583_516352

theorem selected_cut_20174 : selected 9 ⟨516372, by decide⟩
    (prefixPartial 12 72584) = some ⟨12, 2, 0, 516372, 72584, 1977, 65536⟩ := by
  decide +kernel

theorem context_12_72584_516372 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72584 ⟨516372, by decide⟩ :=
  accepted_of_selected 12 72584 ⟨516372, by decide⟩ ⟨12, 2, 0, 516372, 72584, 1977, 65536⟩
    (by decide) selected_cut_20174

theorem selected_cut_20175 : selected 9 ⟨516396, by decide⟩
    (prefixPartial 12 72585) = some ⟨12, 2, 0, 516396, 72585, 2201, 65536⟩ := by
  decide +kernel

theorem context_12_72585_516396 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72585 ⟨516396, by decide⟩ :=
  accepted_of_selected 12 72585 ⟨516396, by decide⟩ ⟨12, 2, 0, 516396, 72585, 2201, 65536⟩
    (by decide) selected_cut_20175

theorem selected_cut_20176 : selected 9 ⟨516424, by decide⟩
    (prefixPartial 12 72586) = some ⟨12, 2, 0, 516424, 72586, 2417, 65536⟩ := by
  decide +kernel

theorem context_12_72586_516424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72586 ⟨516424, by decide⟩ :=
  accepted_of_selected 12 72586 ⟨516424, by decide⟩ ⟨12, 2, 0, 516424, 72586, 2417, 65536⟩
    (by decide) selected_cut_20176

theorem selected_cut_20177 : selected 9 ⟨516446, by decide⟩
    (prefixPartial 12 72587) = some ⟨12, 2, 0, 516446, 72587, 2205, 65536⟩ := by
  decide +kernel

theorem context_12_72587_516446 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72587 ⟨516446, by decide⟩ :=
  accepted_of_selected 12 72587 ⟨516446, by decide⟩ ⟨12, 2, 0, 516446, 72587, 2205, 65536⟩
    (by decide) selected_cut_20177

theorem unmarked_context_11_18146_516447 : frontier 10 ⟨516447, by decide⟩
    (prefixCache 11 18146) (prefixPartial 11 18146) = false := by
  decide +kernel

theorem node_context_11_18146_516447 : EJMOriginalGlobalDAGData.nodes 10 ⟨516447, by decide⟩ =
    .split (coordinate 11) (![⟨516372, by decide⟩,⟨516396, by decide⟩,⟨516424, by decide⟩,⟨516446, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18146_516447 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18146 ⟨516447, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18146
    ⟨516447, by decide⟩ (by decide) (![⟨516372, by decide⟩,⟨516396, by decide⟩,⟨516424, by decide⟩,⟨516446, by decide⟩]) unmarked_context_11_18146_516447 node_context_11_18146_516447
  intro a
  fin_cases a
  · exact context_12_72584_516372
  · exact context_12_72585_516396
  · exact context_12_72586_516424
  · exact context_12_72587_516446

theorem selected_cut_20178 : selected 9 ⟨516469, by decide⟩
    (prefixPartial 12 72588) = some ⟨12, 2, 0, 516469, 72588, 1977, 65536⟩ := by
  decide +kernel

theorem context_12_72588_516469 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72588 ⟨516469, by decide⟩ :=
  accepted_of_selected 12 72588 ⟨516469, by decide⟩ ⟨12, 2, 0, 516469, 72588, 1977, 65536⟩
    (by decide) selected_cut_20178

theorem selected_cut_20179 : selected 9 ⟨516492, by decide⟩
    (prefixPartial 12 72589) = some ⟨12, 2, 0, 516492, 72589, 2177, 65536⟩ := by
  decide +kernel

theorem context_12_72589_516492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72589 ⟨516492, by decide⟩ :=
  accepted_of_selected 12 72589 ⟨516492, by decide⟩ ⟨12, 2, 0, 516492, 72589, 2177, 65536⟩
    (by decide) selected_cut_20179

theorem selected_cut_20180 : selected 9 ⟨516517, by decide⟩
    (prefixPartial 12 72590) = some ⟨12, 2, 0, 516517, 72590, 2413, 65536⟩ := by
  decide +kernel

theorem context_12_72590_516517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72590 ⟨516517, by decide⟩ :=
  accepted_of_selected 12 72590 ⟨516517, by decide⟩ ⟨12, 2, 0, 516517, 72590, 2413, 65536⟩
    (by decide) selected_cut_20180

theorem selected_cut_20181 : selected 9 ⟨516568, by decide⟩
    (prefixPartial 12 72591) = some ⟨12, 2, 0, 516568, 72591, 3245, 65536⟩ := by
  decide +kernel

theorem context_12_72591_516568 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72591 ⟨516568, by decide⟩ :=
  accepted_of_selected 12 72591 ⟨516568, by decide⟩ ⟨12, 2, 0, 516568, 72591, 3245, 65536⟩
    (by decide) selected_cut_20181

theorem unmarked_context_11_18147_516569 : frontier 10 ⟨516569, by decide⟩
    (prefixCache 11 18147) (prefixPartial 11 18147) = false := by
  decide +kernel

theorem node_context_11_18147_516569 : EJMOriginalGlobalDAGData.nodes 10 ⟨516569, by decide⟩ =
    .split (coordinate 11) (![⟨516469, by decide⟩,⟨516492, by decide⟩,⟨516517, by decide⟩,⟨516568, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18147_516569 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18147 ⟨516569, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18147
    ⟨516569, by decide⟩ (by decide) (![⟨516469, by decide⟩,⟨516492, by decide⟩,⟨516517, by decide⟩,⟨516568, by decide⟩]) unmarked_context_11_18147_516569 node_context_11_18147_516569
  intro a
  fin_cases a
  · exact context_12_72588_516469
  · exact context_12_72589_516492
  · exact context_12_72590_516517
  · exact context_12_72591_516568

theorem unmarked_context_10_4536_516570 : frontier 11 ⟨516570, by decide⟩
    (prefixCache 10 4536) (prefixPartial 10 4536) = false := by
  decide +kernel

theorem node_context_10_4536_516570 : EJMOriginalGlobalDAGData.nodes 11 ⟨516570, by decide⟩ =
    .split (coordinate 10) (![⟨516247, by decide⟩,⟨516353, by decide⟩,⟨516447, by decide⟩,⟨516569, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4536_516570 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4536 ⟨516570, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4536
    ⟨516570, by decide⟩ (by decide) (![⟨516247, by decide⟩,⟨516353, by decide⟩,⟨516447, by decide⟩,⟨516569, by decide⟩]) unmarked_context_10_4536_516570 node_context_10_4536_516570
  intro a
  fin_cases a
  · exact context_11_18144_516247
  · exact context_11_18145_516353
  · exact context_11_18146_516447
  · exact context_11_18147_516569

theorem selected_cut_20182 : selected 9 ⟨516592, by decide⟩
    (prefixPartial 12 72592) = some ⟨12, 2, 0, 516592, 72592, 1845, 65536⟩ := by
  decide +kernel

theorem context_12_72592_516592 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72592 ⟨516592, by decide⟩ :=
  accepted_of_selected 12 72592 ⟨516592, by decide⟩ ⟨12, 2, 0, 516592, 72592, 1845, 65536⟩
    (by decide) selected_cut_20182

theorem selected_cut_20183 : selected 9 ⟨516627, by decide⟩
    (prefixPartial 12 72593) = some ⟨12, 2, 0, 516627, 72593, 2165, 65536⟩ := by
  decide +kernel

theorem context_12_72593_516627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72593 ⟨516627, by decide⟩ :=
  accepted_of_selected 12 72593 ⟨516627, by decide⟩ ⟨12, 2, 0, 516627, 72593, 2165, 65536⟩
    (by decide) selected_cut_20183

theorem selected_cut_20184 : selected 9 ⟨516669, by decide⟩
    (prefixPartial 12 72594) = some ⟨12, 2, 0, 516669, 72594, 2421, 65536⟩ := by
  decide +kernel

theorem context_12_72594_516669 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72594 ⟨516669, by decide⟩ :=
  accepted_of_selected 12 72594 ⟨516669, by decide⟩ ⟨12, 2, 0, 516669, 72594, 2421, 65536⟩
    (by decide) selected_cut_20184

theorem selected_cut_20185 : selected 9 ⟨516692, by decide⟩
    (prefixPartial 12 72595) = some ⟨12, 2, 0, 516692, 72595, 1981, 65536⟩ := by
  decide +kernel

theorem context_12_72595_516692 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72595 ⟨516692, by decide⟩ :=
  accepted_of_selected 12 72595 ⟨516692, by decide⟩ ⟨12, 2, 0, 516692, 72595, 1981, 65536⟩
    (by decide) selected_cut_20185

theorem unmarked_context_11_18148_516693 : frontier 10 ⟨516693, by decide⟩
    (prefixCache 11 18148) (prefixPartial 11 18148) = false := by
  decide +kernel

theorem node_context_11_18148_516693 : EJMOriginalGlobalDAGData.nodes 10 ⟨516693, by decide⟩ =
    .split (coordinate 11) (![⟨516592, by decide⟩,⟨516627, by decide⟩,⟨516669, by decide⟩,⟨516692, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18148_516693 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18148 ⟨516693, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18148
    ⟨516693, by decide⟩ (by decide) (![⟨516592, by decide⟩,⟨516627, by decide⟩,⟨516669, by decide⟩,⟨516692, by decide⟩]) unmarked_context_11_18148_516693 node_context_11_18148_516693
  intro a
  fin_cases a
  · exact context_12_72592_516592
  · exact context_12_72593_516627
  · exact context_12_72594_516669
  · exact context_12_72595_516692

theorem selected_cut_20186 : selected 9 ⟨516717, by decide⟩
    (prefixPartial 12 72596) = some ⟨12, 2, 0, 516717, 72596, 1961, 65536⟩ := by
  decide +kernel

theorem context_12_72596_516717 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72596 ⟨516717, by decide⟩ :=
  accepted_of_selected 12 72596 ⟨516717, by decide⟩ ⟨12, 2, 0, 516717, 72596, 1961, 65536⟩
    (by decide) selected_cut_20186

theorem selected_cut_20187 : selected 9 ⟨516741, by decide⟩
    (prefixPartial 12 72597) = some ⟨12, 2, 0, 516741, 72597, 2009, 65536⟩ := by
  decide +kernel

theorem context_12_72597_516741 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72597 ⟨516741, by decide⟩ :=
  accepted_of_selected 12 72597 ⟨516741, by decide⟩ ⟨12, 2, 0, 516741, 72597, 2009, 65536⟩
    (by decide) selected_cut_20187

theorem selected_cut_20188 : selected 9 ⟨516781, by decide⟩
    (prefixPartial 12 72598) = some ⟨12, 2, 0, 516781, 72598, 2461, 65536⟩ := by
  decide +kernel

theorem context_12_72598_516781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72598 ⟨516781, by decide⟩ :=
  accepted_of_selected 12 72598 ⟨516781, by decide⟩ ⟨12, 2, 0, 516781, 72598, 2461, 65536⟩
    (by decide) selected_cut_20188

theorem selected_cut_20189 : selected 9 ⟨516800, by decide⟩
    (prefixPartial 12 72599) = some ⟨12, 2, 0, 516800, 72599, 1841, 65536⟩ := by
  decide +kernel

theorem context_12_72599_516800 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72599 ⟨516800, by decide⟩ :=
  accepted_of_selected 12 72599 ⟨516800, by decide⟩ ⟨12, 2, 0, 516800, 72599, 1841, 65536⟩
    (by decide) selected_cut_20189

theorem unmarked_context_11_18149_516801 : frontier 10 ⟨516801, by decide⟩
    (prefixCache 11 18149) (prefixPartial 11 18149) = false := by
  decide +kernel

theorem node_context_11_18149_516801 : EJMOriginalGlobalDAGData.nodes 10 ⟨516801, by decide⟩ =
    .split (coordinate 11) (![⟨516717, by decide⟩,⟨516741, by decide⟩,⟨516781, by decide⟩,⟨516800, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18149_516801 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18149 ⟨516801, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18149
    ⟨516801, by decide⟩ (by decide) (![⟨516717, by decide⟩,⟨516741, by decide⟩,⟨516781, by decide⟩,⟨516800, by decide⟩]) unmarked_context_11_18149_516801 node_context_11_18149_516801
  intro a
  fin_cases a
  · exact context_12_72596_516717
  · exact context_12_72597_516741
  · exact context_12_72598_516781
  · exact context_12_72599_516800

theorem selected_cut_20190 : selected 9 ⟨516818, by decide⟩
    (prefixPartial 12 72600) = some ⟨12, 2, 0, 516818, 72600, 1825, 65536⟩ := by
  decide +kernel

theorem context_12_72600_516818 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72600 ⟨516818, by decide⟩ :=
  accepted_of_selected 12 72600 ⟨516818, by decide⟩ ⟨12, 2, 0, 516818, 72600, 1825, 65536⟩
    (by decide) selected_cut_20190

theorem selected_cut_20191 : selected 9 ⟨516844, by decide⟩
    (prefixPartial 12 72601) = some ⟨12, 2, 0, 516844, 72601, 2009, 65536⟩ := by
  decide +kernel

theorem context_12_72601_516844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72601 ⟨516844, by decide⟩ :=
  accepted_of_selected 12 72601 ⟨516844, by decide⟩ ⟨12, 2, 0, 516844, 72601, 2009, 65536⟩
    (by decide) selected_cut_20191

theorem selected_cut_20192 : selected 9 ⟨516873, by decide⟩
    (prefixPartial 12 72602) = some ⟨12, 2, 0, 516873, 72602, 2185, 65536⟩ := by
  decide +kernel

theorem context_12_72602_516873 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72602 ⟨516873, by decide⟩ :=
  accepted_of_selected 12 72602 ⟨516873, by decide⟩ ⟨12, 2, 0, 516873, 72602, 2185, 65536⟩
    (by decide) selected_cut_20192

theorem selected_cut_20193 : selected 9 ⟨516894, by decide⟩
    (prefixPartial 12 72603) = some ⟨12, 2, 0, 516894, 72603, 1725, 65536⟩ := by
  decide +kernel

theorem context_12_72603_516894 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72603 ⟨516894, by decide⟩ :=
  accepted_of_selected 12 72603 ⟨516894, by decide⟩ ⟨12, 2, 0, 516894, 72603, 1725, 65536⟩
    (by decide) selected_cut_20193

theorem unmarked_context_11_18150_516895 : frontier 10 ⟨516895, by decide⟩
    (prefixCache 11 18150) (prefixPartial 11 18150) = false := by
  decide +kernel

theorem node_context_11_18150_516895 : EJMOriginalGlobalDAGData.nodes 10 ⟨516895, by decide⟩ =
    .split (coordinate 11) (![⟨516818, by decide⟩,⟨516844, by decide⟩,⟨516873, by decide⟩,⟨516894, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18150_516895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18150 ⟨516895, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18150
    ⟨516895, by decide⟩ (by decide) (![⟨516818, by decide⟩,⟨516844, by decide⟩,⟨516873, by decide⟩,⟨516894, by decide⟩]) unmarked_context_11_18150_516895 node_context_11_18150_516895
  intro a
  fin_cases a
  · exact context_12_72600_516818
  · exact context_12_72601_516844
  · exact context_12_72602_516873
  · exact context_12_72603_516894

theorem selected_cut_20194 : selected 9 ⟨516916, by decide⟩
    (prefixPartial 12 72604) = some ⟨12, 2, 0, 516916, 72604, 1773, 65536⟩ := by
  decide +kernel

theorem context_12_72604_516916 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72604 ⟨516916, by decide⟩ :=
  accepted_of_selected 12 72604 ⟨516916, by decide⟩ ⟨12, 2, 0, 516916, 72604, 1773, 65536⟩
    (by decide) selected_cut_20194

theorem selected_cut_20195 : selected 9 ⟨516939, by decide⟩
    (prefixPartial 12 72605) = some ⟨12, 2, 0, 516939, 72605, 1893, 65536⟩ := by
  decide +kernel

theorem context_12_72605_516939 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72605 ⟨516939, by decide⟩ :=
  accepted_of_selected 12 72605 ⟨516939, by decide⟩ ⟨12, 2, 0, 516939, 72605, 1893, 65536⟩
    (by decide) selected_cut_20195

theorem selected_cut_20196 : selected 9 ⟨516961, by decide⟩
    (prefixPartial 12 72606) = some ⟨12, 2, 0, 516961, 72606, 2005, 65536⟩ := by
  decide +kernel

theorem context_12_72606_516961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72606 ⟨516961, by decide⟩ :=
  accepted_of_selected 12 72606 ⟨516961, by decide⟩ ⟨12, 2, 0, 516961, 72606, 2005, 65536⟩
    (by decide) selected_cut_20196

theorem selected_cut_20197 : selected 9 ⟨517004, by decide⟩
    (prefixPartial 12 72607) = some ⟨12, 2, 0, 517004, 72607, 2393, 65536⟩ := by
  decide +kernel

theorem context_12_72607_517004 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72607 ⟨517004, by decide⟩ :=
  accepted_of_selected 12 72607 ⟨517004, by decide⟩ ⟨12, 2, 0, 517004, 72607, 2393, 65536⟩
    (by decide) selected_cut_20197

theorem unmarked_context_11_18151_517005 : frontier 10 ⟨517005, by decide⟩
    (prefixCache 11 18151) (prefixPartial 11 18151) = false := by
  decide +kernel

theorem node_context_11_18151_517005 : EJMOriginalGlobalDAGData.nodes 10 ⟨517005, by decide⟩ =
    .split (coordinate 11) (![⟨516916, by decide⟩,⟨516939, by decide⟩,⟨516961, by decide⟩,⟨517004, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18151_517005 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18151 ⟨517005, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18151
    ⟨517005, by decide⟩ (by decide) (![⟨516916, by decide⟩,⟨516939, by decide⟩,⟨516961, by decide⟩,⟨517004, by decide⟩]) unmarked_context_11_18151_517005 node_context_11_18151_517005
  intro a
  fin_cases a
  · exact context_12_72604_516916
  · exact context_12_72605_516939
  · exact context_12_72606_516961
  · exact context_12_72607_517004

theorem unmarked_context_10_4537_517006 : frontier 11 ⟨517006, by decide⟩
    (prefixCache 10 4537) (prefixPartial 10 4537) = false := by
  decide +kernel

theorem node_context_10_4537_517006 : EJMOriginalGlobalDAGData.nodes 11 ⟨517006, by decide⟩ =
    .split (coordinate 10) (![⟨516693, by decide⟩,⟨516801, by decide⟩,⟨516895, by decide⟩,⟨517005, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4537_517006 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4537 ⟨517006, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4537
    ⟨517006, by decide⟩ (by decide) (![⟨516693, by decide⟩,⟨516801, by decide⟩,⟨516895, by decide⟩,⟨517005, by decide⟩]) unmarked_context_10_4537_517006 node_context_10_4537_517006
  intro a
  fin_cases a
  · exact context_11_18148_516693
  · exact context_11_18149_516801
  · exact context_11_18150_516895
  · exact context_11_18151_517005

theorem selected_cut_20198 : selected 9 ⟨517024, by decide⟩
    (prefixPartial 12 72608) = some ⟨12, 2, 0, 517024, 72608, 1325, 65536⟩ := by
  decide +kernel

theorem context_12_72608_517024 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72608 ⟨517024, by decide⟩ :=
  accepted_of_selected 12 72608 ⟨517024, by decide⟩ ⟨12, 2, 0, 517024, 72608, 1325, 65536⟩
    (by decide) selected_cut_20198

theorem selected_cut_20199 : selected 9 ⟨517043, by decide⟩
    (prefixPartial 12 72609) = some ⟨12, 2, 0, 517043, 72609, 1561, 65536⟩ := by
  decide +kernel

theorem context_12_72609_517043 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72609 ⟨517043, by decide⟩ :=
  accepted_of_selected 12 72609 ⟨517043, by decide⟩ ⟨12, 2, 0, 517043, 72609, 1561, 65536⟩
    (by decide) selected_cut_20199

theorem selected_cut_20200 : selected 9 ⟨517062, by decide⟩
    (prefixPartial 12 72610) = some ⟨12, 2, 0, 517062, 72610, 1585, 65536⟩ := by
  decide +kernel

theorem context_12_72610_517062 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72610 ⟨517062, by decide⟩ :=
  accepted_of_selected 12 72610 ⟨517062, by decide⟩ ⟨12, 2, 0, 517062, 72610, 1585, 65536⟩
    (by decide) selected_cut_20200

theorem selected_cut_20201 : selected 9 ⟨517073, by decide⟩
    (prefixPartial 12 72611) = some ⟨12, 2, 0, 517073, 72611, 1365, 65536⟩ := by
  decide +kernel

theorem context_12_72611_517073 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72611 ⟨517073, by decide⟩ :=
  accepted_of_selected 12 72611 ⟨517073, by decide⟩ ⟨12, 2, 0, 517073, 72611, 1365, 65536⟩
    (by decide) selected_cut_20201

theorem unmarked_context_11_18152_517074 : frontier 10 ⟨517074, by decide⟩
    (prefixCache 11 18152) (prefixPartial 11 18152) = false := by
  decide +kernel

theorem node_context_11_18152_517074 : EJMOriginalGlobalDAGData.nodes 10 ⟨517074, by decide⟩ =
    .split (coordinate 11) (![⟨517024, by decide⟩,⟨517043, by decide⟩,⟨517062, by decide⟩,⟨517073, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18152_517074 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18152 ⟨517074, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18152
    ⟨517074, by decide⟩ (by decide) (![⟨517024, by decide⟩,⟨517043, by decide⟩,⟨517062, by decide⟩,⟨517073, by decide⟩]) unmarked_context_11_18152_517074 node_context_11_18152_517074
  intro a
  fin_cases a
  · exact context_12_72608_517024
  · exact context_12_72609_517043
  · exact context_12_72610_517062
  · exact context_12_72611_517073

theorem selected_cut_20202 : selected 9 ⟨517093, by decide⟩
    (prefixPartial 12 72612) = some ⟨12, 2, 0, 517093, 72612, 1513, 65536⟩ := by
  decide +kernel

theorem context_12_72612_517093 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72612 ⟨517093, by decide⟩ :=
  accepted_of_selected 12 72612 ⟨517093, by decide⟩ ⟨12, 2, 0, 517093, 72612, 1513, 65536⟩
    (by decide) selected_cut_20202

theorem selected_cut_20203 : selected 9 ⟨517111, by decide⟩
    (prefixPartial 12 72613) = some ⟨12, 2, 0, 517111, 72613, 1565, 65536⟩ := by
  decide +kernel

theorem context_12_72613_517111 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72613 ⟨517111, by decide⟩ :=
  accepted_of_selected 12 72613 ⟨517111, by decide⟩ ⟨12, 2, 0, 517111, 72613, 1565, 65536⟩
    (by decide) selected_cut_20203

theorem selected_cut_20204 : selected 9 ⟨517129, by decide⟩
    (prefixPartial 12 72614) = some ⟨12, 2, 0, 517129, 72614, 1645, 65536⟩ := by
  decide +kernel

theorem context_12_72614_517129 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72614 ⟨517129, by decide⟩ :=
  accepted_of_selected 12 72614 ⟨517129, by decide⟩ ⟨12, 2, 0, 517129, 72614, 1645, 65536⟩
    (by decide) selected_cut_20204

theorem selected_cut_20205 : selected 9 ⟨517145, by decide⟩
    (prefixPartial 12 72615) = some ⟨12, 2, 0, 517145, 72615, 1425, 65536⟩ := by
  decide +kernel

theorem context_12_72615_517145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72615 ⟨517145, by decide⟩ :=
  accepted_of_selected 12 72615 ⟨517145, by decide⟩ ⟨12, 2, 0, 517145, 72615, 1425, 65536⟩
    (by decide) selected_cut_20205

theorem unmarked_context_11_18153_517146 : frontier 10 ⟨517146, by decide⟩
    (prefixCache 11 18153) (prefixPartial 11 18153) = false := by
  decide +kernel

theorem node_context_11_18153_517146 : EJMOriginalGlobalDAGData.nodes 10 ⟨517146, by decide⟩ =
    .split (coordinate 11) (![⟨517093, by decide⟩,⟨517111, by decide⟩,⟨517129, by decide⟩,⟨517145, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18153_517146 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18153 ⟨517146, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18153
    ⟨517146, by decide⟩ (by decide) (![⟨517093, by decide⟩,⟨517111, by decide⟩,⟨517129, by decide⟩,⟨517145, by decide⟩]) unmarked_context_11_18153_517146 node_context_11_18153_517146
  intro a
  fin_cases a
  · exact context_12_72612_517093
  · exact context_12_72613_517111
  · exact context_12_72614_517129
  · exact context_12_72615_517145

theorem selected_cut_20206 : selected 10 ⟨479708, by decide⟩
    (prefixPartial 11 18154) = some ⟨11, 1, 0, 479708, 18154, 1, 262144⟩ := by
  decide +kernel

theorem context_11_18154_479708 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18154 ⟨479708, by decide⟩ :=
  accepted_of_selected 11 18154 ⟨479708, by decide⟩ ⟨11, 1, 0, 479708, 18154, 1, 262144⟩
    (by decide) selected_cut_20206

theorem selected_cut_20207 : selected 9 ⟨517162, by decide⟩
    (prefixPartial 12 72620) = some ⟨12, 2, 0, 517162, 72620, 1377, 65536⟩ := by
  decide +kernel

theorem context_12_72620_517162 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72620 ⟨517162, by decide⟩ :=
  accepted_of_selected 12 72620 ⟨517162, by decide⟩ ⟨12, 2, 0, 517162, 72620, 1377, 65536⟩
    (by decide) selected_cut_20207

theorem selected_cut_20208 : selected 9 ⟨517176, by decide⟩
    (prefixPartial 12 72621) = some ⟨12, 2, 0, 517176, 72621, 1441, 65536⟩ := by
  decide +kernel

theorem context_12_72621_517176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72621 ⟨517176, by decide⟩ :=
  accepted_of_selected 12 72621 ⟨517176, by decide⟩ ⟨12, 2, 0, 517176, 72621, 1441, 65536⟩
    (by decide) selected_cut_20208

theorem selected_cut_20209 : selected 9 ⟨517191, by decide⟩
    (prefixPartial 12 72622) = some ⟨12, 2, 0, 517191, 72622, 1345, 65536⟩ := by
  decide +kernel

theorem context_12_72622_517191 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72622 ⟨517191, by decide⟩ :=
  accepted_of_selected 12 72622 ⟨517191, by decide⟩ ⟨12, 2, 0, 517191, 72622, 1345, 65536⟩
    (by decide) selected_cut_20209

theorem selected_cut_20210 : selected 9 ⟨517217, by decide⟩
    (prefixPartial 12 72623) = some ⟨12, 2, 0, 517217, 72623, 1873, 65536⟩ := by
  decide +kernel

theorem context_12_72623_517217 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72623 ⟨517217, by decide⟩ :=
  accepted_of_selected 12 72623 ⟨517217, by decide⟩ ⟨12, 2, 0, 517217, 72623, 1873, 65536⟩
    (by decide) selected_cut_20210

theorem unmarked_context_11_18155_517218 : frontier 10 ⟨517218, by decide⟩
    (prefixCache 11 18155) (prefixPartial 11 18155) = false := by
  decide +kernel

theorem node_context_11_18155_517218 : EJMOriginalGlobalDAGData.nodes 10 ⟨517218, by decide⟩ =
    .split (coordinate 11) (![⟨517162, by decide⟩,⟨517176, by decide⟩,⟨517191, by decide⟩,⟨517217, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18155_517218 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18155 ⟨517218, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18155
    ⟨517218, by decide⟩ (by decide) (![⟨517162, by decide⟩,⟨517176, by decide⟩,⟨517191, by decide⟩,⟨517217, by decide⟩]) unmarked_context_11_18155_517218 node_context_11_18155_517218
  intro a
  fin_cases a
  · exact context_12_72620_517162
  · exact context_12_72621_517176
  · exact context_12_72622_517191
  · exact context_12_72623_517217

theorem unmarked_context_10_4538_517219 : frontier 11 ⟨517219, by decide⟩
    (prefixCache 10 4538) (prefixPartial 10 4538) = false := by
  decide +kernel

theorem node_context_10_4538_517219 : EJMOriginalGlobalDAGData.nodes 11 ⟨517219, by decide⟩ =
    .split (coordinate 10) (![⟨517074, by decide⟩,⟨517146, by decide⟩,⟨479708, by decide⟩,⟨517218, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4538_517219 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4538 ⟨517219, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4538
    ⟨517219, by decide⟩ (by decide) (![⟨517074, by decide⟩,⟨517146, by decide⟩,⟨479708, by decide⟩,⟨517218, by decide⟩]) unmarked_context_10_4538_517219 node_context_10_4538_517219
  intro a
  fin_cases a
  · exact context_11_18152_517074
  · exact context_11_18153_517146
  · exact context_11_18154_479708
  · exact context_11_18155_517218

theorem selected_cut_20211 : selected 9 ⟨517235, by decide⟩
    (prefixPartial 12 72624) = some ⟨12, 2, 0, 517235, 72624, 1369, 65536⟩ := by
  decide +kernel

theorem context_12_72624_517235 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72624 ⟨517235, by decide⟩ :=
  accepted_of_selected 12 72624 ⟨517235, by decide⟩ ⟨12, 2, 0, 517235, 72624, 1369, 65536⟩
    (by decide) selected_cut_20211

theorem selected_cut_20212 : selected 9 ⟨517250, by decide⟩
    (prefixPartial 12 72625) = some ⟨12, 2, 0, 517250, 72625, 1521, 65536⟩ := by
  decide +kernel

theorem context_12_72625_517250 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72625 ⟨517250, by decide⟩ :=
  accepted_of_selected 12 72625 ⟨517250, by decide⟩ ⟨12, 2, 0, 517250, 72625, 1521, 65536⟩
    (by decide) selected_cut_20212

theorem selected_cut_20213 : selected 9 ⟨517264, by decide⟩
    (prefixPartial 12 72626) = some ⟨12, 2, 0, 517264, 72626, 1465, 65536⟩ := by
  decide +kernel

theorem context_12_72626_517264 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72626 ⟨517264, by decide⟩ :=
  accepted_of_selected 12 72626 ⟨517264, by decide⟩ ⟨12, 2, 0, 517264, 72626, 1465, 65536⟩
    (by decide) selected_cut_20213

theorem selected_cut_20214 : selected 9 ⟨517277, by decide⟩
    (prefixPartial 12 72627) = some ⟨12, 2, 0, 517277, 72627, 1253, 65536⟩ := by
  decide +kernel

theorem context_12_72627_517277 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72627 ⟨517277, by decide⟩ :=
  accepted_of_selected 12 72627 ⟨517277, by decide⟩ ⟨12, 2, 0, 517277, 72627, 1253, 65536⟩
    (by decide) selected_cut_20214

theorem unmarked_context_11_18156_517278 : frontier 10 ⟨517278, by decide⟩
    (prefixCache 11 18156) (prefixPartial 11 18156) = false := by
  decide +kernel

theorem node_context_11_18156_517278 : EJMOriginalGlobalDAGData.nodes 10 ⟨517278, by decide⟩ =
    .split (coordinate 11) (![⟨517235, by decide⟩,⟨517250, by decide⟩,⟨517264, by decide⟩,⟨517277, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18156_517278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18156 ⟨517278, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18156
    ⟨517278, by decide⟩ (by decide) (![⟨517235, by decide⟩,⟨517250, by decide⟩,⟨517264, by decide⟩,⟨517277, by decide⟩]) unmarked_context_11_18156_517278 node_context_11_18156_517278
  intro a
  fin_cases a
  · exact context_12_72624_517235
  · exact context_12_72625_517250
  · exact context_12_72626_517264
  · exact context_12_72627_517277

theorem selected_cut_20215 : selected 9 ⟨517299, by decide⟩
    (prefixPartial 12 72628) = some ⟨12, 2, 0, 517299, 72628, 1409, 65536⟩ := by
  decide +kernel

theorem context_12_72628_517299 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72628 ⟨517299, by decide⟩ :=
  accepted_of_selected 12 72628 ⟨517299, by decide⟩ ⟨12, 2, 0, 517299, 72628, 1409, 65536⟩
    (by decide) selected_cut_20215

theorem selected_cut_20216 : selected 9 ⟨517312, by decide⟩
    (prefixPartial 12 72629) = some ⟨12, 2, 0, 517312, 72629, 1437, 65536⟩ := by
  decide +kernel

theorem context_12_72629_517312 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72629 ⟨517312, by decide⟩ :=
  accepted_of_selected 12 72629 ⟨517312, by decide⟩ ⟨12, 2, 0, 517312, 72629, 1437, 65536⟩
    (by decide) selected_cut_20216

theorem selected_cut_20217 : selected 9 ⟨517338, by decide⟩
    (prefixPartial 12 72630) = some ⟨12, 2, 0, 517338, 72630, 1469, 65536⟩ := by
  decide +kernel

theorem context_12_72630_517338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72630 ⟨517338, by decide⟩ :=
  accepted_of_selected 12 72630 ⟨517338, by decide⟩ ⟨12, 2, 0, 517338, 72630, 1469, 65536⟩
    (by decide) selected_cut_20217

theorem selected_cut_20218 : selected 9 ⟨517349, by decide⟩
    (prefixPartial 12 72631) = some ⟨12, 2, 0, 517349, 72631, 1225, 65536⟩ := by
  decide +kernel

theorem context_12_72631_517349 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72631 ⟨517349, by decide⟩ :=
  accepted_of_selected 12 72631 ⟨517349, by decide⟩ ⟨12, 2, 0, 517349, 72631, 1225, 65536⟩
    (by decide) selected_cut_20218

theorem unmarked_context_11_18157_517350 : frontier 10 ⟨517350, by decide⟩
    (prefixCache 11 18157) (prefixPartial 11 18157) = false := by
  decide +kernel

theorem node_context_11_18157_517350 : EJMOriginalGlobalDAGData.nodes 10 ⟨517350, by decide⟩ =
    .split (coordinate 11) (![⟨517299, by decide⟩,⟨517312, by decide⟩,⟨517338, by decide⟩,⟨517349, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18157_517350 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18157 ⟨517350, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18157
    ⟨517350, by decide⟩ (by decide) (![⟨517299, by decide⟩,⟨517312, by decide⟩,⟨517338, by decide⟩,⟨517349, by decide⟩]) unmarked_context_11_18157_517350 node_context_11_18157_517350
  intro a
  fin_cases a
  · exact context_12_72628_517299
  · exact context_12_72629_517312
  · exact context_12_72630_517338
  · exact context_12_72631_517349

theorem selected_cut_20219 : selected 9 ⟨517366, by decide⟩
    (prefixPartial 12 72632) = some ⟨12, 2, 0, 517366, 72632, 1265, 65536⟩ := by
  decide +kernel

theorem context_12_72632_517366 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72632 ⟨517366, by decide⟩ :=
  accepted_of_selected 12 72632 ⟨517366, by decide⟩ ⟨12, 2, 0, 517366, 72632, 1265, 65536⟩
    (by decide) selected_cut_20219

theorem selected_cut_20220 : selected 9 ⟨517378, by decide⟩
    (prefixPartial 12 72633) = some ⟨12, 2, 0, 517378, 72633, 1365, 65536⟩ := by
  decide +kernel

theorem context_12_72633_517378 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72633 ⟨517378, by decide⟩ :=
  accepted_of_selected 12 72633 ⟨517378, by decide⟩ ⟨12, 2, 0, 517378, 72633, 1365, 65536⟩
    (by decide) selected_cut_20220

theorem selected_cut_20221 : selected 9 ⟨517390, by decide⟩
    (prefixPartial 12 72634) = some ⟨12, 2, 0, 517390, 72634, 1253, 65536⟩ := by
  decide +kernel

theorem context_12_72634_517390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72634 ⟨517390, by decide⟩ :=
  accepted_of_selected 12 72634 ⟨517390, by decide⟩ ⟨12, 2, 0, 517390, 72634, 1253, 65536⟩
    (by decide) selected_cut_20221

theorem selected_cut_20222 : selected 9 ⟨517402, by decide⟩
    (prefixPartial 12 72635) = some ⟨12, 2, 0, 517402, 72635, 1169, 65536⟩ := by
  decide +kernel

theorem context_12_72635_517402 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72635 ⟨517402, by decide⟩ :=
  accepted_of_selected 12 72635 ⟨517402, by decide⟩ ⟨12, 2, 0, 517402, 72635, 1169, 65536⟩
    (by decide) selected_cut_20222

theorem unmarked_context_11_18158_517403 : frontier 10 ⟨517403, by decide⟩
    (prefixCache 11 18158) (prefixPartial 11 18158) = false := by
  decide +kernel

theorem node_context_11_18158_517403 : EJMOriginalGlobalDAGData.nodes 10 ⟨517403, by decide⟩ =
    .split (coordinate 11) (![⟨517366, by decide⟩,⟨517378, by decide⟩,⟨517390, by decide⟩,⟨517402, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18158_517403 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18158 ⟨517403, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18158
    ⟨517403, by decide⟩ (by decide) (![⟨517366, by decide⟩,⟨517378, by decide⟩,⟨517390, by decide⟩,⟨517402, by decide⟩]) unmarked_context_11_18158_517403 node_context_11_18158_517403
  intro a
  fin_cases a
  · exact context_12_72632_517366
  · exact context_12_72633_517378
  · exact context_12_72634_517390
  · exact context_12_72635_517402

theorem selected_cut_20223 : selected 10 ⟨517435, by decide⟩
    (prefixPartial 11 18159) = some ⟨11, 2, 0, 517435, 18159, 3389, 262144⟩ := by
  decide +kernel

theorem context_11_18159_517435 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18159 ⟨517435, by decide⟩ :=
  accepted_of_selected 11 18159 ⟨517435, by decide⟩ ⟨11, 2, 0, 517435, 18159, 3389, 262144⟩
    (by decide) selected_cut_20223

theorem unmarked_context_10_4539_517436 : frontier 11 ⟨517436, by decide⟩
    (prefixCache 10 4539) (prefixPartial 10 4539) = false := by
  decide +kernel

theorem node_context_10_4539_517436 : EJMOriginalGlobalDAGData.nodes 11 ⟨517436, by decide⟩ =
    .split (coordinate 10) (![⟨517278, by decide⟩,⟨517350, by decide⟩,⟨517403, by decide⟩,⟨517435, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4539_517436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4539 ⟨517436, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4539
    ⟨517436, by decide⟩ (by decide) (![⟨517278, by decide⟩,⟨517350, by decide⟩,⟨517403, by decide⟩,⟨517435, by decide⟩]) unmarked_context_10_4539_517436 node_context_10_4539_517436
  intro a
  fin_cases a
  · exact context_11_18156_517278
  · exact context_11_18157_517350
  · exact context_11_18158_517403
  · exact context_11_18159_517435

theorem unmarked_context_9_1134_517437 : frontier 12 ⟨517437, by decide⟩
    (prefixCache 9 1134) (prefixPartial 9 1134) = false := by
  decide +kernel

theorem node_context_9_1134_517437 : EJMOriginalGlobalDAGData.nodes 12 ⟨517437, by decide⟩ =
    .split (coordinate 9) (![⟨516570, by decide⟩,⟨517006, by decide⟩,⟨517219, by decide⟩,⟨517436, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1134_517437 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1134 ⟨517437, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1134
    ⟨517437, by decide⟩ (by decide) (![⟨516570, by decide⟩,⟨517006, by decide⟩,⟨517219, by decide⟩,⟨517436, by decide⟩]) unmarked_context_9_1134_517437 node_context_9_1134_517437
  intro a
  fin_cases a
  · exact context_10_4536_516570
  · exact context_10_4537_517006
  · exact context_10_4538_517219
  · exact context_10_4539_517436

theorem selected_cut_20224 : selected 10 ⟨517465, by decide⟩
    (prefixPartial 11 18160) = some ⟨11, 2, 0, 517465, 18160, 2369, 262144⟩ := by
  decide +kernel

theorem context_11_18160_517465 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18160 ⟨517465, by decide⟩ :=
  accepted_of_selected 11 18160 ⟨517465, by decide⟩ ⟨11, 2, 0, 517465, 18160, 2369, 262144⟩
    (by decide) selected_cut_20224

theorem selected_cut_20225 : selected 10 ⟨517492, by decide⟩
    (prefixPartial 11 18161) = some ⟨11, 2, 0, 517492, 18161, 2557, 262144⟩ := by
  decide +kernel

theorem context_11_18161_517492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18161 ⟨517492, by decide⟩ :=
  accepted_of_selected 11 18161 ⟨517492, by decide⟩ ⟨11, 2, 0, 517492, 18161, 2557, 262144⟩
    (by decide) selected_cut_20225

theorem selected_cut_20226 : selected 10 ⟨517518, by decide⟩
    (prefixPartial 11 18162) = some ⟨11, 2, 0, 517518, 18162, 2137, 262144⟩ := by
  decide +kernel

theorem context_11_18162_517518 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18162 ⟨517518, by decide⟩ :=
  accepted_of_selected 11 18162 ⟨517518, by decide⟩ ⟨11, 2, 0, 517518, 18162, 2137, 262144⟩
    (by decide) selected_cut_20226

theorem selected_cut_20227 : selected 10 ⟨517542, by decide⟩
    (prefixPartial 11 18163) = some ⟨11, 2, 0, 517542, 18163, 1801, 262144⟩ := by
  decide +kernel

theorem context_11_18163_517542 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18163 ⟨517542, by decide⟩ :=
  accepted_of_selected 11 18163 ⟨517542, by decide⟩ ⟨11, 2, 0, 517542, 18163, 1801, 262144⟩
    (by decide) selected_cut_20227

theorem unmarked_context_10_4540_517543 : frontier 11 ⟨517543, by decide⟩
    (prefixCache 10 4540) (prefixPartial 10 4540) = false := by
  decide +kernel

theorem node_context_10_4540_517543 : EJMOriginalGlobalDAGData.nodes 11 ⟨517543, by decide⟩ =
    .split (coordinate 10) (![⟨517465, by decide⟩,⟨517492, by decide⟩,⟨517518, by decide⟩,⟨517542, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4540_517543 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4540 ⟨517543, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4540
    ⟨517543, by decide⟩ (by decide) (![⟨517465, by decide⟩,⟨517492, by decide⟩,⟨517518, by decide⟩,⟨517542, by decide⟩]) unmarked_context_10_4540_517543 node_context_10_4540_517543
  intro a
  fin_cases a
  · exact context_11_18160_517465
  · exact context_11_18161_517492
  · exact context_11_18162_517518
  · exact context_11_18163_517542

theorem selected_cut_20228 : selected 10 ⟨517569, by decide⟩
    (prefixPartial 11 18164) = some ⟨11, 2, 0, 517569, 18164, 2249, 262144⟩ := by
  decide +kernel

theorem context_11_18164_517569 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18164 ⟨517569, by decide⟩ :=
  accepted_of_selected 11 18164 ⟨517569, by decide⟩ ⟨11, 2, 0, 517569, 18164, 2249, 262144⟩
    (by decide) selected_cut_20228

theorem selected_cut_20229 : selected 10 ⟨517597, by decide⟩
    (prefixPartial 11 18165) = some ⟨11, 2, 0, 517597, 18165, 2237, 262144⟩ := by
  decide +kernel

theorem context_11_18165_517597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18165 ⟨517597, by decide⟩ :=
  accepted_of_selected 11 18165 ⟨517597, by decide⟩ ⟨11, 2, 0, 517597, 18165, 2237, 262144⟩
    (by decide) selected_cut_20229

theorem selected_cut_20230 : selected 10 ⟨517619, by decide⟩
    (prefixPartial 11 18166) = some ⟨11, 2, 0, 517619, 18166, 1977, 262144⟩ := by
  decide +kernel

theorem context_11_18166_517619 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18166 ⟨517619, by decide⟩ :=
  accepted_of_selected 11 18166 ⟨517619, by decide⟩ ⟨11, 2, 0, 517619, 18166, 1977, 262144⟩
    (by decide) selected_cut_20230

theorem selected_cut_20231 : selected 10 ⟨517640, by decide⟩
    (prefixPartial 11 18167) = some ⟨11, 2, 0, 517640, 18167, 1369, 262144⟩ := by
  decide +kernel

theorem context_11_18167_517640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18167 ⟨517640, by decide⟩ :=
  accepted_of_selected 11 18167 ⟨517640, by decide⟩ ⟨11, 2, 0, 517640, 18167, 1369, 262144⟩
    (by decide) selected_cut_20231

theorem unmarked_context_10_4541_517641 : frontier 11 ⟨517641, by decide⟩
    (prefixCache 10 4541) (prefixPartial 10 4541) = false := by
  decide +kernel

theorem node_context_10_4541_517641 : EJMOriginalGlobalDAGData.nodes 11 ⟨517641, by decide⟩ =
    .split (coordinate 10) (![⟨517569, by decide⟩,⟨517597, by decide⟩,⟨517619, by decide⟩,⟨517640, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4541_517641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4541 ⟨517641, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4541
    ⟨517641, by decide⟩ (by decide) (![⟨517569, by decide⟩,⟨517597, by decide⟩,⟨517619, by decide⟩,⟨517640, by decide⟩]) unmarked_context_10_4541_517641 node_context_10_4541_517641
  intro a
  fin_cases a
  · exact context_11_18164_517569
  · exact context_11_18165_517597
  · exact context_11_18166_517619
  · exact context_11_18167_517640

theorem selected_cut_20232 : selected 10 ⟨517660, by decide⟩
    (prefixPartial 11 18168) = some ⟨11, 2, 0, 517660, 18168, 1373, 262144⟩ := by
  decide +kernel

theorem context_11_18168_517660 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18168 ⟨517660, by decide⟩ :=
  accepted_of_selected 11 18168 ⟨517660, by decide⟩ ⟨11, 2, 0, 517660, 18168, 1373, 262144⟩
    (by decide) selected_cut_20232

theorem selected_cut_20233 : selected 10 ⟨517681, by decide⟩
    (prefixPartial 11 18169) = some ⟨11, 2, 0, 517681, 18169, 1377, 262144⟩ := by
  decide +kernel

theorem context_11_18169_517681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18169 ⟨517681, by decide⟩ :=
  accepted_of_selected 11 18169 ⟨517681, by decide⟩ ⟨11, 2, 0, 517681, 18169, 1377, 262144⟩
    (by decide) selected_cut_20233

theorem selected_cut_20234 : selected 10 ⟨517695, by decide⟩
    (prefixPartial 11 18170) = some ⟨11, 2, 0, 517695, 18170, 877, 262144⟩ := by
  decide +kernel

theorem context_11_18170_517695 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18170 ⟨517695, by decide⟩ :=
  accepted_of_selected 11 18170 ⟨517695, by decide⟩ ⟨11, 2, 0, 517695, 18170, 877, 262144⟩
    (by decide) selected_cut_20234

theorem selected_cut_20235 : selected 10 ⟨517709, by decide⟩
    (prefixPartial 11 18171) = some ⟨11, 2, 0, 517709, 18171, 681, 262144⟩ := by
  decide +kernel

theorem context_11_18171_517709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18171 ⟨517709, by decide⟩ :=
  accepted_of_selected 11 18171 ⟨517709, by decide⟩ ⟨11, 2, 0, 517709, 18171, 681, 262144⟩
    (by decide) selected_cut_20235

theorem unmarked_context_10_4542_517710 : frontier 11 ⟨517710, by decide⟩
    (prefixCache 10 4542) (prefixPartial 10 4542) = false := by
  decide +kernel

theorem node_context_10_4542_517710 : EJMOriginalGlobalDAGData.nodes 11 ⟨517710, by decide⟩ =
    .split (coordinate 10) (![⟨517660, by decide⟩,⟨517681, by decide⟩,⟨517695, by decide⟩,⟨517709, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4542_517710 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4542 ⟨517710, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4542
    ⟨517710, by decide⟩ (by decide) (![⟨517660, by decide⟩,⟨517681, by decide⟩,⟨517695, by decide⟩,⟨517709, by decide⟩]) unmarked_context_10_4542_517710 node_context_10_4542_517710
  intro a
  fin_cases a
  · exact context_11_18168_517660
  · exact context_11_18169_517681
  · exact context_11_18170_517695
  · exact context_11_18171_517709

theorem selected_cut_20236 : selected 11 ⟨517761, by decide⟩
    (prefixPartial 10 4543) = some ⟨10, 2, 0, 517761, 4543, 1541, 1048576⟩ := by
  decide +kernel

theorem context_10_4543_517761 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4543 ⟨517761, by decide⟩ :=
  accepted_of_selected 10 4543 ⟨517761, by decide⟩ ⟨10, 2, 0, 517761, 4543, 1541, 1048576⟩
    (by decide) selected_cut_20236

theorem unmarked_context_9_1135_517762 : frontier 12 ⟨517762, by decide⟩
    (prefixCache 9 1135) (prefixPartial 9 1135) = false := by
  decide +kernel

theorem node_context_9_1135_517762 : EJMOriginalGlobalDAGData.nodes 12 ⟨517762, by decide⟩ =
    .split (coordinate 9) (![⟨517543, by decide⟩,⟨517641, by decide⟩,⟨517710, by decide⟩,⟨517761, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1135_517762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1135 ⟨517762, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1135
    ⟨517762, by decide⟩ (by decide) (![⟨517543, by decide⟩,⟨517641, by decide⟩,⟨517710, by decide⟩,⟨517761, by decide⟩]) unmarked_context_9_1135_517762 node_context_9_1135_517762
  intro a
  fin_cases a
  · exact context_10_4540_517543
  · exact context_10_4541_517641
  · exact context_10_4542_517710
  · exact context_10_4543_517761

theorem unmarked_context_8_283_517763 : frontier 13 ⟨517763, by decide⟩
    (prefixCache 8 283) (prefixPartial 8 283) = false := by
  decide +kernel

theorem node_context_8_283_517763 : EJMOriginalGlobalDAGData.nodes 13 ⟨517763, by decide⟩ =
    .split (coordinate 8) (![⟨512559, by decide⟩,⟨516122, by decide⟩,⟨517437, by decide⟩,⟨517762, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_283_517763 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 283 ⟨517763, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 283
    ⟨517763, by decide⟩ (by decide) (![⟨512559, by decide⟩,⟨516122, by decide⟩,⟨517437, by decide⟩,⟨517762, by decide⟩]) unmarked_context_8_283_517763 node_context_8_283_517763
  intro a
  fin_cases a
  · exact context_9_1132_512559
  · exact context_9_1133_516122
  · exact context_9_1134_517437
  · exact context_9_1135_517762

theorem unmarked_context_7_70_517764 : frontier 14 ⟨517764, by decide⟩
    (prefixCache 7 70) (prefixPartial 7 70) = false := by
  decide +kernel

theorem node_context_7_70_517764 : EJMOriginalGlobalDAGData.nodes 14 ⟨517764, by decide⟩ =
    .split (coordinate 7) (![⟨480396, by decide⟩,⟨494474, by decide⟩,⟨507053, by decide⟩,⟨517763, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_70_517764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 70 ⟨517764, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 70
    ⟨517764, by decide⟩ (by decide) (![⟨480396, by decide⟩,⟨494474, by decide⟩,⟨507053, by decide⟩,⟨517763, by decide⟩]) unmarked_context_7_70_517764 node_context_7_70_517764
  intro a
  fin_cases a
  · exact context_8_280_480396
  · exact context_8_281_494474
  · exact context_8_282_507053
  · exact context_8_283_517763

theorem selected_cut_20237 : selected 14 ⟨34032, by decide⟩
    (prefixPartial 7 71) = some ⟨7, 1, 0, 34032, 71, 1, 67108864⟩ := by
  decide +kernel

theorem context_7_71_34032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 71 ⟨34032, by decide⟩ :=
  accepted_of_selected 7 71 ⟨34032, by decide⟩ ⟨7, 1, 0, 34032, 71, 1, 67108864⟩
    (by decide) selected_cut_20237

theorem unmarked_context_6_17_517765 : frontier 15 ⟨517765, by decide⟩
    (prefixCache 6 17) (prefixPartial 6 17) = false := by
  decide +kernel

theorem node_context_6_17_517765 : EJMOriginalGlobalDAGData.nodes 15 ⟨517765, by decide⟩ =
    .split (coordinate 6) (![⟨448747, by decide⟩,⟨470523, by decide⟩,⟨517764, by decide⟩,⟨34032, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_6_17_517765 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 17 ⟨517765, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 6 17
    ⟨517765, by decide⟩ (by decide) (![⟨448747, by decide⟩,⟨470523, by decide⟩,⟨517764, by decide⟩,⟨34032, by decide⟩]) unmarked_context_6_17_517765 node_context_6_17_517765
  intro a
  fin_cases a
  · exact context_7_68_448747
  · exact context_7_69_470523
  · exact context_7_70_517764
  · exact context_7_71_34032

theorem selected_cut_20238 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 18432) = some ⟨11, 1, 0, 434745, 18432, 1, 262144⟩ := by
  decide +kernel

theorem context_11_18432_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18432 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 18432 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 18432, 1, 262144⟩
    (by decide) selected_cut_20238

theorem selected_cut_20239 : selected 9 ⟨4595, by decide⟩
    (prefixPartial 12 73732) = some ⟨12, 1, 0, 4595, 73732, 1, 65536⟩ := by
  decide +kernel

theorem context_12_73732_4595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73732 ⟨4595, by decide⟩ :=
  accepted_of_selected 12 73732 ⟨4595, by decide⟩ ⟨12, 1, 0, 4595, 73732, 1, 65536⟩
    (by decide) selected_cut_20239

theorem selected_cut_20240 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 73733) = some ⟨12, 1, 0, 34034, 73733, 1, 65536⟩ := by
  decide +kernel

theorem context_12_73733_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73733 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 73733 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 73733, 1, 65536⟩
    (by decide) selected_cut_20240

theorem selected_cut_20241 : selected 9 ⟨517859, by decide⟩
    (prefixPartial 12 73734) = some ⟨12, 2, 0, 517859, 73734, 1989, 65536⟩ := by
  decide +kernel

theorem context_12_73734_517859 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73734 ⟨517859, by decide⟩ :=
  accepted_of_selected 12 73734 ⟨517859, by decide⟩ ⟨12, 2, 0, 517859, 73734, 1989, 65536⟩
    (by decide) selected_cut_20241

theorem selected_cut_20242 : selected 9 ⟨518006, by decide⟩
    (prefixPartial 12 73735) = some ⟨12, 2, 0, 518006, 73735, 3729, 65536⟩ := by
  decide +kernel

theorem context_12_73735_518006 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73735 ⟨518006, by decide⟩ :=
  accepted_of_selected 12 73735 ⟨518006, by decide⟩ ⟨12, 2, 0, 518006, 73735, 3729, 65536⟩
    (by decide) selected_cut_20242

theorem unmarked_context_11_18433_518007 : frontier 10 ⟨518007, by decide⟩
    (prefixCache 11 18433) (prefixPartial 11 18433) = false := by
  decide +kernel

theorem node_context_11_18433_518007 : EJMOriginalGlobalDAGData.nodes 10 ⟨518007, by decide⟩ =
    .split (coordinate 11) (![⟨4595, by decide⟩,⟨34034, by decide⟩,⟨517859, by decide⟩,⟨518006, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18433_518007 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18433 ⟨518007, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18433
    ⟨518007, by decide⟩ (by decide) (![⟨4595, by decide⟩,⟨34034, by decide⟩,⟨517859, by decide⟩,⟨518006, by decide⟩]) unmarked_context_11_18433_518007 node_context_11_18433_518007
  intro a
  fin_cases a
  · exact context_12_73732_4595
  · exact context_12_73733_34034
  · exact context_12_73734_517859
  · exact context_12_73735_518006

theorem selected_cut_20243 : selected 9 ⟨4595, by decide⟩
    (prefixPartial 12 73736) = some ⟨12, 1, 0, 4595, 73736, 1, 65536⟩ := by
  decide +kernel

theorem context_12_73736_4595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73736 ⟨4595, by decide⟩ :=
  accepted_of_selected 12 73736 ⟨4595, by decide⟩ ⟨12, 1, 0, 4595, 73736, 1, 65536⟩
    (by decide) selected_cut_20243

theorem selected_cut_20244 : selected 9 ⟨518132, by decide⟩
    (prefixPartial 12 73737) = some ⟨12, 2, 0, 518132, 73737, 3937, 65536⟩ := by
  decide +kernel

theorem context_12_73737_518132 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73737 ⟨518132, by decide⟩ :=
  accepted_of_selected 12 73737 ⟨518132, by decide⟩ ⟨12, 2, 0, 518132, 73737, 3937, 65536⟩
    (by decide) selected_cut_20244

theorem selected_cut_20245 : selected 9 ⟨4595, by decide⟩
    (prefixPartial 12 73738) = some ⟨12, 1, 0, 4595, 73738, 1, 65536⟩ := by
  decide +kernel

theorem context_12_73738_4595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73738 ⟨4595, by decide⟩ :=
  accepted_of_selected 12 73738 ⟨4595, by decide⟩ ⟨12, 1, 0, 4595, 73738, 1, 65536⟩
    (by decide) selected_cut_20245

theorem selected_cut_20246 : selected 9 ⟨518276, by decide⟩
    (prefixPartial 12 73739) = some ⟨12, 2, 0, 518276, 73739, 3645, 65536⟩ := by
  decide +kernel

theorem context_12_73739_518276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73739 ⟨518276, by decide⟩ :=
  accepted_of_selected 12 73739 ⟨518276, by decide⟩ ⟨12, 2, 0, 518276, 73739, 3645, 65536⟩
    (by decide) selected_cut_20246

theorem unmarked_context_11_18434_518277 : frontier 10 ⟨518277, by decide⟩
    (prefixCache 11 18434) (prefixPartial 11 18434) = false := by
  decide +kernel

theorem node_context_11_18434_518277 : EJMOriginalGlobalDAGData.nodes 10 ⟨518277, by decide⟩ =
    .split (coordinate 11) (![⟨4595, by decide⟩,⟨518132, by decide⟩,⟨4595, by decide⟩,⟨518276, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18434_518277 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18434 ⟨518277, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18434
    ⟨518277, by decide⟩ (by decide) (![⟨4595, by decide⟩,⟨518132, by decide⟩,⟨4595, by decide⟩,⟨518276, by decide⟩]) unmarked_context_11_18434_518277 node_context_11_18434_518277
  intro a
  fin_cases a
  · exact context_12_73736_4595
  · exact context_12_73737_518132
  · exact context_12_73738_4595
  · exact context_12_73739_518276

theorem selected_cut_20247 : selected 10 ⟨518279, by decide⟩
    (prefixPartial 11 18435) = some ⟨11, 2, 0, 518279, 18435, 5, 262144⟩ := by
  decide +kernel

theorem context_11_18435_518279 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18435 ⟨518279, by decide⟩ :=
  accepted_of_selected 11 18435 ⟨518279, by decide⟩ ⟨11, 2, 0, 518279, 18435, 5, 262144⟩
    (by decide) selected_cut_20247

theorem unmarked_context_10_4608_518280 : frontier 11 ⟨518280, by decide⟩
    (prefixCache 10 4608) (prefixPartial 10 4608) = false := by
  decide +kernel

theorem node_context_10_4608_518280 : EJMOriginalGlobalDAGData.nodes 11 ⟨518280, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨518007, by decide⟩,⟨518277, by decide⟩,⟨518279, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4608_518280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4608 ⟨518280, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4608
    ⟨518280, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨518007, by decide⟩,⟨518277, by decide⟩,⟨518279, by decide⟩]) unmarked_context_10_4608_518280 node_context_10_4608_518280
  intro a
  fin_cases a
  · exact context_11_18432_434745
  · exact context_11_18433_518007
  · exact context_11_18434_518277
  · exact context_11_18435_518279

theorem selected_cut_20248 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 73744) = some ⟨12, 1, 0, 435160, 73744, 1, 65536⟩ := by
  decide +kernel

theorem context_12_73744_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73744 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 73744 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 73744, 1, 65536⟩
    (by decide) selected_cut_20248

theorem selected_cut_20249 : selected 9 ⟨518347, by decide⟩
    (prefixPartial 12 73745) = some ⟨12, 2, 0, 518347, 73745, 3693, 65536⟩ := by
  decide +kernel

theorem context_12_73745_518347 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73745 ⟨518347, by decide⟩ :=
  accepted_of_selected 12 73745 ⟨518347, by decide⟩ ⟨12, 2, 0, 518347, 73745, 3693, 65536⟩
    (by decide) selected_cut_20249

theorem selected_cut_20250 : selected 9 ⟨518400, by decide⟩
    (prefixPartial 12 73746) = some ⟨12, 2, 0, 518400, 73746, 3317, 65536⟩ := by
  decide +kernel

theorem context_12_73746_518400 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73746 ⟨518400, by decide⟩ :=
  accepted_of_selected 12 73746 ⟨518400, by decide⟩ ⟨12, 2, 0, 518400, 73746, 3317, 65536⟩
    (by decide) selected_cut_20250

theorem selected_cut_20251 : selected 9 ⟨518454, by decide⟩
    (prefixPartial 12 73747) = some ⟨12, 2, 0, 518454, 73747, 3357, 65536⟩ := by
  decide +kernel

theorem context_12_73747_518454 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73747 ⟨518454, by decide⟩ :=
  accepted_of_selected 12 73747 ⟨518454, by decide⟩ ⟨12, 2, 0, 518454, 73747, 3357, 65536⟩
    (by decide) selected_cut_20251

theorem unmarked_context_11_18436_518455 : frontier 10 ⟨518455, by decide⟩
    (prefixCache 11 18436) (prefixPartial 11 18436) = false := by
  decide +kernel

theorem node_context_11_18436_518455 : EJMOriginalGlobalDAGData.nodes 10 ⟨518455, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨518347, by decide⟩,⟨518400, by decide⟩,⟨518454, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18436_518455 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18436 ⟨518455, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18436
    ⟨518455, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨518347, by decide⟩,⟨518400, by decide⟩,⟨518454, by decide⟩]) unmarked_context_11_18436_518455 node_context_11_18436_518455
  intro a
  fin_cases a
  · exact context_12_73744_435160
  · exact context_12_73745_518347
  · exact context_12_73746_518400
  · exact context_12_73747_518454

theorem selected_cut_20252 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 73748) = some ⟨12, 1, 0, 435160, 73748, 1, 65536⟩ := by
  decide +kernel

theorem context_12_73748_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73748 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 73748 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 73748, 1, 65536⟩
    (by decide) selected_cut_20252

theorem selected_cut_20253 : selected 8 ⟨518480, by decide⟩
    (prefixPartial 13 294996) = some ⟨13, 2, 0, 518480, 294996, 1341, 16384⟩ := by
  decide +kernel

theorem context_13_294996_518480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 294996 ⟨518480, by decide⟩ :=
  accepted_of_selected 13 294996 ⟨518480, by decide⟩ ⟨13, 2, 0, 518480, 294996, 1341, 16384⟩
    (by decide) selected_cut_20253

theorem selected_cut_20254 : selected 8 ⟨518502, by decide⟩
    (prefixPartial 13 294997) = some ⟨13, 2, 0, 518502, 294997, 1241, 16384⟩ := by
  decide +kernel

theorem context_13_294997_518502 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 294997 ⟨518502, by decide⟩ :=
  accepted_of_selected 13 294997 ⟨518502, by decide⟩ ⟨13, 2, 0, 518502, 294997, 1241, 16384⟩
    (by decide) selected_cut_20254

theorem selected_cut_20255 : selected 8 ⟨518528, by decide⟩
    (prefixPartial 13 294998) = some ⟨13, 2, 0, 518528, 294998, 1745, 16384⟩ := by
  decide +kernel

theorem context_13_294998_518528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 294998 ⟨518528, by decide⟩ :=
  accepted_of_selected 13 294998 ⟨518528, by decide⟩ ⟨13, 2, 0, 518528, 294998, 1745, 16384⟩
    (by decide) selected_cut_20255

theorem selected_cut_20256 : selected 8 ⟨518545, by decide⟩
    (prefixPartial 13 294999) = some ⟨13, 2, 0, 518545, 294999, 781, 16384⟩ := by
  decide +kernel

theorem context_13_294999_518545 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 294999 ⟨518545, by decide⟩ :=
  accepted_of_selected 13 294999 ⟨518545, by decide⟩ ⟨13, 2, 0, 518545, 294999, 781, 16384⟩
    (by decide) selected_cut_20256

theorem unmarked_context_12_73749_518546 : frontier 9 ⟨518546, by decide⟩
    (prefixCache 12 73749) (prefixPartial 12 73749) = false := by
  decide +kernel

theorem node_context_12_73749_518546 : EJMOriginalGlobalDAGData.nodes 9 ⟨518546, by decide⟩ =
    .split (coordinate 12) (![⟨518480, by decide⟩,⟨518502, by decide⟩,⟨518528, by decide⟩,⟨518545, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_73749_518546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73749 ⟨518546, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 73749
    ⟨518546, by decide⟩ (by decide) (![⟨518480, by decide⟩,⟨518502, by decide⟩,⟨518528, by decide⟩,⟨518545, by decide⟩]) unmarked_context_12_73749_518546 node_context_12_73749_518546
  intro a
  fin_cases a
  · exact context_13_294996_518480
  · exact context_13_294997_518502
  · exact context_13_294998_518528
  · exact context_13_294999_518545

theorem selected_cut_20257 : selected 8 ⟨518572, by decide⟩
    (prefixPartial 13 295000) = some ⟨13, 2, 0, 518572, 295000, 1121, 16384⟩ := by
  decide +kernel

theorem context_13_295000_518572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 295000 ⟨518572, by decide⟩ :=
  accepted_of_selected 13 295000 ⟨518572, by decide⟩ ⟨13, 2, 0, 518572, 295000, 1121, 16384⟩
    (by decide) selected_cut_20257

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
