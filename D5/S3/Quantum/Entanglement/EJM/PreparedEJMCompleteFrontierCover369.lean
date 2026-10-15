/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover368
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_35427 : selected 9 ⟨931099, by decide⟩
    (prefixPartial 12 285573) = some ⟨12, 2, 0, 931099, 285573, 1149, 65536⟩ := by
  decide +kernel

theorem context_12_285573_931099 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285573 ⟨931099, by decide⟩ :=
  accepted_of_selected 12 285573 ⟨931099, by decide⟩ ⟨12, 2, 0, 931099, 285573, 1149, 65536⟩
    (by decide) selected_cut_35427

theorem selected_cut_35428 : selected 9 ⟨931114, by decide⟩
    (prefixPartial 12 285574) = some ⟨12, 2, 0, 931114, 285574, 1077, 65536⟩ := by
  decide +kernel

theorem context_12_285574_931114 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285574 ⟨931114, by decide⟩ :=
  accepted_of_selected 12 285574 ⟨931114, by decide⟩ ⟨12, 2, 0, 931114, 285574, 1077, 65536⟩
    (by decide) selected_cut_35428

theorem selected_cut_35429 : selected 9 ⟨931127, by decide⟩
    (prefixPartial 12 285575) = some ⟨12, 2, 0, 931127, 285575, 1089, 65536⟩ := by
  decide +kernel

theorem context_12_285575_931127 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285575 ⟨931127, by decide⟩ :=
  accepted_of_selected 12 285575 ⟨931127, by decide⟩ ⟨12, 2, 0, 931127, 285575, 1089, 65536⟩
    (by decide) selected_cut_35429

theorem unmarked_context_11_71393_931128 : frontier 10 ⟨931128, by decide⟩
    (prefixCache 11 71393) (prefixPartial 11 71393) = false := by
  decide +kernel

theorem node_context_11_71393_931128 : EJMOriginalGlobalDAGData.nodes 10 ⟨931128, by decide⟩ =
    .split (coordinate 11) (![⟨931082, by decide⟩,⟨931099, by decide⟩,⟨931114, by decide⟩,⟨931127, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71393_931128 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71393 ⟨931128, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71393
    ⟨931128, by decide⟩ (by decide) (![⟨931082, by decide⟩,⟨931099, by decide⟩,⟨931114, by decide⟩,⟨931127, by decide⟩]) unmarked_context_11_71393_931128 node_context_11_71393_931128
  intro a
  fin_cases a
  · exact context_12_285572_931082
  · exact context_12_285573_931099
  · exact context_12_285574_931114
  · exact context_12_285575_931127

theorem selected_cut_35430 : selected 9 ⟨931169, by decide⟩
    (prefixPartial 12 285576) = some ⟨12, 2, 0, 931169, 285576, 1681, 65536⟩ := by
  decide +kernel

theorem context_12_285576_931169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285576 ⟨931169, by decide⟩ :=
  accepted_of_selected 12 285576 ⟨931169, by decide⟩ ⟨12, 2, 0, 931169, 285576, 1681, 65536⟩
    (by decide) selected_cut_35430

theorem selected_cut_35431 : selected 9 ⟨931196, by decide⟩
    (prefixPartial 12 285577) = some ⟨12, 2, 0, 931196, 285577, 1345, 65536⟩ := by
  decide +kernel

theorem context_12_285577_931196 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285577 ⟨931196, by decide⟩ :=
  accepted_of_selected 12 285577 ⟨931196, by decide⟩ ⟨12, 2, 0, 931196, 285577, 1345, 65536⟩
    (by decide) selected_cut_35431

theorem selected_cut_35432 : selected 9 ⟨931215, by decide⟩
    (prefixPartial 12 285578) = some ⟨12, 2, 0, 931215, 285578, 1193, 65536⟩ := by
  decide +kernel

theorem context_12_285578_931215 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285578 ⟨931215, by decide⟩ :=
  accepted_of_selected 12 285578 ⟨931215, by decide⟩ ⟨12, 2, 0, 931215, 285578, 1193, 65536⟩
    (by decide) selected_cut_35432

theorem selected_cut_35433 : selected 9 ⟨931236, by decide⟩
    (prefixPartial 12 285579) = some ⟨12, 2, 0, 931236, 285579, 1273, 65536⟩ := by
  decide +kernel

theorem context_12_285579_931236 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285579 ⟨931236, by decide⟩ :=
  accepted_of_selected 12 285579 ⟨931236, by decide⟩ ⟨12, 2, 0, 931236, 285579, 1273, 65536⟩
    (by decide) selected_cut_35433

theorem unmarked_context_11_71394_931237 : frontier 10 ⟨931237, by decide⟩
    (prefixCache 11 71394) (prefixPartial 11 71394) = false := by
  decide +kernel

theorem node_context_11_71394_931237 : EJMOriginalGlobalDAGData.nodes 10 ⟨931237, by decide⟩ =
    .split (coordinate 11) (![⟨931169, by decide⟩,⟨931196, by decide⟩,⟨931215, by decide⟩,⟨931236, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71394_931237 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71394 ⟨931237, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71394
    ⟨931237, by decide⟩ (by decide) (![⟨931169, by decide⟩,⟨931196, by decide⟩,⟨931215, by decide⟩,⟨931236, by decide⟩]) unmarked_context_11_71394_931237 node_context_11_71394_931237
  intro a
  fin_cases a
  · exact context_12_285576_931169
  · exact context_12_285577_931196
  · exact context_12_285578_931215
  · exact context_12_285579_931236

theorem selected_cut_35434 : selected 10 ⟨931302, by decide⟩
    (prefixPartial 11 71395) = some ⟨11, 2, 0, 931302, 71395, 3557, 262144⟩ := by
  decide +kernel

theorem context_11_71395_931302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71395 ⟨931302, by decide⟩ :=
  accepted_of_selected 11 71395 ⟨931302, by decide⟩ ⟨11, 2, 0, 931302, 71395, 3557, 262144⟩
    (by decide) selected_cut_35434

theorem unmarked_context_10_17848_931303 : frontier 11 ⟨931303, by decide⟩
    (prefixCache 10 17848) (prefixPartial 10 17848) = false := by
  decide +kernel

theorem node_context_10_17848_931303 : EJMOriginalGlobalDAGData.nodes 11 ⟨931303, by decide⟩ =
    .split (coordinate 10) (![⟨931060, by decide⟩,⟨931128, by decide⟩,⟨931237, by decide⟩,⟨931302, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17848_931303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17848 ⟨931303, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17848
    ⟨931303, by decide⟩ (by decide) (![⟨931060, by decide⟩,⟨931128, by decide⟩,⟨931237, by decide⟩,⟨931302, by decide⟩]) unmarked_context_10_17848_931303 node_context_10_17848_931303
  intro a
  fin_cases a
  · exact context_11_71392_931060
  · exact context_11_71393_931128
  · exact context_11_71394_931237
  · exact context_11_71395_931302

theorem selected_cut_35435 : selected 10 ⟨931377, by decide⟩
    (prefixPartial 11 71396) = some ⟨11, 2, 0, 931377, 71396, 3937, 262144⟩ := by
  decide +kernel

theorem context_11_71396_931377 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71396 ⟨931377, by decide⟩ :=
  accepted_of_selected 11 71396 ⟨931377, by decide⟩ ⟨11, 2, 0, 931377, 71396, 3937, 262144⟩
    (by decide) selected_cut_35435

theorem selected_cut_35436 : selected 10 ⟨931426, by decide⟩
    (prefixPartial 11 71397) = some ⟨11, 2, 0, 931426, 71397, 3089, 262144⟩ := by
  decide +kernel

theorem context_11_71397_931426 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71397 ⟨931426, by decide⟩ :=
  accepted_of_selected 11 71397 ⟨931426, by decide⟩ ⟨11, 2, 0, 931426, 71397, 3089, 262144⟩
    (by decide) selected_cut_35436

theorem selected_cut_35437 : selected 10 ⟨931495, by decide⟩
    (prefixPartial 11 71398) = some ⟨11, 2, 0, 931495, 71398, 3561, 262144⟩ := by
  decide +kernel

theorem context_11_71398_931495 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71398 ⟨931495, by decide⟩ :=
  accepted_of_selected 11 71398 ⟨931495, by decide⟩ ⟨11, 2, 0, 931495, 71398, 3561, 262144⟩
    (by decide) selected_cut_35437

theorem selected_cut_35438 : selected 10 ⟨931544, by decide⟩
    (prefixPartial 11 71399) = some ⟨11, 2, 0, 931544, 71399, 2225, 262144⟩ := by
  decide +kernel

theorem context_11_71399_931544 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71399 ⟨931544, by decide⟩ :=
  accepted_of_selected 11 71399 ⟨931544, by decide⟩ ⟨11, 2, 0, 931544, 71399, 2225, 262144⟩
    (by decide) selected_cut_35438

theorem unmarked_context_10_17849_931545 : frontier 11 ⟨931545, by decide⟩
    (prefixCache 10 17849) (prefixPartial 10 17849) = false := by
  decide +kernel

theorem node_context_10_17849_931545 : EJMOriginalGlobalDAGData.nodes 11 ⟨931545, by decide⟩ =
    .split (coordinate 10) (![⟨931377, by decide⟩,⟨931426, by decide⟩,⟨931495, by decide⟩,⟨931544, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17849_931545 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17849 ⟨931545, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17849
    ⟨931545, by decide⟩ (by decide) (![⟨931377, by decide⟩,⟨931426, by decide⟩,⟨931495, by decide⟩,⟨931544, by decide⟩]) unmarked_context_10_17849_931545 node_context_10_17849_931545
  intro a
  fin_cases a
  · exact context_11_71396_931377
  · exact context_11_71397_931426
  · exact context_11_71398_931495
  · exact context_11_71399_931544

theorem selected_cut_35439 : selected 10 ⟨931594, by decide⟩
    (prefixPartial 11 71400) = some ⟨11, 2, 0, 931594, 71400, 2401, 262144⟩ := by
  decide +kernel

theorem context_11_71400_931594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71400 ⟨931594, by decide⟩ :=
  accepted_of_selected 11 71400 ⟨931594, by decide⟩ ⟨11, 2, 0, 931594, 71400, 2401, 262144⟩
    (by decide) selected_cut_35439

theorem selected_cut_35440 : selected 10 ⟨931626, by decide⟩
    (prefixPartial 11 71401) = some ⟨11, 2, 0, 931626, 71401, 1461, 262144⟩ := by
  decide +kernel

theorem context_11_71401_931626 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71401 ⟨931626, by decide⟩ :=
  accepted_of_selected 11 71401 ⟨931626, by decide⟩ ⟨11, 2, 0, 931626, 71401, 1461, 262144⟩
    (by decide) selected_cut_35440

theorem selected_cut_35441 : selected 10 ⟨906566, by decide⟩
    (prefixPartial 11 71402) = some ⟨11, 1, 0, 906566, 71402, 1, 262144⟩ := by
  decide +kernel

theorem context_11_71402_906566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71402 ⟨906566, by decide⟩ :=
  accepted_of_selected 11 71402 ⟨906566, by decide⟩ ⟨11, 1, 0, 906566, 71402, 1, 262144⟩
    (by decide) selected_cut_35441

theorem selected_cut_35442 : selected 10 ⟨931666, by decide⟩
    (prefixPartial 11 71403) = some ⟨11, 2, 0, 931666, 71403, 1577, 262144⟩ := by
  decide +kernel

theorem context_11_71403_931666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71403 ⟨931666, by decide⟩ :=
  accepted_of_selected 11 71403 ⟨931666, by decide⟩ ⟨11, 2, 0, 931666, 71403, 1577, 262144⟩
    (by decide) selected_cut_35442

theorem unmarked_context_10_17850_931667 : frontier 11 ⟨931667, by decide⟩
    (prefixCache 10 17850) (prefixPartial 10 17850) = false := by
  decide +kernel

theorem node_context_10_17850_931667 : EJMOriginalGlobalDAGData.nodes 11 ⟨931667, by decide⟩ =
    .split (coordinate 10) (![⟨931594, by decide⟩,⟨931626, by decide⟩,⟨906566, by decide⟩,⟨931666, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17850_931667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17850 ⟨931667, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17850
    ⟨931667, by decide⟩ (by decide) (![⟨931594, by decide⟩,⟨931626, by decide⟩,⟨906566, by decide⟩,⟨931666, by decide⟩]) unmarked_context_10_17850_931667 node_context_10_17850_931667
  intro a
  fin_cases a
  · exact context_11_71400_931594
  · exact context_11_71401_931626
  · exact context_11_71402_906566
  · exact context_11_71403_931666

theorem selected_cut_35443 : selected 10 ⟨931722, by decide⟩
    (prefixPartial 11 71404) = some ⟨11, 2, 0, 931722, 71404, 1961, 262144⟩ := by
  decide +kernel

theorem context_11_71404_931722 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71404 ⟨931722, by decide⟩ :=
  accepted_of_selected 11 71404 ⟨931722, by decide⟩ ⟨11, 2, 0, 931722, 71404, 1961, 262144⟩
    (by decide) selected_cut_35443

theorem selected_cut_35444 : selected 10 ⟨931758, by decide⟩
    (prefixPartial 11 71405) = some ⟨11, 2, 0, 931758, 71405, 1341, 262144⟩ := by
  decide +kernel

theorem context_11_71405_931758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71405 ⟨931758, by decide⟩ :=
  accepted_of_selected 11 71405 ⟨931758, by decide⟩ ⟨11, 2, 0, 931758, 71405, 1341, 262144⟩
    (by decide) selected_cut_35444

theorem selected_cut_35445 : selected 10 ⟨931791, by decide⟩
    (prefixPartial 11 71406) = some ⟨11, 2, 0, 931791, 71406, 1057, 262144⟩ := by
  decide +kernel

theorem context_11_71406_931791 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71406 ⟨931791, by decide⟩ :=
  accepted_of_selected 11 71406 ⟨931791, by decide⟩ ⟨11, 2, 0, 931791, 71406, 1057, 262144⟩
    (by decide) selected_cut_35445

theorem selected_cut_35446 : selected 10 ⟨931804, by decide⟩
    (prefixPartial 11 71407) = some ⟨11, 2, 0, 931804, 71407, 417, 262144⟩ := by
  decide +kernel

theorem context_11_71407_931804 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71407 ⟨931804, by decide⟩ :=
  accepted_of_selected 11 71407 ⟨931804, by decide⟩ ⟨11, 2, 0, 931804, 71407, 417, 262144⟩
    (by decide) selected_cut_35446

theorem unmarked_context_10_17851_931805 : frontier 11 ⟨931805, by decide⟩
    (prefixCache 10 17851) (prefixPartial 10 17851) = false := by
  decide +kernel

theorem node_context_10_17851_931805 : EJMOriginalGlobalDAGData.nodes 11 ⟨931805, by decide⟩ =
    .split (coordinate 10) (![⟨931722, by decide⟩,⟨931758, by decide⟩,⟨931791, by decide⟩,⟨931804, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17851_931805 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17851 ⟨931805, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17851
    ⟨931805, by decide⟩ (by decide) (![⟨931722, by decide⟩,⟨931758, by decide⟩,⟨931791, by decide⟩,⟨931804, by decide⟩]) unmarked_context_10_17851_931805 node_context_10_17851_931805
  intro a
  fin_cases a
  · exact context_11_71404_931722
  · exact context_11_71405_931758
  · exact context_11_71406_931791
  · exact context_11_71407_931804

theorem unmarked_context_9_4462_931806 : frontier 12 ⟨931806, by decide⟩
    (prefixCache 9 4462) (prefixPartial 9 4462) = false := by
  decide +kernel

theorem node_context_9_4462_931806 : EJMOriginalGlobalDAGData.nodes 12 ⟨931806, by decide⟩ =
    .split (coordinate 9) (![⟨931303, by decide⟩,⟨931545, by decide⟩,⟨931667, by decide⟩,⟨931805, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4462_931806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4462 ⟨931806, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4462
    ⟨931806, by decide⟩ (by decide) (![⟨931303, by decide⟩,⟨931545, by decide⟩,⟨931667, by decide⟩,⟨931805, by decide⟩]) unmarked_context_9_4462_931806 node_context_9_4462_931806
  intro a
  fin_cases a
  · exact context_10_17848_931303
  · exact context_10_17849_931545
  · exact context_10_17850_931667
  · exact context_10_17851_931805

theorem selected_cut_35447 : selected 12 ⟨116309, by decide⟩
    (prefixPartial 9 4463) = some ⟨9, 1, 0, 116309, 4463, 1, 4194304⟩ := by
  decide +kernel

theorem context_9_4463_116309 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4463 ⟨116309, by decide⟩ :=
  accepted_of_selected 9 4463 ⟨116309, by decide⟩ ⟨9, 1, 0, 116309, 4463, 1, 4194304⟩
    (by decide) selected_cut_35447

theorem unmarked_context_8_1115_931807 : frontier 13 ⟨931807, by decide⟩
    (prefixCache 8 1115) (prefixPartial 8 1115) = false := by
  decide +kernel

theorem node_context_8_1115_931807 : EJMOriginalGlobalDAGData.nodes 13 ⟨931807, by decide⟩ =
    .split (coordinate 8) (![⟨930380, by decide⟩,⟨930975, by decide⟩,⟨931806, by decide⟩,⟨116309, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1115_931807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1115 ⟨931807, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1115
    ⟨931807, by decide⟩ (by decide) (![⟨930380, by decide⟩,⟨930975, by decide⟩,⟨931806, by decide⟩,⟨116309, by decide⟩]) unmarked_context_8_1115_931807 node_context_8_1115_931807
  intro a
  fin_cases a
  · exact context_9_4460_930380
  · exact context_9_4461_930975
  · exact context_9_4462_931806
  · exact context_9_4463_116309

theorem unmarked_context_7_278_931808 : frontier 14 ⟨931808, by decide⟩
    (prefixCache 7 278) (prefixPartial 7 278) = false := by
  decide +kernel

theorem node_context_7_278_931808 : EJMOriginalGlobalDAGData.nodes 14 ⟨931808, by decide⟩ =
    .split (coordinate 7) (![⟨14300, by decide⟩,⟨14300, by decide⟩,⟨928720, by decide⟩,⟨931807, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_278_931808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 278 ⟨931808, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 278
    ⟨931808, by decide⟩ (by decide) (![⟨14300, by decide⟩,⟨14300, by decide⟩,⟨928720, by decide⟩,⟨931807, by decide⟩]) unmarked_context_7_278_931808 node_context_7_278_931808
  intro a
  fin_cases a
  · exact context_8_1112_14300
  · exact context_8_1113_14300
  · exact context_8_1114_928720
  · exact context_8_1115_931807

theorem selected_cut_35448 : selected 14 ⟨34032, by decide⟩
    (prefixPartial 7 279) = some ⟨7, 1, 0, 34032, 279, 1, 67108864⟩ := by
  decide +kernel

theorem context_7_279_34032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 279 ⟨34032, by decide⟩ :=
  accepted_of_selected 7 279 ⟨34032, by decide⟩ ⟨7, 1, 0, 34032, 279, 1, 67108864⟩
    (by decide) selected_cut_35448

theorem unmarked_context_6_69_931809 : frontier 15 ⟨931809, by decide⟩
    (prefixCache 6 69) (prefixPartial 6 69) = false := by
  decide +kernel

theorem node_context_6_69_931809 : EJMOriginalGlobalDAGData.nodes 15 ⟨931809, by decide⟩ =
    .split (coordinate 6) (![⟨916891, by decide⟩,⟨924241, by decide⟩,⟨931808, by decide⟩,⟨34032, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_6_69_931809 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 69 ⟨931809, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 6 69
    ⟨931809, by decide⟩ (by decide) (![⟨916891, by decide⟩,⟨924241, by decide⟩,⟨931808, by decide⟩,⟨34032, by decide⟩]) unmarked_context_6_69_931809 node_context_6_69_931809
  intro a
  fin_cases a
  · exact context_7_276_916891
  · exact context_7_277_924241
  · exact context_7_278_931808
  · exact context_7_279_34032

theorem selected_cut_35449 : selected 10 ⟨167448, by decide⟩
    (prefixPartial 11 71680) = some ⟨11, 1, 0, 167448, 71680, 1, 262144⟩ := by
  decide +kernel

theorem context_11_71680_167448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71680 ⟨167448, by decide⟩ :=
  accepted_of_selected 11 71680 ⟨167448, by decide⟩ ⟨11, 1, 0, 167448, 71680, 1, 262144⟩
    (by decide) selected_cut_35449

theorem selected_cut_35450 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 286724) = some ⟨12, 1, 0, 34034, 286724, 1, 65536⟩ := by
  decide +kernel

theorem context_12_286724_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286724 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 286724 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 286724, 1, 65536⟩
    (by decide) selected_cut_35450

theorem selected_cut_35451 : selected 9 ⟨931856, by decide⟩
    (prefixPartial 12 286725) = some ⟨12, 2, 0, 931856, 286725, 2737, 65536⟩ := by
  decide +kernel

theorem context_12_286725_931856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286725 ⟨931856, by decide⟩ :=
  accepted_of_selected 12 286725 ⟨931856, by decide⟩ ⟨12, 2, 0, 931856, 286725, 2737, 65536⟩
    (by decide) selected_cut_35451

theorem selected_cut_35452 : selected 9 ⟨931901, by decide⟩
    (prefixPartial 12 286726) = some ⟨12, 2, 0, 931901, 286726, 2885, 65536⟩ := by
  decide +kernel

theorem context_12_286726_931901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286726 ⟨931901, by decide⟩ :=
  accepted_of_selected 12 286726 ⟨931901, by decide⟩ ⟨12, 2, 0, 931901, 286726, 2885, 65536⟩
    (by decide) selected_cut_35452

theorem selected_cut_35453 : selected 9 ⟨931948, by decide⟩
    (prefixPartial 12 286727) = some ⟨12, 2, 0, 931948, 286727, 3121, 65536⟩ := by
  decide +kernel

theorem context_12_286727_931948 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286727 ⟨931948, by decide⟩ :=
  accepted_of_selected 12 286727 ⟨931948, by decide⟩ ⟨12, 2, 0, 931948, 286727, 3121, 65536⟩
    (by decide) selected_cut_35453

theorem unmarked_context_11_71681_931949 : frontier 10 ⟨931949, by decide⟩
    (prefixCache 11 71681) (prefixPartial 11 71681) = false := by
  decide +kernel

theorem node_context_11_71681_931949 : EJMOriginalGlobalDAGData.nodes 10 ⟨931949, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨931856, by decide⟩,⟨931901, by decide⟩,⟨931948, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71681_931949 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71681 ⟨931949, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71681
    ⟨931949, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨931856, by decide⟩,⟨931901, by decide⟩,⟨931948, by decide⟩]) unmarked_context_11_71681_931949 node_context_11_71681_931949
  intro a
  fin_cases a
  · exact context_12_286724_34034
  · exact context_12_286725_931856
  · exact context_12_286726_931901
  · exact context_12_286727_931948

theorem selected_cut_35454 : selected 9 ⟨932011, by decide⟩
    (prefixPartial 12 286728) = some ⟨12, 2, 0, 932011, 286728, 2345, 65536⟩ := by
  decide +kernel

theorem context_12_286728_932011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286728 ⟨932011, by decide⟩ :=
  accepted_of_selected 12 286728 ⟨932011, by decide⟩ ⟨12, 2, 0, 932011, 286728, 2345, 65536⟩
    (by decide) selected_cut_35454

theorem selected_cut_35455 : selected 9 ⟨932060, by decide⟩
    (prefixPartial 12 286729) = some ⟨12, 2, 0, 932060, 286729, 2989, 65536⟩ := by
  decide +kernel

theorem context_12_286729_932060 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286729 ⟨932060, by decide⟩ :=
  accepted_of_selected 12 286729 ⟨932060, by decide⟩ ⟨12, 2, 0, 932060, 286729, 2989, 65536⟩
    (by decide) selected_cut_35455

theorem selected_cut_35456 : selected 9 ⟨932106, by decide⟩
    (prefixPartial 12 286730) = some ⟨12, 2, 0, 932106, 286730, 2989, 65536⟩ := by
  decide +kernel

theorem context_12_286730_932106 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286730 ⟨932106, by decide⟩ :=
  accepted_of_selected 12 286730 ⟨932106, by decide⟩ ⟨12, 2, 0, 932106, 286730, 2989, 65536⟩
    (by decide) selected_cut_35456

theorem selected_cut_35457 : selected 9 ⟨932164, by decide⟩
    (prefixPartial 12 286731) = some ⟨12, 2, 0, 932164, 286731, 3509, 65536⟩ := by
  decide +kernel

theorem context_12_286731_932164 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286731 ⟨932164, by decide⟩ :=
  accepted_of_selected 12 286731 ⟨932164, by decide⟩ ⟨12, 2, 0, 932164, 286731, 3509, 65536⟩
    (by decide) selected_cut_35457

theorem unmarked_context_11_71682_932165 : frontier 10 ⟨932165, by decide⟩
    (prefixCache 11 71682) (prefixPartial 11 71682) = false := by
  decide +kernel

theorem node_context_11_71682_932165 : EJMOriginalGlobalDAGData.nodes 10 ⟨932165, by decide⟩ =
    .split (coordinate 11) (![⟨932011, by decide⟩,⟨932060, by decide⟩,⟨932106, by decide⟩,⟨932164, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71682_932165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71682 ⟨932165, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71682
    ⟨932165, by decide⟩ (by decide) (![⟨932011, by decide⟩,⟨932060, by decide⟩,⟨932106, by decide⟩,⟨932164, by decide⟩]) unmarked_context_11_71682_932165 node_context_11_71682_932165
  intro a
  fin_cases a
  · exact context_12_286728_932011
  · exact context_12_286729_932060
  · exact context_12_286730_932106
  · exact context_12_286731_932164

theorem selected_cut_35458 : selected 9 ⟨932211, by decide⟩
    (prefixPartial 12 286732) = some ⟨12, 2, 0, 932211, 286732, 973, 65536⟩ := by
  decide +kernel

theorem context_12_286732_932211 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286732 ⟨932211, by decide⟩ :=
  accepted_of_selected 12 286732 ⟨932211, by decide⟩ ⟨12, 2, 0, 932211, 286732, 973, 65536⟩
    (by decide) selected_cut_35458

theorem selected_cut_35459 : selected 9 ⟨932251, by decide⟩
    (prefixPartial 12 286733) = some ⟨12, 2, 0, 932251, 286733, 2657, 65536⟩ := by
  decide +kernel

theorem context_12_286733_932251 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286733 ⟨932251, by decide⟩ :=
  accepted_of_selected 12 286733 ⟨932251, by decide⟩ ⟨12, 2, 0, 932251, 286733, 2657, 65536⟩
    (by decide) selected_cut_35459

theorem selected_cut_35460 : selected 9 ⟨932294, by decide⟩
    (prefixPartial 12 286734) = some ⟨12, 2, 0, 932294, 286734, 2821, 65536⟩ := by
  decide +kernel

theorem context_12_286734_932294 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286734 ⟨932294, by decide⟩ :=
  accepted_of_selected 12 286734 ⟨932294, by decide⟩ ⟨12, 2, 0, 932294, 286734, 2821, 65536⟩
    (by decide) selected_cut_35460

theorem selected_cut_35461 : selected 9 ⟨932338, by decide⟩
    (prefixPartial 12 286735) = some ⟨12, 2, 0, 932338, 286735, 2777, 65536⟩ := by
  decide +kernel

theorem context_12_286735_932338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286735 ⟨932338, by decide⟩ :=
  accepted_of_selected 12 286735 ⟨932338, by decide⟩ ⟨12, 2, 0, 932338, 286735, 2777, 65536⟩
    (by decide) selected_cut_35461

theorem unmarked_context_11_71683_932339 : frontier 10 ⟨932339, by decide⟩
    (prefixCache 11 71683) (prefixPartial 11 71683) = false := by
  decide +kernel

theorem node_context_11_71683_932339 : EJMOriginalGlobalDAGData.nodes 10 ⟨932339, by decide⟩ =
    .split (coordinate 11) (![⟨932211, by decide⟩,⟨932251, by decide⟩,⟨932294, by decide⟩,⟨932338, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71683_932339 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71683 ⟨932339, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71683
    ⟨932339, by decide⟩ (by decide) (![⟨932211, by decide⟩,⟨932251, by decide⟩,⟨932294, by decide⟩,⟨932338, by decide⟩]) unmarked_context_11_71683_932339 node_context_11_71683_932339
  intro a
  fin_cases a
  · exact context_12_286732_932211
  · exact context_12_286733_932251
  · exact context_12_286734_932294
  · exact context_12_286735_932338

theorem unmarked_context_10_17920_932340 : frontier 11 ⟨932340, by decide⟩
    (prefixCache 10 17920) (prefixPartial 10 17920) = false := by
  decide +kernel

theorem node_context_10_17920_932340 : EJMOriginalGlobalDAGData.nodes 11 ⟨932340, by decide⟩ =
    .split (coordinate 10) (![⟨167448, by decide⟩,⟨931949, by decide⟩,⟨932165, by decide⟩,⟨932339, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17920_932340 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17920 ⟨932340, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17920
    ⟨932340, by decide⟩ (by decide) (![⟨167448, by decide⟩,⟨931949, by decide⟩,⟨932165, by decide⟩,⟨932339, by decide⟩]) unmarked_context_10_17920_932340 node_context_10_17920_932340
  intro a
  fin_cases a
  · exact context_11_71680_167448
  · exact context_11_71681_931949
  · exact context_11_71682_932165
  · exact context_11_71683_932339

theorem selected_cut_35462 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 286736) = some ⟨12, 1, 0, 1738, 286736, 1, 65536⟩ := by
  decide +kernel

theorem context_12_286736_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286736 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 286736 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 286736, 1, 65536⟩
    (by decide) selected_cut_35462

theorem selected_cut_35463 : selected 9 ⟨932371, by decide⟩
    (prefixPartial 12 286737) = some ⟨12, 2, 0, 932371, 286737, 1493, 65536⟩ := by
  decide +kernel

theorem context_12_286737_932371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286737 ⟨932371, by decide⟩ :=
  accepted_of_selected 12 286737 ⟨932371, by decide⟩ ⟨12, 2, 0, 932371, 286737, 1493, 65536⟩
    (by decide) selected_cut_35463

theorem selected_cut_35464 : selected 9 ⟨932399, by decide⟩
    (prefixPartial 12 286738) = some ⟨12, 2, 0, 932399, 286738, 2105, 65536⟩ := by
  decide +kernel

theorem context_12_286738_932399 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286738 ⟨932399, by decide⟩ :=
  accepted_of_selected 12 286738 ⟨932399, by decide⟩ ⟨12, 2, 0, 932399, 286738, 2105, 65536⟩
    (by decide) selected_cut_35464

theorem selected_cut_35465 : selected 9 ⟨932429, by decide⟩
    (prefixPartial 12 286739) = some ⟨12, 2, 0, 932429, 286739, 2269, 65536⟩ := by
  decide +kernel

theorem context_12_286739_932429 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286739 ⟨932429, by decide⟩ :=
  accepted_of_selected 12 286739 ⟨932429, by decide⟩ ⟨12, 2, 0, 932429, 286739, 2269, 65536⟩
    (by decide) selected_cut_35465

theorem unmarked_context_11_71684_932430 : frontier 10 ⟨932430, by decide⟩
    (prefixCache 11 71684) (prefixPartial 11 71684) = false := by
  decide +kernel

theorem node_context_11_71684_932430 : EJMOriginalGlobalDAGData.nodes 10 ⟨932430, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨932371, by decide⟩,⟨932399, by decide⟩,⟨932429, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71684_932430 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71684 ⟨932430, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71684
    ⟨932430, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨932371, by decide⟩,⟨932399, by decide⟩,⟨932429, by decide⟩]) unmarked_context_11_71684_932430 node_context_11_71684_932430
  intro a
  fin_cases a
  · exact context_12_286736_1738
  · exact context_12_286737_932371
  · exact context_12_286738_932399
  · exact context_12_286739_932429

theorem selected_cut_35466 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 286740) = some ⟨12, 1, 0, 1738, 286740, 1, 65536⟩ := by
  decide +kernel

theorem context_12_286740_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286740 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 286740 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 286740, 1, 65536⟩
    (by decide) selected_cut_35466

theorem selected_cut_35467 : selected 9 ⟨68180, by decide⟩
    (prefixPartial 12 286741) = some ⟨12, 1, 0, 68180, 286741, 1, 65536⟩ := by
  decide +kernel

theorem context_12_286741_68180 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286741 ⟨68180, by decide⟩ :=
  accepted_of_selected 12 286741 ⟨68180, by decide⟩ ⟨12, 1, 0, 68180, 286741, 1, 65536⟩
    (by decide) selected_cut_35467

theorem selected_cut_35468 : selected 9 ⟨932469, by decide⟩
    (prefixPartial 12 286742) = some ⟨12, 2, 0, 932469, 286742, 2353, 65536⟩ := by
  decide +kernel

theorem context_12_286742_932469 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286742 ⟨932469, by decide⟩ :=
  accepted_of_selected 12 286742 ⟨932469, by decide⟩ ⟨12, 2, 0, 932469, 286742, 2353, 65536⟩
    (by decide) selected_cut_35468

theorem selected_cut_35469 : selected 9 ⟨932509, by decide⟩
    (prefixPartial 12 286743) = some ⟨12, 2, 0, 932509, 286743, 2457, 65536⟩ := by
  decide +kernel

theorem context_12_286743_932509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286743 ⟨932509, by decide⟩ :=
  accepted_of_selected 12 286743 ⟨932509, by decide⟩ ⟨12, 2, 0, 932509, 286743, 2457, 65536⟩
    (by decide) selected_cut_35469

theorem unmarked_context_11_71685_932510 : frontier 10 ⟨932510, by decide⟩
    (prefixCache 11 71685) (prefixPartial 11 71685) = false := by
  decide +kernel

theorem node_context_11_71685_932510 : EJMOriginalGlobalDAGData.nodes 10 ⟨932510, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨68180, by decide⟩,⟨932469, by decide⟩,⟨932509, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71685_932510 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71685 ⟨932510, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71685
    ⟨932510, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨68180, by decide⟩,⟨932469, by decide⟩,⟨932509, by decide⟩]) unmarked_context_11_71685_932510 node_context_11_71685_932510
  intro a
  fin_cases a
  · exact context_12_286740_1738
  · exact context_12_286741_68180
  · exact context_12_286742_932469
  · exact context_12_286743_932509

theorem selected_cut_35470 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 286744) = some ⟨12, 1, 0, 1738, 286744, 1, 65536⟩ := by
  decide +kernel

theorem context_12_286744_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286744 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 286744 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 286744, 1, 65536⟩
    (by decide) selected_cut_35470

theorem selected_cut_35471 : selected 9 ⟨932548, by decide⟩
    (prefixPartial 12 286745) = some ⟨12, 2, 0, 932548, 286745, 1797, 65536⟩ := by
  decide +kernel

theorem context_12_286745_932548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286745 ⟨932548, by decide⟩ :=
  accepted_of_selected 12 286745 ⟨932548, by decide⟩ ⟨12, 2, 0, 932548, 286745, 1797, 65536⟩
    (by decide) selected_cut_35471

theorem selected_cut_35472 : selected 9 ⟨932582, by decide⟩
    (prefixPartial 12 286746) = some ⟨12, 2, 0, 932582, 286746, 2541, 65536⟩ := by
  decide +kernel

theorem context_12_286746_932582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286746 ⟨932582, by decide⟩ :=
  accepted_of_selected 12 286746 ⟨932582, by decide⟩ ⟨12, 2, 0, 932582, 286746, 2541, 65536⟩
    (by decide) selected_cut_35472

theorem selected_cut_35473 : selected 9 ⟨932627, by decide⟩
    (prefixPartial 12 286747) = some ⟨12, 2, 0, 932627, 286747, 2833, 65536⟩ := by
  decide +kernel

theorem context_12_286747_932627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286747 ⟨932627, by decide⟩ :=
  accepted_of_selected 12 286747 ⟨932627, by decide⟩ ⟨12, 2, 0, 932627, 286747, 2833, 65536⟩
    (by decide) selected_cut_35473

theorem unmarked_context_11_71686_932628 : frontier 10 ⟨932628, by decide⟩
    (prefixCache 11 71686) (prefixPartial 11 71686) = false := by
  decide +kernel

theorem node_context_11_71686_932628 : EJMOriginalGlobalDAGData.nodes 10 ⟨932628, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨932548, by decide⟩,⟨932582, by decide⟩,⟨932627, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71686_932628 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71686 ⟨932628, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71686
    ⟨932628, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨932548, by decide⟩,⟨932582, by decide⟩,⟨932627, by decide⟩]) unmarked_context_11_71686_932628 node_context_11_71686_932628
  intro a
  fin_cases a
  · exact context_12_286744_1738
  · exact context_12_286745_932548
  · exact context_12_286746_932582
  · exact context_12_286747_932627

theorem selected_cut_35474 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 286748) = some ⟨12, 1, 0, 1738, 286748, 1, 65536⟩ := by
  decide +kernel

theorem context_12_286748_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286748 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 286748 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 286748, 1, 65536⟩
    (by decide) selected_cut_35474

theorem selected_cut_35475 : selected 9 ⟨932662, by decide⟩
    (prefixPartial 12 286749) = some ⟨12, 2, 0, 932662, 286749, 1753, 65536⟩ := by
  decide +kernel

theorem context_12_286749_932662 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286749 ⟨932662, by decide⟩ :=
  accepted_of_selected 12 286749 ⟨932662, by decide⟩ ⟨12, 2, 0, 932662, 286749, 1753, 65536⟩
    (by decide) selected_cut_35475

theorem selected_cut_35476 : selected 9 ⟨932704, by decide⟩
    (prefixPartial 12 286750) = some ⟨12, 2, 0, 932704, 286750, 2565, 65536⟩ := by
  decide +kernel

theorem context_12_286750_932704 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286750 ⟨932704, by decide⟩ :=
  accepted_of_selected 12 286750 ⟨932704, by decide⟩ ⟨12, 2, 0, 932704, 286750, 2565, 65536⟩
    (by decide) selected_cut_35476

theorem selected_cut_35477 : selected 9 ⟨932738, by decide⟩
    (prefixPartial 12 286751) = some ⟨12, 2, 0, 932738, 286751, 2481, 65536⟩ := by
  decide +kernel

theorem context_12_286751_932738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286751 ⟨932738, by decide⟩ :=
  accepted_of_selected 12 286751 ⟨932738, by decide⟩ ⟨12, 2, 0, 932738, 286751, 2481, 65536⟩
    (by decide) selected_cut_35477

theorem unmarked_context_11_71687_932739 : frontier 10 ⟨932739, by decide⟩
    (prefixCache 11 71687) (prefixPartial 11 71687) = false := by
  decide +kernel

theorem node_context_11_71687_932739 : EJMOriginalGlobalDAGData.nodes 10 ⟨932739, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨932662, by decide⟩,⟨932704, by decide⟩,⟨932738, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71687_932739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71687 ⟨932739, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71687
    ⟨932739, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨932662, by decide⟩,⟨932704, by decide⟩,⟨932738, by decide⟩]) unmarked_context_11_71687_932739 node_context_11_71687_932739
  intro a
  fin_cases a
  · exact context_12_286748_1738
  · exact context_12_286749_932662
  · exact context_12_286750_932704
  · exact context_12_286751_932738

theorem unmarked_context_10_17921_932740 : frontier 11 ⟨932740, by decide⟩
    (prefixCache 10 17921) (prefixPartial 10 17921) = false := by
  decide +kernel

theorem node_context_10_17921_932740 : EJMOriginalGlobalDAGData.nodes 11 ⟨932740, by decide⟩ =
    .split (coordinate 10) (![⟨932430, by decide⟩,⟨932510, by decide⟩,⟨932628, by decide⟩,⟨932739, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17921_932740 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17921 ⟨932740, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17921
    ⟨932740, by decide⟩ (by decide) (![⟨932430, by decide⟩,⟨932510, by decide⟩,⟨932628, by decide⟩,⟨932739, by decide⟩]) unmarked_context_10_17921_932740 node_context_10_17921_932740
  intro a
  fin_cases a
  · exact context_11_71684_932430
  · exact context_11_71685_932510
  · exact context_11_71686_932628
  · exact context_11_71687_932739

theorem selected_cut_35478 : selected 10 ⟨932802, by decide⟩
    (prefixPartial 11 71688) = some ⟨11, 2, 0, 932802, 71688, 3577, 262144⟩ := by
  decide +kernel

theorem context_11_71688_932802 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71688 ⟨932802, by decide⟩ :=
  accepted_of_selected 11 71688 ⟨932802, by decide⟩ ⟨11, 2, 0, 932802, 71688, 3577, 262144⟩
    (by decide) selected_cut_35478

theorem selected_cut_35479 : selected 10 ⟨932873, by decide⟩
    (prefixPartial 11 71689) = some ⟨11, 2, 0, 932873, 71689, 4013, 262144⟩ := by
  decide +kernel

theorem context_11_71689_932873 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71689 ⟨932873, by decide⟩ :=
  accepted_of_selected 11 71689 ⟨932873, by decide⟩ ⟨11, 2, 0, 932873, 71689, 4013, 262144⟩
    (by decide) selected_cut_35479

theorem selected_cut_35480 : selected 10 ⟨932922, by decide⟩
    (prefixPartial 11 71690) = some ⟨11, 2, 0, 932922, 71690, 2665, 262144⟩ := by
  decide +kernel

theorem context_11_71690_932922 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71690 ⟨932922, by decide⟩ :=
  accepted_of_selected 11 71690 ⟨932922, by decide⟩ ⟨11, 2, 0, 932922, 71690, 2665, 262144⟩
    (by decide) selected_cut_35480

theorem selected_cut_35481 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 286764) = some ⟨12, 1, 0, 1738, 286764, 1, 65536⟩ := by
  decide +kernel

theorem context_12_286764_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286764 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 286764 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 286764, 1, 65536⟩
    (by decide) selected_cut_35481

theorem selected_cut_35482 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 286765) = some ⟨12, 1, 0, 1738, 286765, 1, 65536⟩ := by
  decide +kernel

theorem context_12_286765_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286765 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 286765 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 286765, 1, 65536⟩
    (by decide) selected_cut_35482

theorem selected_cut_35483 : selected 9 ⟨932972, by decide⟩
    (prefixPartial 12 286766) = some ⟨12, 2, 0, 932972, 286766, 2017, 65536⟩ := by
  decide +kernel

theorem context_12_286766_932972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286766 ⟨932972, by decide⟩ :=
  accepted_of_selected 12 286766 ⟨932972, by decide⟩ ⟨12, 2, 0, 932972, 286766, 2017, 65536⟩
    (by decide) selected_cut_35483

theorem selected_cut_35484 : selected 9 ⟨933009, by decide⟩
    (prefixPartial 12 286767) = some ⟨12, 2, 0, 933009, 286767, 2413, 65536⟩ := by
  decide +kernel

theorem context_12_286767_933009 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286767 ⟨933009, by decide⟩ :=
  accepted_of_selected 12 286767 ⟨933009, by decide⟩ ⟨12, 2, 0, 933009, 286767, 2413, 65536⟩
    (by decide) selected_cut_35484

theorem unmarked_context_11_71691_933010 : frontier 10 ⟨933010, by decide⟩
    (prefixCache 11 71691) (prefixPartial 11 71691) = false := by
  decide +kernel

theorem node_context_11_71691_933010 : EJMOriginalGlobalDAGData.nodes 10 ⟨933010, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨932972, by decide⟩,⟨933009, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71691_933010 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71691 ⟨933010, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71691
    ⟨933010, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨932972, by decide⟩,⟨933009, by decide⟩]) unmarked_context_11_71691_933010 node_context_11_71691_933010
  intro a
  fin_cases a
  · exact context_12_286764_1738
  · exact context_12_286765_1738
  · exact context_12_286766_932972
  · exact context_12_286767_933009

theorem unmarked_context_10_17922_933011 : frontier 11 ⟨933011, by decide⟩
    (prefixCache 10 17922) (prefixPartial 10 17922) = false := by
  decide +kernel

theorem node_context_10_17922_933011 : EJMOriginalGlobalDAGData.nodes 11 ⟨933011, by decide⟩ =
    .split (coordinate 10) (![⟨932802, by decide⟩,⟨932873, by decide⟩,⟨932922, by decide⟩,⟨933010, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17922_933011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17922 ⟨933011, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17922
    ⟨933011, by decide⟩ (by decide) (![⟨932802, by decide⟩,⟨932873, by decide⟩,⟨932922, by decide⟩,⟨933010, by decide⟩]) unmarked_context_10_17922_933011 node_context_10_17922_933011
  intro a
  fin_cases a
  · exact context_11_71688_932802
  · exact context_11_71689_932873
  · exact context_11_71690_932922
  · exact context_11_71691_933010

theorem selected_cut_35485 : selected 10 ⟨933044, by decide⟩
    (prefixPartial 11 71692) = some ⟨11, 2, 0, 933044, 71692, 1561, 262144⟩ := by
  decide +kernel

theorem context_11_71692_933044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71692 ⟨933044, by decide⟩ :=
  accepted_of_selected 11 71692 ⟨933044, by decide⟩ ⟨11, 2, 0, 933044, 71692, 1561, 262144⟩
    (by decide) selected_cut_35485

theorem selected_cut_35486 : selected 10 ⟨933080, by decide⟩
    (prefixPartial 11 71693) = some ⟨11, 2, 0, 933080, 71693, 1701, 262144⟩ := by
  decide +kernel

theorem context_11_71693_933080 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71693 ⟨933080, by decide⟩ :=
  accepted_of_selected 11 71693 ⟨933080, by decide⟩ ⟨11, 2, 0, 933080, 71693, 1701, 262144⟩
    (by decide) selected_cut_35486

theorem selected_cut_35487 : selected 10 ⟨933127, by decide⟩
    (prefixPartial 11 71694) = some ⟨11, 2, 0, 933127, 71694, 2153, 262144⟩ := by
  decide +kernel

theorem context_11_71694_933127 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71694 ⟨933127, by decide⟩ :=
  accepted_of_selected 11 71694 ⟨933127, by decide⟩ ⟨11, 2, 0, 933127, 71694, 2153, 262144⟩
    (by decide) selected_cut_35487

theorem selected_cut_35488 : selected 10 ⟨933128, by decide⟩
    (prefixPartial 11 71695) = some ⟨11, 2, 0, 933128, 71695, 5, 262144⟩ := by
  decide +kernel

theorem context_11_71695_933128 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71695 ⟨933128, by decide⟩ :=
  accepted_of_selected 11 71695 ⟨933128, by decide⟩ ⟨11, 2, 0, 933128, 71695, 5, 262144⟩
    (by decide) selected_cut_35488

theorem unmarked_context_10_17923_933129 : frontier 11 ⟨933129, by decide⟩
    (prefixCache 10 17923) (prefixPartial 10 17923) = false := by
  decide +kernel

theorem node_context_10_17923_933129 : EJMOriginalGlobalDAGData.nodes 11 ⟨933129, by decide⟩ =
    .split (coordinate 10) (![⟨933044, by decide⟩,⟨933080, by decide⟩,⟨933127, by decide⟩,⟨933128, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17923_933129 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17923 ⟨933129, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17923
    ⟨933129, by decide⟩ (by decide) (![⟨933044, by decide⟩,⟨933080, by decide⟩,⟨933127, by decide⟩,⟨933128, by decide⟩]) unmarked_context_10_17923_933129 node_context_10_17923_933129
  intro a
  fin_cases a
  · exact context_11_71692_933044
  · exact context_11_71693_933080
  · exact context_11_71694_933127
  · exact context_11_71695_933128

theorem unmarked_context_9_4480_933130 : frontier 12 ⟨933130, by decide⟩
    (prefixCache 9 4480) (prefixPartial 9 4480) = false := by
  decide +kernel

theorem node_context_9_4480_933130 : EJMOriginalGlobalDAGData.nodes 12 ⟨933130, by decide⟩ =
    .split (coordinate 9) (![⟨932340, by decide⟩,⟨932740, by decide⟩,⟨933011, by decide⟩,⟨933129, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4480_933130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4480 ⟨933130, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4480
    ⟨933130, by decide⟩ (by decide) (![⟨932340, by decide⟩,⟨932740, by decide⟩,⟨933011, by decide⟩,⟨933129, by decide⟩]) unmarked_context_9_4480_933130 node_context_9_4480_933130
  intro a
  fin_cases a
  · exact context_10_17920_932340
  · exact context_10_17921_932740
  · exact context_10_17922_933011
  · exact context_10_17923_933129

theorem selected_cut_35489 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 71696) = some ⟨11, 1, 0, 907917, 71696, 1, 262144⟩ := by
  decide +kernel

theorem context_11_71696_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71696 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 71696 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 71696, 1, 262144⟩
    (by decide) selected_cut_35489

theorem selected_cut_35490 : selected 9 ⟨933154, by decide⟩
    (prefixPartial 12 286788) = some ⟨12, 2, 0, 933154, 286788, 1321, 65536⟩ := by
  decide +kernel

theorem context_12_286788_933154 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286788 ⟨933154, by decide⟩ :=
  accepted_of_selected 12 286788 ⟨933154, by decide⟩ ⟨12, 2, 0, 933154, 286788, 1321, 65536⟩
    (by decide) selected_cut_35490

theorem selected_cut_35491 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 286789) = some ⟨12, 1, 0, 896706, 286789, 1, 65536⟩ := by
  decide +kernel

theorem context_12_286789_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286789 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 286789 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 286789, 1, 65536⟩
    (by decide) selected_cut_35491

theorem selected_cut_35492 : selected 9 ⟨933181, by decide⟩
    (prefixPartial 12 286790) = some ⟨12, 2, 0, 933181, 286790, 1989, 65536⟩ := by
  decide +kernel

theorem context_12_286790_933181 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286790 ⟨933181, by decide⟩ :=
  accepted_of_selected 12 286790 ⟨933181, by decide⟩ ⟨12, 2, 0, 933181, 286790, 1989, 65536⟩
    (by decide) selected_cut_35492

theorem selected_cut_35493 : selected 9 ⟨933214, by decide⟩
    (prefixPartial 12 286791) = some ⟨12, 2, 0, 933214, 286791, 2153, 65536⟩ := by
  decide +kernel

theorem context_12_286791_933214 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286791 ⟨933214, by decide⟩ :=
  accepted_of_selected 12 286791 ⟨933214, by decide⟩ ⟨12, 2, 0, 933214, 286791, 2153, 65536⟩
    (by decide) selected_cut_35493

theorem unmarked_context_11_71697_933215 : frontier 10 ⟨933215, by decide⟩
    (prefixCache 11 71697) (prefixPartial 11 71697) = false := by
  decide +kernel

theorem node_context_11_71697_933215 : EJMOriginalGlobalDAGData.nodes 10 ⟨933215, by decide⟩ =
    .split (coordinate 11) (![⟨933154, by decide⟩,⟨896706, by decide⟩,⟨933181, by decide⟩,⟨933214, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71697_933215 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71697 ⟨933215, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71697
    ⟨933215, by decide⟩ (by decide) (![⟨933154, by decide⟩,⟨896706, by decide⟩,⟨933181, by decide⟩,⟨933214, by decide⟩]) unmarked_context_11_71697_933215 node_context_11_71697_933215
  intro a
  fin_cases a
  · exact context_12_286788_933154
  · exact context_12_286789_896706
  · exact context_12_286790_933181
  · exact context_12_286791_933214

theorem selected_cut_35494 : selected 9 ⟨933241, by decide⟩
    (prefixPartial 12 286792) = some ⟨12, 2, 0, 933241, 286792, 1525, 65536⟩ := by
  decide +kernel

theorem context_12_286792_933241 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286792 ⟨933241, by decide⟩ :=
  accepted_of_selected 12 286792 ⟨933241, by decide⟩ ⟨12, 2, 0, 933241, 286792, 1525, 65536⟩
    (by decide) selected_cut_35494

theorem selected_cut_35495 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 286793) = some ⟨12, 1, 0, 896706, 286793, 1, 65536⟩ := by
  decide +kernel

theorem context_12_286793_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286793 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 286793 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 286793, 1, 65536⟩
    (by decide) selected_cut_35495

theorem selected_cut_35496 : selected 9 ⟨933276, by decide⟩
    (prefixPartial 12 286794) = some ⟨12, 2, 0, 933276, 286794, 2225, 65536⟩ := by
  decide +kernel

theorem context_12_286794_933276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286794 ⟨933276, by decide⟩ :=
  accepted_of_selected 12 286794 ⟨933276, by decide⟩ ⟨12, 2, 0, 933276, 286794, 2225, 65536⟩
    (by decide) selected_cut_35496

theorem selected_cut_35497 : selected 9 ⟨933326, by decide⟩
    (prefixPartial 12 286795) = some ⟨12, 2, 0, 933326, 286795, 2581, 65536⟩ := by
  decide +kernel

theorem context_12_286795_933326 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286795 ⟨933326, by decide⟩ :=
  accepted_of_selected 12 286795 ⟨933326, by decide⟩ ⟨12, 2, 0, 933326, 286795, 2581, 65536⟩
    (by decide) selected_cut_35497

theorem unmarked_context_11_71698_933327 : frontier 10 ⟨933327, by decide⟩
    (prefixCache 11 71698) (prefixPartial 11 71698) = false := by
  decide +kernel

theorem node_context_11_71698_933327 : EJMOriginalGlobalDAGData.nodes 10 ⟨933327, by decide⟩ =
    .split (coordinate 11) (![⟨933241, by decide⟩,⟨896706, by decide⟩,⟨933276, by decide⟩,⟨933326, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71698_933327 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71698 ⟨933327, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71698
    ⟨933327, by decide⟩ (by decide) (![⟨933241, by decide⟩,⟨896706, by decide⟩,⟨933276, by decide⟩,⟨933326, by decide⟩]) unmarked_context_11_71698_933327 node_context_11_71698_933327
  intro a
  fin_cases a
  · exact context_12_286792_933241
  · exact context_12_286793_896706
  · exact context_12_286794_933276
  · exact context_12_286795_933326

theorem selected_cut_35498 : selected 9 ⟨933348, by decide⟩
    (prefixPartial 12 286796) = some ⟨12, 2, 0, 933348, 286796, 1277, 65536⟩ := by
  decide +kernel

theorem context_12_286796_933348 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286796 ⟨933348, by decide⟩ :=
  accepted_of_selected 12 286796 ⟨933348, by decide⟩ ⟨12, 2, 0, 933348, 286796, 1277, 65536⟩
    (by decide) selected_cut_35498

theorem selected_cut_35499 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 286797) = some ⟨12, 1, 0, 896706, 286797, 1, 65536⟩ := by
  decide +kernel

theorem context_12_286797_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286797 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 286797 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 286797, 1, 65536⟩
    (by decide) selected_cut_35499

theorem selected_cut_35500 : selected 9 ⟨933388, by decide⟩
    (prefixPartial 12 286798) = some ⟨12, 2, 0, 933388, 286798, 2269, 65536⟩ := by
  decide +kernel

theorem context_12_286798_933388 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286798 ⟨933388, by decide⟩ :=
  accepted_of_selected 12 286798 ⟨933388, by decide⟩ ⟨12, 2, 0, 933388, 286798, 2269, 65536⟩
    (by decide) selected_cut_35500

theorem selected_cut_35501 : selected 9 ⟨933429, by decide⟩
    (prefixPartial 12 286799) = some ⟨12, 2, 0, 933429, 286799, 2237, 65536⟩ := by
  decide +kernel

theorem context_12_286799_933429 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286799 ⟨933429, by decide⟩ :=
  accepted_of_selected 12 286799 ⟨933429, by decide⟩ ⟨12, 2, 0, 933429, 286799, 2237, 65536⟩
    (by decide) selected_cut_35501

theorem unmarked_context_11_71699_933430 : frontier 10 ⟨933430, by decide⟩
    (prefixCache 11 71699) (prefixPartial 11 71699) = false := by
  decide +kernel

theorem node_context_11_71699_933430 : EJMOriginalGlobalDAGData.nodes 10 ⟨933430, by decide⟩ =
    .split (coordinate 11) (![⟨933348, by decide⟩,⟨896706, by decide⟩,⟨933388, by decide⟩,⟨933429, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71699_933430 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71699 ⟨933430, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71699
    ⟨933430, by decide⟩ (by decide) (![⟨933348, by decide⟩,⟨896706, by decide⟩,⟨933388, by decide⟩,⟨933429, by decide⟩]) unmarked_context_11_71699_933430 node_context_11_71699_933430
  intro a
  fin_cases a
  · exact context_12_286796_933348
  · exact context_12_286797_896706
  · exact context_12_286798_933388
  · exact context_12_286799_933429

theorem unmarked_context_10_17924_933431 : frontier 11 ⟨933431, by decide⟩
    (prefixCache 10 17924) (prefixPartial 10 17924) = false := by
  decide +kernel

theorem node_context_10_17924_933431 : EJMOriginalGlobalDAGData.nodes 11 ⟨933431, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨933215, by decide⟩,⟨933327, by decide⟩,⟨933430, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17924_933431 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17924 ⟨933431, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17924
    ⟨933431, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨933215, by decide⟩,⟨933327, by decide⟩,⟨933430, by decide⟩]) unmarked_context_10_17924_933431 node_context_10_17924_933431
  intro a
  fin_cases a
  · exact context_11_71696_907917
  · exact context_11_71697_933215
  · exact context_11_71698_933327
  · exact context_11_71699_933430

theorem selected_cut_35502 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 17925) = some ⟨10, 1, 0, 893098, 17925, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_17925_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17925 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 17925 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 17925, 1, 1048576⟩
    (by decide) selected_cut_35502

theorem selected_cut_35503 : selected 10 ⟨933491, by decide⟩
    (prefixPartial 11 71704) = some ⟨11, 2, 0, 933491, 71704, 2961, 262144⟩ := by
  decide +kernel

theorem context_11_71704_933491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71704 ⟨933491, by decide⟩ :=
  accepted_of_selected 11 71704 ⟨933491, by decide⟩ ⟨11, 2, 0, 933491, 71704, 2961, 262144⟩
    (by decide) selected_cut_35503

theorem selected_cut_35504 : selected 10 ⟨933553, by decide⟩
    (prefixPartial 11 71705) = some ⟨11, 2, 0, 933553, 71705, 3049, 262144⟩ := by
  decide +kernel

theorem context_11_71705_933553 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71705 ⟨933553, by decide⟩ :=
  accepted_of_selected 11 71705 ⟨933553, by decide⟩ ⟨11, 2, 0, 933553, 71705, 3049, 262144⟩
    (by decide) selected_cut_35504

theorem selected_cut_35505 : selected 10 ⟨933612, by decide⟩
    (prefixPartial 11 71706) = some ⟨11, 2, 0, 933612, 71706, 3485, 262144⟩ := by
  decide +kernel

theorem context_11_71706_933612 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71706 ⟨933612, by decide⟩ :=
  accepted_of_selected 11 71706 ⟨933612, by decide⟩ ⟨11, 2, 0, 933612, 71706, 3485, 262144⟩
    (by decide) selected_cut_35505

theorem selected_cut_35506 : selected 10 ⟨933704, by decide⟩
    (prefixPartial 11 71707) = some ⟨11, 2, 0, 933704, 71707, 3853, 262144⟩ := by
  decide +kernel

theorem context_11_71707_933704 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71707 ⟨933704, by decide⟩ :=
  accepted_of_selected 11 71707 ⟨933704, by decide⟩ ⟨11, 2, 0, 933704, 71707, 3853, 262144⟩
    (by decide) selected_cut_35506

theorem unmarked_context_10_17926_933705 : frontier 11 ⟨933705, by decide⟩
    (prefixCache 10 17926) (prefixPartial 10 17926) = false := by
  decide +kernel

theorem node_context_10_17926_933705 : EJMOriginalGlobalDAGData.nodes 11 ⟨933705, by decide⟩ =
    .split (coordinate 10) (![⟨933491, by decide⟩,⟨933553, by decide⟩,⟨933612, by decide⟩,⟨933704, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17926_933705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17926 ⟨933705, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17926
    ⟨933705, by decide⟩ (by decide) (![⟨933491, by decide⟩,⟨933553, by decide⟩,⟨933612, by decide⟩,⟨933704, by decide⟩]) unmarked_context_10_17926_933705 node_context_10_17926_933705
  intro a
  fin_cases a
  · exact context_11_71704_933491
  · exact context_11_71705_933553
  · exact context_11_71706_933612
  · exact context_11_71707_933704

theorem selected_cut_35507 : selected 10 ⟨933731, by decide⟩
    (prefixPartial 11 71708) = some ⟨11, 2, 0, 933731, 71708, 1273, 262144⟩ := by
  decide +kernel

theorem context_11_71708_933731 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71708 ⟨933731, by decide⟩ :=
  accepted_of_selected 11 71708 ⟨933731, by decide⟩ ⟨11, 2, 0, 933731, 71708, 1273, 262144⟩
    (by decide) selected_cut_35507

theorem selected_cut_35508 : selected 10 ⟨933757, by decide⟩
    (prefixPartial 11 71709) = some ⟨11, 2, 0, 933757, 71709, 1313, 262144⟩ := by
  decide +kernel

theorem context_11_71709_933757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71709 ⟨933757, by decide⟩ :=
  accepted_of_selected 11 71709 ⟨933757, by decide⟩ ⟨11, 2, 0, 933757, 71709, 1313, 262144⟩
    (by decide) selected_cut_35508

theorem selected_cut_35509 : selected 10 ⟨933798, by decide⟩
    (prefixPartial 11 71710) = some ⟨11, 2, 0, 933798, 71710, 1697, 262144⟩ := by
  decide +kernel

theorem context_11_71710_933798 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71710 ⟨933798, by decide⟩ :=
  accepted_of_selected 11 71710 ⟨933798, by decide⟩ ⟨11, 2, 0, 933798, 71710, 1697, 262144⟩
    (by decide) selected_cut_35509

theorem selected_cut_35510 : selected 10 ⟨933837, by decide⟩
    (prefixPartial 11 71711) = some ⟨11, 2, 0, 933837, 71711, 1489, 262144⟩ := by
  decide +kernel

theorem context_11_71711_933837 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71711 ⟨933837, by decide⟩ :=
  accepted_of_selected 11 71711 ⟨933837, by decide⟩ ⟨11, 2, 0, 933837, 71711, 1489, 262144⟩
    (by decide) selected_cut_35510

theorem unmarked_context_10_17927_933838 : frontier 11 ⟨933838, by decide⟩
    (prefixCache 10 17927) (prefixPartial 10 17927) = false := by
  decide +kernel

theorem node_context_10_17927_933838 : EJMOriginalGlobalDAGData.nodes 11 ⟨933838, by decide⟩ =
    .split (coordinate 10) (![⟨933731, by decide⟩,⟨933757, by decide⟩,⟨933798, by decide⟩,⟨933837, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17927_933838 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17927 ⟨933838, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17927
    ⟨933838, by decide⟩ (by decide) (![⟨933731, by decide⟩,⟨933757, by decide⟩,⟨933798, by decide⟩,⟨933837, by decide⟩]) unmarked_context_10_17927_933838 node_context_10_17927_933838
  intro a
  fin_cases a
  · exact context_11_71708_933731
  · exact context_11_71709_933757
  · exact context_11_71710_933798
  · exact context_11_71711_933837

theorem unmarked_context_9_4481_933839 : frontier 12 ⟨933839, by decide⟩
    (prefixCache 9 4481) (prefixPartial 9 4481) = false := by
  decide +kernel

theorem node_context_9_4481_933839 : EJMOriginalGlobalDAGData.nodes 12 ⟨933839, by decide⟩ =
    .split (coordinate 9) (![⟨933431, by decide⟩,⟨893098, by decide⟩,⟨933705, by decide⟩,⟨933838, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4481_933839 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4481 ⟨933839, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4481
    ⟨933839, by decide⟩ (by decide) (![⟨933431, by decide⟩,⟨893098, by decide⟩,⟨933705, by decide⟩,⟨933838, by decide⟩]) unmarked_context_9_4481_933839 node_context_9_4481_933839
  intro a
  fin_cases a
  · exact context_10_17924_933431
  · exact context_10_17925_893098
  · exact context_10_17926_933705
  · exact context_10_17927_933838

theorem selected_cut_35511 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 71712) = some ⟨11, 1, 0, 907917, 71712, 1, 262144⟩ := by
  decide +kernel

theorem context_11_71712_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71712 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 71712 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 71712, 1, 262144⟩
    (by decide) selected_cut_35511

theorem selected_cut_35512 : selected 9 ⟨933858, by decide⟩
    (prefixPartial 12 286852) = some ⟨12, 2, 0, 933858, 286852, 937, 65536⟩ := by
  decide +kernel

theorem context_12_286852_933858 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286852 ⟨933858, by decide⟩ :=
  accepted_of_selected 12 286852 ⟨933858, by decide⟩ ⟨12, 2, 0, 933858, 286852, 937, 65536⟩
    (by decide) selected_cut_35512

theorem selected_cut_35513 : selected 9 ⟨933879, by decide⟩
    (prefixPartial 12 286853) = some ⟨12, 2, 0, 933879, 286853, 1389, 65536⟩ := by
  decide +kernel

theorem context_12_286853_933879 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286853 ⟨933879, by decide⟩ :=
  accepted_of_selected 12 286853 ⟨933879, by decide⟩ ⟨12, 2, 0, 933879, 286853, 1389, 65536⟩
    (by decide) selected_cut_35513

theorem selected_cut_35514 : selected 9 ⟨933904, by decide⟩
    (prefixPartial 12 286854) = some ⟨12, 2, 0, 933904, 286854, 1497, 65536⟩ := by
  decide +kernel

theorem context_12_286854_933904 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286854 ⟨933904, by decide⟩ :=
  accepted_of_selected 12 286854 ⟨933904, by decide⟩ ⟨12, 2, 0, 933904, 286854, 1497, 65536⟩
    (by decide) selected_cut_35514

theorem selected_cut_35515 : selected 9 ⟨933929, by decide⟩
    (prefixPartial 12 286855) = some ⟨12, 2, 0, 933929, 286855, 1429, 65536⟩ := by
  decide +kernel

theorem context_12_286855_933929 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286855 ⟨933929, by decide⟩ :=
  accepted_of_selected 12 286855 ⟨933929, by decide⟩ ⟨12, 2, 0, 933929, 286855, 1429, 65536⟩
    (by decide) selected_cut_35515

theorem unmarked_context_11_71713_933930 : frontier 10 ⟨933930, by decide⟩
    (prefixCache 11 71713) (prefixPartial 11 71713) = false := by
  decide +kernel

theorem node_context_11_71713_933930 : EJMOriginalGlobalDAGData.nodes 10 ⟨933930, by decide⟩ =
    .split (coordinate 11) (![⟨933858, by decide⟩,⟨933879, by decide⟩,⟨933904, by decide⟩,⟨933929, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71713_933930 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71713 ⟨933930, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71713
    ⟨933930, by decide⟩ (by decide) (![⟨933858, by decide⟩,⟨933879, by decide⟩,⟨933904, by decide⟩,⟨933929, by decide⟩]) unmarked_context_11_71713_933930 node_context_11_71713_933930
  intro a
  fin_cases a
  · exact context_12_286852_933858
  · exact context_12_286853_933879
  · exact context_12_286854_933904
  · exact context_12_286855_933929

theorem selected_cut_35516 : selected 9 ⟨933961, by decide⟩
    (prefixPartial 12 286856) = some ⟨12, 2, 0, 933961, 286856, 1121, 65536⟩ := by
  decide +kernel

theorem context_12_286856_933961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286856 ⟨933961, by decide⟩ :=
  accepted_of_selected 12 286856 ⟨933961, by decide⟩ ⟨12, 2, 0, 933961, 286856, 1121, 65536⟩
    (by decide) selected_cut_35516

theorem selected_cut_35517 : selected 9 ⟨933991, by decide⟩
    (prefixPartial 12 286857) = some ⟨12, 2, 0, 933991, 286857, 1641, 65536⟩ := by
  decide +kernel

theorem context_12_286857_933991 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286857 ⟨933991, by decide⟩ :=
  accepted_of_selected 12 286857 ⟨933991, by decide⟩ ⟨12, 2, 0, 933991, 286857, 1641, 65536⟩
    (by decide) selected_cut_35517

theorem selected_cut_35518 : selected 9 ⟨934016, by decide⟩
    (prefixPartial 12 286858) = some ⟨12, 2, 0, 934016, 286858, 1589, 65536⟩ := by
  decide +kernel

theorem context_12_286858_934016 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286858 ⟨934016, by decide⟩ :=
  accepted_of_selected 12 286858 ⟨934016, by decide⟩ ⟨12, 2, 0, 934016, 286858, 1589, 65536⟩
    (by decide) selected_cut_35518

theorem selected_cut_35519 : selected 9 ⟨934054, by decide⟩
    (prefixPartial 12 286859) = some ⟨12, 2, 0, 934054, 286859, 1829, 65536⟩ := by
  decide +kernel

theorem context_12_286859_934054 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286859 ⟨934054, by decide⟩ :=
  accepted_of_selected 12 286859 ⟨934054, by decide⟩ ⟨12, 2, 0, 934054, 286859, 1829, 65536⟩
    (by decide) selected_cut_35519

theorem unmarked_context_11_71714_934055 : frontier 10 ⟨934055, by decide⟩
    (prefixCache 11 71714) (prefixPartial 11 71714) = false := by
  decide +kernel

theorem node_context_11_71714_934055 : EJMOriginalGlobalDAGData.nodes 10 ⟨934055, by decide⟩ =
    .split (coordinate 11) (![⟨933961, by decide⟩,⟨933991, by decide⟩,⟨934016, by decide⟩,⟨934054, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71714_934055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71714 ⟨934055, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71714
    ⟨934055, by decide⟩ (by decide) (![⟨933961, by decide⟩,⟨933991, by decide⟩,⟨934016, by decide⟩,⟨934054, by decide⟩]) unmarked_context_11_71714_934055 node_context_11_71714_934055
  intro a
  fin_cases a
  · exact context_12_286856_933961
  · exact context_12_286857_933991
  · exact context_12_286858_934016
  · exact context_12_286859_934054

theorem selected_cut_35520 : selected 9 ⟨934071, by decide⟩
    (prefixPartial 12 286860) = some ⟨12, 2, 0, 934071, 286860, 861, 65536⟩ := by
  decide +kernel

theorem context_12_286860_934071 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286860 ⟨934071, by decide⟩ :=
  accepted_of_selected 12 286860 ⟨934071, by decide⟩ ⟨12, 2, 0, 934071, 286860, 861, 65536⟩
    (by decide) selected_cut_35520

theorem selected_cut_35521 : selected 9 ⟨934093, by decide⟩
    (prefixPartial 12 286861) = some ⟨12, 2, 0, 934093, 286861, 1285, 65536⟩ := by
  decide +kernel

theorem context_12_286861_934093 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286861 ⟨934093, by decide⟩ :=
  accepted_of_selected 12 286861 ⟨934093, by decide⟩ ⟨12, 2, 0, 934093, 286861, 1285, 65536⟩
    (by decide) selected_cut_35521

theorem selected_cut_35522 : selected 9 ⟨934118, by decide⟩
    (prefixPartial 12 286862) = some ⟨12, 2, 0, 934118, 286862, 1377, 65536⟩ := by
  decide +kernel

theorem context_12_286862_934118 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286862 ⟨934118, by decide⟩ :=
  accepted_of_selected 12 286862 ⟨934118, by decide⟩ ⟨12, 2, 0, 934118, 286862, 1377, 65536⟩
    (by decide) selected_cut_35522

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
