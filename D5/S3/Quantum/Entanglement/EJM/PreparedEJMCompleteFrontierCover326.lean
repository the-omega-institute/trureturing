/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover325
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_31299 : selected 9 ⟨772506, by decide⟩
    (prefixPartial 12 105765) = some ⟨12, 1, 0, 772506, 105765, 1, 65536⟩ := by
  decide +kernel

theorem context_12_105765_772506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105765 ⟨772506, by decide⟩ :=
  accepted_of_selected 12 105765 ⟨772506, by decide⟩ ⟨12, 1, 0, 772506, 105765, 1, 65536⟩
    (by decide) selected_cut_31299

theorem selected_cut_31300 : selected 8 ⟨800796, by decide⟩
    (prefixPartial 13 423064) = some ⟨13, 2, 0, 800796, 423064, 1461, 16384⟩ := by
  decide +kernel

theorem context_13_423064_800796 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423064 ⟨800796, by decide⟩ :=
  accepted_of_selected 13 423064 ⟨800796, by decide⟩ ⟨13, 2, 0, 800796, 423064, 1461, 16384⟩
    (by decide) selected_cut_31300

theorem selected_cut_31301 : selected 8 ⟨800830, by decide⟩
    (prefixPartial 13 423065) = some ⟨13, 2, 0, 800830, 423065, 2041, 16384⟩ := by
  decide +kernel

theorem context_13_423065_800830 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423065 ⟨800830, by decide⟩ :=
  accepted_of_selected 13 423065 ⟨800830, by decide⟩ ⟨13, 2, 0, 800830, 423065, 2041, 16384⟩
    (by decide) selected_cut_31301

theorem selected_cut_31302 : selected 8 ⟨800868, by decide⟩
    (prefixPartial 13 423066) = some ⟨13, 2, 0, 800868, 423066, 1317, 16384⟩ := by
  decide +kernel

theorem context_13_423066_800868 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423066 ⟨800868, by decide⟩ :=
  accepted_of_selected 13 423066 ⟨800868, by decide⟩ ⟨13, 2, 0, 800868, 423066, 1317, 16384⟩
    (by decide) selected_cut_31302

theorem selected_cut_31303 : selected 8 ⟨800906, by decide⟩
    (prefixPartial 13 423067) = some ⟨13, 2, 0, 800906, 423067, 1013, 16384⟩ := by
  decide +kernel

theorem context_13_423067_800906 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423067 ⟨800906, by decide⟩ :=
  accepted_of_selected 13 423067 ⟨800906, by decide⟩ ⟨13, 2, 0, 800906, 423067, 1013, 16384⟩
    (by decide) selected_cut_31303

theorem unmarked_context_12_105766_800907 : frontier 9 ⟨800907, by decide⟩
    (prefixCache 12 105766) (prefixPartial 12 105766) = false := by
  decide +kernel

theorem node_context_12_105766_800907 : EJMOriginalGlobalDAGData.nodes 9 ⟨800907, by decide⟩ =
    .split (coordinate 12) (![⟨800796, by decide⟩,⟨800830, by decide⟩,⟨800868, by decide⟩,⟨800906, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105766_800907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105766 ⟨800907, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105766
    ⟨800907, by decide⟩ (by decide) (![⟨800796, by decide⟩,⟨800830, by decide⟩,⟨800868, by decide⟩,⟨800906, by decide⟩]) unmarked_context_12_105766_800907 node_context_12_105766_800907
  intro a
  fin_cases a
  · exact context_13_423064_800796
  · exact context_13_423065_800830
  · exact context_13_423066_800868
  · exact context_13_423067_800906

theorem selected_cut_31304 : selected 9 ⟨801131, by decide⟩
    (prefixPartial 12 105767) = some ⟨12, 2, 0, 801131, 105767, 4001, 65536⟩ := by
  decide +kernel

theorem context_12_105767_801131 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105767 ⟨801131, by decide⟩ :=
  accepted_of_selected 12 105767 ⟨801131, by decide⟩ ⟨12, 2, 0, 801131, 105767, 4001, 65536⟩
    (by decide) selected_cut_31304

theorem unmarked_context_11_26441_801132 : frontier 10 ⟨801132, by decide⟩
    (prefixCache 11 26441) (prefixPartial 11 26441) = false := by
  decide +kernel

theorem node_context_11_26441_801132 : EJMOriginalGlobalDAGData.nodes 10 ⟨801132, by decide⟩ =
    .split (coordinate 11) (![⟨461082, by decide⟩,⟨772506, by decide⟩,⟨800907, by decide⟩,⟨801131, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26441_801132 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26441 ⟨801132, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26441
    ⟨801132, by decide⟩ (by decide) (![⟨461082, by decide⟩,⟨772506, by decide⟩,⟨800907, by decide⟩,⟨801131, by decide⟩]) unmarked_context_11_26441_801132 node_context_11_26441_801132
  intro a
  fin_cases a
  · exact context_12_105764_461082
  · exact context_12_105765_772506
  · exact context_12_105766_800907
  · exact context_12_105767_801131

theorem selected_cut_31305 : selected 8 ⟨801160, by decide⟩
    (prefixPartial 13 423072) = some ⟨13, 2, 0, 801160, 423072, 1181, 16384⟩ := by
  decide +kernel

theorem context_13_423072_801160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423072 ⟨801160, by decide⟩ :=
  accepted_of_selected 13 423072 ⟨801160, by decide⟩ ⟨13, 2, 0, 801160, 423072, 1181, 16384⟩
    (by decide) selected_cut_31305

theorem selected_cut_31306 : selected 8 ⟨801216, by decide⟩
    (prefixPartial 13 423073) = some ⟨13, 2, 0, 801216, 423073, 2013, 16384⟩ := by
  decide +kernel

theorem context_13_423073_801216 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423073 ⟨801216, by decide⟩ :=
  accepted_of_selected 13 423073 ⟨801216, by decide⟩ ⟨13, 2, 0, 801216, 423073, 2013, 16384⟩
    (by decide) selected_cut_31306

theorem selected_cut_31307 : selected 8 ⟨801282, by decide⟩
    (prefixPartial 13 423074) = some ⟨13, 2, 0, 801282, 423074, 1625, 16384⟩ := by
  decide +kernel

theorem context_13_423074_801282 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423074 ⟨801282, by decide⟩ :=
  accepted_of_selected 13 423074 ⟨801282, by decide⟩ ⟨13, 2, 0, 801282, 423074, 1625, 16384⟩
    (by decide) selected_cut_31307

theorem selected_cut_31308 : selected 8 ⟨801313, by decide⟩
    (prefixPartial 13 423075) = some ⟨13, 2, 0, 801313, 423075, 885, 16384⟩ := by
  decide +kernel

theorem context_13_423075_801313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423075 ⟨801313, by decide⟩ :=
  accepted_of_selected 13 423075 ⟨801313, by decide⟩ ⟨13, 2, 0, 801313, 423075, 885, 16384⟩
    (by decide) selected_cut_31308

theorem unmarked_context_12_105768_801314 : frontier 9 ⟨801314, by decide⟩
    (prefixCache 12 105768) (prefixPartial 12 105768) = false := by
  decide +kernel

theorem node_context_12_105768_801314 : EJMOriginalGlobalDAGData.nodes 9 ⟨801314, by decide⟩ =
    .split (coordinate 12) (![⟨801160, by decide⟩,⟨801216, by decide⟩,⟨801282, by decide⟩,⟨801313, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105768_801314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105768 ⟨801314, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105768
    ⟨801314, by decide⟩ (by decide) (![⟨801160, by decide⟩,⟨801216, by decide⟩,⟨801282, by decide⟩,⟨801313, by decide⟩]) unmarked_context_12_105768_801314 node_context_12_105768_801314
  intro a
  fin_cases a
  · exact context_13_423072_801160
  · exact context_13_423073_801216
  · exact context_13_423074_801282
  · exact context_13_423075_801313

theorem selected_cut_31309 : selected 9 ⟨801458, by decide⟩
    (prefixPartial 12 105769) = some ⟨12, 2, 0, 801458, 105769, 3557, 65536⟩ := by
  decide +kernel

theorem context_12_105769_801458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105769 ⟨801458, by decide⟩ :=
  accepted_of_selected 12 105769 ⟨801458, by decide⟩ ⟨12, 2, 0, 801458, 105769, 3557, 65536⟩
    (by decide) selected_cut_31309

theorem selected_cut_31310 : selected 8 ⟨801482, by decide⟩
    (prefixPartial 13 423080) = some ⟨13, 2, 0, 801482, 423080, 1077, 16384⟩ := by
  decide +kernel

theorem context_13_423080_801482 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423080 ⟨801482, by decide⟩ :=
  accepted_of_selected 13 423080 ⟨801482, by decide⟩ ⟨13, 2, 0, 801482, 423080, 1077, 16384⟩
    (by decide) selected_cut_31310

theorem selected_cut_31311 : selected 8 ⟨801528, by decide⟩
    (prefixPartial 13 423081) = some ⟨13, 2, 0, 801528, 423081, 2009, 16384⟩ := by
  decide +kernel

theorem context_13_423081_801528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423081 ⟨801528, by decide⟩ :=
  accepted_of_selected 13 423081 ⟨801528, by decide⟩ ⟨13, 2, 0, 801528, 423081, 2009, 16384⟩
    (by decide) selected_cut_31311

theorem selected_cut_31312 : selected 8 ⟨801561, by decide⟩
    (prefixPartial 13 423082) = some ⟨13, 2, 0, 801561, 423082, 1409, 16384⟩ := by
  decide +kernel

theorem context_13_423082_801561 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423082 ⟨801561, by decide⟩ :=
  accepted_of_selected 13 423082 ⟨801561, by decide⟩ ⟨13, 2, 0, 801561, 423082, 1409, 16384⟩
    (by decide) selected_cut_31312

theorem selected_cut_31313 : selected 8 ⟨801582, by decide⟩
    (prefixPartial 13 423083) = some ⟨13, 2, 0, 801582, 423083, 829, 16384⟩ := by
  decide +kernel

theorem context_13_423083_801582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423083 ⟨801582, by decide⟩ :=
  accepted_of_selected 13 423083 ⟨801582, by decide⟩ ⟨13, 2, 0, 801582, 423083, 829, 16384⟩
    (by decide) selected_cut_31313

theorem unmarked_context_12_105770_801583 : frontier 9 ⟨801583, by decide⟩
    (prefixCache 12 105770) (prefixPartial 12 105770) = false := by
  decide +kernel

theorem node_context_12_105770_801583 : EJMOriginalGlobalDAGData.nodes 9 ⟨801583, by decide⟩ =
    .split (coordinate 12) (![⟨801482, by decide⟩,⟨801528, by decide⟩,⟨801561, by decide⟩,⟨801582, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105770_801583 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105770 ⟨801583, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105770
    ⟨801583, by decide⟩ (by decide) (![⟨801482, by decide⟩,⟨801528, by decide⟩,⟨801561, by decide⟩,⟨801582, by decide⟩]) unmarked_context_12_105770_801583 node_context_12_105770_801583
  intro a
  fin_cases a
  · exact context_13_423080_801482
  · exact context_13_423081_801528
  · exact context_13_423082_801561
  · exact context_13_423083_801582

theorem selected_cut_31314 : selected 8 ⟨801614, by decide⟩
    (prefixPartial 13 423084) = some ⟨13, 2, 0, 801614, 423084, 1073, 16384⟩ := by
  decide +kernel

theorem context_13_423084_801614 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423084 ⟨801614, by decide⟩ :=
  accepted_of_selected 13 423084 ⟨801614, by decide⟩ ⟨13, 2, 0, 801614, 423084, 1073, 16384⟩
    (by decide) selected_cut_31314

theorem selected_cut_31315 : selected 8 ⟨801666, by decide⟩
    (prefixPartial 13 423085) = some ⟨13, 2, 0, 801666, 423085, 2053, 16384⟩ := by
  decide +kernel

theorem context_13_423085_801666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423085 ⟨801666, by decide⟩ :=
  accepted_of_selected 13 423085 ⟨801666, by decide⟩ ⟨13, 2, 0, 801666, 423085, 2053, 16384⟩
    (by decide) selected_cut_31315

theorem selected_cut_31316 : selected 8 ⟨801741, by decide⟩
    (prefixPartial 13 423086) = some ⟨13, 2, 0, 801741, 423086, 1713, 16384⟩ := by
  decide +kernel

theorem context_13_423086_801741 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423086 ⟨801741, by decide⟩ :=
  accepted_of_selected 13 423086 ⟨801741, by decide⟩ ⟨13, 2, 0, 801741, 423086, 1713, 16384⟩
    (by decide) selected_cut_31316

theorem selected_cut_31317 : selected 8 ⟨801776, by decide⟩
    (prefixPartial 13 423087) = some ⟨13, 2, 0, 801776, 423087, 797, 16384⟩ := by
  decide +kernel

theorem context_13_423087_801776 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423087 ⟨801776, by decide⟩ :=
  accepted_of_selected 13 423087 ⟨801776, by decide⟩ ⟨13, 2, 0, 801776, 423087, 797, 16384⟩
    (by decide) selected_cut_31317

theorem unmarked_context_12_105771_801777 : frontier 9 ⟨801777, by decide⟩
    (prefixCache 12 105771) (prefixPartial 12 105771) = false := by
  decide +kernel

theorem node_context_12_105771_801777 : EJMOriginalGlobalDAGData.nodes 9 ⟨801777, by decide⟩ =
    .split (coordinate 12) (![⟨801614, by decide⟩,⟨801666, by decide⟩,⟨801741, by decide⟩,⟨801776, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105771_801777 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105771 ⟨801777, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105771
    ⟨801777, by decide⟩ (by decide) (![⟨801614, by decide⟩,⟨801666, by decide⟩,⟨801741, by decide⟩,⟨801776, by decide⟩]) unmarked_context_12_105771_801777 node_context_12_105771_801777
  intro a
  fin_cases a
  · exact context_13_423084_801614
  · exact context_13_423085_801666
  · exact context_13_423086_801741
  · exact context_13_423087_801776

theorem unmarked_context_11_26442_801778 : frontier 10 ⟨801778, by decide⟩
    (prefixCache 11 26442) (prefixPartial 11 26442) = false := by
  decide +kernel

theorem node_context_11_26442_801778 : EJMOriginalGlobalDAGData.nodes 10 ⟨801778, by decide⟩ =
    .split (coordinate 11) (![⟨801314, by decide⟩,⟨801458, by decide⟩,⟨801583, by decide⟩,⟨801777, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26442_801778 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26442 ⟨801778, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26442
    ⟨801778, by decide⟩ (by decide) (![⟨801314, by decide⟩,⟨801458, by decide⟩,⟨801583, by decide⟩,⟨801777, by decide⟩]) unmarked_context_11_26442_801778 node_context_11_26442_801778
  intro a
  fin_cases a
  · exact context_12_105768_801314
  · exact context_12_105769_801458
  · exact context_12_105770_801583
  · exact context_12_105771_801777

theorem selected_cut_31318 : selected 8 ⟨801801, by decide⟩
    (prefixPartial 13 423088) = some ⟨13, 2, 0, 801801, 423088, 749, 16384⟩ := by
  decide +kernel

theorem context_13_423088_801801 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423088 ⟨801801, by decide⟩ :=
  accepted_of_selected 13 423088 ⟨801801, by decide⟩ ⟨13, 2, 0, 801801, 423088, 749, 16384⟩
    (by decide) selected_cut_31318

theorem selected_cut_31319 : selected 8 ⟨801848, by decide⟩
    (prefixPartial 13 423089) = some ⟨13, 2, 0, 801848, 423089, 1837, 16384⟩ := by
  decide +kernel

theorem context_13_423089_801848 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423089 ⟨801848, by decide⟩ :=
  accepted_of_selected 13 423089 ⟨801848, by decide⟩ ⟨13, 2, 0, 801848, 423089, 1837, 16384⟩
    (by decide) selected_cut_31319

theorem selected_cut_31320 : selected 8 ⟨801892, by decide⟩
    (prefixPartial 13 423090) = some ⟨13, 2, 0, 801892, 423090, 1441, 16384⟩ := by
  decide +kernel

theorem context_13_423090_801892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423090 ⟨801892, by decide⟩ :=
  accepted_of_selected 13 423090 ⟨801892, by decide⟩ ⟨13, 2, 0, 801892, 423090, 1441, 16384⟩
    (by decide) selected_cut_31320

theorem selected_cut_31321 : selected 8 ⟨801926, by decide⟩
    (prefixPartial 13 423091) = some ⟨13, 2, 0, 801926, 423091, 729, 16384⟩ := by
  decide +kernel

theorem context_13_423091_801926 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423091 ⟨801926, by decide⟩ :=
  accepted_of_selected 13 423091 ⟨801926, by decide⟩ ⟨13, 2, 0, 801926, 423091, 729, 16384⟩
    (by decide) selected_cut_31321

theorem unmarked_context_12_105772_801927 : frontier 9 ⟨801927, by decide⟩
    (prefixCache 12 105772) (prefixPartial 12 105772) = false := by
  decide +kernel

theorem node_context_12_105772_801927 : EJMOriginalGlobalDAGData.nodes 9 ⟨801927, by decide⟩ =
    .split (coordinate 12) (![⟨801801, by decide⟩,⟨801848, by decide⟩,⟨801892, by decide⟩,⟨801926, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105772_801927 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105772 ⟨801927, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105772
    ⟨801927, by decide⟩ (by decide) (![⟨801801, by decide⟩,⟨801848, by decide⟩,⟨801892, by decide⟩,⟨801926, by decide⟩]) unmarked_context_12_105772_801927 node_context_12_105772_801927
  intro a
  fin_cases a
  · exact context_13_423088_801801
  · exact context_13_423089_801848
  · exact context_13_423090_801892
  · exact context_13_423091_801926

theorem selected_cut_31322 : selected 8 ⟨801948, by decide⟩
    (prefixPartial 13 423092) = some ⟨13, 2, 0, 801948, 423092, 689, 16384⟩ := by
  decide +kernel

theorem context_13_423092_801948 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423092 ⟨801948, by decide⟩ :=
  accepted_of_selected 13 423092 ⟨801948, by decide⟩ ⟨13, 2, 0, 801948, 423092, 689, 16384⟩
    (by decide) selected_cut_31322

theorem selected_cut_31323 : selected 8 ⟨801977, by decide⟩
    (prefixPartial 13 423093) = some ⟨13, 2, 0, 801977, 423093, 1705, 16384⟩ := by
  decide +kernel

theorem context_13_423093_801977 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423093 ⟨801977, by decide⟩ :=
  accepted_of_selected 13 423093 ⟨801977, by decide⟩ ⟨13, 2, 0, 801977, 423093, 1705, 16384⟩
    (by decide) selected_cut_31323

theorem selected_cut_31324 : selected 8 ⟨802018, by decide⟩
    (prefixPartial 13 423094) = some ⟨13, 2, 0, 802018, 423094, 1389, 16384⟩ := by
  decide +kernel

theorem context_13_423094_802018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423094 ⟨802018, by decide⟩ :=
  accepted_of_selected 13 423094 ⟨802018, by decide⟩ ⟨13, 2, 0, 802018, 423094, 1389, 16384⟩
    (by decide) selected_cut_31324

theorem selected_cut_31325 : selected 8 ⟨802031, by decide⟩
    (prefixPartial 13 423095) = some ⟨13, 2, 0, 802031, 423095, 657, 16384⟩ := by
  decide +kernel

theorem context_13_423095_802031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423095 ⟨802031, by decide⟩ :=
  accepted_of_selected 13 423095 ⟨802031, by decide⟩ ⟨13, 2, 0, 802031, 423095, 657, 16384⟩
    (by decide) selected_cut_31325

theorem unmarked_context_12_105773_802032 : frontier 9 ⟨802032, by decide⟩
    (prefixCache 12 105773) (prefixPartial 12 105773) = false := by
  decide +kernel

theorem node_context_12_105773_802032 : EJMOriginalGlobalDAGData.nodes 9 ⟨802032, by decide⟩ =
    .split (coordinate 12) (![⟨801948, by decide⟩,⟨801977, by decide⟩,⟨802018, by decide⟩,⟨802031, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105773_802032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105773 ⟨802032, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105773
    ⟨802032, by decide⟩ (by decide) (![⟨801948, by decide⟩,⟨801977, by decide⟩,⟨802018, by decide⟩,⟨802031, by decide⟩]) unmarked_context_12_105773_802032 node_context_12_105773_802032
  intro a
  fin_cases a
  · exact context_13_423092_801948
  · exact context_13_423093_801977
  · exact context_13_423094_802018
  · exact context_13_423095_802031

theorem selected_cut_31326 : selected 8 ⟨802055, by decide⟩
    (prefixPartial 13 423096) = some ⟨13, 2, 0, 802055, 423096, 633, 16384⟩ := by
  decide +kernel

theorem context_13_423096_802055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423096 ⟨802055, by decide⟩ :=
  accepted_of_selected 13 423096 ⟨802055, by decide⟩ ⟨13, 2, 0, 802055, 423096, 633, 16384⟩
    (by decide) selected_cut_31326

theorem selected_cut_31327 : selected 8 ⟨802099, by decide⟩
    (prefixPartial 13 423097) = some ⟨13, 2, 0, 802099, 423097, 1861, 16384⟩ := by
  decide +kernel

theorem context_13_423097_802099 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423097 ⟨802099, by decide⟩ :=
  accepted_of_selected 13 423097 ⟨802099, by decide⟩ ⟨13, 2, 0, 802099, 423097, 1861, 16384⟩
    (by decide) selected_cut_31327

theorem selected_cut_31328 : selected 8 ⟨802123, by decide⟩
    (prefixPartial 13 423098) = some ⟨13, 2, 0, 802123, 423098, 1225, 16384⟩ := by
  decide +kernel

theorem context_13_423098_802123 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423098 ⟨802123, by decide⟩ :=
  accepted_of_selected 13 423098 ⟨802123, by decide⟩ ⟨13, 2, 0, 802123, 423098, 1225, 16384⟩
    (by decide) selected_cut_31328

theorem selected_cut_31329 : selected 8 ⟨802153, by decide⟩
    (prefixPartial 13 423099) = some ⟨13, 2, 0, 802153, 423099, 709, 16384⟩ := by
  decide +kernel

theorem context_13_423099_802153 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423099 ⟨802153, by decide⟩ :=
  accepted_of_selected 13 423099 ⟨802153, by decide⟩ ⟨13, 2, 0, 802153, 423099, 709, 16384⟩
    (by decide) selected_cut_31329

theorem unmarked_context_12_105774_802154 : frontier 9 ⟨802154, by decide⟩
    (prefixCache 12 105774) (prefixPartial 12 105774) = false := by
  decide +kernel

theorem node_context_12_105774_802154 : EJMOriginalGlobalDAGData.nodes 9 ⟨802154, by decide⟩ =
    .split (coordinate 12) (![⟨802055, by decide⟩,⟨802099, by decide⟩,⟨802123, by decide⟩,⟨802153, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105774_802154 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105774 ⟨802154, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105774
    ⟨802154, by decide⟩ (by decide) (![⟨802055, by decide⟩,⟨802099, by decide⟩,⟨802123, by decide⟩,⟨802153, by decide⟩]) unmarked_context_12_105774_802154 node_context_12_105774_802154
  intro a
  fin_cases a
  · exact context_13_423096_802055
  · exact context_13_423097_802099
  · exact context_13_423098_802123
  · exact context_13_423099_802153

theorem selected_cut_31330 : selected 8 ⟨802172, by decide⟩
    (prefixPartial 13 423100) = some ⟨13, 2, 0, 802172, 423100, 573, 16384⟩ := by
  decide +kernel

theorem context_13_423100_802172 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423100 ⟨802172, by decide⟩ :=
  accepted_of_selected 13 423100 ⟨802172, by decide⟩ ⟨13, 2, 0, 802172, 423100, 573, 16384⟩
    (by decide) selected_cut_31330

theorem selected_cut_31331 : selected 8 ⟨802214, by decide⟩
    (prefixPartial 13 423101) = some ⟨13, 2, 0, 802214, 423101, 1909, 16384⟩ := by
  decide +kernel

theorem context_13_423101_802214 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423101 ⟨802214, by decide⟩ :=
  accepted_of_selected 13 423101 ⟨802214, by decide⟩ ⟨13, 2, 0, 802214, 423101, 1909, 16384⟩
    (by decide) selected_cut_31331

theorem selected_cut_31332 : selected 8 ⟨802265, by decide⟩
    (prefixPartial 13 423102) = some ⟨13, 2, 0, 802265, 423102, 1353, 16384⟩ := by
  decide +kernel

theorem context_13_423102_802265 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423102 ⟨802265, by decide⟩ :=
  accepted_of_selected 13 423102 ⟨802265, by decide⟩ ⟨13, 2, 0, 802265, 423102, 1353, 16384⟩
    (by decide) selected_cut_31332

theorem selected_cut_31333 : selected 8 ⟨802290, by decide⟩
    (prefixPartial 13 423103) = some ⟨13, 2, 0, 802290, 423103, 689, 16384⟩ := by
  decide +kernel

theorem context_13_423103_802290 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423103 ⟨802290, by decide⟩ :=
  accepted_of_selected 13 423103 ⟨802290, by decide⟩ ⟨13, 2, 0, 802290, 423103, 689, 16384⟩
    (by decide) selected_cut_31333

theorem unmarked_context_12_105775_802291 : frontier 9 ⟨802291, by decide⟩
    (prefixCache 12 105775) (prefixPartial 12 105775) = false := by
  decide +kernel

theorem node_context_12_105775_802291 : EJMOriginalGlobalDAGData.nodes 9 ⟨802291, by decide⟩ =
    .split (coordinate 12) (![⟨802172, by decide⟩,⟨802214, by decide⟩,⟨802265, by decide⟩,⟨802290, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105775_802291 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105775 ⟨802291, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105775
    ⟨802291, by decide⟩ (by decide) (![⟨802172, by decide⟩,⟨802214, by decide⟩,⟨802265, by decide⟩,⟨802290, by decide⟩]) unmarked_context_12_105775_802291 node_context_12_105775_802291
  intro a
  fin_cases a
  · exact context_13_423100_802172
  · exact context_13_423101_802214
  · exact context_13_423102_802265
  · exact context_13_423103_802290

theorem unmarked_context_11_26443_802292 : frontier 10 ⟨802292, by decide⟩
    (prefixCache 11 26443) (prefixPartial 11 26443) = false := by
  decide +kernel

theorem node_context_11_26443_802292 : EJMOriginalGlobalDAGData.nodes 10 ⟨802292, by decide⟩ =
    .split (coordinate 11) (![⟨801927, by decide⟩,⟨802032, by decide⟩,⟨802154, by decide⟩,⟨802291, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26443_802292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26443 ⟨802292, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26443
    ⟨802292, by decide⟩ (by decide) (![⟨801927, by decide⟩,⟨802032, by decide⟩,⟨802154, by decide⟩,⟨802291, by decide⟩]) unmarked_context_11_26443_802292 node_context_11_26443_802292
  intro a
  fin_cases a
  · exact context_12_105772_801927
  · exact context_12_105773_802032
  · exact context_12_105774_802154
  · exact context_12_105775_802291

theorem unmarked_context_10_6610_802293 : frontier 11 ⟨802293, by decide⟩
    (prefixCache 10 6610) (prefixPartial 10 6610) = false := by
  decide +kernel

theorem node_context_10_6610_802293 : EJMOriginalGlobalDAGData.nodes 11 ⟨802293, by decide⟩ =
    .split (coordinate 10) (![⟨800749, by decide⟩,⟨801132, by decide⟩,⟨801778, by decide⟩,⟨802292, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6610_802293 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6610 ⟨802293, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6610
    ⟨802293, by decide⟩ (by decide) (![⟨800749, by decide⟩,⟨801132, by decide⟩,⟨801778, by decide⟩,⟨802292, by decide⟩]) unmarked_context_10_6610_802293 node_context_10_6610_802293
  intro a
  fin_cases a
  · exact context_11_26440_800749
  · exact context_11_26441_801132
  · exact context_11_26442_801778
  · exact context_11_26443_802292

theorem selected_cut_31334 : selected 9 ⟨802411, by decide⟩
    (prefixPartial 12 105776) = some ⟨12, 2, 0, 802411, 105776, 3397, 65536⟩ := by
  decide +kernel

theorem context_12_105776_802411 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105776 ⟨802411, by decide⟩ :=
  accepted_of_selected 12 105776 ⟨802411, by decide⟩ ⟨12, 2, 0, 802411, 105776, 3397, 65536⟩
    (by decide) selected_cut_31334

theorem selected_cut_31335 : selected 9 ⟨772506, by decide⟩
    (prefixPartial 12 105777) = some ⟨12, 1, 0, 772506, 105777, 1, 65536⟩ := by
  decide +kernel

theorem context_12_105777_772506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105777 ⟨772506, by decide⟩ :=
  accepted_of_selected 12 105777 ⟨772506, by decide⟩ ⟨12, 1, 0, 772506, 105777, 1, 65536⟩
    (by decide) selected_cut_31335

theorem selected_cut_31336 : selected 9 ⟨802503, by decide⟩
    (prefixPartial 12 105778) = some ⟨12, 2, 0, 802503, 105778, 3449, 65536⟩ := by
  decide +kernel

theorem context_12_105778_802503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105778 ⟨802503, by decide⟩ :=
  accepted_of_selected 12 105778 ⟨802503, by decide⟩ ⟨12, 2, 0, 802503, 105778, 3449, 65536⟩
    (by decide) selected_cut_31336

theorem selected_cut_31337 : selected 9 ⟨802668, by decide⟩
    (prefixPartial 12 105779) = some ⟨12, 2, 0, 802668, 105779, 3997, 65536⟩ := by
  decide +kernel

theorem context_12_105779_802668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105779 ⟨802668, by decide⟩ :=
  accepted_of_selected 12 105779 ⟨802668, by decide⟩ ⟨12, 2, 0, 802668, 105779, 3997, 65536⟩
    (by decide) selected_cut_31337

theorem unmarked_context_11_26444_802669 : frontier 10 ⟨802669, by decide⟩
    (prefixCache 11 26444) (prefixPartial 11 26444) = false := by
  decide +kernel

theorem node_context_11_26444_802669 : EJMOriginalGlobalDAGData.nodes 10 ⟨802669, by decide⟩ =
    .split (coordinate 11) (![⟨802411, by decide⟩,⟨772506, by decide⟩,⟨802503, by decide⟩,⟨802668, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26444_802669 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26444 ⟨802669, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26444
    ⟨802669, by decide⟩ (by decide) (![⟨802411, by decide⟩,⟨772506, by decide⟩,⟨802503, by decide⟩,⟨802668, by decide⟩]) unmarked_context_11_26444_802669 node_context_11_26444_802669
  intro a
  fin_cases a
  · exact context_12_105776_802411
  · exact context_12_105777_772506
  · exact context_12_105778_802503
  · exact context_12_105779_802668

theorem selected_cut_31338 : selected 10 ⟨802769, by decide⟩
    (prefixPartial 11 26445) = some ⟨11, 2, 0, 802769, 26445, 2085, 262144⟩ := by
  decide +kernel

theorem context_11_26445_802769 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26445 ⟨802769, by decide⟩ :=
  accepted_of_selected 11 26445 ⟨802769, by decide⟩ ⟨11, 2, 0, 802769, 26445, 2085, 262144⟩
    (by decide) selected_cut_31338

theorem selected_cut_31339 : selected 9 ⟨802889, by decide⟩
    (prefixPartial 12 105784) = some ⟨12, 2, 0, 802889, 105784, 3273, 65536⟩ := by
  decide +kernel

theorem context_12_105784_802889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105784 ⟨802889, by decide⟩ :=
  accepted_of_selected 12 105784 ⟨802889, by decide⟩ ⟨12, 2, 0, 802889, 105784, 3273, 65536⟩
    (by decide) selected_cut_31339

theorem selected_cut_31340 : selected 9 ⟨772506, by decide⟩
    (prefixPartial 12 105785) = some ⟨12, 1, 0, 772506, 105785, 1, 65536⟩ := by
  decide +kernel

theorem context_12_105785_772506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105785 ⟨772506, by decide⟩ :=
  accepted_of_selected 12 105785 ⟨772506, by decide⟩ ⟨12, 1, 0, 772506, 105785, 1, 65536⟩
    (by decide) selected_cut_31340

theorem selected_cut_31341 : selected 9 ⟨802958, by decide⟩
    (prefixPartial 12 105786) = some ⟨12, 2, 0, 802958, 105786, 2809, 65536⟩ := by
  decide +kernel

theorem context_12_105786_802958 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105786 ⟨802958, by decide⟩ :=
  accepted_of_selected 12 105786 ⟨802958, by decide⟩ ⟨12, 2, 0, 802958, 105786, 2809, 65536⟩
    (by decide) selected_cut_31341

theorem selected_cut_31342 : selected 9 ⟨803074, by decide⟩
    (prefixPartial 12 105787) = some ⟨12, 2, 0, 803074, 105787, 3317, 65536⟩ := by
  decide +kernel

theorem context_12_105787_803074 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105787 ⟨803074, by decide⟩ :=
  accepted_of_selected 12 105787 ⟨803074, by decide⟩ ⟨12, 2, 0, 803074, 105787, 3317, 65536⟩
    (by decide) selected_cut_31342

theorem unmarked_context_11_26446_803075 : frontier 10 ⟨803075, by decide⟩
    (prefixCache 11 26446) (prefixPartial 11 26446) = false := by
  decide +kernel

theorem node_context_11_26446_803075 : EJMOriginalGlobalDAGData.nodes 10 ⟨803075, by decide⟩ =
    .split (coordinate 11) (![⟨802889, by decide⟩,⟨772506, by decide⟩,⟨802958, by decide⟩,⟨803074, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26446_803075 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26446 ⟨803075, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26446
    ⟨803075, by decide⟩ (by decide) (![⟨802889, by decide⟩,⟨772506, by decide⟩,⟨802958, by decide⟩,⟨803074, by decide⟩]) unmarked_context_11_26446_803075 node_context_11_26446_803075
  intro a
  fin_cases a
  · exact context_12_105784_802889
  · exact context_12_105785_772506
  · exact context_12_105786_802958
  · exact context_12_105787_803074

theorem selected_cut_31343 : selected 10 ⟨793294, by decide⟩
    (prefixPartial 11 26447) = some ⟨11, 1, 0, 793294, 26447, 1, 262144⟩ := by
  decide +kernel

theorem context_11_26447_793294 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26447 ⟨793294, by decide⟩ :=
  accepted_of_selected 11 26447 ⟨793294, by decide⟩ ⟨11, 1, 0, 793294, 26447, 1, 262144⟩
    (by decide) selected_cut_31343

theorem unmarked_context_10_6611_803076 : frontier 11 ⟨803076, by decide⟩
    (prefixCache 10 6611) (prefixPartial 10 6611) = false := by
  decide +kernel

theorem node_context_10_6611_803076 : EJMOriginalGlobalDAGData.nodes 11 ⟨803076, by decide⟩ =
    .split (coordinate 10) (![⟨802669, by decide⟩,⟨802769, by decide⟩,⟨803075, by decide⟩,⟨793294, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6611_803076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6611 ⟨803076, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6611
    ⟨803076, by decide⟩ (by decide) (![⟨802669, by decide⟩,⟨802769, by decide⟩,⟨803075, by decide⟩,⟨793294, by decide⟩]) unmarked_context_10_6611_803076 node_context_10_6611_803076
  intro a
  fin_cases a
  · exact context_11_26444_802669
  · exact context_11_26445_802769
  · exact context_11_26446_803075
  · exact context_11_26447_793294

theorem unmarked_context_9_1652_803077 : frontier 12 ⟨803077, by decide⟩
    (prefixCache 9 1652) (prefixPartial 9 1652) = false := by
  decide +kernel

theorem node_context_9_1652_803077 : EJMOriginalGlobalDAGData.nodes 12 ⟨803077, by decide⟩ =
    .split (coordinate 9) (![⟨797446, by decide⟩,⟨800219, by decide⟩,⟨802293, by decide⟩,⟨803076, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1652_803077 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1652 ⟨803077, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1652
    ⟨803077, by decide⟩ (by decide) (![⟨797446, by decide⟩,⟨800219, by decide⟩,⟨802293, by decide⟩,⟨803076, by decide⟩]) unmarked_context_9_1652_803077 node_context_9_1652_803077
  intro a
  fin_cases a
  · exact context_10_6608_797446
  · exact context_10_6609_800219
  · exact context_10_6610_802293
  · exact context_10_6611_803076

theorem selected_cut_31344 : selected 11 ⟨793297, by decide⟩
    (prefixPartial 10 6612) = some ⟨10, 1, 0, 793297, 6612, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_6612_793297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6612 ⟨793297, by decide⟩ :=
  accepted_of_selected 10 6612 ⟨793297, by decide⟩ ⟨10, 1, 0, 793297, 6612, 1, 1048576⟩
    (by decide) selected_cut_31344

theorem selected_cut_31345 : selected 9 ⟨803139, by decide⟩
    (prefixPartial 12 105808) = some ⟨12, 2, 0, 803139, 105808, 881, 65536⟩ := by
  decide +kernel

theorem context_12_105808_803139 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105808 ⟨803139, by decide⟩ :=
  accepted_of_selected 12 105808 ⟨803139, by decide⟩ ⟨12, 2, 0, 803139, 105808, 881, 65536⟩
    (by decide) selected_cut_31345

theorem selected_cut_31346 : selected 9 ⟨775937, by decide⟩
    (prefixPartial 12 105809) = some ⟨12, 1, 0, 775937, 105809, 1, 65536⟩ := by
  decide +kernel

theorem context_12_105809_775937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105809 ⟨775937, by decide⟩ :=
  accepted_of_selected 12 105809 ⟨775937, by decide⟩ ⟨12, 1, 0, 775937, 105809, 1, 65536⟩
    (by decide) selected_cut_31346

theorem selected_cut_31347 : selected 9 ⟨803270, by decide⟩
    (prefixPartial 12 105810) = some ⟨12, 2, 0, 803270, 105810, 2245, 65536⟩ := by
  decide +kernel

theorem context_12_105810_803270 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105810 ⟨803270, by decide⟩ :=
  accepted_of_selected 12 105810 ⟨803270, by decide⟩ ⟨12, 2, 0, 803270, 105810, 2245, 65536⟩
    (by decide) selected_cut_31347

theorem selected_cut_31348 : selected 9 ⟨803373, by decide⟩
    (prefixPartial 12 105811) = some ⟨12, 2, 0, 803373, 105811, 2257, 65536⟩ := by
  decide +kernel

theorem context_12_105811_803373 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105811 ⟨803373, by decide⟩ :=
  accepted_of_selected 12 105811 ⟨803373, by decide⟩ ⟨12, 2, 0, 803373, 105811, 2257, 65536⟩
    (by decide) selected_cut_31348

theorem unmarked_context_11_26452_803374 : frontier 10 ⟨803374, by decide⟩
    (prefixCache 11 26452) (prefixPartial 11 26452) = false := by
  decide +kernel

theorem node_context_11_26452_803374 : EJMOriginalGlobalDAGData.nodes 10 ⟨803374, by decide⟩ =
    .split (coordinate 11) (![⟨803139, by decide⟩,⟨775937, by decide⟩,⟨803270, by decide⟩,⟨803373, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26452_803374 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26452 ⟨803374, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26452
    ⟨803374, by decide⟩ (by decide) (![⟨803139, by decide⟩,⟨775937, by decide⟩,⟨803270, by decide⟩,⟨803373, by decide⟩]) unmarked_context_11_26452_803374 node_context_11_26452_803374
  intro a
  fin_cases a
  · exact context_12_105808_803139
  · exact context_12_105809_775937
  · exact context_12_105810_803270
  · exact context_12_105811_803373

theorem selected_cut_31349 : selected 10 ⟨803375, by decide⟩
    (prefixPartial 11 26453) = some ⟨11, 1, 0, 803375, 26453, 1, 262144⟩ := by
  decide +kernel

theorem context_11_26453_803375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26453 ⟨803375, by decide⟩ :=
  accepted_of_selected 11 26453 ⟨803375, by decide⟩ ⟨11, 1, 0, 803375, 26453, 1, 262144⟩
    (by decide) selected_cut_31349

theorem selected_cut_31350 : selected 10 ⟨803525, by decide⟩
    (prefixPartial 11 26454) = some ⟨11, 2, 0, 803525, 26454, 3321, 262144⟩ := by
  decide +kernel

theorem context_11_26454_803525 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26454 ⟨803525, by decide⟩ :=
  accepted_of_selected 11 26454 ⟨803525, by decide⟩ ⟨11, 2, 0, 803525, 26454, 3321, 262144⟩
    (by decide) selected_cut_31350

theorem selected_cut_31351 : selected 10 ⟨803566, by decide⟩
    (prefixPartial 11 26455) = some ⟨11, 2, 0, 803566, 26455, 1097, 262144⟩ := by
  decide +kernel

theorem context_11_26455_803566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26455 ⟨803566, by decide⟩ :=
  accepted_of_selected 11 26455 ⟨803566, by decide⟩ ⟨11, 2, 0, 803566, 26455, 1097, 262144⟩
    (by decide) selected_cut_31351

theorem unmarked_context_10_6613_803567 : frontier 11 ⟨803567, by decide⟩
    (prefixCache 10 6613) (prefixPartial 10 6613) = false := by
  decide +kernel

theorem node_context_10_6613_803567 : EJMOriginalGlobalDAGData.nodes 11 ⟨803567, by decide⟩ =
    .split (coordinate 10) (![⟨803374, by decide⟩,⟨803375, by decide⟩,⟨803525, by decide⟩,⟨803566, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6613_803567 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6613 ⟨803567, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6613
    ⟨803567, by decide⟩ (by decide) (![⟨803374, by decide⟩,⟨803375, by decide⟩,⟨803525, by decide⟩,⟨803566, by decide⟩]) unmarked_context_10_6613_803567 node_context_10_6613_803567
  intro a
  fin_cases a
  · exact context_11_26452_803374
  · exact context_11_26453_803375
  · exact context_11_26454_803525
  · exact context_11_26455_803566

theorem selected_cut_31352 : selected 10 ⟨803800, by decide⟩
    (prefixPartial 11 26456) = some ⟨11, 2, 0, 803800, 26456, 3341, 262144⟩ := by
  decide +kernel

theorem context_11_26456_803800 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26456 ⟨803800, by decide⟩ :=
  accepted_of_selected 11 26456 ⟨803800, by decide⟩ ⟨11, 2, 0, 803800, 26456, 3341, 262144⟩
    (by decide) selected_cut_31352

theorem selected_cut_31353 : selected 10 ⟨803375, by decide⟩
    (prefixPartial 11 26457) = some ⟨11, 1, 0, 803375, 26457, 1, 262144⟩ := by
  decide +kernel

theorem context_11_26457_803375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26457 ⟨803375, by decide⟩ :=
  accepted_of_selected 11 26457 ⟨803375, by decide⟩ ⟨11, 1, 0, 803375, 26457, 1, 262144⟩
    (by decide) selected_cut_31353

theorem selected_cut_31354 : selected 9 ⟨803934, by decide⟩
    (prefixPartial 12 105832) = some ⟨12, 2, 0, 803934, 105832, 1477, 65536⟩ := by
  decide +kernel

theorem context_12_105832_803934 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105832 ⟨803934, by decide⟩ :=
  accepted_of_selected 12 105832 ⟨803934, by decide⟩ ⟨12, 2, 0, 803934, 105832, 1477, 65536⟩
    (by decide) selected_cut_31354

theorem selected_cut_31355 : selected 9 ⟨775937, by decide⟩
    (prefixPartial 12 105833) = some ⟨12, 1, 0, 775937, 105833, 1, 65536⟩ := by
  decide +kernel

theorem context_12_105833_775937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105833 ⟨775937, by decide⟩ :=
  accepted_of_selected 12 105833 ⟨775937, by decide⟩ ⟨12, 1, 0, 775937, 105833, 1, 65536⟩
    (by decide) selected_cut_31355

theorem selected_cut_31356 : selected 9 ⟨804008, by decide⟩
    (prefixPartial 12 105834) = some ⟨12, 2, 0, 804008, 105834, 1597, 65536⟩ := by
  decide +kernel

theorem context_12_105834_804008 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105834 ⟨804008, by decide⟩ :=
  accepted_of_selected 12 105834 ⟨804008, by decide⟩ ⟨12, 2, 0, 804008, 105834, 1597, 65536⟩
    (by decide) selected_cut_31356

theorem selected_cut_31357 : selected 9 ⟨804095, by decide⟩
    (prefixPartial 12 105835) = some ⟨12, 2, 0, 804095, 105835, 1657, 65536⟩ := by
  decide +kernel

theorem context_12_105835_804095 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105835 ⟨804095, by decide⟩ :=
  accepted_of_selected 12 105835 ⟨804095, by decide⟩ ⟨12, 2, 0, 804095, 105835, 1657, 65536⟩
    (by decide) selected_cut_31357

theorem unmarked_context_11_26458_804096 : frontier 10 ⟨804096, by decide⟩
    (prefixCache 11 26458) (prefixPartial 11 26458) = false := by
  decide +kernel

theorem node_context_11_26458_804096 : EJMOriginalGlobalDAGData.nodes 10 ⟨804096, by decide⟩ =
    .split (coordinate 11) (![⟨803934, by decide⟩,⟨775937, by decide⟩,⟨804008, by decide⟩,⟨804095, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26458_804096 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26458 ⟨804096, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26458
    ⟨804096, by decide⟩ (by decide) (![⟨803934, by decide⟩,⟨775937, by decide⟩,⟨804008, by decide⟩,⟨804095, by decide⟩]) unmarked_context_11_26458_804096 node_context_11_26458_804096
  intro a
  fin_cases a
  · exact context_12_105832_803934
  · exact context_12_105833_775937
  · exact context_12_105834_804008
  · exact context_12_105835_804095

theorem selected_cut_31358 : selected 10 ⟨804269, by decide⟩
    (prefixPartial 11 26459) = some ⟨11, 2, 0, 804269, 26459, 3869, 262144⟩ := by
  decide +kernel

theorem context_11_26459_804269 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26459 ⟨804269, by decide⟩ :=
  accepted_of_selected 11 26459 ⟨804269, by decide⟩ ⟨11, 2, 0, 804269, 26459, 3869, 262144⟩
    (by decide) selected_cut_31358

theorem unmarked_context_10_6614_804270 : frontier 11 ⟨804270, by decide⟩
    (prefixCache 10 6614) (prefixPartial 10 6614) = false := by
  decide +kernel

theorem node_context_10_6614_804270 : EJMOriginalGlobalDAGData.nodes 11 ⟨804270, by decide⟩ =
    .split (coordinate 10) (![⟨803800, by decide⟩,⟨803375, by decide⟩,⟨804096, by decide⟩,⟨804269, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6614_804270 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6614 ⟨804270, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6614
    ⟨804270, by decide⟩ (by decide) (![⟨803800, by decide⟩,⟨803375, by decide⟩,⟨804096, by decide⟩,⟨804269, by decide⟩]) unmarked_context_10_6614_804270 node_context_10_6614_804270
  intro a
  fin_cases a
  · exact context_11_26456_803800
  · exact context_11_26457_803375
  · exact context_11_26458_804096
  · exact context_11_26459_804269

theorem selected_cut_31359 : selected 11 ⟨804547, by decide⟩
    (prefixPartial 10 6615) = some ⟨10, 2, 0, 804547, 6615, 3025, 1048576⟩ := by
  decide +kernel

theorem context_10_6615_804547 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6615 ⟨804547, by decide⟩ :=
  accepted_of_selected 10 6615 ⟨804547, by decide⟩ ⟨10, 2, 0, 804547, 6615, 3025, 1048576⟩
    (by decide) selected_cut_31359

theorem unmarked_context_9_1653_804548 : frontier 12 ⟨804548, by decide⟩
    (prefixCache 9 1653) (prefixPartial 9 1653) = false := by
  decide +kernel

theorem node_context_9_1653_804548 : EJMOriginalGlobalDAGData.nodes 12 ⟨804548, by decide⟩ =
    .split (coordinate 9) (![⟨793297, by decide⟩,⟨803567, by decide⟩,⟨804270, by decide⟩,⟨804547, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1653_804548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1653 ⟨804548, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1653
    ⟨804548, by decide⟩ (by decide) (![⟨793297, by decide⟩,⟨803567, by decide⟩,⟨804270, by decide⟩,⟨804547, by decide⟩]) unmarked_context_9_1653_804548 node_context_9_1653_804548
  intro a
  fin_cases a
  · exact context_10_6612_793297
  · exact context_10_6613_803567
  · exact context_10_6614_804270
  · exact context_10_6615_804547

theorem selected_cut_31360 : selected 12 ⟨804623, by decide⟩
    (prefixPartial 9 1654) = some ⟨9, 2, 0, 804623, 1654, 485, 4194304⟩ := by
  decide +kernel

theorem context_9_1654_804623 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1654 ⟨804623, by decide⟩ :=
  accepted_of_selected 9 1654 ⟨804623, by decide⟩ ⟨9, 2, 0, 804623, 1654, 485, 4194304⟩
    (by decide) selected_cut_31360

theorem selected_cut_31361 : selected 12 ⟨804630, by decide⟩
    (prefixPartial 9 1655) = some ⟨9, 2, 0, 804630, 1655, 41, 4194304⟩ := by
  decide +kernel

theorem context_9_1655_804630 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1655 ⟨804630, by decide⟩ :=
  accepted_of_selected 9 1655 ⟨804630, by decide⟩ ⟨9, 2, 0, 804630, 1655, 41, 4194304⟩
    (by decide) selected_cut_31361

theorem unmarked_context_8_413_804631 : frontier 13 ⟨804631, by decide⟩
    (prefixCache 8 413) (prefixPartial 8 413) = false := by
  decide +kernel

theorem node_context_8_413_804631 : EJMOriginalGlobalDAGData.nodes 13 ⟨804631, by decide⟩ =
    .split (coordinate 8) (![⟨803077, by decide⟩,⟨804548, by decide⟩,⟨804623, by decide⟩,⟨804630, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_413_804631 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 413 ⟨804631, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 413
    ⟨804631, by decide⟩ (by decide) (![⟨803077, by decide⟩,⟨804548, by decide⟩,⟨804623, by decide⟩,⟨804630, by decide⟩]) unmarked_context_8_413_804631 node_context_8_413_804631
  intro a
  fin_cases a
  · exact context_9_1652_803077
  · exact context_9_1653_804548
  · exact context_9_1654_804623
  · exact context_9_1655_804630

theorem selected_cut_31362 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 26496) = some ⟨11, 1, 0, 434745, 26496, 1, 262144⟩ := by
  decide +kernel

theorem context_11_26496_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26496 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 26496 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 26496, 1, 262144⟩
    (by decide) selected_cut_31362

theorem selected_cut_31363 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 105988) = some ⟨12, 1, 0, 448748, 105988, 1, 65536⟩ := by
  decide +kernel

theorem context_12_105988_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105988 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 105988 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 105988, 1, 65536⟩
    (by decide) selected_cut_31363

theorem selected_cut_31364 : selected 8 ⟨804775, by decide⟩
    (prefixPartial 13 423956) = some ⟨13, 2, 0, 804775, 423956, 3849, 16384⟩ := by
  decide +kernel

theorem context_13_423956_804775 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423956 ⟨804775, by decide⟩ :=
  accepted_of_selected 13 423956 ⟨804775, by decide⟩ ⟨13, 2, 0, 804775, 423956, 3849, 16384⟩
    (by decide) selected_cut_31364

theorem selected_cut_31365 : selected 7 ⟨804809, by decide⟩
    (prefixPartial 14 1695828) = some ⟨14, 2, 0, 804809, 1695828, 1117, 4096⟩ := by
  decide +kernel

theorem context_14_1695828_804809 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1695828 ⟨804809, by decide⟩ :=
  accepted_of_selected 14 1695828 ⟨804809, by decide⟩ ⟨14, 2, 0, 804809, 1695828, 1117, 4096⟩
    (by decide) selected_cut_31365

theorem selected_cut_31366 : selected 7 ⟨804846, by decide⟩
    (prefixPartial 14 1695829) = some ⟨14, 2, 0, 804846, 1695829, 1105, 4096⟩ := by
  decide +kernel

theorem context_14_1695829_804846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1695829 ⟨804846, by decide⟩ :=
  accepted_of_selected 14 1695829 ⟨804846, by decide⟩ ⟨14, 2, 0, 804846, 1695829, 1105, 4096⟩
    (by decide) selected_cut_31366

theorem selected_cut_31367 : selected 7 ⟨804874, by decide⟩
    (prefixPartial 14 1695830) = some ⟨14, 2, 0, 804874, 1695830, 1061, 4096⟩ := by
  decide +kernel

theorem context_14_1695830_804874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1695830 ⟨804874, by decide⟩ :=
  accepted_of_selected 14 1695830 ⟨804874, by decide⟩ ⟨14, 2, 0, 804874, 1695830, 1061, 4096⟩
    (by decide) selected_cut_31367

theorem selected_cut_31368 : selected 7 ⟨804907, by decide⟩
    (prefixPartial 14 1695831) = some ⟨14, 2, 0, 804907, 1695831, 1017, 4096⟩ := by
  decide +kernel

theorem context_14_1695831_804907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1695831 ⟨804907, by decide⟩ :=
  accepted_of_selected 14 1695831 ⟨804907, by decide⟩ ⟨14, 2, 0, 804907, 1695831, 1017, 4096⟩
    (by decide) selected_cut_31368

theorem unmarked_context_13_423957_804908 : frontier 8 ⟨804908, by decide⟩
    (prefixCache 13 423957) (prefixPartial 13 423957) = false := by
  decide +kernel

theorem node_context_13_423957_804908 : EJMOriginalGlobalDAGData.nodes 8 ⟨804908, by decide⟩ =
    .split (coordinate 13) (![⟨804809, by decide⟩,⟨804846, by decide⟩,⟨804874, by decide⟩,⟨804907, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_423957_804908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423957 ⟨804908, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 423957
    ⟨804908, by decide⟩ (by decide) (![⟨804809, by decide⟩,⟨804846, by decide⟩,⟨804874, by decide⟩,⟨804907, by decide⟩]) unmarked_context_13_423957_804908 node_context_13_423957_804908
  intro a
  fin_cases a
  · exact context_14_1695828_804809
  · exact context_14_1695829_804846
  · exact context_14_1695830_804874
  · exact context_14_1695831_804907

theorem selected_cut_31369 : selected 8 ⟨804966, by decide⟩
    (prefixPartial 13 423958) = some ⟨13, 2, 0, 804966, 423958, 1909, 16384⟩ := by
  decide +kernel

theorem context_13_423958_804966 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423958 ⟨804966, by decide⟩ :=
  accepted_of_selected 13 423958 ⟨804966, by decide⟩ ⟨13, 2, 0, 804966, 423958, 1909, 16384⟩
    (by decide) selected_cut_31369

theorem selected_cut_31370 : selected 8 ⟨805015, by decide⟩
    (prefixPartial 13 423959) = some ⟨13, 2, 0, 805015, 423959, 1193, 16384⟩ := by
  decide +kernel

theorem context_13_423959_805015 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423959 ⟨805015, by decide⟩ :=
  accepted_of_selected 13 423959 ⟨805015, by decide⟩ ⟨13, 2, 0, 805015, 423959, 1193, 16384⟩
    (by decide) selected_cut_31370

theorem unmarked_context_12_105989_805016 : frontier 9 ⟨805016, by decide⟩
    (prefixCache 12 105989) (prefixPartial 12 105989) = false := by
  decide +kernel

theorem node_context_12_105989_805016 : EJMOriginalGlobalDAGData.nodes 9 ⟨805016, by decide⟩ =
    .split (coordinate 12) (![⟨804775, by decide⟩,⟨804908, by decide⟩,⟨804966, by decide⟩,⟨805015, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105989_805016 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105989 ⟨805016, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105989
    ⟨805016, by decide⟩ (by decide) (![⟨804775, by decide⟩,⟨804908, by decide⟩,⟨804966, by decide⟩,⟨805015, by decide⟩]) unmarked_context_12_105989_805016 node_context_12_105989_805016
  intro a
  fin_cases a
  · exact context_13_423956_804775
  · exact context_13_423957_804908
  · exact context_13_423958_804966
  · exact context_13_423959_805015

theorem selected_cut_31371 : selected 9 ⟨763842, by decide⟩
    (prefixPartial 12 105990) = some ⟨12, 1, 0, 763842, 105990, 1, 65536⟩ := by
  decide +kernel

theorem context_12_105990_763842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105990 ⟨763842, by decide⟩ :=
  accepted_of_selected 12 105990 ⟨763842, by decide⟩ ⟨12, 1, 0, 763842, 105990, 1, 65536⟩
    (by decide) selected_cut_31371

theorem selected_cut_31372 : selected 8 ⟨805110, by decide⟩
    (prefixPartial 13 423964) = some ⟨13, 2, 0, 805110, 423964, 3837, 16384⟩ := by
  decide +kernel

theorem context_13_423964_805110 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423964 ⟨805110, by decide⟩ :=
  accepted_of_selected 13 423964 ⟨805110, by decide⟩ ⟨13, 2, 0, 805110, 423964, 3837, 16384⟩
    (by decide) selected_cut_31372

theorem selected_cut_31373 : selected 7 ⟨805138, by decide⟩
    (prefixPartial 14 1695860) = some ⟨14, 2, 0, 805138, 1695860, 1265, 4096⟩ := by
  decide +kernel

theorem context_14_1695860_805138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1695860 ⟨805138, by decide⟩ :=
  accepted_of_selected 14 1695860 ⟨805138, by decide⟩ ⟨14, 2, 0, 805138, 1695860, 1265, 4096⟩
    (by decide) selected_cut_31373

theorem selected_cut_31374 : selected 7 ⟨805168, by decide⟩
    (prefixPartial 14 1695861) = some ⟨14, 2, 0, 805168, 1695861, 1217, 4096⟩ := by
  decide +kernel

theorem context_14_1695861_805168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1695861 ⟨805168, by decide⟩ :=
  accepted_of_selected 14 1695861 ⟨805168, by decide⟩ ⟨14, 2, 0, 805168, 1695861, 1217, 4096⟩
    (by decide) selected_cut_31374

theorem selected_cut_31375 : selected 7 ⟨805191, by decide⟩
    (prefixPartial 14 1695862) = some ⟨14, 2, 0, 805191, 1695862, 1133, 4096⟩ := by
  decide +kernel

theorem context_14_1695862_805191 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1695862 ⟨805191, by decide⟩ :=
  accepted_of_selected 14 1695862 ⟨805191, by decide⟩ ⟨14, 2, 0, 805191, 1695862, 1133, 4096⟩
    (by decide) selected_cut_31375

theorem selected_cut_31376 : selected 7 ⟨805220, by decide⟩
    (prefixPartial 14 1695863) = some ⟨14, 2, 0, 805220, 1695863, 1113, 4096⟩ := by
  decide +kernel

theorem context_14_1695863_805220 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1695863 ⟨805220, by decide⟩ :=
  accepted_of_selected 14 1695863 ⟨805220, by decide⟩ ⟨14, 2, 0, 805220, 1695863, 1113, 4096⟩
    (by decide) selected_cut_31376

theorem unmarked_context_13_423965_805221 : frontier 8 ⟨805221, by decide⟩
    (prefixCache 13 423965) (prefixPartial 13 423965) = false := by
  decide +kernel

theorem node_context_13_423965_805221 : EJMOriginalGlobalDAGData.nodes 8 ⟨805221, by decide⟩ =
    .split (coordinate 13) (![⟨805138, by decide⟩,⟨805168, by decide⟩,⟨805191, by decide⟩,⟨805220, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_423965_805221 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423965 ⟨805221, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 423965
    ⟨805221, by decide⟩ (by decide) (![⟨805138, by decide⟩,⟨805168, by decide⟩,⟨805191, by decide⟩,⟨805220, by decide⟩]) unmarked_context_13_423965_805221 node_context_13_423965_805221
  intro a
  fin_cases a
  · exact context_14_1695860_805138
  · exact context_14_1695861_805168
  · exact context_14_1695862_805191
  · exact context_14_1695863_805220

theorem selected_cut_31377 : selected 8 ⟨805312, by decide⟩
    (prefixPartial 13 423966) = some ⟨13, 2, 0, 805312, 423966, 2413, 16384⟩ := by
  decide +kernel

theorem context_13_423966_805312 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423966 ⟨805312, by decide⟩ :=
  accepted_of_selected 13 423966 ⟨805312, by decide⟩ ⟨13, 2, 0, 805312, 423966, 2413, 16384⟩
    (by decide) selected_cut_31377

theorem selected_cut_31378 : selected 8 ⟨805367, by decide⟩
    (prefixPartial 13 423967) = some ⟨13, 2, 0, 805367, 423967, 1401, 16384⟩ := by
  decide +kernel

theorem context_13_423967_805367 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423967 ⟨805367, by decide⟩ :=
  accepted_of_selected 13 423967 ⟨805367, by decide⟩ ⟨13, 2, 0, 805367, 423967, 1401, 16384⟩
    (by decide) selected_cut_31378

theorem unmarked_context_12_105991_805368 : frontier 9 ⟨805368, by decide⟩
    (prefixCache 12 105991) (prefixPartial 12 105991) = false := by
  decide +kernel

theorem node_context_12_105991_805368 : EJMOriginalGlobalDAGData.nodes 9 ⟨805368, by decide⟩ =
    .split (coordinate 12) (![⟨805110, by decide⟩,⟨805221, by decide⟩,⟨805312, by decide⟩,⟨805367, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105991_805368 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105991 ⟨805368, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105991
    ⟨805368, by decide⟩ (by decide) (![⟨805110, by decide⟩,⟨805221, by decide⟩,⟨805312, by decide⟩,⟨805367, by decide⟩]) unmarked_context_12_105991_805368 node_context_12_105991_805368
  intro a
  fin_cases a
  · exact context_13_423964_805110
  · exact context_13_423965_805221
  · exact context_13_423966_805312
  · exact context_13_423967_805367

theorem unmarked_context_11_26497_805369 : frontier 10 ⟨805369, by decide⟩
    (prefixCache 11 26497) (prefixPartial 11 26497) = false := by
  decide +kernel

theorem node_context_11_26497_805369 : EJMOriginalGlobalDAGData.nodes 10 ⟨805369, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨805016, by decide⟩,⟨763842, by decide⟩,⟨805368, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26497_805369 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26497 ⟨805369, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26497
    ⟨805369, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨805016, by decide⟩,⟨763842, by decide⟩,⟨805368, by decide⟩]) unmarked_context_11_26497_805369 node_context_11_26497_805369
  intro a
  fin_cases a
  · exact context_12_105988_448748
  · exact context_12_105989_805016
  · exact context_12_105990_763842
  · exact context_12_105991_805368

theorem selected_cut_31379 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 105992) = some ⟨12, 1, 0, 448748, 105992, 1, 65536⟩ := by
  decide +kernel

theorem context_12_105992_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105992 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 105992 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 105992, 1, 65536⟩
    (by decide) selected_cut_31379

theorem selected_cut_31380 : selected 8 ⟨805446, by decide⟩
    (prefixPartial 13 423972) = some ⟨13, 2, 0, 805446, 423972, 3713, 16384⟩ := by
  decide +kernel

theorem context_13_423972_805446 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423972 ⟨805446, by decide⟩ :=
  accepted_of_selected 13 423972 ⟨805446, by decide⟩ ⟨13, 2, 0, 805446, 423972, 3713, 16384⟩
    (by decide) selected_cut_31380

theorem selected_cut_31381 : selected 8 ⟨805517, by decide⟩
    (prefixPartial 13 423973) = some ⟨13, 2, 0, 805517, 423973, 3725, 16384⟩ := by
  decide +kernel

theorem context_13_423973_805517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423973 ⟨805517, by decide⟩ :=
  accepted_of_selected 13 423973 ⟨805517, by decide⟩ ⟨13, 2, 0, 805517, 423973, 3725, 16384⟩
    (by decide) selected_cut_31381

theorem selected_cut_31382 : selected 8 ⟨805565, by decide⟩
    (prefixPartial 13 423974) = some ⟨13, 2, 0, 805565, 423974, 1981, 16384⟩ := by
  decide +kernel

theorem context_13_423974_805565 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423974 ⟨805565, by decide⟩ :=
  accepted_of_selected 13 423974 ⟨805565, by decide⟩ ⟨13, 2, 0, 805565, 423974, 1981, 16384⟩
    (by decide) selected_cut_31382

theorem selected_cut_31383 : selected 8 ⟨805577, by decide⟩
    (prefixPartial 13 423975) = some ⟨13, 2, 0, 805577, 423975, 1073, 16384⟩ := by
  decide +kernel

theorem context_13_423975_805577 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423975 ⟨805577, by decide⟩ :=
  accepted_of_selected 13 423975 ⟨805577, by decide⟩ ⟨13, 2, 0, 805577, 423975, 1073, 16384⟩
    (by decide) selected_cut_31383

theorem unmarked_context_12_105993_805578 : frontier 9 ⟨805578, by decide⟩
    (prefixCache 12 105993) (prefixPartial 12 105993) = false := by
  decide +kernel

theorem node_context_12_105993_805578 : EJMOriginalGlobalDAGData.nodes 9 ⟨805578, by decide⟩ =
    .split (coordinate 12) (![⟨805446, by decide⟩,⟨805517, by decide⟩,⟨805565, by decide⟩,⟨805577, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105993_805578 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105993 ⟨805578, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105993
    ⟨805578, by decide⟩ (by decide) (![⟨805446, by decide⟩,⟨805517, by decide⟩,⟨805565, by decide⟩,⟨805577, by decide⟩]) unmarked_context_12_105993_805578 node_context_12_105993_805578
  intro a
  fin_cases a
  · exact context_13_423972_805446
  · exact context_13_423973_805517
  · exact context_13_423974_805565
  · exact context_13_423975_805577

theorem selected_cut_31384 : selected 9 ⟨763842, by decide⟩
    (prefixPartial 12 105994) = some ⟨12, 1, 0, 763842, 105994, 1, 65536⟩ := by
  decide +kernel

theorem context_12_105994_763842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105994 ⟨763842, by decide⟩ :=
  accepted_of_selected 12 105994 ⟨763842, by decide⟩ ⟨12, 1, 0, 763842, 105994, 1, 65536⟩
    (by decide) selected_cut_31384

theorem selected_cut_31385 : selected 8 ⟨805651, by decide⟩
    (prefixPartial 13 423980) = some ⟨13, 2, 0, 805651, 423980, 3753, 16384⟩ := by
  decide +kernel

theorem context_13_423980_805651 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423980 ⟨805651, by decide⟩ :=
  accepted_of_selected 13 423980 ⟨805651, by decide⟩ ⟨13, 2, 0, 805651, 423980, 3753, 16384⟩
    (by decide) selected_cut_31385

theorem selected_cut_31386 : selected 7 ⟨805674, by decide⟩
    (prefixPartial 14 1695924) = some ⟨14, 2, 0, 805674, 1695924, 1173, 4096⟩ := by
  decide +kernel

theorem context_14_1695924_805674 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1695924 ⟨805674, by decide⟩ :=
  accepted_of_selected 14 1695924 ⟨805674, by decide⟩ ⟨14, 2, 0, 805674, 1695924, 1173, 4096⟩
    (by decide) selected_cut_31386

theorem selected_cut_31387 : selected 7 ⟨805696, by decide⟩
    (prefixPartial 14 1695925) = some ⟨14, 2, 0, 805696, 1695925, 1137, 4096⟩ := by
  decide +kernel

theorem context_14_1695925_805696 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1695925 ⟨805696, by decide⟩ :=
  accepted_of_selected 14 1695925 ⟨805696, by decide⟩ ⟨14, 2, 0, 805696, 1695925, 1137, 4096⟩
    (by decide) selected_cut_31387

theorem selected_cut_31388 : selected 7 ⟨805717, by decide⟩
    (prefixPartial 14 1695926) = some ⟨14, 2, 0, 805717, 1695926, 1133, 4096⟩ := by
  decide +kernel

theorem context_14_1695926_805717 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1695926 ⟨805717, by decide⟩ :=
  accepted_of_selected 14 1695926 ⟨805717, by decide⟩ ⟨14, 2, 0, 805717, 1695926, 1133, 4096⟩
    (by decide) selected_cut_31388

theorem selected_cut_31389 : selected 7 ⟨805738, by decide⟩
    (prefixPartial 14 1695927) = some ⟨14, 2, 0, 805738, 1695927, 973, 4096⟩ := by
  decide +kernel

theorem context_14_1695927_805738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1695927 ⟨805738, by decide⟩ :=
  accepted_of_selected 14 1695927 ⟨805738, by decide⟩ ⟨14, 2, 0, 805738, 1695927, 973, 4096⟩
    (by decide) selected_cut_31389

theorem unmarked_context_13_423981_805739 : frontier 8 ⟨805739, by decide⟩
    (prefixCache 13 423981) (prefixPartial 13 423981) = false := by
  decide +kernel

theorem node_context_13_423981_805739 : EJMOriginalGlobalDAGData.nodes 8 ⟨805739, by decide⟩ =
    .split (coordinate 13) (![⟨805674, by decide⟩,⟨805696, by decide⟩,⟨805717, by decide⟩,⟨805738, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_423981_805739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423981 ⟨805739, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 423981
    ⟨805739, by decide⟩ (by decide) (![⟨805674, by decide⟩,⟨805696, by decide⟩,⟨805717, by decide⟩,⟨805738, by decide⟩]) unmarked_context_13_423981_805739 node_context_13_423981_805739
  intro a
  fin_cases a
  · exact context_14_1695924_805674
  · exact context_14_1695925_805696
  · exact context_14_1695926_805717
  · exact context_14_1695927_805738

theorem selected_cut_31390 : selected 8 ⟨805787, by decide⟩
    (prefixPartial 13 423982) = some ⟨13, 2, 0, 805787, 423982, 2109, 16384⟩ := by
  decide +kernel

theorem context_13_423982_805787 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423982 ⟨805787, by decide⟩ :=
  accepted_of_selected 13 423982 ⟨805787, by decide⟩ ⟨13, 2, 0, 805787, 423982, 2109, 16384⟩
    (by decide) selected_cut_31390

theorem selected_cut_31391 : selected 8 ⟨805815, by decide⟩
    (prefixPartial 13 423983) = some ⟨13, 2, 0, 805815, 423983, 1161, 16384⟩ := by
  decide +kernel

theorem context_13_423983_805815 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 423983 ⟨805815, by decide⟩ :=
  accepted_of_selected 13 423983 ⟨805815, by decide⟩ ⟨13, 2, 0, 805815, 423983, 1161, 16384⟩
    (by decide) selected_cut_31391

theorem unmarked_context_12_105995_805816 : frontier 9 ⟨805816, by decide⟩
    (prefixCache 12 105995) (prefixPartial 12 105995) = false := by
  decide +kernel

theorem node_context_12_105995_805816 : EJMOriginalGlobalDAGData.nodes 9 ⟨805816, by decide⟩ =
    .split (coordinate 12) (![⟨805651, by decide⟩,⟨805739, by decide⟩,⟨805787, by decide⟩,⟨805815, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_105995_805816 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 105995 ⟨805816, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 105995
    ⟨805816, by decide⟩ (by decide) (![⟨805651, by decide⟩,⟨805739, by decide⟩,⟨805787, by decide⟩,⟨805815, by decide⟩]) unmarked_context_12_105995_805816 node_context_12_105995_805816
  intro a
  fin_cases a
  · exact context_13_423980_805651
  · exact context_13_423981_805739
  · exact context_13_423982_805787
  · exact context_13_423983_805815

theorem unmarked_context_11_26498_805817 : frontier 10 ⟨805817, by decide⟩
    (prefixCache 11 26498) (prefixPartial 11 26498) = false := by
  decide +kernel

theorem node_context_11_26498_805817 : EJMOriginalGlobalDAGData.nodes 10 ⟨805817, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨805578, by decide⟩,⟨763842, by decide⟩,⟨805816, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26498_805817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26498 ⟨805817, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26498
    ⟨805817, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨805578, by decide⟩,⟨763842, by decide⟩,⟨805816, by decide⟩]) unmarked_context_11_26498_805817 node_context_11_26498_805817
  intro a
  fin_cases a
  · exact context_12_105992_448748
  · exact context_12_105993_805578
  · exact context_12_105994_763842
  · exact context_12_105995_805816

theorem selected_cut_31392 : selected 10 ⟨789341, by decide⟩
    (prefixPartial 11 26499) = some ⟨11, 1, 0, 789341, 26499, 1, 262144⟩ := by
  decide +kernel

theorem context_11_26499_789341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26499 ⟨789341, by decide⟩ :=
  accepted_of_selected 11 26499 ⟨789341, by decide⟩ ⟨11, 1, 0, 789341, 26499, 1, 262144⟩
    (by decide) selected_cut_31392

theorem unmarked_context_10_6624_805818 : frontier 11 ⟨805818, by decide⟩
    (prefixCache 10 6624) (prefixPartial 10 6624) = false := by
  decide +kernel

theorem node_context_10_6624_805818 : EJMOriginalGlobalDAGData.nodes 11 ⟨805818, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨805369, by decide⟩,⟨805817, by decide⟩,⟨789341, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6624_805818 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6624 ⟨805818, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6624
    ⟨805818, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨805369, by decide⟩,⟨805817, by decide⟩,⟨789341, by decide⟩]) unmarked_context_10_6624_805818 node_context_10_6624_805818
  intro a
  fin_cases a
  · exact context_11_26496_434745
  · exact context_11_26497_805369
  · exact context_11_26498_805817
  · exact context_11_26499_789341

theorem selected_cut_31393 : selected 8 ⟨805863, by decide⟩
    (prefixPartial 13 424000) = some ⟨13, 2, 0, 805863, 424000, 2041, 16384⟩ := by
  decide +kernel

theorem context_13_424000_805863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424000 ⟨805863, by decide⟩ :=
  accepted_of_selected 13 424000 ⟨805863, by decide⟩ ⟨13, 2, 0, 805863, 424000, 2041, 16384⟩
    (by decide) selected_cut_31393

theorem selected_cut_31394 : selected 8 ⟨805892, by decide⟩
    (prefixPartial 13 424001) = some ⟨13, 2, 0, 805892, 424001, 2093, 16384⟩ := by
  decide +kernel

theorem context_13_424001_805892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424001 ⟨805892, by decide⟩ :=
  accepted_of_selected 13 424001 ⟨805892, by decide⟩ ⟨13, 2, 0, 805892, 424001, 2093, 16384⟩
    (by decide) selected_cut_31394

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
