/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover359
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_34563 : selected 8 ⟨898607, by decide⟩
    (prefixPartial 13 1124382) = some ⟨13, 2, 0, 898607, 1124382, 1157, 16384⟩ := by
  decide +kernel

theorem context_13_1124382_898607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1124382 ⟨898607, by decide⟩ :=
  accepted_of_selected 13 1124382 ⟨898607, by decide⟩ ⟨13, 2, 0, 898607, 1124382, 1157, 16384⟩
    (by decide) selected_cut_34563

theorem selected_cut_34564 : selected 8 ⟨898626, by decide⟩
    (prefixPartial 13 1124383) = some ⟨13, 2, 0, 898626, 1124383, 817, 16384⟩ := by
  decide +kernel

theorem context_13_1124383_898626 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1124383 ⟨898626, by decide⟩ :=
  accepted_of_selected 13 1124383 ⟨898626, by decide⟩ ⟨13, 2, 0, 898626, 1124383, 817, 16384⟩
    (by decide) selected_cut_34564

theorem unmarked_context_12_281095_898627 : frontier 9 ⟨898627, by decide⟩
    (prefixCache 12 281095) (prefixPartial 12 281095) = false := by
  decide +kernel

theorem node_context_12_281095_898627 : EJMOriginalGlobalDAGData.nodes 9 ⟨898627, by decide⟩ =
    .split (coordinate 12) (![⟨898553, by decide⟩,⟨898578, by decide⟩,⟨898607, by decide⟩,⟨898626, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_281095_898627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281095 ⟨898627, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 281095
    ⟨898627, by decide⟩ (by decide) (![⟨898553, by decide⟩,⟨898578, by decide⟩,⟨898607, by decide⟩,⟨898626, by decide⟩]) unmarked_context_12_281095_898627 node_context_12_281095_898627
  intro a
  fin_cases a
  · exact context_13_1124380_898553
  · exact context_13_1124381_898578
  · exact context_13_1124382_898607
  · exact context_13_1124383_898626

theorem unmarked_context_11_70273_898628 : frontier 10 ⟨898628, by decide⟩
    (prefixCache 11 70273) (prefixPartial 11 70273) = false := by
  decide +kernel

theorem node_context_11_70273_898628 : EJMOriginalGlobalDAGData.nodes 10 ⟨898628, by decide⟩ =
    .split (coordinate 11) (![⟨898284, by decide⟩,⟨898384, by decide⟩,⟨898503, by decide⟩,⟨898627, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70273_898628 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70273 ⟨898628, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70273
    ⟨898628, by decide⟩ (by decide) (![⟨898284, by decide⟩,⟨898384, by decide⟩,⟨898503, by decide⟩,⟨898627, by decide⟩]) unmarked_context_11_70273_898628 node_context_11_70273_898628
  intro a
  fin_cases a
  · exact context_12_281092_898284
  · exact context_12_281093_898384
  · exact context_12_281094_898503
  · exact context_12_281095_898627

theorem selected_cut_34565 : selected 9 ⟨898719, by decide⟩
    (prefixPartial 12 281096) = some ⟨12, 2, 0, 898719, 281096, 2769, 65536⟩ := by
  decide +kernel

theorem context_12_281096_898719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281096 ⟨898719, by decide⟩ :=
  accepted_of_selected 12 281096 ⟨898719, by decide⟩ ⟨12, 2, 0, 898719, 281096, 2769, 65536⟩
    (by decide) selected_cut_34565

theorem selected_cut_34566 : selected 9 ⟨898815, by decide⟩
    (prefixPartial 12 281097) = some ⟨12, 2, 0, 898815, 281097, 3689, 65536⟩ := by
  decide +kernel

theorem context_12_281097_898815 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281097 ⟨898815, by decide⟩ :=
  accepted_of_selected 12 281097 ⟨898815, by decide⟩ ⟨12, 2, 0, 898815, 281097, 3689, 65536⟩
    (by decide) selected_cut_34566

theorem selected_cut_34567 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 281098) = some ⟨12, 1, 0, 893903, 281098, 1, 65536⟩ := by
  decide +kernel

theorem context_12_281098_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281098 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 281098 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 281098, 1, 65536⟩
    (by decide) selected_cut_34567

theorem selected_cut_34568 : selected 8 ⟨898854, by decide⟩
    (prefixPartial 13 1124396) = some ⟨13, 2, 0, 898854, 1124396, 1405, 16384⟩ := by
  decide +kernel

theorem context_13_1124396_898854 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1124396 ⟨898854, by decide⟩ :=
  accepted_of_selected 13 1124396 ⟨898854, by decide⟩ ⟨13, 2, 0, 898854, 1124396, 1405, 16384⟩
    (by decide) selected_cut_34568

theorem selected_cut_34569 : selected 8 ⟨898879, by decide⟩
    (prefixPartial 13 1124397) = some ⟨13, 2, 0, 898879, 1124397, 849, 16384⟩ := by
  decide +kernel

theorem context_13_1124397_898879 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1124397 ⟨898879, by decide⟩ :=
  accepted_of_selected 13 1124397 ⟨898879, by decide⟩ ⟨13, 2, 0, 898879, 1124397, 849, 16384⟩
    (by decide) selected_cut_34569

theorem selected_cut_34570 : selected 8 ⟨898900, by decide⟩
    (prefixPartial 13 1124398) = some ⟨13, 2, 0, 898900, 1124398, 1241, 16384⟩ := by
  decide +kernel

theorem context_13_1124398_898900 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1124398 ⟨898900, by decide⟩ :=
  accepted_of_selected 13 1124398 ⟨898900, by decide⟩ ⟨13, 2, 0, 898900, 1124398, 1241, 16384⟩
    (by decide) selected_cut_34570

theorem selected_cut_34571 : selected 8 ⟨898919, by decide⟩
    (prefixPartial 13 1124399) = some ⟨13, 2, 0, 898919, 1124399, 865, 16384⟩ := by
  decide +kernel

theorem context_13_1124399_898919 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1124399 ⟨898919, by decide⟩ :=
  accepted_of_selected 13 1124399 ⟨898919, by decide⟩ ⟨13, 2, 0, 898919, 1124399, 865, 16384⟩
    (by decide) selected_cut_34571

theorem unmarked_context_12_281099_898920 : frontier 9 ⟨898920, by decide⟩
    (prefixCache 12 281099) (prefixPartial 12 281099) = false := by
  decide +kernel

theorem node_context_12_281099_898920 : EJMOriginalGlobalDAGData.nodes 9 ⟨898920, by decide⟩ =
    .split (coordinate 12) (![⟨898854, by decide⟩,⟨898879, by decide⟩,⟨898900, by decide⟩,⟨898919, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_281099_898920 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281099 ⟨898920, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 281099
    ⟨898920, by decide⟩ (by decide) (![⟨898854, by decide⟩,⟨898879, by decide⟩,⟨898900, by decide⟩,⟨898919, by decide⟩]) unmarked_context_12_281099_898920 node_context_12_281099_898920
  intro a
  fin_cases a
  · exact context_13_1124396_898854
  · exact context_13_1124397_898879
  · exact context_13_1124398_898900
  · exact context_13_1124399_898919

theorem unmarked_context_11_70274_898921 : frontier 10 ⟨898921, by decide⟩
    (prefixCache 11 70274) (prefixPartial 11 70274) = false := by
  decide +kernel

theorem node_context_11_70274_898921 : EJMOriginalGlobalDAGData.nodes 10 ⟨898921, by decide⟩ =
    .split (coordinate 11) (![⟨898719, by decide⟩,⟨898815, by decide⟩,⟨893903, by decide⟩,⟨898920, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70274_898921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70274 ⟨898921, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70274
    ⟨898921, by decide⟩ (by decide) (![⟨898719, by decide⟩,⟨898815, by decide⟩,⟨893903, by decide⟩,⟨898920, by decide⟩]) unmarked_context_11_70274_898921 node_context_11_70274_898921
  intro a
  fin_cases a
  · exact context_12_281096_898719
  · exact context_12_281097_898815
  · exact context_12_281098_893903
  · exact context_12_281099_898920

theorem selected_cut_34572 : selected 9 ⟨899015, by decide⟩
    (prefixPartial 12 281100) = some ⟨12, 2, 0, 899015, 281100, 2941, 65536⟩ := by
  decide +kernel

theorem context_12_281100_899015 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281100 ⟨899015, by decide⟩ :=
  accepted_of_selected 12 281100 ⟨899015, by decide⟩ ⟨12, 2, 0, 899015, 281100, 2941, 65536⟩
    (by decide) selected_cut_34572

theorem selected_cut_34573 : selected 9 ⟨899102, by decide⟩
    (prefixPartial 12 281101) = some ⟨12, 2, 0, 899102, 281101, 3957, 65536⟩ := by
  decide +kernel

theorem context_12_281101_899102 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281101 ⟨899102, by decide⟩ :=
  accepted_of_selected 12 281101 ⟨899102, by decide⟩ ⟨12, 2, 0, 899102, 281101, 3957, 65536⟩
    (by decide) selected_cut_34573

theorem selected_cut_34574 : selected 8 ⟨899139, by decide⟩
    (prefixPartial 13 1124408) = some ⟨13, 2, 0, 899139, 1124408, 1437, 16384⟩ := by
  decide +kernel

theorem context_13_1124408_899139 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1124408 ⟨899139, by decide⟩ :=
  accepted_of_selected 13 1124408 ⟨899139, by decide⟩ ⟨13, 2, 0, 899139, 1124408, 1437, 16384⟩
    (by decide) selected_cut_34574

theorem selected_cut_34575 : selected 8 ⟨899168, by decide⟩
    (prefixPartial 13 1124409) = some ⟨13, 2, 0, 899168, 1124409, 873, 16384⟩ := by
  decide +kernel

theorem context_13_1124409_899168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1124409 ⟨899168, by decide⟩ :=
  accepted_of_selected 13 1124409 ⟨899168, by decide⟩ ⟨13, 2, 0, 899168, 1124409, 873, 16384⟩
    (by decide) selected_cut_34575

theorem selected_cut_34576 : selected 8 ⟨899199, by decide⟩
    (prefixPartial 13 1124410) = some ⟨13, 2, 0, 899199, 1124410, 1329, 16384⟩ := by
  decide +kernel

theorem context_13_1124410_899199 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1124410 ⟨899199, by decide⟩ :=
  accepted_of_selected 13 1124410 ⟨899199, by decide⟩ ⟨13, 2, 0, 899199, 1124410, 1329, 16384⟩
    (by decide) selected_cut_34576

theorem selected_cut_34577 : selected 8 ⟨899213, by decide⟩
    (prefixPartial 13 1124411) = some ⟨13, 2, 0, 899213, 1124411, 757, 16384⟩ := by
  decide +kernel

theorem context_13_1124411_899213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1124411 ⟨899213, by decide⟩ :=
  accepted_of_selected 13 1124411 ⟨899213, by decide⟩ ⟨13, 2, 0, 899213, 1124411, 757, 16384⟩
    (by decide) selected_cut_34577

theorem unmarked_context_12_281102_899214 : frontier 9 ⟨899214, by decide⟩
    (prefixCache 12 281102) (prefixPartial 12 281102) = false := by
  decide +kernel

theorem node_context_12_281102_899214 : EJMOriginalGlobalDAGData.nodes 9 ⟨899214, by decide⟩ =
    .split (coordinate 12) (![⟨899139, by decide⟩,⟨899168, by decide⟩,⟨899199, by decide⟩,⟨899213, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_281102_899214 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281102 ⟨899214, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 281102
    ⟨899214, by decide⟩ (by decide) (![⟨899139, by decide⟩,⟨899168, by decide⟩,⟨899199, by decide⟩,⟨899213, by decide⟩]) unmarked_context_12_281102_899214 node_context_12_281102_899214
  intro a
  fin_cases a
  · exact context_13_1124408_899139
  · exact context_13_1124409_899168
  · exact context_13_1124410_899199
  · exact context_13_1124411_899213

theorem selected_cut_34578 : selected 8 ⟨899251, by decide⟩
    (prefixPartial 13 1124412) = some ⟨13, 2, 0, 899251, 1124412, 1385, 16384⟩ := by
  decide +kernel

theorem context_13_1124412_899251 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1124412 ⟨899251, by decide⟩ :=
  accepted_of_selected 13 1124412 ⟨899251, by decide⟩ ⟨13, 2, 0, 899251, 1124412, 1385, 16384⟩
    (by decide) selected_cut_34578

theorem selected_cut_34579 : selected 8 ⟨899273, by decide⟩
    (prefixPartial 13 1124413) = some ⟨13, 2, 0, 899273, 1124413, 849, 16384⟩ := by
  decide +kernel

theorem context_13_1124413_899273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1124413 ⟨899273, by decide⟩ :=
  accepted_of_selected 13 1124413 ⟨899273, by decide⟩ ⟨13, 2, 0, 899273, 1124413, 849, 16384⟩
    (by decide) selected_cut_34579

theorem selected_cut_34580 : selected 8 ⟨899295, by decide⟩
    (prefixPartial 13 1124414) = some ⟨13, 2, 0, 899295, 1124414, 1225, 16384⟩ := by
  decide +kernel

theorem context_13_1124414_899295 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1124414 ⟨899295, by decide⟩ :=
  accepted_of_selected 13 1124414 ⟨899295, by decide⟩ ⟨13, 2, 0, 899295, 1124414, 1225, 16384⟩
    (by decide) selected_cut_34580

theorem selected_cut_34581 : selected 8 ⟨899309, by decide⟩
    (prefixPartial 13 1124415) = some ⟨13, 2, 0, 899309, 1124415, 753, 16384⟩ := by
  decide +kernel

theorem context_13_1124415_899309 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1124415 ⟨899309, by decide⟩ :=
  accepted_of_selected 13 1124415 ⟨899309, by decide⟩ ⟨13, 2, 0, 899309, 1124415, 753, 16384⟩
    (by decide) selected_cut_34581

theorem unmarked_context_12_281103_899310 : frontier 9 ⟨899310, by decide⟩
    (prefixCache 12 281103) (prefixPartial 12 281103) = false := by
  decide +kernel

theorem node_context_12_281103_899310 : EJMOriginalGlobalDAGData.nodes 9 ⟨899310, by decide⟩ =
    .split (coordinate 12) (![⟨899251, by decide⟩,⟨899273, by decide⟩,⟨899295, by decide⟩,⟨899309, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_281103_899310 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281103 ⟨899310, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 281103
    ⟨899310, by decide⟩ (by decide) (![⟨899251, by decide⟩,⟨899273, by decide⟩,⟨899295, by decide⟩,⟨899309, by decide⟩]) unmarked_context_12_281103_899310 node_context_12_281103_899310
  intro a
  fin_cases a
  · exact context_13_1124412_899251
  · exact context_13_1124413_899273
  · exact context_13_1124414_899295
  · exact context_13_1124415_899309

theorem unmarked_context_11_70275_899311 : frontier 10 ⟨899311, by decide⟩
    (prefixCache 11 70275) (prefixPartial 11 70275) = false := by
  decide +kernel

theorem node_context_11_70275_899311 : EJMOriginalGlobalDAGData.nodes 10 ⟨899311, by decide⟩ =
    .split (coordinate 11) (![⟨899015, by decide⟩,⟨899102, by decide⟩,⟨899214, by decide⟩,⟨899310, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70275_899311 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70275 ⟨899311, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70275
    ⟨899311, by decide⟩ (by decide) (![⟨899015, by decide⟩,⟨899102, by decide⟩,⟨899214, by decide⟩,⟨899310, by decide⟩]) unmarked_context_11_70275_899311 node_context_11_70275_899311
  intro a
  fin_cases a
  · exact context_12_281100_899015
  · exact context_12_281101_899102
  · exact context_12_281102_899214
  · exact context_12_281103_899310

theorem unmarked_context_10_17568_899312 : frontier 11 ⟨899312, by decide⟩
    (prefixCache 10 17568) (prefixPartial 10 17568) = false := by
  decide +kernel

theorem node_context_10_17568_899312 : EJMOriginalGlobalDAGData.nodes 11 ⟨899312, by decide⟩ =
    .split (coordinate 10) (![⟨898148, by decide⟩,⟨898628, by decide⟩,⟨898921, by decide⟩,⟨899311, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17568_899312 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17568 ⟨899312, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17568
    ⟨899312, by decide⟩ (by decide) (![⟨898148, by decide⟩,⟨898628, by decide⟩,⟨898921, by decide⟩,⟨899311, by decide⟩]) unmarked_context_10_17568_899312 node_context_10_17568_899312
  intro a
  fin_cases a
  · exact context_11_70272_898148
  · exact context_11_70273_898628
  · exact context_11_70274_898921
  · exact context_11_70275_899311

theorem selected_cut_34582 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 281104) = some ⟨12, 1, 0, 1738, 281104, 1, 65536⟩ := by
  decide +kernel

theorem context_12_281104_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281104 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 281104 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 281104, 1, 65536⟩
    (by decide) selected_cut_34582

theorem selected_cut_34583 : selected 9 ⟨899425, by decide⟩
    (prefixPartial 12 281105) = some ⟨12, 2, 0, 899425, 281105, 2853, 65536⟩ := by
  decide +kernel

theorem context_12_281105_899425 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281105 ⟨899425, by decide⟩ :=
  accepted_of_selected 12 281105 ⟨899425, by decide⟩ ⟨12, 2, 0, 899425, 281105, 2853, 65536⟩
    (by decide) selected_cut_34583

theorem selected_cut_34584 : selected 9 ⟨899555, by decide⟩
    (prefixPartial 12 281106) = some ⟨12, 2, 0, 899555, 281106, 2665, 65536⟩ := by
  decide +kernel

theorem context_12_281106_899555 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281106 ⟨899555, by decide⟩ :=
  accepted_of_selected 12 281106 ⟨899555, by decide⟩ ⟨12, 2, 0, 899555, 281106, 2665, 65536⟩
    (by decide) selected_cut_34584

theorem selected_cut_34585 : selected 8 ⟨899599, by decide⟩
    (prefixPartial 13 1124428) = some ⟨13, 2, 0, 899599, 1124428, 1585, 16384⟩ := by
  decide +kernel

theorem context_13_1124428_899599 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1124428 ⟨899599, by decide⟩ :=
  accepted_of_selected 13 1124428 ⟨899599, by decide⟩ ⟨13, 2, 0, 899599, 1124428, 1585, 16384⟩
    (by decide) selected_cut_34585

theorem selected_cut_34586 : selected 8 ⟨899624, by decide⟩
    (prefixPartial 13 1124429) = some ⟨13, 2, 0, 899624, 1124429, 829, 16384⟩ := by
  decide +kernel

theorem context_13_1124429_899624 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1124429 ⟨899624, by decide⟩ :=
  accepted_of_selected 13 1124429 ⟨899624, by decide⟩ ⟨13, 2, 0, 899624, 1124429, 829, 16384⟩
    (by decide) selected_cut_34586

theorem selected_cut_34587 : selected 8 ⟨899664, by decide⟩
    (prefixPartial 13 1124430) = some ⟨13, 2, 0, 899664, 1124430, 1281, 16384⟩ := by
  decide +kernel

theorem context_13_1124430_899664 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1124430 ⟨899664, by decide⟩ :=
  accepted_of_selected 13 1124430 ⟨899664, by decide⟩ ⟨13, 2, 0, 899664, 1124430, 1281, 16384⟩
    (by decide) selected_cut_34587

theorem selected_cut_34588 : selected 8 ⟨899674, by decide⟩
    (prefixPartial 13 1124431) = some ⟨13, 2, 0, 899674, 1124431, 625, 16384⟩ := by
  decide +kernel

theorem context_13_1124431_899674 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1124431 ⟨899674, by decide⟩ :=
  accepted_of_selected 13 1124431 ⟨899674, by decide⟩ ⟨13, 2, 0, 899674, 1124431, 625, 16384⟩
    (by decide) selected_cut_34588

theorem unmarked_context_12_281107_899675 : frontier 9 ⟨899675, by decide⟩
    (prefixCache 12 281107) (prefixPartial 12 281107) = false := by
  decide +kernel

theorem node_context_12_281107_899675 : EJMOriginalGlobalDAGData.nodes 9 ⟨899675, by decide⟩ =
    .split (coordinate 12) (![⟨899599, by decide⟩,⟨899624, by decide⟩,⟨899664, by decide⟩,⟨899674, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_281107_899675 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281107 ⟨899675, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 281107
    ⟨899675, by decide⟩ (by decide) (![⟨899599, by decide⟩,⟨899624, by decide⟩,⟨899664, by decide⟩,⟨899674, by decide⟩]) unmarked_context_12_281107_899675 node_context_12_281107_899675
  intro a
  fin_cases a
  · exact context_13_1124428_899599
  · exact context_13_1124429_899624
  · exact context_13_1124430_899664
  · exact context_13_1124431_899674

theorem unmarked_context_11_70276_899676 : frontier 10 ⟨899676, by decide⟩
    (prefixCache 11 70276) (prefixPartial 11 70276) = false := by
  decide +kernel

theorem node_context_11_70276_899676 : EJMOriginalGlobalDAGData.nodes 10 ⟨899676, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨899425, by decide⟩,⟨899555, by decide⟩,⟨899675, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70276_899676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70276 ⟨899676, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70276
    ⟨899676, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨899425, by decide⟩,⟨899555, by decide⟩,⟨899675, by decide⟩]) unmarked_context_11_70276_899676 node_context_11_70276_899676
  intro a
  fin_cases a
  · exact context_12_281104_1738
  · exact context_12_281105_899425
  · exact context_12_281106_899555
  · exact context_12_281107_899675

theorem selected_cut_34589 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 281108) = some ⟨12, 1, 0, 1738, 281108, 1, 65536⟩ := by
  decide +kernel

theorem context_12_281108_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281108 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 281108 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 281108, 1, 65536⟩
    (by decide) selected_cut_34589

theorem selected_cut_34590 : selected 9 ⟨899756, by decide⟩
    (prefixPartial 12 281109) = some ⟨12, 2, 0, 899756, 281109, 2077, 65536⟩ := by
  decide +kernel

theorem context_12_281109_899756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281109 ⟨899756, by decide⟩ :=
  accepted_of_selected 12 281109 ⟨899756, by decide⟩ ⟨12, 2, 0, 899756, 281109, 2077, 65536⟩
    (by decide) selected_cut_34590

theorem selected_cut_34591 : selected 9 ⟨899846, by decide⟩
    (prefixPartial 12 281110) = some ⟨12, 2, 0, 899846, 281110, 3117, 65536⟩ := by
  decide +kernel

theorem context_12_281110_899846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281110 ⟨899846, by decide⟩ :=
  accepted_of_selected 12 281110 ⟨899846, by decide⟩ ⟨12, 2, 0, 899846, 281110, 3117, 65536⟩
    (by decide) selected_cut_34591

theorem selected_cut_34592 : selected 9 ⟨899931, by decide⟩
    (prefixPartial 12 281111) = some ⟨12, 2, 0, 899931, 281111, 3353, 65536⟩ := by
  decide +kernel

theorem context_12_281111_899931 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281111 ⟨899931, by decide⟩ :=
  accepted_of_selected 12 281111 ⟨899931, by decide⟩ ⟨12, 2, 0, 899931, 281111, 3353, 65536⟩
    (by decide) selected_cut_34592

theorem unmarked_context_11_70277_899932 : frontier 10 ⟨899932, by decide⟩
    (prefixCache 11 70277) (prefixPartial 11 70277) = false := by
  decide +kernel

theorem node_context_11_70277_899932 : EJMOriginalGlobalDAGData.nodes 10 ⟨899932, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨899756, by decide⟩,⟨899846, by decide⟩,⟨899931, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70277_899932 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70277 ⟨899932, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70277
    ⟨899932, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨899756, by decide⟩,⟨899846, by decide⟩,⟨899931, by decide⟩]) unmarked_context_11_70277_899932 node_context_11_70277_899932
  intro a
  fin_cases a
  · exact context_12_281108_1738
  · exact context_12_281109_899756
  · exact context_12_281110_899846
  · exact context_12_281111_899931

theorem selected_cut_34593 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 281112) = some ⟨12, 1, 0, 1738, 281112, 1, 65536⟩ := by
  decide +kernel

theorem context_12_281112_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281112 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 281112 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 281112, 1, 65536⟩
    (by decide) selected_cut_34593

theorem selected_cut_34594 : selected 9 ⟨900019, by decide⟩
    (prefixPartial 12 281113) = some ⟨12, 2, 0, 900019, 281113, 2133, 65536⟩ := by
  decide +kernel

theorem context_12_281113_900019 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281113 ⟨900019, by decide⟩ :=
  accepted_of_selected 12 281113 ⟨900019, by decide⟩ ⟨12, 2, 0, 900019, 281113, 2133, 65536⟩
    (by decide) selected_cut_34594

theorem selected_cut_34595 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 281114) = some ⟨12, 1, 0, 893903, 281114, 1, 65536⟩ := by
  decide +kernel

theorem context_12_281114_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281114 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 281114 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 281114, 1, 65536⟩
    (by decide) selected_cut_34595

theorem selected_cut_34596 : selected 9 ⟨900125, by decide⟩
    (prefixPartial 12 281115) = some ⟨12, 2, 0, 900125, 281115, 3505, 65536⟩ := by
  decide +kernel

theorem context_12_281115_900125 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281115 ⟨900125, by decide⟩ :=
  accepted_of_selected 12 281115 ⟨900125, by decide⟩ ⟨12, 2, 0, 900125, 281115, 3505, 65536⟩
    (by decide) selected_cut_34596

theorem unmarked_context_11_70278_900126 : frontier 10 ⟨900126, by decide⟩
    (prefixCache 11 70278) (prefixPartial 11 70278) = false := by
  decide +kernel

theorem node_context_11_70278_900126 : EJMOriginalGlobalDAGData.nodes 10 ⟨900126, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨900019, by decide⟩,⟨893903, by decide⟩,⟨900125, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70278_900126 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70278 ⟨900126, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70278
    ⟨900126, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨900019, by decide⟩,⟨893903, by decide⟩,⟨900125, by decide⟩]) unmarked_context_11_70278_900126 node_context_11_70278_900126
  intro a
  fin_cases a
  · exact context_12_281112_1738
  · exact context_12_281113_900019
  · exact context_12_281114_893903
  · exact context_12_281115_900125

theorem selected_cut_34597 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 281116) = some ⟨12, 1, 0, 1738, 281116, 1, 65536⟩ := by
  decide +kernel

theorem context_12_281116_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281116 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 281116 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 281116, 1, 65536⟩
    (by decide) selected_cut_34597

theorem selected_cut_34598 : selected 9 ⟨900196, by decide⟩
    (prefixPartial 12 281117) = some ⟨12, 2, 0, 900196, 281117, 2101, 65536⟩ := by
  decide +kernel

theorem context_12_281117_900196 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281117 ⟨900196, by decide⟩ :=
  accepted_of_selected 12 281117 ⟨900196, by decide⟩ ⟨12, 2, 0, 900196, 281117, 2101, 65536⟩
    (by decide) selected_cut_34598

theorem selected_cut_34599 : selected 9 ⟨900283, by decide⟩
    (prefixPartial 12 281118) = some ⟨12, 2, 0, 900283, 281118, 3189, 65536⟩ := by
  decide +kernel

theorem context_12_281118_900283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281118 ⟨900283, by decide⟩ :=
  accepted_of_selected 12 281118 ⟨900283, by decide⟩ ⟨12, 2, 0, 900283, 281118, 3189, 65536⟩
    (by decide) selected_cut_34599

theorem selected_cut_34600 : selected 9 ⟨900360, by decide⟩
    (prefixPartial 12 281119) = some ⟨12, 2, 0, 900360, 281119, 3085, 65536⟩ := by
  decide +kernel

theorem context_12_281119_900360 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281119 ⟨900360, by decide⟩ :=
  accepted_of_selected 12 281119 ⟨900360, by decide⟩ ⟨12, 2, 0, 900360, 281119, 3085, 65536⟩
    (by decide) selected_cut_34600

theorem unmarked_context_11_70279_900361 : frontier 10 ⟨900361, by decide⟩
    (prefixCache 11 70279) (prefixPartial 11 70279) = false := by
  decide +kernel

theorem node_context_11_70279_900361 : EJMOriginalGlobalDAGData.nodes 10 ⟨900361, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨900196, by decide⟩,⟨900283, by decide⟩,⟨900360, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70279_900361 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70279 ⟨900361, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70279
    ⟨900361, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨900196, by decide⟩,⟨900283, by decide⟩,⟨900360, by decide⟩]) unmarked_context_11_70279_900361 node_context_11_70279_900361
  intro a
  fin_cases a
  · exact context_12_281116_1738
  · exact context_12_281117_900196
  · exact context_12_281118_900283
  · exact context_12_281119_900360

theorem unmarked_context_10_17569_900362 : frontier 11 ⟨900362, by decide⟩
    (prefixCache 10 17569) (prefixPartial 10 17569) = false := by
  decide +kernel

theorem node_context_10_17569_900362 : EJMOriginalGlobalDAGData.nodes 11 ⟨900362, by decide⟩ =
    .split (coordinate 10) (![⟨899676, by decide⟩,⟨899932, by decide⟩,⟨900126, by decide⟩,⟨900361, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17569_900362 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17569 ⟨900362, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17569
    ⟨900362, by decide⟩ (by decide) (![⟨899676, by decide⟩,⟨899932, by decide⟩,⟨900126, by decide⟩,⟨900361, by decide⟩]) unmarked_context_10_17569_900362 node_context_10_17569_900362
  intro a
  fin_cases a
  · exact context_11_70276_899676
  · exact context_11_70277_899932
  · exact context_11_70278_900126
  · exact context_11_70279_900361

theorem selected_cut_34601 : selected 10 ⟨900363, by decide⟩
    (prefixPartial 11 70280) = some ⟨11, 1, 0, 900363, 70280, 1, 262144⟩ := by
  decide +kernel

theorem context_11_70280_900363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70280 ⟨900363, by decide⟩ :=
  accepted_of_selected 11 70280 ⟨900363, by decide⟩ ⟨11, 1, 0, 900363, 70280, 1, 262144⟩
    (by decide) selected_cut_34601

theorem selected_cut_34602 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 281124) = some ⟨12, 1, 0, 1738, 281124, 1, 65536⟩ := by
  decide +kernel

theorem context_12_281124_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281124 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 281124 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 281124, 1, 65536⟩
    (by decide) selected_cut_34602

theorem selected_cut_34603 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 281125) = some ⟨12, 1, 0, 1738, 281125, 1, 65536⟩ := by
  decide +kernel

theorem context_12_281125_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281125 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 281125 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 281125, 1, 65536⟩
    (by decide) selected_cut_34603

theorem selected_cut_34604 : selected 9 ⟨900475, by decide⟩
    (prefixPartial 12 281126) = some ⟨12, 2, 0, 900475, 281126, 2001, 65536⟩ := by
  decide +kernel

theorem context_12_281126_900475 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281126 ⟨900475, by decide⟩ :=
  accepted_of_selected 12 281126 ⟨900475, by decide⟩ ⟨12, 2, 0, 900475, 281126, 2001, 65536⟩
    (by decide) selected_cut_34604

theorem selected_cut_34605 : selected 9 ⟨900585, by decide⟩
    (prefixPartial 12 281127) = some ⟨12, 2, 0, 900585, 281127, 2777, 65536⟩ := by
  decide +kernel

theorem context_12_281127_900585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281127 ⟨900585, by decide⟩ :=
  accepted_of_selected 12 281127 ⟨900585, by decide⟩ ⟨12, 2, 0, 900585, 281127, 2777, 65536⟩
    (by decide) selected_cut_34605

theorem unmarked_context_11_70281_900586 : frontier 10 ⟨900586, by decide⟩
    (prefixCache 11 70281) (prefixPartial 11 70281) = false := by
  decide +kernel

theorem node_context_11_70281_900586 : EJMOriginalGlobalDAGData.nodes 10 ⟨900586, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨900475, by decide⟩,⟨900585, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70281_900586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70281 ⟨900586, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70281
    ⟨900586, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨900475, by decide⟩,⟨900585, by decide⟩]) unmarked_context_11_70281_900586 node_context_11_70281_900586
  intro a
  fin_cases a
  · exact context_12_281124_1738
  · exact context_12_281125_1738
  · exact context_12_281126_900475
  · exact context_12_281127_900585

theorem selected_cut_34606 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 70282) = some ⟨11, 1, 0, 900587, 70282, 1, 262144⟩ := by
  decide +kernel

theorem context_11_70282_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70282 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 70282 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 70282, 1, 262144⟩
    (by decide) selected_cut_34606

theorem selected_cut_34607 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 281132) = some ⟨12, 1, 0, 1738, 281132, 1, 65536⟩ := by
  decide +kernel

theorem context_12_281132_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281132 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 281132 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 281132, 1, 65536⟩
    (by decide) selected_cut_34607

theorem selected_cut_34608 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 281133) = some ⟨12, 1, 0, 1738, 281133, 1, 65536⟩ := by
  decide +kernel

theorem context_12_281133_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281133 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 281133 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 281133, 1, 65536⟩
    (by decide) selected_cut_34608

theorem selected_cut_34609 : selected 9 ⟨900699, by decide⟩
    (prefixPartial 12 281134) = some ⟨12, 2, 0, 900699, 281134, 2365, 65536⟩ := by
  decide +kernel

theorem context_12_281134_900699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281134 ⟨900699, by decide⟩ :=
  accepted_of_selected 12 281134 ⟨900699, by decide⟩ ⟨12, 2, 0, 900699, 281134, 2365, 65536⟩
    (by decide) selected_cut_34609

theorem selected_cut_34610 : selected 9 ⟨900806, by decide⟩
    (prefixPartial 12 281135) = some ⟨12, 2, 0, 900806, 281135, 2985, 65536⟩ := by
  decide +kernel

theorem context_12_281135_900806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281135 ⟨900806, by decide⟩ :=
  accepted_of_selected 12 281135 ⟨900806, by decide⟩ ⟨12, 2, 0, 900806, 281135, 2985, 65536⟩
    (by decide) selected_cut_34610

theorem unmarked_context_11_70283_900807 : frontier 10 ⟨900807, by decide⟩
    (prefixCache 11 70283) (prefixPartial 11 70283) = false := by
  decide +kernel

theorem node_context_11_70283_900807 : EJMOriginalGlobalDAGData.nodes 10 ⟨900807, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨900699, by decide⟩,⟨900806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70283_900807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70283 ⟨900807, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70283
    ⟨900807, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨1738, by decide⟩,⟨900699, by decide⟩,⟨900806, by decide⟩]) unmarked_context_11_70283_900807 node_context_11_70283_900807
  intro a
  fin_cases a
  · exact context_12_281132_1738
  · exact context_12_281133_1738
  · exact context_12_281134_900699
  · exact context_12_281135_900806

theorem unmarked_context_10_17570_900808 : frontier 11 ⟨900808, by decide⟩
    (prefixCache 10 17570) (prefixPartial 10 17570) = false := by
  decide +kernel

theorem node_context_10_17570_900808 : EJMOriginalGlobalDAGData.nodes 11 ⟨900808, by decide⟩ =
    .split (coordinate 10) (![⟨900363, by decide⟩,⟨900586, by decide⟩,⟨900587, by decide⟩,⟨900807, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17570_900808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17570 ⟨900808, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17570
    ⟨900808, by decide⟩ (by decide) (![⟨900363, by decide⟩,⟨900586, by decide⟩,⟨900587, by decide⟩,⟨900807, by decide⟩]) unmarked_context_10_17570_900808 node_context_10_17570_900808
  intro a
  fin_cases a
  · exact context_11_70280_900363
  · exact context_11_70281_900586
  · exact context_11_70282_900587
  · exact context_11_70283_900807

theorem selected_cut_34611 : selected 10 ⟨900903, by decide⟩
    (prefixPartial 11 70284) = some ⟨11, 2, 0, 900903, 70284, 1517, 262144⟩ := by
  decide +kernel

theorem context_11_70284_900903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70284 ⟨900903, by decide⟩ :=
  accepted_of_selected 11 70284 ⟨900903, by decide⟩ ⟨11, 2, 0, 900903, 70284, 1517, 262144⟩
    (by decide) selected_cut_34611

theorem selected_cut_34612 : selected 10 ⟨900988, by decide⟩
    (prefixPartial 11 70285) = some ⟨11, 2, 0, 900988, 70285, 1881, 262144⟩ := by
  decide +kernel

theorem context_11_70285_900988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70285 ⟨900988, by decide⟩ :=
  accepted_of_selected 11 70285 ⟨900988, by decide⟩ ⟨11, 2, 0, 900988, 70285, 1881, 262144⟩
    (by decide) selected_cut_34612

theorem selected_cut_34613 : selected 10 ⟨901087, by decide⟩
    (prefixPartial 11 70286) = some ⟨11, 2, 0, 901087, 70286, 2125, 262144⟩ := by
  decide +kernel

theorem context_11_70286_901087 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70286 ⟨901087, by decide⟩ :=
  accepted_of_selected 11 70286 ⟨901087, by decide⟩ ⟨11, 2, 0, 901087, 70286, 2125, 262144⟩
    (by decide) selected_cut_34613

theorem selected_cut_34614 : selected 10 ⟨901156, by decide⟩
    (prefixPartial 11 70287) = some ⟨11, 2, 0, 901156, 70287, 1757, 262144⟩ := by
  decide +kernel

theorem context_11_70287_901156 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70287 ⟨901156, by decide⟩ :=
  accepted_of_selected 11 70287 ⟨901156, by decide⟩ ⟨11, 2, 0, 901156, 70287, 1757, 262144⟩
    (by decide) selected_cut_34614

theorem unmarked_context_10_17571_901157 : frontier 11 ⟨901157, by decide⟩
    (prefixCache 10 17571) (prefixPartial 10 17571) = false := by
  decide +kernel

theorem node_context_10_17571_901157 : EJMOriginalGlobalDAGData.nodes 11 ⟨901157, by decide⟩ =
    .split (coordinate 10) (![⟨900903, by decide⟩,⟨900988, by decide⟩,⟨901087, by decide⟩,⟨901156, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17571_901157 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17571 ⟨901157, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17571
    ⟨901157, by decide⟩ (by decide) (![⟨900903, by decide⟩,⟨900988, by decide⟩,⟨901087, by decide⟩,⟨901156, by decide⟩]) unmarked_context_10_17571_901157 node_context_10_17571_901157
  intro a
  fin_cases a
  · exact context_11_70284_900903
  · exact context_11_70285_900988
  · exact context_11_70286_901087
  · exact context_11_70287_901156

theorem unmarked_context_9_4392_901158 : frontier 12 ⟨901158, by decide⟩
    (prefixCache 9 4392) (prefixPartial 9 4392) = false := by
  decide +kernel

theorem node_context_9_4392_901158 : EJMOriginalGlobalDAGData.nodes 12 ⟨901158, by decide⟩ =
    .split (coordinate 9) (![⟨899312, by decide⟩,⟨900362, by decide⟩,⟨900808, by decide⟩,⟨901157, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4392_901158 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4392 ⟨901158, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4392
    ⟨901158, by decide⟩ (by decide) (![⟨899312, by decide⟩,⟨900362, by decide⟩,⟨900808, by decide⟩,⟨901157, by decide⟩]) unmarked_context_9_4392_901158 node_context_9_4392_901158
  intro a
  fin_cases a
  · exact context_10_17568_899312
  · exact context_10_17569_900362
  · exact context_10_17570_900808
  · exact context_10_17571_901157

theorem selected_cut_34615 : selected 10 ⟨901159, by decide⟩
    (prefixPartial 11 70288) = some ⟨11, 1, 0, 901159, 70288, 1, 262144⟩ := by
  decide +kernel

theorem context_11_70288_901159 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70288 ⟨901159, by decide⟩ :=
  accepted_of_selected 11 70288 ⟨901159, by decide⟩ ⟨11, 1, 0, 901159, 70288, 1, 262144⟩
    (by decide) selected_cut_34615

theorem selected_cut_34616 : selected 9 ⟨901281, by decide⟩
    (prefixPartial 12 281156) = some ⟨12, 2, 0, 901281, 281156, 1713, 65536⟩ := by
  decide +kernel

theorem context_12_281156_901281 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281156 ⟨901281, by decide⟩ :=
  accepted_of_selected 12 281156 ⟨901281, by decide⟩ ⟨12, 2, 0, 901281, 281156, 1713, 65536⟩
    (by decide) selected_cut_34616

theorem selected_cut_34617 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 281157) = some ⟨12, 1, 0, 896706, 281157, 1, 65536⟩ := by
  decide +kernel

theorem context_12_281157_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281157 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 281157 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 281157, 1, 65536⟩
    (by decide) selected_cut_34617

theorem selected_cut_34618 : selected 9 ⟨901359, by decide⟩
    (prefixPartial 12 281158) = some ⟨12, 2, 0, 901359, 281158, 1965, 65536⟩ := by
  decide +kernel

theorem context_12_281158_901359 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281158 ⟨901359, by decide⟩ :=
  accepted_of_selected 12 281158 ⟨901359, by decide⟩ ⟨12, 2, 0, 901359, 281158, 1965, 65536⟩
    (by decide) selected_cut_34618

theorem selected_cut_34619 : selected 9 ⟨901432, by decide⟩
    (prefixPartial 12 281159) = some ⟨12, 2, 0, 901432, 281159, 2025, 65536⟩ := by
  decide +kernel

theorem context_12_281159_901432 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281159 ⟨901432, by decide⟩ :=
  accepted_of_selected 12 281159 ⟨901432, by decide⟩ ⟨12, 2, 0, 901432, 281159, 2025, 65536⟩
    (by decide) selected_cut_34619

theorem unmarked_context_11_70289_901433 : frontier 10 ⟨901433, by decide⟩
    (prefixCache 11 70289) (prefixPartial 11 70289) = false := by
  decide +kernel

theorem node_context_11_70289_901433 : EJMOriginalGlobalDAGData.nodes 10 ⟨901433, by decide⟩ =
    .split (coordinate 11) (![⟨901281, by decide⟩,⟨896706, by decide⟩,⟨901359, by decide⟩,⟨901432, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70289_901433 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70289 ⟨901433, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70289
    ⟨901433, by decide⟩ (by decide) (![⟨901281, by decide⟩,⟨896706, by decide⟩,⟨901359, by decide⟩,⟨901432, by decide⟩]) unmarked_context_11_70289_901433 node_context_11_70289_901433
  intro a
  fin_cases a
  · exact context_12_281156_901281
  · exact context_12_281157_896706
  · exact context_12_281158_901359
  · exact context_12_281159_901432

theorem selected_cut_34620 : selected 10 ⟨901577, by decide⟩
    (prefixPartial 11 70290) = some ⟨11, 2, 0, 901577, 70290, 2321, 262144⟩ := by
  decide +kernel

theorem context_11_70290_901577 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70290 ⟨901577, by decide⟩ :=
  accepted_of_selected 11 70290 ⟨901577, by decide⟩ ⟨11, 2, 0, 901577, 70290, 2321, 262144⟩
    (by decide) selected_cut_34620

theorem selected_cut_34621 : selected 9 ⟨901647, by decide⟩
    (prefixPartial 12 281164) = some ⟨12, 2, 0, 901647, 281164, 1645, 65536⟩ := by
  decide +kernel

theorem context_12_281164_901647 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281164 ⟨901647, by decide⟩ :=
  accepted_of_selected 12 281164 ⟨901647, by decide⟩ ⟨12, 2, 0, 901647, 281164, 1645, 65536⟩
    (by decide) selected_cut_34621

theorem selected_cut_34622 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 281165) = some ⟨12, 1, 0, 896706, 281165, 1, 65536⟩ := by
  decide +kernel

theorem context_12_281165_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281165 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 281165 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 281165, 1, 65536⟩
    (by decide) selected_cut_34622

theorem selected_cut_34623 : selected 9 ⟨901720, by decide⟩
    (prefixPartial 12 281166) = some ⟨12, 2, 0, 901720, 281166, 2113, 65536⟩ := by
  decide +kernel

theorem context_12_281166_901720 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281166 ⟨901720, by decide⟩ :=
  accepted_of_selected 12 281166 ⟨901720, by decide⟩ ⟨12, 2, 0, 901720, 281166, 2113, 65536⟩
    (by decide) selected_cut_34623

theorem selected_cut_34624 : selected 9 ⟨901776, by decide⟩
    (prefixPartial 12 281167) = some ⟨12, 2, 0, 901776, 281167, 2061, 65536⟩ := by
  decide +kernel

theorem context_12_281167_901776 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281167 ⟨901776, by decide⟩ :=
  accepted_of_selected 12 281167 ⟨901776, by decide⟩ ⟨12, 2, 0, 901776, 281167, 2061, 65536⟩
    (by decide) selected_cut_34624

theorem unmarked_context_11_70291_901777 : frontier 10 ⟨901777, by decide⟩
    (prefixCache 11 70291) (prefixPartial 11 70291) = false := by
  decide +kernel

theorem node_context_11_70291_901777 : EJMOriginalGlobalDAGData.nodes 10 ⟨901777, by decide⟩ =
    .split (coordinate 11) (![⟨901647, by decide⟩,⟨896706, by decide⟩,⟨901720, by decide⟩,⟨901776, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70291_901777 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70291 ⟨901777, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70291
    ⟨901777, by decide⟩ (by decide) (![⟨901647, by decide⟩,⟨896706, by decide⟩,⟨901720, by decide⟩,⟨901776, by decide⟩]) unmarked_context_11_70291_901777 node_context_11_70291_901777
  intro a
  fin_cases a
  · exact context_12_281164_901647
  · exact context_12_281165_896706
  · exact context_12_281166_901720
  · exact context_12_281167_901776

theorem unmarked_context_10_17572_901778 : frontier 11 ⟨901778, by decide⟩
    (prefixCache 10 17572) (prefixPartial 10 17572) = false := by
  decide +kernel

theorem node_context_10_17572_901778 : EJMOriginalGlobalDAGData.nodes 11 ⟨901778, by decide⟩ =
    .split (coordinate 10) (![⟨901159, by decide⟩,⟨901433, by decide⟩,⟨901577, by decide⟩,⟨901777, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17572_901778 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17572 ⟨901778, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17572
    ⟨901778, by decide⟩ (by decide) (![⟨901159, by decide⟩,⟨901433, by decide⟩,⟨901577, by decide⟩,⟨901777, by decide⟩]) unmarked_context_10_17572_901778 node_context_10_17572_901778
  intro a
  fin_cases a
  · exact context_11_70288_901159
  · exact context_11_70289_901433
  · exact context_11_70290_901577
  · exact context_11_70291_901777

theorem selected_cut_34625 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 17573) = some ⟨10, 1, 0, 893098, 17573, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_17573_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17573 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 17573 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 17573, 1, 1048576⟩
    (by decide) selected_cut_34625

theorem selected_cut_34626 : selected 10 ⟨901159, by decide⟩
    (prefixPartial 11 70296) = some ⟨11, 1, 0, 901159, 70296, 1, 262144⟩ := by
  decide +kernel

theorem context_11_70296_901159 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70296 ⟨901159, by decide⟩ :=
  accepted_of_selected 11 70296 ⟨901159, by decide⟩ ⟨11, 1, 0, 901159, 70296, 1, 262144⟩
    (by decide) selected_cut_34626

theorem selected_cut_34627 : selected 10 ⟨901910, by decide⟩
    (prefixPartial 11 70297) = some ⟨11, 2, 0, 901910, 70297, 2369, 262144⟩ := by
  decide +kernel

theorem context_11_70297_901910 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70297 ⟨901910, by decide⟩ :=
  accepted_of_selected 11 70297 ⟨901910, by decide⟩ ⟨11, 2, 0, 901910, 70297, 2369, 262144⟩
    (by decide) selected_cut_34627

theorem selected_cut_34628 : selected 10 ⟨900363, by decide⟩
    (prefixPartial 11 70298) = some ⟨11, 1, 0, 900363, 70298, 1, 262144⟩ := by
  decide +kernel

theorem context_11_70298_900363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70298 ⟨900363, by decide⟩ :=
  accepted_of_selected 11 70298 ⟨900363, by decide⟩ ⟨11, 1, 0, 900363, 70298, 1, 262144⟩
    (by decide) selected_cut_34628

theorem selected_cut_34629 : selected 10 ⟨902048, by decide⟩
    (prefixPartial 11 70299) = some ⟨11, 2, 0, 902048, 70299, 3001, 262144⟩ := by
  decide +kernel

theorem context_11_70299_902048 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70299 ⟨902048, by decide⟩ :=
  accepted_of_selected 11 70299 ⟨902048, by decide⟩ ⟨11, 2, 0, 902048, 70299, 3001, 262144⟩
    (by decide) selected_cut_34629

theorem unmarked_context_10_17574_902049 : frontier 11 ⟨902049, by decide⟩
    (prefixCache 10 17574) (prefixPartial 10 17574) = false := by
  decide +kernel

theorem node_context_10_17574_902049 : EJMOriginalGlobalDAGData.nodes 11 ⟨902049, by decide⟩ =
    .split (coordinate 10) (![⟨901159, by decide⟩,⟨901910, by decide⟩,⟨900363, by decide⟩,⟨902048, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17574_902049 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17574 ⟨902049, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17574
    ⟨902049, by decide⟩ (by decide) (![⟨901159, by decide⟩,⟨901910, by decide⟩,⟨900363, by decide⟩,⟨902048, by decide⟩]) unmarked_context_10_17574_902049 node_context_10_17574_902049
  intro a
  fin_cases a
  · exact context_11_70296_901159
  · exact context_11_70297_901910
  · exact context_11_70298_900363
  · exact context_11_70299_902048

theorem selected_cut_34630 : selected 11 ⟨902216, by decide⟩
    (prefixPartial 10 17575) = some ⟨10, 2, 0, 902216, 17575, 2785, 1048576⟩ := by
  decide +kernel

theorem context_10_17575_902216 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17575 ⟨902216, by decide⟩ :=
  accepted_of_selected 10 17575 ⟨902216, by decide⟩ ⟨10, 2, 0, 902216, 17575, 2785, 1048576⟩
    (by decide) selected_cut_34630

theorem unmarked_context_9_4393_902217 : frontier 12 ⟨902217, by decide⟩
    (prefixCache 9 4393) (prefixPartial 9 4393) = false := by
  decide +kernel

theorem node_context_9_4393_902217 : EJMOriginalGlobalDAGData.nodes 12 ⟨902217, by decide⟩ =
    .split (coordinate 9) (![⟨901778, by decide⟩,⟨893098, by decide⟩,⟨902049, by decide⟩,⟨902216, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4393_902217 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4393 ⟨902217, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4393
    ⟨902217, by decide⟩ (by decide) (![⟨901778, by decide⟩,⟨893098, by decide⟩,⟨902049, by decide⟩,⟨902216, by decide⟩]) unmarked_context_9_4393_902217 node_context_9_4393_902217
  intro a
  fin_cases a
  · exact context_10_17572_901778
  · exact context_10_17573_893098
  · exact context_10_17574_902049
  · exact context_10_17575_902216

theorem selected_cut_34631 : selected 10 ⟨901159, by decide⟩
    (prefixPartial 11 70304) = some ⟨11, 1, 0, 901159, 70304, 1, 262144⟩ := by
  decide +kernel

theorem context_11_70304_901159 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70304 ⟨901159, by decide⟩ :=
  accepted_of_selected 11 70304 ⟨901159, by decide⟩ ⟨11, 1, 0, 901159, 70304, 1, 262144⟩
    (by decide) selected_cut_34631

theorem selected_cut_34632 : selected 10 ⟨902335, by decide⟩
    (prefixPartial 11 70305) = some ⟨11, 2, 0, 902335, 70305, 2245, 262144⟩ := by
  decide +kernel

theorem context_11_70305_902335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70305 ⟨902335, by decide⟩ :=
  accepted_of_selected 11 70305 ⟨902335, by decide⟩ ⟨11, 2, 0, 902335, 70305, 2245, 262144⟩
    (by decide) selected_cut_34632

theorem selected_cut_34633 : selected 10 ⟨901159, by decide⟩
    (prefixPartial 11 70306) = some ⟨11, 1, 0, 901159, 70306, 1, 262144⟩ := by
  decide +kernel

theorem context_11_70306_901159 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70306 ⟨901159, by decide⟩ :=
  accepted_of_selected 11 70306 ⟨901159, by decide⟩ ⟨11, 1, 0, 901159, 70306, 1, 262144⟩
    (by decide) selected_cut_34633

theorem selected_cut_34634 : selected 10 ⟨902482, by decide⟩
    (prefixPartial 11 70307) = some ⟨11, 2, 0, 902482, 70307, 3613, 262144⟩ := by
  decide +kernel

theorem context_11_70307_902482 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70307 ⟨902482, by decide⟩ :=
  accepted_of_selected 11 70307 ⟨902482, by decide⟩ ⟨11, 2, 0, 902482, 70307, 3613, 262144⟩
    (by decide) selected_cut_34634

theorem unmarked_context_10_17576_902483 : frontier 11 ⟨902483, by decide⟩
    (prefixCache 10 17576) (prefixPartial 10 17576) = false := by
  decide +kernel

theorem node_context_10_17576_902483 : EJMOriginalGlobalDAGData.nodes 11 ⟨902483, by decide⟩ =
    .split (coordinate 10) (![⟨901159, by decide⟩,⟨902335, by decide⟩,⟨901159, by decide⟩,⟨902482, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17576_902483 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17576 ⟨902483, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17576
    ⟨902483, by decide⟩ (by decide) (![⟨901159, by decide⟩,⟨902335, by decide⟩,⟨901159, by decide⟩,⟨902482, by decide⟩]) unmarked_context_10_17576_902483 node_context_10_17576_902483
  intro a
  fin_cases a
  · exact context_11_70304_901159
  · exact context_11_70305_902335
  · exact context_11_70306_901159
  · exact context_11_70307_902482

theorem selected_cut_34635 : selected 11 ⟨902626, by decide⟩
    (prefixPartial 10 17577) = some ⟨10, 2, 0, 902626, 17577, 2805, 1048576⟩ := by
  decide +kernel

theorem context_10_17577_902626 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17577 ⟨902626, by decide⟩ :=
  accepted_of_selected 10 17577 ⟨902626, by decide⟩ ⟨10, 2, 0, 902626, 17577, 2805, 1048576⟩
    (by decide) selected_cut_34635

theorem selected_cut_34636 : selected 11 ⟨902676, by decide⟩
    (prefixPartial 10 17578) = some ⟨10, 2, 0, 902676, 17578, 673, 1048576⟩ := by
  decide +kernel

theorem context_10_17578_902676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17578 ⟨902676, by decide⟩ :=
  accepted_of_selected 10 17578 ⟨902676, by decide⟩ ⟨10, 2, 0, 902676, 17578, 673, 1048576⟩
    (by decide) selected_cut_34636

theorem selected_cut_34637 : selected 11 ⟨902709, by decide⟩
    (prefixPartial 10 17579) = some ⟨10, 2, 0, 902709, 17579, 381, 1048576⟩ := by
  decide +kernel

theorem context_10_17579_902709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17579 ⟨902709, by decide⟩ :=
  accepted_of_selected 10 17579 ⟨902709, by decide⟩ ⟨10, 2, 0, 902709, 17579, 381, 1048576⟩
    (by decide) selected_cut_34637

theorem unmarked_context_9_4394_902710 : frontier 12 ⟨902710, by decide⟩
    (prefixCache 9 4394) (prefixPartial 9 4394) = false := by
  decide +kernel

theorem node_context_9_4394_902710 : EJMOriginalGlobalDAGData.nodes 12 ⟨902710, by decide⟩ =
    .split (coordinate 9) (![⟨902483, by decide⟩,⟨902626, by decide⟩,⟨902676, by decide⟩,⟨902709, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4394_902710 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4394 ⟨902710, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4394
    ⟨902710, by decide⟩ (by decide) (![⟨902483, by decide⟩,⟨902626, by decide⟩,⟨902676, by decide⟩,⟨902709, by decide⟩]) unmarked_context_9_4394_902710 node_context_9_4394_902710
  intro a
  fin_cases a
  · exact context_10_17576_902483
  · exact context_10_17577_902626
  · exact context_10_17578_902676
  · exact context_10_17579_902709

theorem selected_cut_34638 : selected 12 ⟨902807, by decide⟩
    (prefixPartial 9 4395) = some ⟨9, 2, 0, 902807, 4395, 945, 4194304⟩ := by
  decide +kernel

theorem context_9_4395_902807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4395 ⟨902807, by decide⟩ :=
  accepted_of_selected 9 4395 ⟨902807, by decide⟩ ⟨9, 2, 0, 902807, 4395, 945, 4194304⟩
    (by decide) selected_cut_34638

theorem unmarked_context_8_1098_902808 : frontier 13 ⟨902808, by decide⟩
    (prefixCache 8 1098) (prefixPartial 8 1098) = false := by
  decide +kernel

theorem node_context_8_1098_902808 : EJMOriginalGlobalDAGData.nodes 13 ⟨902808, by decide⟩ =
    .split (coordinate 8) (![⟨901158, by decide⟩,⟨902217, by decide⟩,⟨902710, by decide⟩,⟨902807, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1098_902808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1098 ⟨902808, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1098
    ⟨902808, by decide⟩ (by decide) (![⟨901158, by decide⟩,⟨902217, by decide⟩,⟨902710, by decide⟩,⟨902807, by decide⟩]) unmarked_context_8_1098_902808 node_context_8_1098_902808
  intro a
  fin_cases a
  · exact context_9_4392_901158
  · exact context_9_4393_902217
  · exact context_9_4394_902710
  · exact context_9_4395_902807

theorem selected_cut_34639 : selected 9 ⟨902890, by decide⟩
    (prefixPartial 12 281344) = some ⟨12, 2, 0, 902890, 281344, 2257, 65536⟩ := by
  decide +kernel

theorem context_12_281344_902890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281344 ⟨902890, by decide⟩ :=
  accepted_of_selected 12 281344 ⟨902890, by decide⟩ ⟨12, 2, 0, 902890, 281344, 2257, 65536⟩
    (by decide) selected_cut_34639

theorem selected_cut_34640 : selected 9 ⟨902985, by decide⟩
    (prefixPartial 12 281345) = some ⟨12, 2, 0, 902985, 281345, 3881, 65536⟩ := by
  decide +kernel

theorem context_12_281345_902985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281345 ⟨902985, by decide⟩ :=
  accepted_of_selected 12 281345 ⟨902985, by decide⟩ ⟨12, 2, 0, 902985, 281345, 3881, 65536⟩
    (by decide) selected_cut_34640

theorem selected_cut_34641 : selected 8 ⟨903008, by decide⟩
    (prefixPartial 13 1125384) = some ⟨13, 2, 0, 903008, 1125384, 1709, 16384⟩ := by
  decide +kernel

theorem context_13_1125384_903008 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1125384 ⟨903008, by decide⟩ :=
  accepted_of_selected 13 1125384 ⟨903008, by decide⟩ ⟨13, 2, 0, 903008, 1125384, 1709, 16384⟩
    (by decide) selected_cut_34641

theorem selected_cut_34642 : selected 8 ⟨903025, by decide⟩
    (prefixPartial 13 1125385) = some ⟨13, 2, 0, 903025, 1125385, 793, 16384⟩ := by
  decide +kernel

theorem context_13_1125385_903025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1125385 ⟨903025, by decide⟩ :=
  accepted_of_selected 13 1125385 ⟨903025, by decide⟩ ⟨13, 2, 0, 903025, 1125385, 793, 16384⟩
    (by decide) selected_cut_34642

theorem selected_cut_34643 : selected 8 ⟨903047, by decide⟩
    (prefixPartial 13 1125386) = some ⟨13, 2, 0, 903047, 1125386, 1061, 16384⟩ := by
  decide +kernel

theorem context_13_1125386_903047 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1125386 ⟨903047, by decide⟩ :=
  accepted_of_selected 13 1125386 ⟨903047, by decide⟩ ⟨13, 2, 0, 903047, 1125386, 1061, 16384⟩
    (by decide) selected_cut_34643

theorem selected_cut_34644 : selected 8 ⟨903057, by decide⟩
    (prefixPartial 13 1125387) = some ⟨13, 2, 0, 903057, 1125387, 569, 16384⟩ := by
  decide +kernel

theorem context_13_1125387_903057 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1125387 ⟨903057, by decide⟩ :=
  accepted_of_selected 13 1125387 ⟨903057, by decide⟩ ⟨13, 2, 0, 903057, 1125387, 569, 16384⟩
    (by decide) selected_cut_34644

theorem unmarked_context_12_281346_903058 : frontier 9 ⟨903058, by decide⟩
    (prefixCache 12 281346) (prefixPartial 12 281346) = false := by
  decide +kernel

theorem node_context_12_281346_903058 : EJMOriginalGlobalDAGData.nodes 9 ⟨903058, by decide⟩ =
    .split (coordinate 12) (![⟨903008, by decide⟩,⟨903025, by decide⟩,⟨903047, by decide⟩,⟨903057, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_281346_903058 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281346 ⟨903058, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 281346
    ⟨903058, by decide⟩ (by decide) (![⟨903008, by decide⟩,⟨903025, by decide⟩,⟨903047, by decide⟩,⟨903057, by decide⟩]) unmarked_context_12_281346_903058 node_context_12_281346_903058
  intro a
  fin_cases a
  · exact context_13_1125384_903008
  · exact context_13_1125385_903025
  · exact context_13_1125386_903047
  · exact context_13_1125387_903057

theorem selected_cut_34645 : selected 9 ⟨903138, by decide⟩
    (prefixPartial 12 281347) = some ⟨12, 2, 0, 903138, 281347, 3937, 65536⟩ := by
  decide +kernel

theorem context_12_281347_903138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281347 ⟨903138, by decide⟩ :=
  accepted_of_selected 12 281347 ⟨903138, by decide⟩ ⟨12, 2, 0, 903138, 281347, 3937, 65536⟩
    (by decide) selected_cut_34645

theorem unmarked_context_11_70336_903139 : frontier 10 ⟨903139, by decide⟩
    (prefixCache 11 70336) (prefixPartial 11 70336) = false := by
  decide +kernel

theorem node_context_11_70336_903139 : EJMOriginalGlobalDAGData.nodes 10 ⟨903139, by decide⟩ =
    .split (coordinate 11) (![⟨902890, by decide⟩,⟨902985, by decide⟩,⟨903058, by decide⟩,⟨903138, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70336_903139 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70336 ⟨903139, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70336
    ⟨903139, by decide⟩ (by decide) (![⟨902890, by decide⟩,⟨902985, by decide⟩,⟨903058, by decide⟩,⟨903138, by decide⟩]) unmarked_context_11_70336_903139 node_context_11_70336_903139
  intro a
  fin_cases a
  · exact context_12_281344_902890
  · exact context_12_281345_902985
  · exact context_12_281346_903058
  · exact context_12_281347_903138

theorem selected_cut_34646 : selected 9 ⟨903203, by decide⟩
    (prefixPartial 12 281348) = some ⟨12, 2, 0, 903203, 281348, 2221, 65536⟩ := by
  decide +kernel

theorem context_12_281348_903203 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281348 ⟨903203, by decide⟩ :=
  accepted_of_selected 12 281348 ⟨903203, by decide⟩ ⟨12, 2, 0, 903203, 281348, 2221, 65536⟩
    (by decide) selected_cut_34646

theorem selected_cut_34647 : selected 9 ⟨903273, by decide⟩
    (prefixPartial 12 281349) = some ⟨12, 2, 0, 903273, 281349, 3581, 65536⟩ := by
  decide +kernel

theorem context_12_281349_903273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281349 ⟨903273, by decide⟩ :=
  accepted_of_selected 12 281349 ⟨903273, by decide⟩ ⟨12, 2, 0, 903273, 281349, 3581, 65536⟩
    (by decide) selected_cut_34647

theorem selected_cut_34648 : selected 9 ⟨903346, by decide⟩
    (prefixPartial 12 281350) = some ⟨12, 2, 0, 903346, 281350, 3877, 65536⟩ := by
  decide +kernel

theorem context_12_281350_903346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281350 ⟨903346, by decide⟩ :=
  accepted_of_selected 12 281350 ⟨903346, by decide⟩ ⟨12, 2, 0, 903346, 281350, 3877, 65536⟩
    (by decide) selected_cut_34648

theorem selected_cut_34649 : selected 9 ⟨903413, by decide⟩
    (prefixPartial 12 281351) = some ⟨12, 2, 0, 903413, 281351, 3737, 65536⟩ := by
  decide +kernel

theorem context_12_281351_903413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281351 ⟨903413, by decide⟩ :=
  accepted_of_selected 12 281351 ⟨903413, by decide⟩ ⟨12, 2, 0, 903413, 281351, 3737, 65536⟩
    (by decide) selected_cut_34649

theorem unmarked_context_11_70337_903414 : frontier 10 ⟨903414, by decide⟩
    (prefixCache 11 70337) (prefixPartial 11 70337) = false := by
  decide +kernel

theorem node_context_11_70337_903414 : EJMOriginalGlobalDAGData.nodes 10 ⟨903414, by decide⟩ =
    .split (coordinate 11) (![⟨903203, by decide⟩,⟨903273, by decide⟩,⟨903346, by decide⟩,⟨903413, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70337_903414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70337 ⟨903414, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70337
    ⟨903414, by decide⟩ (by decide) (![⟨903203, by decide⟩,⟨903273, by decide⟩,⟨903346, by decide⟩,⟨903413, by decide⟩]) unmarked_context_11_70337_903414 node_context_11_70337_903414
  intro a
  fin_cases a
  · exact context_12_281348_903203
  · exact context_12_281349_903273
  · exact context_12_281350_903346
  · exact context_12_281351_903413

theorem selected_cut_34650 : selected 9 ⟨903486, by decide⟩
    (prefixPartial 12 281352) = some ⟨12, 2, 0, 903486, 281352, 3533, 65536⟩ := by
  decide +kernel

theorem context_12_281352_903486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281352 ⟨903486, by decide⟩ :=
  accepted_of_selected 12 281352 ⟨903486, by decide⟩ ⟨12, 2, 0, 903486, 281352, 3533, 65536⟩
    (by decide) selected_cut_34650

theorem selected_cut_34651 : selected 9 ⟨903548, by decide⟩
    (prefixPartial 12 281353) = some ⟨12, 2, 0, 903548, 281353, 3473, 65536⟩ := by
  decide +kernel

theorem context_12_281353_903548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281353 ⟨903548, by decide⟩ :=
  accepted_of_selected 12 281353 ⟨903548, by decide⟩ ⟨12, 2, 0, 903548, 281353, 3473, 65536⟩
    (by decide) selected_cut_34651

theorem selected_cut_34652 : selected 9 ⟨903615, by decide⟩
    (prefixPartial 12 281354) = some ⟨12, 2, 0, 903615, 281354, 3741, 65536⟩ := by
  decide +kernel

theorem context_12_281354_903615 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281354 ⟨903615, by decide⟩ :=
  accepted_of_selected 12 281354 ⟨903615, by decide⟩ ⟨12, 2, 0, 903615, 281354, 3741, 65536⟩
    (by decide) selected_cut_34652

theorem selected_cut_34653 : selected 9 ⟨903684, by decide⟩
    (prefixPartial 12 281355) = some ⟨12, 2, 0, 903684, 281355, 3733, 65536⟩ := by
  decide +kernel

theorem context_12_281355_903684 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281355 ⟨903684, by decide⟩ :=
  accepted_of_selected 12 281355 ⟨903684, by decide⟩ ⟨12, 2, 0, 903684, 281355, 3733, 65536⟩
    (by decide) selected_cut_34653

theorem unmarked_context_11_70338_903685 : frontier 10 ⟨903685, by decide⟩
    (prefixCache 11 70338) (prefixPartial 11 70338) = false := by
  decide +kernel

theorem node_context_11_70338_903685 : EJMOriginalGlobalDAGData.nodes 10 ⟨903685, by decide⟩ =
    .split (coordinate 11) (![⟨903486, by decide⟩,⟨903548, by decide⟩,⟨903615, by decide⟩,⟨903684, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70338_903685 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70338 ⟨903685, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70338
    ⟨903685, by decide⟩ (by decide) (![⟨903486, by decide⟩,⟨903548, by decide⟩,⟨903615, by decide⟩,⟨903684, by decide⟩]) unmarked_context_11_70338_903685 node_context_11_70338_903685
  intro a
  fin_cases a
  · exact context_12_281352_903486
  · exact context_12_281353_903548
  · exact context_12_281354_903615
  · exact context_12_281355_903684

theorem selected_cut_34654 : selected 9 ⟨4596, by decide⟩
    (prefixPartial 12 281356) = some ⟨12, 1, 0, 4596, 281356, 1, 65536⟩ := by
  decide +kernel

theorem context_12_281356_4596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281356 ⟨4596, by decide⟩ :=
  accepted_of_selected 12 281356 ⟨4596, by decide⟩ ⟨12, 1, 0, 4596, 281356, 1, 65536⟩
    (by decide) selected_cut_34654

theorem selected_cut_34655 : selected 9 ⟨903744, by decide⟩
    (prefixPartial 12 281357) = some ⟨12, 2, 0, 903744, 281357, 3293, 65536⟩ := by
  decide +kernel

theorem context_12_281357_903744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281357 ⟨903744, by decide⟩ :=
  accepted_of_selected 12 281357 ⟨903744, by decide⟩ ⟨12, 2, 0, 903744, 281357, 3293, 65536⟩
    (by decide) selected_cut_34655

theorem selected_cut_34656 : selected 9 ⟨903805, by decide⟩
    (prefixPartial 12 281358) = some ⟨12, 2, 0, 903805, 281358, 3729, 65536⟩ := by
  decide +kernel

theorem context_12_281358_903805 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281358 ⟨903805, by decide⟩ :=
  accepted_of_selected 12 281358 ⟨903805, by decide⟩ ⟨12, 2, 0, 903805, 281358, 3729, 65536⟩
    (by decide) selected_cut_34656

theorem selected_cut_34657 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 281359) = some ⟨12, 1, 0, 903806, 281359, 1, 65536⟩ := by
  decide +kernel

theorem context_12_281359_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281359 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 281359 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 281359, 1, 65536⟩
    (by decide) selected_cut_34657

theorem unmarked_context_11_70339_903807 : frontier 10 ⟨903807, by decide⟩
    (prefixCache 11 70339) (prefixPartial 11 70339) = false := by
  decide +kernel

theorem node_context_11_70339_903807 : EJMOriginalGlobalDAGData.nodes 10 ⟨903807, by decide⟩ =
    .split (coordinate 11) (![⟨4596, by decide⟩,⟨903744, by decide⟩,⟨903805, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70339_903807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70339 ⟨903807, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70339
    ⟨903807, by decide⟩ (by decide) (![⟨4596, by decide⟩,⟨903744, by decide⟩,⟨903805, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_70339_903807 node_context_11_70339_903807
  intro a
  fin_cases a
  · exact context_12_281356_4596
  · exact context_12_281357_903744
  · exact context_12_281358_903805
  · exact context_12_281359_903806

theorem unmarked_context_10_17584_903808 : frontier 11 ⟨903808, by decide⟩
    (prefixCache 10 17584) (prefixPartial 10 17584) = false := by
  decide +kernel

theorem node_context_10_17584_903808 : EJMOriginalGlobalDAGData.nodes 11 ⟨903808, by decide⟩ =
    .split (coordinate 10) (![⟨903139, by decide⟩,⟨903414, by decide⟩,⟨903685, by decide⟩,⟨903807, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17584_903808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17584 ⟨903808, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17584
    ⟨903808, by decide⟩ (by decide) (![⟨903139, by decide⟩,⟨903414, by decide⟩,⟨903685, by decide⟩,⟨903807, by decide⟩]) unmarked_context_10_17584_903808 node_context_10_17584_903808
  intro a
  fin_cases a
  · exact context_11_70336_903139
  · exact context_11_70337_903414
  · exact context_11_70338_903685
  · exact context_11_70339_903807

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
