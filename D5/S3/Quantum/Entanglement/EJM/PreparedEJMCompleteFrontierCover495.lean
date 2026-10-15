/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover494
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_10_23346_1330321 : frontier 11 ⟨1330321, by decide⟩
    (prefixCache 10 23346) (prefixPartial 10 23346) = false := by
  decide +kernel

theorem node_context_10_23346_1330321 : EJMOriginalGlobalDAGData.nodes 11 ⟨1330321, by decide⟩ =
    .split (coordinate 10) (![⟨1329950, by decide⟩,⟨1330119, by decide⟩,⟨1330155, by decide⟩,⟨1330320, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23346_1330321 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23346 ⟨1330321, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23346
    ⟨1330321, by decide⟩ (by decide) (![⟨1329950, by decide⟩,⟨1330119, by decide⟩,⟨1330155, by decide⟩,⟨1330320, by decide⟩]) unmarked_context_10_23346_1330321 node_context_10_23346_1330321
  intro a
  fin_cases a
  · exact context_11_93384_1329950
  · exact context_11_93385_1330119
  · exact context_11_93386_1330155
  · exact context_11_93387_1330320

theorem selected_cut_47524 : selected 9 ⟨792260, by decide⟩
    (prefixPartial 12 373552) = some ⟨12, 1, 0, 792260, 373552, 1, 65536⟩ := by
  decide +kernel

theorem context_12_373552_792260 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373552 ⟨792260, by decide⟩ :=
  accepted_of_selected 12 373552 ⟨792260, by decide⟩ ⟨12, 1, 0, 792260, 373552, 1, 65536⟩
    (by decide) selected_cut_47524

theorem selected_cut_47525 : selected 9 ⟨1330358, by decide⟩
    (prefixPartial 12 373553) = some ⟨12, 2, 0, 1330358, 373553, 1933, 65536⟩ := by
  decide +kernel

theorem context_12_373553_1330358 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373553 ⟨1330358, by decide⟩ :=
  accepted_of_selected 12 373553 ⟨1330358, by decide⟩ ⟨12, 2, 0, 1330358, 373553, 1933, 65536⟩
    (by decide) selected_cut_47525

theorem selected_cut_47526 : selected 9 ⟨1330394, by decide⟩
    (prefixPartial 12 373554) = some ⟨12, 2, 0, 1330394, 373554, 1925, 65536⟩ := by
  decide +kernel

theorem context_12_373554_1330394 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373554 ⟨1330394, by decide⟩ :=
  accepted_of_selected 12 373554 ⟨1330394, by decide⟩ ⟨12, 2, 0, 1330394, 373554, 1925, 65536⟩
    (by decide) selected_cut_47526

theorem selected_cut_47527 : selected 9 ⟨1330419, by decide⟩
    (prefixPartial 12 373555) = some ⟨12, 2, 0, 1330419, 373555, 1769, 65536⟩ := by
  decide +kernel

theorem context_12_373555_1330419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373555 ⟨1330419, by decide⟩ :=
  accepted_of_selected 12 373555 ⟨1330419, by decide⟩ ⟨12, 2, 0, 1330419, 373555, 1769, 65536⟩
    (by decide) selected_cut_47527

theorem unmarked_context_11_93388_1330420 : frontier 10 ⟨1330420, by decide⟩
    (prefixCache 11 93388) (prefixPartial 11 93388) = false := by
  decide +kernel

theorem node_context_11_93388_1330420 : EJMOriginalGlobalDAGData.nodes 10 ⟨1330420, by decide⟩ =
    .split (coordinate 11) (![⟨792260, by decide⟩,⟨1330358, by decide⟩,⟨1330394, by decide⟩,⟨1330419, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93388_1330420 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93388 ⟨1330420, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93388
    ⟨1330420, by decide⟩ (by decide) (![⟨792260, by decide⟩,⟨1330358, by decide⟩,⟨1330394, by decide⟩,⟨1330419, by decide⟩]) unmarked_context_11_93388_1330420 node_context_11_93388_1330420
  intro a
  fin_cases a
  · exact context_12_373552_792260
  · exact context_12_373553_1330358
  · exact context_12_373554_1330394
  · exact context_12_373555_1330419

theorem selected_cut_47528 : selected 9 ⟨1330469, by decide⟩
    (prefixPartial 12 373556) = some ⟨12, 2, 0, 1330469, 373556, 2601, 65536⟩ := by
  decide +kernel

theorem context_12_373556_1330469 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373556 ⟨1330469, by decide⟩ :=
  accepted_of_selected 12 373556 ⟨1330469, by decide⟩ ⟨12, 2, 0, 1330469, 373556, 2601, 65536⟩
    (by decide) selected_cut_47528

theorem selected_cut_47529 : selected 9 ⟨410616, by decide⟩
    (prefixPartial 12 373557) = some ⟨12, 1, 0, 410616, 373557, 1, 65536⟩ := by
  decide +kernel

theorem context_12_373557_410616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373557 ⟨410616, by decide⟩ :=
  accepted_of_selected 12 373557 ⟨410616, by decide⟩ ⟨12, 1, 0, 410616, 373557, 1, 65536⟩
    (by decide) selected_cut_47529

theorem selected_cut_47530 : selected 9 ⟨1330517, by decide⟩
    (prefixPartial 12 373558) = some ⟨12, 2, 0, 1330517, 373558, 2433, 65536⟩ := by
  decide +kernel

theorem context_12_373558_1330517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373558 ⟨1330517, by decide⟩ :=
  accepted_of_selected 12 373558 ⟨1330517, by decide⟩ ⟨12, 2, 0, 1330517, 373558, 2433, 65536⟩
    (by decide) selected_cut_47530

theorem selected_cut_47531 : selected 9 ⟨1330558, by decide⟩
    (prefixPartial 12 373559) = some ⟨12, 2, 0, 1330558, 373559, 2185, 65536⟩ := by
  decide +kernel

theorem context_12_373559_1330558 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373559 ⟨1330558, by decide⟩ :=
  accepted_of_selected 12 373559 ⟨1330558, by decide⟩ ⟨12, 2, 0, 1330558, 373559, 2185, 65536⟩
    (by decide) selected_cut_47531

theorem unmarked_context_11_93389_1330559 : frontier 10 ⟨1330559, by decide⟩
    (prefixCache 11 93389) (prefixPartial 11 93389) = false := by
  decide +kernel

theorem node_context_11_93389_1330559 : EJMOriginalGlobalDAGData.nodes 10 ⟨1330559, by decide⟩ =
    .split (coordinate 11) (![⟨1330469, by decide⟩,⟨410616, by decide⟩,⟨1330517, by decide⟩,⟨1330558, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93389_1330559 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93389 ⟨1330559, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93389
    ⟨1330559, by decide⟩ (by decide) (![⟨1330469, by decide⟩,⟨410616, by decide⟩,⟨1330517, by decide⟩,⟨1330558, by decide⟩]) unmarked_context_11_93389_1330559 node_context_11_93389_1330559
  intro a
  fin_cases a
  · exact context_12_373556_1330469
  · exact context_12_373557_410616
  · exact context_12_373558_1330517
  · exact context_12_373559_1330558

theorem selected_cut_47532 : selected 9 ⟨1082322, by decide⟩
    (prefixPartial 12 373560) = some ⟨12, 1, 0, 1082322, 373560, 1, 65536⟩ := by
  decide +kernel

theorem context_12_373560_1082322 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373560 ⟨1082322, by decide⟩ :=
  accepted_of_selected 12 373560 ⟨1082322, by decide⟩ ⟨12, 1, 0, 1082322, 373560, 1, 65536⟩
    (by decide) selected_cut_47532

theorem selected_cut_47533 : selected 9 ⟨1330607, by decide⟩
    (prefixPartial 12 373561) = some ⟨12, 2, 0, 1330607, 373561, 2181, 65536⟩ := by
  decide +kernel

theorem context_12_373561_1330607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373561 ⟨1330607, by decide⟩ :=
  accepted_of_selected 12 373561 ⟨1330607, by decide⟩ ⟨12, 2, 0, 1330607, 373561, 2181, 65536⟩
    (by decide) selected_cut_47533

theorem selected_cut_47534 : selected 9 ⟨421425, by decide⟩
    (prefixPartial 12 373562) = some ⟨12, 1, 0, 421425, 373562, 1, 65536⟩ := by
  decide +kernel

theorem context_12_373562_421425 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373562 ⟨421425, by decide⟩ :=
  accepted_of_selected 12 373562 ⟨421425, by decide⟩ ⟨12, 1, 0, 421425, 373562, 1, 65536⟩
    (by decide) selected_cut_47534

theorem selected_cut_47535 : selected 9 ⟨1330649, by decide⟩
    (prefixPartial 12 373563) = some ⟨12, 2, 0, 1330649, 373563, 1993, 65536⟩ := by
  decide +kernel

theorem context_12_373563_1330649 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373563 ⟨1330649, by decide⟩ :=
  accepted_of_selected 12 373563 ⟨1330649, by decide⟩ ⟨12, 2, 0, 1330649, 373563, 1993, 65536⟩
    (by decide) selected_cut_47535

theorem unmarked_context_11_93390_1330650 : frontier 10 ⟨1330650, by decide⟩
    (prefixCache 11 93390) (prefixPartial 11 93390) = false := by
  decide +kernel

theorem node_context_11_93390_1330650 : EJMOriginalGlobalDAGData.nodes 10 ⟨1330650, by decide⟩ =
    .split (coordinate 11) (![⟨1082322, by decide⟩,⟨1330607, by decide⟩,⟨421425, by decide⟩,⟨1330649, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93390_1330650 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93390 ⟨1330650, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93390
    ⟨1330650, by decide⟩ (by decide) (![⟨1082322, by decide⟩,⟨1330607, by decide⟩,⟨421425, by decide⟩,⟨1330649, by decide⟩]) unmarked_context_11_93390_1330650 node_context_11_93390_1330650
  intro a
  fin_cases a
  · exact context_12_373560_1082322
  · exact context_12_373561_1330607
  · exact context_12_373562_421425
  · exact context_12_373563_1330649

theorem selected_cut_47536 : selected 10 ⟨1330710, by decide⟩
    (prefixPartial 11 93391) = some ⟨11, 2, 0, 1330710, 93391, 1657, 262144⟩ := by
  decide +kernel

theorem context_11_93391_1330710 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93391 ⟨1330710, by decide⟩ :=
  accepted_of_selected 11 93391 ⟨1330710, by decide⟩ ⟨11, 2, 0, 1330710, 93391, 1657, 262144⟩
    (by decide) selected_cut_47536

theorem unmarked_context_10_23347_1330711 : frontier 11 ⟨1330711, by decide⟩
    (prefixCache 10 23347) (prefixPartial 10 23347) = false := by
  decide +kernel

theorem node_context_10_23347_1330711 : EJMOriginalGlobalDAGData.nodes 11 ⟨1330711, by decide⟩ =
    .split (coordinate 10) (![⟨1330420, by decide⟩,⟨1330559, by decide⟩,⟨1330650, by decide⟩,⟨1330710, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23347_1330711 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23347 ⟨1330711, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23347
    ⟨1330711, by decide⟩ (by decide) (![⟨1330420, by decide⟩,⟨1330559, by decide⟩,⟨1330650, by decide⟩,⟨1330710, by decide⟩]) unmarked_context_10_23347_1330711 node_context_10_23347_1330711
  intro a
  fin_cases a
  · exact context_11_93388_1330420
  · exact context_11_93389_1330559
  · exact context_11_93390_1330650
  · exact context_11_93391_1330710

theorem unmarked_context_9_5836_1330712 : frontier 12 ⟨1330712, by decide⟩
    (prefixCache 9 5836) (prefixPartial 9 5836) = false := by
  decide +kernel

theorem node_context_9_5836_1330712 : EJMOriginalGlobalDAGData.nodes 12 ⟨1330712, by decide⟩ =
    .split (coordinate 9) (![⟨1329357, by decide⟩,⟨1329835, by decide⟩,⟨1330321, by decide⟩,⟨1330711, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5836_1330712 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5836 ⟨1330712, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5836
    ⟨1330712, by decide⟩ (by decide) (![⟨1329357, by decide⟩,⟨1329835, by decide⟩,⟨1330321, by decide⟩,⟨1330711, by decide⟩]) unmarked_context_9_5836_1330712 node_context_9_5836_1330712
  intro a
  fin_cases a
  · exact context_10_23344_1329357
  · exact context_10_23345_1329835
  · exact context_10_23346_1330321
  · exact context_10_23347_1330711

theorem selected_cut_47537 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 93392) = some ⟨11, 1, 0, 907917, 93392, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93392_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93392 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 93392 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 93392, 1, 262144⟩
    (by decide) selected_cut_47537

theorem selected_cut_47538 : selected 9 ⟨1330755, by decide⟩
    (prefixPartial 12 373572) = some ⟨12, 2, 0, 1330755, 373572, 2225, 65536⟩ := by
  decide +kernel

theorem context_12_373572_1330755 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373572 ⟨1330755, by decide⟩ :=
  accepted_of_selected 12 373572 ⟨1330755, by decide⟩ ⟨12, 2, 0, 1330755, 373572, 2225, 65536⟩
    (by decide) selected_cut_47538

theorem selected_cut_47539 : selected 9 ⟨1257136, by decide⟩
    (prefixPartial 12 373573) = some ⟨12, 1, 0, 1257136, 373573, 1, 65536⟩ := by
  decide +kernel

theorem context_12_373573_1257136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373573 ⟨1257136, by decide⟩ :=
  accepted_of_selected 12 373573 ⟨1257136, by decide⟩ ⟨12, 1, 0, 1257136, 373573, 1, 65536⟩
    (by decide) selected_cut_47539

theorem selected_cut_47540 : selected 9 ⟨1330788, by decide⟩
    (prefixPartial 12 373574) = some ⟨12, 2, 0, 1330788, 373574, 1989, 65536⟩ := by
  decide +kernel

theorem context_12_373574_1330788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373574 ⟨1330788, by decide⟩ :=
  accepted_of_selected 12 373574 ⟨1330788, by decide⟩ ⟨12, 2, 0, 1330788, 373574, 1989, 65536⟩
    (by decide) selected_cut_47540

theorem selected_cut_47541 : selected 9 ⟨1330822, by decide⟩
    (prefixPartial 12 373575) = some ⟨12, 2, 0, 1330822, 373575, 1853, 65536⟩ := by
  decide +kernel

theorem context_12_373575_1330822 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373575 ⟨1330822, by decide⟩ :=
  accepted_of_selected 12 373575 ⟨1330822, by decide⟩ ⟨12, 2, 0, 1330822, 373575, 1853, 65536⟩
    (by decide) selected_cut_47541

theorem unmarked_context_11_93393_1330823 : frontier 10 ⟨1330823, by decide⟩
    (prefixCache 11 93393) (prefixPartial 11 93393) = false := by
  decide +kernel

theorem node_context_11_93393_1330823 : EJMOriginalGlobalDAGData.nodes 10 ⟨1330823, by decide⟩ =
    .split (coordinate 11) (![⟨1330755, by decide⟩,⟨1257136, by decide⟩,⟨1330788, by decide⟩,⟨1330822, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93393_1330823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93393 ⟨1330823, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93393
    ⟨1330823, by decide⟩ (by decide) (![⟨1330755, by decide⟩,⟨1257136, by decide⟩,⟨1330788, by decide⟩,⟨1330822, by decide⟩]) unmarked_context_11_93393_1330823 node_context_11_93393_1330823
  intro a
  fin_cases a
  · exact context_12_373572_1330755
  · exact context_12_373573_1257136
  · exact context_12_373574_1330788
  · exact context_12_373575_1330822

theorem selected_cut_47542 : selected 9 ⟨1330863, by decide⟩
    (prefixPartial 12 373576) = some ⟨12, 2, 0, 1330863, 373576, 2001, 65536⟩ := by
  decide +kernel

theorem context_12_373576_1330863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373576 ⟨1330863, by decide⟩ :=
  accepted_of_selected 12 373576 ⟨1330863, by decide⟩ ⟨12, 2, 0, 1330863, 373576, 2001, 65536⟩
    (by decide) selected_cut_47542

theorem selected_cut_47543 : selected 9 ⟨753187, by decide⟩
    (prefixPartial 12 373577) = some ⟨12, 1, 0, 753187, 373577, 1, 65536⟩ := by
  decide +kernel

theorem context_12_373577_753187 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373577 ⟨753187, by decide⟩ :=
  accepted_of_selected 12 373577 ⟨753187, by decide⟩ ⟨12, 1, 0, 753187, 373577, 1, 65536⟩
    (by decide) selected_cut_47543

theorem selected_cut_47544 : selected 9 ⟨1330896, by decide⟩
    (prefixPartial 12 373578) = some ⟨12, 2, 0, 1330896, 373578, 1761, 65536⟩ := by
  decide +kernel

theorem context_12_373578_1330896 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373578 ⟨1330896, by decide⟩ :=
  accepted_of_selected 12 373578 ⟨1330896, by decide⟩ ⟨12, 2, 0, 1330896, 373578, 1761, 65536⟩
    (by decide) selected_cut_47544

theorem selected_cut_47545 : selected 9 ⟨1330924, by decide⟩
    (prefixPartial 12 373579) = some ⟨12, 2, 0, 1330924, 373579, 1765, 65536⟩ := by
  decide +kernel

theorem context_12_373579_1330924 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373579 ⟨1330924, by decide⟩ :=
  accepted_of_selected 12 373579 ⟨1330924, by decide⟩ ⟨12, 2, 0, 1330924, 373579, 1765, 65536⟩
    (by decide) selected_cut_47545

theorem unmarked_context_11_93394_1330925 : frontier 10 ⟨1330925, by decide⟩
    (prefixCache 11 93394) (prefixPartial 11 93394) = false := by
  decide +kernel

theorem node_context_11_93394_1330925 : EJMOriginalGlobalDAGData.nodes 10 ⟨1330925, by decide⟩ =
    .split (coordinate 11) (![⟨1330863, by decide⟩,⟨753187, by decide⟩,⟨1330896, by decide⟩,⟨1330924, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93394_1330925 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93394 ⟨1330925, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93394
    ⟨1330925, by decide⟩ (by decide) (![⟨1330863, by decide⟩,⟨753187, by decide⟩,⟨1330896, by decide⟩,⟨1330924, by decide⟩]) unmarked_context_11_93394_1330925 node_context_11_93394_1330925
  intro a
  fin_cases a
  · exact context_12_373576_1330863
  · exact context_12_373577_753187
  · exact context_12_373578_1330896
  · exact context_12_373579_1330924

theorem selected_cut_47546 : selected 9 ⟨1330963, by decide⟩
    (prefixPartial 12 373580) = some ⟨12, 2, 0, 1330963, 373580, 1865, 65536⟩ := by
  decide +kernel

theorem context_12_373580_1330963 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373580 ⟨1330963, by decide⟩ :=
  accepted_of_selected 12 373580 ⟨1330963, by decide⟩ ⟨12, 2, 0, 1330963, 373580, 1865, 65536⟩
    (by decide) selected_cut_47546

theorem selected_cut_47547 : selected 9 ⟨1331000, by decide⟩
    (prefixPartial 12 373581) = some ⟨12, 2, 0, 1331000, 373581, 1817, 65536⟩ := by
  decide +kernel

theorem context_12_373581_1331000 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373581 ⟨1331000, by decide⟩ :=
  accepted_of_selected 12 373581 ⟨1331000, by decide⟩ ⟨12, 2, 0, 1331000, 373581, 1817, 65536⟩
    (by decide) selected_cut_47547

theorem selected_cut_47548 : selected 9 ⟨1331035, by decide⟩
    (prefixPartial 12 373582) = some ⟨12, 2, 0, 1331035, 373582, 1753, 65536⟩ := by
  decide +kernel

theorem context_12_373582_1331035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373582 ⟨1331035, by decide⟩ :=
  accepted_of_selected 12 373582 ⟨1331035, by decide⟩ ⟨12, 2, 0, 1331035, 373582, 1753, 65536⟩
    (by decide) selected_cut_47548

theorem selected_cut_47549 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 373583) = some ⟨12, 1, 0, 903806, 373583, 1, 65536⟩ := by
  decide +kernel

theorem context_12_373583_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373583 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 373583 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 373583, 1, 65536⟩
    (by decide) selected_cut_47549

theorem unmarked_context_11_93395_1331036 : frontier 10 ⟨1331036, by decide⟩
    (prefixCache 11 93395) (prefixPartial 11 93395) = false := by
  decide +kernel

theorem node_context_11_93395_1331036 : EJMOriginalGlobalDAGData.nodes 10 ⟨1331036, by decide⟩ =
    .split (coordinate 11) (![⟨1330963, by decide⟩,⟨1331000, by decide⟩,⟨1331035, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93395_1331036 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93395 ⟨1331036, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93395
    ⟨1331036, by decide⟩ (by decide) (![⟨1330963, by decide⟩,⟨1331000, by decide⟩,⟨1331035, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_93395_1331036 node_context_11_93395_1331036
  intro a
  fin_cases a
  · exact context_12_373580_1330963
  · exact context_12_373581_1331000
  · exact context_12_373582_1331035
  · exact context_12_373583_903806

theorem unmarked_context_10_23348_1331037 : frontier 11 ⟨1331037, by decide⟩
    (prefixCache 10 23348) (prefixPartial 10 23348) = false := by
  decide +kernel

theorem node_context_10_23348_1331037 : EJMOriginalGlobalDAGData.nodes 11 ⟨1331037, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨1330823, by decide⟩,⟨1330925, by decide⟩,⟨1331036, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23348_1331037 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23348 ⟨1331037, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23348
    ⟨1331037, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨1330823, by decide⟩,⟨1330925, by decide⟩,⟨1331036, by decide⟩]) unmarked_context_10_23348_1331037 node_context_10_23348_1331037
  intro a
  fin_cases a
  · exact context_11_93392_907917
  · exact context_11_93393_1330823
  · exact context_11_93394_1330925
  · exact context_11_93395_1331036

theorem selected_cut_47550 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 23349) = some ⟨10, 1, 0, 893098, 23349, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_23349_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23349 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 23349 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 23349, 1, 1048576⟩
    (by decide) selected_cut_47550

theorem selected_cut_47551 : selected 10 ⟨1331101, by decide⟩
    (prefixPartial 11 93400) = some ⟨11, 2, 0, 1331101, 93400, 4073, 262144⟩ := by
  decide +kernel

theorem context_11_93400_1331101 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93400 ⟨1331101, by decide⟩ :=
  accepted_of_selected 11 93400 ⟨1331101, by decide⟩ ⟨11, 2, 0, 1331101, 93400, 4073, 262144⟩
    (by decide) selected_cut_47551

theorem selected_cut_47552 : selected 9 ⟨1331132, by decide⟩
    (prefixPartial 12 373604) = some ⟨12, 2, 0, 1331132, 373604, 1757, 65536⟩ := by
  decide +kernel

theorem context_12_373604_1331132 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373604 ⟨1331132, by decide⟩ :=
  accepted_of_selected 12 373604 ⟨1331132, by decide⟩ ⟨12, 2, 0, 1331132, 373604, 1757, 65536⟩
    (by decide) selected_cut_47552

theorem selected_cut_47553 : selected 9 ⟨1256866, by decide⟩
    (prefixPartial 12 373605) = some ⟨12, 1, 0, 1256866, 373605, 1, 65536⟩ := by
  decide +kernel

theorem context_12_373605_1256866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373605 ⟨1256866, by decide⟩ :=
  accepted_of_selected 12 373605 ⟨1256866, by decide⟩ ⟨12, 1, 0, 1256866, 373605, 1, 65536⟩
    (by decide) selected_cut_47553

theorem selected_cut_47554 : selected 9 ⟨1331159, by decide⟩
    (prefixPartial 12 373606) = some ⟨12, 2, 0, 1331159, 373606, 1645, 65536⟩ := by
  decide +kernel

theorem context_12_373606_1331159 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373606 ⟨1331159, by decide⟩ :=
  accepted_of_selected 12 373606 ⟨1331159, by decide⟩ ⟨12, 2, 0, 1331159, 373606, 1645, 65536⟩
    (by decide) selected_cut_47554

theorem selected_cut_47555 : selected 9 ⟨1331185, by decide⟩
    (prefixPartial 12 373607) = some ⟨12, 2, 0, 1331185, 373607, 1489, 65536⟩ := by
  decide +kernel

theorem context_12_373607_1331185 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373607 ⟨1331185, by decide⟩ :=
  accepted_of_selected 12 373607 ⟨1331185, by decide⟩ ⟨12, 2, 0, 1331185, 373607, 1489, 65536⟩
    (by decide) selected_cut_47555

theorem unmarked_context_11_93401_1331186 : frontier 10 ⟨1331186, by decide⟩
    (prefixCache 11 93401) (prefixPartial 11 93401) = false := by
  decide +kernel

theorem node_context_11_93401_1331186 : EJMOriginalGlobalDAGData.nodes 10 ⟨1331186, by decide⟩ =
    .split (coordinate 11) (![⟨1331132, by decide⟩,⟨1256866, by decide⟩,⟨1331159, by decide⟩,⟨1331185, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93401_1331186 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93401 ⟨1331186, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93401
    ⟨1331186, by decide⟩ (by decide) (![⟨1331132, by decide⟩,⟨1256866, by decide⟩,⟨1331159, by decide⟩,⟨1331185, by decide⟩]) unmarked_context_11_93401_1331186 node_context_11_93401_1331186
  intro a
  fin_cases a
  · exact context_12_373604_1331132
  · exact context_12_373605_1256866
  · exact context_12_373606_1331159
  · exact context_12_373607_1331185

theorem selected_cut_47556 : selected 10 ⟨1331240, by decide⟩
    (prefixPartial 11 93402) = some ⟨11, 2, 0, 1331240, 93402, 2749, 262144⟩ := by
  decide +kernel

theorem context_11_93402_1331240 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93402 ⟨1331240, by decide⟩ :=
  accepted_of_selected 11 93402 ⟨1331240, by decide⟩ ⟨11, 2, 0, 1331240, 93402, 2749, 262144⟩
    (by decide) selected_cut_47556

theorem selected_cut_47557 : selected 10 ⟨1331296, by decide⟩
    (prefixPartial 11 93403) = some ⟨11, 2, 0, 1331296, 93403, 2853, 262144⟩ := by
  decide +kernel

theorem context_11_93403_1331296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93403 ⟨1331296, by decide⟩ :=
  accepted_of_selected 11 93403 ⟨1331296, by decide⟩ ⟨11, 2, 0, 1331296, 93403, 2853, 262144⟩
    (by decide) selected_cut_47557

theorem unmarked_context_10_23350_1331297 : frontier 11 ⟨1331297, by decide⟩
    (prefixCache 10 23350) (prefixPartial 10 23350) = false := by
  decide +kernel

theorem node_context_10_23350_1331297 : EJMOriginalGlobalDAGData.nodes 11 ⟨1331297, by decide⟩ =
    .split (coordinate 10) (![⟨1331101, by decide⟩,⟨1331186, by decide⟩,⟨1331240, by decide⟩,⟨1331296, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23350_1331297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23350 ⟨1331297, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23350
    ⟨1331297, by decide⟩ (by decide) (![⟨1331101, by decide⟩,⟨1331186, by decide⟩,⟨1331240, by decide⟩,⟨1331296, by decide⟩]) unmarked_context_10_23350_1331297 node_context_10_23350_1331297
  intro a
  fin_cases a
  · exact context_11_93400_1331101
  · exact context_11_93401_1331186
  · exact context_11_93402_1331240
  · exact context_11_93403_1331296

theorem selected_cut_47558 : selected 10 ⟨1331360, by decide⟩
    (prefixPartial 11 93404) = some ⟨11, 2, 0, 1331360, 93404, 3477, 262144⟩ := by
  decide +kernel

theorem context_11_93404_1331360 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93404 ⟨1331360, by decide⟩ :=
  accepted_of_selected 11 93404 ⟨1331360, by decide⟩ ⟨11, 2, 0, 1331360, 93404, 3477, 262144⟩
    (by decide) selected_cut_47558

theorem selected_cut_47559 : selected 9 ⟨1331387, by decide⟩
    (prefixPartial 12 373620) = some ⟨12, 2, 0, 1331387, 373620, 1489, 65536⟩ := by
  decide +kernel

theorem context_12_373620_1331387 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373620 ⟨1331387, by decide⟩ :=
  accepted_of_selected 12 373620 ⟨1331387, by decide⟩ ⟨12, 2, 0, 1331387, 373620, 1489, 65536⟩
    (by decide) selected_cut_47559

theorem selected_cut_47560 : selected 9 ⟨410616, by decide⟩
    (prefixPartial 12 373621) = some ⟨12, 1, 0, 410616, 373621, 1, 65536⟩ := by
  decide +kernel

theorem context_12_373621_410616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373621 ⟨410616, by decide⟩ :=
  accepted_of_selected 12 373621 ⟨410616, by decide⟩ ⟨12, 1, 0, 410616, 373621, 1, 65536⟩
    (by decide) selected_cut_47560

theorem selected_cut_47561 : selected 9 ⟨1331411, by decide⟩
    (prefixPartial 12 373622) = some ⟨12, 2, 0, 1331411, 373622, 1365, 65536⟩ := by
  decide +kernel

theorem context_12_373622_1331411 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373622 ⟨1331411, by decide⟩ :=
  accepted_of_selected 12 373622 ⟨1331411, by decide⟩ ⟨12, 2, 0, 1331411, 373622, 1365, 65536⟩
    (by decide) selected_cut_47561

theorem selected_cut_47562 : selected 9 ⟨1331434, by decide⟩
    (prefixPartial 12 373623) = some ⟨12, 2, 0, 1331434, 373623, 1241, 65536⟩ := by
  decide +kernel

theorem context_12_373623_1331434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373623 ⟨1331434, by decide⟩ :=
  accepted_of_selected 12 373623 ⟨1331434, by decide⟩ ⟨12, 2, 0, 1331434, 373623, 1241, 65536⟩
    (by decide) selected_cut_47562

theorem unmarked_context_11_93405_1331435 : frontier 10 ⟨1331435, by decide⟩
    (prefixCache 11 93405) (prefixPartial 11 93405) = false := by
  decide +kernel

theorem node_context_11_93405_1331435 : EJMOriginalGlobalDAGData.nodes 10 ⟨1331435, by decide⟩ =
    .split (coordinate 11) (![⟨1331387, by decide⟩,⟨410616, by decide⟩,⟨1331411, by decide⟩,⟨1331434, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93405_1331435 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93405 ⟨1331435, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93405
    ⟨1331435, by decide⟩ (by decide) (![⟨1331387, by decide⟩,⟨410616, by decide⟩,⟨1331411, by decide⟩,⟨1331434, by decide⟩]) unmarked_context_11_93405_1331435 node_context_11_93405_1331435
  intro a
  fin_cases a
  · exact context_12_373620_1331387
  · exact context_12_373621_410616
  · exact context_12_373622_1331411
  · exact context_12_373623_1331434

theorem selected_cut_47563 : selected 10 ⟨1331525, by decide⟩
    (prefixPartial 11 93406) = some ⟨11, 2, 0, 1331525, 93406, 2817, 262144⟩ := by
  decide +kernel

theorem context_11_93406_1331525 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93406 ⟨1331525, by decide⟩ :=
  accepted_of_selected 11 93406 ⟨1331525, by decide⟩ ⟨11, 2, 0, 1331525, 93406, 2817, 262144⟩
    (by decide) selected_cut_47563

theorem selected_cut_47564 : selected 10 ⟨1331566, by decide⟩
    (prefixPartial 11 93407) = some ⟨11, 2, 0, 1331566, 93407, 2149, 262144⟩ := by
  decide +kernel

theorem context_11_93407_1331566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93407 ⟨1331566, by decide⟩ :=
  accepted_of_selected 11 93407 ⟨1331566, by decide⟩ ⟨11, 2, 0, 1331566, 93407, 2149, 262144⟩
    (by decide) selected_cut_47564

theorem unmarked_context_10_23351_1331567 : frontier 11 ⟨1331567, by decide⟩
    (prefixCache 10 23351) (prefixPartial 10 23351) = false := by
  decide +kernel

theorem node_context_10_23351_1331567 : EJMOriginalGlobalDAGData.nodes 11 ⟨1331567, by decide⟩ =
    .split (coordinate 10) (![⟨1331360, by decide⟩,⟨1331435, by decide⟩,⟨1331525, by decide⟩,⟨1331566, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23351_1331567 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23351 ⟨1331567, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23351
    ⟨1331567, by decide⟩ (by decide) (![⟨1331360, by decide⟩,⟨1331435, by decide⟩,⟨1331525, by decide⟩,⟨1331566, by decide⟩]) unmarked_context_10_23351_1331567 node_context_10_23351_1331567
  intro a
  fin_cases a
  · exact context_11_93404_1331360
  · exact context_11_93405_1331435
  · exact context_11_93406_1331525
  · exact context_11_93407_1331566

theorem unmarked_context_9_5837_1331568 : frontier 12 ⟨1331568, by decide⟩
    (prefixCache 9 5837) (prefixPartial 9 5837) = false := by
  decide +kernel

theorem node_context_9_5837_1331568 : EJMOriginalGlobalDAGData.nodes 12 ⟨1331568, by decide⟩ =
    .split (coordinate 9) (![⟨1331037, by decide⟩,⟨893098, by decide⟩,⟨1331297, by decide⟩,⟨1331567, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5837_1331568 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5837 ⟨1331568, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5837
    ⟨1331568, by decide⟩ (by decide) (![⟨1331037, by decide⟩,⟨893098, by decide⟩,⟨1331297, by decide⟩,⟨1331567, by decide⟩]) unmarked_context_9_5837_1331568 node_context_9_5837_1331568
  intro a
  fin_cases a
  · exact context_10_23348_1331037
  · exact context_10_23349_893098
  · exact context_10_23350_1331297
  · exact context_10_23351_1331567

theorem selected_cut_47565 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 93408) = some ⟨11, 1, 0, 907917, 93408, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93408_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93408 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 93408 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 93408, 1, 262144⟩
    (by decide) selected_cut_47565

theorem selected_cut_47566 : selected 10 ⟨1331620, by decide⟩
    (prefixPartial 11 93409) = some ⟨11, 2, 0, 1331620, 93409, 2865, 262144⟩ := by
  decide +kernel

theorem context_11_93409_1331620 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93409 ⟨1331620, by decide⟩ :=
  accepted_of_selected 11 93409 ⟨1331620, by decide⟩ ⟨11, 2, 0, 1331620, 93409, 2865, 262144⟩
    (by decide) selected_cut_47566

theorem selected_cut_47567 : selected 10 ⟨1331671, by decide⟩
    (prefixPartial 11 93410) = some ⟨11, 2, 0, 1331671, 93410, 2761, 262144⟩ := by
  decide +kernel

theorem context_11_93410_1331671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93410 ⟨1331671, by decide⟩ :=
  accepted_of_selected 11 93410 ⟨1331671, by decide⟩ ⟨11, 2, 0, 1331671, 93410, 2761, 262144⟩
    (by decide) selected_cut_47567

theorem selected_cut_47568 : selected 10 ⟨1331703, by decide⟩
    (prefixPartial 11 93411) = some ⟨11, 2, 0, 1331703, 93411, 1685, 262144⟩ := by
  decide +kernel

theorem context_11_93411_1331703 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93411 ⟨1331703, by decide⟩ :=
  accepted_of_selected 11 93411 ⟨1331703, by decide⟩ ⟨11, 2, 0, 1331703, 93411, 1685, 262144⟩
    (by decide) selected_cut_47568

theorem unmarked_context_10_23352_1331704 : frontier 11 ⟨1331704, by decide⟩
    (prefixCache 10 23352) (prefixPartial 10 23352) = false := by
  decide +kernel

theorem node_context_10_23352_1331704 : EJMOriginalGlobalDAGData.nodes 11 ⟨1331704, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨1331620, by decide⟩,⟨1331671, by decide⟩,⟨1331703, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23352_1331704 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23352 ⟨1331704, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23352
    ⟨1331704, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨1331620, by decide⟩,⟨1331671, by decide⟩,⟨1331703, by decide⟩]) unmarked_context_10_23352_1331704 node_context_10_23352_1331704
  intro a
  fin_cases a
  · exact context_11_93408_907917
  · exact context_11_93409_1331620
  · exact context_11_93410_1331671
  · exact context_11_93411_1331703

theorem selected_cut_47569 : selected 10 ⟨1331742, by decide⟩
    (prefixPartial 11 93412) = some ⟨11, 2, 0, 1331742, 93412, 2225, 262144⟩ := by
  decide +kernel

theorem context_11_93412_1331742 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93412 ⟨1331742, by decide⟩ :=
  accepted_of_selected 11 93412 ⟨1331742, by decide⟩ ⟨11, 2, 0, 1331742, 93412, 2225, 262144⟩
    (by decide) selected_cut_47569

theorem selected_cut_47570 : selected 10 ⟨1331774, by decide⟩
    (prefixPartial 11 93413) = some ⟨11, 2, 0, 1331774, 93413, 973, 262144⟩ := by
  decide +kernel

theorem context_11_93413_1331774 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93413 ⟨1331774, by decide⟩ :=
  accepted_of_selected 11 93413 ⟨1331774, by decide⟩ ⟨11, 2, 0, 1331774, 93413, 973, 262144⟩
    (by decide) selected_cut_47570

theorem selected_cut_47571 : selected 10 ⟨1331811, by decide⟩
    (prefixPartial 11 93414) = some ⟨11, 2, 0, 1331811, 93414, 2125, 262144⟩ := by
  decide +kernel

theorem context_11_93414_1331811 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93414 ⟨1331811, by decide⟩ :=
  accepted_of_selected 11 93414 ⟨1331811, by decide⟩ ⟨11, 2, 0, 1331811, 93414, 2125, 262144⟩
    (by decide) selected_cut_47571

theorem selected_cut_47572 : selected 10 ⟨1331832, by decide⟩
    (prefixPartial 11 93415) = some ⟨11, 2, 0, 1331832, 93415, 1277, 262144⟩ := by
  decide +kernel

theorem context_11_93415_1331832 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93415 ⟨1331832, by decide⟩ :=
  accepted_of_selected 11 93415 ⟨1331832, by decide⟩ ⟨11, 2, 0, 1331832, 93415, 1277, 262144⟩
    (by decide) selected_cut_47572

theorem unmarked_context_10_23353_1331833 : frontier 11 ⟨1331833, by decide⟩
    (prefixCache 10 23353) (prefixPartial 10 23353) = false := by
  decide +kernel

theorem node_context_10_23353_1331833 : EJMOriginalGlobalDAGData.nodes 11 ⟨1331833, by decide⟩ =
    .split (coordinate 10) (![⟨1331742, by decide⟩,⟨1331774, by decide⟩,⟨1331811, by decide⟩,⟨1331832, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23353_1331833 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23353 ⟨1331833, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23353
    ⟨1331833, by decide⟩ (by decide) (![⟨1331742, by decide⟩,⟨1331774, by decide⟩,⟨1331811, by decide⟩,⟨1331832, by decide⟩]) unmarked_context_10_23353_1331833 node_context_10_23353_1331833
  intro a
  fin_cases a
  · exact context_11_93412_1331742
  · exact context_11_93413_1331774
  · exact context_11_93414_1331811
  · exact context_11_93415_1331832

theorem selected_cut_47573 : selected 11 ⟨1331870, by decide⟩
    (prefixPartial 10 23354) = some ⟨10, 2, 0, 1331870, 23354, 1869, 1048576⟩ := by
  decide +kernel

theorem context_10_23354_1331870 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23354 ⟨1331870, by decide⟩ :=
  accepted_of_selected 10 23354 ⟨1331870, by decide⟩ ⟨10, 2, 0, 1331870, 23354, 1869, 1048576⟩
    (by decide) selected_cut_47573

theorem selected_cut_47574 : selected 10 ⟨1331888, by decide⟩
    (prefixPartial 11 93420) = some ⟨11, 2, 0, 1331888, 93420, 1065, 262144⟩ := by
  decide +kernel

theorem context_11_93420_1331888 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93420 ⟨1331888, by decide⟩ :=
  accepted_of_selected 11 93420 ⟨1331888, by decide⟩ ⟨11, 2, 0, 1331888, 93420, 1065, 262144⟩
    (by decide) selected_cut_47574

theorem selected_cut_47575 : selected 10 ⟨1331914, by decide⟩
    (prefixPartial 11 93421) = some ⟨11, 2, 0, 1331914, 93421, 1561, 262144⟩ := by
  decide +kernel

theorem context_11_93421_1331914 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93421 ⟨1331914, by decide⟩ :=
  accepted_of_selected 11 93421 ⟨1331914, by decide⟩ ⟨11, 2, 0, 1331914, 93421, 1561, 262144⟩
    (by decide) selected_cut_47575

theorem selected_cut_47576 : selected 10 ⟨1331943, by decide⟩
    (prefixPartial 11 93422) = some ⟨11, 2, 0, 1331943, 93422, 1417, 262144⟩ := by
  decide +kernel

theorem context_11_93422_1331943 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93422 ⟨1331943, by decide⟩ :=
  accepted_of_selected 11 93422 ⟨1331943, by decide⟩ ⟨11, 2, 0, 1331943, 93422, 1417, 262144⟩
    (by decide) selected_cut_47576

theorem selected_cut_47577 : selected 10 ⟨1331950, by decide⟩
    (prefixPartial 11 93423) = some ⟨11, 2, 0, 1331950, 93423, 461, 262144⟩ := by
  decide +kernel

theorem context_11_93423_1331950 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93423 ⟨1331950, by decide⟩ :=
  accepted_of_selected 11 93423 ⟨1331950, by decide⟩ ⟨11, 2, 0, 1331950, 93423, 461, 262144⟩
    (by decide) selected_cut_47577

theorem unmarked_context_10_23355_1331951 : frontier 11 ⟨1331951, by decide⟩
    (prefixCache 10 23355) (prefixPartial 10 23355) = false := by
  decide +kernel

theorem node_context_10_23355_1331951 : EJMOriginalGlobalDAGData.nodes 11 ⟨1331951, by decide⟩ =
    .split (coordinate 10) (![⟨1331888, by decide⟩,⟨1331914, by decide⟩,⟨1331943, by decide⟩,⟨1331950, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23355_1331951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23355 ⟨1331951, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23355
    ⟨1331951, by decide⟩ (by decide) (![⟨1331888, by decide⟩,⟨1331914, by decide⟩,⟨1331943, by decide⟩,⟨1331950, by decide⟩]) unmarked_context_10_23355_1331951 node_context_10_23355_1331951
  intro a
  fin_cases a
  · exact context_11_93420_1331888
  · exact context_11_93421_1331914
  · exact context_11_93422_1331943
  · exact context_11_93423_1331950

theorem unmarked_context_9_5838_1331952 : frontier 12 ⟨1331952, by decide⟩
    (prefixCache 9 5838) (prefixPartial 9 5838) = false := by
  decide +kernel

theorem node_context_9_5838_1331952 : EJMOriginalGlobalDAGData.nodes 12 ⟨1331952, by decide⟩ =
    .split (coordinate 9) (![⟨1331704, by decide⟩,⟨1331833, by decide⟩,⟨1331870, by decide⟩,⟨1331951, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5838_1331952 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5838 ⟨1331952, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5838
    ⟨1331952, by decide⟩ (by decide) (![⟨1331704, by decide⟩,⟨1331833, by decide⟩,⟨1331870, by decide⟩,⟨1331951, by decide⟩]) unmarked_context_9_5838_1331952 node_context_9_5838_1331952
  intro a
  fin_cases a
  · exact context_10_23352_1331704
  · exact context_10_23353_1331833
  · exact context_10_23354_1331870
  · exact context_10_23355_1331951

theorem selected_cut_47578 : selected 11 ⟨1332016, by decide⟩
    (prefixPartial 10 23356) = some ⟨10, 2, 0, 1332016, 23356, 3185, 1048576⟩ := by
  decide +kernel

theorem context_10_23356_1332016 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23356 ⟨1332016, by decide⟩ :=
  accepted_of_selected 10 23356 ⟨1332016, by decide⟩ ⟨10, 2, 0, 1332016, 23356, 3185, 1048576⟩
    (by decide) selected_cut_47578

theorem selected_cut_47579 : selected 11 ⟨1332063, by decide⟩
    (prefixPartial 10 23357) = some ⟨10, 2, 0, 1332063, 23357, 2213, 1048576⟩ := by
  decide +kernel

theorem context_10_23357_1332063 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23357 ⟨1332063, by decide⟩ :=
  accepted_of_selected 10 23357 ⟨1332063, by decide⟩ ⟨10, 2, 0, 1332063, 23357, 2213, 1048576⟩
    (by decide) selected_cut_47579

theorem selected_cut_47580 : selected 11 ⟨1332094, by decide⟩
    (prefixPartial 10 23358) = some ⟨10, 2, 0, 1332094, 23358, 1017, 1048576⟩ := by
  decide +kernel

theorem context_10_23358_1332094 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23358 ⟨1332094, by decide⟩ :=
  accepted_of_selected 10 23358 ⟨1332094, by decide⟩ ⟨10, 2, 0, 1332094, 23358, 1017, 1048576⟩
    (by decide) selected_cut_47580

theorem selected_cut_47581 : selected 11 ⟨1332110, by decide⟩
    (prefixPartial 10 23359) = some ⟨10, 2, 0, 1332110, 23359, 185, 1048576⟩ := by
  decide +kernel

theorem context_10_23359_1332110 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23359 ⟨1332110, by decide⟩ :=
  accepted_of_selected 10 23359 ⟨1332110, by decide⟩ ⟨10, 2, 0, 1332110, 23359, 185, 1048576⟩
    (by decide) selected_cut_47581

theorem unmarked_context_9_5839_1332111 : frontier 12 ⟨1332111, by decide⟩
    (prefixCache 9 5839) (prefixPartial 9 5839) = false := by
  decide +kernel

theorem node_context_9_5839_1332111 : EJMOriginalGlobalDAGData.nodes 12 ⟨1332111, by decide⟩ =
    .split (coordinate 9) (![⟨1332016, by decide⟩,⟨1332063, by decide⟩,⟨1332094, by decide⟩,⟨1332110, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5839_1332111 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5839 ⟨1332111, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5839
    ⟨1332111, by decide⟩ (by decide) (![⟨1332016, by decide⟩,⟨1332063, by decide⟩,⟨1332094, by decide⟩,⟨1332110, by decide⟩]) unmarked_context_9_5839_1332111 node_context_9_5839_1332111
  intro a
  fin_cases a
  · exact context_10_23356_1332016
  · exact context_10_23357_1332063
  · exact context_10_23358_1332094
  · exact context_10_23359_1332110

theorem unmarked_context_8_1459_1332112 : frontier 13 ⟨1332112, by decide⟩
    (prefixCache 8 1459) (prefixPartial 8 1459) = false := by
  decide +kernel

theorem node_context_8_1459_1332112 : EJMOriginalGlobalDAGData.nodes 13 ⟨1332112, by decide⟩ =
    .split (coordinate 8) (![⟨1330712, by decide⟩,⟨1331568, by decide⟩,⟨1331952, by decide⟩,⟨1332111, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1459_1332112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1459 ⟨1332112, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1459
    ⟨1332112, by decide⟩ (by decide) (![⟨1330712, by decide⟩,⟨1331568, by decide⟩,⟨1331952, by decide⟩,⟨1332111, by decide⟩]) unmarked_context_8_1459_1332112 node_context_8_1459_1332112
  intro a
  fin_cases a
  · exact context_9_5836_1330712
  · exact context_9_5837_1331568
  · exact context_9_5838_1331952
  · exact context_9_5839_1332111

theorem unmarked_context_7_364_1332113 : frontier 14 ⟨1332113, by decide⟩
    (prefixCache 7 364) (prefixPartial 7 364) = false := by
  decide +kernel

theorem node_context_7_364_1332113 : EJMOriginalGlobalDAGData.nodes 14 ⟨1332113, by decide⟩ =
    .split (coordinate 7) (![⟨1323706, by decide⟩,⟨1326119, by decide⟩,⟨1329127, by decide⟩,⟨1332112, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_364_1332113 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 364 ⟨1332113, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 364
    ⟨1332113, by decide⟩ (by decide) (![⟨1323706, by decide⟩,⟨1326119, by decide⟩,⟨1329127, by decide⟩,⟨1332112, by decide⟩]) unmarked_context_7_364_1332113 node_context_7_364_1332113
  intro a
  fin_cases a
  · exact context_8_1456_1323706
  · exact context_8_1457_1326119
  · exact context_8_1458_1329127
  · exact context_8_1459_1332112

theorem selected_cut_47582 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 93440) = some ⟨11, 1, 0, 434745, 93440, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93440_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93440 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 93440 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 93440, 1, 262144⟩
    (by decide) selected_cut_47582

theorem selected_cut_47583 : selected 10 ⟨167448, by decide⟩
    (prefixPartial 11 93441) = some ⟨11, 1, 0, 167448, 93441, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93441_167448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93441 ⟨167448, by decide⟩ :=
  accepted_of_selected 11 93441 ⟨167448, by decide⟩ ⟨11, 1, 0, 167448, 93441, 1, 262144⟩
    (by decide) selected_cut_47583

theorem selected_cut_47584 : selected 10 ⟨1332188, by decide⟩
    (prefixPartial 11 93442) = some ⟨11, 2, 0, 1332188, 93442, 3173, 262144⟩ := by
  decide +kernel

theorem context_11_93442_1332188 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93442 ⟨1332188, by decide⟩ :=
  accepted_of_selected 11 93442 ⟨1332188, by decide⟩ ⟨11, 2, 0, 1332188, 93442, 3173, 262144⟩
    (by decide) selected_cut_47584

theorem selected_cut_47585 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 373772) = some ⟨12, 1, 0, 448748, 373772, 1, 65536⟩ := by
  decide +kernel

theorem context_12_373772_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373772 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 373772 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 373772, 1, 65536⟩
    (by decide) selected_cut_47585

theorem selected_cut_47586 : selected 9 ⟨1332243, by decide⟩
    (prefixPartial 12 373773) = some ⟨12, 2, 0, 1332243, 373773, 2657, 65536⟩ := by
  decide +kernel

theorem context_12_373773_1332243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373773 ⟨1332243, by decide⟩ :=
  accepted_of_selected 12 373773 ⟨1332243, by decide⟩ ⟨12, 2, 0, 1332243, 373773, 2657, 65536⟩
    (by decide) selected_cut_47586

theorem selected_cut_47587 : selected 9 ⟨1332313, by decide⟩
    (prefixPartial 12 373774) = some ⟨12, 2, 0, 1332313, 373774, 3045, 65536⟩ := by
  decide +kernel

theorem context_12_373774_1332313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373774 ⟨1332313, by decide⟩ :=
  accepted_of_selected 12 373774 ⟨1332313, by decide⟩ ⟨12, 2, 0, 1332313, 373774, 3045, 65536⟩
    (by decide) selected_cut_47587

theorem selected_cut_47588 : selected 9 ⟨296530, by decide⟩
    (prefixPartial 12 373775) = some ⟨12, 1, 0, 296530, 373775, 1, 65536⟩ := by
  decide +kernel

theorem context_12_373775_296530 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373775 ⟨296530, by decide⟩ :=
  accepted_of_selected 12 373775 ⟨296530, by decide⟩ ⟨12, 1, 0, 296530, 373775, 1, 65536⟩
    (by decide) selected_cut_47588

theorem unmarked_context_11_93443_1332314 : frontier 10 ⟨1332314, by decide⟩
    (prefixCache 11 93443) (prefixPartial 11 93443) = false := by
  decide +kernel

theorem node_context_11_93443_1332314 : EJMOriginalGlobalDAGData.nodes 10 ⟨1332314, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1332243, by decide⟩,⟨1332313, by decide⟩,⟨296530, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93443_1332314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93443 ⟨1332314, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93443
    ⟨1332314, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1332243, by decide⟩,⟨1332313, by decide⟩,⟨296530, by decide⟩]) unmarked_context_11_93443_1332314 node_context_11_93443_1332314
  intro a
  fin_cases a
  · exact context_12_373772_448748
  · exact context_12_373773_1332243
  · exact context_12_373774_1332313
  · exact context_12_373775_296530

theorem unmarked_context_10_23360_1332315 : frontier 11 ⟨1332315, by decide⟩
    (prefixCache 10 23360) (prefixPartial 10 23360) = false := by
  decide +kernel

theorem node_context_10_23360_1332315 : EJMOriginalGlobalDAGData.nodes 11 ⟨1332315, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨167448, by decide⟩,⟨1332188, by decide⟩,⟨1332314, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23360_1332315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23360 ⟨1332315, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23360
    ⟨1332315, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨167448, by decide⟩,⟨1332188, by decide⟩,⟨1332314, by decide⟩]) unmarked_context_10_23360_1332315 node_context_10_23360_1332315
  intro a
  fin_cases a
  · exact context_11_93440_434745
  · exact context_11_93441_167448
  · exact context_11_93442_1332188
  · exact context_11_93443_1332314

theorem selected_cut_47589 : selected 9 ⟨985390, by decide⟩
    (prefixPartial 12 373776) = some ⟨12, 1, 0, 985390, 373776, 1, 65536⟩ := by
  decide +kernel

theorem context_12_373776_985390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373776 ⟨985390, by decide⟩ :=
  accepted_of_selected 12 373776 ⟨985390, by decide⟩ ⟨12, 1, 0, 985390, 373776, 1, 65536⟩
    (by decide) selected_cut_47589

theorem selected_cut_47590 : selected 9 ⟨1332350, by decide⟩
    (prefixPartial 12 373777) = some ⟨12, 2, 0, 1332350, 373777, 2045, 65536⟩ := by
  decide +kernel

theorem context_12_373777_1332350 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373777 ⟨1332350, by decide⟩ :=
  accepted_of_selected 12 373777 ⟨1332350, by decide⟩ ⟨12, 2, 0, 1332350, 373777, 2045, 65536⟩
    (by decide) selected_cut_47590

theorem selected_cut_47591 : selected 9 ⟨1332394, by decide⟩
    (prefixPartial 12 373778) = some ⟨12, 2, 0, 1332394, 373778, 2317, 65536⟩ := by
  decide +kernel

theorem context_12_373778_1332394 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373778 ⟨1332394, by decide⟩ :=
  accepted_of_selected 12 373778 ⟨1332394, by decide⟩ ⟨12, 2, 0, 1332394, 373778, 2317, 65536⟩
    (by decide) selected_cut_47591

theorem selected_cut_47592 : selected 9 ⟨1332442, by decide⟩
    (prefixPartial 12 373779) = some ⟨12, 2, 0, 1332442, 373779, 2549, 65536⟩ := by
  decide +kernel

theorem context_12_373779_1332442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373779 ⟨1332442, by decide⟩ :=
  accepted_of_selected 12 373779 ⟨1332442, by decide⟩ ⟨12, 2, 0, 1332442, 373779, 2549, 65536⟩
    (by decide) selected_cut_47592

theorem unmarked_context_11_93444_1332443 : frontier 10 ⟨1332443, by decide⟩
    (prefixCache 11 93444) (prefixPartial 11 93444) = false := by
  decide +kernel

theorem node_context_11_93444_1332443 : EJMOriginalGlobalDAGData.nodes 10 ⟨1332443, by decide⟩ =
    .split (coordinate 11) (![⟨985390, by decide⟩,⟨1332350, by decide⟩,⟨1332394, by decide⟩,⟨1332442, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93444_1332443 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93444 ⟨1332443, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93444
    ⟨1332443, by decide⟩ (by decide) (![⟨985390, by decide⟩,⟨1332350, by decide⟩,⟨1332394, by decide⟩,⟨1332442, by decide⟩]) unmarked_context_11_93444_1332443 node_context_11_93444_1332443
  intro a
  fin_cases a
  · exact context_12_373776_985390
  · exact context_12_373777_1332350
  · exact context_12_373778_1332394
  · exact context_12_373779_1332442

theorem selected_cut_47593 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 93445) = some ⟨11, 1, 0, 892405, 93445, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93445_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93445 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 93445 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 93445, 1, 262144⟩
    (by decide) selected_cut_47593

theorem selected_cut_47594 : selected 9 ⟨994572, by decide⟩
    (prefixPartial 12 373784) = some ⟨12, 1, 0, 994572, 373784, 1, 65536⟩ := by
  decide +kernel

theorem context_12_373784_994572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373784 ⟨994572, by decide⟩ :=
  accepted_of_selected 12 373784 ⟨994572, by decide⟩ ⟨12, 1, 0, 994572, 373784, 1, 65536⟩
    (by decide) selected_cut_47594

theorem selected_cut_47595 : selected 9 ⟨1332475, by decide⟩
    (prefixPartial 12 373785) = some ⟨12, 2, 0, 1332475, 373785, 2073, 65536⟩ := by
  decide +kernel

theorem context_12_373785_1332475 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373785 ⟨1332475, by decide⟩ :=
  accepted_of_selected 12 373785 ⟨1332475, by decide⟩ ⟨12, 2, 0, 1332475, 373785, 2073, 65536⟩
    (by decide) selected_cut_47595

theorem selected_cut_47596 : selected 9 ⟨806997, by decide⟩
    (prefixPartial 12 373786) = some ⟨12, 1, 0, 806997, 373786, 1, 65536⟩ := by
  decide +kernel

theorem context_12_373786_806997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373786 ⟨806997, by decide⟩ :=
  accepted_of_selected 12 373786 ⟨806997, by decide⟩ ⟨12, 1, 0, 806997, 373786, 1, 65536⟩
    (by decide) selected_cut_47596

theorem selected_cut_47597 : selected 9 ⟨1332525, by decide⟩
    (prefixPartial 12 373787) = some ⟨12, 2, 0, 1332525, 373787, 2777, 65536⟩ := by
  decide +kernel

theorem context_12_373787_1332525 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373787 ⟨1332525, by decide⟩ :=
  accepted_of_selected 12 373787 ⟨1332525, by decide⟩ ⟨12, 2, 0, 1332525, 373787, 2777, 65536⟩
    (by decide) selected_cut_47597

theorem unmarked_context_11_93446_1332526 : frontier 10 ⟨1332526, by decide⟩
    (prefixCache 11 93446) (prefixPartial 11 93446) = false := by
  decide +kernel

theorem node_context_11_93446_1332526 : EJMOriginalGlobalDAGData.nodes 10 ⟨1332526, by decide⟩ =
    .split (coordinate 11) (![⟨994572, by decide⟩,⟨1332475, by decide⟩,⟨806997, by decide⟩,⟨1332525, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93446_1332526 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93446 ⟨1332526, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93446
    ⟨1332526, by decide⟩ (by decide) (![⟨994572, by decide⟩,⟨1332475, by decide⟩,⟨806997, by decide⟩,⟨1332525, by decide⟩]) unmarked_context_11_93446_1332526 node_context_11_93446_1332526
  intro a
  fin_cases a
  · exact context_12_373784_994572
  · exact context_12_373785_1332475
  · exact context_12_373786_806997
  · exact context_12_373787_1332525

theorem selected_cut_47598 : selected 9 ⟨1332578, by decide⟩
    (prefixPartial 12 373788) = some ⟨12, 2, 0, 1332578, 373788, 2381, 65536⟩ := by
  decide +kernel

theorem context_12_373788_1332578 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373788 ⟨1332578, by decide⟩ :=
  accepted_of_selected 12 373788 ⟨1332578, by decide⟩ ⟨12, 2, 0, 1332578, 373788, 2381, 65536⟩
    (by decide) selected_cut_47598

theorem selected_cut_47599 : selected 9 ⟨1332606, by decide⟩
    (prefixPartial 12 373789) = some ⟨12, 2, 0, 1332606, 373789, 2061, 65536⟩ := by
  decide +kernel

theorem context_12_373789_1332606 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373789 ⟨1332606, by decide⟩ :=
  accepted_of_selected 12 373789 ⟨1332606, by decide⟩ ⟨12, 2, 0, 1332606, 373789, 2061, 65536⟩
    (by decide) selected_cut_47599

theorem selected_cut_47600 : selected 9 ⟨1332660, by decide⟩
    (prefixPartial 12 373790) = some ⟨12, 2, 0, 1332660, 373790, 2573, 65536⟩ := by
  decide +kernel

theorem context_12_373790_1332660 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373790 ⟨1332660, by decide⟩ :=
  accepted_of_selected 12 373790 ⟨1332660, by decide⟩ ⟨12, 2, 0, 1332660, 373790, 2573, 65536⟩
    (by decide) selected_cut_47600

theorem selected_cut_47601 : selected 9 ⟨1332707, by decide⟩
    (prefixPartial 12 373791) = some ⟨12, 2, 0, 1332707, 373791, 2597, 65536⟩ := by
  decide +kernel

theorem context_12_373791_1332707 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373791 ⟨1332707, by decide⟩ :=
  accepted_of_selected 12 373791 ⟨1332707, by decide⟩ ⟨12, 2, 0, 1332707, 373791, 2597, 65536⟩
    (by decide) selected_cut_47601

theorem unmarked_context_11_93447_1332708 : frontier 10 ⟨1332708, by decide⟩
    (prefixCache 11 93447) (prefixPartial 11 93447) = false := by
  decide +kernel

theorem node_context_11_93447_1332708 : EJMOriginalGlobalDAGData.nodes 10 ⟨1332708, by decide⟩ =
    .split (coordinate 11) (![⟨1332578, by decide⟩,⟨1332606, by decide⟩,⟨1332660, by decide⟩,⟨1332707, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93447_1332708 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93447 ⟨1332708, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93447
    ⟨1332708, by decide⟩ (by decide) (![⟨1332578, by decide⟩,⟨1332606, by decide⟩,⟨1332660, by decide⟩,⟨1332707, by decide⟩]) unmarked_context_11_93447_1332708 node_context_11_93447_1332708
  intro a
  fin_cases a
  · exact context_12_373788_1332578
  · exact context_12_373789_1332606
  · exact context_12_373790_1332660
  · exact context_12_373791_1332707

theorem unmarked_context_10_23361_1332709 : frontier 11 ⟨1332709, by decide⟩
    (prefixCache 10 23361) (prefixPartial 10 23361) = false := by
  decide +kernel

theorem node_context_10_23361_1332709 : EJMOriginalGlobalDAGData.nodes 11 ⟨1332709, by decide⟩ =
    .split (coordinate 10) (![⟨1332443, by decide⟩,⟨892405, by decide⟩,⟨1332526, by decide⟩,⟨1332708, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23361_1332709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23361 ⟨1332709, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23361
    ⟨1332709, by decide⟩ (by decide) (![⟨1332443, by decide⟩,⟨892405, by decide⟩,⟨1332526, by decide⟩,⟨1332708, by decide⟩]) unmarked_context_10_23361_1332709 node_context_10_23361_1332709
  intro a
  fin_cases a
  · exact context_11_93444_1332443
  · exact context_11_93445_892405
  · exact context_11_93446_1332526
  · exact context_11_93447_1332708

theorem selected_cut_47602 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 373792) = some ⟨12, 1, 0, 435790, 373792, 1, 65536⟩ := by
  decide +kernel

theorem context_12_373792_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373792 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 373792 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 373792, 1, 65536⟩
    (by decide) selected_cut_47602

theorem selected_cut_47603 : selected 9 ⟨1332746, by decide⟩
    (prefixPartial 12 373793) = some ⟨12, 2, 0, 1332746, 373793, 2069, 65536⟩ := by
  decide +kernel

theorem context_12_373793_1332746 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373793 ⟨1332746, by decide⟩ :=
  accepted_of_selected 12 373793 ⟨1332746, by decide⟩ ⟨12, 2, 0, 1332746, 373793, 2069, 65536⟩
    (by decide) selected_cut_47603

theorem selected_cut_47604 : selected 9 ⟨1332794, by decide⟩
    (prefixPartial 12 373794) = some ⟨12, 2, 0, 1332794, 373794, 2397, 65536⟩ := by
  decide +kernel

theorem context_12_373794_1332794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373794 ⟨1332794, by decide⟩ :=
  accepted_of_selected 12 373794 ⟨1332794, by decide⟩ ⟨12, 2, 0, 1332794, 373794, 2397, 65536⟩
    (by decide) selected_cut_47604

theorem selected_cut_47605 : selected 9 ⟨1332839, by decide⟩
    (prefixPartial 12 373795) = some ⟨12, 2, 0, 1332839, 373795, 2493, 65536⟩ := by
  decide +kernel

theorem context_12_373795_1332839 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373795 ⟨1332839, by decide⟩ :=
  accepted_of_selected 12 373795 ⟨1332839, by decide⟩ ⟨12, 2, 0, 1332839, 373795, 2493, 65536⟩
    (by decide) selected_cut_47605

theorem unmarked_context_11_93448_1332840 : frontier 10 ⟨1332840, by decide⟩
    (prefixCache 11 93448) (prefixPartial 11 93448) = false := by
  decide +kernel

theorem node_context_11_93448_1332840 : EJMOriginalGlobalDAGData.nodes 10 ⟨1332840, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨1332746, by decide⟩,⟨1332794, by decide⟩,⟨1332839, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93448_1332840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93448 ⟨1332840, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93448
    ⟨1332840, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨1332746, by decide⟩,⟨1332794, by decide⟩,⟨1332839, by decide⟩]) unmarked_context_11_93448_1332840 node_context_11_93448_1332840
  intro a
  fin_cases a
  · exact context_12_373792_435790
  · exact context_12_373793_1332746
  · exact context_12_373794_1332794
  · exact context_12_373795_1332839

theorem selected_cut_47606 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 373796) = some ⟨12, 1, 0, 435790, 373796, 1, 65536⟩ := by
  decide +kernel

theorem context_12_373796_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373796 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 373796 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 373796, 1, 65536⟩
    (by decide) selected_cut_47606

theorem selected_cut_47607 : selected 9 ⟨1321747, by decide⟩
    (prefixPartial 12 373797) = some ⟨12, 1, 0, 1321747, 373797, 1, 65536⟩ := by
  decide +kernel

theorem context_12_373797_1321747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373797 ⟨1321747, by decide⟩ :=
  accepted_of_selected 12 373797 ⟨1321747, by decide⟩ ⟨12, 1, 0, 1321747, 373797, 1, 65536⟩
    (by decide) selected_cut_47607

theorem selected_cut_47608 : selected 9 ⟨1332891, by decide⟩
    (prefixPartial 12 373798) = some ⟨12, 2, 0, 1332891, 373798, 2541, 65536⟩ := by
  decide +kernel

theorem context_12_373798_1332891 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373798 ⟨1332891, by decide⟩ :=
  accepted_of_selected 12 373798 ⟨1332891, by decide⟩ ⟨12, 2, 0, 1332891, 373798, 2541, 65536⟩
    (by decide) selected_cut_47608

theorem selected_cut_47609 : selected 9 ⟨1332947, by decide⟩
    (prefixPartial 12 373799) = some ⟨12, 2, 0, 1332947, 373799, 2525, 65536⟩ := by
  decide +kernel

theorem context_12_373799_1332947 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373799 ⟨1332947, by decide⟩ :=
  accepted_of_selected 12 373799 ⟨1332947, by decide⟩ ⟨12, 2, 0, 1332947, 373799, 2525, 65536⟩
    (by decide) selected_cut_47609

theorem unmarked_context_11_93449_1332948 : frontier 10 ⟨1332948, by decide⟩
    (prefixCache 11 93449) (prefixPartial 11 93449) = false := by
  decide +kernel

theorem node_context_11_93449_1332948 : EJMOriginalGlobalDAGData.nodes 10 ⟨1332948, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨1321747, by decide⟩,⟨1332891, by decide⟩,⟨1332947, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93449_1332948 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93449 ⟨1332948, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93449
    ⟨1332948, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨1321747, by decide⟩,⟨1332891, by decide⟩,⟨1332947, by decide⟩]) unmarked_context_11_93449_1332948 node_context_11_93449_1332948
  intro a
  fin_cases a
  · exact context_12_373796_435790
  · exact context_12_373797_1321747
  · exact context_12_373798_1332891
  · exact context_12_373799_1332947

theorem selected_cut_47610 : selected 10 ⟨1332995, by decide⟩
    (prefixPartial 11 93450) = some ⟨11, 2, 0, 1332995, 93450, 2573, 262144⟩ := by
  decide +kernel

theorem context_11_93450_1332995 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93450 ⟨1332995, by decide⟩ :=
  accepted_of_selected 11 93450 ⟨1332995, by decide⟩ ⟨11, 2, 0, 1332995, 93450, 2573, 262144⟩
    (by decide) selected_cut_47610

theorem selected_cut_47611 : selected 9 ⟨450498, by decide⟩
    (prefixPartial 12 373804) = some ⟨12, 1, 0, 450498, 373804, 1, 65536⟩ := by
  decide +kernel

theorem context_12_373804_450498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373804 ⟨450498, by decide⟩ :=
  accepted_of_selected 12 373804 ⟨450498, by decide⟩ ⟨12, 1, 0, 450498, 373804, 1, 65536⟩
    (by decide) selected_cut_47611

theorem selected_cut_47612 : selected 9 ⟨1333034, by decide⟩
    (prefixPartial 12 373805) = some ⟨12, 2, 0, 1333034, 373805, 2137, 65536⟩ := by
  decide +kernel

theorem context_12_373805_1333034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373805 ⟨1333034, by decide⟩ :=
  accepted_of_selected 12 373805 ⟨1333034, by decide⟩ ⟨12, 2, 0, 1333034, 373805, 2137, 65536⟩
    (by decide) selected_cut_47612

theorem selected_cut_47613 : selected 9 ⟨1333084, by decide⟩
    (prefixPartial 12 373806) = some ⟨12, 2, 0, 1333084, 373806, 2533, 65536⟩ := by
  decide +kernel

theorem context_12_373806_1333084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373806 ⟨1333084, by decide⟩ :=
  accepted_of_selected 12 373806 ⟨1333084, by decide⟩ ⟨12, 2, 0, 1333084, 373806, 2533, 65536⟩
    (by decide) selected_cut_47613

theorem selected_cut_47614 : selected 9 ⟨1321995, by decide⟩
    (prefixPartial 12 373807) = some ⟨12, 1, 0, 1321995, 373807, 1, 65536⟩ := by
  decide +kernel

theorem context_12_373807_1321995 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373807 ⟨1321995, by decide⟩ :=
  accepted_of_selected 12 373807 ⟨1321995, by decide⟩ ⟨12, 1, 0, 1321995, 373807, 1, 65536⟩
    (by decide) selected_cut_47614

theorem unmarked_context_11_93451_1333085 : frontier 10 ⟨1333085, by decide⟩
    (prefixCache 11 93451) (prefixPartial 11 93451) = false := by
  decide +kernel

theorem node_context_11_93451_1333085 : EJMOriginalGlobalDAGData.nodes 10 ⟨1333085, by decide⟩ =
    .split (coordinate 11) (![⟨450498, by decide⟩,⟨1333034, by decide⟩,⟨1333084, by decide⟩,⟨1321995, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93451_1333085 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93451 ⟨1333085, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93451
    ⟨1333085, by decide⟩ (by decide) (![⟨450498, by decide⟩,⟨1333034, by decide⟩,⟨1333084, by decide⟩,⟨1321995, by decide⟩]) unmarked_context_11_93451_1333085 node_context_11_93451_1333085
  intro a
  fin_cases a
  · exact context_12_373804_450498
  · exact context_12_373805_1333034
  · exact context_12_373806_1333084
  · exact context_12_373807_1321995

theorem unmarked_context_10_23362_1333086 : frontier 11 ⟨1333086, by decide⟩
    (prefixCache 10 23362) (prefixPartial 10 23362) = false := by
  decide +kernel

theorem node_context_10_23362_1333086 : EJMOriginalGlobalDAGData.nodes 11 ⟨1333086, by decide⟩ =
    .split (coordinate 10) (![⟨1332840, by decide⟩,⟨1332948, by decide⟩,⟨1332995, by decide⟩,⟨1333085, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23362_1333086 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23362 ⟨1333086, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23362
    ⟨1333086, by decide⟩ (by decide) (![⟨1332840, by decide⟩,⟨1332948, by decide⟩,⟨1332995, by decide⟩,⟨1333085, by decide⟩]) unmarked_context_10_23362_1333086 node_context_10_23362_1333086
  intro a
  fin_cases a
  · exact context_11_93448_1332840
  · exact context_11_93449_1332948
  · exact context_11_93450_1332995
  · exact context_11_93451_1333085

theorem selected_cut_47615 : selected 9 ⟨985390, by decide⟩
    (prefixPartial 12 373808) = some ⟨12, 1, 0, 985390, 373808, 1, 65536⟩ := by
  decide +kernel

theorem context_12_373808_985390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373808 ⟨985390, by decide⟩ :=
  accepted_of_selected 12 373808 ⟨985390, by decide⟩ ⟨12, 1, 0, 985390, 373808, 1, 65536⟩
    (by decide) selected_cut_47615

theorem selected_cut_47616 : selected 9 ⟨1333115, by decide⟩
    (prefixPartial 12 373809) = some ⟨12, 2, 0, 1333115, 373809, 1853, 65536⟩ := by
  decide +kernel

theorem context_12_373809_1333115 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373809 ⟨1333115, by decide⟩ :=
  accepted_of_selected 12 373809 ⟨1333115, by decide⟩ ⟨12, 2, 0, 1333115, 373809, 1853, 65536⟩
    (by decide) selected_cut_47616

theorem selected_cut_47617 : selected 9 ⟨1333160, by decide⟩
    (prefixPartial 12 373810) = some ⟨12, 2, 0, 1333160, 373810, 2233, 65536⟩ := by
  decide +kernel

theorem context_12_373810_1333160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373810 ⟨1333160, by decide⟩ :=
  accepted_of_selected 12 373810 ⟨1333160, by decide⟩ ⟨12, 2, 0, 1333160, 373810, 2233, 65536⟩
    (by decide) selected_cut_47617

theorem selected_cut_47618 : selected 9 ⟨1333200, by decide⟩
    (prefixPartial 12 373811) = some ⟨12, 2, 0, 1333200, 373811, 2293, 65536⟩ := by
  decide +kernel

theorem context_12_373811_1333200 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373811 ⟨1333200, by decide⟩ :=
  accepted_of_selected 12 373811 ⟨1333200, by decide⟩ ⟨12, 2, 0, 1333200, 373811, 2293, 65536⟩
    (by decide) selected_cut_47618

theorem unmarked_context_11_93452_1333201 : frontier 10 ⟨1333201, by decide⟩
    (prefixCache 11 93452) (prefixPartial 11 93452) = false := by
  decide +kernel

theorem node_context_11_93452_1333201 : EJMOriginalGlobalDAGData.nodes 10 ⟨1333201, by decide⟩ =
    .split (coordinate 11) (![⟨985390, by decide⟩,⟨1333115, by decide⟩,⟨1333160, by decide⟩,⟨1333200, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93452_1333201 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93452 ⟨1333201, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93452
    ⟨1333201, by decide⟩ (by decide) (![⟨985390, by decide⟩,⟨1333115, by decide⟩,⟨1333160, by decide⟩,⟨1333200, by decide⟩]) unmarked_context_11_93452_1333201 node_context_11_93452_1333201
  intro a
  fin_cases a
  · exact context_12_373808_985390
  · exact context_12_373809_1333115
  · exact context_12_373810_1333160
  · exact context_12_373811_1333200

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
