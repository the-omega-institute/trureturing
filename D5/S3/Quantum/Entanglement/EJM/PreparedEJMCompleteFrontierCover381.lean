/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover380
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_36579 : selected 9 ⟨970550, by decide⟩
    (prefixPartial 12 289554) = some ⟨12, 2, 0, 970550, 289554, 3893, 65536⟩ := by
  decide +kernel

theorem context_12_289554_970550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289554 ⟨970550, by decide⟩ :=
  accepted_of_selected 12 289554 ⟨970550, by decide⟩ ⟨12, 2, 0, 970550, 289554, 3893, 65536⟩
    (by decide) selected_cut_36579

theorem selected_cut_36580 : selected 9 ⟨970608, by decide⟩
    (prefixPartial 12 289555) = some ⟨12, 2, 0, 970608, 289555, 3937, 65536⟩ := by
  decide +kernel

theorem context_12_289555_970608 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289555 ⟨970608, by decide⟩ :=
  accepted_of_selected 12 289555 ⟨970608, by decide⟩ ⟨12, 2, 0, 970608, 289555, 3937, 65536⟩
    (by decide) selected_cut_36580

theorem unmarked_context_11_72388_970609 : frontier 10 ⟨970609, by decide⟩
    (prefixCache 11 72388) (prefixPartial 11 72388) = false := by
  decide +kernel

theorem node_context_11_72388_970609 : EJMOriginalGlobalDAGData.nodes 10 ⟨970609, by decide⟩ =
    .split (coordinate 11) (![⟨970432, by decide⟩,⟨970492, by decide⟩,⟨970550, by decide⟩,⟨970608, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72388_970609 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72388 ⟨970609, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72388
    ⟨970609, by decide⟩ (by decide) (![⟨970432, by decide⟩,⟨970492, by decide⟩,⟨970550, by decide⟩,⟨970608, by decide⟩]) unmarked_context_11_72388_970609 node_context_11_72388_970609
  intro a
  fin_cases a
  · exact context_12_289552_970432
  · exact context_12_289553_970492
  · exact context_12_289554_970550
  · exact context_12_289555_970608

theorem selected_cut_36581 : selected 9 ⟨970652, by decide⟩
    (prefixPartial 12 289556) = some ⟨12, 2, 0, 970652, 289556, 3329, 65536⟩ := by
  decide +kernel

theorem context_12_289556_970652 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289556 ⟨970652, by decide⟩ :=
  accepted_of_selected 12 289556 ⟨970652, by decide⟩ ⟨12, 2, 0, 970652, 289556, 3329, 65536⟩
    (by decide) selected_cut_36581

theorem selected_cut_36582 : selected 9 ⟨970707, by decide⟩
    (prefixPartial 12 289557) = some ⟨12, 2, 0, 970707, 289557, 3549, 65536⟩ := by
  decide +kernel

theorem context_12_289557_970707 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289557 ⟨970707, by decide⟩ :=
  accepted_of_selected 12 289557 ⟨970707, by decide⟩ ⟨12, 2, 0, 970707, 289557, 3549, 65536⟩
    (by decide) selected_cut_36582

theorem selected_cut_36583 : selected 9 ⟨970760, by decide⟩
    (prefixPartial 12 289558) = some ⟨12, 2, 0, 970760, 289558, 3429, 65536⟩ := by
  decide +kernel

theorem context_12_289558_970760 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289558 ⟨970760, by decide⟩ :=
  accepted_of_selected 12 289558 ⟨970760, by decide⟩ ⟨12, 2, 0, 970760, 289558, 3429, 65536⟩
    (by decide) selected_cut_36583

theorem selected_cut_36584 : selected 9 ⟨970811, by decide⟩
    (prefixPartial 12 289559) = some ⟨12, 2, 0, 970811, 289559, 3529, 65536⟩ := by
  decide +kernel

theorem context_12_289559_970811 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289559 ⟨970811, by decide⟩ :=
  accepted_of_selected 12 289559 ⟨970811, by decide⟩ ⟨12, 2, 0, 970811, 289559, 3529, 65536⟩
    (by decide) selected_cut_36584

theorem unmarked_context_11_72389_970812 : frontier 10 ⟨970812, by decide⟩
    (prefixCache 11 72389) (prefixPartial 11 72389) = false := by
  decide +kernel

theorem node_context_11_72389_970812 : EJMOriginalGlobalDAGData.nodes 10 ⟨970812, by decide⟩ =
    .split (coordinate 11) (![⟨970652, by decide⟩,⟨970707, by decide⟩,⟨970760, by decide⟩,⟨970811, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72389_970812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72389 ⟨970812, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72389
    ⟨970812, by decide⟩ (by decide) (![⟨970652, by decide⟩,⟨970707, by decide⟩,⟨970760, by decide⟩,⟨970811, by decide⟩]) unmarked_context_11_72389_970812 node_context_11_72389_970812
  intro a
  fin_cases a
  · exact context_12_289556_970652
  · exact context_12_289557_970707
  · exact context_12_289558_970760
  · exact context_12_289559_970811

theorem selected_cut_36585 : selected 9 ⟨970870, by decide⟩
    (prefixPartial 12 289560) = some ⟨12, 2, 0, 970870, 289560, 3533, 65536⟩ := by
  decide +kernel

theorem context_12_289560_970870 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289560 ⟨970870, by decide⟩ :=
  accepted_of_selected 12 289560 ⟨970870, by decide⟩ ⟨12, 2, 0, 970870, 289560, 3533, 65536⟩
    (by decide) selected_cut_36585

theorem selected_cut_36586 : selected 9 ⟨970923, by decide⟩
    (prefixPartial 12 289561) = some ⟨12, 2, 0, 970923, 289561, 3441, 65536⟩ := by
  decide +kernel

theorem context_12_289561_970923 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289561 ⟨970923, by decide⟩ :=
  accepted_of_selected 12 289561 ⟨970923, by decide⟩ ⟨12, 2, 0, 970923, 289561, 3441, 65536⟩
    (by decide) selected_cut_36586

theorem selected_cut_36587 : selected 9 ⟨970978, by decide⟩
    (prefixPartial 12 289562) = some ⟨12, 2, 0, 970978, 289562, 3253, 65536⟩ := by
  decide +kernel

theorem context_12_289562_970978 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289562 ⟨970978, by decide⟩ :=
  accepted_of_selected 12 289562 ⟨970978, by decide⟩ ⟨12, 2, 0, 970978, 289562, 3253, 65536⟩
    (by decide) selected_cut_36587

theorem selected_cut_36588 : selected 9 ⟨971035, by decide⟩
    (prefixPartial 12 289563) = some ⟨12, 2, 0, 971035, 289563, 3553, 65536⟩ := by
  decide +kernel

theorem context_12_289563_971035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289563 ⟨971035, by decide⟩ :=
  accepted_of_selected 12 289563 ⟨971035, by decide⟩ ⟨12, 2, 0, 971035, 289563, 3553, 65536⟩
    (by decide) selected_cut_36588

theorem unmarked_context_11_72390_971036 : frontier 10 ⟨971036, by decide⟩
    (prefixCache 11 72390) (prefixPartial 11 72390) = false := by
  decide +kernel

theorem node_context_11_72390_971036 : EJMOriginalGlobalDAGData.nodes 10 ⟨971036, by decide⟩ =
    .split (coordinate 11) (![⟨970870, by decide⟩,⟨970923, by decide⟩,⟨970978, by decide⟩,⟨971035, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72390_971036 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72390 ⟨971036, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72390
    ⟨971036, by decide⟩ (by decide) (![⟨970870, by decide⟩,⟨970923, by decide⟩,⟨970978, by decide⟩,⟨971035, by decide⟩]) unmarked_context_11_72390_971036 node_context_11_72390_971036
  intro a
  fin_cases a
  · exact context_12_289560_970870
  · exact context_12_289561_970923
  · exact context_12_289562_970978
  · exact context_12_289563_971035

theorem selected_cut_36589 : selected 9 ⟨971084, by decide⟩
    (prefixPartial 12 289564) = some ⟨12, 2, 0, 971084, 289564, 3193, 65536⟩ := by
  decide +kernel

theorem context_12_289564_971084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289564 ⟨971084, by decide⟩ :=
  accepted_of_selected 12 289564 ⟨971084, by decide⟩ ⟨12, 2, 0, 971084, 289564, 3193, 65536⟩
    (by decide) selected_cut_36589

theorem selected_cut_36590 : selected 9 ⟨971129, by decide⟩
    (prefixPartial 12 289565) = some ⟨12, 2, 0, 971129, 289565, 3157, 65536⟩ := by
  decide +kernel

theorem context_12_289565_971129 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289565 ⟨971129, by decide⟩ :=
  accepted_of_selected 12 289565 ⟨971129, by decide⟩ ⟨12, 2, 0, 971129, 289565, 3157, 65536⟩
    (by decide) selected_cut_36590

theorem selected_cut_36591 : selected 9 ⟨971178, by decide⟩
    (prefixPartial 12 289566) = some ⟨12, 2, 0, 971178, 289566, 3289, 65536⟩ := by
  decide +kernel

theorem context_12_289566_971178 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289566 ⟨971178, by decide⟩ :=
  accepted_of_selected 12 289566 ⟨971178, by decide⟩ ⟨12, 2, 0, 971178, 289566, 3289, 65536⟩
    (by decide) selected_cut_36591

theorem selected_cut_36592 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 289567) = some ⟨12, 1, 0, 903806, 289567, 1, 65536⟩ := by
  decide +kernel

theorem context_12_289567_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289567 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 289567 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 289567, 1, 65536⟩
    (by decide) selected_cut_36592

theorem unmarked_context_11_72391_971179 : frontier 10 ⟨971179, by decide⟩
    (prefixCache 11 72391) (prefixPartial 11 72391) = false := by
  decide +kernel

theorem node_context_11_72391_971179 : EJMOriginalGlobalDAGData.nodes 10 ⟨971179, by decide⟩ =
    .split (coordinate 11) (![⟨971084, by decide⟩,⟨971129, by decide⟩,⟨971178, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72391_971179 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72391 ⟨971179, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72391
    ⟨971179, by decide⟩ (by decide) (![⟨971084, by decide⟩,⟨971129, by decide⟩,⟨971178, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_72391_971179 node_context_11_72391_971179
  intro a
  fin_cases a
  · exact context_12_289564_971084
  · exact context_12_289565_971129
  · exact context_12_289566_971178
  · exact context_12_289567_903806

theorem unmarked_context_10_18097_971180 : frontier 11 ⟨971180, by decide⟩
    (prefixCache 10 18097) (prefixPartial 10 18097) = false := by
  decide +kernel

theorem node_context_10_18097_971180 : EJMOriginalGlobalDAGData.nodes 11 ⟨971180, by decide⟩ =
    .split (coordinate 10) (![⟨970609, by decide⟩,⟨970812, by decide⟩,⟨971036, by decide⟩,⟨971179, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18097_971180 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18097 ⟨971180, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18097
    ⟨971180, by decide⟩ (by decide) (![⟨970609, by decide⟩,⟨970812, by decide⟩,⟨971036, by decide⟩,⟨971179, by decide⟩]) unmarked_context_10_18097_971180 node_context_10_18097_971180
  intro a
  fin_cases a
  · exact context_11_72388_970609
  · exact context_11_72389_970812
  · exact context_11_72390_971036
  · exact context_11_72391_971179

theorem selected_cut_36593 : selected 9 ⟨971221, by decide⟩
    (prefixPartial 12 289568) = some ⟨12, 2, 0, 971221, 289568, 2793, 65536⟩ := by
  decide +kernel

theorem context_12_289568_971221 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289568 ⟨971221, by decide⟩ :=
  accepted_of_selected 12 289568 ⟨971221, by decide⟩ ⟨12, 2, 0, 971221, 289568, 2793, 65536⟩
    (by decide) selected_cut_36593

theorem selected_cut_36594 : selected 9 ⟨971262, by decide⟩
    (prefixPartial 12 289569) = some ⟨12, 2, 0, 971262, 289569, 2845, 65536⟩ := by
  decide +kernel

theorem context_12_289569_971262 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289569 ⟨971262, by decide⟩ :=
  accepted_of_selected 12 289569 ⟨971262, by decide⟩ ⟨12, 2, 0, 971262, 289569, 2845, 65536⟩
    (by decide) selected_cut_36594

theorem selected_cut_36595 : selected 9 ⟨971317, by decide⟩
    (prefixPartial 12 289570) = some ⟨12, 2, 0, 971317, 289570, 3173, 65536⟩ := by
  decide +kernel

theorem context_12_289570_971317 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289570 ⟨971317, by decide⟩ :=
  accepted_of_selected 12 289570 ⟨971317, by decide⟩ ⟨12, 2, 0, 971317, 289570, 3173, 65536⟩
    (by decide) selected_cut_36595

theorem selected_cut_36596 : selected 9 ⟨971367, by decide⟩
    (prefixPartial 12 289571) = some ⟨12, 2, 0, 971367, 289571, 3133, 65536⟩ := by
  decide +kernel

theorem context_12_289571_971367 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289571 ⟨971367, by decide⟩ :=
  accepted_of_selected 12 289571 ⟨971367, by decide⟩ ⟨12, 2, 0, 971367, 289571, 3133, 65536⟩
    (by decide) selected_cut_36596

theorem unmarked_context_11_72392_971368 : frontier 10 ⟨971368, by decide⟩
    (prefixCache 11 72392) (prefixPartial 11 72392) = false := by
  decide +kernel

theorem node_context_11_72392_971368 : EJMOriginalGlobalDAGData.nodes 10 ⟨971368, by decide⟩ =
    .split (coordinate 11) (![⟨971221, by decide⟩,⟨971262, by decide⟩,⟨971317, by decide⟩,⟨971367, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72392_971368 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72392 ⟨971368, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72392
    ⟨971368, by decide⟩ (by decide) (![⟨971221, by decide⟩,⟨971262, by decide⟩,⟨971317, by decide⟩,⟨971367, by decide⟩]) unmarked_context_11_72392_971368 node_context_11_72392_971368
  intro a
  fin_cases a
  · exact context_12_289568_971221
  · exact context_12_289569_971262
  · exact context_12_289570_971317
  · exact context_12_289571_971367

theorem selected_cut_36597 : selected 9 ⟨971412, by decide⟩
    (prefixPartial 12 289572) = some ⟨12, 2, 0, 971412, 289572, 2849, 65536⟩ := by
  decide +kernel

theorem context_12_289572_971412 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289572 ⟨971412, by decide⟩ :=
  accepted_of_selected 12 289572 ⟨971412, by decide⟩ ⟨12, 2, 0, 971412, 289572, 2849, 65536⟩
    (by decide) selected_cut_36597

theorem selected_cut_36598 : selected 9 ⟨971448, by decide⟩
    (prefixPartial 12 289573) = some ⟨12, 2, 0, 971448, 289573, 2757, 65536⟩ := by
  decide +kernel

theorem context_12_289573_971448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289573 ⟨971448, by decide⟩ :=
  accepted_of_selected 12 289573 ⟨971448, by decide⟩ ⟨12, 2, 0, 971448, 289573, 2757, 65536⟩
    (by decide) selected_cut_36598

theorem selected_cut_36599 : selected 9 ⟨971495, by decide⟩
    (prefixPartial 12 289574) = some ⟨12, 2, 0, 971495, 289574, 2761, 65536⟩ := by
  decide +kernel

theorem context_12_289574_971495 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289574 ⟨971495, by decide⟩ :=
  accepted_of_selected 12 289574 ⟨971495, by decide⟩ ⟨12, 2, 0, 971495, 289574, 2761, 65536⟩
    (by decide) selected_cut_36599

theorem selected_cut_36600 : selected 9 ⟨971538, by decide⟩
    (prefixPartial 12 289575) = some ⟨12, 2, 0, 971538, 289575, 2765, 65536⟩ := by
  decide +kernel

theorem context_12_289575_971538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289575 ⟨971538, by decide⟩ :=
  accepted_of_selected 12 289575 ⟨971538, by decide⟩ ⟨12, 2, 0, 971538, 289575, 2765, 65536⟩
    (by decide) selected_cut_36600

theorem unmarked_context_11_72393_971539 : frontier 10 ⟨971539, by decide⟩
    (prefixCache 11 72393) (prefixPartial 11 72393) = false := by
  decide +kernel

theorem node_context_11_72393_971539 : EJMOriginalGlobalDAGData.nodes 10 ⟨971539, by decide⟩ =
    .split (coordinate 11) (![⟨971412, by decide⟩,⟨971448, by decide⟩,⟨971495, by decide⟩,⟨971538, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72393_971539 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72393 ⟨971539, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72393
    ⟨971539, by decide⟩ (by decide) (![⟨971412, by decide⟩,⟨971448, by decide⟩,⟨971495, by decide⟩,⟨971538, by decide⟩]) unmarked_context_11_72393_971539 node_context_11_72393_971539
  intro a
  fin_cases a
  · exact context_12_289572_971412
  · exact context_12_289573_971448
  · exact context_12_289574_971495
  · exact context_12_289575_971538

theorem selected_cut_36601 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 72394) = some ⟨11, 1, 0, 900587, 72394, 1, 262144⟩ := by
  decide +kernel

theorem context_11_72394_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72394 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 72394 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 72394, 1, 262144⟩
    (by decide) selected_cut_36601

theorem selected_cut_36602 : selected 9 ⟨971581, by decide⟩
    (prefixPartial 12 289580) = some ⟨12, 2, 0, 971581, 289580, 2849, 65536⟩ := by
  decide +kernel

theorem context_12_289580_971581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289580 ⟨971581, by decide⟩ :=
  accepted_of_selected 12 289580 ⟨971581, by decide⟩ ⟨12, 2, 0, 971581, 289580, 2849, 65536⟩
    (by decide) selected_cut_36602

theorem selected_cut_36603 : selected 9 ⟨971614, by decide⟩
    (prefixPartial 12 289581) = some ⟨12, 2, 0, 971614, 289581, 2649, 65536⟩ := by
  decide +kernel

theorem context_12_289581_971614 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289581 ⟨971614, by decide⟩ :=
  accepted_of_selected 12 289581 ⟨971614, by decide⟩ ⟨12, 2, 0, 971614, 289581, 2649, 65536⟩
    (by decide) selected_cut_36603

theorem selected_cut_36604 : selected 9 ⟨971665, by decide⟩
    (prefixPartial 12 289582) = some ⟨12, 2, 0, 971665, 289582, 3013, 65536⟩ := by
  decide +kernel

theorem context_12_289582_971665 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289582 ⟨971665, by decide⟩ :=
  accepted_of_selected 12 289582 ⟨971665, by decide⟩ ⟨12, 2, 0, 971665, 289582, 3013, 65536⟩
    (by decide) selected_cut_36604

theorem selected_cut_36605 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 289583) = some ⟨12, 1, 0, 903806, 289583, 1, 65536⟩ := by
  decide +kernel

theorem context_12_289583_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289583 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 289583 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 289583, 1, 65536⟩
    (by decide) selected_cut_36605

theorem unmarked_context_11_72395_971666 : frontier 10 ⟨971666, by decide⟩
    (prefixCache 11 72395) (prefixPartial 11 72395) = false := by
  decide +kernel

theorem node_context_11_72395_971666 : EJMOriginalGlobalDAGData.nodes 10 ⟨971666, by decide⟩ =
    .split (coordinate 11) (![⟨971581, by decide⟩,⟨971614, by decide⟩,⟨971665, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72395_971666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72395 ⟨971666, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72395
    ⟨971666, by decide⟩ (by decide) (![⟨971581, by decide⟩,⟨971614, by decide⟩,⟨971665, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_72395_971666 node_context_11_72395_971666
  intro a
  fin_cases a
  · exact context_12_289580_971581
  · exact context_12_289581_971614
  · exact context_12_289582_971665
  · exact context_12_289583_903806

theorem unmarked_context_10_18098_971667 : frontier 11 ⟨971667, by decide⟩
    (prefixCache 10 18098) (prefixPartial 10 18098) = false := by
  decide +kernel

theorem node_context_10_18098_971667 : EJMOriginalGlobalDAGData.nodes 11 ⟨971667, by decide⟩ =
    .split (coordinate 10) (![⟨971368, by decide⟩,⟨971539, by decide⟩,⟨900587, by decide⟩,⟨971666, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18098_971667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18098 ⟨971667, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18098
    ⟨971667, by decide⟩ (by decide) (![⟨971368, by decide⟩,⟨971539, by decide⟩,⟨900587, by decide⟩,⟨971666, by decide⟩]) unmarked_context_10_18098_971667 node_context_10_18098_971667
  intro a
  fin_cases a
  · exact context_11_72392_971368
  · exact context_11_72393_971539
  · exact context_11_72394_900587
  · exact context_11_72395_971666

theorem selected_cut_36606 : selected 9 ⟨971709, by decide⟩
    (prefixPartial 12 289584) = some ⟨12, 2, 0, 971709, 289584, 2929, 65536⟩ := by
  decide +kernel

theorem context_12_289584_971709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289584 ⟨971709, by decide⟩ :=
  accepted_of_selected 12 289584 ⟨971709, by decide⟩ ⟨12, 2, 0, 971709, 289584, 2929, 65536⟩
    (by decide) selected_cut_36606

theorem selected_cut_36607 : selected 9 ⟨971768, by decide⟩
    (prefixPartial 12 289585) = some ⟨12, 2, 0, 971768, 289585, 3205, 65536⟩ := by
  decide +kernel

theorem context_12_289585_971768 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289585 ⟨971768, by decide⟩ :=
  accepted_of_selected 12 289585 ⟨971768, by decide⟩ ⟨12, 2, 0, 971768, 289585, 3205, 65536⟩
    (by decide) selected_cut_36607

theorem selected_cut_36608 : selected 9 ⟨971825, by decide⟩
    (prefixPartial 12 289586) = some ⟨12, 2, 0, 971825, 289586, 3341, 65536⟩ := by
  decide +kernel

theorem context_12_289586_971825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289586 ⟨971825, by decide⟩ :=
  accepted_of_selected 12 289586 ⟨971825, by decide⟩ ⟨12, 2, 0, 971825, 289586, 3341, 65536⟩
    (by decide) selected_cut_36608

theorem selected_cut_36609 : selected 9 ⟨971888, by decide⟩
    (prefixPartial 12 289587) = some ⟨12, 2, 0, 971888, 289587, 3473, 65536⟩ := by
  decide +kernel

theorem context_12_289587_971888 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289587 ⟨971888, by decide⟩ :=
  accepted_of_selected 12 289587 ⟨971888, by decide⟩ ⟨12, 2, 0, 971888, 289587, 3473, 65536⟩
    (by decide) selected_cut_36609

theorem unmarked_context_11_72396_971889 : frontier 10 ⟨971889, by decide⟩
    (prefixCache 11 72396) (prefixPartial 11 72396) = false := by
  decide +kernel

theorem node_context_11_72396_971889 : EJMOriginalGlobalDAGData.nodes 10 ⟨971889, by decide⟩ =
    .split (coordinate 11) (![⟨971709, by decide⟩,⟨971768, by decide⟩,⟨971825, by decide⟩,⟨971888, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72396_971889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72396 ⟨971889, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72396
    ⟨971889, by decide⟩ (by decide) (![⟨971709, by decide⟩,⟨971768, by decide⟩,⟨971825, by decide⟩,⟨971888, by decide⟩]) unmarked_context_11_72396_971889 node_context_11_72396_971889
  intro a
  fin_cases a
  · exact context_12_289584_971709
  · exact context_12_289585_971768
  · exact context_12_289586_971825
  · exact context_12_289587_971888

theorem selected_cut_36610 : selected 9 ⟨971933, by decide⟩
    (prefixPartial 12 289588) = some ⟨12, 2, 0, 971933, 289588, 2865, 65536⟩ := by
  decide +kernel

theorem context_12_289588_971933 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289588 ⟨971933, by decide⟩ :=
  accepted_of_selected 12 289588 ⟨971933, by decide⟩ ⟨12, 2, 0, 971933, 289588, 2865, 65536⟩
    (by decide) selected_cut_36610

theorem selected_cut_36611 : selected 9 ⟨971977, by decide⟩
    (prefixPartial 12 289589) = some ⟨12, 2, 0, 971977, 289589, 2873, 65536⟩ := by
  decide +kernel

theorem context_12_289589_971977 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289589 ⟨971977, by decide⟩ :=
  accepted_of_selected 12 289589 ⟨971977, by decide⟩ ⟨12, 2, 0, 971977, 289589, 2873, 65536⟩
    (by decide) selected_cut_36611

theorem selected_cut_36612 : selected 9 ⟨972024, by decide⟩
    (prefixPartial 12 289590) = some ⟨12, 2, 0, 972024, 289590, 2873, 65536⟩ := by
  decide +kernel

theorem context_12_289590_972024 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289590 ⟨972024, by decide⟩ :=
  accepted_of_selected 12 289590 ⟨972024, by decide⟩ ⟨12, 2, 0, 972024, 289590, 2873, 65536⟩
    (by decide) selected_cut_36612

theorem selected_cut_36613 : selected 9 ⟨972072, by decide⟩
    (prefixPartial 12 289591) = some ⟨12, 2, 0, 972072, 289591, 2949, 65536⟩ := by
  decide +kernel

theorem context_12_289591_972072 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289591 ⟨972072, by decide⟩ :=
  accepted_of_selected 12 289591 ⟨972072, by decide⟩ ⟨12, 2, 0, 972072, 289591, 2949, 65536⟩
    (by decide) selected_cut_36613

theorem unmarked_context_11_72397_972073 : frontier 10 ⟨972073, by decide⟩
    (prefixCache 11 72397) (prefixPartial 11 72397) = false := by
  decide +kernel

theorem node_context_11_72397_972073 : EJMOriginalGlobalDAGData.nodes 10 ⟨972073, by decide⟩ =
    .split (coordinate 11) (![⟨971933, by decide⟩,⟨971977, by decide⟩,⟨972024, by decide⟩,⟨972072, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72397_972073 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72397 ⟨972073, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72397
    ⟨972073, by decide⟩ (by decide) (![⟨971933, by decide⟩,⟨971977, by decide⟩,⟨972024, by decide⟩,⟨972072, by decide⟩]) unmarked_context_11_72397_972073 node_context_11_72397_972073
  intro a
  fin_cases a
  · exact context_12_289588_971933
  · exact context_12_289589_971977
  · exact context_12_289590_972024
  · exact context_12_289591_972072

theorem selected_cut_36614 : selected 9 ⟨972139, by decide⟩
    (prefixPartial 12 289592) = some ⟨12, 2, 0, 972139, 289592, 3369, 65536⟩ := by
  decide +kernel

theorem context_12_289592_972139 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289592 ⟨972139, by decide⟩ :=
  accepted_of_selected 12 289592 ⟨972139, by decide⟩ ⟨12, 2, 0, 972139, 289592, 3369, 65536⟩
    (by decide) selected_cut_36614

theorem selected_cut_36615 : selected 9 ⟨972193, by decide⟩
    (prefixPartial 12 289593) = some ⟨12, 2, 0, 972193, 289593, 3165, 65536⟩ := by
  decide +kernel

theorem context_12_289593_972193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289593 ⟨972193, by decide⟩ :=
  accepted_of_selected 12 289593 ⟨972193, by decide⟩ ⟨12, 2, 0, 972193, 289593, 3165, 65536⟩
    (by decide) selected_cut_36615

theorem selected_cut_36616 : selected 9 ⟨972243, by decide⟩
    (prefixPartial 12 289594) = some ⟨12, 2, 0, 972243, 289594, 2913, 65536⟩ := by
  decide +kernel

theorem context_12_289594_972243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289594 ⟨972243, by decide⟩ :=
  accepted_of_selected 12 289594 ⟨972243, by decide⟩ ⟨12, 2, 0, 972243, 289594, 2913, 65536⟩
    (by decide) selected_cut_36616

theorem selected_cut_36617 : selected 9 ⟨972302, by decide⟩
    (prefixPartial 12 289595) = some ⟨12, 2, 0, 972302, 289595, 3197, 65536⟩ := by
  decide +kernel

theorem context_12_289595_972302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289595 ⟨972302, by decide⟩ :=
  accepted_of_selected 12 289595 ⟨972302, by decide⟩ ⟨12, 2, 0, 972302, 289595, 3197, 65536⟩
    (by decide) selected_cut_36617

theorem unmarked_context_11_72398_972303 : frontier 10 ⟨972303, by decide⟩
    (prefixCache 11 72398) (prefixPartial 11 72398) = false := by
  decide +kernel

theorem node_context_11_72398_972303 : EJMOriginalGlobalDAGData.nodes 10 ⟨972303, by decide⟩ =
    .split (coordinate 11) (![⟨972139, by decide⟩,⟨972193, by decide⟩,⟨972243, by decide⟩,⟨972302, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72398_972303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72398 ⟨972303, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72398
    ⟨972303, by decide⟩ (by decide) (![⟨972139, by decide⟩,⟨972193, by decide⟩,⟨972243, by decide⟩,⟨972302, by decide⟩]) unmarked_context_11_72398_972303 node_context_11_72398_972303
  intro a
  fin_cases a
  · exact context_12_289592_972139
  · exact context_12_289593_972193
  · exact context_12_289594_972243
  · exact context_12_289595_972302

theorem selected_cut_36618 : selected 9 ⟨972348, by decide⟩
    (prefixPartial 12 289596) = some ⟨12, 2, 0, 972348, 289596, 2669, 65536⟩ := by
  decide +kernel

theorem context_12_289596_972348 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289596 ⟨972348, by decide⟩ :=
  accepted_of_selected 12 289596 ⟨972348, by decide⟩ ⟨12, 2, 0, 972348, 289596, 2669, 65536⟩
    (by decide) selected_cut_36618

theorem selected_cut_36619 : selected 9 ⟨972390, by decide⟩
    (prefixPartial 12 289597) = some ⟨12, 2, 0, 972390, 289597, 2529, 65536⟩ := by
  decide +kernel

theorem context_12_289597_972390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289597 ⟨972390, by decide⟩ :=
  accepted_of_selected 12 289597 ⟨972390, by decide⟩ ⟨12, 2, 0, 972390, 289597, 2529, 65536⟩
    (by decide) selected_cut_36619

theorem selected_cut_36620 : selected 9 ⟨972436, by decide⟩
    (prefixPartial 12 289598) = some ⟨12, 2, 0, 972436, 289598, 2717, 65536⟩ := by
  decide +kernel

theorem context_12_289598_972436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289598 ⟨972436, by decide⟩ :=
  accepted_of_selected 12 289598 ⟨972436, by decide⟩ ⟨12, 2, 0, 972436, 289598, 2717, 65536⟩
    (by decide) selected_cut_36620

theorem selected_cut_36621 : selected 9 ⟨762109, by decide⟩
    (prefixPartial 12 289599) = some ⟨12, 1, 0, 762109, 289599, 1, 65536⟩ := by
  decide +kernel

theorem context_12_289599_762109 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289599 ⟨762109, by decide⟩ :=
  accepted_of_selected 12 289599 ⟨762109, by decide⟩ ⟨12, 1, 0, 762109, 289599, 1, 65536⟩
    (by decide) selected_cut_36621

theorem unmarked_context_11_72399_972437 : frontier 10 ⟨972437, by decide⟩
    (prefixCache 11 72399) (prefixPartial 11 72399) = false := by
  decide +kernel

theorem node_context_11_72399_972437 : EJMOriginalGlobalDAGData.nodes 10 ⟨972437, by decide⟩ =
    .split (coordinate 11) (![⟨972348, by decide⟩,⟨972390, by decide⟩,⟨972436, by decide⟩,⟨762109, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72399_972437 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72399 ⟨972437, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72399
    ⟨972437, by decide⟩ (by decide) (![⟨972348, by decide⟩,⟨972390, by decide⟩,⟨972436, by decide⟩,⟨762109, by decide⟩]) unmarked_context_11_72399_972437 node_context_11_72399_972437
  intro a
  fin_cases a
  · exact context_12_289596_972348
  · exact context_12_289597_972390
  · exact context_12_289598_972436
  · exact context_12_289599_762109

theorem unmarked_context_10_18099_972438 : frontier 11 ⟨972438, by decide⟩
    (prefixCache 10 18099) (prefixPartial 10 18099) = false := by
  decide +kernel

theorem node_context_10_18099_972438 : EJMOriginalGlobalDAGData.nodes 11 ⟨972438, by decide⟩ =
    .split (coordinate 10) (![⟨971889, by decide⟩,⟨972073, by decide⟩,⟨972303, by decide⟩,⟨972437, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18099_972438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18099 ⟨972438, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18099
    ⟨972438, by decide⟩ (by decide) (![⟨971889, by decide⟩,⟨972073, by decide⟩,⟨972303, by decide⟩,⟨972437, by decide⟩]) unmarked_context_10_18099_972438 node_context_10_18099_972438
  intro a
  fin_cases a
  · exact context_11_72396_971889
  · exact context_11_72397_972073
  · exact context_11_72398_972303
  · exact context_11_72399_972437

theorem unmarked_context_9_4524_972439 : frontier 12 ⟨972439, by decide⟩
    (prefixCache 9 4524) (prefixPartial 9 4524) = false := by
  decide +kernel

theorem node_context_9_4524_972439 : EJMOriginalGlobalDAGData.nodes 12 ⟨972439, by decide⟩ =
    .split (coordinate 9) (![⟨970378, by decide⟩,⟨971180, by decide⟩,⟨971667, by decide⟩,⟨972438, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4524_972439 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4524 ⟨972439, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4524
    ⟨972439, by decide⟩ (by decide) (![⟨970378, by decide⟩,⟨971180, by decide⟩,⟨971667, by decide⟩,⟨972438, by decide⟩]) unmarked_context_9_4524_972439 node_context_9_4524_972439
  intro a
  fin_cases a
  · exact context_10_18096_970378
  · exact context_10_18097_971180
  · exact context_10_18098_971667
  · exact context_10_18099_972438

theorem selected_cut_36622 : selected 9 ⟨972487, by decide⟩
    (prefixPartial 12 289600) = some ⟨12, 2, 0, 972487, 289600, 2753, 65536⟩ := by
  decide +kernel

theorem context_12_289600_972487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289600 ⟨972487, by decide⟩ :=
  accepted_of_selected 12 289600 ⟨972487, by decide⟩ ⟨12, 2, 0, 972487, 289600, 2753, 65536⟩
    (by decide) selected_cut_36622

theorem selected_cut_36623 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 289601) = some ⟨12, 1, 0, 896706, 289601, 1, 65536⟩ := by
  decide +kernel

theorem context_12_289601_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289601 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 289601 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 289601, 1, 65536⟩
    (by decide) selected_cut_36623

theorem selected_cut_36624 : selected 9 ⟨972537, by decide⟩
    (prefixPartial 12 289602) = some ⟨12, 2, 0, 972537, 289602, 2493, 65536⟩ := by
  decide +kernel

theorem context_12_289602_972537 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289602 ⟨972537, by decide⟩ :=
  accepted_of_selected 12 289602 ⟨972537, by decide⟩ ⟨12, 2, 0, 972537, 289602, 2493, 65536⟩
    (by decide) selected_cut_36624

theorem selected_cut_36625 : selected 9 ⟨972580, by decide⟩
    (prefixPartial 12 289603) = some ⟨12, 2, 0, 972580, 289603, 2557, 65536⟩ := by
  decide +kernel

theorem context_12_289603_972580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289603 ⟨972580, by decide⟩ :=
  accepted_of_selected 12 289603 ⟨972580, by decide⟩ ⟨12, 2, 0, 972580, 289603, 2557, 65536⟩
    (by decide) selected_cut_36625

theorem unmarked_context_11_72400_972581 : frontier 10 ⟨972581, by decide⟩
    (prefixCache 11 72400) (prefixPartial 11 72400) = false := by
  decide +kernel

theorem node_context_11_72400_972581 : EJMOriginalGlobalDAGData.nodes 10 ⟨972581, by decide⟩ =
    .split (coordinate 11) (![⟨972487, by decide⟩,⟨896706, by decide⟩,⟨972537, by decide⟩,⟨972580, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72400_972581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72400 ⟨972581, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72400
    ⟨972581, by decide⟩ (by decide) (![⟨972487, by decide⟩,⟨896706, by decide⟩,⟨972537, by decide⟩,⟨972580, by decide⟩]) unmarked_context_11_72400_972581 node_context_11_72400_972581
  intro a
  fin_cases a
  · exact context_12_289600_972487
  · exact context_12_289601_896706
  · exact context_12_289602_972537
  · exact context_12_289603_972580

theorem selected_cut_36626 : selected 9 ⟨972624, by decide⟩
    (prefixPartial 12 289604) = some ⟨12, 2, 0, 972624, 289604, 2601, 65536⟩ := by
  decide +kernel

theorem context_12_289604_972624 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289604 ⟨972624, by decide⟩ :=
  accepted_of_selected 12 289604 ⟨972624, by decide⟩ ⟨12, 2, 0, 972624, 289604, 2601, 65536⟩
    (by decide) selected_cut_36626

theorem selected_cut_36627 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 289605) = some ⟨12, 1, 0, 896706, 289605, 1, 65536⟩ := by
  decide +kernel

theorem context_12_289605_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289605 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 289605 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 289605, 1, 65536⟩
    (by decide) selected_cut_36627

theorem selected_cut_36628 : selected 9 ⟨972659, by decide⟩
    (prefixPartial 12 289606) = some ⟨12, 2, 0, 972659, 289606, 2269, 65536⟩ := by
  decide +kernel

theorem context_12_289606_972659 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289606 ⟨972659, by decide⟩ :=
  accepted_of_selected 12 289606 ⟨972659, by decide⟩ ⟨12, 2, 0, 972659, 289606, 2269, 65536⟩
    (by decide) selected_cut_36628

theorem selected_cut_36629 : selected 9 ⟨972697, by decide⟩
    (prefixPartial 12 289607) = some ⟨12, 2, 0, 972697, 289607, 2389, 65536⟩ := by
  decide +kernel

theorem context_12_289607_972697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289607 ⟨972697, by decide⟩ :=
  accepted_of_selected 12 289607 ⟨972697, by decide⟩ ⟨12, 2, 0, 972697, 289607, 2389, 65536⟩
    (by decide) selected_cut_36629

theorem unmarked_context_11_72401_972698 : frontier 10 ⟨972698, by decide⟩
    (prefixCache 11 72401) (prefixPartial 11 72401) = false := by
  decide +kernel

theorem node_context_11_72401_972698 : EJMOriginalGlobalDAGData.nodes 10 ⟨972698, by decide⟩ =
    .split (coordinate 11) (![⟨972624, by decide⟩,⟨896706, by decide⟩,⟨972659, by decide⟩,⟨972697, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72401_972698 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72401 ⟨972698, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72401
    ⟨972698, by decide⟩ (by decide) (![⟨972624, by decide⟩,⟨896706, by decide⟩,⟨972659, by decide⟩,⟨972697, by decide⟩]) unmarked_context_11_72401_972698 node_context_11_72401_972698
  intro a
  fin_cases a
  · exact context_12_289604_972624
  · exact context_12_289605_896706
  · exact context_12_289606_972659
  · exact context_12_289607_972697

theorem selected_cut_36630 : selected 9 ⟨972755, by decide⟩
    (prefixPartial 12 289608) = some ⟨12, 2, 0, 972755, 289608, 2869, 65536⟩ := by
  decide +kernel

theorem context_12_289608_972755 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289608 ⟨972755, by decide⟩ :=
  accepted_of_selected 12 289608 ⟨972755, by decide⟩ ⟨12, 2, 0, 972755, 289608, 2869, 65536⟩
    (by decide) selected_cut_36630

theorem selected_cut_36631 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 289609) = some ⟨12, 1, 0, 896706, 289609, 1, 65536⟩ := by
  decide +kernel

theorem context_12_289609_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289609 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 289609 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 289609, 1, 65536⟩
    (by decide) selected_cut_36631

theorem selected_cut_36632 : selected 9 ⟨972788, by decide⟩
    (prefixPartial 12 289610) = some ⟨12, 2, 0, 972788, 289610, 2217, 65536⟩ := by
  decide +kernel

theorem context_12_289610_972788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289610 ⟨972788, by decide⟩ :=
  accepted_of_selected 12 289610 ⟨972788, by decide⟩ ⟨12, 2, 0, 972788, 289610, 2217, 65536⟩
    (by decide) selected_cut_36632

theorem selected_cut_36633 : selected 9 ⟨972834, by decide⟩
    (prefixPartial 12 289611) = some ⟨12, 2, 0, 972834, 289611, 2413, 65536⟩ := by
  decide +kernel

theorem context_12_289611_972834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289611 ⟨972834, by decide⟩ :=
  accepted_of_selected 12 289611 ⟨972834, by decide⟩ ⟨12, 2, 0, 972834, 289611, 2413, 65536⟩
    (by decide) selected_cut_36633

theorem unmarked_context_11_72402_972835 : frontier 10 ⟨972835, by decide⟩
    (prefixCache 11 72402) (prefixPartial 11 72402) = false := by
  decide +kernel

theorem node_context_11_72402_972835 : EJMOriginalGlobalDAGData.nodes 10 ⟨972835, by decide⟩ =
    .split (coordinate 11) (![⟨972755, by decide⟩,⟨896706, by decide⟩,⟨972788, by decide⟩,⟨972834, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72402_972835 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72402 ⟨972835, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72402
    ⟨972835, by decide⟩ (by decide) (![⟨972755, by decide⟩,⟨896706, by decide⟩,⟨972788, by decide⟩,⟨972834, by decide⟩]) unmarked_context_11_72402_972835 node_context_11_72402_972835
  intro a
  fin_cases a
  · exact context_12_289608_972755
  · exact context_12_289609_896706
  · exact context_12_289610_972788
  · exact context_12_289611_972834

theorem selected_cut_36634 : selected 9 ⟨972872, by decide⟩
    (prefixPartial 12 289612) = some ⟨12, 2, 0, 972872, 289612, 2513, 65536⟩ := by
  decide +kernel

theorem context_12_289612_972872 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289612 ⟨972872, by decide⟩ :=
  accepted_of_selected 12 289612 ⟨972872, by decide⟩ ⟨12, 2, 0, 972872, 289612, 2513, 65536⟩
    (by decide) selected_cut_36634

theorem selected_cut_36635 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 289613) = some ⟨12, 1, 0, 896706, 289613, 1, 65536⟩ := by
  decide +kernel

theorem context_12_289613_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289613 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 289613 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 289613, 1, 65536⟩
    (by decide) selected_cut_36635

theorem selected_cut_36636 : selected 9 ⟨972912, by decide⟩
    (prefixPartial 12 289614) = some ⟨12, 2, 0, 972912, 289614, 2201, 65536⟩ := by
  decide +kernel

theorem context_12_289614_972912 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289614 ⟨972912, by decide⟩ :=
  accepted_of_selected 12 289614 ⟨972912, by decide⟩ ⟨12, 2, 0, 972912, 289614, 2201, 65536⟩
    (by decide) selected_cut_36636

theorem selected_cut_36637 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 289615) = some ⟨12, 1, 0, 903806, 289615, 1, 65536⟩ := by
  decide +kernel

theorem context_12_289615_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289615 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 289615 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 289615, 1, 65536⟩
    (by decide) selected_cut_36637

theorem unmarked_context_11_72403_972913 : frontier 10 ⟨972913, by decide⟩
    (prefixCache 11 72403) (prefixPartial 11 72403) = false := by
  decide +kernel

theorem node_context_11_72403_972913 : EJMOriginalGlobalDAGData.nodes 10 ⟨972913, by decide⟩ =
    .split (coordinate 11) (![⟨972872, by decide⟩,⟨896706, by decide⟩,⟨972912, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72403_972913 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72403 ⟨972913, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72403
    ⟨972913, by decide⟩ (by decide) (![⟨972872, by decide⟩,⟨896706, by decide⟩,⟨972912, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_72403_972913 node_context_11_72403_972913
  intro a
  fin_cases a
  · exact context_12_289612_972872
  · exact context_12_289613_896706
  · exact context_12_289614_972912
  · exact context_12_289615_903806

theorem unmarked_context_10_18100_972914 : frontier 11 ⟨972914, by decide⟩
    (prefixCache 10 18100) (prefixPartial 10 18100) = false := by
  decide +kernel

theorem node_context_10_18100_972914 : EJMOriginalGlobalDAGData.nodes 11 ⟨972914, by decide⟩ =
    .split (coordinate 10) (![⟨972581, by decide⟩,⟨972698, by decide⟩,⟨972835, by decide⟩,⟨972913, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18100_972914 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18100 ⟨972914, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18100
    ⟨972914, by decide⟩ (by decide) (![⟨972581, by decide⟩,⟨972698, by decide⟩,⟨972835, by decide⟩,⟨972913, by decide⟩]) unmarked_context_10_18100_972914 node_context_10_18100_972914
  intro a
  fin_cases a
  · exact context_11_72400_972581
  · exact context_11_72401_972698
  · exact context_11_72402_972835
  · exact context_11_72403_972913

theorem selected_cut_36638 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 18101) = some ⟨10, 1, 0, 893098, 18101, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_18101_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18101 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 18101 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 18101, 1, 1048576⟩
    (by decide) selected_cut_36638

theorem selected_cut_36639 : selected 9 ⟨972934, by decide⟩
    (prefixPartial 12 289632) = some ⟨12, 2, 0, 972934, 289632, 1777, 65536⟩ := by
  decide +kernel

theorem context_12_289632_972934 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289632 ⟨972934, by decide⟩ :=
  accepted_of_selected 12 289632 ⟨972934, by decide⟩ ⟨12, 2, 0, 972934, 289632, 1777, 65536⟩
    (by decide) selected_cut_36639

theorem selected_cut_36640 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 289633) = some ⟨12, 1, 0, 896706, 289633, 1, 65536⟩ := by
  decide +kernel

theorem context_12_289633_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289633 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 289633 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 289633, 1, 65536⟩
    (by decide) selected_cut_36640

theorem selected_cut_36641 : selected 9 ⟨972963, by decide⟩
    (prefixPartial 12 289634) = some ⟨12, 2, 0, 972963, 289634, 2005, 65536⟩ := by
  decide +kernel

theorem context_12_289634_972963 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289634 ⟨972963, by decide⟩ :=
  accepted_of_selected 12 289634 ⟨972963, by decide⟩ ⟨12, 2, 0, 972963, 289634, 2005, 65536⟩
    (by decide) selected_cut_36641

theorem selected_cut_36642 : selected 9 ⟨972994, by decide⟩
    (prefixPartial 12 289635) = some ⟨12, 2, 0, 972994, 289635, 1937, 65536⟩ := by
  decide +kernel

theorem context_12_289635_972994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289635 ⟨972994, by decide⟩ :=
  accepted_of_selected 12 289635 ⟨972994, by decide⟩ ⟨12, 2, 0, 972994, 289635, 1937, 65536⟩
    (by decide) selected_cut_36642

theorem unmarked_context_11_72408_972995 : frontier 10 ⟨972995, by decide⟩
    (prefixCache 11 72408) (prefixPartial 11 72408) = false := by
  decide +kernel

theorem node_context_11_72408_972995 : EJMOriginalGlobalDAGData.nodes 10 ⟨972995, by decide⟩ =
    .split (coordinate 11) (![⟨972934, by decide⟩,⟨896706, by decide⟩,⟨972963, by decide⟩,⟨972994, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72408_972995 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72408 ⟨972995, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72408
    ⟨972995, by decide⟩ (by decide) (![⟨972934, by decide⟩,⟨896706, by decide⟩,⟨972963, by decide⟩,⟨972994, by decide⟩]) unmarked_context_11_72408_972995 node_context_11_72408_972995
  intro a
  fin_cases a
  · exact context_12_289632_972934
  · exact context_12_289633_896706
  · exact context_12_289634_972963
  · exact context_12_289635_972994

theorem selected_cut_36643 : selected 9 ⟨973018, by decide⟩
    (prefixPartial 12 289636) = some ⟨12, 2, 0, 973018, 289636, 1789, 65536⟩ := by
  decide +kernel

theorem context_12_289636_973018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289636 ⟨973018, by decide⟩ :=
  accepted_of_selected 12 289636 ⟨973018, by decide⟩ ⟨12, 2, 0, 973018, 289636, 1789, 65536⟩
    (by decide) selected_cut_36643

theorem selected_cut_36644 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 289637) = some ⟨12, 1, 0, 896706, 289637, 1, 65536⟩ := by
  decide +kernel

theorem context_12_289637_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289637 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 289637 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 289637, 1, 65536⟩
    (by decide) selected_cut_36644

theorem selected_cut_36645 : selected 9 ⟨973043, by decide⟩
    (prefixPartial 12 289638) = some ⟨12, 2, 0, 973043, 289638, 1817, 65536⟩ := by
  decide +kernel

theorem context_12_289638_973043 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289638 ⟨973043, by decide⟩ :=
  accepted_of_selected 12 289638 ⟨973043, by decide⟩ ⟨12, 2, 0, 973043, 289638, 1817, 65536⟩
    (by decide) selected_cut_36645

theorem selected_cut_36646 : selected 9 ⟨973065, by decide⟩
    (prefixPartial 12 289639) = some ⟨12, 2, 0, 973065, 289639, 1757, 65536⟩ := by
  decide +kernel

theorem context_12_289639_973065 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289639 ⟨973065, by decide⟩ :=
  accepted_of_selected 12 289639 ⟨973065, by decide⟩ ⟨12, 2, 0, 973065, 289639, 1757, 65536⟩
    (by decide) selected_cut_36646

theorem unmarked_context_11_72409_973066 : frontier 10 ⟨973066, by decide⟩
    (prefixCache 11 72409) (prefixPartial 11 72409) = false := by
  decide +kernel

theorem node_context_11_72409_973066 : EJMOriginalGlobalDAGData.nodes 10 ⟨973066, by decide⟩ =
    .split (coordinate 11) (![⟨973018, by decide⟩,⟨896706, by decide⟩,⟨973043, by decide⟩,⟨973065, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72409_973066 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72409 ⟨973066, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72409
    ⟨973066, by decide⟩ (by decide) (![⟨973018, by decide⟩,⟨896706, by decide⟩,⟨973043, by decide⟩,⟨973065, by decide⟩]) unmarked_context_11_72409_973066 node_context_11_72409_973066
  intro a
  fin_cases a
  · exact context_12_289636_973018
  · exact context_12_289637_896706
  · exact context_12_289638_973043
  · exact context_12_289639_973065

theorem selected_cut_36647 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 72410) = some ⟨11, 1, 0, 900587, 72410, 1, 262144⟩ := by
  decide +kernel

theorem context_11_72410_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72410 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 72410 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 72410, 1, 262144⟩
    (by decide) selected_cut_36647

theorem selected_cut_36648 : selected 10 ⟨973117, by decide⟩
    (prefixPartial 11 72411) = some ⟨11, 2, 0, 973117, 72411, 3645, 262144⟩ := by
  decide +kernel

theorem context_11_72411_973117 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72411 ⟨973117, by decide⟩ :=
  accepted_of_selected 11 72411 ⟨973117, by decide⟩ ⟨11, 2, 0, 973117, 72411, 3645, 262144⟩
    (by decide) selected_cut_36648

theorem unmarked_context_10_18102_973118 : frontier 11 ⟨973118, by decide⟩
    (prefixCache 10 18102) (prefixPartial 10 18102) = false := by
  decide +kernel

theorem node_context_10_18102_973118 : EJMOriginalGlobalDAGData.nodes 11 ⟨973118, by decide⟩ =
    .split (coordinate 10) (![⟨972995, by decide⟩,⟨973066, by decide⟩,⟨900587, by decide⟩,⟨973117, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18102_973118 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18102 ⟨973118, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18102
    ⟨973118, by decide⟩ (by decide) (![⟨972995, by decide⟩,⟨973066, by decide⟩,⟨900587, by decide⟩,⟨973117, by decide⟩]) unmarked_context_10_18102_973118 node_context_10_18102_973118
  intro a
  fin_cases a
  · exact context_11_72408_972995
  · exact context_11_72409_973066
  · exact context_11_72410_900587
  · exact context_11_72411_973117

theorem selected_cut_36649 : selected 9 ⟨973139, by decide⟩
    (prefixPartial 12 289648) = some ⟨12, 2, 0, 973139, 289648, 1881, 65536⟩ := by
  decide +kernel

theorem context_12_289648_973139 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289648 ⟨973139, by decide⟩ :=
  accepted_of_selected 12 289648 ⟨973139, by decide⟩ ⟨12, 2, 0, 973139, 289648, 1881, 65536⟩
    (by decide) selected_cut_36649

theorem selected_cut_36650 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 289649) = some ⟨12, 1, 0, 896706, 289649, 1, 65536⟩ := by
  decide +kernel

theorem context_12_289649_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289649 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 289649 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 289649, 1, 65536⟩
    (by decide) selected_cut_36650

theorem selected_cut_36651 : selected 9 ⟨973173, by decide⟩
    (prefixPartial 12 289650) = some ⟨12, 2, 0, 973173, 289650, 2241, 65536⟩ := by
  decide +kernel

theorem context_12_289650_973173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289650 ⟨973173, by decide⟩ :=
  accepted_of_selected 12 289650 ⟨973173, by decide⟩ ⟨12, 2, 0, 973173, 289650, 2241, 65536⟩
    (by decide) selected_cut_36651

theorem selected_cut_36652 : selected 9 ⟨973203, by decide⟩
    (prefixPartial 12 289651) = some ⟨12, 2, 0, 973203, 289651, 2141, 65536⟩ := by
  decide +kernel

theorem context_12_289651_973203 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289651 ⟨973203, by decide⟩ :=
  accepted_of_selected 12 289651 ⟨973203, by decide⟩ ⟨12, 2, 0, 973203, 289651, 2141, 65536⟩
    (by decide) selected_cut_36652

theorem unmarked_context_11_72412_973204 : frontier 10 ⟨973204, by decide⟩
    (prefixCache 11 72412) (prefixPartial 11 72412) = false := by
  decide +kernel

theorem node_context_11_72412_973204 : EJMOriginalGlobalDAGData.nodes 10 ⟨973204, by decide⟩ =
    .split (coordinate 11) (![⟨973139, by decide⟩,⟨896706, by decide⟩,⟨973173, by decide⟩,⟨973203, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72412_973204 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72412 ⟨973204, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72412
    ⟨973204, by decide⟩ (by decide) (![⟨973139, by decide⟩,⟨896706, by decide⟩,⟨973173, by decide⟩,⟨973203, by decide⟩]) unmarked_context_11_72412_973204 node_context_11_72412_973204
  intro a
  fin_cases a
  · exact context_12_289648_973139
  · exact context_12_289649_896706
  · exact context_12_289650_973173
  · exact context_12_289651_973203

theorem selected_cut_36653 : selected 9 ⟨973227, by decide⟩
    (prefixPartial 12 289652) = some ⟨12, 2, 0, 973227, 289652, 1813, 65536⟩ := by
  decide +kernel

theorem context_12_289652_973227 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289652 ⟨973227, by decide⟩ :=
  accepted_of_selected 12 289652 ⟨973227, by decide⟩ ⟨12, 2, 0, 973227, 289652, 1813, 65536⟩
    (by decide) selected_cut_36653

theorem selected_cut_36654 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 289653) = some ⟨12, 1, 0, 896706, 289653, 1, 65536⟩ := by
  decide +kernel

theorem context_12_289653_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289653 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 289653 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 289653, 1, 65536⟩
    (by decide) selected_cut_36654

theorem selected_cut_36655 : selected 9 ⟨973255, by decide⟩
    (prefixPartial 12 289654) = some ⟨12, 2, 0, 973255, 289654, 1897, 65536⟩ := by
  decide +kernel

theorem context_12_289654_973255 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289654 ⟨973255, by decide⟩ :=
  accepted_of_selected 12 289654 ⟨973255, by decide⟩ ⟨12, 2, 0, 973255, 289654, 1897, 65536⟩
    (by decide) selected_cut_36655

theorem selected_cut_36656 : selected 9 ⟨973287, by decide⟩
    (prefixPartial 12 289655) = some ⟨12, 2, 0, 973287, 289655, 1913, 65536⟩ := by
  decide +kernel

theorem context_12_289655_973287 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289655 ⟨973287, by decide⟩ :=
  accepted_of_selected 12 289655 ⟨973287, by decide⟩ ⟨12, 2, 0, 973287, 289655, 1913, 65536⟩
    (by decide) selected_cut_36656

theorem unmarked_context_11_72413_973288 : frontier 10 ⟨973288, by decide⟩
    (prefixCache 11 72413) (prefixPartial 11 72413) = false := by
  decide +kernel

theorem node_context_11_72413_973288 : EJMOriginalGlobalDAGData.nodes 10 ⟨973288, by decide⟩ =
    .split (coordinate 11) (![⟨973227, by decide⟩,⟨896706, by decide⟩,⟨973255, by decide⟩,⟨973287, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72413_973288 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72413 ⟨973288, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72413
    ⟨973288, by decide⟩ (by decide) (![⟨973227, by decide⟩,⟨896706, by decide⟩,⟨973255, by decide⟩,⟨973287, by decide⟩]) unmarked_context_11_72413_973288 node_context_11_72413_973288
  intro a
  fin_cases a
  · exact context_12_289652_973227
  · exact context_12_289653_896706
  · exact context_12_289654_973255
  · exact context_12_289655_973287

theorem selected_cut_36657 : selected 9 ⟨973324, by decide⟩
    (prefixPartial 12 289656) = some ⟨12, 2, 0, 973324, 289656, 2101, 65536⟩ := by
  decide +kernel

theorem context_12_289656_973324 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289656 ⟨973324, by decide⟩ :=
  accepted_of_selected 12 289656 ⟨973324, by decide⟩ ⟨12, 2, 0, 973324, 289656, 2101, 65536⟩
    (by decide) selected_cut_36657

theorem selected_cut_36658 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 289657) = some ⟨12, 1, 0, 896706, 289657, 1, 65536⟩ := by
  decide +kernel

theorem context_12_289657_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289657 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 289657 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 289657, 1, 65536⟩
    (by decide) selected_cut_36658

theorem selected_cut_36659 : selected 9 ⟨973356, by decide⟩
    (prefixPartial 12 289658) = some ⟨12, 2, 0, 973356, 289658, 1833, 65536⟩ := by
  decide +kernel

theorem context_12_289658_973356 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289658 ⟨973356, by decide⟩ :=
  accepted_of_selected 12 289658 ⟨973356, by decide⟩ ⟨12, 2, 0, 973356, 289658, 1833, 65536⟩
    (by decide) selected_cut_36659

theorem selected_cut_36660 : selected 9 ⟨973392, by decide⟩
    (prefixPartial 12 289659) = some ⟨12, 2, 0, 973392, 289659, 2069, 65536⟩ := by
  decide +kernel

theorem context_12_289659_973392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289659 ⟨973392, by decide⟩ :=
  accepted_of_selected 12 289659 ⟨973392, by decide⟩ ⟨12, 2, 0, 973392, 289659, 2069, 65536⟩
    (by decide) selected_cut_36660

theorem unmarked_context_11_72414_973393 : frontier 10 ⟨973393, by decide⟩
    (prefixCache 11 72414) (prefixPartial 11 72414) = false := by
  decide +kernel

theorem node_context_11_72414_973393 : EJMOriginalGlobalDAGData.nodes 10 ⟨973393, by decide⟩ =
    .split (coordinate 11) (![⟨973324, by decide⟩,⟨896706, by decide⟩,⟨973356, by decide⟩,⟨973392, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72414_973393 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72414 ⟨973393, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72414
    ⟨973393, by decide⟩ (by decide) (![⟨973324, by decide⟩,⟨896706, by decide⟩,⟨973356, by decide⟩,⟨973392, by decide⟩]) unmarked_context_11_72414_973393 node_context_11_72414_973393
  intro a
  fin_cases a
  · exact context_12_289656_973324
  · exact context_12_289657_896706
  · exact context_12_289658_973356
  · exact context_12_289659_973392

theorem selected_cut_36661 : selected 10 ⟨973450, by decide⟩
    (prefixPartial 11 72415) = some ⟨11, 2, 0, 973450, 72415, 3569, 262144⟩ := by
  decide +kernel

theorem context_11_72415_973450 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72415 ⟨973450, by decide⟩ :=
  accepted_of_selected 11 72415 ⟨973450, by decide⟩ ⟨11, 2, 0, 973450, 72415, 3569, 262144⟩
    (by decide) selected_cut_36661

theorem unmarked_context_10_18103_973451 : frontier 11 ⟨973451, by decide⟩
    (prefixCache 10 18103) (prefixPartial 10 18103) = false := by
  decide +kernel

theorem node_context_10_18103_973451 : EJMOriginalGlobalDAGData.nodes 11 ⟨973451, by decide⟩ =
    .split (coordinate 10) (![⟨973204, by decide⟩,⟨973288, by decide⟩,⟨973393, by decide⟩,⟨973450, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18103_973451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18103 ⟨973451, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18103
    ⟨973451, by decide⟩ (by decide) (![⟨973204, by decide⟩,⟨973288, by decide⟩,⟨973393, by decide⟩,⟨973450, by decide⟩]) unmarked_context_10_18103_973451 node_context_10_18103_973451
  intro a
  fin_cases a
  · exact context_11_72412_973204
  · exact context_11_72413_973288
  · exact context_11_72414_973393
  · exact context_11_72415_973450

theorem unmarked_context_9_4525_973452 : frontier 12 ⟨973452, by decide⟩
    (prefixCache 9 4525) (prefixPartial 9 4525) = false := by
  decide +kernel

theorem node_context_9_4525_973452 : EJMOriginalGlobalDAGData.nodes 12 ⟨973452, by decide⟩ =
    .split (coordinate 9) (![⟨972914, by decide⟩,⟨893098, by decide⟩,⟨973118, by decide⟩,⟨973451, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4525_973452 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4525 ⟨973452, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4525
    ⟨973452, by decide⟩ (by decide) (![⟨972914, by decide⟩,⟨893098, by decide⟩,⟨973118, by decide⟩,⟨973451, by decide⟩]) unmarked_context_9_4525_973452 node_context_9_4525_973452
  intro a
  fin_cases a
  · exact context_10_18100_972914
  · exact context_10_18101_893098
  · exact context_10_18102_973118
  · exact context_10_18103_973451

theorem selected_cut_36662 : selected 9 ⟨973475, by decide⟩
    (prefixPartial 12 289664) = some ⟨12, 2, 0, 973475, 289664, 1841, 65536⟩ := by
  decide +kernel

theorem context_12_289664_973475 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289664 ⟨973475, by decide⟩ :=
  accepted_of_selected 12 289664 ⟨973475, by decide⟩ ⟨12, 2, 0, 973475, 289664, 1841, 65536⟩
    (by decide) selected_cut_36662

theorem selected_cut_36663 : selected 9 ⟨973501, by decide⟩
    (prefixPartial 12 289665) = some ⟨12, 2, 0, 973501, 289665, 1657, 65536⟩ := by
  decide +kernel

theorem context_12_289665_973501 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289665 ⟨973501, by decide⟩ :=
  accepted_of_selected 12 289665 ⟨973501, by decide⟩ ⟨12, 2, 0, 973501, 289665, 1657, 65536⟩
    (by decide) selected_cut_36663

theorem selected_cut_36664 : selected 9 ⟨973525, by decide⟩
    (prefixPartial 12 289666) = some ⟨12, 2, 0, 973525, 289666, 1545, 65536⟩ := by
  decide +kernel

theorem context_12_289666_973525 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289666 ⟨973525, by decide⟩ :=
  accepted_of_selected 12 289666 ⟨973525, by decide⟩ ⟨12, 2, 0, 973525, 289666, 1545, 65536⟩
    (by decide) selected_cut_36664

theorem selected_cut_36665 : selected 9 ⟨973546, by decide⟩
    (prefixPartial 12 289667) = some ⟨12, 2, 0, 973546, 289667, 1461, 65536⟩ := by
  decide +kernel

theorem context_12_289667_973546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289667 ⟨973546, by decide⟩ :=
  accepted_of_selected 12 289667 ⟨973546, by decide⟩ ⟨12, 2, 0, 973546, 289667, 1461, 65536⟩
    (by decide) selected_cut_36665

theorem unmarked_context_11_72416_973547 : frontier 10 ⟨973547, by decide⟩
    (prefixCache 11 72416) (prefixPartial 11 72416) = false := by
  decide +kernel

theorem node_context_11_72416_973547 : EJMOriginalGlobalDAGData.nodes 10 ⟨973547, by decide⟩ =
    .split (coordinate 11) (![⟨973475, by decide⟩,⟨973501, by decide⟩,⟨973525, by decide⟩,⟨973546, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72416_973547 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72416 ⟨973547, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72416
    ⟨973547, by decide⟩ (by decide) (![⟨973475, by decide⟩,⟨973501, by decide⟩,⟨973525, by decide⟩,⟨973546, by decide⟩]) unmarked_context_11_72416_973547 node_context_11_72416_973547
  intro a
  fin_cases a
  · exact context_12_289664_973475
  · exact context_12_289665_973501
  · exact context_12_289666_973525
  · exact context_12_289667_973546

theorem selected_cut_36666 : selected 9 ⟨973573, by decide⟩
    (prefixPartial 12 289668) = some ⟨12, 2, 0, 973573, 289668, 1897, 65536⟩ := by
  decide +kernel

theorem context_12_289668_973573 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289668 ⟨973573, by decide⟩ :=
  accepted_of_selected 12 289668 ⟨973573, by decide⟩ ⟨12, 2, 0, 973573, 289668, 1897, 65536⟩
    (by decide) selected_cut_36666

theorem selected_cut_36667 : selected 9 ⟨973598, by decide⟩
    (prefixPartial 12 289669) = some ⟨12, 2, 0, 973598, 289669, 1665, 65536⟩ := by
  decide +kernel

theorem context_12_289669_973598 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289669 ⟨973598, by decide⟩ :=
  accepted_of_selected 12 289669 ⟨973598, by decide⟩ ⟨12, 2, 0, 973598, 289669, 1665, 65536⟩
    (by decide) selected_cut_36667

theorem selected_cut_36668 : selected 9 ⟨973625, by decide⟩
    (prefixPartial 12 289670) = some ⟨12, 2, 0, 973625, 289670, 1597, 65536⟩ := by
  decide +kernel

theorem context_12_289670_973625 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289670 ⟨973625, by decide⟩ :=
  accepted_of_selected 12 289670 ⟨973625, by decide⟩ ⟨12, 2, 0, 973625, 289670, 1597, 65536⟩
    (by decide) selected_cut_36668

theorem selected_cut_36669 : selected 9 ⟨973648, by decide⟩
    (prefixPartial 12 289671) = some ⟨12, 2, 0, 973648, 289671, 1529, 65536⟩ := by
  decide +kernel

theorem context_12_289671_973648 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289671 ⟨973648, by decide⟩ :=
  accepted_of_selected 12 289671 ⟨973648, by decide⟩ ⟨12, 2, 0, 973648, 289671, 1529, 65536⟩
    (by decide) selected_cut_36669

theorem unmarked_context_11_72417_973649 : frontier 10 ⟨973649, by decide⟩
    (prefixCache 11 72417) (prefixPartial 11 72417) = false := by
  decide +kernel

theorem node_context_11_72417_973649 : EJMOriginalGlobalDAGData.nodes 10 ⟨973649, by decide⟩ =
    .split (coordinate 11) (![⟨973573, by decide⟩,⟨973598, by decide⟩,⟨973625, by decide⟩,⟨973648, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72417_973649 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72417 ⟨973649, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72417
    ⟨973649, by decide⟩ (by decide) (![⟨973573, by decide⟩,⟨973598, by decide⟩,⟨973625, by decide⟩,⟨973648, by decide⟩]) unmarked_context_11_72417_973649 node_context_11_72417_973649
  intro a
  fin_cases a
  · exact context_12_289668_973573
  · exact context_12_289669_973598
  · exact context_12_289670_973625
  · exact context_12_289671_973648

theorem selected_cut_36670 : selected 9 ⟨973686, by decide⟩
    (prefixPartial 12 289672) = some ⟨12, 2, 0, 973686, 289672, 2025, 65536⟩ := by
  decide +kernel

theorem context_12_289672_973686 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289672 ⟨973686, by decide⟩ :=
  accepted_of_selected 12 289672 ⟨973686, by decide⟩ ⟨12, 2, 0, 973686, 289672, 2025, 65536⟩
    (by decide) selected_cut_36670

theorem selected_cut_36671 : selected 9 ⟨973712, by decide⟩
    (prefixPartial 12 289673) = some ⟨12, 2, 0, 973712, 289673, 1653, 65536⟩ := by
  decide +kernel

theorem context_12_289673_973712 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289673 ⟨973712, by decide⟩ :=
  accepted_of_selected 12 289673 ⟨973712, by decide⟩ ⟨12, 2, 0, 973712, 289673, 1653, 65536⟩
    (by decide) selected_cut_36671

theorem selected_cut_36672 : selected 9 ⟨973733, by decide⟩
    (prefixPartial 12 289674) = some ⟨12, 2, 0, 973733, 289674, 1449, 65536⟩ := by
  decide +kernel

theorem context_12_289674_973733 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289674 ⟨973733, by decide⟩ :=
  accepted_of_selected 12 289674 ⟨973733, by decide⟩ ⟨12, 2, 0, 973733, 289674, 1449, 65536⟩
    (by decide) selected_cut_36672

theorem selected_cut_36673 : selected 9 ⟨973756, by decide⟩
    (prefixPartial 12 289675) = some ⟨12, 2, 0, 973756, 289675, 1525, 65536⟩ := by
  decide +kernel

theorem context_12_289675_973756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289675 ⟨973756, by decide⟩ :=
  accepted_of_selected 12 289675 ⟨973756, by decide⟩ ⟨12, 2, 0, 973756, 289675, 1525, 65536⟩
    (by decide) selected_cut_36673

theorem unmarked_context_11_72418_973757 : frontier 10 ⟨973757, by decide⟩
    (prefixCache 11 72418) (prefixPartial 11 72418) = false := by
  decide +kernel

theorem node_context_11_72418_973757 : EJMOriginalGlobalDAGData.nodes 10 ⟨973757, by decide⟩ =
    .split (coordinate 11) (![⟨973686, by decide⟩,⟨973712, by decide⟩,⟨973733, by decide⟩,⟨973756, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72418_973757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72418 ⟨973757, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72418
    ⟨973757, by decide⟩ (by decide) (![⟨973686, by decide⟩,⟨973712, by decide⟩,⟨973733, by decide⟩,⟨973756, by decide⟩]) unmarked_context_11_72418_973757 node_context_11_72418_973757
  intro a
  fin_cases a
  · exact context_12_289672_973686
  · exact context_12_289673_973712
  · exact context_12_289674_973733
  · exact context_12_289675_973756

theorem selected_cut_36674 : selected 9 ⟨973788, by decide⟩
    (prefixPartial 12 289676) = some ⟨12, 2, 0, 973788, 289676, 1897, 65536⟩ := by
  decide +kernel

theorem context_12_289676_973788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289676 ⟨973788, by decide⟩ :=
  accepted_of_selected 12 289676 ⟨973788, by decide⟩ ⟨12, 2, 0, 973788, 289676, 1897, 65536⟩
    (by decide) selected_cut_36674

theorem selected_cut_36675 : selected 9 ⟨973815, by decide⟩
    (prefixPartial 12 289677) = some ⟨12, 2, 0, 973815, 289677, 1549, 65536⟩ := by
  decide +kernel

theorem context_12_289677_973815 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 289677 ⟨973815, by decide⟩ :=
  accepted_of_selected 12 289677 ⟨973815, by decide⟩ ⟨12, 2, 0, 973815, 289677, 1549, 65536⟩
    (by decide) selected_cut_36675

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
