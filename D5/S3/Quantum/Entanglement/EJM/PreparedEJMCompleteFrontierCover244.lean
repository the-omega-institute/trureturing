/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover243
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_11_19095_593243 : frontier 10 ⟨593243, by decide⟩
    (prefixCache 11 19095) (prefixPartial 11 19095) = false := by
  decide +kernel

theorem node_context_11_19095_593243 : EJMOriginalGlobalDAGData.nodes 10 ⟨593243, by decide⟩ =
    .split (coordinate 11) (![⟨593082, by decide⟩,⟨593130, by decide⟩,⟨593186, by decide⟩,⟨593242, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19095_593243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19095 ⟨593243, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19095
    ⟨593243, by decide⟩ (by decide) (![⟨593082, by decide⟩,⟨593130, by decide⟩,⟨593186, by decide⟩,⟨593242, by decide⟩]) unmarked_context_11_19095_593243 node_context_11_19095_593243
  intro a
  fin_cases a
  · exact context_12_76380_593082
  · exact context_12_76381_593130
  · exact context_12_76382_593186
  · exact context_12_76383_593242

theorem unmarked_context_10_4773_593244 : frontier 11 ⟨593244, by decide⟩
    (prefixCache 10 4773) (prefixPartial 10 4773) = false := by
  decide +kernel

theorem node_context_10_4773_593244 : EJMOriginalGlobalDAGData.nodes 11 ⟨593244, by decide⟩ =
    .split (coordinate 10) (![⟨592676, by decide⟩,⟨592890, by decide⟩,⟨593034, by decide⟩,⟨593243, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4773_593244 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4773 ⟨593244, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4773
    ⟨593244, by decide⟩ (by decide) (![⟨592676, by decide⟩,⟨592890, by decide⟩,⟨593034, by decide⟩,⟨593243, by decide⟩]) unmarked_context_10_4773_593244 node_context_10_4773_593244
  intro a
  fin_cases a
  · exact context_11_19092_592676
  · exact context_11_19093_592890
  · exact context_11_19094_593034
  · exact context_11_19095_593243

theorem selected_cut_23428 : selected 9 ⟨593285, by decide⟩
    (prefixPartial 12 76384) = some ⟨12, 2, 0, 593285, 76384, 3173, 65536⟩ := by
  decide +kernel

theorem context_12_76384_593285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76384 ⟨593285, by decide⟩ :=
  accepted_of_selected 12 76384 ⟨593285, by decide⟩ ⟨12, 2, 0, 593285, 76384, 3173, 65536⟩
    (by decide) selected_cut_23428

theorem selected_cut_23429 : selected 9 ⟨593319, by decide⟩
    (prefixPartial 12 76385) = some ⟨12, 2, 0, 593319, 76385, 3073, 65536⟩ := by
  decide +kernel

theorem context_12_76385_593319 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76385 ⟨593319, by decide⟩ :=
  accepted_of_selected 12 76385 ⟨593319, by decide⟩ ⟨12, 2, 0, 593319, 76385, 3073, 65536⟩
    (by decide) selected_cut_23429

theorem selected_cut_23430 : selected 9 ⟨593353, by decide⟩
    (prefixPartial 12 76386) = some ⟨12, 2, 0, 593353, 76386, 2693, 65536⟩ := by
  decide +kernel

theorem context_12_76386_593353 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76386 ⟨593353, by decide⟩ :=
  accepted_of_selected 12 76386 ⟨593353, by decide⟩ ⟨12, 2, 0, 593353, 76386, 2693, 65536⟩
    (by decide) selected_cut_23430

theorem selected_cut_23431 : selected 9 ⟨593400, by decide⟩
    (prefixPartial 12 76387) = some ⟨12, 2, 0, 593400, 76387, 3837, 65536⟩ := by
  decide +kernel

theorem context_12_76387_593400 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76387 ⟨593400, by decide⟩ :=
  accepted_of_selected 12 76387 ⟨593400, by decide⟩ ⟨12, 2, 0, 593400, 76387, 3837, 65536⟩
    (by decide) selected_cut_23431

theorem unmarked_context_11_19096_593401 : frontier 10 ⟨593401, by decide⟩
    (prefixCache 11 19096) (prefixPartial 11 19096) = false := by
  decide +kernel

theorem node_context_11_19096_593401 : EJMOriginalGlobalDAGData.nodes 10 ⟨593401, by decide⟩ =
    .split (coordinate 11) (![⟨593285, by decide⟩,⟨593319, by decide⟩,⟨593353, by decide⟩,⟨593400, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19096_593401 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19096 ⟨593401, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19096
    ⟨593401, by decide⟩ (by decide) (![⟨593285, by decide⟩,⟨593319, by decide⟩,⟨593353, by decide⟩,⟨593400, by decide⟩]) unmarked_context_11_19096_593401 node_context_11_19096_593401
  intro a
  fin_cases a
  · exact context_12_76384_593285
  · exact context_12_76385_593319
  · exact context_12_76386_593353
  · exact context_12_76387_593400

theorem selected_cut_23432 : selected 9 ⟨593443, by decide⟩
    (prefixPartial 12 76388) = some ⟨12, 2, 0, 593443, 76388, 3377, 65536⟩ := by
  decide +kernel

theorem context_12_76388_593443 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76388 ⟨593443, by decide⟩ :=
  accepted_of_selected 12 76388 ⟨593443, by decide⟩ ⟨12, 2, 0, 593443, 76388, 3377, 65536⟩
    (by decide) selected_cut_23432

theorem selected_cut_23433 : selected 9 ⟨593478, by decide⟩
    (prefixPartial 12 76389) = some ⟨12, 2, 0, 593478, 76389, 3061, 65536⟩ := by
  decide +kernel

theorem context_12_76389_593478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76389 ⟨593478, by decide⟩ :=
  accepted_of_selected 12 76389 ⟨593478, by decide⟩ ⟨12, 2, 0, 593478, 76389, 3061, 65536⟩
    (by decide) selected_cut_23433

theorem selected_cut_23434 : selected 9 ⟨593515, by decide⟩
    (prefixPartial 12 76390) = some ⟨12, 2, 0, 593515, 76390, 2909, 65536⟩ := by
  decide +kernel

theorem context_12_76390_593515 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76390 ⟨593515, by decide⟩ :=
  accepted_of_selected 12 76390 ⟨593515, by decide⟩ ⟨12, 2, 0, 593515, 76390, 2909, 65536⟩
    (by decide) selected_cut_23434

theorem selected_cut_23435 : selected 9 ⟨593562, by decide⟩
    (prefixPartial 12 76391) = some ⟨12, 2, 0, 593562, 76391, 3837, 65536⟩ := by
  decide +kernel

theorem context_12_76391_593562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76391 ⟨593562, by decide⟩ :=
  accepted_of_selected 12 76391 ⟨593562, by decide⟩ ⟨12, 2, 0, 593562, 76391, 3837, 65536⟩
    (by decide) selected_cut_23435

theorem unmarked_context_11_19097_593563 : frontier 10 ⟨593563, by decide⟩
    (prefixCache 11 19097) (prefixPartial 11 19097) = false := by
  decide +kernel

theorem node_context_11_19097_593563 : EJMOriginalGlobalDAGData.nodes 10 ⟨593563, by decide⟩ =
    .split (coordinate 11) (![⟨593443, by decide⟩,⟨593478, by decide⟩,⟨593515, by decide⟩,⟨593562, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19097_593563 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19097 ⟨593563, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19097
    ⟨593563, by decide⟩ (by decide) (![⟨593443, by decide⟩,⟨593478, by decide⟩,⟨593515, by decide⟩,⟨593562, by decide⟩]) unmarked_context_11_19097_593563 node_context_11_19097_593563
  intro a
  fin_cases a
  · exact context_12_76388_593443
  · exact context_12_76389_593478
  · exact context_12_76390_593515
  · exact context_12_76391_593562

theorem selected_cut_23436 : selected 9 ⟨93922, by decide⟩
    (prefixPartial 12 76392) = some ⟨12, 1, 0, 93922, 76392, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76392_93922 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76392 ⟨93922, by decide⟩ :=
  accepted_of_selected 12 76392 ⟨93922, by decide⟩ ⟨12, 1, 0, 93922, 76392, 1, 65536⟩
    (by decide) selected_cut_23436

theorem selected_cut_23437 : selected 9 ⟨364560, by decide⟩
    (prefixPartial 12 76393) = some ⟨12, 1, 0, 364560, 76393, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76393_364560 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76393 ⟨364560, by decide⟩ :=
  accepted_of_selected 12 76393 ⟨364560, by decide⟩ ⟨12, 1, 0, 364560, 76393, 1, 65536⟩
    (by decide) selected_cut_23437

theorem selected_cut_23438 : selected 9 ⟨474208, by decide⟩
    (prefixPartial 12 76394) = some ⟨12, 1, 0, 474208, 76394, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76394_474208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76394 ⟨474208, by decide⟩ :=
  accepted_of_selected 12 76394 ⟨474208, by decide⟩ ⟨12, 1, 0, 474208, 76394, 1, 65536⟩
    (by decide) selected_cut_23438

theorem selected_cut_23439 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 305580) = some ⟨13, 1, 0, 3444, 305580, 1, 16384⟩ := by
  decide +kernel

theorem context_13_305580_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305580 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 305580 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 305580, 1, 16384⟩
    (by decide) selected_cut_23439

theorem selected_cut_23440 : selected 8 ⟨593577, by decide⟩
    (prefixPartial 13 305581) = some ⟨13, 2, 0, 593577, 305581, 1137, 16384⟩ := by
  decide +kernel

theorem context_13_305581_593577 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305581 ⟨593577, by decide⟩ :=
  accepted_of_selected 13 305581 ⟨593577, by decide⟩ ⟨13, 2, 0, 593577, 305581, 1137, 16384⟩
    (by decide) selected_cut_23440

theorem selected_cut_23441 : selected 8 ⟨593603, by decide⟩
    (prefixPartial 13 305582) = some ⟨13, 2, 0, 593603, 305582, 2117, 16384⟩ := by
  decide +kernel

theorem context_13_305582_593603 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305582 ⟨593603, by decide⟩ :=
  accepted_of_selected 13 305582 ⟨593603, by decide⟩ ⟨13, 2, 0, 593603, 305582, 2117, 16384⟩
    (by decide) selected_cut_23441

theorem selected_cut_23442 : selected 8 ⟨593616, by decide⟩
    (prefixPartial 13 305583) = some ⟨13, 2, 0, 593616, 305583, 1117, 16384⟩ := by
  decide +kernel

theorem context_13_305583_593616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305583 ⟨593616, by decide⟩ :=
  accepted_of_selected 13 305583 ⟨593616, by decide⟩ ⟨13, 2, 0, 593616, 305583, 1117, 16384⟩
    (by decide) selected_cut_23442

theorem unmarked_context_12_76395_593617 : frontier 9 ⟨593617, by decide⟩
    (prefixCache 12 76395) (prefixPartial 12 76395) = false := by
  decide +kernel

theorem node_context_12_76395_593617 : EJMOriginalGlobalDAGData.nodes 9 ⟨593617, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨593577, by decide⟩,⟨593603, by decide⟩,⟨593616, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76395_593617 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76395 ⟨593617, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76395
    ⟨593617, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨593577, by decide⟩,⟨593603, by decide⟩,⟨593616, by decide⟩]) unmarked_context_12_76395_593617 node_context_12_76395_593617
  intro a
  fin_cases a
  · exact context_13_305580_3444
  · exact context_13_305581_593577
  · exact context_13_305582_593603
  · exact context_13_305583_593616

theorem unmarked_context_11_19098_593618 : frontier 10 ⟨593618, by decide⟩
    (prefixCache 11 19098) (prefixPartial 11 19098) = false := by
  decide +kernel

theorem node_context_11_19098_593618 : EJMOriginalGlobalDAGData.nodes 10 ⟨593618, by decide⟩ =
    .split (coordinate 11) (![⟨93922, by decide⟩,⟨364560, by decide⟩,⟨474208, by decide⟩,⟨593617, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19098_593618 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19098 ⟨593618, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19098
    ⟨593618, by decide⟩ (by decide) (![⟨93922, by decide⟩,⟨364560, by decide⟩,⟨474208, by decide⟩,⟨593617, by decide⟩]) unmarked_context_11_19098_593618 node_context_11_19098_593618
  intro a
  fin_cases a
  · exact context_12_76392_93922
  · exact context_12_76393_364560
  · exact context_12_76394_474208
  · exact context_12_76395_593617

theorem selected_cut_23443 : selected 9 ⟨593658, by decide⟩
    (prefixPartial 12 76396) = some ⟨12, 2, 0, 593658, 76396, 3301, 65536⟩ := by
  decide +kernel

theorem context_12_76396_593658 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76396 ⟨593658, by decide⟩ :=
  accepted_of_selected 12 76396 ⟨593658, by decide⟩ ⟨12, 2, 0, 593658, 76396, 3301, 65536⟩
    (by decide) selected_cut_23443

theorem selected_cut_23444 : selected 9 ⟨593693, by decide⟩
    (prefixPartial 12 76397) = some ⟨12, 2, 0, 593693, 76397, 2869, 65536⟩ := by
  decide +kernel

theorem context_12_76397_593693 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76397 ⟨593693, by decide⟩ :=
  accepted_of_selected 12 76397 ⟨593693, by decide⟩ ⟨12, 2, 0, 593693, 76397, 2869, 65536⟩
    (by decide) selected_cut_23444

theorem selected_cut_23445 : selected 9 ⟨593728, by decide⟩
    (prefixPartial 12 76398) = some ⟨12, 2, 0, 593728, 76398, 2649, 65536⟩ := by
  decide +kernel

theorem context_12_76398_593728 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76398 ⟨593728, by decide⟩ :=
  accepted_of_selected 12 76398 ⟨593728, by decide⟩ ⟨12, 2, 0, 593728, 76398, 2649, 65536⟩
    (by decide) selected_cut_23445

theorem selected_cut_23446 : selected 9 ⟨593761, by decide⟩
    (prefixPartial 12 76399) = some ⟨12, 2, 0, 593761, 76399, 3553, 65536⟩ := by
  decide +kernel

theorem context_12_76399_593761 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76399 ⟨593761, by decide⟩ :=
  accepted_of_selected 12 76399 ⟨593761, by decide⟩ ⟨12, 2, 0, 593761, 76399, 3553, 65536⟩
    (by decide) selected_cut_23446

theorem unmarked_context_11_19099_593762 : frontier 10 ⟨593762, by decide⟩
    (prefixCache 11 19099) (prefixPartial 11 19099) = false := by
  decide +kernel

theorem node_context_11_19099_593762 : EJMOriginalGlobalDAGData.nodes 10 ⟨593762, by decide⟩ =
    .split (coordinate 11) (![⟨593658, by decide⟩,⟨593693, by decide⟩,⟨593728, by decide⟩,⟨593761, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19099_593762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19099 ⟨593762, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19099
    ⟨593762, by decide⟩ (by decide) (![⟨593658, by decide⟩,⟨593693, by decide⟩,⟨593728, by decide⟩,⟨593761, by decide⟩]) unmarked_context_11_19099_593762 node_context_11_19099_593762
  intro a
  fin_cases a
  · exact context_12_76396_593658
  · exact context_12_76397_593693
  · exact context_12_76398_593728
  · exact context_12_76399_593761

theorem unmarked_context_10_4774_593763 : frontier 11 ⟨593763, by decide⟩
    (prefixCache 10 4774) (prefixPartial 10 4774) = false := by
  decide +kernel

theorem node_context_10_4774_593763 : EJMOriginalGlobalDAGData.nodes 11 ⟨593763, by decide⟩ =
    .split (coordinate 10) (![⟨593401, by decide⟩,⟨593563, by decide⟩,⟨593618, by decide⟩,⟨593762, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4774_593763 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4774 ⟨593763, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4774
    ⟨593763, by decide⟩ (by decide) (![⟨593401, by decide⟩,⟨593563, by decide⟩,⟨593618, by decide⟩,⟨593762, by decide⟩]) unmarked_context_10_4774_593763 node_context_10_4774_593763
  intro a
  fin_cases a
  · exact context_11_19096_593401
  · exact context_11_19097_593563
  · exact context_11_19098_593618
  · exact context_11_19099_593762

theorem selected_cut_23447 : selected 9 ⟨593802, by decide⟩
    (prefixPartial 12 76400) = some ⟨12, 2, 0, 593802, 76400, 2649, 65536⟩ := by
  decide +kernel

theorem context_12_76400_593802 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76400 ⟨593802, by decide⟩ :=
  accepted_of_selected 12 76400 ⟨593802, by decide⟩ ⟨12, 2, 0, 593802, 76400, 2649, 65536⟩
    (by decide) selected_cut_23447

theorem selected_cut_23448 : selected 9 ⟨593837, by decide⟩
    (prefixPartial 12 76401) = some ⟨12, 2, 0, 593837, 76401, 2809, 65536⟩ := by
  decide +kernel

theorem context_12_76401_593837 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76401 ⟨593837, by decide⟩ :=
  accepted_of_selected 12 76401 ⟨593837, by decide⟩ ⟨12, 2, 0, 593837, 76401, 2809, 65536⟩
    (by decide) selected_cut_23448

theorem selected_cut_23449 : selected 9 ⟨593875, by decide⟩
    (prefixPartial 12 76402) = some ⟨12, 2, 0, 593875, 76402, 2885, 65536⟩ := by
  decide +kernel

theorem context_12_76402_593875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76402 ⟨593875, by decide⟩ :=
  accepted_of_selected 12 76402 ⟨593875, by decide⟩ ⟨12, 2, 0, 593875, 76402, 2885, 65536⟩
    (by decide) selected_cut_23449

theorem selected_cut_23450 : selected 9 ⟨593923, by decide⟩
    (prefixPartial 12 76403) = some ⟨12, 2, 0, 593923, 76403, 3169, 65536⟩ := by
  decide +kernel

theorem context_12_76403_593923 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76403 ⟨593923, by decide⟩ :=
  accepted_of_selected 12 76403 ⟨593923, by decide⟩ ⟨12, 2, 0, 593923, 76403, 3169, 65536⟩
    (by decide) selected_cut_23450

theorem unmarked_context_11_19100_593924 : frontier 10 ⟨593924, by decide⟩
    (prefixCache 11 19100) (prefixPartial 11 19100) = false := by
  decide +kernel

theorem node_context_11_19100_593924 : EJMOriginalGlobalDAGData.nodes 10 ⟨593924, by decide⟩ =
    .split (coordinate 11) (![⟨593802, by decide⟩,⟨593837, by decide⟩,⟨593875, by decide⟩,⟨593923, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19100_593924 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19100 ⟨593924, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19100
    ⟨593924, by decide⟩ (by decide) (![⟨593802, by decide⟩,⟨593837, by decide⟩,⟨593875, by decide⟩,⟨593923, by decide⟩]) unmarked_context_11_19100_593924 node_context_11_19100_593924
  intro a
  fin_cases a
  · exact context_12_76400_593802
  · exact context_12_76401_593837
  · exact context_12_76402_593875
  · exact context_12_76403_593923

theorem selected_cut_23451 : selected 9 ⟨593960, by decide⟩
    (prefixPartial 12 76404) = some ⟨12, 2, 0, 593960, 76404, 2681, 65536⟩ := by
  decide +kernel

theorem context_12_76404_593960 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76404 ⟨593960, by decide⟩ :=
  accepted_of_selected 12 76404 ⟨593960, by decide⟩ ⟨12, 2, 0, 593960, 76404, 2681, 65536⟩
    (by decide) selected_cut_23451

theorem selected_cut_23452 : selected 9 ⟨593989, by decide⟩
    (prefixPartial 12 76405) = some ⟨12, 2, 0, 593989, 76405, 2585, 65536⟩ := by
  decide +kernel

theorem context_12_76405_593989 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76405 ⟨593989, by decide⟩ :=
  accepted_of_selected 12 76405 ⟨593989, by decide⟩ ⟨12, 2, 0, 593989, 76405, 2585, 65536⟩
    (by decide) selected_cut_23452

theorem selected_cut_23453 : selected 9 ⟨594027, by decide⟩
    (prefixPartial 12 76406) = some ⟨12, 2, 0, 594027, 76406, 2877, 65536⟩ := by
  decide +kernel

theorem context_12_76406_594027 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76406 ⟨594027, by decide⟩ :=
  accepted_of_selected 12 76406 ⟨594027, by decide⟩ ⟨12, 2, 0, 594027, 76406, 2877, 65536⟩
    (by decide) selected_cut_23453

theorem selected_cut_23454 : selected 9 ⟨594076, by decide⟩
    (prefixPartial 12 76407) = some ⟨12, 2, 0, 594076, 76407, 3217, 65536⟩ := by
  decide +kernel

theorem context_12_76407_594076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76407 ⟨594076, by decide⟩ :=
  accepted_of_selected 12 76407 ⟨594076, by decide⟩ ⟨12, 2, 0, 594076, 76407, 3217, 65536⟩
    (by decide) selected_cut_23454

theorem unmarked_context_11_19101_594077 : frontier 10 ⟨594077, by decide⟩
    (prefixCache 11 19101) (prefixPartial 11 19101) = false := by
  decide +kernel

theorem node_context_11_19101_594077 : EJMOriginalGlobalDAGData.nodes 10 ⟨594077, by decide⟩ =
    .split (coordinate 11) (![⟨593960, by decide⟩,⟨593989, by decide⟩,⟨594027, by decide⟩,⟨594076, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19101_594077 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19101 ⟨594077, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19101
    ⟨594077, by decide⟩ (by decide) (![⟨593960, by decide⟩,⟨593989, by decide⟩,⟨594027, by decide⟩,⟨594076, by decide⟩]) unmarked_context_11_19101_594077 node_context_11_19101_594077
  intro a
  fin_cases a
  · exact context_12_76404_593960
  · exact context_12_76405_593989
  · exact context_12_76406_594027
  · exact context_12_76407_594076

theorem selected_cut_23455 : selected 9 ⟨594108, by decide⟩
    (prefixPartial 12 76408) = some ⟨12, 2, 0, 594108, 76408, 2353, 65536⟩ := by
  decide +kernel

theorem context_12_76408_594108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76408 ⟨594108, by decide⟩ :=
  accepted_of_selected 12 76408 ⟨594108, by decide⟩ ⟨12, 2, 0, 594108, 76408, 2353, 65536⟩
    (by decide) selected_cut_23455

theorem selected_cut_23456 : selected 9 ⟨594138, by decide⟩
    (prefixPartial 12 76409) = some ⟨12, 2, 0, 594138, 76409, 2405, 65536⟩ := by
  decide +kernel

theorem context_12_76409_594138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76409 ⟨594138, by decide⟩ :=
  accepted_of_selected 12 76409 ⟨594138, by decide⟩ ⟨12, 2, 0, 594138, 76409, 2405, 65536⟩
    (by decide) selected_cut_23456

theorem selected_cut_23457 : selected 9 ⟨594214, by decide⟩
    (prefixPartial 12 76410) = some ⟨12, 2, 0, 594214, 76410, 4001, 65536⟩ := by
  decide +kernel

theorem context_12_76410_594214 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76410 ⟨594214, by decide⟩ :=
  accepted_of_selected 12 76410 ⟨594214, by decide⟩ ⟨12, 2, 0, 594214, 76410, 4001, 65536⟩
    (by decide) selected_cut_23457

theorem selected_cut_23458 : selected 9 ⟨594248, by decide⟩
    (prefixPartial 12 76411) = some ⟨12, 2, 0, 594248, 76411, 2465, 65536⟩ := by
  decide +kernel

theorem context_12_76411_594248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76411 ⟨594248, by decide⟩ :=
  accepted_of_selected 12 76411 ⟨594248, by decide⟩ ⟨12, 2, 0, 594248, 76411, 2465, 65536⟩
    (by decide) selected_cut_23458

theorem unmarked_context_11_19102_594249 : frontier 10 ⟨594249, by decide⟩
    (prefixCache 11 19102) (prefixPartial 11 19102) = false := by
  decide +kernel

theorem node_context_11_19102_594249 : EJMOriginalGlobalDAGData.nodes 10 ⟨594249, by decide⟩ =
    .split (coordinate 11) (![⟨594108, by decide⟩,⟨594138, by decide⟩,⟨594214, by decide⟩,⟨594248, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19102_594249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19102 ⟨594249, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19102
    ⟨594249, by decide⟩ (by decide) (![⟨594108, by decide⟩,⟨594138, by decide⟩,⟨594214, by decide⟩,⟨594248, by decide⟩]) unmarked_context_11_19102_594249 node_context_11_19102_594249
  intro a
  fin_cases a
  · exact context_12_76408_594108
  · exact context_12_76409_594138
  · exact context_12_76410_594214
  · exact context_12_76411_594248

theorem selected_cut_23459 : selected 9 ⟨594277, by decide⟩
    (prefixPartial 12 76412) = some ⟨12, 2, 0, 594277, 76412, 2297, 65536⟩ := by
  decide +kernel

theorem context_12_76412_594277 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76412 ⟨594277, by decide⟩ :=
  accepted_of_selected 12 76412 ⟨594277, by decide⟩ ⟨12, 2, 0, 594277, 76412, 2297, 65536⟩
    (by decide) selected_cut_23459

theorem selected_cut_23460 : selected 9 ⟨594302, by decide⟩
    (prefixPartial 12 76413) = some ⟨12, 2, 0, 594302, 76413, 2185, 65536⟩ := by
  decide +kernel

theorem context_12_76413_594302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76413 ⟨594302, by decide⟩ :=
  accepted_of_selected 12 76413 ⟨594302, by decide⟩ ⟨12, 2, 0, 594302, 76413, 2185, 65536⟩
    (by decide) selected_cut_23460

theorem selected_cut_23461 : selected 9 ⟨594334, by decide⟩
    (prefixPartial 12 76414) = some ⟨12, 2, 0, 594334, 76414, 2273, 65536⟩ := by
  decide +kernel

theorem context_12_76414_594334 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76414 ⟨594334, by decide⟩ :=
  accepted_of_selected 12 76414 ⟨594334, by decide⟩ ⟨12, 2, 0, 594334, 76414, 2273, 65536⟩
    (by decide) selected_cut_23461

theorem selected_cut_23462 : selected 9 ⟨594365, by decide⟩
    (prefixPartial 12 76415) = some ⟨12, 2, 0, 594365, 76415, 2681, 65536⟩ := by
  decide +kernel

theorem context_12_76415_594365 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76415 ⟨594365, by decide⟩ :=
  accepted_of_selected 12 76415 ⟨594365, by decide⟩ ⟨12, 2, 0, 594365, 76415, 2681, 65536⟩
    (by decide) selected_cut_23462

theorem unmarked_context_11_19103_594366 : frontier 10 ⟨594366, by decide⟩
    (prefixCache 11 19103) (prefixPartial 11 19103) = false := by
  decide +kernel

theorem node_context_11_19103_594366 : EJMOriginalGlobalDAGData.nodes 10 ⟨594366, by decide⟩ =
    .split (coordinate 11) (![⟨594277, by decide⟩,⟨594302, by decide⟩,⟨594334, by decide⟩,⟨594365, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19103_594366 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19103 ⟨594366, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19103
    ⟨594366, by decide⟩ (by decide) (![⟨594277, by decide⟩,⟨594302, by decide⟩,⟨594334, by decide⟩,⟨594365, by decide⟩]) unmarked_context_11_19103_594366 node_context_11_19103_594366
  intro a
  fin_cases a
  · exact context_12_76412_594277
  · exact context_12_76413_594302
  · exact context_12_76414_594334
  · exact context_12_76415_594365

theorem unmarked_context_10_4775_594367 : frontier 11 ⟨594367, by decide⟩
    (prefixCache 10 4775) (prefixPartial 10 4775) = false := by
  decide +kernel

theorem node_context_10_4775_594367 : EJMOriginalGlobalDAGData.nodes 11 ⟨594367, by decide⟩ =
    .split (coordinate 10) (![⟨593924, by decide⟩,⟨594077, by decide⟩,⟨594249, by decide⟩,⟨594366, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4775_594367 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4775 ⟨594367, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4775
    ⟨594367, by decide⟩ (by decide) (![⟨593924, by decide⟩,⟨594077, by decide⟩,⟨594249, by decide⟩,⟨594366, by decide⟩]) unmarked_context_10_4775_594367 node_context_10_4775_594367
  intro a
  fin_cases a
  · exact context_11_19100_593924
  · exact context_11_19101_594077
  · exact context_11_19102_594249
  · exact context_11_19103_594366

theorem unmarked_context_9_1193_594368 : frontier 12 ⟨594368, by decide⟩
    (prefixCache 9 1193) (prefixPartial 9 1193) = false := by
  decide +kernel

theorem node_context_9_1193_594368 : EJMOriginalGlobalDAGData.nodes 12 ⟨594368, by decide⟩ =
    .split (coordinate 9) (![⟨592460, by decide⟩,⟨593244, by decide⟩,⟨593763, by decide⟩,⟨594367, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1193_594368 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1193 ⟨594368, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1193
    ⟨594368, by decide⟩ (by decide) (![⟨592460, by decide⟩,⟨593244, by decide⟩,⟨593763, by decide⟩,⟨594367, by decide⟩]) unmarked_context_9_1193_594368 node_context_9_1193_594368
  intro a
  fin_cases a
  · exact context_10_4772_592460
  · exact context_10_4773_593244
  · exact context_10_4774_593763
  · exact context_10_4775_594367

theorem selected_cut_23463 : selected 9 ⟨594391, by decide⟩
    (prefixPartial 12 76416) = some ⟨12, 2, 0, 594391, 76416, 1513, 65536⟩ := by
  decide +kernel

theorem context_12_76416_594391 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76416 ⟨594391, by decide⟩ :=
  accepted_of_selected 12 76416 ⟨594391, by decide⟩ ⟨12, 2, 0, 594391, 76416, 1513, 65536⟩
    (by decide) selected_cut_23463

theorem selected_cut_23464 : selected 9 ⟨594411, by decide⟩
    (prefixPartial 12 76417) = some ⟨12, 2, 0, 594411, 76417, 1833, 65536⟩ := by
  decide +kernel

theorem context_12_76417_594411 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76417 ⟨594411, by decide⟩ :=
  accepted_of_selected 12 76417 ⟨594411, by decide⟩ ⟨12, 2, 0, 594411, 76417, 1833, 65536⟩
    (by decide) selected_cut_23464

theorem selected_cut_23465 : selected 9 ⟨594437, by decide⟩
    (prefixPartial 12 76418) = some ⟨12, 2, 0, 594437, 76418, 1697, 65536⟩ := by
  decide +kernel

theorem context_12_76418_594437 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76418 ⟨594437, by decide⟩ :=
  accepted_of_selected 12 76418 ⟨594437, by decide⟩ ⟨12, 2, 0, 594437, 76418, 1697, 65536⟩
    (by decide) selected_cut_23465

theorem selected_cut_23466 : selected 9 ⟨594458, by decide⟩
    (prefixPartial 12 76419) = some ⟨12, 2, 0, 594458, 76419, 1745, 65536⟩ := by
  decide +kernel

theorem context_12_76419_594458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76419 ⟨594458, by decide⟩ :=
  accepted_of_selected 12 76419 ⟨594458, by decide⟩ ⟨12, 2, 0, 594458, 76419, 1745, 65536⟩
    (by decide) selected_cut_23466

theorem unmarked_context_11_19104_594459 : frontier 10 ⟨594459, by decide⟩
    (prefixCache 11 19104) (prefixPartial 11 19104) = false := by
  decide +kernel

theorem node_context_11_19104_594459 : EJMOriginalGlobalDAGData.nodes 10 ⟨594459, by decide⟩ =
    .split (coordinate 11) (![⟨594391, by decide⟩,⟨594411, by decide⟩,⟨594437, by decide⟩,⟨594458, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19104_594459 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19104 ⟨594459, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19104
    ⟨594459, by decide⟩ (by decide) (![⟨594391, by decide⟩,⟨594411, by decide⟩,⟨594437, by decide⟩,⟨594458, by decide⟩]) unmarked_context_11_19104_594459 node_context_11_19104_594459
  intro a
  fin_cases a
  · exact context_12_76416_594391
  · exact context_12_76417_594411
  · exact context_12_76418_594437
  · exact context_12_76419_594458

theorem selected_cut_23467 : selected 9 ⟨594479, by decide⟩
    (prefixPartial 12 76420) = some ⟨12, 2, 0, 594479, 76420, 1509, 65536⟩ := by
  decide +kernel

theorem context_12_76420_594479 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76420 ⟨594479, by decide⟩ :=
  accepted_of_selected 12 76420 ⟨594479, by decide⟩ ⟨12, 2, 0, 594479, 76420, 1509, 65536⟩
    (by decide) selected_cut_23467

theorem selected_cut_23468 : selected 9 ⟨594499, by decide⟩
    (prefixPartial 12 76421) = some ⟨12, 2, 0, 594499, 76421, 1681, 65536⟩ := by
  decide +kernel

theorem context_12_76421_594499 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76421 ⟨594499, by decide⟩ :=
  accepted_of_selected 12 76421 ⟨594499, by decide⟩ ⟨12, 2, 0, 594499, 76421, 1681, 65536⟩
    (by decide) selected_cut_23468

theorem selected_cut_23469 : selected 9 ⟨594519, by decide⟩
    (prefixPartial 12 76422) = some ⟨12, 2, 0, 594519, 76422, 1733, 65536⟩ := by
  decide +kernel

theorem context_12_76422_594519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76422 ⟨594519, by decide⟩ :=
  accepted_of_selected 12 76422 ⟨594519, by decide⟩ ⟨12, 2, 0, 594519, 76422, 1733, 65536⟩
    (by decide) selected_cut_23469

theorem selected_cut_23470 : selected 9 ⟨594535, by decide⟩
    (prefixPartial 12 76423) = some ⟨12, 2, 0, 594535, 76423, 1725, 65536⟩ := by
  decide +kernel

theorem context_12_76423_594535 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76423 ⟨594535, by decide⟩ :=
  accepted_of_selected 12 76423 ⟨594535, by decide⟩ ⟨12, 2, 0, 594535, 76423, 1725, 65536⟩
    (by decide) selected_cut_23470

theorem unmarked_context_11_19105_594536 : frontier 10 ⟨594536, by decide⟩
    (prefixCache 11 19105) (prefixPartial 11 19105) = false := by
  decide +kernel

theorem node_context_11_19105_594536 : EJMOriginalGlobalDAGData.nodes 10 ⟨594536, by decide⟩ =
    .split (coordinate 11) (![⟨594479, by decide⟩,⟨594499, by decide⟩,⟨594519, by decide⟩,⟨594535, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19105_594536 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19105 ⟨594536, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19105
    ⟨594536, by decide⟩ (by decide) (![⟨594479, by decide⟩,⟨594499, by decide⟩,⟨594519, by decide⟩,⟨594535, by decide⟩]) unmarked_context_11_19105_594536 node_context_11_19105_594536
  intro a
  fin_cases a
  · exact context_12_76420_594479
  · exact context_12_76421_594499
  · exact context_12_76422_594519
  · exact context_12_76423_594535

theorem selected_cut_23471 : selected 9 ⟨594556, by decide⟩
    (prefixPartial 12 76424) = some ⟨12, 2, 0, 594556, 76424, 1301, 65536⟩ := by
  decide +kernel

theorem context_12_76424_594556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76424 ⟨594556, by decide⟩ :=
  accepted_of_selected 12 76424 ⟨594556, by decide⟩ ⟨12, 2, 0, 594556, 76424, 1301, 65536⟩
    (by decide) selected_cut_23471

theorem selected_cut_23472 : selected 9 ⟨594579, by decide⟩
    (prefixPartial 12 76425) = some ⟨12, 2, 0, 594579, 76425, 1653, 65536⟩ := by
  decide +kernel

theorem context_12_76425_594579 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76425 ⟨594579, by decide⟩ :=
  accepted_of_selected 12 76425 ⟨594579, by decide⟩ ⟨12, 2, 0, 594579, 76425, 1653, 65536⟩
    (by decide) selected_cut_23472

theorem selected_cut_23473 : selected 9 ⟨188189, by decide⟩
    (prefixPartial 12 76426) = some ⟨12, 1, 0, 188189, 76426, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76426_188189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76426 ⟨188189, by decide⟩ :=
  accepted_of_selected 12 76426 ⟨188189, by decide⟩ ⟨12, 1, 0, 188189, 76426, 1, 65536⟩
    (by decide) selected_cut_23473

theorem selected_cut_23474 : selected 9 ⟨594596, by decide⟩
    (prefixPartial 12 76427) = some ⟨12, 2, 0, 594596, 76427, 1361, 65536⟩ := by
  decide +kernel

theorem context_12_76427_594596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76427 ⟨594596, by decide⟩ :=
  accepted_of_selected 12 76427 ⟨594596, by decide⟩ ⟨12, 2, 0, 594596, 76427, 1361, 65536⟩
    (by decide) selected_cut_23474

theorem unmarked_context_11_19106_594597 : frontier 10 ⟨594597, by decide⟩
    (prefixCache 11 19106) (prefixPartial 11 19106) = false := by
  decide +kernel

theorem node_context_11_19106_594597 : EJMOriginalGlobalDAGData.nodes 10 ⟨594597, by decide⟩ =
    .split (coordinate 11) (![⟨594556, by decide⟩,⟨594579, by decide⟩,⟨188189, by decide⟩,⟨594596, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19106_594597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19106 ⟨594597, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19106
    ⟨594597, by decide⟩ (by decide) (![⟨594556, by decide⟩,⟨594579, by decide⟩,⟨188189, by decide⟩,⟨594596, by decide⟩]) unmarked_context_11_19106_594597 node_context_11_19106_594597
  intro a
  fin_cases a
  · exact context_12_76424_594556
  · exact context_12_76425_594579
  · exact context_12_76426_188189
  · exact context_12_76427_594596

theorem selected_cut_23475 : selected 9 ⟨594617, by decide⟩
    (prefixPartial 12 76428) = some ⟨12, 2, 0, 594617, 76428, 1657, 65536⟩ := by
  decide +kernel

theorem context_12_76428_594617 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76428 ⟨594617, by decide⟩ :=
  accepted_of_selected 12 76428 ⟨594617, by decide⟩ ⟨12, 2, 0, 594617, 76428, 1657, 65536⟩
    (by decide) selected_cut_23475

theorem selected_cut_23476 : selected 9 ⟨594648, by decide⟩
    (prefixPartial 12 76429) = some ⟨12, 2, 0, 594648, 76429, 1881, 65536⟩ := by
  decide +kernel

theorem context_12_76429_594648 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76429 ⟨594648, by decide⟩ :=
  accepted_of_selected 12 76429 ⟨594648, by decide⟩ ⟨12, 2, 0, 594648, 76429, 1881, 65536⟩
    (by decide) selected_cut_23476

theorem selected_cut_23477 : selected 9 ⟨594673, by decide⟩
    (prefixPartial 12 76430) = some ⟨12, 2, 0, 594673, 76430, 1789, 65536⟩ := by
  decide +kernel

theorem context_12_76430_594673 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76430 ⟨594673, by decide⟩ :=
  accepted_of_selected 12 76430 ⟨594673, by decide⟩ ⟨12, 2, 0, 594673, 76430, 1789, 65536⟩
    (by decide) selected_cut_23477

theorem selected_cut_23478 : selected 9 ⟨594692, by decide⟩
    (prefixPartial 12 76431) = some ⟨12, 2, 0, 594692, 76431, 1805, 65536⟩ := by
  decide +kernel

theorem context_12_76431_594692 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76431 ⟨594692, by decide⟩ :=
  accepted_of_selected 12 76431 ⟨594692, by decide⟩ ⟨12, 2, 0, 594692, 76431, 1805, 65536⟩
    (by decide) selected_cut_23478

theorem unmarked_context_11_19107_594693 : frontier 10 ⟨594693, by decide⟩
    (prefixCache 11 19107) (prefixPartial 11 19107) = false := by
  decide +kernel

theorem node_context_11_19107_594693 : EJMOriginalGlobalDAGData.nodes 10 ⟨594693, by decide⟩ =
    .split (coordinate 11) (![⟨594617, by decide⟩,⟨594648, by decide⟩,⟨594673, by decide⟩,⟨594692, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19107_594693 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19107 ⟨594693, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19107
    ⟨594693, by decide⟩ (by decide) (![⟨594617, by decide⟩,⟨594648, by decide⟩,⟨594673, by decide⟩,⟨594692, by decide⟩]) unmarked_context_11_19107_594693 node_context_11_19107_594693
  intro a
  fin_cases a
  · exact context_12_76428_594617
  · exact context_12_76429_594648
  · exact context_12_76430_594673
  · exact context_12_76431_594692

theorem unmarked_context_10_4776_594694 : frontier 11 ⟨594694, by decide⟩
    (prefixCache 10 4776) (prefixPartial 10 4776) = false := by
  decide +kernel

theorem node_context_10_4776_594694 : EJMOriginalGlobalDAGData.nodes 11 ⟨594694, by decide⟩ =
    .split (coordinate 10) (![⟨594459, by decide⟩,⟨594536, by decide⟩,⟨594597, by decide⟩,⟨594693, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4776_594694 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4776 ⟨594694, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4776
    ⟨594694, by decide⟩ (by decide) (![⟨594459, by decide⟩,⟨594536, by decide⟩,⟨594597, by decide⟩,⟨594693, by decide⟩]) unmarked_context_10_4776_594694 node_context_10_4776_594694
  intro a
  fin_cases a
  · exact context_11_19104_594459
  · exact context_11_19105_594536
  · exact context_11_19106_594597
  · exact context_11_19107_594693

theorem selected_cut_23479 : selected 9 ⟨594715, by decide⟩
    (prefixPartial 12 76432) = some ⟨12, 2, 0, 594715, 76432, 1741, 65536⟩ := by
  decide +kernel

theorem context_12_76432_594715 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76432 ⟨594715, by decide⟩ :=
  accepted_of_selected 12 76432 ⟨594715, by decide⟩ ⟨12, 2, 0, 594715, 76432, 1741, 65536⟩
    (by decide) selected_cut_23479

theorem selected_cut_23480 : selected 9 ⟨594743, by decide⟩
    (prefixPartial 12 76433) = some ⟨12, 2, 0, 594743, 76433, 2117, 65536⟩ := by
  decide +kernel

theorem context_12_76433_594743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76433 ⟨594743, by decide⟩ :=
  accepted_of_selected 12 76433 ⟨594743, by decide⟩ ⟨12, 2, 0, 594743, 76433, 2117, 65536⟩
    (by decide) selected_cut_23480

theorem selected_cut_23481 : selected 9 ⟨594773, by decide⟩
    (prefixPartial 12 76434) = some ⟨12, 2, 0, 594773, 76434, 1945, 65536⟩ := by
  decide +kernel

theorem context_12_76434_594773 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76434 ⟨594773, by decide⟩ :=
  accepted_of_selected 12 76434 ⟨594773, by decide⟩ ⟨12, 2, 0, 594773, 76434, 1945, 65536⟩
    (by decide) selected_cut_23481

theorem selected_cut_23482 : selected 9 ⟨594799, by decide⟩
    (prefixPartial 12 76435) = some ⟨12, 2, 0, 594799, 76435, 1909, 65536⟩ := by
  decide +kernel

theorem context_12_76435_594799 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76435 ⟨594799, by decide⟩ :=
  accepted_of_selected 12 76435 ⟨594799, by decide⟩ ⟨12, 2, 0, 594799, 76435, 1909, 65536⟩
    (by decide) selected_cut_23482

theorem unmarked_context_11_19108_594800 : frontier 10 ⟨594800, by decide⟩
    (prefixCache 11 19108) (prefixPartial 11 19108) = false := by
  decide +kernel

theorem node_context_11_19108_594800 : EJMOriginalGlobalDAGData.nodes 10 ⟨594800, by decide⟩ =
    .split (coordinate 11) (![⟨594715, by decide⟩,⟨594743, by decide⟩,⟨594773, by decide⟩,⟨594799, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19108_594800 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19108 ⟨594800, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19108
    ⟨594800, by decide⟩ (by decide) (![⟨594715, by decide⟩,⟨594743, by decide⟩,⟨594773, by decide⟩,⟨594799, by decide⟩]) unmarked_context_11_19108_594800 node_context_11_19108_594800
  intro a
  fin_cases a
  · exact context_12_76432_594715
  · exact context_12_76433_594743
  · exact context_12_76434_594773
  · exact context_12_76435_594799

theorem selected_cut_23483 : selected 9 ⟨594825, by decide⟩
    (prefixPartial 12 76436) = some ⟨12, 2, 0, 594825, 76436, 1745, 65536⟩ := by
  decide +kernel

theorem context_12_76436_594825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76436 ⟨594825, by decide⟩ :=
  accepted_of_selected 12 76436 ⟨594825, by decide⟩ ⟨12, 2, 0, 594825, 76436, 1745, 65536⟩
    (by decide) selected_cut_23483

theorem selected_cut_23484 : selected 9 ⟨594849, by decide⟩
    (prefixPartial 12 76437) = some ⟨12, 2, 0, 594849, 76437, 1949, 65536⟩ := by
  decide +kernel

theorem context_12_76437_594849 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76437 ⟨594849, by decide⟩ :=
  accepted_of_selected 12 76437 ⟨594849, by decide⟩ ⟨12, 2, 0, 594849, 76437, 1949, 65536⟩
    (by decide) selected_cut_23484

theorem selected_cut_23485 : selected 9 ⟨594871, by decide⟩
    (prefixPartial 12 76438) = some ⟨12, 2, 0, 594871, 76438, 1949, 65536⟩ := by
  decide +kernel

theorem context_12_76438_594871 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76438 ⟨594871, by decide⟩ :=
  accepted_of_selected 12 76438 ⟨594871, by decide⟩ ⟨12, 2, 0, 594871, 76438, 1949, 65536⟩
    (by decide) selected_cut_23485

theorem selected_cut_23486 : selected 9 ⟨594896, by decide⟩
    (prefixPartial 12 76439) = some ⟨12, 2, 0, 594896, 76439, 1921, 65536⟩ := by
  decide +kernel

theorem context_12_76439_594896 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76439 ⟨594896, by decide⟩ :=
  accepted_of_selected 12 76439 ⟨594896, by decide⟩ ⟨12, 2, 0, 594896, 76439, 1921, 65536⟩
    (by decide) selected_cut_23486

theorem unmarked_context_11_19109_594897 : frontier 10 ⟨594897, by decide⟩
    (prefixCache 11 19109) (prefixPartial 11 19109) = false := by
  decide +kernel

theorem node_context_11_19109_594897 : EJMOriginalGlobalDAGData.nodes 10 ⟨594897, by decide⟩ =
    .split (coordinate 11) (![⟨594825, by decide⟩,⟨594849, by decide⟩,⟨594871, by decide⟩,⟨594896, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19109_594897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19109 ⟨594897, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19109
    ⟨594897, by decide⟩ (by decide) (![⟨594825, by decide⟩,⟨594849, by decide⟩,⟨594871, by decide⟩,⟨594896, by decide⟩]) unmarked_context_11_19109_594897 node_context_11_19109_594897
  intro a
  fin_cases a
  · exact context_12_76436_594825
  · exact context_12_76437_594849
  · exact context_12_76438_594871
  · exact context_12_76439_594896

theorem selected_cut_23487 : selected 9 ⟨594914, by decide⟩
    (prefixPartial 12 76440) = some ⟨12, 2, 0, 594914, 76440, 1417, 65536⟩ := by
  decide +kernel

theorem context_12_76440_594914 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76440 ⟨594914, by decide⟩ :=
  accepted_of_selected 12 76440 ⟨594914, by decide⟩ ⟨12, 2, 0, 594914, 76440, 1417, 65536⟩
    (by decide) selected_cut_23487

theorem selected_cut_23488 : selected 9 ⟨594934, by decide⟩
    (prefixPartial 12 76441) = some ⟨12, 2, 0, 594934, 76441, 1789, 65536⟩ := by
  decide +kernel

theorem context_12_76441_594934 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76441 ⟨594934, by decide⟩ :=
  accepted_of_selected 12 76441 ⟨594934, by decide⟩ ⟨12, 2, 0, 594934, 76441, 1789, 65536⟩
    (by decide) selected_cut_23488

theorem selected_cut_23489 : selected 9 ⟨212113, by decide⟩
    (prefixPartial 12 76442) = some ⟨12, 1, 0, 212113, 76442, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76442_212113 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76442 ⟨212113, by decide⟩ :=
  accepted_of_selected 12 76442 ⟨212113, by decide⟩ ⟨12, 1, 0, 212113, 76442, 1, 65536⟩
    (by decide) selected_cut_23489

theorem selected_cut_23490 : selected 9 ⟨594951, by decide⟩
    (prefixPartial 12 76443) = some ⟨12, 2, 0, 594951, 76443, 1445, 65536⟩ := by
  decide +kernel

theorem context_12_76443_594951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76443 ⟨594951, by decide⟩ :=
  accepted_of_selected 12 76443 ⟨594951, by decide⟩ ⟨12, 2, 0, 594951, 76443, 1445, 65536⟩
    (by decide) selected_cut_23490

theorem unmarked_context_11_19110_594952 : frontier 10 ⟨594952, by decide⟩
    (prefixCache 11 19110) (prefixPartial 11 19110) = false := by
  decide +kernel

theorem node_context_11_19110_594952 : EJMOriginalGlobalDAGData.nodes 10 ⟨594952, by decide⟩ =
    .split (coordinate 11) (![⟨594914, by decide⟩,⟨594934, by decide⟩,⟨212113, by decide⟩,⟨594951, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19110_594952 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19110 ⟨594952, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19110
    ⟨594952, by decide⟩ (by decide) (![⟨594914, by decide⟩,⟨594934, by decide⟩,⟨212113, by decide⟩,⟨594951, by decide⟩]) unmarked_context_11_19110_594952 node_context_11_19110_594952
  intro a
  fin_cases a
  · exact context_12_76440_594914
  · exact context_12_76441_594934
  · exact context_12_76442_212113
  · exact context_12_76443_594951

theorem selected_cut_23491 : selected 9 ⟨594975, by decide⟩
    (prefixPartial 12 76444) = some ⟨12, 2, 0, 594975, 76444, 1773, 65536⟩ := by
  decide +kernel

theorem context_12_76444_594975 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76444 ⟨594975, by decide⟩ :=
  accepted_of_selected 12 76444 ⟨594975, by decide⟩ ⟨12, 2, 0, 594975, 76444, 1773, 65536⟩
    (by decide) selected_cut_23491

theorem selected_cut_23492 : selected 9 ⟨594998, by decide⟩
    (prefixPartial 12 76445) = some ⟨12, 2, 0, 594998, 76445, 1917, 65536⟩ := by
  decide +kernel

theorem context_12_76445_594998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76445 ⟨594998, by decide⟩ :=
  accepted_of_selected 12 76445 ⟨594998, by decide⟩ ⟨12, 2, 0, 594998, 76445, 1917, 65536⟩
    (by decide) selected_cut_23492

theorem selected_cut_23493 : selected 9 ⟨595021, by decide⟩
    (prefixPartial 12 76446) = some ⟨12, 2, 0, 595021, 76446, 1813, 65536⟩ := by
  decide +kernel

theorem context_12_76446_595021 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76446 ⟨595021, by decide⟩ :=
  accepted_of_selected 12 76446 ⟨595021, by decide⟩ ⟨12, 2, 0, 595021, 76446, 1813, 65536⟩
    (by decide) selected_cut_23493

theorem selected_cut_23494 : selected 9 ⟨595045, by decide⟩
    (prefixPartial 12 76447) = some ⟨12, 2, 0, 595045, 76447, 1821, 65536⟩ := by
  decide +kernel

theorem context_12_76447_595045 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76447 ⟨595045, by decide⟩ :=
  accepted_of_selected 12 76447 ⟨595045, by decide⟩ ⟨12, 2, 0, 595045, 76447, 1821, 65536⟩
    (by decide) selected_cut_23494

theorem unmarked_context_11_19111_595046 : frontier 10 ⟨595046, by decide⟩
    (prefixCache 11 19111) (prefixPartial 11 19111) = false := by
  decide +kernel

theorem node_context_11_19111_595046 : EJMOriginalGlobalDAGData.nodes 10 ⟨595046, by decide⟩ =
    .split (coordinate 11) (![⟨594975, by decide⟩,⟨594998, by decide⟩,⟨595021, by decide⟩,⟨595045, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19111_595046 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19111 ⟨595046, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19111
    ⟨595046, by decide⟩ (by decide) (![⟨594975, by decide⟩,⟨594998, by decide⟩,⟨595021, by decide⟩,⟨595045, by decide⟩]) unmarked_context_11_19111_595046 node_context_11_19111_595046
  intro a
  fin_cases a
  · exact context_12_76444_594975
  · exact context_12_76445_594998
  · exact context_12_76446_595021
  · exact context_12_76447_595045

theorem unmarked_context_10_4777_595047 : frontier 11 ⟨595047, by decide⟩
    (prefixCache 10 4777) (prefixPartial 10 4777) = false := by
  decide +kernel

theorem node_context_10_4777_595047 : EJMOriginalGlobalDAGData.nodes 11 ⟨595047, by decide⟩ =
    .split (coordinate 10) (![⟨594800, by decide⟩,⟨594897, by decide⟩,⟨594952, by decide⟩,⟨595046, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4777_595047 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4777 ⟨595047, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4777
    ⟨595047, by decide⟩ (by decide) (![⟨594800, by decide⟩,⟨594897, by decide⟩,⟨594952, by decide⟩,⟨595046, by decide⟩]) unmarked_context_10_4777_595047 node_context_10_4777_595047
  intro a
  fin_cases a
  · exact context_11_19108_594800
  · exact context_11_19109_594897
  · exact context_11_19110_594952
  · exact context_11_19111_595046

theorem selected_cut_23495 : selected 9 ⟨595060, by decide⟩
    (prefixPartial 12 76448) = some ⟨12, 2, 0, 595060, 76448, 1181, 65536⟩ := by
  decide +kernel

theorem context_12_76448_595060 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76448 ⟨595060, by decide⟩ :=
  accepted_of_selected 12 76448 ⟨595060, by decide⟩ ⟨12, 2, 0, 595060, 76448, 1181, 65536⟩
    (by decide) selected_cut_23495

theorem selected_cut_23496 : selected 9 ⟨595076, by decide⟩
    (prefixPartial 12 76449) = some ⟨12, 2, 0, 595076, 76449, 1369, 65536⟩ := by
  decide +kernel

theorem context_12_76449_595076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76449 ⟨595076, by decide⟩ :=
  accepted_of_selected 12 76449 ⟨595076, by decide⟩ ⟨12, 2, 0, 595076, 76449, 1369, 65536⟩
    (by decide) selected_cut_23496

theorem selected_cut_23497 : selected 9 ⟨595088, by decide⟩
    (prefixPartial 12 76450) = some ⟨12, 2, 0, 595088, 76450, 1137, 65536⟩ := by
  decide +kernel

theorem context_12_76450_595088 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76450 ⟨595088, by decide⟩ :=
  accepted_of_selected 12 76450 ⟨595088, by decide⟩ ⟨12, 2, 0, 595088, 76450, 1137, 65536⟩
    (by decide) selected_cut_23497

theorem selected_cut_23498 : selected 9 ⟨595104, by decide⟩
    (prefixPartial 12 76451) = some ⟨12, 2, 0, 595104, 76451, 1293, 65536⟩ := by
  decide +kernel

theorem context_12_76451_595104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76451 ⟨595104, by decide⟩ :=
  accepted_of_selected 12 76451 ⟨595104, by decide⟩ ⟨12, 2, 0, 595104, 76451, 1293, 65536⟩
    (by decide) selected_cut_23498

theorem unmarked_context_11_19112_595105 : frontier 10 ⟨595105, by decide⟩
    (prefixCache 11 19112) (prefixPartial 11 19112) = false := by
  decide +kernel

theorem node_context_11_19112_595105 : EJMOriginalGlobalDAGData.nodes 10 ⟨595105, by decide⟩ =
    .split (coordinate 11) (![⟨595060, by decide⟩,⟨595076, by decide⟩,⟨595088, by decide⟩,⟨595104, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19112_595105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19112 ⟨595105, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19112
    ⟨595105, by decide⟩ (by decide) (![⟨595060, by decide⟩,⟨595076, by decide⟩,⟨595088, by decide⟩,⟨595104, by decide⟩]) unmarked_context_11_19112_595105 node_context_11_19112_595105
  intro a
  fin_cases a
  · exact context_12_76448_595060
  · exact context_12_76449_595076
  · exact context_12_76450_595088
  · exact context_12_76451_595104

theorem selected_cut_23499 : selected 9 ⟨595122, by decide⟩
    (prefixPartial 12 76452) = some ⟨12, 2, 0, 595122, 76452, 1321, 65536⟩ := by
  decide +kernel

theorem context_12_76452_595122 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76452 ⟨595122, by decide⟩ :=
  accepted_of_selected 12 76452 ⟨595122, by decide⟩ ⟨12, 2, 0, 595122, 76452, 1321, 65536⟩
    (by decide) selected_cut_23499

theorem selected_cut_23500 : selected 9 ⟨595137, by decide⟩
    (prefixPartial 12 76453) = some ⟨12, 2, 0, 595137, 76453, 1445, 65536⟩ := by
  decide +kernel

theorem context_12_76453_595137 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76453 ⟨595137, by decide⟩ :=
  accepted_of_selected 12 76453 ⟨595137, by decide⟩ ⟨12, 2, 0, 595137, 76453, 1445, 65536⟩
    (by decide) selected_cut_23500

theorem selected_cut_23501 : selected 9 ⟨595150, by decide⟩
    (prefixPartial 12 76454) = some ⟨12, 2, 0, 595150, 76454, 1257, 65536⟩ := by
  decide +kernel

theorem context_12_76454_595150 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76454 ⟨595150, by decide⟩ :=
  accepted_of_selected 12 76454 ⟨595150, by decide⟩ ⟨12, 2, 0, 595150, 76454, 1257, 65536⟩
    (by decide) selected_cut_23501

theorem selected_cut_23502 : selected 9 ⟨595166, by decide⟩
    (prefixPartial 12 76455) = some ⟨12, 2, 0, 595166, 76455, 1445, 65536⟩ := by
  decide +kernel

theorem context_12_76455_595166 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76455 ⟨595166, by decide⟩ :=
  accepted_of_selected 12 76455 ⟨595166, by decide⟩ ⟨12, 2, 0, 595166, 76455, 1445, 65536⟩
    (by decide) selected_cut_23502

theorem unmarked_context_11_19113_595167 : frontier 10 ⟨595167, by decide⟩
    (prefixCache 11 19113) (prefixPartial 11 19113) = false := by
  decide +kernel

theorem node_context_11_19113_595167 : EJMOriginalGlobalDAGData.nodes 10 ⟨595167, by decide⟩ =
    .split (coordinate 11) (![⟨595122, by decide⟩,⟨595137, by decide⟩,⟨595150, by decide⟩,⟨595166, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19113_595167 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19113 ⟨595167, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19113
    ⟨595167, by decide⟩ (by decide) (![⟨595122, by decide⟩,⟨595137, by decide⟩,⟨595150, by decide⟩,⟨595166, by decide⟩]) unmarked_context_11_19113_595167 node_context_11_19113_595167
  intro a
  fin_cases a
  · exact context_12_76452_595122
  · exact context_12_76453_595137
  · exact context_12_76454_595150
  · exact context_12_76455_595166

theorem selected_cut_23503 : selected 10 ⟨479708, by decide⟩
    (prefixPartial 11 19114) = some ⟨11, 1, 0, 479708, 19114, 1, 262144⟩ := by
  decide +kernel

theorem context_11_19114_479708 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19114 ⟨479708, by decide⟩ :=
  accepted_of_selected 11 19114 ⟨479708, by decide⟩ ⟨11, 1, 0, 479708, 19114, 1, 262144⟩
    (by decide) selected_cut_23503

theorem selected_cut_23504 : selected 9 ⟨595180, by decide⟩
    (prefixPartial 12 76460) = some ⟨12, 2, 0, 595180, 76460, 1357, 65536⟩ := by
  decide +kernel

theorem context_12_76460_595180 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76460 ⟨595180, by decide⟩ :=
  accepted_of_selected 12 76460 ⟨595180, by decide⟩ ⟨12, 2, 0, 595180, 76460, 1357, 65536⟩
    (by decide) selected_cut_23504

theorem selected_cut_23505 : selected 9 ⟨595197, by decide⟩
    (prefixPartial 12 76461) = some ⟨12, 2, 0, 595197, 76461, 1393, 65536⟩ := by
  decide +kernel

theorem context_12_76461_595197 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76461 ⟨595197, by decide⟩ :=
  accepted_of_selected 12 76461 ⟨595197, by decide⟩ ⟨12, 2, 0, 595197, 76461, 1393, 65536⟩
    (by decide) selected_cut_23505

theorem selected_cut_23506 : selected 9 ⟨595211, by decide⟩
    (prefixPartial 12 76462) = some ⟨12, 2, 0, 595211, 76462, 1201, 65536⟩ := by
  decide +kernel

theorem context_12_76462_595211 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76462 ⟨595211, by decide⟩ :=
  accepted_of_selected 12 76462 ⟨595211, by decide⟩ ⟨12, 2, 0, 595211, 76462, 1201, 65536⟩
    (by decide) selected_cut_23506

theorem selected_cut_23507 : selected 9 ⟨595225, by decide⟩
    (prefixPartial 12 76463) = some ⟨12, 2, 0, 595225, 76463, 1365, 65536⟩ := by
  decide +kernel

theorem context_12_76463_595225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76463 ⟨595225, by decide⟩ :=
  accepted_of_selected 12 76463 ⟨595225, by decide⟩ ⟨12, 2, 0, 595225, 76463, 1365, 65536⟩
    (by decide) selected_cut_23507

theorem unmarked_context_11_19115_595226 : frontier 10 ⟨595226, by decide⟩
    (prefixCache 11 19115) (prefixPartial 11 19115) = false := by
  decide +kernel

theorem node_context_11_19115_595226 : EJMOriginalGlobalDAGData.nodes 10 ⟨595226, by decide⟩ =
    .split (coordinate 11) (![⟨595180, by decide⟩,⟨595197, by decide⟩,⟨595211, by decide⟩,⟨595225, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19115_595226 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19115 ⟨595226, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19115
    ⟨595226, by decide⟩ (by decide) (![⟨595180, by decide⟩,⟨595197, by decide⟩,⟨595211, by decide⟩,⟨595225, by decide⟩]) unmarked_context_11_19115_595226 node_context_11_19115_595226
  intro a
  fin_cases a
  · exact context_12_76460_595180
  · exact context_12_76461_595197
  · exact context_12_76462_595211
  · exact context_12_76463_595225

theorem unmarked_context_10_4778_595227 : frontier 11 ⟨595227, by decide⟩
    (prefixCache 10 4778) (prefixPartial 10 4778) = false := by
  decide +kernel

theorem node_context_10_4778_595227 : EJMOriginalGlobalDAGData.nodes 11 ⟨595227, by decide⟩ =
    .split (coordinate 10) (![⟨595105, by decide⟩,⟨595167, by decide⟩,⟨479708, by decide⟩,⟨595226, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4778_595227 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4778 ⟨595227, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4778
    ⟨595227, by decide⟩ (by decide) (![⟨595105, by decide⟩,⟨595167, by decide⟩,⟨479708, by decide⟩,⟨595226, by decide⟩]) unmarked_context_10_4778_595227 node_context_10_4778_595227
  intro a
  fin_cases a
  · exact context_11_19112_595105
  · exact context_11_19113_595167
  · exact context_11_19114_479708
  · exact context_11_19115_595226

theorem selected_cut_23508 : selected 9 ⟨595239, by decide⟩
    (prefixPartial 12 76464) = some ⟨12, 2, 0, 595239, 76464, 1097, 65536⟩ := by
  decide +kernel

theorem context_12_76464_595239 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76464 ⟨595239, by decide⟩ :=
  accepted_of_selected 12 76464 ⟨595239, by decide⟩ ⟨12, 2, 0, 595239, 76464, 1097, 65536⟩
    (by decide) selected_cut_23508

theorem selected_cut_23509 : selected 9 ⟨595254, by decide⟩
    (prefixPartial 12 76465) = some ⟨12, 2, 0, 595254, 76465, 1357, 65536⟩ := by
  decide +kernel

theorem context_12_76465_595254 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76465 ⟨595254, by decide⟩ :=
  accepted_of_selected 12 76465 ⟨595254, by decide⟩ ⟨12, 2, 0, 595254, 76465, 1357, 65536⟩
    (by decide) selected_cut_23509

theorem selected_cut_23510 : selected 9 ⟨595264, by decide⟩
    (prefixPartial 12 76466) = some ⟨12, 2, 0, 595264, 76466, 1177, 65536⟩ := by
  decide +kernel

theorem context_12_76466_595264 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76466 ⟨595264, by decide⟩ :=
  accepted_of_selected 12 76466 ⟨595264, by decide⟩ ⟨12, 2, 0, 595264, 76466, 1177, 65536⟩
    (by decide) selected_cut_23510

theorem selected_cut_23511 : selected 9 ⟨595277, by decide⟩
    (prefixPartial 12 76467) = some ⟨12, 2, 0, 595277, 76467, 1121, 65536⟩ := by
  decide +kernel

theorem context_12_76467_595277 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76467 ⟨595277, by decide⟩ :=
  accepted_of_selected 12 76467 ⟨595277, by decide⟩ ⟨12, 2, 0, 595277, 76467, 1121, 65536⟩
    (by decide) selected_cut_23511

theorem unmarked_context_11_19116_595278 : frontier 10 ⟨595278, by decide⟩
    (prefixCache 11 19116) (prefixPartial 11 19116) = false := by
  decide +kernel

theorem node_context_11_19116_595278 : EJMOriginalGlobalDAGData.nodes 10 ⟨595278, by decide⟩ =
    .split (coordinate 11) (![⟨595239, by decide⟩,⟨595254, by decide⟩,⟨595264, by decide⟩,⟨595277, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19116_595278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19116 ⟨595278, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19116
    ⟨595278, by decide⟩ (by decide) (![⟨595239, by decide⟩,⟨595254, by decide⟩,⟨595264, by decide⟩,⟨595277, by decide⟩]) unmarked_context_11_19116_595278 node_context_11_19116_595278
  intro a
  fin_cases a
  · exact context_12_76464_595239
  · exact context_12_76465_595254
  · exact context_12_76466_595264
  · exact context_12_76467_595277

theorem selected_cut_23512 : selected 9 ⟨595291, by decide⟩
    (prefixPartial 12 76468) = some ⟨12, 2, 0, 595291, 76468, 1165, 65536⟩ := by
  decide +kernel

theorem context_12_76468_595291 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76468 ⟨595291, by decide⟩ :=
  accepted_of_selected 12 76468 ⟨595291, by decide⟩ ⟨12, 2, 0, 595291, 76468, 1165, 65536⟩
    (by decide) selected_cut_23512

theorem selected_cut_23513 : selected 9 ⟨595303, by decide⟩
    (prefixPartial 12 76469) = some ⟨12, 2, 0, 595303, 76469, 1269, 65536⟩ := by
  decide +kernel

theorem context_12_76469_595303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76469 ⟨595303, by decide⟩ :=
  accepted_of_selected 12 76469 ⟨595303, by decide⟩ ⟨12, 2, 0, 595303, 76469, 1269, 65536⟩
    (by decide) selected_cut_23513

theorem selected_cut_23514 : selected 9 ⟨595317, by decide⟩
    (prefixPartial 12 76470) = some ⟨12, 2, 0, 595317, 76470, 1225, 65536⟩ := by
  decide +kernel

theorem context_12_76470_595317 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76470 ⟨595317, by decide⟩ :=
  accepted_of_selected 12 76470 ⟨595317, by decide⟩ ⟨12, 2, 0, 595317, 76470, 1225, 65536⟩
    (by decide) selected_cut_23514

theorem selected_cut_23515 : selected 9 ⟨595331, by decide⟩
    (prefixPartial 12 76471) = some ⟨12, 2, 0, 595331, 76471, 1137, 65536⟩ := by
  decide +kernel

theorem context_12_76471_595331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76471 ⟨595331, by decide⟩ :=
  accepted_of_selected 12 76471 ⟨595331, by decide⟩ ⟨12, 2, 0, 595331, 76471, 1137, 65536⟩
    (by decide) selected_cut_23515

theorem unmarked_context_11_19117_595332 : frontier 10 ⟨595332, by decide⟩
    (prefixCache 11 19117) (prefixPartial 11 19117) = false := by
  decide +kernel

theorem node_context_11_19117_595332 : EJMOriginalGlobalDAGData.nodes 10 ⟨595332, by decide⟩ =
    .split (coordinate 11) (![⟨595291, by decide⟩,⟨595303, by decide⟩,⟨595317, by decide⟩,⟨595331, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19117_595332 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19117 ⟨595332, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19117
    ⟨595332, by decide⟩ (by decide) (![⟨595291, by decide⟩,⟨595303, by decide⟩,⟨595317, by decide⟩,⟨595331, by decide⟩]) unmarked_context_11_19117_595332 node_context_11_19117_595332
  intro a
  fin_cases a
  · exact context_12_76468_595291
  · exact context_12_76469_595303
  · exact context_12_76470_595317
  · exact context_12_76471_595331

theorem selected_cut_23516 : selected 10 ⟨595367, by decide⟩
    (prefixPartial 11 19118) = some ⟨11, 2, 0, 595367, 19118, 2957, 262144⟩ := by
  decide +kernel

theorem context_11_19118_595367 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19118 ⟨595367, by decide⟩ :=
  accepted_of_selected 11 19118 ⟨595367, by decide⟩ ⟨11, 2, 0, 595367, 19118, 2957, 262144⟩
    (by decide) selected_cut_23516

theorem selected_cut_23517 : selected 9 ⟨595376, by decide⟩
    (prefixPartial 12 76476) = some ⟨12, 2, 0, 595376, 76476, 1069, 65536⟩ := by
  decide +kernel

theorem context_12_76476_595376 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76476 ⟨595376, by decide⟩ :=
  accepted_of_selected 12 76476 ⟨595376, by decide⟩ ⟨12, 2, 0, 595376, 76476, 1069, 65536⟩
    (by decide) selected_cut_23517

theorem selected_cut_23518 : selected 9 ⟨595392, by decide⟩
    (prefixPartial 12 76477) = some ⟨12, 2, 0, 595392, 76477, 1209, 65536⟩ := by
  decide +kernel

theorem context_12_76477_595392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76477 ⟨595392, by decide⟩ :=
  accepted_of_selected 12 76477 ⟨595392, by decide⟩ ⟨12, 2, 0, 595392, 76477, 1209, 65536⟩
    (by decide) selected_cut_23518

theorem selected_cut_23519 : selected 9 ⟨595402, by decide⟩
    (prefixPartial 12 76478) = some ⟨12, 2, 0, 595402, 76478, 1073, 65536⟩ := by
  decide +kernel

theorem context_12_76478_595402 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76478 ⟨595402, by decide⟩ :=
  accepted_of_selected 12 76478 ⟨595402, by decide⟩ ⟨12, 2, 0, 595402, 76478, 1073, 65536⟩
    (by decide) selected_cut_23519

theorem selected_cut_23520 : selected 9 ⟨595412, by decide⟩
    (prefixPartial 12 76479) = some ⟨12, 2, 0, 595412, 76479, 961, 65536⟩ := by
  decide +kernel

theorem context_12_76479_595412 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76479 ⟨595412, by decide⟩ :=
  accepted_of_selected 12 76479 ⟨595412, by decide⟩ ⟨12, 2, 0, 595412, 76479, 961, 65536⟩
    (by decide) selected_cut_23520

theorem unmarked_context_11_19119_595413 : frontier 10 ⟨595413, by decide⟩
    (prefixCache 11 19119) (prefixPartial 11 19119) = false := by
  decide +kernel

theorem node_context_11_19119_595413 : EJMOriginalGlobalDAGData.nodes 10 ⟨595413, by decide⟩ =
    .split (coordinate 11) (![⟨595376, by decide⟩,⟨595392, by decide⟩,⟨595402, by decide⟩,⟨595412, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19119_595413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19119 ⟨595413, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19119
    ⟨595413, by decide⟩ (by decide) (![⟨595376, by decide⟩,⟨595392, by decide⟩,⟨595402, by decide⟩,⟨595412, by decide⟩]) unmarked_context_11_19119_595413 node_context_11_19119_595413
  intro a
  fin_cases a
  · exact context_12_76476_595376
  · exact context_12_76477_595392
  · exact context_12_76478_595402
  · exact context_12_76479_595412

theorem unmarked_context_10_4779_595414 : frontier 11 ⟨595414, by decide⟩
    (prefixCache 10 4779) (prefixPartial 10 4779) = false := by
  decide +kernel

theorem node_context_10_4779_595414 : EJMOriginalGlobalDAGData.nodes 11 ⟨595414, by decide⟩ =
    .split (coordinate 10) (![⟨595278, by decide⟩,⟨595332, by decide⟩,⟨595367, by decide⟩,⟨595413, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4779_595414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4779 ⟨595414, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4779
    ⟨595414, by decide⟩ (by decide) (![⟨595278, by decide⟩,⟨595332, by decide⟩,⟨595367, by decide⟩,⟨595413, by decide⟩]) unmarked_context_10_4779_595414 node_context_10_4779_595414
  intro a
  fin_cases a
  · exact context_11_19116_595278
  · exact context_11_19117_595332
  · exact context_11_19118_595367
  · exact context_11_19119_595413

theorem unmarked_context_9_1194_595415 : frontier 12 ⟨595415, by decide⟩
    (prefixCache 9 1194) (prefixPartial 9 1194) = false := by
  decide +kernel

theorem node_context_9_1194_595415 : EJMOriginalGlobalDAGData.nodes 12 ⟨595415, by decide⟩ =
    .split (coordinate 9) (![⟨594694, by decide⟩,⟨595047, by decide⟩,⟨595227, by decide⟩,⟨595414, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1194_595415 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1194 ⟨595415, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1194
    ⟨595415, by decide⟩ (by decide) (![⟨594694, by decide⟩,⟨595047, by decide⟩,⟨595227, by decide⟩,⟨595414, by decide⟩]) unmarked_context_9_1194_595415 node_context_9_1194_595415
  intro a
  fin_cases a
  · exact context_10_4776_594694
  · exact context_10_4777_595047
  · exact context_10_4778_595227
  · exact context_10_4779_595414

theorem selected_cut_23521 : selected 10 ⟨595454, by decide⟩
    (prefixPartial 11 19120) = some ⟨11, 2, 0, 595454, 19120, 4001, 262144⟩ := by
  decide +kernel

theorem context_11_19120_595454 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19120 ⟨595454, by decide⟩ :=
  accepted_of_selected 11 19120 ⟨595454, by decide⟩ ⟨11, 2, 0, 595454, 19120, 4001, 262144⟩
    (by decide) selected_cut_23521

theorem selected_cut_23522 : selected 10 ⟨595490, by decide⟩
    (prefixPartial 11 19121) = some ⟨11, 2, 0, 595490, 19121, 3457, 262144⟩ := by
  decide +kernel

theorem context_11_19121_595490 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19121 ⟨595490, by decide⟩ :=
  accepted_of_selected 11 19121 ⟨595490, by decide⟩ ⟨11, 2, 0, 595490, 19121, 3457, 262144⟩
    (by decide) selected_cut_23522

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
