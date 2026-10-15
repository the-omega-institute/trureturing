/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover353
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_8_440_878224 : frontier 13 ⟨878224, by decide⟩
    (prefixCache 8 440) (prefixPartial 8 440) = false := by
  decide +kernel

theorem node_context_8_440_878224 : EJMOriginalGlobalDAGData.nodes 13 ⟨878224, by decide⟩ =
    .split (coordinate 8) (![⟨875477, by decide⟩,⟨877646, by decide⟩,⟨878137, by decide⟩,⟨878223, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_440_878224 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 440 ⟨878224, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 440
    ⟨878224, by decide⟩ (by decide) (![⟨875477, by decide⟩,⟨877646, by decide⟩,⟨878137, by decide⟩,⟨878223, by decide⟩]) unmarked_context_8_440_878224 node_context_8_440_878224
  intro a
  fin_cases a
  · exact context_9_1760_875477
  · exact context_9_1761_877646
  · exact context_9_1762_878137
  · exact context_9_1763_878223

theorem selected_cut_33987 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 28224) = some ⟨11, 1, 0, 434745, 28224, 1, 262144⟩ := by
  decide +kernel

theorem context_11_28224_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28224 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 28224 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 28224, 1, 262144⟩
    (by decide) selected_cut_33987

theorem selected_cut_33988 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 112900) = some ⟨12, 1, 0, 448748, 112900, 1, 65536⟩ := by
  decide +kernel

theorem context_12_112900_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112900 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 112900 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 112900, 1, 65536⟩
    (by decide) selected_cut_33988

theorem selected_cut_33989 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 112901) = some ⟨12, 1, 0, 34034, 112901, 1, 65536⟩ := by
  decide +kernel

theorem context_12_112901_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112901 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 112901 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 112901, 1, 65536⟩
    (by decide) selected_cut_33989

theorem selected_cut_33990 : selected 9 ⟨763842, by decide⟩
    (prefixPartial 12 112902) = some ⟨12, 1, 0, 763842, 112902, 1, 65536⟩ := by
  decide +kernel

theorem context_12_112902_763842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112902 ⟨763842, by decide⟩ :=
  accepted_of_selected 12 112902 ⟨763842, by decide⟩ ⟨12, 1, 0, 763842, 112902, 1, 65536⟩
    (by decide) selected_cut_33990

theorem selected_cut_33991 : selected 8 ⟨878281, by decide⟩
    (prefixPartial 13 451612) = some ⟨13, 2, 0, 878281, 451612, 2149, 16384⟩ := by
  decide +kernel

theorem context_13_451612_878281 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451612 ⟨878281, by decide⟩ :=
  accepted_of_selected 13 451612 ⟨878281, by decide⟩ ⟨13, 2, 0, 878281, 451612, 2149, 16384⟩
    (by decide) selected_cut_33991

theorem selected_cut_33992 : selected 8 ⟨878339, by decide⟩
    (prefixPartial 13 451613) = some ⟨13, 2, 0, 878339, 451613, 1433, 16384⟩ := by
  decide +kernel

theorem context_13_451613_878339 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451613 ⟨878339, by decide⟩ :=
  accepted_of_selected 13 451613 ⟨878339, by decide⟩ ⟨13, 2, 0, 878339, 451613, 1433, 16384⟩
    (by decide) selected_cut_33992

theorem selected_cut_33993 : selected 8 ⟨878354, by decide⟩
    (prefixPartial 13 451614) = some ⟨13, 2, 0, 878354, 451614, 409, 16384⟩ := by
  decide +kernel

theorem context_13_451614_878354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451614 ⟨878354, by decide⟩ :=
  accepted_of_selected 13 451614 ⟨878354, by decide⟩ ⟨13, 2, 0, 878354, 451614, 409, 16384⟩
    (by decide) selected_cut_33993

theorem selected_cut_33994 : selected 8 ⟨878357, by decide⟩
    (prefixPartial 13 451615) = some ⟨13, 2, 0, 878357, 451615, 133, 16384⟩ := by
  decide +kernel

theorem context_13_451615_878357 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451615 ⟨878357, by decide⟩ :=
  accepted_of_selected 13 451615 ⟨878357, by decide⟩ ⟨13, 2, 0, 878357, 451615, 133, 16384⟩
    (by decide) selected_cut_33994

theorem unmarked_context_12_112903_878358 : frontier 9 ⟨878358, by decide⟩
    (prefixCache 12 112903) (prefixPartial 12 112903) = false := by
  decide +kernel

theorem node_context_12_112903_878358 : EJMOriginalGlobalDAGData.nodes 9 ⟨878358, by decide⟩ =
    .split (coordinate 12) (![⟨878281, by decide⟩,⟨878339, by decide⟩,⟨878354, by decide⟩,⟨878357, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_112903_878358 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112903 ⟨878358, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 112903
    ⟨878358, by decide⟩ (by decide) (![⟨878281, by decide⟩,⟨878339, by decide⟩,⟨878354, by decide⟩,⟨878357, by decide⟩]) unmarked_context_12_112903_878358 node_context_12_112903_878358
  intro a
  fin_cases a
  · exact context_13_451612_878281
  · exact context_13_451613_878339
  · exact context_13_451614_878354
  · exact context_13_451615_878357

theorem unmarked_context_11_28225_878359 : frontier 10 ⟨878359, by decide⟩
    (prefixCache 11 28225) (prefixPartial 11 28225) = false := by
  decide +kernel

theorem node_context_11_28225_878359 : EJMOriginalGlobalDAGData.nodes 10 ⟨878359, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨763842, by decide⟩,⟨878358, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28225_878359 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28225 ⟨878359, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28225
    ⟨878359, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨763842, by decide⟩,⟨878358, by decide⟩]) unmarked_context_11_28225_878359 node_context_11_28225_878359
  intro a
  fin_cases a
  · exact context_12_112900_448748
  · exact context_12_112901_34034
  · exact context_12_112902_763842
  · exact context_12_112903_878358

theorem selected_cut_33995 : selected 10 ⟨764169, by decide⟩
    (prefixPartial 11 28226) = some ⟨11, 1, 0, 764169, 28226, 1, 262144⟩ := by
  decide +kernel

theorem context_11_28226_764169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28226 ⟨764169, by decide⟩ :=
  accepted_of_selected 11 28226 ⟨764169, by decide⟩ ⟨11, 1, 0, 764169, 28226, 1, 262144⟩
    (by decide) selected_cut_33995

theorem selected_cut_33996 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 112908) = some ⟨12, 1, 0, 448748, 112908, 1, 65536⟩ := by
  decide +kernel

theorem context_12_112908_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112908 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 112908 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 112908, 1, 65536⟩
    (by decide) selected_cut_33996

theorem selected_cut_33997 : selected 8 ⟨878452, by decide⟩
    (prefixPartial 13 451636) = some ⟨13, 2, 0, 878452, 451636, 2981, 16384⟩ := by
  decide +kernel

theorem context_13_451636_878452 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451636 ⟨878452, by decide⟩ :=
  accepted_of_selected 13 451636 ⟨878452, by decide⟩ ⟨13, 2, 0, 878452, 451636, 2981, 16384⟩
    (by decide) selected_cut_33997

theorem selected_cut_33998 : selected 8 ⟨878542, by decide⟩
    (prefixPartial 13 451637) = some ⟨13, 2, 0, 878542, 451637, 3349, 16384⟩ := by
  decide +kernel

theorem context_13_451637_878542 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451637 ⟨878542, by decide⟩ :=
  accepted_of_selected 13 451637 ⟨878542, by decide⟩ ⟨13, 2, 0, 878542, 451637, 3349, 16384⟩
    (by decide) selected_cut_33998

theorem selected_cut_33999 : selected 8 ⟨878606, by decide⟩
    (prefixPartial 13 451638) = some ⟨13, 2, 0, 878606, 451638, 1765, 16384⟩ := by
  decide +kernel

theorem context_13_451638_878606 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451638 ⟨878606, by decide⟩ :=
  accepted_of_selected 13 451638 ⟨878606, by decide⟩ ⟨13, 2, 0, 878606, 451638, 1765, 16384⟩
    (by decide) selected_cut_33999

theorem selected_cut_34000 : selected 8 ⟨878649, by decide⟩
    (prefixPartial 13 451639) = some ⟨13, 2, 0, 878649, 451639, 1249, 16384⟩ := by
  decide +kernel

theorem context_13_451639_878649 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451639 ⟨878649, by decide⟩ :=
  accepted_of_selected 13 451639 ⟨878649, by decide⟩ ⟨13, 2, 0, 878649, 451639, 1249, 16384⟩
    (by decide) selected_cut_34000

theorem unmarked_context_12_112909_878650 : frontier 9 ⟨878650, by decide⟩
    (prefixCache 12 112909) (prefixPartial 12 112909) = false := by
  decide +kernel

theorem node_context_12_112909_878650 : EJMOriginalGlobalDAGData.nodes 9 ⟨878650, by decide⟩ =
    .split (coordinate 12) (![⟨878452, by decide⟩,⟨878542, by decide⟩,⟨878606, by decide⟩,⟨878649, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_112909_878650 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112909 ⟨878650, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 112909
    ⟨878650, by decide⟩ (by decide) (![⟨878452, by decide⟩,⟨878542, by decide⟩,⟨878606, by decide⟩,⟨878649, by decide⟩]) unmarked_context_12_112909_878650 node_context_12_112909_878650
  intro a
  fin_cases a
  · exact context_13_451636_878452
  · exact context_13_451637_878542
  · exact context_13_451638_878606
  · exact context_13_451639_878649

theorem selected_cut_34001 : selected 9 ⟨763842, by decide⟩
    (prefixPartial 12 112910) = some ⟨12, 1, 0, 763842, 112910, 1, 65536⟩ := by
  decide +kernel

theorem context_12_112910_763842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112910 ⟨763842, by decide⟩ :=
  accepted_of_selected 12 112910 ⟨763842, by decide⟩ ⟨12, 1, 0, 763842, 112910, 1, 65536⟩
    (by decide) selected_cut_34001

theorem selected_cut_34002 : selected 9 ⟨815334, by decide⟩
    (prefixPartial 12 112911) = some ⟨12, 1, 0, 815334, 112911, 1, 65536⟩ := by
  decide +kernel

theorem context_12_112911_815334 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112911 ⟨815334, by decide⟩ :=
  accepted_of_selected 12 112911 ⟨815334, by decide⟩ ⟨12, 1, 0, 815334, 112911, 1, 65536⟩
    (by decide) selected_cut_34002

theorem unmarked_context_11_28227_878651 : frontier 10 ⟨878651, by decide⟩
    (prefixCache 11 28227) (prefixPartial 11 28227) = false := by
  decide +kernel

theorem node_context_11_28227_878651 : EJMOriginalGlobalDAGData.nodes 10 ⟨878651, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨878650, by decide⟩,⟨763842, by decide⟩,⟨815334, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28227_878651 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28227 ⟨878651, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28227
    ⟨878651, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨878650, by decide⟩,⟨763842, by decide⟩,⟨815334, by decide⟩]) unmarked_context_11_28227_878651 node_context_11_28227_878651
  intro a
  fin_cases a
  · exact context_12_112908_448748
  · exact context_12_112909_878650
  · exact context_12_112910_763842
  · exact context_12_112911_815334

theorem unmarked_context_10_7056_878652 : frontier 11 ⟨878652, by decide⟩
    (prefixCache 10 7056) (prefixPartial 10 7056) = false := by
  decide +kernel

theorem node_context_10_7056_878652 : EJMOriginalGlobalDAGData.nodes 11 ⟨878652, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨878359, by decide⟩,⟨764169, by decide⟩,⟨878651, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_7056_878652 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 7056 ⟨878652, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 7056
    ⟨878652, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨878359, by decide⟩,⟨764169, by decide⟩,⟨878651, by decide⟩]) unmarked_context_10_7056_878652 node_context_10_7056_878652
  intro a
  fin_cases a
  · exact context_11_28224_434745
  · exact context_11_28225_878359
  · exact context_11_28226_764169
  · exact context_11_28227_878651

theorem selected_cut_34003 : selected 8 ⟨878676, by decide⟩
    (prefixPartial 13 451648) = some ⟨13, 2, 0, 878676, 451648, 1573, 16384⟩ := by
  decide +kernel

theorem context_13_451648_878676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451648 ⟨878676, by decide⟩ :=
  accepted_of_selected 13 451648 ⟨878676, by decide⟩ ⟨13, 2, 0, 878676, 451648, 1573, 16384⟩
    (by decide) selected_cut_34003

theorem selected_cut_34004 : selected 8 ⟨878697, by decide⟩
    (prefixPartial 13 451649) = some ⟨13, 2, 0, 878697, 451649, 2013, 16384⟩ := by
  decide +kernel

theorem context_13_451649_878697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451649 ⟨878697, by decide⟩ :=
  accepted_of_selected 13 451649 ⟨878697, by decide⟩ ⟨13, 2, 0, 878697, 451649, 2013, 16384⟩
    (by decide) selected_cut_34004

theorem selected_cut_34005 : selected 8 ⟨878719, by decide⟩
    (prefixPartial 13 451650) = some ⟨13, 2, 0, 878719, 451650, 977, 16384⟩ := by
  decide +kernel

theorem context_13_451650_878719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451650 ⟨878719, by decide⟩ :=
  accepted_of_selected 13 451650 ⟨878719, by decide⟩ ⟨13, 2, 0, 878719, 451650, 977, 16384⟩
    (by decide) selected_cut_34005

theorem selected_cut_34006 : selected 8 ⟨878726, by decide⟩
    (prefixPartial 13 451651) = some ⟨13, 2, 0, 878726, 451651, 693, 16384⟩ := by
  decide +kernel

theorem context_13_451651_878726 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451651 ⟨878726, by decide⟩ :=
  accepted_of_selected 13 451651 ⟨878726, by decide⟩ ⟨13, 2, 0, 878726, 451651, 693, 16384⟩
    (by decide) selected_cut_34006

theorem unmarked_context_12_112912_878727 : frontier 9 ⟨878727, by decide⟩
    (prefixCache 12 112912) (prefixPartial 12 112912) = false := by
  decide +kernel

theorem node_context_12_112912_878727 : EJMOriginalGlobalDAGData.nodes 9 ⟨878727, by decide⟩ =
    .split (coordinate 12) (![⟨878676, by decide⟩,⟨878697, by decide⟩,⟨878719, by decide⟩,⟨878726, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_112912_878727 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112912 ⟨878727, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 112912
    ⟨878727, by decide⟩ (by decide) (![⟨878676, by decide⟩,⟨878697, by decide⟩,⟨878719, by decide⟩,⟨878726, by decide⟩]) unmarked_context_12_112912_878727 node_context_12_112912_878727
  intro a
  fin_cases a
  · exact context_13_451648_878676
  · exact context_13_451649_878697
  · exact context_13_451650_878719
  · exact context_13_451651_878726

theorem selected_cut_34007 : selected 8 ⟨878752, by decide⟩
    (prefixPartial 13 451652) = some ⟨13, 2, 0, 878752, 451652, 1857, 16384⟩ := by
  decide +kernel

theorem context_13_451652_878752 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451652 ⟨878752, by decide⟩ :=
  accepted_of_selected 13 451652 ⟨878752, by decide⟩ ⟨13, 2, 0, 878752, 451652, 1857, 16384⟩
    (by decide) selected_cut_34007

theorem selected_cut_34008 : selected 8 ⟨878775, by decide⟩
    (prefixPartial 13 451653) = some ⟨13, 2, 0, 878775, 451653, 2509, 16384⟩ := by
  decide +kernel

theorem context_13_451653_878775 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451653 ⟨878775, by decide⟩ :=
  accepted_of_selected 13 451653 ⟨878775, by decide⟩ ⟨13, 2, 0, 878775, 451653, 2509, 16384⟩
    (by decide) selected_cut_34008

theorem selected_cut_34009 : selected 8 ⟨878792, by decide⟩
    (prefixPartial 13 451654) = some ⟨13, 2, 0, 878792, 451654, 1193, 16384⟩ := by
  decide +kernel

theorem context_13_451654_878792 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451654 ⟨878792, by decide⟩ :=
  accepted_of_selected 13 451654 ⟨878792, by decide⟩ ⟨13, 2, 0, 878792, 451654, 1193, 16384⟩
    (by decide) selected_cut_34009

theorem selected_cut_34010 : selected 8 ⟨878797, by decide⟩
    (prefixPartial 13 451655) = some ⟨13, 2, 0, 878797, 451655, 857, 16384⟩ := by
  decide +kernel

theorem context_13_451655_878797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451655 ⟨878797, by decide⟩ :=
  accepted_of_selected 13 451655 ⟨878797, by decide⟩ ⟨13, 2, 0, 878797, 451655, 857, 16384⟩
    (by decide) selected_cut_34010

theorem unmarked_context_12_112913_878798 : frontier 9 ⟨878798, by decide⟩
    (prefixCache 12 112913) (prefixPartial 12 112913) = false := by
  decide +kernel

theorem node_context_12_112913_878798 : EJMOriginalGlobalDAGData.nodes 9 ⟨878798, by decide⟩ =
    .split (coordinate 12) (![⟨878752, by decide⟩,⟨878775, by decide⟩,⟨878792, by decide⟩,⟨878797, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_112913_878798 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112913 ⟨878798, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 112913
    ⟨878798, by decide⟩ (by decide) (![⟨878752, by decide⟩,⟨878775, by decide⟩,⟨878792, by decide⟩,⟨878797, by decide⟩]) unmarked_context_12_112913_878798 node_context_12_112913_878798
  intro a
  fin_cases a
  · exact context_13_451652_878752
  · exact context_13_451653_878775
  · exact context_13_451654_878792
  · exact context_13_451655_878797

theorem selected_cut_34011 : selected 8 ⟨878829, by decide⟩
    (prefixPartial 13 451656) = some ⟨13, 2, 0, 878829, 451656, 1765, 16384⟩ := by
  decide +kernel

theorem context_13_451656_878829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451656 ⟨878829, by decide⟩ :=
  accepted_of_selected 13 451656 ⟨878829, by decide⟩ ⟨13, 2, 0, 878829, 451656, 1765, 16384⟩
    (by decide) selected_cut_34011

theorem selected_cut_34012 : selected 8 ⟨878856, by decide⟩
    (prefixPartial 13 451657) = some ⟨13, 2, 0, 878856, 451657, 2321, 16384⟩ := by
  decide +kernel

theorem context_13_451657_878856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451657 ⟨878856, by decide⟩ :=
  accepted_of_selected 13 451657 ⟨878856, by decide⟩ ⟨13, 2, 0, 878856, 451657, 2321, 16384⟩
    (by decide) selected_cut_34012

theorem selected_cut_34013 : selected 8 ⟨878879, by decide⟩
    (prefixPartial 13 451658) = some ⟨13, 2, 0, 878879, 451658, 1125, 16384⟩ := by
  decide +kernel

theorem context_13_451658_878879 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451658 ⟨878879, by decide⟩ :=
  accepted_of_selected 13 451658 ⟨878879, by decide⟩ ⟨13, 2, 0, 878879, 451658, 1125, 16384⟩
    (by decide) selected_cut_34013

theorem selected_cut_34014 : selected 8 ⟨878886, by decide⟩
    (prefixPartial 13 451659) = some ⟨13, 2, 0, 878886, 451659, 837, 16384⟩ := by
  decide +kernel

theorem context_13_451659_878886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451659 ⟨878886, by decide⟩ :=
  accepted_of_selected 13 451659 ⟨878886, by decide⟩ ⟨13, 2, 0, 878886, 451659, 837, 16384⟩
    (by decide) selected_cut_34014

theorem unmarked_context_12_112914_878887 : frontier 9 ⟨878887, by decide⟩
    (prefixCache 12 112914) (prefixPartial 12 112914) = false := by
  decide +kernel

theorem node_context_12_112914_878887 : EJMOriginalGlobalDAGData.nodes 9 ⟨878887, by decide⟩ =
    .split (coordinate 12) (![⟨878829, by decide⟩,⟨878856, by decide⟩,⟨878879, by decide⟩,⟨878886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_112914_878887 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112914 ⟨878887, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 112914
    ⟨878887, by decide⟩ (by decide) (![⟨878829, by decide⟩,⟨878856, by decide⟩,⟨878879, by decide⟩,⟨878886, by decide⟩]) unmarked_context_12_112914_878887 node_context_12_112914_878887
  intro a
  fin_cases a
  · exact context_13_451656_878829
  · exact context_13_451657_878856
  · exact context_13_451658_878879
  · exact context_13_451659_878886

theorem selected_cut_34015 : selected 8 ⟨878917, by decide⟩
    (prefixPartial 13 451660) = some ⟨13, 2, 0, 878917, 451660, 1745, 16384⟩ := by
  decide +kernel

theorem context_13_451660_878917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451660 ⟨878917, by decide⟩ :=
  accepted_of_selected 13 451660 ⟨878917, by decide⟩ ⟨13, 2, 0, 878917, 451660, 1745, 16384⟩
    (by decide) selected_cut_34015

theorem selected_cut_34016 : selected 8 ⟨878948, by decide⟩
    (prefixPartial 13 451661) = some ⟨13, 2, 0, 878948, 451661, 2457, 16384⟩ := by
  decide +kernel

theorem context_13_451661_878948 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451661 ⟨878948, by decide⟩ :=
  accepted_of_selected 13 451661 ⟨878948, by decide⟩ ⟨13, 2, 0, 878948, 451661, 2457, 16384⟩
    (by decide) selected_cut_34016

theorem selected_cut_34017 : selected 8 ⟨878968, by decide⟩
    (prefixPartial 13 451662) = some ⟨13, 2, 0, 878968, 451662, 1173, 16384⟩ := by
  decide +kernel

theorem context_13_451662_878968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451662 ⟨878968, by decide⟩ :=
  accepted_of_selected 13 451662 ⟨878968, by decide⟩ ⟨13, 2, 0, 878968, 451662, 1173, 16384⟩
    (by decide) selected_cut_34017

theorem selected_cut_34018 : selected 8 ⟨878973, by decide⟩
    (prefixPartial 13 451663) = some ⟨13, 2, 0, 878973, 451663, 801, 16384⟩ := by
  decide +kernel

theorem context_13_451663_878973 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451663 ⟨878973, by decide⟩ :=
  accepted_of_selected 13 451663 ⟨878973, by decide⟩ ⟨13, 2, 0, 878973, 451663, 801, 16384⟩
    (by decide) selected_cut_34018

theorem unmarked_context_12_112915_878974 : frontier 9 ⟨878974, by decide⟩
    (prefixCache 12 112915) (prefixPartial 12 112915) = false := by
  decide +kernel

theorem node_context_12_112915_878974 : EJMOriginalGlobalDAGData.nodes 9 ⟨878974, by decide⟩ =
    .split (coordinate 12) (![⟨878917, by decide⟩,⟨878948, by decide⟩,⟨878968, by decide⟩,⟨878973, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_112915_878974 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112915 ⟨878974, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 112915
    ⟨878974, by decide⟩ (by decide) (![⟨878917, by decide⟩,⟨878948, by decide⟩,⟨878968, by decide⟩,⟨878973, by decide⟩]) unmarked_context_12_112915_878974 node_context_12_112915_878974
  intro a
  fin_cases a
  · exact context_13_451660_878917
  · exact context_13_451661_878948
  · exact context_13_451662_878968
  · exact context_13_451663_878973

theorem unmarked_context_11_28228_878975 : frontier 10 ⟨878975, by decide⟩
    (prefixCache 11 28228) (prefixPartial 11 28228) = false := by
  decide +kernel

theorem node_context_11_28228_878975 : EJMOriginalGlobalDAGData.nodes 10 ⟨878975, by decide⟩ =
    .split (coordinate 11) (![⟨878727, by decide⟩,⟨878798, by decide⟩,⟨878887, by decide⟩,⟨878974, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28228_878975 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28228 ⟨878975, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28228
    ⟨878975, by decide⟩ (by decide) (![⟨878727, by decide⟩,⟨878798, by decide⟩,⟨878887, by decide⟩,⟨878974, by decide⟩]) unmarked_context_11_28228_878975 node_context_11_28228_878975
  intro a
  fin_cases a
  · exact context_12_112912_878727
  · exact context_12_112913_878798
  · exact context_12_112914_878887
  · exact context_12_112915_878974

theorem selected_cut_34019 : selected 8 ⟨878993, by decide⟩
    (prefixPartial 13 451664) = some ⟨13, 2, 0, 878993, 451664, 1217, 16384⟩ := by
  decide +kernel

theorem context_13_451664_878993 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451664 ⟨878993, by decide⟩ :=
  accepted_of_selected 13 451664 ⟨878993, by decide⟩ ⟨13, 2, 0, 878993, 451664, 1217, 16384⟩
    (by decide) selected_cut_34019

theorem selected_cut_34020 : selected 8 ⟨879013, by decide⟩
    (prefixPartial 13 451665) = some ⟨13, 2, 0, 879013, 451665, 1597, 16384⟩ := by
  decide +kernel

theorem context_13_451665_879013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451665 ⟨879013, by decide⟩ :=
  accepted_of_selected 13 451665 ⟨879013, by decide⟩ ⟨13, 2, 0, 879013, 451665, 1597, 16384⟩
    (by decide) selected_cut_34020

theorem selected_cut_34021 : selected 8 ⟨879028, by decide⟩
    (prefixPartial 13 451666) = some ⟨13, 2, 0, 879028, 451666, 649, 16384⟩ := by
  decide +kernel

theorem context_13_451666_879028 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451666 ⟨879028, by decide⟩ :=
  accepted_of_selected 13 451666 ⟨879028, by decide⟩ ⟨13, 2, 0, 879028, 451666, 649, 16384⟩
    (by decide) selected_cut_34021

theorem selected_cut_34022 : selected 8 ⟨879036, by decide⟩
    (prefixPartial 13 451667) = some ⟨13, 2, 0, 879036, 451667, 645, 16384⟩ := by
  decide +kernel

theorem context_13_451667_879036 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451667 ⟨879036, by decide⟩ :=
  accepted_of_selected 13 451667 ⟨879036, by decide⟩ ⟨13, 2, 0, 879036, 451667, 645, 16384⟩
    (by decide) selected_cut_34022

theorem unmarked_context_12_112916_879037 : frontier 9 ⟨879037, by decide⟩
    (prefixCache 12 112916) (prefixPartial 12 112916) = false := by
  decide +kernel

theorem node_context_12_112916_879037 : EJMOriginalGlobalDAGData.nodes 9 ⟨879037, by decide⟩ =
    .split (coordinate 12) (![⟨878993, by decide⟩,⟨879013, by decide⟩,⟨879028, by decide⟩,⟨879036, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_112916_879037 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112916 ⟨879037, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 112916
    ⟨879037, by decide⟩ (by decide) (![⟨878993, by decide⟩,⟨879013, by decide⟩,⟨879028, by decide⟩,⟨879036, by decide⟩]) unmarked_context_12_112916_879037 node_context_12_112916_879037
  intro a
  fin_cases a
  · exact context_13_451664_878993
  · exact context_13_451665_879013
  · exact context_13_451666_879028
  · exact context_13_451667_879036

theorem selected_cut_34023 : selected 9 ⟨439069, by decide⟩
    (prefixPartial 12 112917) = some ⟨12, 1, 0, 439069, 112917, 1, 65536⟩ := by
  decide +kernel

theorem context_12_112917_439069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112917 ⟨439069, by decide⟩ :=
  accepted_of_selected 12 112917 ⟨439069, by decide⟩ ⟨12, 1, 0, 439069, 112917, 1, 65536⟩
    (by decide) selected_cut_34023

theorem selected_cut_34024 : selected 8 ⟨879062, by decide⟩
    (prefixPartial 13 451672) = some ⟨13, 2, 0, 879062, 451672, 1457, 16384⟩ := by
  decide +kernel

theorem context_13_451672_879062 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451672 ⟨879062, by decide⟩ :=
  accepted_of_selected 13 451672 ⟨879062, by decide⟩ ⟨13, 2, 0, 879062, 451672, 1457, 16384⟩
    (by decide) selected_cut_34024

theorem selected_cut_34025 : selected 8 ⟨879084, by decide⟩
    (prefixPartial 13 451673) = some ⟨13, 2, 0, 879084, 451673, 1845, 16384⟩ := by
  decide +kernel

theorem context_13_451673_879084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451673 ⟨879084, by decide⟩ :=
  accepted_of_selected 13 451673 ⟨879084, by decide⟩ ⟨13, 2, 0, 879084, 451673, 1845, 16384⟩
    (by decide) selected_cut_34025

theorem selected_cut_34026 : selected 8 ⟨879104, by decide⟩
    (prefixPartial 13 451674) = some ⟨13, 2, 0, 879104, 451674, 801, 16384⟩ := by
  decide +kernel

theorem context_13_451674_879104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451674 ⟨879104, by decide⟩ :=
  accepted_of_selected 13 451674 ⟨879104, by decide⟩ ⟨13, 2, 0, 879104, 451674, 801, 16384⟩
    (by decide) selected_cut_34026

theorem selected_cut_34027 : selected 8 ⟨879111, by decide⟩
    (prefixPartial 13 451675) = some ⟨13, 2, 0, 879111, 451675, 833, 16384⟩ := by
  decide +kernel

theorem context_13_451675_879111 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451675 ⟨879111, by decide⟩ :=
  accepted_of_selected 13 451675 ⟨879111, by decide⟩ ⟨13, 2, 0, 879111, 451675, 833, 16384⟩
    (by decide) selected_cut_34027

theorem unmarked_context_12_112918_879112 : frontier 9 ⟨879112, by decide⟩
    (prefixCache 12 112918) (prefixPartial 12 112918) = false := by
  decide +kernel

theorem node_context_12_112918_879112 : EJMOriginalGlobalDAGData.nodes 9 ⟨879112, by decide⟩ =
    .split (coordinate 12) (![⟨879062, by decide⟩,⟨879084, by decide⟩,⟨879104, by decide⟩,⟨879111, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_112918_879112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112918 ⟨879112, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 112918
    ⟨879112, by decide⟩ (by decide) (![⟨879062, by decide⟩,⟨879084, by decide⟩,⟨879104, by decide⟩,⟨879111, by decide⟩]) unmarked_context_12_112918_879112 node_context_12_112918_879112
  intro a
  fin_cases a
  · exact context_13_451672_879062
  · exact context_13_451673_879084
  · exact context_13_451674_879104
  · exact context_13_451675_879111

theorem selected_cut_34028 : selected 8 ⟨879138, by decide⟩
    (prefixPartial 13 451676) = some ⟨13, 2, 0, 879138, 451676, 1437, 16384⟩ := by
  decide +kernel

theorem context_13_451676_879138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451676 ⟨879138, by decide⟩ :=
  accepted_of_selected 13 451676 ⟨879138, by decide⟩ ⟨13, 2, 0, 879138, 451676, 1437, 16384⟩
    (by decide) selected_cut_34028

theorem selected_cut_34029 : selected 8 ⟨879165, by decide⟩
    (prefixPartial 13 451677) = some ⟨13, 2, 0, 879165, 451677, 1953, 16384⟩ := by
  decide +kernel

theorem context_13_451677_879165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451677 ⟨879165, by decide⟩ :=
  accepted_of_selected 13 451677 ⟨879165, by decide⟩ ⟨13, 2, 0, 879165, 451677, 1953, 16384⟩
    (by decide) selected_cut_34029

theorem selected_cut_34030 : selected 8 ⟨879179, by decide⟩
    (prefixPartial 13 451678) = some ⟨13, 2, 0, 879179, 451678, 785, 16384⟩ := by
  decide +kernel

theorem context_13_451678_879179 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451678 ⟨879179, by decide⟩ :=
  accepted_of_selected 13 451678 ⟨879179, by decide⟩ ⟨13, 2, 0, 879179, 451678, 785, 16384⟩
    (by decide) selected_cut_34030

theorem selected_cut_34031 : selected 8 ⟨879184, by decide⟩
    (prefixPartial 13 451679) = some ⟨13, 2, 0, 879184, 451679, 693, 16384⟩ := by
  decide +kernel

theorem context_13_451679_879184 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451679 ⟨879184, by decide⟩ :=
  accepted_of_selected 13 451679 ⟨879184, by decide⟩ ⟨13, 2, 0, 879184, 451679, 693, 16384⟩
    (by decide) selected_cut_34031

theorem unmarked_context_12_112919_879185 : frontier 9 ⟨879185, by decide⟩
    (prefixCache 12 112919) (prefixPartial 12 112919) = false := by
  decide +kernel

theorem node_context_12_112919_879185 : EJMOriginalGlobalDAGData.nodes 9 ⟨879185, by decide⟩ =
    .split (coordinate 12) (![⟨879138, by decide⟩,⟨879165, by decide⟩,⟨879179, by decide⟩,⟨879184, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_112919_879185 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112919 ⟨879185, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 112919
    ⟨879185, by decide⟩ (by decide) (![⟨879138, by decide⟩,⟨879165, by decide⟩,⟨879179, by decide⟩,⟨879184, by decide⟩]) unmarked_context_12_112919_879185 node_context_12_112919_879185
  intro a
  fin_cases a
  · exact context_13_451676_879138
  · exact context_13_451677_879165
  · exact context_13_451678_879179
  · exact context_13_451679_879184

theorem unmarked_context_11_28229_879186 : frontier 10 ⟨879186, by decide⟩
    (prefixCache 11 28229) (prefixPartial 11 28229) = false := by
  decide +kernel

theorem node_context_11_28229_879186 : EJMOriginalGlobalDAGData.nodes 10 ⟨879186, by decide⟩ =
    .split (coordinate 11) (![⟨879037, by decide⟩,⟨439069, by decide⟩,⟨879112, by decide⟩,⟨879185, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28229_879186 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28229 ⟨879186, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28229
    ⟨879186, by decide⟩ (by decide) (![⟨879037, by decide⟩,⟨439069, by decide⟩,⟨879112, by decide⟩,⟨879185, by decide⟩]) unmarked_context_11_28229_879186 node_context_11_28229_879186
  intro a
  fin_cases a
  · exact context_12_112916_879037
  · exact context_12_112917_439069
  · exact context_12_112918_879112
  · exact context_12_112919_879185

theorem selected_cut_34032 : selected 8 ⟨879202, by decide⟩
    (prefixPartial 13 451680) = some ⟨13, 2, 0, 879202, 451680, 1153, 16384⟩ := by
  decide +kernel

theorem context_13_451680_879202 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451680 ⟨879202, by decide⟩ :=
  accepted_of_selected 13 451680 ⟨879202, by decide⟩ ⟨13, 2, 0, 879202, 451680, 1153, 16384⟩
    (by decide) selected_cut_34032

theorem selected_cut_34033 : selected 8 ⟨879223, by decide⟩
    (prefixPartial 13 451681) = some ⟨13, 2, 0, 879223, 451681, 2085, 16384⟩ := by
  decide +kernel

theorem context_13_451681_879223 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451681 ⟨879223, by decide⟩ :=
  accepted_of_selected 13 451681 ⟨879223, by decide⟩ ⟨13, 2, 0, 879223, 451681, 2085, 16384⟩
    (by decide) selected_cut_34033

theorem selected_cut_34034 : selected 8 ⟨879243, by decide⟩
    (prefixPartial 13 451682) = some ⟨13, 2, 0, 879243, 451682, 1037, 16384⟩ := by
  decide +kernel

theorem context_13_451682_879243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451682 ⟨879243, by decide⟩ :=
  accepted_of_selected 13 451682 ⟨879243, by decide⟩ ⟨13, 2, 0, 879243, 451682, 1037, 16384⟩
    (by decide) selected_cut_34034

theorem selected_cut_34035 : selected 8 ⟨879247, by decide⟩
    (prefixPartial 13 451683) = some ⟨13, 2, 0, 879247, 451683, 673, 16384⟩ := by
  decide +kernel

theorem context_13_451683_879247 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451683 ⟨879247, by decide⟩ :=
  accepted_of_selected 13 451683 ⟨879247, by decide⟩ ⟨13, 2, 0, 879247, 451683, 673, 16384⟩
    (by decide) selected_cut_34035

theorem unmarked_context_12_112920_879248 : frontier 9 ⟨879248, by decide⟩
    (prefixCache 12 112920) (prefixPartial 12 112920) = false := by
  decide +kernel

theorem node_context_12_112920_879248 : EJMOriginalGlobalDAGData.nodes 9 ⟨879248, by decide⟩ =
    .split (coordinate 12) (![⟨879202, by decide⟩,⟨879223, by decide⟩,⟨879243, by decide⟩,⟨879247, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_112920_879248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112920 ⟨879248, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 112920
    ⟨879248, by decide⟩ (by decide) (![⟨879202, by decide⟩,⟨879223, by decide⟩,⟨879243, by decide⟩,⟨879247, by decide⟩]) unmarked_context_12_112920_879248 node_context_12_112920_879248
  intro a
  fin_cases a
  · exact context_13_451680_879202
  · exact context_13_451681_879223
  · exact context_13_451682_879243
  · exact context_13_451683_879247

theorem selected_cut_34036 : selected 8 ⟨879268, by decide⟩
    (prefixPartial 13 451684) = some ⟨13, 2, 0, 879268, 451684, 1485, 16384⟩ := by
  decide +kernel

theorem context_13_451684_879268 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451684 ⟨879268, by decide⟩ :=
  accepted_of_selected 13 451684 ⟨879268, by decide⟩ ⟨13, 2, 0, 879268, 451684, 1485, 16384⟩
    (by decide) selected_cut_34036

theorem selected_cut_34037 : selected 8 ⟨879299, by decide⟩
    (prefixPartial 13 451685) = some ⟨13, 2, 0, 879299, 451685, 2369, 16384⟩ := by
  decide +kernel

theorem context_13_451685_879299 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451685 ⟨879299, by decide⟩ :=
  accepted_of_selected 13 451685 ⟨879299, by decide⟩ ⟨13, 2, 0, 879299, 451685, 2369, 16384⟩
    (by decide) selected_cut_34037

theorem selected_cut_34038 : selected 8 ⟨879314, by decide⟩
    (prefixPartial 13 451686) = some ⟨13, 2, 0, 879314, 451686, 1197, 16384⟩ := by
  decide +kernel

theorem context_13_451686_879314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451686 ⟨879314, by decide⟩ :=
  accepted_of_selected 13 451686 ⟨879314, by decide⟩ ⟨13, 2, 0, 879314, 451686, 1197, 16384⟩
    (by decide) selected_cut_34038

theorem selected_cut_34039 : selected 8 ⟨879324, by decide⟩
    (prefixPartial 13 451687) = some ⟨13, 2, 0, 879324, 451687, 833, 16384⟩ := by
  decide +kernel

theorem context_13_451687_879324 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451687 ⟨879324, by decide⟩ :=
  accepted_of_selected 13 451687 ⟨879324, by decide⟩ ⟨13, 2, 0, 879324, 451687, 833, 16384⟩
    (by decide) selected_cut_34039

theorem unmarked_context_12_112921_879325 : frontier 9 ⟨879325, by decide⟩
    (prefixCache 12 112921) (prefixPartial 12 112921) = false := by
  decide +kernel

theorem node_context_12_112921_879325 : EJMOriginalGlobalDAGData.nodes 9 ⟨879325, by decide⟩ =
    .split (coordinate 12) (![⟨879268, by decide⟩,⟨879299, by decide⟩,⟨879314, by decide⟩,⟨879324, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_112921_879325 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112921 ⟨879325, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 112921
    ⟨879325, by decide⟩ (by decide) (![⟨879268, by decide⟩,⟨879299, by decide⟩,⟨879314, by decide⟩,⟨879324, by decide⟩]) unmarked_context_12_112921_879325 node_context_12_112921_879325
  intro a
  fin_cases a
  · exact context_13_451684_879268
  · exact context_13_451685_879299
  · exact context_13_451686_879314
  · exact context_13_451687_879324

theorem selected_cut_34040 : selected 8 ⟨879346, by decide⟩
    (prefixPartial 13 451688) = some ⟨13, 2, 0, 879346, 451688, 1365, 16384⟩ := by
  decide +kernel

theorem context_13_451688_879346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451688 ⟨879346, by decide⟩ :=
  accepted_of_selected 13 451688 ⟨879346, by decide⟩ ⟨13, 2, 0, 879346, 451688, 1365, 16384⟩
    (by decide) selected_cut_34040

theorem selected_cut_34041 : selected 8 ⟨879367, by decide⟩
    (prefixPartial 13 451689) = some ⟨13, 2, 0, 879367, 451689, 2077, 16384⟩ := by
  decide +kernel

theorem context_13_451689_879367 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451689 ⟨879367, by decide⟩ :=
  accepted_of_selected 13 451689 ⟨879367, by decide⟩ ⟨13, 2, 0, 879367, 451689, 2077, 16384⟩
    (by decide) selected_cut_34041

theorem selected_cut_34042 : selected 8 ⟨879388, by decide⟩
    (prefixPartial 13 451690) = some ⟨13, 2, 0, 879388, 451690, 1205, 16384⟩ := by
  decide +kernel

theorem context_13_451690_879388 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451690 ⟨879388, by decide⟩ :=
  accepted_of_selected 13 451690 ⟨879388, by decide⟩ ⟨13, 2, 0, 879388, 451690, 1205, 16384⟩
    (by decide) selected_cut_34042

theorem selected_cut_34043 : selected 8 ⟨879398, by decide⟩
    (prefixPartial 13 451691) = some ⟨13, 2, 0, 879398, 451691, 817, 16384⟩ := by
  decide +kernel

theorem context_13_451691_879398 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451691 ⟨879398, by decide⟩ :=
  accepted_of_selected 13 451691 ⟨879398, by decide⟩ ⟨13, 2, 0, 879398, 451691, 817, 16384⟩
    (by decide) selected_cut_34043

theorem unmarked_context_12_112922_879399 : frontier 9 ⟨879399, by decide⟩
    (prefixCache 12 112922) (prefixPartial 12 112922) = false := by
  decide +kernel

theorem node_context_12_112922_879399 : EJMOriginalGlobalDAGData.nodes 9 ⟨879399, by decide⟩ =
    .split (coordinate 12) (![⟨879346, by decide⟩,⟨879367, by decide⟩,⟨879388, by decide⟩,⟨879398, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_112922_879399 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112922 ⟨879399, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 112922
    ⟨879399, by decide⟩ (by decide) (![⟨879346, by decide⟩,⟨879367, by decide⟩,⟨879388, by decide⟩,⟨879398, by decide⟩]) unmarked_context_12_112922_879399 node_context_12_112922_879399
  intro a
  fin_cases a
  · exact context_13_451688_879346
  · exact context_13_451689_879367
  · exact context_13_451690_879388
  · exact context_13_451691_879398

theorem selected_cut_34044 : selected 8 ⟨879421, by decide⟩
    (prefixPartial 13 451692) = some ⟨13, 2, 0, 879421, 451692, 1293, 16384⟩ := by
  decide +kernel

theorem context_13_451692_879421 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451692 ⟨879421, by decide⟩ :=
  accepted_of_selected 13 451692 ⟨879421, by decide⟩ ⟨13, 2, 0, 879421, 451692, 1293, 16384⟩
    (by decide) selected_cut_34044

theorem selected_cut_34045 : selected 8 ⟨879455, by decide⟩
    (prefixPartial 13 451693) = some ⟨13, 2, 0, 879455, 451693, 2245, 16384⟩ := by
  decide +kernel

theorem context_13_451693_879455 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451693 ⟨879455, by decide⟩ :=
  accepted_of_selected 13 451693 ⟨879455, by decide⟩ ⟨13, 2, 0, 879455, 451693, 2245, 16384⟩
    (by decide) selected_cut_34045

theorem selected_cut_34046 : selected 8 ⟨879478, by decide⟩
    (prefixPartial 13 451694) = some ⟨13, 2, 0, 879478, 451694, 1165, 16384⟩ := by
  decide +kernel

theorem context_13_451694_879478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451694 ⟨879478, by decide⟩ :=
  accepted_of_selected 13 451694 ⟨879478, by decide⟩ ⟨13, 2, 0, 879478, 451694, 1165, 16384⟩
    (by decide) selected_cut_34046

theorem selected_cut_34047 : selected 8 ⟨879484, by decide⟩
    (prefixPartial 13 451695) = some ⟨13, 2, 0, 879484, 451695, 685, 16384⟩ := by
  decide +kernel

theorem context_13_451695_879484 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451695 ⟨879484, by decide⟩ :=
  accepted_of_selected 13 451695 ⟨879484, by decide⟩ ⟨13, 2, 0, 879484, 451695, 685, 16384⟩
    (by decide) selected_cut_34047

theorem unmarked_context_12_112923_879485 : frontier 9 ⟨879485, by decide⟩
    (prefixCache 12 112923) (prefixPartial 12 112923) = false := by
  decide +kernel

theorem node_context_12_112923_879485 : EJMOriginalGlobalDAGData.nodes 9 ⟨879485, by decide⟩ =
    .split (coordinate 12) (![⟨879421, by decide⟩,⟨879455, by decide⟩,⟨879478, by decide⟩,⟨879484, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_112923_879485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112923 ⟨879485, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 112923
    ⟨879485, by decide⟩ (by decide) (![⟨879421, by decide⟩,⟨879455, by decide⟩,⟨879478, by decide⟩,⟨879484, by decide⟩]) unmarked_context_12_112923_879485 node_context_12_112923_879485
  intro a
  fin_cases a
  · exact context_13_451692_879421
  · exact context_13_451693_879455
  · exact context_13_451694_879478
  · exact context_13_451695_879484

theorem unmarked_context_11_28230_879486 : frontier 10 ⟨879486, by decide⟩
    (prefixCache 11 28230) (prefixPartial 11 28230) = false := by
  decide +kernel

theorem node_context_11_28230_879486 : EJMOriginalGlobalDAGData.nodes 10 ⟨879486, by decide⟩ =
    .split (coordinate 11) (![⟨879248, by decide⟩,⟨879325, by decide⟩,⟨879399, by decide⟩,⟨879485, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28230_879486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28230 ⟨879486, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28230
    ⟨879486, by decide⟩ (by decide) (![⟨879248, by decide⟩,⟨879325, by decide⟩,⟨879399, by decide⟩,⟨879485, by decide⟩]) unmarked_context_11_28230_879486 node_context_11_28230_879486
  intro a
  fin_cases a
  · exact context_12_112920_879248
  · exact context_12_112921_879325
  · exact context_12_112922_879399
  · exact context_12_112923_879485

theorem selected_cut_34048 : selected 8 ⟨879503, by decide⟩
    (prefixPartial 13 451696) = some ⟨13, 2, 0, 879503, 451696, 1153, 16384⟩ := by
  decide +kernel

theorem context_13_451696_879503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451696 ⟨879503, by decide⟩ :=
  accepted_of_selected 13 451696 ⟨879503, by decide⟩ ⟨13, 2, 0, 879503, 451696, 1153, 16384⟩
    (by decide) selected_cut_34048

theorem selected_cut_34049 : selected 8 ⟨879531, by decide⟩
    (prefixPartial 13 451697) = some ⟨13, 2, 0, 879531, 451697, 2165, 16384⟩ := by
  decide +kernel

theorem context_13_451697_879531 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451697 ⟨879531, by decide⟩ :=
  accepted_of_selected 13 451697 ⟨879531, by decide⟩ ⟨13, 2, 0, 879531, 451697, 2165, 16384⟩
    (by decide) selected_cut_34049

theorem selected_cut_34050 : selected 8 ⟨879551, by decide⟩
    (prefixPartial 13 451698) = some ⟨13, 2, 0, 879551, 451698, 1117, 16384⟩ := by
  decide +kernel

theorem context_13_451698_879551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451698 ⟨879551, by decide⟩ :=
  accepted_of_selected 13 451698 ⟨879551, by decide⟩ ⟨13, 2, 0, 879551, 451698, 1117, 16384⟩
    (by decide) selected_cut_34050

theorem selected_cut_34051 : selected 8 ⟨879556, by decide⟩
    (prefixPartial 13 451699) = some ⟨13, 2, 0, 879556, 451699, 733, 16384⟩ := by
  decide +kernel

theorem context_13_451699_879556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451699 ⟨879556, by decide⟩ :=
  accepted_of_selected 13 451699 ⟨879556, by decide⟩ ⟨13, 2, 0, 879556, 451699, 733, 16384⟩
    (by decide) selected_cut_34051

theorem unmarked_context_12_112924_879557 : frontier 9 ⟨879557, by decide⟩
    (prefixCache 12 112924) (prefixPartial 12 112924) = false := by
  decide +kernel

theorem node_context_12_112924_879557 : EJMOriginalGlobalDAGData.nodes 9 ⟨879557, by decide⟩ =
    .split (coordinate 12) (![⟨879503, by decide⟩,⟨879531, by decide⟩,⟨879551, by decide⟩,⟨879556, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_112924_879557 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112924 ⟨879557, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 112924
    ⟨879557, by decide⟩ (by decide) (![⟨879503, by decide⟩,⟨879531, by decide⟩,⟨879551, by decide⟩,⟨879556, by decide⟩]) unmarked_context_12_112924_879557 node_context_12_112924_879557
  intro a
  fin_cases a
  · exact context_13_451696_879503
  · exact context_13_451697_879531
  · exact context_13_451698_879551
  · exact context_13_451699_879556

theorem selected_cut_34052 : selected 8 ⟨879577, by decide⟩
    (prefixPartial 13 451700) = some ⟨13, 2, 0, 879577, 451700, 1437, 16384⟩ := by
  decide +kernel

theorem context_13_451700_879577 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451700 ⟨879577, by decide⟩ :=
  accepted_of_selected 13 451700 ⟨879577, by decide⟩ ⟨13, 2, 0, 879577, 451700, 1437, 16384⟩
    (by decide) selected_cut_34052

theorem selected_cut_34053 : selected 8 ⟨879608, by decide⟩
    (prefixPartial 13 451701) = some ⟨13, 2, 0, 879608, 451701, 2429, 16384⟩ := by
  decide +kernel

theorem context_13_451701_879608 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451701 ⟨879608, by decide⟩ :=
  accepted_of_selected 13 451701 ⟨879608, by decide⟩ ⟨13, 2, 0, 879608, 451701, 2429, 16384⟩
    (by decide) selected_cut_34053

theorem selected_cut_34054 : selected 8 ⟨879626, by decide⟩
    (prefixPartial 13 451702) = some ⟨13, 2, 0, 879626, 451702, 1361, 16384⟩ := by
  decide +kernel

theorem context_13_451702_879626 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451702 ⟨879626, by decide⟩ :=
  accepted_of_selected 13 451702 ⟨879626, by decide⟩ ⟨13, 2, 0, 879626, 451702, 1361, 16384⟩
    (by decide) selected_cut_34054

theorem selected_cut_34055 : selected 8 ⟨879634, by decide⟩
    (prefixPartial 13 451703) = some ⟨13, 2, 0, 879634, 451703, 925, 16384⟩ := by
  decide +kernel

theorem context_13_451703_879634 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451703 ⟨879634, by decide⟩ :=
  accepted_of_selected 13 451703 ⟨879634, by decide⟩ ⟨13, 2, 0, 879634, 451703, 925, 16384⟩
    (by decide) selected_cut_34055

theorem unmarked_context_12_112925_879635 : frontier 9 ⟨879635, by decide⟩
    (prefixCache 12 112925) (prefixPartial 12 112925) = false := by
  decide +kernel

theorem node_context_12_112925_879635 : EJMOriginalGlobalDAGData.nodes 9 ⟨879635, by decide⟩ =
    .split (coordinate 12) (![⟨879577, by decide⟩,⟨879608, by decide⟩,⟨879626, by decide⟩,⟨879634, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_112925_879635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112925 ⟨879635, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 112925
    ⟨879635, by decide⟩ (by decide) (![⟨879577, by decide⟩,⟨879608, by decide⟩,⟨879626, by decide⟩,⟨879634, by decide⟩]) unmarked_context_12_112925_879635 node_context_12_112925_879635
  intro a
  fin_cases a
  · exact context_13_451700_879577
  · exact context_13_451701_879608
  · exact context_13_451702_879626
  · exact context_13_451703_879634

theorem selected_cut_34056 : selected 8 ⟨879657, by decide⟩
    (prefixPartial 13 451704) = some ⟨13, 2, 0, 879657, 451704, 1285, 16384⟩ := by
  decide +kernel

theorem context_13_451704_879657 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451704 ⟨879657, by decide⟩ :=
  accepted_of_selected 13 451704 ⟨879657, by decide⟩ ⟨13, 2, 0, 879657, 451704, 1285, 16384⟩
    (by decide) selected_cut_34056

theorem selected_cut_34057 : selected 8 ⟨879689, by decide⟩
    (prefixPartial 13 451705) = some ⟨13, 2, 0, 879689, 451705, 2389, 16384⟩ := by
  decide +kernel

theorem context_13_451705_879689 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451705 ⟨879689, by decide⟩ :=
  accepted_of_selected 13 451705 ⟨879689, by decide⟩ ⟨13, 2, 0, 879689, 451705, 2389, 16384⟩
    (by decide) selected_cut_34057

theorem selected_cut_34058 : selected 8 ⟨879707, by decide⟩
    (prefixPartial 13 451706) = some ⟨13, 2, 0, 879707, 451706, 1193, 16384⟩ := by
  decide +kernel

theorem context_13_451706_879707 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451706 ⟨879707, by decide⟩ :=
  accepted_of_selected 13 451706 ⟨879707, by decide⟩ ⟨13, 2, 0, 879707, 451706, 1193, 16384⟩
    (by decide) selected_cut_34058

theorem selected_cut_34059 : selected 8 ⟨879715, by decide⟩
    (prefixPartial 13 451707) = some ⟨13, 2, 0, 879715, 451707, 921, 16384⟩ := by
  decide +kernel

theorem context_13_451707_879715 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451707 ⟨879715, by decide⟩ :=
  accepted_of_selected 13 451707 ⟨879715, by decide⟩ ⟨13, 2, 0, 879715, 451707, 921, 16384⟩
    (by decide) selected_cut_34059

theorem unmarked_context_12_112926_879716 : frontier 9 ⟨879716, by decide⟩
    (prefixCache 12 112926) (prefixPartial 12 112926) = false := by
  decide +kernel

theorem node_context_12_112926_879716 : EJMOriginalGlobalDAGData.nodes 9 ⟨879716, by decide⟩ =
    .split (coordinate 12) (![⟨879657, by decide⟩,⟨879689, by decide⟩,⟨879707, by decide⟩,⟨879715, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_112926_879716 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112926 ⟨879716, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 112926
    ⟨879716, by decide⟩ (by decide) (![⟨879657, by decide⟩,⟨879689, by decide⟩,⟨879707, by decide⟩,⟨879715, by decide⟩]) unmarked_context_12_112926_879716 node_context_12_112926_879716
  intro a
  fin_cases a
  · exact context_13_451704_879657
  · exact context_13_451705_879689
  · exact context_13_451706_879707
  · exact context_13_451707_879715

theorem selected_cut_34060 : selected 8 ⟨879737, by decide⟩
    (prefixPartial 13 451708) = some ⟨13, 2, 0, 879737, 451708, 1185, 16384⟩ := by
  decide +kernel

theorem context_13_451708_879737 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451708 ⟨879737, by decide⟩ :=
  accepted_of_selected 13 451708 ⟨879737, by decide⟩ ⟨13, 2, 0, 879737, 451708, 1185, 16384⟩
    (by decide) selected_cut_34060

theorem selected_cut_34061 : selected 8 ⟨879764, by decide⟩
    (prefixPartial 13 451709) = some ⟨13, 2, 0, 879764, 451709, 2397, 16384⟩ := by
  decide +kernel

theorem context_13_451709_879764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451709 ⟨879764, by decide⟩ :=
  accepted_of_selected 13 451709 ⟨879764, by decide⟩ ⟨13, 2, 0, 879764, 451709, 2397, 16384⟩
    (by decide) selected_cut_34061

theorem selected_cut_34062 : selected 8 ⟨879782, by decide⟩
    (prefixPartial 13 451710) = some ⟨13, 2, 0, 879782, 451710, 1165, 16384⟩ := by
  decide +kernel

theorem context_13_451710_879782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451710 ⟨879782, by decide⟩ :=
  accepted_of_selected 13 451710 ⟨879782, by decide⟩ ⟨13, 2, 0, 879782, 451710, 1165, 16384⟩
    (by decide) selected_cut_34062

theorem selected_cut_34063 : selected 8 ⟨879790, by decide⟩
    (prefixPartial 13 451711) = some ⟨13, 2, 0, 879790, 451711, 793, 16384⟩ := by
  decide +kernel

theorem context_13_451711_879790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451711 ⟨879790, by decide⟩ :=
  accepted_of_selected 13 451711 ⟨879790, by decide⟩ ⟨13, 2, 0, 879790, 451711, 793, 16384⟩
    (by decide) selected_cut_34063

theorem unmarked_context_12_112927_879791 : frontier 9 ⟨879791, by decide⟩
    (prefixCache 12 112927) (prefixPartial 12 112927) = false := by
  decide +kernel

theorem node_context_12_112927_879791 : EJMOriginalGlobalDAGData.nodes 9 ⟨879791, by decide⟩ =
    .split (coordinate 12) (![⟨879737, by decide⟩,⟨879764, by decide⟩,⟨879782, by decide⟩,⟨879790, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_112927_879791 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112927 ⟨879791, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 112927
    ⟨879791, by decide⟩ (by decide) (![⟨879737, by decide⟩,⟨879764, by decide⟩,⟨879782, by decide⟩,⟨879790, by decide⟩]) unmarked_context_12_112927_879791 node_context_12_112927_879791
  intro a
  fin_cases a
  · exact context_13_451708_879737
  · exact context_13_451709_879764
  · exact context_13_451710_879782
  · exact context_13_451711_879790

theorem unmarked_context_11_28231_879792 : frontier 10 ⟨879792, by decide⟩
    (prefixCache 11 28231) (prefixPartial 11 28231) = false := by
  decide +kernel

theorem node_context_11_28231_879792 : EJMOriginalGlobalDAGData.nodes 10 ⟨879792, by decide⟩ =
    .split (coordinate 11) (![⟨879557, by decide⟩,⟨879635, by decide⟩,⟨879716, by decide⟩,⟨879791, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28231_879792 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28231 ⟨879792, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28231
    ⟨879792, by decide⟩ (by decide) (![⟨879557, by decide⟩,⟨879635, by decide⟩,⟨879716, by decide⟩,⟨879791, by decide⟩]) unmarked_context_11_28231_879792 node_context_11_28231_879792
  intro a
  fin_cases a
  · exact context_12_112924_879557
  · exact context_12_112925_879635
  · exact context_12_112926_879716
  · exact context_12_112927_879791

theorem unmarked_context_10_7057_879793 : frontier 11 ⟨879793, by decide⟩
    (prefixCache 10 7057) (prefixPartial 10 7057) = false := by
  decide +kernel

theorem node_context_10_7057_879793 : EJMOriginalGlobalDAGData.nodes 11 ⟨879793, by decide⟩ =
    .split (coordinate 10) (![⟨878975, by decide⟩,⟨879186, by decide⟩,⟨879486, by decide⟩,⟨879792, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_7057_879793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 7057 ⟨879793, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 7057
    ⟨879793, by decide⟩ (by decide) (![⟨878975, by decide⟩,⟨879186, by decide⟩,⟨879486, by decide⟩,⟨879792, by decide⟩]) unmarked_context_10_7057_879793 node_context_10_7057_879793
  intro a
  fin_cases a
  · exact context_11_28228_878975
  · exact context_11_28229_879186
  · exact context_11_28230_879486
  · exact context_11_28231_879792

theorem selected_cut_34064 : selected 8 ⟨879812, by decide⟩
    (prefixPartial 13 451712) = some ⟨13, 2, 0, 879812, 451712, 1121, 16384⟩ := by
  decide +kernel

theorem context_13_451712_879812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451712 ⟨879812, by decide⟩ :=
  accepted_of_selected 13 451712 ⟨879812, by decide⟩ ⟨13, 2, 0, 879812, 451712, 1121, 16384⟩
    (by decide) selected_cut_34064

theorem selected_cut_34065 : selected 8 ⟨879832, by decide⟩
    (prefixPartial 13 451713) = some ⟨13, 2, 0, 879832, 451713, 1757, 16384⟩ := by
  decide +kernel

theorem context_13_451713_879832 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451713 ⟨879832, by decide⟩ :=
  accepted_of_selected 13 451713 ⟨879832, by decide⟩ ⟨13, 2, 0, 879832, 451713, 1757, 16384⟩
    (by decide) selected_cut_34065

theorem selected_cut_34066 : selected 8 ⟨879846, by decide⟩
    (prefixPartial 13 451714) = some ⟨13, 2, 0, 879846, 451714, 721, 16384⟩ := by
  decide +kernel

theorem context_13_451714_879846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451714 ⟨879846, by decide⟩ :=
  accepted_of_selected 13 451714 ⟨879846, by decide⟩ ⟨13, 2, 0, 879846, 451714, 721, 16384⟩
    (by decide) selected_cut_34066

theorem selected_cut_34067 : selected 8 ⟨879851, by decide⟩
    (prefixPartial 13 451715) = some ⟨13, 2, 0, 879851, 451715, 733, 16384⟩ := by
  decide +kernel

theorem context_13_451715_879851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451715 ⟨879851, by decide⟩ :=
  accepted_of_selected 13 451715 ⟨879851, by decide⟩ ⟨13, 2, 0, 879851, 451715, 733, 16384⟩
    (by decide) selected_cut_34067

theorem unmarked_context_12_112928_879852 : frontier 9 ⟨879852, by decide⟩
    (prefixCache 12 112928) (prefixPartial 12 112928) = false := by
  decide +kernel

theorem node_context_12_112928_879852 : EJMOriginalGlobalDAGData.nodes 9 ⟨879852, by decide⟩ =
    .split (coordinate 12) (![⟨879812, by decide⟩,⟨879832, by decide⟩,⟨879846, by decide⟩,⟨879851, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_112928_879852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112928 ⟨879852, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 112928
    ⟨879852, by decide⟩ (by decide) (![⟨879812, by decide⟩,⟨879832, by decide⟩,⟨879846, by decide⟩,⟨879851, by decide⟩]) unmarked_context_12_112928_879852 node_context_12_112928_879852
  intro a
  fin_cases a
  · exact context_13_451712_879812
  · exact context_13_451713_879832
  · exact context_13_451714_879846
  · exact context_13_451715_879851

theorem selected_cut_34068 : selected 8 ⟨879870, by decide⟩
    (prefixPartial 13 451716) = some ⟨13, 2, 0, 879870, 451716, 1201, 16384⟩ := by
  decide +kernel

theorem context_13_451716_879870 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451716 ⟨879870, by decide⟩ :=
  accepted_of_selected 13 451716 ⟨879870, by decide⟩ ⟨13, 2, 0, 879870, 451716, 1201, 16384⟩
    (by decide) selected_cut_34068

theorem selected_cut_34069 : selected 8 ⟨879894, by decide⟩
    (prefixPartial 13 451717) = some ⟨13, 2, 0, 879894, 451717, 2173, 16384⟩ := by
  decide +kernel

theorem context_13_451717_879894 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451717 ⟨879894, by decide⟩ :=
  accepted_of_selected 13 451717 ⟨879894, by decide⟩ ⟨13, 2, 0, 879894, 451717, 2173, 16384⟩
    (by decide) selected_cut_34069

theorem selected_cut_34070 : selected 8 ⟨879908, by decide⟩
    (prefixPartial 13 451718) = some ⟨13, 2, 0, 879908, 451718, 841, 16384⟩ := by
  decide +kernel

theorem context_13_451718_879908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451718 ⟨879908, by decide⟩ :=
  accepted_of_selected 13 451718 ⟨879908, by decide⟩ ⟨13, 2, 0, 879908, 451718, 841, 16384⟩
    (by decide) selected_cut_34070

theorem selected_cut_34071 : selected 8 ⟨879918, by decide⟩
    (prefixPartial 13 451719) = some ⟨13, 2, 0, 879918, 451719, 861, 16384⟩ := by
  decide +kernel

theorem context_13_451719_879918 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451719 ⟨879918, by decide⟩ :=
  accepted_of_selected 13 451719 ⟨879918, by decide⟩ ⟨13, 2, 0, 879918, 451719, 861, 16384⟩
    (by decide) selected_cut_34071

theorem unmarked_context_12_112929_879919 : frontier 9 ⟨879919, by decide⟩
    (prefixCache 12 112929) (prefixPartial 12 112929) = false := by
  decide +kernel

theorem node_context_12_112929_879919 : EJMOriginalGlobalDAGData.nodes 9 ⟨879919, by decide⟩ =
    .split (coordinate 12) (![⟨879870, by decide⟩,⟨879894, by decide⟩,⟨879908, by decide⟩,⟨879918, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_112929_879919 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112929 ⟨879919, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 112929
    ⟨879919, by decide⟩ (by decide) (![⟨879870, by decide⟩,⟨879894, by decide⟩,⟨879908, by decide⟩,⟨879918, by decide⟩]) unmarked_context_12_112929_879919 node_context_12_112929_879919
  intro a
  fin_cases a
  · exact context_13_451716_879870
  · exact context_13_451717_879894
  · exact context_13_451718_879908
  · exact context_13_451719_879918

theorem selected_cut_34072 : selected 8 ⟨879933, by decide⟩
    (prefixPartial 13 451720) = some ⟨13, 2, 0, 879933, 451720, 1197, 16384⟩ := by
  decide +kernel

theorem context_13_451720_879933 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451720 ⟨879933, by decide⟩ :=
  accepted_of_selected 13 451720 ⟨879933, by decide⟩ ⟨13, 2, 0, 879933, 451720, 1197, 16384⟩
    (by decide) selected_cut_34072

theorem selected_cut_34073 : selected 8 ⟨879957, by decide⟩
    (prefixPartial 13 451721) = some ⟨13, 2, 0, 879957, 451721, 2009, 16384⟩ := by
  decide +kernel

theorem context_13_451721_879957 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451721 ⟨879957, by decide⟩ :=
  accepted_of_selected 13 451721 ⟨879957, by decide⟩ ⟨13, 2, 0, 879957, 451721, 2009, 16384⟩
    (by decide) selected_cut_34073

theorem selected_cut_34074 : selected 8 ⟨879974, by decide⟩
    (prefixPartial 13 451722) = some ⟨13, 2, 0, 879974, 451722, 861, 16384⟩ := by
  decide +kernel

theorem context_13_451722_879974 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451722 ⟨879974, by decide⟩ :=
  accepted_of_selected 13 451722 ⟨879974, by decide⟩ ⟨13, 2, 0, 879974, 451722, 861, 16384⟩
    (by decide) selected_cut_34074

theorem selected_cut_34075 : selected 8 ⟨879984, by decide⟩
    (prefixPartial 13 451723) = some ⟨13, 2, 0, 879984, 451723, 841, 16384⟩ := by
  decide +kernel

theorem context_13_451723_879984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451723 ⟨879984, by decide⟩ :=
  accepted_of_selected 13 451723 ⟨879984, by decide⟩ ⟨13, 2, 0, 879984, 451723, 841, 16384⟩
    (by decide) selected_cut_34075

theorem unmarked_context_12_112930_879985 : frontier 9 ⟨879985, by decide⟩
    (prefixCache 12 112930) (prefixPartial 12 112930) = false := by
  decide +kernel

theorem node_context_12_112930_879985 : EJMOriginalGlobalDAGData.nodes 9 ⟨879985, by decide⟩ =
    .split (coordinate 12) (![⟨879933, by decide⟩,⟨879957, by decide⟩,⟨879974, by decide⟩,⟨879984, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_112930_879985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112930 ⟨879985, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 112930
    ⟨879985, by decide⟩ (by decide) (![⟨879933, by decide⟩,⟨879957, by decide⟩,⟨879974, by decide⟩,⟨879984, by decide⟩]) unmarked_context_12_112930_879985 node_context_12_112930_879985
  intro a
  fin_cases a
  · exact context_13_451720_879933
  · exact context_13_451721_879957
  · exact context_13_451722_879974
  · exact context_13_451723_879984

theorem selected_cut_34076 : selected 8 ⟨880004, by decide⟩
    (prefixPartial 13 451724) = some ⟨13, 2, 0, 880004, 451724, 1145, 16384⟩ := by
  decide +kernel

theorem context_13_451724_880004 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451724 ⟨880004, by decide⟩ :=
  accepted_of_selected 13 451724 ⟨880004, by decide⟩ ⟨13, 2, 0, 880004, 451724, 1145, 16384⟩
    (by decide) selected_cut_34076

theorem selected_cut_34077 : selected 8 ⟨880028, by decide⟩
    (prefixPartial 13 451725) = some ⟨13, 2, 0, 880028, 451725, 2025, 16384⟩ := by
  decide +kernel

theorem context_13_451725_880028 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451725 ⟨880028, by decide⟩ :=
  accepted_of_selected 13 451725 ⟨880028, by decide⟩ ⟨13, 2, 0, 880028, 451725, 2025, 16384⟩
    (by decide) selected_cut_34077

theorem selected_cut_34078 : selected 8 ⟨880041, by decide⟩
    (prefixPartial 13 451726) = some ⟨13, 2, 0, 880041, 451726, 793, 16384⟩ := by
  decide +kernel

theorem context_13_451726_880041 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451726 ⟨880041, by decide⟩ :=
  accepted_of_selected 13 451726 ⟨880041, by decide⟩ ⟨13, 2, 0, 880041, 451726, 793, 16384⟩
    (by decide) selected_cut_34078

theorem selected_cut_34079 : selected 8 ⟨880046, by decide⟩
    (prefixPartial 13 451727) = some ⟨13, 2, 0, 880046, 451727, 813, 16384⟩ := by
  decide +kernel

theorem context_13_451727_880046 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451727 ⟨880046, by decide⟩ :=
  accepted_of_selected 13 451727 ⟨880046, by decide⟩ ⟨13, 2, 0, 880046, 451727, 813, 16384⟩
    (by decide) selected_cut_34079

theorem unmarked_context_12_112931_880047 : frontier 9 ⟨880047, by decide⟩
    (prefixCache 12 112931) (prefixPartial 12 112931) = false := by
  decide +kernel

theorem node_context_12_112931_880047 : EJMOriginalGlobalDAGData.nodes 9 ⟨880047, by decide⟩ =
    .split (coordinate 12) (![⟨880004, by decide⟩,⟨880028, by decide⟩,⟨880041, by decide⟩,⟨880046, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_112931_880047 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112931 ⟨880047, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 112931
    ⟨880047, by decide⟩ (by decide) (![⟨880004, by decide⟩,⟨880028, by decide⟩,⟨880041, by decide⟩,⟨880046, by decide⟩]) unmarked_context_12_112931_880047 node_context_12_112931_880047
  intro a
  fin_cases a
  · exact context_13_451724_880004
  · exact context_13_451725_880028
  · exact context_13_451726_880041
  · exact context_13_451727_880046

theorem unmarked_context_11_28232_880048 : frontier 10 ⟨880048, by decide⟩
    (prefixCache 11 28232) (prefixPartial 11 28232) = false := by
  decide +kernel

theorem node_context_11_28232_880048 : EJMOriginalGlobalDAGData.nodes 10 ⟨880048, by decide⟩ =
    .split (coordinate 11) (![⟨879852, by decide⟩,⟨879919, by decide⟩,⟨879985, by decide⟩,⟨880047, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28232_880048 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28232 ⟨880048, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28232
    ⟨880048, by decide⟩ (by decide) (![⟨879852, by decide⟩,⟨879919, by decide⟩,⟨879985, by decide⟩,⟨880047, by decide⟩]) unmarked_context_11_28232_880048 node_context_11_28232_880048
  intro a
  fin_cases a
  · exact context_12_112928_879852
  · exact context_12_112929_879919
  · exact context_12_112930_879985
  · exact context_12_112931_880047

theorem selected_cut_34080 : selected 9 ⟨880105, by decide⟩
    (prefixPartial 12 112932) = some ⟨12, 2, 0, 880105, 112932, 3881, 65536⟩ := by
  decide +kernel

theorem context_12_112932_880105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112932 ⟨880105, by decide⟩ :=
  accepted_of_selected 12 112932 ⟨880105, by decide⟩ ⟨12, 2, 0, 880105, 112932, 3881, 65536⟩
    (by decide) selected_cut_34080

theorem selected_cut_34081 : selected 9 ⟨688903, by decide⟩
    (prefixPartial 12 112933) = some ⟨12, 1, 0, 688903, 112933, 1, 65536⟩ := by
  decide +kernel

theorem context_12_112933_688903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 112933 ⟨688903, by decide⟩ :=
  accepted_of_selected 12 112933 ⟨688903, by decide⟩ ⟨12, 1, 0, 688903, 112933, 1, 65536⟩
    (by decide) selected_cut_34081

theorem selected_cut_34082 : selected 8 ⟨880120, by decide⟩
    (prefixPartial 13 451736) = some ⟨13, 2, 0, 880120, 451736, 997, 16384⟩ := by
  decide +kernel

theorem context_13_451736_880120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451736 ⟨880120, by decide⟩ :=
  accepted_of_selected 13 451736 ⟨880120, by decide⟩ ⟨13, 2, 0, 880120, 451736, 997, 16384⟩
    (by decide) selected_cut_34082

theorem selected_cut_34083 : selected 8 ⟨880142, by decide⟩
    (prefixPartial 13 451737) = some ⟨13, 2, 0, 880142, 451737, 1705, 16384⟩ := by
  decide +kernel

theorem context_13_451737_880142 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 451737 ⟨880142, by decide⟩ :=
  accepted_of_selected 13 451737 ⟨880142, by decide⟩ ⟨13, 2, 0, 880142, 451737, 1705, 16384⟩
    (by decide) selected_cut_34083

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
