/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover111
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_10755 : selected 9 ⟨290359, by decide⟩
    (prefixPartial 12 25227) = some ⟨12, 2, 0, 290359, 25227, 2073, 65536⟩ := by
  decide +kernel

theorem context_12_25227_290359 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25227 ⟨290359, by decide⟩ :=
  accepted_of_selected 12 25227 ⟨290359, by decide⟩ ⟨12, 2, 0, 290359, 25227, 2073, 65536⟩
    (by decide) selected_cut_10755

theorem unmarked_context_11_6306_290360 : frontier 10 ⟨290360, by decide⟩
    (prefixCache 11 6306) (prefixPartial 11 6306) = false := by
  decide +kernel

theorem node_context_11_6306_290360 : EJMOriginalGlobalDAGData.nodes 10 ⟨290360, by decide⟩ =
    .split (coordinate 11) (![⟨290278, by decide⟩,⟨290306, by decide⟩,⟨290332, by decide⟩,⟨290359, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6306_290360 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6306 ⟨290360, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6306
    ⟨290360, by decide⟩ (by decide) (![⟨290278, by decide⟩,⟨290306, by decide⟩,⟨290332, by decide⟩,⟨290359, by decide⟩]) unmarked_context_11_6306_290360 node_context_11_6306_290360
  intro a
  fin_cases a
  · exact context_12_25224_290278
  · exact context_12_25225_290306
  · exact context_12_25226_290332
  · exact context_12_25227_290359

theorem selected_cut_10756 : selected 9 ⟨290383, by decide⟩
    (prefixPartial 12 25228) = some ⟨12, 2, 0, 290383, 25228, 1889, 65536⟩ := by
  decide +kernel

theorem context_12_25228_290383 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25228 ⟨290383, by decide⟩ :=
  accepted_of_selected 12 25228 ⟨290383, by decide⟩ ⟨12, 2, 0, 290383, 25228, 1889, 65536⟩
    (by decide) selected_cut_10756

theorem selected_cut_10757 : selected 9 ⟨290409, by decide⟩
    (prefixPartial 12 25229) = some ⟨12, 2, 0, 290409, 25229, 1977, 65536⟩ := by
  decide +kernel

theorem context_12_25229_290409 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25229 ⟨290409, by decide⟩ :=
  accepted_of_selected 12 25229 ⟨290409, by decide⟩ ⟨12, 2, 0, 290409, 25229, 1977, 65536⟩
    (by decide) selected_cut_10757

theorem selected_cut_10758 : selected 9 ⟨290432, by decide⟩
    (prefixPartial 12 25230) = some ⟨12, 2, 0, 290432, 25230, 1893, 65536⟩ := by
  decide +kernel

theorem context_12_25230_290432 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25230 ⟨290432, by decide⟩ :=
  accepted_of_selected 12 25230 ⟨290432, by decide⟩ ⟨12, 2, 0, 290432, 25230, 1893, 65536⟩
    (by decide) selected_cut_10758

theorem selected_cut_10759 : selected 9 ⟨290455, by decide⟩
    (prefixPartial 12 25231) = some ⟨12, 2, 0, 290455, 25231, 2157, 65536⟩ := by
  decide +kernel

theorem context_12_25231_290455 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25231 ⟨290455, by decide⟩ :=
  accepted_of_selected 12 25231 ⟨290455, by decide⟩ ⟨12, 2, 0, 290455, 25231, 2157, 65536⟩
    (by decide) selected_cut_10759

theorem unmarked_context_11_6307_290456 : frontier 10 ⟨290456, by decide⟩
    (prefixCache 11 6307) (prefixPartial 11 6307) = false := by
  decide +kernel

theorem node_context_11_6307_290456 : EJMOriginalGlobalDAGData.nodes 10 ⟨290456, by decide⟩ =
    .split (coordinate 11) (![⟨290383, by decide⟩,⟨290409, by decide⟩,⟨290432, by decide⟩,⟨290455, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6307_290456 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6307 ⟨290456, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6307
    ⟨290456, by decide⟩ (by decide) (![⟨290383, by decide⟩,⟨290409, by decide⟩,⟨290432, by decide⟩,⟨290455, by decide⟩]) unmarked_context_11_6307_290456 node_context_11_6307_290456
  intro a
  fin_cases a
  · exact context_12_25228_290383
  · exact context_12_25229_290409
  · exact context_12_25230_290432
  · exact context_12_25231_290455

theorem unmarked_context_10_1576_290457 : frontier 11 ⟨290457, by decide⟩
    (prefixCache 10 1576) (prefixPartial 10 1576) = false := by
  decide +kernel

theorem node_context_10_1576_290457 : EJMOriginalGlobalDAGData.nodes 11 ⟨290457, by decide⟩ =
    .split (coordinate 10) (![⟨290150, by decide⟩,⟨290259, by decide⟩,⟨290360, by decide⟩,⟨290456, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1576_290457 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1576 ⟨290457, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1576
    ⟨290457, by decide⟩ (by decide) (![⟨290150, by decide⟩,⟨290259, by decide⟩,⟨290360, by decide⟩,⟨290456, by decide⟩]) unmarked_context_10_1576_290457 node_context_10_1576_290457
  intro a
  fin_cases a
  · exact context_11_6304_290150
  · exact context_11_6305_290259
  · exact context_11_6306_290360
  · exact context_11_6307_290456

theorem selected_cut_10760 : selected 9 ⟨290475, by decide⟩
    (prefixPartial 12 25232) = some ⟨12, 2, 0, 290475, 25232, 1641, 65536⟩ := by
  decide +kernel

theorem context_12_25232_290475 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25232 ⟨290475, by decide⟩ :=
  accepted_of_selected 12 25232 ⟨290475, by decide⟩ ⟨12, 2, 0, 290475, 25232, 1641, 65536⟩
    (by decide) selected_cut_10760

theorem selected_cut_10761 : selected 9 ⟨290499, by decide⟩
    (prefixPartial 12 25233) = some ⟨12, 2, 0, 290499, 25233, 2157, 65536⟩ := by
  decide +kernel

theorem context_12_25233_290499 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25233 ⟨290499, by decide⟩ :=
  accepted_of_selected 12 25233 ⟨290499, by decide⟩ ⟨12, 2, 0, 290499, 25233, 2157, 65536⟩
    (by decide) selected_cut_10761

theorem selected_cut_10762 : selected 9 ⟨290522, by decide⟩
    (prefixPartial 12 25234) = some ⟨12, 2, 0, 290522, 25234, 1965, 65536⟩ := by
  decide +kernel

theorem context_12_25234_290522 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25234 ⟨290522, by decide⟩ :=
  accepted_of_selected 12 25234 ⟨290522, by decide⟩ ⟨12, 2, 0, 290522, 25234, 1965, 65536⟩
    (by decide) selected_cut_10762

theorem selected_cut_10763 : selected 9 ⟨290545, by decide⟩
    (prefixPartial 12 25235) = some ⟨12, 2, 0, 290545, 25235, 2293, 65536⟩ := by
  decide +kernel

theorem context_12_25235_290545 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25235 ⟨290545, by decide⟩ :=
  accepted_of_selected 12 25235 ⟨290545, by decide⟩ ⟨12, 2, 0, 290545, 25235, 2293, 65536⟩
    (by decide) selected_cut_10763

theorem unmarked_context_11_6308_290546 : frontier 10 ⟨290546, by decide⟩
    (prefixCache 11 6308) (prefixPartial 11 6308) = false := by
  decide +kernel

theorem node_context_11_6308_290546 : EJMOriginalGlobalDAGData.nodes 10 ⟨290546, by decide⟩ =
    .split (coordinate 11) (![⟨290475, by decide⟩,⟨290499, by decide⟩,⟨290522, by decide⟩,⟨290545, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6308_290546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6308 ⟨290546, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6308
    ⟨290546, by decide⟩ (by decide) (![⟨290475, by decide⟩,⟨290499, by decide⟩,⟨290522, by decide⟩,⟨290545, by decide⟩]) unmarked_context_11_6308_290546 node_context_11_6308_290546
  intro a
  fin_cases a
  · exact context_12_25232_290475
  · exact context_12_25233_290499
  · exact context_12_25234_290522
  · exact context_12_25235_290545

theorem selected_cut_10764 : selected 9 ⟨290569, by decide⟩
    (prefixPartial 12 25236) = some ⟨12, 2, 0, 290569, 25236, 1885, 65536⟩ := by
  decide +kernel

theorem context_12_25236_290569 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25236 ⟨290569, by decide⟩ :=
  accepted_of_selected 12 25236 ⟨290569, by decide⟩ ⟨12, 2, 0, 290569, 25236, 1885, 65536⟩
    (by decide) selected_cut_10764

theorem selected_cut_10765 : selected 9 ⟨290594, by decide⟩
    (prefixPartial 12 25237) = some ⟨12, 2, 0, 290594, 25237, 2345, 65536⟩ := by
  decide +kernel

theorem context_12_25237_290594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25237 ⟨290594, by decide⟩ :=
  accepted_of_selected 12 25237 ⟨290594, by decide⟩ ⟨12, 2, 0, 290594, 25237, 2345, 65536⟩
    (by decide) selected_cut_10765

theorem selected_cut_10766 : selected 9 ⟨290614, by decide⟩
    (prefixPartial 12 25238) = some ⟨12, 2, 0, 290614, 25238, 2205, 65536⟩ := by
  decide +kernel

theorem context_12_25238_290614 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25238 ⟨290614, by decide⟩ :=
  accepted_of_selected 12 25238 ⟨290614, by decide⟩ ⟨12, 2, 0, 290614, 25238, 2205, 65536⟩
    (by decide) selected_cut_10766

theorem selected_cut_10767 : selected 9 ⟨290635, by decide⟩
    (prefixPartial 12 25239) = some ⟨12, 2, 0, 290635, 25239, 2457, 65536⟩ := by
  decide +kernel

theorem context_12_25239_290635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25239 ⟨290635, by decide⟩ :=
  accepted_of_selected 12 25239 ⟨290635, by decide⟩ ⟨12, 2, 0, 290635, 25239, 2457, 65536⟩
    (by decide) selected_cut_10767

theorem unmarked_context_11_6309_290636 : frontier 10 ⟨290636, by decide⟩
    (prefixCache 11 6309) (prefixPartial 11 6309) = false := by
  decide +kernel

theorem node_context_11_6309_290636 : EJMOriginalGlobalDAGData.nodes 10 ⟨290636, by decide⟩ =
    .split (coordinate 11) (![⟨290569, by decide⟩,⟨290594, by decide⟩,⟨290614, by decide⟩,⟨290635, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6309_290636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6309 ⟨290636, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6309
    ⟨290636, by decide⟩ (by decide) (![⟨290569, by decide⟩,⟨290594, by decide⟩,⟨290614, by decide⟩,⟨290635, by decide⟩]) unmarked_context_11_6309_290636 node_context_11_6309_290636
  intro a
  fin_cases a
  · exact context_12_25236_290569
  · exact context_12_25237_290594
  · exact context_12_25238_290614
  · exact context_12_25239_290635

theorem selected_cut_10768 : selected 9 ⟨290652, by decide⟩
    (prefixPartial 12 25240) = some ⟨12, 2, 0, 290652, 25240, 1593, 65536⟩ := by
  decide +kernel

theorem context_12_25240_290652 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25240 ⟨290652, by decide⟩ :=
  accepted_of_selected 12 25240 ⟨290652, by decide⟩ ⟨12, 2, 0, 290652, 25240, 1593, 65536⟩
    (by decide) selected_cut_10768

theorem selected_cut_10769 : selected 9 ⟨290672, by decide⟩
    (prefixPartial 12 25241) = some ⟨12, 2, 0, 290672, 25241, 2121, 65536⟩ := by
  decide +kernel

theorem context_12_25241_290672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25241 ⟨290672, by decide⟩ :=
  accepted_of_selected 12 25241 ⟨290672, by decide⟩ ⟨12, 2, 0, 290672, 25241, 2121, 65536⟩
    (by decide) selected_cut_10769

theorem selected_cut_10770 : selected 9 ⟨290673, by decide⟩
    (prefixPartial 12 25242) = some ⟨12, 1, 0, 290673, 25242, 1, 65536⟩ := by
  decide +kernel

theorem context_12_25242_290673 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25242 ⟨290673, by decide⟩ :=
  accepted_of_selected 12 25242 ⟨290673, by decide⟩ ⟨12, 1, 0, 290673, 25242, 1, 65536⟩
    (by decide) selected_cut_10770

theorem selected_cut_10771 : selected 9 ⟨290697, by decide⟩
    (prefixPartial 12 25243) = some ⟨12, 2, 0, 290697, 25243, 2109, 65536⟩ := by
  decide +kernel

theorem context_12_25243_290697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25243 ⟨290697, by decide⟩ :=
  accepted_of_selected 12 25243 ⟨290697, by decide⟩ ⟨12, 2, 0, 290697, 25243, 2109, 65536⟩
    (by decide) selected_cut_10771

theorem unmarked_context_11_6310_290698 : frontier 10 ⟨290698, by decide⟩
    (prefixCache 11 6310) (prefixPartial 11 6310) = false := by
  decide +kernel

theorem node_context_11_6310_290698 : EJMOriginalGlobalDAGData.nodes 10 ⟨290698, by decide⟩ =
    .split (coordinate 11) (![⟨290652, by decide⟩,⟨290672, by decide⟩,⟨290673, by decide⟩,⟨290697, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6310_290698 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6310 ⟨290698, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6310
    ⟨290698, by decide⟩ (by decide) (![⟨290652, by decide⟩,⟨290672, by decide⟩,⟨290673, by decide⟩,⟨290697, by decide⟩]) unmarked_context_11_6310_290698 node_context_11_6310_290698
  intro a
  fin_cases a
  · exact context_12_25240_290652
  · exact context_12_25241_290672
  · exact context_12_25242_290673
  · exact context_12_25243_290697

theorem selected_cut_10772 : selected 9 ⟨290717, by decide⟩
    (prefixPartial 12 25244) = some ⟨12, 2, 0, 290717, 25244, 1729, 65536⟩ := by
  decide +kernel

theorem context_12_25244_290717 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25244 ⟨290717, by decide⟩ :=
  accepted_of_selected 12 25244 ⟨290717, by decide⟩ ⟨12, 2, 0, 290717, 25244, 1729, 65536⟩
    (by decide) selected_cut_10772

theorem selected_cut_10773 : selected 9 ⟨290740, by decide⟩
    (prefixPartial 12 25245) = some ⟨12, 2, 0, 290740, 25245, 2017, 65536⟩ := by
  decide +kernel

theorem context_12_25245_290740 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25245 ⟨290740, by decide⟩ :=
  accepted_of_selected 12 25245 ⟨290740, by decide⟩ ⟨12, 2, 0, 290740, 25245, 2017, 65536⟩
    (by decide) selected_cut_10773

theorem selected_cut_10774 : selected 9 ⟨290761, by decide⟩
    (prefixPartial 12 25246) = some ⟨12, 2, 0, 290761, 25246, 1781, 65536⟩ := by
  decide +kernel

theorem context_12_25246_290761 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25246 ⟨290761, by decide⟩ :=
  accepted_of_selected 12 25246 ⟨290761, by decide⟩ ⟨12, 2, 0, 290761, 25246, 1781, 65536⟩
    (by decide) selected_cut_10774

theorem selected_cut_10775 : selected 9 ⟨290782, by decide⟩
    (prefixPartial 12 25247) = some ⟨12, 2, 0, 290782, 25247, 2081, 65536⟩ := by
  decide +kernel

theorem context_12_25247_290782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25247 ⟨290782, by decide⟩ :=
  accepted_of_selected 12 25247 ⟨290782, by decide⟩ ⟨12, 2, 0, 290782, 25247, 2081, 65536⟩
    (by decide) selected_cut_10775

theorem unmarked_context_11_6311_290783 : frontier 10 ⟨290783, by decide⟩
    (prefixCache 11 6311) (prefixPartial 11 6311) = false := by
  decide +kernel

theorem node_context_11_6311_290783 : EJMOriginalGlobalDAGData.nodes 10 ⟨290783, by decide⟩ =
    .split (coordinate 11) (![⟨290717, by decide⟩,⟨290740, by decide⟩,⟨290761, by decide⟩,⟨290782, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6311_290783 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6311 ⟨290783, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6311
    ⟨290783, by decide⟩ (by decide) (![⟨290717, by decide⟩,⟨290740, by decide⟩,⟨290761, by decide⟩,⟨290782, by decide⟩]) unmarked_context_11_6311_290783 node_context_11_6311_290783
  intro a
  fin_cases a
  · exact context_12_25244_290717
  · exact context_12_25245_290740
  · exact context_12_25246_290761
  · exact context_12_25247_290782

theorem unmarked_context_10_1577_290784 : frontier 11 ⟨290784, by decide⟩
    (prefixCache 10 1577) (prefixPartial 10 1577) = false := by
  decide +kernel

theorem node_context_10_1577_290784 : EJMOriginalGlobalDAGData.nodes 11 ⟨290784, by decide⟩ =
    .split (coordinate 10) (![⟨290546, by decide⟩,⟨290636, by decide⟩,⟨290698, by decide⟩,⟨290783, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1577_290784 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1577 ⟨290784, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1577
    ⟨290784, by decide⟩ (by decide) (![⟨290546, by decide⟩,⟨290636, by decide⟩,⟨290698, by decide⟩,⟨290783, by decide⟩]) unmarked_context_10_1577_290784 node_context_10_1577_290784
  intro a
  fin_cases a
  · exact context_11_6308_290546
  · exact context_11_6309_290636
  · exact context_11_6310_290698
  · exact context_11_6311_290783

theorem selected_cut_10776 : selected 9 ⟨290797, by decide⟩
    (prefixPartial 12 25248) = some ⟨12, 2, 0, 290797, 25248, 1221, 65536⟩ := by
  decide +kernel

theorem context_12_25248_290797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25248 ⟨290797, by decide⟩ :=
  accepted_of_selected 12 25248 ⟨290797, by decide⟩ ⟨12, 2, 0, 290797, 25248, 1221, 65536⟩
    (by decide) selected_cut_10776

theorem selected_cut_10777 : selected 9 ⟨290815, by decide⟩
    (prefixPartial 12 25249) = some ⟨12, 2, 0, 290815, 25249, 1609, 65536⟩ := by
  decide +kernel

theorem context_12_25249_290815 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25249 ⟨290815, by decide⟩ :=
  accepted_of_selected 12 25249 ⟨290815, by decide⟩ ⟨12, 2, 0, 290815, 25249, 1609, 65536⟩
    (by decide) selected_cut_10777

theorem selected_cut_10778 : selected 9 ⟨290832, by decide⟩
    (prefixPartial 12 25250) = some ⟨12, 2, 0, 290832, 25250, 1265, 65536⟩ := by
  decide +kernel

theorem context_12_25250_290832 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25250 ⟨290832, by decide⟩ :=
  accepted_of_selected 12 25250 ⟨290832, by decide⟩ ⟨12, 2, 0, 290832, 25250, 1265, 65536⟩
    (by decide) selected_cut_10778

theorem selected_cut_10779 : selected 9 ⟨290851, by decide⟩
    (prefixPartial 12 25251) = some ⟨12, 2, 0, 290851, 25251, 1517, 65536⟩ := by
  decide +kernel

theorem context_12_25251_290851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25251 ⟨290851, by decide⟩ :=
  accepted_of_selected 12 25251 ⟨290851, by decide⟩ ⟨12, 2, 0, 290851, 25251, 1517, 65536⟩
    (by decide) selected_cut_10779

theorem unmarked_context_11_6312_290852 : frontier 10 ⟨290852, by decide⟩
    (prefixCache 11 6312) (prefixPartial 11 6312) = false := by
  decide +kernel

theorem node_context_11_6312_290852 : EJMOriginalGlobalDAGData.nodes 10 ⟨290852, by decide⟩ =
    .split (coordinate 11) (![⟨290797, by decide⟩,⟨290815, by decide⟩,⟨290832, by decide⟩,⟨290851, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6312_290852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6312 ⟨290852, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6312
    ⟨290852, by decide⟩ (by decide) (![⟨290797, by decide⟩,⟨290815, by decide⟩,⟨290832, by decide⟩,⟨290851, by decide⟩]) unmarked_context_11_6312_290852 node_context_11_6312_290852
  intro a
  fin_cases a
  · exact context_12_25248_290797
  · exact context_12_25249_290815
  · exact context_12_25250_290832
  · exact context_12_25251_290851

theorem selected_cut_10780 : selected 9 ⟨290866, by decide⟩
    (prefixPartial 12 25252) = some ⟨12, 2, 0, 290866, 25252, 1333, 65536⟩ := by
  decide +kernel

theorem context_12_25252_290866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25252 ⟨290866, by decide⟩ :=
  accepted_of_selected 12 25252 ⟨290866, by decide⟩ ⟨12, 2, 0, 290866, 25252, 1333, 65536⟩
    (by decide) selected_cut_10780

theorem selected_cut_10781 : selected 9 ⟨290887, by decide⟩
    (prefixPartial 12 25253) = some ⟨12, 2, 0, 290887, 25253, 1701, 65536⟩ := by
  decide +kernel

theorem context_12_25253_290887 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25253 ⟨290887, by decide⟩ :=
  accepted_of_selected 12 25253 ⟨290887, by decide⟩ ⟨12, 2, 0, 290887, 25253, 1701, 65536⟩
    (by decide) selected_cut_10781

theorem selected_cut_10782 : selected 9 ⟨290903, by decide⟩
    (prefixPartial 12 25254) = some ⟨12, 2, 0, 290903, 25254, 1473, 65536⟩ := by
  decide +kernel

theorem context_12_25254_290903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25254 ⟨290903, by decide⟩ :=
  accepted_of_selected 12 25254 ⟨290903, by decide⟩ ⟨12, 2, 0, 290903, 25254, 1473, 65536⟩
    (by decide) selected_cut_10782

theorem selected_cut_10783 : selected 9 ⟨290921, by decide⟩
    (prefixPartial 12 25255) = some ⟨12, 2, 0, 290921, 25255, 1669, 65536⟩ := by
  decide +kernel

theorem context_12_25255_290921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25255 ⟨290921, by decide⟩ :=
  accepted_of_selected 12 25255 ⟨290921, by decide⟩ ⟨12, 2, 0, 290921, 25255, 1669, 65536⟩
    (by decide) selected_cut_10783

theorem unmarked_context_11_6313_290922 : frontier 10 ⟨290922, by decide⟩
    (prefixCache 11 6313) (prefixPartial 11 6313) = false := by
  decide +kernel

theorem node_context_11_6313_290922 : EJMOriginalGlobalDAGData.nodes 10 ⟨290922, by decide⟩ =
    .split (coordinate 11) (![⟨290866, by decide⟩,⟨290887, by decide⟩,⟨290903, by decide⟩,⟨290921, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6313_290922 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6313 ⟨290922, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6313
    ⟨290922, by decide⟩ (by decide) (![⟨290866, by decide⟩,⟨290887, by decide⟩,⟨290903, by decide⟩,⟨290921, by decide⟩]) unmarked_context_11_6313_290922 node_context_11_6313_290922
  intro a
  fin_cases a
  · exact context_12_25252_290866
  · exact context_12_25253_290887
  · exact context_12_25254_290903
  · exact context_12_25255_290921

theorem selected_cut_10784 : selected 10 ⟨290967, by decide⟩
    (prefixPartial 11 6314) = some ⟨11, 2, 0, 290967, 6314, 3957, 262144⟩ := by
  decide +kernel

theorem context_11_6314_290967 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6314 ⟨290967, by decide⟩ :=
  accepted_of_selected 11 6314 ⟨290967, by decide⟩ ⟨11, 2, 0, 290967, 6314, 3957, 262144⟩
    (by decide) selected_cut_10784

theorem selected_cut_10785 : selected 9 ⟨290984, by decide⟩
    (prefixPartial 12 25260) = some ⟨12, 2, 0, 290984, 25260, 1441, 65536⟩ := by
  decide +kernel

theorem context_12_25260_290984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25260 ⟨290984, by decide⟩ :=
  accepted_of_selected 12 25260 ⟨290984, by decide⟩ ⟨12, 2, 0, 290984, 25260, 1441, 65536⟩
    (by decide) selected_cut_10785

theorem selected_cut_10786 : selected 9 ⟨291000, by decide⟩
    (prefixPartial 12 25261) = some ⟨12, 2, 0, 291000, 25261, 1661, 65536⟩ := by
  decide +kernel

theorem context_12_25261_291000 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25261 ⟨291000, by decide⟩ :=
  accepted_of_selected 12 25261 ⟨291000, by decide⟩ ⟨12, 2, 0, 291000, 25261, 1661, 65536⟩
    (by decide) selected_cut_10786

theorem selected_cut_10787 : selected 9 ⟨291016, by decide⟩
    (prefixPartial 12 25262) = some ⟨12, 2, 0, 291016, 25262, 1329, 65536⟩ := by
  decide +kernel

theorem context_12_25262_291016 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25262 ⟨291016, by decide⟩ :=
  accepted_of_selected 12 25262 ⟨291016, by decide⟩ ⟨12, 2, 0, 291016, 25262, 1329, 65536⟩
    (by decide) selected_cut_10787

theorem selected_cut_10788 : selected 9 ⟨291033, by decide⟩
    (prefixPartial 12 25263) = some ⟨12, 2, 0, 291033, 25263, 1573, 65536⟩ := by
  decide +kernel

theorem context_12_25263_291033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25263 ⟨291033, by decide⟩ :=
  accepted_of_selected 12 25263 ⟨291033, by decide⟩ ⟨12, 2, 0, 291033, 25263, 1573, 65536⟩
    (by decide) selected_cut_10788

theorem unmarked_context_11_6315_291034 : frontier 10 ⟨291034, by decide⟩
    (prefixCache 11 6315) (prefixPartial 11 6315) = false := by
  decide +kernel

theorem node_context_11_6315_291034 : EJMOriginalGlobalDAGData.nodes 10 ⟨291034, by decide⟩ =
    .split (coordinate 11) (![⟨290984, by decide⟩,⟨291000, by decide⟩,⟨291016, by decide⟩,⟨291033, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6315_291034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6315 ⟨291034, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6315
    ⟨291034, by decide⟩ (by decide) (![⟨290984, by decide⟩,⟨291000, by decide⟩,⟨291016, by decide⟩,⟨291033, by decide⟩]) unmarked_context_11_6315_291034 node_context_11_6315_291034
  intro a
  fin_cases a
  · exact context_12_25260_290984
  · exact context_12_25261_291000
  · exact context_12_25262_291016
  · exact context_12_25263_291033

theorem unmarked_context_10_1578_291035 : frontier 11 ⟨291035, by decide⟩
    (prefixCache 10 1578) (prefixPartial 10 1578) = false := by
  decide +kernel

theorem node_context_10_1578_291035 : EJMOriginalGlobalDAGData.nodes 11 ⟨291035, by decide⟩ =
    .split (coordinate 10) (![⟨290852, by decide⟩,⟨290922, by decide⟩,⟨290967, by decide⟩,⟨291034, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1578_291035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1578 ⟨291035, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1578
    ⟨291035, by decide⟩ (by decide) (![⟨290852, by decide⟩,⟨290922, by decide⟩,⟨290967, by decide⟩,⟨291034, by decide⟩]) unmarked_context_10_1578_291035 node_context_10_1578_291035
  intro a
  fin_cases a
  · exact context_11_6312_290852
  · exact context_11_6313_290922
  · exact context_11_6314_290967
  · exact context_11_6315_291034

theorem selected_cut_10789 : selected 9 ⟨291043, by decide⟩
    (prefixPartial 12 25264) = some ⟨12, 2, 0, 291043, 25264, 961, 65536⟩ := by
  decide +kernel

theorem context_12_25264_291043 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25264 ⟨291043, by decide⟩ :=
  accepted_of_selected 12 25264 ⟨291043, by decide⟩ ⟨12, 2, 0, 291043, 25264, 961, 65536⟩
    (by decide) selected_cut_10789

theorem selected_cut_10790 : selected 9 ⟨291053, by decide⟩
    (prefixPartial 12 25265) = some ⟨12, 2, 0, 291053, 25265, 1101, 65536⟩ := by
  decide +kernel

theorem context_12_25265_291053 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25265 ⟨291053, by decide⟩ :=
  accepted_of_selected 12 25265 ⟨291053, by decide⟩ ⟨12, 2, 0, 291053, 25265, 1101, 65536⟩
    (by decide) selected_cut_10790

theorem selected_cut_10791 : selected 9 ⟨291063, by decide⟩
    (prefixPartial 12 25266) = some ⟨12, 2, 0, 291063, 25266, 945, 65536⟩ := by
  decide +kernel

theorem context_12_25266_291063 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25266 ⟨291063, by decide⟩ :=
  accepted_of_selected 12 25266 ⟨291063, by decide⟩ ⟨12, 2, 0, 291063, 25266, 945, 65536⟩
    (by decide) selected_cut_10791

theorem selected_cut_10792 : selected 9 ⟨291076, by decide⟩
    (prefixPartial 12 25267) = some ⟨12, 2, 0, 291076, 25267, 1269, 65536⟩ := by
  decide +kernel

theorem context_12_25267_291076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25267 ⟨291076, by decide⟩ :=
  accepted_of_selected 12 25267 ⟨291076, by decide⟩ ⟨12, 2, 0, 291076, 25267, 1269, 65536⟩
    (by decide) selected_cut_10792

theorem unmarked_context_11_6316_291077 : frontier 10 ⟨291077, by decide⟩
    (prefixCache 11 6316) (prefixPartial 11 6316) = false := by
  decide +kernel

theorem node_context_11_6316_291077 : EJMOriginalGlobalDAGData.nodes 10 ⟨291077, by decide⟩ =
    .split (coordinate 11) (![⟨291043, by decide⟩,⟨291053, by decide⟩,⟨291063, by decide⟩,⟨291076, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6316_291077 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6316 ⟨291077, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6316
    ⟨291077, by decide⟩ (by decide) (![⟨291043, by decide⟩,⟨291053, by decide⟩,⟨291063, by decide⟩,⟨291076, by decide⟩]) unmarked_context_11_6316_291077 node_context_11_6316_291077
  intro a
  fin_cases a
  · exact context_12_25264_291043
  · exact context_12_25265_291053
  · exact context_12_25266_291063
  · exact context_12_25267_291076

theorem selected_cut_10793 : selected 9 ⟨291089, by decide⟩
    (prefixPartial 12 25268) = some ⟨12, 2, 0, 291089, 25268, 1117, 65536⟩ := by
  decide +kernel

theorem context_12_25268_291089 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25268 ⟨291089, by decide⟩ :=
  accepted_of_selected 12 25268 ⟨291089, by decide⟩ ⟨12, 2, 0, 291089, 25268, 1117, 65536⟩
    (by decide) selected_cut_10793

theorem selected_cut_10794 : selected 9 ⟨291107, by decide⟩
    (prefixPartial 12 25269) = some ⟨12, 2, 0, 291107, 25269, 1257, 65536⟩ := by
  decide +kernel

theorem context_12_25269_291107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25269 ⟨291107, by decide⟩ :=
  accepted_of_selected 12 25269 ⟨291107, by decide⟩ ⟨12, 2, 0, 291107, 25269, 1257, 65536⟩
    (by decide) selected_cut_10794

theorem selected_cut_10795 : selected 9 ⟨291122, by decide⟩
    (prefixPartial 12 25270) = some ⟨12, 2, 0, 291122, 25270, 1197, 65536⟩ := by
  decide +kernel

theorem context_12_25270_291122 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25270 ⟨291122, by decide⟩ :=
  accepted_of_selected 12 25270 ⟨291122, by decide⟩ ⟨12, 2, 0, 291122, 25270, 1197, 65536⟩
    (by decide) selected_cut_10795

theorem selected_cut_10796 : selected 9 ⟨291136, by decide⟩
    (prefixPartial 12 25271) = some ⟨12, 2, 0, 291136, 25271, 1413, 65536⟩ := by
  decide +kernel

theorem context_12_25271_291136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25271 ⟨291136, by decide⟩ :=
  accepted_of_selected 12 25271 ⟨291136, by decide⟩ ⟨12, 2, 0, 291136, 25271, 1413, 65536⟩
    (by decide) selected_cut_10796

theorem unmarked_context_11_6317_291137 : frontier 10 ⟨291137, by decide⟩
    (prefixCache 11 6317) (prefixPartial 11 6317) = false := by
  decide +kernel

theorem node_context_11_6317_291137 : EJMOriginalGlobalDAGData.nodes 10 ⟨291137, by decide⟩ =
    .split (coordinate 11) (![⟨291089, by decide⟩,⟨291107, by decide⟩,⟨291122, by decide⟩,⟨291136, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6317_291137 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6317 ⟨291137, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6317
    ⟨291137, by decide⟩ (by decide) (![⟨291089, by decide⟩,⟨291107, by decide⟩,⟨291122, by decide⟩,⟨291136, by decide⟩]) unmarked_context_11_6317_291137 node_context_11_6317_291137
  intro a
  fin_cases a
  · exact context_12_25268_291089
  · exact context_12_25269_291107
  · exact context_12_25270_291122
  · exact context_12_25271_291136

theorem selected_cut_10797 : selected 9 ⟨291146, by decide⟩
    (prefixPartial 12 25272) = some ⟨12, 2, 0, 291146, 25272, 913, 65536⟩ := by
  decide +kernel

theorem context_12_25272_291146 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25272 ⟨291146, by decide⟩ :=
  accepted_of_selected 12 25272 ⟨291146, by decide⟩ ⟨12, 2, 0, 291146, 25272, 913, 65536⟩
    (by decide) selected_cut_10797

theorem selected_cut_10798 : selected 9 ⟨291162, by decide⟩
    (prefixPartial 12 25273) = some ⟨12, 2, 0, 291162, 25273, 1033, 65536⟩ := by
  decide +kernel

theorem context_12_25273_291162 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25273 ⟨291162, by decide⟩ :=
  accepted_of_selected 12 25273 ⟨291162, by decide⟩ ⟨12, 2, 0, 291162, 25273, 1033, 65536⟩
    (by decide) selected_cut_10798

theorem selected_cut_10799 : selected 9 ⟨291176, by decide⟩
    (prefixPartial 12 25274) = some ⟨12, 2, 0, 291176, 25274, 1397, 65536⟩ := by
  decide +kernel

theorem context_12_25274_291176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25274 ⟨291176, by decide⟩ :=
  accepted_of_selected 12 25274 ⟨291176, by decide⟩ ⟨12, 2, 0, 291176, 25274, 1397, 65536⟩
    (by decide) selected_cut_10799

theorem selected_cut_10800 : selected 9 ⟨291189, by decide⟩
    (prefixPartial 12 25275) = some ⟨12, 2, 0, 291189, 25275, 1029, 65536⟩ := by
  decide +kernel

theorem context_12_25275_291189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25275 ⟨291189, by decide⟩ :=
  accepted_of_selected 12 25275 ⟨291189, by decide⟩ ⟨12, 2, 0, 291189, 25275, 1029, 65536⟩
    (by decide) selected_cut_10800

theorem unmarked_context_11_6318_291190 : frontier 10 ⟨291190, by decide⟩
    (prefixCache 11 6318) (prefixPartial 11 6318) = false := by
  decide +kernel

theorem node_context_11_6318_291190 : EJMOriginalGlobalDAGData.nodes 10 ⟨291190, by decide⟩ =
    .split (coordinate 11) (![⟨291146, by decide⟩,⟨291162, by decide⟩,⟨291176, by decide⟩,⟨291189, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6318_291190 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6318 ⟨291190, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6318
    ⟨291190, by decide⟩ (by decide) (![⟨291146, by decide⟩,⟨291162, by decide⟩,⟨291176, by decide⟩,⟨291189, by decide⟩]) unmarked_context_11_6318_291190 node_context_11_6318_291190
  intro a
  fin_cases a
  · exact context_12_25272_291146
  · exact context_12_25273_291162
  · exact context_12_25274_291176
  · exact context_12_25275_291189

theorem selected_cut_10801 : selected 10 ⟨291233, by decide⟩
    (prefixPartial 11 6319) = some ⟨11, 2, 0, 291233, 6319, 3845, 262144⟩ := by
  decide +kernel

theorem context_11_6319_291233 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6319 ⟨291233, by decide⟩ :=
  accepted_of_selected 11 6319 ⟨291233, by decide⟩ ⟨11, 2, 0, 291233, 6319, 3845, 262144⟩
    (by decide) selected_cut_10801

theorem unmarked_context_10_1579_291234 : frontier 11 ⟨291234, by decide⟩
    (prefixCache 10 1579) (prefixPartial 10 1579) = false := by
  decide +kernel

theorem node_context_10_1579_291234 : EJMOriginalGlobalDAGData.nodes 11 ⟨291234, by decide⟩ =
    .split (coordinate 10) (![⟨291077, by decide⟩,⟨291137, by decide⟩,⟨291190, by decide⟩,⟨291233, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1579_291234 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1579 ⟨291234, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1579
    ⟨291234, by decide⟩ (by decide) (![⟨291077, by decide⟩,⟨291137, by decide⟩,⟨291190, by decide⟩,⟨291233, by decide⟩]) unmarked_context_10_1579_291234 node_context_10_1579_291234
  intro a
  fin_cases a
  · exact context_11_6316_291077
  · exact context_11_6317_291137
  · exact context_11_6318_291190
  · exact context_11_6319_291233

theorem unmarked_context_9_394_291235 : frontier 12 ⟨291235, by decide⟩
    (prefixCache 9 394) (prefixPartial 9 394) = false := by
  decide +kernel

theorem node_context_9_394_291235 : EJMOriginalGlobalDAGData.nodes 12 ⟨291235, by decide⟩ =
    .split (coordinate 9) (![⟨290457, by decide⟩,⟨290784, by decide⟩,⟨291035, by decide⟩,⟨291234, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_394_291235 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 394 ⟨291235, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 394
    ⟨291235, by decide⟩ (by decide) (![⟨290457, by decide⟩,⟨290784, by decide⟩,⟨291035, by decide⟩,⟨291234, by decide⟩]) unmarked_context_9_394_291235 node_context_9_394_291235
  intro a
  fin_cases a
  · exact context_10_1576_290457
  · exact context_10_1577_290784
  · exact context_10_1578_291035
  · exact context_10_1579_291234

theorem selected_cut_10802 : selected 9 ⟨291245, by decide⟩
    (prefixPartial 12 25280) = some ⟨12, 2, 0, 291245, 25280, 941, 65536⟩ := by
  decide +kernel

theorem context_12_25280_291245 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25280 ⟨291245, by decide⟩ :=
  accepted_of_selected 12 25280 ⟨291245, by decide⟩ ⟨12, 2, 0, 291245, 25280, 941, 65536⟩
    (by decide) selected_cut_10802

theorem selected_cut_10803 : selected 9 ⟨291253, by decide⟩
    (prefixPartial 12 25281) = some ⟨12, 2, 0, 291253, 25281, 1109, 65536⟩ := by
  decide +kernel

theorem context_12_25281_291253 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25281 ⟨291253, by decide⟩ :=
  accepted_of_selected 12 25281 ⟨291253, by decide⟩ ⟨12, 2, 0, 291253, 25281, 1109, 65536⟩
    (by decide) selected_cut_10803

theorem selected_cut_10804 : selected 9 ⟨291260, by decide⟩
    (prefixPartial 12 25282) = some ⟨12, 2, 0, 291260, 25282, 1089, 65536⟩ := by
  decide +kernel

theorem context_12_25282_291260 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25282 ⟨291260, by decide⟩ :=
  accepted_of_selected 12 25282 ⟨291260, by decide⟩ ⟨12, 2, 0, 291260, 25282, 1089, 65536⟩
    (by decide) selected_cut_10804

theorem selected_cut_10805 : selected 9 ⟨291268, by decide⟩
    (prefixPartial 12 25283) = some ⟨12, 2, 0, 291268, 25283, 1057, 65536⟩ := by
  decide +kernel

theorem context_12_25283_291268 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25283 ⟨291268, by decide⟩ :=
  accepted_of_selected 12 25283 ⟨291268, by decide⟩ ⟨12, 2, 0, 291268, 25283, 1057, 65536⟩
    (by decide) selected_cut_10805

theorem unmarked_context_11_6320_291269 : frontier 10 ⟨291269, by decide⟩
    (prefixCache 11 6320) (prefixPartial 11 6320) = false := by
  decide +kernel

theorem node_context_11_6320_291269 : EJMOriginalGlobalDAGData.nodes 10 ⟨291269, by decide⟩ =
    .split (coordinate 11) (![⟨291245, by decide⟩,⟨291253, by decide⟩,⟨291260, by decide⟩,⟨291268, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6320_291269 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6320 ⟨291269, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6320
    ⟨291269, by decide⟩ (by decide) (![⟨291245, by decide⟩,⟨291253, by decide⟩,⟨291260, by decide⟩,⟨291268, by decide⟩]) unmarked_context_11_6320_291269 node_context_11_6320_291269
  intro a
  fin_cases a
  · exact context_12_25280_291245
  · exact context_12_25281_291253
  · exact context_12_25282_291260
  · exact context_12_25283_291268

theorem selected_cut_10806 : selected 10 ⟨291294, by decide⟩
    (prefixPartial 11 6321) = some ⟨11, 2, 0, 291294, 6321, 2713, 262144⟩ := by
  decide +kernel

theorem context_11_6321_291294 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6321 ⟨291294, by decide⟩ :=
  accepted_of_selected 11 6321 ⟨291294, by decide⟩ ⟨11, 2, 0, 291294, 6321, 2713, 262144⟩
    (by decide) selected_cut_10806

theorem selected_cut_10807 : selected 10 ⟨291315, by decide⟩
    (prefixPartial 11 6322) = some ⟨11, 2, 0, 291315, 6322, 2661, 262144⟩ := by
  decide +kernel

theorem context_11_6322_291315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6322 ⟨291315, by decide⟩ :=
  accepted_of_selected 11 6322 ⟨291315, by decide⟩ ⟨11, 2, 0, 291315, 6322, 2661, 262144⟩
    (by decide) selected_cut_10807

theorem selected_cut_10808 : selected 10 ⟨291344, by decide⟩
    (prefixPartial 11 6323) = some ⟨11, 2, 0, 291344, 6323, 2625, 262144⟩ := by
  decide +kernel

theorem context_11_6323_291344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6323 ⟨291344, by decide⟩ :=
  accepted_of_selected 11 6323 ⟨291344, by decide⟩ ⟨11, 2, 0, 291344, 6323, 2625, 262144⟩
    (by decide) selected_cut_10808

theorem unmarked_context_10_1580_291345 : frontier 11 ⟨291345, by decide⟩
    (prefixCache 10 1580) (prefixPartial 10 1580) = false := by
  decide +kernel

theorem node_context_10_1580_291345 : EJMOriginalGlobalDAGData.nodes 11 ⟨291345, by decide⟩ =
    .split (coordinate 10) (![⟨291269, by decide⟩,⟨291294, by decide⟩,⟨291315, by decide⟩,⟨291344, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1580_291345 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1580 ⟨291345, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1580
    ⟨291345, by decide⟩ (by decide) (![⟨291269, by decide⟩,⟨291294, by decide⟩,⟨291315, by decide⟩,⟨291344, by decide⟩]) unmarked_context_10_1580_291345 node_context_10_1580_291345
  intro a
  fin_cases a
  · exact context_11_6320_291269
  · exact context_11_6321_291294
  · exact context_11_6322_291315
  · exact context_11_6323_291344

theorem selected_cut_10809 : selected 10 ⟨291368, by decide⟩
    (prefixPartial 11 6324) = some ⟨11, 2, 0, 291368, 6324, 2297, 262144⟩ := by
  decide +kernel

theorem context_11_6324_291368 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6324 ⟨291368, by decide⟩ :=
  accepted_of_selected 11 6324 ⟨291368, by decide⟩ ⟨11, 2, 0, 291368, 6324, 2297, 262144⟩
    (by decide) selected_cut_10809

theorem selected_cut_10810 : selected 10 ⟨291390, by decide⟩
    (prefixPartial 11 6325) = some ⟨11, 2, 0, 291390, 6325, 2265, 262144⟩ := by
  decide +kernel

theorem context_11_6325_291390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6325 ⟨291390, by decide⟩ :=
  accepted_of_selected 11 6325 ⟨291390, by decide⟩ ⟨11, 2, 0, 291390, 6325, 2265, 262144⟩
    (by decide) selected_cut_10810

theorem selected_cut_10811 : selected 10 ⟨291410, by decide⟩
    (prefixPartial 11 6326) = some ⟨11, 2, 0, 291410, 6326, 1901, 262144⟩ := by
  decide +kernel

theorem context_11_6326_291410 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6326 ⟨291410, by decide⟩ :=
  accepted_of_selected 11 6326 ⟨291410, by decide⟩ ⟨11, 2, 0, 291410, 6326, 1901, 262144⟩
    (by decide) selected_cut_10811

theorem selected_cut_10812 : selected 10 ⟨291431, by decide⟩
    (prefixPartial 11 6327) = some ⟨11, 2, 0, 291431, 6327, 1729, 262144⟩ := by
  decide +kernel

theorem context_11_6327_291431 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6327 ⟨291431, by decide⟩ :=
  accepted_of_selected 11 6327 ⟨291431, by decide⟩ ⟨11, 2, 0, 291431, 6327, 1729, 262144⟩
    (by decide) selected_cut_10812

theorem unmarked_context_10_1581_291432 : frontier 11 ⟨291432, by decide⟩
    (prefixCache 10 1581) (prefixPartial 10 1581) = false := by
  decide +kernel

theorem node_context_10_1581_291432 : EJMOriginalGlobalDAGData.nodes 11 ⟨291432, by decide⟩ =
    .split (coordinate 10) (![⟨291368, by decide⟩,⟨291390, by decide⟩,⟨291410, by decide⟩,⟨291431, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1581_291432 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1581 ⟨291432, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1581
    ⟨291432, by decide⟩ (by decide) (![⟨291368, by decide⟩,⟨291390, by decide⟩,⟨291410, by decide⟩,⟨291431, by decide⟩]) unmarked_context_10_1581_291432 node_context_10_1581_291432
  intro a
  fin_cases a
  · exact context_11_6324_291368
  · exact context_11_6325_291390
  · exact context_11_6326_291410
  · exact context_11_6327_291431

theorem selected_cut_10813 : selected 11 ⟨291479, by decide⟩
    (prefixPartial 10 1582) = some ⟨10, 2, 0, 291479, 1582, 4049, 1048576⟩ := by
  decide +kernel

theorem context_10_1582_291479 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1582 ⟨291479, by decide⟩ :=
  accepted_of_selected 10 1582 ⟨291479, by decide⟩ ⟨10, 2, 0, 291479, 1582, 4049, 1048576⟩
    (by decide) selected_cut_10813

theorem selected_cut_10814 : selected 11 ⟨291504, by decide⟩
    (prefixPartial 10 1583) = some ⟨10, 2, 0, 291504, 1583, 1685, 1048576⟩ := by
  decide +kernel

theorem context_10_1583_291504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1583 ⟨291504, by decide⟩ :=
  accepted_of_selected 10 1583 ⟨291504, by decide⟩ ⟨10, 2, 0, 291504, 1583, 1685, 1048576⟩
    (by decide) selected_cut_10814

theorem unmarked_context_9_395_291505 : frontier 12 ⟨291505, by decide⟩
    (prefixCache 9 395) (prefixPartial 9 395) = false := by
  decide +kernel

theorem node_context_9_395_291505 : EJMOriginalGlobalDAGData.nodes 12 ⟨291505, by decide⟩ =
    .split (coordinate 9) (![⟨291345, by decide⟩,⟨291432, by decide⟩,⟨291479, by decide⟩,⟨291504, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_395_291505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 395 ⟨291505, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 395
    ⟨291505, by decide⟩ (by decide) (![⟨291345, by decide⟩,⟨291432, by decide⟩,⟨291479, by decide⟩,⟨291504, by decide⟩]) unmarked_context_9_395_291505 node_context_9_395_291505
  intro a
  fin_cases a
  · exact context_10_1580_291345
  · exact context_10_1581_291432
  · exact context_10_1582_291479
  · exact context_10_1583_291504

theorem unmarked_context_8_98_291506 : frontier 13 ⟨291506, by decide⟩
    (prefixCache 8 98) (prefixPartial 8 98) = false := by
  decide +kernel

theorem node_context_8_98_291506 : EJMOriginalGlobalDAGData.nodes 13 ⟨291506, by decide⟩ =
    .split (coordinate 8) (![⟨287259, by decide⟩,⟨290055, by decide⟩,⟨291235, by decide⟩,⟨291505, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_98_291506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 98 ⟨291506, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 98
    ⟨291506, by decide⟩ (by decide) (![⟨287259, by decide⟩,⟨290055, by decide⟩,⟨291235, by decide⟩,⟨291505, by decide⟩]) unmarked_context_8_98_291506 node_context_8_98_291506
  intro a
  fin_cases a
  · exact context_9_392_287259
  · exact context_9_393_290055
  · exact context_9_394_291235
  · exact context_9_395_291505

theorem selected_cut_10815 : selected 10 ⟨167448, by decide⟩
    (prefixPartial 11 6336) = some ⟨11, 1, 0, 167448, 6336, 1, 262144⟩ := by
  decide +kernel

theorem context_11_6336_167448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6336 ⟨167448, by decide⟩ :=
  accepted_of_selected 11 6336 ⟨167448, by decide⟩ ⟨11, 1, 0, 167448, 6336, 1, 262144⟩
    (by decide) selected_cut_10815

theorem selected_cut_10816 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 25348) = some ⟨12, 1, 0, 34034, 25348, 1, 65536⟩ := by
  decide +kernel

theorem context_12_25348_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25348 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 25348 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 25348, 1, 65536⟩
    (by decide) selected_cut_10816

theorem selected_cut_10817 : selected 8 ⟨291583, by decide⟩
    (prefixPartial 13 101396) = some ⟨13, 2, 0, 291583, 101396, 3689, 16384⟩ := by
  decide +kernel

theorem context_13_101396_291583 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101396 ⟨291583, by decide⟩ :=
  accepted_of_selected 13 101396 ⟨291583, by decide⟩ ⟨13, 2, 0, 291583, 101396, 3689, 16384⟩
    (by decide) selected_cut_10817

theorem selected_cut_10818 : selected 8 ⟨291643, by decide⟩
    (prefixPartial 13 101397) = some ⟨13, 2, 0, 291643, 101397, 3521, 16384⟩ := by
  decide +kernel

theorem context_13_101397_291643 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101397 ⟨291643, by decide⟩ :=
  accepted_of_selected 13 101397 ⟨291643, by decide⟩ ⟨13, 2, 0, 291643, 101397, 3521, 16384⟩
    (by decide) selected_cut_10818

theorem selected_cut_10819 : selected 8 ⟨291678, by decide⟩
    (prefixPartial 13 101398) = some ⟨13, 2, 0, 291678, 101398, 2373, 16384⟩ := by
  decide +kernel

theorem context_13_101398_291678 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101398 ⟨291678, by decide⟩ :=
  accepted_of_selected 13 101398 ⟨291678, by decide⟩ ⟨13, 2, 0, 291678, 101398, 2373, 16384⟩
    (by decide) selected_cut_10819

theorem selected_cut_10820 : selected 8 ⟨291690, by decide⟩
    (prefixPartial 13 101399) = some ⟨13, 2, 0, 291690, 101399, 885, 16384⟩ := by
  decide +kernel

theorem context_13_101399_291690 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101399 ⟨291690, by decide⟩ :=
  accepted_of_selected 13 101399 ⟨291690, by decide⟩ ⟨13, 2, 0, 291690, 101399, 885, 16384⟩
    (by decide) selected_cut_10820

theorem unmarked_context_12_25349_291691 : frontier 9 ⟨291691, by decide⟩
    (prefixCache 12 25349) (prefixPartial 12 25349) = false := by
  decide +kernel

theorem node_context_12_25349_291691 : EJMOriginalGlobalDAGData.nodes 9 ⟨291691, by decide⟩ =
    .split (coordinate 12) (![⟨291583, by decide⟩,⟨291643, by decide⟩,⟨291678, by decide⟩,⟨291690, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25349_291691 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25349 ⟨291691, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25349
    ⟨291691, by decide⟩ (by decide) (![⟨291583, by decide⟩,⟨291643, by decide⟩,⟨291678, by decide⟩,⟨291690, by decide⟩]) unmarked_context_12_25349_291691 node_context_12_25349_291691
  intro a
  fin_cases a
  · exact context_13_101396_291583
  · exact context_13_101397_291643
  · exact context_13_101398_291678
  · exact context_13_101399_291690

theorem selected_cut_10821 : selected 8 ⟨291765, by decide⟩
    (prefixPartial 13 101400) = some ⟨13, 2, 0, 291765, 101400, 3721, 16384⟩ := by
  decide +kernel

theorem context_13_101400_291765 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101400 ⟨291765, by decide⟩ :=
  accepted_of_selected 13 101400 ⟨291765, by decide⟩ ⟨13, 2, 0, 291765, 101400, 3721, 16384⟩
    (by decide) selected_cut_10821

theorem selected_cut_10822 : selected 8 ⟨291809, by decide⟩
    (prefixPartial 13 101401) = some ⟨13, 2, 0, 291809, 101401, 3377, 16384⟩ := by
  decide +kernel

theorem context_13_101401_291809 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101401 ⟨291809, by decide⟩ :=
  accepted_of_selected 13 101401 ⟨291809, by decide⟩ ⟨13, 2, 0, 291809, 101401, 3377, 16384⟩
    (by decide) selected_cut_10822

theorem selected_cut_10823 : selected 8 ⟨291854, by decide⟩
    (prefixPartial 13 101402) = some ⟨13, 2, 0, 291854, 101402, 2537, 16384⟩ := by
  decide +kernel

theorem context_13_101402_291854 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101402 ⟨291854, by decide⟩ :=
  accepted_of_selected 13 101402 ⟨291854, by decide⟩ ⟨13, 2, 0, 291854, 101402, 2537, 16384⟩
    (by decide) selected_cut_10823

theorem selected_cut_10824 : selected 8 ⟨291867, by decide⟩
    (prefixPartial 13 101403) = some ⟨13, 2, 0, 291867, 101403, 989, 16384⟩ := by
  decide +kernel

theorem context_13_101403_291867 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101403 ⟨291867, by decide⟩ :=
  accepted_of_selected 13 101403 ⟨291867, by decide⟩ ⟨13, 2, 0, 291867, 101403, 989, 16384⟩
    (by decide) selected_cut_10824

theorem unmarked_context_12_25350_291868 : frontier 9 ⟨291868, by decide⟩
    (prefixCache 12 25350) (prefixPartial 12 25350) = false := by
  decide +kernel

theorem node_context_12_25350_291868 : EJMOriginalGlobalDAGData.nodes 9 ⟨291868, by decide⟩ =
    .split (coordinate 12) (![⟨291765, by decide⟩,⟨291809, by decide⟩,⟨291854, by decide⟩,⟨291867, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25350_291868 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25350 ⟨291868, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25350
    ⟨291868, by decide⟩ (by decide) (![⟨291765, by decide⟩,⟨291809, by decide⟩,⟨291854, by decide⟩,⟨291867, by decide⟩]) unmarked_context_12_25350_291868 node_context_12_25350_291868
  intro a
  fin_cases a
  · exact context_13_101400_291765
  · exact context_13_101401_291809
  · exact context_13_101402_291854
  · exact context_13_101403_291867

theorem selected_cut_10825 : selected 8 ⟨291935, by decide⟩
    (prefixPartial 13 101404) = some ⟨13, 2, 0, 291935, 101404, 4081, 16384⟩ := by
  decide +kernel

theorem context_13_101404_291935 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101404 ⟨291935, by decide⟩ :=
  accepted_of_selected 13 101404 ⟨291935, by decide⟩ ⟨13, 2, 0, 291935, 101404, 4081, 16384⟩
    (by decide) selected_cut_10825

theorem selected_cut_10826 : selected 8 ⟨291978, by decide⟩
    (prefixPartial 13 101405) = some ⟨13, 2, 0, 291978, 101405, 3353, 16384⟩ := by
  decide +kernel

theorem context_13_101405_291978 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101405 ⟨291978, by decide⟩ :=
  accepted_of_selected 13 101405 ⟨291978, by decide⟩ ⟨13, 2, 0, 291978, 101405, 3353, 16384⟩
    (by decide) selected_cut_10826

theorem selected_cut_10827 : selected 8 ⟨292011, by decide⟩
    (prefixPartial 13 101406) = some ⟨13, 2, 0, 292011, 101406, 2413, 16384⟩ := by
  decide +kernel

theorem context_13_101406_292011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101406 ⟨292011, by decide⟩ :=
  accepted_of_selected 13 101406 ⟨292011, by decide⟩ ⟨13, 2, 0, 292011, 101406, 2413, 16384⟩
    (by decide) selected_cut_10827

theorem selected_cut_10828 : selected 8 ⟨292025, by decide⟩
    (prefixPartial 13 101407) = some ⟨13, 2, 0, 292025, 101407, 1005, 16384⟩ := by
  decide +kernel

theorem context_13_101407_292025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101407 ⟨292025, by decide⟩ :=
  accepted_of_selected 13 101407 ⟨292025, by decide⟩ ⟨13, 2, 0, 292025, 101407, 1005, 16384⟩
    (by decide) selected_cut_10828

theorem unmarked_context_12_25351_292026 : frontier 9 ⟨292026, by decide⟩
    (prefixCache 12 25351) (prefixPartial 12 25351) = false := by
  decide +kernel

theorem node_context_12_25351_292026 : EJMOriginalGlobalDAGData.nodes 9 ⟨292026, by decide⟩ =
    .split (coordinate 12) (![⟨291935, by decide⟩,⟨291978, by decide⟩,⟨292011, by decide⟩,⟨292025, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25351_292026 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25351 ⟨292026, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25351
    ⟨292026, by decide⟩ (by decide) (![⟨291935, by decide⟩,⟨291978, by decide⟩,⟨292011, by decide⟩,⟨292025, by decide⟩]) unmarked_context_12_25351_292026 node_context_12_25351_292026
  intro a
  fin_cases a
  · exact context_13_101404_291935
  · exact context_13_101405_291978
  · exact context_13_101406_292011
  · exact context_13_101407_292025

theorem unmarked_context_11_6337_292027 : frontier 10 ⟨292027, by decide⟩
    (prefixCache 11 6337) (prefixPartial 11 6337) = false := by
  decide +kernel

theorem node_context_11_6337_292027 : EJMOriginalGlobalDAGData.nodes 10 ⟨292027, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨291691, by decide⟩,⟨291868, by decide⟩,⟨292026, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6337_292027 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6337 ⟨292027, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6337
    ⟨292027, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨291691, by decide⟩,⟨291868, by decide⟩,⟨292026, by decide⟩]) unmarked_context_11_6337_292027 node_context_11_6337_292027
  intro a
  fin_cases a
  · exact context_12_25348_34034
  · exact context_12_25349_291691
  · exact context_12_25350_291868
  · exact context_12_25351_292026

theorem selected_cut_10829 : selected 8 ⟨292087, by decide⟩
    (prefixPartial 13 101408) = some ⟨13, 2, 0, 292087, 101408, 3277, 16384⟩ := by
  decide +kernel

theorem context_13_101408_292087 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101408 ⟨292087, by decide⟩ :=
  accepted_of_selected 13 101408 ⟨292087, by decide⟩ ⟨13, 2, 0, 292087, 101408, 3277, 16384⟩
    (by decide) selected_cut_10829

theorem selected_cut_10830 : selected 8 ⟨292132, by decide⟩
    (prefixPartial 13 101409) = some ⟨13, 2, 0, 292132, 101409, 3325, 16384⟩ := by
  decide +kernel

theorem context_13_101409_292132 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101409 ⟨292132, by decide⟩ :=
  accepted_of_selected 13 101409 ⟨292132, by decide⟩ ⟨13, 2, 0, 292132, 101409, 3325, 16384⟩
    (by decide) selected_cut_10830

theorem selected_cut_10831 : selected 8 ⟨292169, by decide⟩
    (prefixPartial 13 101410) = some ⟨13, 2, 0, 292169, 101410, 2493, 16384⟩ := by
  decide +kernel

theorem context_13_101410_292169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101410 ⟨292169, by decide⟩ :=
  accepted_of_selected 13 101410 ⟨292169, by decide⟩ ⟨13, 2, 0, 292169, 101410, 2493, 16384⟩
    (by decide) selected_cut_10831

theorem selected_cut_10832 : selected 8 ⟨292185, by decide⟩
    (prefixPartial 13 101411) = some ⟨13, 2, 0, 292185, 101411, 965, 16384⟩ := by
  decide +kernel

theorem context_13_101411_292185 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101411 ⟨292185, by decide⟩ :=
  accepted_of_selected 13 101411 ⟨292185, by decide⟩ ⟨13, 2, 0, 292185, 101411, 965, 16384⟩
    (by decide) selected_cut_10832

theorem unmarked_context_12_25352_292186 : frontier 9 ⟨292186, by decide⟩
    (prefixCache 12 25352) (prefixPartial 12 25352) = false := by
  decide +kernel

theorem node_context_12_25352_292186 : EJMOriginalGlobalDAGData.nodes 9 ⟨292186, by decide⟩ =
    .split (coordinate 12) (![⟨292087, by decide⟩,⟨292132, by decide⟩,⟨292169, by decide⟩,⟨292185, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25352_292186 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25352 ⟨292186, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25352
    ⟨292186, by decide⟩ (by decide) (![⟨292087, by decide⟩,⟨292132, by decide⟩,⟨292169, by decide⟩,⟨292185, by decide⟩]) unmarked_context_12_25352_292186 node_context_12_25352_292186
  intro a
  fin_cases a
  · exact context_13_101408_292087
  · exact context_13_101409_292132
  · exact context_13_101410_292169
  · exact context_13_101411_292185

theorem selected_cut_10833 : selected 8 ⟨292245, by decide⟩
    (prefixPartial 13 101412) = some ⟨13, 2, 0, 292245, 101412, 3389, 16384⟩ := by
  decide +kernel

theorem context_13_101412_292245 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101412 ⟨292245, by decide⟩ :=
  accepted_of_selected 13 101412 ⟨292245, by decide⟩ ⟨13, 2, 0, 292245, 101412, 3389, 16384⟩
    (by decide) selected_cut_10833

theorem selected_cut_10834 : selected 8 ⟨292298, by decide⟩
    (prefixPartial 13 101413) = some ⟨13, 2, 0, 292298, 101413, 3681, 16384⟩ := by
  decide +kernel

theorem context_13_101413_292298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101413 ⟨292298, by decide⟩ :=
  accepted_of_selected 13 101413 ⟨292298, by decide⟩ ⟨13, 2, 0, 292298, 101413, 3681, 16384⟩
    (by decide) selected_cut_10834

theorem selected_cut_10835 : selected 8 ⟨292329, by decide⟩
    (prefixPartial 13 101414) = some ⟨13, 2, 0, 292329, 101414, 2401, 16384⟩ := by
  decide +kernel

theorem context_13_101414_292329 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101414 ⟨292329, by decide⟩ :=
  accepted_of_selected 13 101414 ⟨292329, by decide⟩ ⟨13, 2, 0, 292329, 101414, 2401, 16384⟩
    (by decide) selected_cut_10835

theorem selected_cut_10836 : selected 8 ⟨292343, by decide⟩
    (prefixPartial 13 101415) = some ⟨13, 2, 0, 292343, 101415, 981, 16384⟩ := by
  decide +kernel

theorem context_13_101415_292343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101415 ⟨292343, by decide⟩ :=
  accepted_of_selected 13 101415 ⟨292343, by decide⟩ ⟨13, 2, 0, 292343, 101415, 981, 16384⟩
    (by decide) selected_cut_10836

theorem unmarked_context_12_25353_292344 : frontier 9 ⟨292344, by decide⟩
    (prefixCache 12 25353) (prefixPartial 12 25353) = false := by
  decide +kernel

theorem node_context_12_25353_292344 : EJMOriginalGlobalDAGData.nodes 9 ⟨292344, by decide⟩ =
    .split (coordinate 12) (![⟨292245, by decide⟩,⟨292298, by decide⟩,⟨292329, by decide⟩,⟨292343, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25353_292344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25353 ⟨292344, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25353
    ⟨292344, by decide⟩ (by decide) (![⟨292245, by decide⟩,⟨292298, by decide⟩,⟨292329, by decide⟩,⟨292343, by decide⟩]) unmarked_context_12_25353_292344 node_context_12_25353_292344
  intro a
  fin_cases a
  · exact context_13_101412_292245
  · exact context_13_101413_292298
  · exact context_13_101414_292329
  · exact context_13_101415_292343

theorem selected_cut_10837 : selected 8 ⟨292393, by decide⟩
    (prefixPartial 13 101416) = some ⟨13, 2, 0, 292393, 101416, 3145, 16384⟩ := by
  decide +kernel

theorem context_13_101416_292393 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101416 ⟨292393, by decide⟩ :=
  accepted_of_selected 13 101416 ⟨292393, by decide⟩ ⟨13, 2, 0, 292393, 101416, 3145, 16384⟩
    (by decide) selected_cut_10837

theorem selected_cut_10838 : selected 8 ⟨292444, by decide⟩
    (prefixPartial 13 101417) = some ⟨13, 2, 0, 292444, 101417, 3477, 16384⟩ := by
  decide +kernel

theorem context_13_101417_292444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101417 ⟨292444, by decide⟩ :=
  accepted_of_selected 13 101417 ⟨292444, by decide⟩ ⟨13, 2, 0, 292444, 101417, 3477, 16384⟩
    (by decide) selected_cut_10838

theorem selected_cut_10839 : selected 8 ⟨292482, by decide⟩
    (prefixPartial 13 101418) = some ⟨13, 2, 0, 292482, 101418, 2525, 16384⟩ := by
  decide +kernel

theorem context_13_101418_292482 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101418 ⟨292482, by decide⟩ :=
  accepted_of_selected 13 101418 ⟨292482, by decide⟩ ⟨13, 2, 0, 292482, 101418, 2525, 16384⟩
    (by decide) selected_cut_10839

theorem selected_cut_10840 : selected 8 ⟨292491, by decide⟩
    (prefixPartial 13 101419) = some ⟨13, 2, 0, 292491, 101419, 905, 16384⟩ := by
  decide +kernel

theorem context_13_101419_292491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101419 ⟨292491, by decide⟩ :=
  accepted_of_selected 13 101419 ⟨292491, by decide⟩ ⟨13, 2, 0, 292491, 101419, 905, 16384⟩
    (by decide) selected_cut_10840

theorem unmarked_context_12_25354_292492 : frontier 9 ⟨292492, by decide⟩
    (prefixCache 12 25354) (prefixPartial 12 25354) = false := by
  decide +kernel

theorem node_context_12_25354_292492 : EJMOriginalGlobalDAGData.nodes 9 ⟨292492, by decide⟩ =
    .split (coordinate 12) (![⟨292393, by decide⟩,⟨292444, by decide⟩,⟨292482, by decide⟩,⟨292491, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25354_292492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25354 ⟨292492, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25354
    ⟨292492, by decide⟩ (by decide) (![⟨292393, by decide⟩,⟨292444, by decide⟩,⟨292482, by decide⟩,⟨292491, by decide⟩]) unmarked_context_12_25354_292492 node_context_12_25354_292492
  intro a
  fin_cases a
  · exact context_13_101416_292393
  · exact context_13_101417_292444
  · exact context_13_101418_292482
  · exact context_13_101419_292491

theorem selected_cut_10841 : selected 8 ⟨292552, by decide⟩
    (prefixPartial 13 101420) = some ⟨13, 2, 0, 292552, 101420, 3425, 16384⟩ := by
  decide +kernel

theorem context_13_101420_292552 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101420 ⟨292552, by decide⟩ :=
  accepted_of_selected 13 101420 ⟨292552, by decide⟩ ⟨13, 2, 0, 292552, 101420, 3425, 16384⟩
    (by decide) selected_cut_10841

theorem selected_cut_10842 : selected 8 ⟨292605, by decide⟩
    (prefixPartial 13 101421) = some ⟨13, 2, 0, 292605, 101421, 3553, 16384⟩ := by
  decide +kernel

theorem context_13_101421_292605 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101421 ⟨292605, by decide⟩ :=
  accepted_of_selected 13 101421 ⟨292605, by decide⟩ ⟨13, 2, 0, 292605, 101421, 3553, 16384⟩
    (by decide) selected_cut_10842

theorem selected_cut_10843 : selected 8 ⟨292634, by decide⟩
    (prefixPartial 13 101422) = some ⟨13, 2, 0, 292634, 101422, 2257, 16384⟩ := by
  decide +kernel

theorem context_13_101422_292634 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101422 ⟨292634, by decide⟩ :=
  accepted_of_selected 13 101422 ⟨292634, by decide⟩ ⟨13, 2, 0, 292634, 101422, 2257, 16384⟩
    (by decide) selected_cut_10843

theorem selected_cut_10844 : selected 8 ⟨292648, by decide⟩
    (prefixPartial 13 101423) = some ⟨13, 2, 0, 292648, 101423, 917, 16384⟩ := by
  decide +kernel

theorem context_13_101423_292648 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101423 ⟨292648, by decide⟩ :=
  accepted_of_selected 13 101423 ⟨292648, by decide⟩ ⟨13, 2, 0, 292648, 101423, 917, 16384⟩
    (by decide) selected_cut_10844

theorem unmarked_context_12_25355_292649 : frontier 9 ⟨292649, by decide⟩
    (prefixCache 12 25355) (prefixPartial 12 25355) = false := by
  decide +kernel

theorem node_context_12_25355_292649 : EJMOriginalGlobalDAGData.nodes 9 ⟨292649, by decide⟩ =
    .split (coordinate 12) (![⟨292552, by decide⟩,⟨292605, by decide⟩,⟨292634, by decide⟩,⟨292648, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25355_292649 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25355 ⟨292649, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25355
    ⟨292649, by decide⟩ (by decide) (![⟨292552, by decide⟩,⟨292605, by decide⟩,⟨292634, by decide⟩,⟨292648, by decide⟩]) unmarked_context_12_25355_292649 node_context_12_25355_292649
  intro a
  fin_cases a
  · exact context_13_101420_292552
  · exact context_13_101421_292605
  · exact context_13_101422_292634
  · exact context_13_101423_292648

theorem unmarked_context_11_6338_292650 : frontier 10 ⟨292650, by decide⟩
    (prefixCache 11 6338) (prefixPartial 11 6338) = false := by
  decide +kernel

theorem node_context_11_6338_292650 : EJMOriginalGlobalDAGData.nodes 10 ⟨292650, by decide⟩ =
    .split (coordinate 11) (![⟨292186, by decide⟩,⟨292344, by decide⟩,⟨292492, by decide⟩,⟨292649, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6338_292650 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6338 ⟨292650, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6338
    ⟨292650, by decide⟩ (by decide) (![⟨292186, by decide⟩,⟨292344, by decide⟩,⟨292492, by decide⟩,⟨292649, by decide⟩]) unmarked_context_11_6338_292650 node_context_11_6338_292650
  intro a
  fin_cases a
  · exact context_12_25352_292186
  · exact context_12_25353_292344
  · exact context_12_25354_292492
  · exact context_12_25355_292649

theorem selected_cut_10845 : selected 9 ⟨292651, by decide⟩
    (prefixPartial 12 25356) = some ⟨12, 1, 0, 292651, 25356, 1, 65536⟩ := by
  decide +kernel

theorem context_12_25356_292651 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25356 ⟨292651, by decide⟩ :=
  accepted_of_selected 12 25356 ⟨292651, by decide⟩ ⟨12, 1, 0, 292651, 25356, 1, 65536⟩
    (by decide) selected_cut_10845

theorem selected_cut_10846 : selected 8 ⟨292695, by decide⟩
    (prefixPartial 13 101428) = some ⟨13, 2, 0, 292695, 101428, 2901, 16384⟩ := by
  decide +kernel

theorem context_13_101428_292695 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101428 ⟨292695, by decide⟩ :=
  accepted_of_selected 13 101428 ⟨292695, by decide⟩ ⟨13, 2, 0, 292695, 101428, 2901, 16384⟩
    (by decide) selected_cut_10846

theorem selected_cut_10847 : selected 8 ⟨292748, by decide⟩
    (prefixPartial 13 101429) = some ⟨13, 2, 0, 292748, 101429, 3349, 16384⟩ := by
  decide +kernel

theorem context_13_101429_292748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101429 ⟨292748, by decide⟩ :=
  accepted_of_selected 13 101429 ⟨292748, by decide⟩ ⟨13, 2, 0, 292748, 101429, 3349, 16384⟩
    (by decide) selected_cut_10847

theorem selected_cut_10848 : selected 8 ⟨292779, by decide⟩
    (prefixPartial 13 101430) = some ⟨13, 2, 0, 292779, 101430, 2321, 16384⟩ := by
  decide +kernel

theorem context_13_101430_292779 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101430 ⟨292779, by decide⟩ :=
  accepted_of_selected 13 101430 ⟨292779, by decide⟩ ⟨13, 2, 0, 292779, 101430, 2321, 16384⟩
    (by decide) selected_cut_10848

theorem selected_cut_10849 : selected 8 ⟨292792, by decide⟩
    (prefixPartial 13 101431) = some ⟨13, 2, 0, 292792, 101431, 845, 16384⟩ := by
  decide +kernel

theorem context_13_101431_292792 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101431 ⟨292792, by decide⟩ :=
  accepted_of_selected 13 101431 ⟨292792, by decide⟩ ⟨13, 2, 0, 292792, 101431, 845, 16384⟩
    (by decide) selected_cut_10849

theorem unmarked_context_12_25357_292793 : frontier 9 ⟨292793, by decide⟩
    (prefixCache 12 25357) (prefixPartial 12 25357) = false := by
  decide +kernel

theorem node_context_12_25357_292793 : EJMOriginalGlobalDAGData.nodes 9 ⟨292793, by decide⟩ =
    .split (coordinate 12) (![⟨292695, by decide⟩,⟨292748, by decide⟩,⟨292779, by decide⟩,⟨292792, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25357_292793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25357 ⟨292793, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25357
    ⟨292793, by decide⟩ (by decide) (![⟨292695, by decide⟩,⟨292748, by decide⟩,⟨292779, by decide⟩,⟨292792, by decide⟩]) unmarked_context_12_25357_292793 node_context_12_25357_292793
  intro a
  fin_cases a
  · exact context_13_101428_292695
  · exact context_13_101429_292748
  · exact context_13_101430_292779
  · exact context_13_101431_292792

theorem selected_cut_10850 : selected 8 ⟨292837, by decide⟩
    (prefixPartial 13 101432) = some ⟨13, 2, 0, 292837, 101432, 3073, 16384⟩ := by
  decide +kernel

theorem context_13_101432_292837 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101432 ⟨292837, by decide⟩ :=
  accepted_of_selected 13 101432 ⟨292837, by decide⟩ ⟨13, 2, 0, 292837, 101432, 3073, 16384⟩
    (by decide) selected_cut_10850

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
