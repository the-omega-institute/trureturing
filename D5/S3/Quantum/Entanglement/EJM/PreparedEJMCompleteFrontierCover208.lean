/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover207
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_19972 : selected 8 ⟨511357, by decide⟩
    (prefixPartial 13 289978) = some ⟨13, 2, 0, 511357, 289978, 1853, 16384⟩ := by
  decide +kernel

theorem context_13_289978_511357 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289978 ⟨511357, by decide⟩ :=
  accepted_of_selected 13 289978 ⟨511357, by decide⟩ ⟨13, 2, 0, 511357, 289978, 1853, 16384⟩
    (by decide) selected_cut_19972

theorem selected_cut_19973 : selected 8 ⟨511363, by decide⟩
    (prefixPartial 13 289979) = some ⟨13, 2, 0, 511363, 289979, 761, 16384⟩ := by
  decide +kernel

theorem context_13_289979_511363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289979 ⟨511363, by decide⟩ :=
  accepted_of_selected 13 289979 ⟨511363, by decide⟩ ⟨13, 2, 0, 511363, 289979, 761, 16384⟩
    (by decide) selected_cut_19973

theorem unmarked_context_12_72494_511364 : frontier 9 ⟨511364, by decide⟩
    (prefixCache 12 72494) (prefixPartial 12 72494) = false := by
  decide +kernel

theorem node_context_12_72494_511364 : EJMOriginalGlobalDAGData.nodes 9 ⟨511364, by decide⟩ =
    .split (coordinate 12) (![⟨511294, by decide⟩,⟨511333, by decide⟩,⟨511357, by decide⟩,⟨511363, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72494_511364 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72494 ⟨511364, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72494
    ⟨511364, by decide⟩ (by decide) (![⟨511294, by decide⟩,⟨511333, by decide⟩,⟨511357, by decide⟩,⟨511363, by decide⟩]) unmarked_context_12_72494_511364 node_context_12_72494_511364
  intro a
  fin_cases a
  · exact context_13_289976_511294
  · exact context_13_289977_511333
  · exact context_13_289978_511357
  · exact context_13_289979_511363

theorem selected_cut_19974 : selected 8 ⟨511382, by decide⟩
    (prefixPartial 13 289980) = some ⟨13, 2, 0, 511382, 289980, 1077, 16384⟩ := by
  decide +kernel

theorem context_13_289980_511382 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289980 ⟨511382, by decide⟩ :=
  accepted_of_selected 13 289980 ⟨511382, by decide⟩ ⟨13, 2, 0, 511382, 289980, 1077, 16384⟩
    (by decide) selected_cut_19974

theorem selected_cut_19975 : selected 8 ⟨511423, by decide⟩
    (prefixPartial 13 289981) = some ⟨13, 2, 0, 511423, 289981, 3809, 16384⟩ := by
  decide +kernel

theorem context_13_289981_511423 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289981 ⟨511423, by decide⟩ :=
  accepted_of_selected 13 289981 ⟨511423, by decide⟩ ⟨13, 2, 0, 511423, 289981, 3809, 16384⟩
    (by decide) selected_cut_19975

theorem selected_cut_19976 : selected 8 ⟨511489, by decide⟩
    (prefixPartial 13 289982) = some ⟨13, 2, 0, 511489, 289982, 2793, 16384⟩ := by
  decide +kernel

theorem context_13_289982_511489 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289982 ⟨511489, by decide⟩ :=
  accepted_of_selected 13 289982 ⟨511489, by decide⟩ ⟨13, 2, 0, 511489, 289982, 2793, 16384⟩
    (by decide) selected_cut_19976

theorem selected_cut_19977 : selected 8 ⟨511499, by decide⟩
    (prefixPartial 13 289983) = some ⟨13, 2, 0, 511499, 289983, 1129, 16384⟩ := by
  decide +kernel

theorem context_13_289983_511499 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289983 ⟨511499, by decide⟩ :=
  accepted_of_selected 13 289983 ⟨511499, by decide⟩ ⟨13, 2, 0, 511499, 289983, 1129, 16384⟩
    (by decide) selected_cut_19977

theorem unmarked_context_12_72495_511500 : frontier 9 ⟨511500, by decide⟩
    (prefixCache 12 72495) (prefixPartial 12 72495) = false := by
  decide +kernel

theorem node_context_12_72495_511500 : EJMOriginalGlobalDAGData.nodes 9 ⟨511500, by decide⟩ =
    .split (coordinate 12) (![⟨511382, by decide⟩,⟨511423, by decide⟩,⟨511489, by decide⟩,⟨511499, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72495_511500 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72495 ⟨511500, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72495
    ⟨511500, by decide⟩ (by decide) (![⟨511382, by decide⟩,⟨511423, by decide⟩,⟨511489, by decide⟩,⟨511499, by decide⟩]) unmarked_context_12_72495_511500 node_context_12_72495_511500
  intro a
  fin_cases a
  · exact context_13_289980_511382
  · exact context_13_289981_511423
  · exact context_13_289982_511489
  · exact context_13_289983_511499

theorem unmarked_context_11_18123_511501 : frontier 10 ⟨511501, by decide⟩
    (prefixCache 11 18123) (prefixPartial 11 18123) = false := by
  decide +kernel

theorem node_context_11_18123_511501 : EJMOriginalGlobalDAGData.nodes 10 ⟨511501, by decide⟩ =
    .split (coordinate 11) (![⟨511211, by decide⟩,⟨511281, by decide⟩,⟨511364, by decide⟩,⟨511500, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18123_511501 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18123 ⟨511501, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18123
    ⟨511501, by decide⟩ (by decide) (![⟨511211, by decide⟩,⟨511281, by decide⟩,⟨511364, by decide⟩,⟨511500, by decide⟩]) unmarked_context_11_18123_511501 node_context_11_18123_511501
  intro a
  fin_cases a
  · exact context_12_72492_511211
  · exact context_12_72493_511281
  · exact context_12_72494_511364
  · exact context_12_72495_511500

theorem unmarked_context_10_4530_511502 : frontier 11 ⟨511502, by decide⟩
    (prefixCache 10 4530) (prefixPartial 10 4530) = false := by
  decide +kernel

theorem node_context_10_4530_511502 : EJMOriginalGlobalDAGData.nodes 11 ⟨511502, by decide⟩ =
    .split (coordinate 10) (![⟨510488, by decide⟩,⟨510900, by decide⟩,⟨511103, by decide⟩,⟨511501, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4530_511502 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4530 ⟨511502, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4530
    ⟨511502, by decide⟩ (by decide) (![⟨510488, by decide⟩,⟨510900, by decide⟩,⟨511103, by decide⟩,⟨511501, by decide⟩]) unmarked_context_10_4530_511502 node_context_10_4530_511502
  intro a
  fin_cases a
  · exact context_11_18120_510488
  · exact context_11_18121_510900
  · exact context_11_18122_511103
  · exact context_11_18123_511501

theorem selected_cut_19978 : selected 9 ⟨445562, by decide⟩
    (prefixPartial 12 72496) = some ⟨12, 1, 0, 445562, 72496, 1, 65536⟩ := by
  decide +kernel

theorem context_12_72496_445562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72496 ⟨445562, by decide⟩ :=
  accepted_of_selected 12 72496 ⟨445562, by decide⟩ ⟨12, 1, 0, 445562, 72496, 1, 65536⟩
    (by decide) selected_cut_19978

theorem selected_cut_19979 : selected 8 ⟨511514, by decide⟩
    (prefixPartial 13 289988) = some ⟨13, 2, 0, 511514, 289988, 537, 16384⟩ := by
  decide +kernel

theorem context_13_289988_511514 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289988 ⟨511514, by decide⟩ :=
  accepted_of_selected 13 289988 ⟨511514, by decide⟩ ⟨13, 2, 0, 511514, 289988, 537, 16384⟩
    (by decide) selected_cut_19979

theorem selected_cut_19980 : selected 8 ⟨511552, by decide⟩
    (prefixPartial 13 289989) = some ⟨13, 2, 0, 511552, 289989, 2313, 16384⟩ := by
  decide +kernel

theorem context_13_289989_511552 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289989 ⟨511552, by decide⟩ :=
  accepted_of_selected 13 289989 ⟨511552, by decide⟩ ⟨13, 2, 0, 511552, 289989, 2313, 16384⟩
    (by decide) selected_cut_19980

theorem selected_cut_19981 : selected 8 ⟨511571, by decide⟩
    (prefixPartial 13 289990) = some ⟨13, 2, 0, 511571, 289990, 1549, 16384⟩ := by
  decide +kernel

theorem context_13_289990_511571 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289990 ⟨511571, by decide⟩ :=
  accepted_of_selected 13 289990 ⟨511571, by decide⟩ ⟨13, 2, 0, 511571, 289990, 1549, 16384⟩
    (by decide) selected_cut_19981

theorem selected_cut_19982 : selected 8 ⟨511579, by decide⟩
    (prefixPartial 13 289991) = some ⟨13, 2, 0, 511579, 289991, 837, 16384⟩ := by
  decide +kernel

theorem context_13_289991_511579 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289991 ⟨511579, by decide⟩ :=
  accepted_of_selected 13 289991 ⟨511579, by decide⟩ ⟨13, 2, 0, 511579, 289991, 837, 16384⟩
    (by decide) selected_cut_19982

theorem unmarked_context_12_72497_511580 : frontier 9 ⟨511580, by decide⟩
    (prefixCache 12 72497) (prefixPartial 12 72497) = false := by
  decide +kernel

theorem node_context_12_72497_511580 : EJMOriginalGlobalDAGData.nodes 9 ⟨511580, by decide⟩ =
    .split (coordinate 12) (![⟨511514, by decide⟩,⟨511552, by decide⟩,⟨511571, by decide⟩,⟨511579, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72497_511580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72497 ⟨511580, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72497
    ⟨511580, by decide⟩ (by decide) (![⟨511514, by decide⟩,⟨511552, by decide⟩,⟨511571, by decide⟩,⟨511579, by decide⟩]) unmarked_context_12_72497_511580 node_context_12_72497_511580
  intro a
  fin_cases a
  · exact context_13_289988_511514
  · exact context_13_289989_511552
  · exact context_13_289990_511571
  · exact context_13_289991_511579

theorem selected_cut_19983 : selected 8 ⟨511594, by decide⟩
    (prefixPartial 13 289992) = some ⟨13, 2, 0, 511594, 289992, 561, 16384⟩ := by
  decide +kernel

theorem context_13_289992_511594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289992 ⟨511594, by decide⟩ :=
  accepted_of_selected 13 289992 ⟨511594, by decide⟩ ⟨13, 2, 0, 511594, 289992, 561, 16384⟩
    (by decide) selected_cut_19983

theorem selected_cut_19984 : selected 8 ⟨511628, by decide⟩
    (prefixPartial 13 289993) = some ⟨13, 2, 0, 511628, 289993, 2405, 16384⟩ := by
  decide +kernel

theorem context_13_289993_511628 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289993 ⟨511628, by decide⟩ :=
  accepted_of_selected 13 289993 ⟨511628, by decide⟩ ⟨13, 2, 0, 511628, 289993, 2405, 16384⟩
    (by decide) selected_cut_19984

theorem selected_cut_19985 : selected 8 ⟨511651, by decide⟩
    (prefixPartial 13 289994) = some ⟨13, 2, 0, 511651, 289994, 1949, 16384⟩ := by
  decide +kernel

theorem context_13_289994_511651 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289994 ⟨511651, by decide⟩ :=
  accepted_of_selected 13 289994 ⟨511651, by decide⟩ ⟨13, 2, 0, 511651, 289994, 1949, 16384⟩
    (by decide) selected_cut_19985

theorem selected_cut_19986 : selected 8 ⟨511657, by decide⟩
    (prefixPartial 13 289995) = some ⟨13, 2, 0, 511657, 289995, 833, 16384⟩ := by
  decide +kernel

theorem context_13_289995_511657 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289995 ⟨511657, by decide⟩ :=
  accepted_of_selected 13 289995 ⟨511657, by decide⟩ ⟨13, 2, 0, 511657, 289995, 833, 16384⟩
    (by decide) selected_cut_19986

theorem unmarked_context_12_72498_511658 : frontier 9 ⟨511658, by decide⟩
    (prefixCache 12 72498) (prefixPartial 12 72498) = false := by
  decide +kernel

theorem node_context_12_72498_511658 : EJMOriginalGlobalDAGData.nodes 9 ⟨511658, by decide⟩ =
    .split (coordinate 12) (![⟨511594, by decide⟩,⟨511628, by decide⟩,⟨511651, by decide⟩,⟨511657, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72498_511658 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72498 ⟨511658, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72498
    ⟨511658, by decide⟩ (by decide) (![⟨511594, by decide⟩,⟨511628, by decide⟩,⟨511651, by decide⟩,⟨511657, by decide⟩]) unmarked_context_12_72498_511658 node_context_12_72498_511658
  intro a
  fin_cases a
  · exact context_13_289992_511594
  · exact context_13_289993_511628
  · exact context_13_289994_511651
  · exact context_13_289995_511657

theorem selected_cut_19987 : selected 8 ⟨511665, by decide⟩
    (prefixPartial 13 289996) = some ⟨13, 2, 0, 511665, 289996, 453, 16384⟩ := by
  decide +kernel

theorem context_13_289996_511665 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289996 ⟨511665, by decide⟩ :=
  accepted_of_selected 13 289996 ⟨511665, by decide⟩ ⟨13, 2, 0, 511665, 289996, 453, 16384⟩
    (by decide) selected_cut_19987

theorem selected_cut_19988 : selected 8 ⟨511693, by decide⟩
    (prefixPartial 13 289997) = some ⟨13, 2, 0, 511693, 289997, 1925, 16384⟩ := by
  decide +kernel

theorem context_13_289997_511693 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289997 ⟨511693, by decide⟩ :=
  accepted_of_selected 13 289997 ⟨511693, by decide⟩ ⟨13, 2, 0, 511693, 289997, 1925, 16384⟩
    (by decide) selected_cut_19988

theorem selected_cut_19989 : selected 8 ⟨511714, by decide⟩
    (prefixPartial 13 289998) = some ⟨13, 2, 0, 511714, 289998, 1689, 16384⟩ := by
  decide +kernel

theorem context_13_289998_511714 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289998 ⟨511714, by decide⟩ :=
  accepted_of_selected 13 289998 ⟨511714, by decide⟩ ⟨13, 2, 0, 511714, 289998, 1689, 16384⟩
    (by decide) selected_cut_19989

theorem selected_cut_19990 : selected 8 ⟨511720, by decide⟩
    (prefixPartial 13 289999) = some ⟨13, 2, 0, 511720, 289999, 725, 16384⟩ := by
  decide +kernel

theorem context_13_289999_511720 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289999 ⟨511720, by decide⟩ :=
  accepted_of_selected 13 289999 ⟨511720, by decide⟩ ⟨13, 2, 0, 511720, 289999, 725, 16384⟩
    (by decide) selected_cut_19990

theorem unmarked_context_12_72499_511721 : frontier 9 ⟨511721, by decide⟩
    (prefixCache 12 72499) (prefixPartial 12 72499) = false := by
  decide +kernel

theorem node_context_12_72499_511721 : EJMOriginalGlobalDAGData.nodes 9 ⟨511721, by decide⟩ =
    .split (coordinate 12) (![⟨511665, by decide⟩,⟨511693, by decide⟩,⟨511714, by decide⟩,⟨511720, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72499_511721 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72499 ⟨511721, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72499
    ⟨511721, by decide⟩ (by decide) (![⟨511665, by decide⟩,⟨511693, by decide⟩,⟨511714, by decide⟩,⟨511720, by decide⟩]) unmarked_context_12_72499_511721 node_context_12_72499_511721
  intro a
  fin_cases a
  · exact context_13_289996_511665
  · exact context_13_289997_511693
  · exact context_13_289998_511714
  · exact context_13_289999_511720

theorem unmarked_context_11_18124_511722 : frontier 10 ⟨511722, by decide⟩
    (prefixCache 11 18124) (prefixPartial 11 18124) = false := by
  decide +kernel

theorem node_context_11_18124_511722 : EJMOriginalGlobalDAGData.nodes 10 ⟨511722, by decide⟩ =
    .split (coordinate 11) (![⟨445562, by decide⟩,⟨511580, by decide⟩,⟨511658, by decide⟩,⟨511721, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18124_511722 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18124 ⟨511722, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18124
    ⟨511722, by decide⟩ (by decide) (![⟨445562, by decide⟩,⟨511580, by decide⟩,⟨511658, by decide⟩,⟨511721, by decide⟩]) unmarked_context_11_18124_511722 node_context_11_18124_511722
  intro a
  fin_cases a
  · exact context_12_72496_445562
  · exact context_12_72497_511580
  · exact context_12_72498_511658
  · exact context_12_72499_511721

theorem selected_cut_19991 : selected 8 ⟨511732, by decide⟩
    (prefixPartial 13 290000) = some ⟨13, 2, 0, 511732, 290000, 509, 16384⟩ := by
  decide +kernel

theorem context_13_290000_511732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290000 ⟨511732, by decide⟩ :=
  accepted_of_selected 13 290000 ⟨511732, by decide⟩ ⟨13, 2, 0, 511732, 290000, 509, 16384⟩
    (by decide) selected_cut_19991

theorem selected_cut_19992 : selected 8 ⟨511792, by decide⟩
    (prefixPartial 13 290001) = some ⟨13, 2, 0, 511792, 290001, 3173, 16384⟩ := by
  decide +kernel

theorem context_13_290001_511792 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290001 ⟨511792, by decide⟩ :=
  accepted_of_selected 13 290001 ⟨511792, by decide⟩ ⟨13, 2, 0, 511792, 290001, 3173, 16384⟩
    (by decide) selected_cut_19992

theorem selected_cut_19993 : selected 8 ⟨511845, by decide⟩
    (prefixPartial 13 290002) = some ⟨13, 2, 0, 511845, 290002, 2413, 16384⟩ := by
  decide +kernel

theorem context_13_290002_511845 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290002 ⟨511845, by decide⟩ :=
  accepted_of_selected 13 290002 ⟨511845, by decide⟩ ⟨13, 2, 0, 511845, 290002, 2413, 16384⟩
    (by decide) selected_cut_19993

theorem selected_cut_19994 : selected 8 ⟨511898, by decide⟩
    (prefixPartial 13 290003) = some ⟨13, 2, 0, 511898, 290003, 1213, 16384⟩ := by
  decide +kernel

theorem context_13_290003_511898 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290003 ⟨511898, by decide⟩ :=
  accepted_of_selected 13 290003 ⟨511898, by decide⟩ ⟨13, 2, 0, 511898, 290003, 1213, 16384⟩
    (by decide) selected_cut_19994

theorem unmarked_context_12_72500_511899 : frontier 9 ⟨511899, by decide⟩
    (prefixCache 12 72500) (prefixPartial 12 72500) = false := by
  decide +kernel

theorem node_context_12_72500_511899 : EJMOriginalGlobalDAGData.nodes 9 ⟨511899, by decide⟩ =
    .split (coordinate 12) (![⟨511732, by decide⟩,⟨511792, by decide⟩,⟨511845, by decide⟩,⟨511898, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72500_511899 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72500 ⟨511899, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72500
    ⟨511899, by decide⟩ (by decide) (![⟨511732, by decide⟩,⟨511792, by decide⟩,⟨511845, by decide⟩,⟨511898, by decide⟩]) unmarked_context_12_72500_511899 node_context_12_72500_511899
  intro a
  fin_cases a
  · exact context_13_290000_511732
  · exact context_13_290001_511792
  · exact context_13_290002_511845
  · exact context_13_290003_511898

theorem selected_cut_19995 : selected 8 ⟨511905, by decide⟩
    (prefixPartial 13 290004) = some ⟨13, 2, 0, 511905, 290004, 369, 16384⟩ := by
  decide +kernel

theorem context_13_290004_511905 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290004 ⟨511905, by decide⟩ :=
  accepted_of_selected 13 290004 ⟨511905, by decide⟩ ⟨13, 2, 0, 511905, 290004, 369, 16384⟩
    (by decide) selected_cut_19995

theorem selected_cut_19996 : selected 8 ⟨511935, by decide⟩
    (prefixPartial 13 290005) = some ⟨13, 2, 0, 511935, 290005, 2233, 16384⟩ := by
  decide +kernel

theorem context_13_290005_511935 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290005 ⟨511935, by decide⟩ :=
  accepted_of_selected 13 290005 ⟨511935, by decide⟩ ⟨13, 2, 0, 511935, 290005, 2233, 16384⟩
    (by decide) selected_cut_19996

theorem selected_cut_19997 : selected 8 ⟨511955, by decide⟩
    (prefixPartial 13 290006) = some ⟨13, 2, 0, 511955, 290006, 1485, 16384⟩ := by
  decide +kernel

theorem context_13_290006_511955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290006 ⟨511955, by decide⟩ :=
  accepted_of_selected 13 290006 ⟨511955, by decide⟩ ⟨13, 2, 0, 511955, 290006, 1485, 16384⟩
    (by decide) selected_cut_19997

theorem selected_cut_19998 : selected 8 ⟨511961, by decide⟩
    (prefixPartial 13 290007) = some ⟨13, 2, 0, 511961, 290007, 893, 16384⟩ := by
  decide +kernel

theorem context_13_290007_511961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290007 ⟨511961, by decide⟩ :=
  accepted_of_selected 13 290007 ⟨511961, by decide⟩ ⟨13, 2, 0, 511961, 290007, 893, 16384⟩
    (by decide) selected_cut_19998

theorem unmarked_context_12_72501_511962 : frontier 9 ⟨511962, by decide⟩
    (prefixCache 12 72501) (prefixPartial 12 72501) = false := by
  decide +kernel

theorem node_context_12_72501_511962 : EJMOriginalGlobalDAGData.nodes 9 ⟨511962, by decide⟩ =
    .split (coordinate 12) (![⟨511905, by decide⟩,⟨511935, by decide⟩,⟨511955, by decide⟩,⟨511961, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72501_511962 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72501 ⟨511962, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72501
    ⟨511962, by decide⟩ (by decide) (![⟨511905, by decide⟩,⟨511935, by decide⟩,⟨511955, by decide⟩,⟨511961, by decide⟩]) unmarked_context_12_72501_511962 node_context_12_72501_511962
  intro a
  fin_cases a
  · exact context_13_290004_511905
  · exact context_13_290005_511935
  · exact context_13_290006_511955
  · exact context_13_290007_511961

theorem selected_cut_19999 : selected 8 ⟨511968, by decide⟩
    (prefixPartial 13 290008) = some ⟨13, 2, 0, 511968, 290008, 337, 16384⟩ := by
  decide +kernel

theorem context_13_290008_511968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290008 ⟨511968, by decide⟩ :=
  accepted_of_selected 13 290008 ⟨511968, by decide⟩ ⟨13, 2, 0, 511968, 290008, 337, 16384⟩
    (by decide) selected_cut_19999

theorem selected_cut_20000 : selected 8 ⟨512007, by decide⟩
    (prefixPartial 13 290009) = some ⟨13, 2, 0, 512007, 290009, 2445, 16384⟩ := by
  decide +kernel

theorem context_13_290009_512007 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290009 ⟨512007, by decide⟩ :=
  accepted_of_selected 13 290009 ⟨512007, by decide⟩ ⟨13, 2, 0, 512007, 290009, 2445, 16384⟩
    (by decide) selected_cut_20000

theorem selected_cut_20001 : selected 8 ⟨512035, by decide⟩
    (prefixPartial 13 290010) = some ⟨13, 2, 0, 512035, 290010, 2029, 16384⟩ := by
  decide +kernel

theorem context_13_290010_512035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290010 ⟨512035, by decide⟩ :=
  accepted_of_selected 13 290010 ⟨512035, by decide⟩ ⟨13, 2, 0, 512035, 290010, 2029, 16384⟩
    (by decide) selected_cut_20001

theorem selected_cut_20002 : selected 8 ⟨512050, by decide⟩
    (prefixPartial 13 290011) = some ⟨13, 2, 0, 512050, 290011, 941, 16384⟩ := by
  decide +kernel

theorem context_13_290011_512050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290011 ⟨512050, by decide⟩ :=
  accepted_of_selected 13 290011 ⟨512050, by decide⟩ ⟨13, 2, 0, 512050, 290011, 941, 16384⟩
    (by decide) selected_cut_20002

theorem unmarked_context_12_72502_512051 : frontier 9 ⟨512051, by decide⟩
    (prefixCache 12 72502) (prefixPartial 12 72502) = false := by
  decide +kernel

theorem node_context_12_72502_512051 : EJMOriginalGlobalDAGData.nodes 9 ⟨512051, by decide⟩ =
    .split (coordinate 12) (![⟨511968, by decide⟩,⟨512007, by decide⟩,⟨512035, by decide⟩,⟨512050, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72502_512051 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72502 ⟨512051, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72502
    ⟨512051, by decide⟩ (by decide) (![⟨511968, by decide⟩,⟨512007, by decide⟩,⟨512035, by decide⟩,⟨512050, by decide⟩]) unmarked_context_12_72502_512051 node_context_12_72502_512051
  intro a
  fin_cases a
  · exact context_13_290008_511968
  · exact context_13_290009_512007
  · exact context_13_290010_512035
  · exact context_13_290011_512050

theorem selected_cut_20003 : selected 8 ⟨512056, by decide⟩
    (prefixPartial 13 290012) = some ⟨13, 2, 0, 512056, 290012, 253, 16384⟩ := by
  decide +kernel

theorem context_13_290012_512056 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290012 ⟨512056, by decide⟩ :=
  accepted_of_selected 13 290012 ⟨512056, by decide⟩ ⟨13, 2, 0, 512056, 290012, 253, 16384⟩
    (by decide) selected_cut_20003

theorem selected_cut_20004 : selected 8 ⟨512087, by decide⟩
    (prefixPartial 13 290013) = some ⟨13, 2, 0, 512087, 290013, 2097, 16384⟩ := by
  decide +kernel

theorem context_13_290013_512087 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290013 ⟨512087, by decide⟩ :=
  accepted_of_selected 13 290013 ⟨512087, by decide⟩ ⟨13, 2, 0, 512087, 290013, 2097, 16384⟩
    (by decide) selected_cut_20004

theorem selected_cut_20005 : selected 8 ⟨512106, by decide⟩
    (prefixPartial 13 290014) = some ⟨13, 2, 0, 512106, 290014, 1697, 16384⟩ := by
  decide +kernel

theorem context_13_290014_512106 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290014 ⟨512106, by decide⟩ :=
  accepted_of_selected 13 290014 ⟨512106, by decide⟩ ⟨13, 2, 0, 512106, 290014, 1697, 16384⟩
    (by decide) selected_cut_20005

theorem selected_cut_20006 : selected 8 ⟨512112, by decide⟩
    (prefixPartial 13 290015) = some ⟨13, 2, 0, 512112, 290015, 805, 16384⟩ := by
  decide +kernel

theorem context_13_290015_512112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290015 ⟨512112, by decide⟩ :=
  accepted_of_selected 13 290015 ⟨512112, by decide⟩ ⟨13, 2, 0, 512112, 290015, 805, 16384⟩
    (by decide) selected_cut_20006

theorem unmarked_context_12_72503_512113 : frontier 9 ⟨512113, by decide⟩
    (prefixCache 12 72503) (prefixPartial 12 72503) = false := by
  decide +kernel

theorem node_context_12_72503_512113 : EJMOriginalGlobalDAGData.nodes 9 ⟨512113, by decide⟩ =
    .split (coordinate 12) (![⟨512056, by decide⟩,⟨512087, by decide⟩,⟨512106, by decide⟩,⟨512112, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72503_512113 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72503 ⟨512113, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72503
    ⟨512113, by decide⟩ (by decide) (![⟨512056, by decide⟩,⟨512087, by decide⟩,⟨512106, by decide⟩,⟨512112, by decide⟩]) unmarked_context_12_72503_512113 node_context_12_72503_512113
  intro a
  fin_cases a
  · exact context_13_290012_512056
  · exact context_13_290013_512087
  · exact context_13_290014_512106
  · exact context_13_290015_512112

theorem unmarked_context_11_18125_512114 : frontier 10 ⟨512114, by decide⟩
    (prefixCache 11 18125) (prefixPartial 11 18125) = false := by
  decide +kernel

theorem node_context_11_18125_512114 : EJMOriginalGlobalDAGData.nodes 10 ⟨512114, by decide⟩ =
    .split (coordinate 11) (![⟨511899, by decide⟩,⟨511962, by decide⟩,⟨512051, by decide⟩,⟨512113, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18125_512114 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18125 ⟨512114, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18125
    ⟨512114, by decide⟩ (by decide) (![⟨511899, by decide⟩,⟨511962, by decide⟩,⟨512051, by decide⟩,⟨512113, by decide⟩]) unmarked_context_11_18125_512114 node_context_11_18125_512114
  intro a
  fin_cases a
  · exact context_12_72500_511899
  · exact context_12_72501_511962
  · exact context_12_72502_512051
  · exact context_12_72503_512113

theorem selected_cut_20007 : selected 8 ⟨512120, by decide⟩
    (prefixPartial 13 290016) = some ⟨13, 2, 0, 512120, 290016, 325, 16384⟩ := by
  decide +kernel

theorem context_13_290016_512120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290016 ⟨512120, by decide⟩ :=
  accepted_of_selected 13 290016 ⟨512120, by decide⟩ ⟨13, 2, 0, 512120, 290016, 325, 16384⟩
    (by decide) selected_cut_20007

theorem selected_cut_20008 : selected 8 ⟨512170, by decide⟩
    (prefixPartial 13 290017) = some ⟨13, 2, 0, 512170, 290017, 3117, 16384⟩ := by
  decide +kernel

theorem context_13_290017_512170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290017 ⟨512170, by decide⟩ :=
  accepted_of_selected 13 290017 ⟨512170, by decide⟩ ⟨13, 2, 0, 512170, 290017, 3117, 16384⟩
    (by decide) selected_cut_20008

theorem selected_cut_20009 : selected 8 ⟨512214, by decide⟩
    (prefixPartial 13 290018) = some ⟨13, 2, 0, 512214, 290018, 2345, 16384⟩ := by
  decide +kernel

theorem context_13_290018_512214 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290018 ⟨512214, by decide⟩ :=
  accepted_of_selected 13 290018 ⟨512214, by decide⟩ ⟨13, 2, 0, 512214, 290018, 2345, 16384⟩
    (by decide) selected_cut_20009

theorem selected_cut_20010 : selected 8 ⟨512246, by decide⟩
    (prefixPartial 13 290019) = some ⟨13, 2, 0, 512246, 290019, 1217, 16384⟩ := by
  decide +kernel

theorem context_13_290019_512246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290019 ⟨512246, by decide⟩ :=
  accepted_of_selected 13 290019 ⟨512246, by decide⟩ ⟨13, 2, 0, 512246, 290019, 1217, 16384⟩
    (by decide) selected_cut_20010

theorem unmarked_context_12_72504_512247 : frontier 9 ⟨512247, by decide⟩
    (prefixCache 12 72504) (prefixPartial 12 72504) = false := by
  decide +kernel

theorem node_context_12_72504_512247 : EJMOriginalGlobalDAGData.nodes 9 ⟨512247, by decide⟩ =
    .split (coordinate 12) (![⟨512120, by decide⟩,⟨512170, by decide⟩,⟨512214, by decide⟩,⟨512246, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72504_512247 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72504 ⟨512247, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72504
    ⟨512247, by decide⟩ (by decide) (![⟨512120, by decide⟩,⟨512170, by decide⟩,⟨512214, by decide⟩,⟨512246, by decide⟩]) unmarked_context_12_72504_512247 node_context_12_72504_512247
  intro a
  fin_cases a
  · exact context_13_290016_512120
  · exact context_13_290017_512170
  · exact context_13_290018_512214
  · exact context_13_290019_512246

theorem selected_cut_20011 : selected 8 ⟨512251, by decide⟩
    (prefixPartial 13 290020) = some ⟨13, 2, 0, 512251, 290020, 193, 16384⟩ := by
  decide +kernel

theorem context_13_290020_512251 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290020 ⟨512251, by decide⟩ :=
  accepted_of_selected 13 290020 ⟨512251, by decide⟩ ⟨13, 2, 0, 512251, 290020, 193, 16384⟩
    (by decide) selected_cut_20011

theorem selected_cut_20012 : selected 8 ⟨512283, by decide⟩
    (prefixPartial 13 290021) = some ⟨13, 2, 0, 512283, 290021, 2265, 16384⟩ := by
  decide +kernel

theorem context_13_290021_512283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290021 ⟨512283, by decide⟩ :=
  accepted_of_selected 13 290021 ⟨512283, by decide⟩ ⟨13, 2, 0, 512283, 290021, 2265, 16384⟩
    (by decide) selected_cut_20012

theorem selected_cut_20013 : selected 8 ⟨512303, by decide⟩
    (prefixPartial 13 290022) = some ⟨13, 2, 0, 512303, 290022, 1593, 16384⟩ := by
  decide +kernel

theorem context_13_290022_512303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290022 ⟨512303, by decide⟩ :=
  accepted_of_selected 13 290022 ⟨512303, by decide⟩ ⟨13, 2, 0, 512303, 290022, 1593, 16384⟩
    (by decide) selected_cut_20013

theorem selected_cut_20014 : selected 8 ⟨512311, by decide⟩
    (prefixPartial 13 290023) = some ⟨13, 2, 0, 512311, 290023, 953, 16384⟩ := by
  decide +kernel

theorem context_13_290023_512311 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290023 ⟨512311, by decide⟩ :=
  accepted_of_selected 13 290023 ⟨512311, by decide⟩ ⟨13, 2, 0, 512311, 290023, 953, 16384⟩
    (by decide) selected_cut_20014

theorem unmarked_context_12_72505_512312 : frontier 9 ⟨512312, by decide⟩
    (prefixCache 12 72505) (prefixPartial 12 72505) = false := by
  decide +kernel

theorem node_context_12_72505_512312 : EJMOriginalGlobalDAGData.nodes 9 ⟨512312, by decide⟩ =
    .split (coordinate 12) (![⟨512251, by decide⟩,⟨512283, by decide⟩,⟨512303, by decide⟩,⟨512311, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72505_512312 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72505 ⟨512312, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72505
    ⟨512312, by decide⟩ (by decide) (![⟨512251, by decide⟩,⟨512283, by decide⟩,⟨512303, by decide⟩,⟨512311, by decide⟩]) unmarked_context_12_72505_512312 node_context_12_72505_512312
  intro a
  fin_cases a
  · exact context_13_290020_512251
  · exact context_13_290021_512283
  · exact context_13_290022_512303
  · exact context_13_290023_512311

theorem selected_cut_20015 : selected 8 ⟨512316, by decide⟩
    (prefixPartial 13 290024) = some ⟨13, 2, 0, 512316, 290024, 181, 16384⟩ := by
  decide +kernel

theorem context_13_290024_512316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290024 ⟨512316, by decide⟩ :=
  accepted_of_selected 13 290024 ⟨512316, by decide⟩ ⟨13, 2, 0, 512316, 290024, 181, 16384⟩
    (by decide) selected_cut_20015

theorem selected_cut_20016 : selected 8 ⟨512343, by decide⟩
    (prefixPartial 13 290025) = some ⟨13, 2, 0, 512343, 290025, 2529, 16384⟩ := by
  decide +kernel

theorem context_13_290025_512343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290025 ⟨512343, by decide⟩ :=
  accepted_of_selected 13 290025 ⟨512343, by decide⟩ ⟨13, 2, 0, 512343, 290025, 2529, 16384⟩
    (by decide) selected_cut_20016

theorem selected_cut_20017 : selected 8 ⟨512366, by decide⟩
    (prefixPartial 13 290026) = some ⟨13, 2, 0, 512366, 290026, 2005, 16384⟩ := by
  decide +kernel

theorem context_13_290026_512366 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290026 ⟨512366, by decide⟩ :=
  accepted_of_selected 13 290026 ⟨512366, by decide⟩ ⟨13, 2, 0, 512366, 290026, 2005, 16384⟩
    (by decide) selected_cut_20017

theorem selected_cut_20018 : selected 8 ⟨512374, by decide⟩
    (prefixPartial 13 290027) = some ⟨13, 2, 0, 512374, 290027, 957, 16384⟩ := by
  decide +kernel

theorem context_13_290027_512374 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290027 ⟨512374, by decide⟩ :=
  accepted_of_selected 13 290027 ⟨512374, by decide⟩ ⟨13, 2, 0, 512374, 290027, 957, 16384⟩
    (by decide) selected_cut_20018

theorem unmarked_context_12_72506_512375 : frontier 9 ⟨512375, by decide⟩
    (prefixCache 12 72506) (prefixPartial 12 72506) = false := by
  decide +kernel

theorem node_context_12_72506_512375 : EJMOriginalGlobalDAGData.nodes 9 ⟨512375, by decide⟩ =
    .split (coordinate 12) (![⟨512316, by decide⟩,⟨512343, by decide⟩,⟨512366, by decide⟩,⟨512374, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72506_512375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72506 ⟨512375, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72506
    ⟨512375, by decide⟩ (by decide) (![⟨512316, by decide⟩,⟨512343, by decide⟩,⟨512366, by decide⟩,⟨512374, by decide⟩]) unmarked_context_12_72506_512375 node_context_12_72506_512375
  intro a
  fin_cases a
  · exact context_13_290024_512316
  · exact context_13_290025_512343
  · exact context_13_290026_512366
  · exact context_13_290027_512374

theorem selected_cut_20019 : selected 8 ⟨512378, by decide⟩
    (prefixPartial 13 290028) = some ⟨13, 2, 0, 512378, 290028, 121, 16384⟩ := by
  decide +kernel

theorem context_13_290028_512378 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290028 ⟨512378, by decide⟩ :=
  accepted_of_selected 13 290028 ⟨512378, by decide⟩ ⟨13, 2, 0, 512378, 290028, 121, 16384⟩
    (by decide) selected_cut_20019

theorem selected_cut_20020 : selected 8 ⟨512410, by decide⟩
    (prefixPartial 13 290029) = some ⟨13, 2, 0, 512410, 290029, 2229, 16384⟩ := by
  decide +kernel

theorem context_13_290029_512410 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290029 ⟨512410, by decide⟩ :=
  accepted_of_selected 13 290029 ⟨512410, by decide⟩ ⟨13, 2, 0, 512410, 290029, 2229, 16384⟩
    (by decide) selected_cut_20020

theorem selected_cut_20021 : selected 8 ⟨512431, by decide⟩
    (prefixPartial 13 290030) = some ⟨13, 2, 0, 512431, 290030, 1697, 16384⟩ := by
  decide +kernel

theorem context_13_290030_512431 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290030 ⟨512431, by decide⟩ :=
  accepted_of_selected 13 290030 ⟨512431, by decide⟩ ⟨13, 2, 0, 512431, 290030, 1697, 16384⟩
    (by decide) selected_cut_20021

theorem selected_cut_20022 : selected 8 ⟨512438, by decide⟩
    (prefixPartial 13 290031) = some ⟨13, 2, 0, 512438, 290031, 921, 16384⟩ := by
  decide +kernel

theorem context_13_290031_512438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290031 ⟨512438, by decide⟩ :=
  accepted_of_selected 13 290031 ⟨512438, by decide⟩ ⟨13, 2, 0, 512438, 290031, 921, 16384⟩
    (by decide) selected_cut_20022

theorem unmarked_context_12_72507_512439 : frontier 9 ⟨512439, by decide⟩
    (prefixCache 12 72507) (prefixPartial 12 72507) = false := by
  decide +kernel

theorem node_context_12_72507_512439 : EJMOriginalGlobalDAGData.nodes 9 ⟨512439, by decide⟩ =
    .split (coordinate 12) (![⟨512378, by decide⟩,⟨512410, by decide⟩,⟨512431, by decide⟩,⟨512438, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72507_512439 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72507 ⟨512439, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72507
    ⟨512439, by decide⟩ (by decide) (![⟨512378, by decide⟩,⟨512410, by decide⟩,⟨512431, by decide⟩,⟨512438, by decide⟩]) unmarked_context_12_72507_512439 node_context_12_72507_512439
  intro a
  fin_cases a
  · exact context_13_290028_512378
  · exact context_13_290029_512410
  · exact context_13_290030_512431
  · exact context_13_290031_512438

theorem unmarked_context_11_18126_512440 : frontier 10 ⟨512440, by decide⟩
    (prefixCache 11 18126) (prefixPartial 11 18126) = false := by
  decide +kernel

theorem node_context_11_18126_512440 : EJMOriginalGlobalDAGData.nodes 10 ⟨512440, by decide⟩ =
    .split (coordinate 11) (![⟨512247, by decide⟩,⟨512312, by decide⟩,⟨512375, by decide⟩,⟨512439, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18126_512440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18126 ⟨512440, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18126
    ⟨512440, by decide⟩ (by decide) (![⟨512247, by decide⟩,⟨512312, by decide⟩,⟨512375, by decide⟩,⟨512439, by decide⟩]) unmarked_context_11_18126_512440 node_context_11_18126_512440
  intro a
  fin_cases a
  · exact context_12_72504_512247
  · exact context_12_72505_512312
  · exact context_12_72506_512375
  · exact context_12_72507_512439

theorem selected_cut_20023 : selected 9 ⟨475533, by decide⟩
    (prefixPartial 12 72508) = some ⟨12, 1, 0, 475533, 72508, 1, 65536⟩ := by
  decide +kernel

theorem context_12_72508_475533 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72508 ⟨475533, by decide⟩ :=
  accepted_of_selected 12 72508 ⟨475533, by decide⟩ ⟨12, 1, 0, 475533, 72508, 1, 65536⟩
    (by decide) selected_cut_20023

theorem selected_cut_20024 : selected 8 ⟨512444, by decide⟩
    (prefixPartial 13 290036) = some ⟨13, 2, 0, 512444, 290036, 81, 16384⟩ := by
  decide +kernel

theorem context_13_290036_512444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290036 ⟨512444, by decide⟩ :=
  accepted_of_selected 13 290036 ⟨512444, by decide⟩ ⟨13, 2, 0, 512444, 290036, 81, 16384⟩
    (by decide) selected_cut_20024

theorem selected_cut_20025 : selected 8 ⟨512472, by decide⟩
    (prefixPartial 13 290037) = some ⟨13, 2, 0, 512472, 290037, 2077, 16384⟩ := by
  decide +kernel

theorem context_13_290037_512472 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290037 ⟨512472, by decide⟩ :=
  accepted_of_selected 13 290037 ⟨512472, by decide⟩ ⟨13, 2, 0, 512472, 290037, 2077, 16384⟩
    (by decide) selected_cut_20025

theorem selected_cut_20026 : selected 8 ⟨512491, by decide⟩
    (prefixPartial 13 290038) = some ⟨13, 2, 0, 512491, 290038, 1701, 16384⟩ := by
  decide +kernel

theorem context_13_290038_512491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290038 ⟨512491, by decide⟩ :=
  accepted_of_selected 13 290038 ⟨512491, by decide⟩ ⟨13, 2, 0, 512491, 290038, 1701, 16384⟩
    (by decide) selected_cut_20026

theorem selected_cut_20027 : selected 8 ⟨512496, by decide⟩
    (prefixPartial 13 290039) = some ⟨13, 2, 0, 512496, 290039, 905, 16384⟩ := by
  decide +kernel

theorem context_13_290039_512496 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290039 ⟨512496, by decide⟩ :=
  accepted_of_selected 13 290039 ⟨512496, by decide⟩ ⟨13, 2, 0, 512496, 290039, 905, 16384⟩
    (by decide) selected_cut_20027

theorem unmarked_context_12_72509_512497 : frontier 9 ⟨512497, by decide⟩
    (prefixCache 12 72509) (prefixPartial 12 72509) = false := by
  decide +kernel

theorem node_context_12_72509_512497 : EJMOriginalGlobalDAGData.nodes 9 ⟨512497, by decide⟩ =
    .split (coordinate 12) (![⟨512444, by decide⟩,⟨512472, by decide⟩,⟨512491, by decide⟩,⟨512496, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72509_512497 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72509 ⟨512497, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72509
    ⟨512497, by decide⟩ (by decide) (![⟨512444, by decide⟩,⟨512472, by decide⟩,⟨512491, by decide⟩,⟨512496, by decide⟩]) unmarked_context_12_72509_512497 node_context_12_72509_512497
  intro a
  fin_cases a
  · exact context_13_290036_512444
  · exact context_13_290037_512472
  · exact context_13_290038_512491
  · exact context_13_290039_512496

theorem selected_cut_20028 : selected 8 ⟨512500, by decide⟩
    (prefixPartial 13 290040) = some ⟨13, 2, 0, 512500, 290040, 49, 16384⟩ := by
  decide +kernel

theorem context_13_290040_512500 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290040 ⟨512500, by decide⟩ :=
  accepted_of_selected 13 290040 ⟨512500, by decide⟩ ⟨13, 2, 0, 512500, 290040, 49, 16384⟩
    (by decide) selected_cut_20028

theorem selected_cut_20029 : selected 8 ⟨512531, by decide⟩
    (prefixPartial 13 290041) = some ⟨13, 2, 0, 512531, 290041, 2549, 16384⟩ := by
  decide +kernel

theorem context_13_290041_512531 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290041 ⟨512531, by decide⟩ :=
  accepted_of_selected 13 290041 ⟨512531, by decide⟩ ⟨13, 2, 0, 512531, 290041, 2549, 16384⟩
    (by decide) selected_cut_20029

theorem selected_cut_20030 : selected 8 ⟨512549, by decide⟩
    (prefixPartial 13 290042) = some ⟨13, 2, 0, 512549, 290042, 1945, 16384⟩ := by
  decide +kernel

theorem context_13_290042_512549 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290042 ⟨512549, by decide⟩ :=
  accepted_of_selected 13 290042 ⟨512549, by decide⟩ ⟨13, 2, 0, 512549, 290042, 1945, 16384⟩
    (by decide) selected_cut_20030

theorem selected_cut_20031 : selected 8 ⟨512554, by decide⟩
    (prefixPartial 13 290043) = some ⟨13, 2, 0, 512554, 290043, 909, 16384⟩ := by
  decide +kernel

theorem context_13_290043_512554 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290043 ⟨512554, by decide⟩ :=
  accepted_of_selected 13 290043 ⟨512554, by decide⟩ ⟨13, 2, 0, 512554, 290043, 909, 16384⟩
    (by decide) selected_cut_20031

theorem unmarked_context_12_72510_512555 : frontier 9 ⟨512555, by decide⟩
    (prefixCache 12 72510) (prefixPartial 12 72510) = false := by
  decide +kernel

theorem node_context_12_72510_512555 : EJMOriginalGlobalDAGData.nodes 9 ⟨512555, by decide⟩ =
    .split (coordinate 12) (![⟨512500, by decide⟩,⟨512531, by decide⟩,⟨512549, by decide⟩,⟨512554, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72510_512555 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72510 ⟨512555, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72510
    ⟨512555, by decide⟩ (by decide) (![⟨512500, by decide⟩,⟨512531, by decide⟩,⟨512549, by decide⟩,⟨512554, by decide⟩]) unmarked_context_12_72510_512555 node_context_12_72510_512555
  intro a
  fin_cases a
  · exact context_13_290040_512500
  · exact context_13_290041_512531
  · exact context_13_290042_512549
  · exact context_13_290043_512554

theorem selected_cut_20032 : selected 9 ⟨512556, by decide⟩
    (prefixPartial 12 72511) = some ⟨12, 1, 0, 512556, 72511, 1, 65536⟩ := by
  decide +kernel

theorem context_12_72511_512556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72511 ⟨512556, by decide⟩ :=
  accepted_of_selected 12 72511 ⟨512556, by decide⟩ ⟨12, 1, 0, 512556, 72511, 1, 65536⟩
    (by decide) selected_cut_20032

theorem unmarked_context_11_18127_512557 : frontier 10 ⟨512557, by decide⟩
    (prefixCache 11 18127) (prefixPartial 11 18127) = false := by
  decide +kernel

theorem node_context_11_18127_512557 : EJMOriginalGlobalDAGData.nodes 10 ⟨512557, by decide⟩ =
    .split (coordinate 11) (![⟨475533, by decide⟩,⟨512497, by decide⟩,⟨512555, by decide⟩,⟨512556, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18127_512557 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18127 ⟨512557, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18127
    ⟨512557, by decide⟩ (by decide) (![⟨475533, by decide⟩,⟨512497, by decide⟩,⟨512555, by decide⟩,⟨512556, by decide⟩]) unmarked_context_11_18127_512557 node_context_11_18127_512557
  intro a
  fin_cases a
  · exact context_12_72508_475533
  · exact context_12_72509_512497
  · exact context_12_72510_512555
  · exact context_12_72511_512556

theorem unmarked_context_10_4531_512558 : frontier 11 ⟨512558, by decide⟩
    (prefixCache 10 4531) (prefixPartial 10 4531) = false := by
  decide +kernel

theorem node_context_10_4531_512558 : EJMOriginalGlobalDAGData.nodes 11 ⟨512558, by decide⟩ =
    .split (coordinate 10) (![⟨511722, by decide⟩,⟨512114, by decide⟩,⟨512440, by decide⟩,⟨512557, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4531_512558 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4531 ⟨512558, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4531
    ⟨512558, by decide⟩ (by decide) (![⟨511722, by decide⟩,⟨512114, by decide⟩,⟨512440, by decide⟩,⟨512557, by decide⟩]) unmarked_context_10_4531_512558 node_context_10_4531_512558
  intro a
  fin_cases a
  · exact context_11_18124_511722
  · exact context_11_18125_512114
  · exact context_11_18126_512440
  · exact context_11_18127_512557

theorem unmarked_context_9_1132_512559 : frontier 12 ⟨512559, by decide⟩
    (prefixCache 9 1132) (prefixPartial 9 1132) = false := by
  decide +kernel

theorem node_context_9_1132_512559 : EJMOriginalGlobalDAGData.nodes 12 ⟨512559, by decide⟩ =
    .split (coordinate 9) (![⟨508417, by decide⟩,⟨510231, by decide⟩,⟨511502, by decide⟩,⟨512558, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1132_512559 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1132 ⟨512559, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1132
    ⟨512559, by decide⟩ (by decide) (![⟨508417, by decide⟩,⟨510231, by decide⟩,⟨511502, by decide⟩,⟨512558, by decide⟩]) unmarked_context_9_1132_512559 node_context_9_1132_512559
  intro a
  fin_cases a
  · exact context_10_4528_508417
  · exact context_10_4529_510231
  · exact context_10_4530_511502
  · exact context_10_4531_512558

theorem selected_cut_20033 : selected 9 ⟨512608, by decide⟩
    (prefixPartial 12 72512) = some ⟨12, 2, 0, 512608, 72512, 3657, 65536⟩ := by
  decide +kernel

theorem context_12_72512_512608 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72512 ⟨512608, by decide⟩ :=
  accepted_of_selected 12 72512 ⟨512608, by decide⟩ ⟨12, 2, 0, 512608, 72512, 3657, 65536⟩
    (by decide) selected_cut_20033

theorem selected_cut_20034 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 290052) = some ⟨13, 1, 0, 3444, 290052, 1, 16384⟩ := by
  decide +kernel

theorem context_13_290052_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290052 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 290052 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 290052, 1, 16384⟩
    (by decide) selected_cut_20034

theorem selected_cut_20035 : selected 8 ⟨512637, by decide⟩
    (prefixPartial 13 290053) = some ⟨13, 2, 0, 512637, 290053, 2213, 16384⟩ := by
  decide +kernel

theorem context_13_290053_512637 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290053 ⟨512637, by decide⟩ :=
  accepted_of_selected 13 290053 ⟨512637, by decide⟩ ⟨13, 2, 0, 512637, 290053, 2213, 16384⟩
    (by decide) selected_cut_20035

theorem selected_cut_20036 : selected 8 ⟨512652, by decide⟩
    (prefixPartial 13 290054) = some ⟨13, 2, 0, 512652, 290054, 1193, 16384⟩ := by
  decide +kernel

theorem context_13_290054_512652 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290054 ⟨512652, by decide⟩ :=
  accepted_of_selected 13 290054 ⟨512652, by decide⟩ ⟨13, 2, 0, 512652, 290054, 1193, 16384⟩
    (by decide) selected_cut_20036

theorem selected_cut_20037 : selected 8 ⟨512659, by decide⟩
    (prefixPartial 13 290055) = some ⟨13, 2, 0, 512659, 290055, 717, 16384⟩ := by
  decide +kernel

theorem context_13_290055_512659 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290055 ⟨512659, by decide⟩ :=
  accepted_of_selected 13 290055 ⟨512659, by decide⟩ ⟨13, 2, 0, 512659, 290055, 717, 16384⟩
    (by decide) selected_cut_20037

theorem unmarked_context_12_72513_512660 : frontier 9 ⟨512660, by decide⟩
    (prefixCache 12 72513) (prefixPartial 12 72513) = false := by
  decide +kernel

theorem node_context_12_72513_512660 : EJMOriginalGlobalDAGData.nodes 9 ⟨512660, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨512637, by decide⟩,⟨512652, by decide⟩,⟨512659, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72513_512660 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72513 ⟨512660, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72513
    ⟨512660, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨512637, by decide⟩,⟨512652, by decide⟩,⟨512659, by decide⟩]) unmarked_context_12_72513_512660 node_context_12_72513_512660
  intro a
  fin_cases a
  · exact context_13_290052_3444
  · exact context_13_290053_512637
  · exact context_13_290054_512652
  · exact context_13_290055_512659

theorem selected_cut_20038 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 290056) = some ⟨13, 1, 0, 3444, 290056, 1, 16384⟩ := by
  decide +kernel

theorem context_13_290056_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290056 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 290056 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 290056, 1, 16384⟩
    (by decide) selected_cut_20038

theorem selected_cut_20039 : selected 8 ⟨512702, by decide⟩
    (prefixPartial 13 290057) = some ⟨13, 2, 0, 512702, 290057, 2641, 16384⟩ := by
  decide +kernel

theorem context_13_290057_512702 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290057 ⟨512702, by decide⟩ :=
  accepted_of_selected 13 290057 ⟨512702, by decide⟩ ⟨13, 2, 0, 512702, 290057, 2641, 16384⟩
    (by decide) selected_cut_20039

theorem selected_cut_20040 : selected 8 ⟨512726, by decide⟩
    (prefixPartial 13 290058) = some ⟨13, 2, 0, 512726, 290058, 1597, 16384⟩ := by
  decide +kernel

theorem context_13_290058_512726 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290058 ⟨512726, by decide⟩ :=
  accepted_of_selected 13 290058 ⟨512726, by decide⟩ ⟨13, 2, 0, 512726, 290058, 1597, 16384⟩
    (by decide) selected_cut_20040

theorem selected_cut_20041 : selected 8 ⟨512731, by decide⟩
    (prefixPartial 13 290059) = some ⟨13, 2, 0, 512731, 290059, 681, 16384⟩ := by
  decide +kernel

theorem context_13_290059_512731 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290059 ⟨512731, by decide⟩ :=
  accepted_of_selected 13 290059 ⟨512731, by decide⟩ ⟨13, 2, 0, 512731, 290059, 681, 16384⟩
    (by decide) selected_cut_20041

theorem unmarked_context_12_72514_512732 : frontier 9 ⟨512732, by decide⟩
    (prefixCache 12 72514) (prefixPartial 12 72514) = false := by
  decide +kernel

theorem node_context_12_72514_512732 : EJMOriginalGlobalDAGData.nodes 9 ⟨512732, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨512702, by decide⟩,⟨512726, by decide⟩,⟨512731, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72514_512732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72514 ⟨512732, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72514
    ⟨512732, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨512702, by decide⟩,⟨512726, by decide⟩,⟨512731, by decide⟩]) unmarked_context_12_72514_512732 node_context_12_72514_512732
  intro a
  fin_cases a
  · exact context_13_290056_3444
  · exact context_13_290057_512702
  · exact context_13_290058_512726
  · exact context_13_290059_512731

theorem selected_cut_20042 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 290060) = some ⟨13, 1, 0, 3444, 290060, 1, 16384⟩ := by
  decide +kernel

theorem context_13_290060_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290060 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 290060 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 290060, 1, 16384⟩
    (by decide) selected_cut_20042

theorem selected_cut_20043 : selected 8 ⟨512768, by decide⟩
    (prefixPartial 13 290061) = some ⟨13, 2, 0, 512768, 290061, 2461, 16384⟩ := by
  decide +kernel

theorem context_13_290061_512768 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290061 ⟨512768, by decide⟩ :=
  accepted_of_selected 13 290061 ⟨512768, by decide⟩ ⟨13, 2, 0, 512768, 290061, 2461, 16384⟩
    (by decide) selected_cut_20043

theorem selected_cut_20044 : selected 8 ⟨512789, by decide⟩
    (prefixPartial 13 290062) = some ⟨13, 2, 0, 512789, 290062, 1473, 16384⟩ := by
  decide +kernel

theorem context_13_290062_512789 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290062 ⟨512789, by decide⟩ :=
  accepted_of_selected 13 290062 ⟨512789, by decide⟩ ⟨13, 2, 0, 512789, 290062, 1473, 16384⟩
    (by decide) selected_cut_20044

theorem selected_cut_20045 : selected 8 ⟨512798, by decide⟩
    (prefixPartial 13 290063) = some ⟨13, 2, 0, 512798, 290063, 669, 16384⟩ := by
  decide +kernel

theorem context_13_290063_512798 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290063 ⟨512798, by decide⟩ :=
  accepted_of_selected 13 290063 ⟨512798, by decide⟩ ⟨13, 2, 0, 512798, 290063, 669, 16384⟩
    (by decide) selected_cut_20045

theorem unmarked_context_12_72515_512799 : frontier 9 ⟨512799, by decide⟩
    (prefixCache 12 72515) (prefixPartial 12 72515) = false := by
  decide +kernel

theorem node_context_12_72515_512799 : EJMOriginalGlobalDAGData.nodes 9 ⟨512799, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨512768, by decide⟩,⟨512789, by decide⟩,⟨512798, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72515_512799 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72515 ⟨512799, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72515
    ⟨512799, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨512768, by decide⟩,⟨512789, by decide⟩,⟨512798, by decide⟩]) unmarked_context_12_72515_512799 node_context_12_72515_512799
  intro a
  fin_cases a
  · exact context_13_290060_3444
  · exact context_13_290061_512768
  · exact context_13_290062_512789
  · exact context_13_290063_512798

theorem unmarked_context_11_18128_512800 : frontier 10 ⟨512800, by decide⟩
    (prefixCache 11 18128) (prefixPartial 11 18128) = false := by
  decide +kernel

theorem node_context_11_18128_512800 : EJMOriginalGlobalDAGData.nodes 10 ⟨512800, by decide⟩ =
    .split (coordinate 11) (![⟨512608, by decide⟩,⟨512660, by decide⟩,⟨512732, by decide⟩,⟨512799, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18128_512800 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18128 ⟨512800, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18128
    ⟨512800, by decide⟩ (by decide) (![⟨512608, by decide⟩,⟨512660, by decide⟩,⟨512732, by decide⟩,⟨512799, by decide⟩]) unmarked_context_11_18128_512800 node_context_11_18128_512800
  intro a
  fin_cases a
  · exact context_12_72512_512608
  · exact context_12_72513_512660
  · exact context_12_72514_512732
  · exact context_12_72515_512799

theorem selected_cut_20046 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 290064) = some ⟨13, 1, 0, 3444, 290064, 1, 16384⟩ := by
  decide +kernel

theorem context_13_290064_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290064 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 290064 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 290064, 1, 16384⟩
    (by decide) selected_cut_20046

theorem selected_cut_20047 : selected 8 ⟨512834, by decide⟩
    (prefixPartial 13 290065) = some ⟨13, 2, 0, 512834, 290065, 2233, 16384⟩ := by
  decide +kernel

theorem context_13_290065_512834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290065 ⟨512834, by decide⟩ :=
  accepted_of_selected 13 290065 ⟨512834, by decide⟩ ⟨13, 2, 0, 512834, 290065, 2233, 16384⟩
    (by decide) selected_cut_20047

theorem selected_cut_20048 : selected 8 ⟨512853, by decide⟩
    (prefixPartial 13 290066) = some ⟨13, 2, 0, 512853, 290066, 1377, 16384⟩ := by
  decide +kernel

theorem context_13_290066_512853 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290066 ⟨512853, by decide⟩ :=
  accepted_of_selected 13 290066 ⟨512853, by decide⟩ ⟨13, 2, 0, 512853, 290066, 1377, 16384⟩
    (by decide) selected_cut_20048

theorem selected_cut_20049 : selected 8 ⟨512864, by decide⟩
    (prefixPartial 13 290067) = some ⟨13, 2, 0, 512864, 290067, 837, 16384⟩ := by
  decide +kernel

theorem context_13_290067_512864 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290067 ⟨512864, by decide⟩ :=
  accepted_of_selected 13 290067 ⟨512864, by decide⟩ ⟨13, 2, 0, 512864, 290067, 837, 16384⟩
    (by decide) selected_cut_20049

theorem unmarked_context_12_72516_512865 : frontier 9 ⟨512865, by decide⟩
    (prefixCache 12 72516) (prefixPartial 12 72516) = false := by
  decide +kernel

theorem node_context_12_72516_512865 : EJMOriginalGlobalDAGData.nodes 9 ⟨512865, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨512834, by decide⟩,⟨512853, by decide⟩,⟨512864, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72516_512865 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72516 ⟨512865, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72516
    ⟨512865, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨512834, by decide⟩,⟨512853, by decide⟩,⟨512864, by decide⟩]) unmarked_context_12_72516_512865 node_context_12_72516_512865
  intro a
  fin_cases a
  · exact context_13_290064_3444
  · exact context_13_290065_512834
  · exact context_13_290066_512853
  · exact context_13_290067_512864

theorem selected_cut_20050 : selected 9 ⟨512915, by decide⟩
    (prefixPartial 12 72517) = some ⟨12, 2, 0, 512915, 72517, 3969, 65536⟩ := by
  decide +kernel

theorem context_12_72517_512915 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72517 ⟨512915, by decide⟩ :=
  accepted_of_selected 12 72517 ⟨512915, by decide⟩ ⟨12, 2, 0, 512915, 72517, 3969, 65536⟩
    (by decide) selected_cut_20050

theorem selected_cut_20051 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 290072) = some ⟨13, 1, 0, 3444, 290072, 1, 16384⟩ := by
  decide +kernel

theorem context_13_290072_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290072 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 290072 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 290072, 1, 16384⟩
    (by decide) selected_cut_20051

theorem selected_cut_20052 : selected 8 ⟨512954, by decide⟩
    (prefixPartial 13 290073) = some ⟨13, 2, 0, 512954, 290073, 2385, 16384⟩ := by
  decide +kernel

theorem context_13_290073_512954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290073 ⟨512954, by decide⟩ :=
  accepted_of_selected 13 290073 ⟨512954, by decide⟩ ⟨13, 2, 0, 512954, 290073, 2385, 16384⟩
    (by decide) selected_cut_20052

theorem selected_cut_20053 : selected 8 ⟨512983, by decide⟩
    (prefixPartial 13 290074) = some ⟨13, 2, 0, 512983, 290074, 1845, 16384⟩ := by
  decide +kernel

theorem context_13_290074_512983 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290074 ⟨512983, by decide⟩ :=
  accepted_of_selected 13 290074 ⟨512983, by decide⟩ ⟨13, 2, 0, 512983, 290074, 1845, 16384⟩
    (by decide) selected_cut_20053

theorem selected_cut_20054 : selected 8 ⟨512990, by decide⟩
    (prefixPartial 13 290075) = some ⟨13, 2, 0, 512990, 290075, 797, 16384⟩ := by
  decide +kernel

theorem context_13_290075_512990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290075 ⟨512990, by decide⟩ :=
  accepted_of_selected 13 290075 ⟨512990, by decide⟩ ⟨13, 2, 0, 512990, 290075, 797, 16384⟩
    (by decide) selected_cut_20054

theorem unmarked_context_12_72518_512991 : frontier 9 ⟨512991, by decide⟩
    (prefixCache 12 72518) (prefixPartial 12 72518) = false := by
  decide +kernel

theorem node_context_12_72518_512991 : EJMOriginalGlobalDAGData.nodes 9 ⟨512991, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨512954, by decide⟩,⟨512983, by decide⟩,⟨512990, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72518_512991 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72518 ⟨512991, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72518
    ⟨512991, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨512954, by decide⟩,⟨512983, by decide⟩,⟨512990, by decide⟩]) unmarked_context_12_72518_512991 node_context_12_72518_512991
  intro a
  fin_cases a
  · exact context_13_290072_3444
  · exact context_13_290073_512954
  · exact context_13_290074_512983
  · exact context_13_290075_512990

theorem selected_cut_20055 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 290076) = some ⟨13, 1, 0, 3444, 290076, 1, 16384⟩ := by
  decide +kernel

theorem context_13_290076_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290076 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 290076 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 290076, 1, 16384⟩
    (by decide) selected_cut_20055

theorem selected_cut_20056 : selected 8 ⟨513025, by decide⟩
    (prefixPartial 13 290077) = some ⟨13, 2, 0, 513025, 290077, 2285, 16384⟩ := by
  decide +kernel

theorem context_13_290077_513025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290077 ⟨513025, by decide⟩ :=
  accepted_of_selected 13 290077 ⟨513025, by decide⟩ ⟨13, 2, 0, 513025, 290077, 2285, 16384⟩
    (by decide) selected_cut_20056

theorem selected_cut_20057 : selected 8 ⟨513054, by decide⟩
    (prefixPartial 13 290078) = some ⟨13, 2, 0, 513054, 290078, 1717, 16384⟩ := by
  decide +kernel

theorem context_13_290078_513054 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290078 ⟨513054, by decide⟩ :=
  accepted_of_selected 13 290078 ⟨513054, by decide⟩ ⟨13, 2, 0, 513054, 290078, 1717, 16384⟩
    (by decide) selected_cut_20057

theorem selected_cut_20058 : selected 8 ⟨513060, by decide⟩
    (prefixPartial 13 290079) = some ⟨13, 2, 0, 513060, 290079, 833, 16384⟩ := by
  decide +kernel

theorem context_13_290079_513060 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290079 ⟨513060, by decide⟩ :=
  accepted_of_selected 13 290079 ⟨513060, by decide⟩ ⟨13, 2, 0, 513060, 290079, 833, 16384⟩
    (by decide) selected_cut_20058

theorem unmarked_context_12_72519_513061 : frontier 9 ⟨513061, by decide⟩
    (prefixCache 12 72519) (prefixPartial 12 72519) = false := by
  decide +kernel

theorem node_context_12_72519_513061 : EJMOriginalGlobalDAGData.nodes 9 ⟨513061, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨513025, by decide⟩,⟨513054, by decide⟩,⟨513060, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72519_513061 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72519 ⟨513061, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72519
    ⟨513061, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨513025, by decide⟩,⟨513054, by decide⟩,⟨513060, by decide⟩]) unmarked_context_12_72519_513061 node_context_12_72519_513061
  intro a
  fin_cases a
  · exact context_13_290076_3444
  · exact context_13_290077_513025
  · exact context_13_290078_513054
  · exact context_13_290079_513060

theorem unmarked_context_11_18129_513062 : frontier 10 ⟨513062, by decide⟩
    (prefixCache 11 18129) (prefixPartial 11 18129) = false := by
  decide +kernel

theorem node_context_11_18129_513062 : EJMOriginalGlobalDAGData.nodes 10 ⟨513062, by decide⟩ =
    .split (coordinate 11) (![⟨512865, by decide⟩,⟨512915, by decide⟩,⟨512991, by decide⟩,⟨513061, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18129_513062 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18129 ⟨513062, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18129
    ⟨513062, by decide⟩ (by decide) (![⟨512865, by decide⟩,⟨512915, by decide⟩,⟨512991, by decide⟩,⟨513061, by decide⟩]) unmarked_context_11_18129_513062 node_context_11_18129_513062
  intro a
  fin_cases a
  · exact context_12_72516_512865
  · exact context_12_72517_512915
  · exact context_12_72518_512991
  · exact context_12_72519_513061

theorem selected_cut_20059 : selected 9 ⟨513110, by decide⟩
    (prefixPartial 12 72520) = some ⟨12, 2, 0, 513110, 72520, 3977, 65536⟩ := by
  decide +kernel

theorem context_12_72520_513110 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72520 ⟨513110, by decide⟩ :=
  accepted_of_selected 12 72520 ⟨513110, by decide⟩ ⟨12, 2, 0, 513110, 72520, 3977, 65536⟩
    (by decide) selected_cut_20059

theorem selected_cut_20060 : selected 9 ⟨513156, by decide⟩
    (prefixPartial 12 72521) = some ⟨12, 2, 0, 513156, 72521, 3849, 65536⟩ := by
  decide +kernel

theorem context_12_72521_513156 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72521 ⟨513156, by decide⟩ :=
  accepted_of_selected 12 72521 ⟨513156, by decide⟩ ⟨12, 2, 0, 513156, 72521, 3849, 65536⟩
    (by decide) selected_cut_20060

theorem selected_cut_20061 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 290088) = some ⟨13, 1, 0, 3444, 290088, 1, 16384⟩ := by
  decide +kernel

theorem context_13_290088_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290088 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 290088 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 290088, 1, 16384⟩
    (by decide) selected_cut_20061

theorem selected_cut_20062 : selected 8 ⟨513184, by decide⟩
    (prefixPartial 13 290089) = some ⟨13, 2, 0, 513184, 290089, 2173, 16384⟩ := by
  decide +kernel

theorem context_13_290089_513184 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290089 ⟨513184, by decide⟩ :=
  accepted_of_selected 13 290089 ⟨513184, by decide⟩ ⟨13, 2, 0, 513184, 290089, 2173, 16384⟩
    (by decide) selected_cut_20062

theorem selected_cut_20063 : selected 8 ⟨513207, by decide⟩
    (prefixPartial 13 290090) = some ⟨13, 2, 0, 513207, 290090, 1765, 16384⟩ := by
  decide +kernel

theorem context_13_290090_513207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290090 ⟨513207, by decide⟩ :=
  accepted_of_selected 13 290090 ⟨513207, by decide⟩ ⟨13, 2, 0, 513207, 290090, 1765, 16384⟩
    (by decide) selected_cut_20063

theorem selected_cut_20064 : selected 8 ⟨513213, by decide⟩
    (prefixPartial 13 290091) = some ⟨13, 2, 0, 513213, 290091, 797, 16384⟩ := by
  decide +kernel

theorem context_13_290091_513213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290091 ⟨513213, by decide⟩ :=
  accepted_of_selected 13 290091 ⟨513213, by decide⟩ ⟨13, 2, 0, 513213, 290091, 797, 16384⟩
    (by decide) selected_cut_20064

theorem unmarked_context_12_72522_513214 : frontier 9 ⟨513214, by decide⟩
    (prefixCache 12 72522) (prefixPartial 12 72522) = false := by
  decide +kernel

theorem node_context_12_72522_513214 : EJMOriginalGlobalDAGData.nodes 9 ⟨513214, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨513184, by decide⟩,⟨513207, by decide⟩,⟨513213, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72522_513214 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72522 ⟨513214, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72522
    ⟨513214, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨513184, by decide⟩,⟨513207, by decide⟩,⟨513213, by decide⟩]) unmarked_context_12_72522_513214 node_context_12_72522_513214
  intro a
  fin_cases a
  · exact context_13_290088_3444
  · exact context_13_290089_513184
  · exact context_13_290090_513207
  · exact context_13_290091_513213

theorem selected_cut_20065 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 290092) = some ⟨13, 1, 0, 3444, 290092, 1, 16384⟩ := by
  decide +kernel

theorem context_13_290092_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290092 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 290092 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 290092, 1, 16384⟩
    (by decide) selected_cut_20065

theorem selected_cut_20066 : selected 8 ⟨513236, by decide⟩
    (prefixPartial 13 290093) = some ⟨13, 2, 0, 513236, 290093, 2233, 16384⟩ := by
  decide +kernel

theorem context_13_290093_513236 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290093 ⟨513236, by decide⟩ :=
  accepted_of_selected 13 290093 ⟨513236, by decide⟩ ⟨13, 2, 0, 513236, 290093, 2233, 16384⟩
    (by decide) selected_cut_20066

theorem selected_cut_20067 : selected 8 ⟨513256, by decide⟩
    (prefixPartial 13 290094) = some ⟨13, 2, 0, 513256, 290094, 1689, 16384⟩ := by
  decide +kernel

theorem context_13_290094_513256 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 290094 ⟨513256, by decide⟩ :=
  accepted_of_selected 13 290094 ⟨513256, by decide⟩ ⟨13, 2, 0, 513256, 290094, 1689, 16384⟩
    (by decide) selected_cut_20067

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
