/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover484
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_46564 : selected 9 ⟨1298697, by decide⟩
    (prefixPartial 12 370990) = some ⟨12, 2, 0, 1298697, 370990, 1889, 65536⟩ := by
  decide +kernel

theorem context_12_370990_1298697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370990 ⟨1298697, by decide⟩ :=
  accepted_of_selected 12 370990 ⟨1298697, by decide⟩ ⟨12, 2, 0, 1298697, 370990, 1889, 65536⟩
    (by decide) selected_cut_46564

theorem selected_cut_46565 : selected 9 ⟨1298727, by decide⟩
    (prefixPartial 12 370991) = some ⟨12, 2, 0, 1298727, 370991, 2161, 65536⟩ := by
  decide +kernel

theorem context_12_370991_1298727 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370991 ⟨1298727, by decide⟩ :=
  accepted_of_selected 12 370991 ⟨1298727, by decide⟩ ⟨12, 2, 0, 1298727, 370991, 2161, 65536⟩
    (by decide) selected_cut_46565

theorem unmarked_context_11_92747_1298728 : frontier 10 ⟨1298728, by decide⟩
    (prefixCache 11 92747) (prefixPartial 11 92747) = false := by
  decide +kernel

theorem node_context_11_92747_1298728 : EJMOriginalGlobalDAGData.nodes 10 ⟨1298728, by decide⟩ =
    .split (coordinate 11) (![⟨1298637, by decide⟩,⟨1298669, by decide⟩,⟨1298697, by decide⟩,⟨1298727, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92747_1298728 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92747 ⟨1298728, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92747
    ⟨1298728, by decide⟩ (by decide) (![⟨1298637, by decide⟩,⟨1298669, by decide⟩,⟨1298697, by decide⟩,⟨1298727, by decide⟩]) unmarked_context_11_92747_1298728 node_context_11_92747_1298728
  intro a
  fin_cases a
  · exact context_12_370988_1298637
  · exact context_12_370989_1298669
  · exact context_12_370990_1298697
  · exact context_12_370991_1298727

theorem unmarked_context_10_23186_1298729 : frontier 11 ⟨1298729, by decide⟩
    (prefixCache 10 23186) (prefixPartial 10 23186) = false := by
  decide +kernel

theorem node_context_10_23186_1298729 : EJMOriginalGlobalDAGData.nodes 11 ⟨1298729, by decide⟩ =
    .split (coordinate 10) (![⟨1298512, by decide⟩,⟨1298609, by decide⟩,⟨900587, by decide⟩,⟨1298728, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23186_1298729 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23186 ⟨1298729, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23186
    ⟨1298729, by decide⟩ (by decide) (![⟨1298512, by decide⟩,⟨1298609, by decide⟩,⟨900587, by decide⟩,⟨1298728, by decide⟩]) unmarked_context_10_23186_1298729 node_context_10_23186_1298729
  intro a
  fin_cases a
  · exact context_11_92744_1298512
  · exact context_11_92745_1298609
  · exact context_11_92746_900587
  · exact context_11_92747_1298728

theorem selected_cut_46566 : selected 9 ⟨1255011, by decide⟩
    (prefixPartial 12 370992) = some ⟨12, 1, 0, 1255011, 370992, 1, 65536⟩ := by
  decide +kernel

theorem context_12_370992_1255011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370992 ⟨1255011, by decide⟩ :=
  accepted_of_selected 12 370992 ⟨1255011, by decide⟩ ⟨12, 1, 0, 1255011, 370992, 1, 65536⟩
    (by decide) selected_cut_46566

theorem selected_cut_46567 : selected 9 ⟨1298756, by decide⟩
    (prefixPartial 12 370993) = some ⟨12, 2, 0, 1298756, 370993, 2041, 65536⟩ := by
  decide +kernel

theorem context_12_370993_1298756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370993 ⟨1298756, by decide⟩ :=
  accepted_of_selected 12 370993 ⟨1298756, by decide⟩ ⟨12, 2, 0, 1298756, 370993, 2041, 65536⟩
    (by decide) selected_cut_46567

theorem selected_cut_46568 : selected 9 ⟨1298787, by decide⟩
    (prefixPartial 12 370994) = some ⟨12, 2, 0, 1298787, 370994, 1781, 65536⟩ := by
  decide +kernel

theorem context_12_370994_1298787 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370994 ⟨1298787, by decide⟩ :=
  accepted_of_selected 12 370994 ⟨1298787, by decide⟩ ⟨12, 2, 0, 1298787, 370994, 1781, 65536⟩
    (by decide) selected_cut_46568

theorem selected_cut_46569 : selected 9 ⟨1298838, by decide⟩
    (prefixPartial 12 370995) = some ⟨12, 2, 0, 1298838, 370995, 2185, 65536⟩ := by
  decide +kernel

theorem context_12_370995_1298838 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370995 ⟨1298838, by decide⟩ :=
  accepted_of_selected 12 370995 ⟨1298838, by decide⟩ ⟨12, 2, 0, 1298838, 370995, 2185, 65536⟩
    (by decide) selected_cut_46569

theorem unmarked_context_11_92748_1298839 : frontier 10 ⟨1298839, by decide⟩
    (prefixCache 11 92748) (prefixPartial 11 92748) = false := by
  decide +kernel

theorem node_context_11_92748_1298839 : EJMOriginalGlobalDAGData.nodes 10 ⟨1298839, by decide⟩ =
    .split (coordinate 11) (![⟨1255011, by decide⟩,⟨1298756, by decide⟩,⟨1298787, by decide⟩,⟨1298838, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92748_1298839 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92748 ⟨1298839, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92748
    ⟨1298839, by decide⟩ (by decide) (![⟨1255011, by decide⟩,⟨1298756, by decide⟩,⟨1298787, by decide⟩,⟨1298838, by decide⟩]) unmarked_context_11_92748_1298839 node_context_11_92748_1298839
  intro a
  fin_cases a
  · exact context_12_370992_1255011
  · exact context_12_370993_1298756
  · exact context_12_370994_1298787
  · exact context_12_370995_1298838

theorem selected_cut_46570 : selected 9 ⟨1298880, by decide⟩
    (prefixPartial 12 370996) = some ⟨12, 2, 0, 1298880, 370996, 2193, 65536⟩ := by
  decide +kernel

theorem context_12_370996_1298880 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370996 ⟨1298880, by decide⟩ :=
  accepted_of_selected 12 370996 ⟨1298880, by decide⟩ ⟨12, 2, 0, 1298880, 370996, 2193, 65536⟩
    (by decide) selected_cut_46570

theorem selected_cut_46571 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 370997) = some ⟨12, 1, 0, 891951, 370997, 1, 65536⟩ := by
  decide +kernel

theorem context_12_370997_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370997 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 370997 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 370997, 1, 65536⟩
    (by decide) selected_cut_46571

theorem selected_cut_46572 : selected 9 ⟨1298907, by decide⟩
    (prefixPartial 12 370998) = some ⟨12, 2, 0, 1298907, 370998, 1965, 65536⟩ := by
  decide +kernel

theorem context_12_370998_1298907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370998 ⟨1298907, by decide⟩ :=
  accepted_of_selected 12 370998 ⟨1298907, by decide⟩ ⟨12, 2, 0, 1298907, 370998, 1965, 65536⟩
    (by decide) selected_cut_46572

theorem selected_cut_46573 : selected 9 ⟨1298952, by decide⟩
    (prefixPartial 12 370999) = some ⟨12, 2, 0, 1298952, 370999, 2241, 65536⟩ := by
  decide +kernel

theorem context_12_370999_1298952 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 370999 ⟨1298952, by decide⟩ :=
  accepted_of_selected 12 370999 ⟨1298952, by decide⟩ ⟨12, 2, 0, 1298952, 370999, 2241, 65536⟩
    (by decide) selected_cut_46573

theorem unmarked_context_11_92749_1298953 : frontier 10 ⟨1298953, by decide⟩
    (prefixCache 11 92749) (prefixPartial 11 92749) = false := by
  decide +kernel

theorem node_context_11_92749_1298953 : EJMOriginalGlobalDAGData.nodes 10 ⟨1298953, by decide⟩ =
    .split (coordinate 11) (![⟨1298880, by decide⟩,⟨891951, by decide⟩,⟨1298907, by decide⟩,⟨1298952, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92749_1298953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92749 ⟨1298953, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92749
    ⟨1298953, by decide⟩ (by decide) (![⟨1298880, by decide⟩,⟨891951, by decide⟩,⟨1298907, by decide⟩,⟨1298952, by decide⟩]) unmarked_context_11_92749_1298953 node_context_11_92749_1298953
  intro a
  fin_cases a
  · exact context_12_370996_1298880
  · exact context_12_370997_891951
  · exact context_12_370998_1298907
  · exact context_12_370999_1298952

theorem selected_cut_46574 : selected 9 ⟨1298985, by decide⟩
    (prefixPartial 12 371000) = some ⟨12, 2, 0, 1298985, 371000, 1833, 65536⟩ := by
  decide +kernel

theorem context_12_371000_1298985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371000 ⟨1298985, by decide⟩ :=
  accepted_of_selected 12 371000 ⟨1298985, by decide⟩ ⟨12, 2, 0, 1298985, 371000, 1833, 65536⟩
    (by decide) selected_cut_46574

theorem selected_cut_46575 : selected 9 ⟨1299012, by decide⟩
    (prefixPartial 12 371001) = some ⟨12, 2, 0, 1299012, 371001, 2029, 65536⟩ := by
  decide +kernel

theorem context_12_371001_1299012 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371001 ⟨1299012, by decide⟩ :=
  accepted_of_selected 12 371001 ⟨1299012, by decide⟩ ⟨12, 2, 0, 1299012, 371001, 2029, 65536⟩
    (by decide) selected_cut_46575

theorem selected_cut_46576 : selected 9 ⟨1299044, by decide⟩
    (prefixPartial 12 371002) = some ⟨12, 2, 0, 1299044, 371002, 1717, 65536⟩ := by
  decide +kernel

theorem context_12_371002_1299044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371002 ⟨1299044, by decide⟩ :=
  accepted_of_selected 12 371002 ⟨1299044, by decide⟩ ⟨12, 2, 0, 1299044, 371002, 1717, 65536⟩
    (by decide) selected_cut_46576

theorem selected_cut_46577 : selected 9 ⟨1299076, by decide⟩
    (prefixPartial 12 371003) = some ⟨12, 2, 0, 1299076, 371003, 1937, 65536⟩ := by
  decide +kernel

theorem context_12_371003_1299076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371003 ⟨1299076, by decide⟩ :=
  accepted_of_selected 12 371003 ⟨1299076, by decide⟩ ⟨12, 2, 0, 1299076, 371003, 1937, 65536⟩
    (by decide) selected_cut_46577

theorem unmarked_context_11_92750_1299077 : frontier 10 ⟨1299077, by decide⟩
    (prefixCache 11 92750) (prefixPartial 11 92750) = false := by
  decide +kernel

theorem node_context_11_92750_1299077 : EJMOriginalGlobalDAGData.nodes 10 ⟨1299077, by decide⟩ =
    .split (coordinate 11) (![⟨1298985, by decide⟩,⟨1299012, by decide⟩,⟨1299044, by decide⟩,⟨1299076, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92750_1299077 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92750 ⟨1299077, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92750
    ⟨1299077, by decide⟩ (by decide) (![⟨1298985, by decide⟩,⟨1299012, by decide⟩,⟨1299044, by decide⟩,⟨1299076, by decide⟩]) unmarked_context_11_92750_1299077 node_context_11_92750_1299077
  intro a
  fin_cases a
  · exact context_12_371000_1298985
  · exact context_12_371001_1299012
  · exact context_12_371002_1299044
  · exact context_12_371003_1299076

theorem selected_cut_46578 : selected 9 ⟨1299105, by decide⟩
    (prefixPartial 12 371004) = some ⟨12, 2, 0, 1299105, 371004, 1713, 65536⟩ := by
  decide +kernel

theorem context_12_371004_1299105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371004 ⟨1299105, by decide⟩ :=
  accepted_of_selected 12 371004 ⟨1299105, by decide⟩ ⟨12, 2, 0, 1299105, 371004, 1713, 65536⟩
    (by decide) selected_cut_46578

theorem selected_cut_46579 : selected 9 ⟨1299134, by decide⟩
    (prefixPartial 12 371005) = some ⟨12, 2, 0, 1299134, 371005, 1705, 65536⟩ := by
  decide +kernel

theorem context_12_371005_1299134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371005 ⟨1299134, by decide⟩ :=
  accepted_of_selected 12 371005 ⟨1299134, by decide⟩ ⟨12, 2, 0, 1299134, 371005, 1705, 65536⟩
    (by decide) selected_cut_46579

theorem selected_cut_46580 : selected 9 ⟨1299157, by decide⟩
    (prefixPartial 12 371006) = some ⟨12, 2, 0, 1299157, 371006, 1553, 65536⟩ := by
  decide +kernel

theorem context_12_371006_1299157 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371006 ⟨1299157, by decide⟩ :=
  accepted_of_selected 12 371006 ⟨1299157, by decide⟩ ⟨12, 2, 0, 1299157, 371006, 1553, 65536⟩
    (by decide) selected_cut_46580

theorem selected_cut_46581 : selected 9 ⟨1120582, by decide⟩
    (prefixPartial 12 371007) = some ⟨12, 1, 0, 1120582, 371007, 1, 65536⟩ := by
  decide +kernel

theorem context_12_371007_1120582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371007 ⟨1120582, by decide⟩ :=
  accepted_of_selected 12 371007 ⟨1120582, by decide⟩ ⟨12, 1, 0, 1120582, 371007, 1, 65536⟩
    (by decide) selected_cut_46581

theorem unmarked_context_11_92751_1299158 : frontier 10 ⟨1299158, by decide⟩
    (prefixCache 11 92751) (prefixPartial 11 92751) = false := by
  decide +kernel

theorem node_context_11_92751_1299158 : EJMOriginalGlobalDAGData.nodes 10 ⟨1299158, by decide⟩ =
    .split (coordinate 11) (![⟨1299105, by decide⟩,⟨1299134, by decide⟩,⟨1299157, by decide⟩,⟨1120582, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92751_1299158 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92751 ⟨1299158, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92751
    ⟨1299158, by decide⟩ (by decide) (![⟨1299105, by decide⟩,⟨1299134, by decide⟩,⟨1299157, by decide⟩,⟨1120582, by decide⟩]) unmarked_context_11_92751_1299158 node_context_11_92751_1299158
  intro a
  fin_cases a
  · exact context_12_371004_1299105
  · exact context_12_371005_1299134
  · exact context_12_371006_1299157
  · exact context_12_371007_1120582

theorem unmarked_context_10_23187_1299159 : frontier 11 ⟨1299159, by decide⟩
    (prefixCache 10 23187) (prefixPartial 10 23187) = false := by
  decide +kernel

theorem node_context_10_23187_1299159 : EJMOriginalGlobalDAGData.nodes 11 ⟨1299159, by decide⟩ =
    .split (coordinate 10) (![⟨1298839, by decide⟩,⟨1298953, by decide⟩,⟨1299077, by decide⟩,⟨1299158, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23187_1299159 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23187 ⟨1299159, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23187
    ⟨1299159, by decide⟩ (by decide) (![⟨1298839, by decide⟩,⟨1298953, by decide⟩,⟨1299077, by decide⟩,⟨1299158, by decide⟩]) unmarked_context_10_23187_1299159 node_context_10_23187_1299159
  intro a
  fin_cases a
  · exact context_11_92748_1298839
  · exact context_11_92749_1298953
  · exact context_11_92750_1299077
  · exact context_11_92751_1299158

theorem unmarked_context_9_5796_1299160 : frontier 12 ⟨1299160, by decide⟩
    (prefixCache 9 5796) (prefixPartial 9 5796) = false := by
  decide +kernel

theorem node_context_9_5796_1299160 : EJMOriginalGlobalDAGData.nodes 12 ⟨1299160, by decide⟩ =
    .split (coordinate 9) (![⟨1297894, by decide⟩,⟨1298412, by decide⟩,⟨1298729, by decide⟩,⟨1299159, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5796_1299160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5796 ⟨1299160, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5796
    ⟨1299160, by decide⟩ (by decide) (![⟨1297894, by decide⟩,⟨1298412, by decide⟩,⟨1298729, by decide⟩,⟨1299159, by decide⟩]) unmarked_context_9_5796_1299160 node_context_9_5796_1299160
  intro a
  fin_cases a
  · exact context_10_23184_1297894
  · exact context_10_23185_1298412
  · exact context_10_23186_1298729
  · exact context_10_23187_1299159

theorem selected_cut_46582 : selected 10 ⟨1299250, by decide⟩
    (prefixPartial 11 92752) = some ⟨11, 2, 0, 1299250, 92752, 3361, 262144⟩ := by
  decide +kernel

theorem context_11_92752_1299250 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92752 ⟨1299250, by decide⟩ :=
  accepted_of_selected 11 92752 ⟨1299250, by decide⟩ ⟨11, 2, 0, 1299250, 92752, 3361, 262144⟩
    (by decide) selected_cut_46582

theorem selected_cut_46583 : selected 9 ⟨1299276, by decide⟩
    (prefixPartial 12 371012) = some ⟨12, 2, 0, 1299276, 371012, 1605, 65536⟩ := by
  decide +kernel

theorem context_12_371012_1299276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371012 ⟨1299276, by decide⟩ :=
  accepted_of_selected 12 371012 ⟨1299276, by decide⟩ ⟨12, 2, 0, 1299276, 371012, 1605, 65536⟩
    (by decide) selected_cut_46583

theorem selected_cut_46584 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 371013) = some ⟨12, 1, 0, 891951, 371013, 1, 65536⟩ := by
  decide +kernel

theorem context_12_371013_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371013 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 371013 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 371013, 1, 65536⟩
    (by decide) selected_cut_46584

theorem selected_cut_46585 : selected 9 ⟨1299300, by decide⟩
    (prefixPartial 12 371014) = some ⟨12, 2, 0, 1299300, 371014, 1421, 65536⟩ := by
  decide +kernel

theorem context_12_371014_1299300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371014 ⟨1299300, by decide⟩ :=
  accepted_of_selected 12 371014 ⟨1299300, by decide⟩ ⟨12, 2, 0, 1299300, 371014, 1421, 65536⟩
    (by decide) selected_cut_46585

theorem selected_cut_46586 : selected 9 ⟨1299328, by decide⟩
    (prefixPartial 12 371015) = some ⟨12, 2, 0, 1299328, 371015, 1541, 65536⟩ := by
  decide +kernel

theorem context_12_371015_1299328 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371015 ⟨1299328, by decide⟩ :=
  accepted_of_selected 12 371015 ⟨1299328, by decide⟩ ⟨12, 2, 0, 1299328, 371015, 1541, 65536⟩
    (by decide) selected_cut_46586

theorem unmarked_context_11_92753_1299329 : frontier 10 ⟨1299329, by decide⟩
    (prefixCache 11 92753) (prefixPartial 11 92753) = false := by
  decide +kernel

theorem node_context_11_92753_1299329 : EJMOriginalGlobalDAGData.nodes 10 ⟨1299329, by decide⟩ =
    .split (coordinate 11) (![⟨1299276, by decide⟩,⟨891951, by decide⟩,⟨1299300, by decide⟩,⟨1299328, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92753_1299329 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92753 ⟨1299329, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92753
    ⟨1299329, by decide⟩ (by decide) (![⟨1299276, by decide⟩,⟨891951, by decide⟩,⟨1299300, by decide⟩,⟨1299328, by decide⟩]) unmarked_context_11_92753_1299329 node_context_11_92753_1299329
  intro a
  fin_cases a
  · exact context_12_371012_1299276
  · exact context_12_371013_891951
  · exact context_12_371014_1299300
  · exact context_12_371015_1299328

theorem selected_cut_46587 : selected 10 ⟨1299377, by decide⟩
    (prefixPartial 11 92754) = some ⟨11, 2, 0, 1299377, 92754, 2881, 262144⟩ := by
  decide +kernel

theorem context_11_92754_1299377 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92754 ⟨1299377, by decide⟩ :=
  accepted_of_selected 11 92754 ⟨1299377, by decide⟩ ⟨11, 2, 0, 1299377, 92754, 2881, 262144⟩
    (by decide) selected_cut_46587

theorem selected_cut_46588 : selected 9 ⟨1299404, by decide⟩
    (prefixPartial 12 371020) = some ⟨12, 2, 0, 1299404, 371020, 1329, 65536⟩ := by
  decide +kernel

theorem context_12_371020_1299404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371020 ⟨1299404, by decide⟩ :=
  accepted_of_selected 12 371020 ⟨1299404, by decide⟩ ⟨12, 2, 0, 1299404, 371020, 1329, 65536⟩
    (by decide) selected_cut_46588

theorem selected_cut_46589 : selected 9 ⟨1299423, by decide⟩
    (prefixPartial 12 371021) = some ⟨12, 2, 0, 1299423, 371021, 1329, 65536⟩ := by
  decide +kernel

theorem context_12_371021_1299423 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371021 ⟨1299423, by decide⟩ :=
  accepted_of_selected 12 371021 ⟨1299423, by decide⟩ ⟨12, 2, 0, 1299423, 371021, 1329, 65536⟩
    (by decide) selected_cut_46589

theorem selected_cut_46590 : selected 9 ⟨1299448, by decide⟩
    (prefixPartial 12 371022) = some ⟨12, 2, 0, 1299448, 371022, 1253, 65536⟩ := by
  decide +kernel

theorem context_12_371022_1299448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371022 ⟨1299448, by decide⟩ :=
  accepted_of_selected 12 371022 ⟨1299448, by decide⟩ ⟨12, 2, 0, 1299448, 371022, 1253, 65536⟩
    (by decide) selected_cut_46590

theorem selected_cut_46591 : selected 9 ⟨1299468, by decide⟩
    (prefixPartial 12 371023) = some ⟨12, 2, 0, 1299468, 371023, 1389, 65536⟩ := by
  decide +kernel

theorem context_12_371023_1299468 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371023 ⟨1299468, by decide⟩ :=
  accepted_of_selected 12 371023 ⟨1299468, by decide⟩ ⟨12, 2, 0, 1299468, 371023, 1389, 65536⟩
    (by decide) selected_cut_46591

theorem unmarked_context_11_92755_1299469 : frontier 10 ⟨1299469, by decide⟩
    (prefixCache 11 92755) (prefixPartial 11 92755) = false := by
  decide +kernel

theorem node_context_11_92755_1299469 : EJMOriginalGlobalDAGData.nodes 10 ⟨1299469, by decide⟩ =
    .split (coordinate 11) (![⟨1299404, by decide⟩,⟨1299423, by decide⟩,⟨1299448, by decide⟩,⟨1299468, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92755_1299469 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92755 ⟨1299469, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92755
    ⟨1299469, by decide⟩ (by decide) (![⟨1299404, by decide⟩,⟨1299423, by decide⟩,⟨1299448, by decide⟩,⟨1299468, by decide⟩]) unmarked_context_11_92755_1299469 node_context_11_92755_1299469
  intro a
  fin_cases a
  · exact context_12_371020_1299404
  · exact context_12_371021_1299423
  · exact context_12_371022_1299448
  · exact context_12_371023_1299468

theorem unmarked_context_10_23188_1299470 : frontier 11 ⟨1299470, by decide⟩
    (prefixCache 10 23188) (prefixPartial 10 23188) = false := by
  decide +kernel

theorem node_context_10_23188_1299470 : EJMOriginalGlobalDAGData.nodes 11 ⟨1299470, by decide⟩ =
    .split (coordinate 10) (![⟨1299250, by decide⟩,⟨1299329, by decide⟩,⟨1299377, by decide⟩,⟨1299469, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23188_1299470 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23188 ⟨1299470, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23188
    ⟨1299470, by decide⟩ (by decide) (![⟨1299250, by decide⟩,⟨1299329, by decide⟩,⟨1299377, by decide⟩,⟨1299469, by decide⟩]) unmarked_context_10_23188_1299470 node_context_10_23188_1299470
  intro a
  fin_cases a
  · exact context_11_92752_1299250
  · exact context_11_92753_1299329
  · exact context_11_92754_1299377
  · exact context_11_92755_1299469

theorem selected_cut_46592 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 23189) = some ⟨10, 1, 0, 893098, 23189, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_23189_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23189 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 23189 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 23189, 1, 1048576⟩
    (by decide) selected_cut_46592

theorem selected_cut_46593 : selected 10 ⟨1299526, by decide⟩
    (prefixPartial 11 92760) = some ⟨11, 2, 0, 1299526, 92760, 2625, 262144⟩ := by
  decide +kernel

theorem context_11_92760_1299526 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92760 ⟨1299526, by decide⟩ :=
  accepted_of_selected 11 92760 ⟨1299526, by decide⟩ ⟨11, 2, 0, 1299526, 92760, 2625, 262144⟩
    (by decide) selected_cut_46593

theorem selected_cut_46594 : selected 10 ⟨1299586, by decide⟩
    (prefixPartial 11 92761) = some ⟨11, 2, 0, 1299586, 92761, 3345, 262144⟩ := by
  decide +kernel

theorem context_11_92761_1299586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92761 ⟨1299586, by decide⟩ :=
  accepted_of_selected 11 92761 ⟨1299586, by decide⟩ ⟨11, 2, 0, 1299586, 92761, 3345, 262144⟩
    (by decide) selected_cut_46594

theorem selected_cut_46595 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 92762) = some ⟨11, 1, 0, 900587, 92762, 1, 262144⟩ := by
  decide +kernel

theorem context_11_92762_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92762 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 92762 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 92762, 1, 262144⟩
    (by decide) selected_cut_46595

theorem selected_cut_46596 : selected 10 ⟨1299648, by decide⟩
    (prefixPartial 11 92763) = some ⟨11, 2, 0, 1299648, 92763, 2449, 262144⟩ := by
  decide +kernel

theorem context_11_92763_1299648 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92763 ⟨1299648, by decide⟩ :=
  accepted_of_selected 11 92763 ⟨1299648, by decide⟩ ⟨11, 2, 0, 1299648, 92763, 2449, 262144⟩
    (by decide) selected_cut_46596

theorem unmarked_context_10_23190_1299649 : frontier 11 ⟨1299649, by decide⟩
    (prefixCache 10 23190) (prefixPartial 10 23190) = false := by
  decide +kernel

theorem node_context_10_23190_1299649 : EJMOriginalGlobalDAGData.nodes 11 ⟨1299649, by decide⟩ =
    .split (coordinate 10) (![⟨1299526, by decide⟩,⟨1299586, by decide⟩,⟨900587, by decide⟩,⟨1299648, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23190_1299649 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23190 ⟨1299649, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23190
    ⟨1299649, by decide⟩ (by decide) (![⟨1299526, by decide⟩,⟨1299586, by decide⟩,⟨900587, by decide⟩,⟨1299648, by decide⟩]) unmarked_context_10_23190_1299649 node_context_10_23190_1299649
  intro a
  fin_cases a
  · exact context_11_92760_1299526
  · exact context_11_92761_1299586
  · exact context_11_92762_900587
  · exact context_11_92763_1299648

theorem selected_cut_46597 : selected 9 ⟨1299668, by decide⟩
    (prefixPartial 12 371056) = some ⟨12, 2, 0, 1299668, 371056, 1125, 65536⟩ := by
  decide +kernel

theorem context_12_371056_1299668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371056 ⟨1299668, by decide⟩ :=
  accepted_of_selected 12 371056 ⟨1299668, by decide⟩ ⟨12, 2, 0, 1299668, 371056, 1125, 65536⟩
    (by decide) selected_cut_46597

theorem selected_cut_46598 : selected 9 ⟨1299688, by decide⟩
    (prefixPartial 12 371057) = some ⟨12, 2, 0, 1299688, 371057, 1037, 65536⟩ := by
  decide +kernel

theorem context_12_371057_1299688 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371057 ⟨1299688, by decide⟩ :=
  accepted_of_selected 12 371057 ⟨1299688, by decide⟩ ⟨12, 2, 0, 1299688, 371057, 1037, 65536⟩
    (by decide) selected_cut_46598

theorem selected_cut_46599 : selected 9 ⟨1299706, by decide⟩
    (prefixPartial 12 371058) = some ⟨12, 2, 0, 1299706, 371058, 937, 65536⟩ := by
  decide +kernel

theorem context_12_371058_1299706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371058 ⟨1299706, by decide⟩ :=
  accepted_of_selected 12 371058 ⟨1299706, by decide⟩ ⟨12, 2, 0, 1299706, 371058, 937, 65536⟩
    (by decide) selected_cut_46599

theorem selected_cut_46600 : selected 9 ⟨1299729, by decide⟩
    (prefixPartial 12 371059) = some ⟨12, 2, 0, 1299729, 371059, 1053, 65536⟩ := by
  decide +kernel

theorem context_12_371059_1299729 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371059 ⟨1299729, by decide⟩ :=
  accepted_of_selected 12 371059 ⟨1299729, by decide⟩ ⟨12, 2, 0, 1299729, 371059, 1053, 65536⟩
    (by decide) selected_cut_46600

theorem unmarked_context_11_92764_1299730 : frontier 10 ⟨1299730, by decide⟩
    (prefixCache 11 92764) (prefixPartial 11 92764) = false := by
  decide +kernel

theorem node_context_11_92764_1299730 : EJMOriginalGlobalDAGData.nodes 10 ⟨1299730, by decide⟩ =
    .split (coordinate 11) (![⟨1299668, by decide⟩,⟨1299688, by decide⟩,⟨1299706, by decide⟩,⟨1299729, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92764_1299730 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92764 ⟨1299730, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92764
    ⟨1299730, by decide⟩ (by decide) (![⟨1299668, by decide⟩,⟨1299688, by decide⟩,⟨1299706, by decide⟩,⟨1299729, by decide⟩]) unmarked_context_11_92764_1299730 node_context_11_92764_1299730
  intro a
  fin_cases a
  · exact context_12_371056_1299668
  · exact context_12_371057_1299688
  · exact context_12_371058_1299706
  · exact context_12_371059_1299729

theorem selected_cut_46601 : selected 10 ⟨1299783, by decide⟩
    (prefixPartial 11 92765) = some ⟨11, 2, 0, 1299783, 92765, 3097, 262144⟩ := by
  decide +kernel

theorem context_11_92765_1299783 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92765 ⟨1299783, by decide⟩ :=
  accepted_of_selected 11 92765 ⟨1299783, by decide⟩ ⟨11, 2, 0, 1299783, 92765, 3097, 262144⟩
    (by decide) selected_cut_46601

theorem selected_cut_46602 : selected 10 ⟨1299812, by decide⟩
    (prefixPartial 11 92766) = some ⟨11, 2, 0, 1299812, 92766, 1929, 262144⟩ := by
  decide +kernel

theorem context_11_92766_1299812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92766 ⟨1299812, by decide⟩ :=
  accepted_of_selected 11 92766 ⟨1299812, by decide⟩ ⟨11, 2, 0, 1299812, 92766, 1929, 262144⟩
    (by decide) selected_cut_46602

theorem selected_cut_46603 : selected 10 ⟨1299858, by decide⟩
    (prefixPartial 11 92767) = some ⟨11, 2, 0, 1299858, 92767, 1965, 262144⟩ := by
  decide +kernel

theorem context_11_92767_1299858 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92767 ⟨1299858, by decide⟩ :=
  accepted_of_selected 11 92767 ⟨1299858, by decide⟩ ⟨11, 2, 0, 1299858, 92767, 1965, 262144⟩
    (by decide) selected_cut_46603

theorem unmarked_context_10_23191_1299859 : frontier 11 ⟨1299859, by decide⟩
    (prefixCache 10 23191) (prefixPartial 10 23191) = false := by
  decide +kernel

theorem node_context_10_23191_1299859 : EJMOriginalGlobalDAGData.nodes 11 ⟨1299859, by decide⟩ =
    .split (coordinate 10) (![⟨1299730, by decide⟩,⟨1299783, by decide⟩,⟨1299812, by decide⟩,⟨1299858, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23191_1299859 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23191 ⟨1299859, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23191
    ⟨1299859, by decide⟩ (by decide) (![⟨1299730, by decide⟩,⟨1299783, by decide⟩,⟨1299812, by decide⟩,⟨1299858, by decide⟩]) unmarked_context_10_23191_1299859 node_context_10_23191_1299859
  intro a
  fin_cases a
  · exact context_11_92764_1299730
  · exact context_11_92765_1299783
  · exact context_11_92766_1299812
  · exact context_11_92767_1299858

theorem unmarked_context_9_5797_1299860 : frontier 12 ⟨1299860, by decide⟩
    (prefixCache 9 5797) (prefixPartial 9 5797) = false := by
  decide +kernel

theorem node_context_9_5797_1299860 : EJMOriginalGlobalDAGData.nodes 12 ⟨1299860, by decide⟩ =
    .split (coordinate 9) (![⟨1299470, by decide⟩,⟨893098, by decide⟩,⟨1299649, by decide⟩,⟨1299859, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5797_1299860 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5797 ⟨1299860, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5797
    ⟨1299860, by decide⟩ (by decide) (![⟨1299470, by decide⟩,⟨893098, by decide⟩,⟨1299649, by decide⟩,⟨1299859, by decide⟩]) unmarked_context_9_5797_1299860 node_context_9_5797_1299860
  intro a
  fin_cases a
  · exact context_10_23188_1299470
  · exact context_10_23189_893098
  · exact context_10_23190_1299649
  · exact context_10_23191_1299859

theorem selected_cut_46604 : selected 10 ⟨1299880, by decide⟩
    (prefixPartial 11 92768) = some ⟨11, 2, 0, 1299880, 92768, 901, 262144⟩ := by
  decide +kernel

theorem context_11_92768_1299880 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92768 ⟨1299880, by decide⟩ :=
  accepted_of_selected 11 92768 ⟨1299880, by decide⟩ ⟨11, 2, 0, 1299880, 92768, 901, 262144⟩
    (by decide) selected_cut_46604

theorem selected_cut_46605 : selected 10 ⟨1299921, by decide⟩
    (prefixPartial 11 92769) = some ⟨11, 2, 0, 1299921, 92769, 2001, 262144⟩ := by
  decide +kernel

theorem context_11_92769_1299921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92769 ⟨1299921, by decide⟩ :=
  accepted_of_selected 11 92769 ⟨1299921, by decide⟩ ⟨11, 2, 0, 1299921, 92769, 2001, 262144⟩
    (by decide) selected_cut_46605

theorem selected_cut_46606 : selected 10 ⟨1299986, by decide⟩
    (prefixPartial 11 92770) = some ⟨11, 2, 0, 1299986, 92770, 3181, 262144⟩ := by
  decide +kernel

theorem context_11_92770_1299986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92770 ⟨1299986, by decide⟩ :=
  accepted_of_selected 11 92770 ⟨1299986, by decide⟩ ⟨11, 2, 0, 1299986, 92770, 3181, 262144⟩
    (by decide) selected_cut_46606

theorem selected_cut_46607 : selected 10 ⟨1300030, by decide⟩
    (prefixPartial 11 92771) = some ⟨11, 2, 0, 1300030, 92771, 2805, 262144⟩ := by
  decide +kernel

theorem context_11_92771_1300030 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92771 ⟨1300030, by decide⟩ :=
  accepted_of_selected 11 92771 ⟨1300030, by decide⟩ ⟨11, 2, 0, 1300030, 92771, 2805, 262144⟩
    (by decide) selected_cut_46607

theorem unmarked_context_10_23192_1300031 : frontier 11 ⟨1300031, by decide⟩
    (prefixCache 10 23192) (prefixPartial 10 23192) = false := by
  decide +kernel

theorem node_context_10_23192_1300031 : EJMOriginalGlobalDAGData.nodes 11 ⟨1300031, by decide⟩ =
    .split (coordinate 10) (![⟨1299880, by decide⟩,⟨1299921, by decide⟩,⟨1299986, by decide⟩,⟨1300030, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23192_1300031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23192 ⟨1300031, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23192
    ⟨1300031, by decide⟩ (by decide) (![⟨1299880, by decide⟩,⟨1299921, by decide⟩,⟨1299986, by decide⟩,⟨1300030, by decide⟩]) unmarked_context_10_23192_1300031 node_context_10_23192_1300031
  intro a
  fin_cases a
  · exact context_11_92768_1299880
  · exact context_11_92769_1299921
  · exact context_11_92770_1299986
  · exact context_11_92771_1300030

theorem selected_cut_46608 : selected 10 ⟨1300083, by decide⟩
    (prefixPartial 11 92772) = some ⟨11, 2, 0, 1300083, 92772, 1817, 262144⟩ := by
  decide +kernel

theorem context_11_92772_1300083 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92772 ⟨1300083, by decide⟩ :=
  accepted_of_selected 11 92772 ⟨1300083, by decide⟩ ⟨11, 2, 0, 1300083, 92772, 1817, 262144⟩
    (by decide) selected_cut_46608

theorem selected_cut_46609 : selected 10 ⟨1192826, by decide⟩
    (prefixPartial 11 92773) = some ⟨11, 1, 0, 1192826, 92773, 1, 262144⟩ := by
  decide +kernel

theorem context_11_92773_1192826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92773 ⟨1192826, by decide⟩ :=
  accepted_of_selected 11 92773 ⟨1192826, by decide⟩ ⟨11, 1, 0, 1192826, 92773, 1, 262144⟩
    (by decide) selected_cut_46609

theorem selected_cut_46610 : selected 10 ⟨1300122, by decide⟩
    (prefixPartial 11 92774) = some ⟨11, 2, 0, 1300122, 92774, 2085, 262144⟩ := by
  decide +kernel

theorem context_11_92774_1300122 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92774 ⟨1300122, by decide⟩ :=
  accepted_of_selected 11 92774 ⟨1300122, by decide⟩ ⟨11, 2, 0, 1300122, 92774, 2085, 262144⟩
    (by decide) selected_cut_46610

theorem selected_cut_46611 : selected 10 ⟨1300155, by decide⟩
    (prefixPartial 11 92775) = some ⟨11, 2, 0, 1300155, 92775, 1465, 262144⟩ := by
  decide +kernel

theorem context_11_92775_1300155 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92775 ⟨1300155, by decide⟩ :=
  accepted_of_selected 11 92775 ⟨1300155, by decide⟩ ⟨11, 2, 0, 1300155, 92775, 1465, 262144⟩
    (by decide) selected_cut_46611

theorem unmarked_context_10_23193_1300156 : frontier 11 ⟨1300156, by decide⟩
    (prefixCache 10 23193) (prefixPartial 10 23193) = false := by
  decide +kernel

theorem node_context_10_23193_1300156 : EJMOriginalGlobalDAGData.nodes 11 ⟨1300156, by decide⟩ =
    .split (coordinate 10) (![⟨1300083, by decide⟩,⟨1192826, by decide⟩,⟨1300122, by decide⟩,⟨1300155, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23193_1300156 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23193 ⟨1300156, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23193
    ⟨1300156, by decide⟩ (by decide) (![⟨1300083, by decide⟩,⟨1192826, by decide⟩,⟨1300122, by decide⟩,⟨1300155, by decide⟩]) unmarked_context_10_23193_1300156 node_context_10_23193_1300156
  intro a
  fin_cases a
  · exact context_11_92772_1300083
  · exact context_11_92773_1192826
  · exact context_11_92774_1300122
  · exact context_11_92775_1300155

theorem selected_cut_46612 : selected 11 ⟨1300205, by decide⟩
    (prefixPartial 10 23194) = some ⟨10, 2, 0, 1300205, 23194, 2469, 1048576⟩ := by
  decide +kernel

theorem context_10_23194_1300205 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23194 ⟨1300205, by decide⟩ :=
  accepted_of_selected 10 23194 ⟨1300205, by decide⟩ ⟨10, 2, 0, 1300205, 23194, 2469, 1048576⟩
    (by decide) selected_cut_46612

theorem selected_cut_46613 : selected 10 ⟨1300232, by decide⟩
    (prefixPartial 11 92780) = some ⟨11, 2, 0, 1300232, 92780, 1509, 262144⟩ := by
  decide +kernel

theorem context_11_92780_1300232 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92780 ⟨1300232, by decide⟩ :=
  accepted_of_selected 11 92780 ⟨1300232, by decide⟩ ⟨11, 2, 0, 1300232, 92780, 1509, 262144⟩
    (by decide) selected_cut_46613

theorem selected_cut_46614 : selected 10 ⟨1300248, by decide⟩
    (prefixPartial 11 92781) = some ⟨11, 2, 0, 1300248, 92781, 1061, 262144⟩ := by
  decide +kernel

theorem context_11_92781_1300248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92781 ⟨1300248, by decide⟩ :=
  accepted_of_selected 11 92781 ⟨1300248, by decide⟩ ⟨11, 2, 0, 1300248, 92781, 1061, 262144⟩
    (by decide) selected_cut_46614

theorem selected_cut_46615 : selected 10 ⟨1300269, by decide⟩
    (prefixPartial 11 92782) = some ⟨11, 2, 0, 1300269, 92782, 1353, 262144⟩ := by
  decide +kernel

theorem context_11_92782_1300269 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92782 ⟨1300269, by decide⟩ :=
  accepted_of_selected 11 92782 ⟨1300269, by decide⟩ ⟨11, 2, 0, 1300269, 92782, 1353, 262144⟩
    (by decide) selected_cut_46615

theorem selected_cut_46616 : selected 10 ⟨1300294, by decide⟩
    (prefixPartial 11 92783) = some ⟨11, 2, 0, 1300294, 92783, 565, 262144⟩ := by
  decide +kernel

theorem context_11_92783_1300294 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92783 ⟨1300294, by decide⟩ :=
  accepted_of_selected 11 92783 ⟨1300294, by decide⟩ ⟨11, 2, 0, 1300294, 92783, 565, 262144⟩
    (by decide) selected_cut_46616

theorem unmarked_context_10_23195_1300295 : frontier 11 ⟨1300295, by decide⟩
    (prefixCache 10 23195) (prefixPartial 10 23195) = false := by
  decide +kernel

theorem node_context_10_23195_1300295 : EJMOriginalGlobalDAGData.nodes 11 ⟨1300295, by decide⟩ =
    .split (coordinate 10) (![⟨1300232, by decide⟩,⟨1300248, by decide⟩,⟨1300269, by decide⟩,⟨1300294, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23195_1300295 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23195 ⟨1300295, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23195
    ⟨1300295, by decide⟩ (by decide) (![⟨1300232, by decide⟩,⟨1300248, by decide⟩,⟨1300269, by decide⟩,⟨1300294, by decide⟩]) unmarked_context_10_23195_1300295 node_context_10_23195_1300295
  intro a
  fin_cases a
  · exact context_11_92780_1300232
  · exact context_11_92781_1300248
  · exact context_11_92782_1300269
  · exact context_11_92783_1300294

theorem unmarked_context_9_5798_1300296 : frontier 12 ⟨1300296, by decide⟩
    (prefixCache 9 5798) (prefixPartial 9 5798) = false := by
  decide +kernel

theorem node_context_9_5798_1300296 : EJMOriginalGlobalDAGData.nodes 12 ⟨1300296, by decide⟩ =
    .split (coordinate 9) (![⟨1300031, by decide⟩,⟨1300156, by decide⟩,⟨1300205, by decide⟩,⟨1300295, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5798_1300296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5798 ⟨1300296, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5798
    ⟨1300296, by decide⟩ (by decide) (![⟨1300031, by decide⟩,⟨1300156, by decide⟩,⟨1300205, by decide⟩,⟨1300295, by decide⟩]) unmarked_context_9_5798_1300296 node_context_9_5798_1300296
  intro a
  fin_cases a
  · exact context_10_23192_1300031
  · exact context_10_23193_1300156
  · exact context_10_23194_1300205
  · exact context_10_23195_1300295

theorem selected_cut_46617 : selected 10 ⟨1300325, by decide⟩
    (prefixPartial 11 92784) = some ⟨11, 2, 0, 1300325, 92784, 1413, 262144⟩ := by
  decide +kernel

theorem context_11_92784_1300325 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92784 ⟨1300325, by decide⟩ :=
  accepted_of_selected 11 92784 ⟨1300325, by decide⟩ ⟨11, 2, 0, 1300325, 92784, 1413, 262144⟩
    (by decide) selected_cut_46617

theorem selected_cut_46618 : selected 10 ⟨1300350, by decide⟩
    (prefixPartial 11 92785) = some ⟨11, 2, 0, 1300350, 92785, 1565, 262144⟩ := by
  decide +kernel

theorem context_11_92785_1300350 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92785 ⟨1300350, by decide⟩ :=
  accepted_of_selected 11 92785 ⟨1300350, by decide⟩ ⟨11, 2, 0, 1300350, 92785, 1565, 262144⟩
    (by decide) selected_cut_46618

theorem selected_cut_46619 : selected 10 ⟨1300395, by decide⟩
    (prefixPartial 11 92786) = some ⟨11, 2, 0, 1300395, 92786, 1773, 262144⟩ := by
  decide +kernel

theorem context_11_92786_1300395 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92786 ⟨1300395, by decide⟩ :=
  accepted_of_selected 11 92786 ⟨1300395, by decide⟩ ⟨11, 2, 0, 1300395, 92786, 1773, 262144⟩
    (by decide) selected_cut_46619

theorem selected_cut_46620 : selected 10 ⟨1300416, by decide⟩
    (prefixPartial 11 92787) = some ⟨11, 2, 0, 1300416, 92787, 1269, 262144⟩ := by
  decide +kernel

theorem context_11_92787_1300416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92787 ⟨1300416, by decide⟩ :=
  accepted_of_selected 11 92787 ⟨1300416, by decide⟩ ⟨11, 2, 0, 1300416, 92787, 1269, 262144⟩
    (by decide) selected_cut_46620

theorem unmarked_context_10_23196_1300417 : frontier 11 ⟨1300417, by decide⟩
    (prefixCache 10 23196) (prefixPartial 10 23196) = false := by
  decide +kernel

theorem node_context_10_23196_1300417 : EJMOriginalGlobalDAGData.nodes 11 ⟨1300417, by decide⟩ =
    .split (coordinate 10) (![⟨1300325, by decide⟩,⟨1300350, by decide⟩,⟨1300395, by decide⟩,⟨1300416, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23196_1300417 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23196 ⟨1300417, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23196
    ⟨1300417, by decide⟩ (by decide) (![⟨1300325, by decide⟩,⟨1300350, by decide⟩,⟨1300395, by decide⟩,⟨1300416, by decide⟩]) unmarked_context_10_23196_1300417 node_context_10_23196_1300417
  intro a
  fin_cases a
  · exact context_11_92784_1300325
  · exact context_11_92785_1300350
  · exact context_11_92786_1300395
  · exact context_11_92787_1300416

theorem selected_cut_46621 : selected 11 ⟨1300478, by decide⟩
    (prefixPartial 10 23197) = some ⟨10, 2, 0, 1300478, 23197, 2933, 1048576⟩ := by
  decide +kernel

theorem context_10_23197_1300478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23197 ⟨1300478, by decide⟩ :=
  accepted_of_selected 10 23197 ⟨1300478, by decide⟩ ⟨10, 2, 0, 1300478, 23197, 2933, 1048576⟩
    (by decide) selected_cut_46621

theorem selected_cut_46622 : selected 11 ⟨1300515, by decide⟩
    (prefixPartial 10 23198) = some ⟨10, 2, 0, 1300515, 23198, 1333, 1048576⟩ := by
  decide +kernel

theorem context_10_23198_1300515 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23198 ⟨1300515, by decide⟩ :=
  accepted_of_selected 10 23198 ⟨1300515, by decide⟩ ⟨10, 2, 0, 1300515, 23198, 1333, 1048576⟩
    (by decide) selected_cut_46622

theorem selected_cut_46623 : selected 11 ⟨1300529, by decide⟩
    (prefixPartial 10 23199) = some ⟨10, 2, 0, 1300529, 23199, 313, 1048576⟩ := by
  decide +kernel

theorem context_10_23199_1300529 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23199 ⟨1300529, by decide⟩ :=
  accepted_of_selected 10 23199 ⟨1300529, by decide⟩ ⟨10, 2, 0, 1300529, 23199, 313, 1048576⟩
    (by decide) selected_cut_46623

theorem unmarked_context_9_5799_1300530 : frontier 12 ⟨1300530, by decide⟩
    (prefixCache 9 5799) (prefixPartial 9 5799) = false := by
  decide +kernel

theorem node_context_9_5799_1300530 : EJMOriginalGlobalDAGData.nodes 12 ⟨1300530, by decide⟩ =
    .split (coordinate 9) (![⟨1300417, by decide⟩,⟨1300478, by decide⟩,⟨1300515, by decide⟩,⟨1300529, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5799_1300530 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5799 ⟨1300530, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5799
    ⟨1300530, by decide⟩ (by decide) (![⟨1300417, by decide⟩,⟨1300478, by decide⟩,⟨1300515, by decide⟩,⟨1300529, by decide⟩]) unmarked_context_9_5799_1300530 node_context_9_5799_1300530
  intro a
  fin_cases a
  · exact context_10_23196_1300417
  · exact context_10_23197_1300478
  · exact context_10_23198_1300515
  · exact context_10_23199_1300529

theorem unmarked_context_8_1449_1300531 : frontier 13 ⟨1300531, by decide⟩
    (prefixCache 8 1449) (prefixPartial 8 1449) = false := by
  decide +kernel

theorem node_context_8_1449_1300531 : EJMOriginalGlobalDAGData.nodes 13 ⟨1300531, by decide⟩ =
    .split (coordinate 8) (![⟨1299160, by decide⟩,⟨1299860, by decide⟩,⟨1300296, by decide⟩,⟨1300530, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1449_1300531 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1449 ⟨1300531, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1449
    ⟨1300531, by decide⟩ (by decide) (![⟨1299160, by decide⟩,⟨1299860, by decide⟩,⟨1300296, by decide⟩,⟨1300530, by decide⟩]) unmarked_context_8_1449_1300531 node_context_8_1449_1300531
  intro a
  fin_cases a
  · exact context_9_5796_1299160
  · exact context_9_5797_1299860
  · exact context_9_5798_1300296
  · exact context_9_5799_1300530

theorem selected_cut_46624 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 92800) = some ⟨11, 1, 0, 434745, 92800, 1, 262144⟩ := by
  decide +kernel

theorem context_11_92800_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92800 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 92800 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 92800, 1, 262144⟩
    (by decide) selected_cut_46624

theorem selected_cut_46625 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 371204) = some ⟨12, 1, 0, 448748, 371204, 1, 65536⟩ := by
  decide +kernel

theorem context_12_371204_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371204 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 371204 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 371204, 1, 65536⟩
    (by decide) selected_cut_46625

theorem selected_cut_46626 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 371205) = some ⟨12, 1, 0, 34034, 371205, 1, 65536⟩ := by
  decide +kernel

theorem context_12_371205_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371205 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 371205 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 371205, 1, 65536⟩
    (by decide) selected_cut_46626

theorem selected_cut_46627 : selected 9 ⟨1300595, by decide⟩
    (prefixPartial 12 371206) = some ⟨12, 2, 0, 1300595, 371206, 1613, 65536⟩ := by
  decide +kernel

theorem context_12_371206_1300595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371206 ⟨1300595, by decide⟩ :=
  accepted_of_selected 12 371206 ⟨1300595, by decide⟩ ⟨12, 2, 0, 1300595, 371206, 1613, 65536⟩
    (by decide) selected_cut_46627

theorem selected_cut_46628 : selected 9 ⟨1300691, by decide⟩
    (prefixPartial 12 371207) = some ⟨12, 2, 0, 1300691, 371207, 3909, 65536⟩ := by
  decide +kernel

theorem context_12_371207_1300691 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371207 ⟨1300691, by decide⟩ :=
  accepted_of_selected 12 371207 ⟨1300691, by decide⟩ ⟨12, 2, 0, 1300691, 371207, 3909, 65536⟩
    (by decide) selected_cut_46628

theorem unmarked_context_11_92801_1300692 : frontier 10 ⟨1300692, by decide⟩
    (prefixCache 11 92801) (prefixPartial 11 92801) = false := by
  decide +kernel

theorem node_context_11_92801_1300692 : EJMOriginalGlobalDAGData.nodes 10 ⟨1300692, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1300595, by decide⟩,⟨1300691, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92801_1300692 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92801 ⟨1300692, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92801
    ⟨1300692, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1300595, by decide⟩,⟨1300691, by decide⟩]) unmarked_context_11_92801_1300692 node_context_11_92801_1300692
  intro a
  fin_cases a
  · exact context_12_371204_448748
  · exact context_12_371205_34034
  · exact context_12_371206_1300595
  · exact context_12_371207_1300691

theorem selected_cut_46629 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 371208) = some ⟨12, 1, 0, 448748, 371208, 1, 65536⟩ := by
  decide +kernel

theorem context_12_371208_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371208 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 371208 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 371208, 1, 65536⟩
    (by decide) selected_cut_46629

theorem selected_cut_46630 : selected 9 ⟨1300774, by decide⟩
    (prefixPartial 12 371209) = some ⟨12, 2, 0, 1300774, 371209, 3293, 65536⟩ := by
  decide +kernel

theorem context_12_371209_1300774 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371209 ⟨1300774, by decide⟩ :=
  accepted_of_selected 12 371209 ⟨1300774, by decide⟩ ⟨12, 2, 0, 1300774, 371209, 3293, 65536⟩
    (by decide) selected_cut_46630

theorem selected_cut_46631 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 371210) = some ⟨12, 1, 0, 893903, 371210, 1, 65536⟩ := by
  decide +kernel

theorem context_12_371210_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371210 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 371210 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 371210, 1, 65536⟩
    (by decide) selected_cut_46631

theorem selected_cut_46632 : selected 9 ⟨1300848, by decide⟩
    (prefixPartial 12 371211) = some ⟨12, 2, 0, 1300848, 371211, 3333, 65536⟩ := by
  decide +kernel

theorem context_12_371211_1300848 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371211 ⟨1300848, by decide⟩ :=
  accepted_of_selected 12 371211 ⟨1300848, by decide⟩ ⟨12, 2, 0, 1300848, 371211, 3333, 65536⟩
    (by decide) selected_cut_46632

theorem unmarked_context_11_92802_1300849 : frontier 10 ⟨1300849, by decide⟩
    (prefixCache 11 92802) (prefixPartial 11 92802) = false := by
  decide +kernel

theorem node_context_11_92802_1300849 : EJMOriginalGlobalDAGData.nodes 10 ⟨1300849, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1300774, by decide⟩,⟨893903, by decide⟩,⟨1300848, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92802_1300849 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92802 ⟨1300849, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92802
    ⟨1300849, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1300774, by decide⟩,⟨893903, by decide⟩,⟨1300848, by decide⟩]) unmarked_context_11_92802_1300849 node_context_11_92802_1300849
  intro a
  fin_cases a
  · exact context_12_371208_448748
  · exact context_12_371209_1300774
  · exact context_12_371210_893903
  · exact context_12_371211_1300848

theorem selected_cut_46633 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 371212) = some ⟨12, 1, 0, 448748, 371212, 1, 65536⟩ := by
  decide +kernel

theorem context_12_371212_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371212 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 371212 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 371212, 1, 65536⟩
    (by decide) selected_cut_46633

theorem selected_cut_46634 : selected 9 ⟨1300924, by decide⟩
    (prefixPartial 12 371213) = some ⟨12, 2, 0, 1300924, 371213, 3253, 65536⟩ := by
  decide +kernel

theorem context_12_371213_1300924 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371213 ⟨1300924, by decide⟩ :=
  accepted_of_selected 12 371213 ⟨1300924, by decide⟩ ⟨12, 2, 0, 1300924, 371213, 3253, 65536⟩
    (by decide) selected_cut_46634

theorem selected_cut_46635 : selected 9 ⟨1300977, by decide⟩
    (prefixPartial 12 371214) = some ⟨12, 2, 0, 1300977, 371214, 2501, 65536⟩ := by
  decide +kernel

theorem context_12_371214_1300977 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371214 ⟨1300977, by decide⟩ :=
  accepted_of_selected 12 371214 ⟨1300977, by decide⟩ ⟨12, 2, 0, 1300977, 371214, 2501, 65536⟩
    (by decide) selected_cut_46635

theorem selected_cut_46636 : selected 9 ⟨1301044, by decide⟩
    (prefixPartial 12 371215) = some ⟨12, 2, 0, 1301044, 371215, 3077, 65536⟩ := by
  decide +kernel

theorem context_12_371215_1301044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371215 ⟨1301044, by decide⟩ :=
  accepted_of_selected 12 371215 ⟨1301044, by decide⟩ ⟨12, 2, 0, 1301044, 371215, 3077, 65536⟩
    (by decide) selected_cut_46636

theorem unmarked_context_11_92803_1301045 : frontier 10 ⟨1301045, by decide⟩
    (prefixCache 11 92803) (prefixPartial 11 92803) = false := by
  decide +kernel

theorem node_context_11_92803_1301045 : EJMOriginalGlobalDAGData.nodes 10 ⟨1301045, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1300924, by decide⟩,⟨1300977, by decide⟩,⟨1301044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92803_1301045 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92803 ⟨1301045, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92803
    ⟨1301045, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1300924, by decide⟩,⟨1300977, by decide⟩,⟨1301044, by decide⟩]) unmarked_context_11_92803_1301045 node_context_11_92803_1301045
  intro a
  fin_cases a
  · exact context_12_371212_448748
  · exact context_12_371213_1300924
  · exact context_12_371214_1300977
  · exact context_12_371215_1301044

theorem unmarked_context_10_23200_1301046 : frontier 11 ⟨1301046, by decide⟩
    (prefixCache 10 23200) (prefixPartial 10 23200) = false := by
  decide +kernel

theorem node_context_10_23200_1301046 : EJMOriginalGlobalDAGData.nodes 11 ⟨1301046, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨1300692, by decide⟩,⟨1300849, by decide⟩,⟨1301045, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23200_1301046 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23200 ⟨1301046, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23200
    ⟨1301046, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨1300692, by decide⟩,⟨1300849, by decide⟩,⟨1301045, by decide⟩]) unmarked_context_10_23200_1301046 node_context_10_23200_1301046
  intro a
  fin_cases a
  · exact context_11_92800_434745
  · exact context_11_92801_1300692
  · exact context_11_92802_1300849
  · exact context_11_92803_1301045

theorem selected_cut_46637 : selected 9 ⟨1255011, by decide⟩
    (prefixPartial 12 371216) = some ⟨12, 1, 0, 1255011, 371216, 1, 65536⟩ := by
  decide +kernel

theorem context_12_371216_1255011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371216 ⟨1255011, by decide⟩ :=
  accepted_of_selected 12 371216 ⟨1255011, by decide⟩ ⟨12, 1, 0, 1255011, 371216, 1, 65536⟩
    (by decide) selected_cut_46637

theorem selected_cut_46638 : selected 9 ⟨1301112, by decide⟩
    (prefixPartial 12 371217) = some ⟨12, 2, 0, 1301112, 371217, 2837, 65536⟩ := by
  decide +kernel

theorem context_12_371217_1301112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371217 ⟨1301112, by decide⟩ :=
  accepted_of_selected 12 371217 ⟨1301112, by decide⟩ ⟨12, 2, 0, 1301112, 371217, 2837, 65536⟩
    (by decide) selected_cut_46638

theorem selected_cut_46639 : selected 9 ⟨1301150, by decide⟩
    (prefixPartial 12 371218) = some ⟨12, 2, 0, 1301150, 371218, 2369, 65536⟩ := by
  decide +kernel

theorem context_12_371218_1301150 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371218 ⟨1301150, by decide⟩ :=
  accepted_of_selected 12 371218 ⟨1301150, by decide⟩ ⟨12, 2, 0, 1301150, 371218, 2369, 65536⟩
    (by decide) selected_cut_46639

theorem selected_cut_46640 : selected 9 ⟨1301213, by decide⟩
    (prefixPartial 12 371219) = some ⟨12, 2, 0, 1301213, 371219, 3357, 65536⟩ := by
  decide +kernel

theorem context_12_371219_1301213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371219 ⟨1301213, by decide⟩ :=
  accepted_of_selected 12 371219 ⟨1301213, by decide⟩ ⟨12, 2, 0, 1301213, 371219, 3357, 65536⟩
    (by decide) selected_cut_46640

theorem unmarked_context_11_92804_1301214 : frontier 10 ⟨1301214, by decide⟩
    (prefixCache 11 92804) (prefixPartial 11 92804) = false := by
  decide +kernel

theorem node_context_11_92804_1301214 : EJMOriginalGlobalDAGData.nodes 10 ⟨1301214, by decide⟩ =
    .split (coordinate 11) (![⟨1255011, by decide⟩,⟨1301112, by decide⟩,⟨1301150, by decide⟩,⟨1301213, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92804_1301214 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92804 ⟨1301214, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92804
    ⟨1301214, by decide⟩ (by decide) (![⟨1255011, by decide⟩,⟨1301112, by decide⟩,⟨1301150, by decide⟩,⟨1301213, by decide⟩]) unmarked_context_11_92804_1301214 node_context_11_92804_1301214
  intro a
  fin_cases a
  · exact context_12_371216_1255011
  · exact context_12_371217_1301112
  · exact context_12_371218_1301150
  · exact context_12_371219_1301213

theorem selected_cut_46641 : selected 9 ⟨1301287, by decide⟩
    (prefixPartial 12 371220) = some ⟨12, 2, 0, 1301287, 371220, 3057, 65536⟩ := by
  decide +kernel

theorem context_12_371220_1301287 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371220 ⟨1301287, by decide⟩ :=
  accepted_of_selected 12 371220 ⟨1301287, by decide⟩ ⟨12, 2, 0, 1301287, 371220, 3057, 65536⟩
    (by decide) selected_cut_46641

theorem selected_cut_46642 : selected 9 ⟨1118965, by decide⟩
    (prefixPartial 12 371221) = some ⟨12, 1, 0, 1118965, 371221, 1, 65536⟩ := by
  decide +kernel

theorem context_12_371221_1118965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371221 ⟨1118965, by decide⟩ :=
  accepted_of_selected 12 371221 ⟨1118965, by decide⟩ ⟨12, 1, 0, 1118965, 371221, 1, 65536⟩
    (by decide) selected_cut_46642

theorem selected_cut_46643 : selected 9 ⟨692793, by decide⟩
    (prefixPartial 12 371222) = some ⟨12, 1, 0, 692793, 371222, 1, 65536⟩ := by
  decide +kernel

theorem context_12_371222_692793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371222 ⟨692793, by decide⟩ :=
  accepted_of_selected 12 371222 ⟨692793, by decide⟩ ⟨12, 1, 0, 692793, 371222, 1, 65536⟩
    (by decide) selected_cut_46643

theorem selected_cut_46644 : selected 9 ⟨1301374, by decide⟩
    (prefixPartial 12 371223) = some ⟨12, 2, 0, 1301374, 371223, 3661, 65536⟩ := by
  decide +kernel

theorem context_12_371223_1301374 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371223 ⟨1301374, by decide⟩ :=
  accepted_of_selected 12 371223 ⟨1301374, by decide⟩ ⟨12, 2, 0, 1301374, 371223, 3661, 65536⟩
    (by decide) selected_cut_46644

theorem unmarked_context_11_92805_1301375 : frontier 10 ⟨1301375, by decide⟩
    (prefixCache 11 92805) (prefixPartial 11 92805) = false := by
  decide +kernel

theorem node_context_11_92805_1301375 : EJMOriginalGlobalDAGData.nodes 10 ⟨1301375, by decide⟩ =
    .split (coordinate 11) (![⟨1301287, by decide⟩,⟨1118965, by decide⟩,⟨692793, by decide⟩,⟨1301374, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92805_1301375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92805 ⟨1301375, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92805
    ⟨1301375, by decide⟩ (by decide) (![⟨1301287, by decide⟩,⟨1118965, by decide⟩,⟨692793, by decide⟩,⟨1301374, by decide⟩]) unmarked_context_11_92805_1301375 node_context_11_92805_1301375
  intro a
  fin_cases a
  · exact context_12_371220_1301287
  · exact context_12_371221_1118965
  · exact context_12_371222_692793
  · exact context_12_371223_1301374

theorem selected_cut_46645 : selected 9 ⟨994572, by decide⟩
    (prefixPartial 12 371224) = some ⟨12, 1, 0, 994572, 371224, 1, 65536⟩ := by
  decide +kernel

theorem context_12_371224_994572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371224 ⟨994572, by decide⟩ :=
  accepted_of_selected 12 371224 ⟨994572, by decide⟩ ⟨12, 1, 0, 994572, 371224, 1, 65536⟩
    (by decide) selected_cut_46645

theorem selected_cut_46646 : selected 9 ⟨1301422, by decide⟩
    (prefixPartial 12 371225) = some ⟨12, 2, 0, 1301422, 371225, 2517, 65536⟩ := by
  decide +kernel

theorem context_12_371225_1301422 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371225 ⟨1301422, by decide⟩ :=
  accepted_of_selected 12 371225 ⟨1301422, by decide⟩ ⟨12, 2, 0, 1301422, 371225, 2517, 65536⟩
    (by decide) selected_cut_46646

theorem selected_cut_46647 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 371226) = some ⟨12, 1, 0, 893903, 371226, 1, 65536⟩ := by
  decide +kernel

theorem context_12_371226_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371226 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 371226 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 371226, 1, 65536⟩
    (by decide) selected_cut_46647

theorem selected_cut_46648 : selected 9 ⟨1301479, by decide⟩
    (prefixPartial 12 371227) = some ⟨12, 2, 0, 1301479, 371227, 2825, 65536⟩ := by
  decide +kernel

theorem context_12_371227_1301479 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371227 ⟨1301479, by decide⟩ :=
  accepted_of_selected 12 371227 ⟨1301479, by decide⟩ ⟨12, 2, 0, 1301479, 371227, 2825, 65536⟩
    (by decide) selected_cut_46648

theorem unmarked_context_11_92806_1301480 : frontier 10 ⟨1301480, by decide⟩
    (prefixCache 11 92806) (prefixPartial 11 92806) = false := by
  decide +kernel

theorem node_context_11_92806_1301480 : EJMOriginalGlobalDAGData.nodes 10 ⟨1301480, by decide⟩ =
    .split (coordinate 11) (![⟨994572, by decide⟩,⟨1301422, by decide⟩,⟨893903, by decide⟩,⟨1301479, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92806_1301480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92806 ⟨1301480, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92806
    ⟨1301480, by decide⟩ (by decide) (![⟨994572, by decide⟩,⟨1301422, by decide⟩,⟨893903, by decide⟩,⟨1301479, by decide⟩]) unmarked_context_11_92806_1301480 node_context_11_92806_1301480
  intro a
  fin_cases a
  · exact context_12_371224_994572
  · exact context_12_371225_1301422
  · exact context_12_371226_893903
  · exact context_12_371227_1301479

theorem selected_cut_46649 : selected 9 ⟨1301529, by decide⟩
    (prefixPartial 12 371228) = some ⟨12, 2, 0, 1301529, 371228, 2517, 65536⟩ := by
  decide +kernel

theorem context_12_371228_1301529 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371228 ⟨1301529, by decide⟩ :=
  accepted_of_selected 12 371228 ⟨1301529, by decide⟩ ⟨12, 2, 0, 1301529, 371228, 2517, 65536⟩
    (by decide) selected_cut_46649

theorem selected_cut_46650 : selected 9 ⟨1301579, by decide⟩
    (prefixPartial 12 371229) = some ⟨12, 2, 0, 1301579, 371229, 2573, 65536⟩ := by
  decide +kernel

theorem context_12_371229_1301579 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371229 ⟨1301579, by decide⟩ :=
  accepted_of_selected 12 371229 ⟨1301579, by decide⟩ ⟨12, 2, 0, 1301579, 371229, 2573, 65536⟩
    (by decide) selected_cut_46650

theorem selected_cut_46651 : selected 9 ⟨1301611, by decide⟩
    (prefixPartial 12 371230) = some ⟨12, 2, 0, 1301611, 371230, 2149, 65536⟩ := by
  decide +kernel

theorem context_12_371230_1301611 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371230 ⟨1301611, by decide⟩ :=
  accepted_of_selected 12 371230 ⟨1301611, by decide⟩ ⟨12, 2, 0, 1301611, 371230, 2149, 65536⟩
    (by decide) selected_cut_46651

theorem selected_cut_46652 : selected 9 ⟨1301665, by decide⟩
    (prefixPartial 12 371231) = some ⟨12, 2, 0, 1301665, 371231, 2681, 65536⟩ := by
  decide +kernel

theorem context_12_371231_1301665 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371231 ⟨1301665, by decide⟩ :=
  accepted_of_selected 12 371231 ⟨1301665, by decide⟩ ⟨12, 2, 0, 1301665, 371231, 2681, 65536⟩
    (by decide) selected_cut_46652

theorem unmarked_context_11_92807_1301666 : frontier 10 ⟨1301666, by decide⟩
    (prefixCache 11 92807) (prefixPartial 11 92807) = false := by
  decide +kernel

theorem node_context_11_92807_1301666 : EJMOriginalGlobalDAGData.nodes 10 ⟨1301666, by decide⟩ =
    .split (coordinate 11) (![⟨1301529, by decide⟩,⟨1301579, by decide⟩,⟨1301611, by decide⟩,⟨1301665, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92807_1301666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92807 ⟨1301666, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92807
    ⟨1301666, by decide⟩ (by decide) (![⟨1301529, by decide⟩,⟨1301579, by decide⟩,⟨1301611, by decide⟩,⟨1301665, by decide⟩]) unmarked_context_11_92807_1301666 node_context_11_92807_1301666
  intro a
  fin_cases a
  · exact context_12_371228_1301529
  · exact context_12_371229_1301579
  · exact context_12_371230_1301611
  · exact context_12_371231_1301665

theorem unmarked_context_10_23201_1301667 : frontier 11 ⟨1301667, by decide⟩
    (prefixCache 10 23201) (prefixPartial 10 23201) = false := by
  decide +kernel

theorem node_context_10_23201_1301667 : EJMOriginalGlobalDAGData.nodes 11 ⟨1301667, by decide⟩ =
    .split (coordinate 10) (![⟨1301214, by decide⟩,⟨1301375, by decide⟩,⟨1301480, by decide⟩,⟨1301666, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23201_1301667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23201 ⟨1301667, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23201
    ⟨1301667, by decide⟩ (by decide) (![⟨1301214, by decide⟩,⟨1301375, by decide⟩,⟨1301480, by decide⟩,⟨1301666, by decide⟩]) unmarked_context_10_23201_1301667 node_context_10_23201_1301667
  intro a
  fin_cases a
  · exact context_11_92804_1301214
  · exact context_11_92805_1301375
  · exact context_11_92806_1301480
  · exact context_11_92807_1301666

theorem selected_cut_46653 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 371232) = some ⟨12, 1, 0, 435790, 371232, 1, 65536⟩ := by
  decide +kernel

theorem context_12_371232_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371232 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 371232 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 371232, 1, 65536⟩
    (by decide) selected_cut_46653

theorem selected_cut_46654 : selected 9 ⟨1301707, by decide⟩
    (prefixPartial 12 371233) = some ⟨12, 2, 0, 1301707, 371233, 2085, 65536⟩ := by
  decide +kernel

theorem context_12_371233_1301707 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371233 ⟨1301707, by decide⟩ :=
  accepted_of_selected 12 371233 ⟨1301707, by decide⟩ ⟨12, 2, 0, 1301707, 371233, 2085, 65536⟩
    (by decide) selected_cut_46654

theorem selected_cut_46655 : selected 9 ⟨1301743, by decide⟩
    (prefixPartial 12 371234) = some ⟨12, 2, 0, 1301743, 371234, 1749, 65536⟩ := by
  decide +kernel

theorem context_12_371234_1301743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371234 ⟨1301743, by decide⟩ :=
  accepted_of_selected 12 371234 ⟨1301743, by decide⟩ ⟨12, 2, 0, 1301743, 371234, 1749, 65536⟩
    (by decide) selected_cut_46655

theorem selected_cut_46656 : selected 9 ⟨1301794, by decide⟩
    (prefixPartial 12 371235) = some ⟨12, 2, 0, 1301794, 371235, 2305, 65536⟩ := by
  decide +kernel

theorem context_12_371235_1301794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371235 ⟨1301794, by decide⟩ :=
  accepted_of_selected 12 371235 ⟨1301794, by decide⟩ ⟨12, 2, 0, 1301794, 371235, 2305, 65536⟩
    (by decide) selected_cut_46656

theorem unmarked_context_11_92808_1301795 : frontier 10 ⟨1301795, by decide⟩
    (prefixCache 11 92808) (prefixPartial 11 92808) = false := by
  decide +kernel

theorem node_context_11_92808_1301795 : EJMOriginalGlobalDAGData.nodes 10 ⟨1301795, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨1301707, by decide⟩,⟨1301743, by decide⟩,⟨1301794, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92808_1301795 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92808 ⟨1301795, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92808
    ⟨1301795, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨1301707, by decide⟩,⟨1301743, by decide⟩,⟨1301794, by decide⟩]) unmarked_context_11_92808_1301795 node_context_11_92808_1301795
  intro a
  fin_cases a
  · exact context_12_371232_435790
  · exact context_12_371233_1301707
  · exact context_12_371234_1301743
  · exact context_12_371235_1301794

theorem selected_cut_46657 : selected 9 ⟨450498, by decide⟩
    (prefixPartial 12 371236) = some ⟨12, 1, 0, 450498, 371236, 1, 65536⟩ := by
  decide +kernel

theorem context_12_371236_450498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371236 ⟨450498, by decide⟩ :=
  accepted_of_selected 12 371236 ⟨450498, by decide⟩ ⟨12, 1, 0, 450498, 371236, 1, 65536⟩
    (by decide) selected_cut_46657

theorem selected_cut_46658 : selected 9 ⟨688903, by decide⟩
    (prefixPartial 12 371237) = some ⟨12, 1, 0, 688903, 371237, 1, 65536⟩ := by
  decide +kernel

theorem context_12_371237_688903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371237 ⟨688903, by decide⟩ :=
  accepted_of_selected 12 371237 ⟨688903, by decide⟩ ⟨12, 1, 0, 688903, 371237, 1, 65536⟩
    (by decide) selected_cut_46658

theorem selected_cut_46659 : selected 9 ⟨1301830, by decide⟩
    (prefixPartial 12 371238) = some ⟨12, 2, 0, 1301830, 371238, 1833, 65536⟩ := by
  decide +kernel

theorem context_12_371238_1301830 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371238 ⟨1301830, by decide⟩ :=
  accepted_of_selected 12 371238 ⟨1301830, by decide⟩ ⟨12, 2, 0, 1301830, 371238, 1833, 65536⟩
    (by decide) selected_cut_46659

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
