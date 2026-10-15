/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover100
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_11_6155_267818 : frontier 10 ⟨267818, by decide⟩
    (prefixCache 11 6155) (prefixPartial 11 6155) = false := by
  decide +kernel

theorem node_context_11_6155_267818 : EJMOriginalGlobalDAGData.nodes 10 ⟨267818, by decide⟩ =
    .split (coordinate 11) (![⟨267665, by decide⟩,⟨267719, by decide⟩,⟨267772, by decide⟩,⟨267817, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6155_267818 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6155 ⟨267818, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6155
    ⟨267818, by decide⟩ (by decide) (![⟨267665, by decide⟩,⟨267719, by decide⟩,⟨267772, by decide⟩,⟨267817, by decide⟩]) unmarked_context_11_6155_267818 node_context_11_6155_267818
  intro a
  fin_cases a
  · exact context_12_24620_267665
  · exact context_12_24621_267719
  · exact context_12_24622_267772
  · exact context_12_24623_267817

theorem unmarked_context_10_1538_267819 : frontier 11 ⟨267819, by decide⟩
    (prefixCache 10 1538) (prefixPartial 10 1538) = false := by
  decide +kernel

theorem node_context_10_1538_267819 : EJMOriginalGlobalDAGData.nodes 11 ⟨267819, by decide⟩ =
    .split (coordinate 10) (![⟨267221, by decide⟩,⟨267428, by decide⟩,⟨267623, by decide⟩,⟨267818, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1538_267819 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1538 ⟨267819, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1538
    ⟨267819, by decide⟩ (by decide) (![⟨267221, by decide⟩,⟨267428, by decide⟩,⟨267623, by decide⟩,⟨267818, by decide⟩]) unmarked_context_10_1538_267819 node_context_10_1538_267819
  intro a
  fin_cases a
  · exact context_11_6152_267221
  · exact context_11_6153_267428
  · exact context_11_6154_267623
  · exact context_11_6155_267818

theorem selected_cut_09699 : selected 9 ⟨267906, by decide⟩
    (prefixPartial 12 24624) = some ⟨12, 2, 0, 267906, 24624, 3297, 65536⟩ := by
  decide +kernel

theorem context_12_24624_267906 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24624 ⟨267906, by decide⟩ :=
  accepted_of_selected 12 24624 ⟨267906, by decide⟩ ⟨12, 2, 0, 267906, 24624, 3297, 65536⟩
    (by decide) selected_cut_09699

theorem selected_cut_09700 : selected 9 ⟨267944, by decide⟩
    (prefixPartial 12 24625) = some ⟨12, 2, 0, 267944, 24625, 2701, 65536⟩ := by
  decide +kernel

theorem context_12_24625_267944 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24625 ⟨267944, by decide⟩ :=
  accepted_of_selected 12 24625 ⟨267944, by decide⟩ ⟨12, 2, 0, 267944, 24625, 2701, 65536⟩
    (by decide) selected_cut_09700

theorem selected_cut_09701 : selected 9 ⟨267977, by decide⟩
    (prefixPartial 12 24626) = some ⟨12, 2, 0, 267977, 24626, 2621, 65536⟩ := by
  decide +kernel

theorem context_12_24626_267977 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24626 ⟨267977, by decide⟩ :=
  accepted_of_selected 12 24626 ⟨267977, by decide⟩ ⟨12, 2, 0, 267977, 24626, 2621, 65536⟩
    (by decide) selected_cut_09701

theorem selected_cut_09702 : selected 9 ⟨268023, by decide⟩
    (prefixPartial 12 24627) = some ⟨12, 2, 0, 268023, 24627, 3149, 65536⟩ := by
  decide +kernel

theorem context_12_24627_268023 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24627 ⟨268023, by decide⟩ :=
  accepted_of_selected 12 24627 ⟨268023, by decide⟩ ⟨12, 2, 0, 268023, 24627, 3149, 65536⟩
    (by decide) selected_cut_09702

theorem unmarked_context_11_6156_268024 : frontier 10 ⟨268024, by decide⟩
    (prefixCache 11 6156) (prefixPartial 11 6156) = false := by
  decide +kernel

theorem node_context_11_6156_268024 : EJMOriginalGlobalDAGData.nodes 10 ⟨268024, by decide⟩ =
    .split (coordinate 11) (![⟨267906, by decide⟩,⟨267944, by decide⟩,⟨267977, by decide⟩,⟨268023, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6156_268024 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6156 ⟨268024, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6156
    ⟨268024, by decide⟩ (by decide) (![⟨267906, by decide⟩,⟨267944, by decide⟩,⟨267977, by decide⟩,⟨268023, by decide⟩]) unmarked_context_11_6156_268024 node_context_11_6156_268024
  intro a
  fin_cases a
  · exact context_12_24624_267906
  · exact context_12_24625_267944
  · exact context_12_24626_267977
  · exact context_12_24627_268023

theorem selected_cut_09703 : selected 9 ⟨268071, by decide⟩
    (prefixPartial 12 24628) = some ⟨12, 2, 0, 268071, 24628, 3373, 65536⟩ := by
  decide +kernel

theorem context_12_24628_268071 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24628 ⟨268071, by decide⟩ :=
  accepted_of_selected 12 24628 ⟨268071, by decide⟩ ⟨12, 2, 0, 268071, 24628, 3373, 65536⟩
    (by decide) selected_cut_09703

theorem selected_cut_09704 : selected 9 ⟨268113, by decide⟩
    (prefixPartial 12 24629) = some ⟨12, 2, 0, 268113, 24629, 3557, 65536⟩ := by
  decide +kernel

theorem context_12_24629_268113 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24629 ⟨268113, by decide⟩ :=
  accepted_of_selected 12 24629 ⟨268113, by decide⟩ ⟨12, 2, 0, 268113, 24629, 3557, 65536⟩
    (by decide) selected_cut_09704

theorem selected_cut_09705 : selected 9 ⟨268162, by decide⟩
    (prefixPartial 12 24630) = some ⟨12, 2, 0, 268162, 24630, 3745, 65536⟩ := by
  decide +kernel

theorem context_12_24630_268162 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24630 ⟨268162, by decide⟩ :=
  accepted_of_selected 12 24630 ⟨268162, by decide⟩ ⟨12, 2, 0, 268162, 24630, 3745, 65536⟩
    (by decide) selected_cut_09705

theorem selected_cut_09706 : selected 8 ⟨268168, by decide⟩
    (prefixPartial 13 98524) = some ⟨13, 2, 0, 268168, 98524, 317, 16384⟩ := by
  decide +kernel

theorem context_13_98524_268168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98524 ⟨268168, by decide⟩ :=
  accepted_of_selected 13 98524 ⟨268168, by decide⟩ ⟨13, 2, 0, 268168, 98524, 317, 16384⟩
    (by decide) selected_cut_09706

theorem selected_cut_09707 : selected 8 ⟨268193, by decide⟩
    (prefixPartial 13 98525) = some ⟨13, 2, 0, 268193, 98525, 2057, 16384⟩ := by
  decide +kernel

theorem context_13_98525_268193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98525 ⟨268193, by decide⟩ :=
  accepted_of_selected 13 98525 ⟨268193, by decide⟩ ⟨13, 2, 0, 268193, 98525, 2057, 16384⟩
    (by decide) selected_cut_09707

theorem selected_cut_09708 : selected 8 ⟨268209, by decide⟩
    (prefixPartial 13 98526) = some ⟨13, 2, 0, 268209, 98526, 1233, 16384⟩ := by
  decide +kernel

theorem context_13_98526_268209 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98526 ⟨268209, by decide⟩ :=
  accepted_of_selected 13 98526 ⟨268209, by decide⟩ ⟨13, 2, 0, 268209, 98526, 1233, 16384⟩
    (by decide) selected_cut_09708

theorem selected_cut_09709 : selected 8 ⟨268217, by decide⟩
    (prefixPartial 13 98527) = some ⟨13, 2, 0, 268217, 98527, 789, 16384⟩ := by
  decide +kernel

theorem context_13_98527_268217 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98527 ⟨268217, by decide⟩ :=
  accepted_of_selected 13 98527 ⟨268217, by decide⟩ ⟨13, 2, 0, 268217, 98527, 789, 16384⟩
    (by decide) selected_cut_09709

theorem unmarked_context_12_24631_268218 : frontier 9 ⟨268218, by decide⟩
    (prefixCache 12 24631) (prefixPartial 12 24631) = false := by
  decide +kernel

theorem node_context_12_24631_268218 : EJMOriginalGlobalDAGData.nodes 9 ⟨268218, by decide⟩ =
    .split (coordinate 12) (![⟨268168, by decide⟩,⟨268193, by decide⟩,⟨268209, by decide⟩,⟨268217, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24631_268218 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24631 ⟨268218, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24631
    ⟨268218, by decide⟩ (by decide) (![⟨268168, by decide⟩,⟨268193, by decide⟩,⟨268209, by decide⟩,⟨268217, by decide⟩]) unmarked_context_12_24631_268218 node_context_12_24631_268218
  intro a
  fin_cases a
  · exact context_13_98524_268168
  · exact context_13_98525_268193
  · exact context_13_98526_268209
  · exact context_13_98527_268217

theorem unmarked_context_11_6157_268219 : frontier 10 ⟨268219, by decide⟩
    (prefixCache 11 6157) (prefixPartial 11 6157) = false := by
  decide +kernel

theorem node_context_11_6157_268219 : EJMOriginalGlobalDAGData.nodes 10 ⟨268219, by decide⟩ =
    .split (coordinate 11) (![⟨268071, by decide⟩,⟨268113, by decide⟩,⟨268162, by decide⟩,⟨268218, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6157_268219 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6157 ⟨268219, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6157
    ⟨268219, by decide⟩ (by decide) (![⟨268071, by decide⟩,⟨268113, by decide⟩,⟨268162, by decide⟩,⟨268218, by decide⟩]) unmarked_context_11_6157_268219 node_context_11_6157_268219
  intro a
  fin_cases a
  · exact context_12_24628_268071
  · exact context_12_24629_268113
  · exact context_12_24630_268162
  · exact context_12_24631_268218

theorem selected_cut_09710 : selected 9 ⟨268266, by decide⟩
    (prefixPartial 12 24632) = some ⟨12, 2, 0, 268266, 24632, 3669, 65536⟩ := by
  decide +kernel

theorem context_12_24632_268266 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24632 ⟨268266, by decide⟩ :=
  accepted_of_selected 12 24632 ⟨268266, by decide⟩ ⟨12, 2, 0, 268266, 24632, 3669, 65536⟩
    (by decide) selected_cut_09710

theorem selected_cut_09711 : selected 9 ⟨268313, by decide⟩
    (prefixPartial 12 24633) = some ⟨12, 2, 0, 268313, 24633, 3897, 65536⟩ := by
  decide +kernel

theorem context_12_24633_268313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24633 ⟨268313, by decide⟩ :=
  accepted_of_selected 12 24633 ⟨268313, by decide⟩ ⟨12, 2, 0, 268313, 24633, 3897, 65536⟩
    (by decide) selected_cut_09711

theorem selected_cut_09712 : selected 9 ⟨268357, by decide⟩
    (prefixPartial 12 24634) = some ⟨12, 2, 0, 268357, 24634, 3537, 65536⟩ := by
  decide +kernel

theorem context_12_24634_268357 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24634 ⟨268357, by decide⟩ :=
  accepted_of_selected 12 24634 ⟨268357, by decide⟩ ⟨12, 2, 0, 268357, 24634, 3537, 65536⟩
    (by decide) selected_cut_09712

theorem selected_cut_09713 : selected 8 ⟨268363, by decide⟩
    (prefixPartial 13 98540) = some ⟨13, 2, 0, 268363, 98540, 189, 16384⟩ := by
  decide +kernel

theorem context_13_98540_268363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98540 ⟨268363, by decide⟩ :=
  accepted_of_selected 13 98540 ⟨268363, by decide⟩ ⟨13, 2, 0, 268363, 98540, 189, 16384⟩
    (by decide) selected_cut_09713

theorem selected_cut_09714 : selected 8 ⟨268392, by decide⟩
    (prefixPartial 13 98541) = some ⟨13, 2, 0, 268392, 98541, 2149, 16384⟩ := by
  decide +kernel

theorem context_13_98541_268392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98541 ⟨268392, by decide⟩ :=
  accepted_of_selected 13 98541 ⟨268392, by decide⟩ ⟨13, 2, 0, 268392, 98541, 2149, 16384⟩
    (by decide) selected_cut_09714

theorem selected_cut_09715 : selected 8 ⟨268407, by decide⟩
    (prefixPartial 13 98542) = some ⟨13, 2, 0, 268407, 98542, 1261, 16384⟩ := by
  decide +kernel

theorem context_13_98542_268407 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98542 ⟨268407, by decide⟩ :=
  accepted_of_selected 13 98542 ⟨268407, by decide⟩ ⟨13, 2, 0, 268407, 98542, 1261, 16384⟩
    (by decide) selected_cut_09715

theorem selected_cut_09716 : selected 8 ⟨268417, by decide⟩
    (prefixPartial 13 98543) = some ⟨13, 2, 0, 268417, 98543, 737, 16384⟩ := by
  decide +kernel

theorem context_13_98543_268417 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98543 ⟨268417, by decide⟩ :=
  accepted_of_selected 13 98543 ⟨268417, by decide⟩ ⟨13, 2, 0, 268417, 98543, 737, 16384⟩
    (by decide) selected_cut_09716

theorem unmarked_context_12_24635_268418 : frontier 9 ⟨268418, by decide⟩
    (prefixCache 12 24635) (prefixPartial 12 24635) = false := by
  decide +kernel

theorem node_context_12_24635_268418 : EJMOriginalGlobalDAGData.nodes 9 ⟨268418, by decide⟩ =
    .split (coordinate 12) (![⟨268363, by decide⟩,⟨268392, by decide⟩,⟨268407, by decide⟩,⟨268417, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24635_268418 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24635 ⟨268418, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24635
    ⟨268418, by decide⟩ (by decide) (![⟨268363, by decide⟩,⟨268392, by decide⟩,⟨268407, by decide⟩,⟨268417, by decide⟩]) unmarked_context_12_24635_268418 node_context_12_24635_268418
  intro a
  fin_cases a
  · exact context_13_98540_268363
  · exact context_13_98541_268392
  · exact context_13_98542_268407
  · exact context_13_98543_268417

theorem unmarked_context_11_6158_268419 : frontier 10 ⟨268419, by decide⟩
    (prefixCache 11 6158) (prefixPartial 11 6158) = false := by
  decide +kernel

theorem node_context_11_6158_268419 : EJMOriginalGlobalDAGData.nodes 10 ⟨268419, by decide⟩ =
    .split (coordinate 11) (![⟨268266, by decide⟩,⟨268313, by decide⟩,⟨268357, by decide⟩,⟨268418, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6158_268419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6158 ⟨268419, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6158
    ⟨268419, by decide⟩ (by decide) (![⟨268266, by decide⟩,⟨268313, by decide⟩,⟨268357, by decide⟩,⟨268418, by decide⟩]) unmarked_context_11_6158_268419 node_context_11_6158_268419
  intro a
  fin_cases a
  · exact context_12_24632_268266
  · exact context_12_24633_268313
  · exact context_12_24634_268357
  · exact context_12_24635_268418

theorem selected_cut_09717 : selected 9 ⟨268457, by decide⟩
    (prefixPartial 12 24636) = some ⟨12, 2, 0, 268457, 24636, 3077, 65536⟩ := by
  decide +kernel

theorem context_12_24636_268457 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24636 ⟨268457, by decide⟩ :=
  accepted_of_selected 12 24636 ⟨268457, by decide⟩ ⟨12, 2, 0, 268457, 24636, 3077, 65536⟩
    (by decide) selected_cut_09717

theorem selected_cut_09718 : selected 9 ⟨268509, by decide⟩
    (prefixPartial 12 24637) = some ⟨12, 2, 0, 268509, 24637, 3717, 65536⟩ := by
  decide +kernel

theorem context_12_24637_268509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24637 ⟨268509, by decide⟩ :=
  accepted_of_selected 12 24637 ⟨268509, by decide⟩ ⟨12, 2, 0, 268509, 24637, 3717, 65536⟩
    (by decide) selected_cut_09718

theorem selected_cut_09719 : selected 9 ⟨268554, by decide⟩
    (prefixPartial 12 24638) = some ⟨12, 2, 0, 268554, 24638, 3597, 65536⟩ := by
  decide +kernel

theorem context_12_24638_268554 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24638 ⟨268554, by decide⟩ :=
  accepted_of_selected 12 24638 ⟨268554, by decide⟩ ⟨12, 2, 0, 268554, 24638, 3597, 65536⟩
    (by decide) selected_cut_09719

theorem selected_cut_09720 : selected 9 ⟨268613, by decide⟩
    (prefixPartial 12 24639) = some ⟨12, 2, 0, 268613, 24639, 4001, 65536⟩ := by
  decide +kernel

theorem context_12_24639_268613 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24639 ⟨268613, by decide⟩ :=
  accepted_of_selected 12 24639 ⟨268613, by decide⟩ ⟨12, 2, 0, 268613, 24639, 4001, 65536⟩
    (by decide) selected_cut_09720

theorem unmarked_context_11_6159_268614 : frontier 10 ⟨268614, by decide⟩
    (prefixCache 11 6159) (prefixPartial 11 6159) = false := by
  decide +kernel

theorem node_context_11_6159_268614 : EJMOriginalGlobalDAGData.nodes 10 ⟨268614, by decide⟩ =
    .split (coordinate 11) (![⟨268457, by decide⟩,⟨268509, by decide⟩,⟨268554, by decide⟩,⟨268613, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6159_268614 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6159 ⟨268614, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6159
    ⟨268614, by decide⟩ (by decide) (![⟨268457, by decide⟩,⟨268509, by decide⟩,⟨268554, by decide⟩,⟨268613, by decide⟩]) unmarked_context_11_6159_268614 node_context_11_6159_268614
  intro a
  fin_cases a
  · exact context_12_24636_268457
  · exact context_12_24637_268509
  · exact context_12_24638_268554
  · exact context_12_24639_268613

theorem unmarked_context_10_1539_268615 : frontier 11 ⟨268615, by decide⟩
    (prefixCache 10 1539) (prefixPartial 10 1539) = false := by
  decide +kernel

theorem node_context_10_1539_268615 : EJMOriginalGlobalDAGData.nodes 11 ⟨268615, by decide⟩ =
    .split (coordinate 10) (![⟨268024, by decide⟩,⟨268219, by decide⟩,⟨268419, by decide⟩,⟨268614, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1539_268615 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1539 ⟨268615, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1539
    ⟨268615, by decide⟩ (by decide) (![⟨268024, by decide⟩,⟨268219, by decide⟩,⟨268419, by decide⟩,⟨268614, by decide⟩]) unmarked_context_10_1539_268615 node_context_10_1539_268615
  intro a
  fin_cases a
  · exact context_11_6156_268024
  · exact context_11_6157_268219
  · exact context_11_6158_268419
  · exact context_11_6159_268614

theorem unmarked_context_9_384_268616 : frontier 12 ⟨268616, by decide⟩
    (prefixCache 9 384) (prefixPartial 9 384) = false := by
  decide +kernel

theorem node_context_9_384_268616 : EJMOriginalGlobalDAGData.nodes 12 ⟨268616, by decide⟩ =
    .split (coordinate 9) (![⟨266169, by decide⟩,⟨267020, by decide⟩,⟨267819, by decide⟩,⟨268615, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_384_268616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 384 ⟨268616, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 384
    ⟨268616, by decide⟩ (by decide) (![⟨266169, by decide⟩,⟨267020, by decide⟩,⟨267819, by decide⟩,⟨268615, by decide⟩]) unmarked_context_9_384_268616 node_context_9_384_268616
  intro a
  fin_cases a
  · exact context_10_1536_266169
  · exact context_10_1537_267020
  · exact context_10_1538_267819
  · exact context_10_1539_268615

theorem selected_cut_09721 : selected 9 ⟨169790, by decide⟩
    (prefixPartial 12 24640) = some ⟨12, 1, 0, 169790, 24640, 1, 65536⟩ := by
  decide +kernel

theorem context_12_24640_169790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24640 ⟨169790, by decide⟩ :=
  accepted_of_selected 12 24640 ⟨169790, by decide⟩ ⟨12, 1, 0, 169790, 24640, 1, 65536⟩
    (by decide) selected_cut_09721

theorem selected_cut_09722 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 98564) = some ⟨13, 1, 0, 3444, 98564, 1, 16384⟩ := by
  decide +kernel

theorem context_13_98564_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98564 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 98564 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 98564, 1, 16384⟩
    (by decide) selected_cut_09722

theorem selected_cut_09723 : selected 8 ⟨268675, by decide⟩
    (prefixPartial 13 98565) = some ⟨13, 2, 0, 268675, 98565, 3693, 16384⟩ := by
  decide +kernel

theorem context_13_98565_268675 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98565 ⟨268675, by decide⟩ :=
  accepted_of_selected 13 98565 ⟨268675, by decide⟩ ⟨13, 2, 0, 268675, 98565, 3693, 16384⟩
    (by decide) selected_cut_09723

theorem selected_cut_09724 : selected 8 ⟨268710, by decide⟩
    (prefixPartial 13 98566) = some ⟨13, 2, 0, 268710, 98566, 2521, 16384⟩ := by
  decide +kernel

theorem context_13_98566_268710 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98566 ⟨268710, by decide⟩ :=
  accepted_of_selected 13 98566 ⟨268710, by decide⟩ ⟨13, 2, 0, 268710, 98566, 2521, 16384⟩
    (by decide) selected_cut_09724

theorem selected_cut_09725 : selected 8 ⟨268718, by decide⟩
    (prefixPartial 13 98567) = some ⟨13, 2, 0, 268718, 98567, 1165, 16384⟩ := by
  decide +kernel

theorem context_13_98567_268718 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98567 ⟨268718, by decide⟩ :=
  accepted_of_selected 13 98567 ⟨268718, by decide⟩ ⟨13, 2, 0, 268718, 98567, 1165, 16384⟩
    (by decide) selected_cut_09725

theorem unmarked_context_12_24641_268719 : frontier 9 ⟨268719, by decide⟩
    (prefixCache 12 24641) (prefixPartial 12 24641) = false := by
  decide +kernel

theorem node_context_12_24641_268719 : EJMOriginalGlobalDAGData.nodes 9 ⟨268719, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨268675, by decide⟩,⟨268710, by decide⟩,⟨268718, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24641_268719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24641 ⟨268719, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24641
    ⟨268719, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨268675, by decide⟩,⟨268710, by decide⟩,⟨268718, by decide⟩]) unmarked_context_12_24641_268719 node_context_12_24641_268719
  intro a
  fin_cases a
  · exact context_13_98564_3444
  · exact context_13_98565_268675
  · exact context_13_98566_268710
  · exact context_13_98567_268718

theorem selected_cut_09726 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 98568) = some ⟨13, 1, 0, 3444, 98568, 1, 16384⟩ := by
  decide +kernel

theorem context_13_98568_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98568 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 98568 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 98568, 1, 16384⟩
    (by decide) selected_cut_09726

theorem selected_cut_09727 : selected 8 ⟨268758, by decide⟩
    (prefixPartial 13 98569) = some ⟨13, 2, 0, 268758, 98569, 3093, 16384⟩ := by
  decide +kernel

theorem context_13_98569_268758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98569 ⟨268758, by decide⟩ :=
  accepted_of_selected 13 98569 ⟨268758, by decide⟩ ⟨13, 2, 0, 268758, 98569, 3093, 16384⟩
    (by decide) selected_cut_09727

theorem selected_cut_09728 : selected 8 ⟨268780, by decide⟩
    (prefixPartial 13 98570) = some ⟨13, 2, 0, 268780, 98570, 1673, 16384⟩ := by
  decide +kernel

theorem context_13_98570_268780 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98570 ⟨268780, by decide⟩ :=
  accepted_of_selected 13 98570 ⟨268780, by decide⟩ ⟨13, 2, 0, 268780, 98570, 1673, 16384⟩
    (by decide) selected_cut_09728

theorem selected_cut_09729 : selected 8 ⟨268789, by decide⟩
    (prefixPartial 13 98571) = some ⟨13, 2, 0, 268789, 98571, 1009, 16384⟩ := by
  decide +kernel

theorem context_13_98571_268789 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98571 ⟨268789, by decide⟩ :=
  accepted_of_selected 13 98571 ⟨268789, by decide⟩ ⟨13, 2, 0, 268789, 98571, 1009, 16384⟩
    (by decide) selected_cut_09729

theorem unmarked_context_12_24642_268790 : frontier 9 ⟨268790, by decide⟩
    (prefixCache 12 24642) (prefixPartial 12 24642) = false := by
  decide +kernel

theorem node_context_12_24642_268790 : EJMOriginalGlobalDAGData.nodes 9 ⟨268790, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨268758, by decide⟩,⟨268780, by decide⟩,⟨268789, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24642_268790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24642 ⟨268790, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24642
    ⟨268790, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨268758, by decide⟩,⟨268780, by decide⟩,⟨268789, by decide⟩]) unmarked_context_12_24642_268790 node_context_12_24642_268790
  intro a
  fin_cases a
  · exact context_13_98568_3444
  · exact context_13_98569_268758
  · exact context_13_98570_268780
  · exact context_13_98571_268789

theorem selected_cut_09730 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 98572) = some ⟨13, 1, 0, 3444, 98572, 1, 16384⟩ := by
  decide +kernel

theorem context_13_98572_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98572 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 98572 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 98572, 1, 16384⟩
    (by decide) selected_cut_09730

theorem selected_cut_09731 : selected 8 ⟨268837, by decide⟩
    (prefixPartial 13 98573) = some ⟨13, 2, 0, 268837, 98573, 3189, 16384⟩ := by
  decide +kernel

theorem context_13_98573_268837 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98573 ⟨268837, by decide⟩ :=
  accepted_of_selected 13 98573 ⟨268837, by decide⟩ ⟨13, 2, 0, 268837, 98573, 3189, 16384⟩
    (by decide) selected_cut_09731

theorem selected_cut_09732 : selected 8 ⟨268862, by decide⟩
    (prefixPartial 13 98574) = some ⟨13, 2, 0, 268862, 98574, 2053, 16384⟩ := by
  decide +kernel

theorem context_13_98574_268862 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98574 ⟨268862, by decide⟩ :=
  accepted_of_selected 13 98574 ⟨268862, by decide⟩ ⟨13, 2, 0, 268862, 98574, 2053, 16384⟩
    (by decide) selected_cut_09732

theorem selected_cut_09733 : selected 8 ⟨268873, by decide⟩
    (prefixPartial 13 98575) = some ⟨13, 2, 0, 268873, 98575, 993, 16384⟩ := by
  decide +kernel

theorem context_13_98575_268873 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98575 ⟨268873, by decide⟩ :=
  accepted_of_selected 13 98575 ⟨268873, by decide⟩ ⟨13, 2, 0, 268873, 98575, 993, 16384⟩
    (by decide) selected_cut_09733

theorem unmarked_context_12_24643_268874 : frontier 9 ⟨268874, by decide⟩
    (prefixCache 12 24643) (prefixPartial 12 24643) = false := by
  decide +kernel

theorem node_context_12_24643_268874 : EJMOriginalGlobalDAGData.nodes 9 ⟨268874, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨268837, by decide⟩,⟨268862, by decide⟩,⟨268873, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24643_268874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24643 ⟨268874, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24643
    ⟨268874, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨268837, by decide⟩,⟨268862, by decide⟩,⟨268873, by decide⟩]) unmarked_context_12_24643_268874 node_context_12_24643_268874
  intro a
  fin_cases a
  · exact context_13_98572_3444
  · exact context_13_98573_268837
  · exact context_13_98574_268862
  · exact context_13_98575_268873

theorem unmarked_context_11_6160_268875 : frontier 10 ⟨268875, by decide⟩
    (prefixCache 11 6160) (prefixPartial 11 6160) = false := by
  decide +kernel

theorem node_context_11_6160_268875 : EJMOriginalGlobalDAGData.nodes 10 ⟨268875, by decide⟩ =
    .split (coordinate 11) (![⟨169790, by decide⟩,⟨268719, by decide⟩,⟨268790, by decide⟩,⟨268874, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6160_268875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6160 ⟨268875, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6160
    ⟨268875, by decide⟩ (by decide) (![⟨169790, by decide⟩,⟨268719, by decide⟩,⟨268790, by decide⟩,⟨268874, by decide⟩]) unmarked_context_11_6160_268875 node_context_11_6160_268875
  intro a
  fin_cases a
  · exact context_12_24640_169790
  · exact context_12_24641_268719
  · exact context_12_24642_268790
  · exact context_12_24643_268874

theorem selected_cut_09734 : selected 9 ⟨268916, by decide⟩
    (prefixPartial 12 24644) = some ⟨12, 2, 0, 268916, 24644, 3029, 65536⟩ := by
  decide +kernel

theorem context_12_24644_268916 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24644 ⟨268916, by decide⟩ :=
  accepted_of_selected 12 24644 ⟨268916, by decide⟩ ⟨12, 2, 0, 268916, 24644, 3029, 65536⟩
    (by decide) selected_cut_09734

theorem selected_cut_09735 : selected 9 ⟨268917, by decide⟩
    (prefixPartial 12 24645) = some ⟨12, 1, 0, 268917, 24645, 1, 65536⟩ := by
  decide +kernel

theorem context_12_24645_268917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24645 ⟨268917, by decide⟩ :=
  accepted_of_selected 12 24645 ⟨268917, by decide⟩ ⟨12, 1, 0, 268917, 24645, 1, 65536⟩
    (by decide) selected_cut_09735

theorem selected_cut_09736 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 98584) = some ⟨13, 1, 0, 3444, 98584, 1, 16384⟩ := by
  decide +kernel

theorem context_13_98584_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98584 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 98584 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 98584, 1, 16384⟩
    (by decide) selected_cut_09736

theorem selected_cut_09737 : selected 8 ⟨268937, by decide⟩
    (prefixPartial 13 98585) = some ⟨13, 2, 0, 268937, 98585, 2405, 16384⟩ := by
  decide +kernel

theorem context_13_98585_268937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98585 ⟨268937, by decide⟩ :=
  accepted_of_selected 13 98585 ⟨268937, by decide⟩ ⟨13, 2, 0, 268937, 98585, 2405, 16384⟩
    (by decide) selected_cut_09737

theorem selected_cut_09738 : selected 8 ⟨268958, by decide⟩
    (prefixPartial 13 98586) = some ⟨13, 2, 0, 268958, 98586, 1401, 16384⟩ := by
  decide +kernel

theorem context_13_98586_268958 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98586 ⟨268958, by decide⟩ :=
  accepted_of_selected 13 98586 ⟨268958, by decide⟩ ⟨13, 2, 0, 268958, 98586, 1401, 16384⟩
    (by decide) selected_cut_09738

theorem selected_cut_09739 : selected 8 ⟨268967, by decide⟩
    (prefixPartial 13 98587) = some ⟨13, 2, 0, 268967, 98587, 777, 16384⟩ := by
  decide +kernel

theorem context_13_98587_268967 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98587 ⟨268967, by decide⟩ :=
  accepted_of_selected 13 98587 ⟨268967, by decide⟩ ⟨13, 2, 0, 268967, 98587, 777, 16384⟩
    (by decide) selected_cut_09739

theorem unmarked_context_12_24646_268968 : frontier 9 ⟨268968, by decide⟩
    (prefixCache 12 24646) (prefixPartial 12 24646) = false := by
  decide +kernel

theorem node_context_12_24646_268968 : EJMOriginalGlobalDAGData.nodes 9 ⟨268968, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨268937, by decide⟩,⟨268958, by decide⟩,⟨268967, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24646_268968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24646 ⟨268968, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24646
    ⟨268968, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨268937, by decide⟩,⟨268958, by decide⟩,⟨268967, by decide⟩]) unmarked_context_12_24646_268968 node_context_12_24646_268968
  intro a
  fin_cases a
  · exact context_13_98584_3444
  · exact context_13_98585_268937
  · exact context_13_98586_268958
  · exact context_13_98587_268967

theorem selected_cut_09740 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 98588) = some ⟨13, 1, 0, 3444, 98588, 1, 16384⟩ := by
  decide +kernel

theorem context_13_98588_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98588 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 98588 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 98588, 1, 16384⟩
    (by decide) selected_cut_09740

theorem selected_cut_09741 : selected 8 ⟨268992, by decide⟩
    (prefixPartial 13 98589) = some ⟨13, 2, 0, 268992, 98589, 2469, 16384⟩ := by
  decide +kernel

theorem context_13_98589_268992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98589 ⟨268992, by decide⟩ :=
  accepted_of_selected 13 98589 ⟨268992, by decide⟩ ⟨13, 2, 0, 268992, 98589, 2469, 16384⟩
    (by decide) selected_cut_09741

theorem selected_cut_09742 : selected 8 ⟨269014, by decide⟩
    (prefixPartial 13 98590) = some ⟨13, 2, 0, 269014, 98590, 1641, 16384⟩ := by
  decide +kernel

theorem context_13_98590_269014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98590 ⟨269014, by decide⟩ :=
  accepted_of_selected 13 98590 ⟨269014, by decide⟩ ⟨13, 2, 0, 269014, 98590, 1641, 16384⟩
    (by decide) selected_cut_09742

theorem selected_cut_09743 : selected 8 ⟨269023, by decide⟩
    (prefixPartial 13 98591) = some ⟨13, 2, 0, 269023, 98591, 877, 16384⟩ := by
  decide +kernel

theorem context_13_98591_269023 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98591 ⟨269023, by decide⟩ :=
  accepted_of_selected 13 98591 ⟨269023, by decide⟩ ⟨13, 2, 0, 269023, 98591, 877, 16384⟩
    (by decide) selected_cut_09743

theorem unmarked_context_12_24647_269024 : frontier 9 ⟨269024, by decide⟩
    (prefixCache 12 24647) (prefixPartial 12 24647) = false := by
  decide +kernel

theorem node_context_12_24647_269024 : EJMOriginalGlobalDAGData.nodes 9 ⟨269024, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨268992, by decide⟩,⟨269014, by decide⟩,⟨269023, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24647_269024 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24647 ⟨269024, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24647
    ⟨269024, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨268992, by decide⟩,⟨269014, by decide⟩,⟨269023, by decide⟩]) unmarked_context_12_24647_269024 node_context_12_24647_269024
  intro a
  fin_cases a
  · exact context_13_98588_3444
  · exact context_13_98589_268992
  · exact context_13_98590_269014
  · exact context_13_98591_269023

theorem unmarked_context_11_6161_269025 : frontier 10 ⟨269025, by decide⟩
    (prefixCache 11 6161) (prefixPartial 11 6161) = false := by
  decide +kernel

theorem node_context_11_6161_269025 : EJMOriginalGlobalDAGData.nodes 10 ⟨269025, by decide⟩ =
    .split (coordinate 11) (![⟨268916, by decide⟩,⟨268917, by decide⟩,⟨268968, by decide⟩,⟨269024, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6161_269025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6161 ⟨269025, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6161
    ⟨269025, by decide⟩ (by decide) (![⟨268916, by decide⟩,⟨268917, by decide⟩,⟨268968, by decide⟩,⟨269024, by decide⟩]) unmarked_context_11_6161_269025 node_context_11_6161_269025
  intro a
  fin_cases a
  · exact context_12_24644_268916
  · exact context_12_24645_268917
  · exact context_12_24646_268968
  · exact context_12_24647_269024

theorem selected_cut_09744 : selected 9 ⟨269066, by decide⟩
    (prefixPartial 12 24648) = some ⟨12, 2, 0, 269066, 24648, 3345, 65536⟩ := by
  decide +kernel

theorem context_12_24648_269066 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24648 ⟨269066, by decide⟩ :=
  accepted_of_selected 12 24648 ⟨269066, by decide⟩ ⟨12, 2, 0, 269066, 24648, 3345, 65536⟩
    (by decide) selected_cut_09744

theorem selected_cut_09745 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 98596) = some ⟨13, 1, 0, 3444, 98596, 1, 16384⟩ := by
  decide +kernel

theorem context_13_98596_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98596 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 98596 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 98596, 1, 16384⟩
    (by decide) selected_cut_09745

theorem selected_cut_09746 : selected 8 ⟨269090, by decide⟩
    (prefixPartial 13 98597) = some ⟨13, 2, 0, 269090, 98597, 2685, 16384⟩ := by
  decide +kernel

theorem context_13_98597_269090 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98597 ⟨269090, by decide⟩ :=
  accepted_of_selected 13 98597 ⟨269090, by decide⟩ ⟨13, 2, 0, 269090, 98597, 2685, 16384⟩
    (by decide) selected_cut_09746

theorem selected_cut_09747 : selected 8 ⟨269114, by decide⟩
    (prefixPartial 13 98598) = some ⟨13, 2, 0, 269114, 98598, 2201, 16384⟩ := by
  decide +kernel

theorem context_13_98598_269114 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98598 ⟨269114, by decide⟩ :=
  accepted_of_selected 13 98598 ⟨269114, by decide⟩ ⟨13, 2, 0, 269114, 98598, 2201, 16384⟩
    (by decide) selected_cut_09747

theorem selected_cut_09748 : selected 8 ⟨269122, by decide⟩
    (prefixPartial 13 98599) = some ⟨13, 2, 0, 269122, 98599, 985, 16384⟩ := by
  decide +kernel

theorem context_13_98599_269122 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98599 ⟨269122, by decide⟩ :=
  accepted_of_selected 13 98599 ⟨269122, by decide⟩ ⟨13, 2, 0, 269122, 98599, 985, 16384⟩
    (by decide) selected_cut_09748

theorem unmarked_context_12_24649_269123 : frontier 9 ⟨269123, by decide⟩
    (prefixCache 12 24649) (prefixPartial 12 24649) = false := by
  decide +kernel

theorem node_context_12_24649_269123 : EJMOriginalGlobalDAGData.nodes 9 ⟨269123, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨269090, by decide⟩,⟨269114, by decide⟩,⟨269122, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24649_269123 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24649 ⟨269123, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24649
    ⟨269123, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨269090, by decide⟩,⟨269114, by decide⟩,⟨269122, by decide⟩]) unmarked_context_12_24649_269123 node_context_12_24649_269123
  intro a
  fin_cases a
  · exact context_13_98596_3444
  · exact context_13_98597_269090
  · exact context_13_98598_269114
  · exact context_13_98599_269122

theorem selected_cut_09749 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 98600) = some ⟨13, 1, 0, 3444, 98600, 1, 16384⟩ := by
  decide +kernel

theorem context_13_98600_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98600 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 98600 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 98600, 1, 16384⟩
    (by decide) selected_cut_09749

theorem selected_cut_09750 : selected 8 ⟨269148, by decide⟩
    (prefixPartial 13 98601) = some ⟨13, 2, 0, 269148, 98601, 2073, 16384⟩ := by
  decide +kernel

theorem context_13_98601_269148 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98601 ⟨269148, by decide⟩ :=
  accepted_of_selected 13 98601 ⟨269148, by decide⟩ ⟨13, 2, 0, 269148, 98601, 2073, 16384⟩
    (by decide) selected_cut_09750

theorem selected_cut_09751 : selected 8 ⟨269168, by decide⟩
    (prefixPartial 13 98602) = some ⟨13, 2, 0, 269168, 98602, 1349, 16384⟩ := by
  decide +kernel

theorem context_13_98602_269168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98602 ⟨269168, by decide⟩ :=
  accepted_of_selected 13 98602 ⟨269168, by decide⟩ ⟨13, 2, 0, 269168, 98602, 1349, 16384⟩
    (by decide) selected_cut_09751

theorem selected_cut_09752 : selected 8 ⟨269177, by decide⟩
    (prefixPartial 13 98603) = some ⟨13, 2, 0, 269177, 98603, 821, 16384⟩ := by
  decide +kernel

theorem context_13_98603_269177 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98603 ⟨269177, by decide⟩ :=
  accepted_of_selected 13 98603 ⟨269177, by decide⟩ ⟨13, 2, 0, 269177, 98603, 821, 16384⟩
    (by decide) selected_cut_09752

theorem unmarked_context_12_24650_269178 : frontier 9 ⟨269178, by decide⟩
    (prefixCache 12 24650) (prefixPartial 12 24650) = false := by
  decide +kernel

theorem node_context_12_24650_269178 : EJMOriginalGlobalDAGData.nodes 9 ⟨269178, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨269148, by decide⟩,⟨269168, by decide⟩,⟨269177, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24650_269178 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24650 ⟨269178, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24650
    ⟨269178, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨269148, by decide⟩,⟨269168, by decide⟩,⟨269177, by decide⟩]) unmarked_context_12_24650_269178 node_context_12_24650_269178
  intro a
  fin_cases a
  · exact context_13_98600_3444
  · exact context_13_98601_269148
  · exact context_13_98602_269168
  · exact context_13_98603_269177

theorem selected_cut_09753 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 98604) = some ⟨13, 1, 0, 3444, 98604, 1, 16384⟩ := by
  decide +kernel

theorem context_13_98604_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98604 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 98604 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 98604, 1, 16384⟩
    (by decide) selected_cut_09753

theorem selected_cut_09754 : selected 8 ⟨269203, by decide⟩
    (prefixPartial 13 98605) = some ⟨13, 2, 0, 269203, 98605, 2229, 16384⟩ := by
  decide +kernel

theorem context_13_98605_269203 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98605 ⟨269203, by decide⟩ :=
  accepted_of_selected 13 98605 ⟨269203, by decide⟩ ⟨13, 2, 0, 269203, 98605, 2229, 16384⟩
    (by decide) selected_cut_09754

theorem selected_cut_09755 : selected 8 ⟨269225, by decide⟩
    (prefixPartial 13 98606) = some ⟨13, 2, 0, 269225, 98606, 1785, 16384⟩ := by
  decide +kernel

theorem context_13_98606_269225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98606 ⟨269225, by decide⟩ :=
  accepted_of_selected 13 98606 ⟨269225, by decide⟩ ⟨13, 2, 0, 269225, 98606, 1785, 16384⟩
    (by decide) selected_cut_09755

theorem selected_cut_09756 : selected 8 ⟨269234, by decide⟩
    (prefixPartial 13 98607) = some ⟨13, 2, 0, 269234, 98607, 949, 16384⟩ := by
  decide +kernel

theorem context_13_98607_269234 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98607 ⟨269234, by decide⟩ :=
  accepted_of_selected 13 98607 ⟨269234, by decide⟩ ⟨13, 2, 0, 269234, 98607, 949, 16384⟩
    (by decide) selected_cut_09756

theorem unmarked_context_12_24651_269235 : frontier 9 ⟨269235, by decide⟩
    (prefixCache 12 24651) (prefixPartial 12 24651) = false := by
  decide +kernel

theorem node_context_12_24651_269235 : EJMOriginalGlobalDAGData.nodes 9 ⟨269235, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨269203, by decide⟩,⟨269225, by decide⟩,⟨269234, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24651_269235 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24651 ⟨269235, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24651
    ⟨269235, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨269203, by decide⟩,⟨269225, by decide⟩,⟨269234, by decide⟩]) unmarked_context_12_24651_269235 node_context_12_24651_269235
  intro a
  fin_cases a
  · exact context_13_98604_3444
  · exact context_13_98605_269203
  · exact context_13_98606_269225
  · exact context_13_98607_269234

theorem unmarked_context_11_6162_269236 : frontier 10 ⟨269236, by decide⟩
    (prefixCache 11 6162) (prefixPartial 11 6162) = false := by
  decide +kernel

theorem node_context_11_6162_269236 : EJMOriginalGlobalDAGData.nodes 10 ⟨269236, by decide⟩ =
    .split (coordinate 11) (![⟨269066, by decide⟩,⟨269123, by decide⟩,⟨269178, by decide⟩,⟨269235, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6162_269236 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6162 ⟨269236, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6162
    ⟨269236, by decide⟩ (by decide) (![⟨269066, by decide⟩,⟨269123, by decide⟩,⟨269178, by decide⟩,⟨269235, by decide⟩]) unmarked_context_11_6162_269236 node_context_11_6162_269236
  intro a
  fin_cases a
  · exact context_12_24648_269066
  · exact context_12_24649_269123
  · exact context_12_24650_269178
  · exact context_12_24651_269235

theorem selected_cut_09757 : selected 9 ⟨269274, by decide⟩
    (prefixPartial 12 24652) = some ⟨12, 2, 0, 269274, 24652, 2837, 65536⟩ := by
  decide +kernel

theorem context_12_24652_269274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24652 ⟨269274, by decide⟩ :=
  accepted_of_selected 12 24652 ⟨269274, by decide⟩ ⟨12, 2, 0, 269274, 24652, 2837, 65536⟩
    (by decide) selected_cut_09757

theorem selected_cut_09758 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 98612) = some ⟨13, 1, 0, 3444, 98612, 1, 16384⟩ := by
  decide +kernel

theorem context_13_98612_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98612 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 98612 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 98612, 1, 16384⟩
    (by decide) selected_cut_09758

theorem selected_cut_09759 : selected 8 ⟨269303, by decide⟩
    (prefixPartial 13 98613) = some ⟨13, 2, 0, 269303, 98613, 2441, 16384⟩ := by
  decide +kernel

theorem context_13_98613_269303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98613 ⟨269303, by decide⟩ :=
  accepted_of_selected 13 98613 ⟨269303, by decide⟩ ⟨13, 2, 0, 269303, 98613, 2441, 16384⟩
    (by decide) selected_cut_09759

theorem selected_cut_09760 : selected 8 ⟨269329, by decide⟩
    (prefixPartial 13 98614) = some ⟨13, 2, 0, 269329, 98614, 2077, 16384⟩ := by
  decide +kernel

theorem context_13_98614_269329 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98614 ⟨269329, by decide⟩ :=
  accepted_of_selected 13 98614 ⟨269329, by decide⟩ ⟨13, 2, 0, 269329, 98614, 2077, 16384⟩
    (by decide) selected_cut_09760

theorem selected_cut_09761 : selected 8 ⟨269338, by decide⟩
    (prefixPartial 13 98615) = some ⟨13, 2, 0, 269338, 98615, 1001, 16384⟩ := by
  decide +kernel

theorem context_13_98615_269338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98615 ⟨269338, by decide⟩ :=
  accepted_of_selected 13 98615 ⟨269338, by decide⟩ ⟨13, 2, 0, 269338, 98615, 1001, 16384⟩
    (by decide) selected_cut_09761

theorem unmarked_context_12_24653_269339 : frontier 9 ⟨269339, by decide⟩
    (prefixCache 12 24653) (prefixPartial 12 24653) = false := by
  decide +kernel

theorem node_context_12_24653_269339 : EJMOriginalGlobalDAGData.nodes 9 ⟨269339, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨269303, by decide⟩,⟨269329, by decide⟩,⟨269338, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24653_269339 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24653 ⟨269339, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24653
    ⟨269339, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨269303, by decide⟩,⟨269329, by decide⟩,⟨269338, by decide⟩]) unmarked_context_12_24653_269339 node_context_12_24653_269339
  intro a
  fin_cases a
  · exact context_13_98612_3444
  · exact context_13_98613_269303
  · exact context_13_98614_269329
  · exact context_13_98615_269338

theorem selected_cut_09762 : selected 9 ⟨269390, by decide⟩
    (prefixPartial 12 24654) = some ⟨12, 2, 0, 269390, 24654, 4093, 65536⟩ := by
  decide +kernel

theorem context_12_24654_269390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24654 ⟨269390, by decide⟩ :=
  accepted_of_selected 12 24654 ⟨269390, by decide⟩ ⟨12, 2, 0, 269390, 24654, 4093, 65536⟩
    (by decide) selected_cut_09762

theorem selected_cut_09763 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 98620) = some ⟨13, 1, 0, 3444, 98620, 1, 16384⟩ := by
  decide +kernel

theorem context_13_98620_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98620 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 98620 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 98620, 1, 16384⟩
    (by decide) selected_cut_09763

theorem selected_cut_09764 : selected 8 ⟨269415, by decide⟩
    (prefixPartial 13 98621) = some ⟨13, 2, 0, 269415, 98621, 1905, 16384⟩ := by
  decide +kernel

theorem context_13_98621_269415 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98621 ⟨269415, by decide⟩ :=
  accepted_of_selected 13 98621 ⟨269415, by decide⟩ ⟨13, 2, 0, 269415, 98621, 1905, 16384⟩
    (by decide) selected_cut_09764

theorem selected_cut_09765 : selected 8 ⟨269435, by decide⟩
    (prefixPartial 13 98622) = some ⟨13, 2, 0, 269435, 98622, 1561, 16384⟩ := by
  decide +kernel

theorem context_13_98622_269435 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98622 ⟨269435, by decide⟩ :=
  accepted_of_selected 13 98622 ⟨269435, by decide⟩ ⟨13, 2, 0, 269435, 98622, 1561, 16384⟩
    (by decide) selected_cut_09765

theorem selected_cut_09766 : selected 8 ⟨269444, by decide⟩
    (prefixPartial 13 98623) = some ⟨13, 2, 0, 269444, 98623, 897, 16384⟩ := by
  decide +kernel

theorem context_13_98623_269444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98623 ⟨269444, by decide⟩ :=
  accepted_of_selected 13 98623 ⟨269444, by decide⟩ ⟨13, 2, 0, 269444, 98623, 897, 16384⟩
    (by decide) selected_cut_09766

theorem unmarked_context_12_24655_269445 : frontier 9 ⟨269445, by decide⟩
    (prefixCache 12 24655) (prefixPartial 12 24655) = false := by
  decide +kernel

theorem node_context_12_24655_269445 : EJMOriginalGlobalDAGData.nodes 9 ⟨269445, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨269415, by decide⟩,⟨269435, by decide⟩,⟨269444, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24655_269445 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24655 ⟨269445, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24655
    ⟨269445, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨269415, by decide⟩,⟨269435, by decide⟩,⟨269444, by decide⟩]) unmarked_context_12_24655_269445 node_context_12_24655_269445
  intro a
  fin_cases a
  · exact context_13_98620_3444
  · exact context_13_98621_269415
  · exact context_13_98622_269435
  · exact context_13_98623_269444

theorem unmarked_context_11_6163_269446 : frontier 10 ⟨269446, by decide⟩
    (prefixCache 11 6163) (prefixPartial 11 6163) = false := by
  decide +kernel

theorem node_context_11_6163_269446 : EJMOriginalGlobalDAGData.nodes 10 ⟨269446, by decide⟩ =
    .split (coordinate 11) (![⟨269274, by decide⟩,⟨269339, by decide⟩,⟨269390, by decide⟩,⟨269445, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6163_269446 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6163 ⟨269446, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6163
    ⟨269446, by decide⟩ (by decide) (![⟨269274, by decide⟩,⟨269339, by decide⟩,⟨269390, by decide⟩,⟨269445, by decide⟩]) unmarked_context_11_6163_269446 node_context_11_6163_269446
  intro a
  fin_cases a
  · exact context_12_24652_269274
  · exact context_12_24653_269339
  · exact context_12_24654_269390
  · exact context_12_24655_269445

theorem unmarked_context_10_1540_269447 : frontier 11 ⟨269447, by decide⟩
    (prefixCache 10 1540) (prefixPartial 10 1540) = false := by
  decide +kernel

theorem node_context_10_1540_269447 : EJMOriginalGlobalDAGData.nodes 11 ⟨269447, by decide⟩ =
    .split (coordinate 10) (![⟨268875, by decide⟩,⟨269025, by decide⟩,⟨269236, by decide⟩,⟨269446, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1540_269447 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1540 ⟨269447, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1540
    ⟨269447, by decide⟩ (by decide) (![⟨268875, by decide⟩,⟨269025, by decide⟩,⟨269236, by decide⟩,⟨269446, by decide⟩]) unmarked_context_10_1540_269447 node_context_10_1540_269447
  intro a
  fin_cases a
  · exact context_11_6160_268875
  · exact context_11_6161_269025
  · exact context_11_6162_269236
  · exact context_11_6163_269446

theorem selected_cut_09767 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 98624) = some ⟨13, 1, 0, 3444, 98624, 1, 16384⟩ := by
  decide +kernel

theorem context_13_98624_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98624 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 98624 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 98624, 1, 16384⟩
    (by decide) selected_cut_09767

theorem selected_cut_09768 : selected 8 ⟨269470, by decide⟩
    (prefixPartial 13 98625) = some ⟨13, 2, 0, 269470, 98625, 2189, 16384⟩ := by
  decide +kernel

theorem context_13_98625_269470 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98625 ⟨269470, by decide⟩ :=
  accepted_of_selected 13 98625 ⟨269470, by decide⟩ ⟨13, 2, 0, 269470, 98625, 2189, 16384⟩
    (by decide) selected_cut_09768

theorem selected_cut_09769 : selected 8 ⟨269495, by decide⟩
    (prefixPartial 13 98626) = some ⟨13, 2, 0, 269495, 98626, 2141, 16384⟩ := by
  decide +kernel

theorem context_13_98626_269495 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98626 ⟨269495, by decide⟩ :=
  accepted_of_selected 13 98626 ⟨269495, by decide⟩ ⟨13, 2, 0, 269495, 98626, 2141, 16384⟩
    (by decide) selected_cut_09769

theorem selected_cut_09770 : selected 8 ⟨269503, by decide⟩
    (prefixPartial 13 98627) = some ⟨13, 2, 0, 269503, 98627, 1049, 16384⟩ := by
  decide +kernel

theorem context_13_98627_269503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98627 ⟨269503, by decide⟩ :=
  accepted_of_selected 13 98627 ⟨269503, by decide⟩ ⟨13, 2, 0, 269503, 98627, 1049, 16384⟩
    (by decide) selected_cut_09770

theorem unmarked_context_12_24656_269504 : frontier 9 ⟨269504, by decide⟩
    (prefixCache 12 24656) (prefixPartial 12 24656) = false := by
  decide +kernel

theorem node_context_12_24656_269504 : EJMOriginalGlobalDAGData.nodes 9 ⟨269504, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨269470, by decide⟩,⟨269495, by decide⟩,⟨269503, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24656_269504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24656 ⟨269504, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24656
    ⟨269504, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨269470, by decide⟩,⟨269495, by decide⟩,⟨269503, by decide⟩]) unmarked_context_12_24656_269504 node_context_12_24656_269504
  intro a
  fin_cases a
  · exact context_13_98624_3444
  · exact context_13_98625_269470
  · exact context_13_98626_269495
  · exact context_13_98627_269503

theorem selected_cut_09771 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 24657) = some ⟨12, 1, 0, 170504, 24657, 1, 65536⟩ := by
  decide +kernel

theorem context_12_24657_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24657 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 24657 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 24657, 1, 65536⟩
    (by decide) selected_cut_09771

theorem selected_cut_09772 : selected 9 ⟨269547, by decide⟩
    (prefixPartial 12 24658) = some ⟨12, 2, 0, 269547, 24658, 3641, 65536⟩ := by
  decide +kernel

theorem context_12_24658_269547 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24658 ⟨269547, by decide⟩ :=
  accepted_of_selected 12 24658 ⟨269547, by decide⟩ ⟨12, 2, 0, 269547, 24658, 3641, 65536⟩
    (by decide) selected_cut_09772

theorem selected_cut_09773 : selected 9 ⟨269593, by decide⟩
    (prefixPartial 12 24659) = some ⟨12, 2, 0, 269593, 24659, 3845, 65536⟩ := by
  decide +kernel

theorem context_12_24659_269593 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24659 ⟨269593, by decide⟩ :=
  accepted_of_selected 12 24659 ⟨269593, by decide⟩ ⟨12, 2, 0, 269593, 24659, 3845, 65536⟩
    (by decide) selected_cut_09773

theorem unmarked_context_11_6164_269594 : frontier 10 ⟨269594, by decide⟩
    (prefixCache 11 6164) (prefixPartial 11 6164) = false := by
  decide +kernel

theorem node_context_11_6164_269594 : EJMOriginalGlobalDAGData.nodes 10 ⟨269594, by decide⟩ =
    .split (coordinate 11) (![⟨269504, by decide⟩,⟨170504, by decide⟩,⟨269547, by decide⟩,⟨269593, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6164_269594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6164 ⟨269594, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6164
    ⟨269594, by decide⟩ (by decide) (![⟨269504, by decide⟩,⟨170504, by decide⟩,⟨269547, by decide⟩,⟨269593, by decide⟩]) unmarked_context_11_6164_269594 node_context_11_6164_269594
  intro a
  fin_cases a
  · exact context_12_24656_269504
  · exact context_12_24657_170504
  · exact context_12_24658_269547
  · exact context_12_24659_269593

theorem selected_cut_09774 : selected 9 ⟨269633, by decide⟩
    (prefixPartial 12 24660) = some ⟨12, 2, 0, 269633, 24660, 3269, 65536⟩ := by
  decide +kernel

theorem context_12_24660_269633 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24660 ⟨269633, by decide⟩ :=
  accepted_of_selected 12 24660 ⟨269633, by decide⟩ ⟨12, 2, 0, 269633, 24660, 3269, 65536⟩
    (by decide) selected_cut_09774

theorem selected_cut_09775 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 24661) = some ⟨12, 1, 0, 170504, 24661, 1, 65536⟩ := by
  decide +kernel

theorem context_12_24661_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24661 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 24661 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 24661, 1, 65536⟩
    (by decide) selected_cut_09775

theorem selected_cut_09776 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 98648) = some ⟨13, 1, 0, 3444, 98648, 1, 16384⟩ := by
  decide +kernel

theorem context_13_98648_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98648 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 98648 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 98648, 1, 16384⟩
    (by decide) selected_cut_09776

theorem selected_cut_09777 : selected 8 ⟨269648, by decide⟩
    (prefixPartial 13 98649) = some ⟨13, 2, 0, 269648, 98649, 1789, 16384⟩ := by
  decide +kernel

theorem context_13_98649_269648 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98649 ⟨269648, by decide⟩ :=
  accepted_of_selected 13 98649 ⟨269648, by decide⟩ ⟨13, 2, 0, 269648, 98649, 1789, 16384⟩
    (by decide) selected_cut_09777

theorem selected_cut_09778 : selected 8 ⟨269671, by decide⟩
    (prefixPartial 13 98650) = some ⟨13, 2, 0, 269671, 98650, 1597, 16384⟩ := by
  decide +kernel

theorem context_13_98650_269671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98650 ⟨269671, by decide⟩ :=
  accepted_of_selected 13 98650 ⟨269671, by decide⟩ ⟨13, 2, 0, 269671, 98650, 1597, 16384⟩
    (by decide) selected_cut_09778

theorem selected_cut_09779 : selected 8 ⟨269681, by decide⟩
    (prefixPartial 13 98651) = some ⟨13, 2, 0, 269681, 98651, 937, 16384⟩ := by
  decide +kernel

theorem context_13_98651_269681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98651 ⟨269681, by decide⟩ :=
  accepted_of_selected 13 98651 ⟨269681, by decide⟩ ⟨13, 2, 0, 269681, 98651, 937, 16384⟩
    (by decide) selected_cut_09779

theorem unmarked_context_12_24662_269682 : frontier 9 ⟨269682, by decide⟩
    (prefixCache 12 24662) (prefixPartial 12 24662) = false := by
  decide +kernel

theorem node_context_12_24662_269682 : EJMOriginalGlobalDAGData.nodes 9 ⟨269682, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨269648, by decide⟩,⟨269671, by decide⟩,⟨269681, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24662_269682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24662 ⟨269682, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24662
    ⟨269682, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨269648, by decide⟩,⟨269671, by decide⟩,⟨269681, by decide⟩]) unmarked_context_12_24662_269682 node_context_12_24662_269682
  intro a
  fin_cases a
  · exact context_13_98648_3444
  · exact context_13_98649_269648
  · exact context_13_98650_269671
  · exact context_13_98651_269681

theorem selected_cut_09780 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 98652) = some ⟨13, 1, 0, 3444, 98652, 1, 16384⟩ := by
  decide +kernel

theorem context_13_98652_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98652 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 98652 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 98652, 1, 16384⟩
    (by decide) selected_cut_09780

theorem selected_cut_09781 : selected 8 ⟨269701, by decide⟩
    (prefixPartial 13 98653) = some ⟨13, 2, 0, 269701, 98653, 1789, 16384⟩ := by
  decide +kernel

theorem context_13_98653_269701 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98653 ⟨269701, by decide⟩ :=
  accepted_of_selected 13 98653 ⟨269701, by decide⟩ ⟨13, 2, 0, 269701, 98653, 1789, 16384⟩
    (by decide) selected_cut_09781

theorem selected_cut_09782 : selected 8 ⟨269726, by decide⟩
    (prefixPartial 13 98654) = some ⟨13, 2, 0, 269726, 98654, 1993, 16384⟩ := by
  decide +kernel

theorem context_13_98654_269726 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98654 ⟨269726, by decide⟩ :=
  accepted_of_selected 13 98654 ⟨269726, by decide⟩ ⟨13, 2, 0, 269726, 98654, 1993, 16384⟩
    (by decide) selected_cut_09782

theorem selected_cut_09783 : selected 8 ⟨269737, by decide⟩
    (prefixPartial 13 98655) = some ⟨13, 2, 0, 269737, 98655, 1049, 16384⟩ := by
  decide +kernel

theorem context_13_98655_269737 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98655 ⟨269737, by decide⟩ :=
  accepted_of_selected 13 98655 ⟨269737, by decide⟩ ⟨13, 2, 0, 269737, 98655, 1049, 16384⟩
    (by decide) selected_cut_09783

theorem unmarked_context_12_24663_269738 : frontier 9 ⟨269738, by decide⟩
    (prefixCache 12 24663) (prefixPartial 12 24663) = false := by
  decide +kernel

theorem node_context_12_24663_269738 : EJMOriginalGlobalDAGData.nodes 9 ⟨269738, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨269701, by decide⟩,⟨269726, by decide⟩,⟨269737, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24663_269738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24663 ⟨269738, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24663
    ⟨269738, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨269701, by decide⟩,⟨269726, by decide⟩,⟨269737, by decide⟩]) unmarked_context_12_24663_269738 node_context_12_24663_269738
  intro a
  fin_cases a
  · exact context_13_98652_3444
  · exact context_13_98653_269701
  · exact context_13_98654_269726
  · exact context_13_98655_269737

theorem unmarked_context_11_6165_269739 : frontier 10 ⟨269739, by decide⟩
    (prefixCache 11 6165) (prefixPartial 11 6165) = false := by
  decide +kernel

theorem node_context_11_6165_269739 : EJMOriginalGlobalDAGData.nodes 10 ⟨269739, by decide⟩ =
    .split (coordinate 11) (![⟨269633, by decide⟩,⟨170504, by decide⟩,⟨269682, by decide⟩,⟨269738, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6165_269739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6165 ⟨269739, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6165
    ⟨269739, by decide⟩ (by decide) (![⟨269633, by decide⟩,⟨170504, by decide⟩,⟨269682, by decide⟩,⟨269738, by decide⟩]) unmarked_context_11_6165_269739 node_context_11_6165_269739
  intro a
  fin_cases a
  · exact context_12_24660_269633
  · exact context_12_24661_170504
  · exact context_12_24662_269682
  · exact context_12_24663_269738

theorem selected_cut_09784 : selected 9 ⟨269782, by decide⟩
    (prefixPartial 12 24664) = some ⟨12, 2, 0, 269782, 24664, 3397, 65536⟩ := by
  decide +kernel

theorem context_12_24664_269782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24664 ⟨269782, by decide⟩ :=
  accepted_of_selected 12 24664 ⟨269782, by decide⟩ ⟨12, 2, 0, 269782, 24664, 3397, 65536⟩
    (by decide) selected_cut_09784

theorem selected_cut_09785 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 98660) = some ⟨13, 1, 0, 3444, 98660, 1, 16384⟩ := by
  decide +kernel

theorem context_13_98660_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98660 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 98660 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 98660, 1, 16384⟩
    (by decide) selected_cut_09785

theorem selected_cut_09786 : selected 8 ⟨269811, by decide⟩
    (prefixPartial 13 98661) = some ⟨13, 2, 0, 269811, 98661, 1917, 16384⟩ := by
  decide +kernel

theorem context_13_98661_269811 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98661 ⟨269811, by decide⟩ :=
  accepted_of_selected 13 98661 ⟨269811, by decide⟩ ⟨13, 2, 0, 269811, 98661, 1917, 16384⟩
    (by decide) selected_cut_09786

theorem selected_cut_09787 : selected 8 ⟨269850, by decide⟩
    (prefixPartial 13 98662) = some ⟨13, 2, 0, 269850, 98662, 2425, 16384⟩ := by
  decide +kernel

theorem context_13_98662_269850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98662 ⟨269850, by decide⟩ :=
  accepted_of_selected 13 98662 ⟨269850, by decide⟩ ⟨13, 2, 0, 269850, 98662, 2425, 16384⟩
    (by decide) selected_cut_09787

theorem selected_cut_09788 : selected 8 ⟨269860, by decide⟩
    (prefixPartial 13 98663) = some ⟨13, 2, 0, 269860, 98663, 1113, 16384⟩ := by
  decide +kernel

theorem context_13_98663_269860 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98663 ⟨269860, by decide⟩ :=
  accepted_of_selected 13 98663 ⟨269860, by decide⟩ ⟨13, 2, 0, 269860, 98663, 1113, 16384⟩
    (by decide) selected_cut_09788

theorem unmarked_context_12_24665_269861 : frontier 9 ⟨269861, by decide⟩
    (prefixCache 12 24665) (prefixPartial 12 24665) = false := by
  decide +kernel

theorem node_context_12_24665_269861 : EJMOriginalGlobalDAGData.nodes 9 ⟨269861, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨269811, by decide⟩,⟨269850, by decide⟩,⟨269860, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24665_269861 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24665 ⟨269861, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24665
    ⟨269861, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨269811, by decide⟩,⟨269850, by decide⟩,⟨269860, by decide⟩]) unmarked_context_12_24665_269861 node_context_12_24665_269861
  intro a
  fin_cases a
  · exact context_13_98660_3444
  · exact context_13_98661_269811
  · exact context_13_98662_269850
  · exact context_13_98663_269860

theorem selected_cut_09789 : selected 9 ⟨269904, by decide⟩
    (prefixPartial 12 24666) = some ⟨12, 2, 0, 269904, 24666, 3765, 65536⟩ := by
  decide +kernel

theorem context_12_24666_269904 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24666 ⟨269904, by decide⟩ :=
  accepted_of_selected 12 24666 ⟨269904, by decide⟩ ⟨12, 2, 0, 269904, 24666, 3765, 65536⟩
    (by decide) selected_cut_09789

theorem selected_cut_09790 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 98668) = some ⟨13, 1, 0, 3444, 98668, 1, 16384⟩ := by
  decide +kernel

theorem context_13_98668_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98668 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 98668 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 98668, 1, 16384⟩
    (by decide) selected_cut_09790

theorem selected_cut_09791 : selected 8 ⟨269921, by decide⟩
    (prefixPartial 13 98669) = some ⟨13, 2, 0, 269921, 98669, 1333, 16384⟩ := by
  decide +kernel

theorem context_13_98669_269921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98669 ⟨269921, by decide⟩ :=
  accepted_of_selected 13 98669 ⟨269921, by decide⟩ ⟨13, 2, 0, 269921, 98669, 1333, 16384⟩
    (by decide) selected_cut_09791

theorem selected_cut_09792 : selected 8 ⟨269942, by decide⟩
    (prefixPartial 13 98670) = some ⟨13, 2, 0, 269942, 98670, 1945, 16384⟩ := by
  decide +kernel

theorem context_13_98670_269942 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98670 ⟨269942, by decide⟩ :=
  accepted_of_selected 13 98670 ⟨269942, by decide⟩ ⟨13, 2, 0, 269942, 98670, 1945, 16384⟩
    (by decide) selected_cut_09792

theorem selected_cut_09793 : selected 8 ⟨269950, by decide⟩
    (prefixPartial 13 98671) = some ⟨13, 2, 0, 269950, 98671, 1069, 16384⟩ := by
  decide +kernel

theorem context_13_98671_269950 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 98671 ⟨269950, by decide⟩ :=
  accepted_of_selected 13 98671 ⟨269950, by decide⟩ ⟨13, 2, 0, 269950, 98671, 1069, 16384⟩
    (by decide) selected_cut_09793

theorem unmarked_context_12_24667_269951 : frontier 9 ⟨269951, by decide⟩
    (prefixCache 12 24667) (prefixPartial 12 24667) = false := by
  decide +kernel

theorem node_context_12_24667_269951 : EJMOriginalGlobalDAGData.nodes 9 ⟨269951, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨269921, by decide⟩,⟨269942, by decide⟩,⟨269950, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24667_269951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24667 ⟨269951, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24667
    ⟨269951, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨269921, by decide⟩,⟨269942, by decide⟩,⟨269950, by decide⟩]) unmarked_context_12_24667_269951 node_context_12_24667_269951
  intro a
  fin_cases a
  · exact context_13_98668_3444
  · exact context_13_98669_269921
  · exact context_13_98670_269942
  · exact context_13_98671_269950

theorem unmarked_context_11_6166_269952 : frontier 10 ⟨269952, by decide⟩
    (prefixCache 11 6166) (prefixPartial 11 6166) = false := by
  decide +kernel

theorem node_context_11_6166_269952 : EJMOriginalGlobalDAGData.nodes 10 ⟨269952, by decide⟩ =
    .split (coordinate 11) (![⟨269782, by decide⟩,⟨269861, by decide⟩,⟨269904, by decide⟩,⟨269951, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6166_269952 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6166 ⟨269952, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6166
    ⟨269952, by decide⟩ (by decide) (![⟨269782, by decide⟩,⟨269861, by decide⟩,⟨269904, by decide⟩,⟨269951, by decide⟩]) unmarked_context_11_6166_269952 node_context_11_6166_269952
  intro a
  fin_cases a
  · exact context_12_24664_269782
  · exact context_12_24665_269861
  · exact context_12_24666_269904
  · exact context_12_24667_269951

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
