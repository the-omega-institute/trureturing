/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover141
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_10_1676_356953 : frontier 11 ⟨356953, by decide⟩
    (prefixCache 10 1676) (prefixPartial 10 1676) = false := by
  decide +kernel

theorem node_context_10_1676_356953 : EJMOriginalGlobalDAGData.nodes 11 ⟨356953, by decide⟩ =
    .split (coordinate 10) (![⟨356864, by decide⟩,⟨356894, by decide⟩,⟨356925, by decide⟩,⟨356952, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1676_356953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1676 ⟨356953, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1676
    ⟨356953, by decide⟩ (by decide) (![⟨356864, by decide⟩,⟨356894, by decide⟩,⟨356925, by decide⟩,⟨356952, by decide⟩]) unmarked_context_10_1676_356953 node_context_10_1676_356953
  intro a
  fin_cases a
  · exact context_11_6704_356864
  · exact context_11_6705_356894
  · exact context_11_6706_356925
  · exact context_11_6707_356952

theorem selected_cut_13635 : selected 10 ⟨356995, by decide⟩
    (prefixPartial 11 6708) = some ⟨11, 2, 0, 356995, 6708, 3201, 262144⟩ := by
  decide +kernel

theorem context_11_6708_356995 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6708 ⟨356995, by decide⟩ :=
  accepted_of_selected 11 6708 ⟨356995, by decide⟩ ⟨11, 2, 0, 356995, 6708, 3201, 262144⟩
    (by decide) selected_cut_13635

theorem selected_cut_13636 : selected 10 ⟨357018, by decide⟩
    (prefixPartial 11 6709) = some ⟨11, 2, 0, 357018, 6709, 2529, 262144⟩ := by
  decide +kernel

theorem context_11_6709_357018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6709 ⟨357018, by decide⟩ :=
  accepted_of_selected 11 6709 ⟨357018, by decide⟩ ⟨11, 2, 0, 357018, 6709, 2529, 262144⟩
    (by decide) selected_cut_13636

theorem selected_cut_13637 : selected 10 ⟨357039, by decide⟩
    (prefixPartial 11 6710) = some ⟨11, 2, 0, 357039, 6710, 2197, 262144⟩ := by
  decide +kernel

theorem context_11_6710_357039 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6710 ⟨357039, by decide⟩ :=
  accepted_of_selected 11 6710 ⟨357039, by decide⟩ ⟨11, 2, 0, 357039, 6710, 2197, 262144⟩
    (by decide) selected_cut_13637

theorem selected_cut_13638 : selected 10 ⟨357057, by decide⟩
    (prefixPartial 11 6711) = some ⟨11, 2, 0, 357057, 6711, 1797, 262144⟩ := by
  decide +kernel

theorem context_11_6711_357057 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6711 ⟨357057, by decide⟩ :=
  accepted_of_selected 11 6711 ⟨357057, by decide⟩ ⟨11, 2, 0, 357057, 6711, 1797, 262144⟩
    (by decide) selected_cut_13638

theorem unmarked_context_10_1677_357058 : frontier 11 ⟨357058, by decide⟩
    (prefixCache 10 1677) (prefixPartial 10 1677) = false := by
  decide +kernel

theorem node_context_10_1677_357058 : EJMOriginalGlobalDAGData.nodes 11 ⟨357058, by decide⟩ =
    .split (coordinate 10) (![⟨356995, by decide⟩,⟨357018, by decide⟩,⟨357039, by decide⟩,⟨357057, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1677_357058 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1677 ⟨357058, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1677
    ⟨357058, by decide⟩ (by decide) (![⟨356995, by decide⟩,⟨357018, by decide⟩,⟨357039, by decide⟩,⟨357057, by decide⟩]) unmarked_context_10_1677_357058 node_context_10_1677_357058
  intro a
  fin_cases a
  · exact context_11_6708_356995
  · exact context_11_6709_357018
  · exact context_11_6710_357039
  · exact context_11_6711_357057

theorem selected_cut_13639 : selected 10 ⟨357076, by decide⟩
    (prefixPartial 11 6712) = some ⟨11, 2, 0, 357076, 6712, 1617, 262144⟩ := by
  decide +kernel

theorem context_11_6712_357076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6712 ⟨357076, by decide⟩ :=
  accepted_of_selected 11 6712 ⟨357076, by decide⟩ ⟨11, 2, 0, 357076, 6712, 1617, 262144⟩
    (by decide) selected_cut_13639

theorem selected_cut_13640 : selected 10 ⟨357091, by decide⟩
    (prefixPartial 11 6713) = some ⟨11, 2, 0, 357091, 6713, 1281, 262144⟩ := by
  decide +kernel

theorem context_11_6713_357091 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6713 ⟨357091, by decide⟩ :=
  accepted_of_selected 11 6713 ⟨357091, by decide⟩ ⟨11, 2, 0, 357091, 6713, 1281, 262144⟩
    (by decide) selected_cut_13640

theorem selected_cut_13641 : selected 10 ⟨357105, by decide⟩
    (prefixPartial 11 6714) = some ⟨11, 2, 0, 357105, 6714, 981, 262144⟩ := by
  decide +kernel

theorem context_11_6714_357105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6714 ⟨357105, by decide⟩ :=
  accepted_of_selected 11 6714 ⟨357105, by decide⟩ ⟨11, 2, 0, 357105, 6714, 981, 262144⟩
    (by decide) selected_cut_13641

theorem selected_cut_13642 : selected 10 ⟨357115, by decide⟩
    (prefixPartial 11 6715) = some ⟨11, 2, 0, 357115, 6715, 849, 262144⟩ := by
  decide +kernel

theorem context_11_6715_357115 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6715 ⟨357115, by decide⟩ :=
  accepted_of_selected 11 6715 ⟨357115, by decide⟩ ⟨11, 2, 0, 357115, 6715, 849, 262144⟩
    (by decide) selected_cut_13642

theorem unmarked_context_10_1678_357116 : frontier 11 ⟨357116, by decide⟩
    (prefixCache 10 1678) (prefixPartial 10 1678) = false := by
  decide +kernel

theorem node_context_10_1678_357116 : EJMOriginalGlobalDAGData.nodes 11 ⟨357116, by decide⟩ =
    .split (coordinate 10) (![⟨357076, by decide⟩,⟨357091, by decide⟩,⟨357105, by decide⟩,⟨357115, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1678_357116 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1678 ⟨357116, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1678
    ⟨357116, by decide⟩ (by decide) (![⟨357076, by decide⟩,⟨357091, by decide⟩,⟨357105, by decide⟩,⟨357115, by decide⟩]) unmarked_context_10_1678_357116 node_context_10_1678_357116
  intro a
  fin_cases a
  · exact context_11_6712_357076
  · exact context_11_6713_357091
  · exact context_11_6714_357105
  · exact context_11_6715_357115

theorem selected_cut_13643 : selected 11 ⟨357144, by decide⟩
    (prefixPartial 10 1679) = some ⟨10, 2, 0, 357144, 1679, 1609, 1048576⟩ := by
  decide +kernel

theorem context_10_1679_357144 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1679 ⟨357144, by decide⟩ :=
  accepted_of_selected 10 1679 ⟨357144, by decide⟩ ⟨10, 2, 0, 357144, 1679, 1609, 1048576⟩
    (by decide) selected_cut_13643

theorem unmarked_context_9_419_357145 : frontier 12 ⟨357145, by decide⟩
    (prefixCache 9 419) (prefixPartial 9 419) = false := by
  decide +kernel

theorem node_context_9_419_357145 : EJMOriginalGlobalDAGData.nodes 12 ⟨357145, by decide⟩ =
    .split (coordinate 9) (![⟨356953, by decide⟩,⟨357058, by decide⟩,⟨357116, by decide⟩,⟨357144, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_419_357145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 419 ⟨357145, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 419
    ⟨357145, by decide⟩ (by decide) (![⟨356953, by decide⟩,⟨357058, by decide⟩,⟨357116, by decide⟩,⟨357144, by decide⟩]) unmarked_context_9_419_357145 node_context_9_419_357145
  intro a
  fin_cases a
  · exact context_10_1676_356953
  · exact context_10_1677_357058
  · exact context_10_1678_357116
  · exact context_10_1679_357144

theorem unmarked_context_8_104_357146 : frontier 13 ⟨357146, by decide⟩
    (prefixCache 8 104) (prefixPartial 8 104) = false := by
  decide +kernel

theorem node_context_8_104_357146 : EJMOriginalGlobalDAGData.nodes 13 ⟨357146, by decide⟩ =
    .split (coordinate 8) (![⟨352376, by decide⟩,⟨355611, by decide⟩,⟨356821, by decide⟩,⟨357145, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_104_357146 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 104 ⟨357146, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 104
    ⟨357146, by decide⟩ (by decide) (![⟨352376, by decide⟩,⟨355611, by decide⟩,⟨356821, by decide⟩,⟨357145, by decide⟩]) unmarked_context_8_104_357146 node_context_8_104_357146
  intro a
  fin_cases a
  · exact context_9_416_352376
  · exact context_9_417_355611
  · exact context_9_418_356821
  · exact context_9_419_357145

theorem selected_cut_13644 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 26880) = some ⟨12, 1, 0, 34034, 26880, 1, 65536⟩ := by
  decide +kernel

theorem context_12_26880_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26880 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 26880 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 26880, 1, 65536⟩
    (by decide) selected_cut_13644

theorem selected_cut_13645 : selected 8 ⟨357201, by decide⟩
    (prefixPartial 13 107524) = some ⟨13, 2, 0, 357201, 107524, 3489, 16384⟩ := by
  decide +kernel

theorem context_13_107524_357201 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107524 ⟨357201, by decide⟩ :=
  accepted_of_selected 13 107524 ⟨357201, by decide⟩ ⟨13, 2, 0, 357201, 107524, 3489, 16384⟩
    (by decide) selected_cut_13645

theorem selected_cut_13646 : selected 8 ⟨357244, by decide⟩
    (prefixPartial 13 107525) = some ⟨13, 2, 0, 357244, 107525, 2909, 16384⟩ := by
  decide +kernel

theorem context_13_107525_357244 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107525 ⟨357244, by decide⟩ :=
  accepted_of_selected 13 107525 ⟨357244, by decide⟩ ⟨13, 2, 0, 357244, 107525, 2909, 16384⟩
    (by decide) selected_cut_13646

theorem selected_cut_13647 : selected 8 ⟨357269, by decide⟩
    (prefixPartial 13 107526) = some ⟨13, 2, 0, 357269, 107526, 2201, 16384⟩ := by
  decide +kernel

theorem context_13_107526_357269 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107526 ⟨357269, by decide⟩ :=
  accepted_of_selected 13 107526 ⟨357269, by decide⟩ ⟨13, 2, 0, 357269, 107526, 2201, 16384⟩
    (by decide) selected_cut_13647

theorem selected_cut_13648 : selected 8 ⟨357277, by decide⟩
    (prefixPartial 13 107527) = some ⟨13, 2, 0, 357277, 107527, 1149, 16384⟩ := by
  decide +kernel

theorem context_13_107527_357277 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107527 ⟨357277, by decide⟩ :=
  accepted_of_selected 13 107527 ⟨357277, by decide⟩ ⟨13, 2, 0, 357277, 107527, 1149, 16384⟩
    (by decide) selected_cut_13648

theorem unmarked_context_12_26881_357278 : frontier 9 ⟨357278, by decide⟩
    (prefixCache 12 26881) (prefixPartial 12 26881) = false := by
  decide +kernel

theorem node_context_12_26881_357278 : EJMOriginalGlobalDAGData.nodes 9 ⟨357278, by decide⟩ =
    .split (coordinate 12) (![⟨357201, by decide⟩,⟨357244, by decide⟩,⟨357269, by decide⟩,⟨357277, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26881_357278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26881 ⟨357278, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26881
    ⟨357278, by decide⟩ (by decide) (![⟨357201, by decide⟩,⟨357244, by decide⟩,⟨357269, by decide⟩,⟨357277, by decide⟩]) unmarked_context_12_26881_357278 node_context_12_26881_357278
  intro a
  fin_cases a
  · exact context_13_107524_357201
  · exact context_13_107525_357244
  · exact context_13_107526_357269
  · exact context_13_107527_357277

theorem selected_cut_13649 : selected 9 ⟨347601, by decide⟩
    (prefixPartial 12 26882) = some ⟨12, 1, 0, 347601, 26882, 1, 65536⟩ := by
  decide +kernel

theorem context_12_26882_347601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26882 ⟨347601, by decide⟩ :=
  accepted_of_selected 12 26882 ⟨347601, by decide⟩ ⟨12, 1, 0, 347601, 26882, 1, 65536⟩
    (by decide) selected_cut_13649

theorem selected_cut_13650 : selected 7 ⟨357313, by decide⟩
    (prefixPartial 14 430128) = some ⟨14, 2, 0, 357313, 430128, 1377, 4096⟩ := by
  decide +kernel

theorem context_14_430128_357313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 430128 ⟨357313, by decide⟩ :=
  accepted_of_selected 14 430128 ⟨357313, by decide⟩ ⟨14, 2, 0, 357313, 430128, 1377, 4096⟩
    (by decide) selected_cut_13650

theorem selected_cut_13651 : selected 7 ⟨357328, by decide⟩
    (prefixPartial 14 430129) = some ⟨14, 2, 0, 357328, 430129, 897, 4096⟩ := by
  decide +kernel

theorem context_14_430129_357328 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 430129 ⟨357328, by decide⟩ :=
  accepted_of_selected 14 430129 ⟨357328, by decide⟩ ⟨14, 2, 0, 357328, 430129, 897, 4096⟩
    (by decide) selected_cut_13651

theorem selected_cut_13652 : selected 7 ⟨357345, by decide⟩
    (prefixPartial 14 430130) = some ⟨14, 2, 0, 357345, 430130, 1117, 4096⟩ := by
  decide +kernel

theorem context_14_430130_357345 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 430130 ⟨357345, by decide⟩ :=
  accepted_of_selected 14 430130 ⟨357345, by decide⟩ ⟨14, 2, 0, 357345, 430130, 1117, 4096⟩
    (by decide) selected_cut_13652

theorem selected_cut_13653 : selected 7 ⟨357368, by decide⟩
    (prefixPartial 14 430131) = some ⟨14, 2, 0, 357368, 430131, 1169, 4096⟩ := by
  decide +kernel

theorem context_14_430131_357368 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 430131 ⟨357368, by decide⟩ :=
  accepted_of_selected 14 430131 ⟨357368, by decide⟩ ⟨14, 2, 0, 357368, 430131, 1169, 4096⟩
    (by decide) selected_cut_13653

theorem unmarked_context_13_107532_357369 : frontier 8 ⟨357369, by decide⟩
    (prefixCache 13 107532) (prefixPartial 13 107532) = false := by
  decide +kernel

theorem node_context_13_107532_357369 : EJMOriginalGlobalDAGData.nodes 8 ⟨357369, by decide⟩ =
    .split (coordinate 13) (![⟨357313, by decide⟩,⟨357328, by decide⟩,⟨357345, by decide⟩,⟨357368, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_107532_357369 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107532 ⟨357369, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 107532
    ⟨357369, by decide⟩ (by decide) (![⟨357313, by decide⟩,⟨357328, by decide⟩,⟨357345, by decide⟩,⟨357368, by decide⟩]) unmarked_context_13_107532_357369 node_context_13_107532_357369
  intro a
  fin_cases a
  · exact context_14_430128_357313
  · exact context_14_430129_357328
  · exact context_14_430130_357345
  · exact context_14_430131_357368

theorem selected_cut_13654 : selected 8 ⟨357450, by decide⟩
    (prefixPartial 13 107533) = some ⟨13, 2, 0, 357450, 107533, 3941, 16384⟩ := by
  decide +kernel

theorem context_13_107533_357450 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107533 ⟨357450, by decide⟩ :=
  accepted_of_selected 13 107533 ⟨357450, by decide⟩ ⟨13, 2, 0, 357450, 107533, 3941, 16384⟩
    (by decide) selected_cut_13654

theorem selected_cut_13655 : selected 8 ⟨357500, by decide⟩
    (prefixPartial 13 107534) = some ⟨13, 2, 0, 357500, 107534, 2601, 16384⟩ := by
  decide +kernel

theorem context_13_107534_357500 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107534 ⟨357500, by decide⟩ :=
  accepted_of_selected 13 107534 ⟨357500, by decide⟩ ⟨13, 2, 0, 357500, 107534, 2601, 16384⟩
    (by decide) selected_cut_13655

theorem selected_cut_13656 : selected 8 ⟨357520, by decide⟩
    (prefixPartial 13 107535) = some ⟨13, 2, 0, 357520, 107535, 1265, 16384⟩ := by
  decide +kernel

theorem context_13_107535_357520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107535 ⟨357520, by decide⟩ :=
  accepted_of_selected 13 107535 ⟨357520, by decide⟩ ⟨13, 2, 0, 357520, 107535, 1265, 16384⟩
    (by decide) selected_cut_13656

theorem unmarked_context_12_26883_357521 : frontier 9 ⟨357521, by decide⟩
    (prefixCache 12 26883) (prefixPartial 12 26883) = false := by
  decide +kernel

theorem node_context_12_26883_357521 : EJMOriginalGlobalDAGData.nodes 9 ⟨357521, by decide⟩ =
    .split (coordinate 12) (![⟨357369, by decide⟩,⟨357450, by decide⟩,⟨357500, by decide⟩,⟨357520, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26883_357521 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26883 ⟨357521, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26883
    ⟨357521, by decide⟩ (by decide) (![⟨357369, by decide⟩,⟨357450, by decide⟩,⟨357500, by decide⟩,⟨357520, by decide⟩]) unmarked_context_12_26883_357521 node_context_12_26883_357521
  intro a
  fin_cases a
  · exact context_13_107532_357369
  · exact context_13_107533_357450
  · exact context_13_107534_357500
  · exact context_13_107535_357520

theorem unmarked_context_11_6720_357522 : frontier 10 ⟨357522, by decide⟩
    (prefixCache 11 6720) (prefixPartial 11 6720) = false := by
  decide +kernel

theorem node_context_11_6720_357522 : EJMOriginalGlobalDAGData.nodes 10 ⟨357522, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨357278, by decide⟩,⟨347601, by decide⟩,⟨357521, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6720_357522 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6720 ⟨357522, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6720
    ⟨357522, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨357278, by decide⟩,⟨347601, by decide⟩,⟨357521, by decide⟩]) unmarked_context_11_6720_357522 node_context_11_6720_357522
  intro a
  fin_cases a
  · exact context_12_26880_34034
  · exact context_12_26881_357278
  · exact context_12_26882_347601
  · exact context_12_26883_357521

theorem selected_cut_13657 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 26884) = some ⟨12, 1, 0, 34034, 26884, 1, 65536⟩ := by
  decide +kernel

theorem context_12_26884_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26884 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 26884 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 26884, 1, 65536⟩
    (by decide) selected_cut_13657

theorem selected_cut_13658 : selected 7 ⟨357566, by decide⟩
    (prefixPartial 14 430160) = some ⟨14, 2, 0, 357566, 430160, 2141, 4096⟩ := by
  decide +kernel

theorem context_14_430160_357566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 430160 ⟨357566, by decide⟩ :=
  accepted_of_selected 14 430160 ⟨357566, by decide⟩ ⟨14, 2, 0, 357566, 430160, 2141, 4096⟩
    (by decide) selected_cut_13658

theorem selected_cut_13659 : selected 7 ⟨357585, by decide⟩
    (prefixPartial 14 430161) = some ⟨14, 2, 0, 357585, 430161, 1185, 4096⟩ := by
  decide +kernel

theorem context_14_430161_357585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 430161 ⟨357585, by decide⟩ :=
  accepted_of_selected 14 430161 ⟨357585, by decide⟩ ⟨14, 2, 0, 357585, 430161, 1185, 4096⟩
    (by decide) selected_cut_13659

theorem selected_cut_13660 : selected 7 ⟨357602, by decide⟩
    (prefixPartial 14 430162) = some ⟨14, 2, 0, 357602, 430162, 1313, 4096⟩ := by
  decide +kernel

theorem context_14_430162_357602 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 430162 ⟨357602, by decide⟩ :=
  accepted_of_selected 14 430162 ⟨357602, by decide⟩ ⟨14, 2, 0, 357602, 430162, 1313, 4096⟩
    (by decide) selected_cut_13660

theorem selected_cut_13661 : selected 7 ⟨357630, by decide⟩
    (prefixPartial 14 430163) = some ⟨14, 2, 0, 357630, 430163, 1441, 4096⟩ := by
  decide +kernel

theorem context_14_430163_357630 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 430163 ⟨357630, by decide⟩ :=
  accepted_of_selected 14 430163 ⟨357630, by decide⟩ ⟨14, 2, 0, 357630, 430163, 1441, 4096⟩
    (by decide) selected_cut_13661

theorem unmarked_context_13_107540_357631 : frontier 8 ⟨357631, by decide⟩
    (prefixCache 13 107540) (prefixPartial 13 107540) = false := by
  decide +kernel

theorem node_context_13_107540_357631 : EJMOriginalGlobalDAGData.nodes 8 ⟨357631, by decide⟩ =
    .split (coordinate 13) (![⟨357566, by decide⟩,⟨357585, by decide⟩,⟨357602, by decide⟩,⟨357630, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_107540_357631 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107540 ⟨357631, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 107540
    ⟨357631, by decide⟩ (by decide) (![⟨357566, by decide⟩,⟨357585, by decide⟩,⟨357602, by decide⟩,⟨357630, by decide⟩]) unmarked_context_13_107540_357631 node_context_13_107540_357631
  intro a
  fin_cases a
  · exact context_14_430160_357566
  · exact context_14_430161_357585
  · exact context_14_430162_357602
  · exact context_14_430163_357630

theorem selected_cut_13662 : selected 7 ⟨357665, by decide⟩
    (prefixPartial 14 430164) = some ⟨14, 2, 0, 357665, 430164, 1213, 4096⟩ := by
  decide +kernel

theorem context_14_430164_357665 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 430164 ⟨357665, by decide⟩ :=
  accepted_of_selected 14 430164 ⟨357665, by decide⟩ ⟨14, 2, 0, 357665, 430164, 1213, 4096⟩
    (by decide) selected_cut_13662

theorem selected_cut_13663 : selected 7 ⟨357682, by decide⟩
    (prefixPartial 14 430165) = some ⟨14, 2, 0, 357682, 430165, 769, 4096⟩ := by
  decide +kernel

theorem context_14_430165_357682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 430165 ⟨357682, by decide⟩ :=
  accepted_of_selected 14 430165 ⟨357682, by decide⟩ ⟨14, 2, 0, 357682, 430165, 769, 4096⟩
    (by decide) selected_cut_13663

theorem selected_cut_13664 : selected 7 ⟨357728, by decide⟩
    (prefixPartial 14 430166) = some ⟨14, 2, 0, 357728, 430166, 1525, 4096⟩ := by
  decide +kernel

theorem context_14_430166_357728 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 430166 ⟨357728, by decide⟩ :=
  accepted_of_selected 14 430166 ⟨357728, by decide⟩ ⟨14, 2, 0, 357728, 430166, 1525, 4096⟩
    (by decide) selected_cut_13664

theorem selected_cut_13665 : selected 7 ⟨357762, by decide⟩
    (prefixPartial 14 430167) = some ⟨14, 2, 0, 357762, 430167, 1417, 4096⟩ := by
  decide +kernel

theorem context_14_430167_357762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 430167 ⟨357762, by decide⟩ :=
  accepted_of_selected 14 430167 ⟨357762, by decide⟩ ⟨14, 2, 0, 357762, 430167, 1417, 4096⟩
    (by decide) selected_cut_13665

theorem unmarked_context_13_107541_357763 : frontier 8 ⟨357763, by decide⟩
    (prefixCache 13 107541) (prefixPartial 13 107541) = false := by
  decide +kernel

theorem node_context_13_107541_357763 : EJMOriginalGlobalDAGData.nodes 8 ⟨357763, by decide⟩ =
    .split (coordinate 13) (![⟨357665, by decide⟩,⟨357682, by decide⟩,⟨357728, by decide⟩,⟨357762, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_107541_357763 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107541 ⟨357763, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 107541
    ⟨357763, by decide⟩ (by decide) (![⟨357665, by decide⟩,⟨357682, by decide⟩,⟨357728, by decide⟩,⟨357762, by decide⟩]) unmarked_context_13_107541_357763 node_context_13_107541_357763
  intro a
  fin_cases a
  · exact context_14_430164_357665
  · exact context_14_430165_357682
  · exact context_14_430166_357728
  · exact context_14_430167_357762

theorem selected_cut_13666 : selected 8 ⟨357855, by decide⟩
    (prefixPartial 13 107542) = some ⟨13, 2, 0, 357855, 107542, 3285, 16384⟩ := by
  decide +kernel

theorem context_13_107542_357855 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107542 ⟨357855, by decide⟩ :=
  accepted_of_selected 13 107542 ⟨357855, by decide⟩ ⟨13, 2, 0, 357855, 107542, 3285, 16384⟩
    (by decide) selected_cut_13666

theorem selected_cut_13667 : selected 8 ⟨357888, by decide⟩
    (prefixPartial 13 107543) = some ⟨13, 2, 0, 357888, 107543, 1581, 16384⟩ := by
  decide +kernel

theorem context_13_107543_357888 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107543 ⟨357888, by decide⟩ :=
  accepted_of_selected 13 107543 ⟨357888, by decide⟩ ⟨13, 2, 0, 357888, 107543, 1581, 16384⟩
    (by decide) selected_cut_13667

theorem unmarked_context_12_26885_357889 : frontier 9 ⟨357889, by decide⟩
    (prefixCache 12 26885) (prefixPartial 12 26885) = false := by
  decide +kernel

theorem node_context_12_26885_357889 : EJMOriginalGlobalDAGData.nodes 9 ⟨357889, by decide⟩ =
    .split (coordinate 12) (![⟨357631, by decide⟩,⟨357763, by decide⟩,⟨357855, by decide⟩,⟨357888, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26885_357889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26885 ⟨357889, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26885
    ⟨357889, by decide⟩ (by decide) (![⟨357631, by decide⟩,⟨357763, by decide⟩,⟨357855, by decide⟩,⟨357888, by decide⟩]) unmarked_context_12_26885_357889 node_context_12_26885_357889
  intro a
  fin_cases a
  · exact context_13_107540_357631
  · exact context_13_107541_357763
  · exact context_13_107542_357855
  · exact context_13_107543_357888

theorem selected_cut_13668 : selected 8 ⟨357942, by decide⟩
    (prefixPartial 13 107544) = some ⟨13, 2, 0, 357942, 107544, 3889, 16384⟩ := by
  decide +kernel

theorem context_13_107544_357942 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107544 ⟨357942, by decide⟩ :=
  accepted_of_selected 13 107544 ⟨357942, by decide⟩ ⟨13, 2, 0, 357942, 107544, 3889, 16384⟩
    (by decide) selected_cut_13668

theorem selected_cut_13669 : selected 8 ⟨357988, by decide⟩
    (prefixPartial 13 107545) = some ⟨13, 2, 0, 357988, 107545, 3317, 16384⟩ := by
  decide +kernel

theorem context_13_107545_357988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107545 ⟨357988, by decide⟩ :=
  accepted_of_selected 13 107545 ⟨357988, by decide⟩ ⟨13, 2, 0, 357988, 107545, 3317, 16384⟩
    (by decide) selected_cut_13669

theorem selected_cut_13670 : selected 8 ⟨358019, by decide⟩
    (prefixPartial 13 107546) = some ⟨13, 2, 0, 358019, 107546, 2373, 16384⟩ := by
  decide +kernel

theorem context_13_107546_358019 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107546 ⟨358019, by decide⟩ :=
  accepted_of_selected 13 107546 ⟨358019, by decide⟩ ⟨13, 2, 0, 358019, 107546, 2373, 16384⟩
    (by decide) selected_cut_13670

theorem selected_cut_13671 : selected 8 ⟨358035, by decide⟩
    (prefixPartial 13 107547) = some ⟨13, 2, 0, 358035, 107547, 1277, 16384⟩ := by
  decide +kernel

theorem context_13_107547_358035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107547 ⟨358035, by decide⟩ :=
  accepted_of_selected 13 107547 ⟨358035, by decide⟩ ⟨13, 2, 0, 358035, 107547, 1277, 16384⟩
    (by decide) selected_cut_13671

theorem unmarked_context_12_26886_358036 : frontier 9 ⟨358036, by decide⟩
    (prefixCache 12 26886) (prefixPartial 12 26886) = false := by
  decide +kernel

theorem node_context_12_26886_358036 : EJMOriginalGlobalDAGData.nodes 9 ⟨358036, by decide⟩ =
    .split (coordinate 12) (![⟨357942, by decide⟩,⟨357988, by decide⟩,⟨358019, by decide⟩,⟨358035, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26886_358036 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26886 ⟨358036, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26886
    ⟨358036, by decide⟩ (by decide) (![⟨357942, by decide⟩,⟨357988, by decide⟩,⟨358019, by decide⟩,⟨358035, by decide⟩]) unmarked_context_12_26886_358036 node_context_12_26886_358036
  intro a
  fin_cases a
  · exact context_13_107544_357942
  · exact context_13_107545_357988
  · exact context_13_107546_358019
  · exact context_13_107547_358035

theorem selected_cut_13672 : selected 8 ⟨358095, by decide⟩
    (prefixPartial 13 107548) = some ⟨13, 2, 0, 358095, 107548, 4029, 16384⟩ := by
  decide +kernel

theorem context_13_107548_358095 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107548 ⟨358095, by decide⟩ :=
  accepted_of_selected 13 107548 ⟨358095, by decide⟩ ⟨13, 2, 0, 358095, 107548, 4029, 16384⟩
    (by decide) selected_cut_13672

theorem selected_cut_13673 : selected 8 ⟨358144, by decide⟩
    (prefixPartial 13 107549) = some ⟨13, 2, 0, 358144, 107549, 3641, 16384⟩ := by
  decide +kernel

theorem context_13_107549_358144 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107549 ⟨358144, by decide⟩ :=
  accepted_of_selected 13 107549 ⟨358144, by decide⟩ ⟨13, 2, 0, 358144, 107549, 3641, 16384⟩
    (by decide) selected_cut_13673

theorem selected_cut_13674 : selected 8 ⟨358184, by decide⟩
    (prefixPartial 13 107550) = some ⟨13, 2, 0, 358184, 107550, 2481, 16384⟩ := by
  decide +kernel

theorem context_13_107550_358184 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107550 ⟨358184, by decide⟩ :=
  accepted_of_selected 13 107550 ⟨358184, by decide⟩ ⟨13, 2, 0, 358184, 107550, 2481, 16384⟩
    (by decide) selected_cut_13674

theorem selected_cut_13675 : selected 8 ⟨358199, by decide⟩
    (prefixPartial 13 107551) = some ⟨13, 2, 0, 358199, 107551, 1217, 16384⟩ := by
  decide +kernel

theorem context_13_107551_358199 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107551 ⟨358199, by decide⟩ :=
  accepted_of_selected 13 107551 ⟨358199, by decide⟩ ⟨13, 2, 0, 358199, 107551, 1217, 16384⟩
    (by decide) selected_cut_13675

theorem unmarked_context_12_26887_358200 : frontier 9 ⟨358200, by decide⟩
    (prefixCache 12 26887) (prefixPartial 12 26887) = false := by
  decide +kernel

theorem node_context_12_26887_358200 : EJMOriginalGlobalDAGData.nodes 9 ⟨358200, by decide⟩ =
    .split (coordinate 12) (![⟨358095, by decide⟩,⟨358144, by decide⟩,⟨358184, by decide⟩,⟨358199, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26887_358200 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26887 ⟨358200, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26887
    ⟨358200, by decide⟩ (by decide) (![⟨358095, by decide⟩,⟨358144, by decide⟩,⟨358184, by decide⟩,⟨358199, by decide⟩]) unmarked_context_12_26887_358200 node_context_12_26887_358200
  intro a
  fin_cases a
  · exact context_13_107548_358095
  · exact context_13_107549_358144
  · exact context_13_107550_358184
  · exact context_13_107551_358199

theorem unmarked_context_11_6721_358201 : frontier 10 ⟨358201, by decide⟩
    (prefixCache 11 6721) (prefixPartial 11 6721) = false := by
  decide +kernel

theorem node_context_11_6721_358201 : EJMOriginalGlobalDAGData.nodes 10 ⟨358201, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨357889, by decide⟩,⟨358036, by decide⟩,⟨358200, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6721_358201 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6721 ⟨358201, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6721
    ⟨358201, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨357889, by decide⟩,⟨358036, by decide⟩,⟨358200, by decide⟩]) unmarked_context_11_6721_358201 node_context_11_6721_358201
  intro a
  fin_cases a
  · exact context_12_26884_34034
  · exact context_12_26885_357889
  · exact context_12_26886_358036
  · exact context_12_26887_358200

theorem selected_cut_13676 : selected 8 ⟨358256, by decide⟩
    (prefixPartial 13 107552) = some ⟨13, 2, 0, 358256, 107552, 3477, 16384⟩ := by
  decide +kernel

theorem context_13_107552_358256 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107552 ⟨358256, by decide⟩ :=
  accepted_of_selected 13 107552 ⟨358256, by decide⟩ ⟨13, 2, 0, 358256, 107552, 3477, 16384⟩
    (by decide) selected_cut_13676

theorem selected_cut_13677 : selected 8 ⟨358338, by decide⟩
    (prefixPartial 13 107553) = some ⟨13, 2, 0, 358338, 107553, 4069, 16384⟩ := by
  decide +kernel

theorem context_13_107553_358338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107553 ⟨358338, by decide⟩ :=
  accepted_of_selected 13 107553 ⟨358338, by decide⟩ ⟨13, 2, 0, 358338, 107553, 4069, 16384⟩
    (by decide) selected_cut_13677

theorem selected_cut_13678 : selected 8 ⟨358379, by decide⟩
    (prefixPartial 13 107554) = some ⟨13, 2, 0, 358379, 107554, 2369, 16384⟩ := by
  decide +kernel

theorem context_13_107554_358379 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107554 ⟨358379, by decide⟩ :=
  accepted_of_selected 13 107554 ⟨358379, by decide⟩ ⟨13, 2, 0, 358379, 107554, 2369, 16384⟩
    (by decide) selected_cut_13678

theorem selected_cut_13679 : selected 8 ⟨358393, by decide⟩
    (prefixPartial 13 107555) = some ⟨13, 2, 0, 358393, 107555, 1257, 16384⟩ := by
  decide +kernel

theorem context_13_107555_358393 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107555 ⟨358393, by decide⟩ :=
  accepted_of_selected 13 107555 ⟨358393, by decide⟩ ⟨13, 2, 0, 358393, 107555, 1257, 16384⟩
    (by decide) selected_cut_13679

theorem unmarked_context_12_26888_358394 : frontier 9 ⟨358394, by decide⟩
    (prefixCache 12 26888) (prefixPartial 12 26888) = false := by
  decide +kernel

theorem node_context_12_26888_358394 : EJMOriginalGlobalDAGData.nodes 9 ⟨358394, by decide⟩ =
    .split (coordinate 12) (![⟨358256, by decide⟩,⟨358338, by decide⟩,⟨358379, by decide⟩,⟨358393, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26888_358394 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26888 ⟨358394, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26888
    ⟨358394, by decide⟩ (by decide) (![⟨358256, by decide⟩,⟨358338, by decide⟩,⟨358379, by decide⟩,⟨358393, by decide⟩]) unmarked_context_12_26888_358394 node_context_12_26888_358394
  intro a
  fin_cases a
  · exact context_13_107552_358256
  · exact context_13_107553_358338
  · exact context_13_107554_358379
  · exact context_13_107555_358393

theorem selected_cut_13680 : selected 8 ⟨358438, by decide⟩
    (prefixPartial 13 107556) = some ⟨13, 2, 0, 358438, 107556, 3161, 16384⟩ := by
  decide +kernel

theorem context_13_107556_358438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107556 ⟨358438, by decide⟩ :=
  accepted_of_selected 13 107556 ⟨358438, by decide⟩ ⟨13, 2, 0, 358438, 107556, 3161, 16384⟩
    (by decide) selected_cut_13680

theorem selected_cut_13681 : selected 8 ⟨358471, by decide⟩
    (prefixPartial 13 107557) = some ⟨13, 2, 0, 358471, 107557, 3033, 16384⟩ := by
  decide +kernel

theorem context_13_107557_358471 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107557 ⟨358471, by decide⟩ :=
  accepted_of_selected 13 107557 ⟨358471, by decide⟩ ⟨13, 2, 0, 358471, 107557, 3033, 16384⟩
    (by decide) selected_cut_13681

theorem selected_cut_13682 : selected 8 ⟨358494, by decide⟩
    (prefixPartial 13 107558) = some ⟨13, 2, 0, 358494, 107558, 2297, 16384⟩ := by
  decide +kernel

theorem context_13_107558_358494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107558 ⟨358494, by decide⟩ :=
  accepted_of_selected 13 107558 ⟨358494, by decide⟩ ⟨13, 2, 0, 358494, 107558, 2297, 16384⟩
    (by decide) selected_cut_13682

theorem selected_cut_13683 : selected 8 ⟨358501, by decide⟩
    (prefixPartial 13 107559) = some ⟨13, 2, 0, 358501, 107559, 1173, 16384⟩ := by
  decide +kernel

theorem context_13_107559_358501 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107559 ⟨358501, by decide⟩ :=
  accepted_of_selected 13 107559 ⟨358501, by decide⟩ ⟨13, 2, 0, 358501, 107559, 1173, 16384⟩
    (by decide) selected_cut_13683

theorem unmarked_context_12_26889_358502 : frontier 9 ⟨358502, by decide⟩
    (prefixCache 12 26889) (prefixPartial 12 26889) = false := by
  decide +kernel

theorem node_context_12_26889_358502 : EJMOriginalGlobalDAGData.nodes 9 ⟨358502, by decide⟩ =
    .split (coordinate 12) (![⟨358438, by decide⟩,⟨358471, by decide⟩,⟨358494, by decide⟩,⟨358501, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26889_358502 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26889 ⟨358502, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26889
    ⟨358502, by decide⟩ (by decide) (![⟨358438, by decide⟩,⟨358471, by decide⟩,⟨358494, by decide⟩,⟨358501, by decide⟩]) unmarked_context_12_26889_358502 node_context_12_26889_358502
  intro a
  fin_cases a
  · exact context_13_107556_358438
  · exact context_13_107557_358471
  · exact context_13_107558_358494
  · exact context_13_107559_358501

theorem selected_cut_13684 : selected 8 ⟨358560, by decide⟩
    (prefixPartial 13 107560) = some ⟨13, 2, 0, 358560, 107560, 3533, 16384⟩ := by
  decide +kernel

theorem context_13_107560_358560 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107560 ⟨358560, by decide⟩ :=
  accepted_of_selected 13 107560 ⟨358560, by decide⟩ ⟨13, 2, 0, 358560, 107560, 3533, 16384⟩
    (by decide) selected_cut_13684

theorem selected_cut_13685 : selected 8 ⟨358609, by decide⟩
    (prefixPartial 13 107561) = some ⟨13, 2, 0, 358609, 107561, 3653, 16384⟩ := by
  decide +kernel

theorem context_13_107561_358609 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107561 ⟨358609, by decide⟩ :=
  accepted_of_selected 13 107561 ⟨358609, by decide⟩ ⟨13, 2, 0, 358609, 107561, 3653, 16384⟩
    (by decide) selected_cut_13685

theorem selected_cut_13686 : selected 8 ⟨358649, by decide⟩
    (prefixPartial 13 107562) = some ⟨13, 2, 0, 358649, 107562, 2585, 16384⟩ := by
  decide +kernel

theorem context_13_107562_358649 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107562 ⟨358649, by decide⟩ :=
  accepted_of_selected 13 107562 ⟨358649, by decide⟩ ⟨13, 2, 0, 358649, 107562, 2585, 16384⟩
    (by decide) selected_cut_13686

theorem selected_cut_13687 : selected 8 ⟨358664, by decide⟩
    (prefixPartial 13 107563) = some ⟨13, 2, 0, 358664, 107563, 1241, 16384⟩ := by
  decide +kernel

theorem context_13_107563_358664 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107563 ⟨358664, by decide⟩ :=
  accepted_of_selected 13 107563 ⟨358664, by decide⟩ ⟨13, 2, 0, 358664, 107563, 1241, 16384⟩
    (by decide) selected_cut_13687

theorem unmarked_context_12_26890_358665 : frontier 9 ⟨358665, by decide⟩
    (prefixCache 12 26890) (prefixPartial 12 26890) = false := by
  decide +kernel

theorem node_context_12_26890_358665 : EJMOriginalGlobalDAGData.nodes 9 ⟨358665, by decide⟩ =
    .split (coordinate 12) (![⟨358560, by decide⟩,⟨358609, by decide⟩,⟨358649, by decide⟩,⟨358664, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26890_358665 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26890 ⟨358665, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26890
    ⟨358665, by decide⟩ (by decide) (![⟨358560, by decide⟩,⟨358609, by decide⟩,⟨358649, by decide⟩,⟨358664, by decide⟩]) unmarked_context_12_26890_358665 node_context_12_26890_358665
  intro a
  fin_cases a
  · exact context_13_107560_358560
  · exact context_13_107561_358609
  · exact context_13_107562_358649
  · exact context_13_107563_358664

theorem selected_cut_13688 : selected 8 ⟨358727, by decide⟩
    (prefixPartial 13 107564) = some ⟨13, 2, 0, 358727, 107564, 3909, 16384⟩ := by
  decide +kernel

theorem context_13_107564_358727 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107564 ⟨358727, by decide⟩ :=
  accepted_of_selected 13 107564 ⟨358727, by decide⟩ ⟨13, 2, 0, 358727, 107564, 3909, 16384⟩
    (by decide) selected_cut_13688

theorem selected_cut_13689 : selected 7 ⟨358749, by decide⟩
    (prefixPartial 14 430260) = some ⟨14, 2, 0, 358749, 430260, 1189, 4096⟩ := by
  decide +kernel

theorem context_14_430260_358749 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 430260 ⟨358749, by decide⟩ :=
  accepted_of_selected 14 430260 ⟨358749, by decide⟩ ⟨14, 2, 0, 358749, 430260, 1189, 4096⟩
    (by decide) selected_cut_13689

theorem selected_cut_13690 : selected 7 ⟨358755, by decide⟩
    (prefixPartial 14 430261) = some ⟨14, 2, 0, 358755, 430261, 701, 4096⟩ := by
  decide +kernel

theorem context_14_430261_358755 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 430261 ⟨358755, by decide⟩ :=
  accepted_of_selected 14 430261 ⟨358755, by decide⟩ ⟨14, 2, 0, 358755, 430261, 701, 4096⟩
    (by decide) selected_cut_13690

theorem selected_cut_13691 : selected 7 ⟨358777, by decide⟩
    (prefixPartial 14 430262) = some ⟨14, 2, 0, 358777, 430262, 1205, 4096⟩ := by
  decide +kernel

theorem context_14_430262_358777 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 430262 ⟨358777, by decide⟩ :=
  accepted_of_selected 14 430262 ⟨358777, by decide⟩ ⟨14, 2, 0, 358777, 430262, 1205, 4096⟩
    (by decide) selected_cut_13691

theorem selected_cut_13692 : selected 7 ⟨358798, by decide⟩
    (prefixPartial 14 430263) = some ⟨14, 2, 0, 358798, 430263, 1181, 4096⟩ := by
  decide +kernel

theorem context_14_430263_358798 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 430263 ⟨358798, by decide⟩ :=
  accepted_of_selected 14 430263 ⟨358798, by decide⟩ ⟨14, 2, 0, 358798, 430263, 1181, 4096⟩
    (by decide) selected_cut_13692

theorem unmarked_context_13_107565_358799 : frontier 8 ⟨358799, by decide⟩
    (prefixCache 13 107565) (prefixPartial 13 107565) = false := by
  decide +kernel

theorem node_context_13_107565_358799 : EJMOriginalGlobalDAGData.nodes 8 ⟨358799, by decide⟩ =
    .split (coordinate 13) (![⟨358749, by decide⟩,⟨358755, by decide⟩,⟨358777, by decide⟩,⟨358798, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_107565_358799 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107565 ⟨358799, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 107565
    ⟨358799, by decide⟩ (by decide) (![⟨358749, by decide⟩,⟨358755, by decide⟩,⟨358777, by decide⟩,⟨358798, by decide⟩]) unmarked_context_13_107565_358799 node_context_13_107565_358799
  intro a
  fin_cases a
  · exact context_14_430260_358749
  · exact context_14_430261_358755
  · exact context_14_430262_358777
  · exact context_14_430263_358798

theorem selected_cut_13693 : selected 8 ⟨358831, by decide⟩
    (prefixPartial 13 107566) = some ⟨13, 2, 0, 358831, 107566, 2549, 16384⟩ := by
  decide +kernel

theorem context_13_107566_358831 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107566 ⟨358831, by decide⟩ :=
  accepted_of_selected 13 107566 ⟨358831, by decide⟩ ⟨13, 2, 0, 358831, 107566, 2549, 16384⟩
    (by decide) selected_cut_13693

theorem selected_cut_13694 : selected 8 ⟨358847, by decide⟩
    (prefixPartial 13 107567) = some ⟨13, 2, 0, 358847, 107567, 1269, 16384⟩ := by
  decide +kernel

theorem context_13_107567_358847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107567 ⟨358847, by decide⟩ :=
  accepted_of_selected 13 107567 ⟨358847, by decide⟩ ⟨13, 2, 0, 358847, 107567, 1269, 16384⟩
    (by decide) selected_cut_13694

theorem unmarked_context_12_26891_358848 : frontier 9 ⟨358848, by decide⟩
    (prefixCache 12 26891) (prefixPartial 12 26891) = false := by
  decide +kernel

theorem node_context_12_26891_358848 : EJMOriginalGlobalDAGData.nodes 9 ⟨358848, by decide⟩ =
    .split (coordinate 12) (![⟨358727, by decide⟩,⟨358799, by decide⟩,⟨358831, by decide⟩,⟨358847, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26891_358848 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26891 ⟨358848, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26891
    ⟨358848, by decide⟩ (by decide) (![⟨358727, by decide⟩,⟨358799, by decide⟩,⟨358831, by decide⟩,⟨358847, by decide⟩]) unmarked_context_12_26891_358848 node_context_12_26891_358848
  intro a
  fin_cases a
  · exact context_13_107564_358727
  · exact context_13_107565_358799
  · exact context_13_107566_358831
  · exact context_13_107567_358847

theorem unmarked_context_11_6722_358849 : frontier 10 ⟨358849, by decide⟩
    (prefixCache 11 6722) (prefixPartial 11 6722) = false := by
  decide +kernel

theorem node_context_11_6722_358849 : EJMOriginalGlobalDAGData.nodes 10 ⟨358849, by decide⟩ =
    .split (coordinate 11) (![⟨358394, by decide⟩,⟨358502, by decide⟩,⟨358665, by decide⟩,⟨358848, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6722_358849 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6722 ⟨358849, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6722
    ⟨358849, by decide⟩ (by decide) (![⟨358394, by decide⟩,⟨358502, by decide⟩,⟨358665, by decide⟩,⟨358848, by decide⟩]) unmarked_context_11_6722_358849 node_context_11_6722_358849
  intro a
  fin_cases a
  · exact context_12_26888_358394
  · exact context_12_26889_358502
  · exact context_12_26890_358665
  · exact context_12_26891_358848

theorem selected_cut_13695 : selected 8 ⟨358887, by decide⟩
    (prefixPartial 13 107568) = some ⟨13, 2, 0, 358887, 107568, 2833, 16384⟩ := by
  decide +kernel

theorem context_13_107568_358887 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107568 ⟨358887, by decide⟩ :=
  accepted_of_selected 13 107568 ⟨358887, by decide⟩ ⟨13, 2, 0, 358887, 107568, 2833, 16384⟩
    (by decide) selected_cut_13695

theorem selected_cut_13696 : selected 7 ⟨358908, by decide⟩
    (prefixPartial 14 430276) = some ⟨14, 2, 0, 358908, 430276, 1245, 4096⟩ := by
  decide +kernel

theorem context_14_430276_358908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 430276 ⟨358908, by decide⟩ :=
  accepted_of_selected 14 430276 ⟨358908, by decide⟩ ⟨14, 2, 0, 358908, 430276, 1245, 4096⟩
    (by decide) selected_cut_13696

theorem selected_cut_13697 : selected 7 ⟨358913, by decide⟩
    (prefixPartial 14 430277) = some ⟨14, 2, 0, 358913, 430277, 573, 4096⟩ := by
  decide +kernel

theorem context_14_430277_358913 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 430277 ⟨358913, by decide⟩ :=
  accepted_of_selected 14 430277 ⟨358913, by decide⟩ ⟨14, 2, 0, 358913, 430277, 573, 4096⟩
    (by decide) selected_cut_13697

theorem selected_cut_13698 : selected 7 ⟨358935, by decide⟩
    (prefixPartial 14 430278) = some ⟨14, 2, 0, 358935, 430278, 1265, 4096⟩ := by
  decide +kernel

theorem context_14_430278_358935 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 430278 ⟨358935, by decide⟩ :=
  accepted_of_selected 14 430278 ⟨358935, by decide⟩ ⟨14, 2, 0, 358935, 430278, 1265, 4096⟩
    (by decide) selected_cut_13698

theorem selected_cut_13699 : selected 7 ⟨358947, by decide⟩
    (prefixPartial 14 430279) = some ⟨14, 2, 0, 358947, 430279, 1017, 4096⟩ := by
  decide +kernel

theorem context_14_430279_358947 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 430279 ⟨358947, by decide⟩ :=
  accepted_of_selected 14 430279 ⟨358947, by decide⟩ ⟨14, 2, 0, 358947, 430279, 1017, 4096⟩
    (by decide) selected_cut_13699

theorem unmarked_context_13_107569_358948 : frontier 8 ⟨358948, by decide⟩
    (prefixCache 13 107569) (prefixPartial 13 107569) = false := by
  decide +kernel

theorem node_context_13_107569_358948 : EJMOriginalGlobalDAGData.nodes 8 ⟨358948, by decide⟩ =
    .split (coordinate 13) (![⟨358908, by decide⟩,⟨358913, by decide⟩,⟨358935, by decide⟩,⟨358947, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_107569_358948 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107569 ⟨358948, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 107569
    ⟨358948, by decide⟩ (by decide) (![⟨358908, by decide⟩,⟨358913, by decide⟩,⟨358935, by decide⟩,⟨358947, by decide⟩]) unmarked_context_13_107569_358948 node_context_13_107569_358948
  intro a
  fin_cases a
  · exact context_14_430276_358908
  · exact context_14_430277_358913
  · exact context_14_430278_358935
  · exact context_14_430279_358947

theorem selected_cut_13700 : selected 8 ⟨358979, by decide⟩
    (prefixPartial 13 107570) = some ⟨13, 2, 0, 358979, 107570, 2313, 16384⟩ := by
  decide +kernel

theorem context_13_107570_358979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107570 ⟨358979, by decide⟩ :=
  accepted_of_selected 13 107570 ⟨358979, by decide⟩ ⟨13, 2, 0, 358979, 107570, 2313, 16384⟩
    (by decide) selected_cut_13700

theorem selected_cut_13701 : selected 8 ⟨358995, by decide⟩
    (prefixPartial 13 107571) = some ⟨13, 2, 0, 358995, 107571, 1273, 16384⟩ := by
  decide +kernel

theorem context_13_107571_358995 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107571 ⟨358995, by decide⟩ :=
  accepted_of_selected 13 107571 ⟨358995, by decide⟩ ⟨13, 2, 0, 358995, 107571, 1273, 16384⟩
    (by decide) selected_cut_13701

theorem unmarked_context_12_26892_358996 : frontier 9 ⟨358996, by decide⟩
    (prefixCache 12 26892) (prefixPartial 12 26892) = false := by
  decide +kernel

theorem node_context_12_26892_358996 : EJMOriginalGlobalDAGData.nodes 9 ⟨358996, by decide⟩ =
    .split (coordinate 12) (![⟨358887, by decide⟩,⟨358948, by decide⟩,⟨358979, by decide⟩,⟨358995, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26892_358996 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26892 ⟨358996, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26892
    ⟨358996, by decide⟩ (by decide) (![⟨358887, by decide⟩,⟨358948, by decide⟩,⟨358979, by decide⟩,⟨358995, by decide⟩]) unmarked_context_12_26892_358996 node_context_12_26892_358996
  intro a
  fin_cases a
  · exact context_13_107568_358887
  · exact context_13_107569_358948
  · exact context_13_107570_358979
  · exact context_13_107571_358995

theorem selected_cut_13702 : selected 8 ⟨359033, by decide⟩
    (prefixPartial 13 107572) = some ⟨13, 2, 0, 359033, 107572, 3005, 16384⟩ := by
  decide +kernel

theorem context_13_107572_359033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107572 ⟨359033, by decide⟩ :=
  accepted_of_selected 13 107572 ⟨359033, by decide⟩ ⟨13, 2, 0, 359033, 107572, 3005, 16384⟩
    (by decide) selected_cut_13702

theorem selected_cut_13703 : selected 8 ⟨359073, by decide⟩
    (prefixPartial 13 107573) = some ⟨13, 2, 0, 359073, 107573, 3189, 16384⟩ := by
  decide +kernel

theorem context_13_107573_359073 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107573 ⟨359073, by decide⟩ :=
  accepted_of_selected 13 107573 ⟨359073, by decide⟩ ⟨13, 2, 0, 359073, 107573, 3189, 16384⟩
    (by decide) selected_cut_13703

theorem selected_cut_13704 : selected 8 ⟨359092, by decide⟩
    (prefixPartial 13 107574) = some ⟨13, 2, 0, 359092, 107574, 2241, 16384⟩ := by
  decide +kernel

theorem context_13_107574_359092 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107574 ⟨359092, by decide⟩ :=
  accepted_of_selected 13 107574 ⟨359092, by decide⟩ ⟨13, 2, 0, 359092, 107574, 2241, 16384⟩
    (by decide) selected_cut_13704

theorem selected_cut_13705 : selected 8 ⟨359095, by decide⟩
    (prefixPartial 13 107575) = some ⟨13, 2, 0, 359095, 107575, 1141, 16384⟩ := by
  decide +kernel

theorem context_13_107575_359095 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107575 ⟨359095, by decide⟩ :=
  accepted_of_selected 13 107575 ⟨359095, by decide⟩ ⟨13, 2, 0, 359095, 107575, 1141, 16384⟩
    (by decide) selected_cut_13705

theorem unmarked_context_12_26893_359096 : frontier 9 ⟨359096, by decide⟩
    (prefixCache 12 26893) (prefixPartial 12 26893) = false := by
  decide +kernel

theorem node_context_12_26893_359096 : EJMOriginalGlobalDAGData.nodes 9 ⟨359096, by decide⟩ =
    .split (coordinate 12) (![⟨359033, by decide⟩,⟨359073, by decide⟩,⟨359092, by decide⟩,⟨359095, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26893_359096 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26893 ⟨359096, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26893
    ⟨359096, by decide⟩ (by decide) (![⟨359033, by decide⟩,⟨359073, by decide⟩,⟨359092, by decide⟩,⟨359095, by decide⟩]) unmarked_context_12_26893_359096 node_context_12_26893_359096
  intro a
  fin_cases a
  · exact context_13_107572_359033
  · exact context_13_107573_359073
  · exact context_13_107574_359092
  · exact context_13_107575_359095

theorem selected_cut_13706 : selected 8 ⟨359153, by decide⟩
    (prefixPartial 13 107576) = some ⟨13, 2, 0, 359153, 107576, 3545, 16384⟩ := by
  decide +kernel

theorem context_13_107576_359153 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107576 ⟨359153, by decide⟩ :=
  accepted_of_selected 13 107576 ⟨359153, by decide⟩ ⟨13, 2, 0, 359153, 107576, 3545, 16384⟩
    (by decide) selected_cut_13706

theorem selected_cut_13707 : selected 8 ⟨359216, by decide⟩
    (prefixPartial 13 107577) = some ⟨13, 2, 0, 359216, 107577, 3921, 16384⟩ := by
  decide +kernel

theorem context_13_107577_359216 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107577 ⟨359216, by decide⟩ :=
  accepted_of_selected 13 107577 ⟨359216, by decide⟩ ⟨13, 2, 0, 359216, 107577, 3921, 16384⟩
    (by decide) selected_cut_13707

theorem selected_cut_13708 : selected 8 ⟨359262, by decide⟩
    (prefixPartial 13 107578) = some ⟨13, 2, 0, 359262, 107578, 2505, 16384⟩ := by
  decide +kernel

theorem context_13_107578_359262 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107578 ⟨359262, by decide⟩ :=
  accepted_of_selected 13 107578 ⟨359262, by decide⟩ ⟨13, 2, 0, 359262, 107578, 2505, 16384⟩
    (by decide) selected_cut_13708

theorem selected_cut_13709 : selected 8 ⟨359275, by decide⟩
    (prefixPartial 13 107579) = some ⟨13, 2, 0, 359275, 107579, 1249, 16384⟩ := by
  decide +kernel

theorem context_13_107579_359275 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107579 ⟨359275, by decide⟩ :=
  accepted_of_selected 13 107579 ⟨359275, by decide⟩ ⟨13, 2, 0, 359275, 107579, 1249, 16384⟩
    (by decide) selected_cut_13709

theorem unmarked_context_12_26894_359276 : frontier 9 ⟨359276, by decide⟩
    (prefixCache 12 26894) (prefixPartial 12 26894) = false := by
  decide +kernel

theorem node_context_12_26894_359276 : EJMOriginalGlobalDAGData.nodes 9 ⟨359276, by decide⟩ =
    .split (coordinate 12) (![⟨359153, by decide⟩,⟨359216, by decide⟩,⟨359262, by decide⟩,⟨359275, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26894_359276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26894 ⟨359276, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26894
    ⟨359276, by decide⟩ (by decide) (![⟨359153, by decide⟩,⟨359216, by decide⟩,⟨359262, by decide⟩,⟨359275, by decide⟩]) unmarked_context_12_26894_359276 node_context_12_26894_359276
  intro a
  fin_cases a
  · exact context_13_107576_359153
  · exact context_13_107577_359216
  · exact context_13_107578_359262
  · exact context_13_107579_359275

theorem selected_cut_13710 : selected 8 ⟨359324, by decide⟩
    (prefixPartial 13 107580) = some ⟨13, 2, 0, 359324, 107580, 3657, 16384⟩ := by
  decide +kernel

theorem context_13_107580_359324 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107580 ⟨359324, by decide⟩ :=
  accepted_of_selected 13 107580 ⟨359324, by decide⟩ ⟨13, 2, 0, 359324, 107580, 3657, 16384⟩
    (by decide) selected_cut_13710

theorem selected_cut_13711 : selected 8 ⟨359369, by decide⟩
    (prefixPartial 13 107581) = some ⟨13, 2, 0, 359369, 107581, 3785, 16384⟩ := by
  decide +kernel

theorem context_13_107581_359369 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107581 ⟨359369, by decide⟩ :=
  accepted_of_selected 13 107581 ⟨359369, by decide⟩ ⟨13, 2, 0, 359369, 107581, 3785, 16384⟩
    (by decide) selected_cut_13711

theorem selected_cut_13712 : selected 8 ⟨359404, by decide⟩
    (prefixPartial 13 107582) = some ⟨13, 2, 0, 359404, 107582, 2477, 16384⟩ := by
  decide +kernel

theorem context_13_107582_359404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107582 ⟨359404, by decide⟩ :=
  accepted_of_selected 13 107582 ⟨359404, by decide⟩ ⟨13, 2, 0, 359404, 107582, 2477, 16384⟩
    (by decide) selected_cut_13712

theorem selected_cut_13713 : selected 8 ⟨359422, by decide⟩
    (prefixPartial 13 107583) = some ⟨13, 2, 0, 359422, 107583, 1253, 16384⟩ := by
  decide +kernel

theorem context_13_107583_359422 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107583 ⟨359422, by decide⟩ :=
  accepted_of_selected 13 107583 ⟨359422, by decide⟩ ⟨13, 2, 0, 359422, 107583, 1253, 16384⟩
    (by decide) selected_cut_13713

theorem unmarked_context_12_26895_359423 : frontier 9 ⟨359423, by decide⟩
    (prefixCache 12 26895) (prefixPartial 12 26895) = false := by
  decide +kernel

theorem node_context_12_26895_359423 : EJMOriginalGlobalDAGData.nodes 9 ⟨359423, by decide⟩ =
    .split (coordinate 12) (![⟨359324, by decide⟩,⟨359369, by decide⟩,⟨359404, by decide⟩,⟨359422, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26895_359423 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26895 ⟨359423, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26895
    ⟨359423, by decide⟩ (by decide) (![⟨359324, by decide⟩,⟨359369, by decide⟩,⟨359404, by decide⟩,⟨359422, by decide⟩]) unmarked_context_12_26895_359423 node_context_12_26895_359423
  intro a
  fin_cases a
  · exact context_13_107580_359324
  · exact context_13_107581_359369
  · exact context_13_107582_359404
  · exact context_13_107583_359422

theorem unmarked_context_11_6723_359424 : frontier 10 ⟨359424, by decide⟩
    (prefixCache 11 6723) (prefixPartial 11 6723) = false := by
  decide +kernel

theorem node_context_11_6723_359424 : EJMOriginalGlobalDAGData.nodes 10 ⟨359424, by decide⟩ =
    .split (coordinate 11) (![⟨358996, by decide⟩,⟨359096, by decide⟩,⟨359276, by decide⟩,⟨359423, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6723_359424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6723 ⟨359424, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6723
    ⟨359424, by decide⟩ (by decide) (![⟨358996, by decide⟩,⟨359096, by decide⟩,⟨359276, by decide⟩,⟨359423, by decide⟩]) unmarked_context_11_6723_359424 node_context_11_6723_359424
  intro a
  fin_cases a
  · exact context_12_26892_358996
  · exact context_12_26893_359096
  · exact context_12_26894_359276
  · exact context_12_26895_359423

theorem unmarked_context_10_1680_359425 : frontier 11 ⟨359425, by decide⟩
    (prefixCache 10 1680) (prefixPartial 10 1680) = false := by
  decide +kernel

theorem node_context_10_1680_359425 : EJMOriginalGlobalDAGData.nodes 11 ⟨359425, by decide⟩ =
    .split (coordinate 10) (![⟨357522, by decide⟩,⟨358201, by decide⟩,⟨358849, by decide⟩,⟨359424, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1680_359425 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1680 ⟨359425, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1680
    ⟨359425, by decide⟩ (by decide) (![⟨357522, by decide⟩,⟨358201, by decide⟩,⟨358849, by decide⟩,⟨359424, by decide⟩]) unmarked_context_10_1680_359425 node_context_10_1680_359425
  intro a
  fin_cases a
  · exact context_11_6720_357522
  · exact context_11_6721_358201
  · exact context_11_6722_358849
  · exact context_11_6723_359424

theorem selected_cut_13714 : selected 8 ⟨359442, by decide⟩
    (prefixPartial 13 107584) = some ⟨13, 2, 0, 359442, 107584, 1593, 16384⟩ := by
  decide +kernel

theorem context_13_107584_359442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107584 ⟨359442, by decide⟩ :=
  accepted_of_selected 13 107584 ⟨359442, by decide⟩ ⟨13, 2, 0, 359442, 107584, 1593, 16384⟩
    (by decide) selected_cut_13714

theorem selected_cut_13715 : selected 8 ⟨359464, by decide⟩
    (prefixPartial 13 107585) = some ⟨13, 2, 0, 359464, 107585, 2113, 16384⟩ := by
  decide +kernel

theorem context_13_107585_359464 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107585 ⟨359464, by decide⟩ :=
  accepted_of_selected 13 107585 ⟨359464, by decide⟩ ⟨13, 2, 0, 359464, 107585, 2113, 16384⟩
    (by decide) selected_cut_13715

theorem selected_cut_13716 : selected 8 ⟨359478, by decide⟩
    (prefixPartial 13 107586) = some ⟨13, 2, 0, 359478, 107586, 1193, 16384⟩ := by
  decide +kernel

theorem context_13_107586_359478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107586 ⟨359478, by decide⟩ :=
  accepted_of_selected 13 107586 ⟨359478, by decide⟩ ⟨13, 2, 0, 359478, 107586, 1193, 16384⟩
    (by decide) selected_cut_13716

theorem selected_cut_13717 : selected 8 ⟨359485, by decide⟩
    (prefixPartial 13 107587) = some ⟨13, 2, 0, 359485, 107587, 821, 16384⟩ := by
  decide +kernel

theorem context_13_107587_359485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107587 ⟨359485, by decide⟩ :=
  accepted_of_selected 13 107587 ⟨359485, by decide⟩ ⟨13, 2, 0, 359485, 107587, 821, 16384⟩
    (by decide) selected_cut_13717

theorem unmarked_context_12_26896_359486 : frontier 9 ⟨359486, by decide⟩
    (prefixCache 12 26896) (prefixPartial 12 26896) = false := by
  decide +kernel

theorem node_context_12_26896_359486 : EJMOriginalGlobalDAGData.nodes 9 ⟨359486, by decide⟩ =
    .split (coordinate 12) (![⟨359442, by decide⟩,⟨359464, by decide⟩,⟨359478, by decide⟩,⟨359485, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26896_359486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26896 ⟨359486, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26896
    ⟨359486, by decide⟩ (by decide) (![⟨359442, by decide⟩,⟨359464, by decide⟩,⟨359478, by decide⟩,⟨359485, by decide⟩]) unmarked_context_12_26896_359486 node_context_12_26896_359486
  intro a
  fin_cases a
  · exact context_13_107584_359442
  · exact context_13_107585_359464
  · exact context_13_107586_359478
  · exact context_13_107587_359485

theorem selected_cut_13718 : selected 8 ⟨359505, by decide⟩
    (prefixPartial 13 107588) = some ⟨13, 2, 0, 359505, 107588, 1561, 16384⟩ := by
  decide +kernel

theorem context_13_107588_359505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107588 ⟨359505, by decide⟩ :=
  accepted_of_selected 13 107588 ⟨359505, by decide⟩ ⟨13, 2, 0, 359505, 107588, 1561, 16384⟩
    (by decide) selected_cut_13718

theorem selected_cut_13719 : selected 8 ⟨359525, by decide⟩
    (prefixPartial 13 107589) = some ⟨13, 2, 0, 359525, 107589, 1693, 16384⟩ := by
  decide +kernel

theorem context_13_107589_359525 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107589 ⟨359525, by decide⟩ :=
  accepted_of_selected 13 107589 ⟨359525, by decide⟩ ⟨13, 2, 0, 359525, 107589, 1693, 16384⟩
    (by decide) selected_cut_13719

theorem selected_cut_13720 : selected 8 ⟨359540, by decide⟩
    (prefixPartial 13 107590) = some ⟨13, 2, 0, 359540, 107590, 1345, 16384⟩ := by
  decide +kernel

theorem context_13_107590_359540 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107590 ⟨359540, by decide⟩ :=
  accepted_of_selected 13 107590 ⟨359540, by decide⟩ ⟨13, 2, 0, 359540, 107590, 1345, 16384⟩
    (by decide) selected_cut_13720

theorem selected_cut_13721 : selected 8 ⟨359546, by decide⟩
    (prefixPartial 13 107591) = some ⟨13, 2, 0, 359546, 107591, 833, 16384⟩ := by
  decide +kernel

theorem context_13_107591_359546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107591 ⟨359546, by decide⟩ :=
  accepted_of_selected 13 107591 ⟨359546, by decide⟩ ⟨13, 2, 0, 359546, 107591, 833, 16384⟩
    (by decide) selected_cut_13721

theorem unmarked_context_12_26897_359547 : frontier 9 ⟨359547, by decide⟩
    (prefixCache 12 26897) (prefixPartial 12 26897) = false := by
  decide +kernel

theorem node_context_12_26897_359547 : EJMOriginalGlobalDAGData.nodes 9 ⟨359547, by decide⟩ =
    .split (coordinate 12) (![⟨359505, by decide⟩,⟨359525, by decide⟩,⟨359540, by decide⟩,⟨359546, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26897_359547 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26897 ⟨359547, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26897
    ⟨359547, by decide⟩ (by decide) (![⟨359505, by decide⟩,⟨359525, by decide⟩,⟨359540, by decide⟩,⟨359546, by decide⟩]) unmarked_context_12_26897_359547 node_context_12_26897_359547
  intro a
  fin_cases a
  · exact context_13_107588_359505
  · exact context_13_107589_359525
  · exact context_13_107590_359540
  · exact context_13_107591_359546

theorem selected_cut_13722 : selected 8 ⟨359572, by decide⟩
    (prefixPartial 13 107592) = some ⟨13, 2, 0, 359572, 107592, 1945, 16384⟩ := by
  decide +kernel

theorem context_13_107592_359572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107592 ⟨359572, by decide⟩ :=
  accepted_of_selected 13 107592 ⟨359572, by decide⟩ ⟨13, 2, 0, 359572, 107592, 1945, 16384⟩
    (by decide) selected_cut_13722

theorem selected_cut_13723 : selected 8 ⟨359597, by decide⟩
    (prefixPartial 13 107593) = some ⟨13, 2, 0, 359597, 107593, 2281, 16384⟩ := by
  decide +kernel

theorem context_13_107593_359597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107593 ⟨359597, by decide⟩ :=
  accepted_of_selected 13 107593 ⟨359597, by decide⟩ ⟨13, 2, 0, 359597, 107593, 2281, 16384⟩
    (by decide) selected_cut_13723

theorem selected_cut_13724 : selected 8 ⟨359616, by decide⟩
    (prefixPartial 13 107594) = some ⟨13, 2, 0, 359616, 107594, 1665, 16384⟩ := by
  decide +kernel

theorem context_13_107594_359616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107594 ⟨359616, by decide⟩ :=
  accepted_of_selected 13 107594 ⟨359616, by decide⟩ ⟨13, 2, 0, 359616, 107594, 1665, 16384⟩
    (by decide) selected_cut_13724

theorem selected_cut_13725 : selected 8 ⟨359623, by decide⟩
    (prefixPartial 13 107595) = some ⟨13, 2, 0, 359623, 107595, 997, 16384⟩ := by
  decide +kernel

theorem context_13_107595_359623 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107595 ⟨359623, by decide⟩ :=
  accepted_of_selected 13 107595 ⟨359623, by decide⟩ ⟨13, 2, 0, 359623, 107595, 997, 16384⟩
    (by decide) selected_cut_13725

theorem unmarked_context_12_26898_359624 : frontier 9 ⟨359624, by decide⟩
    (prefixCache 12 26898) (prefixPartial 12 26898) = false := by
  decide +kernel

theorem node_context_12_26898_359624 : EJMOriginalGlobalDAGData.nodes 9 ⟨359624, by decide⟩ =
    .split (coordinate 12) (![⟨359572, by decide⟩,⟨359597, by decide⟩,⟨359616, by decide⟩,⟨359623, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26898_359624 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26898 ⟨359624, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26898
    ⟨359624, by decide⟩ (by decide) (![⟨359572, by decide⟩,⟨359597, by decide⟩,⟨359616, by decide⟩,⟨359623, by decide⟩]) unmarked_context_12_26898_359624 node_context_12_26898_359624
  intro a
  fin_cases a
  · exact context_13_107592_359572
  · exact context_13_107593_359597
  · exact context_13_107594_359616
  · exact context_13_107595_359623

theorem selected_cut_13726 : selected 8 ⟨359646, by decide⟩
    (prefixPartial 13 107596) = some ⟨13, 2, 0, 359646, 107596, 1957, 16384⟩ := by
  decide +kernel

theorem context_13_107596_359646 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107596 ⟨359646, by decide⟩ :=
  accepted_of_selected 13 107596 ⟨359646, by decide⟩ ⟨13, 2, 0, 359646, 107596, 1957, 16384⟩
    (by decide) selected_cut_13726

theorem selected_cut_13727 : selected 8 ⟨359673, by decide⟩
    (prefixPartial 13 107597) = some ⟨13, 2, 0, 359673, 107597, 2389, 16384⟩ := by
  decide +kernel

theorem context_13_107597_359673 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107597 ⟨359673, by decide⟩ :=
  accepted_of_selected 13 107597 ⟨359673, by decide⟩ ⟨13, 2, 0, 359673, 107597, 2389, 16384⟩
    (by decide) selected_cut_13727

theorem selected_cut_13728 : selected 8 ⟨359692, by decide⟩
    (prefixPartial 13 107598) = some ⟨13, 2, 0, 359692, 107598, 1569, 16384⟩ := by
  decide +kernel

theorem context_13_107598_359692 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107598 ⟨359692, by decide⟩ :=
  accepted_of_selected 13 107598 ⟨359692, by decide⟩ ⟨13, 2, 0, 359692, 107598, 1569, 16384⟩
    (by decide) selected_cut_13728

theorem selected_cut_13729 : selected 8 ⟨359703, by decide⟩
    (prefixPartial 13 107599) = some ⟨13, 2, 0, 359703, 107599, 1013, 16384⟩ := by
  decide +kernel

theorem context_13_107599_359703 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 107599 ⟨359703, by decide⟩ :=
  accepted_of_selected 13 107599 ⟨359703, by decide⟩ ⟨13, 2, 0, 359703, 107599, 1013, 16384⟩
    (by decide) selected_cut_13729

theorem unmarked_context_12_26899_359704 : frontier 9 ⟨359704, by decide⟩
    (prefixCache 12 26899) (prefixPartial 12 26899) = false := by
  decide +kernel

theorem node_context_12_26899_359704 : EJMOriginalGlobalDAGData.nodes 9 ⟨359704, by decide⟩ =
    .split (coordinate 12) (![⟨359646, by decide⟩,⟨359673, by decide⟩,⟨359692, by decide⟩,⟨359703, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26899_359704 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26899 ⟨359704, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26899
    ⟨359704, by decide⟩ (by decide) (![⟨359646, by decide⟩,⟨359673, by decide⟩,⟨359692, by decide⟩,⟨359703, by decide⟩]) unmarked_context_12_26899_359704 node_context_12_26899_359704
  intro a
  fin_cases a
  · exact context_13_107596_359646
  · exact context_13_107597_359673
  · exact context_13_107598_359692
  · exact context_13_107599_359703

theorem unmarked_context_11_6724_359705 : frontier 10 ⟨359705, by decide⟩
    (prefixCache 11 6724) (prefixPartial 11 6724) = false := by
  decide +kernel

theorem node_context_11_6724_359705 : EJMOriginalGlobalDAGData.nodes 10 ⟨359705, by decide⟩ =
    .split (coordinate 11) (![⟨359486, by decide⟩,⟨359547, by decide⟩,⟨359624, by decide⟩,⟨359704, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6724_359705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6724 ⟨359705, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6724
    ⟨359705, by decide⟩ (by decide) (![⟨359486, by decide⟩,⟨359547, by decide⟩,⟨359624, by decide⟩,⟨359704, by decide⟩]) unmarked_context_11_6724_359705 node_context_11_6724_359705
  intro a
  fin_cases a
  · exact context_12_26896_359486
  · exact context_12_26897_359547
  · exact context_12_26898_359624
  · exact context_12_26899_359704

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
