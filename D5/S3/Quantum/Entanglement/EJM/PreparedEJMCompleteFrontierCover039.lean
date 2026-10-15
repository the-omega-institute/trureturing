/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover038
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_03746 : selected 7 ⟨118205, by decide⟩
    (prefixPartial 14 278705) = some ⟨14, 2, 0, 118205, 278705, 1857, 4096⟩ := by
  decide +kernel

theorem context_14_278705_118205 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 278705 ⟨118205, by decide⟩ :=
  accepted_of_selected 14 278705 ⟨118205, by decide⟩ ⟨14, 2, 0, 118205, 278705, 1857, 4096⟩
    (by decide) selected_cut_03746

theorem selected_cut_03747 : selected 7 ⟨118249, by decide⟩
    (prefixPartial 14 278706) = some ⟨14, 2, 0, 118249, 278706, 1433, 4096⟩ := by
  decide +kernel

theorem context_14_278706_118249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 278706 ⟨118249, by decide⟩ :=
  accepted_of_selected 14 278706 ⟨118249, by decide⟩ ⟨14, 2, 0, 118249, 278706, 1433, 4096⟩
    (by decide) selected_cut_03747

theorem selected_cut_03748 : selected 7 ⟨118293, by decide⟩
    (prefixPartial 14 278707) = some ⟨14, 2, 0, 118293, 278707, 1321, 4096⟩ := by
  decide +kernel

theorem context_14_278707_118293 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 278707 ⟨118293, by decide⟩ :=
  accepted_of_selected 14 278707 ⟨118293, by decide⟩ ⟨14, 2, 0, 118293, 278707, 1321, 4096⟩
    (by decide) selected_cut_03748

theorem unmarked_context_13_69676_118294 : frontier 8 ⟨118294, by decide⟩
    (prefixCache 13 69676) (prefixPartial 13 69676) = false := by
  decide +kernel

theorem node_context_13_69676_118294 : EJMOriginalGlobalDAGData.nodes 8 ⟨118294, by decide⟩ =
    .split (coordinate 13) (![⟨118152, by decide⟩,⟨118205, by decide⟩,⟨118249, by decide⟩,⟨118293, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_69676_118294 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69676 ⟨118294, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 69676
    ⟨118294, by decide⟩ (by decide) (![⟨118152, by decide⟩,⟨118205, by decide⟩,⟨118249, by decide⟩,⟨118293, by decide⟩]) unmarked_context_13_69676_118294 node_context_13_69676_118294
  intro a
  fin_cases a
  · exact context_14_278704_118152
  · exact context_14_278705_118205
  · exact context_14_278706_118249
  · exact context_14_278707_118293

theorem selected_cut_03749 : selected 8 ⟨118431, by decide⟩
    (prefixPartial 13 69677) = some ⟨13, 2, 0, 118431, 69677, 2977, 16384⟩ := by
  decide +kernel

theorem context_13_69677_118431 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69677 ⟨118431, by decide⟩ :=
  accepted_of_selected 13 69677 ⟨118431, by decide⟩ ⟨13, 2, 0, 118431, 69677, 2977, 16384⟩
    (by decide) selected_cut_03749

theorem selected_cut_03750 : selected 8 ⟨118470, by decide⟩
    (prefixPartial 13 69678) = some ⟨13, 2, 0, 118470, 69678, 689, 16384⟩ := by
  decide +kernel

theorem context_13_69678_118470 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69678 ⟨118470, by decide⟩ :=
  accepted_of_selected 13 69678 ⟨118470, by decide⟩ ⟨13, 2, 0, 118470, 69678, 689, 16384⟩
    (by decide) selected_cut_03750

theorem selected_cut_03751 : selected 8 ⟨118485, by decide⟩
    (prefixPartial 13 69679) = some ⟨13, 2, 0, 118485, 69679, 157, 16384⟩ := by
  decide +kernel

theorem context_13_69679_118485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69679 ⟨118485, by decide⟩ :=
  accepted_of_selected 13 69679 ⟨118485, by decide⟩ ⟨13, 2, 0, 118485, 69679, 157, 16384⟩
    (by decide) selected_cut_03751

theorem unmarked_context_12_17419_118486 : frontier 9 ⟨118486, by decide⟩
    (prefixCache 12 17419) (prefixPartial 12 17419) = false := by
  decide +kernel

theorem node_context_12_17419_118486 : EJMOriginalGlobalDAGData.nodes 9 ⟨118486, by decide⟩ =
    .split (coordinate 12) (![⟨118294, by decide⟩,⟨118431, by decide⟩,⟨118470, by decide⟩,⟨118485, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17419_118486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17419 ⟨118486, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17419
    ⟨118486, by decide⟩ (by decide) (![⟨118294, by decide⟩,⟨118431, by decide⟩,⟨118470, by decide⟩,⟨118485, by decide⟩]) unmarked_context_12_17419_118486 node_context_12_17419_118486
  intro a
  fin_cases a
  · exact context_13_69676_118294
  · exact context_13_69677_118431
  · exact context_13_69678_118470
  · exact context_13_69679_118485

theorem unmarked_context_11_4354_118487 : frontier 10 ⟨118487, by decide⟩
    (prefixCache 11 4354) (prefixPartial 11 4354) = false := by
  decide +kernel

theorem node_context_11_4354_118487 : EJMOriginalGlobalDAGData.nodes 10 ⟨118487, by decide⟩ =
    .split (coordinate 11) (![⟨895, by decide⟩,⟨895, by decide⟩,⟨118137, by decide⟩,⟨118486, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4354_118487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4354 ⟨118487, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4354
    ⟨118487, by decide⟩ (by decide) (![⟨895, by decide⟩,⟨895, by decide⟩,⟨118137, by decide⟩,⟨118486, by decide⟩]) unmarked_context_11_4354_118487 node_context_11_4354_118487
  intro a
  fin_cases a
  · exact context_12_17416_895
  · exact context_12_17417_895
  · exact context_12_17418_118137
  · exact context_12_17419_118486

theorem selected_cut_03752 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 4355) = some ⟨11, 1, 0, 1736, 4355, 1, 262144⟩ := by
  decide +kernel

theorem context_11_4355_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4355 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 4355 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 4355, 1, 262144⟩
    (by decide) selected_cut_03752

theorem unmarked_context_10_1088_118488 : frontier 11 ⟨118488, by decide⟩
    (prefixCache 10 1088) (prefixPartial 10 1088) = false := by
  decide +kernel

theorem node_context_10_1088_118488 : EJMOriginalGlobalDAGData.nodes 11 ⟨118488, by decide⟩ =
    .split (coordinate 10) (![⟨117234, by decide⟩,⟨117835, by decide⟩,⟨118487, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1088_118488 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1088 ⟨118488, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1088
    ⟨118488, by decide⟩ (by decide) (![⟨117234, by decide⟩,⟨117835, by decide⟩,⟨118487, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_1088_118488 node_context_10_1088_118488
  intro a
  fin_cases a
  · exact context_11_4352_117234
  · exact context_11_4353_117835
  · exact context_11_4354_118487
  · exact context_11_4355_1736

theorem selected_cut_03753 : selected 9 ⟨118489, by decide⟩
    (prefixPartial 12 17424) = some ⟨12, 1, 0, 118489, 17424, 1, 65536⟩ := by
  decide +kernel

theorem context_12_17424_118489 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17424 ⟨118489, by decide⟩ :=
  accepted_of_selected 12 17424 ⟨118489, by decide⟩ ⟨12, 1, 0, 118489, 17424, 1, 65536⟩
    (by decide) selected_cut_03753

theorem selected_cut_03754 : selected 9 ⟨118641, by decide⟩
    (prefixPartial 12 17425) = some ⟨12, 2, 0, 118641, 17425, 2425, 65536⟩ := by
  decide +kernel

theorem context_12_17425_118641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17425 ⟨118641, by decide⟩ :=
  accepted_of_selected 12 17425 ⟨118641, by decide⟩ ⟨12, 2, 0, 118641, 17425, 2425, 65536⟩
    (by decide) selected_cut_03754

theorem selected_cut_03755 : selected 8 ⟨118715, by decide⟩
    (prefixPartial 13 69704) = some ⟨13, 2, 0, 118715, 69704, 2673, 16384⟩ := by
  decide +kernel

theorem context_13_69704_118715 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69704 ⟨118715, by decide⟩ :=
  accepted_of_selected 13 69704 ⟨118715, by decide⟩ ⟨13, 2, 0, 118715, 69704, 2673, 16384⟩
    (by decide) selected_cut_03755

theorem selected_cut_03756 : selected 8 ⟨118769, by decide⟩
    (prefixPartial 13 69705) = some ⟨13, 2, 0, 118769, 69705, 2249, 16384⟩ := by
  decide +kernel

theorem context_13_69705_118769 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69705 ⟨118769, by decide⟩ :=
  accepted_of_selected 13 69705 ⟨118769, by decide⟩ ⟨13, 2, 0, 118769, 69705, 2249, 16384⟩
    (by decide) selected_cut_03756

theorem selected_cut_03757 : selected 8 ⟨118800, by decide⟩
    (prefixPartial 13 69706) = some ⟨13, 2, 0, 118800, 69706, 1501, 16384⟩ := by
  decide +kernel

theorem context_13_69706_118800 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69706 ⟨118800, by decide⟩ :=
  accepted_of_selected 13 69706 ⟨118800, by decide⟩ ⟨13, 2, 0, 118800, 69706, 1501, 16384⟩
    (by decide) selected_cut_03757

theorem selected_cut_03758 : selected 8 ⟨118818, by decide⟩
    (prefixPartial 13 69707) = some ⟨13, 2, 0, 118818, 69707, 921, 16384⟩ := by
  decide +kernel

theorem context_13_69707_118818 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69707 ⟨118818, by decide⟩ :=
  accepted_of_selected 13 69707 ⟨118818, by decide⟩ ⟨13, 2, 0, 118818, 69707, 921, 16384⟩
    (by decide) selected_cut_03758

theorem unmarked_context_12_17426_118819 : frontier 9 ⟨118819, by decide⟩
    (prefixCache 12 17426) (prefixPartial 12 17426) = false := by
  decide +kernel

theorem node_context_12_17426_118819 : EJMOriginalGlobalDAGData.nodes 9 ⟨118819, by decide⟩ =
    .split (coordinate 12) (![⟨118715, by decide⟩,⟨118769, by decide⟩,⟨118800, by decide⟩,⟨118818, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17426_118819 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17426 ⟨118819, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17426
    ⟨118819, by decide⟩ (by decide) (![⟨118715, by decide⟩,⟨118769, by decide⟩,⟨118800, by decide⟩,⟨118818, by decide⟩]) unmarked_context_12_17426_118819 node_context_12_17426_118819
  intro a
  fin_cases a
  · exact context_13_69704_118715
  · exact context_13_69705_118769
  · exact context_13_69706_118800
  · exact context_13_69707_118818

theorem selected_cut_03759 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 17427) = some ⟨12, 1, 0, 893, 17427, 1, 65536⟩ := by
  decide +kernel

theorem context_12_17427_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17427 ⟨893, by decide⟩ :=
  accepted_of_selected 12 17427 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 17427, 1, 65536⟩
    (by decide) selected_cut_03759

theorem unmarked_context_11_4356_118820 : frontier 10 ⟨118820, by decide⟩
    (prefixCache 11 4356) (prefixPartial 11 4356) = false := by
  decide +kernel

theorem node_context_11_4356_118820 : EJMOriginalGlobalDAGData.nodes 10 ⟨118820, by decide⟩ =
    .split (coordinate 11) (![⟨118489, by decide⟩,⟨118641, by decide⟩,⟨118819, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4356_118820 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4356 ⟨118820, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4356
    ⟨118820, by decide⟩ (by decide) (![⟨118489, by decide⟩,⟨118641, by decide⟩,⟨118819, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_4356_118820 node_context_11_4356_118820
  intro a
  fin_cases a
  · exact context_12_17424_118489
  · exact context_12_17425_118641
  · exact context_12_17426_118819
  · exact context_12_17427_893

theorem selected_cut_03760 : selected 9 ⟨119014, by decide⟩
    (prefixPartial 12 17428) = some ⟨12, 2, 0, 119014, 17428, 3585, 65536⟩ := by
  decide +kernel

theorem context_12_17428_119014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17428 ⟨119014, by decide⟩ :=
  accepted_of_selected 12 17428 ⟨119014, by decide⟩ ⟨12, 2, 0, 119014, 17428, 3585, 65536⟩
    (by decide) selected_cut_03760

theorem selected_cut_03761 : selected 8 ⟨119054, by decide⟩
    (prefixPartial 13 69716) = some ⟨13, 2, 0, 119054, 69716, 1521, 16384⟩ := by
  decide +kernel

theorem context_13_69716_119054 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69716 ⟨119054, by decide⟩ :=
  accepted_of_selected 13 69716 ⟨119054, by decide⟩ ⟨13, 2, 0, 119054, 69716, 1521, 16384⟩
    (by decide) selected_cut_03761

theorem selected_cut_03762 : selected 8 ⟨119112, by decide⟩
    (prefixPartial 13 69717) = some ⟨13, 2, 0, 119112, 69717, 1709, 16384⟩ := by
  decide +kernel

theorem context_13_69717_119112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69717 ⟨119112, by decide⟩ :=
  accepted_of_selected 13 69717 ⟨119112, by decide⟩ ⟨13, 2, 0, 119112, 69717, 1709, 16384⟩
    (by decide) selected_cut_03762

theorem selected_cut_03763 : selected 8 ⟨119149, by decide⟩
    (prefixPartial 13 69718) = some ⟨13, 2, 0, 119149, 69718, 1897, 16384⟩ := by
  decide +kernel

theorem context_13_69718_119149 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69718 ⟨119149, by decide⟩ :=
  accepted_of_selected 13 69718 ⟨119149, by decide⟩ ⟨13, 2, 0, 119149, 69718, 1897, 16384⟩
    (by decide) selected_cut_03763

theorem selected_cut_03764 : selected 8 ⟨414, by decide⟩
    (prefixPartial 13 69719) = some ⟨13, 1, 0, 414, 69719, 1, 16384⟩ := by
  decide +kernel

theorem context_13_69719_414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69719 ⟨414, by decide⟩ :=
  accepted_of_selected 13 69719 ⟨414, by decide⟩ ⟨13, 1, 0, 414, 69719, 1, 16384⟩
    (by decide) selected_cut_03764

theorem unmarked_context_12_17429_119150 : frontier 9 ⟨119150, by decide⟩
    (prefixCache 12 17429) (prefixPartial 12 17429) = false := by
  decide +kernel

theorem node_context_12_17429_119150 : EJMOriginalGlobalDAGData.nodes 9 ⟨119150, by decide⟩ =
    .split (coordinate 12) (![⟨119054, by decide⟩,⟨119112, by decide⟩,⟨119149, by decide⟩,⟨414, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17429_119150 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17429 ⟨119150, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17429
    ⟨119150, by decide⟩ (by decide) (![⟨119054, by decide⟩,⟨119112, by decide⟩,⟨119149, by decide⟩,⟨414, by decide⟩]) unmarked_context_12_17429_119150 node_context_12_17429_119150
  intro a
  fin_cases a
  · exact context_13_69716_119054
  · exact context_13_69717_119112
  · exact context_13_69718_119149
  · exact context_13_69719_414

theorem selected_cut_03765 : selected 8 ⟨119268, by decide⟩
    (prefixPartial 13 69720) = some ⟨13, 2, 0, 119268, 69720, 3657, 16384⟩ := by
  decide +kernel

theorem context_13_69720_119268 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69720 ⟨119268, by decide⟩ :=
  accepted_of_selected 13 69720 ⟨119268, by decide⟩ ⟨13, 2, 0, 119268, 69720, 3657, 16384⟩
    (by decide) selected_cut_03765

theorem selected_cut_03766 : selected 8 ⟨119401, by decide⟩
    (prefixPartial 13 69721) = some ⟨13, 2, 0, 119401, 69721, 3945, 16384⟩ := by
  decide +kernel

theorem context_13_69721_119401 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69721 ⟨119401, by decide⟩ :=
  accepted_of_selected 13 69721 ⟨119401, by decide⟩ ⟨13, 2, 0, 119401, 69721, 3945, 16384⟩
    (by decide) selected_cut_03766

theorem selected_cut_03767 : selected 8 ⟨119440, by decide⟩
    (prefixPartial 13 69722) = some ⟨13, 2, 0, 119440, 69722, 2261, 16384⟩ := by
  decide +kernel

theorem context_13_69722_119440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69722 ⟨119440, by decide⟩ :=
  accepted_of_selected 13 69722 ⟨119440, by decide⟩ ⟨13, 2, 0, 119440, 69722, 2261, 16384⟩
    (by decide) selected_cut_03767

theorem selected_cut_03768 : selected 8 ⟨119473, by decide⟩
    (prefixPartial 13 69723) = some ⟨13, 2, 0, 119473, 69723, 1229, 16384⟩ := by
  decide +kernel

theorem context_13_69723_119473 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69723 ⟨119473, by decide⟩ :=
  accepted_of_selected 13 69723 ⟨119473, by decide⟩ ⟨13, 2, 0, 119473, 69723, 1229, 16384⟩
    (by decide) selected_cut_03768

theorem unmarked_context_12_17430_119474 : frontier 9 ⟨119474, by decide⟩
    (prefixCache 12 17430) (prefixPartial 12 17430) = false := by
  decide +kernel

theorem node_context_12_17430_119474 : EJMOriginalGlobalDAGData.nodes 9 ⟨119474, by decide⟩ =
    .split (coordinate 12) (![⟨119268, by decide⟩,⟨119401, by decide⟩,⟨119440, by decide⟩,⟨119473, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17430_119474 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17430 ⟨119474, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17430
    ⟨119474, by decide⟩ (by decide) (![⟨119268, by decide⟩,⟨119401, by decide⟩,⟨119440, by decide⟩,⟨119473, by decide⟩]) unmarked_context_12_17430_119474 node_context_12_17430_119474
  intro a
  fin_cases a
  · exact context_13_69720_119268
  · exact context_13_69721_119401
  · exact context_13_69722_119440
  · exact context_13_69723_119473

theorem selected_cut_03769 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 17431) = some ⟨12, 1, 0, 893, 17431, 1, 65536⟩ := by
  decide +kernel

theorem context_12_17431_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17431 ⟨893, by decide⟩ :=
  accepted_of_selected 12 17431 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 17431, 1, 65536⟩
    (by decide) selected_cut_03769

theorem unmarked_context_11_4357_119475 : frontier 10 ⟨119475, by decide⟩
    (prefixCache 11 4357) (prefixPartial 11 4357) = false := by
  decide +kernel

theorem node_context_11_4357_119475 : EJMOriginalGlobalDAGData.nodes 10 ⟨119475, by decide⟩ =
    .split (coordinate 11) (![⟨119014, by decide⟩,⟨119150, by decide⟩,⟨119474, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4357_119475 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4357 ⟨119475, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4357
    ⟨119475, by decide⟩ (by decide) (![⟨119014, by decide⟩,⟨119150, by decide⟩,⟨119474, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_4357_119475 node_context_11_4357_119475
  intro a
  fin_cases a
  · exact context_12_17428_119014
  · exact context_12_17429_119150
  · exact context_12_17430_119474
  · exact context_12_17431_893

theorem selected_cut_03770 : selected 8 ⟨119513, by decide⟩
    (prefixPartial 13 69728) = some ⟨13, 2, 0, 119513, 69728, 1289, 16384⟩ := by
  decide +kernel

theorem context_13_69728_119513 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69728 ⟨119513, by decide⟩ :=
  accepted_of_selected 13 69728 ⟨119513, by decide⟩ ⟨13, 2, 0, 119513, 69728, 1289, 16384⟩
    (by decide) selected_cut_03770

theorem selected_cut_03771 : selected 8 ⟨119554, by decide⟩
    (prefixPartial 13 69729) = some ⟨13, 2, 0, 119554, 69729, 2097, 16384⟩ := by
  decide +kernel

theorem context_13_69729_119554 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69729 ⟨119554, by decide⟩ :=
  accepted_of_selected 13 69729 ⟨119554, by decide⟩ ⟨13, 2, 0, 119554, 69729, 2097, 16384⟩
    (by decide) selected_cut_03771

theorem selected_cut_03772 : selected 8 ⟨119576, by decide⟩
    (prefixPartial 13 69730) = some ⟨13, 2, 0, 119576, 69730, 1789, 16384⟩ := by
  decide +kernel

theorem context_13_69730_119576 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69730 ⟨119576, by decide⟩ :=
  accepted_of_selected 13 69730 ⟨119576, by decide⟩ ⟨13, 2, 0, 119576, 69730, 1789, 16384⟩
    (by decide) selected_cut_03772

theorem selected_cut_03773 : selected 8 ⟨119589, by decide⟩
    (prefixPartial 13 69731) = some ⟨13, 2, 0, 119589, 69731, 997, 16384⟩ := by
  decide +kernel

theorem context_13_69731_119589 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69731 ⟨119589, by decide⟩ :=
  accepted_of_selected 13 69731 ⟨119589, by decide⟩ ⟨13, 2, 0, 119589, 69731, 997, 16384⟩
    (by decide) selected_cut_03773

theorem unmarked_context_12_17432_119590 : frontier 9 ⟨119590, by decide⟩
    (prefixCache 12 17432) (prefixPartial 12 17432) = false := by
  decide +kernel

theorem node_context_12_17432_119590 : EJMOriginalGlobalDAGData.nodes 9 ⟨119590, by decide⟩ =
    .split (coordinate 12) (![⟨119513, by decide⟩,⟨119554, by decide⟩,⟨119576, by decide⟩,⟨119589, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17432_119590 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17432 ⟨119590, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17432
    ⟨119590, by decide⟩ (by decide) (![⟨119513, by decide⟩,⟨119554, by decide⟩,⟨119576, by decide⟩,⟨119589, by decide⟩]) unmarked_context_12_17432_119590 node_context_12_17432_119590
  intro a
  fin_cases a
  · exact context_13_69728_119513
  · exact context_13_69729_119554
  · exact context_13_69730_119576
  · exact context_13_69731_119589

theorem selected_cut_03774 : selected 8 ⟨119636, by decide⟩
    (prefixPartial 13 69732) = some ⟨13, 2, 0, 119636, 69732, 1985, 16384⟩ := by
  decide +kernel

theorem context_13_69732_119636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69732 ⟨119636, by decide⟩ :=
  accepted_of_selected 13 69732 ⟨119636, by decide⟩ ⟨13, 2, 0, 119636, 69732, 1985, 16384⟩
    (by decide) selected_cut_03774

theorem selected_cut_03775 : selected 8 ⟨119682, by decide⟩
    (prefixPartial 13 69733) = some ⟨13, 2, 0, 119682, 69733, 1941, 16384⟩ := by
  decide +kernel

theorem context_13_69733_119682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69733 ⟨119682, by decide⟩ :=
  accepted_of_selected 13 69733 ⟨119682, by decide⟩ ⟨13, 2, 0, 119682, 69733, 1941, 16384⟩
    (by decide) selected_cut_03775

theorem selected_cut_03776 : selected 8 ⟨119705, by decide⟩
    (prefixPartial 13 69734) = some ⟨13, 2, 0, 119705, 69734, 1817, 16384⟩ := by
  decide +kernel

theorem context_13_69734_119705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69734 ⟨119705, by decide⟩ :=
  accepted_of_selected 13 69734 ⟨119705, by decide⟩ ⟨13, 2, 0, 119705, 69734, 1817, 16384⟩
    (by decide) selected_cut_03776

theorem selected_cut_03777 : selected 8 ⟨119717, by decide⟩
    (prefixPartial 13 69735) = some ⟨13, 2, 0, 119717, 69735, 993, 16384⟩ := by
  decide +kernel

theorem context_13_69735_119717 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69735 ⟨119717, by decide⟩ :=
  accepted_of_selected 13 69735 ⟨119717, by decide⟩ ⟨13, 2, 0, 119717, 69735, 993, 16384⟩
    (by decide) selected_cut_03777

theorem unmarked_context_12_17433_119718 : frontier 9 ⟨119718, by decide⟩
    (prefixCache 12 17433) (prefixPartial 12 17433) = false := by
  decide +kernel

theorem node_context_12_17433_119718 : EJMOriginalGlobalDAGData.nodes 9 ⟨119718, by decide⟩ =
    .split (coordinate 12) (![⟨119636, by decide⟩,⟨119682, by decide⟩,⟨119705, by decide⟩,⟨119717, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17433_119718 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17433 ⟨119718, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17433
    ⟨119718, by decide⟩ (by decide) (![⟨119636, by decide⟩,⟨119682, by decide⟩,⟨119705, by decide⟩,⟨119717, by decide⟩]) unmarked_context_12_17433_119718 node_context_12_17433_119718
  intro a
  fin_cases a
  · exact context_13_69732_119636
  · exact context_13_69733_119682
  · exact context_13_69734_119705
  · exact context_13_69735_119717

theorem selected_cut_03778 : selected 8 ⟨119757, by decide⟩
    (prefixPartial 13 69736) = some ⟨13, 2, 0, 119757, 69736, 1673, 16384⟩ := by
  decide +kernel

theorem context_13_69736_119757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69736 ⟨119757, by decide⟩ :=
  accepted_of_selected 13 69736 ⟨119757, by decide⟩ ⟨13, 2, 0, 119757, 69736, 1673, 16384⟩
    (by decide) selected_cut_03778

theorem selected_cut_03779 : selected 8 ⟨119823, by decide⟩
    (prefixPartial 13 69737) = some ⟨13, 2, 0, 119823, 69737, 2081, 16384⟩ := by
  decide +kernel

theorem context_13_69737_119823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69737 ⟨119823, by decide⟩ :=
  accepted_of_selected 13 69737 ⟨119823, by decide⟩ ⟨13, 2, 0, 119823, 69737, 2081, 16384⟩
    (by decide) selected_cut_03779

theorem selected_cut_03780 : selected 8 ⟨119848, by decide⟩
    (prefixPartial 13 69738) = some ⟨13, 2, 0, 119848, 69738, 1425, 16384⟩ := by
  decide +kernel

theorem context_13_69738_119848 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69738 ⟨119848, by decide⟩ :=
  accepted_of_selected 13 69738 ⟨119848, by decide⟩ ⟨13, 2, 0, 119848, 69738, 1425, 16384⟩
    (by decide) selected_cut_03780

theorem selected_cut_03781 : selected 8 ⟨119863, by decide⟩
    (prefixPartial 13 69739) = some ⟨13, 2, 0, 119863, 69739, 965, 16384⟩ := by
  decide +kernel

theorem context_13_69739_119863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69739 ⟨119863, by decide⟩ :=
  accepted_of_selected 13 69739 ⟨119863, by decide⟩ ⟨13, 2, 0, 119863, 69739, 965, 16384⟩
    (by decide) selected_cut_03781

theorem unmarked_context_12_17434_119864 : frontier 9 ⟨119864, by decide⟩
    (prefixCache 12 17434) (prefixPartial 12 17434) = false := by
  decide +kernel

theorem node_context_12_17434_119864 : EJMOriginalGlobalDAGData.nodes 9 ⟨119864, by decide⟩ =
    .split (coordinate 12) (![⟨119757, by decide⟩,⟨119823, by decide⟩,⟨119848, by decide⟩,⟨119863, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17434_119864 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17434 ⟨119864, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17434
    ⟨119864, by decide⟩ (by decide) (![⟨119757, by decide⟩,⟨119823, by decide⟩,⟨119848, by decide⟩,⟨119863, by decide⟩]) unmarked_context_12_17434_119864 node_context_12_17434_119864
  intro a
  fin_cases a
  · exact context_13_69736_119757
  · exact context_13_69737_119823
  · exact context_13_69738_119848
  · exact context_13_69739_119863

theorem selected_cut_03782 : selected 8 ⟨119899, by decide⟩
    (prefixPartial 13 69740) = some ⟨13, 2, 0, 119899, 69740, 1833, 16384⟩ := by
  decide +kernel

theorem context_13_69740_119899 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69740 ⟨119899, by decide⟩ :=
  accepted_of_selected 13 69740 ⟨119899, by decide⟩ ⟨13, 2, 0, 119899, 69740, 1833, 16384⟩
    (by decide) selected_cut_03782

theorem selected_cut_03783 : selected 8 ⟨119954, by decide⟩
    (prefixPartial 13 69741) = some ⟨13, 2, 0, 119954, 69741, 2113, 16384⟩ := by
  decide +kernel

theorem context_13_69741_119954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69741 ⟨119954, by decide⟩ :=
  accepted_of_selected 13 69741 ⟨119954, by decide⟩ ⟨13, 2, 0, 119954, 69741, 2113, 16384⟩
    (by decide) selected_cut_03783

theorem selected_cut_03784 : selected 8 ⟨119977, by decide⟩
    (prefixPartial 13 69742) = some ⟨13, 2, 0, 119977, 69742, 1693, 16384⟩ := by
  decide +kernel

theorem context_13_69742_119977 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69742 ⟨119977, by decide⟩ :=
  accepted_of_selected 13 69742 ⟨119977, by decide⟩ ⟨13, 2, 0, 119977, 69742, 1693, 16384⟩
    (by decide) selected_cut_03784

theorem selected_cut_03785 : selected 8 ⟨119994, by decide⟩
    (prefixPartial 13 69743) = some ⟨13, 2, 0, 119994, 69743, 897, 16384⟩ := by
  decide +kernel

theorem context_13_69743_119994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69743 ⟨119994, by decide⟩ :=
  accepted_of_selected 13 69743 ⟨119994, by decide⟩ ⟨13, 2, 0, 119994, 69743, 897, 16384⟩
    (by decide) selected_cut_03785

theorem unmarked_context_12_17435_119995 : frontier 9 ⟨119995, by decide⟩
    (prefixCache 12 17435) (prefixPartial 12 17435) = false := by
  decide +kernel

theorem node_context_12_17435_119995 : EJMOriginalGlobalDAGData.nodes 9 ⟨119995, by decide⟩ =
    .split (coordinate 12) (![⟨119899, by decide⟩,⟨119954, by decide⟩,⟨119977, by decide⟩,⟨119994, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17435_119995 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17435 ⟨119995, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17435
    ⟨119995, by decide⟩ (by decide) (![⟨119899, by decide⟩,⟨119954, by decide⟩,⟨119977, by decide⟩,⟨119994, by decide⟩]) unmarked_context_12_17435_119995 node_context_12_17435_119995
  intro a
  fin_cases a
  · exact context_13_69740_119899
  · exact context_13_69741_119954
  · exact context_13_69742_119977
  · exact context_13_69743_119994

theorem unmarked_context_11_4358_119996 : frontier 10 ⟨119996, by decide⟩
    (prefixCache 11 4358) (prefixPartial 11 4358) = false := by
  decide +kernel

theorem node_context_11_4358_119996 : EJMOriginalGlobalDAGData.nodes 10 ⟨119996, by decide⟩ =
    .split (coordinate 11) (![⟨119590, by decide⟩,⟨119718, by decide⟩,⟨119864, by decide⟩,⟨119995, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4358_119996 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4358 ⟨119996, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4358
    ⟨119996, by decide⟩ (by decide) (![⟨119590, by decide⟩,⟨119718, by decide⟩,⟨119864, by decide⟩,⟨119995, by decide⟩]) unmarked_context_11_4358_119996 node_context_11_4358_119996
  intro a
  fin_cases a
  · exact context_12_17432_119590
  · exact context_12_17433_119718
  · exact context_12_17434_119864
  · exact context_12_17435_119995

theorem selected_cut_03786 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 4359) = some ⟨11, 1, 0, 1736, 4359, 1, 262144⟩ := by
  decide +kernel

theorem context_11_4359_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4359 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 4359 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 4359, 1, 262144⟩
    (by decide) selected_cut_03786

theorem unmarked_context_10_1089_119997 : frontier 11 ⟨119997, by decide⟩
    (prefixCache 10 1089) (prefixPartial 10 1089) = false := by
  decide +kernel

theorem node_context_10_1089_119997 : EJMOriginalGlobalDAGData.nodes 11 ⟨119997, by decide⟩ =
    .split (coordinate 10) (![⟨118820, by decide⟩,⟨119475, by decide⟩,⟨119996, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1089_119997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1089 ⟨119997, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1089
    ⟨119997, by decide⟩ (by decide) (![⟨118820, by decide⟩,⟨119475, by decide⟩,⟨119996, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_1089_119997 node_context_10_1089_119997
  intro a
  fin_cases a
  · exact context_11_4356_118820
  · exact context_11_4357_119475
  · exact context_11_4358_119996
  · exact context_11_4359_1736

theorem selected_cut_03787 : selected 9 ⟨118489, by decide⟩
    (prefixPartial 12 17440) = some ⟨12, 1, 0, 118489, 17440, 1, 65536⟩ := by
  decide +kernel

theorem context_12_17440_118489 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17440 ⟨118489, by decide⟩ :=
  accepted_of_selected 12 17440 ⟨118489, by decide⟩ ⟨12, 1, 0, 118489, 17440, 1, 65536⟩
    (by decide) selected_cut_03787

theorem selected_cut_03788 : selected 9 ⟨119998, by decide⟩
    (prefixPartial 12 17441) = some ⟨12, 1, 0, 119998, 17441, 1, 65536⟩ := by
  decide +kernel

theorem context_12_17441_119998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17441 ⟨119998, by decide⟩ :=
  accepted_of_selected 12 17441 ⟨119998, by decide⟩ ⟨12, 1, 0, 119998, 17441, 1, 65536⟩
    (by decide) selected_cut_03788

theorem selected_cut_03789 : selected 9 ⟨120209, by decide⟩
    (prefixPartial 12 17442) = some ⟨12, 2, 0, 120209, 17442, 3937, 65536⟩ := by
  decide +kernel

theorem context_12_17442_120209 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17442 ⟨120209, by decide⟩ :=
  accepted_of_selected 12 17442 ⟨120209, by decide⟩ ⟨12, 2, 0, 120209, 17442, 3937, 65536⟩
    (by decide) selected_cut_03789

theorem selected_cut_03790 : selected 9 ⟨120429, by decide⟩
    (prefixPartial 12 17443) = some ⟨12, 2, 0, 120429, 17443, 3629, 65536⟩ := by
  decide +kernel

theorem context_12_17443_120429 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17443 ⟨120429, by decide⟩ :=
  accepted_of_selected 12 17443 ⟨120429, by decide⟩ ⟨12, 2, 0, 120429, 17443, 3629, 65536⟩
    (by decide) selected_cut_03790

theorem unmarked_context_11_4360_120430 : frontier 10 ⟨120430, by decide⟩
    (prefixCache 11 4360) (prefixPartial 11 4360) = false := by
  decide +kernel

theorem node_context_11_4360_120430 : EJMOriginalGlobalDAGData.nodes 10 ⟨120430, by decide⟩ =
    .split (coordinate 11) (![⟨118489, by decide⟩,⟨119998, by decide⟩,⟨120209, by decide⟩,⟨120429, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4360_120430 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4360 ⟨120430, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4360
    ⟨120430, by decide⟩ (by decide) (![⟨118489, by decide⟩,⟨119998, by decide⟩,⟨120209, by decide⟩,⟨120429, by decide⟩]) unmarked_context_11_4360_120430 node_context_11_4360_120430
  intro a
  fin_cases a
  · exact context_12_17440_118489
  · exact context_12_17441_119998
  · exact context_12_17442_120209
  · exact context_12_17443_120429

theorem selected_cut_03791 : selected 9 ⟨118489, by decide⟩
    (prefixPartial 12 17444) = some ⟨12, 1, 0, 118489, 17444, 1, 65536⟩ := by
  decide +kernel

theorem context_12_17444_118489 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17444 ⟨118489, by decide⟩ :=
  accepted_of_selected 12 17444 ⟨118489, by decide⟩ ⟨12, 1, 0, 118489, 17444, 1, 65536⟩
    (by decide) selected_cut_03791

theorem selected_cut_03792 : selected 8 ⟨120471, by decide⟩
    (prefixPartial 13 69780) = some ⟨13, 2, 0, 120471, 69780, 1189, 16384⟩ := by
  decide +kernel

theorem context_13_69780_120471 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69780 ⟨120471, by decide⟩ :=
  accepted_of_selected 13 69780 ⟨120471, by decide⟩ ⟨13, 2, 0, 120471, 69780, 1189, 16384⟩
    (by decide) selected_cut_03792

theorem selected_cut_03793 : selected 8 ⟨120522, by decide⟩
    (prefixPartial 13 69781) = some ⟨13, 2, 0, 120522, 69781, 1813, 16384⟩ := by
  decide +kernel

theorem context_13_69781_120522 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69781 ⟨120522, by decide⟩ :=
  accepted_of_selected 13 69781 ⟨120522, by decide⟩ ⟨13, 2, 0, 120522, 69781, 1813, 16384⟩
    (by decide) selected_cut_03793

theorem selected_cut_03794 : selected 8 ⟨120550, by decide⟩
    (prefixPartial 13 69782) = some ⟨13, 2, 0, 120550, 69782, 1397, 16384⟩ := by
  decide +kernel

theorem context_13_69782_120550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69782 ⟨120550, by decide⟩ :=
  accepted_of_selected 13 69782 ⟨120550, by decide⟩ ⟨13, 2, 0, 120550, 69782, 1397, 16384⟩
    (by decide) selected_cut_03794

theorem selected_cut_03795 : selected 8 ⟨120567, by decide⟩
    (prefixPartial 13 69783) = some ⟨13, 2, 0, 120567, 69783, 781, 16384⟩ := by
  decide +kernel

theorem context_13_69783_120567 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69783 ⟨120567, by decide⟩ :=
  accepted_of_selected 13 69783 ⟨120567, by decide⟩ ⟨13, 2, 0, 120567, 69783, 781, 16384⟩
    (by decide) selected_cut_03795

theorem unmarked_context_12_17445_120568 : frontier 9 ⟨120568, by decide⟩
    (prefixCache 12 17445) (prefixPartial 12 17445) = false := by
  decide +kernel

theorem node_context_12_17445_120568 : EJMOriginalGlobalDAGData.nodes 9 ⟨120568, by decide⟩ =
    .split (coordinate 12) (![⟨120471, by decide⟩,⟨120522, by decide⟩,⟨120550, by decide⟩,⟨120567, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17445_120568 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17445 ⟨120568, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17445
    ⟨120568, by decide⟩ (by decide) (![⟨120471, by decide⟩,⟨120522, by decide⟩,⟨120550, by decide⟩,⟨120567, by decide⟩]) unmarked_context_12_17445_120568 node_context_12_17445_120568
  intro a
  fin_cases a
  · exact context_13_69780_120471
  · exact context_13_69781_120522
  · exact context_13_69782_120550
  · exact context_13_69783_120567

theorem selected_cut_03796 : selected 8 ⟨120605, by decide⟩
    (prefixPartial 13 69784) = some ⟨13, 2, 0, 120605, 69784, 1297, 16384⟩ := by
  decide +kernel

theorem context_13_69784_120605 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69784 ⟨120605, by decide⟩ :=
  accepted_of_selected 13 69784 ⟨120605, by decide⟩ ⟨13, 2, 0, 120605, 69784, 1297, 16384⟩
    (by decide) selected_cut_03796

theorem selected_cut_03797 : selected 8 ⟨120679, by decide⟩
    (prefixPartial 13 69785) = some ⟨13, 2, 0, 120679, 69785, 2141, 16384⟩ := by
  decide +kernel

theorem context_13_69785_120679 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69785 ⟨120679, by decide⟩ :=
  accepted_of_selected 13 69785 ⟨120679, by decide⟩ ⟨13, 2, 0, 120679, 69785, 2141, 16384⟩
    (by decide) selected_cut_03797

theorem selected_cut_03798 : selected 8 ⟨120710, by decide⟩
    (prefixPartial 13 69786) = some ⟨13, 2, 0, 120710, 69786, 1337, 16384⟩ := by
  decide +kernel

theorem context_13_69786_120710 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69786 ⟨120710, by decide⟩ :=
  accepted_of_selected 13 69786 ⟨120710, by decide⟩ ⟨13, 2, 0, 120710, 69786, 1337, 16384⟩
    (by decide) selected_cut_03798

theorem selected_cut_03799 : selected 8 ⟨120727, by decide⟩
    (prefixPartial 13 69787) = some ⟨13, 2, 0, 120727, 69787, 845, 16384⟩ := by
  decide +kernel

theorem context_13_69787_120727 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69787 ⟨120727, by decide⟩ :=
  accepted_of_selected 13 69787 ⟨120727, by decide⟩ ⟨13, 2, 0, 120727, 69787, 845, 16384⟩
    (by decide) selected_cut_03799

theorem unmarked_context_12_17446_120728 : frontier 9 ⟨120728, by decide⟩
    (prefixCache 12 17446) (prefixPartial 12 17446) = false := by
  decide +kernel

theorem node_context_12_17446_120728 : EJMOriginalGlobalDAGData.nodes 9 ⟨120728, by decide⟩ =
    .split (coordinate 12) (![⟨120605, by decide⟩,⟨120679, by decide⟩,⟨120710, by decide⟩,⟨120727, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17446_120728 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17446 ⟨120728, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17446
    ⟨120728, by decide⟩ (by decide) (![⟨120605, by decide⟩,⟨120679, by decide⟩,⟨120710, by decide⟩,⟨120727, by decide⟩]) unmarked_context_12_17446_120728 node_context_12_17446_120728
  intro a
  fin_cases a
  · exact context_13_69784_120605
  · exact context_13_69785_120679
  · exact context_13_69786_120710
  · exact context_13_69787_120727

theorem selected_cut_03800 : selected 8 ⟨120768, by decide⟩
    (prefixPartial 13 69788) = some ⟨13, 2, 0, 120768, 69788, 1141, 16384⟩ := by
  decide +kernel

theorem context_13_69788_120768 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69788 ⟨120768, by decide⟩ :=
  accepted_of_selected 13 69788 ⟨120768, by decide⟩ ⟨13, 2, 0, 120768, 69788, 1141, 16384⟩
    (by decide) selected_cut_03800

theorem selected_cut_03801 : selected 8 ⟨120831, by decide⟩
    (prefixPartial 13 69789) = some ⟨13, 2, 0, 120831, 69789, 1953, 16384⟩ := by
  decide +kernel

theorem context_13_69789_120831 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69789 ⟨120831, by decide⟩ :=
  accepted_of_selected 13 69789 ⟨120831, by decide⟩ ⟨13, 2, 0, 120831, 69789, 1953, 16384⟩
    (by decide) selected_cut_03801

theorem selected_cut_03802 : selected 8 ⟨120862, by decide⟩
    (prefixPartial 13 69790) = some ⟨13, 2, 0, 120862, 69790, 1329, 16384⟩ := by
  decide +kernel

theorem context_13_69790_120862 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69790 ⟨120862, by decide⟩ :=
  accepted_of_selected 13 69790 ⟨120862, by decide⟩ ⟨13, 2, 0, 120862, 69790, 1329, 16384⟩
    (by decide) selected_cut_03802

theorem selected_cut_03803 : selected 8 ⟨120877, by decide⟩
    (prefixPartial 13 69791) = some ⟨13, 2, 0, 120877, 69791, 689, 16384⟩ := by
  decide +kernel

theorem context_13_69791_120877 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69791 ⟨120877, by decide⟩ :=
  accepted_of_selected 13 69791 ⟨120877, by decide⟩ ⟨13, 2, 0, 120877, 69791, 689, 16384⟩
    (by decide) selected_cut_03803

theorem unmarked_context_12_17447_120878 : frontier 9 ⟨120878, by decide⟩
    (prefixCache 12 17447) (prefixPartial 12 17447) = false := by
  decide +kernel

theorem node_context_12_17447_120878 : EJMOriginalGlobalDAGData.nodes 9 ⟨120878, by decide⟩ =
    .split (coordinate 12) (![⟨120768, by decide⟩,⟨120831, by decide⟩,⟨120862, by decide⟩,⟨120877, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17447_120878 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17447 ⟨120878, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17447
    ⟨120878, by decide⟩ (by decide) (![⟨120768, by decide⟩,⟨120831, by decide⟩,⟨120862, by decide⟩,⟨120877, by decide⟩]) unmarked_context_12_17447_120878 node_context_12_17447_120878
  intro a
  fin_cases a
  · exact context_13_69788_120768
  · exact context_13_69789_120831
  · exact context_13_69790_120862
  · exact context_13_69791_120877

theorem unmarked_context_11_4361_120879 : frontier 10 ⟨120879, by decide⟩
    (prefixCache 11 4361) (prefixPartial 11 4361) = false := by
  decide +kernel

theorem node_context_11_4361_120879 : EJMOriginalGlobalDAGData.nodes 10 ⟨120879, by decide⟩ =
    .split (coordinate 11) (![⟨118489, by decide⟩,⟨120568, by decide⟩,⟨120728, by decide⟩,⟨120878, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4361_120879 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4361 ⟨120879, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4361
    ⟨120879, by decide⟩ (by decide) (![⟨118489, by decide⟩,⟨120568, by decide⟩,⟨120728, by decide⟩,⟨120878, by decide⟩]) unmarked_context_11_4361_120879 node_context_11_4361_120879
  intro a
  fin_cases a
  · exact context_12_17444_118489
  · exact context_12_17445_120568
  · exact context_12_17446_120728
  · exact context_12_17447_120878

theorem selected_cut_03804 : selected 9 ⟨120987, by decide⟩
    (prefixPartial 12 17448) = some ⟨12, 2, 0, 120987, 17448, 2841, 65536⟩ := by
  decide +kernel

theorem context_12_17448_120987 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17448 ⟨120987, by decide⟩ :=
  accepted_of_selected 12 17448 ⟨120987, by decide⟩ ⟨12, 2, 0, 120987, 17448, 2841, 65536⟩
    (by decide) selected_cut_03804

theorem selected_cut_03805 : selected 8 ⟨121013, by decide⟩
    (prefixPartial 13 69796) = some ⟨13, 2, 0, 121013, 69796, 869, 16384⟩ := by
  decide +kernel

theorem context_13_69796_121013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69796 ⟨121013, by decide⟩ :=
  accepted_of_selected 13 69796 ⟨121013, by decide⟩ ⟨13, 2, 0, 121013, 69796, 869, 16384⟩
    (by decide) selected_cut_03805

theorem selected_cut_03806 : selected 8 ⟨121053, by decide⟩
    (prefixPartial 13 69797) = some ⟨13, 2, 0, 121053, 69797, 1629, 16384⟩ := by
  decide +kernel

theorem context_13_69797_121053 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69797 ⟨121053, by decide⟩ :=
  accepted_of_selected 13 69797 ⟨121053, by decide⟩ ⟨13, 2, 0, 121053, 69797, 1629, 16384⟩
    (by decide) selected_cut_03806

theorem selected_cut_03807 : selected 8 ⟨121079, by decide⟩
    (prefixPartial 13 69798) = some ⟨13, 2, 0, 121079, 69798, 1201, 16384⟩ := by
  decide +kernel

theorem context_13_69798_121079 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69798 ⟨121079, by decide⟩ :=
  accepted_of_selected 13 69798 ⟨121079, by decide⟩ ⟨13, 2, 0, 121079, 69798, 1201, 16384⟩
    (by decide) selected_cut_03807

theorem selected_cut_03808 : selected 8 ⟨121094, by decide⟩
    (prefixPartial 13 69799) = some ⟨13, 2, 0, 121094, 69799, 761, 16384⟩ := by
  decide +kernel

theorem context_13_69799_121094 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 69799 ⟨121094, by decide⟩ :=
  accepted_of_selected 13 69799 ⟨121094, by decide⟩ ⟨13, 2, 0, 121094, 69799, 761, 16384⟩
    (by decide) selected_cut_03808

theorem unmarked_context_12_17449_121095 : frontier 9 ⟨121095, by decide⟩
    (prefixCache 12 17449) (prefixPartial 12 17449) = false := by
  decide +kernel

theorem node_context_12_17449_121095 : EJMOriginalGlobalDAGData.nodes 9 ⟨121095, by decide⟩ =
    .split (coordinate 12) (![⟨121013, by decide⟩,⟨121053, by decide⟩,⟨121079, by decide⟩,⟨121094, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17449_121095 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17449 ⟨121095, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17449
    ⟨121095, by decide⟩ (by decide) (![⟨121013, by decide⟩,⟨121053, by decide⟩,⟨121079, by decide⟩,⟨121094, by decide⟩]) unmarked_context_12_17449_121095 node_context_12_17449_121095
  intro a
  fin_cases a
  · exact context_13_69796_121013
  · exact context_13_69797_121053
  · exact context_13_69798_121079
  · exact context_13_69799_121094

theorem selected_cut_03809 : selected 9 ⟨121205, by decide⟩
    (prefixPartial 12 17450) = some ⟨12, 2, 0, 121205, 17450, 4009, 65536⟩ := by
  decide +kernel

theorem context_12_17450_121205 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17450 ⟨121205, by decide⟩ :=
  accepted_of_selected 12 17450 ⟨121205, by decide⟩ ⟨12, 2, 0, 121205, 17450, 4009, 65536⟩
    (by decide) selected_cut_03809

theorem selected_cut_03810 : selected 9 ⟨121315, by decide⟩
    (prefixPartial 12 17451) = some ⟨12, 2, 0, 121315, 17451, 3989, 65536⟩ := by
  decide +kernel

theorem context_12_17451_121315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17451 ⟨121315, by decide⟩ :=
  accepted_of_selected 12 17451 ⟨121315, by decide⟩ ⟨12, 2, 0, 121315, 17451, 3989, 65536⟩
    (by decide) selected_cut_03810

theorem unmarked_context_11_4362_121316 : frontier 10 ⟨121316, by decide⟩
    (prefixCache 11 4362) (prefixPartial 11 4362) = false := by
  decide +kernel

theorem node_context_11_4362_121316 : EJMOriginalGlobalDAGData.nodes 10 ⟨121316, by decide⟩ =
    .split (coordinate 11) (![⟨120987, by decide⟩,⟨121095, by decide⟩,⟨121205, by decide⟩,⟨121315, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4362_121316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4362 ⟨121316, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4362
    ⟨121316, by decide⟩ (by decide) (![⟨120987, by decide⟩,⟨121095, by decide⟩,⟨121205, by decide⟩,⟨121315, by decide⟩]) unmarked_context_11_4362_121316 node_context_11_4362_121316
  intro a
  fin_cases a
  · exact context_12_17448_120987
  · exact context_12_17449_121095
  · exact context_12_17450_121205
  · exact context_12_17451_121315

theorem selected_cut_03811 : selected 9 ⟨121444, by decide⟩
    (prefixPartial 12 17452) = some ⟨12, 2, 0, 121444, 17452, 2501, 65536⟩ := by
  decide +kernel

theorem context_12_17452_121444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17452 ⟨121444, by decide⟩ :=
  accepted_of_selected 12 17452 ⟨121444, by decide⟩ ⟨12, 2, 0, 121444, 17452, 2501, 65536⟩
    (by decide) selected_cut_03811

theorem selected_cut_03812 : selected 9 ⟨121565, by decide⟩
    (prefixPartial 12 17453) = some ⟨12, 2, 0, 121565, 17453, 3813, 65536⟩ := by
  decide +kernel

theorem context_12_17453_121565 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17453 ⟨121565, by decide⟩ :=
  accepted_of_selected 12 17453 ⟨121565, by decide⟩ ⟨12, 2, 0, 121565, 17453, 3813, 65536⟩
    (by decide) selected_cut_03812

theorem selected_cut_03813 : selected 9 ⟨121714, by decide⟩
    (prefixPartial 12 17454) = some ⟨12, 2, 0, 121714, 17454, 3725, 65536⟩ := by
  decide +kernel

theorem context_12_17454_121714 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17454 ⟨121714, by decide⟩ :=
  accepted_of_selected 12 17454 ⟨121714, by decide⟩ ⟨12, 2, 0, 121714, 17454, 3725, 65536⟩
    (by decide) selected_cut_03813

theorem selected_cut_03814 : selected 9 ⟨121822, by decide⟩
    (prefixPartial 12 17455) = some ⟨12, 2, 0, 121822, 17455, 3033, 65536⟩ := by
  decide +kernel

theorem context_12_17455_121822 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17455 ⟨121822, by decide⟩ :=
  accepted_of_selected 12 17455 ⟨121822, by decide⟩ ⟨12, 2, 0, 121822, 17455, 3033, 65536⟩
    (by decide) selected_cut_03814

theorem unmarked_context_11_4363_121823 : frontier 10 ⟨121823, by decide⟩
    (prefixCache 11 4363) (prefixPartial 11 4363) = false := by
  decide +kernel

theorem node_context_11_4363_121823 : EJMOriginalGlobalDAGData.nodes 10 ⟨121823, by decide⟩ =
    .split (coordinate 11) (![⟨121444, by decide⟩,⟨121565, by decide⟩,⟨121714, by decide⟩,⟨121822, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4363_121823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4363 ⟨121823, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4363
    ⟨121823, by decide⟩ (by decide) (![⟨121444, by decide⟩,⟨121565, by decide⟩,⟨121714, by decide⟩,⟨121822, by decide⟩]) unmarked_context_11_4363_121823 node_context_11_4363_121823
  intro a
  fin_cases a
  · exact context_12_17452_121444
  · exact context_12_17453_121565
  · exact context_12_17454_121714
  · exact context_12_17455_121822

theorem unmarked_context_10_1090_121824 : frontier 11 ⟨121824, by decide⟩
    (prefixCache 10 1090) (prefixPartial 10 1090) = false := by
  decide +kernel

theorem node_context_10_1090_121824 : EJMOriginalGlobalDAGData.nodes 11 ⟨121824, by decide⟩ =
    .split (coordinate 10) (![⟨120430, by decide⟩,⟨120879, by decide⟩,⟨121316, by decide⟩,⟨121823, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1090_121824 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1090 ⟨121824, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1090
    ⟨121824, by decide⟩ (by decide) (![⟨120430, by decide⟩,⟨120879, by decide⟩,⟨121316, by decide⟩,⟨121823, by decide⟩]) unmarked_context_10_1090_121824 node_context_10_1090_121824
  intro a
  fin_cases a
  · exact context_11_4360_120430
  · exact context_11_4361_120879
  · exact context_11_4362_121316
  · exact context_11_4363_121823

theorem selected_cut_03815 : selected 11 ⟨3440, by decide⟩
    (prefixPartial 10 1091) = some ⟨10, 1, 0, 3440, 1091, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_1091_3440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1091 ⟨3440, by decide⟩ :=
  accepted_of_selected 10 1091 ⟨3440, by decide⟩ ⟨10, 1, 0, 3440, 1091, 1, 1048576⟩
    (by decide) selected_cut_03815

theorem unmarked_context_9_272_121825 : frontier 12 ⟨121825, by decide⟩
    (prefixCache 9 272) (prefixPartial 9 272) = false := by
  decide +kernel

theorem node_context_9_272_121825 : EJMOriginalGlobalDAGData.nodes 12 ⟨121825, by decide⟩ =
    .split (coordinate 9) (![⟨118488, by decide⟩,⟨119997, by decide⟩,⟨121824, by decide⟩,⟨3440, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_272_121825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 272 ⟨121825, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 272
    ⟨121825, by decide⟩ (by decide) (![⟨118488, by decide⟩,⟨119997, by decide⟩,⟨121824, by decide⟩,⟨3440, by decide⟩]) unmarked_context_9_272_121825 node_context_9_272_121825
  intro a
  fin_cases a
  · exact context_10_1088_118488
  · exact context_10_1089_119997
  · exact context_10_1090_121824
  · exact context_10_1091_3440

theorem selected_cut_03816 : selected 11 ⟨3442, by decide⟩
    (prefixPartial 10 1092) = some ⟨10, 1, 0, 3442, 1092, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_1092_3442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1092 ⟨3442, by decide⟩ :=
  accepted_of_selected 10 1092 ⟨3442, by decide⟩ ⟨10, 1, 0, 3442, 1092, 1, 1048576⟩
    (by decide) selected_cut_03816

theorem selected_cut_03817 : selected 10 ⟨121826, by decide⟩
    (prefixPartial 11 4372) = some ⟨11, 1, 0, 121826, 4372, 1, 262144⟩ := by
  decide +kernel

theorem context_11_4372_121826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4372 ⟨121826, by decide⟩ :=
  accepted_of_selected 11 4372 ⟨121826, by decide⟩ ⟨11, 1, 0, 121826, 4372, 1, 262144⟩
    (by decide) selected_cut_03817

theorem selected_cut_03818 : selected 10 ⟨122053, by decide⟩
    (prefixPartial 11 4373) = some ⟨11, 2, 0, 122053, 4373, 3621, 262144⟩ := by
  decide +kernel

theorem context_11_4373_122053 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4373 ⟨122053, by decide⟩ :=
  accepted_of_selected 11 4373 ⟨122053, by decide⟩ ⟨11, 2, 0, 122053, 4373, 3621, 262144⟩
    (by decide) selected_cut_03818

theorem selected_cut_03819 : selected 10 ⟨122213, by decide⟩
    (prefixPartial 11 4374) = some ⟨11, 2, 0, 122213, 4374, 2805, 262144⟩ := by
  decide +kernel

theorem context_11_4374_122213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4374 ⟨122213, by decide⟩ :=
  accepted_of_selected 11 4374 ⟨122213, by decide⟩ ⟨11, 2, 0, 122213, 4374, 2805, 262144⟩
    (by decide) selected_cut_03819

theorem selected_cut_03820 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 4375) = some ⟨11, 1, 0, 1736, 4375, 1, 262144⟩ := by
  decide +kernel

theorem context_11_4375_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4375 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 4375 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 4375, 1, 262144⟩
    (by decide) selected_cut_03820

theorem unmarked_context_10_1093_122214 : frontier 11 ⟨122214, by decide⟩
    (prefixCache 10 1093) (prefixPartial 10 1093) = false := by
  decide +kernel

theorem node_context_10_1093_122214 : EJMOriginalGlobalDAGData.nodes 11 ⟨122214, by decide⟩ =
    .split (coordinate 10) (![⟨121826, by decide⟩,⟨122053, by decide⟩,⟨122213, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1093_122214 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1093 ⟨122214, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1093
    ⟨122214, by decide⟩ (by decide) (![⟨121826, by decide⟩,⟨122053, by decide⟩,⟨122213, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_1093_122214 node_context_10_1093_122214
  intro a
  fin_cases a
  · exact context_11_4372_121826
  · exact context_11_4373_122053
  · exact context_11_4374_122213
  · exact context_11_4375_1736

theorem selected_cut_03821 : selected 10 ⟨121826, by decide⟩
    (prefixPartial 11 4376) = some ⟨11, 1, 0, 121826, 4376, 1, 262144⟩ := by
  decide +kernel

theorem context_11_4376_121826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4376 ⟨121826, by decide⟩ :=
  accepted_of_selected 11 4376 ⟨121826, by decide⟩ ⟨11, 1, 0, 121826, 4376, 1, 262144⟩
    (by decide) selected_cut_03821

theorem selected_cut_03822 : selected 10 ⟨122410, by decide⟩
    (prefixPartial 11 4377) = some ⟨11, 2, 0, 122410, 4377, 2817, 262144⟩ := by
  decide +kernel

theorem context_11_4377_122410 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4377 ⟨122410, by decide⟩ :=
  accepted_of_selected 11 4377 ⟨122410, by decide⟩ ⟨11, 2, 0, 122410, 4377, 2817, 262144⟩
    (by decide) selected_cut_03822

theorem selected_cut_03823 : selected 9 ⟨122215, by decide⟩
    (prefixPartial 12 17512) = some ⟨12, 1, 0, 122215, 17512, 1, 65536⟩ := by
  decide +kernel

theorem context_12_17512_122215 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17512 ⟨122215, by decide⟩ :=
  accepted_of_selected 12 17512 ⟨122215, by decide⟩ ⟨12, 1, 0, 122215, 17512, 1, 65536⟩
    (by decide) selected_cut_03823

theorem selected_cut_03824 : selected 9 ⟨122536, by decide⟩
    (prefixPartial 12 17513) = some ⟨12, 2, 0, 122536, 17513, 1569, 65536⟩ := by
  decide +kernel

theorem context_12_17513_122536 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17513 ⟨122536, by decide⟩ :=
  accepted_of_selected 12 17513 ⟨122536, by decide⟩ ⟨12, 2, 0, 122536, 17513, 1569, 65536⟩
    (by decide) selected_cut_03824

theorem selected_cut_03825 : selected 9 ⟨122609, by decide⟩
    (prefixPartial 12 17514) = some ⟨12, 2, 0, 122609, 17514, 1585, 65536⟩ := by
  decide +kernel

theorem context_12_17514_122609 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17514 ⟨122609, by decide⟩ :=
  accepted_of_selected 12 17514 ⟨122609, by decide⟩ ⟨12, 2, 0, 122609, 17514, 1585, 65536⟩
    (by decide) selected_cut_03825

theorem selected_cut_03826 : selected 9 ⟨122660, by decide⟩
    (prefixPartial 12 17515) = some ⟨12, 2, 0, 122660, 17515, 1361, 65536⟩ := by
  decide +kernel

theorem context_12_17515_122660 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17515 ⟨122660, by decide⟩ :=
  accepted_of_selected 12 17515 ⟨122660, by decide⟩ ⟨12, 2, 0, 122660, 17515, 1361, 65536⟩
    (by decide) selected_cut_03826

theorem unmarked_context_11_4378_122661 : frontier 10 ⟨122661, by decide⟩
    (prefixCache 11 4378) (prefixPartial 11 4378) = false := by
  decide +kernel

theorem node_context_11_4378_122661 : EJMOriginalGlobalDAGData.nodes 10 ⟨122661, by decide⟩ =
    .split (coordinate 11) (![⟨122215, by decide⟩,⟨122536, by decide⟩,⟨122609, by decide⟩,⟨122660, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4378_122661 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4378 ⟨122661, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4378
    ⟨122661, by decide⟩ (by decide) (![⟨122215, by decide⟩,⟨122536, by decide⟩,⟨122609, by decide⟩,⟨122660, by decide⟩]) unmarked_context_11_4378_122661 node_context_11_4378_122661
  intro a
  fin_cases a
  · exact context_12_17512_122215
  · exact context_12_17513_122536
  · exact context_12_17514_122609
  · exact context_12_17515_122660

theorem selected_cut_03827 : selected 10 ⟨122854, by decide⟩
    (prefixPartial 11 4379) = some ⟨11, 2, 0, 122854, 4379, 2665, 262144⟩ := by
  decide +kernel

theorem context_11_4379_122854 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4379 ⟨122854, by decide⟩ :=
  accepted_of_selected 11 4379 ⟨122854, by decide⟩ ⟨11, 2, 0, 122854, 4379, 2665, 262144⟩
    (by decide) selected_cut_03827

theorem unmarked_context_10_1094_122855 : frontier 11 ⟨122855, by decide⟩
    (prefixCache 10 1094) (prefixPartial 10 1094) = false := by
  decide +kernel

theorem node_context_10_1094_122855 : EJMOriginalGlobalDAGData.nodes 11 ⟨122855, by decide⟩ =
    .split (coordinate 10) (![⟨121826, by decide⟩,⟨122410, by decide⟩,⟨122661, by decide⟩,⟨122854, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1094_122855 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1094 ⟨122855, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1094
    ⟨122855, by decide⟩ (by decide) (![⟨121826, by decide⟩,⟨122410, by decide⟩,⟨122661, by decide⟩,⟨122854, by decide⟩]) unmarked_context_10_1094_122855 node_context_10_1094_122855
  intro a
  fin_cases a
  · exact context_11_4376_121826
  · exact context_11_4377_122410
  · exact context_11_4378_122661
  · exact context_11_4379_122854

theorem selected_cut_03828 : selected 11 ⟨3440, by decide⟩
    (prefixPartial 10 1095) = some ⟨10, 1, 0, 3440, 1095, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_1095_3440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1095 ⟨3440, by decide⟩ :=
  accepted_of_selected 10 1095 ⟨3440, by decide⟩ ⟨10, 1, 0, 3440, 1095, 1, 1048576⟩
    (by decide) selected_cut_03828

theorem unmarked_context_9_273_122856 : frontier 12 ⟨122856, by decide⟩
    (prefixCache 9 273) (prefixPartial 9 273) = false := by
  decide +kernel

theorem node_context_9_273_122856 : EJMOriginalGlobalDAGData.nodes 12 ⟨122856, by decide⟩ =
    .split (coordinate 9) (![⟨3442, by decide⟩,⟨122214, by decide⟩,⟨122855, by decide⟩,⟨3440, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_273_122856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 273 ⟨122856, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 273
    ⟨122856, by decide⟩ (by decide) (![⟨3442, by decide⟩,⟨122214, by decide⟩,⟨122855, by decide⟩,⟨3440, by decide⟩]) unmarked_context_9_273_122856 node_context_9_273_122856
  intro a
  fin_cases a
  · exact context_10_1092_3442
  · exact context_10_1093_122214
  · exact context_10_1094_122855
  · exact context_10_1095_3440

theorem selected_cut_03829 : selected 12 ⟨122918, by decide⟩
    (prefixPartial 9 274) = some ⟨9, 2, 0, 122918, 274, 637, 4194304⟩ := by
  decide +kernel

theorem context_9_274_122918 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 274 ⟨122918, by decide⟩ :=
  accepted_of_selected 9 274 ⟨122918, by decide⟩ ⟨9, 2, 0, 122918, 274, 637, 4194304⟩
    (by decide) selected_cut_03829

theorem selected_cut_03830 : selected 12 ⟨4601, by decide⟩
    (prefixPartial 9 275) = some ⟨9, 1, 0, 4601, 275, 1, 4194304⟩ := by
  decide +kernel

theorem context_9_275_4601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 275 ⟨4601, by decide⟩ :=
  accepted_of_selected 9 275 ⟨4601, by decide⟩ ⟨9, 1, 0, 4601, 275, 1, 4194304⟩
    (by decide) selected_cut_03830

theorem unmarked_context_8_68_122919 : frontier 13 ⟨122919, by decide⟩
    (prefixCache 8 68) (prefixPartial 8 68) = false := by
  decide +kernel

theorem node_context_8_68_122919 : EJMOriginalGlobalDAGData.nodes 13 ⟨122919, by decide⟩ =
    .split (coordinate 8) (![⟨121825, by decide⟩,⟨122856, by decide⟩,⟨122918, by decide⟩,⟨4601, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_68_122919 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 68 ⟨122919, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 68
    ⟨122919, by decide⟩ (by decide) (![⟨121825, by decide⟩,⟨122856, by decide⟩,⟨122918, by decide⟩,⟨4601, by decide⟩]) unmarked_context_8_68_122919 node_context_8_68_122919
  intro a
  fin_cases a
  · exact context_9_272_121825
  · exact context_9_273_122856
  · exact context_9_274_122918
  · exact context_9_275_4601

theorem selected_cut_03831 : selected 9 ⟨123043, by decide⟩
    (prefixPartial 12 17664) = some ⟨12, 2, 0, 123043, 17664, 3481, 65536⟩ := by
  decide +kernel

theorem context_12_17664_123043 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17664 ⟨123043, by decide⟩ :=
  accepted_of_selected 12 17664 ⟨123043, by decide⟩ ⟨12, 2, 0, 123043, 17664, 3481, 65536⟩
    (by decide) selected_cut_03831

theorem selected_cut_03832 : selected 8 ⟨123093, by decide⟩
    (prefixPartial 13 70660) = some ⟨13, 2, 0, 123093, 70660, 2089, 16384⟩ := by
  decide +kernel

theorem context_13_70660_123093 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70660 ⟨123093, by decide⟩ :=
  accepted_of_selected 13 70660 ⟨123093, by decide⟩ ⟨13, 2, 0, 123093, 70660, 2089, 16384⟩
    (by decide) selected_cut_03832

theorem selected_cut_03833 : selected 8 ⟨123118, by decide⟩
    (prefixPartial 13 70661) = some ⟨13, 2, 0, 123118, 70661, 1421, 16384⟩ := by
  decide +kernel

theorem context_13_70661_123118 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70661 ⟨123118, by decide⟩ :=
  accepted_of_selected 13 70661 ⟨123118, by decide⟩ ⟨13, 2, 0, 123118, 70661, 1421, 16384⟩
    (by decide) selected_cut_03833

theorem selected_cut_03834 : selected 8 ⟨123140, by decide⟩
    (prefixPartial 13 70662) = some ⟨13, 2, 0, 123140, 70662, 1729, 16384⟩ := by
  decide +kernel

theorem context_13_70662_123140 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70662 ⟨123140, by decide⟩ :=
  accepted_of_selected 13 70662 ⟨123140, by decide⟩ ⟨13, 2, 0, 123140, 70662, 1729, 16384⟩
    (by decide) selected_cut_03834

theorem selected_cut_03835 : selected 8 ⟨414, by decide⟩
    (prefixPartial 13 70663) = some ⟨13, 1, 0, 414, 70663, 1, 16384⟩ := by
  decide +kernel

theorem context_13_70663_414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70663 ⟨414, by decide⟩ :=
  accepted_of_selected 13 70663 ⟨414, by decide⟩ ⟨13, 1, 0, 414, 70663, 1, 16384⟩
    (by decide) selected_cut_03835

theorem unmarked_context_12_17665_123141 : frontier 9 ⟨123141, by decide⟩
    (prefixCache 12 17665) (prefixPartial 12 17665) = false := by
  decide +kernel

theorem node_context_12_17665_123141 : EJMOriginalGlobalDAGData.nodes 9 ⟨123141, by decide⟩ =
    .split (coordinate 12) (![⟨123093, by decide⟩,⟨123118, by decide⟩,⟨123140, by decide⟩,⟨414, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_17665_123141 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 17665 ⟨123141, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 17665
    ⟨123141, by decide⟩ (by decide) (![⟨123093, by decide⟩,⟨123118, by decide⟩,⟨123140, by decide⟩,⟨414, by decide⟩]) unmarked_context_12_17665_123141 node_context_12_17665_123141
  intro a
  fin_cases a
  · exact context_13_70660_123093
  · exact context_13_70661_123118
  · exact context_13_70662_123140
  · exact context_13_70663_414

theorem selected_cut_03836 : selected 7 ⟨123182, by decide⟩
    (prefixPartial 14 282656) = some ⟨14, 2, 0, 123182, 282656, 1217, 4096⟩ := by
  decide +kernel

theorem context_14_282656_123182 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 282656 ⟨123182, by decide⟩ :=
  accepted_of_selected 14 282656 ⟨123182, by decide⟩ ⟨14, 2, 0, 123182, 282656, 1217, 4096⟩
    (by decide) selected_cut_03836

theorem selected_cut_03837 : selected 7 ⟨123198, by decide⟩
    (prefixPartial 14 282657) = some ⟨14, 2, 0, 123198, 282657, 1089, 4096⟩ := by
  decide +kernel

theorem context_14_282657_123198 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 282657 ⟨123198, by decide⟩ :=
  accepted_of_selected 14 282657 ⟨123198, by decide⟩ ⟨14, 2, 0, 123198, 282657, 1089, 4096⟩
    (by decide) selected_cut_03837

theorem selected_cut_03838 : selected 7 ⟨123220, by decide⟩
    (prefixPartial 14 282658) = some ⟨14, 2, 0, 123220, 282658, 1213, 4096⟩ := by
  decide +kernel

theorem context_14_282658_123220 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 282658 ⟨123220, by decide⟩ :=
  accepted_of_selected 14 282658 ⟨123220, by decide⟩ ⟨14, 2, 0, 123220, 282658, 1213, 4096⟩
    (by decide) selected_cut_03838

theorem selected_cut_03839 : selected 7 ⟨123239, by decide⟩
    (prefixPartial 14 282659) = some ⟨14, 2, 0, 123239, 282659, 1201, 4096⟩ := by
  decide +kernel

theorem context_14_282659_123239 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 282659 ⟨123239, by decide⟩ :=
  accepted_of_selected 14 282659 ⟨123239, by decide⟩ ⟨14, 2, 0, 123239, 282659, 1201, 4096⟩
    (by decide) selected_cut_03839

theorem unmarked_context_13_70664_123240 : frontier 8 ⟨123240, by decide⟩
    (prefixCache 13 70664) (prefixPartial 13 70664) = false := by
  decide +kernel

theorem node_context_13_70664_123240 : EJMOriginalGlobalDAGData.nodes 8 ⟨123240, by decide⟩ =
    .split (coordinate 13) (![⟨123182, by decide⟩,⟨123198, by decide⟩,⟨123220, by decide⟩,⟨123239, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_70664_123240 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70664 ⟨123240, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 70664
    ⟨123240, by decide⟩ (by decide) (![⟨123182, by decide⟩,⟨123198, by decide⟩,⟨123220, by decide⟩,⟨123239, by decide⟩]) unmarked_context_13_70664_123240 node_context_13_70664_123240
  intro a
  fin_cases a
  · exact context_14_282656_123182
  · exact context_14_282657_123198
  · exact context_14_282658_123220
  · exact context_14_282659_123239

theorem selected_cut_03840 : selected 8 ⟨123290, by decide⟩
    (prefixPartial 13 70665) = some ⟨13, 2, 0, 123290, 70665, 3041, 16384⟩ := by
  decide +kernel

theorem context_13_70665_123290 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70665 ⟨123290, by decide⟩ :=
  accepted_of_selected 13 70665 ⟨123290, by decide⟩ ⟨13, 2, 0, 123290, 70665, 3041, 16384⟩
    (by decide) selected_cut_03840

theorem selected_cut_03841 : selected 8 ⟨123332, by decide⟩
    (prefixPartial 13 70666) = some ⟨13, 2, 0, 123332, 70666, 2161, 16384⟩ := by
  decide +kernel

theorem context_13_70666_123332 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 70666 ⟨123332, by decide⟩ :=
  accepted_of_selected 13 70666 ⟨123332, by decide⟩ ⟨13, 2, 0, 123332, 70666, 2161, 16384⟩
    (by decide) selected_cut_03841

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
