/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover136
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_13155 : selected 9 ⟨346801, by decide⟩
    (prefixPartial 12 26544) = some ⟨12, 2, 0, 346801, 26544, 1361, 65536⟩ := by
  decide +kernel

theorem context_12_26544_346801 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26544 ⟨346801, by decide⟩ :=
  accepted_of_selected 12 26544 ⟨346801, by decide⟩ ⟨12, 2, 0, 346801, 26544, 1361, 65536⟩
    (by decide) selected_cut_13155

theorem selected_cut_13156 : selected 9 ⟨346827, by decide⟩
    (prefixPartial 12 26545) = some ⟨12, 2, 0, 346827, 26545, 1289, 65536⟩ := by
  decide +kernel

theorem context_12_26545_346827 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26545 ⟨346827, by decide⟩ :=
  accepted_of_selected 12 26545 ⟨346827, by decide⟩ ⟨12, 2, 0, 346827, 26545, 1289, 65536⟩
    (by decide) selected_cut_13156

theorem selected_cut_13157 : selected 9 ⟨346844, by decide⟩
    (prefixPartial 12 26546) = some ⟨12, 2, 0, 346844, 26546, 1285, 65536⟩ := by
  decide +kernel

theorem context_12_26546_346844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26546 ⟨346844, by decide⟩ :=
  accepted_of_selected 12 26546 ⟨346844, by decide⟩ ⟨12, 2, 0, 346844, 26546, 1285, 65536⟩
    (by decide) selected_cut_13157

theorem selected_cut_13158 : selected 9 ⟨346857, by decide⟩
    (prefixPartial 12 26547) = some ⟨12, 2, 0, 346857, 26547, 1201, 65536⟩ := by
  decide +kernel

theorem context_12_26547_346857 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26547 ⟨346857, by decide⟩ :=
  accepted_of_selected 12 26547 ⟨346857, by decide⟩ ⟨12, 2, 0, 346857, 26547, 1201, 65536⟩
    (by decide) selected_cut_13158

theorem unmarked_context_11_6636_346858 : frontier 10 ⟨346858, by decide⟩
    (prefixCache 11 6636) (prefixPartial 11 6636) = false := by
  decide +kernel

theorem node_context_11_6636_346858 : EJMOriginalGlobalDAGData.nodes 10 ⟨346858, by decide⟩ =
    .split (coordinate 11) (![⟨346801, by decide⟩,⟨346827, by decide⟩,⟨346844, by decide⟩,⟨346857, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6636_346858 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6636 ⟨346858, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6636
    ⟨346858, by decide⟩ (by decide) (![⟨346801, by decide⟩,⟨346827, by decide⟩,⟨346844, by decide⟩,⟨346857, by decide⟩]) unmarked_context_11_6636_346858 node_context_11_6636_346858
  intro a
  fin_cases a
  · exact context_12_26544_346801
  · exact context_12_26545_346827
  · exact context_12_26546_346844
  · exact context_12_26547_346857

theorem selected_cut_13159 : selected 9 ⟨346877, by decide⟩
    (prefixPartial 12 26548) = some ⟨12, 2, 0, 346877, 26548, 1221, 65536⟩ := by
  decide +kernel

theorem context_12_26548_346877 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26548 ⟨346877, by decide⟩ :=
  accepted_of_selected 12 26548 ⟨346877, by decide⟩ ⟨12, 2, 0, 346877, 26548, 1221, 65536⟩
    (by decide) selected_cut_13159

theorem selected_cut_13160 : selected 9 ⟨346894, by decide⟩
    (prefixPartial 12 26549) = some ⟨12, 2, 0, 346894, 26549, 1157, 65536⟩ := by
  decide +kernel

theorem context_12_26549_346894 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26549 ⟨346894, by decide⟩ :=
  accepted_of_selected 12 26549 ⟨346894, by decide⟩ ⟨12, 2, 0, 346894, 26549, 1157, 65536⟩
    (by decide) selected_cut_13160

theorem selected_cut_13161 : selected 9 ⟨346909, by decide⟩
    (prefixPartial 12 26550) = some ⟨12, 2, 0, 346909, 26550, 1325, 65536⟩ := by
  decide +kernel

theorem context_12_26550_346909 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26550 ⟨346909, by decide⟩ :=
  accepted_of_selected 12 26550 ⟨346909, by decide⟩ ⟨12, 2, 0, 346909, 26550, 1325, 65536⟩
    (by decide) selected_cut_13161

theorem selected_cut_13162 : selected 9 ⟨346922, by decide⟩
    (prefixPartial 12 26551) = some ⟨12, 2, 0, 346922, 26551, 1193, 65536⟩ := by
  decide +kernel

theorem context_12_26551_346922 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26551 ⟨346922, by decide⟩ :=
  accepted_of_selected 12 26551 ⟨346922, by decide⟩ ⟨12, 2, 0, 346922, 26551, 1193, 65536⟩
    (by decide) selected_cut_13162

theorem unmarked_context_11_6637_346923 : frontier 10 ⟨346923, by decide⟩
    (prefixCache 11 6637) (prefixPartial 11 6637) = false := by
  decide +kernel

theorem node_context_11_6637_346923 : EJMOriginalGlobalDAGData.nodes 10 ⟨346923, by decide⟩ =
    .split (coordinate 11) (![⟨346877, by decide⟩,⟨346894, by decide⟩,⟨346909, by decide⟩,⟨346922, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6637_346923 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6637 ⟨346923, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6637
    ⟨346923, by decide⟩ (by decide) (![⟨346877, by decide⟩,⟨346894, by decide⟩,⟨346909, by decide⟩,⟨346922, by decide⟩]) unmarked_context_11_6637_346923 node_context_11_6637_346923
  intro a
  fin_cases a
  · exact context_12_26548_346877
  · exact context_12_26549_346894
  · exact context_12_26550_346909
  · exact context_12_26551_346922

theorem selected_cut_13163 : selected 9 ⟨346945, by decide⟩
    (prefixPartial 12 26552) = some ⟨12, 2, 0, 346945, 26552, 1225, 65536⟩ := by
  decide +kernel

theorem context_12_26552_346945 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26552 ⟨346945, by decide⟩ :=
  accepted_of_selected 12 26552 ⟨346945, by decide⟩ ⟨12, 2, 0, 346945, 26552, 1225, 65536⟩
    (by decide) selected_cut_13163

theorem selected_cut_13164 : selected 9 ⟨346967, by decide⟩
    (prefixPartial 12 26553) = some ⟨12, 2, 0, 346967, 26553, 1253, 65536⟩ := by
  decide +kernel

theorem context_12_26553_346967 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26553 ⟨346967, by decide⟩ :=
  accepted_of_selected 12 26553 ⟨346967, by decide⟩ ⟨12, 2, 0, 346967, 26553, 1253, 65536⟩
    (by decide) selected_cut_13164

theorem selected_cut_13165 : selected 9 ⟨346979, by decide⟩
    (prefixPartial 12 26554) = some ⟨12, 2, 0, 346979, 26554, 1161, 65536⟩ := by
  decide +kernel

theorem context_12_26554_346979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26554 ⟨346979, by decide⟩ :=
  accepted_of_selected 12 26554 ⟨346979, by decide⟩ ⟨12, 2, 0, 346979, 26554, 1161, 65536⟩
    (by decide) selected_cut_13165

theorem selected_cut_13166 : selected 9 ⟨346992, by decide⟩
    (prefixPartial 12 26555) = some ⟨12, 2, 0, 346992, 26555, 1049, 65536⟩ := by
  decide +kernel

theorem context_12_26555_346992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26555 ⟨346992, by decide⟩ :=
  accepted_of_selected 12 26555 ⟨346992, by decide⟩ ⟨12, 2, 0, 346992, 26555, 1049, 65536⟩
    (by decide) selected_cut_13166

theorem unmarked_context_11_6638_346993 : frontier 10 ⟨346993, by decide⟩
    (prefixCache 11 6638) (prefixPartial 11 6638) = false := by
  decide +kernel

theorem node_context_11_6638_346993 : EJMOriginalGlobalDAGData.nodes 10 ⟨346993, by decide⟩ =
    .split (coordinate 11) (![⟨346945, by decide⟩,⟨346967, by decide⟩,⟨346979, by decide⟩,⟨346992, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6638_346993 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6638 ⟨346993, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6638
    ⟨346993, by decide⟩ (by decide) (![⟨346945, by decide⟩,⟨346967, by decide⟩,⟨346979, by decide⟩,⟨346992, by decide⟩]) unmarked_context_11_6638_346993 node_context_11_6638_346993
  intro a
  fin_cases a
  · exact context_12_26552_346945
  · exact context_12_26553_346967
  · exact context_12_26554_346979
  · exact context_12_26555_346992

theorem selected_cut_13167 : selected 10 ⟨347075, by decide⟩
    (prefixPartial 11 6639) = some ⟨11, 2, 0, 347075, 6639, 3249, 262144⟩ := by
  decide +kernel

theorem context_11_6639_347075 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6639 ⟨347075, by decide⟩ :=
  accepted_of_selected 11 6639 ⟨347075, by decide⟩ ⟨11, 2, 0, 347075, 6639, 3249, 262144⟩
    (by decide) selected_cut_13167

theorem unmarked_context_10_1659_347076 : frontier 11 ⟨347076, by decide⟩
    (prefixCache 10 1659) (prefixPartial 10 1659) = false := by
  decide +kernel

theorem node_context_10_1659_347076 : EJMOriginalGlobalDAGData.nodes 11 ⟨347076, by decide⟩ =
    .split (coordinate 10) (![⟨346858, by decide⟩,⟨346923, by decide⟩,⟨346993, by decide⟩,⟨347075, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1659_347076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1659 ⟨347076, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1659
    ⟨347076, by decide⟩ (by decide) (![⟨346858, by decide⟩,⟨346923, by decide⟩,⟨346993, by decide⟩,⟨347075, by decide⟩]) unmarked_context_10_1659_347076 node_context_10_1659_347076
  intro a
  fin_cases a
  · exact context_11_6636_346858
  · exact context_11_6637_346923
  · exact context_11_6638_346993
  · exact context_11_6639_347075

theorem unmarked_context_9_414_347077 : frontier 12 ⟨347077, by decide⟩
    (prefixCache 9 414) (prefixPartial 9 414) = false := by
  decide +kernel

theorem node_context_9_414_347077 : EJMOriginalGlobalDAGData.nodes 12 ⟨347077, by decide⟩ =
    .split (coordinate 9) (![⟨345887, by decide⟩,⟨346450, by decide⟩,⟨346782, by decide⟩,⟨347076, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_414_347077 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 414 ⟨347077, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 414
    ⟨347077, by decide⟩ (by decide) (![⟨345887, by decide⟩,⟨346450, by decide⟩,⟨346782, by decide⟩,⟨347076, by decide⟩]) unmarked_context_9_414_347077 node_context_9_414_347077
  intro a
  fin_cases a
  · exact context_10_1656_345887
  · exact context_10_1657_346450
  · exact context_10_1658_346782
  · exact context_10_1659_347076

theorem selected_cut_13168 : selected 10 ⟨347108, by decide⟩
    (prefixPartial 11 6640) = some ⟨11, 2, 0, 347108, 6640, 2513, 262144⟩ := by
  decide +kernel

theorem context_11_6640_347108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6640 ⟨347108, by decide⟩ :=
  accepted_of_selected 11 6640 ⟨347108, by decide⟩ ⟨11, 2, 0, 347108, 6640, 2513, 262144⟩
    (by decide) selected_cut_13168

theorem selected_cut_13169 : selected 10 ⟨347135, by decide⟩
    (prefixPartial 11 6641) = some ⟨11, 2, 0, 347135, 6641, 2589, 262144⟩ := by
  decide +kernel

theorem context_11_6641_347135 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6641 ⟨347135, by decide⟩ :=
  accepted_of_selected 11 6641 ⟨347135, by decide⟩ ⟨11, 2, 0, 347135, 6641, 2589, 262144⟩
    (by decide) selected_cut_13169

theorem selected_cut_13170 : selected 10 ⟨347163, by decide⟩
    (prefixPartial 11 6642) = some ⟨11, 2, 0, 347163, 6642, 2385, 262144⟩ := by
  decide +kernel

theorem context_11_6642_347163 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6642 ⟨347163, by decide⟩ :=
  accepted_of_selected 11 6642 ⟨347163, by decide⟩ ⟨11, 2, 0, 347163, 6642, 2385, 262144⟩
    (by decide) selected_cut_13170

theorem selected_cut_13171 : selected 10 ⟨347192, by decide⟩
    (prefixPartial 11 6643) = some ⟨11, 2, 0, 347192, 6643, 1585, 262144⟩ := by
  decide +kernel

theorem context_11_6643_347192 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6643 ⟨347192, by decide⟩ :=
  accepted_of_selected 11 6643 ⟨347192, by decide⟩ ⟨11, 2, 0, 347192, 6643, 1585, 262144⟩
    (by decide) selected_cut_13171

theorem unmarked_context_10_1660_347193 : frontier 11 ⟨347193, by decide⟩
    (prefixCache 10 1660) (prefixPartial 10 1660) = false := by
  decide +kernel

theorem node_context_10_1660_347193 : EJMOriginalGlobalDAGData.nodes 11 ⟨347193, by decide⟩ =
    .split (coordinate 10) (![⟨347108, by decide⟩,⟨347135, by decide⟩,⟨347163, by decide⟩,⟨347192, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1660_347193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1660 ⟨347193, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1660
    ⟨347193, by decide⟩ (by decide) (![⟨347108, by decide⟩,⟨347135, by decide⟩,⟨347163, by decide⟩,⟨347192, by decide⟩]) unmarked_context_10_1660_347193 node_context_10_1660_347193
  intro a
  fin_cases a
  · exact context_11_6640_347108
  · exact context_11_6641_347135
  · exact context_11_6642_347163
  · exact context_11_6643_347192

theorem selected_cut_13172 : selected 10 ⟨347220, by decide⟩
    (prefixPartial 11 6644) = some ⟨11, 2, 0, 347220, 6644, 2133, 262144⟩ := by
  decide +kernel

theorem context_11_6644_347220 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6644 ⟨347220, by decide⟩ :=
  accepted_of_selected 11 6644 ⟨347220, by decide⟩ ⟨11, 2, 0, 347220, 6644, 2133, 262144⟩
    (by decide) selected_cut_13172

theorem selected_cut_13173 : selected 10 ⟨347256, by decide⟩
    (prefixPartial 11 6645) = some ⟨11, 2, 0, 347256, 6645, 2133, 262144⟩ := by
  decide +kernel

theorem context_11_6645_347256 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6645 ⟨347256, by decide⟩ :=
  accepted_of_selected 11 6645 ⟨347256, by decide⟩ ⟨11, 2, 0, 347256, 6645, 2133, 262144⟩
    (by decide) selected_cut_13173

theorem selected_cut_13174 : selected 10 ⟨347289, by decide⟩
    (prefixPartial 11 6646) = some ⟨11, 2, 0, 347289, 6646, 2037, 262144⟩ := by
  decide +kernel

theorem context_11_6646_347289 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6646 ⟨347289, by decide⟩ :=
  accepted_of_selected 11 6646 ⟨347289, by decide⟩ ⟨11, 2, 0, 347289, 6646, 2037, 262144⟩
    (by decide) selected_cut_13174

theorem selected_cut_13175 : selected 10 ⟨347315, by decide⟩
    (prefixPartial 11 6647) = some ⟨11, 2, 0, 347315, 6647, 1285, 262144⟩ := by
  decide +kernel

theorem context_11_6647_347315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6647 ⟨347315, by decide⟩ :=
  accepted_of_selected 11 6647 ⟨347315, by decide⟩ ⟨11, 2, 0, 347315, 6647, 1285, 262144⟩
    (by decide) selected_cut_13175

theorem unmarked_context_10_1661_347316 : frontier 11 ⟨347316, by decide⟩
    (prefixCache 10 1661) (prefixPartial 10 1661) = false := by
  decide +kernel

theorem node_context_10_1661_347316 : EJMOriginalGlobalDAGData.nodes 11 ⟨347316, by decide⟩ =
    .split (coordinate 10) (![⟨347220, by decide⟩,⟨347256, by decide⟩,⟨347289, by decide⟩,⟨347315, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1661_347316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1661 ⟨347316, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1661
    ⟨347316, by decide⟩ (by decide) (![⟨347220, by decide⟩,⟨347256, by decide⟩,⟨347289, by decide⟩,⟨347315, by decide⟩]) unmarked_context_10_1661_347316 node_context_10_1661_347316
  intro a
  fin_cases a
  · exact context_11_6644_347220
  · exact context_11_6645_347256
  · exact context_11_6646_347289
  · exact context_11_6647_347315

theorem selected_cut_13176 : selected 10 ⟨347349, by decide⟩
    (prefixPartial 11 6648) = some ⟨11, 2, 0, 347349, 6648, 1513, 262144⟩ := by
  decide +kernel

theorem context_11_6648_347349 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6648 ⟨347349, by decide⟩ :=
  accepted_of_selected 11 6648 ⟨347349, by decide⟩ ⟨11, 2, 0, 347349, 6648, 1513, 262144⟩
    (by decide) selected_cut_13176

theorem selected_cut_13177 : selected 10 ⟨347366, by decide⟩
    (prefixPartial 11 6649) = some ⟨11, 2, 0, 347366, 6649, 1265, 262144⟩ := by
  decide +kernel

theorem context_11_6649_347366 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6649 ⟨347366, by decide⟩ :=
  accepted_of_selected 11 6649 ⟨347366, by decide⟩ ⟨11, 2, 0, 347366, 6649, 1265, 262144⟩
    (by decide) selected_cut_13177

theorem selected_cut_13178 : selected 10 ⟨347385, by decide⟩
    (prefixPartial 11 6650) = some ⟨11, 2, 0, 347385, 6650, 1049, 262144⟩ := by
  decide +kernel

theorem context_11_6650_347385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6650 ⟨347385, by decide⟩ :=
  accepted_of_selected 11 6650 ⟨347385, by decide⟩ ⟨11, 2, 0, 347385, 6650, 1049, 262144⟩
    (by decide) selected_cut_13178

theorem selected_cut_13179 : selected 10 ⟨347404, by decide⟩
    (prefixPartial 11 6651) = some ⟨11, 2, 0, 347404, 6651, 669, 262144⟩ := by
  decide +kernel

theorem context_11_6651_347404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6651 ⟨347404, by decide⟩ :=
  accepted_of_selected 11 6651 ⟨347404, by decide⟩ ⟨11, 2, 0, 347404, 6651, 669, 262144⟩
    (by decide) selected_cut_13179

theorem unmarked_context_10_1662_347405 : frontier 11 ⟨347405, by decide⟩
    (prefixCache 10 1662) (prefixPartial 10 1662) = false := by
  decide +kernel

theorem node_context_10_1662_347405 : EJMOriginalGlobalDAGData.nodes 11 ⟨347405, by decide⟩ =
    .split (coordinate 10) (![⟨347349, by decide⟩,⟨347366, by decide⟩,⟨347385, by decide⟩,⟨347404, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1662_347405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1662 ⟨347405, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1662
    ⟨347405, by decide⟩ (by decide) (![⟨347349, by decide⟩,⟨347366, by decide⟩,⟨347385, by decide⟩,⟨347404, by decide⟩]) unmarked_context_10_1662_347405 node_context_10_1662_347405
  intro a
  fin_cases a
  · exact context_11_6648_347349
  · exact context_11_6649_347366
  · exact context_11_6650_347385
  · exact context_11_6651_347404

theorem selected_cut_13180 : selected 11 ⟨347458, by decide⟩
    (prefixPartial 10 1663) = some ⟨10, 2, 0, 347458, 1663, 1577, 1048576⟩ := by
  decide +kernel

theorem context_10_1663_347458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1663 ⟨347458, by decide⟩ :=
  accepted_of_selected 10 1663 ⟨347458, by decide⟩ ⟨10, 2, 0, 347458, 1663, 1577, 1048576⟩
    (by decide) selected_cut_13180

theorem unmarked_context_9_415_347459 : frontier 12 ⟨347459, by decide⟩
    (prefixCache 9 415) (prefixPartial 9 415) = false := by
  decide +kernel

theorem node_context_9_415_347459 : EJMOriginalGlobalDAGData.nodes 12 ⟨347459, by decide⟩ =
    .split (coordinate 9) (![⟨347193, by decide⟩,⟨347316, by decide⟩,⟨347405, by decide⟩,⟨347458, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_415_347459 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 415 ⟨347459, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 415
    ⟨347459, by decide⟩ (by decide) (![⟨347193, by decide⟩,⟨347316, by decide⟩,⟨347405, by decide⟩,⟨347458, by decide⟩]) unmarked_context_9_415_347459 node_context_9_415_347459
  intro a
  fin_cases a
  · exact context_10_1660_347193
  · exact context_10_1661_347316
  · exact context_10_1662_347405
  · exact context_10_1663_347458

theorem unmarked_context_8_103_347460 : frontier 13 ⟨347460, by decide⟩
    (prefixCache 8 103) (prefixPartial 8 103) = false := by
  decide +kernel

theorem node_context_8_103_347460 : EJMOriginalGlobalDAGData.nodes 13 ⟨347460, by decide⟩ =
    .split (coordinate 8) (![⟨340834, by decide⟩,⟨345287, by decide⟩,⟨347077, by decide⟩,⟨347459, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_103_347460 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 103 ⟨347460, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 103
    ⟨347460, by decide⟩ (by decide) (![⟨340834, by decide⟩,⟨345287, by decide⟩,⟨347077, by decide⟩,⟨347459, by decide⟩]) unmarked_context_8_103_347460 node_context_8_103_347460
  intro a
  fin_cases a
  · exact context_9_412_340834
  · exact context_9_413_345287
  · exact context_9_414_347077
  · exact context_9_415_347459

theorem unmarked_context_7_25_347461 : frontier 14 ⟨347461, by decide⟩
    (prefixCache 7 25) (prefixPartial 7 25) = false := by
  decide +kernel

theorem node_context_7_25_347461 : EJMOriginalGlobalDAGData.nodes 14 ⟨347461, by decide⟩ =
    .split (coordinate 7) (![⟨313303, by decide⟩,⟨324279, by decide⟩,⟨334668, by decide⟩,⟨347460, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_25_347461 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 25 ⟨347461, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 25
    ⟨347461, by decide⟩ (by decide) (![⟨313303, by decide⟩,⟨324279, by decide⟩,⟨334668, by decide⟩,⟨347460, by decide⟩]) unmarked_context_7_25_347461 node_context_7_25_347461
  intro a
  fin_cases a
  · exact context_8_100_313303
  · exact context_8_101_324279
  · exact context_8_102_334668
  · exact context_8_103_347460

theorem selected_cut_13181 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 26624) = some ⟨12, 1, 0, 34034, 26624, 1, 65536⟩ := by
  decide +kernel

theorem context_12_26624_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26624 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 26624 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 26624, 1, 65536⟩
    (by decide) selected_cut_13181

theorem selected_cut_13182 : selected 8 ⟨347529, by decide⟩
    (prefixPartial 13 106500) = some ⟨13, 2, 0, 347529, 106500, 2529, 16384⟩ := by
  decide +kernel

theorem context_13_106500_347529 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106500 ⟨347529, by decide⟩ :=
  accepted_of_selected 13 106500 ⟨347529, by decide⟩ ⟨13, 2, 0, 347529, 106500, 2529, 16384⟩
    (by decide) selected_cut_13182

theorem selected_cut_13183 : selected 8 ⟨347578, by decide⟩
    (prefixPartial 13 106501) = some ⟨13, 2, 0, 347578, 106501, 1625, 16384⟩ := by
  decide +kernel

theorem context_13_106501_347578 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106501 ⟨347578, by decide⟩ :=
  accepted_of_selected 13 106501 ⟨347578, by decide⟩ ⟨13, 2, 0, 347578, 106501, 1625, 16384⟩
    (by decide) selected_cut_13183

theorem selected_cut_13184 : selected 8 ⟨347597, by decide⟩
    (prefixPartial 13 106502) = some ⟨13, 2, 0, 347597, 106502, 637, 16384⟩ := by
  decide +kernel

theorem context_13_106502_347597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106502 ⟨347597, by decide⟩ :=
  accepted_of_selected 13 106502 ⟨347597, by decide⟩ ⟨13, 2, 0, 347597, 106502, 637, 16384⟩
    (by decide) selected_cut_13184

theorem selected_cut_13185 : selected 8 ⟨347599, by decide⟩
    (prefixPartial 13 106503) = some ⟨13, 2, 0, 347599, 106503, 125, 16384⟩ := by
  decide +kernel

theorem context_13_106503_347599 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106503 ⟨347599, by decide⟩ :=
  accepted_of_selected 13 106503 ⟨347599, by decide⟩ ⟨13, 2, 0, 347599, 106503, 125, 16384⟩
    (by decide) selected_cut_13185

theorem unmarked_context_12_26625_347600 : frontier 9 ⟨347600, by decide⟩
    (prefixCache 12 26625) (prefixPartial 12 26625) = false := by
  decide +kernel

theorem node_context_12_26625_347600 : EJMOriginalGlobalDAGData.nodes 9 ⟨347600, by decide⟩ =
    .split (coordinate 12) (![⟨347529, by decide⟩,⟨347578, by decide⟩,⟨347597, by decide⟩,⟨347599, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26625_347600 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26625 ⟨347600, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26625
    ⟨347600, by decide⟩ (by decide) (![⟨347529, by decide⟩,⟨347578, by decide⟩,⟨347597, by decide⟩,⟨347599, by decide⟩]) unmarked_context_12_26625_347600 node_context_12_26625_347600
  intro a
  fin_cases a
  · exact context_13_106500_347529
  · exact context_13_106501_347578
  · exact context_13_106502_347597
  · exact context_13_106503_347599

theorem selected_cut_13186 : selected 9 ⟨347601, by decide⟩
    (prefixPartial 12 26626) = some ⟨12, 1, 0, 347601, 26626, 1, 65536⟩ := by
  decide +kernel

theorem context_12_26626_347601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26626 ⟨347601, by decide⟩ :=
  accepted_of_selected 12 26626 ⟨347601, by decide⟩ ⟨12, 1, 0, 347601, 26626, 1, 65536⟩
    (by decide) selected_cut_13186

theorem selected_cut_13187 : selected 8 ⟨347665, by decide⟩
    (prefixPartial 13 106508) = some ⟨13, 2, 0, 347665, 106508, 3173, 16384⟩ := by
  decide +kernel

theorem context_13_106508_347665 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106508 ⟨347665, by decide⟩ :=
  accepted_of_selected 13 106508 ⟨347665, by decide⟩ ⟨13, 2, 0, 347665, 106508, 3173, 16384⟩
    (by decide) selected_cut_13187

theorem selected_cut_13188 : selected 8 ⟨347727, by decide⟩
    (prefixPartial 13 106509) = some ⟨13, 2, 0, 347727, 106509, 3301, 16384⟩ := by
  decide +kernel

theorem context_13_106509_347727 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106509 ⟨347727, by decide⟩ :=
  accepted_of_selected 13 106509 ⟨347727, by decide⟩ ⟨13, 2, 0, 347727, 106509, 3301, 16384⟩
    (by decide) selected_cut_13188

theorem selected_cut_13189 : selected 8 ⟨347752, by decide⟩
    (prefixPartial 13 106510) = some ⟨13, 2, 0, 347752, 106510, 1721, 16384⟩ := by
  decide +kernel

theorem context_13_106510_347752 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106510 ⟨347752, by decide⟩ :=
  accepted_of_selected 13 106510 ⟨347752, by decide⟩ ⟨13, 2, 0, 347752, 106510, 1721, 16384⟩
    (by decide) selected_cut_13189

theorem selected_cut_13190 : selected 8 ⟨347763, by decide⟩
    (prefixPartial 13 106511) = some ⟨13, 2, 0, 347763, 106511, 1013, 16384⟩ := by
  decide +kernel

theorem context_13_106511_347763 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106511 ⟨347763, by decide⟩ :=
  accepted_of_selected 13 106511 ⟨347763, by decide⟩ ⟨13, 2, 0, 347763, 106511, 1013, 16384⟩
    (by decide) selected_cut_13190

theorem unmarked_context_12_26627_347764 : frontier 9 ⟨347764, by decide⟩
    (prefixCache 12 26627) (prefixPartial 12 26627) = false := by
  decide +kernel

theorem node_context_12_26627_347764 : EJMOriginalGlobalDAGData.nodes 9 ⟨347764, by decide⟩ =
    .split (coordinate 12) (![⟨347665, by decide⟩,⟨347727, by decide⟩,⟨347752, by decide⟩,⟨347763, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26627_347764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26627 ⟨347764, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26627
    ⟨347764, by decide⟩ (by decide) (![⟨347665, by decide⟩,⟨347727, by decide⟩,⟨347752, by decide⟩,⟨347763, by decide⟩]) unmarked_context_12_26627_347764 node_context_12_26627_347764
  intro a
  fin_cases a
  · exact context_13_106508_347665
  · exact context_13_106509_347727
  · exact context_13_106510_347752
  · exact context_13_106511_347763

theorem unmarked_context_11_6656_347765 : frontier 10 ⟨347765, by decide⟩
    (prefixCache 11 6656) (prefixPartial 11 6656) = false := by
  decide +kernel

theorem node_context_11_6656_347765 : EJMOriginalGlobalDAGData.nodes 10 ⟨347765, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨347600, by decide⟩,⟨347601, by decide⟩,⟨347764, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6656_347765 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6656 ⟨347765, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6656
    ⟨347765, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨347600, by decide⟩,⟨347601, by decide⟩,⟨347764, by decide⟩]) unmarked_context_11_6656_347765 node_context_11_6656_347765
  intro a
  fin_cases a
  · exact context_12_26624_34034
  · exact context_12_26625_347600
  · exact context_12_26626_347601
  · exact context_12_26627_347764

theorem selected_cut_13191 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 26628) = some ⟨12, 1, 0, 34034, 26628, 1, 65536⟩ := by
  decide +kernel

theorem context_12_26628_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26628 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 26628 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 26628, 1, 65536⟩
    (by decide) selected_cut_13191

theorem selected_cut_13192 : selected 8 ⟨347812, by decide⟩
    (prefixPartial 13 106516) = some ⟨13, 2, 0, 347812, 106516, 3157, 16384⟩ := by
  decide +kernel

theorem context_13_106516_347812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106516 ⟨347812, by decide⟩ :=
  accepted_of_selected 13 106516 ⟨347812, by decide⟩ ⟨13, 2, 0, 347812, 106516, 3157, 16384⟩
    (by decide) selected_cut_13192

theorem selected_cut_13193 : selected 8 ⟨347866, by decide⟩
    (prefixPartial 13 106517) = some ⟨13, 2, 0, 347866, 106517, 2957, 16384⟩ := by
  decide +kernel

theorem context_13_106517_347866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106517 ⟨347866, by decide⟩ :=
  accepted_of_selected 13 106517 ⟨347866, by decide⟩ ⟨13, 2, 0, 347866, 106517, 2957, 16384⟩
    (by decide) selected_cut_13193

theorem selected_cut_13194 : selected 8 ⟨347885, by decide⟩
    (prefixPartial 13 106518) = some ⟨13, 2, 0, 347885, 106518, 2077, 16384⟩ := by
  decide +kernel

theorem context_13_106518_347885 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106518 ⟨347885, by decide⟩ :=
  accepted_of_selected 13 106518 ⟨347885, by decide⟩ ⟨13, 2, 0, 347885, 106518, 2077, 16384⟩
    (by decide) selected_cut_13194

theorem selected_cut_13195 : selected 8 ⟨347896, by decide⟩
    (prefixPartial 13 106519) = some ⟨13, 2, 0, 347896, 106519, 1153, 16384⟩ := by
  decide +kernel

theorem context_13_106519_347896 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106519 ⟨347896, by decide⟩ :=
  accepted_of_selected 13 106519 ⟨347896, by decide⟩ ⟨13, 2, 0, 347896, 106519, 1153, 16384⟩
    (by decide) selected_cut_13195

theorem unmarked_context_12_26629_347897 : frontier 9 ⟨347897, by decide⟩
    (prefixCache 12 26629) (prefixPartial 12 26629) = false := by
  decide +kernel

theorem node_context_12_26629_347897 : EJMOriginalGlobalDAGData.nodes 9 ⟨347897, by decide⟩ =
    .split (coordinate 12) (![⟨347812, by decide⟩,⟨347866, by decide⟩,⟨347885, by decide⟩,⟨347896, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26629_347897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26629 ⟨347897, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26629
    ⟨347897, by decide⟩ (by decide) (![⟨347812, by decide⟩,⟨347866, by decide⟩,⟨347885, by decide⟩,⟨347896, by decide⟩]) unmarked_context_12_26629_347897 node_context_12_26629_347897
  intro a
  fin_cases a
  · exact context_13_106516_347812
  · exact context_13_106517_347866
  · exact context_13_106518_347885
  · exact context_13_106519_347896

theorem selected_cut_13196 : selected 8 ⟨347936, by decide⟩
    (prefixPartial 13 106520) = some ⟨13, 2, 0, 347936, 106520, 2881, 16384⟩ := by
  decide +kernel

theorem context_13_106520_347936 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106520 ⟨347936, by decide⟩ :=
  accepted_of_selected 13 106520 ⟨347936, by decide⟩ ⟨13, 2, 0, 347936, 106520, 2881, 16384⟩
    (by decide) selected_cut_13196

theorem selected_cut_13197 : selected 8 ⟨348010, by decide⟩
    (prefixPartial 13 106521) = some ⟨13, 2, 0, 348010, 106521, 3701, 16384⟩ := by
  decide +kernel

theorem context_13_106521_348010 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106521 ⟨348010, by decide⟩ :=
  accepted_of_selected 13 106521 ⟨348010, by decide⟩ ⟨13, 2, 0, 348010, 106521, 3701, 16384⟩
    (by decide) selected_cut_13197

theorem selected_cut_13198 : selected 8 ⟨348039, by decide⟩
    (prefixPartial 13 106522) = some ⟨13, 2, 0, 348039, 106522, 2285, 16384⟩ := by
  decide +kernel

theorem context_13_106522_348039 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106522 ⟨348039, by decide⟩ :=
  accepted_of_selected 13 106522 ⟨348039, by decide⟩ ⟨13, 2, 0, 348039, 106522, 2285, 16384⟩
    (by decide) selected_cut_13198

theorem selected_cut_13199 : selected 8 ⟨348050, by decide⟩
    (prefixPartial 13 106523) = some ⟨13, 2, 0, 348050, 106523, 1133, 16384⟩ := by
  decide +kernel

theorem context_13_106523_348050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106523 ⟨348050, by decide⟩ :=
  accepted_of_selected 13 106523 ⟨348050, by decide⟩ ⟨13, 2, 0, 348050, 106523, 1133, 16384⟩
    (by decide) selected_cut_13199

theorem unmarked_context_12_26630_348051 : frontier 9 ⟨348051, by decide⟩
    (prefixCache 12 26630) (prefixPartial 12 26630) = false := by
  decide +kernel

theorem node_context_12_26630_348051 : EJMOriginalGlobalDAGData.nodes 9 ⟨348051, by decide⟩ =
    .split (coordinate 12) (![⟨347936, by decide⟩,⟨348010, by decide⟩,⟨348039, by decide⟩,⟨348050, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26630_348051 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26630 ⟨348051, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26630
    ⟨348051, by decide⟩ (by decide) (![⟨347936, by decide⟩,⟨348010, by decide⟩,⟨348039, by decide⟩,⟨348050, by decide⟩]) unmarked_context_12_26630_348051 node_context_12_26630_348051
  intro a
  fin_cases a
  · exact context_13_106520_347936
  · exact context_13_106521_348010
  · exact context_13_106522_348039
  · exact context_13_106523_348050

theorem selected_cut_13200 : selected 8 ⟨348102, by decide⟩
    (prefixPartial 13 106524) = some ⟨13, 2, 0, 348102, 106524, 3545, 16384⟩ := by
  decide +kernel

theorem context_13_106524_348102 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106524 ⟨348102, by decide⟩ :=
  accepted_of_selected 13 106524 ⟨348102, by decide⟩ ⟨13, 2, 0, 348102, 106524, 3545, 16384⟩
    (by decide) selected_cut_13200

theorem selected_cut_13201 : selected 8 ⟨348179, by decide⟩
    (prefixPartial 13 106525) = some ⟨13, 2, 0, 348179, 106525, 3821, 16384⟩ := by
  decide +kernel

theorem context_13_106525_348179 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106525 ⟨348179, by decide⟩ :=
  accepted_of_selected 13 106525 ⟨348179, by decide⟩ ⟨13, 2, 0, 348179, 106525, 3821, 16384⟩
    (by decide) selected_cut_13201

theorem selected_cut_13202 : selected 8 ⟨348203, by decide⟩
    (prefixPartial 13 106526) = some ⟨13, 2, 0, 348203, 106526, 2129, 16384⟩ := by
  decide +kernel

theorem context_13_106526_348203 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106526 ⟨348203, by decide⟩ :=
  accepted_of_selected 13 106526 ⟨348203, by decide⟩ ⟨13, 2, 0, 348203, 106526, 2129, 16384⟩
    (by decide) selected_cut_13202

theorem selected_cut_13203 : selected 8 ⟨348220, by decide⟩
    (prefixPartial 13 106527) = some ⟨13, 2, 0, 348220, 106527, 1237, 16384⟩ := by
  decide +kernel

theorem context_13_106527_348220 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106527 ⟨348220, by decide⟩ :=
  accepted_of_selected 13 106527 ⟨348220, by decide⟩ ⟨13, 2, 0, 348220, 106527, 1237, 16384⟩
    (by decide) selected_cut_13203

theorem unmarked_context_12_26631_348221 : frontier 9 ⟨348221, by decide⟩
    (prefixCache 12 26631) (prefixPartial 12 26631) = false := by
  decide +kernel

theorem node_context_12_26631_348221 : EJMOriginalGlobalDAGData.nodes 9 ⟨348221, by decide⟩ =
    .split (coordinate 12) (![⟨348102, by decide⟩,⟨348179, by decide⟩,⟨348203, by decide⟩,⟨348220, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26631_348221 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26631 ⟨348221, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26631
    ⟨348221, by decide⟩ (by decide) (![⟨348102, by decide⟩,⟨348179, by decide⟩,⟨348203, by decide⟩,⟨348220, by decide⟩]) unmarked_context_12_26631_348221 node_context_12_26631_348221
  intro a
  fin_cases a
  · exact context_13_106524_348102
  · exact context_13_106525_348179
  · exact context_13_106526_348203
  · exact context_13_106527_348220

theorem unmarked_context_11_6657_348222 : frontier 10 ⟨348222, by decide⟩
    (prefixCache 11 6657) (prefixPartial 11 6657) = false := by
  decide +kernel

theorem node_context_11_6657_348222 : EJMOriginalGlobalDAGData.nodes 10 ⟨348222, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨347897, by decide⟩,⟨348051, by decide⟩,⟨348221, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6657_348222 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6657 ⟨348222, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6657
    ⟨348222, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨347897, by decide⟩,⟨348051, by decide⟩,⟨348221, by decide⟩]) unmarked_context_11_6657_348222 node_context_11_6657_348222
  intro a
  fin_cases a
  · exact context_12_26628_34034
  · exact context_12_26629_347897
  · exact context_12_26630_348051
  · exact context_12_26631_348221

theorem selected_cut_13204 : selected 8 ⟨348270, by decide⟩
    (prefixPartial 13 106528) = some ⟨13, 2, 0, 348270, 106528, 2561, 16384⟩ := by
  decide +kernel

theorem context_13_106528_348270 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106528 ⟨348270, by decide⟩ :=
  accepted_of_selected 13 106528 ⟨348270, by decide⟩ ⟨13, 2, 0, 348270, 106528, 2561, 16384⟩
    (by decide) selected_cut_13204

theorem selected_cut_13205 : selected 7 ⟨348305, by decide⟩
    (prefixPartial 14 426116) = some ⟨14, 2, 0, 348305, 426116, 1357, 4096⟩ := by
  decide +kernel

theorem context_14_426116_348305 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 426116 ⟨348305, by decide⟩ :=
  accepted_of_selected 14 426116 ⟨348305, by decide⟩ ⟨14, 2, 0, 348305, 426116, 1357, 4096⟩
    (by decide) selected_cut_13205

theorem selected_cut_13206 : selected 7 ⟨348319, by decide⟩
    (prefixPartial 14 426117) = some ⟨14, 2, 0, 348319, 426117, 825, 4096⟩ := by
  decide +kernel

theorem context_14_426117_348319 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 426117 ⟨348319, by decide⟩ :=
  accepted_of_selected 14 426117 ⟨348319, by decide⟩ ⟨14, 2, 0, 348319, 426117, 825, 4096⟩
    (by decide) selected_cut_13206

theorem selected_cut_13207 : selected 7 ⟨348345, by decide⟩
    (prefixPartial 14 426118) = some ⟨14, 2, 0, 348345, 426118, 1149, 4096⟩ := by
  decide +kernel

theorem context_14_426118_348345 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 426118 ⟨348345, by decide⟩ :=
  accepted_of_selected 14 426118 ⟨348345, by decide⟩ ⟨14, 2, 0, 348345, 426118, 1149, 4096⟩
    (by decide) selected_cut_13207

theorem selected_cut_13208 : selected 7 ⟨348361, by decide⟩
    (prefixPartial 14 426119) = some ⟨14, 2, 0, 348361, 426119, 961, 4096⟩ := by
  decide +kernel

theorem context_14_426119_348361 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 426119 ⟨348361, by decide⟩ :=
  accepted_of_selected 14 426119 ⟨348361, by decide⟩ ⟨14, 2, 0, 348361, 426119, 961, 4096⟩
    (by decide) selected_cut_13208

theorem unmarked_context_13_106529_348362 : frontier 8 ⟨348362, by decide⟩
    (prefixCache 13 106529) (prefixPartial 13 106529) = false := by
  decide +kernel

theorem node_context_13_106529_348362 : EJMOriginalGlobalDAGData.nodes 8 ⟨348362, by decide⟩ =
    .split (coordinate 13) (![⟨348305, by decide⟩,⟨348319, by decide⟩,⟨348345, by decide⟩,⟨348361, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_106529_348362 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106529 ⟨348362, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 106529
    ⟨348362, by decide⟩ (by decide) (![⟨348305, by decide⟩,⟨348319, by decide⟩,⟨348345, by decide⟩,⟨348361, by decide⟩]) unmarked_context_13_106529_348362 node_context_13_106529_348362
  intro a
  fin_cases a
  · exact context_14_426116_348305
  · exact context_14_426117_348319
  · exact context_14_426118_348345
  · exact context_14_426119_348361

theorem selected_cut_13209 : selected 8 ⟨348392, by decide⟩
    (prefixPartial 13 106530) = some ⟨13, 2, 0, 348392, 106530, 1977, 16384⟩ := by
  decide +kernel

theorem context_13_106530_348392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106530 ⟨348392, by decide⟩ :=
  accepted_of_selected 13 106530 ⟨348392, by decide⟩ ⟨13, 2, 0, 348392, 106530, 1977, 16384⟩
    (by decide) selected_cut_13209

theorem selected_cut_13210 : selected 8 ⟨348413, by decide⟩
    (prefixPartial 13 106531) = some ⟨13, 2, 0, 348413, 106531, 1197, 16384⟩ := by
  decide +kernel

theorem context_13_106531_348413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106531 ⟨348413, by decide⟩ :=
  accepted_of_selected 13 106531 ⟨348413, by decide⟩ ⟨13, 2, 0, 348413, 106531, 1197, 16384⟩
    (by decide) selected_cut_13210

theorem unmarked_context_12_26632_348414 : frontier 9 ⟨348414, by decide⟩
    (prefixCache 12 26632) (prefixPartial 12 26632) = false := by
  decide +kernel

theorem node_context_12_26632_348414 : EJMOriginalGlobalDAGData.nodes 9 ⟨348414, by decide⟩ =
    .split (coordinate 12) (![⟨348270, by decide⟩,⟨348362, by decide⟩,⟨348392, by decide⟩,⟨348413, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26632_348414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26632 ⟨348414, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26632
    ⟨348414, by decide⟩ (by decide) (![⟨348270, by decide⟩,⟨348362, by decide⟩,⟨348392, by decide⟩,⟨348413, by decide⟩]) unmarked_context_12_26632_348414 node_context_12_26632_348414
  intro a
  fin_cases a
  · exact context_13_106528_348270
  · exact context_13_106529_348362
  · exact context_13_106530_348392
  · exact context_13_106531_348413

theorem selected_cut_13211 : selected 8 ⟨348470, by decide⟩
    (prefixPartial 13 106532) = some ⟨13, 2, 0, 348470, 106532, 3097, 16384⟩ := by
  decide +kernel

theorem context_13_106532_348470 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106532 ⟨348470, by decide⟩ :=
  accepted_of_selected 13 106532 ⟨348470, by decide⟩ ⟨13, 2, 0, 348470, 106532, 3097, 16384⟩
    (by decide) selected_cut_13211

theorem selected_cut_13212 : selected 8 ⟨348526, by decide⟩
    (prefixPartial 13 106533) = some ⟨13, 2, 0, 348526, 106533, 3597, 16384⟩ := by
  decide +kernel

theorem context_13_106533_348526 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106533 ⟨348526, by decide⟩ :=
  accepted_of_selected 13 106533 ⟨348526, by decide⟩ ⟨13, 2, 0, 348526, 106533, 3597, 16384⟩
    (by decide) selected_cut_13212

theorem selected_cut_13213 : selected 8 ⟨348546, by decide⟩
    (prefixPartial 13 106534) = some ⟨13, 2, 0, 348546, 106534, 1921, 16384⟩ := by
  decide +kernel

theorem context_13_106534_348546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106534 ⟨348546, by decide⟩ :=
  accepted_of_selected 13 106534 ⟨348546, by decide⟩ ⟨13, 2, 0, 348546, 106534, 1921, 16384⟩
    (by decide) selected_cut_13213

theorem selected_cut_13214 : selected 8 ⟨348560, by decide⟩
    (prefixPartial 13 106535) = some ⟨13, 2, 0, 348560, 106535, 1165, 16384⟩ := by
  decide +kernel

theorem context_13_106535_348560 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106535 ⟨348560, by decide⟩ :=
  accepted_of_selected 13 106535 ⟨348560, by decide⟩ ⟨13, 2, 0, 348560, 106535, 1165, 16384⟩
    (by decide) selected_cut_13214

theorem unmarked_context_12_26633_348561 : frontier 9 ⟨348561, by decide⟩
    (prefixCache 12 26633) (prefixPartial 12 26633) = false := by
  decide +kernel

theorem node_context_12_26633_348561 : EJMOriginalGlobalDAGData.nodes 9 ⟨348561, by decide⟩ =
    .split (coordinate 12) (![⟨348470, by decide⟩,⟨348526, by decide⟩,⟨348546, by decide⟩,⟨348560, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26633_348561 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26633 ⟨348561, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26633
    ⟨348561, by decide⟩ (by decide) (![⟨348470, by decide⟩,⟨348526, by decide⟩,⟨348546, by decide⟩,⟨348560, by decide⟩]) unmarked_context_12_26633_348561 node_context_12_26633_348561
  intro a
  fin_cases a
  · exact context_13_106532_348470
  · exact context_13_106533_348526
  · exact context_13_106534_348546
  · exact context_13_106535_348560

theorem selected_cut_13215 : selected 8 ⟨348599, by decide⟩
    (prefixPartial 13 106536) = some ⟨13, 2, 0, 348599, 106536, 2245, 16384⟩ := by
  decide +kernel

theorem context_13_106536_348599 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106536 ⟨348599, by decide⟩ :=
  accepted_of_selected 13 106536 ⟨348599, by decide⟩ ⟨13, 2, 0, 348599, 106536, 2245, 16384⟩
    (by decide) selected_cut_13215

theorem selected_cut_13216 : selected 8 ⟨348669, by decide⟩
    (prefixPartial 13 106537) = some ⟨13, 2, 0, 348669, 106537, 3845, 16384⟩ := by
  decide +kernel

theorem context_13_106537_348669 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106537 ⟨348669, by decide⟩ :=
  accepted_of_selected 13 106537 ⟨348669, by decide⟩ ⟨13, 2, 0, 348669, 106537, 3845, 16384⟩
    (by decide) selected_cut_13216

theorem selected_cut_13217 : selected 8 ⟨348692, by decide⟩
    (prefixPartial 13 106538) = some ⟨13, 2, 0, 348692, 106538, 1945, 16384⟩ := by
  decide +kernel

theorem context_13_106538_348692 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106538 ⟨348692, by decide⟩ :=
  accepted_of_selected 13 106538 ⟨348692, by decide⟩ ⟨13, 2, 0, 348692, 106538, 1945, 16384⟩
    (by decide) selected_cut_13217

theorem selected_cut_13218 : selected 8 ⟨348704, by decide⟩
    (prefixPartial 13 106539) = some ⟨13, 2, 0, 348704, 106539, 1169, 16384⟩ := by
  decide +kernel

theorem context_13_106539_348704 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106539 ⟨348704, by decide⟩ :=
  accepted_of_selected 13 106539 ⟨348704, by decide⟩ ⟨13, 2, 0, 348704, 106539, 1169, 16384⟩
    (by decide) selected_cut_13218

theorem unmarked_context_12_26634_348705 : frontier 9 ⟨348705, by decide⟩
    (prefixCache 12 26634) (prefixPartial 12 26634) = false := by
  decide +kernel

theorem node_context_12_26634_348705 : EJMOriginalGlobalDAGData.nodes 9 ⟨348705, by decide⟩ =
    .split (coordinate 12) (![⟨348599, by decide⟩,⟨348669, by decide⟩,⟨348692, by decide⟩,⟨348704, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26634_348705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26634 ⟨348705, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26634
    ⟨348705, by decide⟩ (by decide) (![⟨348599, by decide⟩,⟨348669, by decide⟩,⟨348692, by decide⟩,⟨348704, by decide⟩]) unmarked_context_12_26634_348705 node_context_12_26634_348705
  intro a
  fin_cases a
  · exact context_13_106536_348599
  · exact context_13_106537_348669
  · exact context_13_106538_348692
  · exact context_13_106539_348704

theorem selected_cut_13219 : selected 8 ⟨348766, by decide⟩
    (prefixPartial 13 106540) = some ⟨13, 2, 0, 348766, 106540, 3061, 16384⟩ := by
  decide +kernel

theorem context_13_106540_348766 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106540 ⟨348766, by decide⟩ :=
  accepted_of_selected 13 106540 ⟨348766, by decide⟩ ⟨13, 2, 0, 348766, 106540, 3061, 16384⟩
    (by decide) selected_cut_13219

theorem selected_cut_13220 : selected 7 ⟨348797, by decide⟩
    (prefixPartial 14 426164) = some ⟨14, 2, 0, 348797, 426164, 1177, 4096⟩ := by
  decide +kernel

theorem context_14_426164_348797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 426164 ⟨348797, by decide⟩ :=
  accepted_of_selected 14 426164 ⟨348797, by decide⟩ ⟨14, 2, 0, 348797, 426164, 1177, 4096⟩
    (by decide) selected_cut_13220

theorem selected_cut_13221 : selected 7 ⟨348811, by decide⟩
    (prefixPartial 14 426165) = some ⟨14, 2, 0, 348811, 426165, 925, 4096⟩ := by
  decide +kernel

theorem context_14_426165_348811 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 426165 ⟨348811, by decide⟩ :=
  accepted_of_selected 14 426165 ⟨348811, by decide⟩ ⟨14, 2, 0, 348811, 426165, 925, 4096⟩
    (by decide) selected_cut_13221

theorem selected_cut_13222 : selected 7 ⟨348831, by decide⟩
    (prefixPartial 14 426166) = some ⟨14, 2, 0, 348831, 426166, 1117, 4096⟩ := by
  decide +kernel

theorem context_14_426166_348831 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 426166 ⟨348831, by decide⟩ :=
  accepted_of_selected 14 426166 ⟨348831, by decide⟩ ⟨14, 2, 0, 348831, 426166, 1117, 4096⟩
    (by decide) selected_cut_13222

theorem selected_cut_13223 : selected 7 ⟨348843, by decide⟩
    (prefixPartial 14 426167) = some ⟨14, 2, 0, 348843, 426167, 901, 4096⟩ := by
  decide +kernel

theorem context_14_426167_348843 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 426167 ⟨348843, by decide⟩ :=
  accepted_of_selected 14 426167 ⟨348843, by decide⟩ ⟨14, 2, 0, 348843, 426167, 901, 4096⟩
    (by decide) selected_cut_13223

theorem unmarked_context_13_106541_348844 : frontier 8 ⟨348844, by decide⟩
    (prefixCache 13 106541) (prefixPartial 13 106541) = false := by
  decide +kernel

theorem node_context_13_106541_348844 : EJMOriginalGlobalDAGData.nodes 8 ⟨348844, by decide⟩ =
    .split (coordinate 13) (![⟨348797, by decide⟩,⟨348811, by decide⟩,⟨348831, by decide⟩,⟨348843, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_106541_348844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106541 ⟨348844, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 106541
    ⟨348844, by decide⟩ (by decide) (![⟨348797, by decide⟩,⟨348811, by decide⟩,⟨348831, by decide⟩,⟨348843, by decide⟩]) unmarked_context_13_106541_348844 node_context_13_106541_348844
  intro a
  fin_cases a
  · exact context_14_426164_348797
  · exact context_14_426165_348811
  · exact context_14_426166_348831
  · exact context_14_426167_348843

theorem selected_cut_13224 : selected 8 ⟨348862, by decide⟩
    (prefixPartial 13 106542) = some ⟨13, 2, 0, 348862, 106542, 1949, 16384⟩ := by
  decide +kernel

theorem context_13_106542_348862 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106542 ⟨348862, by decide⟩ :=
  accepted_of_selected 13 106542 ⟨348862, by decide⟩ ⟨13, 2, 0, 348862, 106542, 1949, 16384⟩
    (by decide) selected_cut_13224

theorem selected_cut_13225 : selected 8 ⟨348875, by decide⟩
    (prefixPartial 13 106543) = some ⟨13, 2, 0, 348875, 106543, 1249, 16384⟩ := by
  decide +kernel

theorem context_13_106543_348875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106543 ⟨348875, by decide⟩ :=
  accepted_of_selected 13 106543 ⟨348875, by decide⟩ ⟨13, 2, 0, 348875, 106543, 1249, 16384⟩
    (by decide) selected_cut_13225

theorem unmarked_context_12_26635_348876 : frontier 9 ⟨348876, by decide⟩
    (prefixCache 12 26635) (prefixPartial 12 26635) = false := by
  decide +kernel

theorem node_context_12_26635_348876 : EJMOriginalGlobalDAGData.nodes 9 ⟨348876, by decide⟩ =
    .split (coordinate 12) (![⟨348766, by decide⟩,⟨348844, by decide⟩,⟨348862, by decide⟩,⟨348875, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26635_348876 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26635 ⟨348876, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26635
    ⟨348876, by decide⟩ (by decide) (![⟨348766, by decide⟩,⟨348844, by decide⟩,⟨348862, by decide⟩,⟨348875, by decide⟩]) unmarked_context_12_26635_348876 node_context_12_26635_348876
  intro a
  fin_cases a
  · exact context_13_106540_348766
  · exact context_13_106541_348844
  · exact context_13_106542_348862
  · exact context_13_106543_348875

theorem unmarked_context_11_6658_348877 : frontier 10 ⟨348877, by decide⟩
    (prefixCache 11 6658) (prefixPartial 11 6658) = false := by
  decide +kernel

theorem node_context_11_6658_348877 : EJMOriginalGlobalDAGData.nodes 10 ⟨348877, by decide⟩ =
    .split (coordinate 11) (![⟨348414, by decide⟩,⟨348561, by decide⟩,⟨348705, by decide⟩,⟨348876, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6658_348877 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6658 ⟨348877, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6658
    ⟨348877, by decide⟩ (by decide) (![⟨348414, by decide⟩,⟨348561, by decide⟩,⟨348705, by decide⟩,⟨348876, by decide⟩]) unmarked_context_11_6658_348877 node_context_11_6658_348877
  intro a
  fin_cases a
  · exact context_12_26632_348414
  · exact context_12_26633_348561
  · exact context_12_26634_348705
  · exact context_12_26635_348876

theorem selected_cut_13226 : selected 8 ⟨348915, by decide⟩
    (prefixPartial 13 106544) = some ⟨13, 2, 0, 348915, 106544, 2177, 16384⟩ := by
  decide +kernel

theorem context_13_106544_348915 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106544 ⟨348915, by decide⟩ :=
  accepted_of_selected 13 106544 ⟨348915, by decide⟩ ⟨13, 2, 0, 348915, 106544, 2177, 16384⟩
    (by decide) selected_cut_13226

theorem selected_cut_13227 : selected 8 ⟨348984, by decide⟩
    (prefixPartial 13 106545) = some ⟨13, 2, 0, 348984, 106545, 3905, 16384⟩ := by
  decide +kernel

theorem context_13_106545_348984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106545 ⟨348984, by decide⟩ :=
  accepted_of_selected 13 106545 ⟨348984, by decide⟩ ⟨13, 2, 0, 348984, 106545, 3905, 16384⟩
    (by decide) selected_cut_13227

theorem selected_cut_13228 : selected 8 ⟨349003, by decide⟩
    (prefixPartial 13 106546) = some ⟨13, 2, 0, 349003, 106546, 1961, 16384⟩ := by
  decide +kernel

theorem context_13_106546_349003 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106546 ⟨349003, by decide⟩ :=
  accepted_of_selected 13 106546 ⟨349003, by decide⟩ ⟨13, 2, 0, 349003, 106546, 1961, 16384⟩
    (by decide) selected_cut_13228

theorem selected_cut_13229 : selected 8 ⟨349010, by decide⟩
    (prefixPartial 13 106547) = some ⟨13, 2, 0, 349010, 106547, 1069, 16384⟩ := by
  decide +kernel

theorem context_13_106547_349010 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106547 ⟨349010, by decide⟩ :=
  accepted_of_selected 13 106547 ⟨349010, by decide⟩ ⟨13, 2, 0, 349010, 106547, 1069, 16384⟩
    (by decide) selected_cut_13229

theorem unmarked_context_12_26636_349011 : frontier 9 ⟨349011, by decide⟩
    (prefixCache 12 26636) (prefixPartial 12 26636) = false := by
  decide +kernel

theorem node_context_12_26636_349011 : EJMOriginalGlobalDAGData.nodes 9 ⟨349011, by decide⟩ =
    .split (coordinate 12) (![⟨348915, by decide⟩,⟨348984, by decide⟩,⟨349003, by decide⟩,⟨349010, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26636_349011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26636 ⟨349011, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26636
    ⟨349011, by decide⟩ (by decide) (![⟨348915, by decide⟩,⟨348984, by decide⟩,⟨349003, by decide⟩,⟨349010, by decide⟩]) unmarked_context_12_26636_349011 node_context_12_26636_349011
  intro a
  fin_cases a
  · exact context_13_106544_348915
  · exact context_13_106545_348984
  · exact context_13_106546_349003
  · exact context_13_106547_349010

theorem selected_cut_13230 : selected 8 ⟨349051, by decide⟩
    (prefixPartial 13 106548) = some ⟨13, 2, 0, 349051, 106548, 2853, 16384⟩ := by
  decide +kernel

theorem context_13_106548_349051 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106548 ⟨349051, by decide⟩ :=
  accepted_of_selected 13 106548 ⟨349051, by decide⟩ ⟨13, 2, 0, 349051, 106548, 2853, 16384⟩
    (by decide) selected_cut_13230

theorem selected_cut_13231 : selected 8 ⟨349104, by decide⟩
    (prefixPartial 13 106549) = some ⟨13, 2, 0, 349104, 106549, 3473, 16384⟩ := by
  decide +kernel

theorem context_13_106549_349104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106549 ⟨349104, by decide⟩ :=
  accepted_of_selected 13 106549 ⟨349104, by decide⟩ ⟨13, 2, 0, 349104, 106549, 3473, 16384⟩
    (by decide) selected_cut_13231

theorem selected_cut_13232 : selected 8 ⟨349127, by decide⟩
    (prefixPartial 13 106550) = some ⟨13, 2, 0, 349127, 106550, 2021, 16384⟩ := by
  decide +kernel

theorem context_13_106550_349127 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106550 ⟨349127, by decide⟩ :=
  accepted_of_selected 13 106550 ⟨349127, by decide⟩ ⟨13, 2, 0, 349127, 106550, 2021, 16384⟩
    (by decide) selected_cut_13232

theorem selected_cut_13233 : selected 8 ⟨349136, by decide⟩
    (prefixPartial 13 106551) = some ⟨13, 2, 0, 349136, 106551, 1025, 16384⟩ := by
  decide +kernel

theorem context_13_106551_349136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106551 ⟨349136, by decide⟩ :=
  accepted_of_selected 13 106551 ⟨349136, by decide⟩ ⟨13, 2, 0, 349136, 106551, 1025, 16384⟩
    (by decide) selected_cut_13233

theorem unmarked_context_12_26637_349137 : frontier 9 ⟨349137, by decide⟩
    (prefixCache 12 26637) (prefixPartial 12 26637) = false := by
  decide +kernel

theorem node_context_12_26637_349137 : EJMOriginalGlobalDAGData.nodes 9 ⟨349137, by decide⟩ =
    .split (coordinate 12) (![⟨349051, by decide⟩,⟨349104, by decide⟩,⟨349127, by decide⟩,⟨349136, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26637_349137 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26637 ⟨349137, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26637
    ⟨349137, by decide⟩ (by decide) (![⟨349051, by decide⟩,⟨349104, by decide⟩,⟨349127, by decide⟩,⟨349136, by decide⟩]) unmarked_context_12_26637_349137 node_context_12_26637_349137
  intro a
  fin_cases a
  · exact context_13_106548_349051
  · exact context_13_106549_349104
  · exact context_13_106550_349127
  · exact context_13_106551_349136

theorem selected_cut_13234 : selected 8 ⟨349173, by decide⟩
    (prefixPartial 13 106552) = some ⟨13, 2, 0, 349173, 106552, 2517, 16384⟩ := by
  decide +kernel

theorem context_13_106552_349173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106552 ⟨349173, by decide⟩ :=
  accepted_of_selected 13 106552 ⟨349173, by decide⟩ ⟨13, 2, 0, 349173, 106552, 2517, 16384⟩
    (by decide) selected_cut_13234

theorem selected_cut_13235 : selected 8 ⟨349243, by decide⟩
    (prefixPartial 13 106553) = some ⟨13, 2, 0, 349243, 106553, 3829, 16384⟩ := by
  decide +kernel

theorem context_13_106553_349243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106553 ⟨349243, by decide⟩ :=
  accepted_of_selected 13 106553 ⟨349243, by decide⟩ ⟨13, 2, 0, 349243, 106553, 3829, 16384⟩
    (by decide) selected_cut_13235

theorem selected_cut_13236 : selected 8 ⟨349268, by decide⟩
    (prefixPartial 13 106554) = some ⟨13, 2, 0, 349268, 106554, 2133, 16384⟩ := by
  decide +kernel

theorem context_13_106554_349268 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106554 ⟨349268, by decide⟩ :=
  accepted_of_selected 13 106554 ⟨349268, by decide⟩ ⟨13, 2, 0, 349268, 106554, 2133, 16384⟩
    (by decide) selected_cut_13236

theorem selected_cut_13237 : selected 8 ⟨349279, by decide⟩
    (prefixPartial 13 106555) = some ⟨13, 2, 0, 349279, 106555, 1025, 16384⟩ := by
  decide +kernel

theorem context_13_106555_349279 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106555 ⟨349279, by decide⟩ :=
  accepted_of_selected 13 106555 ⟨349279, by decide⟩ ⟨13, 2, 0, 349279, 106555, 1025, 16384⟩
    (by decide) selected_cut_13237

theorem unmarked_context_12_26638_349280 : frontier 9 ⟨349280, by decide⟩
    (prefixCache 12 26638) (prefixPartial 12 26638) = false := by
  decide +kernel

theorem node_context_12_26638_349280 : EJMOriginalGlobalDAGData.nodes 9 ⟨349280, by decide⟩ =
    .split (coordinate 12) (![⟨349173, by decide⟩,⟨349243, by decide⟩,⟨349268, by decide⟩,⟨349279, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26638_349280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26638 ⟨349280, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26638
    ⟨349280, by decide⟩ (by decide) (![⟨349173, by decide⟩,⟨349243, by decide⟩,⟨349268, by decide⟩,⟨349279, by decide⟩]) unmarked_context_12_26638_349280 node_context_12_26638_349280
  intro a
  fin_cases a
  · exact context_13_106552_349173
  · exact context_13_106553_349243
  · exact context_13_106554_349268
  · exact context_13_106555_349279

theorem selected_cut_13238 : selected 8 ⟨349342, by decide⟩
    (prefixPartial 13 106556) = some ⟨13, 2, 0, 349342, 106556, 2813, 16384⟩ := by
  decide +kernel

theorem context_13_106556_349342 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106556 ⟨349342, by decide⟩ :=
  accepted_of_selected 13 106556 ⟨349342, by decide⟩ ⟨13, 2, 0, 349342, 106556, 2813, 16384⟩
    (by decide) selected_cut_13238

theorem selected_cut_13239 : selected 8 ⟨349400, by decide⟩
    (prefixPartial 13 106557) = some ⟨13, 2, 0, 349400, 106557, 3701, 16384⟩ := by
  decide +kernel

theorem context_13_106557_349400 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106557 ⟨349400, by decide⟩ :=
  accepted_of_selected 13 106557 ⟨349400, by decide⟩ ⟨13, 2, 0, 349400, 106557, 3701, 16384⟩
    (by decide) selected_cut_13239

theorem selected_cut_13240 : selected 8 ⟨349424, by decide⟩
    (prefixPartial 13 106558) = some ⟨13, 2, 0, 349424, 106558, 1909, 16384⟩ := by
  decide +kernel

theorem context_13_106558_349424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106558 ⟨349424, by decide⟩ :=
  accepted_of_selected 13 106558 ⟨349424, by decide⟩ ⟨13, 2, 0, 349424, 106558, 1909, 16384⟩
    (by decide) selected_cut_13240

theorem selected_cut_13241 : selected 8 ⟨349436, by decide⟩
    (prefixPartial 13 106559) = some ⟨13, 2, 0, 349436, 106559, 1029, 16384⟩ := by
  decide +kernel

theorem context_13_106559_349436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106559 ⟨349436, by decide⟩ :=
  accepted_of_selected 13 106559 ⟨349436, by decide⟩ ⟨13, 2, 0, 349436, 106559, 1029, 16384⟩
    (by decide) selected_cut_13241

theorem unmarked_context_12_26639_349437 : frontier 9 ⟨349437, by decide⟩
    (prefixCache 12 26639) (prefixPartial 12 26639) = false := by
  decide +kernel

theorem node_context_12_26639_349437 : EJMOriginalGlobalDAGData.nodes 9 ⟨349437, by decide⟩ =
    .split (coordinate 12) (![⟨349342, by decide⟩,⟨349400, by decide⟩,⟨349424, by decide⟩,⟨349436, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26639_349437 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26639 ⟨349437, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26639
    ⟨349437, by decide⟩ (by decide) (![⟨349342, by decide⟩,⟨349400, by decide⟩,⟨349424, by decide⟩,⟨349436, by decide⟩]) unmarked_context_12_26639_349437 node_context_12_26639_349437
  intro a
  fin_cases a
  · exact context_13_106556_349342
  · exact context_13_106557_349400
  · exact context_13_106558_349424
  · exact context_13_106559_349436

theorem unmarked_context_11_6659_349438 : frontier 10 ⟨349438, by decide⟩
    (prefixCache 11 6659) (prefixPartial 11 6659) = false := by
  decide +kernel

theorem node_context_11_6659_349438 : EJMOriginalGlobalDAGData.nodes 10 ⟨349438, by decide⟩ =
    .split (coordinate 11) (![⟨349011, by decide⟩,⟨349137, by decide⟩,⟨349280, by decide⟩,⟨349437, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6659_349438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6659 ⟨349438, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6659
    ⟨349438, by decide⟩ (by decide) (![⟨349011, by decide⟩,⟨349137, by decide⟩,⟨349280, by decide⟩,⟨349437, by decide⟩]) unmarked_context_11_6659_349438 node_context_11_6659_349438
  intro a
  fin_cases a
  · exact context_12_26636_349011
  · exact context_12_26637_349137
  · exact context_12_26638_349280
  · exact context_12_26639_349437

theorem unmarked_context_10_1664_349439 : frontier 11 ⟨349439, by decide⟩
    (prefixCache 10 1664) (prefixPartial 10 1664) = false := by
  decide +kernel

theorem node_context_10_1664_349439 : EJMOriginalGlobalDAGData.nodes 11 ⟨349439, by decide⟩ =
    .split (coordinate 10) (![⟨347765, by decide⟩,⟨348222, by decide⟩,⟨348877, by decide⟩,⟨349438, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1664_349439 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1664 ⟨349439, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1664
    ⟨349439, by decide⟩ (by decide) (![⟨347765, by decide⟩,⟨348222, by decide⟩,⟨348877, by decide⟩,⟨349438, by decide⟩]) unmarked_context_10_1664_349439 node_context_10_1664_349439
  intro a
  fin_cases a
  · exact context_11_6656_347765
  · exact context_11_6657_348222
  · exact context_11_6658_348877
  · exact context_11_6659_349438

theorem selected_cut_13242 : selected 9 ⟨266170, by decide⟩
    (prefixPartial 12 26640) = some ⟨12, 1, 0, 266170, 26640, 1, 65536⟩ := by
  decide +kernel

theorem context_12_26640_266170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26640 ⟨266170, by decide⟩ :=
  accepted_of_selected 12 26640 ⟨266170, by decide⟩ ⟨12, 1, 0, 266170, 26640, 1, 65536⟩
    (by decide) selected_cut_13242

theorem selected_cut_13243 : selected 8 ⟨349454, by decide⟩
    (prefixPartial 13 106564) = some ⟨13, 2, 0, 349454, 106564, 1277, 16384⟩ := by
  decide +kernel

theorem context_13_106564_349454 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106564 ⟨349454, by decide⟩ :=
  accepted_of_selected 13 106564 ⟨349454, by decide⟩ ⟨13, 2, 0, 349454, 106564, 1277, 16384⟩
    (by decide) selected_cut_13243

theorem selected_cut_13244 : selected 8 ⟨349477, by decide⟩
    (prefixPartial 13 106565) = some ⟨13, 2, 0, 349477, 106565, 1473, 16384⟩ := by
  decide +kernel

theorem context_13_106565_349477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106565 ⟨349477, by decide⟩ :=
  accepted_of_selected 13 106565 ⟨349477, by decide⟩ ⟨13, 2, 0, 349477, 106565, 1473, 16384⟩
    (by decide) selected_cut_13244

theorem selected_cut_13245 : selected 8 ⟨349493, by decide⟩
    (prefixPartial 13 106566) = some ⟨13, 2, 0, 349493, 106566, 1205, 16384⟩ := by
  decide +kernel

theorem context_13_106566_349493 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106566 ⟨349493, by decide⟩ :=
  accepted_of_selected 13 106566 ⟨349493, by decide⟩ ⟨13, 2, 0, 349493, 106566, 1205, 16384⟩
    (by decide) selected_cut_13245

theorem selected_cut_13246 : selected 8 ⟨349500, by decide⟩
    (prefixPartial 13 106567) = some ⟨13, 2, 0, 349500, 106567, 889, 16384⟩ := by
  decide +kernel

theorem context_13_106567_349500 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106567 ⟨349500, by decide⟩ :=
  accepted_of_selected 13 106567 ⟨349500, by decide⟩ ⟨13, 2, 0, 349500, 106567, 889, 16384⟩
    (by decide) selected_cut_13246

theorem unmarked_context_12_26641_349501 : frontier 9 ⟨349501, by decide⟩
    (prefixCache 12 26641) (prefixPartial 12 26641) = false := by
  decide +kernel

theorem node_context_12_26641_349501 : EJMOriginalGlobalDAGData.nodes 9 ⟨349501, by decide⟩ =
    .split (coordinate 12) (![⟨349454, by decide⟩,⟨349477, by decide⟩,⟨349493, by decide⟩,⟨349500, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26641_349501 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26641 ⟨349501, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26641
    ⟨349501, by decide⟩ (by decide) (![⟨349454, by decide⟩,⟨349477, by decide⟩,⟨349493, by decide⟩,⟨349500, by decide⟩]) unmarked_context_12_26641_349501 node_context_12_26641_349501
  intro a
  fin_cases a
  · exact context_13_106564_349454
  · exact context_13_106565_349477
  · exact context_13_106566_349493
  · exact context_13_106567_349500

theorem selected_cut_13247 : selected 8 ⟨349520, by decide⟩
    (prefixPartial 13 106568) = some ⟨13, 2, 0, 349520, 106568, 1409, 16384⟩ := by
  decide +kernel

theorem context_13_106568_349520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106568 ⟨349520, by decide⟩ :=
  accepted_of_selected 13 106568 ⟨349520, by decide⟩ ⟨13, 2, 0, 349520, 106568, 1409, 16384⟩
    (by decide) selected_cut_13247

theorem selected_cut_13248 : selected 8 ⟨349547, by decide⟩
    (prefixPartial 13 106569) = some ⟨13, 2, 0, 349547, 106569, 1793, 16384⟩ := by
  decide +kernel

theorem context_13_106569_349547 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106569 ⟨349547, by decide⟩ :=
  accepted_of_selected 13 106569 ⟨349547, by decide⟩ ⟨13, 2, 0, 349547, 106569, 1793, 16384⟩
    (by decide) selected_cut_13248

theorem selected_cut_13249 : selected 8 ⟨349565, by decide⟩
    (prefixPartial 13 106570) = some ⟨13, 2, 0, 349565, 106570, 1269, 16384⟩ := by
  decide +kernel

theorem context_13_106570_349565 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106570 ⟨349565, by decide⟩ :=
  accepted_of_selected 13 106570 ⟨349565, by decide⟩ ⟨13, 2, 0, 349565, 106570, 1269, 16384⟩
    (by decide) selected_cut_13249

theorem selected_cut_13250 : selected 8 ⟨349573, by decide⟩
    (prefixPartial 13 106571) = some ⟨13, 2, 0, 349573, 106571, 977, 16384⟩ := by
  decide +kernel

theorem context_13_106571_349573 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 106571 ⟨349573, by decide⟩ :=
  accepted_of_selected 13 106571 ⟨349573, by decide⟩ ⟨13, 2, 0, 349573, 106571, 977, 16384⟩
    (by decide) selected_cut_13250

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
