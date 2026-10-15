/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover167
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_16131 : selected 8 ⟨410923, by decide⟩
    (prefixPartial 13 112650) = some ⟨13, 2, 0, 410923, 112650, 557, 16384⟩ := by
  decide +kernel

theorem context_13_112650_410923 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112650 ⟨410923, by decide⟩ :=
  accepted_of_selected 13 112650 ⟨410923, by decide⟩ ⟨13, 2, 0, 410923, 112650, 557, 16384⟩
    (by decide) selected_cut_16131

theorem selected_cut_16132 : selected 8 ⟨410932, by decide⟩
    (prefixPartial 13 112651) = some ⟨13, 2, 0, 410932, 112651, 153, 16384⟩ := by
  decide +kernel

theorem context_13_112651_410932 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112651 ⟨410932, by decide⟩ :=
  accepted_of_selected 13 112651 ⟨410932, by decide⟩ ⟨13, 2, 0, 410932, 112651, 153, 16384⟩
    (by decide) selected_cut_16132

theorem unmarked_context_12_28162_410933 : frontier 9 ⟨410933, by decide⟩
    (prefixCache 12 28162) (prefixPartial 12 28162) = false := by
  decide +kernel

theorem node_context_12_28162_410933 : EJMOriginalGlobalDAGData.nodes 9 ⟨410933, by decide⟩ =
    .split (coordinate 12) (![⟨410838, by decide⟩,⟨410903, by decide⟩,⟨410923, by decide⟩,⟨410932, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28162_410933 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28162 ⟨410933, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28162
    ⟨410933, by decide⟩ (by decide) (![⟨410838, by decide⟩,⟨410903, by decide⟩,⟨410923, by decide⟩,⟨410932, by decide⟩]) unmarked_context_12_28162_410933 node_context_12_28162_410933
  intro a
  fin_cases a
  · exact context_13_112648_410838
  · exact context_13_112649_410903
  · exact context_13_112650_410923
  · exact context_13_112651_410932

theorem selected_cut_16133 : selected 9 ⟨389061, by decide⟩
    (prefixPartial 12 28163) = some ⟨12, 1, 0, 389061, 28163, 1, 65536⟩ := by
  decide +kernel

theorem context_12_28163_389061 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28163 ⟨389061, by decide⟩ :=
  accepted_of_selected 12 28163 ⟨389061, by decide⟩ ⟨12, 1, 0, 389061, 28163, 1, 65536⟩
    (by decide) selected_cut_16133

theorem unmarked_context_11_7040_410934 : frontier 10 ⟨410934, by decide⟩
    (prefixCache 11 7040) (prefixPartial 11 7040) = false := by
  decide +kernel

theorem node_context_11_7040_410934 : EJMOriginalGlobalDAGData.nodes 10 ⟨410934, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨388829, by decide⟩,⟨410933, by decide⟩,⟨389061, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7040_410934 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7040 ⟨410934, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7040
    ⟨410934, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨388829, by decide⟩,⟨410933, by decide⟩,⟨389061, by decide⟩]) unmarked_context_11_7040_410934 node_context_11_7040_410934
  intro a
  fin_cases a
  · exact context_12_28160_34034
  · exact context_12_28161_388829
  · exact context_12_28162_410933
  · exact context_12_28163_389061

theorem selected_cut_16134 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 28164) = some ⟨12, 1, 0, 34034, 28164, 1, 65536⟩ := by
  decide +kernel

theorem context_12_28164_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28164 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 28164 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 28164, 1, 65536⟩
    (by decide) selected_cut_16134

theorem selected_cut_16135 : selected 8 ⟨411012, by decide⟩
    (prefixPartial 13 112660) = some ⟨13, 2, 0, 411012, 112660, 3945, 16384⟩ := by
  decide +kernel

theorem context_13_112660_411012 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112660 ⟨411012, by decide⟩ :=
  accepted_of_selected 13 112660 ⟨411012, by decide⟩ ⟨13, 2, 0, 411012, 112660, 3945, 16384⟩
    (by decide) selected_cut_16135

theorem selected_cut_16136 : selected 8 ⟨411078, by decide⟩
    (prefixPartial 13 112661) = some ⟨13, 2, 0, 411078, 112661, 3205, 16384⟩ := by
  decide +kernel

theorem context_13_112661_411078 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112661 ⟨411078, by decide⟩ :=
  accepted_of_selected 13 112661 ⟨411078, by decide⟩ ⟨13, 2, 0, 411078, 112661, 3205, 16384⟩
    (by decide) selected_cut_16136

theorem selected_cut_16137 : selected 8 ⟨411113, by decide⟩
    (prefixPartial 13 112662) = some ⟨13, 2, 0, 411113, 112662, 2089, 16384⟩ := by
  decide +kernel

theorem context_13_112662_411113 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112662 ⟨411113, by decide⟩ :=
  accepted_of_selected 13 112662 ⟨411113, by decide⟩ ⟨13, 2, 0, 411113, 112662, 2089, 16384⟩
    (by decide) selected_cut_16137

theorem selected_cut_16138 : selected 8 ⟨411130, by decide⟩
    (prefixPartial 13 112663) = some ⟨13, 2, 0, 411130, 112663, 1089, 16384⟩ := by
  decide +kernel

theorem context_13_112663_411130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112663 ⟨411130, by decide⟩ :=
  accepted_of_selected 13 112663 ⟨411130, by decide⟩ ⟨13, 2, 0, 411130, 112663, 1089, 16384⟩
    (by decide) selected_cut_16138

theorem unmarked_context_12_28165_411131 : frontier 9 ⟨411131, by decide⟩
    (prefixCache 12 28165) (prefixPartial 12 28165) = false := by
  decide +kernel

theorem node_context_12_28165_411131 : EJMOriginalGlobalDAGData.nodes 9 ⟨411131, by decide⟩ =
    .split (coordinate 12) (![⟨411012, by decide⟩,⟨411078, by decide⟩,⟨411113, by decide⟩,⟨411130, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28165_411131 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28165 ⟨411131, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28165
    ⟨411131, by decide⟩ (by decide) (![⟨411012, by decide⟩,⟨411078, by decide⟩,⟨411113, by decide⟩,⟨411130, by decide⟩]) unmarked_context_12_28165_411131 node_context_12_28165_411131
  intro a
  fin_cases a
  · exact context_13_112660_411012
  · exact context_13_112661_411078
  · exact context_13_112662_411113
  · exact context_13_112663_411130

theorem selected_cut_16139 : selected 8 ⟨411191, by decide⟩
    (prefixPartial 13 112664) = some ⟨13, 2, 0, 411191, 112664, 3381, 16384⟩ := by
  decide +kernel

theorem context_13_112664_411191 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112664 ⟨411191, by decide⟩ :=
  accepted_of_selected 13 112664 ⟨411191, by decide⟩ ⟨13, 2, 0, 411191, 112664, 3381, 16384⟩
    (by decide) selected_cut_16139

theorem selected_cut_16140 : selected 8 ⟨411242, by decide⟩
    (prefixPartial 13 112665) = some ⟨13, 2, 0, 411242, 112665, 3125, 16384⟩ := by
  decide +kernel

theorem context_13_112665_411242 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112665 ⟨411242, by decide⟩ :=
  accepted_of_selected 13 112665 ⟨411242, by decide⟩ ⟨13, 2, 0, 411242, 112665, 3125, 16384⟩
    (by decide) selected_cut_16140

theorem selected_cut_16141 : selected 8 ⟨411261, by decide⟩
    (prefixPartial 13 112666) = some ⟨13, 2, 0, 411261, 112666, 1817, 16384⟩ := by
  decide +kernel

theorem context_13_112666_411261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112666 ⟨411261, by decide⟩ :=
  accepted_of_selected 13 112666 ⟨411261, by decide⟩ ⟨13, 2, 0, 411261, 112666, 1817, 16384⟩
    (by decide) selected_cut_16141

theorem selected_cut_16142 : selected 8 ⟨411276, by decide⟩
    (prefixPartial 13 112667) = some ⟨13, 2, 0, 411276, 112667, 1105, 16384⟩ := by
  decide +kernel

theorem context_13_112667_411276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112667 ⟨411276, by decide⟩ :=
  accepted_of_selected 13 112667 ⟨411276, by decide⟩ ⟨13, 2, 0, 411276, 112667, 1105, 16384⟩
    (by decide) selected_cut_16142

theorem unmarked_context_12_28166_411277 : frontier 9 ⟨411277, by decide⟩
    (prefixCache 12 28166) (prefixPartial 12 28166) = false := by
  decide +kernel

theorem node_context_12_28166_411277 : EJMOriginalGlobalDAGData.nodes 9 ⟨411277, by decide⟩ =
    .split (coordinate 12) (![⟨411191, by decide⟩,⟨411242, by decide⟩,⟨411261, by decide⟩,⟨411276, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28166_411277 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28166 ⟨411277, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28166
    ⟨411277, by decide⟩ (by decide) (![⟨411191, by decide⟩,⟨411242, by decide⟩,⟨411261, by decide⟩,⟨411276, by decide⟩]) unmarked_context_12_28166_411277 node_context_12_28166_411277
  intro a
  fin_cases a
  · exact context_13_112664_411191
  · exact context_13_112665_411242
  · exact context_13_112666_411261
  · exact context_13_112667_411276

theorem selected_cut_16143 : selected 7 ⟨411309, by decide⟩
    (prefixPartial 14 450672) = some ⟨14, 2, 0, 411309, 450672, 1085, 4096⟩ := by
  decide +kernel

theorem context_14_450672_411309 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 450672 ⟨411309, by decide⟩ :=
  accepted_of_selected 14 450672 ⟨411309, by decide⟩ ⟨14, 2, 0, 411309, 450672, 1085, 4096⟩
    (by decide) selected_cut_16143

theorem selected_cut_16144 : selected 7 ⟨411333, by decide⟩
    (prefixPartial 14 450673) = some ⟨14, 2, 0, 411333, 450673, 1277, 4096⟩ := by
  decide +kernel

theorem context_14_450673_411333 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 450673 ⟨411333, by decide⟩ :=
  accepted_of_selected 14 450673 ⟨411333, by decide⟩ ⟨14, 2, 0, 411333, 450673, 1277, 4096⟩
    (by decide) selected_cut_16144

theorem selected_cut_16145 : selected 7 ⟨411349, by decide⟩
    (prefixPartial 14 450674) = some ⟨14, 2, 0, 411349, 450674, 969, 4096⟩ := by
  decide +kernel

theorem context_14_450674_411349 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 450674 ⟨411349, by decide⟩ :=
  accepted_of_selected 14 450674 ⟨411349, by decide⟩ ⟨14, 2, 0, 411349, 450674, 969, 4096⟩
    (by decide) selected_cut_16145

theorem selected_cut_16146 : selected 7 ⟨411368, by decide⟩
    (prefixPartial 14 450675) = some ⟨14, 2, 0, 411368, 450675, 1089, 4096⟩ := by
  decide +kernel

theorem context_14_450675_411368 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 450675 ⟨411368, by decide⟩ :=
  accepted_of_selected 14 450675 ⟨411368, by decide⟩ ⟨14, 2, 0, 411368, 450675, 1089, 4096⟩
    (by decide) selected_cut_16146

theorem unmarked_context_13_112668_411369 : frontier 8 ⟨411369, by decide⟩
    (prefixCache 13 112668) (prefixPartial 13 112668) = false := by
  decide +kernel

theorem node_context_13_112668_411369 : EJMOriginalGlobalDAGData.nodes 8 ⟨411369, by decide⟩ =
    .split (coordinate 13) (![⟨411309, by decide⟩,⟨411333, by decide⟩,⟨411349, by decide⟩,⟨411368, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_112668_411369 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112668 ⟨411369, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 112668
    ⟨411369, by decide⟩ (by decide) (![⟨411309, by decide⟩,⟨411333, by decide⟩,⟨411349, by decide⟩,⟨411368, by decide⟩]) unmarked_context_13_112668_411369 node_context_13_112668_411369
  intro a
  fin_cases a
  · exact context_14_450672_411309
  · exact context_14_450673_411333
  · exact context_14_450674_411349
  · exact context_14_450675_411368

theorem selected_cut_16147 : selected 8 ⟨411464, by decide⟩
    (prefixPartial 13 112669) = some ⟨13, 2, 0, 411464, 112669, 3877, 16384⟩ := by
  decide +kernel

theorem context_13_112669_411464 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112669 ⟨411464, by decide⟩ :=
  accepted_of_selected 13 112669 ⟨411464, by decide⟩ ⟨13, 2, 0, 411464, 112669, 3877, 16384⟩
    (by decide) selected_cut_16147

theorem selected_cut_16148 : selected 8 ⟨411502, by decide⟩
    (prefixPartial 13 112670) = some ⟨13, 2, 0, 411502, 112670, 2257, 16384⟩ := by
  decide +kernel

theorem context_13_112670_411502 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112670 ⟨411502, by decide⟩ :=
  accepted_of_selected 13 112670 ⟨411502, by decide⟩ ⟨13, 2, 0, 411502, 112670, 2257, 16384⟩
    (by decide) selected_cut_16148

theorem selected_cut_16149 : selected 8 ⟨411519, by decide⟩
    (prefixPartial 13 112671) = some ⟨13, 2, 0, 411519, 112671, 1245, 16384⟩ := by
  decide +kernel

theorem context_13_112671_411519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112671 ⟨411519, by decide⟩ :=
  accepted_of_selected 13 112671 ⟨411519, by decide⟩ ⟨13, 2, 0, 411519, 112671, 1245, 16384⟩
    (by decide) selected_cut_16149

theorem unmarked_context_12_28167_411520 : frontier 9 ⟨411520, by decide⟩
    (prefixCache 12 28167) (prefixPartial 12 28167) = false := by
  decide +kernel

theorem node_context_12_28167_411520 : EJMOriginalGlobalDAGData.nodes 9 ⟨411520, by decide⟩ =
    .split (coordinate 12) (![⟨411369, by decide⟩,⟨411464, by decide⟩,⟨411502, by decide⟩,⟨411519, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28167_411520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28167 ⟨411520, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28167
    ⟨411520, by decide⟩ (by decide) (![⟨411369, by decide⟩,⟨411464, by decide⟩,⟨411502, by decide⟩,⟨411519, by decide⟩]) unmarked_context_12_28167_411520 node_context_12_28167_411520
  intro a
  fin_cases a
  · exact context_13_112668_411369
  · exact context_13_112669_411464
  · exact context_13_112670_411502
  · exact context_13_112671_411519

theorem unmarked_context_11_7041_411521 : frontier 10 ⟨411521, by decide⟩
    (prefixCache 11 7041) (prefixPartial 11 7041) = false := by
  decide +kernel

theorem node_context_11_7041_411521 : EJMOriginalGlobalDAGData.nodes 10 ⟨411521, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨411131, by decide⟩,⟨411277, by decide⟩,⟨411520, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7041_411521 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7041 ⟨411521, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7041
    ⟨411521, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨411131, by decide⟩,⟨411277, by decide⟩,⟨411520, by decide⟩]) unmarked_context_11_7041_411521 node_context_11_7041_411521
  intro a
  fin_cases a
  · exact context_12_28164_34034
  · exact context_12_28165_411131
  · exact context_12_28166_411277
  · exact context_12_28167_411520

theorem selected_cut_16150 : selected 8 ⟨411570, by decide⟩
    (prefixPartial 13 112672) = some ⟨13, 2, 0, 411570, 112672, 2717, 16384⟩ := by
  decide +kernel

theorem context_13_112672_411570 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112672 ⟨411570, by decide⟩ :=
  accepted_of_selected 13 112672 ⟨411570, by decide⟩ ⟨13, 2, 0, 411570, 112672, 2717, 16384⟩
    (by decide) selected_cut_16150

theorem selected_cut_16151 : selected 8 ⟨411637, by decide⟩
    (prefixPartial 13 112673) = some ⟨13, 2, 0, 411637, 112673, 3429, 16384⟩ := by
  decide +kernel

theorem context_13_112673_411637 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112673 ⟨411637, by decide⟩ :=
  accepted_of_selected 13 112673 ⟨411637, by decide⟩ ⟨13, 2, 0, 411637, 112673, 3429, 16384⟩
    (by decide) selected_cut_16151

theorem selected_cut_16152 : selected 8 ⟨411662, by decide⟩
    (prefixPartial 13 112674) = some ⟨13, 2, 0, 411662, 112674, 1785, 16384⟩ := by
  decide +kernel

theorem context_13_112674_411662 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112674 ⟨411662, by decide⟩ :=
  accepted_of_selected 13 112674 ⟨411662, by decide⟩ ⟨13, 2, 0, 411662, 112674, 1785, 16384⟩
    (by decide) selected_cut_16152

theorem selected_cut_16153 : selected 8 ⟨411674, by decide⟩
    (prefixPartial 13 112675) = some ⟨13, 2, 0, 411674, 112675, 1013, 16384⟩ := by
  decide +kernel

theorem context_13_112675_411674 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112675 ⟨411674, by decide⟩ :=
  accepted_of_selected 13 112675 ⟨411674, by decide⟩ ⟨13, 2, 0, 411674, 112675, 1013, 16384⟩
    (by decide) selected_cut_16153

theorem unmarked_context_12_28168_411675 : frontier 9 ⟨411675, by decide⟩
    (prefixCache 12 28168) (prefixPartial 12 28168) = false := by
  decide +kernel

theorem node_context_12_28168_411675 : EJMOriginalGlobalDAGData.nodes 9 ⟨411675, by decide⟩ =
    .split (coordinate 12) (![⟨411570, by decide⟩,⟨411637, by decide⟩,⟨411662, by decide⟩,⟨411674, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28168_411675 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28168 ⟨411675, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28168
    ⟨411675, by decide⟩ (by decide) (![⟨411570, by decide⟩,⟨411637, by decide⟩,⟨411662, by decide⟩,⟨411674, by decide⟩]) unmarked_context_12_28168_411675 node_context_12_28168_411675
  intro a
  fin_cases a
  · exact context_13_112672_411570
  · exact context_13_112673_411637
  · exact context_13_112674_411662
  · exact context_13_112675_411674

theorem selected_cut_16154 : selected 8 ⟨411722, by decide⟩
    (prefixPartial 13 112676) = some ⟨13, 2, 0, 411722, 112676, 3117, 16384⟩ := by
  decide +kernel

theorem context_13_112676_411722 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112676 ⟨411722, by decide⟩ :=
  accepted_of_selected 13 112676 ⟨411722, by decide⟩ ⟨13, 2, 0, 411722, 112676, 3117, 16384⟩
    (by decide) selected_cut_16154

theorem selected_cut_16155 : selected 8 ⟨411776, by decide⟩
    (prefixPartial 13 112677) = some ⟨13, 2, 0, 411776, 112677, 3221, 16384⟩ := by
  decide +kernel

theorem context_13_112677_411776 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112677 ⟨411776, by decide⟩ :=
  accepted_of_selected 13 112677 ⟨411776, by decide⟩ ⟨13, 2, 0, 411776, 112677, 3221, 16384⟩
    (by decide) selected_cut_16155

theorem selected_cut_16156 : selected 8 ⟨411796, by decide⟩
    (prefixPartial 13 112678) = some ⟨13, 2, 0, 411796, 112678, 2081, 16384⟩ := by
  decide +kernel

theorem context_13_112678_411796 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112678 ⟨411796, by decide⟩ :=
  accepted_of_selected 13 112678 ⟨411796, by decide⟩ ⟨13, 2, 0, 411796, 112678, 2081, 16384⟩
    (by decide) selected_cut_16156

theorem selected_cut_16157 : selected 8 ⟨411807, by decide⟩
    (prefixPartial 13 112679) = some ⟨13, 2, 0, 411807, 112679, 1197, 16384⟩ := by
  decide +kernel

theorem context_13_112679_411807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112679 ⟨411807, by decide⟩ :=
  accepted_of_selected 13 112679 ⟨411807, by decide⟩ ⟨13, 2, 0, 411807, 112679, 1197, 16384⟩
    (by decide) selected_cut_16157

theorem unmarked_context_12_28169_411808 : frontier 9 ⟨411808, by decide⟩
    (prefixCache 12 28169) (prefixPartial 12 28169) = false := by
  decide +kernel

theorem node_context_12_28169_411808 : EJMOriginalGlobalDAGData.nodes 9 ⟨411808, by decide⟩ =
    .split (coordinate 12) (![⟨411722, by decide⟩,⟨411776, by decide⟩,⟨411796, by decide⟩,⟨411807, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28169_411808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28169 ⟨411808, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28169
    ⟨411808, by decide⟩ (by decide) (![⟨411722, by decide⟩,⟨411776, by decide⟩,⟨411796, by decide⟩,⟨411807, by decide⟩]) unmarked_context_12_28169_411808 node_context_12_28169_411808
  intro a
  fin_cases a
  · exact context_13_112676_411722
  · exact context_13_112677_411776
  · exact context_13_112678_411796
  · exact context_13_112679_411807

theorem selected_cut_16158 : selected 7 ⟨411826, by decide⟩
    (prefixPartial 14 450720) = some ⟨14, 2, 0, 411826, 450720, 989, 4096⟩ := by
  decide +kernel

theorem context_14_450720_411826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 450720 ⟨411826, by decide⟩ :=
  accepted_of_selected 14 450720 ⟨411826, by decide⟩ ⟨14, 2, 0, 411826, 450720, 989, 4096⟩
    (by decide) selected_cut_16158

theorem selected_cut_16159 : selected 7 ⟨411850, by decide⟩
    (prefixPartial 14 450721) = some ⟨14, 2, 0, 411850, 450721, 1385, 4096⟩ := by
  decide +kernel

theorem context_14_450721_411850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 450721 ⟨411850, by decide⟩ :=
  accepted_of_selected 14 450721 ⟨411850, by decide⟩ ⟨14, 2, 0, 411850, 450721, 1385, 4096⟩
    (by decide) selected_cut_16159

theorem selected_cut_16160 : selected 7 ⟨411881, by decide⟩
    (prefixPartial 14 450722) = some ⟨14, 2, 0, 411881, 450722, 1221, 4096⟩ := by
  decide +kernel

theorem context_14_450722_411881 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 450722 ⟨411881, by decide⟩ :=
  accepted_of_selected 14 450722 ⟨411881, by decide⟩ ⟨14, 2, 0, 411881, 450722, 1221, 4096⟩
    (by decide) selected_cut_16160

theorem selected_cut_16161 : selected 7 ⟨411907, by decide⟩
    (prefixPartial 14 450723) = some ⟨14, 2, 0, 411907, 450723, 1301, 4096⟩ := by
  decide +kernel

theorem context_14_450723_411907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 450723 ⟨411907, by decide⟩ :=
  accepted_of_selected 14 450723 ⟨411907, by decide⟩ ⟨14, 2, 0, 411907, 450723, 1301, 4096⟩
    (by decide) selected_cut_16161

theorem unmarked_context_13_112680_411908 : frontier 8 ⟨411908, by decide⟩
    (prefixCache 13 112680) (prefixPartial 13 112680) = false := by
  decide +kernel

theorem node_context_13_112680_411908 : EJMOriginalGlobalDAGData.nodes 8 ⟨411908, by decide⟩ =
    .split (coordinate 13) (![⟨411826, by decide⟩,⟨411850, by decide⟩,⟨411881, by decide⟩,⟨411907, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_112680_411908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112680 ⟨411908, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 112680
    ⟨411908, by decide⟩ (by decide) (![⟨411826, by decide⟩,⟨411850, by decide⟩,⟨411881, by decide⟩,⟨411907, by decide⟩]) unmarked_context_13_112680_411908 node_context_13_112680_411908
  intro a
  fin_cases a
  · exact context_14_450720_411826
  · exact context_14_450721_411850
  · exact context_14_450722_411881
  · exact context_14_450723_411907

theorem selected_cut_16162 : selected 7 ⟨411952, by decide⟩
    (prefixPartial 14 450724) = some ⟨14, 2, 0, 411952, 450724, 1533, 4096⟩ := by
  decide +kernel

theorem context_14_450724_411952 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 450724 ⟨411952, by decide⟩ :=
  accepted_of_selected 14 450724 ⟨411952, by decide⟩ ⟨14, 2, 0, 411952, 450724, 1533, 4096⟩
    (by decide) selected_cut_16162

theorem selected_cut_16163 : selected 7 ⟨411990, by decide⟩
    (prefixPartial 14 450725) = some ⟨14, 2, 0, 411990, 450725, 1281, 4096⟩ := by
  decide +kernel

theorem context_14_450725_411990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 450725 ⟨411990, by decide⟩ :=
  accepted_of_selected 14 450725 ⟨411990, by decide⟩ ⟨14, 2, 0, 411990, 450725, 1281, 4096⟩
    (by decide) selected_cut_16163

theorem selected_cut_16164 : selected 7 ⟨412022, by decide⟩
    (prefixPartial 14 450726) = some ⟨14, 2, 0, 412022, 450726, 1161, 4096⟩ := by
  decide +kernel

theorem context_14_450726_412022 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 450726 ⟨412022, by decide⟩ :=
  accepted_of_selected 14 450726 ⟨412022, by decide⟩ ⟨14, 2, 0, 412022, 450726, 1161, 4096⟩
    (by decide) selected_cut_16164

theorem selected_cut_16165 : selected 7 ⟨412066, by decide⟩
    (prefixPartial 14 450727) = some ⟨14, 2, 0, 412066, 450727, 1337, 4096⟩ := by
  decide +kernel

theorem context_14_450727_412066 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 450727 ⟨412066, by decide⟩ :=
  accepted_of_selected 14 450727 ⟨412066, by decide⟩ ⟨14, 2, 0, 412066, 450727, 1337, 4096⟩
    (by decide) selected_cut_16165

theorem unmarked_context_13_112681_412067 : frontier 8 ⟨412067, by decide⟩
    (prefixCache 13 112681) (prefixPartial 13 112681) = false := by
  decide +kernel

theorem node_context_13_112681_412067 : EJMOriginalGlobalDAGData.nodes 8 ⟨412067, by decide⟩ =
    .split (coordinate 13) (![⟨411952, by decide⟩,⟨411990, by decide⟩,⟨412022, by decide⟩,⟨412066, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_112681_412067 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112681 ⟨412067, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 112681
    ⟨412067, by decide⟩ (by decide) (![⟨411952, by decide⟩,⟨411990, by decide⟩,⟨412022, by decide⟩,⟨412066, by decide⟩]) unmarked_context_13_112681_412067 node_context_13_112681_412067
  intro a
  fin_cases a
  · exact context_14_450724_411952
  · exact context_14_450725_411990
  · exact context_14_450726_412022
  · exact context_14_450727_412066

theorem selected_cut_16166 : selected 8 ⟨412143, by decide⟩
    (prefixPartial 13 112682) = some ⟨13, 2, 0, 412143, 112682, 2889, 16384⟩ := by
  decide +kernel

theorem context_13_112682_412143 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112682 ⟨412143, by decide⟩ :=
  accepted_of_selected 13 112682 ⟨412143, by decide⟩ ⟨13, 2, 0, 412143, 112682, 2889, 16384⟩
    (by decide) selected_cut_16166

theorem selected_cut_16167 : selected 8 ⟨412185, by decide⟩
    (prefixPartial 13 112683) = some ⟨13, 2, 0, 412185, 112683, 1497, 16384⟩ := by
  decide +kernel

theorem context_13_112683_412185 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112683 ⟨412185, by decide⟩ :=
  accepted_of_selected 13 112683 ⟨412185, by decide⟩ ⟨13, 2, 0, 412185, 112683, 1497, 16384⟩
    (by decide) selected_cut_16167

theorem unmarked_context_12_28170_412186 : frontier 9 ⟨412186, by decide⟩
    (prefixCache 12 28170) (prefixPartial 12 28170) = false := by
  decide +kernel

theorem node_context_12_28170_412186 : EJMOriginalGlobalDAGData.nodes 9 ⟨412186, by decide⟩ =
    .split (coordinate 12) (![⟨411908, by decide⟩,⟨412067, by decide⟩,⟨412143, by decide⟩,⟨412185, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28170_412186 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28170 ⟨412186, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28170
    ⟨412186, by decide⟩ (by decide) (![⟨411908, by decide⟩,⟨412067, by decide⟩,⟨412143, by decide⟩,⟨412185, by decide⟩]) unmarked_context_12_28170_412186 node_context_12_28170_412186
  intro a
  fin_cases a
  · exact context_13_112680_411908
  · exact context_13_112681_412067
  · exact context_13_112682_412143
  · exact context_13_112683_412185

theorem selected_cut_16168 : selected 8 ⟨412242, by decide⟩
    (prefixPartial 13 112684) = some ⟨13, 2, 0, 412242, 112684, 3297, 16384⟩ := by
  decide +kernel

theorem context_13_112684_412242 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112684 ⟨412242, by decide⟩ :=
  accepted_of_selected 13 112684 ⟨412242, by decide⟩ ⟨13, 2, 0, 412242, 112684, 3297, 16384⟩
    (by decide) selected_cut_16168

theorem selected_cut_16169 : selected 8 ⟨412327, by decide⟩
    (prefixPartial 13 112685) = some ⟨13, 2, 0, 412327, 112685, 3985, 16384⟩ := by
  decide +kernel

theorem context_13_112685_412327 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112685 ⟨412327, by decide⟩ :=
  accepted_of_selected 13 112685 ⟨412327, by decide⟩ ⟨13, 2, 0, 412327, 112685, 3985, 16384⟩
    (by decide) selected_cut_16169

theorem selected_cut_16170 : selected 8 ⟨412349, by decide⟩
    (prefixPartial 13 112686) = some ⟨13, 2, 0, 412349, 112686, 2133, 16384⟩ := by
  decide +kernel

theorem context_13_112686_412349 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112686 ⟨412349, by decide⟩ :=
  accepted_of_selected 13 112686 ⟨412349, by decide⟩ ⟨13, 2, 0, 412349, 112686, 2133, 16384⟩
    (by decide) selected_cut_16170

theorem selected_cut_16171 : selected 8 ⟨412361, by decide⟩
    (prefixPartial 13 112687) = some ⟨13, 2, 0, 412361, 112687, 1217, 16384⟩ := by
  decide +kernel

theorem context_13_112687_412361 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112687 ⟨412361, by decide⟩ :=
  accepted_of_selected 13 112687 ⟨412361, by decide⟩ ⟨13, 2, 0, 412361, 112687, 1217, 16384⟩
    (by decide) selected_cut_16171

theorem unmarked_context_12_28171_412362 : frontier 9 ⟨412362, by decide⟩
    (prefixCache 12 28171) (prefixPartial 12 28171) = false := by
  decide +kernel

theorem node_context_12_28171_412362 : EJMOriginalGlobalDAGData.nodes 9 ⟨412362, by decide⟩ =
    .split (coordinate 12) (![⟨412242, by decide⟩,⟨412327, by decide⟩,⟨412349, by decide⟩,⟨412361, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28171_412362 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28171 ⟨412362, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28171
    ⟨412362, by decide⟩ (by decide) (![⟨412242, by decide⟩,⟨412327, by decide⟩,⟨412349, by decide⟩,⟨412361, by decide⟩]) unmarked_context_12_28171_412362 node_context_12_28171_412362
  intro a
  fin_cases a
  · exact context_13_112684_412242
  · exact context_13_112685_412327
  · exact context_13_112686_412349
  · exact context_13_112687_412361

theorem unmarked_context_11_7042_412363 : frontier 10 ⟨412363, by decide⟩
    (prefixCache 11 7042) (prefixPartial 11 7042) = false := by
  decide +kernel

theorem node_context_11_7042_412363 : EJMOriginalGlobalDAGData.nodes 10 ⟨412363, by decide⟩ =
    .split (coordinate 11) (![⟨411675, by decide⟩,⟨411808, by decide⟩,⟨412186, by decide⟩,⟨412362, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7042_412363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7042 ⟨412363, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7042
    ⟨412363, by decide⟩ (by decide) (![⟨411675, by decide⟩,⟨411808, by decide⟩,⟨412186, by decide⟩,⟨412362, by decide⟩]) unmarked_context_11_7042_412363 node_context_11_7042_412363
  intro a
  fin_cases a
  · exact context_12_28168_411675
  · exact context_12_28169_411808
  · exact context_12_28170_412186
  · exact context_12_28171_412362

theorem selected_cut_16172 : selected 9 ⟨390434, by decide⟩
    (prefixPartial 12 28172) = some ⟨12, 1, 0, 390434, 28172, 1, 65536⟩ := by
  decide +kernel

theorem context_12_28172_390434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28172 ⟨390434, by decide⟩ :=
  accepted_of_selected 12 28172 ⟨390434, by decide⟩ ⟨12, 1, 0, 390434, 28172, 1, 65536⟩
    (by decide) selected_cut_16172

theorem selected_cut_16173 : selected 8 ⟨412415, by decide⟩
    (prefixPartial 13 112692) = some ⟨13, 2, 0, 412415, 112692, 3233, 16384⟩ := by
  decide +kernel

theorem context_13_112692_412415 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112692 ⟨412415, by decide⟩ :=
  accepted_of_selected 13 112692 ⟨412415, by decide⟩ ⟨13, 2, 0, 412415, 112692, 3233, 16384⟩
    (by decide) selected_cut_16173

theorem selected_cut_16174 : selected 8 ⟨412480, by decide⟩
    (prefixPartial 13 112693) = some ⟨13, 2, 0, 412480, 112693, 3465, 16384⟩ := by
  decide +kernel

theorem context_13_112693_412480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112693 ⟨412480, by decide⟩ :=
  accepted_of_selected 13 112693 ⟨412480, by decide⟩ ⟨13, 2, 0, 412480, 112693, 3465, 16384⟩
    (by decide) selected_cut_16174

theorem selected_cut_16175 : selected 8 ⟨412512, by decide⟩
    (prefixPartial 13 112694) = some ⟨13, 2, 0, 412512, 112694, 2145, 16384⟩ := by
  decide +kernel

theorem context_13_112694_412512 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112694 ⟨412512, by decide⟩ :=
  accepted_of_selected 13 112694 ⟨412512, by decide⟩ ⟨13, 2, 0, 412512, 112694, 2145, 16384⟩
    (by decide) selected_cut_16175

theorem selected_cut_16176 : selected 8 ⟨412525, by decide⟩
    (prefixPartial 13 112695) = some ⟨13, 2, 0, 412525, 112695, 1149, 16384⟩ := by
  decide +kernel

theorem context_13_112695_412525 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112695 ⟨412525, by decide⟩ :=
  accepted_of_selected 13 112695 ⟨412525, by decide⟩ ⟨13, 2, 0, 412525, 112695, 1149, 16384⟩
    (by decide) selected_cut_16176

theorem unmarked_context_12_28173_412526 : frontier 9 ⟨412526, by decide⟩
    (prefixCache 12 28173) (prefixPartial 12 28173) = false := by
  decide +kernel

theorem node_context_12_28173_412526 : EJMOriginalGlobalDAGData.nodes 9 ⟨412526, by decide⟩ =
    .split (coordinate 12) (![⟨412415, by decide⟩,⟨412480, by decide⟩,⟨412512, by decide⟩,⟨412525, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28173_412526 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28173 ⟨412526, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28173
    ⟨412526, by decide⟩ (by decide) (![⟨412415, by decide⟩,⟨412480, by decide⟩,⟨412512, by decide⟩,⟨412525, by decide⟩]) unmarked_context_12_28173_412526 node_context_12_28173_412526
  intro a
  fin_cases a
  · exact context_13_112692_412415
  · exact context_13_112693_412480
  · exact context_13_112694_412512
  · exact context_13_112695_412525

theorem selected_cut_16177 : selected 8 ⟨412564, by decide⟩
    (prefixPartial 13 112696) = some ⟨13, 2, 0, 412564, 112696, 2773, 16384⟩ := by
  decide +kernel

theorem context_13_112696_412564 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112696 ⟨412564, by decide⟩ :=
  accepted_of_selected 13 112696 ⟨412564, by decide⟩ ⟨13, 2, 0, 412564, 112696, 2773, 16384⟩
    (by decide) selected_cut_16177

theorem selected_cut_16178 : selected 8 ⟨412630, by decide⟩
    (prefixPartial 13 112697) = some ⟨13, 2, 0, 412630, 112697, 3281, 16384⟩ := by
  decide +kernel

theorem context_13_112697_412630 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112697 ⟨412630, by decide⟩ :=
  accepted_of_selected 13 112697 ⟨412630, by decide⟩ ⟨13, 2, 0, 412630, 112697, 3281, 16384⟩
    (by decide) selected_cut_16178

theorem selected_cut_16179 : selected 8 ⟨412650, by decide⟩
    (prefixPartial 13 112698) = some ⟨13, 2, 0, 412650, 112698, 1869, 16384⟩ := by
  decide +kernel

theorem context_13_112698_412650 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112698 ⟨412650, by decide⟩ :=
  accepted_of_selected 13 112698 ⟨412650, by decide⟩ ⟨13, 2, 0, 412650, 112698, 1869, 16384⟩
    (by decide) selected_cut_16179

theorem selected_cut_16180 : selected 8 ⟨412658, by decide⟩
    (prefixPartial 13 112699) = some ⟨13, 2, 0, 412658, 112699, 1129, 16384⟩ := by
  decide +kernel

theorem context_13_112699_412658 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112699 ⟨412658, by decide⟩ :=
  accepted_of_selected 13 112699 ⟨412658, by decide⟩ ⟨13, 2, 0, 412658, 112699, 1129, 16384⟩
    (by decide) selected_cut_16180

theorem unmarked_context_12_28174_412659 : frontier 9 ⟨412659, by decide⟩
    (prefixCache 12 28174) (prefixPartial 12 28174) = false := by
  decide +kernel

theorem node_context_12_28174_412659 : EJMOriginalGlobalDAGData.nodes 9 ⟨412659, by decide⟩ =
    .split (coordinate 12) (![⟨412564, by decide⟩,⟨412630, by decide⟩,⟨412650, by decide⟩,⟨412658, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28174_412659 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28174 ⟨412659, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28174
    ⟨412659, by decide⟩ (by decide) (![⟨412564, by decide⟩,⟨412630, by decide⟩,⟨412650, by decide⟩,⟨412658, by decide⟩]) unmarked_context_12_28174_412659 node_context_12_28174_412659
  intro a
  fin_cases a
  · exact context_13_112696_412564
  · exact context_13_112697_412630
  · exact context_13_112698_412650
  · exact context_13_112699_412658

theorem selected_cut_16181 : selected 8 ⟨412706, by decide⟩
    (prefixPartial 13 112700) = some ⟨13, 2, 0, 412706, 112700, 3297, 16384⟩ := by
  decide +kernel

theorem context_13_112700_412706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112700 ⟨412706, by decide⟩ :=
  accepted_of_selected 13 112700 ⟨412706, by decide⟩ ⟨13, 2, 0, 412706, 112700, 3297, 16384⟩
    (by decide) selected_cut_16181

theorem selected_cut_16182 : selected 8 ⟨412783, by decide⟩
    (prefixPartial 13 112701) = some ⟨13, 2, 0, 412783, 112701, 3733, 16384⟩ := by
  decide +kernel

theorem context_13_112701_412783 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112701 ⟨412783, by decide⟩ :=
  accepted_of_selected 13 112701 ⟨412783, by decide⟩ ⟨13, 2, 0, 412783, 112701, 3733, 16384⟩
    (by decide) selected_cut_16182

theorem selected_cut_16183 : selected 8 ⟨412809, by decide⟩
    (prefixPartial 13 112702) = some ⟨13, 2, 0, 412809, 112702, 2273, 16384⟩ := by
  decide +kernel

theorem context_13_112702_412809 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112702 ⟨412809, by decide⟩ :=
  accepted_of_selected 13 112702 ⟨412809, by decide⟩ ⟨13, 2, 0, 412809, 112702, 2273, 16384⟩
    (by decide) selected_cut_16183

theorem selected_cut_16184 : selected 8 ⟨412818, by decide⟩
    (prefixPartial 13 112703) = some ⟨13, 2, 0, 412818, 112703, 1205, 16384⟩ := by
  decide +kernel

theorem context_13_112703_412818 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112703 ⟨412818, by decide⟩ :=
  accepted_of_selected 13 112703 ⟨412818, by decide⟩ ⟨13, 2, 0, 412818, 112703, 1205, 16384⟩
    (by decide) selected_cut_16184

theorem unmarked_context_12_28175_412819 : frontier 9 ⟨412819, by decide⟩
    (prefixCache 12 28175) (prefixPartial 12 28175) = false := by
  decide +kernel

theorem node_context_12_28175_412819 : EJMOriginalGlobalDAGData.nodes 9 ⟨412819, by decide⟩ =
    .split (coordinate 12) (![⟨412706, by decide⟩,⟨412783, by decide⟩,⟨412809, by decide⟩,⟨412818, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28175_412819 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28175 ⟨412819, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28175
    ⟨412819, by decide⟩ (by decide) (![⟨412706, by decide⟩,⟨412783, by decide⟩,⟨412809, by decide⟩,⟨412818, by decide⟩]) unmarked_context_12_28175_412819 node_context_12_28175_412819
  intro a
  fin_cases a
  · exact context_13_112700_412706
  · exact context_13_112701_412783
  · exact context_13_112702_412809
  · exact context_13_112703_412818

theorem unmarked_context_11_7043_412820 : frontier 10 ⟨412820, by decide⟩
    (prefixCache 11 7043) (prefixPartial 11 7043) = false := by
  decide +kernel

theorem node_context_11_7043_412820 : EJMOriginalGlobalDAGData.nodes 10 ⟨412820, by decide⟩ =
    .split (coordinate 11) (![⟨390434, by decide⟩,⟨412526, by decide⟩,⟨412659, by decide⟩,⟨412819, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7043_412820 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7043 ⟨412820, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7043
    ⟨412820, by decide⟩ (by decide) (![⟨390434, by decide⟩,⟨412526, by decide⟩,⟨412659, by decide⟩,⟨412819, by decide⟩]) unmarked_context_11_7043_412820 node_context_11_7043_412820
  intro a
  fin_cases a
  · exact context_12_28172_390434
  · exact context_12_28173_412526
  · exact context_12_28174_412659
  · exact context_12_28175_412819

theorem unmarked_context_10_1760_412821 : frontier 11 ⟨412821, by decide⟩
    (prefixCache 10 1760) (prefixPartial 10 1760) = false := by
  decide +kernel

theorem node_context_10_1760_412821 : EJMOriginalGlobalDAGData.nodes 11 ⟨412821, by decide⟩ =
    .split (coordinate 10) (![⟨410934, by decide⟩,⟨411521, by decide⟩,⟨412363, by decide⟩,⟨412820, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1760_412821 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1760 ⟨412821, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1760
    ⟨412821, by decide⟩ (by decide) (![⟨410934, by decide⟩,⟨411521, by decide⟩,⟨412363, by decide⟩,⟨412820, by decide⟩]) unmarked_context_10_1760_412821 node_context_10_1760_412821
  intro a
  fin_cases a
  · exact context_11_7040_410934
  · exact context_11_7041_411521
  · exact context_11_7042_412363
  · exact context_11_7043_412820

theorem selected_cut_16185 : selected 8 ⟨412845, by decide⟩
    (prefixPartial 13 112704) = some ⟨13, 2, 0, 412845, 112704, 2009, 16384⟩ := by
  decide +kernel

theorem context_13_112704_412845 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112704 ⟨412845, by decide⟩ :=
  accepted_of_selected 13 112704 ⟨412845, by decide⟩ ⟨13, 2, 0, 412845, 112704, 2009, 16384⟩
    (by decide) selected_cut_16185

theorem selected_cut_16186 : selected 8 ⟨412872, by decide⟩
    (prefixPartial 13 112705) = some ⟨13, 2, 0, 412872, 112705, 2105, 16384⟩ := by
  decide +kernel

theorem context_13_112705_412872 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112705 ⟨412872, by decide⟩ :=
  accepted_of_selected 13 112705 ⟨412872, by decide⟩ ⟨13, 2, 0, 412872, 112705, 2105, 16384⟩
    (by decide) selected_cut_16186

theorem selected_cut_16187 : selected 8 ⟨412890, by decide⟩
    (prefixPartial 13 112706) = some ⟨13, 2, 0, 412890, 112706, 1269, 16384⟩ := by
  decide +kernel

theorem context_13_112706_412890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112706 ⟨412890, by decide⟩ :=
  accepted_of_selected 13 112706 ⟨412890, by decide⟩ ⟨13, 2, 0, 412890, 112706, 1269, 16384⟩
    (by decide) selected_cut_16187

theorem selected_cut_16188 : selected 8 ⟨412902, by decide⟩
    (prefixPartial 13 112707) = some ⟨13, 2, 0, 412902, 112707, 789, 16384⟩ := by
  decide +kernel

theorem context_13_112707_412902 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112707 ⟨412902, by decide⟩ :=
  accepted_of_selected 13 112707 ⟨412902, by decide⟩ ⟨13, 2, 0, 412902, 112707, 789, 16384⟩
    (by decide) selected_cut_16188

theorem unmarked_context_12_28176_412903 : frontier 9 ⟨412903, by decide⟩
    (prefixCache 12 28176) (prefixPartial 12 28176) = false := by
  decide +kernel

theorem node_context_12_28176_412903 : EJMOriginalGlobalDAGData.nodes 9 ⟨412903, by decide⟩ =
    .split (coordinate 12) (![⟨412845, by decide⟩,⟨412872, by decide⟩,⟨412890, by decide⟩,⟨412902, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28176_412903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28176 ⟨412903, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28176
    ⟨412903, by decide⟩ (by decide) (![⟨412845, by decide⟩,⟨412872, by decide⟩,⟨412890, by decide⟩,⟨412902, by decide⟩]) unmarked_context_12_28176_412903 node_context_12_28176_412903
  intro a
  fin_cases a
  · exact context_13_112704_412845
  · exact context_13_112705_412872
  · exact context_13_112706_412890
  · exact context_13_112707_412902

theorem selected_cut_16189 : selected 8 ⟨412935, by decide⟩
    (prefixPartial 13 112708) = some ⟨13, 2, 0, 412935, 112708, 2413, 16384⟩ := by
  decide +kernel

theorem context_13_112708_412935 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112708 ⟨412935, by decide⟩ :=
  accepted_of_selected 13 112708 ⟨412935, by decide⟩ ⟨13, 2, 0, 412935, 112708, 2413, 16384⟩
    (by decide) selected_cut_16189

theorem selected_cut_16190 : selected 8 ⟨412963, by decide⟩
    (prefixPartial 13 112709) = some ⟨13, 2, 0, 412963, 112709, 2233, 16384⟩ := by
  decide +kernel

theorem context_13_112709_412963 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112709 ⟨412963, by decide⟩ :=
  accepted_of_selected 13 112709 ⟨412963, by decide⟩ ⟨13, 2, 0, 412963, 112709, 2233, 16384⟩
    (by decide) selected_cut_16190

theorem selected_cut_16191 : selected 8 ⟨412984, by decide⟩
    (prefixPartial 13 112710) = some ⟨13, 2, 0, 412984, 112710, 1553, 16384⟩ := by
  decide +kernel

theorem context_13_112710_412984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112710 ⟨412984, by decide⟩ :=
  accepted_of_selected 13 112710 ⟨412984, by decide⟩ ⟨13, 2, 0, 412984, 112710, 1553, 16384⟩
    (by decide) selected_cut_16191

theorem selected_cut_16192 : selected 8 ⟨412998, by decide⟩
    (prefixPartial 13 112711) = some ⟨13, 2, 0, 412998, 112711, 1049, 16384⟩ := by
  decide +kernel

theorem context_13_112711_412998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112711 ⟨412998, by decide⟩ :=
  accepted_of_selected 13 112711 ⟨412998, by decide⟩ ⟨13, 2, 0, 412998, 112711, 1049, 16384⟩
    (by decide) selected_cut_16192

theorem unmarked_context_12_28177_412999 : frontier 9 ⟨412999, by decide⟩
    (prefixCache 12 28177) (prefixPartial 12 28177) = false := by
  decide +kernel

theorem node_context_12_28177_412999 : EJMOriginalGlobalDAGData.nodes 9 ⟨412999, by decide⟩ =
    .split (coordinate 12) (![⟨412935, by decide⟩,⟨412963, by decide⟩,⟨412984, by decide⟩,⟨412998, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28177_412999 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28177 ⟨412999, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28177
    ⟨412999, by decide⟩ (by decide) (![⟨412935, by decide⟩,⟨412963, by decide⟩,⟨412984, by decide⟩,⟨412998, by decide⟩]) unmarked_context_12_28177_412999 node_context_12_28177_412999
  intro a
  fin_cases a
  · exact context_13_112708_412935
  · exact context_13_112709_412963
  · exact context_13_112710_412984
  · exact context_13_112711_412998

theorem selected_cut_16193 : selected 8 ⟨413024, by decide⟩
    (prefixPartial 13 112712) = some ⟨13, 2, 0, 413024, 112712, 2229, 16384⟩ := by
  decide +kernel

theorem context_13_112712_413024 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112712 ⟨413024, by decide⟩ :=
  accepted_of_selected 13 112712 ⟨413024, by decide⟩ ⟨13, 2, 0, 413024, 112712, 2229, 16384⟩
    (by decide) selected_cut_16193

theorem selected_cut_16194 : selected 8 ⟨413050, by decide⟩
    (prefixPartial 13 112713) = some ⟨13, 2, 0, 413050, 112713, 2273, 16384⟩ := by
  decide +kernel

theorem context_13_112713_413050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112713 ⟨413050, by decide⟩ :=
  accepted_of_selected 13 112713 ⟨413050, by decide⟩ ⟨13, 2, 0, 413050, 112713, 2273, 16384⟩
    (by decide) selected_cut_16194

theorem selected_cut_16195 : selected 8 ⟨413069, by decide⟩
    (prefixPartial 13 112714) = some ⟨13, 2, 0, 413069, 112714, 1401, 16384⟩ := by
  decide +kernel

theorem context_13_112714_413069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112714 ⟨413069, by decide⟩ :=
  accepted_of_selected 13 112714 ⟨413069, by decide⟩ ⟨13, 2, 0, 413069, 112714, 1401, 16384⟩
    (by decide) selected_cut_16195

theorem selected_cut_16196 : selected 8 ⟨413085, by decide⟩
    (prefixPartial 13 112715) = some ⟨13, 2, 0, 413085, 112715, 977, 16384⟩ := by
  decide +kernel

theorem context_13_112715_413085 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112715 ⟨413085, by decide⟩ :=
  accepted_of_selected 13 112715 ⟨413085, by decide⟩ ⟨13, 2, 0, 413085, 112715, 977, 16384⟩
    (by decide) selected_cut_16196

theorem unmarked_context_12_28178_413086 : frontier 9 ⟨413086, by decide⟩
    (prefixCache 12 28178) (prefixPartial 12 28178) = false := by
  decide +kernel

theorem node_context_12_28178_413086 : EJMOriginalGlobalDAGData.nodes 9 ⟨413086, by decide⟩ =
    .split (coordinate 12) (![⟨413024, by decide⟩,⟨413050, by decide⟩,⟨413069, by decide⟩,⟨413085, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28178_413086 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28178 ⟨413086, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28178
    ⟨413086, by decide⟩ (by decide) (![⟨413024, by decide⟩,⟨413050, by decide⟩,⟨413069, by decide⟩,⟨413085, by decide⟩]) unmarked_context_12_28178_413086 node_context_12_28178_413086
  intro a
  fin_cases a
  · exact context_13_112712_413024
  · exact context_13_112713_413050
  · exact context_13_112714_413069
  · exact context_13_112715_413085

theorem selected_cut_16197 : selected 8 ⟨413116, by decide⟩
    (prefixPartial 13 112716) = some ⟨13, 2, 0, 413116, 112716, 2529, 16384⟩ := by
  decide +kernel

theorem context_13_112716_413116 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112716 ⟨413116, by decide⟩ :=
  accepted_of_selected 13 112716 ⟨413116, by decide⟩ ⟨13, 2, 0, 413116, 112716, 2529, 16384⟩
    (by decide) selected_cut_16197

theorem selected_cut_16198 : selected 8 ⟨413160, by decide⟩
    (prefixPartial 13 112717) = some ⟨13, 2, 0, 413160, 112717, 2773, 16384⟩ := by
  decide +kernel

theorem context_13_112717_413160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112717 ⟨413160, by decide⟩ :=
  accepted_of_selected 13 112717 ⟨413160, by decide⟩ ⟨13, 2, 0, 413160, 112717, 2773, 16384⟩
    (by decide) selected_cut_16198

theorem selected_cut_16199 : selected 8 ⟨413187, by decide⟩
    (prefixPartial 13 112718) = some ⟨13, 2, 0, 413187, 112718, 1929, 16384⟩ := by
  decide +kernel

theorem context_13_112718_413187 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112718 ⟨413187, by decide⟩ :=
  accepted_of_selected 13 112718 ⟨413187, by decide⟩ ⟨13, 2, 0, 413187, 112718, 1929, 16384⟩
    (by decide) selected_cut_16199

theorem selected_cut_16200 : selected 8 ⟨413207, by decide⟩
    (prefixPartial 13 112719) = some ⟨13, 2, 0, 413207, 112719, 1133, 16384⟩ := by
  decide +kernel

theorem context_13_112719_413207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112719 ⟨413207, by decide⟩ :=
  accepted_of_selected 13 112719 ⟨413207, by decide⟩ ⟨13, 2, 0, 413207, 112719, 1133, 16384⟩
    (by decide) selected_cut_16200

theorem unmarked_context_12_28179_413208 : frontier 9 ⟨413208, by decide⟩
    (prefixCache 12 28179) (prefixPartial 12 28179) = false := by
  decide +kernel

theorem node_context_12_28179_413208 : EJMOriginalGlobalDAGData.nodes 9 ⟨413208, by decide⟩ =
    .split (coordinate 12) (![⟨413116, by decide⟩,⟨413160, by decide⟩,⟨413187, by decide⟩,⟨413207, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28179_413208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28179 ⟨413208, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28179
    ⟨413208, by decide⟩ (by decide) (![⟨413116, by decide⟩,⟨413160, by decide⟩,⟨413187, by decide⟩,⟨413207, by decide⟩]) unmarked_context_12_28179_413208 node_context_12_28179_413208
  intro a
  fin_cases a
  · exact context_13_112716_413116
  · exact context_13_112717_413160
  · exact context_13_112718_413187
  · exact context_13_112719_413207

theorem unmarked_context_11_7044_413209 : frontier 10 ⟨413209, by decide⟩
    (prefixCache 11 7044) (prefixPartial 11 7044) = false := by
  decide +kernel

theorem node_context_11_7044_413209 : EJMOriginalGlobalDAGData.nodes 10 ⟨413209, by decide⟩ =
    .split (coordinate 11) (![⟨412903, by decide⟩,⟨412999, by decide⟩,⟨413086, by decide⟩,⟨413208, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7044_413209 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7044 ⟨413209, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7044
    ⟨413209, by decide⟩ (by decide) (![⟨412903, by decide⟩,⟨412999, by decide⟩,⟨413086, by decide⟩,⟨413208, by decide⟩]) unmarked_context_11_7044_413209 node_context_11_7044_413209
  intro a
  fin_cases a
  · exact context_12_28176_412903
  · exact context_12_28177_412999
  · exact context_12_28178_413086
  · exact context_12_28179_413208

theorem selected_cut_16201 : selected 8 ⟨413229, by decide⟩
    (prefixPartial 13 112720) = some ⟨13, 2, 0, 413229, 112720, 1873, 16384⟩ := by
  decide +kernel

theorem context_13_112720_413229 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112720 ⟨413229, by decide⟩ :=
  accepted_of_selected 13 112720 ⟨413229, by decide⟩ ⟨13, 2, 0, 413229, 112720, 1873, 16384⟩
    (by decide) selected_cut_16201

theorem selected_cut_16202 : selected 8 ⟨413261, by decide⟩
    (prefixPartial 13 112721) = some ⟨13, 2, 0, 413261, 112721, 2349, 16384⟩ := by
  decide +kernel

theorem context_13_112721_413261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112721 ⟨413261, by decide⟩ :=
  accepted_of_selected 13 112721 ⟨413261, by decide⟩ ⟨13, 2, 0, 413261, 112721, 2349, 16384⟩
    (by decide) selected_cut_16202

theorem selected_cut_16203 : selected 8 ⟨413277, by decide⟩
    (prefixPartial 13 112722) = some ⟨13, 2, 0, 413277, 112722, 1333, 16384⟩ := by
  decide +kernel

theorem context_13_112722_413277 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112722 ⟨413277, by decide⟩ :=
  accepted_of_selected 13 112722 ⟨413277, by decide⟩ ⟨13, 2, 0, 413277, 112722, 1333, 16384⟩
    (by decide) selected_cut_16203

theorem selected_cut_16204 : selected 8 ⟨413285, by decide⟩
    (prefixPartial 13 112723) = some ⟨13, 2, 0, 413285, 112723, 777, 16384⟩ := by
  decide +kernel

theorem context_13_112723_413285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112723 ⟨413285, by decide⟩ :=
  accepted_of_selected 13 112723 ⟨413285, by decide⟩ ⟨13, 2, 0, 413285, 112723, 777, 16384⟩
    (by decide) selected_cut_16204

theorem unmarked_context_12_28180_413286 : frontier 9 ⟨413286, by decide⟩
    (prefixCache 12 28180) (prefixPartial 12 28180) = false := by
  decide +kernel

theorem node_context_12_28180_413286 : EJMOriginalGlobalDAGData.nodes 9 ⟨413286, by decide⟩ =
    .split (coordinate 12) (![⟨413229, by decide⟩,⟨413261, by decide⟩,⟨413277, by decide⟩,⟨413285, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28180_413286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28180 ⟨413286, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28180
    ⟨413286, by decide⟩ (by decide) (![⟨413229, by decide⟩,⟨413261, by decide⟩,⟨413277, by decide⟩,⟨413285, by decide⟩]) unmarked_context_12_28180_413286 node_context_12_28180_413286
  intro a
  fin_cases a
  · exact context_13_112720_413229
  · exact context_13_112721_413261
  · exact context_13_112722_413277
  · exact context_13_112723_413285

theorem selected_cut_16205 : selected 8 ⟨413314, by decide⟩
    (prefixPartial 13 112724) = some ⟨13, 2, 0, 413314, 112724, 2225, 16384⟩ := by
  decide +kernel

theorem context_13_112724_413314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112724 ⟨413314, by decide⟩ :=
  accepted_of_selected 13 112724 ⟨413314, by decide⟩ ⟨13, 2, 0, 413314, 112724, 2225, 16384⟩
    (by decide) selected_cut_16205

theorem selected_cut_16206 : selected 8 ⟨413346, by decide⟩
    (prefixPartial 13 112725) = some ⟨13, 2, 0, 413346, 112725, 1997, 16384⟩ := by
  decide +kernel

theorem context_13_112725_413346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112725 ⟨413346, by decide⟩ :=
  accepted_of_selected 13 112725 ⟨413346, by decide⟩ ⟨13, 2, 0, 413346, 112725, 1997, 16384⟩
    (by decide) selected_cut_16206

theorem selected_cut_16207 : selected 8 ⟨413361, by decide⟩
    (prefixPartial 13 112726) = some ⟨13, 2, 0, 413361, 112726, 1597, 16384⟩ := by
  decide +kernel

theorem context_13_112726_413361 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112726 ⟨413361, by decide⟩ :=
  accepted_of_selected 13 112726 ⟨413361, by decide⟩ ⟨13, 2, 0, 413361, 112726, 1597, 16384⟩
    (by decide) selected_cut_16207

theorem selected_cut_16208 : selected 8 ⟨413369, by decide⟩
    (prefixPartial 13 112727) = some ⟨13, 2, 0, 413369, 112727, 929, 16384⟩ := by
  decide +kernel

theorem context_13_112727_413369 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112727 ⟨413369, by decide⟩ :=
  accepted_of_selected 13 112727 ⟨413369, by decide⟩ ⟨13, 2, 0, 413369, 112727, 929, 16384⟩
    (by decide) selected_cut_16208

theorem unmarked_context_12_28181_413370 : frontier 9 ⟨413370, by decide⟩
    (prefixCache 12 28181) (prefixPartial 12 28181) = false := by
  decide +kernel

theorem node_context_12_28181_413370 : EJMOriginalGlobalDAGData.nodes 9 ⟨413370, by decide⟩ =
    .split (coordinate 12) (![⟨413314, by decide⟩,⟨413346, by decide⟩,⟨413361, by decide⟩,⟨413369, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28181_413370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28181 ⟨413370, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28181
    ⟨413370, by decide⟩ (by decide) (![⟨413314, by decide⟩,⟨413346, by decide⟩,⟨413361, by decide⟩,⟨413369, by decide⟩]) unmarked_context_12_28181_413370 node_context_12_28181_413370
  intro a
  fin_cases a
  · exact context_13_112724_413314
  · exact context_13_112725_413346
  · exact context_13_112726_413361
  · exact context_13_112727_413369

theorem selected_cut_16209 : selected 8 ⟨413397, by decide⟩
    (prefixPartial 13 112728) = some ⟨13, 2, 0, 413397, 112728, 2057, 16384⟩ := by
  decide +kernel

theorem context_13_112728_413397 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112728 ⟨413397, by decide⟩ :=
  accepted_of_selected 13 112728 ⟨413397, by decide⟩ ⟨13, 2, 0, 413397, 112728, 2057, 16384⟩
    (by decide) selected_cut_16209

theorem selected_cut_16210 : selected 8 ⟨413419, by decide⟩
    (prefixPartial 13 112729) = some ⟨13, 2, 0, 413419, 112729, 2141, 16384⟩ := by
  decide +kernel

theorem context_13_112729_413419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112729 ⟨413419, by decide⟩ :=
  accepted_of_selected 13 112729 ⟨413419, by decide⟩ ⟨13, 2, 0, 413419, 112729, 2141, 16384⟩
    (by decide) selected_cut_16210

theorem selected_cut_16211 : selected 8 ⟨413437, by decide⟩
    (prefixPartial 13 112730) = some ⟨13, 2, 0, 413437, 112730, 1461, 16384⟩ := by
  decide +kernel

theorem context_13_112730_413437 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112730 ⟨413437, by decide⟩ :=
  accepted_of_selected 13 112730 ⟨413437, by decide⟩ ⟨13, 2, 0, 413437, 112730, 1461, 16384⟩
    (by decide) selected_cut_16211

theorem selected_cut_16212 : selected 8 ⟨413446, by decide⟩
    (prefixPartial 13 112731) = some ⟨13, 2, 0, 413446, 112731, 933, 16384⟩ := by
  decide +kernel

theorem context_13_112731_413446 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112731 ⟨413446, by decide⟩ :=
  accepted_of_selected 13 112731 ⟨413446, by decide⟩ ⟨13, 2, 0, 413446, 112731, 933, 16384⟩
    (by decide) selected_cut_16212

theorem unmarked_context_12_28182_413447 : frontier 9 ⟨413447, by decide⟩
    (prefixCache 12 28182) (prefixPartial 12 28182) = false := by
  decide +kernel

theorem node_context_12_28182_413447 : EJMOriginalGlobalDAGData.nodes 9 ⟨413447, by decide⟩ =
    .split (coordinate 12) (![⟨413397, by decide⟩,⟨413419, by decide⟩,⟨413437, by decide⟩,⟨413446, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28182_413447 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28182 ⟨413447, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28182
    ⟨413447, by decide⟩ (by decide) (![⟨413397, by decide⟩,⟨413419, by decide⟩,⟨413437, by decide⟩,⟨413446, by decide⟩]) unmarked_context_12_28182_413447 node_context_12_28182_413447
  intro a
  fin_cases a
  · exact context_13_112728_413397
  · exact context_13_112729_413419
  · exact context_13_112730_413437
  · exact context_13_112731_413446

theorem selected_cut_16213 : selected 8 ⟨413480, by decide⟩
    (prefixPartial 13 112732) = some ⟨13, 2, 0, 413480, 112732, 2417, 16384⟩ := by
  decide +kernel

theorem context_13_112732_413480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112732 ⟨413480, by decide⟩ :=
  accepted_of_selected 13 112732 ⟨413480, by decide⟩ ⟨13, 2, 0, 413480, 112732, 2417, 16384⟩
    (by decide) selected_cut_16213

theorem selected_cut_16214 : selected 8 ⟨413512, by decide⟩
    (prefixPartial 13 112733) = some ⟨13, 2, 0, 413512, 112733, 2521, 16384⟩ := by
  decide +kernel

theorem context_13_112733_413512 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112733 ⟨413512, by decide⟩ :=
  accepted_of_selected 13 112733 ⟨413512, by decide⟩ ⟨13, 2, 0, 413512, 112733, 2521, 16384⟩
    (by decide) selected_cut_16214

theorem selected_cut_16215 : selected 8 ⟨413535, by decide⟩
    (prefixPartial 13 112734) = some ⟨13, 2, 0, 413535, 112734, 1877, 16384⟩ := by
  decide +kernel

theorem context_13_112734_413535 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112734 ⟨413535, by decide⟩ :=
  accepted_of_selected 13 112734 ⟨413535, by decide⟩ ⟨13, 2, 0, 413535, 112734, 1877, 16384⟩
    (by decide) selected_cut_16215

theorem selected_cut_16216 : selected 8 ⟨413540, by decide⟩
    (prefixPartial 13 112735) = some ⟨13, 2, 0, 413540, 112735, 1081, 16384⟩ := by
  decide +kernel

theorem context_13_112735_413540 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112735 ⟨413540, by decide⟩ :=
  accepted_of_selected 13 112735 ⟨413540, by decide⟩ ⟨13, 2, 0, 413540, 112735, 1081, 16384⟩
    (by decide) selected_cut_16216

theorem unmarked_context_12_28183_413541 : frontier 9 ⟨413541, by decide⟩
    (prefixCache 12 28183) (prefixPartial 12 28183) = false := by
  decide +kernel

theorem node_context_12_28183_413541 : EJMOriginalGlobalDAGData.nodes 9 ⟨413541, by decide⟩ =
    .split (coordinate 12) (![⟨413480, by decide⟩,⟨413512, by decide⟩,⟨413535, by decide⟩,⟨413540, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28183_413541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28183 ⟨413541, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28183
    ⟨413541, by decide⟩ (by decide) (![⟨413480, by decide⟩,⟨413512, by decide⟩,⟨413535, by decide⟩,⟨413540, by decide⟩]) unmarked_context_12_28183_413541 node_context_12_28183_413541
  intro a
  fin_cases a
  · exact context_13_112732_413480
  · exact context_13_112733_413512
  · exact context_13_112734_413535
  · exact context_13_112735_413540

theorem unmarked_context_11_7045_413542 : frontier 10 ⟨413542, by decide⟩
    (prefixCache 11 7045) (prefixPartial 11 7045) = false := by
  decide +kernel

theorem node_context_11_7045_413542 : EJMOriginalGlobalDAGData.nodes 10 ⟨413542, by decide⟩ =
    .split (coordinate 11) (![⟨413286, by decide⟩,⟨413370, by decide⟩,⟨413447, by decide⟩,⟨413541, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7045_413542 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7045 ⟨413542, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7045
    ⟨413542, by decide⟩ (by decide) (![⟨413286, by decide⟩,⟨413370, by decide⟩,⟨413447, by decide⟩,⟨413541, by decide⟩]) unmarked_context_11_7045_413542 node_context_11_7045_413542
  intro a
  fin_cases a
  · exact context_12_28180_413286
  · exact context_12_28181_413370
  · exact context_12_28182_413447
  · exact context_12_28183_413541

theorem selected_cut_16217 : selected 8 ⟨413558, by decide⟩
    (prefixPartial 13 112736) = some ⟨13, 2, 0, 413558, 112736, 1417, 16384⟩ := by
  decide +kernel

theorem context_13_112736_413558 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112736 ⟨413558, by decide⟩ :=
  accepted_of_selected 13 112736 ⟨413558, by decide⟩ ⟨13, 2, 0, 413558, 112736, 1417, 16384⟩
    (by decide) selected_cut_16217

theorem selected_cut_16218 : selected 8 ⟨413586, by decide⟩
    (prefixPartial 13 112737) = some ⟨13, 2, 0, 413586, 112737, 2069, 16384⟩ := by
  decide +kernel

theorem context_13_112737_413586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112737 ⟨413586, by decide⟩ :=
  accepted_of_selected 13 112737 ⟨413586, by decide⟩ ⟨13, 2, 0, 413586, 112737, 2069, 16384⟩
    (by decide) selected_cut_16218

theorem selected_cut_16219 : selected 8 ⟨413602, by decide⟩
    (prefixPartial 13 112738) = some ⟨13, 2, 0, 413602, 112738, 1117, 16384⟩ := by
  decide +kernel

theorem context_13_112738_413602 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112738 ⟨413602, by decide⟩ :=
  accepted_of_selected 13 112738 ⟨413602, by decide⟩ ⟨13, 2, 0, 413602, 112738, 1117, 16384⟩
    (by decide) selected_cut_16219

theorem selected_cut_16220 : selected 8 ⟨413611, by decide⟩
    (prefixPartial 13 112739) = some ⟨13, 2, 0, 413611, 112739, 753, 16384⟩ := by
  decide +kernel

theorem context_13_112739_413611 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112739 ⟨413611, by decide⟩ :=
  accepted_of_selected 13 112739 ⟨413611, by decide⟩ ⟨13, 2, 0, 413611, 112739, 753, 16384⟩
    (by decide) selected_cut_16220

theorem unmarked_context_12_28184_413612 : frontier 9 ⟨413612, by decide⟩
    (prefixCache 12 28184) (prefixPartial 12 28184) = false := by
  decide +kernel

theorem node_context_12_28184_413612 : EJMOriginalGlobalDAGData.nodes 9 ⟨413612, by decide⟩ =
    .split (coordinate 12) (![⟨413558, by decide⟩,⟨413586, by decide⟩,⟨413602, by decide⟩,⟨413611, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28184_413612 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28184 ⟨413612, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28184
    ⟨413612, by decide⟩ (by decide) (![⟨413558, by decide⟩,⟨413586, by decide⟩,⟨413602, by decide⟩,⟨413611, by decide⟩]) unmarked_context_12_28184_413612 node_context_12_28184_413612
  intro a
  fin_cases a
  · exact context_13_112736_413558
  · exact context_13_112737_413586
  · exact context_13_112738_413602
  · exact context_13_112739_413611

theorem selected_cut_16221 : selected 8 ⟨413633, by decide⟩
    (prefixPartial 13 112740) = some ⟨13, 2, 0, 413633, 112740, 1677, 16384⟩ := by
  decide +kernel

theorem context_13_112740_413633 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112740 ⟨413633, by decide⟩ :=
  accepted_of_selected 13 112740 ⟨413633, by decide⟩ ⟨13, 2, 0, 413633, 112740, 1677, 16384⟩
    (by decide) selected_cut_16221

theorem selected_cut_16222 : selected 8 ⟨413663, by decide⟩
    (prefixPartial 13 112741) = some ⟨13, 2, 0, 413663, 112741, 2049, 16384⟩ := by
  decide +kernel

theorem context_13_112741_413663 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112741 ⟨413663, by decide⟩ :=
  accepted_of_selected 13 112741 ⟨413663, by decide⟩ ⟨13, 2, 0, 413663, 112741, 2049, 16384⟩
    (by decide) selected_cut_16222

theorem selected_cut_16223 : selected 8 ⟨413680, by decide⟩
    (prefixPartial 13 112742) = some ⟨13, 2, 0, 413680, 112742, 1361, 16384⟩ := by
  decide +kernel

theorem context_13_112742_413680 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112742 ⟨413680, by decide⟩ :=
  accepted_of_selected 13 112742 ⟨413680, by decide⟩ ⟨13, 2, 0, 413680, 112742, 1361, 16384⟩
    (by decide) selected_cut_16223

theorem selected_cut_16224 : selected 8 ⟨413690, by decide⟩
    (prefixPartial 13 112743) = some ⟨13, 2, 0, 413690, 112743, 957, 16384⟩ := by
  decide +kernel

theorem context_13_112743_413690 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112743 ⟨413690, by decide⟩ :=
  accepted_of_selected 13 112743 ⟨413690, by decide⟩ ⟨13, 2, 0, 413690, 112743, 957, 16384⟩
    (by decide) selected_cut_16224

theorem unmarked_context_12_28185_413691 : frontier 9 ⟨413691, by decide⟩
    (prefixCache 12 28185) (prefixPartial 12 28185) = false := by
  decide +kernel

theorem node_context_12_28185_413691 : EJMOriginalGlobalDAGData.nodes 9 ⟨413691, by decide⟩ =
    .split (coordinate 12) (![⟨413633, by decide⟩,⟨413663, by decide⟩,⟨413680, by decide⟩,⟨413690, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28185_413691 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28185 ⟨413691, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28185
    ⟨413691, by decide⟩ (by decide) (![⟨413633, by decide⟩,⟨413663, by decide⟩,⟨413680, by decide⟩,⟨413690, by decide⟩]) unmarked_context_12_28185_413691 node_context_12_28185_413691
  intro a
  fin_cases a
  · exact context_13_112740_413633
  · exact context_13_112741_413663
  · exact context_13_112742_413680
  · exact context_13_112743_413690

theorem selected_cut_16225 : selected 8 ⟨413731, by decide⟩
    (prefixPartial 13 112744) = some ⟨13, 2, 0, 413731, 112744, 2577, 16384⟩ := by
  decide +kernel

theorem context_13_112744_413731 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112744 ⟨413731, by decide⟩ :=
  accepted_of_selected 13 112744 ⟨413731, by decide⟩ ⟨13, 2, 0, 413731, 112744, 2577, 16384⟩
    (by decide) selected_cut_16225

theorem selected_cut_16226 : selected 8 ⟨413798, by decide⟩
    (prefixPartial 13 112745) = some ⟨13, 2, 0, 413798, 112745, 3513, 16384⟩ := by
  decide +kernel

theorem context_13_112745_413798 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112745 ⟨413798, by decide⟩ :=
  accepted_of_selected 13 112745 ⟨413798, by decide⟩ ⟨13, 2, 0, 413798, 112745, 3513, 16384⟩
    (by decide) selected_cut_16226

theorem selected_cut_16227 : selected 8 ⟨413822, by decide⟩
    (prefixPartial 13 112746) = some ⟨13, 2, 0, 413822, 112746, 2081, 16384⟩ := by
  decide +kernel

theorem context_13_112746_413822 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112746 ⟨413822, by decide⟩ :=
  accepted_of_selected 13 112746 ⟨413822, by decide⟩ ⟨13, 2, 0, 413822, 112746, 2081, 16384⟩
    (by decide) selected_cut_16227

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
