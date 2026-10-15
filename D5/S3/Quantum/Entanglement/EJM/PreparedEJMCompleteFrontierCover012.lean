/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover011
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_12_4417_44268 : frontier 9 ⟨44268, by decide⟩
    (prefixCache 12 4417) (prefixPartial 12 4417) = false := by
  decide +kernel

theorem node_context_12_4417_44268 : EJMOriginalGlobalDAGData.nodes 9 ⟨44268, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨44219, by decide⟩,⟨44267, by decide⟩,⟨414, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4417_44268 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4417 ⟨44268, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4417
    ⟨44268, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨44219, by decide⟩,⟨44267, by decide⟩,⟨414, by decide⟩]) unmarked_context_12_4417_44268 node_context_12_4417_44268
  intro a
  fin_cases a
  · exact context_13_17668_3444
  · exact context_13_17669_44219
  · exact context_13_17670_44267
  · exact context_13_17671_414

theorem selected_cut_01154 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 17672) = some ⟨13, 1, 0, 3444, 17672, 1, 16384⟩ := by
  decide +kernel

theorem context_13_17672_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17672 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 17672 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 17672, 1, 16384⟩
    (by decide) selected_cut_01154

theorem selected_cut_01155 : selected 7 ⟨44283, by decide⟩
    (prefixPartial 14 70692) = some ⟨14, 2, 0, 44283, 70692, 853, 4096⟩ := by
  decide +kernel

theorem context_14_70692_44283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 70692 ⟨44283, by decide⟩ :=
  accepted_of_selected 14 70692 ⟨44283, by decide⟩ ⟨14, 2, 0, 44283, 70692, 853, 4096⟩
    (by decide) selected_cut_01155

theorem selected_cut_01156 : selected 7 ⟨44297, by decide⟩
    (prefixPartial 14 70693) = some ⟨14, 2, 0, 44297, 70693, 1021, 4096⟩ := by
  decide +kernel

theorem context_14_70693_44297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 70693 ⟨44297, by decide⟩ :=
  accepted_of_selected 14 70693 ⟨44297, by decide⟩ ⟨14, 2, 0, 44297, 70693, 1021, 4096⟩
    (by decide) selected_cut_01156

theorem selected_cut_01157 : selected 7 ⟨44315, by decide⟩
    (prefixPartial 14 70694) = some ⟨14, 2, 0, 44315, 70694, 1181, 4096⟩ := by
  decide +kernel

theorem context_14_70694_44315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 70694 ⟨44315, by decide⟩ :=
  accepted_of_selected 14 70694 ⟨44315, by decide⟩ ⟨14, 2, 0, 44315, 70694, 1181, 4096⟩
    (by decide) selected_cut_01157

theorem selected_cut_01158 : selected 7 ⟨44333, by decide⟩
    (prefixPartial 14 70695) = some ⟨14, 2, 0, 44333, 70695, 1113, 4096⟩ := by
  decide +kernel

theorem context_14_70695_44333 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 70695 ⟨44333, by decide⟩ :=
  accepted_of_selected 14 70695 ⟨44333, by decide⟩ ⟨14, 2, 0, 44333, 70695, 1113, 4096⟩
    (by decide) selected_cut_01158

theorem unmarked_context_13_17673_44334 : frontier 8 ⟨44334, by decide⟩
    (prefixCache 13 17673) (prefixPartial 13 17673) = false := by
  decide +kernel

theorem node_context_13_17673_44334 : EJMOriginalGlobalDAGData.nodes 8 ⟨44334, by decide⟩ =
    .split (coordinate 13) (![⟨44283, by decide⟩,⟨44297, by decide⟩,⟨44315, by decide⟩,⟨44333, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_17673_44334 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17673 ⟨44334, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 17673
    ⟨44334, by decide⟩ (by decide) (![⟨44283, by decide⟩,⟨44297, by decide⟩,⟨44315, by decide⟩,⟨44333, by decide⟩]) unmarked_context_13_17673_44334 node_context_13_17673_44334
  intro a
  fin_cases a
  · exact context_14_70692_44283
  · exact context_14_70693_44297
  · exact context_14_70694_44315
  · exact context_14_70695_44333

theorem selected_cut_01159 : selected 8 ⟨44404, by decide⟩
    (prefixPartial 13 17674) = some ⟨13, 2, 0, 44404, 17674, 3637, 16384⟩ := by
  decide +kernel

theorem context_13_17674_44404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17674 ⟨44404, by decide⟩ :=
  accepted_of_selected 13 17674 ⟨44404, by decide⟩ ⟨13, 2, 0, 44404, 17674, 3637, 16384⟩
    (by decide) selected_cut_01159

theorem selected_cut_01160 : selected 8 ⟨44430, by decide⟩
    (prefixPartial 13 17675) = some ⟨13, 2, 0, 44430, 17675, 1469, 16384⟩ := by
  decide +kernel

theorem context_13_17675_44430 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17675 ⟨44430, by decide⟩ :=
  accepted_of_selected 13 17675 ⟨44430, by decide⟩ ⟨13, 2, 0, 44430, 17675, 1469, 16384⟩
    (by decide) selected_cut_01160

theorem unmarked_context_12_4418_44431 : frontier 9 ⟨44431, by decide⟩
    (prefixCache 12 4418) (prefixPartial 12 4418) = false := by
  decide +kernel

theorem node_context_12_4418_44431 : EJMOriginalGlobalDAGData.nodes 9 ⟨44431, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨44334, by decide⟩,⟨44404, by decide⟩,⟨44430, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4418_44431 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4418 ⟨44431, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4418
    ⟨44431, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨44334, by decide⟩,⟨44404, by decide⟩,⟨44430, by decide⟩]) unmarked_context_12_4418_44431 node_context_12_4418_44431
  intro a
  fin_cases a
  · exact context_13_17672_3444
  · exact context_13_17673_44334
  · exact context_13_17674_44404
  · exact context_13_17675_44430

theorem selected_cut_01161 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 4419) = some ⟨12, 1, 0, 893, 4419, 1, 65536⟩ := by
  decide +kernel

theorem context_12_4419_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4419 ⟨893, by decide⟩ :=
  accepted_of_selected 12 4419 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 4419, 1, 65536⟩
    (by decide) selected_cut_01161

theorem unmarked_context_11_1104_44432 : frontier 10 ⟨44432, by decide⟩
    (prefixCache 11 1104) (prefixPartial 11 1104) = false := by
  decide +kernel

theorem node_context_11_1104_44432 : EJMOriginalGlobalDAGData.nodes 10 ⟨44432, by decide⟩ =
    .split (coordinate 11) (![⟨44190, by decide⟩,⟨44268, by decide⟩,⟨44431, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1104_44432 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1104 ⟨44432, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1104
    ⟨44432, by decide⟩ (by decide) (![⟨44190, by decide⟩,⟨44268, by decide⟩,⟨44431, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_1104_44432 node_context_11_1104_44432
  intro a
  fin_cases a
  · exact context_12_4416_44190
  · exact context_12_4417_44268
  · exact context_12_4418_44431
  · exact context_12_4419_893

theorem selected_cut_01162 : selected 9 ⟨44474, by decide⟩
    (prefixPartial 12 4420) = some ⟨12, 2, 0, 44474, 4420, 2365, 65536⟩ := by
  decide +kernel

theorem context_12_4420_44474 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4420 ⟨44474, by decide⟩ :=
  accepted_of_selected 12 4420 ⟨44474, by decide⟩ ⟨12, 2, 0, 44474, 4420, 2365, 65536⟩
    (by decide) selected_cut_01162

theorem selected_cut_01163 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 17684) = some ⟨13, 1, 0, 3444, 17684, 1, 16384⟩ := by
  decide +kernel

theorem context_13_17684_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17684 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 17684 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 17684, 1, 16384⟩
    (by decide) selected_cut_01163

theorem selected_cut_01164 : selected 8 ⟨44516, by decide⟩
    (prefixPartial 13 17685) = some ⟨13, 2, 0, 44516, 17685, 2437, 16384⟩ := by
  decide +kernel

theorem context_13_17685_44516 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17685 ⟨44516, by decide⟩ :=
  accepted_of_selected 13 17685 ⟨44516, by decide⟩ ⟨13, 2, 0, 44516, 17685, 2437, 16384⟩
    (by decide) selected_cut_01164

theorem selected_cut_01165 : selected 8 ⟨44556, by decide⟩
    (prefixPartial 13 17686) = some ⟨13, 2, 0, 44556, 17686, 2393, 16384⟩ := by
  decide +kernel

theorem context_13_17686_44556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17686 ⟨44556, by decide⟩ :=
  accepted_of_selected 13 17686 ⟨44556, by decide⟩ ⟨13, 2, 0, 44556, 17686, 2393, 16384⟩
    (by decide) selected_cut_01165

theorem selected_cut_01166 : selected 8 ⟨414, by decide⟩
    (prefixPartial 13 17687) = some ⟨13, 1, 0, 414, 17687, 1, 16384⟩ := by
  decide +kernel

theorem context_13_17687_414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17687 ⟨414, by decide⟩ :=
  accepted_of_selected 13 17687 ⟨414, by decide⟩ ⟨13, 1, 0, 414, 17687, 1, 16384⟩
    (by decide) selected_cut_01166

theorem unmarked_context_12_4421_44557 : frontier 9 ⟨44557, by decide⟩
    (prefixCache 12 4421) (prefixPartial 12 4421) = false := by
  decide +kernel

theorem node_context_12_4421_44557 : EJMOriginalGlobalDAGData.nodes 9 ⟨44557, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨44516, by decide⟩,⟨44556, by decide⟩,⟨414, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4421_44557 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4421 ⟨44557, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4421
    ⟨44557, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨44516, by decide⟩,⟨44556, by decide⟩,⟨414, by decide⟩]) unmarked_context_12_4421_44557 node_context_12_4421_44557
  intro a
  fin_cases a
  · exact context_13_17684_3444
  · exact context_13_17685_44516
  · exact context_13_17686_44556
  · exact context_13_17687_414

theorem selected_cut_01167 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 17688) = some ⟨13, 1, 0, 3444, 17688, 1, 16384⟩ := by
  decide +kernel

theorem context_13_17688_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17688 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 17688 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 17688, 1, 16384⟩
    (by decide) selected_cut_01167

theorem selected_cut_01168 : selected 8 ⟨44587, by decide⟩
    (prefixPartial 13 17689) = some ⟨13, 2, 0, 44587, 17689, 2893, 16384⟩ := by
  decide +kernel

theorem context_13_17689_44587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17689 ⟨44587, by decide⟩ :=
  accepted_of_selected 13 17689 ⟨44587, by decide⟩ ⟨13, 2, 0, 44587, 17689, 2893, 16384⟩
    (by decide) selected_cut_01168

theorem selected_cut_01169 : selected 8 ⟨44618, by decide⟩
    (prefixPartial 13 17690) = some ⟨13, 2, 0, 44618, 17690, 2241, 16384⟩ := by
  decide +kernel

theorem context_13_17690_44618 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17690 ⟨44618, by decide⟩ :=
  accepted_of_selected 13 17690 ⟨44618, by decide⟩ ⟨13, 2, 0, 44618, 17690, 2241, 16384⟩
    (by decide) selected_cut_01169

theorem selected_cut_01170 : selected 8 ⟨44630, by decide⟩
    (prefixPartial 13 17691) = some ⟨13, 2, 0, 44630, 17691, 1077, 16384⟩ := by
  decide +kernel

theorem context_13_17691_44630 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17691 ⟨44630, by decide⟩ :=
  accepted_of_selected 13 17691 ⟨44630, by decide⟩ ⟨13, 2, 0, 44630, 17691, 1077, 16384⟩
    (by decide) selected_cut_01170

theorem unmarked_context_12_4422_44631 : frontier 9 ⟨44631, by decide⟩
    (prefixCache 12 4422) (prefixPartial 12 4422) = false := by
  decide +kernel

theorem node_context_12_4422_44631 : EJMOriginalGlobalDAGData.nodes 9 ⟨44631, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨44587, by decide⟩,⟨44618, by decide⟩,⟨44630, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4422_44631 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4422 ⟨44631, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4422
    ⟨44631, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨44587, by decide⟩,⟨44618, by decide⟩,⟨44630, by decide⟩]) unmarked_context_12_4422_44631 node_context_12_4422_44631
  intro a
  fin_cases a
  · exact context_13_17688_3444
  · exact context_13_17689_44587
  · exact context_13_17690_44618
  · exact context_13_17691_44630

theorem selected_cut_01171 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 4423) = some ⟨12, 1, 0, 893, 4423, 1, 65536⟩ := by
  decide +kernel

theorem context_12_4423_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4423 ⟨893, by decide⟩ :=
  accepted_of_selected 12 4423 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 4423, 1, 65536⟩
    (by decide) selected_cut_01171

theorem unmarked_context_11_1105_44632 : frontier 10 ⟨44632, by decide⟩
    (prefixCache 11 1105) (prefixPartial 11 1105) = false := by
  decide +kernel

theorem node_context_11_1105_44632 : EJMOriginalGlobalDAGData.nodes 10 ⟨44632, by decide⟩ =
    .split (coordinate 11) (![⟨44474, by decide⟩,⟨44557, by decide⟩,⟨44631, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1105_44632 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1105 ⟨44632, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1105
    ⟨44632, by decide⟩ (by decide) (![⟨44474, by decide⟩,⟨44557, by decide⟩,⟨44631, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_1105_44632 node_context_11_1105_44632
  intro a
  fin_cases a
  · exact context_12_4420_44474
  · exact context_12_4421_44557
  · exact context_12_4422_44631
  · exact context_12_4423_893

theorem selected_cut_01172 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 17696) = some ⟨13, 1, 0, 3444, 17696, 1, 16384⟩ := by
  decide +kernel

theorem context_13_17696_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17696 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 17696 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 17696, 1, 16384⟩
    (by decide) selected_cut_01172

theorem selected_cut_01173 : selected 8 ⟨44656, by decide⟩
    (prefixPartial 13 17697) = some ⟨13, 2, 0, 44656, 17697, 1761, 16384⟩ := by
  decide +kernel

theorem context_13_17697_44656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17697 ⟨44656, by decide⟩ :=
  accepted_of_selected 13 17697 ⟨44656, by decide⟩ ⟨13, 2, 0, 44656, 17697, 1761, 16384⟩
    (by decide) selected_cut_01173

theorem selected_cut_01174 : selected 8 ⟨44682, by decide⟩
    (prefixPartial 13 17698) = some ⟨13, 2, 0, 44682, 17698, 1841, 16384⟩ := by
  decide +kernel

theorem context_13_17698_44682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17698 ⟨44682, by decide⟩ :=
  accepted_of_selected 13 17698 ⟨44682, by decide⟩ ⟨13, 2, 0, 44682, 17698, 1841, 16384⟩
    (by decide) selected_cut_01174

theorem selected_cut_01175 : selected 8 ⟨44693, by decide⟩
    (prefixPartial 13 17699) = some ⟨13, 2, 0, 44693, 17699, 825, 16384⟩ := by
  decide +kernel

theorem context_13_17699_44693 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17699 ⟨44693, by decide⟩ :=
  accepted_of_selected 13 17699 ⟨44693, by decide⟩ ⟨13, 2, 0, 44693, 17699, 825, 16384⟩
    (by decide) selected_cut_01175

theorem unmarked_context_12_4424_44694 : frontier 9 ⟨44694, by decide⟩
    (prefixCache 12 4424) (prefixPartial 12 4424) = false := by
  decide +kernel

theorem node_context_12_4424_44694 : EJMOriginalGlobalDAGData.nodes 9 ⟨44694, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨44656, by decide⟩,⟨44682, by decide⟩,⟨44693, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4424_44694 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4424 ⟨44694, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4424
    ⟨44694, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨44656, by decide⟩,⟨44682, by decide⟩,⟨44693, by decide⟩]) unmarked_context_12_4424_44694 node_context_12_4424_44694
  intro a
  fin_cases a
  · exact context_13_17696_3444
  · exact context_13_17697_44656
  · exact context_13_17698_44682
  · exact context_13_17699_44693

theorem selected_cut_01176 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 17700) = some ⟨13, 1, 0, 3444, 17700, 1, 16384⟩ := by
  decide +kernel

theorem context_13_17700_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17700 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 17700 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 17700, 1, 16384⟩
    (by decide) selected_cut_01176

theorem selected_cut_01177 : selected 8 ⟨44716, by decide⟩
    (prefixPartial 13 17701) = some ⟨13, 2, 0, 44716, 17701, 2089, 16384⟩ := by
  decide +kernel

theorem context_13_17701_44716 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17701 ⟨44716, by decide⟩ :=
  accepted_of_selected 13 17701 ⟨44716, by decide⟩ ⟨13, 2, 0, 44716, 17701, 2089, 16384⟩
    (by decide) selected_cut_01177

theorem selected_cut_01178 : selected 8 ⟨44742, by decide⟩
    (prefixPartial 13 17702) = some ⟨13, 2, 0, 44742, 17702, 2145, 16384⟩ := by
  decide +kernel

theorem context_13_17702_44742 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17702 ⟨44742, by decide⟩ :=
  accepted_of_selected 13 17702 ⟨44742, by decide⟩ ⟨13, 2, 0, 44742, 17702, 2145, 16384⟩
    (by decide) selected_cut_01178

theorem selected_cut_01179 : selected 8 ⟨44755, by decide⟩
    (prefixPartial 13 17703) = some ⟨13, 2, 0, 44755, 17703, 1073, 16384⟩ := by
  decide +kernel

theorem context_13_17703_44755 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17703 ⟨44755, by decide⟩ :=
  accepted_of_selected 13 17703 ⟨44755, by decide⟩ ⟨13, 2, 0, 44755, 17703, 1073, 16384⟩
    (by decide) selected_cut_01179

theorem unmarked_context_12_4425_44756 : frontier 9 ⟨44756, by decide⟩
    (prefixCache 12 4425) (prefixPartial 12 4425) = false := by
  decide +kernel

theorem node_context_12_4425_44756 : EJMOriginalGlobalDAGData.nodes 9 ⟨44756, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨44716, by decide⟩,⟨44742, by decide⟩,⟨44755, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4425_44756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4425 ⟨44756, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4425
    ⟨44756, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨44716, by decide⟩,⟨44742, by decide⟩,⟨44755, by decide⟩]) unmarked_context_12_4425_44756 node_context_12_4425_44756
  intro a
  fin_cases a
  · exact context_13_17700_3444
  · exact context_13_17701_44716
  · exact context_13_17702_44742
  · exact context_13_17703_44755

theorem selected_cut_01180 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 17704) = some ⟨13, 1, 0, 3444, 17704, 1, 16384⟩ := by
  decide +kernel

theorem context_13_17704_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17704 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 17704 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 17704, 1, 16384⟩
    (by decide) selected_cut_01180

theorem selected_cut_01181 : selected 8 ⟨44781, by decide⟩
    (prefixPartial 13 17705) = some ⟨13, 2, 0, 44781, 17705, 2281, 16384⟩ := by
  decide +kernel

theorem context_13_17705_44781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17705 ⟨44781, by decide⟩ :=
  accepted_of_selected 13 17705 ⟨44781, by decide⟩ ⟨13, 2, 0, 44781, 17705, 2281, 16384⟩
    (by decide) selected_cut_01181

theorem selected_cut_01182 : selected 8 ⟨44806, by decide⟩
    (prefixPartial 13 17706) = some ⟨13, 2, 0, 44806, 17706, 2309, 16384⟩ := by
  decide +kernel

theorem context_13_17706_44806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17706 ⟨44806, by decide⟩ :=
  accepted_of_selected 13 17706 ⟨44806, by decide⟩ ⟨13, 2, 0, 44806, 17706, 2309, 16384⟩
    (by decide) selected_cut_01182

theorem selected_cut_01183 : selected 8 ⟨44821, by decide⟩
    (prefixPartial 13 17707) = some ⟨13, 2, 0, 44821, 17707, 1017, 16384⟩ := by
  decide +kernel

theorem context_13_17707_44821 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17707 ⟨44821, by decide⟩ :=
  accepted_of_selected 13 17707 ⟨44821, by decide⟩ ⟨13, 2, 0, 44821, 17707, 1017, 16384⟩
    (by decide) selected_cut_01183

theorem unmarked_context_12_4426_44822 : frontier 9 ⟨44822, by decide⟩
    (prefixCache 12 4426) (prefixPartial 12 4426) = false := by
  decide +kernel

theorem node_context_12_4426_44822 : EJMOriginalGlobalDAGData.nodes 9 ⟨44822, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨44781, by decide⟩,⟨44806, by decide⟩,⟨44821, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4426_44822 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4426 ⟨44822, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4426
    ⟨44822, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨44781, by decide⟩,⟨44806, by decide⟩,⟨44821, by decide⟩]) unmarked_context_12_4426_44822 node_context_12_4426_44822
  intro a
  fin_cases a
  · exact context_13_17704_3444
  · exact context_13_17705_44781
  · exact context_13_17706_44806
  · exact context_13_17707_44821

theorem selected_cut_01184 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 17708) = some ⟨13, 1, 0, 3444, 17708, 1, 16384⟩ := by
  decide +kernel

theorem context_13_17708_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17708 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 17708 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 17708, 1, 16384⟩
    (by decide) selected_cut_01184

theorem selected_cut_01185 : selected 8 ⟨44848, by decide⟩
    (prefixPartial 13 17709) = some ⟨13, 2, 0, 44848, 17709, 2269, 16384⟩ := by
  decide +kernel

theorem context_13_17709_44848 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17709 ⟨44848, by decide⟩ :=
  accepted_of_selected 13 17709 ⟨44848, by decide⟩ ⟨13, 2, 0, 44848, 17709, 2269, 16384⟩
    (by decide) selected_cut_01185

theorem selected_cut_01186 : selected 8 ⟨44880, by decide⟩
    (prefixPartial 13 17710) = some ⟨13, 2, 0, 44880, 17710, 2337, 16384⟩ := by
  decide +kernel

theorem context_13_17710_44880 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17710 ⟨44880, by decide⟩ :=
  accepted_of_selected 13 17710 ⟨44880, by decide⟩ ⟨13, 2, 0, 44880, 17710, 2337, 16384⟩
    (by decide) selected_cut_01186

theorem selected_cut_01187 : selected 8 ⟨44892, by decide⟩
    (prefixPartial 13 17711) = some ⟨13, 2, 0, 44892, 17711, 1221, 16384⟩ := by
  decide +kernel

theorem context_13_17711_44892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17711 ⟨44892, by decide⟩ :=
  accepted_of_selected 13 17711 ⟨44892, by decide⟩ ⟨13, 2, 0, 44892, 17711, 1221, 16384⟩
    (by decide) selected_cut_01187

theorem unmarked_context_12_4427_44893 : frontier 9 ⟨44893, by decide⟩
    (prefixCache 12 4427) (prefixPartial 12 4427) = false := by
  decide +kernel

theorem node_context_12_4427_44893 : EJMOriginalGlobalDAGData.nodes 9 ⟨44893, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨44848, by decide⟩,⟨44880, by decide⟩,⟨44892, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4427_44893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4427 ⟨44893, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4427
    ⟨44893, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨44848, by decide⟩,⟨44880, by decide⟩,⟨44892, by decide⟩]) unmarked_context_12_4427_44893 node_context_12_4427_44893
  intro a
  fin_cases a
  · exact context_13_17708_3444
  · exact context_13_17709_44848
  · exact context_13_17710_44880
  · exact context_13_17711_44892

theorem unmarked_context_11_1106_44894 : frontier 10 ⟨44894, by decide⟩
    (prefixCache 11 1106) (prefixPartial 11 1106) = false := by
  decide +kernel

theorem node_context_11_1106_44894 : EJMOriginalGlobalDAGData.nodes 10 ⟨44894, by decide⟩ =
    .split (coordinate 11) (![⟨44694, by decide⟩,⟨44756, by decide⟩,⟨44822, by decide⟩,⟨44893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1106_44894 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1106 ⟨44894, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1106
    ⟨44894, by decide⟩ (by decide) (![⟨44694, by decide⟩,⟨44756, by decide⟩,⟨44822, by decide⟩,⟨44893, by decide⟩]) unmarked_context_11_1106_44894 node_context_11_1106_44894
  intro a
  fin_cases a
  · exact context_12_4424_44694
  · exact context_12_4425_44756
  · exact context_12_4426_44822
  · exact context_12_4427_44893

theorem selected_cut_01188 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 1107) = some ⟨11, 1, 0, 1736, 1107, 1, 262144⟩ := by
  decide +kernel

theorem context_11_1107_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1107 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 1107 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 1107, 1, 262144⟩
    (by decide) selected_cut_01188

theorem unmarked_context_10_276_44895 : frontier 11 ⟨44895, by decide⟩
    (prefixCache 10 276) (prefixPartial 10 276) = false := by
  decide +kernel

theorem node_context_10_276_44895 : EJMOriginalGlobalDAGData.nodes 11 ⟨44895, by decide⟩ =
    .split (coordinate 10) (![⟨44432, by decide⟩,⟨44632, by decide⟩,⟨44894, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_276_44895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 276 ⟨44895, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 276
    ⟨44895, by decide⟩ (by decide) (![⟨44432, by decide⟩,⟨44632, by decide⟩,⟨44894, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_276_44895 node_context_10_276_44895
  intro a
  fin_cases a
  · exact context_11_1104_44432
  · exact context_11_1105_44632
  · exact context_11_1106_44894
  · exact context_11_1107_1736

theorem selected_cut_01189 : selected 9 ⟨44932, by decide⟩
    (prefixPartial 12 4432) = some ⟨12, 2, 0, 44932, 4432, 2073, 65536⟩ := by
  decide +kernel

theorem context_12_4432_44932 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4432 ⟨44932, by decide⟩ :=
  accepted_of_selected 12 4432 ⟨44932, by decide⟩ ⟨12, 2, 0, 44932, 4432, 2073, 65536⟩
    (by decide) selected_cut_01189

theorem selected_cut_01190 : selected 9 ⟨44976, by decide⟩
    (prefixPartial 12 4433) = some ⟨12, 2, 0, 44976, 4433, 2477, 65536⟩ := by
  decide +kernel

theorem context_12_4433_44976 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4433 ⟨44976, by decide⟩ :=
  accepted_of_selected 12 4433 ⟨44976, by decide⟩ ⟨12, 2, 0, 44976, 4433, 2477, 65536⟩
    (by decide) selected_cut_01190

theorem selected_cut_01191 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 17736) = some ⟨13, 1, 0, 3444, 17736, 1, 16384⟩ := by
  decide +kernel

theorem context_13_17736_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17736 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 17736 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 17736, 1, 16384⟩
    (by decide) selected_cut_01191

theorem selected_cut_01192 : selected 8 ⟨44998, by decide⟩
    (prefixPartial 13 17737) = some ⟨13, 2, 0, 44998, 17737, 2065, 16384⟩ := by
  decide +kernel

theorem context_13_17737_44998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17737 ⟨44998, by decide⟩ :=
  accepted_of_selected 13 17737 ⟨44998, by decide⟩ ⟨13, 2, 0, 44998, 17737, 2065, 16384⟩
    (by decide) selected_cut_01192

theorem selected_cut_01193 : selected 8 ⟨45027, by decide⟩
    (prefixPartial 13 17738) = some ⟨13, 2, 0, 45027, 17738, 2273, 16384⟩ := by
  decide +kernel

theorem context_13_17738_45027 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17738 ⟨45027, by decide⟩ :=
  accepted_of_selected 13 17738 ⟨45027, by decide⟩ ⟨13, 2, 0, 45027, 17738, 2273, 16384⟩
    (by decide) selected_cut_01193

theorem selected_cut_01194 : selected 8 ⟨45042, by decide⟩
    (prefixPartial 13 17739) = some ⟨13, 2, 0, 45042, 17739, 1161, 16384⟩ := by
  decide +kernel

theorem context_13_17739_45042 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17739 ⟨45042, by decide⟩ :=
  accepted_of_selected 13 17739 ⟨45042, by decide⟩ ⟨13, 2, 0, 45042, 17739, 1161, 16384⟩
    (by decide) selected_cut_01194

theorem unmarked_context_12_4434_45043 : frontier 9 ⟨45043, by decide⟩
    (prefixCache 12 4434) (prefixPartial 12 4434) = false := by
  decide +kernel

theorem node_context_12_4434_45043 : EJMOriginalGlobalDAGData.nodes 9 ⟨45043, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨44998, by decide⟩,⟨45027, by decide⟩,⟨45042, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4434_45043 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4434 ⟨45043, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4434
    ⟨45043, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨44998, by decide⟩,⟨45027, by decide⟩,⟨45042, by decide⟩]) unmarked_context_12_4434_45043 node_context_12_4434_45043
  intro a
  fin_cases a
  · exact context_13_17736_3444
  · exact context_13_17737_44998
  · exact context_13_17738_45027
  · exact context_13_17739_45042

theorem selected_cut_01195 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 4435) = some ⟨12, 1, 0, 893, 4435, 1, 65536⟩ := by
  decide +kernel

theorem context_12_4435_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4435 ⟨893, by decide⟩ :=
  accepted_of_selected 12 4435 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 4435, 1, 65536⟩
    (by decide) selected_cut_01195

theorem unmarked_context_11_1108_45044 : frontier 10 ⟨45044, by decide⟩
    (prefixCache 11 1108) (prefixPartial 11 1108) = false := by
  decide +kernel

theorem node_context_11_1108_45044 : EJMOriginalGlobalDAGData.nodes 10 ⟨45044, by decide⟩ =
    .split (coordinate 11) (![⟨44932, by decide⟩,⟨44976, by decide⟩,⟨45043, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1108_45044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1108 ⟨45044, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1108
    ⟨45044, by decide⟩ (by decide) (![⟨44932, by decide⟩,⟨44976, by decide⟩,⟨45043, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_1108_45044 node_context_11_1108_45044
  intro a
  fin_cases a
  · exact context_12_4432_44932
  · exact context_12_4433_44976
  · exact context_12_4434_45043
  · exact context_12_4435_893

theorem selected_cut_01196 : selected 9 ⟨45086, by decide⟩
    (prefixPartial 12 4436) = some ⟨12, 2, 0, 45086, 4436, 2353, 65536⟩ := by
  decide +kernel

theorem context_12_4436_45086 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4436 ⟨45086, by decide⟩ :=
  accepted_of_selected 12 4436 ⟨45086, by decide⟩ ⟨12, 2, 0, 45086, 4436, 2353, 65536⟩
    (by decide) selected_cut_01196

theorem selected_cut_01197 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 17748) = some ⟨13, 1, 0, 3444, 17748, 1, 16384⟩ := by
  decide +kernel

theorem context_13_17748_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17748 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 17748 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 17748, 1, 16384⟩
    (by decide) selected_cut_01197

theorem selected_cut_01198 : selected 8 ⟨45106, by decide⟩
    (prefixPartial 13 17749) = some ⟨13, 2, 0, 45106, 17749, 1605, 16384⟩ := by
  decide +kernel

theorem context_13_17749_45106 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17749 ⟨45106, by decide⟩ :=
  accepted_of_selected 13 17749 ⟨45106, by decide⟩ ⟨13, 2, 0, 45106, 17749, 1605, 16384⟩
    (by decide) selected_cut_01198

theorem selected_cut_01199 : selected 8 ⟨45151, by decide⟩
    (prefixPartial 13 17750) = some ⟨13, 2, 0, 45151, 17750, 2549, 16384⟩ := by
  decide +kernel

theorem context_13_17750_45151 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17750 ⟨45151, by decide⟩ :=
  accepted_of_selected 13 17750 ⟨45151, by decide⟩ ⟨13, 2, 0, 45151, 17750, 2549, 16384⟩
    (by decide) selected_cut_01199

theorem selected_cut_01200 : selected 8 ⟨414, by decide⟩
    (prefixPartial 13 17751) = some ⟨13, 1, 0, 414, 17751, 1, 16384⟩ := by
  decide +kernel

theorem context_13_17751_414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17751 ⟨414, by decide⟩ :=
  accepted_of_selected 13 17751 ⟨414, by decide⟩ ⟨13, 1, 0, 414, 17751, 1, 16384⟩
    (by decide) selected_cut_01200

theorem unmarked_context_12_4437_45152 : frontier 9 ⟨45152, by decide⟩
    (prefixCache 12 4437) (prefixPartial 12 4437) = false := by
  decide +kernel

theorem node_context_12_4437_45152 : EJMOriginalGlobalDAGData.nodes 9 ⟨45152, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨45106, by decide⟩,⟨45151, by decide⟩,⟨414, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4437_45152 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4437 ⟨45152, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4437
    ⟨45152, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨45106, by decide⟩,⟨45151, by decide⟩,⟨414, by decide⟩]) unmarked_context_12_4437_45152 node_context_12_4437_45152
  intro a
  fin_cases a
  · exact context_13_17748_3444
  · exact context_13_17749_45106
  · exact context_13_17750_45151
  · exact context_13_17751_414

theorem selected_cut_01201 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 17752) = some ⟨13, 1, 0, 3444, 17752, 1, 16384⟩ := by
  decide +kernel

theorem context_13_17752_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17752 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 17752 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 17752, 1, 16384⟩
    (by decide) selected_cut_01201

theorem selected_cut_01202 : selected 8 ⟨45174, by decide⟩
    (prefixPartial 13 17753) = some ⟨13, 2, 0, 45174, 17753, 2177, 16384⟩ := by
  decide +kernel

theorem context_13_17753_45174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17753 ⟨45174, by decide⟩ :=
  accepted_of_selected 13 17753 ⟨45174, by decide⟩ ⟨13, 2, 0, 45174, 17753, 2177, 16384⟩
    (by decide) selected_cut_01202

theorem selected_cut_01203 : selected 8 ⟨45203, by decide⟩
    (prefixPartial 13 17754) = some ⟨13, 2, 0, 45203, 17754, 2357, 16384⟩ := by
  decide +kernel

theorem context_13_17754_45203 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17754 ⟨45203, by decide⟩ :=
  accepted_of_selected 13 17754 ⟨45203, by decide⟩ ⟨13, 2, 0, 45203, 17754, 2357, 16384⟩
    (by decide) selected_cut_01203

theorem selected_cut_01204 : selected 8 ⟨45224, by decide⟩
    (prefixPartial 13 17755) = some ⟨13, 2, 0, 45224, 17755, 1281, 16384⟩ := by
  decide +kernel

theorem context_13_17755_45224 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17755 ⟨45224, by decide⟩ :=
  accepted_of_selected 13 17755 ⟨45224, by decide⟩ ⟨13, 2, 0, 45224, 17755, 1281, 16384⟩
    (by decide) selected_cut_01204

theorem unmarked_context_12_4438_45225 : frontier 9 ⟨45225, by decide⟩
    (prefixCache 12 4438) (prefixPartial 12 4438) = false := by
  decide +kernel

theorem node_context_12_4438_45225 : EJMOriginalGlobalDAGData.nodes 9 ⟨45225, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨45174, by decide⟩,⟨45203, by decide⟩,⟨45224, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4438_45225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4438 ⟨45225, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4438
    ⟨45225, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨45174, by decide⟩,⟨45203, by decide⟩,⟨45224, by decide⟩]) unmarked_context_12_4438_45225 node_context_12_4438_45225
  intro a
  fin_cases a
  · exact context_13_17752_3444
  · exact context_13_17753_45174
  · exact context_13_17754_45203
  · exact context_13_17755_45224

theorem selected_cut_01205 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 4439) = some ⟨12, 1, 0, 893, 4439, 1, 65536⟩ := by
  decide +kernel

theorem context_12_4439_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4439 ⟨893, by decide⟩ :=
  accepted_of_selected 12 4439 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 4439, 1, 65536⟩
    (by decide) selected_cut_01205

theorem unmarked_context_11_1109_45226 : frontier 10 ⟨45226, by decide⟩
    (prefixCache 11 1109) (prefixPartial 11 1109) = false := by
  decide +kernel

theorem node_context_11_1109_45226 : EJMOriginalGlobalDAGData.nodes 10 ⟨45226, by decide⟩ =
    .split (coordinate 11) (![⟨45086, by decide⟩,⟨45152, by decide⟩,⟨45225, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1109_45226 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1109 ⟨45226, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1109
    ⟨45226, by decide⟩ (by decide) (![⟨45086, by decide⟩,⟨45152, by decide⟩,⟨45225, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_1109_45226 node_context_11_1109_45226
  intro a
  fin_cases a
  · exact context_12_4436_45086
  · exact context_12_4437_45152
  · exact context_12_4438_45225
  · exact context_12_4439_893

theorem selected_cut_01206 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 17760) = some ⟨13, 1, 0, 3444, 17760, 1, 16384⟩ := by
  decide +kernel

theorem context_13_17760_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17760 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 17760 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 17760, 1, 16384⟩
    (by decide) selected_cut_01206

theorem selected_cut_01207 : selected 8 ⟨45247, by decide⟩
    (prefixPartial 13 17761) = some ⟨13, 2, 0, 45247, 17761, 1621, 16384⟩ := by
  decide +kernel

theorem context_13_17761_45247 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17761 ⟨45247, by decide⟩ :=
  accepted_of_selected 13 17761 ⟨45247, by decide⟩ ⟨13, 2, 0, 45247, 17761, 1621, 16384⟩
    (by decide) selected_cut_01207

theorem selected_cut_01208 : selected 8 ⟨45281, by decide⟩
    (prefixPartial 13 17762) = some ⟨13, 2, 0, 45281, 17762, 2177, 16384⟩ := by
  decide +kernel

theorem context_13_17762_45281 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17762 ⟨45281, by decide⟩ :=
  accepted_of_selected 13 17762 ⟨45281, by decide⟩ ⟨13, 2, 0, 45281, 17762, 2177, 16384⟩
    (by decide) selected_cut_01208

theorem selected_cut_01209 : selected 8 ⟨45291, by decide⟩
    (prefixPartial 13 17763) = some ⟨13, 2, 0, 45291, 17763, 1017, 16384⟩ := by
  decide +kernel

theorem context_13_17763_45291 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17763 ⟨45291, by decide⟩ :=
  accepted_of_selected 13 17763 ⟨45291, by decide⟩ ⟨13, 2, 0, 45291, 17763, 1017, 16384⟩
    (by decide) selected_cut_01209

theorem unmarked_context_12_4440_45292 : frontier 9 ⟨45292, by decide⟩
    (prefixCache 12 4440) (prefixPartial 12 4440) = false := by
  decide +kernel

theorem node_context_12_4440_45292 : EJMOriginalGlobalDAGData.nodes 9 ⟨45292, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨45247, by decide⟩,⟨45281, by decide⟩,⟨45291, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4440_45292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4440 ⟨45292, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4440
    ⟨45292, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨45247, by decide⟩,⟨45281, by decide⟩,⟨45291, by decide⟩]) unmarked_context_12_4440_45292 node_context_12_4440_45292
  intro a
  fin_cases a
  · exact context_13_17760_3444
  · exact context_13_17761_45247
  · exact context_13_17762_45281
  · exact context_13_17763_45291

theorem selected_cut_01210 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 17764) = some ⟨13, 1, 0, 3444, 17764, 1, 16384⟩ := by
  decide +kernel

theorem context_13_17764_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17764 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 17764 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 17764, 1, 16384⟩
    (by decide) selected_cut_01210

theorem selected_cut_01211 : selected 8 ⟨45321, by decide⟩
    (prefixPartial 13 17765) = some ⟨13, 2, 0, 45321, 17765, 1793, 16384⟩ := by
  decide +kernel

theorem context_13_17765_45321 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17765 ⟨45321, by decide⟩ :=
  accepted_of_selected 13 17765 ⟨45321, by decide⟩ ⟨13, 2, 0, 45321, 17765, 1793, 16384⟩
    (by decide) selected_cut_01211

theorem selected_cut_01212 : selected 8 ⟨45355, by decide⟩
    (prefixPartial 13 17766) = some ⟨13, 2, 0, 45355, 17766, 2433, 16384⟩ := by
  decide +kernel

theorem context_13_17766_45355 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17766 ⟨45355, by decide⟩ :=
  accepted_of_selected 13 17766 ⟨45355, by decide⟩ ⟨13, 2, 0, 45355, 17766, 2433, 16384⟩
    (by decide) selected_cut_01212

theorem selected_cut_01213 : selected 8 ⟨45371, by decide⟩
    (prefixPartial 13 17767) = some ⟨13, 2, 0, 45371, 17767, 1213, 16384⟩ := by
  decide +kernel

theorem context_13_17767_45371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17767 ⟨45371, by decide⟩ :=
  accepted_of_selected 13 17767 ⟨45371, by decide⟩ ⟨13, 2, 0, 45371, 17767, 1213, 16384⟩
    (by decide) selected_cut_01213

theorem unmarked_context_12_4441_45372 : frontier 9 ⟨45372, by decide⟩
    (prefixCache 12 4441) (prefixPartial 12 4441) = false := by
  decide +kernel

theorem node_context_12_4441_45372 : EJMOriginalGlobalDAGData.nodes 9 ⟨45372, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨45321, by decide⟩,⟨45355, by decide⟩,⟨45371, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4441_45372 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4441 ⟨45372, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4441
    ⟨45372, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨45321, by decide⟩,⟨45355, by decide⟩,⟨45371, by decide⟩]) unmarked_context_12_4441_45372 node_context_12_4441_45372
  intro a
  fin_cases a
  · exact context_13_17764_3444
  · exact context_13_17765_45321
  · exact context_13_17766_45355
  · exact context_13_17767_45371

theorem selected_cut_01214 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 17768) = some ⟨13, 1, 0, 3444, 17768, 1, 16384⟩ := by
  decide +kernel

theorem context_13_17768_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17768 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 17768 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 17768, 1, 16384⟩
    (by decide) selected_cut_01214

theorem selected_cut_01215 : selected 8 ⟨45399, by decide⟩
    (prefixPartial 13 17769) = some ⟨13, 2, 0, 45399, 17769, 2001, 16384⟩ := by
  decide +kernel

theorem context_13_17769_45399 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17769 ⟨45399, by decide⟩ :=
  accepted_of_selected 13 17769 ⟨45399, by decide⟩ ⟨13, 2, 0, 45399, 17769, 2001, 16384⟩
    (by decide) selected_cut_01215

theorem selected_cut_01216 : selected 8 ⟨45437, by decide⟩
    (prefixPartial 13 17770) = some ⟨13, 2, 0, 45437, 17770, 2665, 16384⟩ := by
  decide +kernel

theorem context_13_17770_45437 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17770 ⟨45437, by decide⟩ :=
  accepted_of_selected 13 17770 ⟨45437, by decide⟩ ⟨13, 2, 0, 45437, 17770, 2665, 16384⟩
    (by decide) selected_cut_01216

theorem selected_cut_01217 : selected 8 ⟨45449, by decide⟩
    (prefixPartial 13 17771) = some ⟨13, 2, 0, 45449, 17771, 1329, 16384⟩ := by
  decide +kernel

theorem context_13_17771_45449 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17771 ⟨45449, by decide⟩ :=
  accepted_of_selected 13 17771 ⟨45449, by decide⟩ ⟨13, 2, 0, 45449, 17771, 1329, 16384⟩
    (by decide) selected_cut_01217

theorem unmarked_context_12_4442_45450 : frontier 9 ⟨45450, by decide⟩
    (prefixCache 12 4442) (prefixPartial 12 4442) = false := by
  decide +kernel

theorem node_context_12_4442_45450 : EJMOriginalGlobalDAGData.nodes 9 ⟨45450, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨45399, by decide⟩,⟨45437, by decide⟩,⟨45449, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4442_45450 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4442 ⟨45450, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4442
    ⟨45450, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨45399, by decide⟩,⟨45437, by decide⟩,⟨45449, by decide⟩]) unmarked_context_12_4442_45450 node_context_12_4442_45450
  intro a
  fin_cases a
  · exact context_13_17768_3444
  · exact context_13_17769_45399
  · exact context_13_17770_45437
  · exact context_13_17771_45449

theorem selected_cut_01218 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 17772) = some ⟨13, 1, 0, 3444, 17772, 1, 16384⟩ := by
  decide +kernel

theorem context_13_17772_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17772 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 17772 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 17772, 1, 16384⟩
    (by decide) selected_cut_01218

theorem selected_cut_01219 : selected 8 ⟨45474, by decide⟩
    (prefixPartial 13 17773) = some ⟨13, 2, 0, 45474, 17773, 1973, 16384⟩ := by
  decide +kernel

theorem context_13_17773_45474 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17773 ⟨45474, by decide⟩ :=
  accepted_of_selected 13 17773 ⟨45474, by decide⟩ ⟨13, 2, 0, 45474, 17773, 1973, 16384⟩
    (by decide) selected_cut_01219

theorem selected_cut_01220 : selected 8 ⟨45533, by decide⟩
    (prefixPartial 13 17774) = some ⟨13, 2, 0, 45533, 17774, 3049, 16384⟩ := by
  decide +kernel

theorem context_13_17774_45533 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17774 ⟨45533, by decide⟩ :=
  accepted_of_selected 13 17774 ⟨45533, by decide⟩ ⟨13, 2, 0, 45533, 17774, 3049, 16384⟩
    (by decide) selected_cut_01220

theorem selected_cut_01221 : selected 8 ⟨45546, by decide⟩
    (prefixPartial 13 17775) = some ⟨13, 2, 0, 45546, 17775, 1337, 16384⟩ := by
  decide +kernel

theorem context_13_17775_45546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17775 ⟨45546, by decide⟩ :=
  accepted_of_selected 13 17775 ⟨45546, by decide⟩ ⟨13, 2, 0, 45546, 17775, 1337, 16384⟩
    (by decide) selected_cut_01221

theorem unmarked_context_12_4443_45547 : frontier 9 ⟨45547, by decide⟩
    (prefixCache 12 4443) (prefixPartial 12 4443) = false := by
  decide +kernel

theorem node_context_12_4443_45547 : EJMOriginalGlobalDAGData.nodes 9 ⟨45547, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨45474, by decide⟩,⟨45533, by decide⟩,⟨45546, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4443_45547 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4443 ⟨45547, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4443
    ⟨45547, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨45474, by decide⟩,⟨45533, by decide⟩,⟨45546, by decide⟩]) unmarked_context_12_4443_45547 node_context_12_4443_45547
  intro a
  fin_cases a
  · exact context_13_17772_3444
  · exact context_13_17773_45474
  · exact context_13_17774_45533
  · exact context_13_17775_45546

theorem unmarked_context_11_1110_45548 : frontier 10 ⟨45548, by decide⟩
    (prefixCache 11 1110) (prefixPartial 11 1110) = false := by
  decide +kernel

theorem node_context_11_1110_45548 : EJMOriginalGlobalDAGData.nodes 10 ⟨45548, by decide⟩ =
    .split (coordinate 11) (![⟨45292, by decide⟩,⟨45372, by decide⟩,⟨45450, by decide⟩,⟨45547, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1110_45548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1110 ⟨45548, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1110
    ⟨45548, by decide⟩ (by decide) (![⟨45292, by decide⟩,⟨45372, by decide⟩,⟨45450, by decide⟩,⟨45547, by decide⟩]) unmarked_context_11_1110_45548 node_context_11_1110_45548
  intro a
  fin_cases a
  · exact context_12_4440_45292
  · exact context_12_4441_45372
  · exact context_12_4442_45450
  · exact context_12_4443_45547

theorem selected_cut_01222 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 1111) = some ⟨11, 1, 0, 1736, 1111, 1, 262144⟩ := by
  decide +kernel

theorem context_11_1111_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1111 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 1111 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 1111, 1, 262144⟩
    (by decide) selected_cut_01222

theorem unmarked_context_10_277_45549 : frontier 11 ⟨45549, by decide⟩
    (prefixCache 10 277) (prefixPartial 10 277) = false := by
  decide +kernel

theorem node_context_10_277_45549 : EJMOriginalGlobalDAGData.nodes 11 ⟨45549, by decide⟩ =
    .split (coordinate 10) (![⟨45044, by decide⟩,⟨45226, by decide⟩,⟨45548, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_277_45549 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 277 ⟨45549, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 277
    ⟨45549, by decide⟩ (by decide) (![⟨45044, by decide⟩,⟨45226, by decide⟩,⟨45548, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_277_45549 node_context_10_277_45549
  intro a
  fin_cases a
  · exact context_11_1108_45044
  · exact context_11_1109_45226
  · exact context_11_1110_45548
  · exact context_11_1111_1736

theorem selected_cut_01223 : selected 9 ⟨45601, by decide⟩
    (prefixPartial 12 4448) = some ⟨12, 2, 0, 45601, 4448, 3265, 65536⟩ := by
  decide +kernel

theorem context_12_4448_45601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4448 ⟨45601, by decide⟩ :=
  accepted_of_selected 12 4448 ⟨45601, by decide⟩ ⟨12, 2, 0, 45601, 4448, 3265, 65536⟩
    (by decide) selected_cut_01223

theorem selected_cut_01224 : selected 9 ⟨45652, by decide⟩
    (prefixPartial 12 4449) = some ⟨12, 2, 0, 45652, 4449, 3905, 65536⟩ := by
  decide +kernel

theorem context_12_4449_45652 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4449 ⟨45652, by decide⟩ :=
  accepted_of_selected 12 4449 ⟨45652, by decide⟩ ⟨12, 2, 0, 45652, 4449, 3905, 65536⟩
    (by decide) selected_cut_01224

theorem selected_cut_01225 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 17800) = some ⟨13, 1, 0, 3444, 17800, 1, 16384⟩ := by
  decide +kernel

theorem context_13_17800_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17800 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 17800 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 17800, 1, 16384⟩
    (by decide) selected_cut_01225

theorem selected_cut_01226 : selected 8 ⟨45676, by decide⟩
    (prefixPartial 13 17801) = some ⟨13, 2, 0, 45676, 17801, 1573, 16384⟩ := by
  decide +kernel

theorem context_13_17801_45676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17801 ⟨45676, by decide⟩ :=
  accepted_of_selected 13 17801 ⟨45676, by decide⟩ ⟨13, 2, 0, 45676, 17801, 1573, 16384⟩
    (by decide) selected_cut_01226

theorem selected_cut_01227 : selected 8 ⟨45707, by decide⟩
    (prefixPartial 13 17802) = some ⟨13, 2, 0, 45707, 17802, 2105, 16384⟩ := by
  decide +kernel

theorem context_13_17802_45707 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17802 ⟨45707, by decide⟩ :=
  accepted_of_selected 13 17802 ⟨45707, by decide⟩ ⟨13, 2, 0, 45707, 17802, 2105, 16384⟩
    (by decide) selected_cut_01227

theorem selected_cut_01228 : selected 8 ⟨45722, by decide⟩
    (prefixPartial 13 17803) = some ⟨13, 2, 0, 45722, 17803, 1205, 16384⟩ := by
  decide +kernel

theorem context_13_17803_45722 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17803 ⟨45722, by decide⟩ :=
  accepted_of_selected 13 17803 ⟨45722, by decide⟩ ⟨13, 2, 0, 45722, 17803, 1205, 16384⟩
    (by decide) selected_cut_01228

theorem unmarked_context_12_4450_45723 : frontier 9 ⟨45723, by decide⟩
    (prefixCache 12 4450) (prefixPartial 12 4450) = false := by
  decide +kernel

theorem node_context_12_4450_45723 : EJMOriginalGlobalDAGData.nodes 9 ⟨45723, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨45676, by decide⟩,⟨45707, by decide⟩,⟨45722, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4450_45723 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4450 ⟨45723, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4450
    ⟨45723, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨45676, by decide⟩,⟨45707, by decide⟩,⟨45722, by decide⟩]) unmarked_context_12_4450_45723 node_context_12_4450_45723
  intro a
  fin_cases a
  · exact context_13_17800_3444
  · exact context_13_17801_45676
  · exact context_13_17802_45707
  · exact context_13_17803_45722

theorem selected_cut_01229 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 17804) = some ⟨13, 1, 0, 3444, 17804, 1, 16384⟩ := by
  decide +kernel

theorem context_13_17804_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17804 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 17804 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 17804, 1, 16384⟩
    (by decide) selected_cut_01229

theorem selected_cut_01230 : selected 8 ⟨45743, by decide⟩
    (prefixPartial 13 17805) = some ⟨13, 2, 0, 45743, 17805, 1473, 16384⟩ := by
  decide +kernel

theorem context_13_17805_45743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17805 ⟨45743, by decide⟩ :=
  accepted_of_selected 13 17805 ⟨45743, by decide⟩ ⟨13, 2, 0, 45743, 17805, 1473, 16384⟩
    (by decide) selected_cut_01230

theorem selected_cut_01231 : selected 8 ⟨45774, by decide⟩
    (prefixPartial 13 17806) = some ⟨13, 2, 0, 45774, 17806, 2097, 16384⟩ := by
  decide +kernel

theorem context_13_17806_45774 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17806 ⟨45774, by decide⟩ :=
  accepted_of_selected 13 17806 ⟨45774, by decide⟩ ⟨13, 2, 0, 45774, 17806, 2097, 16384⟩
    (by decide) selected_cut_01231

theorem selected_cut_01232 : selected 8 ⟨45791, by decide⟩
    (prefixPartial 13 17807) = some ⟨13, 2, 0, 45791, 17807, 1169, 16384⟩ := by
  decide +kernel

theorem context_13_17807_45791 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17807 ⟨45791, by decide⟩ :=
  accepted_of_selected 13 17807 ⟨45791, by decide⟩ ⟨13, 2, 0, 45791, 17807, 1169, 16384⟩
    (by decide) selected_cut_01232

theorem unmarked_context_12_4451_45792 : frontier 9 ⟨45792, by decide⟩
    (prefixCache 12 4451) (prefixPartial 12 4451) = false := by
  decide +kernel

theorem node_context_12_4451_45792 : EJMOriginalGlobalDAGData.nodes 9 ⟨45792, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨45743, by decide⟩,⟨45774, by decide⟩,⟨45791, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4451_45792 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4451 ⟨45792, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4451
    ⟨45792, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨45743, by decide⟩,⟨45774, by decide⟩,⟨45791, by decide⟩]) unmarked_context_12_4451_45792 node_context_12_4451_45792
  intro a
  fin_cases a
  · exact context_13_17804_3444
  · exact context_13_17805_45743
  · exact context_13_17806_45774
  · exact context_13_17807_45791

theorem unmarked_context_11_1112_45793 : frontier 10 ⟨45793, by decide⟩
    (prefixCache 11 1112) (prefixPartial 11 1112) = false := by
  decide +kernel

theorem node_context_11_1112_45793 : EJMOriginalGlobalDAGData.nodes 10 ⟨45793, by decide⟩ =
    .split (coordinate 11) (![⟨45601, by decide⟩,⟨45652, by decide⟩,⟨45723, by decide⟩,⟨45792, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1112_45793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1112 ⟨45793, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1112
    ⟨45793, by decide⟩ (by decide) (![⟨45601, by decide⟩,⟨45652, by decide⟩,⟨45723, by decide⟩,⟨45792, by decide⟩]) unmarked_context_11_1112_45793 node_context_11_1112_45793
  intro a
  fin_cases a
  · exact context_12_4448_45601
  · exact context_12_4449_45652
  · exact context_12_4450_45723
  · exact context_12_4451_45792

theorem selected_cut_01233 : selected 9 ⟨45853, by decide⟩
    (prefixPartial 12 4452) = some ⟨12, 2, 0, 45853, 4452, 3677, 65536⟩ := by
  decide +kernel

theorem context_12_4452_45853 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4452 ⟨45853, by decide⟩ :=
  accepted_of_selected 12 4452 ⟨45853, by decide⟩ ⟨12, 2, 0, 45853, 4452, 3677, 65536⟩
    (by decide) selected_cut_01233

theorem selected_cut_01234 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 17812) = some ⟨13, 1, 0, 3444, 17812, 1, 16384⟩ := by
  decide +kernel

theorem context_13_17812_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17812 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 17812 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 17812, 1, 16384⟩
    (by decide) selected_cut_01234

theorem selected_cut_01235 : selected 8 ⟨45887, by decide⟩
    (prefixPartial 13 17813) = some ⟨13, 2, 0, 45887, 17813, 1957, 16384⟩ := by
  decide +kernel

theorem context_13_17813_45887 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17813 ⟨45887, by decide⟩ :=
  accepted_of_selected 13 17813 ⟨45887, by decide⟩ ⟨13, 2, 0, 45887, 17813, 1957, 16384⟩
    (by decide) selected_cut_01235

theorem selected_cut_01236 : selected 8 ⟨45940, by decide⟩
    (prefixPartial 13 17814) = some ⟨13, 2, 0, 45940, 17814, 3089, 16384⟩ := by
  decide +kernel

theorem context_13_17814_45940 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17814 ⟨45940, by decide⟩ :=
  accepted_of_selected 13 17814 ⟨45940, by decide⟩ ⟨13, 2, 0, 45940, 17814, 3089, 16384⟩
    (by decide) selected_cut_01236

theorem selected_cut_01237 : selected 8 ⟨45969, by decide⟩
    (prefixPartial 13 17815) = some ⟨13, 2, 0, 45969, 17815, 1677, 16384⟩ := by
  decide +kernel

theorem context_13_17815_45969 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17815 ⟨45969, by decide⟩ :=
  accepted_of_selected 13 17815 ⟨45969, by decide⟩ ⟨13, 2, 0, 45969, 17815, 1677, 16384⟩
    (by decide) selected_cut_01237

theorem unmarked_context_12_4453_45970 : frontier 9 ⟨45970, by decide⟩
    (prefixCache 12 4453) (prefixPartial 12 4453) = false := by
  decide +kernel

theorem node_context_12_4453_45970 : EJMOriginalGlobalDAGData.nodes 9 ⟨45970, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨45887, by decide⟩,⟨45940, by decide⟩,⟨45969, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4453_45970 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4453 ⟨45970, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4453
    ⟨45970, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨45887, by decide⟩,⟨45940, by decide⟩,⟨45969, by decide⟩]) unmarked_context_12_4453_45970 node_context_12_4453_45970
  intro a
  fin_cases a
  · exact context_13_17812_3444
  · exact context_13_17813_45887
  · exact context_13_17814_45940
  · exact context_13_17815_45969

theorem selected_cut_01238 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 17816) = some ⟨13, 1, 0, 3444, 17816, 1, 16384⟩ := by
  decide +kernel

theorem context_13_17816_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17816 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 17816 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 17816, 1, 16384⟩
    (by decide) selected_cut_01238

theorem selected_cut_01239 : selected 8 ⟨45992, by decide⟩
    (prefixPartial 13 17817) = some ⟨13, 2, 0, 45992, 17817, 1173, 16384⟩ := by
  decide +kernel

theorem context_13_17817_45992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17817 ⟨45992, by decide⟩ :=
  accepted_of_selected 13 17817 ⟨45992, by decide⟩ ⟨13, 2, 0, 45992, 17817, 1173, 16384⟩
    (by decide) selected_cut_01239

theorem selected_cut_01240 : selected 8 ⟨46025, by decide⟩
    (prefixPartial 13 17818) = some ⟨13, 2, 0, 46025, 17818, 2421, 16384⟩ := by
  decide +kernel

theorem context_13_17818_46025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17818 ⟨46025, by decide⟩ :=
  accepted_of_selected 13 17818 ⟨46025, by decide⟩ ⟨13, 2, 0, 46025, 17818, 2421, 16384⟩
    (by decide) selected_cut_01240

theorem selected_cut_01241 : selected 8 ⟨46038, by decide⟩
    (prefixPartial 13 17819) = some ⟨13, 2, 0, 46038, 17819, 1373, 16384⟩ := by
  decide +kernel

theorem context_13_17819_46038 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17819 ⟨46038, by decide⟩ :=
  accepted_of_selected 13 17819 ⟨46038, by decide⟩ ⟨13, 2, 0, 46038, 17819, 1373, 16384⟩
    (by decide) selected_cut_01241

theorem unmarked_context_12_4454_46039 : frontier 9 ⟨46039, by decide⟩
    (prefixCache 12 4454) (prefixPartial 12 4454) = false := by
  decide +kernel

theorem node_context_12_4454_46039 : EJMOriginalGlobalDAGData.nodes 9 ⟨46039, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨45992, by decide⟩,⟨46025, by decide⟩,⟨46038, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4454_46039 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4454 ⟨46039, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4454
    ⟨46039, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨45992, by decide⟩,⟨46025, by decide⟩,⟨46038, by decide⟩]) unmarked_context_12_4454_46039 node_context_12_4454_46039
  intro a
  fin_cases a
  · exact context_13_17816_3444
  · exact context_13_17817_45992
  · exact context_13_17818_46025
  · exact context_13_17819_46038

theorem selected_cut_01242 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 17820) = some ⟨13, 1, 0, 3444, 17820, 1, 16384⟩ := by
  decide +kernel

theorem context_13_17820_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17820 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 17820 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 17820, 1, 16384⟩
    (by decide) selected_cut_01242

theorem selected_cut_01243 : selected 8 ⟨46051, by decide⟩
    (prefixPartial 13 17821) = some ⟨13, 2, 0, 46051, 17821, 993, 16384⟩ := by
  decide +kernel

theorem context_13_17821_46051 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17821 ⟨46051, by decide⟩ :=
  accepted_of_selected 13 17821 ⟨46051, by decide⟩ ⟨13, 2, 0, 46051, 17821, 993, 16384⟩
    (by decide) selected_cut_01243

theorem selected_cut_01244 : selected 8 ⟨46084, by decide⟩
    (prefixPartial 13 17822) = some ⟨13, 2, 0, 46084, 17822, 2353, 16384⟩ := by
  decide +kernel

theorem context_13_17822_46084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17822 ⟨46084, by decide⟩ :=
  accepted_of_selected 13 17822 ⟨46084, by decide⟩ ⟨13, 2, 0, 46084, 17822, 2353, 16384⟩
    (by decide) selected_cut_01244

theorem selected_cut_01245 : selected 8 ⟨46099, by decide⟩
    (prefixPartial 13 17823) = some ⟨13, 2, 0, 46099, 17823, 1321, 16384⟩ := by
  decide +kernel

theorem context_13_17823_46099 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17823 ⟨46099, by decide⟩ :=
  accepted_of_selected 13 17823 ⟨46099, by decide⟩ ⟨13, 2, 0, 46099, 17823, 1321, 16384⟩
    (by decide) selected_cut_01245

theorem unmarked_context_12_4455_46100 : frontier 9 ⟨46100, by decide⟩
    (prefixCache 12 4455) (prefixPartial 12 4455) = false := by
  decide +kernel

theorem node_context_12_4455_46100 : EJMOriginalGlobalDAGData.nodes 9 ⟨46100, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨46051, by decide⟩,⟨46084, by decide⟩,⟨46099, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_4455_46100 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4455 ⟨46100, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 4455
    ⟨46100, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨46051, by decide⟩,⟨46084, by decide⟩,⟨46099, by decide⟩]) unmarked_context_12_4455_46100 node_context_12_4455_46100
  intro a
  fin_cases a
  · exact context_13_17820_3444
  · exact context_13_17821_46051
  · exact context_13_17822_46084
  · exact context_13_17823_46099

theorem unmarked_context_11_1113_46101 : frontier 10 ⟨46101, by decide⟩
    (prefixCache 11 1113) (prefixPartial 11 1113) = false := by
  decide +kernel

theorem node_context_11_1113_46101 : EJMOriginalGlobalDAGData.nodes 10 ⟨46101, by decide⟩ =
    .split (coordinate 11) (![⟨45853, by decide⟩,⟨45970, by decide⟩,⟨46039, by decide⟩,⟨46100, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1113_46101 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1113 ⟨46101, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1113
    ⟨46101, by decide⟩ (by decide) (![⟨45853, by decide⟩,⟨45970, by decide⟩,⟨46039, by decide⟩,⟨46100, by decide⟩]) unmarked_context_11_1113_46101 node_context_11_1113_46101
  intro a
  fin_cases a
  · exact context_12_4452_45853
  · exact context_12_4453_45970
  · exact context_12_4454_46039
  · exact context_12_4455_46100

theorem selected_cut_01246 : selected 9 ⟨46152, by decide⟩
    (prefixPartial 12 4456) = some ⟨12, 2, 0, 46152, 4456, 3569, 65536⟩ := by
  decide +kernel

theorem context_12_4456_46152 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 4456 ⟨46152, by decide⟩ :=
  accepted_of_selected 12 4456 ⟨46152, by decide⟩ ⟨12, 2, 0, 46152, 4456, 3569, 65536⟩
    (by decide) selected_cut_01246

theorem selected_cut_01247 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 17828) = some ⟨13, 1, 0, 3444, 17828, 1, 16384⟩ := by
  decide +kernel

theorem context_13_17828_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17828 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 17828 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 17828, 1, 16384⟩
    (by decide) selected_cut_01247

theorem selected_cut_01248 : selected 8 ⟨46165, by decide⟩
    (prefixPartial 13 17829) = some ⟨13, 2, 0, 46165, 17829, 649, 16384⟩ := by
  decide +kernel

theorem context_13_17829_46165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17829 ⟨46165, by decide⟩ :=
  accepted_of_selected 13 17829 ⟨46165, by decide⟩ ⟨13, 2, 0, 46165, 17829, 649, 16384⟩
    (by decide) selected_cut_01248

theorem selected_cut_01249 : selected 8 ⟨46191, by decide⟩
    (prefixPartial 13 17830) = some ⟨13, 2, 0, 46191, 17830, 2129, 16384⟩ := by
  decide +kernel

theorem context_13_17830_46191 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17830 ⟨46191, by decide⟩ :=
  accepted_of_selected 13 17830 ⟨46191, by decide⟩ ⟨13, 2, 0, 46191, 17830, 2129, 16384⟩
    (by decide) selected_cut_01249

theorem selected_cut_01250 : selected 8 ⟨46207, by decide⟩
    (prefixPartial 13 17831) = some ⟨13, 2, 0, 46207, 17831, 1345, 16384⟩ := by
  decide +kernel

theorem context_13_17831_46207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 17831 ⟨46207, by decide⟩ :=
  accepted_of_selected 13 17831 ⟨46207, by decide⟩ ⟨13, 2, 0, 46207, 17831, 1345, 16384⟩
    (by decide) selected_cut_01250

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
