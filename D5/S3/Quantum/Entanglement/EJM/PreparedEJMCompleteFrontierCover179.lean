/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover178
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_17186 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 69719) = some ⟨12, 1, 0, 893, 69719, 1, 65536⟩ := by
  decide +kernel

theorem context_12_69719_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69719 ⟨893, by decide⟩ :=
  accepted_of_selected 12 69719 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 69719, 1, 65536⟩
    (by decide) selected_cut_17186

theorem unmarked_context_11_17429_436956 : frontier 10 ⟨436956, by decide⟩
    (prefixCache 11 17429) (prefixPartial 11 17429) = false := by
  decide +kernel

theorem node_context_11_17429_436956 : EJMOriginalGlobalDAGData.nodes 10 ⟨436956, by decide⟩ =
    .split (coordinate 11) (![⟨895, by decide⟩,⟨436890, by decide⟩,⟨436955, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17429_436956 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17429 ⟨436956, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17429
    ⟨436956, by decide⟩ (by decide) (![⟨895, by decide⟩,⟨436890, by decide⟩,⟨436955, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_17429_436956 node_context_11_17429_436956
  intro a
  fin_cases a
  · exact context_12_69716_895
  · exact context_12_69717_436890
  · exact context_12_69718_436955
  · exact context_12_69719_893

theorem selected_cut_17187 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 69720) = some ⟨12, 1, 0, 895, 69720, 1, 65536⟩ := by
  decide +kernel

theorem context_12_69720_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69720 ⟨895, by decide⟩ :=
  accepted_of_selected 12 69720 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 69720, 1, 65536⟩
    (by decide) selected_cut_17187

theorem selected_cut_17188 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 69721) = some ⟨12, 1, 0, 895, 69721, 1, 65536⟩ := by
  decide +kernel

theorem context_12_69721_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69721 ⟨895, by decide⟩ :=
  accepted_of_selected 12 69721 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 69721, 1, 65536⟩
    (by decide) selected_cut_17188

theorem selected_cut_17189 : selected 9 ⟨437011, by decide⟩
    (prefixPartial 12 69722) = some ⟨12, 2, 0, 437011, 69722, 2305, 65536⟩ := by
  decide +kernel

theorem context_12_69722_437011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69722 ⟨437011, by decide⟩ :=
  accepted_of_selected 12 69722 ⟨437011, by decide⟩ ⟨12, 2, 0, 437011, 69722, 2305, 65536⟩
    (by decide) selected_cut_17189

theorem selected_cut_17190 : selected 9 ⟨437060, by decide⟩
    (prefixPartial 12 69723) = some ⟨12, 2, 0, 437060, 69723, 2293, 65536⟩ := by
  decide +kernel

theorem context_12_69723_437060 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69723 ⟨437060, by decide⟩ :=
  accepted_of_selected 12 69723 ⟨437060, by decide⟩ ⟨12, 2, 0, 437060, 69723, 2293, 65536⟩
    (by decide) selected_cut_17190

theorem unmarked_context_11_17430_437061 : frontier 10 ⟨437061, by decide⟩
    (prefixCache 11 17430) (prefixPartial 11 17430) = false := by
  decide +kernel

theorem node_context_11_17430_437061 : EJMOriginalGlobalDAGData.nodes 10 ⟨437061, by decide⟩ =
    .split (coordinate 11) (![⟨895, by decide⟩,⟨895, by decide⟩,⟨437011, by decide⟩,⟨437060, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17430_437061 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17430 ⟨437061, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17430
    ⟨437061, by decide⟩ (by decide) (![⟨895, by decide⟩,⟨895, by decide⟩,⟨437011, by decide⟩,⟨437060, by decide⟩]) unmarked_context_11_17430_437061 node_context_11_17430_437061
  intro a
  fin_cases a
  · exact context_12_69720_895
  · exact context_12_69721_895
  · exact context_12_69722_437011
  · exact context_12_69723_437060

theorem selected_cut_17191 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 17431) = some ⟨11, 1, 0, 1736, 17431, 1, 262144⟩ := by
  decide +kernel

theorem context_11_17431_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17431 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 17431 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 17431, 1, 262144⟩
    (by decide) selected_cut_17191

theorem unmarked_context_10_4357_437062 : frontier 11 ⟨437062, by decide⟩
    (prefixCache 10 4357) (prefixPartial 10 4357) = false := by
  decide +kernel

theorem node_context_10_4357_437062 : EJMOriginalGlobalDAGData.nodes 11 ⟨437062, by decide⟩ =
    .split (coordinate 10) (![⟨436856, by decide⟩,⟨436956, by decide⟩,⟨437061, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4357_437062 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4357 ⟨437062, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4357
    ⟨437062, by decide⟩ (by decide) (![⟨436856, by decide⟩,⟨436956, by decide⟩,⟨437061, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_4357_437062 node_context_10_4357_437062
  intro a
  fin_cases a
  · exact context_11_17428_436856
  · exact context_11_17429_436956
  · exact context_11_17430_437061
  · exact context_11_17431_1736

theorem selected_cut_17192 : selected 9 ⟨437132, by decide⟩
    (prefixPartial 12 69728) = some ⟨12, 2, 0, 437132, 69728, 3913, 65536⟩ := by
  decide +kernel

theorem context_12_69728_437132 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69728 ⟨437132, by decide⟩ :=
  accepted_of_selected 12 69728 ⟨437132, by decide⟩ ⟨12, 2, 0, 437132, 69728, 3913, 65536⟩
    (by decide) selected_cut_17192

theorem selected_cut_17193 : selected 9 ⟨437187, by decide⟩
    (prefixPartial 12 69729) = some ⟨12, 2, 0, 437187, 69729, 2949, 65536⟩ := by
  decide +kernel

theorem context_12_69729_437187 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69729 ⟨437187, by decide⟩ :=
  accepted_of_selected 12 69729 ⟨437187, by decide⟩ ⟨12, 2, 0, 437187, 69729, 2949, 65536⟩
    (by decide) selected_cut_17193

theorem selected_cut_17194 : selected 9 ⟨437244, by decide⟩
    (prefixPartial 12 69730) = some ⟨12, 2, 0, 437244, 69730, 2829, 65536⟩ := by
  decide +kernel

theorem context_12_69730_437244 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69730 ⟨437244, by decide⟩ :=
  accepted_of_selected 12 69730 ⟨437244, by decide⟩ ⟨12, 2, 0, 437244, 69730, 2829, 65536⟩
    (by decide) selected_cut_17194

theorem selected_cut_17195 : selected 9 ⟨437285, by decide⟩
    (prefixPartial 12 69731) = some ⟨12, 2, 0, 437285, 69731, 2765, 65536⟩ := by
  decide +kernel

theorem context_12_69731_437285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69731 ⟨437285, by decide⟩ :=
  accepted_of_selected 12 69731 ⟨437285, by decide⟩ ⟨12, 2, 0, 437285, 69731, 2765, 65536⟩
    (by decide) selected_cut_17195

theorem unmarked_context_11_17432_437286 : frontier 10 ⟨437286, by decide⟩
    (prefixCache 11 17432) (prefixPartial 11 17432) = false := by
  decide +kernel

theorem node_context_11_17432_437286 : EJMOriginalGlobalDAGData.nodes 10 ⟨437286, by decide⟩ =
    .split (coordinate 11) (![⟨437132, by decide⟩,⟨437187, by decide⟩,⟨437244, by decide⟩,⟨437285, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17432_437286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17432 ⟨437286, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17432
    ⟨437286, by decide⟩ (by decide) (![⟨437132, by decide⟩,⟨437187, by decide⟩,⟨437244, by decide⟩,⟨437285, by decide⟩]) unmarked_context_11_17432_437286 node_context_11_17432_437286
  intro a
  fin_cases a
  · exact context_12_69728_437132
  · exact context_12_69729_437187
  · exact context_12_69730_437244
  · exact context_12_69731_437285

theorem selected_cut_17196 : selected 9 ⟨437332, by decide⟩
    (prefixPartial 12 69732) = some ⟨12, 2, 0, 437332, 69732, 2461, 65536⟩ := by
  decide +kernel

theorem context_12_69732_437332 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69732 ⟨437332, by decide⟩ :=
  accepted_of_selected 12 69732 ⟨437332, by decide⟩ ⟨12, 2, 0, 437332, 69732, 2461, 65536⟩
    (by decide) selected_cut_17196

theorem selected_cut_17197 : selected 9 ⟨437375, by decide⟩
    (prefixPartial 12 69733) = some ⟨12, 2, 0, 437375, 69733, 2581, 65536⟩ := by
  decide +kernel

theorem context_12_69733_437375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69733 ⟨437375, by decide⟩ :=
  accepted_of_selected 12 69733 ⟨437375, by decide⟩ ⟨12, 2, 0, 437375, 69733, 2581, 65536⟩
    (by decide) selected_cut_17197

theorem selected_cut_17198 : selected 9 ⟨437423, by decide⟩
    (prefixPartial 12 69734) = some ⟨12, 2, 0, 437423, 69734, 2553, 65536⟩ := by
  decide +kernel

theorem context_12_69734_437423 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69734 ⟨437423, by decide⟩ :=
  accepted_of_selected 12 69734 ⟨437423, by decide⟩ ⟨12, 2, 0, 437423, 69734, 2553, 65536⟩
    (by decide) selected_cut_17198

theorem selected_cut_17199 : selected 9 ⟨437464, by decide⟩
    (prefixPartial 12 69735) = some ⟨12, 2, 0, 437464, 69735, 2501, 65536⟩ := by
  decide +kernel

theorem context_12_69735_437464 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69735 ⟨437464, by decide⟩ :=
  accepted_of_selected 12 69735 ⟨437464, by decide⟩ ⟨12, 2, 0, 437464, 69735, 2501, 65536⟩
    (by decide) selected_cut_17199

theorem unmarked_context_11_17433_437465 : frontier 10 ⟨437465, by decide⟩
    (prefixCache 11 17433) (prefixPartial 11 17433) = false := by
  decide +kernel

theorem node_context_11_17433_437465 : EJMOriginalGlobalDAGData.nodes 10 ⟨437465, by decide⟩ =
    .split (coordinate 11) (![⟨437332, by decide⟩,⟨437375, by decide⟩,⟨437423, by decide⟩,⟨437464, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17433_437465 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17433 ⟨437465, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17433
    ⟨437465, by decide⟩ (by decide) (![⟨437332, by decide⟩,⟨437375, by decide⟩,⟨437423, by decide⟩,⟨437464, by decide⟩]) unmarked_context_11_17433_437465 node_context_11_17433_437465
  intro a
  fin_cases a
  · exact context_12_69732_437332
  · exact context_12_69733_437375
  · exact context_12_69734_437423
  · exact context_12_69735_437464

theorem selected_cut_17200 : selected 9 ⟨437499, by decide⟩
    (prefixPartial 12 69736) = some ⟨12, 2, 0, 437499, 69736, 2289, 65536⟩ := by
  decide +kernel

theorem context_12_69736_437499 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69736 ⟨437499, by decide⟩ :=
  accepted_of_selected 12 69736 ⟨437499, by decide⟩ ⟨12, 2, 0, 437499, 69736, 2289, 65536⟩
    (by decide) selected_cut_17200

theorem selected_cut_17201 : selected 9 ⟨437545, by decide⟩
    (prefixPartial 12 69737) = some ⟨12, 2, 0, 437545, 69737, 2529, 65536⟩ := by
  decide +kernel

theorem context_12_69737_437545 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69737 ⟨437545, by decide⟩ :=
  accepted_of_selected 12 69737 ⟨437545, by decide⟩ ⟨12, 2, 0, 437545, 69737, 2529, 65536⟩
    (by decide) selected_cut_17201

theorem selected_cut_17202 : selected 9 ⟨437585, by decide⟩
    (prefixPartial 12 69738) = some ⟨12, 2, 0, 437585, 69738, 2145, 65536⟩ := by
  decide +kernel

theorem context_12_69738_437585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69738 ⟨437585, by decide⟩ :=
  accepted_of_selected 12 69738 ⟨437585, by decide⟩ ⟨12, 2, 0, 437585, 69738, 2145, 65536⟩
    (by decide) selected_cut_17202

theorem selected_cut_17203 : selected 9 ⟨437617, by decide⟩
    (prefixPartial 12 69739) = some ⟨12, 2, 0, 437617, 69739, 2165, 65536⟩ := by
  decide +kernel

theorem context_12_69739_437617 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69739 ⟨437617, by decide⟩ :=
  accepted_of_selected 12 69739 ⟨437617, by decide⟩ ⟨12, 2, 0, 437617, 69739, 2165, 65536⟩
    (by decide) selected_cut_17203

theorem unmarked_context_11_17434_437618 : frontier 10 ⟨437618, by decide⟩
    (prefixCache 11 17434) (prefixPartial 11 17434) = false := by
  decide +kernel

theorem node_context_11_17434_437618 : EJMOriginalGlobalDAGData.nodes 10 ⟨437618, by decide⟩ =
    .split (coordinate 11) (![⟨437499, by decide⟩,⟨437545, by decide⟩,⟨437585, by decide⟩,⟨437617, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17434_437618 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17434 ⟨437618, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17434
    ⟨437618, by decide⟩ (by decide) (![⟨437499, by decide⟩,⟨437545, by decide⟩,⟨437585, by decide⟩,⟨437617, by decide⟩]) unmarked_context_11_17434_437618 node_context_11_17434_437618
  intro a
  fin_cases a
  · exact context_12_69736_437499
  · exact context_12_69737_437545
  · exact context_12_69738_437585
  · exact context_12_69739_437617

theorem selected_cut_17204 : selected 9 ⟨437656, by decide⟩
    (prefixPartial 12 69740) = some ⟨12, 2, 0, 437656, 69740, 1745, 65536⟩ := by
  decide +kernel

theorem context_12_69740_437656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69740 ⟨437656, by decide⟩ :=
  accepted_of_selected 12 69740 ⟨437656, by decide⟩ ⟨12, 2, 0, 437656, 69740, 1745, 65536⟩
    (by decide) selected_cut_17204

theorem selected_cut_17205 : selected 9 ⟨437705, by decide⟩
    (prefixPartial 12 69741) = some ⟨12, 2, 0, 437705, 69741, 1949, 65536⟩ := by
  decide +kernel

theorem context_12_69741_437705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69741 ⟨437705, by decide⟩ :=
  accepted_of_selected 12 69741 ⟨437705, by decide⟩ ⟨12, 2, 0, 437705, 69741, 1949, 65536⟩
    (by decide) selected_cut_17205

theorem selected_cut_17206 : selected 9 ⟨437749, by decide⟩
    (prefixPartial 12 69742) = some ⟨12, 2, 0, 437749, 69742, 1657, 65536⟩ := by
  decide +kernel

theorem context_12_69742_437749 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69742 ⟨437749, by decide⟩ :=
  accepted_of_selected 12 69742 ⟨437749, by decide⟩ ⟨12, 2, 0, 437749, 69742, 1657, 65536⟩
    (by decide) selected_cut_17206

theorem selected_cut_17207 : selected 9 ⟨437777, by decide⟩
    (prefixPartial 12 69743) = some ⟨12, 2, 0, 437777, 69743, 1525, 65536⟩ := by
  decide +kernel

theorem context_12_69743_437777 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69743 ⟨437777, by decide⟩ :=
  accepted_of_selected 12 69743 ⟨437777, by decide⟩ ⟨12, 2, 0, 437777, 69743, 1525, 65536⟩
    (by decide) selected_cut_17207

theorem unmarked_context_11_17435_437778 : frontier 10 ⟨437778, by decide⟩
    (prefixCache 11 17435) (prefixPartial 11 17435) = false := by
  decide +kernel

theorem node_context_11_17435_437778 : EJMOriginalGlobalDAGData.nodes 10 ⟨437778, by decide⟩ =
    .split (coordinate 11) (![⟨437656, by decide⟩,⟨437705, by decide⟩,⟨437749, by decide⟩,⟨437777, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17435_437778 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17435 ⟨437778, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17435
    ⟨437778, by decide⟩ (by decide) (![⟨437656, by decide⟩,⟨437705, by decide⟩,⟨437749, by decide⟩,⟨437777, by decide⟩]) unmarked_context_11_17435_437778 node_context_11_17435_437778
  intro a
  fin_cases a
  · exact context_12_69740_437656
  · exact context_12_69741_437705
  · exact context_12_69742_437749
  · exact context_12_69743_437777

theorem unmarked_context_10_4358_437779 : frontier 11 ⟨437779, by decide⟩
    (prefixCache 10 4358) (prefixPartial 10 4358) = false := by
  decide +kernel

theorem node_context_10_4358_437779 : EJMOriginalGlobalDAGData.nodes 11 ⟨437779, by decide⟩ =
    .split (coordinate 10) (![⟨437286, by decide⟩,⟨437465, by decide⟩,⟨437618, by decide⟩,⟨437778, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4358_437779 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4358 ⟨437779, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4358
    ⟨437779, by decide⟩ (by decide) (![⟨437286, by decide⟩,⟨437465, by decide⟩,⟨437618, by decide⟩,⟨437778, by decide⟩]) unmarked_context_10_4358_437779 node_context_10_4358_437779
  intro a
  fin_cases a
  · exact context_11_17432_437286
  · exact context_11_17433_437465
  · exact context_11_17434_437618
  · exact context_11_17435_437778

theorem selected_cut_17208 : selected 11 ⟨3440, by decide⟩
    (prefixPartial 10 4359) = some ⟨10, 1, 0, 3440, 4359, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_4359_3440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4359 ⟨3440, by decide⟩ :=
  accepted_of_selected 10 4359 ⟨3440, by decide⟩ ⟨10, 1, 0, 3440, 4359, 1, 1048576⟩
    (by decide) selected_cut_17208

theorem unmarked_context_9_1089_437780 : frontier 12 ⟨437780, by decide⟩
    (prefixCache 9 1089) (prefixPartial 9 1089) = false := by
  decide +kernel

theorem node_context_9_1089_437780 : EJMOriginalGlobalDAGData.nodes 12 ⟨437780, by decide⟩ =
    .split (coordinate 9) (![⟨3442, by decide⟩,⟨437062, by decide⟩,⟨437779, by decide⟩,⟨3440, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1089_437780 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1089 ⟨437780, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1089
    ⟨437780, by decide⟩ (by decide) (![⟨3442, by decide⟩,⟨437062, by decide⟩,⟨437779, by decide⟩,⟨3440, by decide⟩]) unmarked_context_9_1089_437780 node_context_9_1089_437780
  intro a
  fin_cases a
  · exact context_10_4356_3442
  · exact context_10_4357_437062
  · exact context_10_4358_437779
  · exact context_10_4359_3440

theorem selected_cut_17209 : selected 11 ⟨3442, by decide⟩
    (prefixPartial 10 4360) = some ⟨10, 1, 0, 3442, 4360, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_4360_3442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4360 ⟨3442, by decide⟩ :=
  accepted_of_selected 10 4360 ⟨3442, by decide⟩ ⟨10, 1, 0, 3442, 4360, 1, 1048576⟩
    (by decide) selected_cut_17209

theorem selected_cut_17210 : selected 11 ⟨3442, by decide⟩
    (prefixPartial 10 4361) = some ⟨10, 1, 0, 3442, 4361, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_4361_3442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4361 ⟨3442, by decide⟩ :=
  accepted_of_selected 10 4361 ⟨3442, by decide⟩ ⟨10, 1, 0, 3442, 4361, 1, 1048576⟩
    (by decide) selected_cut_17210

theorem selected_cut_17211 : selected 10 ⟨437840, by decide⟩
    (prefixPartial 11 17448) = some ⟨11, 2, 0, 437840, 17448, 2425, 262144⟩ := by
  decide +kernel

theorem context_11_17448_437840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17448 ⟨437840, by decide⟩ :=
  accepted_of_selected 11 17448 ⟨437840, by decide⟩ ⟨11, 2, 0, 437840, 17448, 2425, 262144⟩
    (by decide) selected_cut_17211

theorem selected_cut_17212 : selected 10 ⟨437893, by decide⟩
    (prefixPartial 11 17449) = some ⟨11, 2, 0, 437893, 17449, 1997, 262144⟩ := by
  decide +kernel

theorem context_11_17449_437893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17449 ⟨437893, by decide⟩ :=
  accepted_of_selected 11 17449 ⟨437893, by decide⟩ ⟨11, 2, 0, 437893, 17449, 1997, 262144⟩
    (by decide) selected_cut_17212

theorem selected_cut_17213 : selected 10 ⟨437915, by decide⟩
    (prefixPartial 11 17450) = some ⟨11, 2, 0, 437915, 17450, 933, 262144⟩ := by
  decide +kernel

theorem context_11_17450_437915 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17450 ⟨437915, by decide⟩ :=
  accepted_of_selected 11 17450 ⟨437915, by decide⟩ ⟨11, 2, 0, 437915, 17450, 933, 262144⟩
    (by decide) selected_cut_17213

theorem selected_cut_17214 : selected 10 ⟨437922, by decide⟩
    (prefixPartial 11 17451) = some ⟨11, 2, 0, 437922, 17451, 357, 262144⟩ := by
  decide +kernel

theorem context_11_17451_437922 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17451 ⟨437922, by decide⟩ :=
  accepted_of_selected 11 17451 ⟨437922, by decide⟩ ⟨11, 2, 0, 437922, 17451, 357, 262144⟩
    (by decide) selected_cut_17214

theorem unmarked_context_10_4362_437923 : frontier 11 ⟨437923, by decide⟩
    (prefixCache 10 4362) (prefixPartial 10 4362) = false := by
  decide +kernel

theorem node_context_10_4362_437923 : EJMOriginalGlobalDAGData.nodes 11 ⟨437923, by decide⟩ =
    .split (coordinate 10) (![⟨437840, by decide⟩,⟨437893, by decide⟩,⟨437915, by decide⟩,⟨437922, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4362_437923 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4362 ⟨437923, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4362
    ⟨437923, by decide⟩ (by decide) (![⟨437840, by decide⟩,⟨437893, by decide⟩,⟨437915, by decide⟩,⟨437922, by decide⟩]) unmarked_context_10_4362_437923 node_context_10_4362_437923
  intro a
  fin_cases a
  · exact context_11_17448_437840
  · exact context_11_17449_437893
  · exact context_11_17450_437915
  · exact context_11_17451_437922

theorem selected_cut_17215 : selected 11 ⟨437994, by decide⟩
    (prefixPartial 10 4363) = some ⟨10, 2, 0, 437994, 4363, 2525, 1048576⟩ := by
  decide +kernel

theorem context_10_4363_437994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4363 ⟨437994, by decide⟩ :=
  accepted_of_selected 10 4363 ⟨437994, by decide⟩ ⟨10, 2, 0, 437994, 4363, 2525, 1048576⟩
    (by decide) selected_cut_17215

theorem unmarked_context_9_1090_437995 : frontier 12 ⟨437995, by decide⟩
    (prefixCache 9 1090) (prefixPartial 9 1090) = false := by
  decide +kernel

theorem node_context_9_1090_437995 : EJMOriginalGlobalDAGData.nodes 12 ⟨437995, by decide⟩ =
    .split (coordinate 9) (![⟨3442, by decide⟩,⟨3442, by decide⟩,⟨437923, by decide⟩,⟨437994, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1090_437995 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1090 ⟨437995, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1090
    ⟨437995, by decide⟩ (by decide) (![⟨3442, by decide⟩,⟨3442, by decide⟩,⟨437923, by decide⟩,⟨437994, by decide⟩]) unmarked_context_9_1090_437995 node_context_9_1090_437995
  intro a
  fin_cases a
  · exact context_10_4360_3442
  · exact context_10_4361_3442
  · exact context_10_4362_437923
  · exact context_10_4363_437994

theorem selected_cut_17216 : selected 12 ⟨4601, by decide⟩
    (prefixPartial 9 1091) = some ⟨9, 1, 0, 4601, 1091, 1, 4194304⟩ := by
  decide +kernel

theorem context_9_1091_4601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1091 ⟨4601, by decide⟩ :=
  accepted_of_selected 9 1091 ⟨4601, by decide⟩ ⟨9, 1, 0, 4601, 1091, 1, 4194304⟩
    (by decide) selected_cut_17216

theorem unmarked_context_8_272_437996 : frontier 13 ⟨437996, by decide⟩
    (prefixCache 8 272) (prefixPartial 8 272) = false := by
  decide +kernel

theorem node_context_8_272_437996 : EJMOriginalGlobalDAGData.nodes 13 ⟨437996, by decide⟩ =
    .split (coordinate 8) (![⟨436691, by decide⟩,⟨437780, by decide⟩,⟨437995, by decide⟩,⟨4601, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_272_437996 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 272 ⟨437996, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 272
    ⟨437996, by decide⟩ (by decide) (![⟨436691, by decide⟩,⟨437780, by decide⟩,⟨437995, by decide⟩,⟨4601, by decide⟩]) unmarked_context_8_272_437996 node_context_8_272_437996
  intro a
  fin_cases a
  · exact context_9_1088_436691
  · exact context_9_1089_437780
  · exact context_9_1090_437995
  · exact context_9_1091_4601

theorem selected_cut_17217 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 17472) = some ⟨11, 1, 0, 434745, 17472, 1, 262144⟩ := by
  decide +kernel

theorem context_11_17472_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17472 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 17472 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 17472, 1, 262144⟩
    (by decide) selected_cut_17217

theorem selected_cut_17218 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 69892) = some ⟨12, 1, 0, 895, 69892, 1, 65536⟩ := by
  decide +kernel

theorem context_12_69892_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69892 ⟨895, by decide⟩ :=
  accepted_of_selected 12 69892 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 69892, 1, 65536⟩
    (by decide) selected_cut_17218

theorem selected_cut_17219 : selected 7 ⟨438044, by decide⟩
    (prefixPartial 14 1118288) = some ⟨14, 2, 0, 438044, 1118288, 833, 4096⟩ := by
  decide +kernel

theorem context_14_1118288_438044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1118288 ⟨438044, by decide⟩ :=
  accepted_of_selected 14 1118288 ⟨438044, by decide⟩ ⟨14, 2, 0, 438044, 1118288, 833, 4096⟩
    (by decide) selected_cut_17219

theorem selected_cut_17220 : selected 7 ⟨438087, by decide⟩
    (prefixPartial 14 1118289) = some ⟨14, 2, 0, 438087, 1118289, 1045, 4096⟩ := by
  decide +kernel

theorem context_14_1118289_438087 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1118289 ⟨438087, by decide⟩ :=
  accepted_of_selected 14 1118289 ⟨438087, by decide⟩ ⟨14, 2, 0, 438087, 1118289, 1045, 4096⟩
    (by decide) selected_cut_17220

theorem selected_cut_17221 : selected 7 ⟨438156, by decide⟩
    (prefixPartial 14 1118290) = some ⟨14, 2, 0, 438156, 1118290, 2249, 4096⟩ := by
  decide +kernel

theorem context_14_1118290_438156 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1118290 ⟨438156, by decide⟩ :=
  accepted_of_selected 14 1118290 ⟨438156, by decide⟩ ⟨14, 2, 0, 438156, 1118290, 2249, 4096⟩
    (by decide) selected_cut_17221

theorem selected_cut_17222 : selected 7 ⟨291, by decide⟩
    (prefixPartial 14 1118291) = some ⟨14, 1, 0, 291, 1118291, 1, 4096⟩ := by
  decide +kernel

theorem context_14_1118291_291 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1118291 ⟨291, by decide⟩ :=
  accepted_of_selected 14 1118291 ⟨291, by decide⟩ ⟨14, 1, 0, 291, 1118291, 1, 4096⟩
    (by decide) selected_cut_17222

theorem unmarked_context_13_279572_438157 : frontier 8 ⟨438157, by decide⟩
    (prefixCache 13 279572) (prefixPartial 13 279572) = false := by
  decide +kernel

theorem node_context_13_279572_438157 : EJMOriginalGlobalDAGData.nodes 8 ⟨438157, by decide⟩ =
    .split (coordinate 13) (![⟨438044, by decide⟩,⟨438087, by decide⟩,⟨438156, by decide⟩,⟨291, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_279572_438157 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279572 ⟨438157, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 279572
    ⟨438157, by decide⟩ (by decide) (![⟨438044, by decide⟩,⟨438087, by decide⟩,⟨438156, by decide⟩,⟨291, by decide⟩]) unmarked_context_13_279572_438157 node_context_13_279572_438157
  intro a
  fin_cases a
  · exact context_14_1118288_438044
  · exact context_14_1118289_438087
  · exact context_14_1118290_438156
  · exact context_14_1118291_291

theorem selected_cut_17223 : selected 8 ⟨438252, by decide⟩
    (prefixPartial 13 279573) = some ⟨13, 2, 0, 438252, 279573, 1865, 16384⟩ := by
  decide +kernel

theorem context_13_279573_438252 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279573 ⟨438252, by decide⟩ :=
  accepted_of_selected 13 279573 ⟨438252, by decide⟩ ⟨13, 2, 0, 438252, 279573, 1865, 16384⟩
    (by decide) selected_cut_17223

theorem selected_cut_17224 : selected 8 ⟨438289, by decide⟩
    (prefixPartial 13 279574) = some ⟨13, 2, 0, 438289, 279574, 761, 16384⟩ := by
  decide +kernel

theorem context_13_279574_438289 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279574 ⟨438289, by decide⟩ :=
  accepted_of_selected 13 279574 ⟨438289, by decide⟩ ⟨13, 2, 0, 438289, 279574, 761, 16384⟩
    (by decide) selected_cut_17224

theorem selected_cut_17225 : selected 8 ⟨414, by decide⟩
    (prefixPartial 13 279575) = some ⟨13, 1, 0, 414, 279575, 1, 16384⟩ := by
  decide +kernel

theorem context_13_279575_414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279575 ⟨414, by decide⟩ :=
  accepted_of_selected 13 279575 ⟨414, by decide⟩ ⟨13, 1, 0, 414, 279575, 1, 16384⟩
    (by decide) selected_cut_17225

theorem unmarked_context_12_69893_438290 : frontier 9 ⟨438290, by decide⟩
    (prefixCache 12 69893) (prefixPartial 12 69893) = false := by
  decide +kernel

theorem node_context_12_69893_438290 : EJMOriginalGlobalDAGData.nodes 9 ⟨438290, by decide⟩ =
    .split (coordinate 12) (![⟨438157, by decide⟩,⟨438252, by decide⟩,⟨438289, by decide⟩,⟨414, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_69893_438290 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69893 ⟨438290, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 69893
    ⟨438290, by decide⟩ (by decide) (![⟨438157, by decide⟩,⟨438252, by decide⟩,⟨438289, by decide⟩,⟨414, by decide⟩]) unmarked_context_12_69893_438290 node_context_12_69893_438290
  intro a
  fin_cases a
  · exact context_13_279572_438157
  · exact context_13_279573_438252
  · exact context_13_279574_438289
  · exact context_13_279575_414

theorem selected_cut_17226 : selected 7 ⟨438331, by decide⟩
    (prefixPartial 14 1118304) = some ⟨14, 2, 0, 438331, 1118304, 1193, 4096⟩ := by
  decide +kernel

theorem context_14_1118304_438331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1118304 ⟨438331, by decide⟩ :=
  accepted_of_selected 14 1118304 ⟨438331, by decide⟩ ⟨14, 2, 0, 438331, 1118304, 1193, 4096⟩
    (by decide) selected_cut_17226

theorem selected_cut_17227 : selected 7 ⟨438350, by decide⟩
    (prefixPartial 14 1118305) = some ⟨14, 2, 0, 438350, 1118305, 901, 4096⟩ := by
  decide +kernel

theorem context_14_1118305_438350 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1118305 ⟨438350, by decide⟩ :=
  accepted_of_selected 14 1118305 ⟨438350, by decide⟩ ⟨14, 2, 0, 438350, 1118305, 901, 4096⟩
    (by decide) selected_cut_17227

theorem selected_cut_17228 : selected 7 ⟨438375, by decide⟩
    (prefixPartial 14 1118306) = some ⟨14, 2, 0, 438375, 1118306, 1417, 4096⟩ := by
  decide +kernel

theorem context_14_1118306_438375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1118306 ⟨438375, by decide⟩ :=
  accepted_of_selected 14 1118306 ⟨438375, by decide⟩ ⟨14, 2, 0, 438375, 1118306, 1417, 4096⟩
    (by decide) selected_cut_17228

theorem selected_cut_17229 : selected 7 ⟨438402, by decide⟩
    (prefixPartial 14 1118307) = some ⟨14, 2, 0, 438402, 1118307, 1317, 4096⟩ := by
  decide +kernel

theorem context_14_1118307_438402 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1118307 ⟨438402, by decide⟩ :=
  accepted_of_selected 14 1118307 ⟨438402, by decide⟩ ⟨14, 2, 0, 438402, 1118307, 1317, 4096⟩
    (by decide) selected_cut_17229

theorem unmarked_context_13_279576_438403 : frontier 8 ⟨438403, by decide⟩
    (prefixCache 13 279576) (prefixPartial 13 279576) = false := by
  decide +kernel

theorem node_context_13_279576_438403 : EJMOriginalGlobalDAGData.nodes 8 ⟨438403, by decide⟩ =
    .split (coordinate 13) (![⟨438331, by decide⟩,⟨438350, by decide⟩,⟨438375, by decide⟩,⟨438402, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_279576_438403 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279576 ⟨438403, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 279576
    ⟨438403, by decide⟩ (by decide) (![⟨438331, by decide⟩,⟨438350, by decide⟩,⟨438375, by decide⟩,⟨438402, by decide⟩]) unmarked_context_13_279576_438403 node_context_13_279576_438403
  intro a
  fin_cases a
  · exact context_14_1118304_438331
  · exact context_14_1118305_438350
  · exact context_14_1118306_438375
  · exact context_14_1118307_438402

theorem selected_cut_17230 : selected 8 ⟨438463, by decide⟩
    (prefixPartial 13 279577) = some ⟨13, 2, 0, 438463, 279577, 3853, 16384⟩ := by
  decide +kernel

theorem context_13_279577_438463 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279577 ⟨438463, by decide⟩ :=
  accepted_of_selected 13 279577 ⟨438463, by decide⟩ ⟨13, 2, 0, 438463, 279577, 3853, 16384⟩
    (by decide) selected_cut_17230

theorem selected_cut_17231 : selected 8 ⟨438489, by decide⟩
    (prefixPartial 13 279578) = some ⟨13, 2, 0, 438489, 279578, 2477, 16384⟩ := by
  decide +kernel

theorem context_13_279578_438489 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279578 ⟨438489, by decide⟩ :=
  accepted_of_selected 13 279578 ⟨438489, by decide⟩ ⟨13, 2, 0, 438489, 279578, 2477, 16384⟩
    (by decide) selected_cut_17231

theorem selected_cut_17232 : selected 8 ⟨438507, by decide⟩
    (prefixPartial 13 279579) = some ⟨13, 2, 0, 438507, 279579, 1425, 16384⟩ := by
  decide +kernel

theorem context_13_279579_438507 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279579 ⟨438507, by decide⟩ :=
  accepted_of_selected 13 279579 ⟨438507, by decide⟩ ⟨13, 2, 0, 438507, 279579, 1425, 16384⟩
    (by decide) selected_cut_17232

theorem unmarked_context_12_69894_438508 : frontier 9 ⟨438508, by decide⟩
    (prefixCache 12 69894) (prefixPartial 12 69894) = false := by
  decide +kernel

theorem node_context_12_69894_438508 : EJMOriginalGlobalDAGData.nodes 9 ⟨438508, by decide⟩ =
    .split (coordinate 12) (![⟨438403, by decide⟩,⟨438463, by decide⟩,⟨438489, by decide⟩,⟨438507, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_69894_438508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69894 ⟨438508, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 69894
    ⟨438508, by decide⟩ (by decide) (![⟨438403, by decide⟩,⟨438463, by decide⟩,⟨438489, by decide⟩,⟨438507, by decide⟩]) unmarked_context_12_69894_438508 node_context_12_69894_438508
  intro a
  fin_cases a
  · exact context_13_279576_438403
  · exact context_13_279577_438463
  · exact context_13_279578_438489
  · exact context_13_279579_438507

theorem selected_cut_17233 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 69895) = some ⟨12, 1, 0, 893, 69895, 1, 65536⟩ := by
  decide +kernel

theorem context_12_69895_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69895 ⟨893, by decide⟩ :=
  accepted_of_selected 12 69895 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 69895, 1, 65536⟩
    (by decide) selected_cut_17233

theorem unmarked_context_11_17473_438509 : frontier 10 ⟨438509, by decide⟩
    (prefixCache 11 17473) (prefixPartial 11 17473) = false := by
  decide +kernel

theorem node_context_11_17473_438509 : EJMOriginalGlobalDAGData.nodes 10 ⟨438509, by decide⟩ =
    .split (coordinate 11) (![⟨895, by decide⟩,⟨438290, by decide⟩,⟨438508, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17473_438509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17473 ⟨438509, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17473
    ⟨438509, by decide⟩ (by decide) (![⟨895, by decide⟩,⟨438290, by decide⟩,⟨438508, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_17473_438509 node_context_11_17473_438509
  intro a
  fin_cases a
  · exact context_12_69892_895
  · exact context_12_69893_438290
  · exact context_12_69894_438508
  · exact context_12_69895_893

theorem selected_cut_17234 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 69896) = some ⟨12, 1, 0, 895, 69896, 1, 65536⟩ := by
  decide +kernel

theorem context_12_69896_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69896 ⟨895, by decide⟩ :=
  accepted_of_selected 12 69896 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 69896, 1, 65536⟩
    (by decide) selected_cut_17234

theorem selected_cut_17235 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 69897) = some ⟨12, 1, 0, 895, 69897, 1, 65536⟩ := by
  decide +kernel

theorem context_12_69897_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69897 ⟨895, by decide⟩ :=
  accepted_of_selected 12 69897 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 69897, 1, 65536⟩
    (by decide) selected_cut_17235

theorem selected_cut_17236 : selected 8 ⟨438592, by decide⟩
    (prefixPartial 13 279592) = some ⟨13, 2, 0, 438592, 279592, 3985, 16384⟩ := by
  decide +kernel

theorem context_13_279592_438592 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279592 ⟨438592, by decide⟩ :=
  accepted_of_selected 13 279592 ⟨438592, by decide⟩ ⟨13, 2, 0, 438592, 279592, 3985, 16384⟩
    (by decide) selected_cut_17236

theorem selected_cut_17237 : selected 8 ⟨438650, by decide⟩
    (prefixPartial 13 279593) = some ⟨13, 2, 0, 438650, 279593, 1981, 16384⟩ := by
  decide +kernel

theorem context_13_279593_438650 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279593 ⟨438650, by decide⟩ :=
  accepted_of_selected 13 279593 ⟨438650, by decide⟩ ⟨13, 2, 0, 438650, 279593, 1981, 16384⟩
    (by decide) selected_cut_17237

theorem selected_cut_17238 : selected 8 ⟨438665, by decide⟩
    (prefixPartial 13 279594) = some ⟨13, 2, 0, 438665, 279594, 693, 16384⟩ := by
  decide +kernel

theorem context_13_279594_438665 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279594 ⟨438665, by decide⟩ :=
  accepted_of_selected 13 279594 ⟨438665, by decide⟩ ⟨13, 2, 0, 438665, 279594, 693, 16384⟩
    (by decide) selected_cut_17238

theorem selected_cut_17239 : selected 8 ⟨438675, by decide⟩
    (prefixPartial 13 279595) = some ⟨13, 2, 0, 438675, 279595, 169, 16384⟩ := by
  decide +kernel

theorem context_13_279595_438675 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279595 ⟨438675, by decide⟩ :=
  accepted_of_selected 13 279595 ⟨438675, by decide⟩ ⟨13, 2, 0, 438675, 279595, 169, 16384⟩
    (by decide) selected_cut_17239

theorem unmarked_context_12_69898_438676 : frontier 9 ⟨438676, by decide⟩
    (prefixCache 12 69898) (prefixPartial 12 69898) = false := by
  decide +kernel

theorem node_context_12_69898_438676 : EJMOriginalGlobalDAGData.nodes 9 ⟨438676, by decide⟩ =
    .split (coordinate 12) (![⟨438592, by decide⟩,⟨438650, by decide⟩,⟨438665, by decide⟩,⟨438675, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_69898_438676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69898 ⟨438676, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 69898
    ⟨438676, by decide⟩ (by decide) (![⟨438592, by decide⟩,⟨438650, by decide⟩,⟨438665, by decide⟩,⟨438675, by decide⟩]) unmarked_context_12_69898_438676 node_context_12_69898_438676
  intro a
  fin_cases a
  · exact context_13_279592_438592
  · exact context_13_279593_438650
  · exact context_13_279594_438665
  · exact context_13_279595_438675

theorem selected_cut_17240 : selected 8 ⟨438761, by decide⟩
    (prefixPartial 13 279596) = some ⟨13, 2, 0, 438761, 279596, 3817, 16384⟩ := by
  decide +kernel

theorem context_13_279596_438761 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279596 ⟨438761, by decide⟩ :=
  accepted_of_selected 13 279596 ⟨438761, by decide⟩ ⟨13, 2, 0, 438761, 279596, 3817, 16384⟩
    (by decide) selected_cut_17240

theorem selected_cut_17241 : selected 8 ⟨438818, by decide⟩
    (prefixPartial 13 279597) = some ⟨13, 2, 0, 438818, 279597, 2121, 16384⟩ := by
  decide +kernel

theorem context_13_279597_438818 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279597 ⟨438818, by decide⟩ :=
  accepted_of_selected 13 279597 ⟨438818, by decide⟩ ⟨13, 2, 0, 438818, 279597, 2121, 16384⟩
    (by decide) selected_cut_17241

theorem selected_cut_17242 : selected 8 ⟨438835, by decide⟩
    (prefixPartial 13 279598) = some ⟨13, 2, 0, 438835, 279598, 717, 16384⟩ := by
  decide +kernel

theorem context_13_279598_438835 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279598 ⟨438835, by decide⟩ :=
  accepted_of_selected 13 279598 ⟨438835, by decide⟩ ⟨13, 2, 0, 438835, 279598, 717, 16384⟩
    (by decide) selected_cut_17242

theorem selected_cut_17243 : selected 8 ⟨438837, by decide⟩
    (prefixPartial 13 279599) = some ⟨13, 2, 0, 438837, 279599, 141, 16384⟩ := by
  decide +kernel

theorem context_13_279599_438837 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279599 ⟨438837, by decide⟩ :=
  accepted_of_selected 13 279599 ⟨438837, by decide⟩ ⟨13, 2, 0, 438837, 279599, 141, 16384⟩
    (by decide) selected_cut_17243

theorem unmarked_context_12_69899_438838 : frontier 9 ⟨438838, by decide⟩
    (prefixCache 12 69899) (prefixPartial 12 69899) = false := by
  decide +kernel

theorem node_context_12_69899_438838 : EJMOriginalGlobalDAGData.nodes 9 ⟨438838, by decide⟩ =
    .split (coordinate 12) (![⟨438761, by decide⟩,⟨438818, by decide⟩,⟨438835, by decide⟩,⟨438837, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_69899_438838 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69899 ⟨438838, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 69899
    ⟨438838, by decide⟩ (by decide) (![⟨438761, by decide⟩,⟨438818, by decide⟩,⟨438835, by decide⟩,⟨438837, by decide⟩]) unmarked_context_12_69899_438838 node_context_12_69899_438838
  intro a
  fin_cases a
  · exact context_13_279596_438761
  · exact context_13_279597_438818
  · exact context_13_279598_438835
  · exact context_13_279599_438837

theorem unmarked_context_11_17474_438839 : frontier 10 ⟨438839, by decide⟩
    (prefixCache 11 17474) (prefixPartial 11 17474) = false := by
  decide +kernel

theorem node_context_11_17474_438839 : EJMOriginalGlobalDAGData.nodes 10 ⟨438839, by decide⟩ =
    .split (coordinate 11) (![⟨895, by decide⟩,⟨895, by decide⟩,⟨438676, by decide⟩,⟨438838, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17474_438839 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17474 ⟨438839, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17474
    ⟨438839, by decide⟩ (by decide) (![⟨895, by decide⟩,⟨895, by decide⟩,⟨438676, by decide⟩,⟨438838, by decide⟩]) unmarked_context_11_17474_438839 node_context_11_17474_438839
  intro a
  fin_cases a
  · exact context_12_69896_895
  · exact context_12_69897_895
  · exact context_12_69898_438676
  · exact context_12_69899_438838

theorem selected_cut_17244 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 17475) = some ⟨11, 1, 0, 1736, 17475, 1, 262144⟩ := by
  decide +kernel

theorem context_11_17475_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17475 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 17475 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 17475, 1, 262144⟩
    (by decide) selected_cut_17244

theorem unmarked_context_10_4368_438840 : frontier 11 ⟨438840, by decide⟩
    (prefixCache 10 4368) (prefixPartial 10 4368) = false := by
  decide +kernel

theorem node_context_10_4368_438840 : EJMOriginalGlobalDAGData.nodes 11 ⟨438840, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨438509, by decide⟩,⟨438839, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4368_438840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4368 ⟨438840, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4368
    ⟨438840, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨438509, by decide⟩,⟨438839, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_4368_438840 node_context_10_4368_438840
  intro a
  fin_cases a
  · exact context_11_17472_434745
  · exact context_11_17473_438509
  · exact context_11_17474_438839
  · exact context_11_17475_1736

theorem selected_cut_17245 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 69904) = some ⟨12, 1, 0, 435160, 69904, 1, 65536⟩ := by
  decide +kernel

theorem context_12_69904_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69904 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 69904 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 69904, 1, 65536⟩
    (by decide) selected_cut_17245

theorem selected_cut_17246 : selected 9 ⟨438901, by decide⟩
    (prefixPartial 12 69905) = some ⟨12, 2, 0, 438901, 69905, 3657, 65536⟩ := by
  decide +kernel

theorem context_12_69905_438901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69905 ⟨438901, by decide⟩ :=
  accepted_of_selected 12 69905 ⟨438901, by decide⟩ ⟨12, 2, 0, 438901, 69905, 3657, 65536⟩
    (by decide) selected_cut_17246

theorem selected_cut_17247 : selected 8 ⟨438934, by decide⟩
    (prefixPartial 13 279624) = some ⟨13, 2, 0, 438934, 279624, 2413, 16384⟩ := by
  decide +kernel

theorem context_13_279624_438934 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279624 ⟨438934, by decide⟩ :=
  accepted_of_selected 13 279624 ⟨438934, by decide⟩ ⟨13, 2, 0, 438934, 279624, 2413, 16384⟩
    (by decide) selected_cut_17247

theorem selected_cut_17248 : selected 8 ⟨438961, by decide⟩
    (prefixPartial 13 279625) = some ⟨13, 2, 0, 438961, 279625, 2381, 16384⟩ := by
  decide +kernel

theorem context_13_279625_438961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279625 ⟨438961, by decide⟩ :=
  accepted_of_selected 13 279625 ⟨438961, by decide⟩ ⟨13, 2, 0, 438961, 279625, 2381, 16384⟩
    (by decide) selected_cut_17248

theorem selected_cut_17249 : selected 8 ⟨438981, by decide⟩
    (prefixPartial 13 279626) = some ⟨13, 2, 0, 438981, 279626, 1621, 16384⟩ := by
  decide +kernel

theorem context_13_279626_438981 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279626 ⟨438981, by decide⟩ :=
  accepted_of_selected 13 279626 ⟨438981, by decide⟩ ⟨13, 2, 0, 438981, 279626, 1621, 16384⟩
    (by decide) selected_cut_17249

theorem selected_cut_17250 : selected 8 ⟨438990, by decide⟩
    (prefixPartial 13 279627) = some ⟨13, 2, 0, 438990, 279627, 1057, 16384⟩ := by
  decide +kernel

theorem context_13_279627_438990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279627 ⟨438990, by decide⟩ :=
  accepted_of_selected 13 279627 ⟨438990, by decide⟩ ⟨13, 2, 0, 438990, 279627, 1057, 16384⟩
    (by decide) selected_cut_17250

theorem unmarked_context_12_69906_438991 : frontier 9 ⟨438991, by decide⟩
    (prefixCache 12 69906) (prefixPartial 12 69906) = false := by
  decide +kernel

theorem node_context_12_69906_438991 : EJMOriginalGlobalDAGData.nodes 9 ⟨438991, by decide⟩ =
    .split (coordinate 12) (![⟨438934, by decide⟩,⟨438961, by decide⟩,⟨438981, by decide⟩,⟨438990, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_69906_438991 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69906 ⟨438991, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 69906
    ⟨438991, by decide⟩ (by decide) (![⟨438934, by decide⟩,⟨438961, by decide⟩,⟨438981, by decide⟩,⟨438990, by decide⟩]) unmarked_context_12_69906_438991 node_context_12_69906_438991
  intro a
  fin_cases a
  · exact context_13_279624_438934
  · exact context_13_279625_438961
  · exact context_13_279626_438981
  · exact context_13_279627_438990

theorem selected_cut_17251 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 69907) = some ⟨12, 1, 0, 893, 69907, 1, 65536⟩ := by
  decide +kernel

theorem context_12_69907_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69907 ⟨893, by decide⟩ :=
  accepted_of_selected 12 69907 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 69907, 1, 65536⟩
    (by decide) selected_cut_17251

theorem unmarked_context_11_17476_438992 : frontier 10 ⟨438992, by decide⟩
    (prefixCache 11 17476) (prefixPartial 11 17476) = false := by
  decide +kernel

theorem node_context_11_17476_438992 : EJMOriginalGlobalDAGData.nodes 10 ⟨438992, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨438901, by decide⟩,⟨438991, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17476_438992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17476 ⟨438992, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17476
    ⟨438992, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨438901, by decide⟩,⟨438991, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_17476_438992 node_context_11_17476_438992
  intro a
  fin_cases a
  · exact context_12_69904_435160
  · exact context_12_69905_438901
  · exact context_12_69906_438991
  · exact context_12_69907_893

theorem selected_cut_17252 : selected 8 ⟨439015, by decide⟩
    (prefixPartial 13 279632) = some ⟨13, 2, 0, 439015, 279632, 1349, 16384⟩ := by
  decide +kernel

theorem context_13_279632_439015 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279632 ⟨439015, by decide⟩ :=
  accepted_of_selected 13 279632 ⟨439015, by decide⟩ ⟨13, 2, 0, 439015, 279632, 1349, 16384⟩
    (by decide) selected_cut_17252

theorem selected_cut_17253 : selected 8 ⟨439047, by decide⟩
    (prefixPartial 13 279633) = some ⟨13, 2, 0, 439047, 279633, 1749, 16384⟩ := by
  decide +kernel

theorem context_13_279633_439047 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279633 ⟨439047, by decide⟩ :=
  accepted_of_selected 13 279633 ⟨439047, by decide⟩ ⟨13, 2, 0, 439047, 279633, 1749, 16384⟩
    (by decide) selected_cut_17253

theorem selected_cut_17254 : selected 8 ⟨439067, by decide⟩
    (prefixPartial 13 279634) = some ⟨13, 2, 0, 439067, 279634, 1869, 16384⟩ := by
  decide +kernel

theorem context_13_279634_439067 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279634 ⟨439067, by decide⟩ :=
  accepted_of_selected 13 279634 ⟨439067, by decide⟩ ⟨13, 2, 0, 439067, 279634, 1869, 16384⟩
    (by decide) selected_cut_17254

theorem selected_cut_17255 : selected 8 ⟨414, by decide⟩
    (prefixPartial 13 279635) = some ⟨13, 1, 0, 414, 279635, 1, 16384⟩ := by
  decide +kernel

theorem context_13_279635_414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279635 ⟨414, by decide⟩ :=
  accepted_of_selected 13 279635 ⟨414, by decide⟩ ⟨13, 1, 0, 414, 279635, 1, 16384⟩
    (by decide) selected_cut_17255

theorem unmarked_context_12_69908_439068 : frontier 9 ⟨439068, by decide⟩
    (prefixCache 12 69908) (prefixPartial 12 69908) = false := by
  decide +kernel

theorem node_context_12_69908_439068 : EJMOriginalGlobalDAGData.nodes 9 ⟨439068, by decide⟩ =
    .split (coordinate 12) (![⟨439015, by decide⟩,⟨439047, by decide⟩,⟨439067, by decide⟩,⟨414, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_69908_439068 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69908 ⟨439068, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 69908
    ⟨439068, by decide⟩ (by decide) (![⟨439015, by decide⟩,⟨439047, by decide⟩,⟨439067, by decide⟩,⟨414, by decide⟩]) unmarked_context_12_69908_439068 node_context_12_69908_439068
  intro a
  fin_cases a
  · exact context_13_279632_439015
  · exact context_13_279633_439047
  · exact context_13_279634_439067
  · exact context_13_279635_414

theorem selected_cut_17256 : selected 9 ⟨439069, by decide⟩
    (prefixPartial 12 69909) = some ⟨12, 1, 0, 439069, 69909, 1, 65536⟩ := by
  decide +kernel

theorem context_12_69909_439069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69909 ⟨439069, by decide⟩ :=
  accepted_of_selected 12 69909 ⟨439069, by decide⟩ ⟨12, 1, 0, 439069, 69909, 1, 65536⟩
    (by decide) selected_cut_17256

theorem selected_cut_17257 : selected 8 ⟨439111, by decide⟩
    (prefixPartial 13 279640) = some ⟨13, 2, 0, 439111, 279640, 2365, 16384⟩ := by
  decide +kernel

theorem context_13_279640_439111 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279640 ⟨439111, by decide⟩ :=
  accepted_of_selected 13 279640 ⟨439111, by decide⟩ ⟨13, 2, 0, 439111, 279640, 2365, 16384⟩
    (by decide) selected_cut_17257

theorem selected_cut_17258 : selected 8 ⟨439138, by decide⟩
    (prefixPartial 13 279641) = some ⟨13, 2, 0, 439138, 279641, 2521, 16384⟩ := by
  decide +kernel

theorem context_13_279641_439138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279641 ⟨439138, by decide⟩ :=
  accepted_of_selected 13 279641 ⟨439138, by decide⟩ ⟨13, 2, 0, 439138, 279641, 2521, 16384⟩
    (by decide) selected_cut_17258

theorem selected_cut_17259 : selected 8 ⟨439158, by decide⟩
    (prefixPartial 13 279642) = some ⟨13, 2, 0, 439158, 279642, 1689, 16384⟩ := by
  decide +kernel

theorem context_13_279642_439158 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279642 ⟨439158, by decide⟩ :=
  accepted_of_selected 13 279642 ⟨439158, by decide⟩ ⟨13, 2, 0, 439158, 279642, 1689, 16384⟩
    (by decide) selected_cut_17259

theorem selected_cut_17260 : selected 8 ⟨439169, by decide⟩
    (prefixPartial 13 279643) = some ⟨13, 2, 0, 439169, 279643, 1109, 16384⟩ := by
  decide +kernel

theorem context_13_279643_439169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279643 ⟨439169, by decide⟩ :=
  accepted_of_selected 13 279643 ⟨439169, by decide⟩ ⟨13, 2, 0, 439169, 279643, 1109, 16384⟩
    (by decide) selected_cut_17260

theorem unmarked_context_12_69910_439170 : frontier 9 ⟨439170, by decide⟩
    (prefixCache 12 69910) (prefixPartial 12 69910) = false := by
  decide +kernel

theorem node_context_12_69910_439170 : EJMOriginalGlobalDAGData.nodes 9 ⟨439170, by decide⟩ =
    .split (coordinate 12) (![⟨439111, by decide⟩,⟨439138, by decide⟩,⟨439158, by decide⟩,⟨439169, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_69910_439170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69910 ⟨439170, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 69910
    ⟨439170, by decide⟩ (by decide) (![⟨439111, by decide⟩,⟨439138, by decide⟩,⟨439158, by decide⟩,⟨439169, by decide⟩]) unmarked_context_12_69910_439170 node_context_12_69910_439170
  intro a
  fin_cases a
  · exact context_13_279640_439111
  · exact context_13_279641_439138
  · exact context_13_279642_439158
  · exact context_13_279643_439169

theorem selected_cut_17261 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 69911) = some ⟨12, 1, 0, 893, 69911, 1, 65536⟩ := by
  decide +kernel

theorem context_12_69911_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69911 ⟨893, by decide⟩ :=
  accepted_of_selected 12 69911 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 69911, 1, 65536⟩
    (by decide) selected_cut_17261

theorem unmarked_context_11_17477_439171 : frontier 10 ⟨439171, by decide⟩
    (prefixCache 11 17477) (prefixPartial 11 17477) = false := by
  decide +kernel

theorem node_context_11_17477_439171 : EJMOriginalGlobalDAGData.nodes 10 ⟨439171, by decide⟩ =
    .split (coordinate 11) (![⟨439068, by decide⟩,⟨439069, by decide⟩,⟨439170, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17477_439171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17477 ⟨439171, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17477
    ⟨439171, by decide⟩ (by decide) (![⟨439068, by decide⟩,⟨439069, by decide⟩,⟨439170, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_17477_439171 node_context_11_17477_439171
  intro a
  fin_cases a
  · exact context_12_69908_439068
  · exact context_12_69909_439069
  · exact context_12_69910_439170
  · exact context_12_69911_893

theorem selected_cut_17262 : selected 8 ⟨439217, by decide⟩
    (prefixPartial 13 279648) = some ⟨13, 2, 0, 439217, 279648, 2833, 16384⟩ := by
  decide +kernel

theorem context_13_279648_439217 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279648 ⟨439217, by decide⟩ :=
  accepted_of_selected 13 279648 ⟨439217, by decide⟩ ⟨13, 2, 0, 439217, 279648, 2833, 16384⟩
    (by decide) selected_cut_17262

theorem selected_cut_17263 : selected 8 ⟨439283, by decide⟩
    (prefixPartial 13 279649) = some ⟨13, 2, 0, 439283, 279649, 3393, 16384⟩ := by
  decide +kernel

theorem context_13_279649_439283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279649 ⟨439283, by decide⟩ :=
  accepted_of_selected 13 279649 ⟨439283, by decide⟩ ⟨13, 2, 0, 439283, 279649, 3393, 16384⟩
    (by decide) selected_cut_17263

theorem selected_cut_17264 : selected 8 ⟨439318, by decide⟩
    (prefixPartial 13 279650) = some ⟨13, 2, 0, 439318, 279650, 2505, 16384⟩ := by
  decide +kernel

theorem context_13_279650_439318 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279650 ⟨439318, by decide⟩ :=
  accepted_of_selected 13 279650 ⟨439318, by decide⟩ ⟨13, 2, 0, 439318, 279650, 2505, 16384⟩
    (by decide) selected_cut_17264

theorem selected_cut_17265 : selected 8 ⟨439330, by decide⟩
    (prefixPartial 13 279651) = some ⟨13, 2, 0, 439330, 279651, 1169, 16384⟩ := by
  decide +kernel

theorem context_13_279651_439330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279651 ⟨439330, by decide⟩ :=
  accepted_of_selected 13 279651 ⟨439330, by decide⟩ ⟨13, 2, 0, 439330, 279651, 1169, 16384⟩
    (by decide) selected_cut_17265

theorem unmarked_context_12_69912_439331 : frontier 9 ⟨439331, by decide⟩
    (prefixCache 12 69912) (prefixPartial 12 69912) = false := by
  decide +kernel

theorem node_context_12_69912_439331 : EJMOriginalGlobalDAGData.nodes 9 ⟨439331, by decide⟩ =
    .split (coordinate 12) (![⟨439217, by decide⟩,⟨439283, by decide⟩,⟨439318, by decide⟩,⟨439330, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_69912_439331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69912 ⟨439331, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 69912
    ⟨439331, by decide⟩ (by decide) (![⟨439217, by decide⟩,⟨439283, by decide⟩,⟨439318, by decide⟩,⟨439330, by decide⟩]) unmarked_context_12_69912_439331 node_context_12_69912_439331
  intro a
  fin_cases a
  · exact context_13_279648_439217
  · exact context_13_279649_439283
  · exact context_13_279650_439318
  · exact context_13_279651_439330

theorem selected_cut_17266 : selected 8 ⟨439371, by decide⟩
    (prefixPartial 13 279652) = some ⟨13, 2, 0, 439371, 279652, 2277, 16384⟩ := by
  decide +kernel

theorem context_13_279652_439371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279652 ⟨439371, by decide⟩ :=
  accepted_of_selected 13 279652 ⟨439371, by decide⟩ ⟨13, 2, 0, 439371, 279652, 2277, 16384⟩
    (by decide) selected_cut_17266

theorem selected_cut_17267 : selected 8 ⟨439392, by decide⟩
    (prefixPartial 13 279653) = some ⟨13, 2, 0, 439392, 279653, 1753, 16384⟩ := by
  decide +kernel

theorem context_13_279653_439392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279653 ⟨439392, by decide⟩ :=
  accepted_of_selected 13 279653 ⟨439392, by decide⟩ ⟨13, 2, 0, 439392, 279653, 1753, 16384⟩
    (by decide) selected_cut_17267

theorem selected_cut_17268 : selected 8 ⟨439413, by decide⟩
    (prefixPartial 13 279654) = some ⟨13, 2, 0, 439413, 279654, 2185, 16384⟩ := by
  decide +kernel

theorem context_13_279654_439413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279654 ⟨439413, by decide⟩ :=
  accepted_of_selected 13 279654 ⟨439413, by decide⟩ ⟨13, 2, 0, 439413, 279654, 2185, 16384⟩
    (by decide) selected_cut_17268

theorem selected_cut_17269 : selected 8 ⟨439423, by decide⟩
    (prefixPartial 13 279655) = some ⟨13, 2, 0, 439423, 279655, 1077, 16384⟩ := by
  decide +kernel

theorem context_13_279655_439423 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279655 ⟨439423, by decide⟩ :=
  accepted_of_selected 13 279655 ⟨439423, by decide⟩ ⟨13, 2, 0, 439423, 279655, 1077, 16384⟩
    (by decide) selected_cut_17269

theorem unmarked_context_12_69913_439424 : frontier 9 ⟨439424, by decide⟩
    (prefixCache 12 69913) (prefixPartial 12 69913) = false := by
  decide +kernel

theorem node_context_12_69913_439424 : EJMOriginalGlobalDAGData.nodes 9 ⟨439424, by decide⟩ =
    .split (coordinate 12) (![⟨439371, by decide⟩,⟨439392, by decide⟩,⟨439413, by decide⟩,⟨439423, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_69913_439424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69913 ⟨439424, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 69913
    ⟨439424, by decide⟩ (by decide) (![⟨439371, by decide⟩,⟨439392, by decide⟩,⟨439413, by decide⟩,⟨439423, by decide⟩]) unmarked_context_12_69913_439424 node_context_12_69913_439424
  intro a
  fin_cases a
  · exact context_13_279652_439371
  · exact context_13_279653_439392
  · exact context_13_279654_439413
  · exact context_13_279655_439423

theorem selected_cut_17270 : selected 8 ⟨439466, by decide⟩
    (prefixPartial 13 279656) = some ⟨13, 2, 0, 439466, 279656, 2249, 16384⟩ := by
  decide +kernel

theorem context_13_279656_439466 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279656 ⟨439466, by decide⟩ :=
  accepted_of_selected 13 279656 ⟨439466, by decide⟩ ⟨13, 2, 0, 439466, 279656, 2249, 16384⟩
    (by decide) selected_cut_17270

theorem selected_cut_17271 : selected 8 ⟨439496, by decide⟩
    (prefixPartial 13 279657) = some ⟨13, 2, 0, 439496, 279657, 2401, 16384⟩ := by
  decide +kernel

theorem context_13_279657_439496 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279657 ⟨439496, by decide⟩ :=
  accepted_of_selected 13 279657 ⟨439496, by decide⟩ ⟨13, 2, 0, 439496, 279657, 2401, 16384⟩
    (by decide) selected_cut_17271

theorem selected_cut_17272 : selected 8 ⟨439516, by decide⟩
    (prefixPartial 13 279658) = some ⟨13, 2, 0, 439516, 279658, 1789, 16384⟩ := by
  decide +kernel

theorem context_13_279658_439516 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279658 ⟨439516, by decide⟩ :=
  accepted_of_selected 13 279658 ⟨439516, by decide⟩ ⟨13, 2, 0, 439516, 279658, 1789, 16384⟩
    (by decide) selected_cut_17272

theorem selected_cut_17273 : selected 8 ⟨439524, by decide⟩
    (prefixPartial 13 279659) = some ⟨13, 2, 0, 439524, 279659, 1085, 16384⟩ := by
  decide +kernel

theorem context_13_279659_439524 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279659 ⟨439524, by decide⟩ :=
  accepted_of_selected 13 279659 ⟨439524, by decide⟩ ⟨13, 2, 0, 439524, 279659, 1085, 16384⟩
    (by decide) selected_cut_17273

theorem unmarked_context_12_69914_439525 : frontier 9 ⟨439525, by decide⟩
    (prefixCache 12 69914) (prefixPartial 12 69914) = false := by
  decide +kernel

theorem node_context_12_69914_439525 : EJMOriginalGlobalDAGData.nodes 9 ⟨439525, by decide⟩ =
    .split (coordinate 12) (![⟨439466, by decide⟩,⟨439496, by decide⟩,⟨439516, by decide⟩,⟨439524, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_69914_439525 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69914 ⟨439525, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 69914
    ⟨439525, by decide⟩ (by decide) (![⟨439466, by decide⟩,⟨439496, by decide⟩,⟨439516, by decide⟩,⟨439524, by decide⟩]) unmarked_context_12_69914_439525 node_context_12_69914_439525
  intro a
  fin_cases a
  · exact context_13_279656_439466
  · exact context_13_279657_439496
  · exact context_13_279658_439516
  · exact context_13_279659_439524

theorem selected_cut_17274 : selected 8 ⟨439567, by decide⟩
    (prefixPartial 13 279660) = some ⟨13, 2, 0, 439567, 279660, 2189, 16384⟩ := by
  decide +kernel

theorem context_13_279660_439567 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279660 ⟨439567, by decide⟩ :=
  accepted_of_selected 13 279660 ⟨439567, by decide⟩ ⟨13, 2, 0, 439567, 279660, 2189, 16384⟩
    (by decide) selected_cut_17274

theorem selected_cut_17275 : selected 8 ⟨439595, by decide⟩
    (prefixPartial 13 279661) = some ⟨13, 2, 0, 439595, 279661, 2337, 16384⟩ := by
  decide +kernel

theorem context_13_279661_439595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279661 ⟨439595, by decide⟩ :=
  accepted_of_selected 13 279661 ⟨439595, by decide⟩ ⟨13, 2, 0, 439595, 279661, 2337, 16384⟩
    (by decide) selected_cut_17275

theorem selected_cut_17276 : selected 8 ⟨439616, by decide⟩
    (prefixPartial 13 279662) = some ⟨13, 2, 0, 439616, 279662, 1957, 16384⟩ := by
  decide +kernel

theorem context_13_279662_439616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279662 ⟨439616, by decide⟩ :=
  accepted_of_selected 13 279662 ⟨439616, by decide⟩ ⟨13, 2, 0, 439616, 279662, 1957, 16384⟩
    (by decide) selected_cut_17276

theorem selected_cut_17277 : selected 8 ⟨439624, by decide⟩
    (prefixPartial 13 279663) = some ⟨13, 2, 0, 439624, 279663, 853, 16384⟩ := by
  decide +kernel

theorem context_13_279663_439624 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279663 ⟨439624, by decide⟩ :=
  accepted_of_selected 13 279663 ⟨439624, by decide⟩ ⟨13, 2, 0, 439624, 279663, 853, 16384⟩
    (by decide) selected_cut_17277

theorem unmarked_context_12_69915_439625 : frontier 9 ⟨439625, by decide⟩
    (prefixCache 12 69915) (prefixPartial 12 69915) = false := by
  decide +kernel

theorem node_context_12_69915_439625 : EJMOriginalGlobalDAGData.nodes 9 ⟨439625, by decide⟩ =
    .split (coordinate 12) (![⟨439567, by decide⟩,⟨439595, by decide⟩,⟨439616, by decide⟩,⟨439624, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_69915_439625 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69915 ⟨439625, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 69915
    ⟨439625, by decide⟩ (by decide) (![⟨439567, by decide⟩,⟨439595, by decide⟩,⟨439616, by decide⟩,⟨439624, by decide⟩]) unmarked_context_12_69915_439625 node_context_12_69915_439625
  intro a
  fin_cases a
  · exact context_13_279660_439567
  · exact context_13_279661_439595
  · exact context_13_279662_439616
  · exact context_13_279663_439624

theorem unmarked_context_11_17478_439626 : frontier 10 ⟨439626, by decide⟩
    (prefixCache 11 17478) (prefixPartial 11 17478) = false := by
  decide +kernel

theorem node_context_11_17478_439626 : EJMOriginalGlobalDAGData.nodes 10 ⟨439626, by decide⟩ =
    .split (coordinate 11) (![⟨439331, by decide⟩,⟨439424, by decide⟩,⟨439525, by decide⟩,⟨439625, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17478_439626 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17478 ⟨439626, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17478
    ⟨439626, by decide⟩ (by decide) (![⟨439331, by decide⟩,⟨439424, by decide⟩,⟨439525, by decide⟩,⟨439625, by decide⟩]) unmarked_context_11_17478_439626 node_context_11_17478_439626
  intro a
  fin_cases a
  · exact context_12_69912_439331
  · exact context_12_69913_439424
  · exact context_12_69914_439525
  · exact context_12_69915_439625

theorem selected_cut_17278 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 17479) = some ⟨11, 1, 0, 1736, 17479, 1, 262144⟩ := by
  decide +kernel

theorem context_11_17479_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17479 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 17479 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 17479, 1, 262144⟩
    (by decide) selected_cut_17278

theorem unmarked_context_10_4369_439627 : frontier 11 ⟨439627, by decide⟩
    (prefixCache 10 4369) (prefixPartial 10 4369) = false := by
  decide +kernel

theorem node_context_10_4369_439627 : EJMOriginalGlobalDAGData.nodes 11 ⟨439627, by decide⟩ =
    .split (coordinate 10) (![⟨438992, by decide⟩,⟨439171, by decide⟩,⟨439626, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4369_439627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4369 ⟨439627, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4369
    ⟨439627, by decide⟩ (by decide) (![⟨438992, by decide⟩,⟨439171, by decide⟩,⟨439626, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_4369_439627 node_context_10_4369_439627
  intro a
  fin_cases a
  · exact context_11_17476_438992
  · exact context_11_17477_439171
  · exact context_11_17478_439626
  · exact context_11_17479_1736

theorem selected_cut_17279 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 69920) = some ⟨12, 1, 0, 435790, 69920, 1, 65536⟩ := by
  decide +kernel

theorem context_12_69920_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 69920 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 69920 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 69920, 1, 65536⟩
    (by decide) selected_cut_17279

theorem selected_cut_17280 : selected 8 ⟨439665, by decide⟩
    (prefixPartial 13 279684) = some ⟨13, 2, 0, 439665, 279684, 1501, 16384⟩ := by
  decide +kernel

theorem context_13_279684_439665 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279684 ⟨439665, by decide⟩ :=
  accepted_of_selected 13 279684 ⟨439665, by decide⟩ ⟨13, 2, 0, 439665, 279684, 1501, 16384⟩
    (by decide) selected_cut_17280

theorem selected_cut_17281 : selected 8 ⟨439685, by decide⟩
    (prefixPartial 13 279685) = some ⟨13, 2, 0, 439685, 279685, 1481, 16384⟩ := by
  decide +kernel

theorem context_13_279685_439685 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 279685 ⟨439685, by decide⟩ :=
  accepted_of_selected 13 279685 ⟨439685, by decide⟩ ⟨13, 2, 0, 439685, 279685, 1481, 16384⟩
    (by decide) selected_cut_17281

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
