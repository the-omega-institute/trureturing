/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover023
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_12_5657_75432 : frontier 9 ⟨75432, by decide⟩
    (prefixCache 12 5657) (prefixPartial 12 5657) = false := by
  decide +kernel

theorem node_context_12_5657_75432 : EJMOriginalGlobalDAGData.nodes 9 ⟨75432, by decide⟩ =
    .split (coordinate 12) (![⟨75361, by decide⟩,⟨75392, by decide⟩,⟨75418, by decide⟩,⟨75431, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5657_75432 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5657 ⟨75432, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5657
    ⟨75432, by decide⟩ (by decide) (![⟨75361, by decide⟩,⟨75392, by decide⟩,⟨75418, by decide⟩,⟨75431, by decide⟩]) unmarked_context_12_5657_75432 node_context_12_5657_75432
  intro a
  fin_cases a
  · exact context_13_22628_75361
  · exact context_13_22629_75392
  · exact context_13_22630_75418
  · exact context_13_22631_75431

theorem selected_cut_02307 : selected 8 ⟨75475, by decide⟩
    (prefixPartial 13 22632) = some ⟨13, 2, 0, 75475, 22632, 3161, 16384⟩ := by
  decide +kernel

theorem context_13_22632_75475 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22632 ⟨75475, by decide⟩ :=
  accepted_of_selected 13 22632 ⟨75475, by decide⟩ ⟨13, 2, 0, 75475, 22632, 3161, 16384⟩
    (by decide) selected_cut_02307

theorem selected_cut_02308 : selected 8 ⟨75525, by decide⟩
    (prefixPartial 13 22633) = some ⟨13, 2, 0, 75525, 22633, 3857, 16384⟩ := by
  decide +kernel

theorem context_13_22633_75525 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22633 ⟨75525, by decide⟩ :=
  accepted_of_selected 13 22633 ⟨75525, by decide⟩ ⟨13, 2, 0, 75525, 22633, 3857, 16384⟩
    (by decide) selected_cut_02308

theorem selected_cut_02309 : selected 8 ⟨75563, by decide⟩
    (prefixPartial 13 22634) = some ⟨13, 2, 0, 75563, 22634, 2769, 16384⟩ := by
  decide +kernel

theorem context_13_22634_75563 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22634 ⟨75563, by decide⟩ :=
  accepted_of_selected 13 22634 ⟨75563, by decide⟩ ⟨13, 2, 0, 75563, 22634, 2769, 16384⟩
    (by decide) selected_cut_02309

theorem selected_cut_02310 : selected 8 ⟨75590, by decide⟩
    (prefixPartial 13 22635) = some ⟨13, 2, 0, 75590, 22635, 1637, 16384⟩ := by
  decide +kernel

theorem context_13_22635_75590 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22635 ⟨75590, by decide⟩ :=
  accepted_of_selected 13 22635 ⟨75590, by decide⟩ ⟨13, 2, 0, 75590, 22635, 1637, 16384⟩
    (by decide) selected_cut_02310

theorem unmarked_context_12_5658_75591 : frontier 9 ⟨75591, by decide⟩
    (prefixCache 12 5658) (prefixPartial 12 5658) = false := by
  decide +kernel

theorem node_context_12_5658_75591 : EJMOriginalGlobalDAGData.nodes 9 ⟨75591, by decide⟩ =
    .split (coordinate 12) (![⟨75475, by decide⟩,⟨75525, by decide⟩,⟨75563, by decide⟩,⟨75590, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5658_75591 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5658 ⟨75591, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5658
    ⟨75591, by decide⟩ (by decide) (![⟨75475, by decide⟩,⟨75525, by decide⟩,⟨75563, by decide⟩,⟨75590, by decide⟩]) unmarked_context_12_5658_75591 node_context_12_5658_75591
  intro a
  fin_cases a
  · exact context_13_22632_75475
  · exact context_13_22633_75525
  · exact context_13_22634_75563
  · exact context_13_22635_75590

theorem selected_cut_02311 : selected 8 ⟨75635, by decide⟩
    (prefixPartial 13 22636) = some ⟨13, 2, 0, 75635, 22636, 2217, 16384⟩ := by
  decide +kernel

theorem context_13_22636_75635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22636 ⟨75635, by decide⟩ :=
  accepted_of_selected 13 22636 ⟨75635, by decide⟩ ⟨13, 2, 0, 75635, 22636, 2217, 16384⟩
    (by decide) selected_cut_02311

theorem selected_cut_02312 : selected 8 ⟨75665, by decide⟩
    (prefixPartial 13 22637) = some ⟨13, 2, 0, 75665, 22637, 2497, 16384⟩ := by
  decide +kernel

theorem context_13_22637_75665 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22637 ⟨75665, by decide⟩ :=
  accepted_of_selected 13 22637 ⟨75665, by decide⟩ ⟨13, 2, 0, 75665, 22637, 2497, 16384⟩
    (by decide) selected_cut_02312

theorem selected_cut_02313 : selected 8 ⟨75689, by decide⟩
    (prefixPartial 13 22638) = some ⟨13, 2, 0, 75689, 22638, 1929, 16384⟩ := by
  decide +kernel

theorem context_13_22638_75689 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22638 ⟨75689, by decide⟩ :=
  accepted_of_selected 13 22638 ⟨75689, by decide⟩ ⟨13, 2, 0, 75689, 22638, 1929, 16384⟩
    (by decide) selected_cut_02313

theorem selected_cut_02314 : selected 8 ⟨75696, by decide⟩
    (prefixPartial 13 22639) = some ⟨13, 2, 0, 75696, 22639, 1093, 16384⟩ := by
  decide +kernel

theorem context_13_22639_75696 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22639 ⟨75696, by decide⟩ :=
  accepted_of_selected 13 22639 ⟨75696, by decide⟩ ⟨13, 2, 0, 75696, 22639, 1093, 16384⟩
    (by decide) selected_cut_02314

theorem unmarked_context_12_5659_75697 : frontier 9 ⟨75697, by decide⟩
    (prefixCache 12 5659) (prefixPartial 12 5659) = false := by
  decide +kernel

theorem node_context_12_5659_75697 : EJMOriginalGlobalDAGData.nodes 9 ⟨75697, by decide⟩ =
    .split (coordinate 12) (![⟨75635, by decide⟩,⟨75665, by decide⟩,⟨75689, by decide⟩,⟨75696, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5659_75697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5659 ⟨75697, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5659
    ⟨75697, by decide⟩ (by decide) (![⟨75635, by decide⟩,⟨75665, by decide⟩,⟨75689, by decide⟩,⟨75696, by decide⟩]) unmarked_context_12_5659_75697 node_context_12_5659_75697
  intro a
  fin_cases a
  · exact context_13_22636_75635
  · exact context_13_22637_75665
  · exact context_13_22638_75689
  · exact context_13_22639_75696

theorem unmarked_context_11_1414_75698 : frontier 10 ⟨75698, by decide⟩
    (prefixCache 11 1414) (prefixPartial 11 1414) = false := by
  decide +kernel

theorem node_context_11_1414_75698 : EJMOriginalGlobalDAGData.nodes 10 ⟨75698, by decide⟩ =
    .split (coordinate 11) (![⟨75318, by decide⟩,⟨75432, by decide⟩,⟨75591, by decide⟩,⟨75697, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1414_75698 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1414 ⟨75698, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1414
    ⟨75698, by decide⟩ (by decide) (![⟨75318, by decide⟩,⟨75432, by decide⟩,⟨75591, by decide⟩,⟨75697, by decide⟩]) unmarked_context_11_1414_75698 node_context_11_1414_75698
  intro a
  fin_cases a
  · exact context_12_5656_75318
  · exact context_12_5657_75432
  · exact context_12_5658_75591
  · exact context_12_5659_75697

theorem selected_cut_02315 : selected 8 ⟨75734, by decide⟩
    (prefixPartial 13 22640) = some ⟨13, 2, 0, 75734, 22640, 2229, 16384⟩ := by
  decide +kernel

theorem context_13_22640_75734 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22640 ⟨75734, by decide⟩ :=
  accepted_of_selected 13 22640 ⟨75734, by decide⟩ ⟨13, 2, 0, 75734, 22640, 2229, 16384⟩
    (by decide) selected_cut_02315

theorem selected_cut_02316 : selected 8 ⟨75777, by decide⟩
    (prefixPartial 13 22641) = some ⟨13, 2, 0, 75777, 22641, 3437, 16384⟩ := by
  decide +kernel

theorem context_13_22641_75777 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22641 ⟨75777, by decide⟩ :=
  accepted_of_selected 13 22641 ⟨75777, by decide⟩ ⟨13, 2, 0, 75777, 22641, 3437, 16384⟩
    (by decide) selected_cut_02316

theorem selected_cut_02317 : selected 8 ⟨75810, by decide⟩
    (prefixPartial 13 22642) = some ⟨13, 2, 0, 75810, 22642, 2577, 16384⟩ := by
  decide +kernel

theorem context_13_22642_75810 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22642 ⟨75810, by decide⟩ :=
  accepted_of_selected 13 22642 ⟨75810, by decide⟩ ⟨13, 2, 0, 75810, 22642, 2577, 16384⟩
    (by decide) selected_cut_02317

theorem selected_cut_02318 : selected 8 ⟨75824, by decide⟩
    (prefixPartial 13 22643) = some ⟨13, 2, 0, 75824, 22643, 1297, 16384⟩ := by
  decide +kernel

theorem context_13_22643_75824 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22643 ⟨75824, by decide⟩ :=
  accepted_of_selected 13 22643 ⟨75824, by decide⟩ ⟨13, 2, 0, 75824, 22643, 1297, 16384⟩
    (by decide) selected_cut_02318

theorem unmarked_context_12_5660_75825 : frontier 9 ⟨75825, by decide⟩
    (prefixCache 12 5660) (prefixPartial 12 5660) = false := by
  decide +kernel

theorem node_context_12_5660_75825 : EJMOriginalGlobalDAGData.nodes 9 ⟨75825, by decide⟩ =
    .split (coordinate 12) (![⟨75734, by decide⟩,⟨75777, by decide⟩,⟨75810, by decide⟩,⟨75824, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5660_75825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5660 ⟨75825, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5660
    ⟨75825, by decide⟩ (by decide) (![⟨75734, by decide⟩,⟨75777, by decide⟩,⟨75810, by decide⟩,⟨75824, by decide⟩]) unmarked_context_12_5660_75825 node_context_12_5660_75825
  intro a
  fin_cases a
  · exact context_13_22640_75734
  · exact context_13_22641_75777
  · exact context_13_22642_75810
  · exact context_13_22643_75824

theorem selected_cut_02319 : selected 8 ⟨75859, by decide⟩
    (prefixPartial 13 22644) = some ⟨13, 2, 0, 75859, 22644, 1977, 16384⟩ := by
  decide +kernel

theorem context_13_22644_75859 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22644 ⟨75859, by decide⟩ :=
  accepted_of_selected 13 22644 ⟨75859, by decide⟩ ⟨13, 2, 0, 75859, 22644, 1977, 16384⟩
    (by decide) selected_cut_02319

theorem selected_cut_02320 : selected 8 ⟨75894, by decide⟩
    (prefixPartial 13 22645) = some ⟨13, 2, 0, 75894, 22645, 2385, 16384⟩ := by
  decide +kernel

theorem context_13_22645_75894 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22645 ⟨75894, by decide⟩ :=
  accepted_of_selected 13 22645 ⟨75894, by decide⟩ ⟨13, 2, 0, 75894, 22645, 2385, 16384⟩
    (by decide) selected_cut_02320

theorem selected_cut_02321 : selected 8 ⟨75918, by decide⟩
    (prefixPartial 13 22646) = some ⟨13, 2, 0, 75918, 22646, 2021, 16384⟩ := by
  decide +kernel

theorem context_13_22646_75918 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22646 ⟨75918, by decide⟩ :=
  accepted_of_selected 13 22646 ⟨75918, by decide⟩ ⟨13, 2, 0, 75918, 22646, 2021, 16384⟩
    (by decide) selected_cut_02321

theorem selected_cut_02322 : selected 8 ⟨75927, by decide⟩
    (prefixPartial 13 22647) = some ⟨13, 2, 0, 75927, 22647, 997, 16384⟩ := by
  decide +kernel

theorem context_13_22647_75927 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22647 ⟨75927, by decide⟩ :=
  accepted_of_selected 13 22647 ⟨75927, by decide⟩ ⟨13, 2, 0, 75927, 22647, 997, 16384⟩
    (by decide) selected_cut_02322

theorem unmarked_context_12_5661_75928 : frontier 9 ⟨75928, by decide⟩
    (prefixCache 12 5661) (prefixPartial 12 5661) = false := by
  decide +kernel

theorem node_context_12_5661_75928 : EJMOriginalGlobalDAGData.nodes 9 ⟨75928, by decide⟩ =
    .split (coordinate 12) (![⟨75859, by decide⟩,⟨75894, by decide⟩,⟨75918, by decide⟩,⟨75927, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5661_75928 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5661 ⟨75928, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5661
    ⟨75928, by decide⟩ (by decide) (![⟨75859, by decide⟩,⟨75894, by decide⟩,⟨75918, by decide⟩,⟨75927, by decide⟩]) unmarked_context_12_5661_75928 node_context_12_5661_75928
  intro a
  fin_cases a
  · exact context_13_22644_75859
  · exact context_13_22645_75894
  · exact context_13_22646_75918
  · exact context_13_22647_75927

theorem selected_cut_02323 : selected 8 ⟨75959, by decide⟩
    (prefixPartial 13 22648) = some ⟨13, 2, 0, 75959, 22648, 1673, 16384⟩ := by
  decide +kernel

theorem context_13_22648_75959 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22648 ⟨75959, by decide⟩ :=
  accepted_of_selected 13 22648 ⟨75959, by decide⟩ ⟨13, 2, 0, 75959, 22648, 1673, 16384⟩
    (by decide) selected_cut_02323

theorem selected_cut_02324 : selected 8 ⟨75992, by decide⟩
    (prefixPartial 13 22649) = some ⟨13, 2, 0, 75992, 22649, 2529, 16384⟩ := by
  decide +kernel

theorem context_13_22649_75992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22649 ⟨75992, by decide⟩ :=
  accepted_of_selected 13 22649 ⟨75992, by decide⟩ ⟨13, 2, 0, 75992, 22649, 2529, 16384⟩
    (by decide) selected_cut_02324

theorem selected_cut_02325 : selected 8 ⟨76012, by decide⟩
    (prefixPartial 13 22650) = some ⟨13, 2, 0, 76012, 22650, 1741, 16384⟩ := by
  decide +kernel

theorem context_13_22650_76012 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22650 ⟨76012, by decide⟩ :=
  accepted_of_selected 13 22650 ⟨76012, by decide⟩ ⟨13, 2, 0, 76012, 22650, 1741, 16384⟩
    (by decide) selected_cut_02325

theorem selected_cut_02326 : selected 8 ⟨76025, by decide⟩
    (prefixPartial 13 22651) = some ⟨13, 2, 0, 76025, 22651, 989, 16384⟩ := by
  decide +kernel

theorem context_13_22651_76025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22651 ⟨76025, by decide⟩ :=
  accepted_of_selected 13 22651 ⟨76025, by decide⟩ ⟨13, 2, 0, 76025, 22651, 989, 16384⟩
    (by decide) selected_cut_02326

theorem unmarked_context_12_5662_76026 : frontier 9 ⟨76026, by decide⟩
    (prefixCache 12 5662) (prefixPartial 12 5662) = false := by
  decide +kernel

theorem node_context_12_5662_76026 : EJMOriginalGlobalDAGData.nodes 9 ⟨76026, by decide⟩ =
    .split (coordinate 12) (![⟨75959, by decide⟩,⟨75992, by decide⟩,⟨76012, by decide⟩,⟨76025, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5662_76026 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5662 ⟨76026, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5662
    ⟨76026, by decide⟩ (by decide) (![⟨75959, by decide⟩,⟨75992, by decide⟩,⟨76012, by decide⟩,⟨76025, by decide⟩]) unmarked_context_12_5662_76026 node_context_12_5662_76026
  intro a
  fin_cases a
  · exact context_13_22648_75959
  · exact context_13_22649_75992
  · exact context_13_22650_76012
  · exact context_13_22651_76025

theorem selected_cut_02327 : selected 8 ⟨76064, by decide⟩
    (prefixPartial 13 22652) = some ⟨13, 2, 0, 76064, 22652, 1909, 16384⟩ := by
  decide +kernel

theorem context_13_22652_76064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22652 ⟨76064, by decide⟩ :=
  accepted_of_selected 13 22652 ⟨76064, by decide⟩ ⟨13, 2, 0, 76064, 22652, 1909, 16384⟩
    (by decide) selected_cut_02327

theorem selected_cut_02328 : selected 8 ⟨76096, by decide⟩
    (prefixPartial 13 22653) = some ⟨13, 2, 0, 76096, 22653, 2509, 16384⟩ := by
  decide +kernel

theorem context_13_22653_76096 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22653 ⟨76096, by decide⟩ :=
  accepted_of_selected 13 22653 ⟨76096, by decide⟩ ⟨13, 2, 0, 76096, 22653, 2509, 16384⟩
    (by decide) selected_cut_02328

theorem selected_cut_02329 : selected 8 ⟨76116, by decide⟩
    (prefixPartial 13 22654) = some ⟨13, 2, 0, 76116, 22654, 1965, 16384⟩ := by
  decide +kernel

theorem context_13_22654_76116 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22654 ⟨76116, by decide⟩ :=
  accepted_of_selected 13 22654 ⟨76116, by decide⟩ ⟨13, 2, 0, 76116, 22654, 1965, 16384⟩
    (by decide) selected_cut_02329

theorem selected_cut_02330 : selected 8 ⟨76124, by decide⟩
    (prefixPartial 13 22655) = some ⟨13, 2, 0, 76124, 22655, 993, 16384⟩ := by
  decide +kernel

theorem context_13_22655_76124 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22655 ⟨76124, by decide⟩ :=
  accepted_of_selected 13 22655 ⟨76124, by decide⟩ ⟨13, 2, 0, 76124, 22655, 993, 16384⟩
    (by decide) selected_cut_02330

theorem unmarked_context_12_5663_76125 : frontier 9 ⟨76125, by decide⟩
    (prefixCache 12 5663) (prefixPartial 12 5663) = false := by
  decide +kernel

theorem node_context_12_5663_76125 : EJMOriginalGlobalDAGData.nodes 9 ⟨76125, by decide⟩ =
    .split (coordinate 12) (![⟨76064, by decide⟩,⟨76096, by decide⟩,⟨76116, by decide⟩,⟨76124, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5663_76125 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5663 ⟨76125, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5663
    ⟨76125, by decide⟩ (by decide) (![⟨76064, by decide⟩,⟨76096, by decide⟩,⟨76116, by decide⟩,⟨76124, by decide⟩]) unmarked_context_12_5663_76125 node_context_12_5663_76125
  intro a
  fin_cases a
  · exact context_13_22652_76064
  · exact context_13_22653_76096
  · exact context_13_22654_76116
  · exact context_13_22655_76124

theorem unmarked_context_11_1415_76126 : frontier 10 ⟨76126, by decide⟩
    (prefixCache 11 1415) (prefixPartial 11 1415) = false := by
  decide +kernel

theorem node_context_11_1415_76126 : EJMOriginalGlobalDAGData.nodes 10 ⟨76126, by decide⟩ =
    .split (coordinate 11) (![⟨75825, by decide⟩,⟨75928, by decide⟩,⟨76026, by decide⟩,⟨76125, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1415_76126 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1415 ⟨76126, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1415
    ⟨76126, by decide⟩ (by decide) (![⟨75825, by decide⟩,⟨75928, by decide⟩,⟨76026, by decide⟩,⟨76125, by decide⟩]) unmarked_context_11_1415_76126 node_context_11_1415_76126
  intro a
  fin_cases a
  · exact context_12_5660_75825
  · exact context_12_5661_75928
  · exact context_12_5662_76026
  · exact context_12_5663_76125

theorem unmarked_context_10_353_76127 : frontier 11 ⟨76127, by decide⟩
    (prefixCache 10 353) (prefixPartial 10 353) = false := by
  decide +kernel

theorem node_context_10_353_76127 : EJMOriginalGlobalDAGData.nodes 11 ⟨76127, by decide⟩ =
    .split (coordinate 10) (![⟨74355, by decide⟩,⟨75184, by decide⟩,⟨75698, by decide⟩,⟨76126, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_353_76127 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 353 ⟨76127, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 353
    ⟨76127, by decide⟩ (by decide) (![⟨74355, by decide⟩,⟨75184, by decide⟩,⟨75698, by decide⟩,⟨76126, by decide⟩]) unmarked_context_10_353_76127 node_context_10_353_76127
  intro a
  fin_cases a
  · exact context_11_1412_74355
  · exact context_11_1413_75184
  · exact context_11_1414_75698
  · exact context_11_1415_76126

theorem selected_cut_02331 : selected 8 ⟨76161, by decide⟩
    (prefixPartial 13 22656) = some ⟨13, 2, 0, 76161, 22656, 2309, 16384⟩ := by
  decide +kernel

theorem context_13_22656_76161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22656 ⟨76161, by decide⟩ :=
  accepted_of_selected 13 22656 ⟨76161, by decide⟩ ⟨13, 2, 0, 76161, 22656, 2309, 16384⟩
    (by decide) selected_cut_02331

theorem selected_cut_02332 : selected 8 ⟨76216, by decide⟩
    (prefixPartial 13 22657) = some ⟨13, 2, 0, 76216, 22657, 3569, 16384⟩ := by
  decide +kernel

theorem context_13_22657_76216 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22657 ⟨76216, by decide⟩ :=
  accepted_of_selected 13 22657 ⟨76216, by decide⟩ ⟨13, 2, 0, 76216, 22657, 3569, 16384⟩
    (by decide) selected_cut_02332

theorem selected_cut_02333 : selected 8 ⟨76258, by decide⟩
    (prefixPartial 13 22658) = some ⟨13, 2, 0, 76258, 22658, 2677, 16384⟩ := by
  decide +kernel

theorem context_13_22658_76258 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22658 ⟨76258, by decide⟩ :=
  accepted_of_selected 13 22658 ⟨76258, by decide⟩ ⟨13, 2, 0, 76258, 22658, 2677, 16384⟩
    (by decide) selected_cut_02333

theorem selected_cut_02334 : selected 8 ⟨76275, by decide⟩
    (prefixPartial 13 22659) = some ⟨13, 2, 0, 76275, 22659, 1169, 16384⟩ := by
  decide +kernel

theorem context_13_22659_76275 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22659 ⟨76275, by decide⟩ :=
  accepted_of_selected 13 22659 ⟨76275, by decide⟩ ⟨13, 2, 0, 76275, 22659, 1169, 16384⟩
    (by decide) selected_cut_02334

theorem unmarked_context_12_5664_76276 : frontier 9 ⟨76276, by decide⟩
    (prefixCache 12 5664) (prefixPartial 12 5664) = false := by
  decide +kernel

theorem node_context_12_5664_76276 : EJMOriginalGlobalDAGData.nodes 9 ⟨76276, by decide⟩ =
    .split (coordinate 12) (![⟨76161, by decide⟩,⟨76216, by decide⟩,⟨76258, by decide⟩,⟨76275, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5664_76276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5664 ⟨76276, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5664
    ⟨76276, by decide⟩ (by decide) (![⟨76161, by decide⟩,⟨76216, by decide⟩,⟨76258, by decide⟩,⟨76275, by decide⟩]) unmarked_context_12_5664_76276 node_context_12_5664_76276
  intro a
  fin_cases a
  · exact context_13_22656_76161
  · exact context_13_22657_76216
  · exact context_13_22658_76258
  · exact context_13_22659_76275

theorem selected_cut_02335 : selected 8 ⟨76300, by decide⟩
    (prefixPartial 13 22660) = some ⟨13, 2, 0, 76300, 22660, 1805, 16384⟩ := by
  decide +kernel

theorem context_13_22660_76300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22660 ⟨76300, by decide⟩ :=
  accepted_of_selected 13 22660 ⟨76300, by decide⟩ ⟨13, 2, 0, 76300, 22660, 1805, 16384⟩
    (by decide) selected_cut_02335

theorem selected_cut_02336 : selected 8 ⟨76339, by decide⟩
    (prefixPartial 13 22661) = some ⟨13, 2, 0, 76339, 22661, 2997, 16384⟩ := by
  decide +kernel

theorem context_13_22661_76339 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22661 ⟨76339, by decide⟩ :=
  accepted_of_selected 13 22661 ⟨76339, by decide⟩ ⟨13, 2, 0, 76339, 22661, 2997, 16384⟩
    (by decide) selected_cut_02336

theorem selected_cut_02337 : selected 8 ⟨76362, by decide⟩
    (prefixPartial 13 22662) = some ⟨13, 2, 0, 76362, 22662, 1993, 16384⟩ := by
  decide +kernel

theorem context_13_22662_76362 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22662 ⟨76362, by decide⟩ :=
  accepted_of_selected 13 22662 ⟨76362, by decide⟩ ⟨13, 2, 0, 76362, 22662, 1993, 16384⟩
    (by decide) selected_cut_02337

theorem selected_cut_02338 : selected 8 ⟨76377, by decide⟩
    (prefixPartial 13 22663) = some ⟨13, 2, 0, 76377, 22663, 1097, 16384⟩ := by
  decide +kernel

theorem context_13_22663_76377 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22663 ⟨76377, by decide⟩ :=
  accepted_of_selected 13 22663 ⟨76377, by decide⟩ ⟨13, 2, 0, 76377, 22663, 1097, 16384⟩
    (by decide) selected_cut_02338

theorem unmarked_context_12_5665_76378 : frontier 9 ⟨76378, by decide⟩
    (prefixCache 12 5665) (prefixPartial 12 5665) = false := by
  decide +kernel

theorem node_context_12_5665_76378 : EJMOriginalGlobalDAGData.nodes 9 ⟨76378, by decide⟩ =
    .split (coordinate 12) (![⟨76300, by decide⟩,⟨76339, by decide⟩,⟨76362, by decide⟩,⟨76377, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5665_76378 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5665 ⟨76378, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5665
    ⟨76378, by decide⟩ (by decide) (![⟨76300, by decide⟩,⟨76339, by decide⟩,⟨76362, by decide⟩,⟨76377, by decide⟩]) unmarked_context_12_5665_76378 node_context_12_5665_76378
  intro a
  fin_cases a
  · exact context_13_22660_76300
  · exact context_13_22661_76339
  · exact context_13_22662_76362
  · exact context_13_22663_76377

theorem selected_cut_02339 : selected 8 ⟨76402, by decide⟩
    (prefixPartial 13 22664) = some ⟨13, 2, 0, 76402, 22664, 1697, 16384⟩ := by
  decide +kernel

theorem context_13_22664_76402 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22664 ⟨76402, by decide⟩ :=
  accepted_of_selected 13 22664 ⟨76402, by decide⟩ ⟨13, 2, 0, 76402, 22664, 1697, 16384⟩
    (by decide) selected_cut_02339

theorem selected_cut_02340 : selected 8 ⟨76432, by decide⟩
    (prefixPartial 13 22665) = some ⟨13, 2, 0, 76432, 22665, 2773, 16384⟩ := by
  decide +kernel

theorem context_13_22665_76432 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22665 ⟨76432, by decide⟩ :=
  accepted_of_selected 13 22665 ⟨76432, by decide⟩ ⟨13, 2, 0, 76432, 22665, 2773, 16384⟩
    (by decide) selected_cut_02340

theorem selected_cut_02341 : selected 8 ⟨76454, by decide⟩
    (prefixPartial 13 22666) = some ⟨13, 2, 0, 76454, 22666, 1793, 16384⟩ := by
  decide +kernel

theorem context_13_22666_76454 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22666 ⟨76454, by decide⟩ :=
  accepted_of_selected 13 22666 ⟨76454, by decide⟩ ⟨13, 2, 0, 76454, 22666, 1793, 16384⟩
    (by decide) selected_cut_02341

theorem selected_cut_02342 : selected 8 ⟨76465, by decide⟩
    (prefixPartial 13 22667) = some ⟨13, 2, 0, 76465, 22667, 1097, 16384⟩ := by
  decide +kernel

theorem context_13_22667_76465 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22667 ⟨76465, by decide⟩ :=
  accepted_of_selected 13 22667 ⟨76465, by decide⟩ ⟨13, 2, 0, 76465, 22667, 1097, 16384⟩
    (by decide) selected_cut_02342

theorem unmarked_context_12_5666_76466 : frontier 9 ⟨76466, by decide⟩
    (prefixCache 12 5666) (prefixPartial 12 5666) = false := by
  decide +kernel

theorem node_context_12_5666_76466 : EJMOriginalGlobalDAGData.nodes 9 ⟨76466, by decide⟩ =
    .split (coordinate 12) (![⟨76402, by decide⟩,⟨76432, by decide⟩,⟨76454, by decide⟩,⟨76465, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5666_76466 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5666 ⟨76466, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5666
    ⟨76466, by decide⟩ (by decide) (![⟨76402, by decide⟩,⟨76432, by decide⟩,⟨76454, by decide⟩,⟨76465, by decide⟩]) unmarked_context_12_5666_76466 node_context_12_5666_76466
  intro a
  fin_cases a
  · exact context_13_22664_76402
  · exact context_13_22665_76432
  · exact context_13_22666_76454
  · exact context_13_22667_76465

theorem selected_cut_02343 : selected 8 ⟨76490, by decide⟩
    (prefixPartial 13 22668) = some ⟨13, 2, 0, 76490, 22668, 1797, 16384⟩ := by
  decide +kernel

theorem context_13_22668_76490 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22668 ⟨76490, by decide⟩ :=
  accepted_of_selected 13 22668 ⟨76490, by decide⟩ ⟨13, 2, 0, 76490, 22668, 1797, 16384⟩
    (by decide) selected_cut_02343

theorem selected_cut_02344 : selected 8 ⟨76530, by decide⟩
    (prefixPartial 13 22669) = some ⟨13, 2, 0, 76530, 22669, 3113, 16384⟩ := by
  decide +kernel

theorem context_13_22669_76530 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22669 ⟨76530, by decide⟩ :=
  accepted_of_selected 13 22669 ⟨76530, by decide⟩ ⟨13, 2, 0, 76530, 22669, 3113, 16384⟩
    (by decide) selected_cut_02344

theorem selected_cut_02345 : selected 8 ⟨76556, by decide⟩
    (prefixPartial 13 22670) = some ⟨13, 2, 0, 76556, 22670, 2137, 16384⟩ := by
  decide +kernel

theorem context_13_22670_76556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22670 ⟨76556, by decide⟩ :=
  accepted_of_selected 13 22670 ⟨76556, by decide⟩ ⟨13, 2, 0, 76556, 22670, 2137, 16384⟩
    (by decide) selected_cut_02345

theorem selected_cut_02346 : selected 8 ⟨76572, by decide⟩
    (prefixPartial 13 22671) = some ⟨13, 2, 0, 76572, 22671, 1101, 16384⟩ := by
  decide +kernel

theorem context_13_22671_76572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22671 ⟨76572, by decide⟩ :=
  accepted_of_selected 13 22671 ⟨76572, by decide⟩ ⟨13, 2, 0, 76572, 22671, 1101, 16384⟩
    (by decide) selected_cut_02346

theorem unmarked_context_12_5667_76573 : frontier 9 ⟨76573, by decide⟩
    (prefixCache 12 5667) (prefixPartial 12 5667) = false := by
  decide +kernel

theorem node_context_12_5667_76573 : EJMOriginalGlobalDAGData.nodes 9 ⟨76573, by decide⟩ =
    .split (coordinate 12) (![⟨76490, by decide⟩,⟨76530, by decide⟩,⟨76556, by decide⟩,⟨76572, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5667_76573 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5667 ⟨76573, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5667
    ⟨76573, by decide⟩ (by decide) (![⟨76490, by decide⟩,⟨76530, by decide⟩,⟨76556, by decide⟩,⟨76572, by decide⟩]) unmarked_context_12_5667_76573 node_context_12_5667_76573
  intro a
  fin_cases a
  · exact context_13_22668_76490
  · exact context_13_22669_76530
  · exact context_13_22670_76556
  · exact context_13_22671_76572

theorem unmarked_context_11_1416_76574 : frontier 10 ⟨76574, by decide⟩
    (prefixCache 11 1416) (prefixPartial 11 1416) = false := by
  decide +kernel

theorem node_context_11_1416_76574 : EJMOriginalGlobalDAGData.nodes 10 ⟨76574, by decide⟩ =
    .split (coordinate 11) (![⟨76276, by decide⟩,⟨76378, by decide⟩,⟨76466, by decide⟩,⟨76573, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1416_76574 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1416 ⟨76574, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1416
    ⟨76574, by decide⟩ (by decide) (![⟨76276, by decide⟩,⟨76378, by decide⟩,⟨76466, by decide⟩,⟨76573, by decide⟩]) unmarked_context_11_1416_76574 node_context_11_1416_76574
  intro a
  fin_cases a
  · exact context_12_5664_76276
  · exact context_12_5665_76378
  · exact context_12_5666_76466
  · exact context_12_5667_76573

theorem selected_cut_02347 : selected 8 ⟨76610, by decide⟩
    (prefixPartial 13 22672) = some ⟨13, 2, 0, 76610, 22672, 2185, 16384⟩ := by
  decide +kernel

theorem context_13_22672_76610 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22672 ⟨76610, by decide⟩ :=
  accepted_of_selected 13 22672 ⟨76610, by decide⟩ ⟨13, 2, 0, 76610, 22672, 2185, 16384⟩
    (by decide) selected_cut_02347

theorem selected_cut_02348 : selected 8 ⟨76673, by decide⟩
    (prefixPartial 13 22673) = some ⟨13, 2, 0, 76673, 22673, 3825, 16384⟩ := by
  decide +kernel

theorem context_13_22673_76673 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22673 ⟨76673, by decide⟩ :=
  accepted_of_selected 13 22673 ⟨76673, by decide⟩ ⟨13, 2, 0, 76673, 22673, 3825, 16384⟩
    (by decide) selected_cut_02348

theorem selected_cut_02349 : selected 8 ⟨76728, by decide⟩
    (prefixPartial 13 22674) = some ⟨13, 2, 0, 76728, 22674, 2789, 16384⟩ := by
  decide +kernel

theorem context_13_22674_76728 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22674 ⟨76728, by decide⟩ :=
  accepted_of_selected 13 22674 ⟨76728, by decide⟩ ⟨13, 2, 0, 76728, 22674, 2789, 16384⟩
    (by decide) selected_cut_02349

theorem selected_cut_02350 : selected 8 ⟨76759, by decide⟩
    (prefixPartial 13 22675) = some ⟨13, 2, 0, 76759, 22675, 1333, 16384⟩ := by
  decide +kernel

theorem context_13_22675_76759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22675 ⟨76759, by decide⟩ :=
  accepted_of_selected 13 22675 ⟨76759, by decide⟩ ⟨13, 2, 0, 76759, 22675, 1333, 16384⟩
    (by decide) selected_cut_02350

theorem unmarked_context_12_5668_76760 : frontier 9 ⟨76760, by decide⟩
    (prefixCache 12 5668) (prefixPartial 12 5668) = false := by
  decide +kernel

theorem node_context_12_5668_76760 : EJMOriginalGlobalDAGData.nodes 9 ⟨76760, by decide⟩ =
    .split (coordinate 12) (![⟨76610, by decide⟩,⟨76673, by decide⟩,⟨76728, by decide⟩,⟨76759, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5668_76760 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5668 ⟨76760, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5668
    ⟨76760, by decide⟩ (by decide) (![⟨76610, by decide⟩,⟨76673, by decide⟩,⟨76728, by decide⟩,⟨76759, by decide⟩]) unmarked_context_12_5668_76760 node_context_12_5668_76760
  intro a
  fin_cases a
  · exact context_13_22672_76610
  · exact context_13_22673_76673
  · exact context_13_22674_76728
  · exact context_13_22675_76759

theorem selected_cut_02351 : selected 8 ⟨76779, by decide⟩
    (prefixPartial 13 22676) = some ⟨13, 2, 0, 76779, 22676, 1609, 16384⟩ := by
  decide +kernel

theorem context_13_22676_76779 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22676 ⟨76779, by decide⟩ :=
  accepted_of_selected 13 22676 ⟨76779, by decide⟩ ⟨13, 2, 0, 76779, 22676, 1609, 16384⟩
    (by decide) selected_cut_02351

theorem selected_cut_02352 : selected 8 ⟨76810, by decide⟩
    (prefixPartial 13 22677) = some ⟨13, 2, 0, 76810, 22677, 2693, 16384⟩ := by
  decide +kernel

theorem context_13_22677_76810 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22677 ⟨76810, by decide⟩ :=
  accepted_of_selected 13 22677 ⟨76810, by decide⟩ ⟨13, 2, 0, 76810, 22677, 2693, 16384⟩
    (by decide) selected_cut_02352

theorem selected_cut_02353 : selected 8 ⟨76834, by decide⟩
    (prefixPartial 13 22678) = some ⟨13, 2, 0, 76834, 22678, 1941, 16384⟩ := by
  decide +kernel

theorem context_13_22678_76834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22678 ⟨76834, by decide⟩ :=
  accepted_of_selected 13 22678 ⟨76834, by decide⟩ ⟨13, 2, 0, 76834, 22678, 1941, 16384⟩
    (by decide) selected_cut_02353

theorem selected_cut_02354 : selected 8 ⟨76844, by decide⟩
    (prefixPartial 13 22679) = some ⟨13, 2, 0, 76844, 22679, 1093, 16384⟩ := by
  decide +kernel

theorem context_13_22679_76844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22679 ⟨76844, by decide⟩ :=
  accepted_of_selected 13 22679 ⟨76844, by decide⟩ ⟨13, 2, 0, 76844, 22679, 1093, 16384⟩
    (by decide) selected_cut_02354

theorem unmarked_context_12_5669_76845 : frontier 9 ⟨76845, by decide⟩
    (prefixCache 12 5669) (prefixPartial 12 5669) = false := by
  decide +kernel

theorem node_context_12_5669_76845 : EJMOriginalGlobalDAGData.nodes 9 ⟨76845, by decide⟩ =
    .split (coordinate 12) (![⟨76779, by decide⟩,⟨76810, by decide⟩,⟨76834, by decide⟩,⟨76844, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5669_76845 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5669 ⟨76845, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5669
    ⟨76845, by decide⟩ (by decide) (![⟨76779, by decide⟩,⟨76810, by decide⟩,⟨76834, by decide⟩,⟨76844, by decide⟩]) unmarked_context_12_5669_76845 node_context_12_5669_76845
  intro a
  fin_cases a
  · exact context_13_22676_76779
  · exact context_13_22677_76810
  · exact context_13_22678_76834
  · exact context_13_22679_76844

theorem selected_cut_02355 : selected 8 ⟨76874, by decide⟩
    (prefixPartial 13 22680) = some ⟨13, 2, 0, 76874, 22680, 1581, 16384⟩ := by
  decide +kernel

theorem context_13_22680_76874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22680 ⟨76874, by decide⟩ :=
  accepted_of_selected 13 22680 ⟨76874, by decide⟩ ⟨13, 2, 0, 76874, 22680, 1581, 16384⟩
    (by decide) selected_cut_02355

theorem selected_cut_02356 : selected 8 ⟨76903, by decide⟩
    (prefixPartial 13 22681) = some ⟨13, 2, 0, 76903, 22681, 2457, 16384⟩ := by
  decide +kernel

theorem context_13_22681_76903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22681 ⟨76903, by decide⟩ :=
  accepted_of_selected 13 22681 ⟨76903, by decide⟩ ⟨13, 2, 0, 76903, 22681, 2457, 16384⟩
    (by decide) selected_cut_02356

theorem selected_cut_02357 : selected 8 ⟨76926, by decide⟩
    (prefixPartial 13 22682) = some ⟨13, 2, 0, 76926, 22682, 1713, 16384⟩ := by
  decide +kernel

theorem context_13_22682_76926 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22682 ⟨76926, by decide⟩ :=
  accepted_of_selected 13 22682 ⟨76926, by decide⟩ ⟨13, 2, 0, 76926, 22682, 1713, 16384⟩
    (by decide) selected_cut_02357

theorem selected_cut_02358 : selected 8 ⟨76934, by decide⟩
    (prefixPartial 13 22683) = some ⟨13, 2, 0, 76934, 22683, 1121, 16384⟩ := by
  decide +kernel

theorem context_13_22683_76934 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22683 ⟨76934, by decide⟩ :=
  accepted_of_selected 13 22683 ⟨76934, by decide⟩ ⟨13, 2, 0, 76934, 22683, 1121, 16384⟩
    (by decide) selected_cut_02358

theorem unmarked_context_12_5670_76935 : frontier 9 ⟨76935, by decide⟩
    (prefixCache 12 5670) (prefixPartial 12 5670) = false := by
  decide +kernel

theorem node_context_12_5670_76935 : EJMOriginalGlobalDAGData.nodes 9 ⟨76935, by decide⟩ =
    .split (coordinate 12) (![⟨76874, by decide⟩,⟨76903, by decide⟩,⟨76926, by decide⟩,⟨76934, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5670_76935 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5670 ⟨76935, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5670
    ⟨76935, by decide⟩ (by decide) (![⟨76874, by decide⟩,⟨76903, by decide⟩,⟨76926, by decide⟩,⟨76934, by decide⟩]) unmarked_context_12_5670_76935 node_context_12_5670_76935
  intro a
  fin_cases a
  · exact context_13_22680_76874
  · exact context_13_22681_76903
  · exact context_13_22682_76926
  · exact context_13_22683_76934

theorem selected_cut_02359 : selected 8 ⟨76961, by decide⟩
    (prefixPartial 13 22684) = some ⟨13, 2, 0, 76961, 22684, 1669, 16384⟩ := by
  decide +kernel

theorem context_13_22684_76961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22684 ⟨76961, by decide⟩ :=
  accepted_of_selected 13 22684 ⟨76961, by decide⟩ ⟨13, 2, 0, 76961, 22684, 1669, 16384⟩
    (by decide) selected_cut_02359

theorem selected_cut_02360 : selected 8 ⟨76991, by decide⟩
    (prefixPartial 13 22685) = some ⟨13, 2, 0, 76991, 22685, 2741, 16384⟩ := by
  decide +kernel

theorem context_13_22685_76991 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22685 ⟨76991, by decide⟩ :=
  accepted_of_selected 13 22685 ⟨76991, by decide⟩ ⟨13, 2, 0, 76991, 22685, 2741, 16384⟩
    (by decide) selected_cut_02360

theorem selected_cut_02361 : selected 8 ⟨77025, by decide⟩
    (prefixPartial 13 22686) = some ⟨13, 2, 0, 77025, 22686, 2313, 16384⟩ := by
  decide +kernel

theorem context_13_22686_77025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22686 ⟨77025, by decide⟩ :=
  accepted_of_selected 13 22686 ⟨77025, by decide⟩ ⟨13, 2, 0, 77025, 22686, 2313, 16384⟩
    (by decide) selected_cut_02361

theorem selected_cut_02362 : selected 8 ⟨77035, by decide⟩
    (prefixPartial 13 22687) = some ⟨13, 2, 0, 77035, 22687, 1093, 16384⟩ := by
  decide +kernel

theorem context_13_22687_77035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22687 ⟨77035, by decide⟩ :=
  accepted_of_selected 13 22687 ⟨77035, by decide⟩ ⟨13, 2, 0, 77035, 22687, 1093, 16384⟩
    (by decide) selected_cut_02362

theorem unmarked_context_12_5671_77036 : frontier 9 ⟨77036, by decide⟩
    (prefixCache 12 5671) (prefixPartial 12 5671) = false := by
  decide +kernel

theorem node_context_12_5671_77036 : EJMOriginalGlobalDAGData.nodes 9 ⟨77036, by decide⟩ =
    .split (coordinate 12) (![⟨76961, by decide⟩,⟨76991, by decide⟩,⟨77025, by decide⟩,⟨77035, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5671_77036 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5671 ⟨77036, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5671
    ⟨77036, by decide⟩ (by decide) (![⟨76961, by decide⟩,⟨76991, by decide⟩,⟨77025, by decide⟩,⟨77035, by decide⟩]) unmarked_context_12_5671_77036 node_context_12_5671_77036
  intro a
  fin_cases a
  · exact context_13_22684_76961
  · exact context_13_22685_76991
  · exact context_13_22686_77025
  · exact context_13_22687_77035

theorem unmarked_context_11_1417_77037 : frontier 10 ⟨77037, by decide⟩
    (prefixCache 11 1417) (prefixPartial 11 1417) = false := by
  decide +kernel

theorem node_context_11_1417_77037 : EJMOriginalGlobalDAGData.nodes 10 ⟨77037, by decide⟩ =
    .split (coordinate 11) (![⟨76760, by decide⟩,⟨76845, by decide⟩,⟨76935, by decide⟩,⟨77036, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1417_77037 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1417 ⟨77037, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1417
    ⟨77037, by decide⟩ (by decide) (![⟨76760, by decide⟩,⟨76845, by decide⟩,⟨76935, by decide⟩,⟨77036, by decide⟩]) unmarked_context_11_1417_77037 node_context_11_1417_77037
  intro a
  fin_cases a
  · exact context_12_5668_76760
  · exact context_12_5669_76845
  · exact context_12_5670_76935
  · exact context_12_5671_77036

theorem selected_cut_02363 : selected 8 ⟨77064, by decide⟩
    (prefixPartial 13 22688) = some ⟨13, 2, 0, 77064, 22688, 1685, 16384⟩ := by
  decide +kernel

theorem context_13_22688_77064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22688 ⟨77064, by decide⟩ :=
  accepted_of_selected 13 22688 ⟨77064, by decide⟩ ⟨13, 2, 0, 77064, 22688, 1685, 16384⟩
    (by decide) selected_cut_02363

theorem selected_cut_02364 : selected 8 ⟨77106, by decide⟩
    (prefixPartial 13 22689) = some ⟨13, 2, 0, 77106, 22689, 3385, 16384⟩ := by
  decide +kernel

theorem context_13_22689_77106 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22689 ⟨77106, by decide⟩ :=
  accepted_of_selected 13 22689 ⟨77106, by decide⟩ ⟨13, 2, 0, 77106, 22689, 3385, 16384⟩
    (by decide) selected_cut_02364

theorem selected_cut_02365 : selected 8 ⟨77136, by decide⟩
    (prefixPartial 13 22690) = some ⟨13, 2, 0, 77136, 22690, 2453, 16384⟩ := by
  decide +kernel

theorem context_13_22690_77136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22690 ⟨77136, by decide⟩ :=
  accepted_of_selected 13 22690 ⟨77136, by decide⟩ ⟨13, 2, 0, 77136, 22690, 2453, 16384⟩
    (by decide) selected_cut_02365

theorem selected_cut_02366 : selected 8 ⟨77161, by decide⟩
    (prefixPartial 13 22691) = some ⟨13, 2, 0, 77161, 22691, 1341, 16384⟩ := by
  decide +kernel

theorem context_13_22691_77161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22691 ⟨77161, by decide⟩ :=
  accepted_of_selected 13 22691 ⟨77161, by decide⟩ ⟨13, 2, 0, 77161, 22691, 1341, 16384⟩
    (by decide) selected_cut_02366

theorem unmarked_context_12_5672_77162 : frontier 9 ⟨77162, by decide⟩
    (prefixCache 12 5672) (prefixPartial 12 5672) = false := by
  decide +kernel

theorem node_context_12_5672_77162 : EJMOriginalGlobalDAGData.nodes 9 ⟨77162, by decide⟩ =
    .split (coordinate 12) (![⟨77064, by decide⟩,⟨77106, by decide⟩,⟨77136, by decide⟩,⟨77161, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5672_77162 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5672 ⟨77162, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5672
    ⟨77162, by decide⟩ (by decide) (![⟨77064, by decide⟩,⟨77106, by decide⟩,⟨77136, by decide⟩,⟨77161, by decide⟩]) unmarked_context_12_5672_77162 node_context_12_5672_77162
  intro a
  fin_cases a
  · exact context_13_22688_77064
  · exact context_13_22689_77106
  · exact context_13_22690_77136
  · exact context_13_22691_77161

theorem selected_cut_02367 : selected 8 ⟨77179, by decide⟩
    (prefixPartial 13 22692) = some ⟨13, 2, 0, 77179, 22692, 1469, 16384⟩ := by
  decide +kernel

theorem context_13_22692_77179 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22692 ⟨77179, by decide⟩ :=
  accepted_of_selected 13 22692 ⟨77179, by decide⟩ ⟨13, 2, 0, 77179, 22692, 1469, 16384⟩
    (by decide) selected_cut_02367

theorem selected_cut_02368 : selected 8 ⟨77213, by decide⟩
    (prefixPartial 13 22693) = some ⟨13, 2, 0, 77213, 22693, 2717, 16384⟩ := by
  decide +kernel

theorem context_13_22693_77213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22693 ⟨77213, by decide⟩ :=
  accepted_of_selected 13 22693 ⟨77213, by decide⟩ ⟨13, 2, 0, 77213, 22693, 2717, 16384⟩
    (by decide) selected_cut_02368

theorem selected_cut_02369 : selected 8 ⟨77235, by decide⟩
    (prefixPartial 13 22694) = some ⟨13, 2, 0, 77235, 22694, 1941, 16384⟩ := by
  decide +kernel

theorem context_13_22694_77235 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22694 ⟨77235, by decide⟩ :=
  accepted_of_selected 13 22694 ⟨77235, by decide⟩ ⟨13, 2, 0, 77235, 22694, 1941, 16384⟩
    (by decide) selected_cut_02369

theorem selected_cut_02370 : selected 8 ⟨77246, by decide⟩
    (prefixPartial 13 22695) = some ⟨13, 2, 0, 77246, 22695, 1165, 16384⟩ := by
  decide +kernel

theorem context_13_22695_77246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22695 ⟨77246, by decide⟩ :=
  accepted_of_selected 13 22695 ⟨77246, by decide⟩ ⟨13, 2, 0, 77246, 22695, 1165, 16384⟩
    (by decide) selected_cut_02370

theorem unmarked_context_12_5673_77247 : frontier 9 ⟨77247, by decide⟩
    (prefixCache 12 5673) (prefixPartial 12 5673) = false := by
  decide +kernel

theorem node_context_12_5673_77247 : EJMOriginalGlobalDAGData.nodes 9 ⟨77247, by decide⟩ =
    .split (coordinate 12) (![⟨77179, by decide⟩,⟨77213, by decide⟩,⟨77235, by decide⟩,⟨77246, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5673_77247 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5673 ⟨77247, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5673
    ⟨77247, by decide⟩ (by decide) (![⟨77179, by decide⟩,⟨77213, by decide⟩,⟨77235, by decide⟩,⟨77246, by decide⟩]) unmarked_context_12_5673_77247 node_context_12_5673_77247
  intro a
  fin_cases a
  · exact context_13_22692_77179
  · exact context_13_22693_77213
  · exact context_13_22694_77235
  · exact context_13_22695_77246

theorem selected_cut_02371 : selected 8 ⟨77273, by decide⟩
    (prefixPartial 13 22696) = some ⟨13, 2, 0, 77273, 22696, 1961, 16384⟩ := by
  decide +kernel

theorem context_13_22696_77273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22696 ⟨77273, by decide⟩ :=
  accepted_of_selected 13 22696 ⟨77273, by decide⟩ ⟨13, 2, 0, 77273, 22696, 1961, 16384⟩
    (by decide) selected_cut_02371

theorem selected_cut_02372 : selected 8 ⟨77331, by decide⟩
    (prefixPartial 13 22697) = some ⟨13, 2, 0, 77331, 22697, 4057, 16384⟩ := by
  decide +kernel

theorem context_13_22697_77331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22697 ⟨77331, by decide⟩ :=
  accepted_of_selected 13 22697 ⟨77331, by decide⟩ ⟨13, 2, 0, 77331, 22697, 4057, 16384⟩
    (by decide) selected_cut_02372

theorem selected_cut_02373 : selected 8 ⟨77367, by decide⟩
    (prefixPartial 13 22698) = some ⟨13, 2, 0, 77367, 22698, 2713, 16384⟩ := by
  decide +kernel

theorem context_13_22698_77367 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22698 ⟨77367, by decide⟩ :=
  accepted_of_selected 13 22698 ⟨77367, by decide⟩ ⟨13, 2, 0, 77367, 22698, 2713, 16384⟩
    (by decide) selected_cut_02373

theorem selected_cut_02374 : selected 8 ⟨77390, by decide⟩
    (prefixPartial 13 22699) = some ⟨13, 2, 0, 77390, 22699, 1517, 16384⟩ := by
  decide +kernel

theorem context_13_22699_77390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22699 ⟨77390, by decide⟩ :=
  accepted_of_selected 13 22699 ⟨77390, by decide⟩ ⟨13, 2, 0, 77390, 22699, 1517, 16384⟩
    (by decide) selected_cut_02374

theorem unmarked_context_12_5674_77391 : frontier 9 ⟨77391, by decide⟩
    (prefixCache 12 5674) (prefixPartial 12 5674) = false := by
  decide +kernel

theorem node_context_12_5674_77391 : EJMOriginalGlobalDAGData.nodes 9 ⟨77391, by decide⟩ =
    .split (coordinate 12) (![⟨77273, by decide⟩,⟨77331, by decide⟩,⟨77367, by decide⟩,⟨77390, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5674_77391 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5674 ⟨77391, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5674
    ⟨77391, by decide⟩ (by decide) (![⟨77273, by decide⟩,⟨77331, by decide⟩,⟨77367, by decide⟩,⟨77390, by decide⟩]) unmarked_context_12_5674_77391 node_context_12_5674_77391
  intro a
  fin_cases a
  · exact context_13_22696_77273
  · exact context_13_22697_77331
  · exact context_13_22698_77367
  · exact context_13_22699_77390

theorem selected_cut_02375 : selected 8 ⟨77411, by decide⟩
    (prefixPartial 13 22700) = some ⟨13, 2, 0, 77411, 22700, 1237, 16384⟩ := by
  decide +kernel

theorem context_13_22700_77411 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22700 ⟨77411, by decide⟩ :=
  accepted_of_selected 13 22700 ⟨77411, by decide⟩ ⟨13, 2, 0, 77411, 22700, 1237, 16384⟩
    (by decide) selected_cut_02375

theorem selected_cut_02376 : selected 8 ⟨77441, by decide⟩
    (prefixPartial 13 22701) = some ⟨13, 2, 0, 77441, 22701, 2817, 16384⟩ := by
  decide +kernel

theorem context_13_22701_77441 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22701 ⟨77441, by decide⟩ :=
  accepted_of_selected 13 22701 ⟨77441, by decide⟩ ⟨13, 2, 0, 77441, 22701, 2817, 16384⟩
    (by decide) selected_cut_02376

theorem selected_cut_02377 : selected 8 ⟨77466, by decide⟩
    (prefixPartial 13 22702) = some ⟨13, 2, 0, 77466, 22702, 2005, 16384⟩ := by
  decide +kernel

theorem context_13_22702_77466 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22702 ⟨77466, by decide⟩ :=
  accepted_of_selected 13 22702 ⟨77466, by decide⟩ ⟨13, 2, 0, 77466, 22702, 2005, 16384⟩
    (by decide) selected_cut_02377

theorem selected_cut_02378 : selected 8 ⟨77476, by decide⟩
    (prefixPartial 13 22703) = some ⟨13, 2, 0, 77476, 22703, 1085, 16384⟩ := by
  decide +kernel

theorem context_13_22703_77476 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22703 ⟨77476, by decide⟩ :=
  accepted_of_selected 13 22703 ⟨77476, by decide⟩ ⟨13, 2, 0, 77476, 22703, 1085, 16384⟩
    (by decide) selected_cut_02378

theorem unmarked_context_12_5675_77477 : frontier 9 ⟨77477, by decide⟩
    (prefixCache 12 5675) (prefixPartial 12 5675) = false := by
  decide +kernel

theorem node_context_12_5675_77477 : EJMOriginalGlobalDAGData.nodes 9 ⟨77477, by decide⟩ =
    .split (coordinate 12) (![⟨77411, by decide⟩,⟨77441, by decide⟩,⟨77466, by decide⟩,⟨77476, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5675_77477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5675 ⟨77477, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5675
    ⟨77477, by decide⟩ (by decide) (![⟨77411, by decide⟩,⟨77441, by decide⟩,⟨77466, by decide⟩,⟨77476, by decide⟩]) unmarked_context_12_5675_77477 node_context_12_5675_77477
  intro a
  fin_cases a
  · exact context_13_22700_77411
  · exact context_13_22701_77441
  · exact context_13_22702_77466
  · exact context_13_22703_77476

theorem unmarked_context_11_1418_77478 : frontier 10 ⟨77478, by decide⟩
    (prefixCache 11 1418) (prefixPartial 11 1418) = false := by
  decide +kernel

theorem node_context_11_1418_77478 : EJMOriginalGlobalDAGData.nodes 10 ⟨77478, by decide⟩ =
    .split (coordinate 11) (![⟨77162, by decide⟩,⟨77247, by decide⟩,⟨77391, by decide⟩,⟨77477, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1418_77478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1418 ⟨77478, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1418
    ⟨77478, by decide⟩ (by decide) (![⟨77162, by decide⟩,⟨77247, by decide⟩,⟨77391, by decide⟩,⟨77477, by decide⟩]) unmarked_context_11_1418_77478 node_context_11_1418_77478
  intro a
  fin_cases a
  · exact context_12_5672_77162
  · exact context_12_5673_77247
  · exact context_12_5674_77391
  · exact context_12_5675_77477

theorem selected_cut_02379 : selected 8 ⟨77503, by decide⟩
    (prefixPartial 13 22704) = some ⟨13, 2, 0, 77503, 22704, 1433, 16384⟩ := by
  decide +kernel

theorem context_13_22704_77503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22704 ⟨77503, by decide⟩ :=
  accepted_of_selected 13 22704 ⟨77503, by decide⟩ ⟨13, 2, 0, 77503, 22704, 1433, 16384⟩
    (by decide) selected_cut_02379

theorem selected_cut_02380 : selected 8 ⟨77578, by decide⟩
    (prefixPartial 13 22705) = some ⟨13, 2, 0, 77578, 22705, 4077, 16384⟩ := by
  decide +kernel

theorem context_13_22705_77578 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22705 ⟨77578, by decide⟩ :=
  accepted_of_selected 13 22705 ⟨77578, by decide⟩ ⟨13, 2, 0, 77578, 22705, 4077, 16384⟩
    (by decide) selected_cut_02380

theorem selected_cut_02381 : selected 8 ⟨77628, by decide⟩
    (prefixPartial 13 22706) = some ⟨13, 2, 0, 77628, 22706, 3029, 16384⟩ := by
  decide +kernel

theorem context_13_22706_77628 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22706 ⟨77628, by decide⟩ :=
  accepted_of_selected 13 22706 ⟨77628, by decide⟩ ⟨13, 2, 0, 77628, 22706, 3029, 16384⟩
    (by decide) selected_cut_02381

theorem selected_cut_02382 : selected 8 ⟨77649, by decide⟩
    (prefixPartial 13 22707) = some ⟨13, 2, 0, 77649, 22707, 1305, 16384⟩ := by
  decide +kernel

theorem context_13_22707_77649 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22707 ⟨77649, by decide⟩ :=
  accepted_of_selected 13 22707 ⟨77649, by decide⟩ ⟨13, 2, 0, 77649, 22707, 1305, 16384⟩
    (by decide) selected_cut_02382

theorem unmarked_context_12_5676_77650 : frontier 9 ⟨77650, by decide⟩
    (prefixCache 12 5676) (prefixPartial 12 5676) = false := by
  decide +kernel

theorem node_context_12_5676_77650 : EJMOriginalGlobalDAGData.nodes 9 ⟨77650, by decide⟩ =
    .split (coordinate 12) (![⟨77503, by decide⟩,⟨77578, by decide⟩,⟨77628, by decide⟩,⟨77649, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5676_77650 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5676 ⟨77650, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5676
    ⟨77650, by decide⟩ (by decide) (![⟨77503, by decide⟩,⟨77578, by decide⟩,⟨77628, by decide⟩,⟨77649, by decide⟩]) unmarked_context_12_5676_77650 node_context_12_5676_77650
  intro a
  fin_cases a
  · exact context_13_22704_77503
  · exact context_13_22705_77578
  · exact context_13_22706_77628
  · exact context_13_22707_77649

theorem selected_cut_02383 : selected 8 ⟨77669, by decide⟩
    (prefixPartial 13 22708) = some ⟨13, 2, 0, 77669, 22708, 1181, 16384⟩ := by
  decide +kernel

theorem context_13_22708_77669 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22708 ⟨77669, by decide⟩ :=
  accepted_of_selected 13 22708 ⟨77669, by decide⟩ ⟨13, 2, 0, 77669, 22708, 1181, 16384⟩
    (by decide) selected_cut_02383

theorem selected_cut_02384 : selected 8 ⟨77706, by decide⟩
    (prefixPartial 13 22709) = some ⟨13, 2, 0, 77706, 22709, 3117, 16384⟩ := by
  decide +kernel

theorem context_13_22709_77706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22709 ⟨77706, by decide⟩ :=
  accepted_of_selected 13 22709 ⟨77706, by decide⟩ ⟨13, 2, 0, 77706, 22709, 3117, 16384⟩
    (by decide) selected_cut_02384

theorem selected_cut_02385 : selected 8 ⟨77737, by decide⟩
    (prefixPartial 13 22710) = some ⟨13, 2, 0, 77737, 22710, 2245, 16384⟩ := by
  decide +kernel

theorem context_13_22710_77737 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22710 ⟨77737, by decide⟩ :=
  accepted_of_selected 13 22710 ⟨77737, by decide⟩ ⟨13, 2, 0, 77737, 22710, 2245, 16384⟩
    (by decide) selected_cut_02385

theorem selected_cut_02386 : selected 8 ⟨77747, by decide⟩
    (prefixPartial 13 22711) = some ⟨13, 2, 0, 77747, 22711, 1033, 16384⟩ := by
  decide +kernel

theorem context_13_22711_77747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22711 ⟨77747, by decide⟩ :=
  accepted_of_selected 13 22711 ⟨77747, by decide⟩ ⟨13, 2, 0, 77747, 22711, 1033, 16384⟩
    (by decide) selected_cut_02386

theorem unmarked_context_12_5677_77748 : frontier 9 ⟨77748, by decide⟩
    (prefixCache 12 5677) (prefixPartial 12 5677) = false := by
  decide +kernel

theorem node_context_12_5677_77748 : EJMOriginalGlobalDAGData.nodes 9 ⟨77748, by decide⟩ =
    .split (coordinate 12) (![⟨77669, by decide⟩,⟨77706, by decide⟩,⟨77737, by decide⟩,⟨77747, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5677_77748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5677 ⟨77748, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5677
    ⟨77748, by decide⟩ (by decide) (![⟨77669, by decide⟩,⟨77706, by decide⟩,⟨77737, by decide⟩,⟨77747, by decide⟩]) unmarked_context_12_5677_77748 node_context_12_5677_77748
  intro a
  fin_cases a
  · exact context_13_22708_77669
  · exact context_13_22709_77706
  · exact context_13_22710_77737
  · exact context_13_22711_77747

theorem selected_cut_02387 : selected 8 ⟨77767, by decide⟩
    (prefixPartial 13 22712) = some ⟨13, 2, 0, 77767, 22712, 1001, 16384⟩ := by
  decide +kernel

theorem context_13_22712_77767 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22712 ⟨77767, by decide⟩ :=
  accepted_of_selected 13 22712 ⟨77767, by decide⟩ ⟨13, 2, 0, 77767, 22712, 1001, 16384⟩
    (by decide) selected_cut_02387

theorem selected_cut_02388 : selected 8 ⟨77801, by decide⟩
    (prefixPartial 13 22713) = some ⟨13, 2, 0, 77801, 22713, 3061, 16384⟩ := by
  decide +kernel

theorem context_13_22713_77801 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22713 ⟨77801, by decide⟩ :=
  accepted_of_selected 13 22713 ⟨77801, by decide⟩ ⟨13, 2, 0, 77801, 22713, 3061, 16384⟩
    (by decide) selected_cut_02388

theorem selected_cut_02389 : selected 8 ⟨77824, by decide⟩
    (prefixPartial 13 22714) = some ⟨13, 2, 0, 77824, 22714, 1893, 16384⟩ := by
  decide +kernel

theorem context_13_22714_77824 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22714 ⟨77824, by decide⟩ :=
  accepted_of_selected 13 22714 ⟨77824, by decide⟩ ⟨13, 2, 0, 77824, 22714, 1893, 16384⟩
    (by decide) selected_cut_02389

theorem selected_cut_02390 : selected 8 ⟨77840, by decide⟩
    (prefixPartial 13 22715) = some ⟨13, 2, 0, 77840, 22715, 973, 16384⟩ := by
  decide +kernel

theorem context_13_22715_77840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22715 ⟨77840, by decide⟩ :=
  accepted_of_selected 13 22715 ⟨77840, by decide⟩ ⟨13, 2, 0, 77840, 22715, 973, 16384⟩
    (by decide) selected_cut_02390

theorem unmarked_context_12_5678_77841 : frontier 9 ⟨77841, by decide⟩
    (prefixCache 12 5678) (prefixPartial 12 5678) = false := by
  decide +kernel

theorem node_context_12_5678_77841 : EJMOriginalGlobalDAGData.nodes 9 ⟨77841, by decide⟩ =
    .split (coordinate 12) (![⟨77767, by decide⟩,⟨77801, by decide⟩,⟨77824, by decide⟩,⟨77840, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5678_77841 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5678 ⟨77841, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5678
    ⟨77841, by decide⟩ (by decide) (![⟨77767, by decide⟩,⟨77801, by decide⟩,⟨77824, by decide⟩,⟨77840, by decide⟩]) unmarked_context_12_5678_77841 node_context_12_5678_77841
  intro a
  fin_cases a
  · exact context_13_22712_77767
  · exact context_13_22713_77801
  · exact context_13_22714_77824
  · exact context_13_22715_77840

theorem selected_cut_02391 : selected 8 ⟨77860, by decide⟩
    (prefixPartial 13 22716) = some ⟨13, 2, 0, 77860, 22716, 1009, 16384⟩ := by
  decide +kernel

theorem context_13_22716_77860 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22716 ⟨77860, by decide⟩ :=
  accepted_of_selected 13 22716 ⟨77860, by decide⟩ ⟨13, 2, 0, 77860, 22716, 1009, 16384⟩
    (by decide) selected_cut_02391

theorem selected_cut_02392 : selected 8 ⟨77899, by decide⟩
    (prefixPartial 13 22717) = some ⟨13, 2, 0, 77899, 22717, 3165, 16384⟩ := by
  decide +kernel

theorem context_13_22717_77899 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22717 ⟨77899, by decide⟩ :=
  accepted_of_selected 13 22717 ⟨77899, by decide⟩ ⟨13, 2, 0, 77899, 22717, 3165, 16384⟩
    (by decide) selected_cut_02392

theorem selected_cut_02393 : selected 8 ⟨77921, by decide⟩
    (prefixPartial 13 22718) = some ⟨13, 2, 0, 77921, 22718, 2205, 16384⟩ := by
  decide +kernel

theorem context_13_22718_77921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22718 ⟨77921, by decide⟩ :=
  accepted_of_selected 13 22718 ⟨77921, by decide⟩ ⟨13, 2, 0, 77921, 22718, 2205, 16384⟩
    (by decide) selected_cut_02393

theorem selected_cut_02394 : selected 8 ⟨77934, by decide⟩
    (prefixPartial 13 22719) = some ⟨13, 2, 0, 77934, 22719, 1021, 16384⟩ := by
  decide +kernel

theorem context_13_22719_77934 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22719 ⟨77934, by decide⟩ :=
  accepted_of_selected 13 22719 ⟨77934, by decide⟩ ⟨13, 2, 0, 77934, 22719, 1021, 16384⟩
    (by decide) selected_cut_02394

theorem unmarked_context_12_5679_77935 : frontier 9 ⟨77935, by decide⟩
    (prefixCache 12 5679) (prefixPartial 12 5679) = false := by
  decide +kernel

theorem node_context_12_5679_77935 : EJMOriginalGlobalDAGData.nodes 9 ⟨77935, by decide⟩ =
    .split (coordinate 12) (![⟨77860, by decide⟩,⟨77899, by decide⟩,⟨77921, by decide⟩,⟨77934, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5679_77935 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5679 ⟨77935, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5679
    ⟨77935, by decide⟩ (by decide) (![⟨77860, by decide⟩,⟨77899, by decide⟩,⟨77921, by decide⟩,⟨77934, by decide⟩]) unmarked_context_12_5679_77935 node_context_12_5679_77935
  intro a
  fin_cases a
  · exact context_13_22716_77860
  · exact context_13_22717_77899
  · exact context_13_22718_77921
  · exact context_13_22719_77934

theorem unmarked_context_11_1419_77936 : frontier 10 ⟨77936, by decide⟩
    (prefixCache 11 1419) (prefixPartial 11 1419) = false := by
  decide +kernel

theorem node_context_11_1419_77936 : EJMOriginalGlobalDAGData.nodes 10 ⟨77936, by decide⟩ =
    .split (coordinate 11) (![⟨77650, by decide⟩,⟨77748, by decide⟩,⟨77841, by decide⟩,⟨77935, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_1419_77936 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 1419 ⟨77936, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 1419
    ⟨77936, by decide⟩ (by decide) (![⟨77650, by decide⟩,⟨77748, by decide⟩,⟨77841, by decide⟩,⟨77935, by decide⟩]) unmarked_context_11_1419_77936 node_context_11_1419_77936
  intro a
  fin_cases a
  · exact context_12_5676_77650
  · exact context_12_5677_77748
  · exact context_12_5678_77841
  · exact context_12_5679_77935

theorem unmarked_context_10_354_77937 : frontier 11 ⟨77937, by decide⟩
    (prefixCache 10 354) (prefixPartial 10 354) = false := by
  decide +kernel

theorem node_context_10_354_77937 : EJMOriginalGlobalDAGData.nodes 11 ⟨77937, by decide⟩ =
    .split (coordinate 10) (![⟨76574, by decide⟩,⟨77037, by decide⟩,⟨77478, by decide⟩,⟨77936, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_354_77937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 354 ⟨77937, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 354
    ⟨77937, by decide⟩ (by decide) (![⟨76574, by decide⟩,⟨77037, by decide⟩,⟨77478, by decide⟩,⟨77936, by decide⟩]) unmarked_context_10_354_77937 node_context_10_354_77937
  intro a
  fin_cases a
  · exact context_11_1416_76574
  · exact context_11_1417_77037
  · exact context_11_1418_77478
  · exact context_11_1419_77936

theorem selected_cut_02395 : selected 8 ⟨77954, by decide⟩
    (prefixPartial 13 22720) = some ⟨13, 2, 0, 77954, 22720, 1389, 16384⟩ := by
  decide +kernel

theorem context_13_22720_77954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22720 ⟨77954, by decide⟩ :=
  accepted_of_selected 13 22720 ⟨77954, by decide⟩ ⟨13, 2, 0, 77954, 22720, 1389, 16384⟩
    (by decide) selected_cut_02395

theorem selected_cut_02396 : selected 8 ⟨78005, by decide⟩
    (prefixPartial 13 22721) = some ⟨13, 2, 0, 78005, 22721, 3901, 16384⟩ := by
  decide +kernel

theorem context_13_22721_78005 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22721 ⟨78005, by decide⟩ :=
  accepted_of_selected 13 22721 ⟨78005, by decide⟩ ⟨13, 2, 0, 78005, 22721, 3901, 16384⟩
    (by decide) selected_cut_02396

theorem selected_cut_02397 : selected 8 ⟨78040, by decide⟩
    (prefixPartial 13 22722) = some ⟨13, 2, 0, 78040, 22722, 2605, 16384⟩ := by
  decide +kernel

theorem context_13_22722_78040 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22722 ⟨78040, by decide⟩ :=
  accepted_of_selected 13 22722 ⟨78040, by decide⟩ ⟨13, 2, 0, 78040, 22722, 2605, 16384⟩
    (by decide) selected_cut_02397

theorem selected_cut_02398 : selected 8 ⟨78056, by decide⟩
    (prefixPartial 13 22723) = some ⟨13, 2, 0, 78056, 22723, 1233, 16384⟩ := by
  decide +kernel

theorem context_13_22723_78056 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22723 ⟨78056, by decide⟩ :=
  accepted_of_selected 13 22723 ⟨78056, by decide⟩ ⟨13, 2, 0, 78056, 22723, 1233, 16384⟩
    (by decide) selected_cut_02398

theorem unmarked_context_12_5680_78057 : frontier 9 ⟨78057, by decide⟩
    (prefixCache 12 5680) (prefixPartial 12 5680) = false := by
  decide +kernel

theorem node_context_12_5680_78057 : EJMOriginalGlobalDAGData.nodes 9 ⟨78057, by decide⟩ =
    .split (coordinate 12) (![⟨77954, by decide⟩,⟨78005, by decide⟩,⟨78040, by decide⟩,⟨78056, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_5680_78057 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 5680 ⟨78057, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 5680
    ⟨78057, by decide⟩ (by decide) (![⟨77954, by decide⟩,⟨78005, by decide⟩,⟨78040, by decide⟩,⟨78056, by decide⟩]) unmarked_context_12_5680_78057 node_context_12_5680_78057
  intro a
  fin_cases a
  · exact context_13_22720_77954
  · exact context_13_22721_78005
  · exact context_13_22722_78040
  · exact context_13_22723_78056

theorem selected_cut_02399 : selected 8 ⟨78070, by decide⟩
    (prefixPartial 13 22724) = some ⟨13, 2, 0, 78070, 22724, 989, 16384⟩ := by
  decide +kernel

theorem context_13_22724_78070 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22724 ⟨78070, by decide⟩ :=
  accepted_of_selected 13 22724 ⟨78070, by decide⟩ ⟨13, 2, 0, 78070, 22724, 989, 16384⟩
    (by decide) selected_cut_02399

theorem selected_cut_02400 : selected 8 ⟨78120, by decide⟩
    (prefixPartial 13 22725) = some ⟨13, 2, 0, 78120, 22725, 3357, 16384⟩ := by
  decide +kernel

theorem context_13_22725_78120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22725 ⟨78120, by decide⟩ :=
  accepted_of_selected 13 22725 ⟨78120, by decide⟩ ⟨13, 2, 0, 78120, 22725, 3357, 16384⟩
    (by decide) selected_cut_02400

theorem selected_cut_02401 : selected 8 ⟨78145, by decide⟩
    (prefixPartial 13 22726) = some ⟨13, 2, 0, 78145, 22726, 1885, 16384⟩ := by
  decide +kernel

theorem context_13_22726_78145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22726 ⟨78145, by decide⟩ :=
  accepted_of_selected 13 22726 ⟨78145, by decide⟩ ⟨13, 2, 0, 78145, 22726, 1885, 16384⟩
    (by decide) selected_cut_02401

theorem selected_cut_02402 : selected 8 ⟨78156, by decide⟩
    (prefixPartial 13 22727) = some ⟨13, 2, 0, 78156, 22727, 1149, 16384⟩ := by
  decide +kernel

theorem context_13_22727_78156 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 22727 ⟨78156, by decide⟩ :=
  accepted_of_selected 13 22727 ⟨78156, by decide⟩ ⟨13, 2, 0, 78156, 22727, 1149, 16384⟩
    (by decide) selected_cut_02402

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
