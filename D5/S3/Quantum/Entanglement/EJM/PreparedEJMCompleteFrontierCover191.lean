/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover190
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_18339 : selected 9 ⟨469648, by decide⟩
    (prefixPartial 12 71319) = some ⟨12, 2, 0, 469648, 71319, 2653, 65536⟩ := by
  decide +kernel

theorem context_12_71319_469648 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71319 ⟨469648, by decide⟩ :=
  accepted_of_selected 12 71319 ⟨469648, by decide⟩ ⟨12, 2, 0, 469648, 71319, 2653, 65536⟩
    (by decide) selected_cut_18339

theorem unmarked_context_11_17829_469649 : frontier 10 ⟨469649, by decide⟩
    (prefixCache 11 17829) (prefixPartial 11 17829) = false := by
  decide +kernel

theorem node_context_11_17829_469649 : EJMOriginalGlobalDAGData.nodes 10 ⟨469649, by decide⟩ =
    .split (coordinate 11) (![⟨469595, by decide⟩,⟨449506, by decide⟩,⟨469617, by decide⟩,⟨469648, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17829_469649 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17829 ⟨469649, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17829
    ⟨469649, by decide⟩ (by decide) (![⟨469595, by decide⟩,⟨449506, by decide⟩,⟨469617, by decide⟩,⟨469648, by decide⟩]) unmarked_context_11_17829_469649 node_context_11_17829_469649
  intro a
  fin_cases a
  · exact context_12_71316_469595
  · exact context_12_71317_449506
  · exact context_12_71318_469617
  · exact context_12_71319_469648

theorem selected_cut_18340 : selected 9 ⟨469672, by decide⟩
    (prefixPartial 12 71320) = some ⟨12, 2, 0, 469672, 71320, 1817, 65536⟩ := by
  decide +kernel

theorem context_12_71320_469672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71320 ⟨469672, by decide⟩ :=
  accepted_of_selected 12 71320 ⟨469672, by decide⟩ ⟨12, 2, 0, 469672, 71320, 1817, 65536⟩
    (by decide) selected_cut_18340

theorem selected_cut_18341 : selected 9 ⟨469693, by decide⟩
    (prefixPartial 12 71321) = some ⟨12, 2, 0, 469693, 71321, 1745, 65536⟩ := by
  decide +kernel

theorem context_12_71321_469693 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71321 ⟨469693, by decide⟩ :=
  accepted_of_selected 12 71321 ⟨469693, by decide⟩ ⟨12, 2, 0, 469693, 71321, 1745, 65536⟩
    (by decide) selected_cut_18341

theorem selected_cut_18342 : selected 9 ⟨448662, by decide⟩
    (prefixPartial 12 71322) = some ⟨12, 1, 0, 448662, 71322, 1, 65536⟩ := by
  decide +kernel

theorem context_12_71322_448662 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71322 ⟨448662, by decide⟩ :=
  accepted_of_selected 12 71322 ⟨448662, by decide⟩ ⟨12, 1, 0, 448662, 71322, 1, 65536⟩
    (by decide) selected_cut_18342

theorem selected_cut_18343 : selected 9 ⟨469715, by decide⟩
    (prefixPartial 12 71323) = some ⟨12, 2, 0, 469715, 71323, 1865, 65536⟩ := by
  decide +kernel

theorem context_12_71323_469715 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71323 ⟨469715, by decide⟩ :=
  accepted_of_selected 12 71323 ⟨469715, by decide⟩ ⟨12, 2, 0, 469715, 71323, 1865, 65536⟩
    (by decide) selected_cut_18343

theorem unmarked_context_11_17830_469716 : frontier 10 ⟨469716, by decide⟩
    (prefixCache 11 17830) (prefixPartial 11 17830) = false := by
  decide +kernel

theorem node_context_11_17830_469716 : EJMOriginalGlobalDAGData.nodes 10 ⟨469716, by decide⟩ =
    .split (coordinate 11) (![⟨469672, by decide⟩,⟨469693, by decide⟩,⟨448662, by decide⟩,⟨469715, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17830_469716 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17830 ⟨469716, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17830
    ⟨469716, by decide⟩ (by decide) (![⟨469672, by decide⟩,⟨469693, by decide⟩,⟨448662, by decide⟩,⟨469715, by decide⟩]) unmarked_context_11_17830_469716 node_context_11_17830_469716
  intro a
  fin_cases a
  · exact context_12_71320_469672
  · exact context_12_71321_469693
  · exact context_12_71322_448662
  · exact context_12_71323_469715

theorem selected_cut_18344 : selected 9 ⟨469731, by decide⟩
    (prefixPartial 12 71324) = some ⟨12, 2, 0, 469731, 71324, 1741, 65536⟩ := by
  decide +kernel

theorem context_12_71324_469731 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71324 ⟨469731, by decide⟩ :=
  accepted_of_selected 12 71324 ⟨469731, by decide⟩ ⟨12, 2, 0, 469731, 71324, 1741, 65536⟩
    (by decide) selected_cut_18344

theorem selected_cut_18345 : selected 9 ⟨469747, by decide⟩
    (prefixPartial 12 71325) = some ⟨12, 2, 0, 469747, 71325, 1633, 65536⟩ := by
  decide +kernel

theorem context_12_71325_469747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71325 ⟨469747, by decide⟩ :=
  accepted_of_selected 12 71325 ⟨469747, by decide⟩ ⟨12, 2, 0, 469747, 71325, 1633, 65536⟩
    (by decide) selected_cut_18345

theorem selected_cut_18346 : selected 9 ⟨469762, by decide⟩
    (prefixPartial 12 71326) = some ⟨12, 2, 0, 469762, 71326, 1533, 65536⟩ := by
  decide +kernel

theorem context_12_71326_469762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71326 ⟨469762, by decide⟩ :=
  accepted_of_selected 12 71326 ⟨469762, by decide⟩ ⟨12, 2, 0, 469762, 71326, 1533, 65536⟩
    (by decide) selected_cut_18346

theorem selected_cut_18347 : selected 9 ⟨469782, by decide⟩
    (prefixPartial 12 71327) = some ⟨12, 2, 0, 469782, 71327, 1809, 65536⟩ := by
  decide +kernel

theorem context_12_71327_469782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71327 ⟨469782, by decide⟩ :=
  accepted_of_selected 12 71327 ⟨469782, by decide⟩ ⟨12, 2, 0, 469782, 71327, 1809, 65536⟩
    (by decide) selected_cut_18347

theorem unmarked_context_11_17831_469783 : frontier 10 ⟨469783, by decide⟩
    (prefixCache 11 17831) (prefixPartial 11 17831) = false := by
  decide +kernel

theorem node_context_11_17831_469783 : EJMOriginalGlobalDAGData.nodes 10 ⟨469783, by decide⟩ =
    .split (coordinate 11) (![⟨469731, by decide⟩,⟨469747, by decide⟩,⟨469762, by decide⟩,⟨469782, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17831_469783 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17831 ⟨469783, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17831
    ⟨469783, by decide⟩ (by decide) (![⟨469731, by decide⟩,⟨469747, by decide⟩,⟨469762, by decide⟩,⟨469782, by decide⟩]) unmarked_context_11_17831_469783 node_context_11_17831_469783
  intro a
  fin_cases a
  · exact context_12_71324_469731
  · exact context_12_71325_469747
  · exact context_12_71326_469762
  · exact context_12_71327_469782

theorem unmarked_context_10_4457_469784 : frontier 11 ⟨469784, by decide⟩
    (prefixCache 10 4457) (prefixPartial 10 4457) = false := by
  decide +kernel

theorem node_context_10_4457_469784 : EJMOriginalGlobalDAGData.nodes 11 ⟨469784, by decide⟩ =
    .split (coordinate 10) (![⟨469564, by decide⟩,⟨469649, by decide⟩,⟨469716, by decide⟩,⟨469783, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4457_469784 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4457 ⟨469784, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4457
    ⟨469784, by decide⟩ (by decide) (![⟨469564, by decide⟩,⟨469649, by decide⟩,⟨469716, by decide⟩,⟨469783, by decide⟩]) unmarked_context_10_4457_469784 node_context_10_4457_469784
  intro a
  fin_cases a
  · exact context_11_17828_469564
  · exact context_11_17829_469649
  · exact context_11_17830_469716
  · exact context_11_17831_469783

theorem selected_cut_18348 : selected 9 ⟨469797, by decide⟩
    (prefixPartial 12 71328) = some ⟨12, 2, 0, 469797, 71328, 1445, 65536⟩ := by
  decide +kernel

theorem context_12_71328_469797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71328 ⟨469797, by decide⟩ :=
  accepted_of_selected 12 71328 ⟨469797, by decide⟩ ⟨12, 2, 0, 469797, 71328, 1445, 65536⟩
    (by decide) selected_cut_18348

theorem selected_cut_18349 : selected 9 ⟨469819, by decide⟩
    (prefixPartial 12 71329) = some ⟨12, 2, 0, 469819, 71329, 1525, 65536⟩ := by
  decide +kernel

theorem context_12_71329_469819 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71329 ⟨469819, by decide⟩ :=
  accepted_of_selected 12 71329 ⟨469819, by decide⟩ ⟨12, 2, 0, 469819, 71329, 1525, 65536⟩
    (by decide) selected_cut_18349

theorem selected_cut_18350 : selected 9 ⟨469834, by decide⟩
    (prefixPartial 12 71330) = some ⟨12, 2, 0, 469834, 71330, 1365, 65536⟩ := by
  decide +kernel

theorem context_12_71330_469834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71330 ⟨469834, by decide⟩ :=
  accepted_of_selected 12 71330 ⟨469834, by decide⟩ ⟨12, 2, 0, 469834, 71330, 1365, 65536⟩
    (by decide) selected_cut_18350

theorem selected_cut_18351 : selected 9 ⟨469849, by decide⟩
    (prefixPartial 12 71331) = some ⟨12, 2, 0, 469849, 71331, 1489, 65536⟩ := by
  decide +kernel

theorem context_12_71331_469849 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71331 ⟨469849, by decide⟩ :=
  accepted_of_selected 12 71331 ⟨469849, by decide⟩ ⟨12, 2, 0, 469849, 71331, 1489, 65536⟩
    (by decide) selected_cut_18351

theorem unmarked_context_11_17832_469850 : frontier 10 ⟨469850, by decide⟩
    (prefixCache 11 17832) (prefixPartial 11 17832) = false := by
  decide +kernel

theorem node_context_11_17832_469850 : EJMOriginalGlobalDAGData.nodes 10 ⟨469850, by decide⟩ =
    .split (coordinate 11) (![⟨469797, by decide⟩,⟨469819, by decide⟩,⟨469834, by decide⟩,⟨469849, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17832_469850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17832 ⟨469850, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17832
    ⟨469850, by decide⟩ (by decide) (![⟨469797, by decide⟩,⟨469819, by decide⟩,⟨469834, by decide⟩,⟨469849, by decide⟩]) unmarked_context_11_17832_469850 node_context_11_17832_469850
  intro a
  fin_cases a
  · exact context_12_71328_469797
  · exact context_12_71329_469819
  · exact context_12_71330_469834
  · exact context_12_71331_469849

theorem selected_cut_18352 : selected 9 ⟨469868, by decide⟩
    (prefixPartial 12 71332) = some ⟨12, 2, 0, 469868, 71332, 1729, 65536⟩ := by
  decide +kernel

theorem context_12_71332_469868 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71332 ⟨469868, by decide⟩ :=
  accepted_of_selected 12 71332 ⟨469868, by decide⟩ ⟨12, 2, 0, 469868, 71332, 1729, 65536⟩
    (by decide) selected_cut_18352

theorem selected_cut_18353 : selected 9 ⟨469886, by decide⟩
    (prefixPartial 12 71333) = some ⟨12, 2, 0, 469886, 71333, 1525, 65536⟩ := by
  decide +kernel

theorem context_12_71333_469886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71333 ⟨469886, by decide⟩ :=
  accepted_of_selected 12 71333 ⟨469886, by decide⟩ ⟨12, 2, 0, 469886, 71333, 1525, 65536⟩
    (by decide) selected_cut_18353

theorem selected_cut_18354 : selected 9 ⟨469905, by decide⟩
    (prefixPartial 12 71334) = some ⟨12, 2, 0, 469905, 71334, 1573, 65536⟩ := by
  decide +kernel

theorem context_12_71334_469905 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71334 ⟨469905, by decide⟩ :=
  accepted_of_selected 12 71334 ⟨469905, by decide⟩ ⟨12, 2, 0, 469905, 71334, 1573, 65536⟩
    (by decide) selected_cut_18354

theorem selected_cut_18355 : selected 9 ⟨469925, by decide⟩
    (prefixPartial 12 71335) = some ⟨12, 2, 0, 469925, 71335, 1617, 65536⟩ := by
  decide +kernel

theorem context_12_71335_469925 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71335 ⟨469925, by decide⟩ :=
  accepted_of_selected 12 71335 ⟨469925, by decide⟩ ⟨12, 2, 0, 469925, 71335, 1617, 65536⟩
    (by decide) selected_cut_18355

theorem unmarked_context_11_17833_469926 : frontier 10 ⟨469926, by decide⟩
    (prefixCache 11 17833) (prefixPartial 11 17833) = false := by
  decide +kernel

theorem node_context_11_17833_469926 : EJMOriginalGlobalDAGData.nodes 10 ⟨469926, by decide⟩ =
    .split (coordinate 11) (![⟨469868, by decide⟩,⟨469886, by decide⟩,⟨469905, by decide⟩,⟨469925, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17833_469926 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17833 ⟨469926, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17833
    ⟨469926, by decide⟩ (by decide) (![⟨469868, by decide⟩,⟨469886, by decide⟩,⟨469905, by decide⟩,⟨469925, by decide⟩]) unmarked_context_11_17833_469926 node_context_11_17833_469926
  intro a
  fin_cases a
  · exact context_12_71332_469868
  · exact context_12_71333_469886
  · exact context_12_71334_469905
  · exact context_12_71335_469925

theorem selected_cut_18356 : selected 9 ⟨469944, by decide⟩
    (prefixPartial 12 71336) = some ⟨12, 2, 0, 469944, 71336, 1473, 65536⟩ := by
  decide +kernel

theorem context_12_71336_469944 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71336 ⟨469944, by decide⟩ :=
  accepted_of_selected 12 71336 ⟨469944, by decide⟩ ⟨12, 2, 0, 469944, 71336, 1473, 65536⟩
    (by decide) selected_cut_18356

theorem selected_cut_18357 : selected 9 ⟨469958, by decide⟩
    (prefixPartial 12 71337) = some ⟨12, 2, 0, 469958, 71337, 1469, 65536⟩ := by
  decide +kernel

theorem context_12_71337_469958 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71337 ⟨469958, by decide⟩ :=
  accepted_of_selected 12 71337 ⟨469958, by decide⟩ ⟨12, 2, 0, 469958, 71337, 1469, 65536⟩
    (by decide) selected_cut_18357

theorem selected_cut_18358 : selected 9 ⟨445248, by decide⟩
    (prefixPartial 12 71338) = some ⟨12, 1, 0, 445248, 71338, 1, 65536⟩ := by
  decide +kernel

theorem context_12_71338_445248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71338 ⟨445248, by decide⟩ :=
  accepted_of_selected 12 71338 ⟨445248, by decide⟩ ⟨12, 1, 0, 445248, 71338, 1, 65536⟩
    (by decide) selected_cut_18358

theorem selected_cut_18359 : selected 9 ⟨469977, by decide⟩
    (prefixPartial 12 71339) = some ⟨12, 2, 0, 469977, 71339, 1369, 65536⟩ := by
  decide +kernel

theorem context_12_71339_469977 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71339 ⟨469977, by decide⟩ :=
  accepted_of_selected 12 71339 ⟨469977, by decide⟩ ⟨12, 2, 0, 469977, 71339, 1369, 65536⟩
    (by decide) selected_cut_18359

theorem unmarked_context_11_17834_469978 : frontier 10 ⟨469978, by decide⟩
    (prefixCache 11 17834) (prefixPartial 11 17834) = false := by
  decide +kernel

theorem node_context_11_17834_469978 : EJMOriginalGlobalDAGData.nodes 10 ⟨469978, by decide⟩ =
    .split (coordinate 11) (![⟨469944, by decide⟩,⟨469958, by decide⟩,⟨445248, by decide⟩,⟨469977, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17834_469978 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17834 ⟨469978, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17834
    ⟨469978, by decide⟩ (by decide) (![⟨469944, by decide⟩,⟨469958, by decide⟩,⟨445248, by decide⟩,⟨469977, by decide⟩]) unmarked_context_11_17834_469978 node_context_11_17834_469978
  intro a
  fin_cases a
  · exact context_12_71336_469944
  · exact context_12_71337_469958
  · exact context_12_71338_445248
  · exact context_12_71339_469977

theorem selected_cut_18360 : selected 9 ⟨469990, by decide⟩
    (prefixPartial 12 71340) = some ⟨12, 2, 0, 469990, 71340, 1529, 65536⟩ := by
  decide +kernel

theorem context_12_71340_469990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71340 ⟨469990, by decide⟩ :=
  accepted_of_selected 12 71340 ⟨469990, by decide⟩ ⟨12, 2, 0, 469990, 71340, 1529, 65536⟩
    (by decide) selected_cut_18360

theorem selected_cut_18361 : selected 9 ⟨470004, by decide⟩
    (prefixPartial 12 71341) = some ⟨12, 2, 0, 470004, 71341, 1429, 65536⟩ := by
  decide +kernel

theorem context_12_71341_470004 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71341 ⟨470004, by decide⟩ :=
  accepted_of_selected 12 71341 ⟨470004, by decide⟩ ⟨12, 2, 0, 470004, 71341, 1429, 65536⟩
    (by decide) selected_cut_18361

theorem selected_cut_18362 : selected 9 ⟨470017, by decide⟩
    (prefixPartial 12 71342) = some ⟨12, 2, 0, 470017, 71342, 1241, 65536⟩ := by
  decide +kernel

theorem context_12_71342_470017 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71342 ⟨470017, by decide⟩ :=
  accepted_of_selected 12 71342 ⟨470017, by decide⟩ ⟨12, 2, 0, 470017, 71342, 1241, 65536⟩
    (by decide) selected_cut_18362

theorem selected_cut_18363 : selected 9 ⟨470029, by decide⟩
    (prefixPartial 12 71343) = some ⟨12, 2, 0, 470029, 71343, 1429, 65536⟩ := by
  decide +kernel

theorem context_12_71343_470029 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71343 ⟨470029, by decide⟩ :=
  accepted_of_selected 12 71343 ⟨470029, by decide⟩ ⟨12, 2, 0, 470029, 71343, 1429, 65536⟩
    (by decide) selected_cut_18363

theorem unmarked_context_11_17835_470030 : frontier 10 ⟨470030, by decide⟩
    (prefixCache 11 17835) (prefixPartial 11 17835) = false := by
  decide +kernel

theorem node_context_11_17835_470030 : EJMOriginalGlobalDAGData.nodes 10 ⟨470030, by decide⟩ =
    .split (coordinate 11) (![⟨469990, by decide⟩,⟨470004, by decide⟩,⟨470017, by decide⟩,⟨470029, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17835_470030 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17835 ⟨470030, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17835
    ⟨470030, by decide⟩ (by decide) (![⟨469990, by decide⟩,⟨470004, by decide⟩,⟨470017, by decide⟩,⟨470029, by decide⟩]) unmarked_context_11_17835_470030 node_context_11_17835_470030
  intro a
  fin_cases a
  · exact context_12_71340_469990
  · exact context_12_71341_470004
  · exact context_12_71342_470017
  · exact context_12_71343_470029

theorem unmarked_context_10_4458_470031 : frontier 11 ⟨470031, by decide⟩
    (prefixCache 10 4458) (prefixPartial 10 4458) = false := by
  decide +kernel

theorem node_context_10_4458_470031 : EJMOriginalGlobalDAGData.nodes 11 ⟨470031, by decide⟩ =
    .split (coordinate 10) (![⟨469850, by decide⟩,⟨469926, by decide⟩,⟨469978, by decide⟩,⟨470030, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4458_470031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4458 ⟨470031, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4458
    ⟨470031, by decide⟩ (by decide) (![⟨469850, by decide⟩,⟨469926, by decide⟩,⟨469978, by decide⟩,⟨470030, by decide⟩]) unmarked_context_10_4458_470031 node_context_10_4458_470031
  intro a
  fin_cases a
  · exact context_11_17832_469850
  · exact context_11_17833_469926
  · exact context_11_17834_469978
  · exact context_11_17835_470030

theorem selected_cut_18364 : selected 9 ⟨470043, by decide⟩
    (prefixPartial 12 71344) = some ⟨12, 2, 0, 470043, 71344, 1033, 65536⟩ := by
  decide +kernel

theorem context_12_71344_470043 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71344 ⟨470043, by decide⟩ :=
  accepted_of_selected 12 71344 ⟨470043, by decide⟩ ⟨12, 2, 0, 470043, 71344, 1033, 65536⟩
    (by decide) selected_cut_18364

theorem selected_cut_18365 : selected 9 ⟨470058, by decide⟩
    (prefixPartial 12 71345) = some ⟨12, 2, 0, 470058, 71345, 1177, 65536⟩ := by
  decide +kernel

theorem context_12_71345_470058 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71345 ⟨470058, by decide⟩ :=
  accepted_of_selected 12 71345 ⟨470058, by decide⟩ ⟨12, 2, 0, 470058, 71345, 1177, 65536⟩
    (by decide) selected_cut_18365

theorem selected_cut_18366 : selected 9 ⟨470071, by decide⟩
    (prefixPartial 12 71346) = some ⟨12, 2, 0, 470071, 71346, 1069, 65536⟩ := by
  decide +kernel

theorem context_12_71346_470071 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71346 ⟨470071, by decide⟩ :=
  accepted_of_selected 12 71346 ⟨470071, by decide⟩ ⟨12, 2, 0, 470071, 71346, 1069, 65536⟩
    (by decide) selected_cut_18366

theorem selected_cut_18367 : selected 9 ⟨470082, by decide⟩
    (prefixPartial 12 71347) = some ⟨12, 2, 0, 470082, 71347, 1077, 65536⟩ := by
  decide +kernel

theorem context_12_71347_470082 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71347 ⟨470082, by decide⟩ :=
  accepted_of_selected 12 71347 ⟨470082, by decide⟩ ⟨12, 2, 0, 470082, 71347, 1077, 65536⟩
    (by decide) selected_cut_18367

theorem unmarked_context_11_17836_470083 : frontier 10 ⟨470083, by decide⟩
    (prefixCache 11 17836) (prefixPartial 11 17836) = false := by
  decide +kernel

theorem node_context_11_17836_470083 : EJMOriginalGlobalDAGData.nodes 10 ⟨470083, by decide⟩ =
    .split (coordinate 11) (![⟨470043, by decide⟩,⟨470058, by decide⟩,⟨470071, by decide⟩,⟨470082, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17836_470083 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17836 ⟨470083, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17836
    ⟨470083, by decide⟩ (by decide) (![⟨470043, by decide⟩,⟨470058, by decide⟩,⟨470071, by decide⟩,⟨470082, by decide⟩]) unmarked_context_11_17836_470083 node_context_11_17836_470083
  intro a
  fin_cases a
  · exact context_12_71344_470043
  · exact context_12_71345_470058
  · exact context_12_71346_470071
  · exact context_12_71347_470082

theorem selected_cut_18368 : selected 9 ⟨470094, by decide⟩
    (prefixPartial 12 71348) = some ⟨12, 2, 0, 470094, 71348, 1097, 65536⟩ := by
  decide +kernel

theorem context_12_71348_470094 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71348 ⟨470094, by decide⟩ :=
  accepted_of_selected 12 71348 ⟨470094, by decide⟩ ⟨12, 2, 0, 470094, 71348, 1097, 65536⟩
    (by decide) selected_cut_18368

theorem selected_cut_18369 : selected 9 ⟨470107, by decide⟩
    (prefixPartial 12 71349) = some ⟨12, 2, 0, 470107, 71349, 1077, 65536⟩ := by
  decide +kernel

theorem context_12_71349_470107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71349 ⟨470107, by decide⟩ :=
  accepted_of_selected 12 71349 ⟨470107, by decide⟩ ⟨12, 2, 0, 470107, 71349, 1077, 65536⟩
    (by decide) selected_cut_18369

theorem selected_cut_18370 : selected 9 ⟨470117, by decide⟩
    (prefixPartial 12 71350) = some ⟨12, 2, 0, 470117, 71350, 1085, 65536⟩ := by
  decide +kernel

theorem context_12_71350_470117 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71350 ⟨470117, by decide⟩ :=
  accepted_of_selected 12 71350 ⟨470117, by decide⟩ ⟨12, 2, 0, 470117, 71350, 1085, 65536⟩
    (by decide) selected_cut_18370

theorem selected_cut_18371 : selected 9 ⟨470133, by decide⟩
    (prefixPartial 12 71351) = some ⟨12, 2, 0, 470133, 71351, 1109, 65536⟩ := by
  decide +kernel

theorem context_12_71351_470133 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71351 ⟨470133, by decide⟩ :=
  accepted_of_selected 12 71351 ⟨470133, by decide⟩ ⟨12, 2, 0, 470133, 71351, 1109, 65536⟩
    (by decide) selected_cut_18371

theorem unmarked_context_11_17837_470134 : frontier 10 ⟨470134, by decide⟩
    (prefixCache 11 17837) (prefixPartial 11 17837) = false := by
  decide +kernel

theorem node_context_11_17837_470134 : EJMOriginalGlobalDAGData.nodes 10 ⟨470134, by decide⟩ =
    .split (coordinate 11) (![⟨470094, by decide⟩,⟨470107, by decide⟩,⟨470117, by decide⟩,⟨470133, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17837_470134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17837 ⟨470134, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17837
    ⟨470134, by decide⟩ (by decide) (![⟨470094, by decide⟩,⟨470107, by decide⟩,⟨470117, by decide⟩,⟨470133, by decide⟩]) unmarked_context_11_17837_470134 node_context_11_17837_470134
  intro a
  fin_cases a
  · exact context_12_71348_470094
  · exact context_12_71349_470107
  · exact context_12_71350_470117
  · exact context_12_71351_470133

theorem selected_cut_18372 : selected 10 ⟨470172, by decide⟩
    (prefixPartial 11 17838) = some ⟨11, 2, 0, 470172, 17838, 3321, 262144⟩ := by
  decide +kernel

theorem context_11_17838_470172 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17838 ⟨470172, by decide⟩ :=
  accepted_of_selected 11 17838 ⟨470172, by decide⟩ ⟨11, 2, 0, 470172, 17838, 3321, 262144⟩
    (by decide) selected_cut_18372

theorem selected_cut_18373 : selected 10 ⟨470209, by decide⟩
    (prefixPartial 11 17839) = some ⟨11, 2, 0, 470209, 17839, 3473, 262144⟩ := by
  decide +kernel

theorem context_11_17839_470209 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17839 ⟨470209, by decide⟩ :=
  accepted_of_selected 11 17839 ⟨470209, by decide⟩ ⟨11, 2, 0, 470209, 17839, 3473, 262144⟩
    (by decide) selected_cut_18373

theorem unmarked_context_10_4459_470210 : frontier 11 ⟨470210, by decide⟩
    (prefixCache 10 4459) (prefixPartial 10 4459) = false := by
  decide +kernel

theorem node_context_10_4459_470210 : EJMOriginalGlobalDAGData.nodes 11 ⟨470210, by decide⟩ =
    .split (coordinate 10) (![⟨470083, by decide⟩,⟨470134, by decide⟩,⟨470172, by decide⟩,⟨470209, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4459_470210 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4459 ⟨470210, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4459
    ⟨470210, by decide⟩ (by decide) (![⟨470083, by decide⟩,⟨470134, by decide⟩,⟨470172, by decide⟩,⟨470209, by decide⟩]) unmarked_context_10_4459_470210 node_context_10_4459_470210
  intro a
  fin_cases a
  · exact context_11_17836_470083
  · exact context_11_17837_470134
  · exact context_11_17838_470172
  · exact context_11_17839_470209

theorem unmarked_context_9_1114_470211 : frontier 12 ⟨470211, by decide⟩
    (prefixCache 9 1114) (prefixPartial 9 1114) = false := by
  decide +kernel

theorem node_context_9_1114_470211 : EJMOriginalGlobalDAGData.nodes 12 ⟨470211, by decide⟩ =
    .split (coordinate 9) (![⟨469492, by decide⟩,⟨469784, by decide⟩,⟨470031, by decide⟩,⟨470210, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1114_470211 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1114 ⟨470211, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1114
    ⟨470211, by decide⟩ (by decide) (![⟨469492, by decide⟩,⟨469784, by decide⟩,⟨470031, by decide⟩,⟨470210, by decide⟩]) unmarked_context_9_1114_470211 node_context_9_1114_470211
  intro a
  fin_cases a
  · exact context_10_4456_469492
  · exact context_10_4457_469784
  · exact context_10_4458_470031
  · exact context_10_4459_470210

theorem selected_cut_18374 : selected 10 ⟨470248, by decide⟩
    (prefixPartial 11 17840) = some ⟨11, 2, 0, 470248, 17840, 3461, 262144⟩ := by
  decide +kernel

theorem context_11_17840_470248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17840 ⟨470248, by decide⟩ :=
  accepted_of_selected 11 17840 ⟨470248, by decide⟩ ⟨11, 2, 0, 470248, 17840, 3461, 262144⟩
    (by decide) selected_cut_18374

theorem selected_cut_18375 : selected 10 ⟨470279, by decide⟩
    (prefixPartial 11 17841) = some ⟨11, 2, 0, 470279, 17841, 2913, 262144⟩ := by
  decide +kernel

theorem context_11_17841_470279 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17841 ⟨470279, by decide⟩ :=
  accepted_of_selected 11 17841 ⟨470279, by decide⟩ ⟨11, 2, 0, 470279, 17841, 2913, 262144⟩
    (by decide) selected_cut_18375

theorem selected_cut_18376 : selected 10 ⟨470312, by decide⟩
    (prefixPartial 11 17842) = some ⟨11, 2, 0, 470312, 17842, 3001, 262144⟩ := by
  decide +kernel

theorem context_11_17842_470312 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17842 ⟨470312, by decide⟩ :=
  accepted_of_selected 11 17842 ⟨470312, by decide⟩ ⟨11, 2, 0, 470312, 17842, 3001, 262144⟩
    (by decide) selected_cut_18376

theorem selected_cut_18377 : selected 10 ⟨470342, by decide⟩
    (prefixPartial 11 17843) = some ⟨11, 2, 0, 470342, 17843, 2845, 262144⟩ := by
  decide +kernel

theorem context_11_17843_470342 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17843 ⟨470342, by decide⟩ :=
  accepted_of_selected 11 17843 ⟨470342, by decide⟩ ⟨11, 2, 0, 470342, 17843, 2845, 262144⟩
    (by decide) selected_cut_18377

theorem unmarked_context_10_4460_470343 : frontier 11 ⟨470343, by decide⟩
    (prefixCache 10 4460) (prefixPartial 10 4460) = false := by
  decide +kernel

theorem node_context_10_4460_470343 : EJMOriginalGlobalDAGData.nodes 11 ⟨470343, by decide⟩ =
    .split (coordinate 10) (![⟨470248, by decide⟩,⟨470279, by decide⟩,⟨470312, by decide⟩,⟨470342, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4460_470343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4460 ⟨470343, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4460
    ⟨470343, by decide⟩ (by decide) (![⟨470248, by decide⟩,⟨470279, by decide⟩,⟨470312, by decide⟩,⟨470342, by decide⟩]) unmarked_context_10_4460_470343 node_context_10_4460_470343
  intro a
  fin_cases a
  · exact context_11_17840_470248
  · exact context_11_17841_470279
  · exact context_11_17842_470312
  · exact context_11_17843_470342

theorem selected_cut_18378 : selected 10 ⟨470366, by decide⟩
    (prefixPartial 11 17844) = some ⟨11, 2, 0, 470366, 17844, 2329, 262144⟩ := by
  decide +kernel

theorem context_11_17844_470366 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17844 ⟨470366, by decide⟩ :=
  accepted_of_selected 11 17844 ⟨470366, by decide⟩ ⟨11, 2, 0, 470366, 17844, 2329, 262144⟩
    (by decide) selected_cut_18378

theorem selected_cut_18379 : selected 10 ⟨470395, by decide⟩
    (prefixPartial 11 17845) = some ⟨11, 2, 0, 470395, 17845, 2201, 262144⟩ := by
  decide +kernel

theorem context_11_17845_470395 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17845 ⟨470395, by decide⟩ :=
  accepted_of_selected 11 17845 ⟨470395, by decide⟩ ⟨11, 2, 0, 470395, 17845, 2201, 262144⟩
    (by decide) selected_cut_18379

theorem selected_cut_18380 : selected 10 ⟨470417, by decide⟩
    (prefixPartial 11 17846) = some ⟨11, 2, 0, 470417, 17846, 2117, 262144⟩ := by
  decide +kernel

theorem context_11_17846_470417 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17846 ⟨470417, by decide⟩ :=
  accepted_of_selected 11 17846 ⟨470417, by decide⟩ ⟨11, 2, 0, 470417, 17846, 2117, 262144⟩
    (by decide) selected_cut_18380

theorem selected_cut_18381 : selected 10 ⟨470437, by decide⟩
    (prefixPartial 11 17847) = some ⟨11, 2, 0, 470437, 17847, 1841, 262144⟩ := by
  decide +kernel

theorem context_11_17847_470437 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17847 ⟨470437, by decide⟩ :=
  accepted_of_selected 11 17847 ⟨470437, by decide⟩ ⟨11, 2, 0, 470437, 17847, 1841, 262144⟩
    (by decide) selected_cut_18381

theorem unmarked_context_10_4461_470438 : frontier 11 ⟨470438, by decide⟩
    (prefixCache 10 4461) (prefixPartial 10 4461) = false := by
  decide +kernel

theorem node_context_10_4461_470438 : EJMOriginalGlobalDAGData.nodes 11 ⟨470438, by decide⟩ =
    .split (coordinate 10) (![⟨470366, by decide⟩,⟨470395, by decide⟩,⟨470417, by decide⟩,⟨470437, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4461_470438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4461 ⟨470438, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4461
    ⟨470438, by decide⟩ (by decide) (![⟨470366, by decide⟩,⟨470395, by decide⟩,⟨470417, by decide⟩,⟨470437, by decide⟩]) unmarked_context_10_4461_470438 node_context_10_4461_470438
  intro a
  fin_cases a
  · exact context_11_17844_470366
  · exact context_11_17845_470395
  · exact context_11_17846_470417
  · exact context_11_17847_470437

theorem selected_cut_18382 : selected 10 ⟨470452, by decide⟩
    (prefixPartial 11 17848) = some ⟨11, 2, 0, 470452, 17848, 1301, 262144⟩ := by
  decide +kernel

theorem context_11_17848_470452 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17848 ⟨470452, by decide⟩ :=
  accepted_of_selected 11 17848 ⟨470452, by decide⟩ ⟨11, 2, 0, 470452, 17848, 1301, 262144⟩
    (by decide) selected_cut_18382

theorem selected_cut_18383 : selected 10 ⟨470469, by decide⟩
    (prefixPartial 11 17849) = some ⟨11, 2, 0, 470469, 17849, 1233, 262144⟩ := by
  decide +kernel

theorem context_11_17849_470469 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17849 ⟨470469, by decide⟩ :=
  accepted_of_selected 11 17849 ⟨470469, by decide⟩ ⟨11, 2, 0, 470469, 17849, 1233, 262144⟩
    (by decide) selected_cut_18383

theorem selected_cut_18384 : selected 10 ⟨470479, by decide⟩
    (prefixPartial 11 17850) = some ⟨11, 2, 0, 470479, 17850, 717, 262144⟩ := by
  decide +kernel

theorem context_11_17850_470479 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17850 ⟨470479, by decide⟩ :=
  accepted_of_selected 11 17850 ⟨470479, by decide⟩ ⟨11, 2, 0, 470479, 17850, 717, 262144⟩
    (by decide) selected_cut_18384

theorem selected_cut_18385 : selected 10 ⟨470493, by decide⟩
    (prefixPartial 11 17851) = some ⟨11, 2, 0, 470493, 17851, 857, 262144⟩ := by
  decide +kernel

theorem context_11_17851_470493 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17851 ⟨470493, by decide⟩ :=
  accepted_of_selected 11 17851 ⟨470493, by decide⟩ ⟨11, 2, 0, 470493, 17851, 857, 262144⟩
    (by decide) selected_cut_18385

theorem unmarked_context_10_4462_470494 : frontier 11 ⟨470494, by decide⟩
    (prefixCache 10 4462) (prefixPartial 10 4462) = false := by
  decide +kernel

theorem node_context_10_4462_470494 : EJMOriginalGlobalDAGData.nodes 11 ⟨470494, by decide⟩ =
    .split (coordinate 10) (![⟨470452, by decide⟩,⟨470469, by decide⟩,⟨470479, by decide⟩,⟨470493, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4462_470494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4462 ⟨470494, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4462
    ⟨470494, by decide⟩ (by decide) (![⟨470452, by decide⟩,⟨470469, by decide⟩,⟨470479, by decide⟩,⟨470493, by decide⟩]) unmarked_context_10_4462_470494 node_context_10_4462_470494
  intro a
  fin_cases a
  · exact context_11_17848_470452
  · exact context_11_17849_470469
  · exact context_11_17850_470479
  · exact context_11_17851_470493

theorem selected_cut_18386 : selected 11 ⟨470520, by decide⟩
    (prefixPartial 10 4463) = some ⟨10, 2, 0, 470520, 4463, 1557, 1048576⟩ := by
  decide +kernel

theorem context_10_4463_470520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4463 ⟨470520, by decide⟩ :=
  accepted_of_selected 10 4463 ⟨470520, by decide⟩ ⟨10, 2, 0, 470520, 4463, 1557, 1048576⟩
    (by decide) selected_cut_18386

theorem unmarked_context_9_1115_470521 : frontier 12 ⟨470521, by decide⟩
    (prefixCache 9 1115) (prefixPartial 9 1115) = false := by
  decide +kernel

theorem node_context_9_1115_470521 : EJMOriginalGlobalDAGData.nodes 12 ⟨470521, by decide⟩ =
    .split (coordinate 9) (![⟨470343, by decide⟩,⟨470438, by decide⟩,⟨470494, by decide⟩,⟨470520, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1115_470521 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1115 ⟨470521, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1115
    ⟨470521, by decide⟩ (by decide) (![⟨470343, by decide⟩,⟨470438, by decide⟩,⟨470494, by decide⟩,⟨470520, by decide⟩]) unmarked_context_9_1115_470521 node_context_9_1115_470521
  intro a
  fin_cases a
  · exact context_10_4460_470343
  · exact context_10_4461_470438
  · exact context_10_4462_470494
  · exact context_10_4463_470520

theorem unmarked_context_8_278_470522 : frontier 13 ⟨470522, by decide⟩
    (prefixCache 8 278) (prefixPartial 8 278) = false := by
  decide +kernel

theorem node_context_8_278_470522 : EJMOriginalGlobalDAGData.nodes 13 ⟨470522, by decide⟩ =
    .split (coordinate 8) (![⟨466317, by decide⟩,⟨469167, by decide⟩,⟨470211, by decide⟩,⟨470521, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_278_470522 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 278 ⟨470522, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 278
    ⟨470522, by decide⟩ (by decide) (![⟨466317, by decide⟩,⟨469167, by decide⟩,⟨470211, by decide⟩,⟨470521, by decide⟩]) unmarked_context_8_278_470522 node_context_8_278_470522
  intro a
  fin_cases a
  · exact context_9_1112_466317
  · exact context_9_1113_469167
  · exact context_9_1114_470211
  · exact context_9_1115_470521

theorem selected_cut_18387 : selected 13 ⟨14298, by decide⟩
    (prefixPartial 8 279) = some ⟨8, 1, 0, 14298, 279, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_279_14298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 279 ⟨14298, by decide⟩ :=
  accepted_of_selected 8 279 ⟨14298, by decide⟩ ⟨8, 1, 0, 14298, 279, 1, 16777216⟩
    (by decide) selected_cut_18387

theorem unmarked_context_7_69_470523 : frontier 14 ⟨470523, by decide⟩
    (prefixCache 7 69) (prefixPartial 7 69) = false := by
  decide +kernel

theorem node_context_7_69_470523 : EJMOriginalGlobalDAGData.nodes 14 ⟨470523, by decide⟩ =
    .split (coordinate 7) (![⟨453482, by decide⟩,⟨461252, by decide⟩,⟨470522, by decide⟩,⟨14298, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_69_470523 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 69 ⟨470523, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 69
    ⟨470523, by decide⟩ (by decide) (![⟨453482, by decide⟩,⟨461252, by decide⟩,⟨470522, by decide⟩,⟨14298, by decide⟩]) unmarked_context_7_69_470523 node_context_7_69_470523
  intro a
  fin_cases a
  · exact context_8_276_453482
  · exact context_8_277_461252
  · exact context_8_278_470522
  · exact context_8_279_14298

theorem selected_cut_18388 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 17920) = some ⟨11, 1, 0, 434745, 17920, 1, 262144⟩ := by
  decide +kernel

theorem context_11_17920_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17920 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 17920 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 17920, 1, 262144⟩
    (by decide) selected_cut_18388

theorem selected_cut_18389 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 71684) = some ⟨12, 1, 0, 448748, 71684, 1, 65536⟩ := by
  decide +kernel

theorem context_12_71684_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71684 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 71684 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 71684, 1, 65536⟩
    (by decide) selected_cut_18389

theorem selected_cut_18390 : selected 8 ⟨470591, by decide⟩
    (prefixPartial 13 286740) = some ⟨13, 2, 0, 470591, 286740, 2373, 16384⟩ := by
  decide +kernel

theorem context_13_286740_470591 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286740 ⟨470591, by decide⟩ :=
  accepted_of_selected 13 286740 ⟨470591, by decide⟩ ⟨13, 2, 0, 470591, 286740, 2373, 16384⟩
    (by decide) selected_cut_18390

theorem selected_cut_18391 : selected 8 ⟨470670, by decide⟩
    (prefixPartial 13 286741) = some ⟨13, 2, 0, 470670, 286741, 2313, 16384⟩ := by
  decide +kernel

theorem context_13_286741_470670 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286741 ⟨470670, by decide⟩ :=
  accepted_of_selected 13 286741 ⟨470670, by decide⟩ ⟨13, 2, 0, 470670, 286741, 2313, 16384⟩
    (by decide) selected_cut_18391

theorem selected_cut_18392 : selected 8 ⟨470721, by decide⟩
    (prefixPartial 13 286742) = some ⟨13, 2, 0, 470721, 286742, 1669, 16384⟩ := by
  decide +kernel

theorem context_13_286742_470721 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286742 ⟨470721, by decide⟩ :=
  accepted_of_selected 13 286742 ⟨470721, by decide⟩ ⟨13, 2, 0, 470721, 286742, 1669, 16384⟩
    (by decide) selected_cut_18392

theorem selected_cut_18393 : selected 8 ⟨470738, by decide⟩
    (prefixPartial 13 286743) = some ⟨13, 2, 0, 470738, 286743, 1049, 16384⟩ := by
  decide +kernel

theorem context_13_286743_470738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286743 ⟨470738, by decide⟩ :=
  accepted_of_selected 13 286743 ⟨470738, by decide⟩ ⟨13, 2, 0, 470738, 286743, 1049, 16384⟩
    (by decide) selected_cut_18393

theorem unmarked_context_12_71685_470739 : frontier 9 ⟨470739, by decide⟩
    (prefixCache 12 71685) (prefixPartial 12 71685) = false := by
  decide +kernel

theorem node_context_12_71685_470739 : EJMOriginalGlobalDAGData.nodes 9 ⟨470739, by decide⟩ =
    .split (coordinate 12) (![⟨470591, by decide⟩,⟨470670, by decide⟩,⟨470721, by decide⟩,⟨470738, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71685_470739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71685 ⟨470739, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71685
    ⟨470739, by decide⟩ (by decide) (![⟨470591, by decide⟩,⟨470670, by decide⟩,⟨470721, by decide⟩,⟨470738, by decide⟩]) unmarked_context_12_71685_470739 node_context_12_71685_470739
  intro a
  fin_cases a
  · exact context_13_286740_470591
  · exact context_13_286741_470670
  · exact context_13_286742_470721
  · exact context_13_286743_470738

theorem selected_cut_18394 : selected 8 ⟨470808, by decide⟩
    (prefixPartial 13 286744) = some ⟨13, 2, 0, 470808, 286744, 2757, 16384⟩ := by
  decide +kernel

theorem context_13_286744_470808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286744 ⟨470808, by decide⟩ :=
  accepted_of_selected 13 286744 ⟨470808, by decide⟩ ⟨13, 2, 0, 470808, 286744, 2757, 16384⟩
    (by decide) selected_cut_18394

theorem selected_cut_18395 : selected 8 ⟨470873, by decide⟩
    (prefixPartial 13 286745) = some ⟨13, 2, 0, 470873, 286745, 2781, 16384⟩ := by
  decide +kernel

theorem context_13_286745_470873 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286745 ⟨470873, by decide⟩ :=
  accepted_of_selected 13 286745 ⟨470873, by decide⟩ ⟨13, 2, 0, 470873, 286745, 2781, 16384⟩
    (by decide) selected_cut_18395

theorem selected_cut_18396 : selected 8 ⟨470926, by decide⟩
    (prefixPartial 13 286746) = some ⟨13, 2, 0, 470926, 286746, 1997, 16384⟩ := by
  decide +kernel

theorem context_13_286746_470926 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286746 ⟨470926, by decide⟩ :=
  accepted_of_selected 13 286746 ⟨470926, by decide⟩ ⟨13, 2, 0, 470926, 286746, 1997, 16384⟩
    (by decide) selected_cut_18396

theorem selected_cut_18397 : selected 8 ⟨470948, by decide⟩
    (prefixPartial 13 286747) = some ⟨13, 2, 0, 470948, 286747, 1153, 16384⟩ := by
  decide +kernel

theorem context_13_286747_470948 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286747 ⟨470948, by decide⟩ :=
  accepted_of_selected 13 286747 ⟨470948, by decide⟩ ⟨13, 2, 0, 470948, 286747, 1153, 16384⟩
    (by decide) selected_cut_18397

theorem unmarked_context_12_71686_470949 : frontier 9 ⟨470949, by decide⟩
    (prefixCache 12 71686) (prefixPartial 12 71686) = false := by
  decide +kernel

theorem node_context_12_71686_470949 : EJMOriginalGlobalDAGData.nodes 9 ⟨470949, by decide⟩ =
    .split (coordinate 12) (![⟨470808, by decide⟩,⟨470873, by decide⟩,⟨470926, by decide⟩,⟨470948, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71686_470949 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71686 ⟨470949, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71686
    ⟨470949, by decide⟩ (by decide) (![⟨470808, by decide⟩,⟨470873, by decide⟩,⟨470926, by decide⟩,⟨470948, by decide⟩]) unmarked_context_12_71686_470949 node_context_12_71686_470949
  intro a
  fin_cases a
  · exact context_13_286744_470808
  · exact context_13_286745_470873
  · exact context_13_286746_470926
  · exact context_13_286747_470948

theorem selected_cut_18398 : selected 8 ⟨471005, by decide⟩
    (prefixPartial 13 286748) = some ⟨13, 2, 0, 471005, 286748, 2533, 16384⟩ := by
  decide +kernel

theorem context_13_286748_471005 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286748 ⟨471005, by decide⟩ :=
  accepted_of_selected 13 286748 ⟨471005, by decide⟩ ⟨13, 2, 0, 471005, 286748, 2533, 16384⟩
    (by decide) selected_cut_18398

theorem selected_cut_18399 : selected 8 ⟨471077, by decide⟩
    (prefixPartial 13 286749) = some ⟨13, 2, 0, 471077, 286749, 2933, 16384⟩ := by
  decide +kernel

theorem context_13_286749_471077 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286749 ⟨471077, by decide⟩ :=
  accepted_of_selected 13 286749 ⟨471077, by decide⟩ ⟨13, 2, 0, 471077, 286749, 2933, 16384⟩
    (by decide) selected_cut_18399

theorem selected_cut_18400 : selected 8 ⟨471127, by decide⟩
    (prefixPartial 13 286750) = some ⟨13, 2, 0, 471127, 286750, 2121, 16384⟩ := by
  decide +kernel

theorem context_13_286750_471127 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286750 ⟨471127, by decide⟩ :=
  accepted_of_selected 13 286750 ⟨471127, by decide⟩ ⟨13, 2, 0, 471127, 286750, 2121, 16384⟩
    (by decide) selected_cut_18400

theorem selected_cut_18401 : selected 8 ⟨471138, by decide⟩
    (prefixPartial 13 286751) = some ⟨13, 2, 0, 471138, 286751, 1029, 16384⟩ := by
  decide +kernel

theorem context_13_286751_471138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286751 ⟨471138, by decide⟩ :=
  accepted_of_selected 13 286751 ⟨471138, by decide⟩ ⟨13, 2, 0, 471138, 286751, 1029, 16384⟩
    (by decide) selected_cut_18401

theorem unmarked_context_12_71687_471139 : frontier 9 ⟨471139, by decide⟩
    (prefixCache 12 71687) (prefixPartial 12 71687) = false := by
  decide +kernel

theorem node_context_12_71687_471139 : EJMOriginalGlobalDAGData.nodes 9 ⟨471139, by decide⟩ =
    .split (coordinate 12) (![⟨471005, by decide⟩,⟨471077, by decide⟩,⟨471127, by decide⟩,⟨471138, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71687_471139 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71687 ⟨471139, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71687
    ⟨471139, by decide⟩ (by decide) (![⟨471005, by decide⟩,⟨471077, by decide⟩,⟨471127, by decide⟩,⟨471138, by decide⟩]) unmarked_context_12_71687_471139 node_context_12_71687_471139
  intro a
  fin_cases a
  · exact context_13_286748_471005
  · exact context_13_286749_471077
  · exact context_13_286750_471127
  · exact context_13_286751_471138

theorem unmarked_context_11_17921_471140 : frontier 10 ⟨471140, by decide⟩
    (prefixCache 11 17921) (prefixPartial 11 17921) = false := by
  decide +kernel

theorem node_context_11_17921_471140 : EJMOriginalGlobalDAGData.nodes 10 ⟨471140, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨470739, by decide⟩,⟨470949, by decide⟩,⟨471139, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17921_471140 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17921 ⟨471140, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17921
    ⟨471140, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨470739, by decide⟩,⟨470949, by decide⟩,⟨471139, by decide⟩]) unmarked_context_11_17921_471140 node_context_11_17921_471140
  intro a
  fin_cases a
  · exact context_12_71684_448748
  · exact context_12_71685_470739
  · exact context_12_71686_470949
  · exact context_12_71687_471139

theorem selected_cut_18402 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 71688) = some ⟨12, 1, 0, 448748, 71688, 1, 65536⟩ := by
  decide +kernel

theorem context_12_71688_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71688 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 71688 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 71688, 1, 65536⟩
    (by decide) selected_cut_18402

theorem selected_cut_18403 : selected 8 ⟨471198, by decide⟩
    (prefixPartial 13 286756) = some ⟨13, 2, 0, 471198, 286756, 2353, 16384⟩ := by
  decide +kernel

theorem context_13_286756_471198 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286756 ⟨471198, by decide⟩ :=
  accepted_of_selected 13 286756 ⟨471198, by decide⟩ ⟨13, 2, 0, 471198, 286756, 2353, 16384⟩
    (by decide) selected_cut_18403

theorem selected_cut_18404 : selected 8 ⟨471248, by decide⟩
    (prefixPartial 13 286757) = some ⟨13, 2, 0, 471248, 286757, 2393, 16384⟩ := by
  decide +kernel

theorem context_13_286757_471248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286757 ⟨471248, by decide⟩ :=
  accepted_of_selected 13 286757 ⟨471248, by decide⟩ ⟨13, 2, 0, 471248, 286757, 2393, 16384⟩
    (by decide) selected_cut_18404

theorem selected_cut_18405 : selected 8 ⟨471276, by decide⟩
    (prefixPartial 13 286758) = some ⟨13, 2, 0, 471276, 286758, 1761, 16384⟩ := by
  decide +kernel

theorem context_13_286758_471276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286758 ⟨471276, by decide⟩ :=
  accepted_of_selected 13 286758 ⟨471276, by decide⟩ ⟨13, 2, 0, 471276, 286758, 1761, 16384⟩
    (by decide) selected_cut_18405

theorem selected_cut_18406 : selected 8 ⟨471293, by decide⟩
    (prefixPartial 13 286759) = some ⟨13, 2, 0, 471293, 286759, 1125, 16384⟩ := by
  decide +kernel

theorem context_13_286759_471293 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286759 ⟨471293, by decide⟩ :=
  accepted_of_selected 13 286759 ⟨471293, by decide⟩ ⟨13, 2, 0, 471293, 286759, 1125, 16384⟩
    (by decide) selected_cut_18406

theorem unmarked_context_12_71689_471294 : frontier 9 ⟨471294, by decide⟩
    (prefixCache 12 71689) (prefixPartial 12 71689) = false := by
  decide +kernel

theorem node_context_12_71689_471294 : EJMOriginalGlobalDAGData.nodes 9 ⟨471294, by decide⟩ =
    .split (coordinate 12) (![⟨471198, by decide⟩,⟨471248, by decide⟩,⟨471276, by decide⟩,⟨471293, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71689_471294 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71689 ⟨471294, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71689
    ⟨471294, by decide⟩ (by decide) (![⟨471198, by decide⟩,⟨471248, by decide⟩,⟨471276, by decide⟩,⟨471293, by decide⟩]) unmarked_context_12_71689_471294 node_context_12_71689_471294
  intro a
  fin_cases a
  · exact context_13_286756_471198
  · exact context_13_286757_471248
  · exact context_13_286758_471276
  · exact context_13_286759_471293

theorem selected_cut_18407 : selected 9 ⟨88909, by decide⟩
    (prefixPartial 12 71690) = some ⟨12, 1, 0, 88909, 71690, 1, 65536⟩ := by
  decide +kernel

theorem context_12_71690_88909 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71690 ⟨88909, by decide⟩ :=
  accepted_of_selected 12 71690 ⟨88909, by decide⟩ ⟨12, 1, 0, 88909, 71690, 1, 65536⟩
    (by decide) selected_cut_18407

theorem selected_cut_18408 : selected 8 ⟨471343, by decide⟩
    (prefixPartial 13 286764) = some ⟨13, 2, 0, 471343, 286764, 2221, 16384⟩ := by
  decide +kernel

theorem context_13_286764_471343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286764 ⟨471343, by decide⟩ :=
  accepted_of_selected 13 286764 ⟨471343, by decide⟩ ⟨13, 2, 0, 471343, 286764, 2221, 16384⟩
    (by decide) selected_cut_18408

theorem selected_cut_18409 : selected 8 ⟨471385, by decide⟩
    (prefixPartial 13 286765) = some ⟨13, 2, 0, 471385, 286765, 2757, 16384⟩ := by
  decide +kernel

theorem context_13_286765_471385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286765 ⟨471385, by decide⟩ :=
  accepted_of_selected 13 286765 ⟨471385, by decide⟩ ⟨13, 2, 0, 471385, 286765, 2757, 16384⟩
    (by decide) selected_cut_18409

theorem selected_cut_18410 : selected 8 ⟨471415, by decide⟩
    (prefixPartial 13 286766) = some ⟨13, 2, 0, 471415, 286766, 1873, 16384⟩ := by
  decide +kernel

theorem context_13_286766_471415 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286766 ⟨471415, by decide⟩ :=
  accepted_of_selected 13 286766 ⟨471415, by decide⟩ ⟨13, 2, 0, 471415, 286766, 1873, 16384⟩
    (by decide) selected_cut_18410

theorem selected_cut_18411 : selected 8 ⟨471432, by decide⟩
    (prefixPartial 13 286767) = some ⟨13, 2, 0, 471432, 286767, 1049, 16384⟩ := by
  decide +kernel

theorem context_13_286767_471432 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286767 ⟨471432, by decide⟩ :=
  accepted_of_selected 13 286767 ⟨471432, by decide⟩ ⟨13, 2, 0, 471432, 286767, 1049, 16384⟩
    (by decide) selected_cut_18411

theorem unmarked_context_12_71691_471433 : frontier 9 ⟨471433, by decide⟩
    (prefixCache 12 71691) (prefixPartial 12 71691) = false := by
  decide +kernel

theorem node_context_12_71691_471433 : EJMOriginalGlobalDAGData.nodes 9 ⟨471433, by decide⟩ =
    .split (coordinate 12) (![⟨471343, by decide⟩,⟨471385, by decide⟩,⟨471415, by decide⟩,⟨471432, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71691_471433 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71691 ⟨471433, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71691
    ⟨471433, by decide⟩ (by decide) (![⟨471343, by decide⟩,⟨471385, by decide⟩,⟨471415, by decide⟩,⟨471432, by decide⟩]) unmarked_context_12_71691_471433 node_context_12_71691_471433
  intro a
  fin_cases a
  · exact context_13_286764_471343
  · exact context_13_286765_471385
  · exact context_13_286766_471415
  · exact context_13_286767_471432

theorem unmarked_context_11_17922_471434 : frontier 10 ⟨471434, by decide⟩
    (prefixCache 11 17922) (prefixPartial 11 17922) = false := by
  decide +kernel

theorem node_context_11_17922_471434 : EJMOriginalGlobalDAGData.nodes 10 ⟨471434, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨471294, by decide⟩,⟨88909, by decide⟩,⟨471433, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17922_471434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17922 ⟨471434, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17922
    ⟨471434, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨471294, by decide⟩,⟨88909, by decide⟩,⟨471433, by decide⟩]) unmarked_context_11_17922_471434 node_context_11_17922_471434
  intro a
  fin_cases a
  · exact context_12_71688_448748
  · exact context_12_71689_471294
  · exact context_12_71690_88909
  · exact context_12_71691_471433

theorem selected_cut_18412 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 71692) = some ⟨12, 1, 0, 448748, 71692, 1, 65536⟩ := by
  decide +kernel

theorem context_12_71692_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71692 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 71692 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 71692, 1, 65536⟩
    (by decide) selected_cut_18412

theorem selected_cut_18413 : selected 8 ⟨471486, by decide⟩
    (prefixPartial 13 286772) = some ⟨13, 2, 0, 471486, 286772, 2317, 16384⟩ := by
  decide +kernel

theorem context_13_286772_471486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286772 ⟨471486, by decide⟩ :=
  accepted_of_selected 13 286772 ⟨471486, by decide⟩ ⟨13, 2, 0, 471486, 286772, 2317, 16384⟩
    (by decide) selected_cut_18413

theorem selected_cut_18414 : selected 8 ⟨471526, by decide⟩
    (prefixPartial 13 286773) = some ⟨13, 2, 0, 471526, 286773, 2481, 16384⟩ := by
  decide +kernel

theorem context_13_286773_471526 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286773 ⟨471526, by decide⟩ :=
  accepted_of_selected 13 286773 ⟨471526, by decide⟩ ⟨13, 2, 0, 471526, 286773, 2481, 16384⟩
    (by decide) selected_cut_18414

theorem selected_cut_18415 : selected 8 ⟨471557, by decide⟩
    (prefixPartial 13 286774) = some ⟨13, 2, 0, 471557, 286774, 2049, 16384⟩ := by
  decide +kernel

theorem context_13_286774_471557 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286774 ⟨471557, by decide⟩ :=
  accepted_of_selected 13 286774 ⟨471557, by decide⟩ ⟨13, 2, 0, 471557, 286774, 2049, 16384⟩
    (by decide) selected_cut_18415

theorem selected_cut_18416 : selected 8 ⟨471580, by decide⟩
    (prefixPartial 13 286775) = some ⟨13, 2, 0, 471580, 286775, 1185, 16384⟩ := by
  decide +kernel

theorem context_13_286775_471580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286775 ⟨471580, by decide⟩ :=
  accepted_of_selected 13 286775 ⟨471580, by decide⟩ ⟨13, 2, 0, 471580, 286775, 1185, 16384⟩
    (by decide) selected_cut_18416

theorem unmarked_context_12_71693_471581 : frontier 9 ⟨471581, by decide⟩
    (prefixCache 12 71693) (prefixPartial 12 71693) = false := by
  decide +kernel

theorem node_context_12_71693_471581 : EJMOriginalGlobalDAGData.nodes 9 ⟨471581, by decide⟩ =
    .split (coordinate 12) (![⟨471486, by decide⟩,⟨471526, by decide⟩,⟨471557, by decide⟩,⟨471580, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71693_471581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71693 ⟨471581, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71693
    ⟨471581, by decide⟩ (by decide) (![⟨471486, by decide⟩,⟨471526, by decide⟩,⟨471557, by decide⟩,⟨471580, by decide⟩]) unmarked_context_12_71693_471581 node_context_12_71693_471581
  intro a
  fin_cases a
  · exact context_13_286772_471486
  · exact context_13_286773_471526
  · exact context_13_286774_471557
  · exact context_13_286775_471580

theorem selected_cut_18417 : selected 8 ⟨471630, by decide⟩
    (prefixPartial 13 286776) = some ⟨13, 2, 0, 471630, 286776, 2353, 16384⟩ := by
  decide +kernel

theorem context_13_286776_471630 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286776 ⟨471630, by decide⟩ :=
  accepted_of_selected 13 286776 ⟨471630, by decide⟩ ⟨13, 2, 0, 471630, 286776, 2353, 16384⟩
    (by decide) selected_cut_18417

theorem selected_cut_18418 : selected 8 ⟨471668, by decide⟩
    (prefixPartial 13 286777) = some ⟨13, 2, 0, 471668, 286777, 2749, 16384⟩ := by
  decide +kernel

theorem context_13_286777_471668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286777 ⟨471668, by decide⟩ :=
  accepted_of_selected 13 286777 ⟨471668, by decide⟩ ⟨13, 2, 0, 471668, 286777, 2749, 16384⟩
    (by decide) selected_cut_18418

theorem selected_cut_18419 : selected 8 ⟨471712, by decide⟩
    (prefixPartial 13 286778) = some ⟨13, 2, 0, 471712, 286778, 2169, 16384⟩ := by
  decide +kernel

theorem context_13_286778_471712 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286778 ⟨471712, by decide⟩ :=
  accepted_of_selected 13 286778 ⟨471712, by decide⟩ ⟨13, 2, 0, 471712, 286778, 2169, 16384⟩
    (by decide) selected_cut_18419

theorem selected_cut_18420 : selected 8 ⟨471729, by decide⟩
    (prefixPartial 13 286779) = some ⟨13, 2, 0, 471729, 286779, 1181, 16384⟩ := by
  decide +kernel

theorem context_13_286779_471729 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286779 ⟨471729, by decide⟩ :=
  accepted_of_selected 13 286779 ⟨471729, by decide⟩ ⟨13, 2, 0, 471729, 286779, 1181, 16384⟩
    (by decide) selected_cut_18420

theorem unmarked_context_12_71694_471730 : frontier 9 ⟨471730, by decide⟩
    (prefixCache 12 71694) (prefixPartial 12 71694) = false := by
  decide +kernel

theorem node_context_12_71694_471730 : EJMOriginalGlobalDAGData.nodes 9 ⟨471730, by decide⟩ =
    .split (coordinate 12) (![⟨471630, by decide⟩,⟨471668, by decide⟩,⟨471712, by decide⟩,⟨471729, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71694_471730 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71694 ⟨471730, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71694
    ⟨471730, by decide⟩ (by decide) (![⟨471630, by decide⟩,⟨471668, by decide⟩,⟨471712, by decide⟩,⟨471729, by decide⟩]) unmarked_context_12_71694_471730 node_context_12_71694_471730
  intro a
  fin_cases a
  · exact context_13_286776_471630
  · exact context_13_286777_471668
  · exact context_13_286778_471712
  · exact context_13_286779_471729

theorem selected_cut_18421 : selected 9 ⟨471873, by decide⟩
    (prefixPartial 12 71695) = some ⟨12, 2, 0, 471873, 71695, 4081, 65536⟩ := by
  decide +kernel

theorem context_12_71695_471873 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71695 ⟨471873, by decide⟩ :=
  accepted_of_selected 12 71695 ⟨471873, by decide⟩ ⟨12, 2, 0, 471873, 71695, 4081, 65536⟩
    (by decide) selected_cut_18421

theorem unmarked_context_11_17923_471874 : frontier 10 ⟨471874, by decide⟩
    (prefixCache 11 17923) (prefixPartial 11 17923) = false := by
  decide +kernel

theorem node_context_11_17923_471874 : EJMOriginalGlobalDAGData.nodes 10 ⟨471874, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨471581, by decide⟩,⟨471730, by decide⟩,⟨471873, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_17923_471874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 17923 ⟨471874, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 17923
    ⟨471874, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨471581, by decide⟩,⟨471730, by decide⟩,⟨471873, by decide⟩]) unmarked_context_11_17923_471874 node_context_11_17923_471874
  intro a
  fin_cases a
  · exact context_12_71692_448748
  · exact context_12_71693_471581
  · exact context_12_71694_471730
  · exact context_12_71695_471873

theorem unmarked_context_10_4480_471875 : frontier 11 ⟨471875, by decide⟩
    (prefixCache 10 4480) (prefixPartial 10 4480) = false := by
  decide +kernel

theorem node_context_10_4480_471875 : EJMOriginalGlobalDAGData.nodes 11 ⟨471875, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨471140, by decide⟩,⟨471434, by decide⟩,⟨471874, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4480_471875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4480 ⟨471875, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4480
    ⟨471875, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨471140, by decide⟩,⟨471434, by decide⟩,⟨471874, by decide⟩]) unmarked_context_10_4480_471875 node_context_10_4480_471875
  intro a
  fin_cases a
  · exact context_11_17920_434745
  · exact context_11_17921_471140
  · exact context_11_17922_471434
  · exact context_11_17923_471874

theorem selected_cut_18422 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 71696) = some ⟨12, 1, 0, 435160, 71696, 1, 65536⟩ := by
  decide +kernel

theorem context_12_71696_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71696 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 71696 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 71696, 1, 65536⟩
    (by decide) selected_cut_18422

theorem selected_cut_18423 : selected 8 ⟨471916, by decide⟩
    (prefixPartial 13 286788) = some ⟨13, 2, 0, 471916, 286788, 1689, 16384⟩ := by
  decide +kernel

theorem context_13_286788_471916 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286788 ⟨471916, by decide⟩ :=
  accepted_of_selected 13 286788 ⟨471916, by decide⟩ ⟨13, 2, 0, 471916, 286788, 1689, 16384⟩
    (by decide) selected_cut_18423

theorem selected_cut_18424 : selected 8 ⟨471949, by decide⟩
    (prefixPartial 13 286789) = some ⟨13, 2, 0, 471949, 286789, 1629, 16384⟩ := by
  decide +kernel

theorem context_13_286789_471949 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286789 ⟨471949, by decide⟩ :=
  accepted_of_selected 13 286789 ⟨471949, by decide⟩ ⟨13, 2, 0, 471949, 286789, 1629, 16384⟩
    (by decide) selected_cut_18424

theorem selected_cut_18425 : selected 8 ⟨471969, by decide⟩
    (prefixPartial 13 286790) = some ⟨13, 2, 0, 471969, 286790, 1209, 16384⟩ := by
  decide +kernel

theorem context_13_286790_471969 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286790 ⟨471969, by decide⟩ :=
  accepted_of_selected 13 286790 ⟨471969, by decide⟩ ⟨13, 2, 0, 471969, 286790, 1209, 16384⟩
    (by decide) selected_cut_18425

theorem selected_cut_18426 : selected 8 ⟨471976, by decide⟩
    (prefixPartial 13 286791) = some ⟨13, 2, 0, 471976, 286791, 801, 16384⟩ := by
  decide +kernel

theorem context_13_286791_471976 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286791 ⟨471976, by decide⟩ :=
  accepted_of_selected 13 286791 ⟨471976, by decide⟩ ⟨13, 2, 0, 471976, 286791, 801, 16384⟩
    (by decide) selected_cut_18426

theorem unmarked_context_12_71697_471977 : frontier 9 ⟨471977, by decide⟩
    (prefixCache 12 71697) (prefixPartial 12 71697) = false := by
  decide +kernel

theorem node_context_12_71697_471977 : EJMOriginalGlobalDAGData.nodes 9 ⟨471977, by decide⟩ =
    .split (coordinate 12) (![⟨471916, by decide⟩,⟨471949, by decide⟩,⟨471969, by decide⟩,⟨471976, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71697_471977 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71697 ⟨471977, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71697
    ⟨471977, by decide⟩ (by decide) (![⟨471916, by decide⟩,⟨471949, by decide⟩,⟨471969, by decide⟩,⟨471976, by decide⟩]) unmarked_context_12_71697_471977 node_context_12_71697_471977
  intro a
  fin_cases a
  · exact context_13_286788_471916
  · exact context_13_286789_471949
  · exact context_13_286790_471969
  · exact context_13_286791_471976

theorem selected_cut_18427 : selected 8 ⟨472023, by decide⟩
    (prefixPartial 13 286792) = some ⟨13, 2, 0, 472023, 286792, 1661, 16384⟩ := by
  decide +kernel

theorem context_13_286792_472023 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286792 ⟨472023, by decide⟩ :=
  accepted_of_selected 13 286792 ⟨472023, by decide⟩ ⟨13, 2, 0, 472023, 286792, 1661, 16384⟩
    (by decide) selected_cut_18427

theorem selected_cut_18428 : selected 8 ⟨472060, by decide⟩
    (prefixPartial 13 286793) = some ⟨13, 2, 0, 472060, 286793, 1769, 16384⟩ := by
  decide +kernel

theorem context_13_286793_472060 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286793 ⟨472060, by decide⟩ :=
  accepted_of_selected 13 286793 ⟨472060, by decide⟩ ⟨13, 2, 0, 472060, 286793, 1769, 16384⟩
    (by decide) selected_cut_18428

theorem selected_cut_18429 : selected 8 ⟨472081, by decide⟩
    (prefixPartial 13 286794) = some ⟨13, 2, 0, 472081, 286794, 1361, 16384⟩ := by
  decide +kernel

theorem context_13_286794_472081 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286794 ⟨472081, by decide⟩ :=
  accepted_of_selected 13 286794 ⟨472081, by decide⟩ ⟨13, 2, 0, 472081, 286794, 1361, 16384⟩
    (by decide) selected_cut_18429

theorem selected_cut_18430 : selected 8 ⟨472090, by decide⟩
    (prefixPartial 13 286795) = some ⟨13, 2, 0, 472090, 286795, 861, 16384⟩ := by
  decide +kernel

theorem context_13_286795_472090 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286795 ⟨472090, by decide⟩ :=
  accepted_of_selected 13 286795 ⟨472090, by decide⟩ ⟨13, 2, 0, 472090, 286795, 861, 16384⟩
    (by decide) selected_cut_18430

theorem unmarked_context_12_71698_472091 : frontier 9 ⟨472091, by decide⟩
    (prefixCache 12 71698) (prefixPartial 12 71698) = false := by
  decide +kernel

theorem node_context_12_71698_472091 : EJMOriginalGlobalDAGData.nodes 9 ⟨472091, by decide⟩ =
    .split (coordinate 12) (![⟨472023, by decide⟩,⟨472060, by decide⟩,⟨472081, by decide⟩,⟨472090, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_71698_472091 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 71698 ⟨472091, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 71698
    ⟨472091, by decide⟩ (by decide) (![⟨472023, by decide⟩,⟨472060, by decide⟩,⟨472081, by decide⟩,⟨472090, by decide⟩]) unmarked_context_12_71698_472091 node_context_12_71698_472091
  intro a
  fin_cases a
  · exact context_13_286792_472023
  · exact context_13_286793_472060
  · exact context_13_286794_472081
  · exact context_13_286795_472090

theorem selected_cut_18431 : selected 8 ⟨472132, by decide⟩
    (prefixPartial 13 286796) = some ⟨13, 2, 0, 472132, 286796, 1585, 16384⟩ := by
  decide +kernel

theorem context_13_286796_472132 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286796 ⟨472132, by decide⟩ :=
  accepted_of_selected 13 286796 ⟨472132, by decide⟩ ⟨13, 2, 0, 472132, 286796, 1585, 16384⟩
    (by decide) selected_cut_18431

theorem selected_cut_18432 : selected 8 ⟨472169, by decide⟩
    (prefixPartial 13 286797) = some ⟨13, 2, 0, 472169, 286797, 1773, 16384⟩ := by
  decide +kernel

theorem context_13_286797_472169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286797 ⟨472169, by decide⟩ :=
  accepted_of_selected 13 286797 ⟨472169, by decide⟩ ⟨13, 2, 0, 472169, 286797, 1773, 16384⟩
    (by decide) selected_cut_18432

theorem selected_cut_18433 : selected 8 ⟨472193, by decide⟩
    (prefixPartial 13 286798) = some ⟨13, 2, 0, 472193, 286798, 1413, 16384⟩ := by
  decide +kernel

theorem context_13_286798_472193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286798 ⟨472193, by decide⟩ :=
  accepted_of_selected 13 286798 ⟨472193, by decide⟩ ⟨13, 2, 0, 472193, 286798, 1413, 16384⟩
    (by decide) selected_cut_18433

theorem selected_cut_18434 : selected 8 ⟨472199, by decide⟩
    (prefixPartial 13 286799) = some ⟨13, 2, 0, 472199, 286799, 677, 16384⟩ := by
  decide +kernel

theorem context_13_286799_472199 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 286799 ⟨472199, by decide⟩ :=
  accepted_of_selected 13 286799 ⟨472199, by decide⟩ ⟨13, 2, 0, 472199, 286799, 677, 16384⟩
    (by decide) selected_cut_18434

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
