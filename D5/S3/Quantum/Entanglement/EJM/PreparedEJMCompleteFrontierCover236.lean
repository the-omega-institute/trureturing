/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover235
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_11_18956_575645 : frontier 10 ⟨575645, by decide⟩
    (prefixCache 11 18956) (prefixPartial 11 18956) = false := by
  decide +kernel

theorem node_context_11_18956_575645 : EJMOriginalGlobalDAGData.nodes 10 ⟨575645, by decide⟩ =
    .split (coordinate 11) (![⟨445562, by decide⟩,⟨575525, by decide⟩,⟨575580, by decide⟩,⟨575644, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18956_575645 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18956 ⟨575645, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18956
    ⟨575645, by decide⟩ (by decide) (![⟨445562, by decide⟩,⟨575525, by decide⟩,⟨575580, by decide⟩,⟨575644, by decide⟩]) unmarked_context_11_18956_575645 node_context_11_18956_575645
  intro a
  fin_cases a
  · exact context_12_75824_445562
  · exact context_12_75825_575525
  · exact context_12_75826_575580
  · exact context_12_75827_575644

theorem selected_cut_22659 : selected 9 ⟨475533, by decide⟩
    (prefixPartial 12 75828) = some ⟨12, 1, 0, 475533, 75828, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75828_475533 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75828 ⟨475533, by decide⟩ :=
  accepted_of_selected 12 75828 ⟨475533, by decide⟩ ⟨12, 1, 0, 475533, 75828, 1, 65536⟩
    (by decide) selected_cut_22659

theorem selected_cut_22660 : selected 8 ⟨575652, by decide⟩
    (prefixPartial 13 303316) = some ⟨13, 2, 0, 575652, 303316, 357, 16384⟩ := by
  decide +kernel

theorem context_13_303316_575652 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303316 ⟨575652, by decide⟩ :=
  accepted_of_selected 13 303316 ⟨575652, by decide⟩ ⟨13, 2, 0, 575652, 303316, 357, 16384⟩
    (by decide) selected_cut_22660

theorem selected_cut_22661 : selected 8 ⟨575674, by decide⟩
    (prefixPartial 13 303317) = some ⟨13, 2, 0, 575674, 303317, 2085, 16384⟩ := by
  decide +kernel

theorem context_13_303317_575674 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303317 ⟨575674, by decide⟩ :=
  accepted_of_selected 13 303317 ⟨575674, by decide⟩ ⟨13, 2, 0, 575674, 303317, 2085, 16384⟩
    (by decide) selected_cut_22661

theorem selected_cut_22662 : selected 8 ⟨575691, by decide⟩
    (prefixPartial 13 303318) = some ⟨13, 2, 0, 575691, 303318, 1501, 16384⟩ := by
  decide +kernel

theorem context_13_303318_575691 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303318 ⟨575691, by decide⟩ :=
  accepted_of_selected 13 303318 ⟨575691, by decide⟩ ⟨13, 2, 0, 575691, 303318, 1501, 16384⟩
    (by decide) selected_cut_22662

theorem selected_cut_22663 : selected 8 ⟨575696, by decide⟩
    (prefixPartial 13 303319) = some ⟨13, 2, 0, 575696, 303319, 969, 16384⟩ := by
  decide +kernel

theorem context_13_303319_575696 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303319 ⟨575696, by decide⟩ :=
  accepted_of_selected 13 303319 ⟨575696, by decide⟩ ⟨13, 2, 0, 575696, 303319, 969, 16384⟩
    (by decide) selected_cut_22663

theorem unmarked_context_12_75829_575697 : frontier 9 ⟨575697, by decide⟩
    (prefixCache 12 75829) (prefixPartial 12 75829) = false := by
  decide +kernel

theorem node_context_12_75829_575697 : EJMOriginalGlobalDAGData.nodes 9 ⟨575697, by decide⟩ =
    .split (coordinate 12) (![⟨575652, by decide⟩,⟨575674, by decide⟩,⟨575691, by decide⟩,⟨575696, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75829_575697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75829 ⟨575697, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75829
    ⟨575697, by decide⟩ (by decide) (![⟨575652, by decide⟩,⟨575674, by decide⟩,⟨575691, by decide⟩,⟨575696, by decide⟩]) unmarked_context_12_75829_575697 node_context_12_75829_575697
  intro a
  fin_cases a
  · exact context_13_303316_575652
  · exact context_13_303317_575674
  · exact context_13_303318_575691
  · exact context_13_303319_575696

theorem selected_cut_22664 : selected 8 ⟨575708, by decide⟩
    (prefixPartial 13 303320) = some ⟨13, 2, 0, 575708, 303320, 441, 16384⟩ := by
  decide +kernel

theorem context_13_303320_575708 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303320 ⟨575708, by decide⟩ :=
  accepted_of_selected 13 303320 ⟨575708, by decide⟩ ⟨13, 2, 0, 575708, 303320, 441, 16384⟩
    (by decide) selected_cut_22664

theorem selected_cut_22665 : selected 8 ⟨575733, by decide⟩
    (prefixPartial 13 303321) = some ⟨13, 2, 0, 575733, 303321, 2389, 16384⟩ := by
  decide +kernel

theorem context_13_303321_575733 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303321 ⟨575733, by decide⟩ :=
  accepted_of_selected 13 303321 ⟨575733, by decide⟩ ⟨13, 2, 0, 575733, 303321, 2389, 16384⟩
    (by decide) selected_cut_22665

theorem selected_cut_22666 : selected 8 ⟨575755, by decide⟩
    (prefixPartial 13 303322) = some ⟨13, 2, 0, 575755, 303322, 1653, 16384⟩ := by
  decide +kernel

theorem context_13_303322_575755 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303322 ⟨575755, by decide⟩ :=
  accepted_of_selected 13 303322 ⟨575755, by decide⟩ ⟨13, 2, 0, 575755, 303322, 1653, 16384⟩
    (by decide) selected_cut_22666

theorem selected_cut_22667 : selected 8 ⟨575760, by decide⟩
    (prefixPartial 13 303323) = some ⟨13, 2, 0, 575760, 303323, 933, 16384⟩ := by
  decide +kernel

theorem context_13_303323_575760 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303323 ⟨575760, by decide⟩ :=
  accepted_of_selected 13 303323 ⟨575760, by decide⟩ ⟨13, 2, 0, 575760, 303323, 933, 16384⟩
    (by decide) selected_cut_22667

theorem unmarked_context_12_75830_575761 : frontier 9 ⟨575761, by decide⟩
    (prefixCache 12 75830) (prefixPartial 12 75830) = false := by
  decide +kernel

theorem node_context_12_75830_575761 : EJMOriginalGlobalDAGData.nodes 9 ⟨575761, by decide⟩ =
    .split (coordinate 12) (![⟨575708, by decide⟩,⟨575733, by decide⟩,⟨575755, by decide⟩,⟨575760, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75830_575761 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75830 ⟨575761, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75830
    ⟨575761, by decide⟩ (by decide) (![⟨575708, by decide⟩,⟨575733, by decide⟩,⟨575755, by decide⟩,⟨575760, by decide⟩]) unmarked_context_12_75830_575761 node_context_12_75830_575761
  intro a
  fin_cases a
  · exact context_13_303320_575708
  · exact context_13_303321_575733
  · exact context_13_303322_575755
  · exact context_13_303323_575760

theorem selected_cut_22668 : selected 8 ⟨575774, by decide⟩
    (prefixPartial 13 303324) = some ⟨13, 2, 0, 575774, 303324, 405, 16384⟩ := by
  decide +kernel

theorem context_13_303324_575774 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303324 ⟨575774, by decide⟩ :=
  accepted_of_selected 13 303324 ⟨575774, by decide⟩ ⟨13, 2, 0, 575774, 303324, 405, 16384⟩
    (by decide) selected_cut_22668

theorem selected_cut_22669 : selected 8 ⟨575803, by decide⟩
    (prefixPartial 13 303325) = some ⟨13, 2, 0, 575803, 303325, 2469, 16384⟩ := by
  decide +kernel

theorem context_13_303325_575803 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303325 ⟨575803, by decide⟩ :=
  accepted_of_selected 13 303325 ⟨575803, by decide⟩ ⟨13, 2, 0, 575803, 303325, 2469, 16384⟩
    (by decide) selected_cut_22669

theorem selected_cut_22670 : selected 8 ⟨575828, by decide⟩
    (prefixPartial 13 303326) = some ⟨13, 2, 0, 575828, 303326, 1633, 16384⟩ := by
  decide +kernel

theorem context_13_303326_575828 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303326 ⟨575828, by decide⟩ :=
  accepted_of_selected 13 303326 ⟨575828, by decide⟩ ⟨13, 2, 0, 575828, 303326, 1633, 16384⟩
    (by decide) selected_cut_22670

theorem selected_cut_22671 : selected 8 ⟨575834, by decide⟩
    (prefixPartial 13 303327) = some ⟨13, 2, 0, 575834, 303327, 809, 16384⟩ := by
  decide +kernel

theorem context_13_303327_575834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303327 ⟨575834, by decide⟩ :=
  accepted_of_selected 13 303327 ⟨575834, by decide⟩ ⟨13, 2, 0, 575834, 303327, 809, 16384⟩
    (by decide) selected_cut_22671

theorem unmarked_context_12_75831_575835 : frontier 9 ⟨575835, by decide⟩
    (prefixCache 12 75831) (prefixPartial 12 75831) = false := by
  decide +kernel

theorem node_context_12_75831_575835 : EJMOriginalGlobalDAGData.nodes 9 ⟨575835, by decide⟩ =
    .split (coordinate 12) (![⟨575774, by decide⟩,⟨575803, by decide⟩,⟨575828, by decide⟩,⟨575834, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75831_575835 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75831 ⟨575835, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75831
    ⟨575835, by decide⟩ (by decide) (![⟨575774, by decide⟩,⟨575803, by decide⟩,⟨575828, by decide⟩,⟨575834, by decide⟩]) unmarked_context_12_75831_575835 node_context_12_75831_575835
  intro a
  fin_cases a
  · exact context_13_303324_575774
  · exact context_13_303325_575803
  · exact context_13_303326_575828
  · exact context_13_303327_575834

theorem unmarked_context_11_18957_575836 : frontier 10 ⟨575836, by decide⟩
    (prefixCache 11 18957) (prefixPartial 11 18957) = false := by
  decide +kernel

theorem node_context_11_18957_575836 : EJMOriginalGlobalDAGData.nodes 10 ⟨575836, by decide⟩ =
    .split (coordinate 11) (![⟨475533, by decide⟩,⟨575697, by decide⟩,⟨575761, by decide⟩,⟨575835, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18957_575836 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18957 ⟨575836, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18957
    ⟨575836, by decide⟩ (by decide) (![⟨475533, by decide⟩,⟨575697, by decide⟩,⟨575761, by decide⟩,⟨575835, by decide⟩]) unmarked_context_11_18957_575836 node_context_11_18957_575836
  intro a
  fin_cases a
  · exact context_12_75828_475533
  · exact context_12_75829_575697
  · exact context_12_75830_575761
  · exact context_12_75831_575835

theorem selected_cut_22672 : selected 9 ⟨540780, by decide⟩
    (prefixPartial 12 75832) = some ⟨12, 1, 0, 540780, 75832, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75832_540780 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75832 ⟨540780, by decide⟩ :=
  accepted_of_selected 12 75832 ⟨540780, by decide⟩ ⟨12, 1, 0, 540780, 75832, 1, 65536⟩
    (by decide) selected_cut_22672

theorem selected_cut_22673 : selected 8 ⟨575845, by decide⟩
    (prefixPartial 13 303332) = some ⟨13, 2, 0, 575845, 303332, 361, 16384⟩ := by
  decide +kernel

theorem context_13_303332_575845 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303332 ⟨575845, by decide⟩ :=
  accepted_of_selected 13 303332 ⟨575845, by decide⟩ ⟨13, 2, 0, 575845, 303332, 361, 16384⟩
    (by decide) selected_cut_22673

theorem selected_cut_22674 : selected 8 ⟨575869, by decide⟩
    (prefixPartial 13 303333) = some ⟨13, 2, 0, 575869, 303333, 2237, 16384⟩ := by
  decide +kernel

theorem context_13_303333_575869 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303333 ⟨575869, by decide⟩ :=
  accepted_of_selected 13 303333 ⟨575869, by decide⟩ ⟨13, 2, 0, 575869, 303333, 2237, 16384⟩
    (by decide) selected_cut_22674

theorem selected_cut_22675 : selected 8 ⟨575889, by decide⟩
    (prefixPartial 13 303334) = some ⟨13, 2, 0, 575889, 303334, 1441, 16384⟩ := by
  decide +kernel

theorem context_13_303334_575889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303334 ⟨575889, by decide⟩ :=
  accepted_of_selected 13 303334 ⟨575889, by decide⟩ ⟨13, 2, 0, 575889, 303334, 1441, 16384⟩
    (by decide) selected_cut_22675

theorem selected_cut_22676 : selected 8 ⟨575898, by decide⟩
    (prefixPartial 13 303335) = some ⟨13, 2, 0, 575898, 303335, 925, 16384⟩ := by
  decide +kernel

theorem context_13_303335_575898 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303335 ⟨575898, by decide⟩ :=
  accepted_of_selected 13 303335 ⟨575898, by decide⟩ ⟨13, 2, 0, 575898, 303335, 925, 16384⟩
    (by decide) selected_cut_22676

theorem unmarked_context_12_75833_575899 : frontier 9 ⟨575899, by decide⟩
    (prefixCache 12 75833) (prefixPartial 12 75833) = false := by
  decide +kernel

theorem node_context_12_75833_575899 : EJMOriginalGlobalDAGData.nodes 9 ⟨575899, by decide⟩ =
    .split (coordinate 12) (![⟨575845, by decide⟩,⟨575869, by decide⟩,⟨575889, by decide⟩,⟨575898, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75833_575899 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75833 ⟨575899, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75833
    ⟨575899, by decide⟩ (by decide) (![⟨575845, by decide⟩,⟨575869, by decide⟩,⟨575889, by decide⟩,⟨575898, by decide⟩]) unmarked_context_12_75833_575899 node_context_12_75833_575899
  intro a
  fin_cases a
  · exact context_13_303332_575845
  · exact context_13_303333_575869
  · exact context_13_303334_575889
  · exact context_13_303335_575898

theorem selected_cut_22677 : selected 8 ⟨575906, by decide⟩
    (prefixPartial 13 303336) = some ⟨13, 2, 0, 575906, 303336, 241, 16384⟩ := by
  decide +kernel

theorem context_13_303336_575906 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303336 ⟨575906, by decide⟩ :=
  accepted_of_selected 13 303336 ⟨575906, by decide⟩ ⟨13, 2, 0, 575906, 303336, 241, 16384⟩
    (by decide) selected_cut_22677

theorem selected_cut_22678 : selected 8 ⟨575929, by decide⟩
    (prefixPartial 13 303337) = some ⟨13, 2, 0, 575929, 303337, 2013, 16384⟩ := by
  decide +kernel

theorem context_13_303337_575929 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303337 ⟨575929, by decide⟩ :=
  accepted_of_selected 13 303337 ⟨575929, by decide⟩ ⟨13, 2, 0, 575929, 303337, 2013, 16384⟩
    (by decide) selected_cut_22678

theorem selected_cut_22679 : selected 8 ⟨575948, by decide⟩
    (prefixPartial 13 303338) = some ⟨13, 2, 0, 575948, 303338, 1293, 16384⟩ := by
  decide +kernel

theorem context_13_303338_575948 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303338 ⟨575948, by decide⟩ :=
  accepted_of_selected 13 303338 ⟨575948, by decide⟩ ⟨13, 2, 0, 575948, 303338, 1293, 16384⟩
    (by decide) selected_cut_22679

theorem selected_cut_22680 : selected 8 ⟨575954, by decide⟩
    (prefixPartial 13 303339) = some ⟨13, 2, 0, 575954, 303339, 789, 16384⟩ := by
  decide +kernel

theorem context_13_303339_575954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303339 ⟨575954, by decide⟩ :=
  accepted_of_selected 13 303339 ⟨575954, by decide⟩ ⟨13, 2, 0, 575954, 303339, 789, 16384⟩
    (by decide) selected_cut_22680

theorem unmarked_context_12_75834_575955 : frontier 9 ⟨575955, by decide⟩
    (prefixCache 12 75834) (prefixPartial 12 75834) = false := by
  decide +kernel

theorem node_context_12_75834_575955 : EJMOriginalGlobalDAGData.nodes 9 ⟨575955, by decide⟩ =
    .split (coordinate 12) (![⟨575906, by decide⟩,⟨575929, by decide⟩,⟨575948, by decide⟩,⟨575954, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75834_575955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75834 ⟨575955, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75834
    ⟨575955, by decide⟩ (by decide) (![⟨575906, by decide⟩,⟨575929, by decide⟩,⟨575948, by decide⟩,⟨575954, by decide⟩]) unmarked_context_12_75834_575955 node_context_12_75834_575955
  intro a
  fin_cases a
  · exact context_13_303336_575906
  · exact context_13_303337_575929
  · exact context_13_303338_575948
  · exact context_13_303339_575954

theorem selected_cut_22681 : selected 8 ⟨575963, by decide⟩
    (prefixPartial 13 303340) = some ⟨13, 2, 0, 575963, 303340, 209, 16384⟩ := by
  decide +kernel

theorem context_13_303340_575963 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303340 ⟨575963, by decide⟩ :=
  accepted_of_selected 13 303340 ⟨575963, by decide⟩ ⟨13, 2, 0, 575963, 303340, 209, 16384⟩
    (by decide) selected_cut_22681

theorem selected_cut_22682 : selected 8 ⟨575992, by decide⟩
    (prefixPartial 13 303341) = some ⟨13, 2, 0, 575992, 303341, 2461, 16384⟩ := by
  decide +kernel

theorem context_13_303341_575992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303341 ⟨575992, by decide⟩ :=
  accepted_of_selected 13 303341 ⟨575992, by decide⟩ ⟨13, 2, 0, 575992, 303341, 2461, 16384⟩
    (by decide) selected_cut_22682

theorem selected_cut_22683 : selected 8 ⟨576011, by decide⟩
    (prefixPartial 13 303342) = some ⟨13, 2, 0, 576011, 303342, 1313, 16384⟩ := by
  decide +kernel

theorem context_13_303342_576011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303342 ⟨576011, by decide⟩ :=
  accepted_of_selected 13 303342 ⟨576011, by decide⟩ ⟨13, 2, 0, 576011, 303342, 1313, 16384⟩
    (by decide) selected_cut_22683

theorem selected_cut_22684 : selected 8 ⟨576016, by decide⟩
    (prefixPartial 13 303343) = some ⟨13, 2, 0, 576016, 303343, 717, 16384⟩ := by
  decide +kernel

theorem context_13_303343_576016 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303343 ⟨576016, by decide⟩ :=
  accepted_of_selected 13 303343 ⟨576016, by decide⟩ ⟨13, 2, 0, 576016, 303343, 717, 16384⟩
    (by decide) selected_cut_22684

theorem unmarked_context_12_75835_576017 : frontier 9 ⟨576017, by decide⟩
    (prefixCache 12 75835) (prefixPartial 12 75835) = false := by
  decide +kernel

theorem node_context_12_75835_576017 : EJMOriginalGlobalDAGData.nodes 9 ⟨576017, by decide⟩ =
    .split (coordinate 12) (![⟨575963, by decide⟩,⟨575992, by decide⟩,⟨576011, by decide⟩,⟨576016, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75835_576017 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75835 ⟨576017, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75835
    ⟨576017, by decide⟩ (by decide) (![⟨575963, by decide⟩,⟨575992, by decide⟩,⟨576011, by decide⟩,⟨576016, by decide⟩]) unmarked_context_12_75835_576017 node_context_12_75835_576017
  intro a
  fin_cases a
  · exact context_13_303340_575963
  · exact context_13_303341_575992
  · exact context_13_303342_576011
  · exact context_13_303343_576016

theorem unmarked_context_11_18958_576018 : frontier 10 ⟨576018, by decide⟩
    (prefixCache 11 18958) (prefixPartial 11 18958) = false := by
  decide +kernel

theorem node_context_11_18958_576018 : EJMOriginalGlobalDAGData.nodes 10 ⟨576018, by decide⟩ =
    .split (coordinate 11) (![⟨540780, by decide⟩,⟨575899, by decide⟩,⟨575955, by decide⟩,⟨576017, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18958_576018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18958 ⟨576018, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18958
    ⟨576018, by decide⟩ (by decide) (![⟨540780, by decide⟩,⟨575899, by decide⟩,⟨575955, by decide⟩,⟨576017, by decide⟩]) unmarked_context_11_18958_576018 node_context_11_18958_576018
  intro a
  fin_cases a
  · exact context_12_75832_540780
  · exact context_12_75833_575899
  · exact context_12_75834_575955
  · exact context_12_75835_576017

theorem selected_cut_22685 : selected 9 ⟨445562, by decide⟩
    (prefixPartial 12 75836) = some ⟨12, 1, 0, 445562, 75836, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75836_445562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75836 ⟨445562, by decide⟩ :=
  accepted_of_selected 12 75836 ⟨445562, by decide⟩ ⟨12, 1, 0, 445562, 75836, 1, 65536⟩
    (by decide) selected_cut_22685

theorem selected_cut_22686 : selected 8 ⟨576023, by decide⟩
    (prefixPartial 13 303348) = some ⟨13, 2, 0, 576023, 303348, 185, 16384⟩ := by
  decide +kernel

theorem context_13_303348_576023 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303348 ⟨576023, by decide⟩ :=
  accepted_of_selected 13 303348 ⟨576023, by decide⟩ ⟨13, 2, 0, 576023, 303348, 185, 16384⟩
    (by decide) selected_cut_22686

theorem selected_cut_22687 : selected 8 ⟨576054, by decide⟩
    (prefixPartial 13 303349) = some ⟨13, 2, 0, 576054, 303349, 2645, 16384⟩ := by
  decide +kernel

theorem context_13_303349_576054 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303349 ⟨576054, by decide⟩ :=
  accepted_of_selected 13 303349 ⟨576054, by decide⟩ ⟨13, 2, 0, 576054, 303349, 2645, 16384⟩
    (by decide) selected_cut_22687

theorem selected_cut_22688 : selected 8 ⟨576072, by decide⟩
    (prefixPartial 13 303350) = some ⟨13, 2, 0, 576072, 303350, 1593, 16384⟩ := by
  decide +kernel

theorem context_13_303350_576072 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303350 ⟨576072, by decide⟩ :=
  accepted_of_selected 13 303350 ⟨576072, by decide⟩ ⟨13, 2, 0, 576072, 303350, 1593, 16384⟩
    (by decide) selected_cut_22688

theorem selected_cut_22689 : selected 8 ⟨576077, by decide⟩
    (prefixPartial 13 303351) = some ⟨13, 2, 0, 576077, 303351, 913, 16384⟩ := by
  decide +kernel

theorem context_13_303351_576077 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303351 ⟨576077, by decide⟩ :=
  accepted_of_selected 13 303351 ⟨576077, by decide⟩ ⟨13, 2, 0, 576077, 303351, 913, 16384⟩
    (by decide) selected_cut_22689

theorem unmarked_context_12_75837_576078 : frontier 9 ⟨576078, by decide⟩
    (prefixCache 12 75837) (prefixPartial 12 75837) = false := by
  decide +kernel

theorem node_context_12_75837_576078 : EJMOriginalGlobalDAGData.nodes 9 ⟨576078, by decide⟩ =
    .split (coordinate 12) (![⟨576023, by decide⟩,⟨576054, by decide⟩,⟨576072, by decide⟩,⟨576077, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75837_576078 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75837 ⟨576078, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75837
    ⟨576078, by decide⟩ (by decide) (![⟨576023, by decide⟩,⟨576054, by decide⟩,⟨576072, by decide⟩,⟨576077, by decide⟩]) unmarked_context_12_75837_576078 node_context_12_75837_576078
  intro a
  fin_cases a
  · exact context_13_303348_576023
  · exact context_13_303349_576054
  · exact context_13_303350_576072
  · exact context_13_303351_576077

theorem selected_cut_22690 : selected 8 ⟨576082, by decide⟩
    (prefixPartial 13 303352) = some ⟨13, 2, 0, 576082, 303352, 105, 16384⟩ := by
  decide +kernel

theorem context_13_303352_576082 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303352 ⟨576082, by decide⟩ :=
  accepted_of_selected 13 303352 ⟨576082, by decide⟩ ⟨13, 2, 0, 576082, 303352, 105, 16384⟩
    (by decide) selected_cut_22690

theorem selected_cut_22691 : selected 8 ⟨576117, by decide⟩
    (prefixPartial 13 303353) = some ⟨13, 2, 0, 576117, 303353, 2661, 16384⟩ := by
  decide +kernel

theorem context_13_303353_576117 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303353 ⟨576117, by decide⟩ :=
  accepted_of_selected 13 303353 ⟨576117, by decide⟩ ⟨13, 2, 0, 576117, 303353, 2661, 16384⟩
    (by decide) selected_cut_22691

theorem selected_cut_22692 : selected 8 ⟨576138, by decide⟩
    (prefixPartial 13 303354) = some ⟨13, 2, 0, 576138, 303354, 1605, 16384⟩ := by
  decide +kernel

theorem context_13_303354_576138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303354 ⟨576138, by decide⟩ :=
  accepted_of_selected 13 303354 ⟨576138, by decide⟩ ⟨13, 2, 0, 576138, 303354, 1605, 16384⟩
    (by decide) selected_cut_22692

theorem selected_cut_22693 : selected 8 ⟨576143, by decide⟩
    (prefixPartial 13 303355) = some ⟨13, 2, 0, 576143, 303355, 865, 16384⟩ := by
  decide +kernel

theorem context_13_303355_576143 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303355 ⟨576143, by decide⟩ :=
  accepted_of_selected 13 303355 ⟨576143, by decide⟩ ⟨13, 2, 0, 576143, 303355, 865, 16384⟩
    (by decide) selected_cut_22693

theorem unmarked_context_12_75838_576144 : frontier 9 ⟨576144, by decide⟩
    (prefixCache 12 75838) (prefixPartial 12 75838) = false := by
  decide +kernel

theorem node_context_12_75838_576144 : EJMOriginalGlobalDAGData.nodes 9 ⟨576144, by decide⟩ =
    .split (coordinate 12) (![⟨576082, by decide⟩,⟨576117, by decide⟩,⟨576138, by decide⟩,⟨576143, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75838_576144 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75838 ⟨576144, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75838
    ⟨576144, by decide⟩ (by decide) (![⟨576082, by decide⟩,⟨576117, by decide⟩,⟨576138, by decide⟩,⟨576143, by decide⟩]) unmarked_context_12_75838_576144 node_context_12_75838_576144
  intro a
  fin_cases a
  · exact context_13_303352_576082
  · exact context_13_303353_576117
  · exact context_13_303354_576138
  · exact context_13_303355_576143

theorem selected_cut_22694 : selected 8 ⟨576148, by decide⟩
    (prefixPartial 13 303356) = some ⟨13, 2, 0, 576148, 303356, 57, 16384⟩ := by
  decide +kernel

theorem context_13_303356_576148 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303356 ⟨576148, by decide⟩ :=
  accepted_of_selected 13 303356 ⟨576148, by decide⟩ ⟨13, 2, 0, 576148, 303356, 57, 16384⟩
    (by decide) selected_cut_22694

theorem selected_cut_22695 : selected 8 ⟨576179, by decide⟩
    (prefixPartial 13 303357) = some ⟨13, 2, 0, 576179, 303357, 2569, 16384⟩ := by
  decide +kernel

theorem context_13_303357_576179 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303357 ⟨576179, by decide⟩ :=
  accepted_of_selected 13 303357 ⟨576179, by decide⟩ ⟨13, 2, 0, 576179, 303357, 2569, 16384⟩
    (by decide) selected_cut_22695

theorem selected_cut_22696 : selected 8 ⟨576200, by decide⟩
    (prefixPartial 13 303358) = some ⟨13, 2, 0, 576200, 303358, 1457, 16384⟩ := by
  decide +kernel

theorem context_13_303358_576200 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303358 ⟨576200, by decide⟩ :=
  accepted_of_selected 13 303358 ⟨576200, by decide⟩ ⟨13, 2, 0, 576200, 303358, 1457, 16384⟩
    (by decide) selected_cut_22696

theorem selected_cut_22697 : selected 8 ⟨576205, by decide⟩
    (prefixPartial 13 303359) = some ⟨13, 2, 0, 576205, 303359, 717, 16384⟩ := by
  decide +kernel

theorem context_13_303359_576205 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303359 ⟨576205, by decide⟩ :=
  accepted_of_selected 13 303359 ⟨576205, by decide⟩ ⟨13, 2, 0, 576205, 303359, 717, 16384⟩
    (by decide) selected_cut_22697

theorem unmarked_context_12_75839_576206 : frontier 9 ⟨576206, by decide⟩
    (prefixCache 12 75839) (prefixPartial 12 75839) = false := by
  decide +kernel

theorem node_context_12_75839_576206 : EJMOriginalGlobalDAGData.nodes 9 ⟨576206, by decide⟩ =
    .split (coordinate 12) (![⟨576148, by decide⟩,⟨576179, by decide⟩,⟨576200, by decide⟩,⟨576205, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75839_576206 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75839 ⟨576206, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75839
    ⟨576206, by decide⟩ (by decide) (![⟨576148, by decide⟩,⟨576179, by decide⟩,⟨576200, by decide⟩,⟨576205, by decide⟩]) unmarked_context_12_75839_576206 node_context_12_75839_576206
  intro a
  fin_cases a
  · exact context_13_303356_576148
  · exact context_13_303357_576179
  · exact context_13_303358_576200
  · exact context_13_303359_576205

theorem unmarked_context_11_18959_576207 : frontier 10 ⟨576207, by decide⟩
    (prefixCache 11 18959) (prefixPartial 11 18959) = false := by
  decide +kernel

theorem node_context_11_18959_576207 : EJMOriginalGlobalDAGData.nodes 10 ⟨576207, by decide⟩ =
    .split (coordinate 11) (![⟨445562, by decide⟩,⟨576078, by decide⟩,⟨576144, by decide⟩,⟨576206, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18959_576207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18959 ⟨576207, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18959
    ⟨576207, by decide⟩ (by decide) (![⟨445562, by decide⟩,⟨576078, by decide⟩,⟨576144, by decide⟩,⟨576206, by decide⟩]) unmarked_context_11_18959_576207 node_context_11_18959_576207
  intro a
  fin_cases a
  · exact context_12_75836_445562
  · exact context_12_75837_576078
  · exact context_12_75838_576144
  · exact context_12_75839_576206

theorem unmarked_context_10_4739_576208 : frontier 11 ⟨576208, by decide⟩
    (prefixCache 10 4739) (prefixPartial 10 4739) = false := by
  decide +kernel

theorem node_context_10_4739_576208 : EJMOriginalGlobalDAGData.nodes 11 ⟨576208, by decide⟩ =
    .split (coordinate 10) (![⟨575645, by decide⟩,⟨575836, by decide⟩,⟨576018, by decide⟩,⟨576207, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4739_576208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4739 ⟨576208, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4739
    ⟨576208, by decide⟩ (by decide) (![⟨575645, by decide⟩,⟨575836, by decide⟩,⟨576018, by decide⟩,⟨576207, by decide⟩]) unmarked_context_10_4739_576208 node_context_10_4739_576208
  intro a
  fin_cases a
  · exact context_11_18956_575645
  · exact context_11_18957_575836
  · exact context_11_18958_576018
  · exact context_11_18959_576207

theorem unmarked_context_9_1184_576209 : frontier 12 ⟨576209, by decide⟩
    (prefixCache 9 1184) (prefixPartial 9 1184) = false := by
  decide +kernel

theorem node_context_9_1184_576209 : EJMOriginalGlobalDAGData.nodes 12 ⟨576209, by decide⟩ =
    .split (coordinate 9) (![⟨573825, by decide⟩,⟨574765, by decide⟩,⟨575469, by decide⟩,⟨576208, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1184_576209 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1184 ⟨576209, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1184
    ⟨576209, by decide⟩ (by decide) (![⟨573825, by decide⟩,⟨574765, by decide⟩,⟨575469, by decide⟩,⟨576208, by decide⟩]) unmarked_context_9_1184_576209 node_context_9_1184_576209
  intro a
  fin_cases a
  · exact context_10_4736_573825
  · exact context_10_4737_574765
  · exact context_10_4738_575469
  · exact context_10_4739_576208

theorem selected_cut_22698 : selected 9 ⟨450982, by decide⟩
    (prefixPartial 12 75840) = some ⟨12, 1, 0, 450982, 75840, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75840_450982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75840 ⟨450982, by decide⟩ :=
  accepted_of_selected 12 75840 ⟨450982, by decide⟩ ⟨12, 1, 0, 450982, 75840, 1, 65536⟩
    (by decide) selected_cut_22698

theorem selected_cut_22699 : selected 9 ⟨576249, by decide⟩
    (prefixPartial 12 75841) = some ⟨12, 2, 0, 576249, 75841, 2921, 65536⟩ := by
  decide +kernel

theorem context_12_75841_576249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75841 ⟨576249, by decide⟩ :=
  accepted_of_selected 12 75841 ⟨576249, by decide⟩ ⟨12, 2, 0, 576249, 75841, 2921, 65536⟩
    (by decide) selected_cut_22699

theorem selected_cut_22700 : selected 9 ⟨576287, by decide⟩
    (prefixPartial 12 75842) = some ⟨12, 2, 0, 576287, 75842, 3293, 65536⟩ := by
  decide +kernel

theorem context_12_75842_576287 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75842 ⟨576287, by decide⟩ :=
  accepted_of_selected 12 75842 ⟨576287, by decide⟩ ⟨12, 2, 0, 576287, 75842, 3293, 65536⟩
    (by decide) selected_cut_22700

theorem selected_cut_22701 : selected 9 ⟨576328, by decide⟩
    (prefixPartial 12 75843) = some ⟨12, 2, 0, 576328, 75843, 3405, 65536⟩ := by
  decide +kernel

theorem context_12_75843_576328 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75843 ⟨576328, by decide⟩ :=
  accepted_of_selected 12 75843 ⟨576328, by decide⟩ ⟨12, 2, 0, 576328, 75843, 3405, 65536⟩
    (by decide) selected_cut_22701

theorem unmarked_context_11_18960_576329 : frontier 10 ⟨576329, by decide⟩
    (prefixCache 11 18960) (prefixPartial 11 18960) = false := by
  decide +kernel

theorem node_context_11_18960_576329 : EJMOriginalGlobalDAGData.nodes 10 ⟨576329, by decide⟩ =
    .split (coordinate 11) (![⟨450982, by decide⟩,⟨576249, by decide⟩,⟨576287, by decide⟩,⟨576328, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18960_576329 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18960 ⟨576329, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18960
    ⟨576329, by decide⟩ (by decide) (![⟨450982, by decide⟩,⟨576249, by decide⟩,⟨576287, by decide⟩,⟨576328, by decide⟩]) unmarked_context_11_18960_576329 node_context_11_18960_576329
  intro a
  fin_cases a
  · exact context_12_75840_450982
  · exact context_12_75841_576249
  · exact context_12_75842_576287
  · exact context_12_75843_576328

theorem selected_cut_22702 : selected 9 ⟨576365, by decide⟩
    (prefixPartial 12 75844) = some ⟨12, 2, 0, 576365, 75844, 2789, 65536⟩ := by
  decide +kernel

theorem context_12_75844_576365 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75844 ⟨576365, by decide⟩ :=
  accepted_of_selected 12 75844 ⟨576365, by decide⟩ ⟨12, 2, 0, 576365, 75844, 2789, 65536⟩
    (by decide) selected_cut_22702

theorem selected_cut_22703 : selected 9 ⟨576407, by decide⟩
    (prefixPartial 12 75845) = some ⟨12, 2, 0, 576407, 75845, 2945, 65536⟩ := by
  decide +kernel

theorem context_12_75845_576407 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75845 ⟨576407, by decide⟩ :=
  accepted_of_selected 12 75845 ⟨576407, by decide⟩ ⟨12, 2, 0, 576407, 75845, 2945, 65536⟩
    (by decide) selected_cut_22703

theorem selected_cut_22704 : selected 9 ⟨576447, by decide⟩
    (prefixPartial 12 75846) = some ⟨12, 2, 0, 576447, 75846, 3433, 65536⟩ := by
  decide +kernel

theorem context_12_75846_576447 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75846 ⟨576447, by decide⟩ :=
  accepted_of_selected 12 75846 ⟨576447, by decide⟩ ⟨12, 2, 0, 576447, 75846, 3433, 65536⟩
    (by decide) selected_cut_22704

theorem selected_cut_22705 : selected 9 ⟨576497, by decide⟩
    (prefixPartial 12 75847) = some ⟨12, 2, 0, 576497, 75847, 3617, 65536⟩ := by
  decide +kernel

theorem context_12_75847_576497 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75847 ⟨576497, by decide⟩ :=
  accepted_of_selected 12 75847 ⟨576497, by decide⟩ ⟨12, 2, 0, 576497, 75847, 3617, 65536⟩
    (by decide) selected_cut_22705

theorem unmarked_context_11_18961_576498 : frontier 10 ⟨576498, by decide⟩
    (prefixCache 11 18961) (prefixPartial 11 18961) = false := by
  decide +kernel

theorem node_context_11_18961_576498 : EJMOriginalGlobalDAGData.nodes 10 ⟨576498, by decide⟩ =
    .split (coordinate 11) (![⟨576365, by decide⟩,⟨576407, by decide⟩,⟨576447, by decide⟩,⟨576497, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18961_576498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18961 ⟨576498, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18961
    ⟨576498, by decide⟩ (by decide) (![⟨576365, by decide⟩,⟨576407, by decide⟩,⟨576447, by decide⟩,⟨576497, by decide⟩]) unmarked_context_11_18961_576498 node_context_11_18961_576498
  intro a
  fin_cases a
  · exact context_12_75844_576365
  · exact context_12_75845_576407
  · exact context_12_75846_576447
  · exact context_12_75847_576497

theorem selected_cut_22706 : selected 9 ⟨576536, by decide⟩
    (prefixPartial 12 75848) = some ⟨12, 2, 0, 576536, 75848, 2753, 65536⟩ := by
  decide +kernel

theorem context_12_75848_576536 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75848 ⟨576536, by decide⟩ :=
  accepted_of_selected 12 75848 ⟨576536, by decide⟩ ⟨12, 2, 0, 576536, 75848, 2753, 65536⟩
    (by decide) selected_cut_22706

theorem selected_cut_22707 : selected 9 ⟨576581, by decide⟩
    (prefixPartial 12 75849) = some ⟨12, 2, 0, 576581, 75849, 3033, 65536⟩ := by
  decide +kernel

theorem context_12_75849_576581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75849 ⟨576581, by decide⟩ :=
  accepted_of_selected 12 75849 ⟨576581, by decide⟩ ⟨12, 2, 0, 576581, 75849, 3033, 65536⟩
    (by decide) selected_cut_22707

theorem selected_cut_22708 : selected 9 ⟨576622, by decide⟩
    (prefixPartial 12 75850) = some ⟨12, 2, 0, 576622, 75850, 3233, 65536⟩ := by
  decide +kernel

theorem context_12_75850_576622 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75850 ⟨576622, by decide⟩ :=
  accepted_of_selected 12 75850 ⟨576622, by decide⟩ ⟨12, 2, 0, 576622, 75850, 3233, 65536⟩
    (by decide) selected_cut_22708

theorem selected_cut_22709 : selected 9 ⟨576659, by decide⟩
    (prefixPartial 12 75851) = some ⟨12, 2, 0, 576659, 75851, 3409, 65536⟩ := by
  decide +kernel

theorem context_12_75851_576659 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75851 ⟨576659, by decide⟩ :=
  accepted_of_selected 12 75851 ⟨576659, by decide⟩ ⟨12, 2, 0, 576659, 75851, 3409, 65536⟩
    (by decide) selected_cut_22709

theorem unmarked_context_11_18962_576660 : frontier 10 ⟨576660, by decide⟩
    (prefixCache 11 18962) (prefixPartial 11 18962) = false := by
  decide +kernel

theorem node_context_11_18962_576660 : EJMOriginalGlobalDAGData.nodes 10 ⟨576660, by decide⟩ =
    .split (coordinate 11) (![⟨576536, by decide⟩,⟨576581, by decide⟩,⟨576622, by decide⟩,⟨576659, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18962_576660 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18962 ⟨576660, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18962
    ⟨576660, by decide⟩ (by decide) (![⟨576536, by decide⟩,⟨576581, by decide⟩,⟨576622, by decide⟩,⟨576659, by decide⟩]) unmarked_context_11_18962_576660 node_context_11_18962_576660
  intro a
  fin_cases a
  · exact context_12_75848_576536
  · exact context_12_75849_576581
  · exact context_12_75850_576622
  · exact context_12_75851_576659

theorem selected_cut_22710 : selected 9 ⟨576692, by decide⟩
    (prefixPartial 12 75852) = some ⟨12, 2, 0, 576692, 75852, 2677, 65536⟩ := by
  decide +kernel

theorem context_12_75852_576692 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75852 ⟨576692, by decide⟩ :=
  accepted_of_selected 12 75852 ⟨576692, by decide⟩ ⟨12, 2, 0, 576692, 75852, 2677, 65536⟩
    (by decide) selected_cut_22710

theorem selected_cut_22711 : selected 9 ⟨576735, by decide⟩
    (prefixPartial 12 75853) = some ⟨12, 2, 0, 576735, 75853, 2961, 65536⟩ := by
  decide +kernel

theorem context_12_75853_576735 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75853 ⟨576735, by decide⟩ :=
  accepted_of_selected 12 75853 ⟨576735, by decide⟩ ⟨12, 2, 0, 576735, 75853, 2961, 65536⟩
    (by decide) selected_cut_22711

theorem selected_cut_22712 : selected 9 ⟨576784, by decide⟩
    (prefixPartial 12 75854) = some ⟨12, 2, 0, 576784, 75854, 3433, 65536⟩ := by
  decide +kernel

theorem context_12_75854_576784 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75854 ⟨576784, by decide⟩ :=
  accepted_of_selected 12 75854 ⟨576784, by decide⟩ ⟨12, 2, 0, 576784, 75854, 3433, 65536⟩
    (by decide) selected_cut_22712

theorem selected_cut_22713 : selected 9 ⟨576832, by decide⟩
    (prefixPartial 12 75855) = some ⟨12, 2, 0, 576832, 75855, 3333, 65536⟩ := by
  decide +kernel

theorem context_12_75855_576832 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75855 ⟨576832, by decide⟩ :=
  accepted_of_selected 12 75855 ⟨576832, by decide⟩ ⟨12, 2, 0, 576832, 75855, 3333, 65536⟩
    (by decide) selected_cut_22713

theorem unmarked_context_11_18963_576833 : frontier 10 ⟨576833, by decide⟩
    (prefixCache 11 18963) (prefixPartial 11 18963) = false := by
  decide +kernel

theorem node_context_11_18963_576833 : EJMOriginalGlobalDAGData.nodes 10 ⟨576833, by decide⟩ =
    .split (coordinate 11) (![⟨576692, by decide⟩,⟨576735, by decide⟩,⟨576784, by decide⟩,⟨576832, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18963_576833 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18963 ⟨576833, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18963
    ⟨576833, by decide⟩ (by decide) (![⟨576692, by decide⟩,⟨576735, by decide⟩,⟨576784, by decide⟩,⟨576832, by decide⟩]) unmarked_context_11_18963_576833 node_context_11_18963_576833
  intro a
  fin_cases a
  · exact context_12_75852_576692
  · exact context_12_75853_576735
  · exact context_12_75854_576784
  · exact context_12_75855_576832

theorem unmarked_context_10_4740_576834 : frontier 11 ⟨576834, by decide⟩
    (prefixCache 10 4740) (prefixPartial 10 4740) = false := by
  decide +kernel

theorem node_context_10_4740_576834 : EJMOriginalGlobalDAGData.nodes 11 ⟨576834, by decide⟩ =
    .split (coordinate 10) (![⟨576329, by decide⟩,⟨576498, by decide⟩,⟨576660, by decide⟩,⟨576833, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4740_576834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4740 ⟨576834, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4740
    ⟨576834, by decide⟩ (by decide) (![⟨576329, by decide⟩,⟨576498, by decide⟩,⟨576660, by decide⟩,⟨576833, by decide⟩]) unmarked_context_10_4740_576834 node_context_10_4740_576834
  intro a
  fin_cases a
  · exact context_11_18960_576329
  · exact context_11_18961_576498
  · exact context_11_18962_576660
  · exact context_11_18963_576833

theorem selected_cut_22714 : selected 9 ⟨266170, by decide⟩
    (prefixPartial 12 75856) = some ⟨12, 1, 0, 266170, 75856, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75856_266170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75856 ⟨266170, by decide⟩ :=
  accepted_of_selected 12 75856 ⟨266170, by decide⟩ ⟨12, 1, 0, 266170, 75856, 1, 65536⟩
    (by decide) selected_cut_22714

theorem selected_cut_22715 : selected 9 ⟨576874, by decide⟩
    (prefixPartial 12 75857) = some ⟨12, 2, 0, 576874, 75857, 3725, 65536⟩ := by
  decide +kernel

theorem context_12_75857_576874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75857 ⟨576874, by decide⟩ :=
  accepted_of_selected 12 75857 ⟨576874, by decide⟩ ⟨12, 2, 0, 576874, 75857, 3725, 65536⟩
    (by decide) selected_cut_22715

theorem selected_cut_22716 : selected 9 ⟨576914, by decide⟩
    (prefixPartial 12 75858) = some ⟨12, 2, 0, 576914, 75858, 4089, 65536⟩ := by
  decide +kernel

theorem context_12_75858_576914 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75858 ⟨576914, by decide⟩ :=
  accepted_of_selected 12 75858 ⟨576914, by decide⟩ ⟨12, 2, 0, 576914, 75858, 4089, 65536⟩
    (by decide) selected_cut_22716

theorem selected_cut_22717 : selected 9 ⟨576956, by decide⟩
    (prefixPartial 12 75859) = some ⟨12, 2, 0, 576956, 75859, 4057, 65536⟩ := by
  decide +kernel

theorem context_12_75859_576956 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75859 ⟨576956, by decide⟩ :=
  accepted_of_selected 12 75859 ⟨576956, by decide⟩ ⟨12, 2, 0, 576956, 75859, 4057, 65536⟩
    (by decide) selected_cut_22717

theorem unmarked_context_11_18964_576957 : frontier 10 ⟨576957, by decide⟩
    (prefixCache 11 18964) (prefixPartial 11 18964) = false := by
  decide +kernel

theorem node_context_11_18964_576957 : EJMOriginalGlobalDAGData.nodes 10 ⟨576957, by decide⟩ =
    .split (coordinate 11) (![⟨266170, by decide⟩,⟨576874, by decide⟩,⟨576914, by decide⟩,⟨576956, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18964_576957 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18964 ⟨576957, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18964
    ⟨576957, by decide⟩ (by decide) (![⟨266170, by decide⟩,⟨576874, by decide⟩,⟨576914, by decide⟩,⟨576956, by decide⟩]) unmarked_context_11_18964_576957 node_context_11_18964_576957
  intro a
  fin_cases a
  · exact context_12_75856_266170
  · exact context_12_75857_576874
  · exact context_12_75858_576914
  · exact context_12_75859_576956

theorem selected_cut_22718 : selected 9 ⟨576998, by decide⟩
    (prefixPartial 12 75860) = some ⟨12, 2, 0, 576998, 75860, 3733, 65536⟩ := by
  decide +kernel

theorem context_12_75860_576998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75860 ⟨576998, by decide⟩ :=
  accepted_of_selected 12 75860 ⟨576998, by decide⟩ ⟨12, 2, 0, 576998, 75860, 3733, 65536⟩
    (by decide) selected_cut_22718

theorem selected_cut_22719 : selected 9 ⟨577043, by decide⟩
    (prefixPartial 12 75861) = some ⟨12, 2, 0, 577043, 75861, 3861, 65536⟩ := by
  decide +kernel

theorem context_12_75861_577043 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75861 ⟨577043, by decide⟩ :=
  accepted_of_selected 12 75861 ⟨577043, by decide⟩ ⟨12, 2, 0, 577043, 75861, 3861, 65536⟩
    (by decide) selected_cut_22719

theorem selected_cut_22720 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 303448) = some ⟨13, 1, 0, 3444, 303448, 1, 16384⟩ := by
  decide +kernel

theorem context_13_303448_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303448 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 303448 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 303448, 1, 16384⟩
    (by decide) selected_cut_22720

theorem selected_cut_22721 : selected 8 ⟨577064, by decide⟩
    (prefixPartial 13 303449) = some ⟨13, 2, 0, 577064, 303449, 1729, 16384⟩ := by
  decide +kernel

theorem context_13_303449_577064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303449 ⟨577064, by decide⟩ :=
  accepted_of_selected 13 303449 ⟨577064, by decide⟩ ⟨13, 2, 0, 577064, 303449, 1729, 16384⟩
    (by decide) selected_cut_22721

theorem selected_cut_22722 : selected 8 ⟨577088, by decide⟩
    (prefixPartial 13 303450) = some ⟨13, 2, 0, 577088, 303450, 1689, 16384⟩ := by
  decide +kernel

theorem context_13_303450_577088 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303450 ⟨577088, by decide⟩ :=
  accepted_of_selected 13 303450 ⟨577088, by decide⟩ ⟨13, 2, 0, 577088, 303450, 1689, 16384⟩
    (by decide) selected_cut_22722

theorem selected_cut_22723 : selected 8 ⟨577103, by decide⟩
    (prefixPartial 13 303451) = some ⟨13, 2, 0, 577103, 303451, 1021, 16384⟩ := by
  decide +kernel

theorem context_13_303451_577103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303451 ⟨577103, by decide⟩ :=
  accepted_of_selected 13 303451 ⟨577103, by decide⟩ ⟨13, 2, 0, 577103, 303451, 1021, 16384⟩
    (by decide) selected_cut_22723

theorem unmarked_context_12_75862_577104 : frontier 9 ⟨577104, by decide⟩
    (prefixCache 12 75862) (prefixPartial 12 75862) = false := by
  decide +kernel

theorem node_context_12_75862_577104 : EJMOriginalGlobalDAGData.nodes 9 ⟨577104, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨577064, by decide⟩,⟨577088, by decide⟩,⟨577103, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75862_577104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75862 ⟨577104, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75862
    ⟨577104, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨577064, by decide⟩,⟨577088, by decide⟩,⟨577103, by decide⟩]) unmarked_context_12_75862_577104 node_context_12_75862_577104
  intro a
  fin_cases a
  · exact context_13_303448_3444
  · exact context_13_303449_577064
  · exact context_13_303450_577088
  · exact context_13_303451_577103

theorem selected_cut_22724 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 303452) = some ⟨13, 1, 0, 3444, 303452, 1, 16384⟩ := by
  decide +kernel

theorem context_13_303452_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303452 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 303452 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 303452, 1, 16384⟩
    (by decide) selected_cut_22724

theorem selected_cut_22725 : selected 8 ⟨577126, by decide⟩
    (prefixPartial 13 303453) = some ⟨13, 2, 0, 577126, 303453, 1701, 16384⟩ := by
  decide +kernel

theorem context_13_303453_577126 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303453 ⟨577126, by decide⟩ :=
  accepted_of_selected 13 303453 ⟨577126, by decide⟩ ⟨13, 2, 0, 577126, 303453, 1701, 16384⟩
    (by decide) selected_cut_22725

theorem selected_cut_22726 : selected 8 ⟨577147, by decide⟩
    (prefixPartial 13 303454) = some ⟨13, 2, 0, 577147, 303454, 1837, 16384⟩ := by
  decide +kernel

theorem context_13_303454_577147 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303454 ⟨577147, by decide⟩ :=
  accepted_of_selected 13 303454 ⟨577147, by decide⟩ ⟨13, 2, 0, 577147, 303454, 1837, 16384⟩
    (by decide) selected_cut_22726

theorem selected_cut_22727 : selected 8 ⟨577155, by decide⟩
    (prefixPartial 13 303455) = some ⟨13, 2, 0, 577155, 303455, 873, 16384⟩ := by
  decide +kernel

theorem context_13_303455_577155 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303455 ⟨577155, by decide⟩ :=
  accepted_of_selected 13 303455 ⟨577155, by decide⟩ ⟨13, 2, 0, 577155, 303455, 873, 16384⟩
    (by decide) selected_cut_22727

theorem unmarked_context_12_75863_577156 : frontier 9 ⟨577156, by decide⟩
    (prefixCache 12 75863) (prefixPartial 12 75863) = false := by
  decide +kernel

theorem node_context_12_75863_577156 : EJMOriginalGlobalDAGData.nodes 9 ⟨577156, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨577126, by decide⟩,⟨577147, by decide⟩,⟨577155, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75863_577156 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75863 ⟨577156, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75863
    ⟨577156, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨577126, by decide⟩,⟨577147, by decide⟩,⟨577155, by decide⟩]) unmarked_context_12_75863_577156 node_context_12_75863_577156
  intro a
  fin_cases a
  · exact context_13_303452_3444
  · exact context_13_303453_577126
  · exact context_13_303454_577147
  · exact context_13_303455_577155

theorem unmarked_context_11_18965_577157 : frontier 10 ⟨577157, by decide⟩
    (prefixCache 11 18965) (prefixPartial 11 18965) = false := by
  decide +kernel

theorem node_context_11_18965_577157 : EJMOriginalGlobalDAGData.nodes 10 ⟨577157, by decide⟩ =
    .split (coordinate 11) (![⟨576998, by decide⟩,⟨577043, by decide⟩,⟨577104, by decide⟩,⟨577156, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18965_577157 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18965 ⟨577157, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18965
    ⟨577157, by decide⟩ (by decide) (![⟨576998, by decide⟩,⟨577043, by decide⟩,⟨577104, by decide⟩,⟨577156, by decide⟩]) unmarked_context_11_18965_577157 node_context_11_18965_577157
  intro a
  fin_cases a
  · exact context_12_75860_576998
  · exact context_12_75861_577043
  · exact context_12_75862_577104
  · exact context_12_75863_577156

theorem selected_cut_22728 : selected 9 ⟨577195, by decide⟩
    (prefixPartial 12 75864) = some ⟨12, 2, 0, 577195, 75864, 3461, 65536⟩ := by
  decide +kernel

theorem context_12_75864_577195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75864 ⟨577195, by decide⟩ :=
  accepted_of_selected 12 75864 ⟨577195, by decide⟩ ⟨12, 2, 0, 577195, 75864, 3461, 65536⟩
    (by decide) selected_cut_22728

theorem selected_cut_22729 : selected 9 ⟨577242, by decide⟩
    (prefixPartial 12 75865) = some ⟨12, 2, 0, 577242, 75865, 3841, 65536⟩ := by
  decide +kernel

theorem context_12_75865_577242 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75865 ⟨577242, by decide⟩ :=
  accepted_of_selected 12 75865 ⟨577242, by decide⟩ ⟨12, 2, 0, 577242, 75865, 3841, 65536⟩
    (by decide) selected_cut_22729

theorem selected_cut_22730 : selected 9 ⟨577289, by decide⟩
    (prefixPartial 12 75866) = some ⟨12, 2, 0, 577289, 75866, 3801, 65536⟩ := by
  decide +kernel

theorem context_12_75866_577289 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75866 ⟨577289, by decide⟩ :=
  accepted_of_selected 12 75866 ⟨577289, by decide⟩ ⟨12, 2, 0, 577289, 75866, 3801, 65536⟩
    (by decide) selected_cut_22730

theorem selected_cut_22731 : selected 9 ⟨577328, by decide⟩
    (prefixPartial 12 75867) = some ⟨12, 2, 0, 577328, 75867, 3973, 65536⟩ := by
  decide +kernel

theorem context_12_75867_577328 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75867 ⟨577328, by decide⟩ :=
  accepted_of_selected 12 75867 ⟨577328, by decide⟩ ⟨12, 2, 0, 577328, 75867, 3973, 65536⟩
    (by decide) selected_cut_22731

theorem unmarked_context_11_18966_577329 : frontier 10 ⟨577329, by decide⟩
    (prefixCache 11 18966) (prefixPartial 11 18966) = false := by
  decide +kernel

theorem node_context_11_18966_577329 : EJMOriginalGlobalDAGData.nodes 10 ⟨577329, by decide⟩ =
    .split (coordinate 11) (![⟨577195, by decide⟩,⟨577242, by decide⟩,⟨577289, by decide⟩,⟨577328, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18966_577329 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18966 ⟨577329, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18966
    ⟨577329, by decide⟩ (by decide) (![⟨577195, by decide⟩,⟨577242, by decide⟩,⟨577289, by decide⟩,⟨577328, by decide⟩]) unmarked_context_11_18966_577329 node_context_11_18966_577329
  intro a
  fin_cases a
  · exact context_12_75864_577195
  · exact context_12_75865_577242
  · exact context_12_75866_577289
  · exact context_12_75867_577328

theorem selected_cut_22732 : selected 9 ⟨577365, by decide⟩
    (prefixPartial 12 75868) = some ⟨12, 2, 0, 577365, 75868, 3305, 65536⟩ := by
  decide +kernel

theorem context_12_75868_577365 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75868 ⟨577365, by decide⟩ :=
  accepted_of_selected 12 75868 ⟨577365, by decide⟩ ⟨12, 2, 0, 577365, 75868, 3305, 65536⟩
    (by decide) selected_cut_22732

theorem selected_cut_22733 : selected 9 ⟨577404, by decide⟩
    (prefixPartial 12 75869) = some ⟨12, 2, 0, 577404, 75869, 3689, 65536⟩ := by
  decide +kernel

theorem context_12_75869_577404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75869 ⟨577404, by decide⟩ :=
  accepted_of_selected 12 75869 ⟨577404, by decide⟩ ⟨12, 2, 0, 577404, 75869, 3689, 65536⟩
    (by decide) selected_cut_22733

theorem selected_cut_22734 : selected 9 ⟨577451, by decide⟩
    (prefixPartial 12 75870) = some ⟨12, 2, 0, 577451, 75870, 3981, 65536⟩ := by
  decide +kernel

theorem context_12_75870_577451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75870 ⟨577451, by decide⟩ :=
  accepted_of_selected 12 75870 ⟨577451, by decide⟩ ⟨12, 2, 0, 577451, 75870, 3981, 65536⟩
    (by decide) selected_cut_22734

theorem selected_cut_22735 : selected 9 ⟨577486, by decide⟩
    (prefixPartial 12 75871) = some ⟨12, 2, 0, 577486, 75871, 3809, 65536⟩ := by
  decide +kernel

theorem context_12_75871_577486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75871 ⟨577486, by decide⟩ :=
  accepted_of_selected 12 75871 ⟨577486, by decide⟩ ⟨12, 2, 0, 577486, 75871, 3809, 65536⟩
    (by decide) selected_cut_22735

theorem unmarked_context_11_18967_577487 : frontier 10 ⟨577487, by decide⟩
    (prefixCache 11 18967) (prefixPartial 11 18967) = false := by
  decide +kernel

theorem node_context_11_18967_577487 : EJMOriginalGlobalDAGData.nodes 10 ⟨577487, by decide⟩ =
    .split (coordinate 11) (![⟨577365, by decide⟩,⟨577404, by decide⟩,⟨577451, by decide⟩,⟨577486, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18967_577487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18967 ⟨577487, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18967
    ⟨577487, by decide⟩ (by decide) (![⟨577365, by decide⟩,⟨577404, by decide⟩,⟨577451, by decide⟩,⟨577486, by decide⟩]) unmarked_context_11_18967_577487 node_context_11_18967_577487
  intro a
  fin_cases a
  · exact context_12_75868_577365
  · exact context_12_75869_577404
  · exact context_12_75870_577451
  · exact context_12_75871_577486

theorem unmarked_context_10_4741_577488 : frontier 11 ⟨577488, by decide⟩
    (prefixCache 10 4741) (prefixPartial 10 4741) = false := by
  decide +kernel

theorem node_context_10_4741_577488 : EJMOriginalGlobalDAGData.nodes 11 ⟨577488, by decide⟩ =
    .split (coordinate 10) (![⟨576957, by decide⟩,⟨577157, by decide⟩,⟨577329, by decide⟩,⟨577487, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4741_577488 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4741 ⟨577488, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4741
    ⟨577488, by decide⟩ (by decide) (![⟨576957, by decide⟩,⟨577157, by decide⟩,⟨577329, by decide⟩,⟨577487, by decide⟩]) unmarked_context_10_4741_577488 node_context_10_4741_577488
  intro a
  fin_cases a
  · exact context_11_18964_576957
  · exact context_11_18965_577157
  · exact context_11_18966_577329
  · exact context_11_18967_577487

theorem selected_cut_22736 : selected 9 ⟨577584, by decide⟩
    (prefixPartial 12 75872) = some ⟨12, 2, 0, 577584, 75872, 2285, 65536⟩ := by
  decide +kernel

theorem context_12_75872_577584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75872 ⟨577584, by decide⟩ :=
  accepted_of_selected 12 75872 ⟨577584, by decide⟩ ⟨12, 2, 0, 577584, 75872, 2285, 65536⟩
    (by decide) selected_cut_22736

theorem selected_cut_22737 : selected 9 ⟨577617, by decide⟩
    (prefixPartial 12 75873) = some ⟨12, 2, 0, 577617, 75873, 2773, 65536⟩ := by
  decide +kernel

theorem context_12_75873_577617 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75873 ⟨577617, by decide⟩ :=
  accepted_of_selected 12 75873 ⟨577617, by decide⟩ ⟨12, 2, 0, 577617, 75873, 2773, 65536⟩
    (by decide) selected_cut_22737

theorem selected_cut_22738 : selected 9 ⟨577650, by decide⟩
    (prefixPartial 12 75874) = some ⟨12, 2, 0, 577650, 75874, 2969, 65536⟩ := by
  decide +kernel

theorem context_12_75874_577650 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75874 ⟨577650, by decide⟩ :=
  accepted_of_selected 12 75874 ⟨577650, by decide⟩ ⟨12, 2, 0, 577650, 75874, 2969, 65536⟩
    (by decide) selected_cut_22738

theorem selected_cut_22739 : selected 9 ⟨577685, by decide⟩
    (prefixPartial 12 75875) = some ⟨12, 2, 0, 577685, 75875, 3013, 65536⟩ := by
  decide +kernel

theorem context_12_75875_577685 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75875 ⟨577685, by decide⟩ :=
  accepted_of_selected 12 75875 ⟨577685, by decide⟩ ⟨12, 2, 0, 577685, 75875, 3013, 65536⟩
    (by decide) selected_cut_22739

theorem unmarked_context_11_18968_577686 : frontier 10 ⟨577686, by decide⟩
    (prefixCache 11 18968) (prefixPartial 11 18968) = false := by
  decide +kernel

theorem node_context_11_18968_577686 : EJMOriginalGlobalDAGData.nodes 10 ⟨577686, by decide⟩ =
    .split (coordinate 11) (![⟨577584, by decide⟩,⟨577617, by decide⟩,⟨577650, by decide⟩,⟨577685, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18968_577686 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18968 ⟨577686, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18968
    ⟨577686, by decide⟩ (by decide) (![⟨577584, by decide⟩,⟨577617, by decide⟩,⟨577650, by decide⟩,⟨577685, by decide⟩]) unmarked_context_11_18968_577686 node_context_11_18968_577686
  intro a
  fin_cases a
  · exact context_12_75872_577584
  · exact context_12_75873_577617
  · exact context_12_75874_577650
  · exact context_12_75875_577685

theorem selected_cut_22740 : selected 9 ⟨577724, by decide⟩
    (prefixPartial 12 75876) = some ⟨12, 2, 0, 577724, 75876, 3049, 65536⟩ := by
  decide +kernel

theorem context_12_75876_577724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75876 ⟨577724, by decide⟩ :=
  accepted_of_selected 12 75876 ⟨577724, by decide⟩ ⟨12, 2, 0, 577724, 75876, 3049, 65536⟩
    (by decide) selected_cut_22740

theorem selected_cut_22741 : selected 9 ⟨577765, by decide⟩
    (prefixPartial 12 75877) = some ⟨12, 2, 0, 577765, 75877, 2929, 65536⟩ := by
  decide +kernel

theorem context_12_75877_577765 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75877 ⟨577765, by decide⟩ :=
  accepted_of_selected 12 75877 ⟨577765, by decide⟩ ⟨12, 2, 0, 577765, 75877, 2929, 65536⟩
    (by decide) selected_cut_22741

theorem selected_cut_22742 : selected 9 ⟨577810, by decide⟩
    (prefixPartial 12 75878) = some ⟨12, 2, 0, 577810, 75878, 3361, 65536⟩ := by
  decide +kernel

theorem context_12_75878_577810 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75878 ⟨577810, by decide⟩ :=
  accepted_of_selected 12 75878 ⟨577810, by decide⟩ ⟨12, 2, 0, 577810, 75878, 3361, 65536⟩
    (by decide) selected_cut_22742

theorem selected_cut_22743 : selected 9 ⟨577850, by decide⟩
    (prefixPartial 12 75879) = some ⟨12, 2, 0, 577850, 75879, 3453, 65536⟩ := by
  decide +kernel

theorem context_12_75879_577850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75879 ⟨577850, by decide⟩ :=
  accepted_of_selected 12 75879 ⟨577850, by decide⟩ ⟨12, 2, 0, 577850, 75879, 3453, 65536⟩
    (by decide) selected_cut_22743

theorem unmarked_context_11_18969_577851 : frontier 10 ⟨577851, by decide⟩
    (prefixCache 11 18969) (prefixPartial 11 18969) = false := by
  decide +kernel

theorem node_context_11_18969_577851 : EJMOriginalGlobalDAGData.nodes 10 ⟨577851, by decide⟩ =
    .split (coordinate 11) (![⟨577724, by decide⟩,⟨577765, by decide⟩,⟨577810, by decide⟩,⟨577850, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18969_577851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18969 ⟨577851, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18969
    ⟨577851, by decide⟩ (by decide) (![⟨577724, by decide⟩,⟨577765, by decide⟩,⟨577810, by decide⟩,⟨577850, by decide⟩]) unmarked_context_11_18969_577851 node_context_11_18969_577851
  intro a
  fin_cases a
  · exact context_12_75876_577724
  · exact context_12_75877_577765
  · exact context_12_75878_577810
  · exact context_12_75879_577850

theorem selected_cut_22744 : selected 9 ⟨577893, by decide⟩
    (prefixPartial 12 75880) = some ⟨12, 2, 0, 577893, 75880, 3825, 65536⟩ := by
  decide +kernel

theorem context_12_75880_577893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75880 ⟨577893, by decide⟩ :=
  accepted_of_selected 12 75880 ⟨577893, by decide⟩ ⟨12, 2, 0, 577893, 75880, 3825, 65536⟩
    (by decide) selected_cut_22744

theorem selected_cut_22745 : selected 9 ⟨577942, by decide⟩
    (prefixPartial 12 75881) = some ⟨12, 2, 0, 577942, 75881, 4021, 65536⟩ := by
  decide +kernel

theorem context_12_75881_577942 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75881 ⟨577942, by decide⟩ :=
  accepted_of_selected 12 75881 ⟨577942, by decide⟩ ⟨12, 2, 0, 577942, 75881, 4021, 65536⟩
    (by decide) selected_cut_22745

theorem selected_cut_22746 : selected 9 ⟨474208, by decide⟩
    (prefixPartial 12 75882) = some ⟨12, 1, 0, 474208, 75882, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75882_474208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75882 ⟨474208, by decide⟩ :=
  accepted_of_selected 12 75882 ⟨474208, by decide⟩ ⟨12, 1, 0, 474208, 75882, 1, 65536⟩
    (by decide) selected_cut_22746

theorem selected_cut_22747 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 303532) = some ⟨13, 1, 0, 3444, 303532, 1, 16384⟩ := by
  decide +kernel

theorem context_13_303532_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303532 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 303532 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 303532, 1, 16384⟩
    (by decide) selected_cut_22747

theorem selected_cut_22748 : selected 8 ⟨577952, by decide⟩
    (prefixPartial 13 303533) = some ⟨13, 2, 0, 577952, 303533, 1089, 16384⟩ := by
  decide +kernel

theorem context_13_303533_577952 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303533 ⟨577952, by decide⟩ :=
  accepted_of_selected 13 303533 ⟨577952, by decide⟩ ⟨13, 2, 0, 577952, 303533, 1089, 16384⟩
    (by decide) selected_cut_22748

theorem selected_cut_22749 : selected 8 ⟨577970, by decide⟩
    (prefixPartial 13 303534) = some ⟨13, 2, 0, 577970, 303534, 1897, 16384⟩ := by
  decide +kernel

theorem context_13_303534_577970 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303534 ⟨577970, by decide⟩ :=
  accepted_of_selected 13 303534 ⟨577970, by decide⟩ ⟨13, 2, 0, 577970, 303534, 1897, 16384⟩
    (by decide) selected_cut_22749

theorem selected_cut_22750 : selected 8 ⟨577982, by decide⟩
    (prefixPartial 13 303535) = some ⟨13, 2, 0, 577982, 303535, 1121, 16384⟩ := by
  decide +kernel

theorem context_13_303535_577982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303535 ⟨577982, by decide⟩ :=
  accepted_of_selected 13 303535 ⟨577982, by decide⟩ ⟨13, 2, 0, 577982, 303535, 1121, 16384⟩
    (by decide) selected_cut_22750

theorem unmarked_context_12_75883_577983 : frontier 9 ⟨577983, by decide⟩
    (prefixCache 12 75883) (prefixPartial 12 75883) = false := by
  decide +kernel

theorem node_context_12_75883_577983 : EJMOriginalGlobalDAGData.nodes 9 ⟨577983, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨577952, by decide⟩,⟨577970, by decide⟩,⟨577982, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75883_577983 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75883 ⟨577983, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75883
    ⟨577983, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨577952, by decide⟩,⟨577970, by decide⟩,⟨577982, by decide⟩]) unmarked_context_12_75883_577983 node_context_12_75883_577983
  intro a
  fin_cases a
  · exact context_13_303532_3444
  · exact context_13_303533_577952
  · exact context_13_303534_577970
  · exact context_13_303535_577982

theorem unmarked_context_11_18970_577984 : frontier 10 ⟨577984, by decide⟩
    (prefixCache 11 18970) (prefixPartial 11 18970) = false := by
  decide +kernel

theorem node_context_11_18970_577984 : EJMOriginalGlobalDAGData.nodes 10 ⟨577984, by decide⟩ =
    .split (coordinate 11) (![⟨577893, by decide⟩,⟨577942, by decide⟩,⟨474208, by decide⟩,⟨577983, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18970_577984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18970 ⟨577984, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18970
    ⟨577984, by decide⟩ (by decide) (![⟨577893, by decide⟩,⟨577942, by decide⟩,⟨474208, by decide⟩,⟨577983, by decide⟩]) unmarked_context_11_18970_577984 node_context_11_18970_577984
  intro a
  fin_cases a
  · exact context_12_75880_577893
  · exact context_12_75881_577942
  · exact context_12_75882_474208
  · exact context_12_75883_577983

theorem selected_cut_22751 : selected 9 ⟨578016, by decide⟩
    (prefixPartial 12 75884) = some ⟨12, 2, 0, 578016, 75884, 2693, 65536⟩ := by
  decide +kernel

theorem context_12_75884_578016 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75884 ⟨578016, by decide⟩ :=
  accepted_of_selected 12 75884 ⟨578016, by decide⟩ ⟨12, 2, 0, 578016, 75884, 2693, 65536⟩
    (by decide) selected_cut_22751

theorem selected_cut_22752 : selected 9 ⟨578047, by decide⟩
    (prefixPartial 12 75885) = some ⟨12, 2, 0, 578047, 75885, 2885, 65536⟩ := by
  decide +kernel

theorem context_12_75885_578047 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75885 ⟨578047, by decide⟩ :=
  accepted_of_selected 12 75885 ⟨578047, by decide⟩ ⟨12, 2, 0, 578047, 75885, 2885, 65536⟩
    (by decide) selected_cut_22752

theorem selected_cut_22753 : selected 9 ⟨578082, by decide⟩
    (prefixPartial 12 75886) = some ⟨12, 2, 0, 578082, 75886, 3101, 65536⟩ := by
  decide +kernel

theorem context_12_75886_578082 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75886 ⟨578082, by decide⟩ :=
  accepted_of_selected 12 75886 ⟨578082, by decide⟩ ⟨12, 2, 0, 578082, 75886, 3101, 65536⟩
    (by decide) selected_cut_22753

theorem selected_cut_22754 : selected 9 ⟨578115, by decide⟩
    (prefixPartial 12 75887) = some ⟨12, 2, 0, 578115, 75887, 2913, 65536⟩ := by
  decide +kernel

theorem context_12_75887_578115 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75887 ⟨578115, by decide⟩ :=
  accepted_of_selected 12 75887 ⟨578115, by decide⟩ ⟨12, 2, 0, 578115, 75887, 2913, 65536⟩
    (by decide) selected_cut_22754

theorem unmarked_context_11_18971_578116 : frontier 10 ⟨578116, by decide⟩
    (prefixCache 11 18971) (prefixPartial 11 18971) = false := by
  decide +kernel

theorem node_context_11_18971_578116 : EJMOriginalGlobalDAGData.nodes 10 ⟨578116, by decide⟩ =
    .split (coordinate 11) (![⟨578016, by decide⟩,⟨578047, by decide⟩,⟨578082, by decide⟩,⟨578115, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18971_578116 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18971 ⟨578116, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18971
    ⟨578116, by decide⟩ (by decide) (![⟨578016, by decide⟩,⟨578047, by decide⟩,⟨578082, by decide⟩,⟨578115, by decide⟩]) unmarked_context_11_18971_578116 node_context_11_18971_578116
  intro a
  fin_cases a
  · exact context_12_75884_578016
  · exact context_12_75885_578047
  · exact context_12_75886_578082
  · exact context_12_75887_578115

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
