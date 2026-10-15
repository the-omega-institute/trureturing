/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover369
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_35523 : selected 9 ⟨934144, by decide⟩
    (prefixPartial 12 286863) = some ⟨12, 2, 0, 934144, 286863, 1465, 65536⟩ := by
  decide +kernel

theorem context_12_286863_934144 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286863 ⟨934144, by decide⟩ :=
  accepted_of_selected 12 286863 ⟨934144, by decide⟩ ⟨12, 2, 0, 934144, 286863, 1465, 65536⟩
    (by decide) selected_cut_35523

theorem unmarked_context_11_71715_934145 : frontier 10 ⟨934145, by decide⟩
    (prefixCache 11 71715) (prefixPartial 11 71715) = false := by
  decide +kernel

theorem node_context_11_71715_934145 : EJMOriginalGlobalDAGData.nodes 10 ⟨934145, by decide⟩ =
    .split (coordinate 11) (![⟨934071, by decide⟩,⟨934093, by decide⟩,⟨934118, by decide⟩,⟨934144, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71715_934145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71715 ⟨934145, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71715
    ⟨934145, by decide⟩ (by decide) (![⟨934071, by decide⟩,⟨934093, by decide⟩,⟨934118, by decide⟩,⟨934144, by decide⟩]) unmarked_context_11_71715_934145 node_context_11_71715_934145
  intro a
  fin_cases a
  · exact context_12_286860_934071
  · exact context_12_286861_934093
  · exact context_12_286862_934118
  · exact context_12_286863_934144

theorem unmarked_context_10_17928_934146 : frontier 11 ⟨934146, by decide⟩
    (prefixCache 10 17928) (prefixPartial 10 17928) = false := by
  decide +kernel

theorem node_context_10_17928_934146 : EJMOriginalGlobalDAGData.nodes 11 ⟨934146, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨933930, by decide⟩,⟨934055, by decide⟩,⟨934145, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17928_934146 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17928 ⟨934146, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17928
    ⟨934146, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨933930, by decide⟩,⟨934055, by decide⟩,⟨934145, by decide⟩]) unmarked_context_10_17928_934146 node_context_10_17928_934146
  intro a
  fin_cases a
  · exact context_11_71712_907917
  · exact context_11_71713_933930
  · exact context_11_71714_934055
  · exact context_11_71715_934145

theorem selected_cut_35524 : selected 10 ⟨934204, by decide⟩
    (prefixPartial 11 71716) = some ⟨11, 2, 0, 934204, 71716, 2961, 262144⟩ := by
  decide +kernel

theorem context_11_71716_934204 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71716 ⟨934204, by decide⟩ :=
  accepted_of_selected 11 71716 ⟨934204, by decide⟩ ⟨11, 2, 0, 934204, 71716, 2961, 262144⟩
    (by decide) selected_cut_35524

theorem selected_cut_35525 : selected 10 ⟨934265, by decide⟩
    (prefixPartial 11 71717) = some ⟨11, 2, 0, 934265, 71717, 2345, 262144⟩ := by
  decide +kernel

theorem context_11_71717_934265 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71717 ⟨934265, by decide⟩ :=
  accepted_of_selected 11 71717 ⟨934265, by decide⟩ ⟨11, 2, 0, 934265, 71717, 2345, 262144⟩
    (by decide) selected_cut_35525

theorem selected_cut_35526 : selected 10 ⟨934323, by decide⟩
    (prefixPartial 11 71718) = some ⟨11, 2, 0, 934323, 71718, 2989, 262144⟩ := by
  decide +kernel

theorem context_11_71718_934323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71718 ⟨934323, by decide⟩ :=
  accepted_of_selected 11 71718 ⟨934323, by decide⟩ ⟨11, 2, 0, 934323, 71718, 2989, 262144⟩
    (by decide) selected_cut_35526

theorem selected_cut_35527 : selected 10 ⟨934367, by decide⟩
    (prefixPartial 11 71719) = some ⟨11, 2, 0, 934367, 71719, 2593, 262144⟩ := by
  decide +kernel

theorem context_11_71719_934367 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71719 ⟨934367, by decide⟩ :=
  accepted_of_selected 11 71719 ⟨934367, by decide⟩ ⟨11, 2, 0, 934367, 71719, 2593, 262144⟩
    (by decide) selected_cut_35527

theorem unmarked_context_10_17929_934368 : frontier 11 ⟨934368, by decide⟩
    (prefixCache 10 17929) (prefixPartial 10 17929) = false := by
  decide +kernel

theorem node_context_10_17929_934368 : EJMOriginalGlobalDAGData.nodes 11 ⟨934368, by decide⟩ =
    .split (coordinate 10) (![⟨934204, by decide⟩,⟨934265, by decide⟩,⟨934323, by decide⟩,⟨934367, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17929_934368 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17929 ⟨934368, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17929
    ⟨934368, by decide⟩ (by decide) (![⟨934204, by decide⟩,⟨934265, by decide⟩,⟨934323, by decide⟩,⟨934367, by decide⟩]) unmarked_context_10_17929_934368 node_context_10_17929_934368
  intro a
  fin_cases a
  · exact context_11_71716_934204
  · exact context_11_71717_934265
  · exact context_11_71718_934323
  · exact context_11_71719_934367

theorem selected_cut_35528 : selected 10 ⟨934391, by decide⟩
    (prefixPartial 11 71720) = some ⟨11, 2, 0, 934391, 71720, 1561, 262144⟩ := by
  decide +kernel

theorem context_11_71720_934391 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71720 ⟨934391, by decide⟩ :=
  accepted_of_selected 11 71720 ⟨934391, by decide⟩ ⟨11, 2, 0, 934391, 71720, 1561, 262144⟩
    (by decide) selected_cut_35528

theorem selected_cut_35529 : selected 10 ⟨934404, by decide⟩
    (prefixPartial 11 71721) = some ⟨11, 2, 0, 934404, 71721, 845, 262144⟩ := by
  decide +kernel

theorem context_11_71721_934404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71721 ⟨934404, by decide⟩ :=
  accepted_of_selected 11 71721 ⟨934404, by decide⟩ ⟨11, 2, 0, 934404, 71721, 845, 262144⟩
    (by decide) selected_cut_35529

theorem selected_cut_35530 : selected 10 ⟨934422, by decide⟩
    (prefixPartial 11 71722) = some ⟨11, 2, 0, 934422, 71722, 889, 262144⟩ := by
  decide +kernel

theorem context_11_71722_934422 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71722 ⟨934422, by decide⟩ :=
  accepted_of_selected 11 71722 ⟨934422, by decide⟩ ⟨11, 2, 0, 934422, 71722, 889, 262144⟩
    (by decide) selected_cut_35530

theorem selected_cut_35531 : selected 10 ⟨934450, by decide⟩
    (prefixPartial 11 71723) = some ⟨11, 2, 0, 934450, 71723, 1661, 262144⟩ := by
  decide +kernel

theorem context_11_71723_934450 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71723 ⟨934450, by decide⟩ :=
  accepted_of_selected 11 71723 ⟨934450, by decide⟩ ⟨11, 2, 0, 934450, 71723, 1661, 262144⟩
    (by decide) selected_cut_35531

theorem unmarked_context_10_17930_934451 : frontier 11 ⟨934451, by decide⟩
    (prefixCache 10 17930) (prefixPartial 10 17930) = false := by
  decide +kernel

theorem node_context_10_17930_934451 : EJMOriginalGlobalDAGData.nodes 11 ⟨934451, by decide⟩ =
    .split (coordinate 10) (![⟨934391, by decide⟩,⟨934404, by decide⟩,⟨934422, by decide⟩,⟨934450, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17930_934451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17930 ⟨934451, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17930
    ⟨934451, by decide⟩ (by decide) (![⟨934391, by decide⟩,⟨934404, by decide⟩,⟨934422, by decide⟩,⟨934450, by decide⟩]) unmarked_context_10_17930_934451 node_context_10_17930_934451
  intro a
  fin_cases a
  · exact context_11_71720_934391
  · exact context_11_71721_934404
  · exact context_11_71722_934422
  · exact context_11_71723_934450

theorem selected_cut_35532 : selected 11 ⟨934509, by decide⟩
    (prefixPartial 10 17931) = some ⟨10, 2, 0, 934509, 17931, 2465, 1048576⟩ := by
  decide +kernel

theorem context_10_17931_934509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17931 ⟨934509, by decide⟩ :=
  accepted_of_selected 10 17931 ⟨934509, by decide⟩ ⟨10, 2, 0, 934509, 17931, 2465, 1048576⟩
    (by decide) selected_cut_35532

theorem unmarked_context_9_4482_934510 : frontier 12 ⟨934510, by decide⟩
    (prefixCache 9 4482) (prefixPartial 9 4482) = false := by
  decide +kernel

theorem node_context_9_4482_934510 : EJMOriginalGlobalDAGData.nodes 12 ⟨934510, by decide⟩ =
    .split (coordinate 9) (![⟨934146, by decide⟩,⟨934368, by decide⟩,⟨934451, by decide⟩,⟨934509, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4482_934510 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4482 ⟨934510, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4482
    ⟨934510, by decide⟩ (by decide) (![⟨934146, by decide⟩,⟨934368, by decide⟩,⟨934451, by decide⟩,⟨934509, by decide⟩]) unmarked_context_9_4482_934510 node_context_9_4482_934510
  intro a
  fin_cases a
  · exact context_10_17928_934146
  · exact context_10_17929_934368
  · exact context_10_17930_934451
  · exact context_10_17931_934509

theorem selected_cut_35533 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 71728) = some ⟨11, 1, 0, 907917, 71728, 1, 262144⟩ := by
  decide +kernel

theorem context_11_71728_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71728 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 71728 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 71728, 1, 262144⟩
    (by decide) selected_cut_35533

theorem selected_cut_35534 : selected 10 ⟨934536, by decide⟩
    (prefixPartial 11 71729) = some ⟨11, 2, 0, 934536, 71729, 1881, 262144⟩ := by
  decide +kernel

theorem context_11_71729_934536 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71729 ⟨934536, by decide⟩ :=
  accepted_of_selected 11 71729 ⟨934536, by decide⟩ ⟨11, 2, 0, 934536, 71729, 1881, 262144⟩
    (by decide) selected_cut_35534

theorem selected_cut_35535 : selected 10 ⟨934571, by decide⟩
    (prefixPartial 11 71730) = some ⟨11, 2, 0, 934571, 71730, 1905, 262144⟩ := by
  decide +kernel

theorem context_11_71730_934571 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71730 ⟨934571, by decide⟩ :=
  accepted_of_selected 11 71730 ⟨934571, by decide⟩ ⟨11, 2, 0, 934571, 71730, 1905, 262144⟩
    (by decide) selected_cut_35535

theorem selected_cut_35536 : selected 10 ⟨934611, by decide⟩
    (prefixPartial 11 71731) = some ⟨11, 2, 0, 934611, 71731, 1749, 262144⟩ := by
  decide +kernel

theorem context_11_71731_934611 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71731 ⟨934611, by decide⟩ :=
  accepted_of_selected 11 71731 ⟨934611, by decide⟩ ⟨11, 2, 0, 934611, 71731, 1749, 262144⟩
    (by decide) selected_cut_35536

theorem unmarked_context_10_17932_934612 : frontier 11 ⟨934612, by decide⟩
    (prefixCache 10 17932) (prefixPartial 10 17932) = false := by
  decide +kernel

theorem node_context_10_17932_934612 : EJMOriginalGlobalDAGData.nodes 11 ⟨934612, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨934536, by decide⟩,⟨934571, by decide⟩,⟨934611, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17932_934612 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17932 ⟨934612, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17932
    ⟨934612, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨934536, by decide⟩,⟨934571, by decide⟩,⟨934611, by decide⟩]) unmarked_context_10_17932_934612 node_context_10_17932_934612
  intro a
  fin_cases a
  · exact context_11_71728_907917
  · exact context_11_71729_934536
  · exact context_11_71730_934571
  · exact context_11_71731_934611

theorem selected_cut_35537 : selected 11 ⟨934681, by decide⟩
    (prefixPartial 10 17933) = some ⟨10, 2, 0, 934681, 17933, 2829, 1048576⟩ := by
  decide +kernel

theorem context_10_17933_934681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17933 ⟨934681, by decide⟩ :=
  accepted_of_selected 10 17933 ⟨934681, by decide⟩ ⟨10, 2, 0, 934681, 17933, 2829, 1048576⟩
    (by decide) selected_cut_35537

theorem selected_cut_35538 : selected 11 ⟨934718, by decide⟩
    (prefixPartial 10 17934) = some ⟨10, 2, 0, 934718, 17934, 917, 1048576⟩ := by
  decide +kernel

theorem context_10_17934_934718 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17934 ⟨934718, by decide⟩ :=
  accepted_of_selected 10 17934 ⟨934718, by decide⟩ ⟨10, 2, 0, 934718, 17934, 917, 1048576⟩
    (by decide) selected_cut_35538

theorem selected_cut_35539 : selected 11 ⟨934727, by decide⟩
    (prefixPartial 10 17935) = some ⟨10, 2, 0, 934727, 17935, 97, 1048576⟩ := by
  decide +kernel

theorem context_10_17935_934727 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17935 ⟨934727, by decide⟩ :=
  accepted_of_selected 10 17935 ⟨934727, by decide⟩ ⟨10, 2, 0, 934727, 17935, 97, 1048576⟩
    (by decide) selected_cut_35539

theorem unmarked_context_9_4483_934728 : frontier 12 ⟨934728, by decide⟩
    (prefixCache 9 4483) (prefixPartial 9 4483) = false := by
  decide +kernel

theorem node_context_9_4483_934728 : EJMOriginalGlobalDAGData.nodes 12 ⟨934728, by decide⟩ =
    .split (coordinate 9) (![⟨934612, by decide⟩,⟨934681, by decide⟩,⟨934718, by decide⟩,⟨934727, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4483_934728 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4483 ⟨934728, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4483
    ⟨934728, by decide⟩ (by decide) (![⟨934612, by decide⟩,⟨934681, by decide⟩,⟨934718, by decide⟩,⟨934727, by decide⟩]) unmarked_context_9_4483_934728 node_context_9_4483_934728
  intro a
  fin_cases a
  · exact context_10_17932_934612
  · exact context_10_17933_934681
  · exact context_10_17934_934718
  · exact context_10_17935_934727

theorem unmarked_context_8_1120_934729 : frontier 13 ⟨934729, by decide⟩
    (prefixCache 8 1120) (prefixPartial 8 1120) = false := by
  decide +kernel

theorem node_context_8_1120_934729 : EJMOriginalGlobalDAGData.nodes 13 ⟨934729, by decide⟩ =
    .split (coordinate 8) (![⟨933130, by decide⟩,⟨933839, by decide⟩,⟨934510, by decide⟩,⟨934728, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1120_934729 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1120 ⟨934729, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1120
    ⟨934729, by decide⟩ (by decide) (![⟨933130, by decide⟩,⟨933839, by decide⟩,⟨934510, by decide⟩,⟨934728, by decide⟩]) unmarked_context_8_1120_934729 node_context_8_1120_934729
  intro a
  fin_cases a
  · exact context_9_4480_933130
  · exact context_9_4481_933839
  · exact context_9_4482_934510
  · exact context_9_4483_934728

theorem selected_cut_35540 : selected 10 ⟨167448, by decide⟩
    (prefixPartial 11 71744) = some ⟨11, 1, 0, 167448, 71744, 1, 262144⟩ := by
  decide +kernel

theorem context_11_71744_167448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71744 ⟨167448, by decide⟩ :=
  accepted_of_selected 11 71744 ⟨167448, by decide⟩ ⟨11, 1, 0, 167448, 71744, 1, 262144⟩
    (by decide) selected_cut_35540

theorem selected_cut_35541 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 286980) = some ⟨12, 1, 0, 34034, 286980, 1, 65536⟩ := by
  decide +kernel

theorem context_12_286980_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286980 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 286980 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 286980, 1, 65536⟩
    (by decide) selected_cut_35541

theorem selected_cut_35542 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 286981) = some ⟨12, 1, 0, 891951, 286981, 1, 65536⟩ := by
  decide +kernel

theorem context_12_286981_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286981 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 286981 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 286981, 1, 65536⟩
    (by decide) selected_cut_35542

theorem selected_cut_35543 : selected 9 ⟨934783, by decide⟩
    (prefixPartial 12 286982) = some ⟨12, 2, 0, 934783, 286982, 3201, 65536⟩ := by
  decide +kernel

theorem context_12_286982_934783 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286982 ⟨934783, by decide⟩ :=
  accepted_of_selected 12 286982 ⟨934783, by decide⟩ ⟨12, 2, 0, 934783, 286982, 3201, 65536⟩
    (by decide) selected_cut_35543

theorem selected_cut_35544 : selected 9 ⟨934843, by decide⟩
    (prefixPartial 12 286983) = some ⟨12, 2, 0, 934843, 286983, 3625, 65536⟩ := by
  decide +kernel

theorem context_12_286983_934843 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286983 ⟨934843, by decide⟩ :=
  accepted_of_selected 12 286983 ⟨934843, by decide⟩ ⟨12, 2, 0, 934843, 286983, 3625, 65536⟩
    (by decide) selected_cut_35544

theorem unmarked_context_11_71745_934844 : frontier 10 ⟨934844, by decide⟩
    (prefixCache 11 71745) (prefixPartial 11 71745) = false := by
  decide +kernel

theorem node_context_11_71745_934844 : EJMOriginalGlobalDAGData.nodes 10 ⟨934844, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨891951, by decide⟩,⟨934783, by decide⟩,⟨934843, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71745_934844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71745 ⟨934844, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71745
    ⟨934844, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨891951, by decide⟩,⟨934783, by decide⟩,⟨934843, by decide⟩]) unmarked_context_11_71745_934844 node_context_11_71745_934844
  intro a
  fin_cases a
  · exact context_12_286980_34034
  · exact context_12_286981_891951
  · exact context_12_286982_934783
  · exact context_12_286983_934843

theorem selected_cut_35545 : selected 8 ⟨934893, by decide⟩
    (prefixPartial 13 1147936) = some ⟨13, 2, 0, 934893, 1147936, 1881, 16384⟩ := by
  decide +kernel

theorem context_13_1147936_934893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1147936 ⟨934893, by decide⟩ :=
  accepted_of_selected 13 1147936 ⟨934893, by decide⟩ ⟨13, 2, 0, 934893, 1147936, 1881, 16384⟩
    (by decide) selected_cut_35545

theorem selected_cut_35546 : selected 8 ⟨934932, by decide⟩
    (prefixPartial 13 1147937) = some ⟨13, 2, 0, 934932, 1147937, 1465, 16384⟩ := by
  decide +kernel

theorem context_13_1147937_934932 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1147937 ⟨934932, by decide⟩ :=
  accepted_of_selected 13 1147937 ⟨934932, by decide⟩ ⟨13, 2, 0, 934932, 1147937, 1465, 16384⟩
    (by decide) selected_cut_35546

theorem selected_cut_35547 : selected 8 ⟨934963, by decide⟩
    (prefixPartial 13 1147938) = some ⟨13, 2, 0, 934963, 1147938, 1161, 16384⟩ := by
  decide +kernel

theorem context_13_1147938_934963 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1147938 ⟨934963, by decide⟩ :=
  accepted_of_selected 13 1147938 ⟨934963, by decide⟩ ⟨13, 2, 0, 934963, 1147938, 1161, 16384⟩
    (by decide) selected_cut_35547

theorem selected_cut_35548 : selected 8 ⟨934971, by decide⟩
    (prefixPartial 13 1147939) = some ⟨13, 2, 0, 934971, 1147939, 677, 16384⟩ := by
  decide +kernel

theorem context_13_1147939_934971 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1147939 ⟨934971, by decide⟩ :=
  accepted_of_selected 13 1147939 ⟨934971, by decide⟩ ⟨13, 2, 0, 934971, 1147939, 677, 16384⟩
    (by decide) selected_cut_35548

theorem unmarked_context_12_286984_934972 : frontier 9 ⟨934972, by decide⟩
    (prefixCache 12 286984) (prefixPartial 12 286984) = false := by
  decide +kernel

theorem node_context_12_286984_934972 : EJMOriginalGlobalDAGData.nodes 9 ⟨934972, by decide⟩ =
    .split (coordinate 12) (![⟨934893, by decide⟩,⟨934932, by decide⟩,⟨934963, by decide⟩,⟨934971, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_286984_934972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286984 ⟨934972, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 286984
    ⟨934972, by decide⟩ (by decide) (![⟨934893, by decide⟩,⟨934932, by decide⟩,⟨934963, by decide⟩,⟨934971, by decide⟩]) unmarked_context_12_286984_934972 node_context_12_286984_934972
  intro a
  fin_cases a
  · exact context_13_1147936_934893
  · exact context_13_1147937_934932
  · exact context_13_1147938_934963
  · exact context_13_1147939_934971

theorem selected_cut_35549 : selected 9 ⟨935041, by decide⟩
    (prefixPartial 12 286985) = some ⟨12, 2, 0, 935041, 286985, 3589, 65536⟩ := by
  decide +kernel

theorem context_12_286985_935041 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286985 ⟨935041, by decide⟩ :=
  accepted_of_selected 12 286985 ⟨935041, by decide⟩ ⟨12, 2, 0, 935041, 286985, 3589, 65536⟩
    (by decide) selected_cut_35549

theorem selected_cut_35550 : selected 9 ⟨935107, by decide⟩
    (prefixPartial 12 286986) = some ⟨12, 2, 0, 935107, 286986, 3697, 65536⟩ := by
  decide +kernel

theorem context_12_286986_935107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286986 ⟨935107, by decide⟩ :=
  accepted_of_selected 12 286986 ⟨935107, by decide⟩ ⟨12, 2, 0, 935107, 286986, 3697, 65536⟩
    (by decide) selected_cut_35550

theorem selected_cut_35551 : selected 8 ⟨935145, by decide⟩
    (prefixPartial 13 1147948) = some ⟨13, 2, 0, 935145, 1147948, 1801, 16384⟩ := by
  decide +kernel

theorem context_13_1147948_935145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1147948 ⟨935145, by decide⟩ :=
  accepted_of_selected 13 1147948 ⟨935145, by decide⟩ ⟨13, 2, 0, 935145, 1147948, 1801, 16384⟩
    (by decide) selected_cut_35551

theorem selected_cut_35552 : selected 8 ⟨935169, by decide⟩
    (prefixPartial 13 1147949) = some ⟨13, 2, 0, 935169, 1147949, 1085, 16384⟩ := by
  decide +kernel

theorem context_13_1147949_935169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1147949 ⟨935169, by decide⟩ :=
  accepted_of_selected 13 1147949 ⟨935169, by decide⟩ ⟨13, 2, 0, 935169, 1147949, 1085, 16384⟩
    (by decide) selected_cut_35552

theorem selected_cut_35553 : selected 8 ⟨935183, by decide⟩
    (prefixPartial 13 1147950) = some ⟨13, 2, 0, 935183, 1147950, 933, 16384⟩ := by
  decide +kernel

theorem context_13_1147950_935183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1147950 ⟨935183, by decide⟩ :=
  accepted_of_selected 13 1147950 ⟨935183, by decide⟩ ⟨13, 2, 0, 935183, 1147950, 933, 16384⟩
    (by decide) selected_cut_35553

theorem selected_cut_35554 : selected 8 ⟨935188, by decide⟩
    (prefixPartial 13 1147951) = some ⟨13, 2, 0, 935188, 1147951, 573, 16384⟩ := by
  decide +kernel

theorem context_13_1147951_935188 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1147951 ⟨935188, by decide⟩ :=
  accepted_of_selected 13 1147951 ⟨935188, by decide⟩ ⟨13, 2, 0, 935188, 1147951, 573, 16384⟩
    (by decide) selected_cut_35554

theorem unmarked_context_12_286987_935189 : frontier 9 ⟨935189, by decide⟩
    (prefixCache 12 286987) (prefixPartial 12 286987) = false := by
  decide +kernel

theorem node_context_12_286987_935189 : EJMOriginalGlobalDAGData.nodes 9 ⟨935189, by decide⟩ =
    .split (coordinate 12) (![⟨935145, by decide⟩,⟨935169, by decide⟩,⟨935183, by decide⟩,⟨935188, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_286987_935189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286987 ⟨935189, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 286987
    ⟨935189, by decide⟩ (by decide) (![⟨935145, by decide⟩,⟨935169, by decide⟩,⟨935183, by decide⟩,⟨935188, by decide⟩]) unmarked_context_12_286987_935189 node_context_12_286987_935189
  intro a
  fin_cases a
  · exact context_13_1147948_935145
  · exact context_13_1147949_935169
  · exact context_13_1147950_935183
  · exact context_13_1147951_935188

theorem unmarked_context_11_71746_935190 : frontier 10 ⟨935190, by decide⟩
    (prefixCache 11 71746) (prefixPartial 11 71746) = false := by
  decide +kernel

theorem node_context_11_71746_935190 : EJMOriginalGlobalDAGData.nodes 10 ⟨935190, by decide⟩ =
    .split (coordinate 11) (![⟨934972, by decide⟩,⟨935041, by decide⟩,⟨935107, by decide⟩,⟨935189, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71746_935190 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71746 ⟨935190, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71746
    ⟨935190, by decide⟩ (by decide) (![⟨934972, by decide⟩,⟨935041, by decide⟩,⟨935107, by decide⟩,⟨935189, by decide⟩]) unmarked_context_11_71746_935190 node_context_11_71746_935190
  intro a
  fin_cases a
  · exact context_12_286984_934972
  · exact context_12_286985_935041
  · exact context_12_286986_935107
  · exact context_12_286987_935189

theorem selected_cut_35555 : selected 9 ⟨935258, by decide⟩
    (prefixPartial 12 286988) = some ⟨12, 2, 0, 935258, 286988, 2181, 65536⟩ := by
  decide +kernel

theorem context_12_286988_935258 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286988 ⟨935258, by decide⟩ :=
  accepted_of_selected 12 286988 ⟨935258, by decide⟩ ⟨12, 2, 0, 935258, 286988, 2181, 65536⟩
    (by decide) selected_cut_35555

theorem selected_cut_35556 : selected 9 ⟨935311, by decide⟩
    (prefixPartial 12 286989) = some ⟨12, 2, 0, 935311, 286989, 3129, 65536⟩ := by
  decide +kernel

theorem context_12_286989_935311 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286989 ⟨935311, by decide⟩ :=
  accepted_of_selected 12 286989 ⟨935311, by decide⟩ ⟨12, 2, 0, 935311, 286989, 3129, 65536⟩
    (by decide) selected_cut_35556

theorem selected_cut_35557 : selected 9 ⟨935366, by decide⟩
    (prefixPartial 12 286990) = some ⟨12, 2, 0, 935366, 286990, 3433, 65536⟩ := by
  decide +kernel

theorem context_12_286990_935366 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286990 ⟨935366, by decide⟩ :=
  accepted_of_selected 12 286990 ⟨935366, by decide⟩ ⟨12, 2, 0, 935366, 286990, 3433, 65536⟩
    (by decide) selected_cut_35557

theorem selected_cut_35558 : selected 9 ⟨935435, by decide⟩
    (prefixPartial 12 286991) = some ⟨12, 2, 0, 935435, 286991, 3705, 65536⟩ := by
  decide +kernel

theorem context_12_286991_935435 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286991 ⟨935435, by decide⟩ :=
  accepted_of_selected 12 286991 ⟨935435, by decide⟩ ⟨12, 2, 0, 935435, 286991, 3705, 65536⟩
    (by decide) selected_cut_35558

theorem unmarked_context_11_71747_935436 : frontier 10 ⟨935436, by decide⟩
    (prefixCache 11 71747) (prefixPartial 11 71747) = false := by
  decide +kernel

theorem node_context_11_71747_935436 : EJMOriginalGlobalDAGData.nodes 10 ⟨935436, by decide⟩ =
    .split (coordinate 11) (![⟨935258, by decide⟩,⟨935311, by decide⟩,⟨935366, by decide⟩,⟨935435, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71747_935436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71747 ⟨935436, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71747
    ⟨935436, by decide⟩ (by decide) (![⟨935258, by decide⟩,⟨935311, by decide⟩,⟨935366, by decide⟩,⟨935435, by decide⟩]) unmarked_context_11_71747_935436 node_context_11_71747_935436
  intro a
  fin_cases a
  · exact context_12_286988_935258
  · exact context_12_286989_935311
  · exact context_12_286990_935366
  · exact context_12_286991_935435

theorem unmarked_context_10_17936_935437 : frontier 11 ⟨935437, by decide⟩
    (prefixCache 10 17936) (prefixPartial 10 17936) = false := by
  decide +kernel

theorem node_context_10_17936_935437 : EJMOriginalGlobalDAGData.nodes 11 ⟨935437, by decide⟩ =
    .split (coordinate 10) (![⟨167448, by decide⟩,⟨934844, by decide⟩,⟨935190, by decide⟩,⟨935436, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17936_935437 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17936 ⟨935437, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17936
    ⟨935437, by decide⟩ (by decide) (![⟨167448, by decide⟩,⟨934844, by decide⟩,⟨935190, by decide⟩,⟨935436, by decide⟩]) unmarked_context_10_17936_935437 node_context_10_17936_935437
  intro a
  fin_cases a
  · exact context_11_71744_167448
  · exact context_11_71745_934844
  · exact context_11_71746_935190
  · exact context_11_71747_935436

theorem selected_cut_35559 : selected 9 ⟨935438, by decide⟩
    (prefixPartial 12 286992) = some ⟨12, 1, 0, 935438, 286992, 1, 65536⟩ := by
  decide +kernel

theorem context_12_286992_935438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286992 ⟨935438, by decide⟩ :=
  accepted_of_selected 12 286992 ⟨935438, by decide⟩ ⟨12, 1, 0, 935438, 286992, 1, 65536⟩
    (by decide) selected_cut_35559

theorem selected_cut_35560 : selected 9 ⟨935480, by decide⟩
    (prefixPartial 12 286993) = some ⟨12, 2, 0, 935480, 286993, 2457, 65536⟩ := by
  decide +kernel

theorem context_12_286993_935480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286993 ⟨935480, by decide⟩ :=
  accepted_of_selected 12 286993 ⟨935480, by decide⟩ ⟨12, 2, 0, 935480, 286993, 2457, 65536⟩
    (by decide) selected_cut_35560

theorem selected_cut_35561 : selected 9 ⟨935512, by decide⟩
    (prefixPartial 12 286994) = some ⟨12, 2, 0, 935512, 286994, 2649, 65536⟩ := by
  decide +kernel

theorem context_12_286994_935512 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286994 ⟨935512, by decide⟩ :=
  accepted_of_selected 12 286994 ⟨935512, by decide⟩ ⟨12, 2, 0, 935512, 286994, 2649, 65536⟩
    (by decide) selected_cut_35561

theorem selected_cut_35562 : selected 9 ⟨935550, by decide⟩
    (prefixPartial 12 286995) = some ⟨12, 2, 0, 935550, 286995, 2945, 65536⟩ := by
  decide +kernel

theorem context_12_286995_935550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286995 ⟨935550, by decide⟩ :=
  accepted_of_selected 12 286995 ⟨935550, by decide⟩ ⟨12, 2, 0, 935550, 286995, 2945, 65536⟩
    (by decide) selected_cut_35562

theorem unmarked_context_11_71748_935551 : frontier 10 ⟨935551, by decide⟩
    (prefixCache 11 71748) (prefixPartial 11 71748) = false := by
  decide +kernel

theorem node_context_11_71748_935551 : EJMOriginalGlobalDAGData.nodes 10 ⟨935551, by decide⟩ =
    .split (coordinate 11) (![⟨935438, by decide⟩,⟨935480, by decide⟩,⟨935512, by decide⟩,⟨935550, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71748_935551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71748 ⟨935551, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71748
    ⟨935551, by decide⟩ (by decide) (![⟨935438, by decide⟩,⟨935480, by decide⟩,⟨935512, by decide⟩,⟨935550, by decide⟩]) unmarked_context_11_71748_935551 node_context_11_71748_935551
  intro a
  fin_cases a
  · exact context_12_286992_935438
  · exact context_12_286993_935480
  · exact context_12_286994_935512
  · exact context_12_286995_935550

theorem selected_cut_35563 : selected 9 ⟨935598, by decide⟩
    (prefixPartial 12 286996) = some ⟨12, 2, 0, 935598, 286996, 3097, 65536⟩ := by
  decide +kernel

theorem context_12_286996_935598 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286996 ⟨935598, by decide⟩ :=
  accepted_of_selected 12 286996 ⟨935598, by decide⟩ ⟨12, 2, 0, 935598, 286996, 3097, 65536⟩
    (by decide) selected_cut_35563

theorem selected_cut_35564 : selected 9 ⟨124308, by decide⟩
    (prefixPartial 12 286997) = some ⟨12, 1, 0, 124308, 286997, 1, 65536⟩ := by
  decide +kernel

theorem context_12_286997_124308 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286997 ⟨124308, by decide⟩ :=
  accepted_of_selected 12 286997 ⟨124308, by decide⟩ ⟨12, 1, 0, 124308, 286997, 1, 65536⟩
    (by decide) selected_cut_35564

theorem selected_cut_35565 : selected 9 ⟨935638, by decide⟩
    (prefixPartial 12 286998) = some ⟨12, 2, 0, 935638, 286998, 2729, 65536⟩ := by
  decide +kernel

theorem context_12_286998_935638 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286998 ⟨935638, by decide⟩ :=
  accepted_of_selected 12 286998 ⟨935638, by decide⟩ ⟨12, 2, 0, 935638, 286998, 2729, 65536⟩
    (by decide) selected_cut_35565

theorem selected_cut_35566 : selected 9 ⟨935682, by decide⟩
    (prefixPartial 12 286999) = some ⟨12, 2, 0, 935682, 286999, 2961, 65536⟩ := by
  decide +kernel

theorem context_12_286999_935682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 286999 ⟨935682, by decide⟩ :=
  accepted_of_selected 12 286999 ⟨935682, by decide⟩ ⟨12, 2, 0, 935682, 286999, 2961, 65536⟩
    (by decide) selected_cut_35566

theorem unmarked_context_11_71749_935683 : frontier 10 ⟨935683, by decide⟩
    (prefixCache 11 71749) (prefixPartial 11 71749) = false := by
  decide +kernel

theorem node_context_11_71749_935683 : EJMOriginalGlobalDAGData.nodes 10 ⟨935683, by decide⟩ =
    .split (coordinate 11) (![⟨935598, by decide⟩,⟨124308, by decide⟩,⟨935638, by decide⟩,⟨935682, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71749_935683 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71749 ⟨935683, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71749
    ⟨935683, by decide⟩ (by decide) (![⟨935598, by decide⟩,⟨124308, by decide⟩,⟨935638, by decide⟩,⟨935682, by decide⟩]) unmarked_context_11_71749_935683 node_context_11_71749_935683
  intro a
  fin_cases a
  · exact context_12_286996_935598
  · exact context_12_286997_124308
  · exact context_12_286998_935638
  · exact context_12_286999_935682

theorem selected_cut_35567 : selected 9 ⟨935759, by decide⟩
    (prefixPartial 12 287000) = some ⟨12, 2, 0, 935759, 287000, 3777, 65536⟩ := by
  decide +kernel

theorem context_12_287000_935759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287000 ⟨935759, by decide⟩ :=
  accepted_of_selected 12 287000 ⟨935759, by decide⟩ ⟨12, 2, 0, 935759, 287000, 3777, 65536⟩
    (by decide) selected_cut_35567

theorem selected_cut_35568 : selected 9 ⟨935802, by decide⟩
    (prefixPartial 12 287001) = some ⟨12, 2, 0, 935802, 287001, 2893, 65536⟩ := by
  decide +kernel

theorem context_12_287001_935802 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287001 ⟨935802, by decide⟩ :=
  accepted_of_selected 12 287001 ⟨935802, by decide⟩ ⟨12, 2, 0, 935802, 287001, 2893, 65536⟩
    (by decide) selected_cut_35568

theorem selected_cut_35569 : selected 9 ⟨935846, by decide⟩
    (prefixPartial 12 287002) = some ⟨12, 2, 0, 935846, 287002, 3041, 65536⟩ := by
  decide +kernel

theorem context_12_287002_935846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287002 ⟨935846, by decide⟩ :=
  accepted_of_selected 12 287002 ⟨935846, by decide⟩ ⟨12, 2, 0, 935846, 287002, 3041, 65536⟩
    (by decide) selected_cut_35569

theorem selected_cut_35570 : selected 9 ⟨935904, by decide⟩
    (prefixPartial 12 287003) = some ⟨12, 2, 0, 935904, 287003, 3573, 65536⟩ := by
  decide +kernel

theorem context_12_287003_935904 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287003 ⟨935904, by decide⟩ :=
  accepted_of_selected 12 287003 ⟨935904, by decide⟩ ⟨12, 2, 0, 935904, 287003, 3573, 65536⟩
    (by decide) selected_cut_35570

theorem unmarked_context_11_71750_935905 : frontier 10 ⟨935905, by decide⟩
    (prefixCache 11 71750) (prefixPartial 11 71750) = false := by
  decide +kernel

theorem node_context_11_71750_935905 : EJMOriginalGlobalDAGData.nodes 10 ⟨935905, by decide⟩ =
    .split (coordinate 11) (![⟨935759, by decide⟩,⟨935802, by decide⟩,⟨935846, by decide⟩,⟨935904, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71750_935905 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71750 ⟨935905, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71750
    ⟨935905, by decide⟩ (by decide) (![⟨935759, by decide⟩,⟨935802, by decide⟩,⟨935846, by decide⟩,⟨935904, by decide⟩]) unmarked_context_11_71750_935905 node_context_11_71750_935905
  intro a
  fin_cases a
  · exact context_12_287000_935759
  · exact context_12_287001_935802
  · exact context_12_287002_935846
  · exact context_12_287003_935904

theorem selected_cut_35571 : selected 9 ⟨935962, by decide⟩
    (prefixPartial 12 287004) = some ⟨12, 2, 0, 935962, 287004, 3385, 65536⟩ := by
  decide +kernel

theorem context_12_287004_935962 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287004 ⟨935962, by decide⟩ :=
  accepted_of_selected 12 287004 ⟨935962, by decide⟩ ⟨12, 2, 0, 935962, 287004, 3385, 65536⟩
    (by decide) selected_cut_35571

theorem selected_cut_35572 : selected 9 ⟨936010, by decide⟩
    (prefixPartial 12 287005) = some ⟨12, 2, 0, 936010, 287005, 2793, 65536⟩ := by
  decide +kernel

theorem context_12_287005_936010 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287005 ⟨936010, by decide⟩ :=
  accepted_of_selected 12 287005 ⟨936010, by decide⟩ ⟨12, 2, 0, 936010, 287005, 2793, 65536⟩
    (by decide) selected_cut_35572

theorem selected_cut_35573 : selected 9 ⟨936056, by decide⟩
    (prefixPartial 12 287006) = some ⟨12, 2, 0, 936056, 287006, 3057, 65536⟩ := by
  decide +kernel

theorem context_12_287006_936056 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287006 ⟨936056, by decide⟩ :=
  accepted_of_selected 12 287006 ⟨936056, by decide⟩ ⟨12, 2, 0, 936056, 287006, 3057, 65536⟩
    (by decide) selected_cut_35573

theorem selected_cut_35574 : selected 9 ⟨936108, by decide⟩
    (prefixPartial 12 287007) = some ⟨12, 2, 0, 936108, 287007, 3201, 65536⟩ := by
  decide +kernel

theorem context_12_287007_936108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287007 ⟨936108, by decide⟩ :=
  accepted_of_selected 12 287007 ⟨936108, by decide⟩ ⟨12, 2, 0, 936108, 287007, 3201, 65536⟩
    (by decide) selected_cut_35574

theorem unmarked_context_11_71751_936109 : frontier 10 ⟨936109, by decide⟩
    (prefixCache 11 71751) (prefixPartial 11 71751) = false := by
  decide +kernel

theorem node_context_11_71751_936109 : EJMOriginalGlobalDAGData.nodes 10 ⟨936109, by decide⟩ =
    .split (coordinate 11) (![⟨935962, by decide⟩,⟨936010, by decide⟩,⟨936056, by decide⟩,⟨936108, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71751_936109 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71751 ⟨936109, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71751
    ⟨936109, by decide⟩ (by decide) (![⟨935962, by decide⟩,⟨936010, by decide⟩,⟨936056, by decide⟩,⟨936108, by decide⟩]) unmarked_context_11_71751_936109 node_context_11_71751_936109
  intro a
  fin_cases a
  · exact context_12_287004_935962
  · exact context_12_287005_936010
  · exact context_12_287006_936056
  · exact context_12_287007_936108

theorem unmarked_context_10_17937_936110 : frontier 11 ⟨936110, by decide⟩
    (prefixCache 10 17937) (prefixPartial 10 17937) = false := by
  decide +kernel

theorem node_context_10_17937_936110 : EJMOriginalGlobalDAGData.nodes 11 ⟨936110, by decide⟩ =
    .split (coordinate 10) (![⟨935551, by decide⟩,⟨935683, by decide⟩,⟨935905, by decide⟩,⟨936109, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17937_936110 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17937 ⟨936110, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17937
    ⟨936110, by decide⟩ (by decide) (![⟨935551, by decide⟩,⟨935683, by decide⟩,⟨935905, by decide⟩,⟨936109, by decide⟩]) unmarked_context_10_17937_936110 node_context_10_17937_936110
  intro a
  fin_cases a
  · exact context_11_71748_935551
  · exact context_11_71749_935683
  · exact context_11_71750_935905
  · exact context_11_71751_936109

theorem selected_cut_35575 : selected 9 ⟨936181, by decide⟩
    (prefixPartial 12 287008) = some ⟨12, 2, 0, 936181, 287008, 1977, 65536⟩ := by
  decide +kernel

theorem context_12_287008_936181 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287008 ⟨936181, by decide⟩ :=
  accepted_of_selected 12 287008 ⟨936181, by decide⟩ ⟨12, 2, 0, 936181, 287008, 1977, 65536⟩
    (by decide) selected_cut_35575

theorem selected_cut_35576 : selected 9 ⟨936231, by decide⟩
    (prefixPartial 12 287009) = some ⟨12, 2, 0, 936231, 287009, 2749, 65536⟩ := by
  decide +kernel

theorem context_12_287009_936231 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287009 ⟨936231, by decide⟩ :=
  accepted_of_selected 12 287009 ⟨936231, by decide⟩ ⟨12, 2, 0, 936231, 287009, 2749, 65536⟩
    (by decide) selected_cut_35576

theorem selected_cut_35577 : selected 9 ⟨936281, by decide⟩
    (prefixPartial 12 287010) = some ⟨12, 2, 0, 936281, 287010, 2845, 65536⟩ := by
  decide +kernel

theorem context_12_287010_936281 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287010 ⟨936281, by decide⟩ :=
  accepted_of_selected 12 287010 ⟨936281, by decide⟩ ⟨12, 2, 0, 936281, 287010, 2845, 65536⟩
    (by decide) selected_cut_35577

theorem selected_cut_35578 : selected 9 ⟨936329, by decide⟩
    (prefixPartial 12 287011) = some ⟨12, 2, 0, 936329, 287011, 3017, 65536⟩ := by
  decide +kernel

theorem context_12_287011_936329 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287011 ⟨936329, by decide⟩ :=
  accepted_of_selected 12 287011 ⟨936329, by decide⟩ ⟨12, 2, 0, 936329, 287011, 3017, 65536⟩
    (by decide) selected_cut_35578

theorem unmarked_context_11_71752_936330 : frontier 10 ⟨936330, by decide⟩
    (prefixCache 11 71752) (prefixPartial 11 71752) = false := by
  decide +kernel

theorem node_context_11_71752_936330 : EJMOriginalGlobalDAGData.nodes 10 ⟨936330, by decide⟩ =
    .split (coordinate 11) (![⟨936181, by decide⟩,⟨936231, by decide⟩,⟨936281, by decide⟩,⟨936329, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71752_936330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71752 ⟨936330, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71752
    ⟨936330, by decide⟩ (by decide) (![⟨936181, by decide⟩,⟨936231, by decide⟩,⟨936281, by decide⟩,⟨936329, by decide⟩]) unmarked_context_11_71752_936330 node_context_11_71752_936330
  intro a
  fin_cases a
  · exact context_12_287008_936181
  · exact context_12_287009_936231
  · exact context_12_287010_936281
  · exact context_12_287011_936329

theorem selected_cut_35579 : selected 9 ⟨936395, by decide⟩
    (prefixPartial 12 287012) = some ⟨12, 2, 0, 936395, 287012, 3397, 65536⟩ := by
  decide +kernel

theorem context_12_287012_936395 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287012 ⟨936395, by decide⟩ :=
  accepted_of_selected 12 287012 ⟨936395, by decide⟩ ⟨12, 2, 0, 936395, 287012, 3397, 65536⟩
    (by decide) selected_cut_35579

theorem selected_cut_35580 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 287013) = some ⟨12, 1, 0, 891951, 287013, 1, 65536⟩ := by
  decide +kernel

theorem context_12_287013_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287013 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 287013 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 287013, 1, 65536⟩
    (by decide) selected_cut_35580

theorem selected_cut_35581 : selected 9 ⟨936439, by decide⟩
    (prefixPartial 12 287014) = some ⟨12, 2, 0, 936439, 287014, 2965, 65536⟩ := by
  decide +kernel

theorem context_12_287014_936439 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287014 ⟨936439, by decide⟩ :=
  accepted_of_selected 12 287014 ⟨936439, by decide⟩ ⟨12, 2, 0, 936439, 287014, 2965, 65536⟩
    (by decide) selected_cut_35581

theorem selected_cut_35582 : selected 9 ⟨936484, by decide⟩
    (prefixPartial 12 287015) = some ⟨12, 2, 0, 936484, 287015, 3113, 65536⟩ := by
  decide +kernel

theorem context_12_287015_936484 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287015 ⟨936484, by decide⟩ :=
  accepted_of_selected 12 287015 ⟨936484, by decide⟩ ⟨12, 2, 0, 936484, 287015, 3113, 65536⟩
    (by decide) selected_cut_35582

theorem unmarked_context_11_71753_936485 : frontier 10 ⟨936485, by decide⟩
    (prefixCache 11 71753) (prefixPartial 11 71753) = false := by
  decide +kernel

theorem node_context_11_71753_936485 : EJMOriginalGlobalDAGData.nodes 10 ⟨936485, by decide⟩ =
    .split (coordinate 11) (![⟨936395, by decide⟩,⟨891951, by decide⟩,⟨936439, by decide⟩,⟨936484, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71753_936485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71753 ⟨936485, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71753
    ⟨936485, by decide⟩ (by decide) (![⟨936395, by decide⟩,⟨891951, by decide⟩,⟨936439, by decide⟩,⟨936484, by decide⟩]) unmarked_context_11_71753_936485 node_context_11_71753_936485
  intro a
  fin_cases a
  · exact context_12_287012_936395
  · exact context_12_287013_891951
  · exact context_12_287014_936439
  · exact context_12_287015_936484

theorem selected_cut_35583 : selected 9 ⟨936566, by decide⟩
    (prefixPartial 12 287016) = some ⟨12, 2, 0, 936566, 287016, 3929, 65536⟩ := by
  decide +kernel

theorem context_12_287016_936566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287016 ⟨936566, by decide⟩ :=
  accepted_of_selected 12 287016 ⟨936566, by decide⟩ ⟨12, 2, 0, 936566, 287016, 3929, 65536⟩
    (by decide) selected_cut_35583

theorem selected_cut_35584 : selected 9 ⟨936612, by decide⟩
    (prefixPartial 12 287017) = some ⟨12, 2, 0, 936612, 287017, 3009, 65536⟩ := by
  decide +kernel

theorem context_12_287017_936612 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287017 ⟨936612, by decide⟩ :=
  accepted_of_selected 12 287017 ⟨936612, by decide⟩ ⟨12, 2, 0, 936612, 287017, 3009, 65536⟩
    (by decide) selected_cut_35584

theorem selected_cut_35585 : selected 9 ⟨936666, by decide⟩
    (prefixPartial 12 287018) = some ⟨12, 2, 0, 936666, 287018, 3173, 65536⟩ := by
  decide +kernel

theorem context_12_287018_936666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287018 ⟨936666, by decide⟩ :=
  accepted_of_selected 12 287018 ⟨936666, by decide⟩ ⟨12, 2, 0, 936666, 287018, 3173, 65536⟩
    (by decide) selected_cut_35585

theorem selected_cut_35586 : selected 9 ⟨936715, by decide⟩
    (prefixPartial 12 287019) = some ⟨12, 2, 0, 936715, 287019, 3461, 65536⟩ := by
  decide +kernel

theorem context_12_287019_936715 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287019 ⟨936715, by decide⟩ :=
  accepted_of_selected 12 287019 ⟨936715, by decide⟩ ⟨12, 2, 0, 936715, 287019, 3461, 65536⟩
    (by decide) selected_cut_35586

theorem unmarked_context_11_71754_936716 : frontier 10 ⟨936716, by decide⟩
    (prefixCache 11 71754) (prefixPartial 11 71754) = false := by
  decide +kernel

theorem node_context_11_71754_936716 : EJMOriginalGlobalDAGData.nodes 10 ⟨936716, by decide⟩ =
    .split (coordinate 11) (![⟨936566, by decide⟩,⟨936612, by decide⟩,⟨936666, by decide⟩,⟨936715, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71754_936716 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71754 ⟨936716, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71754
    ⟨936716, by decide⟩ (by decide) (![⟨936566, by decide⟩,⟨936612, by decide⟩,⟨936666, by decide⟩,⟨936715, by decide⟩]) unmarked_context_11_71754_936716 node_context_11_71754_936716
  intro a
  fin_cases a
  · exact context_12_287016_936566
  · exact context_12_287017_936612
  · exact context_12_287018_936666
  · exact context_12_287019_936715

theorem selected_cut_35587 : selected 9 ⟨936790, by decide⟩
    (prefixPartial 12 287020) = some ⟨12, 2, 0, 936790, 287020, 3745, 65536⟩ := by
  decide +kernel

theorem context_12_287020_936790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287020 ⟨936790, by decide⟩ :=
  accepted_of_selected 12 287020 ⟨936790, by decide⟩ ⟨12, 2, 0, 936790, 287020, 3745, 65536⟩
    (by decide) selected_cut_35587

theorem selected_cut_35588 : selected 9 ⟨936840, by decide⟩
    (prefixPartial 12 287021) = some ⟨12, 2, 0, 936840, 287021, 3053, 65536⟩ := by
  decide +kernel

theorem context_12_287021_936840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287021 ⟨936840, by decide⟩ :=
  accepted_of_selected 12 287021 ⟨936840, by decide⟩ ⟨12, 2, 0, 936840, 287021, 3053, 65536⟩
    (by decide) selected_cut_35588

theorem selected_cut_35589 : selected 9 ⟨936897, by decide⟩
    (prefixPartial 12 287022) = some ⟨12, 2, 0, 936897, 287022, 3313, 65536⟩ := by
  decide +kernel

theorem context_12_287022_936897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287022 ⟨936897, by decide⟩ :=
  accepted_of_selected 12 287022 ⟨936897, by decide⟩ ⟨12, 2, 0, 936897, 287022, 3313, 65536⟩
    (by decide) selected_cut_35589

theorem selected_cut_35590 : selected 9 ⟨936953, by decide⟩
    (prefixPartial 12 287023) = some ⟨12, 2, 0, 936953, 287023, 3389, 65536⟩ := by
  decide +kernel

theorem context_12_287023_936953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287023 ⟨936953, by decide⟩ :=
  accepted_of_selected 12 287023 ⟨936953, by decide⟩ ⟨12, 2, 0, 936953, 287023, 3389, 65536⟩
    (by decide) selected_cut_35590

theorem unmarked_context_11_71755_936954 : frontier 10 ⟨936954, by decide⟩
    (prefixCache 11 71755) (prefixPartial 11 71755) = false := by
  decide +kernel

theorem node_context_11_71755_936954 : EJMOriginalGlobalDAGData.nodes 10 ⟨936954, by decide⟩ =
    .split (coordinate 11) (![⟨936790, by decide⟩,⟨936840, by decide⟩,⟨936897, by decide⟩,⟨936953, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71755_936954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71755 ⟨936954, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71755
    ⟨936954, by decide⟩ (by decide) (![⟨936790, by decide⟩,⟨936840, by decide⟩,⟨936897, by decide⟩,⟨936953, by decide⟩]) unmarked_context_11_71755_936954 node_context_11_71755_936954
  intro a
  fin_cases a
  · exact context_12_287020_936790
  · exact context_12_287021_936840
  · exact context_12_287022_936897
  · exact context_12_287023_936953

theorem unmarked_context_10_17938_936955 : frontier 11 ⟨936955, by decide⟩
    (prefixCache 10 17938) (prefixPartial 10 17938) = false := by
  decide +kernel

theorem node_context_10_17938_936955 : EJMOriginalGlobalDAGData.nodes 11 ⟨936955, by decide⟩ =
    .split (coordinate 10) (![⟨936330, by decide⟩,⟨936485, by decide⟩,⟨936716, by decide⟩,⟨936954, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17938_936955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17938 ⟨936955, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17938
    ⟨936955, by decide⟩ (by decide) (![⟨936330, by decide⟩,⟨936485, by decide⟩,⟨936716, by decide⟩,⟨936954, by decide⟩]) unmarked_context_10_17938_936955 node_context_10_17938_936955
  intro a
  fin_cases a
  · exact context_11_71752_936330
  · exact context_11_71753_936485
  · exact context_11_71754_936716
  · exact context_11_71755_936954

theorem selected_cut_35591 : selected 9 ⟨937011, by decide⟩
    (prefixPartial 12 287024) = some ⟨12, 2, 0, 937011, 287024, 1701, 65536⟩ := by
  decide +kernel

theorem context_12_287024_937011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287024 ⟨937011, by decide⟩ :=
  accepted_of_selected 12 287024 ⟨937011, by decide⟩ ⟨12, 2, 0, 937011, 287024, 1701, 65536⟩
    (by decide) selected_cut_35591

theorem selected_cut_35592 : selected 9 ⟨937048, by decide⟩
    (prefixPartial 12 287025) = some ⟨12, 2, 0, 937048, 287025, 2581, 65536⟩ := by
  decide +kernel

theorem context_12_287025_937048 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287025 ⟨937048, by decide⟩ :=
  accepted_of_selected 12 287025 ⟨937048, by decide⟩ ⟨12, 2, 0, 937048, 287025, 2581, 65536⟩
    (by decide) selected_cut_35592

theorem selected_cut_35593 : selected 9 ⟨937083, by decide⟩
    (prefixPartial 12 287026) = some ⟨12, 2, 0, 937083, 287026, 2517, 65536⟩ := by
  decide +kernel

theorem context_12_287026_937083 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287026 ⟨937083, by decide⟩ :=
  accepted_of_selected 12 287026 ⟨937083, by decide⟩ ⟨12, 2, 0, 937083, 287026, 2517, 65536⟩
    (by decide) selected_cut_35593

theorem selected_cut_35594 : selected 9 ⟨937136, by decide⟩
    (prefixPartial 12 287027) = some ⟨12, 2, 0, 937136, 287027, 2849, 65536⟩ := by
  decide +kernel

theorem context_12_287027_937136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287027 ⟨937136, by decide⟩ :=
  accepted_of_selected 12 287027 ⟨937136, by decide⟩ ⟨12, 2, 0, 937136, 287027, 2849, 65536⟩
    (by decide) selected_cut_35594

theorem unmarked_context_11_71756_937137 : frontier 10 ⟨937137, by decide⟩
    (prefixCache 11 71756) (prefixPartial 11 71756) = false := by
  decide +kernel

theorem node_context_11_71756_937137 : EJMOriginalGlobalDAGData.nodes 10 ⟨937137, by decide⟩ =
    .split (coordinate 11) (![⟨937011, by decide⟩,⟨937048, by decide⟩,⟨937083, by decide⟩,⟨937136, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71756_937137 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71756 ⟨937137, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71756
    ⟨937137, by decide⟩ (by decide) (![⟨937011, by decide⟩,⟨937048, by decide⟩,⟨937083, by decide⟩,⟨937136, by decide⟩]) unmarked_context_11_71756_937137 node_context_11_71756_937137
  intro a
  fin_cases a
  · exact context_12_287024_937011
  · exact context_12_287025_937048
  · exact context_12_287026_937083
  · exact context_12_287027_937136

theorem selected_cut_35595 : selected 9 ⟨937190, by decide⟩
    (prefixPartial 12 287028) = some ⟨12, 2, 0, 937190, 287028, 3089, 65536⟩ := by
  decide +kernel

theorem context_12_287028_937190 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287028 ⟨937190, by decide⟩ :=
  accepted_of_selected 12 287028 ⟨937190, by decide⟩ ⟨12, 2, 0, 937190, 287028, 3089, 65536⟩
    (by decide) selected_cut_35595

theorem selected_cut_35596 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 287029) = some ⟨12, 1, 0, 891951, 287029, 1, 65536⟩ := by
  decide +kernel

theorem context_12_287029_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287029 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 287029 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 287029, 1, 65536⟩
    (by decide) selected_cut_35596

theorem selected_cut_35597 : selected 9 ⟨937222, by decide⟩
    (prefixPartial 12 287030) = some ⟨12, 2, 0, 937222, 287030, 2573, 65536⟩ := by
  decide +kernel

theorem context_12_287030_937222 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287030 ⟨937222, by decide⟩ :=
  accepted_of_selected 12 287030 ⟨937222, by decide⟩ ⟨12, 2, 0, 937222, 287030, 2573, 65536⟩
    (by decide) selected_cut_35597

theorem selected_cut_35598 : selected 9 ⟨937267, by decide⟩
    (prefixPartial 12 287031) = some ⟨12, 2, 0, 937267, 287031, 2797, 65536⟩ := by
  decide +kernel

theorem context_12_287031_937267 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287031 ⟨937267, by decide⟩ :=
  accepted_of_selected 12 287031 ⟨937267, by decide⟩ ⟨12, 2, 0, 937267, 287031, 2797, 65536⟩
    (by decide) selected_cut_35598

theorem unmarked_context_11_71757_937268 : frontier 10 ⟨937268, by decide⟩
    (prefixCache 11 71757) (prefixPartial 11 71757) = false := by
  decide +kernel

theorem node_context_11_71757_937268 : EJMOriginalGlobalDAGData.nodes 10 ⟨937268, by decide⟩ =
    .split (coordinate 11) (![⟨937190, by decide⟩,⟨891951, by decide⟩,⟨937222, by decide⟩,⟨937267, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71757_937268 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71757 ⟨937268, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71757
    ⟨937268, by decide⟩ (by decide) (![⟨937190, by decide⟩,⟨891951, by decide⟩,⟨937222, by decide⟩,⟨937267, by decide⟩]) unmarked_context_11_71757_937268 node_context_11_71757_937268
  intro a
  fin_cases a
  · exact context_12_287028_937190
  · exact context_12_287029_891951
  · exact context_12_287030_937222
  · exact context_12_287031_937267

theorem selected_cut_35599 : selected 9 ⟨937346, by decide⟩
    (prefixPartial 12 287032) = some ⟨12, 2, 0, 937346, 287032, 3725, 65536⟩ := by
  decide +kernel

theorem context_12_287032_937346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287032 ⟨937346, by decide⟩ :=
  accepted_of_selected 12 287032 ⟨937346, by decide⟩ ⟨12, 2, 0, 937346, 287032, 3725, 65536⟩
    (by decide) selected_cut_35599

theorem selected_cut_35600 : selected 9 ⟨937391, by decide⟩
    (prefixPartial 12 287033) = some ⟨12, 2, 0, 937391, 287033, 2821, 65536⟩ := by
  decide +kernel

theorem context_12_287033_937391 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287033 ⟨937391, by decide⟩ :=
  accepted_of_selected 12 287033 ⟨937391, by decide⟩ ⟨12, 2, 0, 937391, 287033, 2821, 65536⟩
    (by decide) selected_cut_35600

theorem selected_cut_35601 : selected 9 ⟨937436, by decide⟩
    (prefixPartial 12 287034) = some ⟨12, 2, 0, 937436, 287034, 2909, 65536⟩ := by
  decide +kernel

theorem context_12_287034_937436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287034 ⟨937436, by decide⟩ :=
  accepted_of_selected 12 287034 ⟨937436, by decide⟩ ⟨12, 2, 0, 937436, 287034, 2909, 65536⟩
    (by decide) selected_cut_35601

theorem selected_cut_35602 : selected 9 ⟨937494, by decide⟩
    (prefixPartial 12 287035) = some ⟨12, 2, 0, 937494, 287035, 3157, 65536⟩ := by
  decide +kernel

theorem context_12_287035_937494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287035 ⟨937494, by decide⟩ :=
  accepted_of_selected 12 287035 ⟨937494, by decide⟩ ⟨12, 2, 0, 937494, 287035, 3157, 65536⟩
    (by decide) selected_cut_35602

theorem unmarked_context_11_71758_937495 : frontier 10 ⟨937495, by decide⟩
    (prefixCache 11 71758) (prefixPartial 11 71758) = false := by
  decide +kernel

theorem node_context_11_71758_937495 : EJMOriginalGlobalDAGData.nodes 10 ⟨937495, by decide⟩ =
    .split (coordinate 11) (![⟨937346, by decide⟩,⟨937391, by decide⟩,⟨937436, by decide⟩,⟨937494, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71758_937495 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71758 ⟨937495, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71758
    ⟨937495, by decide⟩ (by decide) (![⟨937346, by decide⟩,⟨937391, by decide⟩,⟨937436, by decide⟩,⟨937494, by decide⟩]) unmarked_context_11_71758_937495 node_context_11_71758_937495
  intro a
  fin_cases a
  · exact context_12_287032_937346
  · exact context_12_287033_937391
  · exact context_12_287034_937436
  · exact context_12_287035_937494

theorem selected_cut_35603 : selected 9 ⟨937544, by decide⟩
    (prefixPartial 12 287036) = some ⟨12, 2, 0, 937544, 287036, 2905, 65536⟩ := by
  decide +kernel

theorem context_12_287036_937544 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287036 ⟨937544, by decide⟩ :=
  accepted_of_selected 12 287036 ⟨937544, by decide⟩ ⟨12, 2, 0, 937544, 287036, 2905, 65536⟩
    (by decide) selected_cut_35603

theorem selected_cut_35604 : selected 9 ⟨937583, by decide⟩
    (prefixPartial 12 287037) = some ⟨12, 2, 0, 937583, 287037, 2465, 65536⟩ := by
  decide +kernel

theorem context_12_287037_937583 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287037 ⟨937583, by decide⟩ :=
  accepted_of_selected 12 287037 ⟨937583, by decide⟩ ⟨12, 2, 0, 937583, 287037, 2465, 65536⟩
    (by decide) selected_cut_35604

theorem selected_cut_35605 : selected 9 ⟨937619, by decide⟩
    (prefixPartial 12 287038) = some ⟨12, 2, 0, 937619, 287038, 2469, 65536⟩ := by
  decide +kernel

theorem context_12_287038_937619 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287038 ⟨937619, by decide⟩ :=
  accepted_of_selected 12 287038 ⟨937619, by decide⟩ ⟨12, 2, 0, 937619, 287038, 2469, 65536⟩
    (by decide) selected_cut_35605

theorem selected_cut_35606 : selected 9 ⟨937671, by decide⟩
    (prefixPartial 12 287039) = some ⟨12, 2, 0, 937671, 287039, 2773, 65536⟩ := by
  decide +kernel

theorem context_12_287039_937671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287039 ⟨937671, by decide⟩ :=
  accepted_of_selected 12 287039 ⟨937671, by decide⟩ ⟨12, 2, 0, 937671, 287039, 2773, 65536⟩
    (by decide) selected_cut_35606

theorem unmarked_context_11_71759_937672 : frontier 10 ⟨937672, by decide⟩
    (prefixCache 11 71759) (prefixPartial 11 71759) = false := by
  decide +kernel

theorem node_context_11_71759_937672 : EJMOriginalGlobalDAGData.nodes 10 ⟨937672, by decide⟩ =
    .split (coordinate 11) (![⟨937544, by decide⟩,⟨937583, by decide⟩,⟨937619, by decide⟩,⟨937671, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71759_937672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71759 ⟨937672, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71759
    ⟨937672, by decide⟩ (by decide) (![⟨937544, by decide⟩,⟨937583, by decide⟩,⟨937619, by decide⟩,⟨937671, by decide⟩]) unmarked_context_11_71759_937672 node_context_11_71759_937672
  intro a
  fin_cases a
  · exact context_12_287036_937544
  · exact context_12_287037_937583
  · exact context_12_287038_937619
  · exact context_12_287039_937671

theorem unmarked_context_10_17939_937673 : frontier 11 ⟨937673, by decide⟩
    (prefixCache 10 17939) (prefixPartial 10 17939) = false := by
  decide +kernel

theorem node_context_10_17939_937673 : EJMOriginalGlobalDAGData.nodes 11 ⟨937673, by decide⟩ =
    .split (coordinate 10) (![⟨937137, by decide⟩,⟨937268, by decide⟩,⟨937495, by decide⟩,⟨937672, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17939_937673 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17939 ⟨937673, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17939
    ⟨937673, by decide⟩ (by decide) (![⟨937137, by decide⟩,⟨937268, by decide⟩,⟨937495, by decide⟩,⟨937672, by decide⟩]) unmarked_context_10_17939_937673 node_context_10_17939_937673
  intro a
  fin_cases a
  · exact context_11_71756_937137
  · exact context_11_71757_937268
  · exact context_11_71758_937495
  · exact context_11_71759_937672

theorem unmarked_context_9_4484_937674 : frontier 12 ⟨937674, by decide⟩
    (prefixCache 9 4484) (prefixPartial 9 4484) = false := by
  decide +kernel

theorem node_context_9_4484_937674 : EJMOriginalGlobalDAGData.nodes 12 ⟨937674, by decide⟩ =
    .split (coordinate 9) (![⟨935437, by decide⟩,⟨936110, by decide⟩,⟨936955, by decide⟩,⟨937673, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4484_937674 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4484 ⟨937674, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4484
    ⟨937674, by decide⟩ (by decide) (![⟨935437, by decide⟩,⟨936110, by decide⟩,⟨936955, by decide⟩,⟨937673, by decide⟩]) unmarked_context_9_4484_937674 node_context_9_4484_937674
  intro a
  fin_cases a
  · exact context_10_17936_935437
  · exact context_10_17937_936110
  · exact context_10_17938_936955
  · exact context_10_17939_937673

theorem selected_cut_35607 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 71760) = some ⟨11, 1, 0, 907917, 71760, 1, 262144⟩ := by
  decide +kernel

theorem context_11_71760_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71760 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 71760 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 71760, 1, 262144⟩
    (by decide) selected_cut_35607

theorem selected_cut_35608 : selected 9 ⟨937712, by decide⟩
    (prefixPartial 12 287044) = some ⟨12, 2, 0, 937712, 287044, 2057, 65536⟩ := by
  decide +kernel

theorem context_12_287044_937712 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287044 ⟨937712, by decide⟩ :=
  accepted_of_selected 12 287044 ⟨937712, by decide⟩ ⟨12, 2, 0, 937712, 287044, 2057, 65536⟩
    (by decide) selected_cut_35608

theorem selected_cut_35609 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 287045) = some ⟨12, 1, 0, 896706, 287045, 1, 65536⟩ := by
  decide +kernel

theorem context_12_287045_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287045 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 287045 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 287045, 1, 65536⟩
    (by decide) selected_cut_35609

theorem selected_cut_35610 : selected 9 ⟨937739, by decide⟩
    (prefixPartial 12 287046) = some ⟨12, 2, 0, 937739, 287046, 1817, 65536⟩ := by
  decide +kernel

theorem context_12_287046_937739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287046 ⟨937739, by decide⟩ :=
  accepted_of_selected 12 287046 ⟨937739, by decide⟩ ⟨12, 2, 0, 937739, 287046, 1817, 65536⟩
    (by decide) selected_cut_35610

theorem selected_cut_35611 : selected 9 ⟨937762, by decide⟩
    (prefixPartial 12 287047) = some ⟨12, 2, 0, 937762, 287047, 1881, 65536⟩ := by
  decide +kernel

theorem context_12_287047_937762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287047 ⟨937762, by decide⟩ :=
  accepted_of_selected 12 287047 ⟨937762, by decide⟩ ⟨12, 2, 0, 937762, 287047, 1881, 65536⟩
    (by decide) selected_cut_35611

theorem unmarked_context_11_71761_937763 : frontier 10 ⟨937763, by decide⟩
    (prefixCache 11 71761) (prefixPartial 11 71761) = false := by
  decide +kernel

theorem node_context_11_71761_937763 : EJMOriginalGlobalDAGData.nodes 10 ⟨937763, by decide⟩ =
    .split (coordinate 11) (![⟨937712, by decide⟩,⟨896706, by decide⟩,⟨937739, by decide⟩,⟨937762, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71761_937763 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71761 ⟨937763, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71761
    ⟨937763, by decide⟩ (by decide) (![⟨937712, by decide⟩,⟨896706, by decide⟩,⟨937739, by decide⟩,⟨937762, by decide⟩]) unmarked_context_11_71761_937763 node_context_11_71761_937763
  intro a
  fin_cases a
  · exact context_12_287044_937712
  · exact context_12_287045_896706
  · exact context_12_287046_937739
  · exact context_12_287047_937762

theorem selected_cut_35612 : selected 9 ⟨937811, by decide⟩
    (prefixPartial 12 287048) = some ⟨12, 2, 0, 937811, 287048, 2701, 65536⟩ := by
  decide +kernel

theorem context_12_287048_937811 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287048 ⟨937811, by decide⟩ :=
  accepted_of_selected 12 287048 ⟨937811, by decide⟩ ⟨12, 2, 0, 937811, 287048, 2701, 65536⟩
    (by decide) selected_cut_35612

theorem selected_cut_35613 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 287049) = some ⟨12, 1, 0, 896706, 287049, 1, 65536⟩ := by
  decide +kernel

theorem context_12_287049_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287049 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 287049 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 287049, 1, 65536⟩
    (by decide) selected_cut_35613

theorem selected_cut_35614 : selected 9 ⟨937844, by decide⟩
    (prefixPartial 12 287050) = some ⟨12, 2, 0, 937844, 287050, 2217, 65536⟩ := by
  decide +kernel

theorem context_12_287050_937844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287050 ⟨937844, by decide⟩ :=
  accepted_of_selected 12 287050 ⟨937844, by decide⟩ ⟨12, 2, 0, 937844, 287050, 2217, 65536⟩
    (by decide) selected_cut_35614

theorem selected_cut_35615 : selected 9 ⟨937884, by decide⟩
    (prefixPartial 12 287051) = some ⟨12, 2, 0, 937884, 287051, 2369, 65536⟩ := by
  decide +kernel

theorem context_12_287051_937884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287051 ⟨937884, by decide⟩ :=
  accepted_of_selected 12 287051 ⟨937884, by decide⟩ ⟨12, 2, 0, 937884, 287051, 2369, 65536⟩
    (by decide) selected_cut_35615

theorem unmarked_context_11_71762_937885 : frontier 10 ⟨937885, by decide⟩
    (prefixCache 11 71762) (prefixPartial 11 71762) = false := by
  decide +kernel

theorem node_context_11_71762_937885 : EJMOriginalGlobalDAGData.nodes 10 ⟨937885, by decide⟩ =
    .split (coordinate 11) (![⟨937811, by decide⟩,⟨896706, by decide⟩,⟨937844, by decide⟩,⟨937884, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71762_937885 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71762 ⟨937885, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71762
    ⟨937885, by decide⟩ (by decide) (![⟨937811, by decide⟩,⟨896706, by decide⟩,⟨937844, by decide⟩,⟨937884, by decide⟩]) unmarked_context_11_71762_937885 node_context_11_71762_937885
  intro a
  fin_cases a
  · exact context_12_287048_937811
  · exact context_12_287049_896706
  · exact context_12_287050_937844
  · exact context_12_287051_937884

theorem selected_cut_35616 : selected 9 ⟨937918, by decide⟩
    (prefixPartial 12 287052) = some ⟨12, 2, 0, 937918, 287052, 2201, 65536⟩ := by
  decide +kernel

theorem context_12_287052_937918 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287052 ⟨937918, by decide⟩ :=
  accepted_of_selected 12 287052 ⟨937918, by decide⟩ ⟨12, 2, 0, 937918, 287052, 2201, 65536⟩
    (by decide) selected_cut_35616

theorem selected_cut_35617 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 287053) = some ⟨12, 1, 0, 896706, 287053, 1, 65536⟩ := by
  decide +kernel

theorem context_12_287053_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287053 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 287053 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 287053, 1, 65536⟩
    (by decide) selected_cut_35617

theorem selected_cut_35618 : selected 9 ⟨937943, by decide⟩
    (prefixPartial 12 287054) = some ⟨12, 2, 0, 937943, 287054, 1949, 65536⟩ := by
  decide +kernel

theorem context_12_287054_937943 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 287054 ⟨937943, by decide⟩ :=
  accepted_of_selected 12 287054 ⟨937943, by decide⟩ ⟨12, 2, 0, 937943, 287054, 1949, 65536⟩
    (by decide) selected_cut_35618

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
