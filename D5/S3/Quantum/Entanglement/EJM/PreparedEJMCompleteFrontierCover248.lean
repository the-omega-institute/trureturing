/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover247
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_12_76651_601329 : frontier 9 ⟨601329, by decide⟩
    (prefixCache 12 76651) (prefixPartial 12 76651) = false := by
  decide +kernel

theorem node_context_12_76651_601329 : EJMOriginalGlobalDAGData.nodes 9 ⟨601329, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨601287, by decide⟩,⟨601321, by decide⟩,⟨601328, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76651_601329 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76651 ⟨601329, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76651
    ⟨601329, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨601287, by decide⟩,⟨601321, by decide⟩,⟨601328, by decide⟩]) unmarked_context_12_76651_601329 node_context_12_76651_601329
  intro a
  fin_cases a
  · exact context_13_306604_3444
  · exact context_13_306605_601287
  · exact context_13_306606_601321
  · exact context_13_306607_601328

theorem unmarked_context_11_19162_601330 : frontier 10 ⟨601330, by decide⟩
    (prefixCache 11 19162) (prefixPartial 11 19162) = false := by
  decide +kernel

theorem node_context_11_19162_601330 : EJMOriginalGlobalDAGData.nodes 10 ⟨601330, by decide⟩ =
    .split (coordinate 11) (![⟨601226, by decide⟩,⟨601275, by decide⟩,⟨474208, by decide⟩,⟨601329, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19162_601330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19162 ⟨601330, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19162
    ⟨601330, by decide⟩ (by decide) (![⟨601226, by decide⟩,⟨601275, by decide⟩,⟨474208, by decide⟩,⟨601329, by decide⟩]) unmarked_context_11_19162_601330 node_context_11_19162_601330
  intro a
  fin_cases a
  · exact context_12_76648_601226
  · exact context_12_76649_601275
  · exact context_12_76650_474208
  · exact context_12_76651_601329

theorem selected_cut_23813 : selected 9 ⟨601365, by decide⟩
    (prefixPartial 12 76652) = some ⟨12, 2, 0, 601365, 76652, 2701, 65536⟩ := by
  decide +kernel

theorem context_12_76652_601365 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76652 ⟨601365, by decide⟩ :=
  accepted_of_selected 12 76652 ⟨601365, by decide⟩ ⟨12, 2, 0, 601365, 76652, 2701, 65536⟩
    (by decide) selected_cut_23813

theorem selected_cut_23814 : selected 9 ⟨601400, by decide⟩
    (prefixPartial 12 76653) = some ⟨12, 2, 0, 601400, 76653, 2737, 65536⟩ := by
  decide +kernel

theorem context_12_76653_601400 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76653 ⟨601400, by decide⟩ :=
  accepted_of_selected 12 76653 ⟨601400, by decide⟩ ⟨12, 2, 0, 601400, 76653, 2737, 65536⟩
    (by decide) selected_cut_23814

theorem selected_cut_23815 : selected 9 ⟨601439, by decide⟩
    (prefixPartial 12 76654) = some ⟨12, 2, 0, 601439, 76654, 2793, 65536⟩ := by
  decide +kernel

theorem context_12_76654_601439 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76654 ⟨601439, by decide⟩ :=
  accepted_of_selected 12 76654 ⟨601439, by decide⟩ ⟨12, 2, 0, 601439, 76654, 2793, 65536⟩
    (by decide) selected_cut_23815

theorem selected_cut_23816 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 306620) = some ⟨13, 1, 0, 3444, 306620, 1, 16384⟩ := by
  decide +kernel

theorem context_13_306620_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306620 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 306620 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 306620, 1, 16384⟩
    (by decide) selected_cut_23816

theorem selected_cut_23817 : selected 8 ⟨601458, by decide⟩
    (prefixPartial 13 306621) = some ⟨13, 2, 0, 601458, 306621, 969, 16384⟩ := by
  decide +kernel

theorem context_13_306621_601458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306621 ⟨601458, by decide⟩ :=
  accepted_of_selected 13 306621 ⟨601458, by decide⟩ ⟨13, 2, 0, 601458, 306621, 969, 16384⟩
    (by decide) selected_cut_23817

theorem selected_cut_23818 : selected 8 ⟨601486, by decide⟩
    (prefixPartial 13 306622) = some ⟨13, 2, 0, 601486, 306622, 2517, 16384⟩ := by
  decide +kernel

theorem context_13_306622_601486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306622 ⟨601486, by decide⟩ :=
  accepted_of_selected 13 306622 ⟨601486, by decide⟩ ⟨13, 2, 0, 601486, 306622, 2517, 16384⟩
    (by decide) selected_cut_23818

theorem selected_cut_23819 : selected 8 ⟨601496, by decide⟩
    (prefixPartial 13 306623) = some ⟨13, 2, 0, 601496, 306623, 1189, 16384⟩ := by
  decide +kernel

theorem context_13_306623_601496 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 306623 ⟨601496, by decide⟩ :=
  accepted_of_selected 13 306623 ⟨601496, by decide⟩ ⟨13, 2, 0, 601496, 306623, 1189, 16384⟩
    (by decide) selected_cut_23819

theorem unmarked_context_12_76655_601497 : frontier 9 ⟨601497, by decide⟩
    (prefixCache 12 76655) (prefixPartial 12 76655) = false := by
  decide +kernel

theorem node_context_12_76655_601497 : EJMOriginalGlobalDAGData.nodes 9 ⟨601497, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨601458, by decide⟩,⟨601486, by decide⟩,⟨601496, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76655_601497 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76655 ⟨601497, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76655
    ⟨601497, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨601458, by decide⟩,⟨601486, by decide⟩,⟨601496, by decide⟩]) unmarked_context_12_76655_601497 node_context_12_76655_601497
  intro a
  fin_cases a
  · exact context_13_306620_3444
  · exact context_13_306621_601458
  · exact context_13_306622_601486
  · exact context_13_306623_601496

theorem unmarked_context_11_19163_601498 : frontier 10 ⟨601498, by decide⟩
    (prefixCache 11 19163) (prefixPartial 11 19163) = false := by
  decide +kernel

theorem node_context_11_19163_601498 : EJMOriginalGlobalDAGData.nodes 10 ⟨601498, by decide⟩ =
    .split (coordinate 11) (![⟨601365, by decide⟩,⟨601400, by decide⟩,⟨601439, by decide⟩,⟨601497, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19163_601498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19163 ⟨601498, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19163
    ⟨601498, by decide⟩ (by decide) (![⟨601365, by decide⟩,⟨601400, by decide⟩,⟨601439, by decide⟩,⟨601497, by decide⟩]) unmarked_context_11_19163_601498 node_context_11_19163_601498
  intro a
  fin_cases a
  · exact context_12_76652_601365
  · exact context_12_76653_601400
  · exact context_12_76654_601439
  · exact context_12_76655_601497

theorem unmarked_context_10_4790_601499 : frontier 11 ⟨601499, by decide⟩
    (prefixCache 10 4790) (prefixPartial 10 4790) = false := by
  decide +kernel

theorem node_context_10_4790_601499 : EJMOriginalGlobalDAGData.nodes 11 ⟨601499, by decide⟩ =
    .split (coordinate 10) (![⟨600985, by decide⟩,⟨601156, by decide⟩,⟨601330, by decide⟩,⟨601498, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4790_601499 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4790 ⟨601499, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4790
    ⟨601499, by decide⟩ (by decide) (![⟨600985, by decide⟩,⟨601156, by decide⟩,⟨601330, by decide⟩,⟨601498, by decide⟩]) unmarked_context_10_4790_601499 node_context_10_4790_601499
  intro a
  fin_cases a
  · exact context_11_19160_600985
  · exact context_11_19161_601156
  · exact context_11_19162_601330
  · exact context_11_19163_601498

theorem selected_cut_23820 : selected 9 ⟨601545, by decide⟩
    (prefixPartial 12 76656) = some ⟨12, 2, 0, 601545, 76656, 3437, 65536⟩ := by
  decide +kernel

theorem context_12_76656_601545 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76656 ⟨601545, by decide⟩ :=
  accepted_of_selected 12 76656 ⟨601545, by decide⟩ ⟨12, 2, 0, 601545, 76656, 3437, 65536⟩
    (by decide) selected_cut_23820

theorem selected_cut_23821 : selected 9 ⟨601580, by decide⟩
    (prefixPartial 12 76657) = some ⟨12, 2, 0, 601580, 76657, 3485, 65536⟩ := by
  decide +kernel

theorem context_12_76657_601580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76657 ⟨601580, by decide⟩ :=
  accepted_of_selected 12 76657 ⟨601580, by decide⟩ ⟨12, 2, 0, 601580, 76657, 3485, 65536⟩
    (by decide) selected_cut_23821

theorem selected_cut_23822 : selected 9 ⟨601635, by decide⟩
    (prefixPartial 12 76658) = some ⟨12, 2, 0, 601635, 76658, 3965, 65536⟩ := by
  decide +kernel

theorem context_12_76658_601635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76658 ⟨601635, by decide⟩ :=
  accepted_of_selected 12 76658 ⟨601635, by decide⟩ ⟨12, 2, 0, 601635, 76658, 3965, 65536⟩
    (by decide) selected_cut_23822

theorem selected_cut_23823 : selected 9 ⟨601666, by decide⟩
    (prefixPartial 12 76659) = some ⟨12, 2, 0, 601666, 76659, 3405, 65536⟩ := by
  decide +kernel

theorem context_12_76659_601666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76659 ⟨601666, by decide⟩ :=
  accepted_of_selected 12 76659 ⟨601666, by decide⟩ ⟨12, 2, 0, 601666, 76659, 3405, 65536⟩
    (by decide) selected_cut_23823

theorem unmarked_context_11_19164_601667 : frontier 10 ⟨601667, by decide⟩
    (prefixCache 11 19164) (prefixPartial 11 19164) = false := by
  decide +kernel

theorem node_context_11_19164_601667 : EJMOriginalGlobalDAGData.nodes 10 ⟨601667, by decide⟩ =
    .split (coordinate 11) (![⟨601545, by decide⟩,⟨601580, by decide⟩,⟨601635, by decide⟩,⟨601666, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19164_601667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19164 ⟨601667, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19164
    ⟨601667, by decide⟩ (by decide) (![⟨601545, by decide⟩,⟨601580, by decide⟩,⟨601635, by decide⟩,⟨601666, by decide⟩]) unmarked_context_11_19164_601667 node_context_11_19164_601667
  intro a
  fin_cases a
  · exact context_12_76656_601545
  · exact context_12_76657_601580
  · exact context_12_76658_601635
  · exact context_12_76659_601666

theorem selected_cut_23824 : selected 9 ⟨601711, by decide⟩
    (prefixPartial 12 76660) = some ⟨12, 2, 0, 601711, 76660, 3485, 65536⟩ := by
  decide +kernel

theorem context_12_76660_601711 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76660 ⟨601711, by decide⟩ :=
  accepted_of_selected 12 76660 ⟨601711, by decide⟩ ⟨12, 2, 0, 601711, 76660, 3485, 65536⟩
    (by decide) selected_cut_23824

theorem selected_cut_23825 : selected 9 ⟨601750, by decide⟩
    (prefixPartial 12 76661) = some ⟨12, 2, 0, 601750, 76661, 3229, 65536⟩ := by
  decide +kernel

theorem context_12_76661_601750 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76661 ⟨601750, by decide⟩ :=
  accepted_of_selected 12 76661 ⟨601750, by decide⟩ ⟨12, 2, 0, 601750, 76661, 3229, 65536⟩
    (by decide) selected_cut_23825

theorem selected_cut_23826 : selected 9 ⟨601803, by decide⟩
    (prefixPartial 12 76662) = some ⟨12, 2, 0, 601803, 76662, 3781, 65536⟩ := by
  decide +kernel

theorem context_12_76662_601803 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76662 ⟨601803, by decide⟩ :=
  accepted_of_selected 12 76662 ⟨601803, by decide⟩ ⟨12, 2, 0, 601803, 76662, 3781, 65536⟩
    (by decide) selected_cut_23826

theorem selected_cut_23827 : selected 9 ⟨601840, by decide⟩
    (prefixPartial 12 76663) = some ⟨12, 2, 0, 601840, 76663, 3449, 65536⟩ := by
  decide +kernel

theorem context_12_76663_601840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76663 ⟨601840, by decide⟩ :=
  accepted_of_selected 12 76663 ⟨601840, by decide⟩ ⟨12, 2, 0, 601840, 76663, 3449, 65536⟩
    (by decide) selected_cut_23827

theorem unmarked_context_11_19165_601841 : frontier 10 ⟨601841, by decide⟩
    (prefixCache 11 19165) (prefixPartial 11 19165) = false := by
  decide +kernel

theorem node_context_11_19165_601841 : EJMOriginalGlobalDAGData.nodes 10 ⟨601841, by decide⟩ =
    .split (coordinate 11) (![⟨601711, by decide⟩,⟨601750, by decide⟩,⟨601803, by decide⟩,⟨601840, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19165_601841 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19165 ⟨601841, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19165
    ⟨601841, by decide⟩ (by decide) (![⟨601711, by decide⟩,⟨601750, by decide⟩,⟨601803, by decide⟩,⟨601840, by decide⟩]) unmarked_context_11_19165_601841 node_context_11_19165_601841
  intro a
  fin_cases a
  · exact context_12_76660_601711
  · exact context_12_76661_601750
  · exact context_12_76662_601803
  · exact context_12_76663_601840

theorem selected_cut_23828 : selected 9 ⟨601888, by decide⟩
    (prefixPartial 12 76664) = some ⟨12, 2, 0, 601888, 76664, 3161, 65536⟩ := by
  decide +kernel

theorem context_12_76664_601888 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76664 ⟨601888, by decide⟩ :=
  accepted_of_selected 12 76664 ⟨601888, by decide⟩ ⟨12, 2, 0, 601888, 76664, 3161, 65536⟩
    (by decide) selected_cut_23828

theorem selected_cut_23829 : selected 9 ⟨601935, by decide⟩
    (prefixPartial 12 76665) = some ⟨12, 2, 0, 601935, 76665, 3185, 65536⟩ := by
  decide +kernel

theorem context_12_76665_601935 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76665 ⟨601935, by decide⟩ :=
  accepted_of_selected 12 76665 ⟨601935, by decide⟩ ⟨12, 2, 0, 601935, 76665, 3185, 65536⟩
    (by decide) selected_cut_23829

theorem selected_cut_23830 : selected 9 ⟨601976, by decide⟩
    (prefixPartial 12 76666) = some ⟨12, 2, 0, 601976, 76666, 3349, 65536⟩ := by
  decide +kernel

theorem context_12_76666_601976 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76666 ⟨601976, by decide⟩ :=
  accepted_of_selected 12 76666 ⟨601976, by decide⟩ ⟨12, 2, 0, 601976, 76666, 3349, 65536⟩
    (by decide) selected_cut_23830

theorem selected_cut_23831 : selected 9 ⟨602014, by decide⟩
    (prefixPartial 12 76667) = some ⟨12, 2, 0, 602014, 76667, 3069, 65536⟩ := by
  decide +kernel

theorem context_12_76667_602014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76667 ⟨602014, by decide⟩ :=
  accepted_of_selected 12 76667 ⟨602014, by decide⟩ ⟨12, 2, 0, 602014, 76667, 3069, 65536⟩
    (by decide) selected_cut_23831

theorem unmarked_context_11_19166_602015 : frontier 10 ⟨602015, by decide⟩
    (prefixCache 11 19166) (prefixPartial 11 19166) = false := by
  decide +kernel

theorem node_context_11_19166_602015 : EJMOriginalGlobalDAGData.nodes 10 ⟨602015, by decide⟩ =
    .split (coordinate 11) (![⟨601888, by decide⟩,⟨601935, by decide⟩,⟨601976, by decide⟩,⟨602014, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19166_602015 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19166 ⟨602015, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19166
    ⟨602015, by decide⟩ (by decide) (![⟨601888, by decide⟩,⟨601935, by decide⟩,⟨601976, by decide⟩,⟨602014, by decide⟩]) unmarked_context_11_19166_602015 node_context_11_19166_602015
  intro a
  fin_cases a
  · exact context_12_76664_601888
  · exact context_12_76665_601935
  · exact context_12_76666_601976
  · exact context_12_76667_602014

theorem selected_cut_23832 : selected 9 ⟨602044, by decide⟩
    (prefixPartial 12 76668) = some ⟨12, 2, 0, 602044, 76668, 2605, 65536⟩ := by
  decide +kernel

theorem context_12_76668_602044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76668 ⟨602044, by decide⟩ :=
  accepted_of_selected 12 76668 ⟨602044, by decide⟩ ⟨12, 2, 0, 602044, 76668, 2605, 65536⟩
    (by decide) selected_cut_23832

theorem selected_cut_23833 : selected 9 ⟨602071, by decide⟩
    (prefixPartial 12 76669) = some ⟨12, 2, 0, 602071, 76669, 2645, 65536⟩ := by
  decide +kernel

theorem context_12_76669_602071 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76669 ⟨602071, by decide⟩ :=
  accepted_of_selected 12 76669 ⟨602071, by decide⟩ ⟨12, 2, 0, 602071, 76669, 2645, 65536⟩
    (by decide) selected_cut_23833

theorem selected_cut_23834 : selected 9 ⟨602104, by decide⟩
    (prefixPartial 12 76670) = some ⟨12, 2, 0, 602104, 76670, 2737, 65536⟩ := by
  decide +kernel

theorem context_12_76670_602104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76670 ⟨602104, by decide⟩ :=
  accepted_of_selected 12 76670 ⟨602104, by decide⟩ ⟨12, 2, 0, 602104, 76670, 2737, 65536⟩
    (by decide) selected_cut_23834

theorem selected_cut_23835 : selected 9 ⟨512556, by decide⟩
    (prefixPartial 12 76671) = some ⟨12, 1, 0, 512556, 76671, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76671_512556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76671 ⟨512556, by decide⟩ :=
  accepted_of_selected 12 76671 ⟨512556, by decide⟩ ⟨12, 1, 0, 512556, 76671, 1, 65536⟩
    (by decide) selected_cut_23835

theorem unmarked_context_11_19167_602105 : frontier 10 ⟨602105, by decide⟩
    (prefixCache 11 19167) (prefixPartial 11 19167) = false := by
  decide +kernel

theorem node_context_11_19167_602105 : EJMOriginalGlobalDAGData.nodes 10 ⟨602105, by decide⟩ =
    .split (coordinate 11) (![⟨602044, by decide⟩,⟨602071, by decide⟩,⟨602104, by decide⟩,⟨512556, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19167_602105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19167 ⟨602105, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19167
    ⟨602105, by decide⟩ (by decide) (![⟨602044, by decide⟩,⟨602071, by decide⟩,⟨602104, by decide⟩,⟨512556, by decide⟩]) unmarked_context_11_19167_602105 node_context_11_19167_602105
  intro a
  fin_cases a
  · exact context_12_76668_602044
  · exact context_12_76669_602071
  · exact context_12_76670_602104
  · exact context_12_76671_512556

theorem unmarked_context_10_4791_602106 : frontier 11 ⟨602106, by decide⟩
    (prefixCache 10 4791) (prefixPartial 10 4791) = false := by
  decide +kernel

theorem node_context_10_4791_602106 : EJMOriginalGlobalDAGData.nodes 11 ⟨602106, by decide⟩ =
    .split (coordinate 10) (![⟨601667, by decide⟩,⟨601841, by decide⟩,⟨602015, by decide⟩,⟨602105, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4791_602106 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4791 ⟨602106, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4791
    ⟨602106, by decide⟩ (by decide) (![⟨601667, by decide⟩,⟨601841, by decide⟩,⟨602015, by decide⟩,⟨602105, by decide⟩]) unmarked_context_10_4791_602106 node_context_10_4791_602106
  intro a
  fin_cases a
  · exact context_11_19164_601667
  · exact context_11_19165_601841
  · exact context_11_19166_602015
  · exact context_11_19167_602105

theorem unmarked_context_9_1197_602107 : frontier 12 ⟨602107, by decide⟩
    (prefixCache 9 1197) (prefixPartial 9 1197) = false := by
  decide +kernel

theorem node_context_9_1197_602107 : EJMOriginalGlobalDAGData.nodes 12 ⟨602107, by decide⟩ =
    .split (coordinate 9) (![⟨599898, by decide⟩,⟨600820, by decide⟩,⟨601499, by decide⟩,⟨602106, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1197_602107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1197 ⟨602107, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1197
    ⟨602107, by decide⟩ (by decide) (![⟨599898, by decide⟩,⟨600820, by decide⟩,⟨601499, by decide⟩,⟨602106, by decide⟩]) unmarked_context_9_1197_602107 node_context_9_1197_602107
  intro a
  fin_cases a
  · exact context_10_4788_599898
  · exact context_10_4789_600820
  · exact context_10_4790_601499
  · exact context_10_4791_602106

theorem selected_cut_23836 : selected 9 ⟨602130, by decide⟩
    (prefixPartial 12 76672) = some ⟨12, 2, 0, 602130, 76672, 1849, 65536⟩ := by
  decide +kernel

theorem context_12_76672_602130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76672 ⟨602130, by decide⟩ :=
  accepted_of_selected 12 76672 ⟨602130, by decide⟩ ⟨12, 2, 0, 602130, 76672, 1849, 65536⟩
    (by decide) selected_cut_23836

theorem selected_cut_23837 : selected 9 ⟨602155, by decide⟩
    (prefixPartial 12 76673) = some ⟨12, 2, 0, 602155, 76673, 2069, 65536⟩ := by
  decide +kernel

theorem context_12_76673_602155 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76673 ⟨602155, by decide⟩ :=
  accepted_of_selected 12 76673 ⟨602155, by decide⟩ ⟨12, 2, 0, 602155, 76673, 2069, 65536⟩
    (by decide) selected_cut_23837

theorem selected_cut_23838 : selected 9 ⟨602187, by decide⟩
    (prefixPartial 12 76674) = some ⟨12, 2, 0, 602187, 76674, 2421, 65536⟩ := by
  decide +kernel

theorem context_12_76674_602187 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76674 ⟨602187, by decide⟩ :=
  accepted_of_selected 12 76674 ⟨602187, by decide⟩ ⟨12, 2, 0, 602187, 76674, 2421, 65536⟩
    (by decide) selected_cut_23838

theorem selected_cut_23839 : selected 9 ⟨602211, by decide⟩
    (prefixPartial 12 76675) = some ⟨12, 2, 0, 602211, 76675, 2117, 65536⟩ := by
  decide +kernel

theorem context_12_76675_602211 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76675 ⟨602211, by decide⟩ :=
  accepted_of_selected 12 76675 ⟨602211, by decide⟩ ⟨12, 2, 0, 602211, 76675, 2117, 65536⟩
    (by decide) selected_cut_23839

theorem unmarked_context_11_19168_602212 : frontier 10 ⟨602212, by decide⟩
    (prefixCache 11 19168) (prefixPartial 11 19168) = false := by
  decide +kernel

theorem node_context_11_19168_602212 : EJMOriginalGlobalDAGData.nodes 10 ⟨602212, by decide⟩ =
    .split (coordinate 11) (![⟨602130, by decide⟩,⟨602155, by decide⟩,⟨602187, by decide⟩,⟨602211, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19168_602212 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19168 ⟨602212, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19168
    ⟨602212, by decide⟩ (by decide) (![⟨602130, by decide⟩,⟨602155, by decide⟩,⟨602187, by decide⟩,⟨602211, by decide⟩]) unmarked_context_11_19168_602212 node_context_11_19168_602212
  intro a
  fin_cases a
  · exact context_12_76672_602130
  · exact context_12_76673_602155
  · exact context_12_76674_602187
  · exact context_12_76675_602211

theorem selected_cut_23840 : selected 9 ⟨602232, by decide⟩
    (prefixPartial 12 76676) = some ⟨12, 2, 0, 602232, 76676, 1905, 65536⟩ := by
  decide +kernel

theorem context_12_76676_602232 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76676 ⟨602232, by decide⟩ :=
  accepted_of_selected 12 76676 ⟨602232, by decide⟩ ⟨12, 2, 0, 602232, 76676, 1905, 65536⟩
    (by decide) selected_cut_23840

theorem selected_cut_23841 : selected 9 ⟨602255, by decide⟩
    (prefixPartial 12 76677) = some ⟨12, 2, 0, 602255, 76677, 1993, 65536⟩ := by
  decide +kernel

theorem context_12_76677_602255 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76677 ⟨602255, by decide⟩ :=
  accepted_of_selected 12 76677 ⟨602255, by decide⟩ ⟨12, 2, 0, 602255, 76677, 1993, 65536⟩
    (by decide) selected_cut_23841

theorem selected_cut_23842 : selected 9 ⟨602278, by decide⟩
    (prefixPartial 12 76678) = some ⟨12, 2, 0, 602278, 76678, 2313, 65536⟩ := by
  decide +kernel

theorem context_12_76678_602278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76678 ⟨602278, by decide⟩ :=
  accepted_of_selected 12 76678 ⟨602278, by decide⟩ ⟨12, 2, 0, 602278, 76678, 2313, 65536⟩
    (by decide) selected_cut_23842

theorem selected_cut_23843 : selected 9 ⟨602301, by decide⟩
    (prefixPartial 12 76679) = some ⟨12, 2, 0, 602301, 76679, 2157, 65536⟩ := by
  decide +kernel

theorem context_12_76679_602301 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76679 ⟨602301, by decide⟩ :=
  accepted_of_selected 12 76679 ⟨602301, by decide⟩ ⟨12, 2, 0, 602301, 76679, 2157, 65536⟩
    (by decide) selected_cut_23843

theorem unmarked_context_11_19169_602302 : frontier 10 ⟨602302, by decide⟩
    (prefixCache 11 19169) (prefixPartial 11 19169) = false := by
  decide +kernel

theorem node_context_11_19169_602302 : EJMOriginalGlobalDAGData.nodes 10 ⟨602302, by decide⟩ =
    .split (coordinate 11) (![⟨602232, by decide⟩,⟨602255, by decide⟩,⟨602278, by decide⟩,⟨602301, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19169_602302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19169 ⟨602302, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19169
    ⟨602302, by decide⟩ (by decide) (![⟨602232, by decide⟩,⟨602255, by decide⟩,⟨602278, by decide⟩,⟨602301, by decide⟩]) unmarked_context_11_19169_602302 node_context_11_19169_602302
  intro a
  fin_cases a
  · exact context_12_76676_602232
  · exact context_12_76677_602255
  · exact context_12_76678_602278
  · exact context_12_76679_602301

theorem selected_cut_23844 : selected 9 ⟨602321, by decide⟩
    (prefixPartial 12 76680) = some ⟨12, 2, 0, 602321, 76680, 1793, 65536⟩ := by
  decide +kernel

theorem context_12_76680_602321 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76680 ⟨602321, by decide⟩ :=
  accepted_of_selected 12 76680 ⟨602321, by decide⟩ ⟨12, 2, 0, 602321, 76680, 1793, 65536⟩
    (by decide) selected_cut_23844

theorem selected_cut_23845 : selected 9 ⟨602346, by decide⟩
    (prefixPartial 12 76681) = some ⟨12, 2, 0, 602346, 76681, 2049, 65536⟩ := by
  decide +kernel

theorem context_12_76681_602346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76681 ⟨602346, by decide⟩ :=
  accepted_of_selected 12 76681 ⟨602346, by decide⟩ ⟨12, 2, 0, 602346, 76681, 2049, 65536⟩
    (by decide) selected_cut_23845

theorem selected_cut_23846 : selected 9 ⟨602370, by decide⟩
    (prefixPartial 12 76682) = some ⟨12, 2, 0, 602370, 76682, 2169, 65536⟩ := by
  decide +kernel

theorem context_12_76682_602370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76682 ⟨602370, by decide⟩ :=
  accepted_of_selected 12 76682 ⟨602370, by decide⟩ ⟨12, 2, 0, 602370, 76682, 2169, 65536⟩
    (by decide) selected_cut_23846

theorem selected_cut_23847 : selected 9 ⟨602394, by decide⟩
    (prefixPartial 12 76683) = some ⟨12, 2, 0, 602394, 76683, 1953, 65536⟩ := by
  decide +kernel

theorem context_12_76683_602394 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76683 ⟨602394, by decide⟩ :=
  accepted_of_selected 12 76683 ⟨602394, by decide⟩ ⟨12, 2, 0, 602394, 76683, 1953, 65536⟩
    (by decide) selected_cut_23847

theorem unmarked_context_11_19170_602395 : frontier 10 ⟨602395, by decide⟩
    (prefixCache 11 19170) (prefixPartial 11 19170) = false := by
  decide +kernel

theorem node_context_11_19170_602395 : EJMOriginalGlobalDAGData.nodes 10 ⟨602395, by decide⟩ =
    .split (coordinate 11) (![⟨602321, by decide⟩,⟨602346, by decide⟩,⟨602370, by decide⟩,⟨602394, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19170_602395 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19170 ⟨602395, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19170
    ⟨602395, by decide⟩ (by decide) (![⟨602321, by decide⟩,⟨602346, by decide⟩,⟨602370, by decide⟩,⟨602394, by decide⟩]) unmarked_context_11_19170_602395 node_context_11_19170_602395
  intro a
  fin_cases a
  · exact context_12_76680_602321
  · exact context_12_76681_602346
  · exact context_12_76682_602370
  · exact context_12_76683_602394

theorem selected_cut_23848 : selected 9 ⟨602416, by decide⟩
    (prefixPartial 12 76684) = some ⟨12, 2, 0, 602416, 76684, 1785, 65536⟩ := by
  decide +kernel

theorem context_12_76684_602416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76684 ⟨602416, by decide⟩ :=
  accepted_of_selected 12 76684 ⟨602416, by decide⟩ ⟨12, 2, 0, 602416, 76684, 1785, 65536⟩
    (by decide) selected_cut_23848

theorem selected_cut_23849 : selected 9 ⟨602441, by decide⟩
    (prefixPartial 12 76685) = some ⟨12, 2, 0, 602441, 76685, 2049, 65536⟩ := by
  decide +kernel

theorem context_12_76685_602441 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76685 ⟨602441, by decide⟩ :=
  accepted_of_selected 12 76685 ⟨602441, by decide⟩ ⟨12, 2, 0, 602441, 76685, 2049, 65536⟩
    (by decide) selected_cut_23849

theorem selected_cut_23850 : selected 9 ⟨602462, by decide⟩
    (prefixPartial 12 76686) = some ⟨12, 2, 0, 602462, 76686, 2169, 65536⟩ := by
  decide +kernel

theorem context_12_76686_602462 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76686 ⟨602462, by decide⟩ :=
  accepted_of_selected 12 76686 ⟨602462, by decide⟩ ⟨12, 2, 0, 602462, 76686, 2169, 65536⟩
    (by decide) selected_cut_23850

theorem selected_cut_23851 : selected 9 ⟨602496, by decide⟩
    (prefixPartial 12 76687) = some ⟨12, 2, 0, 602496, 76687, 2805, 65536⟩ := by
  decide +kernel

theorem context_12_76687_602496 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76687 ⟨602496, by decide⟩ :=
  accepted_of_selected 12 76687 ⟨602496, by decide⟩ ⟨12, 2, 0, 602496, 76687, 2805, 65536⟩
    (by decide) selected_cut_23851

theorem unmarked_context_11_19171_602497 : frontier 10 ⟨602497, by decide⟩
    (prefixCache 11 19171) (prefixPartial 11 19171) = false := by
  decide +kernel

theorem node_context_11_19171_602497 : EJMOriginalGlobalDAGData.nodes 10 ⟨602497, by decide⟩ =
    .split (coordinate 11) (![⟨602416, by decide⟩,⟨602441, by decide⟩,⟨602462, by decide⟩,⟨602496, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19171_602497 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19171 ⟨602497, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19171
    ⟨602497, by decide⟩ (by decide) (![⟨602416, by decide⟩,⟨602441, by decide⟩,⟨602462, by decide⟩,⟨602496, by decide⟩]) unmarked_context_11_19171_602497 node_context_11_19171_602497
  intro a
  fin_cases a
  · exact context_12_76684_602416
  · exact context_12_76685_602441
  · exact context_12_76686_602462
  · exact context_12_76687_602496

theorem unmarked_context_10_4792_602498 : frontier 11 ⟨602498, by decide⟩
    (prefixCache 10 4792) (prefixPartial 10 4792) = false := by
  decide +kernel

theorem node_context_10_4792_602498 : EJMOriginalGlobalDAGData.nodes 11 ⟨602498, by decide⟩ =
    .split (coordinate 10) (![⟨602212, by decide⟩,⟨602302, by decide⟩,⟨602395, by decide⟩,⟨602497, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4792_602498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4792 ⟨602498, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4792
    ⟨602498, by decide⟩ (by decide) (![⟨602212, by decide⟩,⟨602302, by decide⟩,⟨602395, by decide⟩,⟨602497, by decide⟩]) unmarked_context_10_4792_602498 node_context_10_4792_602498
  intro a
  fin_cases a
  · exact context_11_19168_602212
  · exact context_11_19169_602302
  · exact context_11_19170_602395
  · exact context_11_19171_602497

theorem selected_cut_23852 : selected 9 ⟨602521, by decide⟩
    (prefixPartial 12 76688) = some ⟨12, 2, 0, 602521, 76688, 2213, 65536⟩ := by
  decide +kernel

theorem context_12_76688_602521 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76688 ⟨602521, by decide⟩ :=
  accepted_of_selected 12 76688 ⟨602521, by decide⟩ ⟨12, 2, 0, 602521, 76688, 2213, 65536⟩
    (by decide) selected_cut_23852

theorem selected_cut_23853 : selected 9 ⟨602546, by decide⟩
    (prefixPartial 12 76689) = some ⟨12, 2, 0, 602546, 76689, 2385, 65536⟩ := by
  decide +kernel

theorem context_12_76689_602546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76689 ⟨602546, by decide⟩ :=
  accepted_of_selected 12 76689 ⟨602546, by decide⟩ ⟨12, 2, 0, 602546, 76689, 2385, 65536⟩
    (by decide) selected_cut_23853

theorem selected_cut_23854 : selected 9 ⟨602585, by decide⟩
    (prefixPartial 12 76690) = some ⟨12, 2, 0, 602585, 76690, 2661, 65536⟩ := by
  decide +kernel

theorem context_12_76690_602585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76690 ⟨602585, by decide⟩ :=
  accepted_of_selected 12 76690 ⟨602585, by decide⟩ ⟨12, 2, 0, 602585, 76690, 2661, 65536⟩
    (by decide) selected_cut_23854

theorem selected_cut_23855 : selected 9 ⟨602601, by decide⟩
    (prefixPartial 12 76691) = some ⟨12, 2, 0, 602601, 76691, 2021, 65536⟩ := by
  decide +kernel

theorem context_12_76691_602601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76691 ⟨602601, by decide⟩ :=
  accepted_of_selected 12 76691 ⟨602601, by decide⟩ ⟨12, 2, 0, 602601, 76691, 2021, 65536⟩
    (by decide) selected_cut_23855

theorem unmarked_context_11_19172_602602 : frontier 10 ⟨602602, by decide⟩
    (prefixCache 11 19172) (prefixPartial 11 19172) = false := by
  decide +kernel

theorem node_context_11_19172_602602 : EJMOriginalGlobalDAGData.nodes 10 ⟨602602, by decide⟩ =
    .split (coordinate 11) (![⟨602521, by decide⟩,⟨602546, by decide⟩,⟨602585, by decide⟩,⟨602601, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19172_602602 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19172 ⟨602602, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19172
    ⟨602602, by decide⟩ (by decide) (![⟨602521, by decide⟩,⟨602546, by decide⟩,⟨602585, by decide⟩,⟨602601, by decide⟩]) unmarked_context_11_19172_602602 node_context_11_19172_602602
  intro a
  fin_cases a
  · exact context_12_76688_602521
  · exact context_12_76689_602546
  · exact context_12_76690_602585
  · exact context_12_76691_602601

theorem selected_cut_23856 : selected 9 ⟨602630, by decide⟩
    (prefixPartial 12 76692) = some ⟨12, 2, 0, 602630, 76692, 2229, 65536⟩ := by
  decide +kernel

theorem context_12_76692_602630 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76692 ⟨602630, by decide⟩ :=
  accepted_of_selected 12 76692 ⟨602630, by decide⟩ ⟨12, 2, 0, 602630, 76692, 2229, 65536⟩
    (by decide) selected_cut_23856

theorem selected_cut_23857 : selected 9 ⟨602653, by decide⟩
    (prefixPartial 12 76693) = some ⟨12, 2, 0, 602653, 76693, 2277, 65536⟩ := by
  decide +kernel

theorem context_12_76693_602653 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76693 ⟨602653, by decide⟩ :=
  accepted_of_selected 12 76693 ⟨602653, by decide⟩ ⟨12, 2, 0, 602653, 76693, 2277, 65536⟩
    (by decide) selected_cut_23857

theorem selected_cut_23858 : selected 9 ⟨602688, by decide⟩
    (prefixPartial 12 76694) = some ⟨12, 2, 0, 602688, 76694, 2649, 65536⟩ := by
  decide +kernel

theorem context_12_76694_602688 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76694 ⟨602688, by decide⟩ :=
  accepted_of_selected 12 76694 ⟨602688, by decide⟩ ⟨12, 2, 0, 602688, 76694, 2649, 65536⟩
    (by decide) selected_cut_23858

theorem selected_cut_23859 : selected 9 ⟨602706, by decide⟩
    (prefixPartial 12 76695) = some ⟨12, 2, 0, 602706, 76695, 2041, 65536⟩ := by
  decide +kernel

theorem context_12_76695_602706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76695 ⟨602706, by decide⟩ :=
  accepted_of_selected 12 76695 ⟨602706, by decide⟩ ⟨12, 2, 0, 602706, 76695, 2041, 65536⟩
    (by decide) selected_cut_23859

theorem unmarked_context_11_19173_602707 : frontier 10 ⟨602707, by decide⟩
    (prefixCache 11 19173) (prefixPartial 11 19173) = false := by
  decide +kernel

theorem node_context_11_19173_602707 : EJMOriginalGlobalDAGData.nodes 10 ⟨602707, by decide⟩ =
    .split (coordinate 11) (![⟨602630, by decide⟩,⟨602653, by decide⟩,⟨602688, by decide⟩,⟨602706, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19173_602707 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19173 ⟨602707, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19173
    ⟨602707, by decide⟩ (by decide) (![⟨602630, by decide⟩,⟨602653, by decide⟩,⟨602688, by decide⟩,⟨602706, by decide⟩]) unmarked_context_11_19173_602707 node_context_11_19173_602707
  intro a
  fin_cases a
  · exact context_12_76692_602630
  · exact context_12_76693_602653
  · exact context_12_76694_602688
  · exact context_12_76695_602706

theorem selected_cut_23860 : selected 9 ⟨602727, by decide⟩
    (prefixPartial 12 76696) = some ⟨12, 2, 0, 602727, 76696, 1965, 65536⟩ := by
  decide +kernel

theorem context_12_76696_602727 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76696 ⟨602727, by decide⟩ :=
  accepted_of_selected 12 76696 ⟨602727, by decide⟩ ⟨12, 2, 0, 602727, 76696, 1965, 65536⟩
    (by decide) selected_cut_23860

theorem selected_cut_23861 : selected 9 ⟨602756, by decide⟩
    (prefixPartial 12 76697) = some ⟨12, 2, 0, 602756, 76697, 2265, 65536⟩ := by
  decide +kernel

theorem context_12_76697_602756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76697 ⟨602756, by decide⟩ :=
  accepted_of_selected 12 76697 ⟨602756, by decide⟩ ⟨12, 2, 0, 602756, 76697, 2265, 65536⟩
    (by decide) selected_cut_23861

theorem selected_cut_23862 : selected 9 ⟨602784, by decide⟩
    (prefixPartial 12 76698) = some ⟨12, 2, 0, 602784, 76698, 2261, 65536⟩ := by
  decide +kernel

theorem context_12_76698_602784 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76698 ⟨602784, by decide⟩ :=
  accepted_of_selected 12 76698 ⟨602784, by decide⟩ ⟨12, 2, 0, 602784, 76698, 2261, 65536⟩
    (by decide) selected_cut_23862

theorem selected_cut_23863 : selected 9 ⟨602800, by decide⟩
    (prefixPartial 12 76699) = some ⟨12, 2, 0, 602800, 76699, 1713, 65536⟩ := by
  decide +kernel

theorem context_12_76699_602800 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76699 ⟨602800, by decide⟩ :=
  accepted_of_selected 12 76699 ⟨602800, by decide⟩ ⟨12, 2, 0, 602800, 76699, 1713, 65536⟩
    (by decide) selected_cut_23863

theorem unmarked_context_11_19174_602801 : frontier 10 ⟨602801, by decide⟩
    (prefixCache 11 19174) (prefixPartial 11 19174) = false := by
  decide +kernel

theorem node_context_11_19174_602801 : EJMOriginalGlobalDAGData.nodes 10 ⟨602801, by decide⟩ =
    .split (coordinate 11) (![⟨602727, by decide⟩,⟨602756, by decide⟩,⟨602784, by decide⟩,⟨602800, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19174_602801 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19174 ⟨602801, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19174
    ⟨602801, by decide⟩ (by decide) (![⟨602727, by decide⟩,⟨602756, by decide⟩,⟨602784, by decide⟩,⟨602800, by decide⟩]) unmarked_context_11_19174_602801 node_context_11_19174_602801
  intro a
  fin_cases a
  · exact context_12_76696_602727
  · exact context_12_76697_602756
  · exact context_12_76698_602784
  · exact context_12_76699_602800

theorem selected_cut_23864 : selected 9 ⟨602820, by decide⟩
    (prefixPartial 12 76700) = some ⟨12, 2, 0, 602820, 76700, 1825, 65536⟩ := by
  decide +kernel

theorem context_12_76700_602820 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76700 ⟨602820, by decide⟩ :=
  accepted_of_selected 12 76700 ⟨602820, by decide⟩ ⟨12, 2, 0, 602820, 76700, 1825, 65536⟩
    (by decide) selected_cut_23864

theorem selected_cut_23865 : selected 9 ⟨602841, by decide⟩
    (prefixPartial 12 76701) = some ⟨12, 2, 0, 602841, 76701, 2025, 65536⟩ := by
  decide +kernel

theorem context_12_76701_602841 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76701 ⟨602841, by decide⟩ :=
  accepted_of_selected 12 76701 ⟨602841, by decide⟩ ⟨12, 2, 0, 602841, 76701, 2025, 65536⟩
    (by decide) selected_cut_23865

theorem selected_cut_23866 : selected 9 ⟨602864, by decide⟩
    (prefixPartial 12 76702) = some ⟨12, 2, 0, 602864, 76702, 2081, 65536⟩ := by
  decide +kernel

theorem context_12_76702_602864 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76702 ⟨602864, by decide⟩ :=
  accepted_of_selected 12 76702 ⟨602864, by decide⟩ ⟨12, 2, 0, 602864, 76702, 2081, 65536⟩
    (by decide) selected_cut_23866

theorem selected_cut_23867 : selected 9 ⟨602898, by decide⟩
    (prefixPartial 12 76703) = some ⟨12, 2, 0, 602898, 76703, 2345, 65536⟩ := by
  decide +kernel

theorem context_12_76703_602898 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76703 ⟨602898, by decide⟩ :=
  accepted_of_selected 12 76703 ⟨602898, by decide⟩ ⟨12, 2, 0, 602898, 76703, 2345, 65536⟩
    (by decide) selected_cut_23867

theorem unmarked_context_11_19175_602899 : frontier 10 ⟨602899, by decide⟩
    (prefixCache 11 19175) (prefixPartial 11 19175) = false := by
  decide +kernel

theorem node_context_11_19175_602899 : EJMOriginalGlobalDAGData.nodes 10 ⟨602899, by decide⟩ =
    .split (coordinate 11) (![⟨602820, by decide⟩,⟨602841, by decide⟩,⟨602864, by decide⟩,⟨602898, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19175_602899 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19175 ⟨602899, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19175
    ⟨602899, by decide⟩ (by decide) (![⟨602820, by decide⟩,⟨602841, by decide⟩,⟨602864, by decide⟩,⟨602898, by decide⟩]) unmarked_context_11_19175_602899 node_context_11_19175_602899
  intro a
  fin_cases a
  · exact context_12_76700_602820
  · exact context_12_76701_602841
  · exact context_12_76702_602864
  · exact context_12_76703_602898

theorem unmarked_context_10_4793_602900 : frontier 11 ⟨602900, by decide⟩
    (prefixCache 10 4793) (prefixPartial 10 4793) = false := by
  decide +kernel

theorem node_context_10_4793_602900 : EJMOriginalGlobalDAGData.nodes 11 ⟨602900, by decide⟩ =
    .split (coordinate 10) (![⟨602602, by decide⟩,⟨602707, by decide⟩,⟨602801, by decide⟩,⟨602899, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4793_602900 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4793 ⟨602900, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4793
    ⟨602900, by decide⟩ (by decide) (![⟨602602, by decide⟩,⟨602707, by decide⟩,⟨602801, by decide⟩,⟨602899, by decide⟩]) unmarked_context_10_4793_602900 node_context_10_4793_602900
  intro a
  fin_cases a
  · exact context_11_19172_602602
  · exact context_11_19173_602707
  · exact context_11_19174_602801
  · exact context_11_19175_602899

theorem selected_cut_23868 : selected 9 ⟨602912, by decide⟩
    (prefixPartial 12 76704) = some ⟨12, 2, 0, 602912, 76704, 1333, 65536⟩ := by
  decide +kernel

theorem context_12_76704_602912 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76704 ⟨602912, by decide⟩ :=
  accepted_of_selected 12 76704 ⟨602912, by decide⟩ ⟨12, 2, 0, 602912, 76704, 1333, 65536⟩
    (by decide) selected_cut_23868

theorem selected_cut_23869 : selected 9 ⟨602927, by decide⟩
    (prefixPartial 12 76705) = some ⟨12, 2, 0, 602927, 76705, 1433, 65536⟩ := by
  decide +kernel

theorem context_12_76705_602927 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76705 ⟨602927, by decide⟩ :=
  accepted_of_selected 12 76705 ⟨602927, by decide⟩ ⟨12, 2, 0, 602927, 76705, 1433, 65536⟩
    (by decide) selected_cut_23869

theorem selected_cut_23870 : selected 9 ⟨602944, by decide⟩
    (prefixPartial 12 76706) = some ⟨12, 2, 0, 602944, 76706, 1481, 65536⟩ := by
  decide +kernel

theorem context_12_76706_602944 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76706 ⟨602944, by decide⟩ :=
  accepted_of_selected 12 76706 ⟨602944, by decide⟩ ⟨12, 2, 0, 602944, 76706, 1481, 65536⟩
    (by decide) selected_cut_23870

theorem selected_cut_23871 : selected 9 ⟨602957, by decide⟩
    (prefixPartial 12 76707) = some ⟨12, 2, 0, 602957, 76707, 1309, 65536⟩ := by
  decide +kernel

theorem context_12_76707_602957 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76707 ⟨602957, by decide⟩ :=
  accepted_of_selected 12 76707 ⟨602957, by decide⟩ ⟨12, 2, 0, 602957, 76707, 1309, 65536⟩
    (by decide) selected_cut_23871

theorem unmarked_context_11_19176_602958 : frontier 10 ⟨602958, by decide⟩
    (prefixCache 11 19176) (prefixPartial 11 19176) = false := by
  decide +kernel

theorem node_context_11_19176_602958 : EJMOriginalGlobalDAGData.nodes 10 ⟨602958, by decide⟩ =
    .split (coordinate 11) (![⟨602912, by decide⟩,⟨602927, by decide⟩,⟨602944, by decide⟩,⟨602957, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19176_602958 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19176 ⟨602958, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19176
    ⟨602958, by decide⟩ (by decide) (![⟨602912, by decide⟩,⟨602927, by decide⟩,⟨602944, by decide⟩,⟨602957, by decide⟩]) unmarked_context_11_19176_602958 node_context_11_19176_602958
  intro a
  fin_cases a
  · exact context_12_76704_602912
  · exact context_12_76705_602927
  · exact context_12_76706_602944
  · exact context_12_76707_602957

theorem selected_cut_23872 : selected 9 ⟨602972, by decide⟩
    (prefixPartial 12 76708) = some ⟨12, 2, 0, 602972, 76708, 1537, 65536⟩ := by
  decide +kernel

theorem context_12_76708_602972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76708 ⟨602972, by decide⟩ :=
  accepted_of_selected 12 76708 ⟨602972, by decide⟩ ⟨12, 2, 0, 602972, 76708, 1537, 65536⟩
    (by decide) selected_cut_23872

theorem selected_cut_23873 : selected 9 ⟨602986, by decide⟩
    (prefixPartial 12 76709) = some ⟨12, 2, 0, 602986, 76709, 1561, 65536⟩ := by
  decide +kernel

theorem context_12_76709_602986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76709 ⟨602986, by decide⟩ :=
  accepted_of_selected 12 76709 ⟨602986, by decide⟩ ⟨12, 2, 0, 602986, 76709, 1561, 65536⟩
    (by decide) selected_cut_23873

theorem selected_cut_23874 : selected 9 ⟨603001, by decide⟩
    (prefixPartial 12 76710) = some ⟨12, 2, 0, 603001, 76710, 1625, 65536⟩ := by
  decide +kernel

theorem context_12_76710_603001 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76710 ⟨603001, by decide⟩ :=
  accepted_of_selected 12 76710 ⟨603001, by decide⟩ ⟨12, 2, 0, 603001, 76710, 1625, 65536⟩
    (by decide) selected_cut_23874

theorem selected_cut_23875 : selected 9 ⟨603013, by decide⟩
    (prefixPartial 12 76711) = some ⟨12, 2, 0, 603013, 76711, 1413, 65536⟩ := by
  decide +kernel

theorem context_12_76711_603013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76711 ⟨603013, by decide⟩ :=
  accepted_of_selected 12 76711 ⟨603013, by decide⟩ ⟨12, 2, 0, 603013, 76711, 1413, 65536⟩
    (by decide) selected_cut_23875

theorem unmarked_context_11_19177_603014 : frontier 10 ⟨603014, by decide⟩
    (prefixCache 11 19177) (prefixPartial 11 19177) = false := by
  decide +kernel

theorem node_context_11_19177_603014 : EJMOriginalGlobalDAGData.nodes 10 ⟨603014, by decide⟩ =
    .split (coordinate 11) (![⟨602972, by decide⟩,⟨602986, by decide⟩,⟨603001, by decide⟩,⟨603013, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19177_603014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19177 ⟨603014, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19177
    ⟨603014, by decide⟩ (by decide) (![⟨602972, by decide⟩,⟨602986, by decide⟩,⟨603001, by decide⟩,⟨603013, by decide⟩]) unmarked_context_11_19177_603014 node_context_11_19177_603014
  intro a
  fin_cases a
  · exact context_12_76708_602972
  · exact context_12_76709_602986
  · exact context_12_76710_603001
  · exact context_12_76711_603013

theorem selected_cut_23876 : selected 10 ⟨479708, by decide⟩
    (prefixPartial 11 19178) = some ⟨11, 1, 0, 479708, 19178, 1, 262144⟩ := by
  decide +kernel

theorem context_11_19178_479708 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19178 ⟨479708, by decide⟩ :=
  accepted_of_selected 11 19178 ⟨479708, by decide⟩ ⟨11, 1, 0, 479708, 19178, 1, 262144⟩
    (by decide) selected_cut_23876

theorem selected_cut_23877 : selected 9 ⟨603026, by decide⟩
    (prefixPartial 12 76716) = some ⟨12, 2, 0, 603026, 76716, 1317, 65536⟩ := by
  decide +kernel

theorem context_12_76716_603026 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76716 ⟨603026, by decide⟩ :=
  accepted_of_selected 12 76716 ⟨603026, by decide⟩ ⟨12, 2, 0, 603026, 76716, 1317, 65536⟩
    (by decide) selected_cut_23877

theorem selected_cut_23878 : selected 9 ⟨603039, by decide⟩
    (prefixPartial 12 76717) = some ⟨12, 2, 0, 603039, 76717, 1401, 65536⟩ := by
  decide +kernel

theorem context_12_76717_603039 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76717 ⟨603039, by decide⟩ :=
  accepted_of_selected 12 76717 ⟨603039, by decide⟩ ⟨12, 2, 0, 603039, 76717, 1401, 65536⟩
    (by decide) selected_cut_23878

theorem selected_cut_23879 : selected 9 ⟨603048, by decide⟩
    (prefixPartial 12 76718) = some ⟨12, 2, 0, 603048, 76718, 1365, 65536⟩ := by
  decide +kernel

theorem context_12_76718_603048 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76718 ⟨603048, by decide⟩ :=
  accepted_of_selected 12 76718 ⟨603048, by decide⟩ ⟨12, 2, 0, 603048, 76718, 1365, 65536⟩
    (by decide) selected_cut_23879

theorem selected_cut_23880 : selected 9 ⟨603071, by decide⟩
    (prefixPartial 12 76719) = some ⟨12, 2, 0, 603071, 76719, 1761, 65536⟩ := by
  decide +kernel

theorem context_12_76719_603071 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76719 ⟨603071, by decide⟩ :=
  accepted_of_selected 12 76719 ⟨603071, by decide⟩ ⟨12, 2, 0, 603071, 76719, 1761, 65536⟩
    (by decide) selected_cut_23880

theorem unmarked_context_11_19179_603072 : frontier 10 ⟨603072, by decide⟩
    (prefixCache 11 19179) (prefixPartial 11 19179) = false := by
  decide +kernel

theorem node_context_11_19179_603072 : EJMOriginalGlobalDAGData.nodes 10 ⟨603072, by decide⟩ =
    .split (coordinate 11) (![⟨603026, by decide⟩,⟨603039, by decide⟩,⟨603048, by decide⟩,⟨603071, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19179_603072 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19179 ⟨603072, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19179
    ⟨603072, by decide⟩ (by decide) (![⟨603026, by decide⟩,⟨603039, by decide⟩,⟨603048, by decide⟩,⟨603071, by decide⟩]) unmarked_context_11_19179_603072 node_context_11_19179_603072
  intro a
  fin_cases a
  · exact context_12_76716_603026
  · exact context_12_76717_603039
  · exact context_12_76718_603048
  · exact context_12_76719_603071

theorem unmarked_context_10_4794_603073 : frontier 11 ⟨603073, by decide⟩
    (prefixCache 10 4794) (prefixPartial 10 4794) = false := by
  decide +kernel

theorem node_context_10_4794_603073 : EJMOriginalGlobalDAGData.nodes 11 ⟨603073, by decide⟩ =
    .split (coordinate 10) (![⟨602958, by decide⟩,⟨603014, by decide⟩,⟨479708, by decide⟩,⟨603072, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4794_603073 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4794 ⟨603073, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4794
    ⟨603073, by decide⟩ (by decide) (![⟨602958, by decide⟩,⟨603014, by decide⟩,⟨479708, by decide⟩,⟨603072, by decide⟩]) unmarked_context_10_4794_603073 node_context_10_4794_603073
  intro a
  fin_cases a
  · exact context_11_19176_602958
  · exact context_11_19177_603014
  · exact context_11_19178_479708
  · exact context_11_19179_603072

theorem selected_cut_23881 : selected 9 ⟨603088, by decide⟩
    (prefixPartial 12 76720) = some ⟨12, 2, 0, 603088, 76720, 1445, 65536⟩ := by
  decide +kernel

theorem context_12_76720_603088 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76720 ⟨603088, by decide⟩ :=
  accepted_of_selected 12 76720 ⟨603088, by decide⟩ ⟨12, 2, 0, 603088, 76720, 1445, 65536⟩
    (by decide) selected_cut_23881

theorem selected_cut_23882 : selected 9 ⟨603102, by decide⟩
    (prefixPartial 12 76721) = some ⟨12, 2, 0, 603102, 76721, 1501, 65536⟩ := by
  decide +kernel

theorem context_12_76721_603102 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76721 ⟨603102, by decide⟩ :=
  accepted_of_selected 12 76721 ⟨603102, by decide⟩ ⟨12, 2, 0, 603102, 76721, 1501, 65536⟩
    (by decide) selected_cut_23882

theorem selected_cut_23883 : selected 9 ⟨603124, by decide⟩
    (prefixPartial 12 76722) = some ⟨12, 2, 0, 603124, 76722, 1517, 65536⟩ := by
  decide +kernel

theorem context_12_76722_603124 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76722 ⟨603124, by decide⟩ :=
  accepted_of_selected 12 76722 ⟨603124, by decide⟩ ⟨12, 2, 0, 603124, 76722, 1517, 65536⟩
    (by decide) selected_cut_23883

theorem selected_cut_23884 : selected 9 ⟨603135, by decide⟩
    (prefixPartial 12 76723) = some ⟨12, 2, 0, 603135, 76723, 1209, 65536⟩ := by
  decide +kernel

theorem context_12_76723_603135 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76723 ⟨603135, by decide⟩ :=
  accepted_of_selected 12 76723 ⟨603135, by decide⟩ ⟨12, 2, 0, 603135, 76723, 1209, 65536⟩
    (by decide) selected_cut_23884

theorem unmarked_context_11_19180_603136 : frontier 10 ⟨603136, by decide⟩
    (prefixCache 11 19180) (prefixPartial 11 19180) = false := by
  decide +kernel

theorem node_context_11_19180_603136 : EJMOriginalGlobalDAGData.nodes 10 ⟨603136, by decide⟩ =
    .split (coordinate 11) (![⟨603088, by decide⟩,⟨603102, by decide⟩,⟨603124, by decide⟩,⟨603135, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19180_603136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19180 ⟨603136, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19180
    ⟨603136, by decide⟩ (by decide) (![⟨603088, by decide⟩,⟨603102, by decide⟩,⟨603124, by decide⟩,⟨603135, by decide⟩]) unmarked_context_11_19180_603136 node_context_11_19180_603136
  intro a
  fin_cases a
  · exact context_12_76720_603088
  · exact context_12_76721_603102
  · exact context_12_76722_603124
  · exact context_12_76723_603135

theorem selected_cut_23885 : selected 9 ⟨603157, by decide⟩
    (prefixPartial 12 76724) = some ⟨12, 2, 0, 603157, 76724, 1505, 65536⟩ := by
  decide +kernel

theorem context_12_76724_603157 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76724 ⟨603157, by decide⟩ :=
  accepted_of_selected 12 76724 ⟨603157, by decide⟩ ⟨12, 2, 0, 603157, 76724, 1505, 65536⟩
    (by decide) selected_cut_23885

theorem selected_cut_23886 : selected 9 ⟨603173, by decide⟩
    (prefixPartial 12 76725) = some ⟨12, 2, 0, 603173, 76725, 1457, 65536⟩ := by
  decide +kernel

theorem context_12_76725_603173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76725 ⟨603173, by decide⟩ :=
  accepted_of_selected 12 76725 ⟨603173, by decide⟩ ⟨12, 2, 0, 603173, 76725, 1457, 65536⟩
    (by decide) selected_cut_23886

theorem selected_cut_23887 : selected 9 ⟨603202, by decide⟩
    (prefixPartial 12 76726) = some ⟨12, 2, 0, 603202, 76726, 1609, 65536⟩ := by
  decide +kernel

theorem context_12_76726_603202 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76726 ⟨603202, by decide⟩ :=
  accepted_of_selected 12 76726 ⟨603202, by decide⟩ ⟨12, 2, 0, 603202, 76726, 1609, 65536⟩
    (by decide) selected_cut_23887

theorem selected_cut_23888 : selected 9 ⟨603213, by decide⟩
    (prefixPartial 12 76727) = some ⟨12, 2, 0, 603213, 76727, 1249, 65536⟩ := by
  decide +kernel

theorem context_12_76727_603213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76727 ⟨603213, by decide⟩ :=
  accepted_of_selected 12 76727 ⟨603213, by decide⟩ ⟨12, 2, 0, 603213, 76727, 1249, 65536⟩
    (by decide) selected_cut_23888

theorem unmarked_context_11_19181_603214 : frontier 10 ⟨603214, by decide⟩
    (prefixCache 11 19181) (prefixPartial 11 19181) = false := by
  decide +kernel

theorem node_context_11_19181_603214 : EJMOriginalGlobalDAGData.nodes 10 ⟨603214, by decide⟩ =
    .split (coordinate 11) (![⟨603157, by decide⟩,⟨603173, by decide⟩,⟨603202, by decide⟩,⟨603213, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19181_603214 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19181 ⟨603214, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19181
    ⟨603214, by decide⟩ (by decide) (![⟨603157, by decide⟩,⟨603173, by decide⟩,⟨603202, by decide⟩,⟨603213, by decide⟩]) unmarked_context_11_19181_603214 node_context_11_19181_603214
  intro a
  fin_cases a
  · exact context_12_76724_603157
  · exact context_12_76725_603173
  · exact context_12_76726_603202
  · exact context_12_76727_603213

theorem selected_cut_23889 : selected 9 ⟨603228, by decide⟩
    (prefixPartial 12 76728) = some ⟨12, 2, 0, 603228, 76728, 1233, 65536⟩ := by
  decide +kernel

theorem context_12_76728_603228 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76728 ⟨603228, by decide⟩ :=
  accepted_of_selected 12 76728 ⟨603228, by decide⟩ ⟨12, 2, 0, 603228, 76728, 1233, 65536⟩
    (by decide) selected_cut_23889

theorem selected_cut_23890 : selected 9 ⟨603245, by decide⟩
    (prefixPartial 12 76729) = some ⟨12, 2, 0, 603245, 76729, 1437, 65536⟩ := by
  decide +kernel

theorem context_12_76729_603245 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76729 ⟨603245, by decide⟩ :=
  accepted_of_selected 12 76729 ⟨603245, by decide⟩ ⟨12, 2, 0, 603245, 76729, 1437, 65536⟩
    (by decide) selected_cut_23890

theorem selected_cut_23891 : selected 9 ⟨603259, by decide⟩
    (prefixPartial 12 76730) = some ⟨12, 2, 0, 603259, 76730, 1245, 65536⟩ := by
  decide +kernel

theorem context_12_76730_603259 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76730 ⟨603259, by decide⟩ :=
  accepted_of_selected 12 76730 ⟨603259, by decide⟩ ⟨12, 2, 0, 603259, 76730, 1245, 65536⟩
    (by decide) selected_cut_23891

theorem selected_cut_23892 : selected 9 ⟨603268, by decide⟩
    (prefixPartial 12 76731) = some ⟨12, 2, 0, 603268, 76731, 1005, 65536⟩ := by
  decide +kernel

theorem context_12_76731_603268 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76731 ⟨603268, by decide⟩ :=
  accepted_of_selected 12 76731 ⟨603268, by decide⟩ ⟨12, 2, 0, 603268, 76731, 1005, 65536⟩
    (by decide) selected_cut_23892

theorem unmarked_context_11_19182_603269 : frontier 10 ⟨603269, by decide⟩
    (prefixCache 11 19182) (prefixPartial 11 19182) = false := by
  decide +kernel

theorem node_context_11_19182_603269 : EJMOriginalGlobalDAGData.nodes 10 ⟨603269, by decide⟩ =
    .split (coordinate 11) (![⟨603228, by decide⟩,⟨603245, by decide⟩,⟨603259, by decide⟩,⟨603268, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19182_603269 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19182 ⟨603269, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19182
    ⟨603269, by decide⟩ (by decide) (![⟨603228, by decide⟩,⟨603245, by decide⟩,⟨603259, by decide⟩,⟨603268, by decide⟩]) unmarked_context_11_19182_603269 node_context_11_19182_603269
  intro a
  fin_cases a
  · exact context_12_76728_603228
  · exact context_12_76729_603245
  · exact context_12_76730_603259
  · exact context_12_76731_603268

theorem selected_cut_23893 : selected 10 ⟨603310, by decide⟩
    (prefixPartial 11 19183) = some ⟨11, 2, 0, 603310, 19183, 3393, 262144⟩ := by
  decide +kernel

theorem context_11_19183_603310 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19183 ⟨603310, by decide⟩ :=
  accepted_of_selected 11 19183 ⟨603310, by decide⟩ ⟨11, 2, 0, 603310, 19183, 3393, 262144⟩
    (by decide) selected_cut_23893

theorem unmarked_context_10_4795_603311 : frontier 11 ⟨603311, by decide⟩
    (prefixCache 10 4795) (prefixPartial 10 4795) = false := by
  decide +kernel

theorem node_context_10_4795_603311 : EJMOriginalGlobalDAGData.nodes 11 ⟨603311, by decide⟩ =
    .split (coordinate 10) (![⟨603136, by decide⟩,⟨603214, by decide⟩,⟨603269, by decide⟩,⟨603310, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4795_603311 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4795 ⟨603311, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4795
    ⟨603311, by decide⟩ (by decide) (![⟨603136, by decide⟩,⟨603214, by decide⟩,⟨603269, by decide⟩,⟨603310, by decide⟩]) unmarked_context_10_4795_603311 node_context_10_4795_603311
  intro a
  fin_cases a
  · exact context_11_19180_603136
  · exact context_11_19181_603214
  · exact context_11_19182_603269
  · exact context_11_19183_603310

theorem unmarked_context_9_1198_603312 : frontier 12 ⟨603312, by decide⟩
    (prefixCache 9 1198) (prefixPartial 9 1198) = false := by
  decide +kernel

theorem node_context_9_1198_603312 : EJMOriginalGlobalDAGData.nodes 12 ⟨603312, by decide⟩ =
    .split (coordinate 9) (![⟨602498, by decide⟩,⟨602900, by decide⟩,⟨603073, by decide⟩,⟨603311, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1198_603312 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1198 ⟨603312, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1198
    ⟨603312, by decide⟩ (by decide) (![⟨602498, by decide⟩,⟨602900, by decide⟩,⟨603073, by decide⟩,⟨603311, by decide⟩]) unmarked_context_9_1198_603312 node_context_9_1198_603312
  intro a
  fin_cases a
  · exact context_10_4792_602498
  · exact context_10_4793_602900
  · exact context_10_4794_603073
  · exact context_10_4795_603311

theorem selected_cut_23894 : selected 10 ⟨603334, by decide⟩
    (prefixPartial 11 19184) = some ⟨11, 2, 0, 603334, 19184, 2529, 262144⟩ := by
  decide +kernel

theorem context_11_19184_603334 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19184 ⟨603334, by decide⟩ :=
  accepted_of_selected 11 19184 ⟨603334, by decide⟩ ⟨11, 2, 0, 603334, 19184, 2529, 262144⟩
    (by decide) selected_cut_23894

theorem selected_cut_23895 : selected 10 ⟨603358, by decide⟩
    (prefixPartial 11 19185) = some ⟨11, 2, 0, 603358, 19185, 2593, 262144⟩ := by
  decide +kernel

theorem context_11_19185_603358 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19185 ⟨603358, by decide⟩ :=
  accepted_of_selected 11 19185 ⟨603358, by decide⟩ ⟨11, 2, 0, 603358, 19185, 2593, 262144⟩
    (by decide) selected_cut_23895

theorem selected_cut_23896 : selected 10 ⟨603391, by decide⟩
    (prefixPartial 11 19186) = some ⟨11, 2, 0, 603391, 19186, 2441, 262144⟩ := by
  decide +kernel

theorem context_11_19186_603391 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19186 ⟨603391, by decide⟩ :=
  accepted_of_selected 11 19186 ⟨603391, by decide⟩ ⟨11, 2, 0, 603391, 19186, 2441, 262144⟩
    (by decide) selected_cut_23896

theorem selected_cut_23897 : selected 10 ⟨603408, by decide⟩
    (prefixPartial 11 19187) = some ⟨11, 2, 0, 603408, 19187, 1849, 262144⟩ := by
  decide +kernel

theorem context_11_19187_603408 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19187 ⟨603408, by decide⟩ :=
  accepted_of_selected 11 19187 ⟨603408, by decide⟩ ⟨11, 2, 0, 603408, 19187, 1849, 262144⟩
    (by decide) selected_cut_23897

theorem unmarked_context_10_4796_603409 : frontier 11 ⟨603409, by decide⟩
    (prefixCache 10 4796) (prefixPartial 10 4796) = false := by
  decide +kernel

theorem node_context_10_4796_603409 : EJMOriginalGlobalDAGData.nodes 11 ⟨603409, by decide⟩ =
    .split (coordinate 10) (![⟨603334, by decide⟩,⟨603358, by decide⟩,⟨603391, by decide⟩,⟨603408, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4796_603409 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4796 ⟨603409, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4796
    ⟨603409, by decide⟩ (by decide) (![⟨603334, by decide⟩,⟨603358, by decide⟩,⟨603391, by decide⟩,⟨603408, by decide⟩]) unmarked_context_10_4796_603409 node_context_10_4796_603409
  intro a
  fin_cases a
  · exact context_11_19184_603334
  · exact context_11_19185_603358
  · exact context_11_19186_603391
  · exact context_11_19187_603408

theorem selected_cut_23898 : selected 10 ⟨603437, by decide⟩
    (prefixPartial 11 19188) = some ⟨11, 2, 0, 603437, 19188, 2421, 262144⟩ := by
  decide +kernel

theorem context_11_19188_603437 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19188 ⟨603437, by decide⟩ :=
  accepted_of_selected 11 19188 ⟨603437, by decide⟩ ⟨11, 2, 0, 603437, 19188, 2421, 262144⟩
    (by decide) selected_cut_23898

theorem selected_cut_23899 : selected 10 ⟨603463, by decide⟩
    (prefixPartial 11 19189) = some ⟨11, 2, 0, 603463, 19189, 2621, 262144⟩ := by
  decide +kernel

theorem context_11_19189_603463 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19189 ⟨603463, by decide⟩ :=
  accepted_of_selected 11 19189 ⟨603463, by decide⟩ ⟨11, 2, 0, 603463, 19189, 2621, 262144⟩
    (by decide) selected_cut_23899

theorem selected_cut_23900 : selected 10 ⟨603487, by decide⟩
    (prefixPartial 11 19190) = some ⟨11, 2, 0, 603487, 19190, 2173, 262144⟩ := by
  decide +kernel

theorem context_11_19190_603487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19190 ⟨603487, by decide⟩ :=
  accepted_of_selected 11 19190 ⟨603487, by decide⟩ ⟨11, 2, 0, 603487, 19190, 2173, 262144⟩
    (by decide) selected_cut_23900

theorem selected_cut_23901 : selected 10 ⟨603506, by decide⟩
    (prefixPartial 11 19191) = some ⟨11, 2, 0, 603506, 19191, 1513, 262144⟩ := by
  decide +kernel

theorem context_11_19191_603506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19191 ⟨603506, by decide⟩ :=
  accepted_of_selected 11 19191 ⟨603506, by decide⟩ ⟨11, 2, 0, 603506, 19191, 1513, 262144⟩
    (by decide) selected_cut_23901

theorem unmarked_context_10_4797_603507 : frontier 11 ⟨603507, by decide⟩
    (prefixCache 10 4797) (prefixPartial 10 4797) = false := by
  decide +kernel

theorem node_context_10_4797_603507 : EJMOriginalGlobalDAGData.nodes 11 ⟨603507, by decide⟩ =
    .split (coordinate 10) (![⟨603437, by decide⟩,⟨603463, by decide⟩,⟨603487, by decide⟩,⟨603506, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4797_603507 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4797 ⟨603507, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4797
    ⟨603507, by decide⟩ (by decide) (![⟨603437, by decide⟩,⟨603463, by decide⟩,⟨603487, by decide⟩,⟨603506, by decide⟩]) unmarked_context_10_4797_603507 node_context_10_4797_603507
  intro a
  fin_cases a
  · exact context_11_19188_603437
  · exact context_11_19189_603463
  · exact context_11_19190_603487
  · exact context_11_19191_603506

theorem selected_cut_23902 : selected 10 ⟨603525, by decide⟩
    (prefixPartial 11 19192) = some ⟨11, 2, 0, 603525, 19192, 1377, 262144⟩ := by
  decide +kernel

theorem context_11_19192_603525 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19192 ⟨603525, by decide⟩ :=
  accepted_of_selected 11 19192 ⟨603525, by decide⟩ ⟨11, 2, 0, 603525, 19192, 1377, 262144⟩
    (by decide) selected_cut_23902

theorem selected_cut_23903 : selected 10 ⟨603539, by decide⟩
    (prefixPartial 11 19193) = some ⟨11, 2, 0, 603539, 19193, 1413, 262144⟩ := by
  decide +kernel

theorem context_11_19193_603539 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19193 ⟨603539, by decide⟩ :=
  accepted_of_selected 11 19193 ⟨603539, by decide⟩ ⟨11, 2, 0, 603539, 19193, 1413, 262144⟩
    (by decide) selected_cut_23903

theorem selected_cut_23904 : selected 10 ⟨603551, by decide⟩
    (prefixPartial 11 19194) = some ⟨11, 2, 0, 603551, 19194, 905, 262144⟩ := by
  decide +kernel

theorem context_11_19194_603551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19194 ⟨603551, by decide⟩ :=
  accepted_of_selected 11 19194 ⟨603551, by decide⟩ ⟨11, 2, 0, 603551, 19194, 905, 262144⟩
    (by decide) selected_cut_23904

theorem selected_cut_23905 : selected 10 ⟨603562, by decide⟩
    (prefixPartial 11 19195) = some ⟨11, 2, 0, 603562, 19195, 693, 262144⟩ := by
  decide +kernel

theorem context_11_19195_603562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19195 ⟨603562, by decide⟩ :=
  accepted_of_selected 11 19195 ⟨603562, by decide⟩ ⟨11, 2, 0, 603562, 19195, 693, 262144⟩
    (by decide) selected_cut_23905

theorem unmarked_context_10_4798_603563 : frontier 11 ⟨603563, by decide⟩
    (prefixCache 10 4798) (prefixPartial 10 4798) = false := by
  decide +kernel

theorem node_context_10_4798_603563 : EJMOriginalGlobalDAGData.nodes 11 ⟨603563, by decide⟩ =
    .split (coordinate 10) (![⟨603525, by decide⟩,⟨603539, by decide⟩,⟨603551, by decide⟩,⟨603562, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4798_603563 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4798 ⟨603563, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4798
    ⟨603563, by decide⟩ (by decide) (![⟨603525, by decide⟩,⟨603539, by decide⟩,⟨603551, by decide⟩,⟨603562, by decide⟩]) unmarked_context_10_4798_603563 node_context_10_4798_603563
  intro a
  fin_cases a
  · exact context_11_19192_603525
  · exact context_11_19193_603539
  · exact context_11_19194_603551
  · exact context_11_19195_603562

theorem selected_cut_23906 : selected 11 ⟨603598, by decide⟩
    (prefixPartial 10 4799) = some ⟨10, 2, 0, 603598, 4799, 1529, 1048576⟩ := by
  decide +kernel

theorem context_10_4799_603598 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4799 ⟨603598, by decide⟩ :=
  accepted_of_selected 10 4799 ⟨603598, by decide⟩ ⟨10, 2, 0, 603598, 4799, 1529, 1048576⟩
    (by decide) selected_cut_23906

theorem unmarked_context_9_1199_603599 : frontier 12 ⟨603599, by decide⟩
    (prefixCache 9 1199) (prefixPartial 9 1199) = false := by
  decide +kernel

theorem node_context_9_1199_603599 : EJMOriginalGlobalDAGData.nodes 12 ⟨603599, by decide⟩ =
    .split (coordinate 9) (![⟨603409, by decide⟩,⟨603507, by decide⟩,⟨603563, by decide⟩,⟨603598, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1199_603599 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1199 ⟨603599, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1199
    ⟨603599, by decide⟩ (by decide) (![⟨603409, by decide⟩,⟨603507, by decide⟩,⟨603563, by decide⟩,⟨603598, by decide⟩]) unmarked_context_9_1199_603599 node_context_9_1199_603599
  intro a
  fin_cases a
  · exact context_10_4796_603409
  · exact context_10_4797_603507
  · exact context_10_4798_603563
  · exact context_10_4799_603598

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
