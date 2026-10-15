/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover254
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_24484 : selected 8 ⟨618480, by decide⟩
    (prefixPartial 13 308623) = some ⟨13, 2, 0, 618480, 308623, 1033, 16384⟩ := by
  decide +kernel

theorem context_13_308623_618480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308623 ⟨618480, by decide⟩ :=
  accepted_of_selected 13 308623 ⟨618480, by decide⟩ ⟨13, 2, 0, 618480, 308623, 1033, 16384⟩
    (by decide) selected_cut_24484

theorem unmarked_context_12_77155_618481 : frontier 9 ⟨618481, by decide⟩
    (prefixCache 12 77155) (prefixPartial 12 77155) = false := by
  decide +kernel

theorem node_context_12_77155_618481 : EJMOriginalGlobalDAGData.nodes 9 ⟨618481, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨618442, by decide⟩,⟨618471, by decide⟩,⟨618480, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77155_618481 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77155 ⟨618481, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77155
    ⟨618481, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨618442, by decide⟩,⟨618471, by decide⟩,⟨618480, by decide⟩]) unmarked_context_12_77155_618481 node_context_12_77155_618481
  intro a
  fin_cases a
  · exact context_13_308620_3444
  · exact context_13_308621_618442
  · exact context_13_308622_618471
  · exact context_13_308623_618480

theorem unmarked_context_11_19288_618482 : frontier 10 ⟨618482, by decide⟩
    (prefixCache 11 19288) (prefixPartial 11 19288) = false := by
  decide +kernel

theorem node_context_11_19288_618482 : EJMOriginalGlobalDAGData.nodes 10 ⟨618482, by decide⟩ =
    .split (coordinate 11) (![⟨618335, by decide⟩,⟨618383, by decide⟩,⟨618429, by decide⟩,⟨618481, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19288_618482 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19288 ⟨618482, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19288
    ⟨618482, by decide⟩ (by decide) (![⟨618335, by decide⟩,⟨618383, by decide⟩,⟨618429, by decide⟩,⟨618481, by decide⟩]) unmarked_context_11_19288_618482 node_context_11_19288_618482
  intro a
  fin_cases a
  · exact context_12_77152_618335
  · exact context_12_77153_618383
  · exact context_12_77154_618429
  · exact context_12_77155_618481

theorem selected_cut_24485 : selected 9 ⟨618527, by decide⟩
    (prefixPartial 12 77156) = some ⟨12, 2, 0, 618527, 77156, 3401, 65536⟩ := by
  decide +kernel

theorem context_12_77156_618527 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77156 ⟨618527, by decide⟩ :=
  accepted_of_selected 12 77156 ⟨618527, by decide⟩ ⟨12, 2, 0, 618527, 77156, 3401, 65536⟩
    (by decide) selected_cut_24485

theorem selected_cut_24486 : selected 9 ⟨441672, by decide⟩
    (prefixPartial 12 77157) = some ⟨12, 1, 0, 441672, 77157, 1, 65536⟩ := by
  decide +kernel

theorem context_12_77157_441672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77157 ⟨441672, by decide⟩ :=
  accepted_of_selected 12 77157 ⟨441672, by decide⟩ ⟨12, 1, 0, 441672, 77157, 1, 65536⟩
    (by decide) selected_cut_24486

theorem selected_cut_24487 : selected 9 ⟨618579, by decide⟩
    (prefixPartial 12 77158) = some ⟨12, 2, 0, 618579, 77158, 3933, 65536⟩ := by
  decide +kernel

theorem context_12_77158_618579 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77158 ⟨618579, by decide⟩ :=
  accepted_of_selected 12 77158 ⟨618579, by decide⟩ ⟨12, 2, 0, 618579, 77158, 3933, 65536⟩
    (by decide) selected_cut_24487

theorem selected_cut_24488 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 308636) = some ⟨13, 1, 0, 3444, 308636, 1, 16384⟩ := by
  decide +kernel

theorem context_13_308636_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308636 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 308636 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 308636, 1, 16384⟩
    (by decide) selected_cut_24488

theorem selected_cut_24489 : selected 8 ⟨618592, by decide⟩
    (prefixPartial 13 308637) = some ⟨13, 2, 0, 618592, 308637, 945, 16384⟩ := by
  decide +kernel

theorem context_13_308637_618592 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308637 ⟨618592, by decide⟩ :=
  accepted_of_selected 13 308637 ⟨618592, by decide⟩ ⟨13, 2, 0, 618592, 308637, 945, 16384⟩
    (by decide) selected_cut_24489

theorem selected_cut_24490 : selected 8 ⟨618626, by decide⟩
    (prefixPartial 13 308638) = some ⟨13, 2, 0, 618626, 308638, 2205, 16384⟩ := by
  decide +kernel

theorem context_13_308638_618626 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308638 ⟨618626, by decide⟩ :=
  accepted_of_selected 13 308638 ⟨618626, by decide⟩ ⟨13, 2, 0, 618626, 308638, 2205, 16384⟩
    (by decide) selected_cut_24490

theorem selected_cut_24491 : selected 8 ⟨618635, by decide⟩
    (prefixPartial 13 308639) = some ⟨13, 2, 0, 618635, 308639, 1021, 16384⟩ := by
  decide +kernel

theorem context_13_308639_618635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308639 ⟨618635, by decide⟩ :=
  accepted_of_selected 13 308639 ⟨618635, by decide⟩ ⟨13, 2, 0, 618635, 308639, 1021, 16384⟩
    (by decide) selected_cut_24491

theorem unmarked_context_12_77159_618636 : frontier 9 ⟨618636, by decide⟩
    (prefixCache 12 77159) (prefixPartial 12 77159) = false := by
  decide +kernel

theorem node_context_12_77159_618636 : EJMOriginalGlobalDAGData.nodes 9 ⟨618636, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨618592, by decide⟩,⟨618626, by decide⟩,⟨618635, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77159_618636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77159 ⟨618636, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77159
    ⟨618636, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨618592, by decide⟩,⟨618626, by decide⟩,⟨618635, by decide⟩]) unmarked_context_12_77159_618636 node_context_12_77159_618636
  intro a
  fin_cases a
  · exact context_13_308636_3444
  · exact context_13_308637_618592
  · exact context_13_308638_618626
  · exact context_13_308639_618635

theorem unmarked_context_11_19289_618637 : frontier 10 ⟨618637, by decide⟩
    (prefixCache 11 19289) (prefixPartial 11 19289) = false := by
  decide +kernel

theorem node_context_11_19289_618637 : EJMOriginalGlobalDAGData.nodes 10 ⟨618637, by decide⟩ =
    .split (coordinate 11) (![⟨618527, by decide⟩,⟨441672, by decide⟩,⟨618579, by decide⟩,⟨618636, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19289_618637 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19289 ⟨618637, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19289
    ⟨618637, by decide⟩ (by decide) (![⟨618527, by decide⟩,⟨441672, by decide⟩,⟨618579, by decide⟩,⟨618636, by decide⟩]) unmarked_context_11_19289_618637 node_context_11_19289_618637
  intro a
  fin_cases a
  · exact context_12_77156_618527
  · exact context_12_77157_441672
  · exact context_12_77158_618579
  · exact context_12_77159_618636

theorem selected_cut_24492 : selected 9 ⟨618686, by decide⟩
    (prefixPartial 12 77160) = some ⟨12, 2, 0, 618686, 77160, 3605, 65536⟩ := by
  decide +kernel

theorem context_12_77160_618686 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77160 ⟨618686, by decide⟩ :=
  accepted_of_selected 12 77160 ⟨618686, by decide⟩ ⟨12, 2, 0, 618686, 77160, 3605, 65536⟩
    (by decide) selected_cut_24492

theorem selected_cut_24493 : selected 9 ⟨618735, by decide⟩
    (prefixPartial 12 77161) = some ⟨12, 2, 0, 618735, 77161, 3613, 65536⟩ := by
  decide +kernel

theorem context_12_77161_618735 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77161 ⟨618735, by decide⟩ :=
  accepted_of_selected 12 77161 ⟨618735, by decide⟩ ⟨12, 2, 0, 618735, 77161, 3613, 65536⟩
    (by decide) selected_cut_24493

theorem selected_cut_24494 : selected 9 ⟨618790, by decide⟩
    (prefixPartial 12 77162) = some ⟨12, 2, 0, 618790, 77162, 3897, 65536⟩ := by
  decide +kernel

theorem context_12_77162_618790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77162 ⟨618790, by decide⟩ :=
  accepted_of_selected 12 77162 ⟨618790, by decide⟩ ⟨12, 2, 0, 618790, 77162, 3897, 65536⟩
    (by decide) selected_cut_24494

theorem selected_cut_24495 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 308652) = some ⟨13, 1, 0, 3444, 308652, 1, 16384⟩ := by
  decide +kernel

theorem context_13_308652_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308652 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 308652 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 308652, 1, 16384⟩
    (by decide) selected_cut_24495

theorem selected_cut_24496 : selected 8 ⟨618802, by decide⟩
    (prefixPartial 13 308653) = some ⟨13, 2, 0, 618802, 308653, 873, 16384⟩ := by
  decide +kernel

theorem context_13_308653_618802 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308653 ⟨618802, by decide⟩ :=
  accepted_of_selected 13 308653 ⟨618802, by decide⟩ ⟨13, 2, 0, 618802, 308653, 873, 16384⟩
    (by decide) selected_cut_24496

theorem selected_cut_24497 : selected 8 ⟨618839, by decide⟩
    (prefixPartial 13 308654) = some ⟨13, 2, 0, 618839, 308654, 2273, 16384⟩ := by
  decide +kernel

theorem context_13_308654_618839 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308654 ⟨618839, by decide⟩ :=
  accepted_of_selected 13 308654 ⟨618839, by decide⟩ ⟨13, 2, 0, 618839, 308654, 2273, 16384⟩
    (by decide) selected_cut_24497

theorem selected_cut_24498 : selected 8 ⟨618859, by decide⟩
    (prefixPartial 13 308655) = some ⟨13, 2, 0, 618859, 308655, 1109, 16384⟩ := by
  decide +kernel

theorem context_13_308655_618859 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 308655 ⟨618859, by decide⟩ :=
  accepted_of_selected 13 308655 ⟨618859, by decide⟩ ⟨13, 2, 0, 618859, 308655, 1109, 16384⟩
    (by decide) selected_cut_24498

theorem unmarked_context_12_77163_618860 : frontier 9 ⟨618860, by decide⟩
    (prefixCache 12 77163) (prefixPartial 12 77163) = false := by
  decide +kernel

theorem node_context_12_77163_618860 : EJMOriginalGlobalDAGData.nodes 9 ⟨618860, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨618802, by decide⟩,⟨618839, by decide⟩,⟨618859, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77163_618860 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77163 ⟨618860, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77163
    ⟨618860, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨618802, by decide⟩,⟨618839, by decide⟩,⟨618859, by decide⟩]) unmarked_context_12_77163_618860 node_context_12_77163_618860
  intro a
  fin_cases a
  · exact context_13_308652_3444
  · exact context_13_308653_618802
  · exact context_13_308654_618839
  · exact context_13_308655_618859

theorem unmarked_context_11_19290_618861 : frontier 10 ⟨618861, by decide⟩
    (prefixCache 11 19290) (prefixPartial 11 19290) = false := by
  decide +kernel

theorem node_context_11_19290_618861 : EJMOriginalGlobalDAGData.nodes 10 ⟨618861, by decide⟩ =
    .split (coordinate 11) (![⟨618686, by decide⟩,⟨618735, by decide⟩,⟨618790, by decide⟩,⟨618860, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19290_618861 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19290 ⟨618861, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19290
    ⟨618861, by decide⟩ (by decide) (![⟨618686, by decide⟩,⟨618735, by decide⟩,⟨618790, by decide⟩,⟨618860, by decide⟩]) unmarked_context_11_19290_618861 node_context_11_19290_618861
  intro a
  fin_cases a
  · exact context_12_77160_618686
  · exact context_12_77161_618735
  · exact context_12_77162_618790
  · exact context_12_77163_618860

theorem selected_cut_24499 : selected 9 ⟨618896, by decide⟩
    (prefixPartial 12 77164) = some ⟨12, 2, 0, 618896, 77164, 3417, 65536⟩ := by
  decide +kernel

theorem context_12_77164_618896 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77164 ⟨618896, by decide⟩ :=
  accepted_of_selected 12 77164 ⟨618896, by decide⟩ ⟨12, 2, 0, 618896, 77164, 3417, 65536⟩
    (by decide) selected_cut_24499

theorem selected_cut_24500 : selected 9 ⟨618935, by decide⟩
    (prefixPartial 12 77165) = some ⟨12, 2, 0, 618935, 77165, 3269, 65536⟩ := by
  decide +kernel

theorem context_12_77165_618935 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77165 ⟨618935, by decide⟩ :=
  accepted_of_selected 12 77165 ⟨618935, by decide⟩ ⟨12, 2, 0, 618935, 77165, 3269, 65536⟩
    (by decide) selected_cut_24500

theorem selected_cut_24501 : selected 9 ⟨618976, by decide⟩
    (prefixPartial 12 77166) = some ⟨12, 2, 0, 618976, 77166, 3761, 65536⟩ := by
  decide +kernel

theorem context_12_77166_618976 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77166 ⟨618976, by decide⟩ :=
  accepted_of_selected 12 77166 ⟨618976, by decide⟩ ⟨12, 2, 0, 618976, 77166, 3761, 65536⟩
    (by decide) selected_cut_24501

theorem selected_cut_24502 : selected 9 ⟨619020, by decide⟩
    (prefixPartial 12 77167) = some ⟨12, 2, 0, 619020, 77167, 3853, 65536⟩ := by
  decide +kernel

theorem context_12_77167_619020 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77167 ⟨619020, by decide⟩ :=
  accepted_of_selected 12 77167 ⟨619020, by decide⟩ ⟨12, 2, 0, 619020, 77167, 3853, 65536⟩
    (by decide) selected_cut_24502

theorem unmarked_context_11_19291_619021 : frontier 10 ⟨619021, by decide⟩
    (prefixCache 11 19291) (prefixPartial 11 19291) = false := by
  decide +kernel

theorem node_context_11_19291_619021 : EJMOriginalGlobalDAGData.nodes 10 ⟨619021, by decide⟩ =
    .split (coordinate 11) (![⟨618896, by decide⟩,⟨618935, by decide⟩,⟨618976, by decide⟩,⟨619020, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19291_619021 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19291 ⟨619021, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19291
    ⟨619021, by decide⟩ (by decide) (![⟨618896, by decide⟩,⟨618935, by decide⟩,⟨618976, by decide⟩,⟨619020, by decide⟩]) unmarked_context_11_19291_619021 node_context_11_19291_619021
  intro a
  fin_cases a
  · exact context_12_77164_618896
  · exact context_12_77165_618935
  · exact context_12_77166_618976
  · exact context_12_77167_619020

theorem unmarked_context_10_4822_619022 : frontier 11 ⟨619022, by decide⟩
    (prefixCache 10 4822) (prefixPartial 10 4822) = false := by
  decide +kernel

theorem node_context_10_4822_619022 : EJMOriginalGlobalDAGData.nodes 11 ⟨619022, by decide⟩ =
    .split (coordinate 10) (![⟨618482, by decide⟩,⟨618637, by decide⟩,⟨618861, by decide⟩,⟨619021, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4822_619022 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4822 ⟨619022, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4822
    ⟨619022, by decide⟩ (by decide) (![⟨618482, by decide⟩,⟨618637, by decide⟩,⟨618861, by decide⟩,⟨619021, by decide⟩]) unmarked_context_10_4822_619022 node_context_10_4822_619022
  intro a
  fin_cases a
  · exact context_11_19288_618482
  · exact context_11_19289_618637
  · exact context_11_19290_618861
  · exact context_11_19291_619021

theorem selected_cut_24503 : selected 9 ⟨619064, by decide⟩
    (prefixPartial 12 77168) = some ⟨12, 2, 0, 619064, 77168, 3209, 65536⟩ := by
  decide +kernel

theorem context_12_77168_619064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77168 ⟨619064, by decide⟩ :=
  accepted_of_selected 12 77168 ⟨619064, by decide⟩ ⟨12, 2, 0, 619064, 77168, 3209, 65536⟩
    (by decide) selected_cut_24503

theorem selected_cut_24504 : selected 9 ⟨619108, by decide⟩
    (prefixPartial 12 77169) = some ⟨12, 2, 0, 619108, 77169, 3249, 65536⟩ := by
  decide +kernel

theorem context_12_77169_619108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77169 ⟨619108, by decide⟩ :=
  accepted_of_selected 12 77169 ⟨619108, by decide⟩ ⟨12, 2, 0, 619108, 77169, 3249, 65536⟩
    (by decide) selected_cut_24504

theorem selected_cut_24505 : selected 9 ⟨619148, by decide⟩
    (prefixPartial 12 77170) = some ⟨12, 2, 0, 619148, 77170, 3845, 65536⟩ := by
  decide +kernel

theorem context_12_77170_619148 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77170 ⟨619148, by decide⟩ :=
  accepted_of_selected 12 77170 ⟨619148, by decide⟩ ⟨12, 2, 0, 619148, 77170, 3845, 65536⟩
    (by decide) selected_cut_24505

theorem selected_cut_24506 : selected 9 ⟨619201, by decide⟩
    (prefixPartial 12 77171) = some ⟨12, 2, 0, 619201, 77171, 3673, 65536⟩ := by
  decide +kernel

theorem context_12_77171_619201 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77171 ⟨619201, by decide⟩ :=
  accepted_of_selected 12 77171 ⟨619201, by decide⟩ ⟨12, 2, 0, 619201, 77171, 3673, 65536⟩
    (by decide) selected_cut_24506

theorem unmarked_context_11_19292_619202 : frontier 10 ⟨619202, by decide⟩
    (prefixCache 11 19292) (prefixPartial 11 19292) = false := by
  decide +kernel

theorem node_context_11_19292_619202 : EJMOriginalGlobalDAGData.nodes 10 ⟨619202, by decide⟩ =
    .split (coordinate 11) (![⟨619064, by decide⟩,⟨619108, by decide⟩,⟨619148, by decide⟩,⟨619201, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19292_619202 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19292 ⟨619202, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19292
    ⟨619202, by decide⟩ (by decide) (![⟨619064, by decide⟩,⟨619108, by decide⟩,⟨619148, by decide⟩,⟨619201, by decide⟩]) unmarked_context_11_19292_619202 node_context_11_19292_619202
  intro a
  fin_cases a
  · exact context_12_77168_619064
  · exact context_12_77169_619108
  · exact context_12_77170_619148
  · exact context_12_77171_619201

theorem selected_cut_24507 : selected 9 ⟨619239, by decide⟩
    (prefixPartial 12 77172) = some ⟨12, 2, 0, 619239, 77172, 2837, 65536⟩ := by
  decide +kernel

theorem context_12_77172_619239 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77172 ⟨619239, by decide⟩ :=
  accepted_of_selected 12 77172 ⟨619239, by decide⟩ ⟨12, 2, 0, 619239, 77172, 2837, 65536⟩
    (by decide) selected_cut_24507

theorem selected_cut_24508 : selected 9 ⟨441672, by decide⟩
    (prefixPartial 12 77173) = some ⟨12, 1, 0, 441672, 77173, 1, 65536⟩ := by
  decide +kernel

theorem context_12_77173_441672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77173 ⟨441672, by decide⟩ :=
  accepted_of_selected 12 77173 ⟨441672, by decide⟩ ⟨12, 1, 0, 441672, 77173, 1, 65536⟩
    (by decide) selected_cut_24508

theorem selected_cut_24509 : selected 9 ⟨619276, by decide⟩
    (prefixPartial 12 77174) = some ⟨12, 2, 0, 619276, 77174, 3437, 65536⟩ := by
  decide +kernel

theorem context_12_77174_619276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77174 ⟨619276, by decide⟩ :=
  accepted_of_selected 12 77174 ⟨619276, by decide⟩ ⟨12, 2, 0, 619276, 77174, 3437, 65536⟩
    (by decide) selected_cut_24509

theorem selected_cut_24510 : selected 9 ⟨619322, by decide⟩
    (prefixPartial 12 77175) = some ⟨12, 2, 0, 619322, 77175, 3321, 65536⟩ := by
  decide +kernel

theorem context_12_77175_619322 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77175 ⟨619322, by decide⟩ :=
  accepted_of_selected 12 77175 ⟨619322, by decide⟩ ⟨12, 2, 0, 619322, 77175, 3321, 65536⟩
    (by decide) selected_cut_24510

theorem unmarked_context_11_19293_619323 : frontier 10 ⟨619323, by decide⟩
    (prefixCache 11 19293) (prefixPartial 11 19293) = false := by
  decide +kernel

theorem node_context_11_19293_619323 : EJMOriginalGlobalDAGData.nodes 10 ⟨619323, by decide⟩ =
    .split (coordinate 11) (![⟨619239, by decide⟩,⟨441672, by decide⟩,⟨619276, by decide⟩,⟨619322, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19293_619323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19293 ⟨619323, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19293
    ⟨619323, by decide⟩ (by decide) (![⟨619239, by decide⟩,⟨441672, by decide⟩,⟨619276, by decide⟩,⟨619322, by decide⟩]) unmarked_context_11_19293_619323 node_context_11_19293_619323
  intro a
  fin_cases a
  · exact context_12_77172_619239
  · exact context_12_77173_441672
  · exact context_12_77174_619276
  · exact context_12_77175_619322

theorem selected_cut_24511 : selected 9 ⟨619368, by decide⟩
    (prefixPartial 12 77176) = some ⟨12, 2, 0, 619368, 77176, 2925, 65536⟩ := by
  decide +kernel

theorem context_12_77176_619368 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77176 ⟨619368, by decide⟩ :=
  accepted_of_selected 12 77176 ⟨619368, by decide⟩ ⟨12, 2, 0, 619368, 77176, 2925, 65536⟩
    (by decide) selected_cut_24511

theorem selected_cut_24512 : selected 9 ⟨619407, by decide⟩
    (prefixPartial 12 77177) = some ⟨12, 2, 0, 619407, 77177, 3101, 65536⟩ := by
  decide +kernel

theorem context_12_77177_619407 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77177 ⟨619407, by decide⟩ :=
  accepted_of_selected 12 77177 ⟨619407, by decide⟩ ⟨12, 2, 0, 619407, 77177, 3101, 65536⟩
    (by decide) selected_cut_24512

theorem selected_cut_24513 : selected 9 ⟨619444, by decide⟩
    (prefixPartial 12 77178) = some ⟨12, 2, 0, 619444, 77178, 3261, 65536⟩ := by
  decide +kernel

theorem context_12_77178_619444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77178 ⟨619444, by decide⟩ :=
  accepted_of_selected 12 77178 ⟨619444, by decide⟩ ⟨12, 2, 0, 619444, 77178, 3261, 65536⟩
    (by decide) selected_cut_24513

theorem selected_cut_24514 : selected 9 ⟨619496, by decide⟩
    (prefixPartial 12 77179) = some ⟨12, 2, 0, 619496, 77179, 3229, 65536⟩ := by
  decide +kernel

theorem context_12_77179_619496 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77179 ⟨619496, by decide⟩ :=
  accepted_of_selected 12 77179 ⟨619496, by decide⟩ ⟨12, 2, 0, 619496, 77179, 3229, 65536⟩
    (by decide) selected_cut_24514

theorem unmarked_context_11_19294_619497 : frontier 10 ⟨619497, by decide⟩
    (prefixCache 11 19294) (prefixPartial 11 19294) = false := by
  decide +kernel

theorem node_context_11_19294_619497 : EJMOriginalGlobalDAGData.nodes 10 ⟨619497, by decide⟩ =
    .split (coordinate 11) (![⟨619368, by decide⟩,⟨619407, by decide⟩,⟨619444, by decide⟩,⟨619496, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19294_619497 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19294 ⟨619497, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19294
    ⟨619497, by decide⟩ (by decide) (![⟨619368, by decide⟩,⟨619407, by decide⟩,⟨619444, by decide⟩,⟨619496, by decide⟩]) unmarked_context_11_19294_619497 node_context_11_19294_619497
  intro a
  fin_cases a
  · exact context_12_77176_619368
  · exact context_12_77177_619407
  · exact context_12_77178_619444
  · exact context_12_77179_619496

theorem selected_cut_24515 : selected 9 ⟨619568, by decide⟩
    (prefixPartial 12 77180) = some ⟨12, 2, 0, 619568, 77180, 3677, 65536⟩ := by
  decide +kernel

theorem context_12_77180_619568 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77180 ⟨619568, by decide⟩ :=
  accepted_of_selected 12 77180 ⟨619568, by decide⟩ ⟨12, 2, 0, 619568, 77180, 3677, 65536⟩
    (by decide) selected_cut_24515

theorem selected_cut_24516 : selected 9 ⟨619621, by decide⟩
    (prefixPartial 12 77181) = some ⟨12, 2, 0, 619621, 77181, 3557, 65536⟩ := by
  decide +kernel

theorem context_12_77181_619621 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77181 ⟨619621, by decide⟩ :=
  accepted_of_selected 12 77181 ⟨619621, by decide⟩ ⟨12, 2, 0, 619621, 77181, 3557, 65536⟩
    (by decide) selected_cut_24516

theorem selected_cut_24517 : selected 9 ⟨619681, by decide⟩
    (prefixPartial 12 77182) = some ⟨12, 2, 0, 619681, 77182, 3873, 65536⟩ := by
  decide +kernel

theorem context_12_77182_619681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77182 ⟨619681, by decide⟩ :=
  accepted_of_selected 12 77182 ⟨619681, by decide⟩ ⟨12, 2, 0, 619681, 77182, 3873, 65536⟩
    (by decide) selected_cut_24517

theorem selected_cut_24518 : selected 9 ⟨607719, by decide⟩
    (prefixPartial 12 77183) = some ⟨12, 1, 0, 607719, 77183, 1, 65536⟩ := by
  decide +kernel

theorem context_12_77183_607719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77183 ⟨607719, by decide⟩ :=
  accepted_of_selected 12 77183 ⟨607719, by decide⟩ ⟨12, 1, 0, 607719, 77183, 1, 65536⟩
    (by decide) selected_cut_24518

theorem unmarked_context_11_19295_619682 : frontier 10 ⟨619682, by decide⟩
    (prefixCache 11 19295) (prefixPartial 11 19295) = false := by
  decide +kernel

theorem node_context_11_19295_619682 : EJMOriginalGlobalDAGData.nodes 10 ⟨619682, by decide⟩ =
    .split (coordinate 11) (![⟨619568, by decide⟩,⟨619621, by decide⟩,⟨619681, by decide⟩,⟨607719, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19295_619682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19295 ⟨619682, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19295
    ⟨619682, by decide⟩ (by decide) (![⟨619568, by decide⟩,⟨619621, by decide⟩,⟨619681, by decide⟩,⟨607719, by decide⟩]) unmarked_context_11_19295_619682 node_context_11_19295_619682
  intro a
  fin_cases a
  · exact context_12_77180_619568
  · exact context_12_77181_619621
  · exact context_12_77182_619681
  · exact context_12_77183_607719

theorem unmarked_context_10_4823_619683 : frontier 11 ⟨619683, by decide⟩
    (prefixCache 10 4823) (prefixPartial 10 4823) = false := by
  decide +kernel

theorem node_context_10_4823_619683 : EJMOriginalGlobalDAGData.nodes 11 ⟨619683, by decide⟩ =
    .split (coordinate 10) (![⟨619202, by decide⟩,⟨619323, by decide⟩,⟨619497, by decide⟩,⟨619682, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4823_619683 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4823 ⟨619683, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4823
    ⟨619683, by decide⟩ (by decide) (![⟨619202, by decide⟩,⟨619323, by decide⟩,⟨619497, by decide⟩,⟨619682, by decide⟩]) unmarked_context_10_4823_619683 node_context_10_4823_619683
  intro a
  fin_cases a
  · exact context_11_19292_619202
  · exact context_11_19293_619323
  · exact context_11_19294_619497
  · exact context_11_19295_619682

theorem unmarked_context_9_1205_619684 : frontier 12 ⟨619684, by decide⟩
    (prefixCache 9 1205) (prefixPartial 9 1205) = false := by
  decide +kernel

theorem node_context_9_1205_619684 : EJMOriginalGlobalDAGData.nodes 12 ⟨619684, by decide⟩ =
    .split (coordinate 9) (![⟨617491, by decide⟩,⟨618291, by decide⟩,⟨619022, by decide⟩,⟨619683, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1205_619684 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1205 ⟨619684, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1205
    ⟨619684, by decide⟩ (by decide) (![⟨617491, by decide⟩,⟨618291, by decide⟩,⟨619022, by decide⟩,⟨619683, by decide⟩]) unmarked_context_9_1205_619684 node_context_9_1205_619684
  intro a
  fin_cases a
  · exact context_10_4820_617491
  · exact context_10_4821_618291
  · exact context_10_4822_619022
  · exact context_10_4823_619683

theorem selected_cut_24519 : selected 9 ⟨619719, by decide⟩
    (prefixPartial 12 77184) = some ⟨12, 2, 0, 619719, 77184, 2425, 65536⟩ := by
  decide +kernel

theorem context_12_77184_619719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77184 ⟨619719, by decide⟩ :=
  accepted_of_selected 12 77184 ⟨619719, by decide⟩ ⟨12, 2, 0, 619719, 77184, 2425, 65536⟩
    (by decide) selected_cut_24519

theorem selected_cut_24520 : selected 9 ⟨619757, by decide⟩
    (prefixPartial 12 77185) = some ⟨12, 2, 0, 619757, 77185, 2513, 65536⟩ := by
  decide +kernel

theorem context_12_77185_619757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77185 ⟨619757, by decide⟩ :=
  accepted_of_selected 12 77185 ⟨619757, by decide⟩ ⟨12, 2, 0, 619757, 77185, 2513, 65536⟩
    (by decide) selected_cut_24520

theorem selected_cut_24521 : selected 9 ⟨619794, by decide⟩
    (prefixPartial 12 77186) = some ⟨12, 2, 0, 619794, 77186, 2757, 65536⟩ := by
  decide +kernel

theorem context_12_77186_619794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77186 ⟨619794, by decide⟩ :=
  accepted_of_selected 12 77186 ⟨619794, by decide⟩ ⟨12, 2, 0, 619794, 77186, 2757, 65536⟩
    (by decide) selected_cut_24521

theorem selected_cut_24522 : selected 9 ⟨619843, by decide⟩
    (prefixPartial 12 77187) = some ⟨12, 2, 0, 619843, 77187, 3105, 65536⟩ := by
  decide +kernel

theorem context_12_77187_619843 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77187 ⟨619843, by decide⟩ :=
  accepted_of_selected 12 77187 ⟨619843, by decide⟩ ⟨12, 2, 0, 619843, 77187, 3105, 65536⟩
    (by decide) selected_cut_24522

theorem unmarked_context_11_19296_619844 : frontier 10 ⟨619844, by decide⟩
    (prefixCache 11 19296) (prefixPartial 11 19296) = false := by
  decide +kernel

theorem node_context_11_19296_619844 : EJMOriginalGlobalDAGData.nodes 10 ⟨619844, by decide⟩ =
    .split (coordinate 11) (![⟨619719, by decide⟩,⟨619757, by decide⟩,⟨619794, by decide⟩,⟨619843, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19296_619844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19296 ⟨619844, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19296
    ⟨619844, by decide⟩ (by decide) (![⟨619719, by decide⟩,⟨619757, by decide⟩,⟨619794, by decide⟩,⟨619843, by decide⟩]) unmarked_context_11_19296_619844 node_context_11_19296_619844
  intro a
  fin_cases a
  · exact context_12_77184_619719
  · exact context_12_77185_619757
  · exact context_12_77186_619794
  · exact context_12_77187_619843

theorem selected_cut_24523 : selected 9 ⟨619869, by decide⟩
    (prefixPartial 12 77188) = some ⟨12, 2, 0, 619869, 77188, 2121, 65536⟩ := by
  decide +kernel

theorem context_12_77188_619869 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77188 ⟨619869, by decide⟩ :=
  accepted_of_selected 12 77188 ⟨619869, by decide⟩ ⟨12, 2, 0, 619869, 77188, 2121, 65536⟩
    (by decide) selected_cut_24523

theorem selected_cut_24524 : selected 9 ⟨619916, by decide⟩
    (prefixPartial 12 77189) = some ⟨12, 2, 0, 619916, 77189, 3445, 65536⟩ := by
  decide +kernel

theorem context_12_77189_619916 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77189 ⟨619916, by decide⟩ :=
  accepted_of_selected 12 77189 ⟨619916, by decide⟩ ⟨12, 2, 0, 619916, 77189, 3445, 65536⟩
    (by decide) selected_cut_24524

theorem selected_cut_24525 : selected 9 ⟨619951, by decide⟩
    (prefixPartial 12 77190) = some ⟨12, 2, 0, 619951, 77190, 2401, 65536⟩ := by
  decide +kernel

theorem context_12_77190_619951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77190 ⟨619951, by decide⟩ :=
  accepted_of_selected 12 77190 ⟨619951, by decide⟩ ⟨12, 2, 0, 619951, 77190, 2401, 65536⟩
    (by decide) selected_cut_24525

theorem selected_cut_24526 : selected 9 ⟨619993, by decide⟩
    (prefixPartial 12 77191) = some ⟨12, 2, 0, 619993, 77191, 2653, 65536⟩ := by
  decide +kernel

theorem context_12_77191_619993 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77191 ⟨619993, by decide⟩ :=
  accepted_of_selected 12 77191 ⟨619993, by decide⟩ ⟨12, 2, 0, 619993, 77191, 2653, 65536⟩
    (by decide) selected_cut_24526

theorem unmarked_context_11_19297_619994 : frontier 10 ⟨619994, by decide⟩
    (prefixCache 11 19297) (prefixPartial 11 19297) = false := by
  decide +kernel

theorem node_context_11_19297_619994 : EJMOriginalGlobalDAGData.nodes 10 ⟨619994, by decide⟩ =
    .split (coordinate 11) (![⟨619869, by decide⟩,⟨619916, by decide⟩,⟨619951, by decide⟩,⟨619993, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19297_619994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19297 ⟨619994, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19297
    ⟨619994, by decide⟩ (by decide) (![⟨619869, by decide⟩,⟨619916, by decide⟩,⟨619951, by decide⟩,⟨619993, by decide⟩]) unmarked_context_11_19297_619994 node_context_11_19297_619994
  intro a
  fin_cases a
  · exact context_12_77188_619869
  · exact context_12_77189_619916
  · exact context_12_77190_619951
  · exact context_12_77191_619993

theorem selected_cut_24527 : selected 9 ⟨620027, by decide⟩
    (prefixPartial 12 77192) = some ⟨12, 2, 0, 620027, 77192, 2593, 65536⟩ := by
  decide +kernel

theorem context_12_77192_620027 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77192 ⟨620027, by decide⟩ :=
  accepted_of_selected 12 77192 ⟨620027, by decide⟩ ⟨12, 2, 0, 620027, 77192, 2593, 65536⟩
    (by decide) selected_cut_24527

theorem selected_cut_24528 : selected 9 ⟨620064, by decide⟩
    (prefixPartial 12 77193) = some ⟨12, 2, 0, 620064, 77193, 2669, 65536⟩ := by
  decide +kernel

theorem context_12_77193_620064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77193 ⟨620064, by decide⟩ :=
  accepted_of_selected 12 77193 ⟨620064, by decide⟩ ⟨12, 2, 0, 620064, 77193, 2669, 65536⟩
    (by decide) selected_cut_24528

theorem selected_cut_24529 : selected 9 ⟨620097, by decide⟩
    (prefixPartial 12 77194) = some ⟨12, 2, 0, 620097, 77194, 2621, 65536⟩ := by
  decide +kernel

theorem context_12_77194_620097 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77194 ⟨620097, by decide⟩ :=
  accepted_of_selected 12 77194 ⟨620097, by decide⟩ ⟨12, 2, 0, 620097, 77194, 2621, 65536⟩
    (by decide) selected_cut_24529

theorem selected_cut_24530 : selected 9 ⟨620146, by decide⟩
    (prefixPartial 12 77195) = some ⟨12, 2, 0, 620146, 77195, 2933, 65536⟩ := by
  decide +kernel

theorem context_12_77195_620146 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77195 ⟨620146, by decide⟩ :=
  accepted_of_selected 12 77195 ⟨620146, by decide⟩ ⟨12, 2, 0, 620146, 77195, 2933, 65536⟩
    (by decide) selected_cut_24530

theorem unmarked_context_11_19298_620147 : frontier 10 ⟨620147, by decide⟩
    (prefixCache 11 19298) (prefixPartial 11 19298) = false := by
  decide +kernel

theorem node_context_11_19298_620147 : EJMOriginalGlobalDAGData.nodes 10 ⟨620147, by decide⟩ =
    .split (coordinate 11) (![⟨620027, by decide⟩,⟨620064, by decide⟩,⟨620097, by decide⟩,⟨620146, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19298_620147 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19298 ⟨620147, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19298
    ⟨620147, by decide⟩ (by decide) (![⟨620027, by decide⟩,⟨620064, by decide⟩,⟨620097, by decide⟩,⟨620146, by decide⟩]) unmarked_context_11_19298_620147 node_context_11_19298_620147
  intro a
  fin_cases a
  · exact context_12_77192_620027
  · exact context_12_77193_620064
  · exact context_12_77194_620097
  · exact context_12_77195_620146

theorem selected_cut_24531 : selected 9 ⟨620173, by decide⟩
    (prefixPartial 12 77196) = some ⟨12, 2, 0, 620173, 77196, 2185, 65536⟩ := by
  decide +kernel

theorem context_12_77196_620173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77196 ⟨620173, by decide⟩ :=
  accepted_of_selected 12 77196 ⟨620173, by decide⟩ ⟨12, 2, 0, 620173, 77196, 2185, 65536⟩
    (by decide) selected_cut_24531

theorem selected_cut_24532 : selected 9 ⟨620200, by decide⟩
    (prefixPartial 12 77197) = some ⟨12, 2, 0, 620200, 77197, 2205, 65536⟩ := by
  decide +kernel

theorem context_12_77197_620200 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77197 ⟨620200, by decide⟩ :=
  accepted_of_selected 12 77197 ⟨620200, by decide⟩ ⟨12, 2, 0, 620200, 77197, 2205, 65536⟩
    (by decide) selected_cut_24532

theorem selected_cut_24533 : selected 9 ⟨620237, by decide⟩
    (prefixPartial 12 77198) = some ⟨12, 2, 0, 620237, 77198, 2385, 65536⟩ := by
  decide +kernel

theorem context_12_77198_620237 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77198 ⟨620237, by decide⟩ :=
  accepted_of_selected 12 77198 ⟨620237, by decide⟩ ⟨12, 2, 0, 620237, 77198, 2385, 65536⟩
    (by decide) selected_cut_24533

theorem selected_cut_24534 : selected 9 ⟨620268, by decide⟩
    (prefixPartial 12 77199) = some ⟨12, 2, 0, 620268, 77199, 2517, 65536⟩ := by
  decide +kernel

theorem context_12_77199_620268 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77199 ⟨620268, by decide⟩ :=
  accepted_of_selected 12 77199 ⟨620268, by decide⟩ ⟨12, 2, 0, 620268, 77199, 2517, 65536⟩
    (by decide) selected_cut_24534

theorem unmarked_context_11_19299_620269 : frontier 10 ⟨620269, by decide⟩
    (prefixCache 11 19299) (prefixPartial 11 19299) = false := by
  decide +kernel

theorem node_context_11_19299_620269 : EJMOriginalGlobalDAGData.nodes 10 ⟨620269, by decide⟩ =
    .split (coordinate 11) (![⟨620173, by decide⟩,⟨620200, by decide⟩,⟨620237, by decide⟩,⟨620268, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19299_620269 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19299 ⟨620269, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19299
    ⟨620269, by decide⟩ (by decide) (![⟨620173, by decide⟩,⟨620200, by decide⟩,⟨620237, by decide⟩,⟨620268, by decide⟩]) unmarked_context_11_19299_620269 node_context_11_19299_620269
  intro a
  fin_cases a
  · exact context_12_77196_620173
  · exact context_12_77197_620200
  · exact context_12_77198_620237
  · exact context_12_77199_620268

theorem unmarked_context_10_4824_620270 : frontier 11 ⟨620270, by decide⟩
    (prefixCache 10 4824) (prefixPartial 10 4824) = false := by
  decide +kernel

theorem node_context_10_4824_620270 : EJMOriginalGlobalDAGData.nodes 11 ⟨620270, by decide⟩ =
    .split (coordinate 10) (![⟨619844, by decide⟩,⟨619994, by decide⟩,⟨620147, by decide⟩,⟨620269, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4824_620270 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4824 ⟨620270, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4824
    ⟨620270, by decide⟩ (by decide) (![⟨619844, by decide⟩,⟨619994, by decide⟩,⟨620147, by decide⟩,⟨620269, by decide⟩]) unmarked_context_10_4824_620270 node_context_10_4824_620270
  intro a
  fin_cases a
  · exact context_11_19296_619844
  · exact context_11_19297_619994
  · exact context_11_19298_620147
  · exact context_11_19299_620269

theorem selected_cut_24535 : selected 9 ⟨620292, by decide⟩
    (prefixPartial 12 77200) = some ⟨12, 2, 0, 620292, 77200, 2117, 65536⟩ := by
  decide +kernel

theorem context_12_77200_620292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77200 ⟨620292, by decide⟩ :=
  accepted_of_selected 12 77200 ⟨620292, by decide⟩ ⟨12, 2, 0, 620292, 77200, 2117, 65536⟩
    (by decide) selected_cut_24535

theorem selected_cut_24536 : selected 9 ⟨620316, by decide⟩
    (prefixPartial 12 77201) = some ⟨12, 2, 0, 620316, 77201, 2321, 65536⟩ := by
  decide +kernel

theorem context_12_77201_620316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77201 ⟨620316, by decide⟩ :=
  accepted_of_selected 12 77201 ⟨620316, by decide⟩ ⟨12, 2, 0, 620316, 77201, 2321, 65536⟩
    (by decide) selected_cut_24536

theorem selected_cut_24537 : selected 9 ⟨620341, by decide⟩
    (prefixPartial 12 77202) = some ⟨12, 2, 0, 620341, 77202, 2465, 65536⟩ := by
  decide +kernel

theorem context_12_77202_620341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77202 ⟨620341, by decide⟩ :=
  accepted_of_selected 12 77202 ⟨620341, by decide⟩ ⟨12, 2, 0, 620341, 77202, 2465, 65536⟩
    (by decide) selected_cut_24537

theorem selected_cut_24538 : selected 9 ⟨620375, by decide⟩
    (prefixPartial 12 77203) = some ⟨12, 2, 0, 620375, 77203, 2669, 65536⟩ := by
  decide +kernel

theorem context_12_77203_620375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77203 ⟨620375, by decide⟩ :=
  accepted_of_selected 12 77203 ⟨620375, by decide⟩ ⟨12, 2, 0, 620375, 77203, 2669, 65536⟩
    (by decide) selected_cut_24538

theorem unmarked_context_11_19300_620376 : frontier 10 ⟨620376, by decide⟩
    (prefixCache 11 19300) (prefixPartial 11 19300) = false := by
  decide +kernel

theorem node_context_11_19300_620376 : EJMOriginalGlobalDAGData.nodes 10 ⟨620376, by decide⟩ =
    .split (coordinate 11) (![⟨620292, by decide⟩,⟨620316, by decide⟩,⟨620341, by decide⟩,⟨620375, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19300_620376 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19300 ⟨620376, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19300
    ⟨620376, by decide⟩ (by decide) (![⟨620292, by decide⟩,⟨620316, by decide⟩,⟨620341, by decide⟩,⟨620375, by decide⟩]) unmarked_context_11_19300_620376 node_context_11_19300_620376
  intro a
  fin_cases a
  · exact context_12_77200_620292
  · exact context_12_77201_620316
  · exact context_12_77202_620341
  · exact context_12_77203_620375

theorem selected_cut_24539 : selected 9 ⟨620399, by decide⟩
    (prefixPartial 12 77204) = some ⟨12, 2, 0, 620399, 77204, 1985, 65536⟩ := by
  decide +kernel

theorem context_12_77204_620399 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77204 ⟨620399, by decide⟩ :=
  accepted_of_selected 12 77204 ⟨620399, by decide⟩ ⟨12, 2, 0, 620399, 77204, 1985, 65536⟩
    (by decide) selected_cut_24539

theorem selected_cut_24540 : selected 9 ⟨439069, by decide⟩
    (prefixPartial 12 77205) = some ⟨12, 1, 0, 439069, 77205, 1, 65536⟩ := by
  decide +kernel

theorem context_12_77205_439069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77205 ⟨439069, by decide⟩ :=
  accepted_of_selected 12 77205 ⟨439069, by decide⟩ ⟨12, 1, 0, 439069, 77205, 1, 65536⟩
    (by decide) selected_cut_24540

theorem selected_cut_24541 : selected 9 ⟨620423, by decide⟩
    (prefixPartial 12 77206) = some ⟨12, 2, 0, 620423, 77206, 2273, 65536⟩ := by
  decide +kernel

theorem context_12_77206_620423 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77206 ⟨620423, by decide⟩ :=
  accepted_of_selected 12 77206 ⟨620423, by decide⟩ ⟨12, 2, 0, 620423, 77206, 2273, 65536⟩
    (by decide) selected_cut_24541

theorem selected_cut_24542 : selected 9 ⟨620458, by decide⟩
    (prefixPartial 12 77207) = some ⟨12, 2, 0, 620458, 77207, 2505, 65536⟩ := by
  decide +kernel

theorem context_12_77207_620458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77207 ⟨620458, by decide⟩ :=
  accepted_of_selected 12 77207 ⟨620458, by decide⟩ ⟨12, 2, 0, 620458, 77207, 2505, 65536⟩
    (by decide) selected_cut_24542

theorem unmarked_context_11_19301_620459 : frontier 10 ⟨620459, by decide⟩
    (prefixCache 11 19301) (prefixPartial 11 19301) = false := by
  decide +kernel

theorem node_context_11_19301_620459 : EJMOriginalGlobalDAGData.nodes 10 ⟨620459, by decide⟩ =
    .split (coordinate 11) (![⟨620399, by decide⟩,⟨439069, by decide⟩,⟨620423, by decide⟩,⟨620458, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19301_620459 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19301 ⟨620459, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19301
    ⟨620459, by decide⟩ (by decide) (![⟨620399, by decide⟩,⟨439069, by decide⟩,⟨620423, by decide⟩,⟨620458, by decide⟩]) unmarked_context_11_19301_620459 node_context_11_19301_620459
  intro a
  fin_cases a
  · exact context_12_77204_620399
  · exact context_12_77205_439069
  · exact context_12_77206_620423
  · exact context_12_77207_620458

theorem selected_cut_24543 : selected 9 ⟨620489, by decide⟩
    (prefixPartial 12 77208) = some ⟨12, 2, 0, 620489, 77208, 2241, 65536⟩ := by
  decide +kernel

theorem context_12_77208_620489 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77208 ⟨620489, by decide⟩ :=
  accepted_of_selected 12 77208 ⟨620489, by decide⟩ ⟨12, 2, 0, 620489, 77208, 2241, 65536⟩
    (by decide) selected_cut_24543

theorem selected_cut_24544 : selected 9 ⟨620518, by decide⟩
    (prefixPartial 12 77209) = some ⟨12, 2, 0, 620518, 77209, 2461, 65536⟩ := by
  decide +kernel

theorem context_12_77209_620518 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77209 ⟨620518, by decide⟩ :=
  accepted_of_selected 12 77209 ⟨620518, by decide⟩ ⟨12, 2, 0, 620518, 77209, 2461, 65536⟩
    (by decide) selected_cut_24544

theorem selected_cut_24545 : selected 9 ⟨620547, by decide⟩
    (prefixPartial 12 77210) = some ⟨12, 2, 0, 620547, 77210, 2393, 65536⟩ := by
  decide +kernel

theorem context_12_77210_620547 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77210 ⟨620547, by decide⟩ :=
  accepted_of_selected 12 77210 ⟨620547, by decide⟩ ⟨12, 2, 0, 620547, 77210, 2393, 65536⟩
    (by decide) selected_cut_24545

theorem selected_cut_24546 : selected 9 ⟨620589, by decide⟩
    (prefixPartial 12 77211) = some ⟨12, 2, 0, 620589, 77211, 2629, 65536⟩ := by
  decide +kernel

theorem context_12_77211_620589 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77211 ⟨620589, by decide⟩ :=
  accepted_of_selected 12 77211 ⟨620589, by decide⟩ ⟨12, 2, 0, 620589, 77211, 2629, 65536⟩
    (by decide) selected_cut_24546

theorem unmarked_context_11_19302_620590 : frontier 10 ⟨620590, by decide⟩
    (prefixCache 11 19302) (prefixPartial 11 19302) = false := by
  decide +kernel

theorem node_context_11_19302_620590 : EJMOriginalGlobalDAGData.nodes 10 ⟨620590, by decide⟩ =
    .split (coordinate 11) (![⟨620489, by decide⟩,⟨620518, by decide⟩,⟨620547, by decide⟩,⟨620589, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19302_620590 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19302 ⟨620590, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19302
    ⟨620590, by decide⟩ (by decide) (![⟨620489, by decide⟩,⟨620518, by decide⟩,⟨620547, by decide⟩,⟨620589, by decide⟩]) unmarked_context_11_19302_620590 node_context_11_19302_620590
  intro a
  fin_cases a
  · exact context_12_77208_620489
  · exact context_12_77209_620518
  · exact context_12_77210_620547
  · exact context_12_77211_620589

theorem selected_cut_24547 : selected 9 ⟨620612, by decide⟩
    (prefixPartial 12 77212) = some ⟨12, 2, 0, 620612, 77212, 1953, 65536⟩ := by
  decide +kernel

theorem context_12_77212_620612 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77212 ⟨620612, by decide⟩ :=
  accepted_of_selected 12 77212 ⟨620612, by decide⟩ ⟨12, 2, 0, 620612, 77212, 1953, 65536⟩
    (by decide) selected_cut_24547

theorem selected_cut_24548 : selected 9 ⟨620631, by decide⟩
    (prefixPartial 12 77213) = some ⟨12, 2, 0, 620631, 77213, 2109, 65536⟩ := by
  decide +kernel

theorem context_12_77213_620631 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77213 ⟨620631, by decide⟩ :=
  accepted_of_selected 12 77213 ⟨620631, by decide⟩ ⟨12, 2, 0, 620631, 77213, 2109, 65536⟩
    (by decide) selected_cut_24548

theorem selected_cut_24549 : selected 9 ⟨620658, by decide⟩
    (prefixPartial 12 77214) = some ⟨12, 2, 0, 620658, 77214, 2233, 65536⟩ := by
  decide +kernel

theorem context_12_77214_620658 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77214 ⟨620658, by decide⟩ :=
  accepted_of_selected 12 77214 ⟨620658, by decide⟩ ⟨12, 2, 0, 620658, 77214, 2233, 65536⟩
    (by decide) selected_cut_24549

theorem selected_cut_24550 : selected 9 ⟨620690, by decide⟩
    (prefixPartial 12 77215) = some ⟨12, 2, 0, 620690, 77215, 2225, 65536⟩ := by
  decide +kernel

theorem context_12_77215_620690 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77215 ⟨620690, by decide⟩ :=
  accepted_of_selected 12 77215 ⟨620690, by decide⟩ ⟨12, 2, 0, 620690, 77215, 2225, 65536⟩
    (by decide) selected_cut_24550

theorem unmarked_context_11_19303_620691 : frontier 10 ⟨620691, by decide⟩
    (prefixCache 11 19303) (prefixPartial 11 19303) = false := by
  decide +kernel

theorem node_context_11_19303_620691 : EJMOriginalGlobalDAGData.nodes 10 ⟨620691, by decide⟩ =
    .split (coordinate 11) (![⟨620612, by decide⟩,⟨620631, by decide⟩,⟨620658, by decide⟩,⟨620690, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19303_620691 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19303 ⟨620691, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19303
    ⟨620691, by decide⟩ (by decide) (![⟨620612, by decide⟩,⟨620631, by decide⟩,⟨620658, by decide⟩,⟨620690, by decide⟩]) unmarked_context_11_19303_620691 node_context_11_19303_620691
  intro a
  fin_cases a
  · exact context_12_77212_620612
  · exact context_12_77213_620631
  · exact context_12_77214_620658
  · exact context_12_77215_620690

theorem unmarked_context_10_4825_620692 : frontier 11 ⟨620692, by decide⟩
    (prefixCache 10 4825) (prefixPartial 10 4825) = false := by
  decide +kernel

theorem node_context_10_4825_620692 : EJMOriginalGlobalDAGData.nodes 11 ⟨620692, by decide⟩ =
    .split (coordinate 10) (![⟨620376, by decide⟩,⟨620459, by decide⟩,⟨620590, by decide⟩,⟨620691, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4825_620692 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4825 ⟨620692, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4825
    ⟨620692, by decide⟩ (by decide) (![⟨620376, by decide⟩,⟨620459, by decide⟩,⟨620590, by decide⟩,⟨620691, by decide⟩]) unmarked_context_10_4825_620692 node_context_10_4825_620692
  intro a
  fin_cases a
  · exact context_11_19300_620376
  · exact context_11_19301_620459
  · exact context_11_19302_620590
  · exact context_11_19303_620691

theorem selected_cut_24551 : selected 9 ⟨620711, by decide⟩
    (prefixPartial 12 77216) = some ⟨12, 2, 0, 620711, 77216, 1585, 65536⟩ := by
  decide +kernel

theorem context_12_77216_620711 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77216 ⟨620711, by decide⟩ :=
  accepted_of_selected 12 77216 ⟨620711, by decide⟩ ⟨12, 2, 0, 620711, 77216, 1585, 65536⟩
    (by decide) selected_cut_24551

theorem selected_cut_24552 : selected 9 ⟨620729, by decide⟩
    (prefixPartial 12 77217) = some ⟨12, 2, 0, 620729, 77217, 1713, 65536⟩ := by
  decide +kernel

theorem context_12_77217_620729 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77217 ⟨620729, by decide⟩ :=
  accepted_of_selected 12 77217 ⟨620729, by decide⟩ ⟨12, 2, 0, 620729, 77217, 1713, 65536⟩
    (by decide) selected_cut_24552

theorem selected_cut_24553 : selected 9 ⟨620749, by decide⟩
    (prefixPartial 12 77218) = some ⟨12, 2, 0, 620749, 77218, 1809, 65536⟩ := by
  decide +kernel

theorem context_12_77218_620749 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77218 ⟨620749, by decide⟩ :=
  accepted_of_selected 12 77218 ⟨620749, by decide⟩ ⟨12, 2, 0, 620749, 77218, 1809, 65536⟩
    (by decide) selected_cut_24553

theorem selected_cut_24554 : selected 9 ⟨620775, by decide⟩
    (prefixPartial 12 77219) = some ⟨12, 2, 0, 620775, 77219, 2045, 65536⟩ := by
  decide +kernel

theorem context_12_77219_620775 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77219 ⟨620775, by decide⟩ :=
  accepted_of_selected 12 77219 ⟨620775, by decide⟩ ⟨12, 2, 0, 620775, 77219, 2045, 65536⟩
    (by decide) selected_cut_24554

theorem unmarked_context_11_19304_620776 : frontier 10 ⟨620776, by decide⟩
    (prefixCache 11 19304) (prefixPartial 11 19304) = false := by
  decide +kernel

theorem node_context_11_19304_620776 : EJMOriginalGlobalDAGData.nodes 10 ⟨620776, by decide⟩ =
    .split (coordinate 11) (![⟨620711, by decide⟩,⟨620729, by decide⟩,⟨620749, by decide⟩,⟨620775, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19304_620776 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19304 ⟨620776, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19304
    ⟨620776, by decide⟩ (by decide) (![⟨620711, by decide⟩,⟨620729, by decide⟩,⟨620749, by decide⟩,⟨620775, by decide⟩]) unmarked_context_11_19304_620776 node_context_11_19304_620776
  intro a
  fin_cases a
  · exact context_12_77216_620711
  · exact context_12_77217_620729
  · exact context_12_77218_620749
  · exact context_12_77219_620775

theorem selected_cut_24555 : selected 9 ⟨620796, by decide⟩
    (prefixPartial 12 77220) = some ⟨12, 2, 0, 620796, 77220, 1593, 65536⟩ := by
  decide +kernel

theorem context_12_77220_620796 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77220 ⟨620796, by decide⟩ :=
  accepted_of_selected 12 77220 ⟨620796, by decide⟩ ⟨12, 2, 0, 620796, 77220, 1593, 65536⟩
    (by decide) selected_cut_24555

theorem selected_cut_24556 : selected 9 ⟨620849, by decide⟩
    (prefixPartial 12 77221) = some ⟨12, 2, 0, 620849, 77221, 2425, 65536⟩ := by
  decide +kernel

theorem context_12_77221_620849 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77221 ⟨620849, by decide⟩ :=
  accepted_of_selected 12 77221 ⟨620849, by decide⟩ ⟨12, 2, 0, 620849, 77221, 2425, 65536⟩
    (by decide) selected_cut_24556

theorem selected_cut_24557 : selected 9 ⟨620869, by decide⟩
    (prefixPartial 12 77222) = some ⟨12, 2, 0, 620869, 77222, 1761, 65536⟩ := by
  decide +kernel

theorem context_12_77222_620869 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77222 ⟨620869, by decide⟩ :=
  accepted_of_selected 12 77222 ⟨620869, by decide⟩ ⟨12, 2, 0, 620869, 77222, 1761, 65536⟩
    (by decide) selected_cut_24557

theorem selected_cut_24558 : selected 9 ⟨620892, by decide⟩
    (prefixPartial 12 77223) = some ⟨12, 2, 0, 620892, 77223, 1941, 65536⟩ := by
  decide +kernel

theorem context_12_77223_620892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77223 ⟨620892, by decide⟩ :=
  accepted_of_selected 12 77223 ⟨620892, by decide⟩ ⟨12, 2, 0, 620892, 77223, 1941, 65536⟩
    (by decide) selected_cut_24558

theorem unmarked_context_11_19305_620893 : frontier 10 ⟨620893, by decide⟩
    (prefixCache 11 19305) (prefixPartial 11 19305) = false := by
  decide +kernel

theorem node_context_11_19305_620893 : EJMOriginalGlobalDAGData.nodes 10 ⟨620893, by decide⟩ =
    .split (coordinate 11) (![⟨620796, by decide⟩,⟨620849, by decide⟩,⟨620869, by decide⟩,⟨620892, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19305_620893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19305 ⟨620893, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19305
    ⟨620893, by decide⟩ (by decide) (![⟨620796, by decide⟩,⟨620849, by decide⟩,⟨620869, by decide⟩,⟨620892, by decide⟩]) unmarked_context_11_19305_620893 node_context_11_19305_620893
  intro a
  fin_cases a
  · exact context_12_77220_620796
  · exact context_12_77221_620849
  · exact context_12_77222_620869
  · exact context_12_77223_620892

theorem selected_cut_24559 : selected 9 ⟨620914, by decide⟩
    (prefixPartial 12 77224) = some ⟨12, 2, 0, 620914, 77224, 1653, 65536⟩ := by
  decide +kernel

theorem context_12_77224_620914 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77224 ⟨620914, by decide⟩ :=
  accepted_of_selected 12 77224 ⟨620914, by decide⟩ ⟨12, 2, 0, 620914, 77224, 1653, 65536⟩
    (by decide) selected_cut_24559

theorem selected_cut_24560 : selected 9 ⟨620932, by decide⟩
    (prefixPartial 12 77225) = some ⟨12, 2, 0, 620932, 77225, 1729, 65536⟩ := by
  decide +kernel

theorem context_12_77225_620932 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77225 ⟨620932, by decide⟩ :=
  accepted_of_selected 12 77225 ⟨620932, by decide⟩ ⟨12, 2, 0, 620932, 77225, 1729, 65536⟩
    (by decide) selected_cut_24560

theorem selected_cut_24561 : selected 9 ⟨620947, by decide⟩
    (prefixPartial 12 77226) = some ⟨12, 2, 0, 620947, 77226, 1697, 65536⟩ := by
  decide +kernel

theorem context_12_77226_620947 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77226 ⟨620947, by decide⟩ :=
  accepted_of_selected 12 77226 ⟨620947, by decide⟩ ⟨12, 2, 0, 620947, 77226, 1697, 65536⟩
    (by decide) selected_cut_24561

theorem selected_cut_24562 : selected 9 ⟨620981, by decide⟩
    (prefixPartial 12 77227) = some ⟨12, 2, 0, 620981, 77227, 1873, 65536⟩ := by
  decide +kernel

theorem context_12_77227_620981 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77227 ⟨620981, by decide⟩ :=
  accepted_of_selected 12 77227 ⟨620981, by decide⟩ ⟨12, 2, 0, 620981, 77227, 1873, 65536⟩
    (by decide) selected_cut_24562

theorem unmarked_context_11_19306_620982 : frontier 10 ⟨620982, by decide⟩
    (prefixCache 11 19306) (prefixPartial 11 19306) = false := by
  decide +kernel

theorem node_context_11_19306_620982 : EJMOriginalGlobalDAGData.nodes 10 ⟨620982, by decide⟩ =
    .split (coordinate 11) (![⟨620914, by decide⟩,⟨620932, by decide⟩,⟨620947, by decide⟩,⟨620981, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19306_620982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19306 ⟨620982, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19306
    ⟨620982, by decide⟩ (by decide) (![⟨620914, by decide⟩,⟨620932, by decide⟩,⟨620947, by decide⟩,⟨620981, by decide⟩]) unmarked_context_11_19306_620982 node_context_11_19306_620982
  intro a
  fin_cases a
  · exact context_12_77224_620914
  · exact context_12_77225_620932
  · exact context_12_77226_620947
  · exact context_12_77227_620981

theorem selected_cut_24563 : selected 9 ⟨620999, by decide⟩
    (prefixPartial 12 77228) = some ⟨12, 2, 0, 620999, 77228, 1449, 65536⟩ := by
  decide +kernel

theorem context_12_77228_620999 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77228 ⟨620999, by decide⟩ :=
  accepted_of_selected 12 77228 ⟨620999, by decide⟩ ⟨12, 2, 0, 620999, 77228, 1449, 65536⟩
    (by decide) selected_cut_24563

theorem selected_cut_24564 : selected 9 ⟨621014, by decide⟩
    (prefixPartial 12 77229) = some ⟨12, 2, 0, 621014, 77229, 1421, 65536⟩ := by
  decide +kernel

theorem context_12_77229_621014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77229 ⟨621014, by decide⟩ :=
  accepted_of_selected 12 77229 ⟨621014, by decide⟩ ⟨12, 2, 0, 621014, 77229, 1421, 65536⟩
    (by decide) selected_cut_24564

theorem selected_cut_24565 : selected 9 ⟨621033, by decide⟩
    (prefixPartial 12 77230) = some ⟨12, 2, 0, 621033, 77230, 1537, 65536⟩ := by
  decide +kernel

theorem context_12_77230_621033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77230 ⟨621033, by decide⟩ :=
  accepted_of_selected 12 77230 ⟨621033, by decide⟩ ⟨12, 2, 0, 621033, 77230, 1537, 65536⟩
    (by decide) selected_cut_24565

theorem selected_cut_24566 : selected 9 ⟨621048, by decide⟩
    (prefixPartial 12 77231) = some ⟨12, 2, 0, 621048, 77231, 1577, 65536⟩ := by
  decide +kernel

theorem context_12_77231_621048 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77231 ⟨621048, by decide⟩ :=
  accepted_of_selected 12 77231 ⟨621048, by decide⟩ ⟨12, 2, 0, 621048, 77231, 1577, 65536⟩
    (by decide) selected_cut_24566

theorem unmarked_context_11_19307_621049 : frontier 10 ⟨621049, by decide⟩
    (prefixCache 11 19307) (prefixPartial 11 19307) = false := by
  decide +kernel

theorem node_context_11_19307_621049 : EJMOriginalGlobalDAGData.nodes 10 ⟨621049, by decide⟩ =
    .split (coordinate 11) (![⟨620999, by decide⟩,⟨621014, by decide⟩,⟨621033, by decide⟩,⟨621048, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19307_621049 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19307 ⟨621049, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19307
    ⟨621049, by decide⟩ (by decide) (![⟨620999, by decide⟩,⟨621014, by decide⟩,⟨621033, by decide⟩,⟨621048, by decide⟩]) unmarked_context_11_19307_621049 node_context_11_19307_621049
  intro a
  fin_cases a
  · exact context_12_77228_620999
  · exact context_12_77229_621014
  · exact context_12_77230_621033
  · exact context_12_77231_621048

theorem unmarked_context_10_4826_621050 : frontier 11 ⟨621050, by decide⟩
    (prefixCache 10 4826) (prefixPartial 10 4826) = false := by
  decide +kernel

theorem node_context_10_4826_621050 : EJMOriginalGlobalDAGData.nodes 11 ⟨621050, by decide⟩ =
    .split (coordinate 10) (![⟨620776, by decide⟩,⟨620893, by decide⟩,⟨620982, by decide⟩,⟨621049, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4826_621050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4826 ⟨621050, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4826
    ⟨621050, by decide⟩ (by decide) (![⟨620776, by decide⟩,⟨620893, by decide⟩,⟨620982, by decide⟩,⟨621049, by decide⟩]) unmarked_context_10_4826_621050 node_context_10_4826_621050
  intro a
  fin_cases a
  · exact context_11_19304_620776
  · exact context_11_19305_620893
  · exact context_11_19306_620982
  · exact context_11_19307_621049

theorem selected_cut_24567 : selected 9 ⟨621067, by decide⟩
    (prefixPartial 12 77232) = some ⟨12, 2, 0, 621067, 77232, 1137, 65536⟩ := by
  decide +kernel

theorem context_12_77232_621067 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77232 ⟨621067, by decide⟩ :=
  accepted_of_selected 12 77232 ⟨621067, by decide⟩ ⟨12, 2, 0, 621067, 77232, 1137, 65536⟩
    (by decide) selected_cut_24567

theorem selected_cut_24568 : selected 9 ⟨621084, by decide⟩
    (prefixPartial 12 77233) = some ⟨12, 2, 0, 621084, 77233, 1297, 65536⟩ := by
  decide +kernel

theorem context_12_77233_621084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77233 ⟨621084, by decide⟩ :=
  accepted_of_selected 12 77233 ⟨621084, by decide⟩ ⟨12, 2, 0, 621084, 77233, 1297, 65536⟩
    (by decide) selected_cut_24568

theorem selected_cut_24569 : selected 9 ⟨621102, by decide⟩
    (prefixPartial 12 77234) = some ⟨12, 2, 0, 621102, 77234, 1345, 65536⟩ := by
  decide +kernel

theorem context_12_77234_621102 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77234 ⟨621102, by decide⟩ :=
  accepted_of_selected 12 77234 ⟨621102, by decide⟩ ⟨12, 2, 0, 621102, 77234, 1345, 65536⟩
    (by decide) selected_cut_24569

theorem selected_cut_24570 : selected 9 ⟨621120, by decide⟩
    (prefixPartial 12 77235) = some ⟨12, 2, 0, 621120, 77235, 1373, 65536⟩ := by
  decide +kernel

theorem context_12_77235_621120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77235 ⟨621120, by decide⟩ :=
  accepted_of_selected 12 77235 ⟨621120, by decide⟩ ⟨12, 2, 0, 621120, 77235, 1373, 65536⟩
    (by decide) selected_cut_24570

theorem unmarked_context_11_19308_621121 : frontier 10 ⟨621121, by decide⟩
    (prefixCache 11 19308) (prefixPartial 11 19308) = false := by
  decide +kernel

theorem node_context_11_19308_621121 : EJMOriginalGlobalDAGData.nodes 10 ⟨621121, by decide⟩ =
    .split (coordinate 11) (![⟨621067, by decide⟩,⟨621084, by decide⟩,⟨621102, by decide⟩,⟨621120, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19308_621121 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19308 ⟨621121, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19308
    ⟨621121, by decide⟩ (by decide) (![⟨621067, by decide⟩,⟨621084, by decide⟩,⟨621102, by decide⟩,⟨621120, by decide⟩]) unmarked_context_11_19308_621121 node_context_11_19308_621121
  intro a
  fin_cases a
  · exact context_12_77232_621067
  · exact context_12_77233_621084
  · exact context_12_77234_621102
  · exact context_12_77235_621120

theorem selected_cut_24571 : selected 9 ⟨621134, by decide⟩
    (prefixPartial 12 77236) = some ⟨12, 2, 0, 621134, 77236, 1017, 65536⟩ := by
  decide +kernel

theorem context_12_77236_621134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77236 ⟨621134, by decide⟩ :=
  accepted_of_selected 12 77236 ⟨621134, by decide⟩ ⟨12, 2, 0, 621134, 77236, 1017, 65536⟩
    (by decide) selected_cut_24571

theorem selected_cut_24572 : selected 9 ⟨621156, by decide⟩
    (prefixPartial 12 77237) = some ⟨12, 2, 0, 621156, 77237, 1633, 65536⟩ := by
  decide +kernel

theorem context_12_77237_621156 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77237 ⟨621156, by decide⟩ :=
  accepted_of_selected 12 77237 ⟨621156, by decide⟩ ⟨12, 2, 0, 621156, 77237, 1633, 65536⟩
    (by decide) selected_cut_24572

theorem selected_cut_24573 : selected 9 ⟨621172, by decide⟩
    (prefixPartial 12 77238) = some ⟨12, 2, 0, 621172, 77238, 1129, 65536⟩ := by
  decide +kernel

theorem context_12_77238_621172 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77238 ⟨621172, by decide⟩ :=
  accepted_of_selected 12 77238 ⟨621172, by decide⟩ ⟨12, 2, 0, 621172, 77238, 1129, 65536⟩
    (by decide) selected_cut_24573

theorem selected_cut_24574 : selected 9 ⟨621184, by decide⟩
    (prefixPartial 12 77239) = some ⟨12, 2, 0, 621184, 77239, 1105, 65536⟩ := by
  decide +kernel

theorem context_12_77239_621184 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77239 ⟨621184, by decide⟩ :=
  accepted_of_selected 12 77239 ⟨621184, by decide⟩ ⟨12, 2, 0, 621184, 77239, 1105, 65536⟩
    (by decide) selected_cut_24574

theorem unmarked_context_11_19309_621185 : frontier 10 ⟨621185, by decide⟩
    (prefixCache 11 19309) (prefixPartial 11 19309) = false := by
  decide +kernel

theorem node_context_11_19309_621185 : EJMOriginalGlobalDAGData.nodes 10 ⟨621185, by decide⟩ =
    .split (coordinate 11) (![⟨621134, by decide⟩,⟨621156, by decide⟩,⟨621172, by decide⟩,⟨621184, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19309_621185 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19309 ⟨621185, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19309
    ⟨621185, by decide⟩ (by decide) (![⟨621134, by decide⟩,⟨621156, by decide⟩,⟨621172, by decide⟩,⟨621184, by decide⟩]) unmarked_context_11_19309_621185 node_context_11_19309_621185
  intro a
  fin_cases a
  · exact context_12_77236_621134
  · exact context_12_77237_621156
  · exact context_12_77238_621172
  · exact context_12_77239_621184

theorem selected_cut_24575 : selected 9 ⟨621200, by decide⟩
    (prefixPartial 12 77240) = some ⟨12, 2, 0, 621200, 77240, 1065, 65536⟩ := by
  decide +kernel

theorem context_12_77240_621200 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77240 ⟨621200, by decide⟩ :=
  accepted_of_selected 12 77240 ⟨621200, by decide⟩ ⟨12, 2, 0, 621200, 77240, 1065, 65536⟩
    (by decide) selected_cut_24575

theorem selected_cut_24576 : selected 9 ⟨621217, by decide⟩
    (prefixPartial 12 77241) = some ⟨12, 2, 0, 621217, 77241, 1229, 65536⟩ := by
  decide +kernel

theorem context_12_77241_621217 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77241 ⟨621217, by decide⟩ :=
  accepted_of_selected 12 77241 ⟨621217, by decide⟩ ⟨12, 2, 0, 621217, 77241, 1229, 65536⟩
    (by decide) selected_cut_24576

theorem selected_cut_24577 : selected 9 ⟨621232, by decide⟩
    (prefixPartial 12 77242) = some ⟨12, 2, 0, 621232, 77242, 1113, 65536⟩ := by
  decide +kernel

theorem context_12_77242_621232 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77242 ⟨621232, by decide⟩ :=
  accepted_of_selected 12 77242 ⟨621232, by decide⟩ ⟨12, 2, 0, 621232, 77242, 1113, 65536⟩
    (by decide) selected_cut_24577

theorem selected_cut_24578 : selected 9 ⟨621251, by decide⟩
    (prefixPartial 12 77243) = some ⟨12, 2, 0, 621251, 77243, 1089, 65536⟩ := by
  decide +kernel

theorem context_12_77243_621251 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77243 ⟨621251, by decide⟩ :=
  accepted_of_selected 12 77243 ⟨621251, by decide⟩ ⟨12, 2, 0, 621251, 77243, 1089, 65536⟩
    (by decide) selected_cut_24578

theorem unmarked_context_11_19310_621252 : frontier 10 ⟨621252, by decide⟩
    (prefixCache 11 19310) (prefixPartial 11 19310) = false := by
  decide +kernel

theorem node_context_11_19310_621252 : EJMOriginalGlobalDAGData.nodes 10 ⟨621252, by decide⟩ =
    .split (coordinate 11) (![⟨621200, by decide⟩,⟨621217, by decide⟩,⟨621232, by decide⟩,⟨621251, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19310_621252 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19310 ⟨621252, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19310
    ⟨621252, by decide⟩ (by decide) (![⟨621200, by decide⟩,⟨621217, by decide⟩,⟨621232, by decide⟩,⟨621251, by decide⟩]) unmarked_context_11_19310_621252 node_context_11_19310_621252
  intro a
  fin_cases a
  · exact context_12_77240_621200
  · exact context_12_77241_621217
  · exact context_12_77242_621232
  · exact context_12_77243_621251

theorem selected_cut_24579 : selected 10 ⟨621306, by decide⟩
    (prefixPartial 11 19311) = some ⟨11, 2, 0, 621306, 19311, 3717, 262144⟩ := by
  decide +kernel

theorem context_11_19311_621306 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19311 ⟨621306, by decide⟩ :=
  accepted_of_selected 11 19311 ⟨621306, by decide⟩ ⟨11, 2, 0, 621306, 19311, 3717, 262144⟩
    (by decide) selected_cut_24579

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
