/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover350
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_33700 : selected 8 ⟨867154, by decide⟩
    (prefixPartial 13 441634) = some ⟨13, 2, 0, 867154, 441634, 1357, 16384⟩ := by
  decide +kernel

theorem context_13_441634_867154 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441634 ⟨867154, by decide⟩ :=
  accepted_of_selected 13 441634 ⟨867154, by decide⟩ ⟨13, 2, 0, 867154, 441634, 1357, 16384⟩
    (by decide) selected_cut_33700

theorem selected_cut_33701 : selected 8 ⟨867159, by decide⟩
    (prefixPartial 13 441635) = some ⟨13, 2, 0, 867159, 441635, 581, 16384⟩ := by
  decide +kernel

theorem context_13_441635_867159 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441635 ⟨867159, by decide⟩ :=
  accepted_of_selected 13 441635 ⟨867159, by decide⟩ ⟨13, 2, 0, 867159, 441635, 581, 16384⟩
    (by decide) selected_cut_33701

theorem unmarked_context_12_110408_867160 : frontier 9 ⟨867160, by decide⟩
    (prefixCache 12 110408) (prefixPartial 12 110408) = false := by
  decide +kernel

theorem node_context_12_110408_867160 : EJMOriginalGlobalDAGData.nodes 9 ⟨867160, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨867123, by decide⟩,⟨867154, by decide⟩,⟨867159, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110408_867160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110408 ⟨867160, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110408
    ⟨867160, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨867123, by decide⟩,⟨867154, by decide⟩,⟨867159, by decide⟩]) unmarked_context_12_110408_867160 node_context_12_110408_867160
  intro a
  fin_cases a
  · exact context_13_441632_3444
  · exact context_13_441633_867123
  · exact context_13_441634_867154
  · exact context_13_441635_867159

theorem selected_cut_33702 : selected 9 ⟨867225, by decide⟩
    (prefixPartial 12 110409) = some ⟨12, 2, 0, 867225, 110409, 3985, 65536⟩ := by
  decide +kernel

theorem context_12_110409_867225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110409 ⟨867225, by decide⟩ :=
  accepted_of_selected 12 110409 ⟨867225, by decide⟩ ⟨12, 2, 0, 867225, 110409, 3985, 65536⟩
    (by decide) selected_cut_33702

theorem selected_cut_33703 : selected 9 ⟨867284, by decide⟩
    (prefixPartial 12 110410) = some ⟨12, 2, 0, 867284, 110410, 3809, 65536⟩ := by
  decide +kernel

theorem context_12_110410_867284 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110410 ⟨867284, by decide⟩ :=
  accepted_of_selected 12 110410 ⟨867284, by decide⟩ ⟨12, 2, 0, 867284, 110410, 3809, 65536⟩
    (by decide) selected_cut_33703

theorem selected_cut_33704 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 441644) = some ⟨13, 1, 0, 3444, 441644, 1, 16384⟩ := by
  decide +kernel

theorem context_13_441644_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441644 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 441644 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 441644, 1, 16384⟩
    (by decide) selected_cut_33704

theorem selected_cut_33705 : selected 8 ⟨867317, by decide⟩
    (prefixPartial 13 441645) = some ⟨13, 2, 0, 867317, 441645, 2333, 16384⟩ := by
  decide +kernel

theorem context_13_441645_867317 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441645 ⟨867317, by decide⟩ :=
  accepted_of_selected 13 441645 ⟨867317, by decide⟩ ⟨13, 2, 0, 867317, 441645, 2333, 16384⟩
    (by decide) selected_cut_33705

theorem selected_cut_33706 : selected 8 ⟨867349, by decide⟩
    (prefixPartial 13 441646) = some ⟨13, 2, 0, 867349, 441646, 1373, 16384⟩ := by
  decide +kernel

theorem context_13_441646_867349 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441646 ⟨867349, by decide⟩ :=
  accepted_of_selected 13 441646 ⟨867349, by decide⟩ ⟨13, 2, 0, 867349, 441646, 1373, 16384⟩
    (by decide) selected_cut_33706

theorem selected_cut_33707 : selected 8 ⟨867354, by decide⟩
    (prefixPartial 13 441647) = some ⟨13, 2, 0, 867354, 441647, 505, 16384⟩ := by
  decide +kernel

theorem context_13_441647_867354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441647 ⟨867354, by decide⟩ :=
  accepted_of_selected 13 441647 ⟨867354, by decide⟩ ⟨13, 2, 0, 867354, 441647, 505, 16384⟩
    (by decide) selected_cut_33707

theorem unmarked_context_12_110411_867355 : frontier 9 ⟨867355, by decide⟩
    (prefixCache 12 110411) (prefixPartial 12 110411) = false := by
  decide +kernel

theorem node_context_12_110411_867355 : EJMOriginalGlobalDAGData.nodes 9 ⟨867355, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨867317, by decide⟩,⟨867349, by decide⟩,⟨867354, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110411_867355 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110411 ⟨867355, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110411
    ⟨867355, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨867317, by decide⟩,⟨867349, by decide⟩,⟨867354, by decide⟩]) unmarked_context_12_110411_867355 node_context_12_110411_867355
  intro a
  fin_cases a
  · exact context_13_441644_3444
  · exact context_13_441645_867317
  · exact context_13_441646_867349
  · exact context_13_441647_867354

theorem unmarked_context_11_27602_867356 : frontier 10 ⟨867356, by decide⟩
    (prefixCache 11 27602) (prefixPartial 11 27602) = false := by
  decide +kernel

theorem node_context_11_27602_867356 : EJMOriginalGlobalDAGData.nodes 10 ⟨867356, by decide⟩ =
    .split (coordinate 11) (![⟨867160, by decide⟩,⟨867225, by decide⟩,⟨867284, by decide⟩,⟨867355, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27602_867356 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27602 ⟨867356, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27602
    ⟨867356, by decide⟩ (by decide) (![⟨867160, by decide⟩,⟨867225, by decide⟩,⟨867284, by decide⟩,⟨867355, by decide⟩]) unmarked_context_11_27602_867356 node_context_11_27602_867356
  intro a
  fin_cases a
  · exact context_12_110408_867160
  · exact context_12_110409_867225
  · exact context_12_110410_867284
  · exact context_12_110411_867355

theorem selected_cut_33708 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 441648) = some ⟨13, 1, 0, 3444, 441648, 1, 16384⟩ := by
  decide +kernel

theorem context_13_441648_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441648 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 441648 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 441648, 1, 16384⟩
    (by decide) selected_cut_33708

theorem selected_cut_33709 : selected 8 ⟨867384, by decide⟩
    (prefixPartial 13 441649) = some ⟨13, 2, 0, 867384, 441649, 2429, 16384⟩ := by
  decide +kernel

theorem context_13_441649_867384 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441649 ⟨867384, by decide⟩ :=
  accepted_of_selected 13 441649 ⟨867384, by decide⟩ ⟨13, 2, 0, 867384, 441649, 2429, 16384⟩
    (by decide) selected_cut_33709

theorem selected_cut_33710 : selected 8 ⟨867404, by decide⟩
    (prefixPartial 13 441650) = some ⟨13, 2, 0, 867404, 441650, 1097, 16384⟩ := by
  decide +kernel

theorem context_13_441650_867404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441650 ⟨867404, by decide⟩ :=
  accepted_of_selected 13 441650 ⟨867404, by decide⟩ ⟨13, 2, 0, 867404, 441650, 1097, 16384⟩
    (by decide) selected_cut_33710

theorem selected_cut_33711 : selected 8 ⟨867410, by decide⟩
    (prefixPartial 13 441651) = some ⟨13, 2, 0, 867410, 441651, 729, 16384⟩ := by
  decide +kernel

theorem context_13_441651_867410 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441651 ⟨867410, by decide⟩ :=
  accepted_of_selected 13 441651 ⟨867410, by decide⟩ ⟨13, 2, 0, 867410, 441651, 729, 16384⟩
    (by decide) selected_cut_33711

theorem unmarked_context_12_110412_867411 : frontier 9 ⟨867411, by decide⟩
    (prefixCache 12 110412) (prefixPartial 12 110412) = false := by
  decide +kernel

theorem node_context_12_110412_867411 : EJMOriginalGlobalDAGData.nodes 9 ⟨867411, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨867384, by decide⟩,⟨867404, by decide⟩,⟨867410, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110412_867411 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110412 ⟨867411, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110412
    ⟨867411, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨867384, by decide⟩,⟨867404, by decide⟩,⟨867410, by decide⟩]) unmarked_context_12_110412_867411 node_context_12_110412_867411
  intro a
  fin_cases a
  · exact context_13_441648_3444
  · exact context_13_441649_867384
  · exact context_13_441650_867404
  · exact context_13_441651_867410

theorem selected_cut_33712 : selected 9 ⟨867460, by decide⟩
    (prefixPartial 12 110413) = some ⟨12, 2, 0, 867460, 110413, 3781, 65536⟩ := by
  decide +kernel

theorem context_12_110413_867460 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110413 ⟨867460, by decide⟩ :=
  accepted_of_selected 12 110413 ⟨867460, by decide⟩ ⟨12, 2, 0, 867460, 110413, 3781, 65536⟩
    (by decide) selected_cut_33712

theorem selected_cut_33713 : selected 9 ⟨867514, by decide⟩
    (prefixPartial 12 110414) = some ⟨12, 2, 0, 867514, 110414, 3473, 65536⟩ := by
  decide +kernel

theorem context_12_110414_867514 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110414 ⟨867514, by decide⟩ :=
  accepted_of_selected 12 110414 ⟨867514, by decide⟩ ⟨12, 2, 0, 867514, 110414, 3473, 65536⟩
    (by decide) selected_cut_33713

theorem selected_cut_33714 : selected 9 ⟨760511, by decide⟩
    (prefixPartial 12 110415) = some ⟨12, 1, 0, 760511, 110415, 1, 65536⟩ := by
  decide +kernel

theorem context_12_110415_760511 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110415 ⟨760511, by decide⟩ :=
  accepted_of_selected 12 110415 ⟨760511, by decide⟩ ⟨12, 1, 0, 760511, 110415, 1, 65536⟩
    (by decide) selected_cut_33714

theorem unmarked_context_11_27603_867515 : frontier 10 ⟨867515, by decide⟩
    (prefixCache 11 27603) (prefixPartial 11 27603) = false := by
  decide +kernel

theorem node_context_11_27603_867515 : EJMOriginalGlobalDAGData.nodes 10 ⟨867515, by decide⟩ =
    .split (coordinate 11) (![⟨867411, by decide⟩,⟨867460, by decide⟩,⟨867514, by decide⟩,⟨760511, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27603_867515 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27603 ⟨867515, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27603
    ⟨867515, by decide⟩ (by decide) (![⟨867411, by decide⟩,⟨867460, by decide⟩,⟨867514, by decide⟩,⟨760511, by decide⟩]) unmarked_context_11_27603_867515 node_context_11_27603_867515
  intro a
  fin_cases a
  · exact context_12_110412_867411
  · exact context_12_110413_867460
  · exact context_12_110414_867514
  · exact context_12_110415_760511

theorem unmarked_context_10_6900_867516 : frontier 11 ⟨867516, by decide⟩
    (prefixCache 10 6900) (prefixPartial 10 6900) = false := by
  decide +kernel

theorem node_context_10_6900_867516 : EJMOriginalGlobalDAGData.nodes 11 ⟨867516, by decide⟩ =
    .split (coordinate 10) (![⟨866764, by decide⟩,⟨867069, by decide⟩,⟨867356, by decide⟩,⟨867515, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6900_867516 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6900 ⟨867516, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6900
    ⟨867516, by decide⟩ (by decide) (![⟨866764, by decide⟩,⟨867069, by decide⟩,⟨867356, by decide⟩,⟨867515, by decide⟩]) unmarked_context_10_6900_867516 node_context_10_6900_867516
  intro a
  fin_cases a
  · exact context_11_27600_866764
  · exact context_11_27601_867069
  · exact context_11_27602_867356
  · exact context_11_27603_867515

theorem selected_cut_33715 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 441664) = some ⟨13, 1, 0, 3444, 441664, 1, 16384⟩ := by
  decide +kernel

theorem context_13_441664_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441664 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 441664 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 441664, 1, 16384⟩
    (by decide) selected_cut_33715

theorem selected_cut_33716 : selected 8 ⟨867551, by decide⟩
    (prefixPartial 13 441665) = some ⟨13, 2, 0, 867551, 441665, 2325, 16384⟩ := by
  decide +kernel

theorem context_13_441665_867551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441665 ⟨867551, by decide⟩ :=
  accepted_of_selected 13 441665 ⟨867551, by decide⟩ ⟨13, 2, 0, 867551, 441665, 2325, 16384⟩
    (by decide) selected_cut_33716

theorem selected_cut_33717 : selected 8 ⟨867574, by decide⟩
    (prefixPartial 13 441666) = some ⟨13, 2, 0, 867574, 441666, 1317, 16384⟩ := by
  decide +kernel

theorem context_13_441666_867574 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441666 ⟨867574, by decide⟩ :=
  accepted_of_selected 13 441666 ⟨867574, by decide⟩ ⟨13, 2, 0, 867574, 441666, 1317, 16384⟩
    (by decide) selected_cut_33717

theorem selected_cut_33718 : selected 8 ⟨867582, by decide⟩
    (prefixPartial 13 441667) = some ⟨13, 2, 0, 867582, 441667, 761, 16384⟩ := by
  decide +kernel

theorem context_13_441667_867582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441667 ⟨867582, by decide⟩ :=
  accepted_of_selected 13 441667 ⟨867582, by decide⟩ ⟨13, 2, 0, 867582, 441667, 761, 16384⟩
    (by decide) selected_cut_33718

theorem unmarked_context_12_110416_867583 : frontier 9 ⟨867583, by decide⟩
    (prefixCache 12 110416) (prefixPartial 12 110416) = false := by
  decide +kernel

theorem node_context_12_110416_867583 : EJMOriginalGlobalDAGData.nodes 9 ⟨867583, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨867551, by decide⟩,⟨867574, by decide⟩,⟨867582, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110416_867583 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110416 ⟨867583, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110416
    ⟨867583, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨867551, by decide⟩,⟨867574, by decide⟩,⟨867582, by decide⟩]) unmarked_context_12_110416_867583 node_context_12_110416_867583
  intro a
  fin_cases a
  · exact context_13_441664_3444
  · exact context_13_441665_867551
  · exact context_13_441666_867574
  · exact context_13_441667_867582

theorem selected_cut_33719 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 441668) = some ⟨13, 1, 0, 3444, 441668, 1, 16384⟩ := by
  decide +kernel

theorem context_13_441668_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441668 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 441668 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 441668, 1, 16384⟩
    (by decide) selected_cut_33719

theorem selected_cut_33720 : selected 8 ⟨867612, by decide⟩
    (prefixPartial 13 441669) = some ⟨13, 2, 0, 867612, 441669, 2049, 16384⟩ := by
  decide +kernel

theorem context_13_441669_867612 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441669 ⟨867612, by decide⟩ :=
  accepted_of_selected 13 441669 ⟨867612, by decide⟩ ⟨13, 2, 0, 867612, 441669, 2049, 16384⟩
    (by decide) selected_cut_33720

theorem selected_cut_33721 : selected 8 ⟨867630, by decide⟩
    (prefixPartial 13 441670) = some ⟨13, 2, 0, 867630, 441670, 1409, 16384⟩ := by
  decide +kernel

theorem context_13_441670_867630 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441670 ⟨867630, by decide⟩ :=
  accepted_of_selected 13 441670 ⟨867630, by decide⟩ ⟨13, 2, 0, 867630, 441670, 1409, 16384⟩
    (by decide) selected_cut_33721

theorem selected_cut_33722 : selected 8 ⟨867636, by decide⟩
    (prefixPartial 13 441671) = some ⟨13, 2, 0, 867636, 441671, 673, 16384⟩ := by
  decide +kernel

theorem context_13_441671_867636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441671 ⟨867636, by decide⟩ :=
  accepted_of_selected 13 441671 ⟨867636, by decide⟩ ⟨13, 2, 0, 867636, 441671, 673, 16384⟩
    (by decide) selected_cut_33722

theorem unmarked_context_12_110417_867637 : frontier 9 ⟨867637, by decide⟩
    (prefixCache 12 110417) (prefixPartial 12 110417) = false := by
  decide +kernel

theorem node_context_12_110417_867637 : EJMOriginalGlobalDAGData.nodes 9 ⟨867637, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨867612, by decide⟩,⟨867630, by decide⟩,⟨867636, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110417_867637 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110417 ⟨867637, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110417
    ⟨867637, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨867612, by decide⟩,⟨867630, by decide⟩,⟨867636, by decide⟩]) unmarked_context_12_110417_867637 node_context_12_110417_867637
  intro a
  fin_cases a
  · exact context_13_441668_3444
  · exact context_13_441669_867612
  · exact context_13_441670_867630
  · exact context_13_441671_867636

theorem selected_cut_33723 : selected 9 ⟨867710, by decide⟩
    (prefixPartial 12 110418) = some ⟨12, 2, 0, 867710, 110418, 4021, 65536⟩ := by
  decide +kernel

theorem context_12_110418_867710 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110418 ⟨867710, by decide⟩ :=
  accepted_of_selected 12 110418 ⟨867710, by decide⟩ ⟨12, 2, 0, 867710, 110418, 4021, 65536⟩
    (by decide) selected_cut_33723

theorem selected_cut_33724 : selected 9 ⟨867766, by decide⟩
    (prefixPartial 12 110419) = some ⟨12, 2, 0, 867766, 110419, 4017, 65536⟩ := by
  decide +kernel

theorem context_12_110419_867766 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110419 ⟨867766, by decide⟩ :=
  accepted_of_selected 12 110419 ⟨867766, by decide⟩ ⟨12, 2, 0, 867766, 110419, 4017, 65536⟩
    (by decide) selected_cut_33724

theorem unmarked_context_11_27604_867767 : frontier 10 ⟨867767, by decide⟩
    (prefixCache 11 27604) (prefixPartial 11 27604) = false := by
  decide +kernel

theorem node_context_11_27604_867767 : EJMOriginalGlobalDAGData.nodes 10 ⟨867767, by decide⟩ =
    .split (coordinate 11) (![⟨867583, by decide⟩,⟨867637, by decide⟩,⟨867710, by decide⟩,⟨867766, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27604_867767 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27604 ⟨867767, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27604
    ⟨867767, by decide⟩ (by decide) (![⟨867583, by decide⟩,⟨867637, by decide⟩,⟨867710, by decide⟩,⟨867766, by decide⟩]) unmarked_context_11_27604_867767 node_context_11_27604_867767
  intro a
  fin_cases a
  · exact context_12_110416_867583
  · exact context_12_110417_867637
  · exact context_12_110418_867710
  · exact context_12_110419_867766

theorem selected_cut_33725 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 441680) = some ⟨13, 1, 0, 3444, 441680, 1, 16384⟩ := by
  decide +kernel

theorem context_13_441680_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441680 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 441680 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 441680, 1, 16384⟩
    (by decide) selected_cut_33725

theorem selected_cut_33726 : selected 8 ⟨867793, by decide⟩
    (prefixPartial 13 441681) = some ⟨13, 2, 0, 867793, 441681, 2001, 16384⟩ := by
  decide +kernel

theorem context_13_441681_867793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441681 ⟨867793, by decide⟩ :=
  accepted_of_selected 13 441681 ⟨867793, by decide⟩ ⟨13, 2, 0, 867793, 441681, 2001, 16384⟩
    (by decide) selected_cut_33726

theorem selected_cut_33727 : selected 8 ⟨867820, by decide⟩
    (prefixPartial 13 441682) = some ⟨13, 2, 0, 867820, 441682, 1621, 16384⟩ := by
  decide +kernel

theorem context_13_441682_867820 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441682 ⟨867820, by decide⟩ :=
  accepted_of_selected 13 441682 ⟨867820, by decide⟩ ⟨13, 2, 0, 867820, 441682, 1621, 16384⟩
    (by decide) selected_cut_33727

theorem selected_cut_33728 : selected 8 ⟨867833, by decide⟩
    (prefixPartial 13 441683) = some ⟨13, 2, 0, 867833, 441683, 833, 16384⟩ := by
  decide +kernel

theorem context_13_441683_867833 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441683 ⟨867833, by decide⟩ :=
  accepted_of_selected 13 441683 ⟨867833, by decide⟩ ⟨13, 2, 0, 867833, 441683, 833, 16384⟩
    (by decide) selected_cut_33728

theorem unmarked_context_12_110420_867834 : frontier 9 ⟨867834, by decide⟩
    (prefixCache 12 110420) (prefixPartial 12 110420) = false := by
  decide +kernel

theorem node_context_12_110420_867834 : EJMOriginalGlobalDAGData.nodes 9 ⟨867834, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨867793, by decide⟩,⟨867820, by decide⟩,⟨867833, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110420_867834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110420 ⟨867834, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110420
    ⟨867834, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨867793, by decide⟩,⟨867820, by decide⟩,⟨867833, by decide⟩]) unmarked_context_12_110420_867834 node_context_12_110420_867834
  intro a
  fin_cases a
  · exact context_13_441680_3444
  · exact context_13_441681_867793
  · exact context_13_441682_867820
  · exact context_13_441683_867833

theorem selected_cut_33729 : selected 9 ⟨867892, by decide⟩
    (prefixPartial 12 110421) = some ⟨12, 2, 0, 867892, 110421, 3885, 65536⟩ := by
  decide +kernel

theorem context_12_110421_867892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110421 ⟨867892, by decide⟩ :=
  accepted_of_selected 12 110421 ⟨867892, by decide⟩ ⟨12, 2, 0, 867892, 110421, 3885, 65536⟩
    (by decide) selected_cut_33729

theorem selected_cut_33730 : selected 9 ⟨867954, by decide⟩
    (prefixPartial 12 110422) = some ⟨12, 2, 0, 867954, 110422, 3773, 65536⟩ := by
  decide +kernel

theorem context_12_110422_867954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110422 ⟨867954, by decide⟩ :=
  accepted_of_selected 12 110422 ⟨867954, by decide⟩ ⟨12, 2, 0, 867954, 110422, 3773, 65536⟩
    (by decide) selected_cut_33730

theorem selected_cut_33731 : selected 9 ⟨868028, by decide⟩
    (prefixPartial 12 110423) = some ⟨12, 2, 0, 868028, 110423, 4077, 65536⟩ := by
  decide +kernel

theorem context_12_110423_868028 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110423 ⟨868028, by decide⟩ :=
  accepted_of_selected 12 110423 ⟨868028, by decide⟩ ⟨12, 2, 0, 868028, 110423, 4077, 65536⟩
    (by decide) selected_cut_33731

theorem unmarked_context_11_27605_868029 : frontier 10 ⟨868029, by decide⟩
    (prefixCache 11 27605) (prefixPartial 11 27605) = false := by
  decide +kernel

theorem node_context_11_27605_868029 : EJMOriginalGlobalDAGData.nodes 10 ⟨868029, by decide⟩ =
    .split (coordinate 11) (![⟨867834, by decide⟩,⟨867892, by decide⟩,⟨867954, by decide⟩,⟨868028, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27605_868029 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27605 ⟨868029, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27605
    ⟨868029, by decide⟩ (by decide) (![⟨867834, by decide⟩,⟨867892, by decide⟩,⟨867954, by decide⟩,⟨868028, by decide⟩]) unmarked_context_11_27605_868029 node_context_11_27605_868029
  intro a
  fin_cases a
  · exact context_12_110420_867834
  · exact context_12_110421_867892
  · exact context_12_110422_867954
  · exact context_12_110423_868028

theorem selected_cut_33732 : selected 9 ⟨868098, by decide⟩
    (prefixPartial 12 110424) = some ⟨12, 2, 0, 868098, 110424, 3869, 65536⟩ := by
  decide +kernel

theorem context_12_110424_868098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110424 ⟨868098, by decide⟩ :=
  accepted_of_selected 12 110424 ⟨868098, by decide⟩ ⟨12, 2, 0, 868098, 110424, 3869, 65536⟩
    (by decide) selected_cut_33732

theorem selected_cut_33733 : selected 9 ⟨868149, by decide⟩
    (prefixPartial 12 110425) = some ⟨12, 2, 0, 868149, 110425, 3329, 65536⟩ := by
  decide +kernel

theorem context_12_110425_868149 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110425 ⟨868149, by decide⟩ :=
  accepted_of_selected 12 110425 ⟨868149, by decide⟩ ⟨12, 2, 0, 868149, 110425, 3329, 65536⟩
    (by decide) selected_cut_33733

theorem selected_cut_33734 : selected 9 ⟨868190, by decide⟩
    (prefixPartial 12 110426) = some ⟨12, 2, 0, 868190, 110426, 3037, 65536⟩ := by
  decide +kernel

theorem context_12_110426_868190 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110426 ⟨868190, by decide⟩ :=
  accepted_of_selected 12 110426 ⟨868190, by decide⟩ ⟨12, 2, 0, 868190, 110426, 3037, 65536⟩
    (by decide) selected_cut_33734

theorem selected_cut_33735 : selected 9 ⟨868248, by decide⟩
    (prefixPartial 12 110427) = some ⟨12, 2, 0, 868248, 110427, 3501, 65536⟩ := by
  decide +kernel

theorem context_12_110427_868248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110427 ⟨868248, by decide⟩ :=
  accepted_of_selected 12 110427 ⟨868248, by decide⟩ ⟨12, 2, 0, 868248, 110427, 3501, 65536⟩
    (by decide) selected_cut_33735

theorem unmarked_context_11_27606_868249 : frontier 10 ⟨868249, by decide⟩
    (prefixCache 11 27606) (prefixPartial 11 27606) = false := by
  decide +kernel

theorem node_context_11_27606_868249 : EJMOriginalGlobalDAGData.nodes 10 ⟨868249, by decide⟩ =
    .split (coordinate 11) (![⟨868098, by decide⟩,⟨868149, by decide⟩,⟨868190, by decide⟩,⟨868248, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27606_868249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27606 ⟨868249, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27606
    ⟨868249, by decide⟩ (by decide) (![⟨868098, by decide⟩,⟨868149, by decide⟩,⟨868190, by decide⟩,⟨868248, by decide⟩]) unmarked_context_11_27606_868249 node_context_11_27606_868249
  intro a
  fin_cases a
  · exact context_12_110424_868098
  · exact context_12_110425_868149
  · exact context_12_110426_868190
  · exact context_12_110427_868248

theorem selected_cut_33736 : selected 9 ⟨868290, by decide⟩
    (prefixPartial 12 110428) = some ⟨12, 2, 0, 868290, 110428, 3241, 65536⟩ := by
  decide +kernel

theorem context_12_110428_868290 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110428 ⟨868290, by decide⟩ :=
  accepted_of_selected 12 110428 ⟨868290, by decide⟩ ⟨12, 2, 0, 868290, 110428, 3241, 65536⟩
    (by decide) selected_cut_33736

theorem selected_cut_33737 : selected 9 ⟨868333, by decide⟩
    (prefixPartial 12 110429) = some ⟨12, 2, 0, 868333, 110429, 3157, 65536⟩ := by
  decide +kernel

theorem context_12_110429_868333 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110429 ⟨868333, by decide⟩ :=
  accepted_of_selected 12 110429 ⟨868333, by decide⟩ ⟨12, 2, 0, 868333, 110429, 3157, 65536⟩
    (by decide) selected_cut_33737

theorem selected_cut_33738 : selected 9 ⟨868375, by decide⟩
    (prefixPartial 12 110430) = some ⟨12, 2, 0, 868375, 110430, 2761, 65536⟩ := by
  decide +kernel

theorem context_12_110430_868375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110430 ⟨868375, by decide⟩ :=
  accepted_of_selected 12 110430 ⟨868375, by decide⟩ ⟨12, 2, 0, 868375, 110430, 2761, 65536⟩
    (by decide) selected_cut_33738

theorem selected_cut_33739 : selected 9 ⟨757807, by decide⟩
    (prefixPartial 12 110431) = some ⟨12, 1, 0, 757807, 110431, 1, 65536⟩ := by
  decide +kernel

theorem context_12_110431_757807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110431 ⟨757807, by decide⟩ :=
  accepted_of_selected 12 110431 ⟨757807, by decide⟩ ⟨12, 1, 0, 757807, 110431, 1, 65536⟩
    (by decide) selected_cut_33739

theorem unmarked_context_11_27607_868376 : frontier 10 ⟨868376, by decide⟩
    (prefixCache 11 27607) (prefixPartial 11 27607) = false := by
  decide +kernel

theorem node_context_11_27607_868376 : EJMOriginalGlobalDAGData.nodes 10 ⟨868376, by decide⟩ =
    .split (coordinate 11) (![⟨868290, by decide⟩,⟨868333, by decide⟩,⟨868375, by decide⟩,⟨757807, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27607_868376 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27607 ⟨868376, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27607
    ⟨868376, by decide⟩ (by decide) (![⟨868290, by decide⟩,⟨868333, by decide⟩,⟨868375, by decide⟩,⟨757807, by decide⟩]) unmarked_context_11_27607_868376 node_context_11_27607_868376
  intro a
  fin_cases a
  · exact context_12_110428_868290
  · exact context_12_110429_868333
  · exact context_12_110430_868375
  · exact context_12_110431_757807

theorem unmarked_context_10_6901_868377 : frontier 11 ⟨868377, by decide⟩
    (prefixCache 10 6901) (prefixPartial 10 6901) = false := by
  decide +kernel

theorem node_context_10_6901_868377 : EJMOriginalGlobalDAGData.nodes 11 ⟨868377, by decide⟩ =
    .split (coordinate 10) (![⟨867767, by decide⟩,⟨868029, by decide⟩,⟨868249, by decide⟩,⟨868376, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6901_868377 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6901 ⟨868377, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6901
    ⟨868377, by decide⟩ (by decide) (![⟨867767, by decide⟩,⟨868029, by decide⟩,⟨868249, by decide⟩,⟨868376, by decide⟩]) unmarked_context_10_6901_868377 node_context_10_6901_868377
  intro a
  fin_cases a
  · exact context_11_27604_867767
  · exact context_11_27605_868029
  · exact context_11_27606_868249
  · exact context_11_27607_868376

theorem selected_cut_33740 : selected 9 ⟨868433, by decide⟩
    (prefixPartial 12 110432) = some ⟨12, 2, 0, 868433, 110432, 3705, 65536⟩ := by
  decide +kernel

theorem context_12_110432_868433 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110432 ⟨868433, by decide⟩ :=
  accepted_of_selected 12 110432 ⟨868433, by decide⟩ ⟨12, 2, 0, 868433, 110432, 3705, 65536⟩
    (by decide) selected_cut_33740

theorem selected_cut_33741 : selected 9 ⟨868487, by decide⟩
    (prefixPartial 12 110433) = some ⟨12, 2, 0, 868487, 110433, 3477, 65536⟩ := by
  decide +kernel

theorem context_12_110433_868487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110433 ⟨868487, by decide⟩ :=
  accepted_of_selected 12 110433 ⟨868487, by decide⟩ ⟨12, 2, 0, 868487, 110433, 3477, 65536⟩
    (by decide) selected_cut_33741

theorem selected_cut_33742 : selected 9 ⟨868540, by decide⟩
    (prefixPartial 12 110434) = some ⟨12, 2, 0, 868540, 110434, 3441, 65536⟩ := by
  decide +kernel

theorem context_12_110434_868540 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110434 ⟨868540, by decide⟩ :=
  accepted_of_selected 12 110434 ⟨868540, by decide⟩ ⟨12, 2, 0, 868540, 110434, 3441, 65536⟩
    (by decide) selected_cut_33742

theorem selected_cut_33743 : selected 9 ⟨868600, by decide⟩
    (prefixPartial 12 110435) = some ⟨12, 2, 0, 868600, 110435, 3381, 65536⟩ := by
  decide +kernel

theorem context_12_110435_868600 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110435 ⟨868600, by decide⟩ :=
  accepted_of_selected 12 110435 ⟨868600, by decide⟩ ⟨12, 2, 0, 868600, 110435, 3381, 65536⟩
    (by decide) selected_cut_33743

theorem unmarked_context_11_27608_868601 : frontier 10 ⟨868601, by decide⟩
    (prefixCache 11 27608) (prefixPartial 11 27608) = false := by
  decide +kernel

theorem node_context_11_27608_868601 : EJMOriginalGlobalDAGData.nodes 10 ⟨868601, by decide⟩ =
    .split (coordinate 11) (![⟨868433, by decide⟩,⟨868487, by decide⟩,⟨868540, by decide⟩,⟨868600, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27608_868601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27608 ⟨868601, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27608
    ⟨868601, by decide⟩ (by decide) (![⟨868433, by decide⟩,⟨868487, by decide⟩,⟨868540, by decide⟩,⟨868600, by decide⟩]) unmarked_context_11_27608_868601 node_context_11_27608_868601
  intro a
  fin_cases a
  · exact context_12_110432_868433
  · exact context_12_110433_868487
  · exact context_12_110434_868540
  · exact context_12_110435_868600

theorem selected_cut_33744 : selected 9 ⟨868654, by decide⟩
    (prefixPartial 12 110436) = some ⟨12, 2, 0, 868654, 110436, 3777, 65536⟩ := by
  decide +kernel

theorem context_12_110436_868654 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110436 ⟨868654, by decide⟩ :=
  accepted_of_selected 12 110436 ⟨868654, by decide⟩ ⟨12, 2, 0, 868654, 110436, 3777, 65536⟩
    (by decide) selected_cut_33744

theorem selected_cut_33745 : selected 9 ⟨868714, by decide⟩
    (prefixPartial 12 110437) = some ⟨12, 2, 0, 868714, 110437, 3393, 65536⟩ := by
  decide +kernel

theorem context_12_110437_868714 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110437 ⟨868714, by decide⟩ :=
  accepted_of_selected 12 110437 ⟨868714, by decide⟩ ⟨12, 2, 0, 868714, 110437, 3393, 65536⟩
    (by decide) selected_cut_33745

theorem selected_cut_33746 : selected 9 ⟨868779, by decide⟩
    (prefixPartial 12 110438) = some ⟨12, 2, 0, 868779, 110438, 3461, 65536⟩ := by
  decide +kernel

theorem context_12_110438_868779 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110438 ⟨868779, by decide⟩ :=
  accepted_of_selected 12 110438 ⟨868779, by decide⟩ ⟨12, 2, 0, 868779, 110438, 3461, 65536⟩
    (by decide) selected_cut_33746

theorem selected_cut_33747 : selected 9 ⟨868844, by decide⟩
    (prefixPartial 12 110439) = some ⟨12, 2, 0, 868844, 110439, 3629, 65536⟩ := by
  decide +kernel

theorem context_12_110439_868844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110439 ⟨868844, by decide⟩ :=
  accepted_of_selected 12 110439 ⟨868844, by decide⟩ ⟨12, 2, 0, 868844, 110439, 3629, 65536⟩
    (by decide) selected_cut_33747

theorem unmarked_context_11_27609_868845 : frontier 10 ⟨868845, by decide⟩
    (prefixCache 11 27609) (prefixPartial 11 27609) = false := by
  decide +kernel

theorem node_context_11_27609_868845 : EJMOriginalGlobalDAGData.nodes 10 ⟨868845, by decide⟩ =
    .split (coordinate 11) (![⟨868654, by decide⟩,⟨868714, by decide⟩,⟨868779, by decide⟩,⟨868844, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27609_868845 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27609 ⟨868845, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27609
    ⟨868845, by decide⟩ (by decide) (![⟨868654, by decide⟩,⟨868714, by decide⟩,⟨868779, by decide⟩,⟨868844, by decide⟩]) unmarked_context_11_27609_868845 node_context_11_27609_868845
  intro a
  fin_cases a
  · exact context_12_110436_868654
  · exact context_12_110437_868714
  · exact context_12_110438_868779
  · exact context_12_110439_868844

theorem selected_cut_33748 : selected 9 ⟨868895, by decide⟩
    (prefixPartial 12 110440) = some ⟨12, 2, 0, 868895, 110440, 3113, 65536⟩ := by
  decide +kernel

theorem context_12_110440_868895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110440 ⟨868895, by decide⟩ :=
  accepted_of_selected 12 110440 ⟨868895, by decide⟩ ⟨12, 2, 0, 868895, 110440, 3113, 65536⟩
    (by decide) selected_cut_33748

theorem selected_cut_33749 : selected 9 ⟨868939, by decide⟩
    (prefixPartial 12 110441) = some ⟨12, 2, 0, 868939, 110441, 2845, 65536⟩ := by
  decide +kernel

theorem context_12_110441_868939 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110441 ⟨868939, by decide⟩ :=
  accepted_of_selected 12 110441 ⟨868939, by decide⟩ ⟨12, 2, 0, 868939, 110441, 2845, 65536⟩
    (by decide) selected_cut_33749

theorem selected_cut_33750 : selected 9 ⟨868977, by decide⟩
    (prefixPartial 12 110442) = some ⟨12, 2, 0, 868977, 110442, 2613, 65536⟩ := by
  decide +kernel

theorem context_12_110442_868977 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110442 ⟨868977, by decide⟩ :=
  accepted_of_selected 12 110442 ⟨868977, by decide⟩ ⟨12, 2, 0, 868977, 110442, 2613, 65536⟩
    (by decide) selected_cut_33750

theorem selected_cut_33751 : selected 9 ⟨869025, by decide⟩
    (prefixPartial 12 110443) = some ⟨12, 2, 0, 869025, 110443, 2829, 65536⟩ := by
  decide +kernel

theorem context_12_110443_869025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110443 ⟨869025, by decide⟩ :=
  accepted_of_selected 12 110443 ⟨869025, by decide⟩ ⟨12, 2, 0, 869025, 110443, 2829, 65536⟩
    (by decide) selected_cut_33751

theorem unmarked_context_11_27610_869026 : frontier 10 ⟨869026, by decide⟩
    (prefixCache 11 27610) (prefixPartial 11 27610) = false := by
  decide +kernel

theorem node_context_11_27610_869026 : EJMOriginalGlobalDAGData.nodes 10 ⟨869026, by decide⟩ =
    .split (coordinate 11) (![⟨868895, by decide⟩,⟨868939, by decide⟩,⟨868977, by decide⟩,⟨869025, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27610_869026 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27610 ⟨869026, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27610
    ⟨869026, by decide⟩ (by decide) (![⟨868895, by decide⟩,⟨868939, by decide⟩,⟨868977, by decide⟩,⟨869025, by decide⟩]) unmarked_context_11_27610_869026 node_context_11_27610_869026
  intro a
  fin_cases a
  · exact context_12_110440_868895
  · exact context_12_110441_868939
  · exact context_12_110442_868977
  · exact context_12_110443_869025

theorem selected_cut_33752 : selected 9 ⟨869069, by decide⟩
    (prefixPartial 12 110444) = some ⟨12, 2, 0, 869069, 110444, 2821, 65536⟩ := by
  decide +kernel

theorem context_12_110444_869069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110444 ⟨869069, by decide⟩ :=
  accepted_of_selected 12 110444 ⟨869069, by decide⟩ ⟨12, 2, 0, 869069, 110444, 2821, 65536⟩
    (by decide) selected_cut_33752

theorem selected_cut_33753 : selected 9 ⟨869101, by decide⟩
    (prefixPartial 12 110445) = some ⟨12, 2, 0, 869101, 110445, 2713, 65536⟩ := by
  decide +kernel

theorem context_12_110445_869101 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110445 ⟨869101, by decide⟩ :=
  accepted_of_selected 12 110445 ⟨869101, by decide⟩ ⟨12, 2, 0, 869101, 110445, 2713, 65536⟩
    (by decide) selected_cut_33753

theorem selected_cut_33754 : selected 9 ⟨869143, by decide⟩
    (prefixPartial 12 110446) = some ⟨12, 2, 0, 869143, 110446, 2505, 65536⟩ := by
  decide +kernel

theorem context_12_110446_869143 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110446 ⟨869143, by decide⟩ :=
  accepted_of_selected 12 110446 ⟨869143, by decide⟩ ⟨12, 2, 0, 869143, 110446, 2505, 65536⟩
    (by decide) selected_cut_33754

theorem selected_cut_33755 : selected 9 ⟨758968, by decide⟩
    (prefixPartial 12 110447) = some ⟨12, 1, 0, 758968, 110447, 1, 65536⟩ := by
  decide +kernel

theorem context_12_110447_758968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110447 ⟨758968, by decide⟩ :=
  accepted_of_selected 12 110447 ⟨758968, by decide⟩ ⟨12, 1, 0, 758968, 110447, 1, 65536⟩
    (by decide) selected_cut_33755

theorem unmarked_context_11_27611_869144 : frontier 10 ⟨869144, by decide⟩
    (prefixCache 11 27611) (prefixPartial 11 27611) = false := by
  decide +kernel

theorem node_context_11_27611_869144 : EJMOriginalGlobalDAGData.nodes 10 ⟨869144, by decide⟩ =
    .split (coordinate 11) (![⟨869069, by decide⟩,⟨869101, by decide⟩,⟨869143, by decide⟩,⟨758968, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27611_869144 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27611 ⟨869144, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27611
    ⟨869144, by decide⟩ (by decide) (![⟨869069, by decide⟩,⟨869101, by decide⟩,⟨869143, by decide⟩,⟨758968, by decide⟩]) unmarked_context_11_27611_869144 node_context_11_27611_869144
  intro a
  fin_cases a
  · exact context_12_110444_869069
  · exact context_12_110445_869101
  · exact context_12_110446_869143
  · exact context_12_110447_758968

theorem unmarked_context_10_6902_869145 : frontier 11 ⟨869145, by decide⟩
    (prefixCache 10 6902) (prefixPartial 10 6902) = false := by
  decide +kernel

theorem node_context_10_6902_869145 : EJMOriginalGlobalDAGData.nodes 11 ⟨869145, by decide⟩ =
    .split (coordinate 10) (![⟨868601, by decide⟩,⟨868845, by decide⟩,⟨869026, by decide⟩,⟨869144, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6902_869145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6902 ⟨869145, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6902
    ⟨869145, by decide⟩ (by decide) (![⟨868601, by decide⟩,⟨868845, by decide⟩,⟨869026, by decide⟩,⟨869144, by decide⟩]) unmarked_context_10_6902_869145 node_context_10_6902_869145
  intro a
  fin_cases a
  · exact context_11_27608_868601
  · exact context_11_27609_868845
  · exact context_11_27610_869026
  · exact context_11_27611_869144

theorem selected_cut_33756 : selected 9 ⟨869189, by decide⟩
    (prefixPartial 12 110448) = some ⟨12, 2, 0, 869189, 110448, 2837, 65536⟩ := by
  decide +kernel

theorem context_12_110448_869189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110448 ⟨869189, by decide⟩ :=
  accepted_of_selected 12 110448 ⟨869189, by decide⟩ ⟨12, 2, 0, 869189, 110448, 2837, 65536⟩
    (by decide) selected_cut_33756

theorem selected_cut_33757 : selected 9 ⟨869229, by decide⟩
    (prefixPartial 12 110449) = some ⟨12, 2, 0, 869229, 110449, 2553, 65536⟩ := by
  decide +kernel

theorem context_12_110449_869229 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110449 ⟨869229, by decide⟩ :=
  accepted_of_selected 12 110449 ⟨869229, by decide⟩ ⟨12, 2, 0, 869229, 110449, 2553, 65536⟩
    (by decide) selected_cut_33757

theorem selected_cut_33758 : selected 9 ⟨869270, by decide⟩
    (prefixPartial 12 110450) = some ⟨12, 2, 0, 869270, 110450, 2541, 65536⟩ := by
  decide +kernel

theorem context_12_110450_869270 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110450 ⟨869270, by decide⟩ :=
  accepted_of_selected 12 110450 ⟨869270, by decide⟩ ⟨12, 2, 0, 869270, 110450, 2541, 65536⟩
    (by decide) selected_cut_33758

theorem selected_cut_33759 : selected 9 ⟨869302, by decide⟩
    (prefixPartial 12 110451) = some ⟨12, 2, 0, 869302, 110451, 2361, 65536⟩ := by
  decide +kernel

theorem context_12_110451_869302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110451 ⟨869302, by decide⟩ :=
  accepted_of_selected 12 110451 ⟨869302, by decide⟩ ⟨12, 2, 0, 869302, 110451, 2361, 65536⟩
    (by decide) selected_cut_33759

theorem unmarked_context_11_27612_869303 : frontier 10 ⟨869303, by decide⟩
    (prefixCache 11 27612) (prefixPartial 11 27612) = false := by
  decide +kernel

theorem node_context_11_27612_869303 : EJMOriginalGlobalDAGData.nodes 10 ⟨869303, by decide⟩ =
    .split (coordinate 11) (![⟨869189, by decide⟩,⟨869229, by decide⟩,⟨869270, by decide⟩,⟨869302, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27612_869303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27612 ⟨869303, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27612
    ⟨869303, by decide⟩ (by decide) (![⟨869189, by decide⟩,⟨869229, by decide⟩,⟨869270, by decide⟩,⟨869302, by decide⟩]) unmarked_context_11_27612_869303 node_context_11_27612_869303
  intro a
  fin_cases a
  · exact context_12_110448_869189
  · exact context_12_110449_869229
  · exact context_12_110450_869270
  · exact context_12_110451_869302

theorem selected_cut_33760 : selected 9 ⟨869344, by decide⟩
    (prefixPartial 12 110452) = some ⟨12, 2, 0, 869344, 110452, 2745, 65536⟩ := by
  decide +kernel

theorem context_12_110452_869344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110452 ⟨869344, by decide⟩ :=
  accepted_of_selected 12 110452 ⟨869344, by decide⟩ ⟨12, 2, 0, 869344, 110452, 2745, 65536⟩
    (by decide) selected_cut_33760

theorem selected_cut_33761 : selected 9 ⟨869372, by decide⟩
    (prefixPartial 12 110453) = some ⟨12, 2, 0, 869372, 110453, 2405, 65536⟩ := by
  decide +kernel

theorem context_12_110453_869372 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110453 ⟨869372, by decide⟩ :=
  accepted_of_selected 12 110453 ⟨869372, by decide⟩ ⟨12, 2, 0, 869372, 110453, 2405, 65536⟩
    (by decide) selected_cut_33761

theorem selected_cut_33762 : selected 9 ⟨869407, by decide⟩
    (prefixPartial 12 110454) = some ⟨12, 2, 0, 869407, 110454, 2401, 65536⟩ := by
  decide +kernel

theorem context_12_110454_869407 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110454 ⟨869407, by decide⟩ :=
  accepted_of_selected 12 110454 ⟨869407, by decide⟩ ⟨12, 2, 0, 869407, 110454, 2401, 65536⟩
    (by decide) selected_cut_33762

theorem selected_cut_33763 : selected 9 ⟨869445, by decide⟩
    (prefixPartial 12 110455) = some ⟨12, 2, 0, 869445, 110455, 2457, 65536⟩ := by
  decide +kernel

theorem context_12_110455_869445 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110455 ⟨869445, by decide⟩ :=
  accepted_of_selected 12 110455 ⟨869445, by decide⟩ ⟨12, 2, 0, 869445, 110455, 2457, 65536⟩
    (by decide) selected_cut_33763

theorem unmarked_context_11_27613_869446 : frontier 10 ⟨869446, by decide⟩
    (prefixCache 11 27613) (prefixPartial 11 27613) = false := by
  decide +kernel

theorem node_context_11_27613_869446 : EJMOriginalGlobalDAGData.nodes 10 ⟨869446, by decide⟩ =
    .split (coordinate 11) (![⟨869344, by decide⟩,⟨869372, by decide⟩,⟨869407, by decide⟩,⟨869445, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27613_869446 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27613 ⟨869446, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27613
    ⟨869446, by decide⟩ (by decide) (![⟨869344, by decide⟩,⟨869372, by decide⟩,⟨869407, by decide⟩,⟨869445, by decide⟩]) unmarked_context_11_27613_869446 node_context_11_27613_869446
  intro a
  fin_cases a
  · exact context_12_110452_869344
  · exact context_12_110453_869372
  · exact context_12_110454_869407
  · exact context_12_110455_869445

theorem selected_cut_33764 : selected 9 ⟨869486, by decide⟩
    (prefixPartial 12 110456) = some ⟨12, 2, 0, 869486, 110456, 2377, 65536⟩ := by
  decide +kernel

theorem context_12_110456_869486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110456 ⟨869486, by decide⟩ :=
  accepted_of_selected 12 110456 ⟨869486, by decide⟩ ⟨12, 2, 0, 869486, 110456, 2377, 65536⟩
    (by decide) selected_cut_33764

theorem selected_cut_33765 : selected 9 ⟨869511, by decide⟩
    (prefixPartial 12 110457) = some ⟨12, 2, 0, 869511, 110457, 2049, 65536⟩ := by
  decide +kernel

theorem context_12_110457_869511 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110457 ⟨869511, by decide⟩ :=
  accepted_of_selected 12 110457 ⟨869511, by decide⟩ ⟨12, 2, 0, 869511, 110457, 2049, 65536⟩
    (by decide) selected_cut_33765

theorem selected_cut_33766 : selected 9 ⟨869537, by decide⟩
    (prefixPartial 12 110458) = some ⟨12, 2, 0, 869537, 110458, 1881, 65536⟩ := by
  decide +kernel

theorem context_12_110458_869537 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110458 ⟨869537, by decide⟩ :=
  accepted_of_selected 12 110458 ⟨869537, by decide⟩ ⟨12, 2, 0, 869537, 110458, 1881, 65536⟩
    (by decide) selected_cut_33766

theorem selected_cut_33767 : selected 9 ⟨869563, by decide⟩
    (prefixPartial 12 110459) = some ⟨12, 2, 0, 869563, 110459, 1917, 65536⟩ := by
  decide +kernel

theorem context_12_110459_869563 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110459 ⟨869563, by decide⟩ :=
  accepted_of_selected 12 110459 ⟨869563, by decide⟩ ⟨12, 2, 0, 869563, 110459, 1917, 65536⟩
    (by decide) selected_cut_33767

theorem unmarked_context_11_27614_869564 : frontier 10 ⟨869564, by decide⟩
    (prefixCache 11 27614) (prefixPartial 11 27614) = false := by
  decide +kernel

theorem node_context_11_27614_869564 : EJMOriginalGlobalDAGData.nodes 10 ⟨869564, by decide⟩ =
    .split (coordinate 11) (![⟨869486, by decide⟩,⟨869511, by decide⟩,⟨869537, by decide⟩,⟨869563, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27614_869564 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27614 ⟨869564, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27614
    ⟨869564, by decide⟩ (by decide) (![⟨869486, by decide⟩,⟨869511, by decide⟩,⟨869537, by decide⟩,⟨869563, by decide⟩]) unmarked_context_11_27614_869564 node_context_11_27614_869564
  intro a
  fin_cases a
  · exact context_12_110456_869486
  · exact context_12_110457_869511
  · exact context_12_110458_869537
  · exact context_12_110459_869563

theorem selected_cut_33768 : selected 10 ⟨869565, by decide⟩
    (prefixPartial 11 27615) = some ⟨11, 2, 0, 869565, 27615, 5, 262144⟩ := by
  decide +kernel

theorem context_11_27615_869565 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27615 ⟨869565, by decide⟩ :=
  accepted_of_selected 11 27615 ⟨869565, by decide⟩ ⟨11, 2, 0, 869565, 27615, 5, 262144⟩
    (by decide) selected_cut_33768

theorem unmarked_context_10_6903_869566 : frontier 11 ⟨869566, by decide⟩
    (prefixCache 10 6903) (prefixPartial 10 6903) = false := by
  decide +kernel

theorem node_context_10_6903_869566 : EJMOriginalGlobalDAGData.nodes 11 ⟨869566, by decide⟩ =
    .split (coordinate 10) (![⟨869303, by decide⟩,⟨869446, by decide⟩,⟨869564, by decide⟩,⟨869565, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6903_869566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6903 ⟨869566, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6903
    ⟨869566, by decide⟩ (by decide) (![⟨869303, by decide⟩,⟨869446, by decide⟩,⟨869564, by decide⟩,⟨869565, by decide⟩]) unmarked_context_10_6903_869566 node_context_10_6903_869566
  intro a
  fin_cases a
  · exact context_11_27612_869303
  · exact context_11_27613_869446
  · exact context_11_27614_869564
  · exact context_11_27615_869565

theorem unmarked_context_9_1725_869567 : frontier 12 ⟨869567, by decide⟩
    (prefixCache 9 1725) (prefixPartial 9 1725) = false := by
  decide +kernel

theorem node_context_9_1725_869567 : EJMOriginalGlobalDAGData.nodes 12 ⟨869567, by decide⟩ =
    .split (coordinate 9) (![⟨867516, by decide⟩,⟨868377, by decide⟩,⟨869145, by decide⟩,⟨869566, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1725_869567 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1725 ⟨869567, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1725
    ⟨869567, by decide⟩ (by decide) (![⟨867516, by decide⟩,⟨868377, by decide⟩,⟨869145, by decide⟩,⟨869566, by decide⟩]) unmarked_context_9_1725_869567 node_context_9_1725_869567
  intro a
  fin_cases a
  · exact context_10_6900_867516
  · exact context_10_6901_868377
  · exact context_10_6902_869145
  · exact context_10_6903_869566

theorem selected_cut_33769 : selected 9 ⟨869594, by decide⟩
    (prefixPartial 12 110464) = some ⟨12, 2, 0, 869594, 110464, 2209, 65536⟩ := by
  decide +kernel

theorem context_12_110464_869594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110464 ⟨869594, by decide⟩ :=
  accepted_of_selected 12 110464 ⟨869594, by decide⟩ ⟨12, 2, 0, 869594, 110464, 2209, 65536⟩
    (by decide) selected_cut_33769

theorem selected_cut_33770 : selected 9 ⟨869627, by decide⟩
    (prefixPartial 12 110465) = some ⟨12, 2, 0, 869627, 110465, 2333, 65536⟩ := by
  decide +kernel

theorem context_12_110465_869627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110465 ⟨869627, by decide⟩ :=
  accepted_of_selected 12 110465 ⟨869627, by decide⟩ ⟨12, 2, 0, 869627, 110465, 2333, 65536⟩
    (by decide) selected_cut_33770

theorem selected_cut_33771 : selected 9 ⟨813440, by decide⟩
    (prefixPartial 12 110466) = some ⟨12, 1, 0, 813440, 110466, 1, 65536⟩ := by
  decide +kernel

theorem context_12_110466_813440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110466 ⟨813440, by decide⟩ :=
  accepted_of_selected 12 110466 ⟨813440, by decide⟩ ⟨12, 1, 0, 813440, 110466, 1, 65536⟩
    (by decide) selected_cut_33771

theorem selected_cut_33772 : selected 9 ⟨869658, by decide⟩
    (prefixPartial 12 110467) = some ⟨12, 2, 0, 869658, 110467, 2093, 65536⟩ := by
  decide +kernel

theorem context_12_110467_869658 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110467 ⟨869658, by decide⟩ :=
  accepted_of_selected 12 110467 ⟨869658, by decide⟩ ⟨12, 2, 0, 869658, 110467, 2093, 65536⟩
    (by decide) selected_cut_33772

theorem unmarked_context_11_27616_869659 : frontier 10 ⟨869659, by decide⟩
    (prefixCache 11 27616) (prefixPartial 11 27616) = false := by
  decide +kernel

theorem node_context_11_27616_869659 : EJMOriginalGlobalDAGData.nodes 10 ⟨869659, by decide⟩ =
    .split (coordinate 11) (![⟨869594, by decide⟩,⟨869627, by decide⟩,⟨813440, by decide⟩,⟨869658, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27616_869659 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27616 ⟨869659, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27616
    ⟨869659, by decide⟩ (by decide) (![⟨869594, by decide⟩,⟨869627, by decide⟩,⟨813440, by decide⟩,⟨869658, by decide⟩]) unmarked_context_11_27616_869659 node_context_11_27616_869659
  intro a
  fin_cases a
  · exact context_12_110464_869594
  · exact context_12_110465_869627
  · exact context_12_110466_813440
  · exact context_12_110467_869658

theorem selected_cut_33773 : selected 9 ⟨869695, by decide⟩
    (prefixPartial 12 110468) = some ⟨12, 2, 0, 869695, 110468, 2401, 65536⟩ := by
  decide +kernel

theorem context_12_110468_869695 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110468 ⟨869695, by decide⟩ :=
  accepted_of_selected 12 110468 ⟨869695, by decide⟩ ⟨12, 2, 0, 869695, 110468, 2401, 65536⟩
    (by decide) selected_cut_33773

theorem selected_cut_33774 : selected 9 ⟨869731, by decide⟩
    (prefixPartial 12 110469) = some ⟨12, 2, 0, 869731, 110469, 2377, 65536⟩ := by
  decide +kernel

theorem context_12_110469_869731 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110469 ⟨869731, by decide⟩ :=
  accepted_of_selected 12 110469 ⟨869731, by decide⟩ ⟨12, 2, 0, 869731, 110469, 2377, 65536⟩
    (by decide) selected_cut_33774

theorem selected_cut_33775 : selected 9 ⟨813440, by decide⟩
    (prefixPartial 12 110470) = some ⟨12, 1, 0, 813440, 110470, 1, 65536⟩ := by
  decide +kernel

theorem context_12_110470_813440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110470 ⟨813440, by decide⟩ :=
  accepted_of_selected 12 110470 ⟨813440, by decide⟩ ⟨12, 1, 0, 813440, 110470, 1, 65536⟩
    (by decide) selected_cut_33775

theorem selected_cut_33776 : selected 9 ⟨869768, by decide⟩
    (prefixPartial 12 110471) = some ⟨12, 2, 0, 869768, 110471, 2389, 65536⟩ := by
  decide +kernel

theorem context_12_110471_869768 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110471 ⟨869768, by decide⟩ :=
  accepted_of_selected 12 110471 ⟨869768, by decide⟩ ⟨12, 2, 0, 869768, 110471, 2389, 65536⟩
    (by decide) selected_cut_33776

theorem unmarked_context_11_27617_869769 : frontier 10 ⟨869769, by decide⟩
    (prefixCache 11 27617) (prefixPartial 11 27617) = false := by
  decide +kernel

theorem node_context_11_27617_869769 : EJMOriginalGlobalDAGData.nodes 10 ⟨869769, by decide⟩ =
    .split (coordinate 11) (![⟨869695, by decide⟩,⟨869731, by decide⟩,⟨813440, by decide⟩,⟨869768, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27617_869769 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27617 ⟨869769, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27617
    ⟨869769, by decide⟩ (by decide) (![⟨869695, by decide⟩,⟨869731, by decide⟩,⟨813440, by decide⟩,⟨869768, by decide⟩]) unmarked_context_11_27617_869769 node_context_11_27617_869769
  intro a
  fin_cases a
  · exact context_12_110468_869695
  · exact context_12_110469_869731
  · exact context_12_110470_813440
  · exact context_12_110471_869768

theorem selected_cut_33777 : selected 9 ⟨869813, by decide⟩
    (prefixPartial 12 110472) = some ⟨12, 2, 0, 869813, 110472, 2189, 65536⟩ := by
  decide +kernel

theorem context_12_110472_869813 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110472 ⟨869813, by decide⟩ :=
  accepted_of_selected 12 110472 ⟨869813, by decide⟩ ⟨12, 2, 0, 869813, 110472, 2189, 65536⟩
    (by decide) selected_cut_33777

theorem selected_cut_33778 : selected 9 ⟨869859, by decide⟩
    (prefixPartial 12 110473) = some ⟨12, 2, 0, 869859, 110473, 2233, 65536⟩ := by
  decide +kernel

theorem context_12_110473_869859 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110473 ⟨869859, by decide⟩ :=
  accepted_of_selected 12 110473 ⟨869859, by decide⟩ ⟨12, 2, 0, 869859, 110473, 2233, 65536⟩
    (by decide) selected_cut_33778

theorem selected_cut_33779 : selected 9 ⟨813440, by decide⟩
    (prefixPartial 12 110474) = some ⟨12, 1, 0, 813440, 110474, 1, 65536⟩ := by
  decide +kernel

theorem context_12_110474_813440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110474 ⟨813440, by decide⟩ :=
  accepted_of_selected 12 110474 ⟨813440, by decide⟩ ⟨12, 1, 0, 813440, 110474, 1, 65536⟩
    (by decide) selected_cut_33779

theorem selected_cut_33780 : selected 9 ⟨869905, by decide⟩
    (prefixPartial 12 110475) = some ⟨12, 2, 0, 869905, 110475, 2057, 65536⟩ := by
  decide +kernel

theorem context_12_110475_869905 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110475 ⟨869905, by decide⟩ :=
  accepted_of_selected 12 110475 ⟨869905, by decide⟩ ⟨12, 2, 0, 869905, 110475, 2057, 65536⟩
    (by decide) selected_cut_33780

theorem unmarked_context_11_27618_869906 : frontier 10 ⟨869906, by decide⟩
    (prefixCache 11 27618) (prefixPartial 11 27618) = false := by
  decide +kernel

theorem node_context_11_27618_869906 : EJMOriginalGlobalDAGData.nodes 10 ⟨869906, by decide⟩ =
    .split (coordinate 11) (![⟨869813, by decide⟩,⟨869859, by decide⟩,⟨813440, by decide⟩,⟨869905, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27618_869906 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27618 ⟨869906, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27618
    ⟨869906, by decide⟩ (by decide) (![⟨869813, by decide⟩,⟨869859, by decide⟩,⟨813440, by decide⟩,⟨869905, by decide⟩]) unmarked_context_11_27618_869906 node_context_11_27618_869906
  intro a
  fin_cases a
  · exact context_12_110472_869813
  · exact context_12_110473_869859
  · exact context_12_110474_813440
  · exact context_12_110475_869905

theorem selected_cut_33781 : selected 10 ⟨869957, by decide⟩
    (prefixPartial 11 27619) = some ⟨11, 2, 0, 869957, 27619, 3857, 262144⟩ := by
  decide +kernel

theorem context_11_27619_869957 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27619 ⟨869957, by decide⟩ :=
  accepted_of_selected 11 27619 ⟨869957, by decide⟩ ⟨11, 2, 0, 869957, 27619, 3857, 262144⟩
    (by decide) selected_cut_33781

theorem unmarked_context_10_6904_869958 : frontier 11 ⟨869958, by decide⟩
    (prefixCache 10 6904) (prefixPartial 10 6904) = false := by
  decide +kernel

theorem node_context_10_6904_869958 : EJMOriginalGlobalDAGData.nodes 11 ⟨869958, by decide⟩ =
    .split (coordinate 10) (![⟨869659, by decide⟩,⟨869769, by decide⟩,⟨869906, by decide⟩,⟨869957, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6904_869958 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6904 ⟨869958, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6904
    ⟨869958, by decide⟩ (by decide) (![⟨869659, by decide⟩,⟨869769, by decide⟩,⟨869906, by decide⟩,⟨869957, by decide⟩]) unmarked_context_10_6904_869958 node_context_10_6904_869958
  intro a
  fin_cases a
  · exact context_11_27616_869659
  · exact context_11_27617_869769
  · exact context_11_27618_869906
  · exact context_11_27619_869957

theorem selected_cut_33782 : selected 9 ⟨869988, by decide⟩
    (prefixPartial 12 110480) = some ⟨12, 2, 0, 869988, 110480, 2129, 65536⟩ := by
  decide +kernel

theorem context_12_110480_869988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110480 ⟨869988, by decide⟩ :=
  accepted_of_selected 12 110480 ⟨869988, by decide⟩ ⟨12, 2, 0, 869988, 110480, 2129, 65536⟩
    (by decide) selected_cut_33782

theorem selected_cut_33783 : selected 9 ⟨870022, by decide⟩
    (prefixPartial 12 110481) = some ⟨12, 2, 0, 870022, 110481, 2233, 65536⟩ := by
  decide +kernel

theorem context_12_110481_870022 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110481 ⟨870022, by decide⟩ :=
  accepted_of_selected 12 110481 ⟨870022, by decide⟩ ⟨12, 2, 0, 870022, 110481, 2233, 65536⟩
    (by decide) selected_cut_33783

theorem selected_cut_33784 : selected 9 ⟨870050, by decide⟩
    (prefixPartial 12 110482) = some ⟨12, 2, 0, 870050, 110482, 593, 65536⟩ := by
  decide +kernel

theorem context_12_110482_870050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110482 ⟨870050, by decide⟩ :=
  accepted_of_selected 12 110482 ⟨870050, by decide⟩ ⟨12, 2, 0, 870050, 110482, 593, 65536⟩
    (by decide) selected_cut_33784

theorem selected_cut_33785 : selected 9 ⟨870079, by decide⟩
    (prefixPartial 12 110483) = some ⟨12, 2, 0, 870079, 110483, 1977, 65536⟩ := by
  decide +kernel

theorem context_12_110483_870079 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110483 ⟨870079, by decide⟩ :=
  accepted_of_selected 12 110483 ⟨870079, by decide⟩ ⟨12, 2, 0, 870079, 110483, 1977, 65536⟩
    (by decide) selected_cut_33785

theorem unmarked_context_11_27620_870080 : frontier 10 ⟨870080, by decide⟩
    (prefixCache 11 27620) (prefixPartial 11 27620) = false := by
  decide +kernel

theorem node_context_11_27620_870080 : EJMOriginalGlobalDAGData.nodes 10 ⟨870080, by decide⟩ =
    .split (coordinate 11) (![⟨869988, by decide⟩,⟨870022, by decide⟩,⟨870050, by decide⟩,⟨870079, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27620_870080 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27620 ⟨870080, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27620
    ⟨870080, by decide⟩ (by decide) (![⟨869988, by decide⟩,⟨870022, by decide⟩,⟨870050, by decide⟩,⟨870079, by decide⟩]) unmarked_context_11_27620_870080 node_context_11_27620_870080
  intro a
  fin_cases a
  · exact context_12_110480_869988
  · exact context_12_110481_870022
  · exact context_12_110482_870050
  · exact context_12_110483_870079

theorem selected_cut_33786 : selected 9 ⟨870104, by decide⟩
    (prefixPartial 12 110484) = some ⟨12, 2, 0, 870104, 110484, 2197, 65536⟩ := by
  decide +kernel

theorem context_12_110484_870104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110484 ⟨870104, by decide⟩ :=
  accepted_of_selected 12 110484 ⟨870104, by decide⟩ ⟨12, 2, 0, 870104, 110484, 2197, 65536⟩
    (by decide) selected_cut_33786

theorem selected_cut_33787 : selected 9 ⟨870137, by decide⟩
    (prefixPartial 12 110485) = some ⟨12, 2, 0, 870137, 110485, 2125, 65536⟩ := by
  decide +kernel

theorem context_12_110485_870137 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110485 ⟨870137, by decide⟩ :=
  accepted_of_selected 12 110485 ⟨870137, by decide⟩ ⟨12, 2, 0, 870137, 110485, 2125, 65536⟩
    (by decide) selected_cut_33787

theorem selected_cut_33788 : selected 9 ⟨813979, by decide⟩
    (prefixPartial 12 110486) = some ⟨12, 1, 0, 813979, 110486, 1, 65536⟩ := by
  decide +kernel

theorem context_12_110486_813979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110486 ⟨813979, by decide⟩ :=
  accepted_of_selected 12 110486 ⟨813979, by decide⟩ ⟨12, 1, 0, 813979, 110486, 1, 65536⟩
    (by decide) selected_cut_33788

theorem selected_cut_33789 : selected 9 ⟨870171, by decide⟩
    (prefixPartial 12 110487) = some ⟨12, 2, 0, 870171, 110487, 2077, 65536⟩ := by
  decide +kernel

theorem context_12_110487_870171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110487 ⟨870171, by decide⟩ :=
  accepted_of_selected 12 110487 ⟨870171, by decide⟩ ⟨12, 2, 0, 870171, 110487, 2077, 65536⟩
    (by decide) selected_cut_33789

theorem unmarked_context_11_27621_870172 : frontier 10 ⟨870172, by decide⟩
    (prefixCache 11 27621) (prefixPartial 11 27621) = false := by
  decide +kernel

theorem node_context_11_27621_870172 : EJMOriginalGlobalDAGData.nodes 10 ⟨870172, by decide⟩ =
    .split (coordinate 11) (![⟨870104, by decide⟩,⟨870137, by decide⟩,⟨813979, by decide⟩,⟨870171, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27621_870172 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27621 ⟨870172, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27621
    ⟨870172, by decide⟩ (by decide) (![⟨870104, by decide⟩,⟨870137, by decide⟩,⟨813979, by decide⟩,⟨870171, by decide⟩]) unmarked_context_11_27621_870172 node_context_11_27621_870172
  intro a
  fin_cases a
  · exact context_12_110484_870104
  · exact context_12_110485_870137
  · exact context_12_110486_813979
  · exact context_12_110487_870171

theorem selected_cut_33790 : selected 9 ⟨870202, by decide⟩
    (prefixPartial 12 110488) = some ⟨12, 2, 0, 870202, 110488, 1729, 65536⟩ := by
  decide +kernel

theorem context_12_110488_870202 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110488 ⟨870202, by decide⟩ :=
  accepted_of_selected 12 110488 ⟨870202, by decide⟩ ⟨12, 2, 0, 870202, 110488, 1729, 65536⟩
    (by decide) selected_cut_33790

theorem selected_cut_33791 : selected 9 ⟨870229, by decide⟩
    (prefixPartial 12 110489) = some ⟨12, 2, 0, 870229, 110489, 1821, 65536⟩ := by
  decide +kernel

theorem context_12_110489_870229 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110489 ⟨870229, by decide⟩ :=
  accepted_of_selected 12 110489 ⟨870229, by decide⟩ ⟨12, 2, 0, 870229, 110489, 1821, 65536⟩
    (by decide) selected_cut_33791

theorem selected_cut_33792 : selected 9 ⟨813979, by decide⟩
    (prefixPartial 12 110490) = some ⟨12, 1, 0, 813979, 110490, 1, 65536⟩ := by
  decide +kernel

theorem context_12_110490_813979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110490 ⟨813979, by decide⟩ :=
  accepted_of_selected 12 110490 ⟨813979, by decide⟩ ⟨12, 1, 0, 813979, 110490, 1, 65536⟩
    (by decide) selected_cut_33792

theorem selected_cut_33793 : selected 9 ⟨870252, by decide⟩
    (prefixPartial 12 110491) = some ⟨12, 2, 0, 870252, 110491, 1569, 65536⟩ := by
  decide +kernel

theorem context_12_110491_870252 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110491 ⟨870252, by decide⟩ :=
  accepted_of_selected 12 110491 ⟨870252, by decide⟩ ⟨12, 2, 0, 870252, 110491, 1569, 65536⟩
    (by decide) selected_cut_33793

theorem unmarked_context_11_27622_870253 : frontier 10 ⟨870253, by decide⟩
    (prefixCache 11 27622) (prefixPartial 11 27622) = false := by
  decide +kernel

theorem node_context_11_27622_870253 : EJMOriginalGlobalDAGData.nodes 10 ⟨870253, by decide⟩ =
    .split (coordinate 11) (![⟨870202, by decide⟩,⟨870229, by decide⟩,⟨813979, by decide⟩,⟨870252, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27622_870253 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27622 ⟨870253, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27622
    ⟨870253, by decide⟩ (by decide) (![⟨870202, by decide⟩,⟨870229, by decide⟩,⟨813979, by decide⟩,⟨870252, by decide⟩]) unmarked_context_11_27622_870253 node_context_11_27622_870253
  intro a
  fin_cases a
  · exact context_12_110488_870202
  · exact context_12_110489_870229
  · exact context_12_110490_813979
  · exact context_12_110491_870252

theorem selected_cut_33794 : selected 10 ⟨870295, by decide⟩
    (prefixPartial 11 27623) = some ⟨11, 2, 0, 870295, 27623, 3237, 262144⟩ := by
  decide +kernel

theorem context_11_27623_870295 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27623 ⟨870295, by decide⟩ :=
  accepted_of_selected 11 27623 ⟨870295, by decide⟩ ⟨11, 2, 0, 870295, 27623, 3237, 262144⟩
    (by decide) selected_cut_33794

theorem unmarked_context_10_6905_870296 : frontier 11 ⟨870296, by decide⟩
    (prefixCache 10 6905) (prefixPartial 10 6905) = false := by
  decide +kernel

theorem node_context_10_6905_870296 : EJMOriginalGlobalDAGData.nodes 11 ⟨870296, by decide⟩ =
    .split (coordinate 10) (![⟨870080, by decide⟩,⟨870172, by decide⟩,⟨870253, by decide⟩,⟨870295, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6905_870296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6905 ⟨870296, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6905
    ⟨870296, by decide⟩ (by decide) (![⟨870080, by decide⟩,⟨870172, by decide⟩,⟨870253, by decide⟩,⟨870295, by decide⟩]) unmarked_context_10_6905_870296 node_context_10_6905_870296
  intro a
  fin_cases a
  · exact context_11_27620_870080
  · exact context_11_27621_870172
  · exact context_11_27622_870253
  · exact context_11_27623_870295

theorem selected_cut_33795 : selected 10 ⟨870351, by decide⟩
    (prefixPartial 11 27624) = some ⟨11, 2, 0, 870351, 27624, 3925, 262144⟩ := by
  decide +kernel

theorem context_11_27624_870351 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27624 ⟨870351, by decide⟩ :=
  accepted_of_selected 11 27624 ⟨870351, by decide⟩ ⟨11, 2, 0, 870351, 27624, 3925, 262144⟩
    (by decide) selected_cut_33795

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
