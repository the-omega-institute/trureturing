/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover455
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_43779 : selected 9 ⟨1200515, by decide⟩
    (prefixPartial 12 352527) = some ⟨12, 2, 0, 1200515, 352527, 2769, 65536⟩ := by
  decide +kernel

theorem context_12_352527_1200515 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352527 ⟨1200515, by decide⟩ :=
  accepted_of_selected 12 352527 ⟨1200515, by decide⟩ ⟨12, 2, 0, 1200515, 352527, 2769, 65536⟩
    (by decide) selected_cut_43779

theorem unmarked_context_11_88131_1200516 : frontier 10 ⟨1200516, by decide⟩
    (prefixCache 11 88131) (prefixPartial 11 88131) = false := by
  decide +kernel

theorem node_context_11_88131_1200516 : EJMOriginalGlobalDAGData.nodes 10 ⟨1200516, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1200435, by decide⟩,⟨1200473, by decide⟩,⟨1200515, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88131_1200516 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88131 ⟨1200516, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88131
    ⟨1200516, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1200435, by decide⟩,⟨1200473, by decide⟩,⟨1200515, by decide⟩]) unmarked_context_11_88131_1200516 node_context_11_88131_1200516
  intro a
  fin_cases a
  · exact context_12_352524_448748
  · exact context_12_352525_1200435
  · exact context_12_352526_1200473
  · exact context_12_352527_1200515

theorem unmarked_context_10_22032_1200517 : frontier 11 ⟨1200517, by decide⟩
    (prefixCache 10 22032) (prefixPartial 10 22032) = false := by
  decide +kernel

theorem node_context_10_22032_1200517 : EJMOriginalGlobalDAGData.nodes 11 ⟨1200517, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨167448, by decide⟩,⟨1200407, by decide⟩,⟨1200516, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22032_1200517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22032 ⟨1200517, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22032
    ⟨1200517, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨167448, by decide⟩,⟨1200407, by decide⟩,⟨1200516, by decide⟩]) unmarked_context_10_22032_1200517 node_context_10_22032_1200517
  intro a
  fin_cases a
  · exact context_11_88128_434745
  · exact context_11_88129_167448
  · exact context_11_88130_1200407
  · exact context_11_88131_1200516

theorem selected_cut_43780 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 352528) = some ⟨12, 1, 0, 435160, 352528, 1, 65536⟩ := by
  decide +kernel

theorem context_12_352528_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352528 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 352528 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 352528, 1, 65536⟩
    (by decide) selected_cut_43780

theorem selected_cut_43781 : selected 9 ⟨1200550, by decide⟩
    (prefixPartial 12 352529) = some ⟨12, 2, 0, 1200550, 352529, 2001, 65536⟩ := by
  decide +kernel

theorem context_12_352529_1200550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352529 ⟨1200550, by decide⟩ :=
  accepted_of_selected 12 352529 ⟨1200550, by decide⟩ ⟨12, 2, 0, 1200550, 352529, 2001, 65536⟩
    (by decide) selected_cut_43781

theorem selected_cut_43782 : selected 9 ⟨1200576, by decide⟩
    (prefixPartial 12 352530) = some ⟨12, 2, 0, 1200576, 352530, 2209, 65536⟩ := by
  decide +kernel

theorem context_12_352530_1200576 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352530 ⟨1200576, by decide⟩ :=
  accepted_of_selected 12 352530 ⟨1200576, by decide⟩ ⟨12, 2, 0, 1200576, 352530, 2209, 65536⟩
    (by decide) selected_cut_43782

theorem selected_cut_43783 : selected 9 ⟨1200606, by decide⟩
    (prefixPartial 12 352531) = some ⟨12, 2, 0, 1200606, 352531, 2337, 65536⟩ := by
  decide +kernel

theorem context_12_352531_1200606 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352531 ⟨1200606, by decide⟩ :=
  accepted_of_selected 12 352531 ⟨1200606, by decide⟩ ⟨12, 2, 0, 1200606, 352531, 2337, 65536⟩
    (by decide) selected_cut_43783

theorem unmarked_context_11_88132_1200607 : frontier 10 ⟨1200607, by decide⟩
    (prefixCache 11 88132) (prefixPartial 11 88132) = false := by
  decide +kernel

theorem node_context_11_88132_1200607 : EJMOriginalGlobalDAGData.nodes 10 ⟨1200607, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨1200550, by decide⟩,⟨1200576, by decide⟩,⟨1200606, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88132_1200607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88132 ⟨1200607, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88132
    ⟨1200607, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨1200550, by decide⟩,⟨1200576, by decide⟩,⟨1200606, by decide⟩]) unmarked_context_11_88132_1200607 node_context_11_88132_1200607
  intro a
  fin_cases a
  · exact context_12_352528_435160
  · exact context_12_352529_1200550
  · exact context_12_352530_1200576
  · exact context_12_352531_1200606

theorem selected_cut_43784 : selected 10 ⟨815620, by decide⟩
    (prefixPartial 11 88133) = some ⟨11, 1, 0, 815620, 88133, 1, 262144⟩ := by
  decide +kernel

theorem context_11_88133_815620 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88133 ⟨815620, by decide⟩ :=
  accepted_of_selected 11 88133 ⟨815620, by decide⟩ ⟨11, 1, 0, 815620, 88133, 1, 262144⟩
    (by decide) selected_cut_43784

theorem selected_cut_43785 : selected 9 ⟨1200661, by decide⟩
    (prefixPartial 12 352536) = some ⟨12, 2, 0, 1200661, 352536, 2849, 65536⟩ := by
  decide +kernel

theorem context_12_352536_1200661 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352536 ⟨1200661, by decide⟩ :=
  accepted_of_selected 12 352536 ⟨1200661, by decide⟩ ⟨12, 2, 0, 1200661, 352536, 2849, 65536⟩
    (by decide) selected_cut_43785

theorem selected_cut_43786 : selected 9 ⟨1200724, by decide⟩
    (prefixPartial 12 352537) = some ⟨12, 2, 0, 1200724, 352537, 2613, 65536⟩ := by
  decide +kernel

theorem context_12_352537_1200724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352537 ⟨1200724, by decide⟩ :=
  accepted_of_selected 12 352537 ⟨1200724, by decide⟩ ⟨12, 2, 0, 1200724, 352537, 2613, 65536⟩
    (by decide) selected_cut_43786

theorem selected_cut_43787 : selected 9 ⟨1200773, by decide⟩
    (prefixPartial 12 352538) = some ⟨12, 2, 0, 1200773, 352538, 2641, 65536⟩ := by
  decide +kernel

theorem context_12_352538_1200773 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352538 ⟨1200773, by decide⟩ :=
  accepted_of_selected 12 352538 ⟨1200773, by decide⟩ ⟨12, 2, 0, 1200773, 352538, 2641, 65536⟩
    (by decide) selected_cut_43787

theorem selected_cut_43788 : selected 9 ⟨1200828, by decide⟩
    (prefixPartial 12 352539) = some ⟨12, 2, 0, 1200828, 352539, 2845, 65536⟩ := by
  decide +kernel

theorem context_12_352539_1200828 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352539 ⟨1200828, by decide⟩ :=
  accepted_of_selected 12 352539 ⟨1200828, by decide⟩ ⟨12, 2, 0, 1200828, 352539, 2845, 65536⟩
    (by decide) selected_cut_43788

theorem unmarked_context_11_88134_1200829 : frontier 10 ⟨1200829, by decide⟩
    (prefixCache 11 88134) (prefixPartial 11 88134) = false := by
  decide +kernel

theorem node_context_11_88134_1200829 : EJMOriginalGlobalDAGData.nodes 10 ⟨1200829, by decide⟩ =
    .split (coordinate 11) (![⟨1200661, by decide⟩,⟨1200724, by decide⟩,⟨1200773, by decide⟩,⟨1200828, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88134_1200829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88134 ⟨1200829, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88134
    ⟨1200829, by decide⟩ (by decide) (![⟨1200661, by decide⟩,⟨1200724, by decide⟩,⟨1200773, by decide⟩,⟨1200828, by decide⟩]) unmarked_context_11_88134_1200829 node_context_11_88134_1200829
  intro a
  fin_cases a
  · exact context_12_352536_1200661
  · exact context_12_352537_1200724
  · exact context_12_352538_1200773
  · exact context_12_352539_1200828

theorem selected_cut_43789 : selected 9 ⟨1200869, by decide⟩
    (prefixPartial 12 352540) = some ⟨12, 2, 0, 1200869, 352540, 2501, 65536⟩ := by
  decide +kernel

theorem context_12_352540_1200869 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352540 ⟨1200869, by decide⟩ :=
  accepted_of_selected 12 352540 ⟨1200869, by decide⟩ ⟨12, 2, 0, 1200869, 352540, 2501, 65536⟩
    (by decide) selected_cut_43789

theorem selected_cut_43790 : selected 9 ⟨1200905, by decide⟩
    (prefixPartial 12 352541) = some ⟨12, 2, 0, 1200905, 352541, 2257, 65536⟩ := by
  decide +kernel

theorem context_12_352541_1200905 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352541 ⟨1200905, by decide⟩ :=
  accepted_of_selected 12 352541 ⟨1200905, by decide⟩ ⟨12, 2, 0, 1200905, 352541, 2257, 65536⟩
    (by decide) selected_cut_43790

theorem selected_cut_43791 : selected 9 ⟨1200944, by decide⟩
    (prefixPartial 12 352542) = some ⟨12, 2, 0, 1200944, 352542, 2413, 65536⟩ := by
  decide +kernel

theorem context_12_352542_1200944 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352542 ⟨1200944, by decide⟩ :=
  accepted_of_selected 12 352542 ⟨1200944, by decide⟩ ⟨12, 2, 0, 1200944, 352542, 2413, 65536⟩
    (by decide) selected_cut_43791

theorem selected_cut_43792 : selected 9 ⟨1200981, by decide⟩
    (prefixPartial 12 352543) = some ⟨12, 2, 0, 1200981, 352543, 2569, 65536⟩ := by
  decide +kernel

theorem context_12_352543_1200981 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352543 ⟨1200981, by decide⟩ :=
  accepted_of_selected 12 352543 ⟨1200981, by decide⟩ ⟨12, 2, 0, 1200981, 352543, 2569, 65536⟩
    (by decide) selected_cut_43792

theorem unmarked_context_11_88135_1200982 : frontier 10 ⟨1200982, by decide⟩
    (prefixCache 11 88135) (prefixPartial 11 88135) = false := by
  decide +kernel

theorem node_context_11_88135_1200982 : EJMOriginalGlobalDAGData.nodes 10 ⟨1200982, by decide⟩ =
    .split (coordinate 11) (![⟨1200869, by decide⟩,⟨1200905, by decide⟩,⟨1200944, by decide⟩,⟨1200981, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88135_1200982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88135 ⟨1200982, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88135
    ⟨1200982, by decide⟩ (by decide) (![⟨1200869, by decide⟩,⟨1200905, by decide⟩,⟨1200944, by decide⟩,⟨1200981, by decide⟩]) unmarked_context_11_88135_1200982 node_context_11_88135_1200982
  intro a
  fin_cases a
  · exact context_12_352540_1200869
  · exact context_12_352541_1200905
  · exact context_12_352542_1200944
  · exact context_12_352543_1200981

theorem unmarked_context_10_22033_1200983 : frontier 11 ⟨1200983, by decide⟩
    (prefixCache 10 22033) (prefixPartial 10 22033) = false := by
  decide +kernel

theorem node_context_10_22033_1200983 : EJMOriginalGlobalDAGData.nodes 11 ⟨1200983, by decide⟩ =
    .split (coordinate 10) (![⟨1200607, by decide⟩,⟨815620, by decide⟩,⟨1200829, by decide⟩,⟨1200982, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22033_1200983 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22033 ⟨1200983, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22033
    ⟨1200983, by decide⟩ (by decide) (![⟨1200607, by decide⟩,⟨815620, by decide⟩,⟨1200829, by decide⟩,⟨1200982, by decide⟩]) unmarked_context_10_22033_1200983 node_context_10_22033_1200983
  intro a
  fin_cases a
  · exact context_11_88132_1200607
  · exact context_11_88133_815620
  · exact context_11_88134_1200829
  · exact context_11_88135_1200982

theorem selected_cut_43793 : selected 9 ⟨1187656, by decide⟩
    (prefixPartial 12 352544) = some ⟨12, 1, 0, 1187656, 352544, 1, 65536⟩ := by
  decide +kernel

theorem context_12_352544_1187656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352544 ⟨1187656, by decide⟩ :=
  accepted_of_selected 12 352544 ⟨1187656, by decide⟩ ⟨12, 1, 0, 1187656, 352544, 1, 65536⟩
    (by decide) selected_cut_43793

theorem selected_cut_43794 : selected 9 ⟨1201024, by decide⟩
    (prefixPartial 12 352545) = some ⟨12, 2, 0, 1201024, 352545, 2389, 65536⟩ := by
  decide +kernel

theorem context_12_352545_1201024 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352545 ⟨1201024, by decide⟩ :=
  accepted_of_selected 12 352545 ⟨1201024, by decide⟩ ⟨12, 2, 0, 1201024, 352545, 2389, 65536⟩
    (by decide) selected_cut_43794

theorem selected_cut_43795 : selected 9 ⟨1201058, by decide⟩
    (prefixPartial 12 352546) = some ⟨12, 2, 0, 1201058, 352546, 2289, 65536⟩ := by
  decide +kernel

theorem context_12_352546_1201058 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352546 ⟨1201058, by decide⟩ :=
  accepted_of_selected 12 352546 ⟨1201058, by decide⟩ ⟨12, 2, 0, 1201058, 352546, 2289, 65536⟩
    (by decide) selected_cut_43795

theorem selected_cut_43796 : selected 9 ⟨1201093, by decide⟩
    (prefixPartial 12 352547) = some ⟨12, 2, 0, 1201093, 352547, 2537, 65536⟩ := by
  decide +kernel

theorem context_12_352547_1201093 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352547 ⟨1201093, by decide⟩ :=
  accepted_of_selected 12 352547 ⟨1201093, by decide⟩ ⟨12, 2, 0, 1201093, 352547, 2537, 65536⟩
    (by decide) selected_cut_43796

theorem unmarked_context_11_88136_1201094 : frontier 10 ⟨1201094, by decide⟩
    (prefixCache 11 88136) (prefixPartial 11 88136) = false := by
  decide +kernel

theorem node_context_11_88136_1201094 : EJMOriginalGlobalDAGData.nodes 10 ⟨1201094, by decide⟩ =
    .split (coordinate 11) (![⟨1187656, by decide⟩,⟨1201024, by decide⟩,⟨1201058, by decide⟩,⟨1201093, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88136_1201094 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88136 ⟨1201094, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88136
    ⟨1201094, by decide⟩ (by decide) (![⟨1187656, by decide⟩,⟨1201024, by decide⟩,⟨1201058, by decide⟩,⟨1201093, by decide⟩]) unmarked_context_11_88136_1201094 node_context_11_88136_1201094
  intro a
  fin_cases a
  · exact context_12_352544_1187656
  · exact context_12_352545_1201024
  · exact context_12_352546_1201058
  · exact context_12_352547_1201093

theorem selected_cut_43797 : selected 9 ⟨1201152, by decide⟩
    (prefixPartial 12 352548) = some ⟨12, 2, 0, 1201152, 352548, 2877, 65536⟩ := by
  decide +kernel

theorem context_12_352548_1201152 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352548 ⟨1201152, by decide⟩ :=
  accepted_of_selected 12 352548 ⟨1201152, by decide⟩ ⟨12, 2, 0, 1201152, 352548, 2877, 65536⟩
    (by decide) selected_cut_43797

theorem selected_cut_43798 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 352549) = some ⟨12, 1, 0, 891951, 352549, 1, 65536⟩ := by
  decide +kernel

theorem context_12_352549_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352549 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 352549 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 352549, 1, 65536⟩
    (by decide) selected_cut_43798

theorem selected_cut_43799 : selected 9 ⟨1201184, by decide⟩
    (prefixPartial 12 352550) = some ⟨12, 2, 0, 1201184, 352550, 2337, 65536⟩ := by
  decide +kernel

theorem context_12_352550_1201184 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352550 ⟨1201184, by decide⟩ :=
  accepted_of_selected 12 352550 ⟨1201184, by decide⟩ ⟨12, 2, 0, 1201184, 352550, 2337, 65536⟩
    (by decide) selected_cut_43799

theorem selected_cut_43800 : selected 9 ⟨1201230, by decide⟩
    (prefixPartial 12 352551) = some ⟨12, 2, 0, 1201230, 352551, 2737, 65536⟩ := by
  decide +kernel

theorem context_12_352551_1201230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352551 ⟨1201230, by decide⟩ :=
  accepted_of_selected 12 352551 ⟨1201230, by decide⟩ ⟨12, 2, 0, 1201230, 352551, 2737, 65536⟩
    (by decide) selected_cut_43800

theorem unmarked_context_11_88137_1201231 : frontier 10 ⟨1201231, by decide⟩
    (prefixCache 11 88137) (prefixPartial 11 88137) = false := by
  decide +kernel

theorem node_context_11_88137_1201231 : EJMOriginalGlobalDAGData.nodes 10 ⟨1201231, by decide⟩ =
    .split (coordinate 11) (![⟨1201152, by decide⟩,⟨891951, by decide⟩,⟨1201184, by decide⟩,⟨1201230, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88137_1201231 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88137 ⟨1201231, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88137
    ⟨1201231, by decide⟩ (by decide) (![⟨1201152, by decide⟩,⟨891951, by decide⟩,⟨1201184, by decide⟩,⟨1201230, by decide⟩]) unmarked_context_11_88137_1201231 node_context_11_88137_1201231
  intro a
  fin_cases a
  · exact context_12_352548_1201152
  · exact context_12_352549_891951
  · exact context_12_352550_1201184
  · exact context_12_352551_1201230

theorem selected_cut_43801 : selected 9 ⟨1201276, by decide⟩
    (prefixPartial 12 352552) = some ⟨12, 2, 0, 1201276, 352552, 2873, 65536⟩ := by
  decide +kernel

theorem context_12_352552_1201276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352552 ⟨1201276, by decide⟩ :=
  accepted_of_selected 12 352552 ⟨1201276, by decide⟩ ⟨12, 2, 0, 1201276, 352552, 2873, 65536⟩
    (by decide) selected_cut_43801

theorem selected_cut_43802 : selected 9 ⟨1201317, by decide⟩
    (prefixPartial 12 352553) = some ⟨12, 2, 0, 1201317, 352553, 2669, 65536⟩ := by
  decide +kernel

theorem context_12_352553_1201317 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352553 ⟨1201317, by decide⟩ :=
  accepted_of_selected 12 352553 ⟨1201317, by decide⟩ ⟨12, 2, 0, 1201317, 352553, 2669, 65536⟩
    (by decide) selected_cut_43802

theorem selected_cut_43803 : selected 9 ⟨474208, by decide⟩
    (prefixPartial 12 352554) = some ⟨12, 1, 0, 474208, 352554, 1, 65536⟩ := by
  decide +kernel

theorem context_12_352554_474208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352554 ⟨474208, by decide⟩ :=
  accepted_of_selected 12 352554 ⟨474208, by decide⟩ ⟨12, 1, 0, 474208, 352554, 1, 65536⟩
    (by decide) selected_cut_43803

theorem selected_cut_43804 : selected 9 ⟨1201365, by decide⟩
    (prefixPartial 12 352555) = some ⟨12, 2, 0, 1201365, 352555, 2789, 65536⟩ := by
  decide +kernel

theorem context_12_352555_1201365 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352555 ⟨1201365, by decide⟩ :=
  accepted_of_selected 12 352555 ⟨1201365, by decide⟩ ⟨12, 2, 0, 1201365, 352555, 2789, 65536⟩
    (by decide) selected_cut_43804

theorem unmarked_context_11_88138_1201366 : frontier 10 ⟨1201366, by decide⟩
    (prefixCache 11 88138) (prefixPartial 11 88138) = false := by
  decide +kernel

theorem node_context_11_88138_1201366 : EJMOriginalGlobalDAGData.nodes 10 ⟨1201366, by decide⟩ =
    .split (coordinate 11) (![⟨1201276, by decide⟩,⟨1201317, by decide⟩,⟨474208, by decide⟩,⟨1201365, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88138_1201366 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88138 ⟨1201366, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88138
    ⟨1201366, by decide⟩ (by decide) (![⟨1201276, by decide⟩,⟨1201317, by decide⟩,⟨474208, by decide⟩,⟨1201365, by decide⟩]) unmarked_context_11_88138_1201366 node_context_11_88138_1201366
  intro a
  fin_cases a
  · exact context_12_352552_1201276
  · exact context_12_352553_1201317
  · exact context_12_352554_474208
  · exact context_12_352555_1201365

theorem selected_cut_43805 : selected 9 ⟨1201410, by decide⟩
    (prefixPartial 12 352556) = some ⟨12, 2, 0, 1201410, 352556, 2633, 65536⟩ := by
  decide +kernel

theorem context_12_352556_1201410 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352556 ⟨1201410, by decide⟩ :=
  accepted_of_selected 12 352556 ⟨1201410, by decide⟩ ⟨12, 2, 0, 1201410, 352556, 2633, 65536⟩
    (by decide) selected_cut_43805

theorem selected_cut_43806 : selected 9 ⟨1201449, by decide⟩
    (prefixPartial 12 352557) = some ⟨12, 2, 0, 1201449, 352557, 2413, 65536⟩ := by
  decide +kernel

theorem context_12_352557_1201449 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352557 ⟨1201449, by decide⟩ :=
  accepted_of_selected 12 352557 ⟨1201449, by decide⟩ ⟨12, 2, 0, 1201449, 352557, 2413, 65536⟩
    (by decide) selected_cut_43806

theorem selected_cut_43807 : selected 9 ⟨1201483, by decide⟩
    (prefixPartial 12 352558) = some ⟨12, 2, 0, 1201483, 352558, 2329, 65536⟩ := by
  decide +kernel

theorem context_12_352558_1201483 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352558 ⟨1201483, by decide⟩ :=
  accepted_of_selected 12 352558 ⟨1201483, by decide⟩ ⟨12, 2, 0, 1201483, 352558, 2329, 65536⟩
    (by decide) selected_cut_43807

theorem selected_cut_43808 : selected 9 ⟨1201525, by decide⟩
    (prefixPartial 12 352559) = some ⟨12, 2, 0, 1201525, 352559, 2649, 65536⟩ := by
  decide +kernel

theorem context_12_352559_1201525 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352559 ⟨1201525, by decide⟩ :=
  accepted_of_selected 12 352559 ⟨1201525, by decide⟩ ⟨12, 2, 0, 1201525, 352559, 2649, 65536⟩
    (by decide) selected_cut_43808

theorem unmarked_context_11_88139_1201526 : frontier 10 ⟨1201526, by decide⟩
    (prefixCache 11 88139) (prefixPartial 11 88139) = false := by
  decide +kernel

theorem node_context_11_88139_1201526 : EJMOriginalGlobalDAGData.nodes 10 ⟨1201526, by decide⟩ =
    .split (coordinate 11) (![⟨1201410, by decide⟩,⟨1201449, by decide⟩,⟨1201483, by decide⟩,⟨1201525, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88139_1201526 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88139 ⟨1201526, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88139
    ⟨1201526, by decide⟩ (by decide) (![⟨1201410, by decide⟩,⟨1201449, by decide⟩,⟨1201483, by decide⟩,⟨1201525, by decide⟩]) unmarked_context_11_88139_1201526 node_context_11_88139_1201526
  intro a
  fin_cases a
  · exact context_12_352556_1201410
  · exact context_12_352557_1201449
  · exact context_12_352558_1201483
  · exact context_12_352559_1201525

theorem unmarked_context_10_22034_1201527 : frontier 11 ⟨1201527, by decide⟩
    (prefixCache 10 22034) (prefixPartial 10 22034) = false := by
  decide +kernel

theorem node_context_10_22034_1201527 : EJMOriginalGlobalDAGData.nodes 11 ⟨1201527, by decide⟩ =
    .split (coordinate 10) (![⟨1201094, by decide⟩,⟨1201231, by decide⟩,⟨1201366, by decide⟩,⟨1201526, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22034_1201527 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22034 ⟨1201527, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22034
    ⟨1201527, by decide⟩ (by decide) (![⟨1201094, by decide⟩,⟨1201231, by decide⟩,⟨1201366, by decide⟩,⟨1201526, by decide⟩]) unmarked_context_10_22034_1201527 node_context_10_22034_1201527
  intro a
  fin_cases a
  · exact context_11_88136_1201094
  · exact context_11_88137_1201231
  · exact context_11_88138_1201366
  · exact context_11_88139_1201526

theorem selected_cut_43809 : selected 9 ⟨1187656, by decide⟩
    (prefixPartial 12 352560) = some ⟨12, 1, 0, 1187656, 352560, 1, 65536⟩ := by
  decide +kernel

theorem context_12_352560_1187656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352560 ⟨1187656, by decide⟩ :=
  accepted_of_selected 12 352560 ⟨1187656, by decide⟩ ⟨12, 1, 0, 1187656, 352560, 1, 65536⟩
    (by decide) selected_cut_43809

theorem selected_cut_43810 : selected 9 ⟨1201565, by decide⟩
    (prefixPartial 12 352561) = some ⟨12, 2, 0, 1201565, 352561, 2225, 65536⟩ := by
  decide +kernel

theorem context_12_352561_1201565 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352561 ⟨1201565, by decide⟩ :=
  accepted_of_selected 12 352561 ⟨1201565, by decide⟩ ⟨12, 2, 0, 1201565, 352561, 2225, 65536⟩
    (by decide) selected_cut_43810

theorem selected_cut_43811 : selected 9 ⟨1201597, by decide⟩
    (prefixPartial 12 352562) = some ⟨12, 2, 0, 1201597, 352562, 2105, 65536⟩ := by
  decide +kernel

theorem context_12_352562_1201597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352562 ⟨1201597, by decide⟩ :=
  accepted_of_selected 12 352562 ⟨1201597, by decide⟩ ⟨12, 2, 0, 1201597, 352562, 2105, 65536⟩
    (by decide) selected_cut_43811

theorem selected_cut_43812 : selected 9 ⟨1201635, by decide⟩
    (prefixPartial 12 352563) = some ⟨12, 2, 0, 1201635, 352563, 2273, 65536⟩ := by
  decide +kernel

theorem context_12_352563_1201635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352563 ⟨1201635, by decide⟩ :=
  accepted_of_selected 12 352563 ⟨1201635, by decide⟩ ⟨12, 2, 0, 1201635, 352563, 2273, 65536⟩
    (by decide) selected_cut_43812

theorem unmarked_context_11_88140_1201636 : frontier 10 ⟨1201636, by decide⟩
    (prefixCache 11 88140) (prefixPartial 11 88140) = false := by
  decide +kernel

theorem node_context_11_88140_1201636 : EJMOriginalGlobalDAGData.nodes 10 ⟨1201636, by decide⟩ =
    .split (coordinate 11) (![⟨1187656, by decide⟩,⟨1201565, by decide⟩,⟨1201597, by decide⟩,⟨1201635, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88140_1201636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88140 ⟨1201636, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88140
    ⟨1201636, by decide⟩ (by decide) (![⟨1187656, by decide⟩,⟨1201565, by decide⟩,⟨1201597, by decide⟩,⟨1201635, by decide⟩]) unmarked_context_11_88140_1201636 node_context_11_88140_1201636
  intro a
  fin_cases a
  · exact context_12_352560_1187656
  · exact context_12_352561_1201565
  · exact context_12_352562_1201597
  · exact context_12_352563_1201635

theorem selected_cut_43813 : selected 9 ⟨1201687, by decide⟩
    (prefixPartial 12 352564) = some ⟨12, 2, 0, 1201687, 352564, 2601, 65536⟩ := by
  decide +kernel

theorem context_12_352564_1201687 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352564 ⟨1201687, by decide⟩ :=
  accepted_of_selected 12 352564 ⟨1201687, by decide⟩ ⟨12, 2, 0, 1201687, 352564, 2601, 65536⟩
    (by decide) selected_cut_43813

theorem selected_cut_43814 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 352565) = some ⟨12, 1, 0, 891951, 352565, 1, 65536⟩ := by
  decide +kernel

theorem context_12_352565_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352565 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 352565 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 352565, 1, 65536⟩
    (by decide) selected_cut_43814

theorem selected_cut_43815 : selected 9 ⟨1201718, by decide⟩
    (prefixPartial 12 352566) = some ⟨12, 2, 0, 1201718, 352566, 2193, 65536⟩ := by
  decide +kernel

theorem context_12_352566_1201718 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352566 ⟨1201718, by decide⟩ :=
  accepted_of_selected 12 352566 ⟨1201718, by decide⟩ ⟨12, 2, 0, 1201718, 352566, 2193, 65536⟩
    (by decide) selected_cut_43815

theorem selected_cut_43816 : selected 9 ⟨1201751, by decide⟩
    (prefixPartial 12 352567) = some ⟨12, 2, 0, 1201751, 352567, 2205, 65536⟩ := by
  decide +kernel

theorem context_12_352567_1201751 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352567 ⟨1201751, by decide⟩ :=
  accepted_of_selected 12 352567 ⟨1201751, by decide⟩ ⟨12, 2, 0, 1201751, 352567, 2205, 65536⟩
    (by decide) selected_cut_43816

theorem unmarked_context_11_88141_1201752 : frontier 10 ⟨1201752, by decide⟩
    (prefixCache 11 88141) (prefixPartial 11 88141) = false := by
  decide +kernel

theorem node_context_11_88141_1201752 : EJMOriginalGlobalDAGData.nodes 10 ⟨1201752, by decide⟩ =
    .split (coordinate 11) (![⟨1201687, by decide⟩,⟨891951, by decide⟩,⟨1201718, by decide⟩,⟨1201751, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88141_1201752 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88141 ⟨1201752, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88141
    ⟨1201752, by decide⟩ (by decide) (![⟨1201687, by decide⟩,⟨891951, by decide⟩,⟨1201718, by decide⟩,⟨1201751, by decide⟩]) unmarked_context_11_88141_1201752 node_context_11_88141_1201752
  intro a
  fin_cases a
  · exact context_12_352564_1201687
  · exact context_12_352565_891951
  · exact context_12_352566_1201718
  · exact context_12_352567_1201751

theorem selected_cut_43817 : selected 9 ⟨1201810, by decide⟩
    (prefixPartial 12 352568) = some ⟨12, 2, 0, 1201810, 352568, 2597, 65536⟩ := by
  decide +kernel

theorem context_12_352568_1201810 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352568 ⟨1201810, by decide⟩ :=
  accepted_of_selected 12 352568 ⟨1201810, by decide⟩ ⟨12, 2, 0, 1201810, 352568, 2597, 65536⟩
    (by decide) selected_cut_43817

theorem selected_cut_43818 : selected 9 ⟨1201850, by decide⟩
    (prefixPartial 12 352569) = some ⟨12, 2, 0, 1201850, 352569, 2537, 65536⟩ := by
  decide +kernel

theorem context_12_352569_1201850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352569 ⟨1201850, by decide⟩ :=
  accepted_of_selected 12 352569 ⟨1201850, by decide⟩ ⟨12, 2, 0, 1201850, 352569, 2537, 65536⟩
    (by decide) selected_cut_43818

theorem selected_cut_43819 : selected 9 ⟨1201892, by decide⟩
    (prefixPartial 12 352570) = some ⟨12, 2, 0, 1201892, 352570, 2349, 65536⟩ := by
  decide +kernel

theorem context_12_352570_1201892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352570 ⟨1201892, by decide⟩ :=
  accepted_of_selected 12 352570 ⟨1201892, by decide⟩ ⟨12, 2, 0, 1201892, 352570, 2349, 65536⟩
    (by decide) selected_cut_43819

theorem selected_cut_43820 : selected 9 ⟨1201938, by decide⟩
    (prefixPartial 12 352571) = some ⟨12, 2, 0, 1201938, 352571, 2381, 65536⟩ := by
  decide +kernel

theorem context_12_352571_1201938 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352571 ⟨1201938, by decide⟩ :=
  accepted_of_selected 12 352571 ⟨1201938, by decide⟩ ⟨12, 2, 0, 1201938, 352571, 2381, 65536⟩
    (by decide) selected_cut_43820

theorem unmarked_context_11_88142_1201939 : frontier 10 ⟨1201939, by decide⟩
    (prefixCache 11 88142) (prefixPartial 11 88142) = false := by
  decide +kernel

theorem node_context_11_88142_1201939 : EJMOriginalGlobalDAGData.nodes 10 ⟨1201939, by decide⟩ =
    .split (coordinate 11) (![⟨1201810, by decide⟩,⟨1201850, by decide⟩,⟨1201892, by decide⟩,⟨1201938, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88142_1201939 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88142 ⟨1201939, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88142
    ⟨1201939, by decide⟩ (by decide) (![⟨1201810, by decide⟩,⟨1201850, by decide⟩,⟨1201892, by decide⟩,⟨1201938, by decide⟩]) unmarked_context_11_88142_1201939 node_context_11_88142_1201939
  intro a
  fin_cases a
  · exact context_12_352568_1201810
  · exact context_12_352569_1201850
  · exact context_12_352570_1201892
  · exact context_12_352571_1201938

theorem selected_cut_43821 : selected 9 ⟨1201981, by decide⟩
    (prefixPartial 12 352572) = some ⟨12, 2, 0, 1201981, 352572, 2077, 65536⟩ := by
  decide +kernel

theorem context_12_352572_1201981 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352572 ⟨1201981, by decide⟩ :=
  accepted_of_selected 12 352572 ⟨1201981, by decide⟩ ⟨12, 2, 0, 1201981, 352572, 2077, 65536⟩
    (by decide) selected_cut_43821

theorem selected_cut_43822 : selected 9 ⟨1202010, by decide⟩
    (prefixPartial 12 352573) = some ⟨12, 2, 0, 1202010, 352573, 2001, 65536⟩ := by
  decide +kernel

theorem context_12_352573_1202010 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352573 ⟨1202010, by decide⟩ :=
  accepted_of_selected 12 352573 ⟨1202010, by decide⟩ ⟨12, 2, 0, 1202010, 352573, 2001, 65536⟩
    (by decide) selected_cut_43822

theorem selected_cut_43823 : selected 9 ⟨1202037, by decide⟩
    (prefixPartial 12 352574) = some ⟨12, 2, 0, 1202037, 352574, 1913, 65536⟩ := by
  decide +kernel

theorem context_12_352574_1202037 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352574 ⟨1202037, by decide⟩ :=
  accepted_of_selected 12 352574 ⟨1202037, by decide⟩ ⟨12, 2, 0, 1202037, 352574, 1913, 65536⟩
    (by decide) selected_cut_43823

theorem selected_cut_43824 : selected 9 ⟨607719, by decide⟩
    (prefixPartial 12 352575) = some ⟨12, 1, 0, 607719, 352575, 1, 65536⟩ := by
  decide +kernel

theorem context_12_352575_607719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352575 ⟨607719, by decide⟩ :=
  accepted_of_selected 12 352575 ⟨607719, by decide⟩ ⟨12, 1, 0, 607719, 352575, 1, 65536⟩
    (by decide) selected_cut_43824

theorem unmarked_context_11_88143_1202038 : frontier 10 ⟨1202038, by decide⟩
    (prefixCache 11 88143) (prefixPartial 11 88143) = false := by
  decide +kernel

theorem node_context_11_88143_1202038 : EJMOriginalGlobalDAGData.nodes 10 ⟨1202038, by decide⟩ =
    .split (coordinate 11) (![⟨1201981, by decide⟩,⟨1202010, by decide⟩,⟨1202037, by decide⟩,⟨607719, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88143_1202038 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88143 ⟨1202038, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88143
    ⟨1202038, by decide⟩ (by decide) (![⟨1201981, by decide⟩,⟨1202010, by decide⟩,⟨1202037, by decide⟩,⟨607719, by decide⟩]) unmarked_context_11_88143_1202038 node_context_11_88143_1202038
  intro a
  fin_cases a
  · exact context_12_352572_1201981
  · exact context_12_352573_1202010
  · exact context_12_352574_1202037
  · exact context_12_352575_607719

theorem unmarked_context_10_22035_1202039 : frontier 11 ⟨1202039, by decide⟩
    (prefixCache 10 22035) (prefixPartial 10 22035) = false := by
  decide +kernel

theorem node_context_10_22035_1202039 : EJMOriginalGlobalDAGData.nodes 11 ⟨1202039, by decide⟩ =
    .split (coordinate 10) (![⟨1201636, by decide⟩,⟨1201752, by decide⟩,⟨1201939, by decide⟩,⟨1202038, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22035_1202039 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22035 ⟨1202039, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22035
    ⟨1202039, by decide⟩ (by decide) (![⟨1201636, by decide⟩,⟨1201752, by decide⟩,⟨1201939, by decide⟩,⟨1202038, by decide⟩]) unmarked_context_10_22035_1202039 node_context_10_22035_1202039
  intro a
  fin_cases a
  · exact context_11_88140_1201636
  · exact context_11_88141_1201752
  · exact context_11_88142_1201939
  · exact context_11_88143_1202038

theorem unmarked_context_9_5508_1202040 : frontier 12 ⟨1202040, by decide⟩
    (prefixCache 9 5508) (prefixPartial 9 5508) = false := by
  decide +kernel

theorem node_context_9_5508_1202040 : EJMOriginalGlobalDAGData.nodes 12 ⟨1202040, by decide⟩ =
    .split (coordinate 9) (![⟨1200517, by decide⟩,⟨1200983, by decide⟩,⟨1201527, by decide⟩,⟨1202039, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5508_1202040 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5508 ⟨1202040, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5508
    ⟨1202040, by decide⟩ (by decide) (![⟨1200517, by decide⟩,⟨1200983, by decide⟩,⟨1201527, by decide⟩,⟨1202039, by decide⟩]) unmarked_context_9_5508_1202040 node_context_9_5508_1202040
  intro a
  fin_cases a
  · exact context_10_22032_1200517
  · exact context_10_22033_1200983
  · exact context_10_22034_1201527
  · exact context_10_22035_1202039

theorem selected_cut_43825 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 88144) = some ⟨11, 1, 0, 907917, 88144, 1, 262144⟩ := by
  decide +kernel

theorem context_11_88144_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88144 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 88144 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 88144, 1, 262144⟩
    (by decide) selected_cut_43825

theorem selected_cut_43826 : selected 9 ⟨1202066, by decide⟩
    (prefixPartial 12 352580) = some ⟨12, 2, 0, 1202066, 352580, 1385, 65536⟩ := by
  decide +kernel

theorem context_12_352580_1202066 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352580 ⟨1202066, by decide⟩ :=
  accepted_of_selected 12 352580 ⟨1202066, by decide⟩ ⟨12, 2, 0, 1202066, 352580, 1385, 65536⟩
    (by decide) selected_cut_43826

theorem selected_cut_43827 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 352581) = some ⟨12, 1, 0, 896706, 352581, 1, 65536⟩ := by
  decide +kernel

theorem context_12_352581_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352581 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 352581 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 352581, 1, 65536⟩
    (by decide) selected_cut_43827

theorem selected_cut_43828 : selected 9 ⟨1202083, by decide⟩
    (prefixPartial 12 352582) = some ⟨12, 2, 0, 1202083, 352582, 1361, 65536⟩ := by
  decide +kernel

theorem context_12_352582_1202083 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352582 ⟨1202083, by decide⟩ :=
  accepted_of_selected 12 352582 ⟨1202083, by decide⟩ ⟨12, 2, 0, 1202083, 352582, 1361, 65536⟩
    (by decide) selected_cut_43828

theorem selected_cut_43829 : selected 9 ⟨1202104, by decide⟩
    (prefixPartial 12 352583) = some ⟨12, 2, 0, 1202104, 352583, 1413, 65536⟩ := by
  decide +kernel

theorem context_12_352583_1202104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352583 ⟨1202104, by decide⟩ :=
  accepted_of_selected 12 352583 ⟨1202104, by decide⟩ ⟨12, 2, 0, 1202104, 352583, 1413, 65536⟩
    (by decide) selected_cut_43829

theorem unmarked_context_11_88145_1202105 : frontier 10 ⟨1202105, by decide⟩
    (prefixCache 11 88145) (prefixPartial 11 88145) = false := by
  decide +kernel

theorem node_context_11_88145_1202105 : EJMOriginalGlobalDAGData.nodes 10 ⟨1202105, by decide⟩ =
    .split (coordinate 11) (![⟨1202066, by decide⟩,⟨896706, by decide⟩,⟨1202083, by decide⟩,⟨1202104, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88145_1202105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88145 ⟨1202105, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88145
    ⟨1202105, by decide⟩ (by decide) (![⟨1202066, by decide⟩,⟨896706, by decide⟩,⟨1202083, by decide⟩,⟨1202104, by decide⟩]) unmarked_context_11_88145_1202105 node_context_11_88145_1202105
  intro a
  fin_cases a
  · exact context_12_352580_1202066
  · exact context_12_352581_896706
  · exact context_12_352582_1202083
  · exact context_12_352583_1202104

theorem selected_cut_43830 : selected 9 ⟨1202132, by decide⟩
    (prefixPartial 12 352584) = some ⟨12, 2, 0, 1202132, 352584, 1549, 65536⟩ := by
  decide +kernel

theorem context_12_352584_1202132 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352584 ⟨1202132, by decide⟩ :=
  accepted_of_selected 12 352584 ⟨1202132, by decide⟩ ⟨12, 2, 0, 1202132, 352584, 1549, 65536⟩
    (by decide) selected_cut_43830

theorem selected_cut_43831 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 352585) = some ⟨12, 1, 0, 896706, 352585, 1, 65536⟩ := by
  decide +kernel

theorem context_12_352585_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352585 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 352585 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 352585, 1, 65536⟩
    (by decide) selected_cut_43831

theorem selected_cut_43832 : selected 9 ⟨1202152, by decide⟩
    (prefixPartial 12 352586) = some ⟨12, 2, 0, 1202152, 352586, 1665, 65536⟩ := by
  decide +kernel

theorem context_12_352586_1202152 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352586 ⟨1202152, by decide⟩ :=
  accepted_of_selected 12 352586 ⟨1202152, by decide⟩ ⟨12, 2, 0, 1202152, 352586, 1665, 65536⟩
    (by decide) selected_cut_43832

theorem selected_cut_43833 : selected 9 ⟨1202176, by decide⟩
    (prefixPartial 12 352587) = some ⟨12, 2, 0, 1202176, 352587, 1645, 65536⟩ := by
  decide +kernel

theorem context_12_352587_1202176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352587 ⟨1202176, by decide⟩ :=
  accepted_of_selected 12 352587 ⟨1202176, by decide⟩ ⟨12, 2, 0, 1202176, 352587, 1645, 65536⟩
    (by decide) selected_cut_43833

theorem unmarked_context_11_88146_1202177 : frontier 10 ⟨1202177, by decide⟩
    (prefixCache 11 88146) (prefixPartial 11 88146) = false := by
  decide +kernel

theorem node_context_11_88146_1202177 : EJMOriginalGlobalDAGData.nodes 10 ⟨1202177, by decide⟩ =
    .split (coordinate 11) (![⟨1202132, by decide⟩,⟨896706, by decide⟩,⟨1202152, by decide⟩,⟨1202176, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88146_1202177 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88146 ⟨1202177, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88146
    ⟨1202177, by decide⟩ (by decide) (![⟨1202132, by decide⟩,⟨896706, by decide⟩,⟨1202152, by decide⟩,⟨1202176, by decide⟩]) unmarked_context_11_88146_1202177 node_context_11_88146_1202177
  intro a
  fin_cases a
  · exact context_12_352584_1202132
  · exact context_12_352585_896706
  · exact context_12_352586_1202152
  · exact context_12_352587_1202176

theorem selected_cut_43834 : selected 9 ⟨1202197, by decide⟩
    (prefixPartial 12 352588) = some ⟨12, 2, 0, 1202197, 352588, 1405, 65536⟩ := by
  decide +kernel

theorem context_12_352588_1202197 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352588 ⟨1202197, by decide⟩ :=
  accepted_of_selected 12 352588 ⟨1202197, by decide⟩ ⟨12, 2, 0, 1202197, 352588, 1405, 65536⟩
    (by decide) selected_cut_43834

theorem selected_cut_43835 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 352589) = some ⟨12, 1, 0, 896706, 352589, 1, 65536⟩ := by
  decide +kernel

theorem context_12_352589_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352589 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 352589 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 352589, 1, 65536⟩
    (by decide) selected_cut_43835

theorem selected_cut_43836 : selected 9 ⟨1202215, by decide⟩
    (prefixPartial 12 352590) = some ⟨12, 2, 0, 1202215, 352590, 1449, 65536⟩ := by
  decide +kernel

theorem context_12_352590_1202215 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352590 ⟨1202215, by decide⟩ :=
  accepted_of_selected 12 352590 ⟨1202215, by decide⟩ ⟨12, 2, 0, 1202215, 352590, 1449, 65536⟩
    (by decide) selected_cut_43836

theorem selected_cut_43837 : selected 9 ⟨1202237, by decide⟩
    (prefixPartial 12 352591) = some ⟨12, 2, 0, 1202237, 352591, 1565, 65536⟩ := by
  decide +kernel

theorem context_12_352591_1202237 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352591 ⟨1202237, by decide⟩ :=
  accepted_of_selected 12 352591 ⟨1202237, by decide⟩ ⟨12, 2, 0, 1202237, 352591, 1565, 65536⟩
    (by decide) selected_cut_43837

theorem unmarked_context_11_88147_1202238 : frontier 10 ⟨1202238, by decide⟩
    (prefixCache 11 88147) (prefixPartial 11 88147) = false := by
  decide +kernel

theorem node_context_11_88147_1202238 : EJMOriginalGlobalDAGData.nodes 10 ⟨1202238, by decide⟩ =
    .split (coordinate 11) (![⟨1202197, by decide⟩,⟨896706, by decide⟩,⟨1202215, by decide⟩,⟨1202237, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88147_1202238 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88147 ⟨1202238, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88147
    ⟨1202238, by decide⟩ (by decide) (![⟨1202197, by decide⟩,⟨896706, by decide⟩,⟨1202215, by decide⟩,⟨1202237, by decide⟩]) unmarked_context_11_88147_1202238 node_context_11_88147_1202238
  intro a
  fin_cases a
  · exact context_12_352588_1202197
  · exact context_12_352589_896706
  · exact context_12_352590_1202215
  · exact context_12_352591_1202237

theorem unmarked_context_10_22036_1202239 : frontier 11 ⟨1202239, by decide⟩
    (prefixCache 10 22036) (prefixPartial 10 22036) = false := by
  decide +kernel

theorem node_context_10_22036_1202239 : EJMOriginalGlobalDAGData.nodes 11 ⟨1202239, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨1202105, by decide⟩,⟨1202177, by decide⟩,⟨1202238, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22036_1202239 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22036 ⟨1202239, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22036
    ⟨1202239, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨1202105, by decide⟩,⟨1202177, by decide⟩,⟨1202238, by decide⟩]) unmarked_context_10_22036_1202239 node_context_10_22036_1202239
  intro a
  fin_cases a
  · exact context_11_88144_907917
  · exact context_11_88145_1202105
  · exact context_11_88146_1202177
  · exact context_11_88147_1202238

theorem selected_cut_43838 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 22037) = some ⟨10, 1, 0, 893098, 22037, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_22037_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22037 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 22037 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 22037, 1, 1048576⟩
    (by decide) selected_cut_43838

theorem selected_cut_43839 : selected 10 ⟨1202294, by decide⟩
    (prefixPartial 11 88152) = some ⟨11, 2, 0, 1202294, 88152, 3473, 262144⟩ := by
  decide +kernel

theorem context_11_88152_1202294 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88152 ⟨1202294, by decide⟩ :=
  accepted_of_selected 11 88152 ⟨1202294, by decide⟩ ⟨11, 2, 0, 1202294, 88152, 3473, 262144⟩
    (by decide) selected_cut_43839

theorem selected_cut_43840 : selected 10 ⟨1202345, by decide⟩
    (prefixPartial 11 88153) = some ⟨11, 2, 0, 1202345, 88153, 3757, 262144⟩ := by
  decide +kernel

theorem context_11_88153_1202345 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88153 ⟨1202345, by decide⟩ :=
  accepted_of_selected 11 88153 ⟨1202345, by decide⟩ ⟨11, 2, 0, 1202345, 88153, 3757, 262144⟩
    (by decide) selected_cut_43840

theorem selected_cut_43841 : selected 10 ⟨1202388, by decide⟩
    (prefixPartial 11 88154) = some ⟨11, 2, 0, 1202388, 88154, 2689, 262144⟩ := by
  decide +kernel

theorem context_11_88154_1202388 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88154 ⟨1202388, by decide⟩ :=
  accepted_of_selected 11 88154 ⟨1202388, by decide⟩ ⟨11, 2, 0, 1202388, 88154, 2689, 262144⟩
    (by decide) selected_cut_43841

theorem selected_cut_43842 : selected 9 ⟨1202412, by decide⟩
    (prefixPartial 12 352620) = some ⟨12, 2, 0, 1202412, 352620, 1393, 65536⟩ := by
  decide +kernel

theorem context_12_352620_1202412 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352620 ⟨1202412, by decide⟩ :=
  accepted_of_selected 12 352620 ⟨1202412, by decide⟩ ⟨12, 2, 0, 1202412, 352620, 1393, 65536⟩
    (by decide) selected_cut_43842

theorem selected_cut_43843 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 352621) = some ⟨12, 1, 0, 896706, 352621, 1, 65536⟩ := by
  decide +kernel

theorem context_12_352621_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352621 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 352621 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 352621, 1, 65536⟩
    (by decide) selected_cut_43843

theorem selected_cut_43844 : selected 9 ⟨1202431, by decide⟩
    (prefixPartial 12 352622) = some ⟨12, 2, 0, 1202431, 352622, 1353, 65536⟩ := by
  decide +kernel

theorem context_12_352622_1202431 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352622 ⟨1202431, by decide⟩ :=
  accepted_of_selected 12 352622 ⟨1202431, by decide⟩ ⟨12, 2, 0, 1202431, 352622, 1353, 65536⟩
    (by decide) selected_cut_43844

theorem selected_cut_43845 : selected 9 ⟨1202451, by decide⟩
    (prefixPartial 12 352623) = some ⟨12, 2, 0, 1202451, 352623, 1509, 65536⟩ := by
  decide +kernel

theorem context_12_352623_1202451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352623 ⟨1202451, by decide⟩ :=
  accepted_of_selected 12 352623 ⟨1202451, by decide⟩ ⟨12, 2, 0, 1202451, 352623, 1509, 65536⟩
    (by decide) selected_cut_43845

theorem unmarked_context_11_88155_1202452 : frontier 10 ⟨1202452, by decide⟩
    (prefixCache 11 88155) (prefixPartial 11 88155) = false := by
  decide +kernel

theorem node_context_11_88155_1202452 : EJMOriginalGlobalDAGData.nodes 10 ⟨1202452, by decide⟩ =
    .split (coordinate 11) (![⟨1202412, by decide⟩,⟨896706, by decide⟩,⟨1202431, by decide⟩,⟨1202451, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88155_1202452 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88155 ⟨1202452, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88155
    ⟨1202452, by decide⟩ (by decide) (![⟨1202412, by decide⟩,⟨896706, by decide⟩,⟨1202431, by decide⟩,⟨1202451, by decide⟩]) unmarked_context_11_88155_1202452 node_context_11_88155_1202452
  intro a
  fin_cases a
  · exact context_12_352620_1202412
  · exact context_12_352621_896706
  · exact context_12_352622_1202431
  · exact context_12_352623_1202451

theorem unmarked_context_10_22038_1202453 : frontier 11 ⟨1202453, by decide⟩
    (prefixCache 10 22038) (prefixPartial 10 22038) = false := by
  decide +kernel

theorem node_context_10_22038_1202453 : EJMOriginalGlobalDAGData.nodes 11 ⟨1202453, by decide⟩ =
    .split (coordinate 10) (![⟨1202294, by decide⟩,⟨1202345, by decide⟩,⟨1202388, by decide⟩,⟨1202452, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22038_1202453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22038 ⟨1202453, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22038
    ⟨1202453, by decide⟩ (by decide) (![⟨1202294, by decide⟩,⟨1202345, by decide⟩,⟨1202388, by decide⟩,⟨1202452, by decide⟩]) unmarked_context_10_22038_1202453 node_context_10_22038_1202453
  intro a
  fin_cases a
  · exact context_11_88152_1202294
  · exact context_11_88153_1202345
  · exact context_11_88154_1202388
  · exact context_11_88155_1202452

theorem selected_cut_43846 : selected 10 ⟨1202512, by decide⟩
    (prefixPartial 11 88156) = some ⟨11, 2, 0, 1202512, 88156, 3273, 262144⟩ := by
  decide +kernel

theorem context_11_88156_1202512 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88156 ⟨1202512, by decide⟩ :=
  accepted_of_selected 11 88156 ⟨1202512, by decide⟩ ⟨11, 2, 0, 1202512, 88156, 3273, 262144⟩
    (by decide) selected_cut_43846

theorem selected_cut_43847 : selected 10 ⟨1202551, by decide⟩
    (prefixPartial 11 88157) = some ⟨11, 2, 0, 1202551, 88157, 3333, 262144⟩ := by
  decide +kernel

theorem context_11_88157_1202551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88157 ⟨1202551, by decide⟩ :=
  accepted_of_selected 11 88157 ⟨1202551, by decide⟩ ⟨11, 2, 0, 1202551, 88157, 3333, 262144⟩
    (by decide) selected_cut_43847

theorem selected_cut_43848 : selected 10 ⟨1202608, by decide⟩
    (prefixPartial 11 88158) = some ⟨11, 2, 0, 1202608, 88158, 3725, 262144⟩ := by
  decide +kernel

theorem context_11_88158_1202608 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88158 ⟨1202608, by decide⟩ :=
  accepted_of_selected 11 88158 ⟨1202608, by decide⟩ ⟨11, 2, 0, 1202608, 88158, 3725, 262144⟩
    (by decide) selected_cut_43848

theorem selected_cut_43849 : selected 10 ⟨1202640, by decide⟩
    (prefixPartial 11 88159) = some ⟨11, 2, 0, 1202640, 88159, 2197, 262144⟩ := by
  decide +kernel

theorem context_11_88159_1202640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88159 ⟨1202640, by decide⟩ :=
  accepted_of_selected 11 88159 ⟨1202640, by decide⟩ ⟨11, 2, 0, 1202640, 88159, 2197, 262144⟩
    (by decide) selected_cut_43849

theorem unmarked_context_10_22039_1202641 : frontier 11 ⟨1202641, by decide⟩
    (prefixCache 10 22039) (prefixPartial 10 22039) = false := by
  decide +kernel

theorem node_context_10_22039_1202641 : EJMOriginalGlobalDAGData.nodes 11 ⟨1202641, by decide⟩ =
    .split (coordinate 10) (![⟨1202512, by decide⟩,⟨1202551, by decide⟩,⟨1202608, by decide⟩,⟨1202640, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22039_1202641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22039 ⟨1202641, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22039
    ⟨1202641, by decide⟩ (by decide) (![⟨1202512, by decide⟩,⟨1202551, by decide⟩,⟨1202608, by decide⟩,⟨1202640, by decide⟩]) unmarked_context_10_22039_1202641 node_context_10_22039_1202641
  intro a
  fin_cases a
  · exact context_11_88156_1202512
  · exact context_11_88157_1202551
  · exact context_11_88158_1202608
  · exact context_11_88159_1202640

theorem unmarked_context_9_5509_1202642 : frontier 12 ⟨1202642, by decide⟩
    (prefixCache 9 5509) (prefixPartial 9 5509) = false := by
  decide +kernel

theorem node_context_9_5509_1202642 : EJMOriginalGlobalDAGData.nodes 12 ⟨1202642, by decide⟩ =
    .split (coordinate 9) (![⟨1202239, by decide⟩,⟨893098, by decide⟩,⟨1202453, by decide⟩,⟨1202641, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5509_1202642 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5509 ⟨1202642, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5509
    ⟨1202642, by decide⟩ (by decide) (![⟨1202239, by decide⟩,⟨893098, by decide⟩,⟨1202453, by decide⟩,⟨1202641, by decide⟩]) unmarked_context_9_5509_1202642 node_context_9_5509_1202642
  intro a
  fin_cases a
  · exact context_10_22036_1202239
  · exact context_10_22037_893098
  · exact context_10_22038_1202453
  · exact context_10_22039_1202641

theorem selected_cut_43850 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 88160) = some ⟨11, 1, 0, 907917, 88160, 1, 262144⟩ := by
  decide +kernel

theorem context_11_88160_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88160 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 88160 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 88160, 1, 262144⟩
    (by decide) selected_cut_43850

theorem selected_cut_43851 : selected 10 ⟨1202697, by decide⟩
    (prefixPartial 11 88161) = some ⟨11, 2, 0, 1202697, 88161, 3385, 262144⟩ := by
  decide +kernel

theorem context_11_88161_1202697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88161 ⟨1202697, by decide⟩ :=
  accepted_of_selected 11 88161 ⟨1202697, by decide⟩ ⟨11, 2, 0, 1202697, 88161, 3385, 262144⟩
    (by decide) selected_cut_43851

theorem selected_cut_43852 : selected 10 ⟨1202771, by decide⟩
    (prefixPartial 11 88162) = some ⟨11, 2, 0, 1202771, 88162, 3741, 262144⟩ := by
  decide +kernel

theorem context_11_88162_1202771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88162 ⟨1202771, by decide⟩ :=
  accepted_of_selected 11 88162 ⟨1202771, by decide⟩ ⟨11, 2, 0, 1202771, 88162, 3741, 262144⟩
    (by decide) selected_cut_43852

theorem selected_cut_43853 : selected 9 ⟨1202788, by decide⟩
    (prefixPartial 12 352652) = some ⟨12, 2, 0, 1202788, 352652, 1057, 65536⟩ := by
  decide +kernel

theorem context_12_352652_1202788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352652 ⟨1202788, by decide⟩ :=
  accepted_of_selected 12 352652 ⟨1202788, by decide⟩ ⟨12, 2, 0, 1202788, 352652, 1057, 65536⟩
    (by decide) selected_cut_43853

theorem selected_cut_43854 : selected 9 ⟨1202800, by decide⟩
    (prefixPartial 12 352653) = some ⟨12, 2, 0, 1202800, 352653, 1021, 65536⟩ := by
  decide +kernel

theorem context_12_352653_1202800 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352653 ⟨1202800, by decide⟩ :=
  accepted_of_selected 12 352653 ⟨1202800, by decide⟩ ⟨12, 2, 0, 1202800, 352653, 1021, 65536⟩
    (by decide) selected_cut_43854

theorem selected_cut_43855 : selected 9 ⟨1202816, by decide⟩
    (prefixPartial 12 352654) = some ⟨12, 2, 0, 1202816, 352654, 1057, 65536⟩ := by
  decide +kernel

theorem context_12_352654_1202816 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352654 ⟨1202816, by decide⟩ :=
  accepted_of_selected 12 352654 ⟨1202816, by decide⟩ ⟨12, 2, 0, 1202816, 352654, 1057, 65536⟩
    (by decide) selected_cut_43855

theorem selected_cut_43856 : selected 9 ⟨1202830, by decide⟩
    (prefixPartial 12 352655) = some ⟨12, 2, 0, 1202830, 352655, 1049, 65536⟩ := by
  decide +kernel

theorem context_12_352655_1202830 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352655 ⟨1202830, by decide⟩ :=
  accepted_of_selected 12 352655 ⟨1202830, by decide⟩ ⟨12, 2, 0, 1202830, 352655, 1049, 65536⟩
    (by decide) selected_cut_43856

theorem unmarked_context_11_88163_1202831 : frontier 10 ⟨1202831, by decide⟩
    (prefixCache 11 88163) (prefixPartial 11 88163) = false := by
  decide +kernel

theorem node_context_11_88163_1202831 : EJMOriginalGlobalDAGData.nodes 10 ⟨1202831, by decide⟩ =
    .split (coordinate 11) (![⟨1202788, by decide⟩,⟨1202800, by decide⟩,⟨1202816, by decide⟩,⟨1202830, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88163_1202831 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88163 ⟨1202831, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88163
    ⟨1202831, by decide⟩ (by decide) (![⟨1202788, by decide⟩,⟨1202800, by decide⟩,⟨1202816, by decide⟩,⟨1202830, by decide⟩]) unmarked_context_11_88163_1202831 node_context_11_88163_1202831
  intro a
  fin_cases a
  · exact context_12_352652_1202788
  · exact context_12_352653_1202800
  · exact context_12_352654_1202816
  · exact context_12_352655_1202830

theorem unmarked_context_10_22040_1202832 : frontier 11 ⟨1202832, by decide⟩
    (prefixCache 10 22040) (prefixPartial 10 22040) = false := by
  decide +kernel

theorem node_context_10_22040_1202832 : EJMOriginalGlobalDAGData.nodes 11 ⟨1202832, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨1202697, by decide⟩,⟨1202771, by decide⟩,⟨1202831, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22040_1202832 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22040 ⟨1202832, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22040
    ⟨1202832, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨1202697, by decide⟩,⟨1202771, by decide⟩,⟨1202831, by decide⟩]) unmarked_context_10_22040_1202832 node_context_10_22040_1202832
  intro a
  fin_cases a
  · exact context_11_88160_907917
  · exact context_11_88161_1202697
  · exact context_11_88162_1202771
  · exact context_11_88163_1202831

theorem selected_cut_43857 : selected 10 ⟨1202858, by decide⟩
    (prefixPartial 11 88164) = some ⟨11, 2, 0, 1202858, 88164, 2545, 262144⟩ := by
  decide +kernel

theorem context_11_88164_1202858 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88164 ⟨1202858, by decide⟩ :=
  accepted_of_selected 11 88164 ⟨1202858, by decide⟩ ⟨11, 2, 0, 1202858, 88164, 2545, 262144⟩
    (by decide) selected_cut_43857

theorem selected_cut_43858 : selected 10 ⟨1202871, by decide⟩
    (prefixPartial 11 88165) = some ⟨11, 2, 0, 1202871, 88165, 825, 262144⟩ := by
  decide +kernel

theorem context_11_88165_1202871 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88165 ⟨1202871, by decide⟩ :=
  accepted_of_selected 11 88165 ⟨1202871, by decide⟩ ⟨11, 2, 0, 1202871, 88165, 825, 262144⟩
    (by decide) selected_cut_43858

theorem selected_cut_43859 : selected 10 ⟨1202911, by decide⟩
    (prefixPartial 11 88166) = some ⟨11, 2, 0, 1202911, 88166, 2753, 262144⟩ := by
  decide +kernel

theorem context_11_88166_1202911 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88166 ⟨1202911, by decide⟩ :=
  accepted_of_selected 11 88166 ⟨1202911, by decide⟩ ⟨11, 2, 0, 1202911, 88166, 2753, 262144⟩
    (by decide) selected_cut_43859

theorem selected_cut_43860 : selected 10 ⟨1202956, by decide⟩
    (prefixPartial 11 88167) = some ⟨11, 2, 0, 1202956, 88167, 3409, 262144⟩ := by
  decide +kernel

theorem context_11_88167_1202956 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88167 ⟨1202956, by decide⟩ :=
  accepted_of_selected 11 88167 ⟨1202956, by decide⟩ ⟨11, 2, 0, 1202956, 88167, 3409, 262144⟩
    (by decide) selected_cut_43860

theorem unmarked_context_10_22041_1202957 : frontier 11 ⟨1202957, by decide⟩
    (prefixCache 10 22041) (prefixPartial 10 22041) = false := by
  decide +kernel

theorem node_context_10_22041_1202957 : EJMOriginalGlobalDAGData.nodes 11 ⟨1202957, by decide⟩ =
    .split (coordinate 10) (![⟨1202858, by decide⟩,⟨1202871, by decide⟩,⟨1202911, by decide⟩,⟨1202956, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22041_1202957 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22041 ⟨1202957, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22041
    ⟨1202957, by decide⟩ (by decide) (![⟨1202858, by decide⟩,⟨1202871, by decide⟩,⟨1202911, by decide⟩,⟨1202956, by decide⟩]) unmarked_context_10_22041_1202957 node_context_10_22041_1202957
  intro a
  fin_cases a
  · exact context_11_88164_1202858
  · exact context_11_88165_1202871
  · exact context_11_88166_1202911
  · exact context_11_88167_1202956

theorem selected_cut_43861 : selected 10 ⟨1202998, by decide⟩
    (prefixPartial 11 88168) = some ⟨11, 2, 0, 1202998, 88168, 2465, 262144⟩ := by
  decide +kernel

theorem context_11_88168_1202998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88168 ⟨1202998, by decide⟩ :=
  accepted_of_selected 11 88168 ⟨1202998, by decide⟩ ⟨11, 2, 0, 1202998, 88168, 2465, 262144⟩
    (by decide) selected_cut_43861

theorem selected_cut_43862 : selected 10 ⟨1203020, by decide⟩
    (prefixPartial 11 88169) = some ⟨11, 2, 0, 1203020, 88169, 1557, 262144⟩ := by
  decide +kernel

theorem context_11_88169_1203020 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88169 ⟨1203020, by decide⟩ :=
  accepted_of_selected 11 88169 ⟨1203020, by decide⟩ ⟨11, 2, 0, 1203020, 88169, 1557, 262144⟩
    (by decide) selected_cut_43862

theorem selected_cut_43863 : selected 10 ⟨1109453, by decide⟩
    (prefixPartial 11 88170) = some ⟨11, 1, 0, 1109453, 88170, 1, 262144⟩ := by
  decide +kernel

theorem context_11_88170_1109453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88170 ⟨1109453, by decide⟩ :=
  accepted_of_selected 11 88170 ⟨1109453, by decide⟩ ⟨11, 1, 0, 1109453, 88170, 1, 262144⟩
    (by decide) selected_cut_43863

theorem selected_cut_43864 : selected 10 ⟨1203057, by decide⟩
    (prefixPartial 11 88171) = some ⟨11, 2, 0, 1203057, 88171, 2405, 262144⟩ := by
  decide +kernel

theorem context_11_88171_1203057 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88171 ⟨1203057, by decide⟩ :=
  accepted_of_selected 11 88171 ⟨1203057, by decide⟩ ⟨11, 2, 0, 1203057, 88171, 2405, 262144⟩
    (by decide) selected_cut_43864

theorem unmarked_context_10_22042_1203058 : frontier 11 ⟨1203058, by decide⟩
    (prefixCache 10 22042) (prefixPartial 10 22042) = false := by
  decide +kernel

theorem node_context_10_22042_1203058 : EJMOriginalGlobalDAGData.nodes 11 ⟨1203058, by decide⟩ =
    .split (coordinate 10) (![⟨1202998, by decide⟩,⟨1203020, by decide⟩,⟨1109453, by decide⟩,⟨1203057, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22042_1203058 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22042 ⟨1203058, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22042
    ⟨1203058, by decide⟩ (by decide) (![⟨1202998, by decide⟩,⟨1203020, by decide⟩,⟨1109453, by decide⟩,⟨1203057, by decide⟩]) unmarked_context_10_22042_1203058 node_context_10_22042_1203058
  intro a
  fin_cases a
  · exact context_11_88168_1202998
  · exact context_11_88169_1203020
  · exact context_11_88170_1109453
  · exact context_11_88171_1203057

theorem selected_cut_43865 : selected 10 ⟨1203099, by decide⟩
    (prefixPartial 11 88172) = some ⟨11, 2, 0, 1203099, 88172, 2693, 262144⟩ := by
  decide +kernel

theorem context_11_88172_1203099 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88172 ⟨1203099, by decide⟩ :=
  accepted_of_selected 11 88172 ⟨1203099, by decide⟩ ⟨11, 2, 0, 1203099, 88172, 2693, 262144⟩
    (by decide) selected_cut_43865

theorem selected_cut_43866 : selected 10 ⟨1203126, by decide⟩
    (prefixPartial 11 88173) = some ⟨11, 2, 0, 1203126, 88173, 1861, 262144⟩ := by
  decide +kernel

theorem context_11_88173_1203126 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88173 ⟨1203126, by decide⟩ :=
  accepted_of_selected 11 88173 ⟨1203126, by decide⟩ ⟨11, 2, 0, 1203126, 88173, 1861, 262144⟩
    (by decide) selected_cut_43866

theorem selected_cut_43867 : selected 10 ⟨1203149, by decide⟩
    (prefixPartial 11 88174) = some ⟨11, 2, 0, 1203149, 88174, 1705, 262144⟩ := by
  decide +kernel

theorem context_11_88174_1203149 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88174 ⟨1203149, by decide⟩ :=
  accepted_of_selected 11 88174 ⟨1203149, by decide⟩ ⟨11, 2, 0, 1203149, 88174, 1705, 262144⟩
    (by decide) selected_cut_43867

theorem selected_cut_43868 : selected 10 ⟨1203173, by decide⟩
    (prefixPartial 11 88175) = some ⟨11, 2, 0, 1203173, 88175, 1609, 262144⟩ := by
  decide +kernel

theorem context_11_88175_1203173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88175 ⟨1203173, by decide⟩ :=
  accepted_of_selected 11 88175 ⟨1203173, by decide⟩ ⟨11, 2, 0, 1203173, 88175, 1609, 262144⟩
    (by decide) selected_cut_43868

theorem unmarked_context_10_22043_1203174 : frontier 11 ⟨1203174, by decide⟩
    (prefixCache 10 22043) (prefixPartial 10 22043) = false := by
  decide +kernel

theorem node_context_10_22043_1203174 : EJMOriginalGlobalDAGData.nodes 11 ⟨1203174, by decide⟩ =
    .split (coordinate 10) (![⟨1203099, by decide⟩,⟨1203126, by decide⟩,⟨1203149, by decide⟩,⟨1203173, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22043_1203174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22043 ⟨1203174, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22043
    ⟨1203174, by decide⟩ (by decide) (![⟨1203099, by decide⟩,⟨1203126, by decide⟩,⟨1203149, by decide⟩,⟨1203173, by decide⟩]) unmarked_context_10_22043_1203174 node_context_10_22043_1203174
  intro a
  fin_cases a
  · exact context_11_88172_1203099
  · exact context_11_88173_1203126
  · exact context_11_88174_1203149
  · exact context_11_88175_1203173

theorem unmarked_context_9_5510_1203175 : frontier 12 ⟨1203175, by decide⟩
    (prefixCache 9 5510) (prefixPartial 9 5510) = false := by
  decide +kernel

theorem node_context_9_5510_1203175 : EJMOriginalGlobalDAGData.nodes 12 ⟨1203175, by decide⟩ =
    .split (coordinate 9) (![⟨1202832, by decide⟩,⟨1202957, by decide⟩,⟨1203058, by decide⟩,⟨1203174, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5510_1203175 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5510 ⟨1203175, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5510
    ⟨1203175, by decide⟩ (by decide) (![⟨1202832, by decide⟩,⟨1202957, by decide⟩,⟨1203058, by decide⟩,⟨1203174, by decide⟩]) unmarked_context_9_5510_1203175 node_context_9_5510_1203175
  intro a
  fin_cases a
  · exact context_10_22040_1202832
  · exact context_10_22041_1202957
  · exact context_10_22042_1203058
  · exact context_10_22043_1203174

theorem selected_cut_43869 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 88176) = some ⟨11, 1, 0, 907917, 88176, 1, 262144⟩ := by
  decide +kernel

theorem context_11_88176_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88176 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 88176 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 88176, 1, 262144⟩
    (by decide) selected_cut_43869

theorem selected_cut_43870 : selected 10 ⟨1203193, by decide⟩
    (prefixPartial 11 88177) = some ⟨11, 2, 0, 1203193, 88177, 1357, 262144⟩ := by
  decide +kernel

theorem context_11_88177_1203193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88177 ⟨1203193, by decide⟩ :=
  accepted_of_selected 11 88177 ⟨1203193, by decide⟩ ⟨11, 2, 0, 1203193, 88177, 1357, 262144⟩
    (by decide) selected_cut_43870

theorem selected_cut_43871 : selected 10 ⟨1203215, by decide⟩
    (prefixPartial 11 88178) = some ⟨11, 2, 0, 1203215, 88178, 1689, 262144⟩ := by
  decide +kernel

theorem context_11_88178_1203215 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88178 ⟨1203215, by decide⟩ :=
  accepted_of_selected 11 88178 ⟨1203215, by decide⟩ ⟨11, 2, 0, 1203215, 88178, 1689, 262144⟩
    (by decide) selected_cut_43871

theorem selected_cut_43872 : selected 10 ⟨1203231, by decide⟩
    (prefixPartial 11 88179) = some ⟨11, 2, 0, 1203231, 88179, 1137, 262144⟩ := by
  decide +kernel

theorem context_11_88179_1203231 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88179 ⟨1203231, by decide⟩ :=
  accepted_of_selected 11 88179 ⟨1203231, by decide⟩ ⟨11, 2, 0, 1203231, 88179, 1137, 262144⟩
    (by decide) selected_cut_43872

theorem unmarked_context_10_22044_1203232 : frontier 11 ⟨1203232, by decide⟩
    (prefixCache 10 22044) (prefixPartial 10 22044) = false := by
  decide +kernel

theorem node_context_10_22044_1203232 : EJMOriginalGlobalDAGData.nodes 11 ⟨1203232, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨1203193, by decide⟩,⟨1203215, by decide⟩,⟨1203231, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22044_1203232 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22044 ⟨1203232, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22044
    ⟨1203232, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨1203193, by decide⟩,⟨1203215, by decide⟩,⟨1203231, by decide⟩]) unmarked_context_10_22044_1203232 node_context_10_22044_1203232
  intro a
  fin_cases a
  · exact context_11_88176_907917
  · exact context_11_88177_1203193
  · exact context_11_88178_1203215
  · exact context_11_88179_1203231

theorem selected_cut_43873 : selected 11 ⟨1203283, by decide⟩
    (prefixPartial 10 22045) = some ⟨10, 2, 0, 1203283, 22045, 3313, 1048576⟩ := by
  decide +kernel

theorem context_10_22045_1203283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22045 ⟨1203283, by decide⟩ :=
  accepted_of_selected 10 22045 ⟨1203283, by decide⟩ ⟨10, 2, 0, 1203283, 22045, 3313, 1048576⟩
    (by decide) selected_cut_43873

theorem selected_cut_43874 : selected 11 ⟨1203331, by decide⟩
    (prefixPartial 10 22046) = some ⟨10, 2, 0, 1203331, 22046, 2329, 1048576⟩ := by
  decide +kernel

theorem context_10_22046_1203331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22046 ⟨1203331, by decide⟩ :=
  accepted_of_selected 10 22046 ⟨1203331, by decide⟩ ⟨10, 2, 0, 1203331, 22046, 2329, 1048576⟩
    (by decide) selected_cut_43874

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
