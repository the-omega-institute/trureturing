/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover456
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_43875 : selected 11 ⟨1203343, by decide⟩
    (prefixPartial 10 22047) = some ⟨10, 2, 0, 1203343, 22047, 477, 1048576⟩ := by
  decide +kernel

theorem context_10_22047_1203343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22047 ⟨1203343, by decide⟩ :=
  accepted_of_selected 10 22047 ⟨1203343, by decide⟩ ⟨10, 2, 0, 1203343, 22047, 477, 1048576⟩
    (by decide) selected_cut_43875

theorem unmarked_context_9_5511_1203344 : frontier 12 ⟨1203344, by decide⟩
    (prefixCache 9 5511) (prefixPartial 9 5511) = false := by
  decide +kernel

theorem node_context_9_5511_1203344 : EJMOriginalGlobalDAGData.nodes 12 ⟨1203344, by decide⟩ =
    .split (coordinate 9) (![⟨1203232, by decide⟩,⟨1203283, by decide⟩,⟨1203331, by decide⟩,⟨1203343, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5511_1203344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5511 ⟨1203344, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5511
    ⟨1203344, by decide⟩ (by decide) (![⟨1203232, by decide⟩,⟨1203283, by decide⟩,⟨1203331, by decide⟩,⟨1203343, by decide⟩]) unmarked_context_9_5511_1203344 node_context_9_5511_1203344
  intro a
  fin_cases a
  · exact context_10_22044_1203232
  · exact context_10_22045_1203283
  · exact context_10_22046_1203331
  · exact context_10_22047_1203343

theorem unmarked_context_8_1377_1203345 : frontier 13 ⟨1203345, by decide⟩
    (prefixCache 8 1377) (prefixPartial 8 1377) = false := by
  decide +kernel

theorem node_context_8_1377_1203345 : EJMOriginalGlobalDAGData.nodes 13 ⟨1203345, by decide⟩ =
    .split (coordinate 8) (![⟨1202040, by decide⟩,⟨1202642, by decide⟩,⟨1203175, by decide⟩,⟨1203344, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1377_1203345 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1377 ⟨1203345, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1377
    ⟨1203345, by decide⟩ (by decide) (![⟨1202040, by decide⟩,⟨1202642, by decide⟩,⟨1203175, by decide⟩,⟨1203344, by decide⟩]) unmarked_context_8_1377_1203345 node_context_8_1377_1203345
  intro a
  fin_cases a
  · exact context_9_5508_1202040
  · exact context_9_5509_1202642
  · exact context_9_5510_1203175
  · exact context_9_5511_1203344

theorem selected_cut_43876 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 88192) = some ⟨11, 1, 0, 434745, 88192, 1, 262144⟩ := by
  decide +kernel

theorem context_11_88192_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88192 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 88192 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 88192, 1, 262144⟩
    (by decide) selected_cut_43876

theorem selected_cut_43877 : selected 10 ⟨167448, by decide⟩
    (prefixPartial 11 88193) = some ⟨11, 1, 0, 167448, 88193, 1, 262144⟩ := by
  decide +kernel

theorem context_11_88193_167448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88193 ⟨167448, by decide⟩ :=
  accepted_of_selected 11 88193 ⟨167448, by decide⟩ ⟨11, 1, 0, 167448, 88193, 1, 262144⟩
    (by decide) selected_cut_43877

theorem selected_cut_43878 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 352776) = some ⟨12, 1, 0, 448748, 352776, 1, 65536⟩ := by
  decide +kernel

theorem context_12_352776_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352776 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 352776 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 352776, 1, 65536⟩
    (by decide) selected_cut_43878

theorem selected_cut_43879 : selected 9 ⟨1203415, by decide⟩
    (prefixPartial 12 352777) = some ⟨12, 2, 0, 1203415, 352777, 2821, 65536⟩ := by
  decide +kernel

theorem context_12_352777_1203415 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352777 ⟨1203415, by decide⟩ :=
  accepted_of_selected 12 352777 ⟨1203415, by decide⟩ ⟨12, 2, 0, 1203415, 352777, 2821, 65536⟩
    (by decide) selected_cut_43879

theorem selected_cut_43880 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 352778) = some ⟨12, 1, 0, 893903, 352778, 1, 65536⟩ := by
  decide +kernel

theorem context_12_352778_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352778 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 352778 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 352778, 1, 65536⟩
    (by decide) selected_cut_43880

theorem selected_cut_43881 : selected 9 ⟨1203494, by decide⟩
    (prefixPartial 12 352779) = some ⟨12, 2, 0, 1203494, 352779, 3473, 65536⟩ := by
  decide +kernel

theorem context_12_352779_1203494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352779 ⟨1203494, by decide⟩ :=
  accepted_of_selected 12 352779 ⟨1203494, by decide⟩ ⟨12, 2, 0, 1203494, 352779, 3473, 65536⟩
    (by decide) selected_cut_43881

theorem unmarked_context_11_88194_1203495 : frontier 10 ⟨1203495, by decide⟩
    (prefixCache 11 88194) (prefixPartial 11 88194) = false := by
  decide +kernel

theorem node_context_11_88194_1203495 : EJMOriginalGlobalDAGData.nodes 10 ⟨1203495, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1203415, by decide⟩,⟨893903, by decide⟩,⟨1203494, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88194_1203495 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88194 ⟨1203495, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88194
    ⟨1203495, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1203415, by decide⟩,⟨893903, by decide⟩,⟨1203494, by decide⟩]) unmarked_context_11_88194_1203495 node_context_11_88194_1203495
  intro a
  fin_cases a
  · exact context_12_352776_448748
  · exact context_12_352777_1203415
  · exact context_12_352778_893903
  · exact context_12_352779_1203494

theorem selected_cut_43882 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 352780) = some ⟨12, 1, 0, 448748, 352780, 1, 65536⟩ := by
  decide +kernel

theorem context_12_352780_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352780 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 352780 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 352780, 1, 65536⟩
    (by decide) selected_cut_43882

theorem selected_cut_43883 : selected 9 ⟨1203538, by decide⟩
    (prefixPartial 12 352781) = some ⟨12, 2, 0, 1203538, 352781, 2525, 65536⟩ := by
  decide +kernel

theorem context_12_352781_1203538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352781 ⟨1203538, by decide⟩ :=
  accepted_of_selected 12 352781 ⟨1203538, by decide⟩ ⟨12, 2, 0, 1203538, 352781, 2525, 65536⟩
    (by decide) selected_cut_43883

theorem selected_cut_43884 : selected 9 ⟨1203581, by decide⟩
    (prefixPartial 12 352782) = some ⟨12, 2, 0, 1203581, 352782, 2573, 65536⟩ := by
  decide +kernel

theorem context_12_352782_1203581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352782 ⟨1203581, by decide⟩ :=
  accepted_of_selected 12 352782 ⟨1203581, by decide⟩ ⟨12, 2, 0, 1203581, 352782, 2573, 65536⟩
    (by decide) selected_cut_43884

theorem selected_cut_43885 : selected 9 ⟨1203620, by decide⟩
    (prefixPartial 12 352783) = some ⟨12, 2, 0, 1203620, 352783, 2713, 65536⟩ := by
  decide +kernel

theorem context_12_352783_1203620 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352783 ⟨1203620, by decide⟩ :=
  accepted_of_selected 12 352783 ⟨1203620, by decide⟩ ⟨12, 2, 0, 1203620, 352783, 2713, 65536⟩
    (by decide) selected_cut_43885

theorem unmarked_context_11_88195_1203621 : frontier 10 ⟨1203621, by decide⟩
    (prefixCache 11 88195) (prefixPartial 11 88195) = false := by
  decide +kernel

theorem node_context_11_88195_1203621 : EJMOriginalGlobalDAGData.nodes 10 ⟨1203621, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1203538, by decide⟩,⟨1203581, by decide⟩,⟨1203620, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88195_1203621 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88195 ⟨1203621, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88195
    ⟨1203621, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1203538, by decide⟩,⟨1203581, by decide⟩,⟨1203620, by decide⟩]) unmarked_context_11_88195_1203621 node_context_11_88195_1203621
  intro a
  fin_cases a
  · exact context_12_352780_448748
  · exact context_12_352781_1203538
  · exact context_12_352782_1203581
  · exact context_12_352783_1203620

theorem unmarked_context_10_22048_1203622 : frontier 11 ⟨1203622, by decide⟩
    (prefixCache 10 22048) (prefixPartial 10 22048) = false := by
  decide +kernel

theorem node_context_10_22048_1203622 : EJMOriginalGlobalDAGData.nodes 11 ⟨1203622, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨167448, by decide⟩,⟨1203495, by decide⟩,⟨1203621, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22048_1203622 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22048 ⟨1203622, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22048
    ⟨1203622, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨167448, by decide⟩,⟨1203495, by decide⟩,⟨1203621, by decide⟩]) unmarked_context_10_22048_1203622 node_context_10_22048_1203622
  intro a
  fin_cases a
  · exact context_11_88192_434745
  · exact context_11_88193_167448
  · exact context_11_88194_1203495
  · exact context_11_88195_1203621

theorem selected_cut_43886 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 352784) = some ⟨12, 1, 0, 435160, 352784, 1, 65536⟩ := by
  decide +kernel

theorem context_12_352784_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352784 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 352784 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 352784, 1, 65536⟩
    (by decide) selected_cut_43886

theorem selected_cut_43887 : selected 9 ⟨1203655, by decide⟩
    (prefixPartial 12 352785) = some ⟨12, 2, 0, 1203655, 352785, 2425, 65536⟩ := by
  decide +kernel

theorem context_12_352785_1203655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352785 ⟨1203655, by decide⟩ :=
  accepted_of_selected 12 352785 ⟨1203655, by decide⟩ ⟨12, 2, 0, 1203655, 352785, 2425, 65536⟩
    (by decide) selected_cut_43887

theorem selected_cut_43888 : selected 9 ⟨1203702, by decide⟩
    (prefixPartial 12 352786) = some ⟨12, 2, 0, 1203702, 352786, 2613, 65536⟩ := by
  decide +kernel

theorem context_12_352786_1203702 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352786 ⟨1203702, by decide⟩ :=
  accepted_of_selected 12 352786 ⟨1203702, by decide⟩ ⟨12, 2, 0, 1203702, 352786, 2613, 65536⟩
    (by decide) selected_cut_43888

theorem selected_cut_43889 : selected 9 ⟨1203763, by decide⟩
    (prefixPartial 12 352787) = some ⟨12, 2, 0, 1203763, 352787, 3161, 65536⟩ := by
  decide +kernel

theorem context_12_352787_1203763 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352787 ⟨1203763, by decide⟩ :=
  accepted_of_selected 12 352787 ⟨1203763, by decide⟩ ⟨12, 2, 0, 1203763, 352787, 3161, 65536⟩
    (by decide) selected_cut_43889

theorem unmarked_context_11_88196_1203764 : frontier 10 ⟨1203764, by decide⟩
    (prefixCache 11 88196) (prefixPartial 11 88196) = false := by
  decide +kernel

theorem node_context_11_88196_1203764 : EJMOriginalGlobalDAGData.nodes 10 ⟨1203764, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨1203655, by decide⟩,⟨1203702, by decide⟩,⟨1203763, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88196_1203764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88196 ⟨1203764, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88196
    ⟨1203764, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨1203655, by decide⟩,⟨1203702, by decide⟩,⟨1203763, by decide⟩]) unmarked_context_11_88196_1203764 node_context_11_88196_1203764
  intro a
  fin_cases a
  · exact context_12_352784_435160
  · exact context_12_352785_1203655
  · exact context_12_352786_1203702
  · exact context_12_352787_1203763

theorem selected_cut_43890 : selected 10 ⟨815620, by decide⟩
    (prefixPartial 11 88197) = some ⟨11, 1, 0, 815620, 88197, 1, 262144⟩ := by
  decide +kernel

theorem context_11_88197_815620 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88197 ⟨815620, by decide⟩ :=
  accepted_of_selected 11 88197 ⟨815620, by decide⟩ ⟨11, 1, 0, 815620, 88197, 1, 262144⟩
    (by decide) selected_cut_43890

theorem selected_cut_43891 : selected 9 ⟨1203826, by decide⟩
    (prefixPartial 12 352792) = some ⟨12, 2, 0, 1203826, 352792, 3349, 65536⟩ := by
  decide +kernel

theorem context_12_352792_1203826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352792 ⟨1203826, by decide⟩ :=
  accepted_of_selected 12 352792 ⟨1203826, by decide⟩ ⟨12, 2, 0, 1203826, 352792, 3349, 65536⟩
    (by decide) selected_cut_43891

theorem selected_cut_43892 : selected 9 ⟨1203883, by decide⟩
    (prefixPartial 12 352793) = some ⟨12, 2, 0, 1203883, 352793, 2873, 65536⟩ := by
  decide +kernel

theorem context_12_352793_1203883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352793 ⟨1203883, by decide⟩ :=
  accepted_of_selected 12 352793 ⟨1203883, by decide⟩ ⟨12, 2, 0, 1203883, 352793, 2873, 65536⟩
    (by decide) selected_cut_43892

theorem selected_cut_43893 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 352794) = some ⟨12, 1, 0, 893903, 352794, 1, 65536⟩ := by
  decide +kernel

theorem context_12_352794_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352794 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 352794 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 352794, 1, 65536⟩
    (by decide) selected_cut_43893

theorem selected_cut_43894 : selected 9 ⟨1203959, by decide⟩
    (prefixPartial 12 352795) = some ⟨12, 2, 0, 1203959, 352795, 3553, 65536⟩ := by
  decide +kernel

theorem context_12_352795_1203959 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352795 ⟨1203959, by decide⟩ :=
  accepted_of_selected 12 352795 ⟨1203959, by decide⟩ ⟨12, 2, 0, 1203959, 352795, 3553, 65536⟩
    (by decide) selected_cut_43894

theorem unmarked_context_11_88198_1203960 : frontier 10 ⟨1203960, by decide⟩
    (prefixCache 11 88198) (prefixPartial 11 88198) = false := by
  decide +kernel

theorem node_context_11_88198_1203960 : EJMOriginalGlobalDAGData.nodes 10 ⟨1203960, by decide⟩ =
    .split (coordinate 11) (![⟨1203826, by decide⟩,⟨1203883, by decide⟩,⟨893903, by decide⟩,⟨1203959, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88198_1203960 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88198 ⟨1203960, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88198
    ⟨1203960, by decide⟩ (by decide) (![⟨1203826, by decide⟩,⟨1203883, by decide⟩,⟨893903, by decide⟩,⟨1203959, by decide⟩]) unmarked_context_11_88198_1203960 node_context_11_88198_1203960
  intro a
  fin_cases a
  · exact context_12_352792_1203826
  · exact context_12_352793_1203883
  · exact context_12_352794_893903
  · exact context_12_352795_1203959

theorem selected_cut_43895 : selected 9 ⟨1204014, by decide⟩
    (prefixPartial 12 352796) = some ⟨12, 2, 0, 1204014, 352796, 3145, 65536⟩ := by
  decide +kernel

theorem context_12_352796_1204014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352796 ⟨1204014, by decide⟩ :=
  accepted_of_selected 12 352796 ⟨1204014, by decide⟩ ⟨12, 2, 0, 1204014, 352796, 3145, 65536⟩
    (by decide) selected_cut_43895

theorem selected_cut_43896 : selected 9 ⟨1204059, by decide⟩
    (prefixPartial 12 352797) = some ⟨12, 2, 0, 1204059, 352797, 2665, 65536⟩ := by
  decide +kernel

theorem context_12_352797_1204059 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352797 ⟨1204059, by decide⟩ :=
  accepted_of_selected 12 352797 ⟨1204059, by decide⟩ ⟨12, 2, 0, 1204059, 352797, 2665, 65536⟩
    (by decide) selected_cut_43896

theorem selected_cut_43897 : selected 9 ⟨1204114, by decide⟩
    (prefixPartial 12 352798) = some ⟨12, 2, 0, 1204114, 352798, 2777, 65536⟩ := by
  decide +kernel

theorem context_12_352798_1204114 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352798 ⟨1204114, by decide⟩ :=
  accepted_of_selected 12 352798 ⟨1204114, by decide⟩ ⟨12, 2, 0, 1204114, 352798, 2777, 65536⟩
    (by decide) selected_cut_43897

theorem selected_cut_43898 : selected 9 ⟨1204167, by decide⟩
    (prefixPartial 12 352799) = some ⟨12, 2, 0, 1204167, 352799, 3049, 65536⟩ := by
  decide +kernel

theorem context_12_352799_1204167 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352799 ⟨1204167, by decide⟩ :=
  accepted_of_selected 12 352799 ⟨1204167, by decide⟩ ⟨12, 2, 0, 1204167, 352799, 3049, 65536⟩
    (by decide) selected_cut_43898

theorem unmarked_context_11_88199_1204168 : frontier 10 ⟨1204168, by decide⟩
    (prefixCache 11 88199) (prefixPartial 11 88199) = false := by
  decide +kernel

theorem node_context_11_88199_1204168 : EJMOriginalGlobalDAGData.nodes 10 ⟨1204168, by decide⟩ =
    .split (coordinate 11) (![⟨1204014, by decide⟩,⟨1204059, by decide⟩,⟨1204114, by decide⟩,⟨1204167, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88199_1204168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88199 ⟨1204168, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88199
    ⟨1204168, by decide⟩ (by decide) (![⟨1204014, by decide⟩,⟨1204059, by decide⟩,⟨1204114, by decide⟩,⟨1204167, by decide⟩]) unmarked_context_11_88199_1204168 node_context_11_88199_1204168
  intro a
  fin_cases a
  · exact context_12_352796_1204014
  · exact context_12_352797_1204059
  · exact context_12_352798_1204114
  · exact context_12_352799_1204167

theorem unmarked_context_10_22049_1204169 : frontier 11 ⟨1204169, by decide⟩
    (prefixCache 10 22049) (prefixPartial 10 22049) = false := by
  decide +kernel

theorem node_context_10_22049_1204169 : EJMOriginalGlobalDAGData.nodes 11 ⟨1204169, by decide⟩ =
    .split (coordinate 10) (![⟨1203764, by decide⟩,⟨815620, by decide⟩,⟨1203960, by decide⟩,⟨1204168, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22049_1204169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22049 ⟨1204169, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22049
    ⟨1204169, by decide⟩ (by decide) (![⟨1203764, by decide⟩,⟨815620, by decide⟩,⟨1203960, by decide⟩,⟨1204168, by decide⟩]) unmarked_context_10_22049_1204169 node_context_10_22049_1204169
  intro a
  fin_cases a
  · exact context_11_88196_1203764
  · exact context_11_88197_815620
  · exact context_11_88198_1203960
  · exact context_11_88199_1204168

theorem selected_cut_43899 : selected 9 ⟨765706, by decide⟩
    (prefixPartial 12 352800) = some ⟨12, 1, 0, 765706, 352800, 1, 65536⟩ := by
  decide +kernel

theorem context_12_352800_765706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352800 ⟨765706, by decide⟩ :=
  accepted_of_selected 12 352800 ⟨765706, by decide⟩ ⟨12, 1, 0, 765706, 352800, 1, 65536⟩
    (by decide) selected_cut_43899

theorem selected_cut_43900 : selected 9 ⟨1204209, by decide⟩
    (prefixPartial 12 352801) = some ⟨12, 2, 0, 1204209, 352801, 2441, 65536⟩ := by
  decide +kernel

theorem context_12_352801_1204209 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352801 ⟨1204209, by decide⟩ :=
  accepted_of_selected 12 352801 ⟨1204209, by decide⟩ ⟨12, 2, 0, 1204209, 352801, 2441, 65536⟩
    (by decide) selected_cut_43900

theorem selected_cut_43901 : selected 9 ⟨1204245, by decide⟩
    (prefixPartial 12 352802) = some ⟨12, 2, 0, 1204245, 352802, 2269, 65536⟩ := by
  decide +kernel

theorem context_12_352802_1204245 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352802 ⟨1204245, by decide⟩ :=
  accepted_of_selected 12 352802 ⟨1204245, by decide⟩ ⟨12, 2, 0, 1204245, 352802, 2269, 65536⟩
    (by decide) selected_cut_43901

theorem selected_cut_43902 : selected 9 ⟨1204292, by decide⟩
    (prefixPartial 12 352803) = some ⟨12, 2, 0, 1204292, 352803, 2841, 65536⟩ := by
  decide +kernel

theorem context_12_352803_1204292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352803 ⟨1204292, by decide⟩ :=
  accepted_of_selected 12 352803 ⟨1204292, by decide⟩ ⟨12, 2, 0, 1204292, 352803, 2841, 65536⟩
    (by decide) selected_cut_43902

theorem unmarked_context_11_88200_1204293 : frontier 10 ⟨1204293, by decide⟩
    (prefixCache 11 88200) (prefixPartial 11 88200) = false := by
  decide +kernel

theorem node_context_11_88200_1204293 : EJMOriginalGlobalDAGData.nodes 10 ⟨1204293, by decide⟩ =
    .split (coordinate 11) (![⟨765706, by decide⟩,⟨1204209, by decide⟩,⟨1204245, by decide⟩,⟨1204292, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88200_1204293 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88200 ⟨1204293, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88200
    ⟨1204293, by decide⟩ (by decide) (![⟨765706, by decide⟩,⟨1204209, by decide⟩,⟨1204245, by decide⟩,⟨1204292, by decide⟩]) unmarked_context_11_88200_1204293 node_context_11_88200_1204293
  intro a
  fin_cases a
  · exact context_12_352800_765706
  · exact context_12_352801_1204209
  · exact context_12_352802_1204245
  · exact context_12_352803_1204292

theorem selected_cut_43903 : selected 9 ⟨1204364, by decide⟩
    (prefixPartial 12 352804) = some ⟨12, 2, 0, 1204364, 352804, 3241, 65536⟩ := by
  decide +kernel

theorem context_12_352804_1204364 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352804 ⟨1204364, by decide⟩ :=
  accepted_of_selected 12 352804 ⟨1204364, by decide⟩ ⟨12, 2, 0, 1204364, 352804, 3241, 65536⟩
    (by decide) selected_cut_43903

theorem selected_cut_43904 : selected 9 ⟨1204408, by decide⟩
    (prefixPartial 12 352805) = some ⟨12, 2, 0, 1204408, 352805, 2553, 65536⟩ := by
  decide +kernel

theorem context_12_352805_1204408 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352805 ⟨1204408, by decide⟩ :=
  accepted_of_selected 12 352805 ⟨1204408, by decide⟩ ⟨12, 2, 0, 1204408, 352805, 2553, 65536⟩
    (by decide) selected_cut_43904

theorem selected_cut_43905 : selected 9 ⟨1204454, by decide⟩
    (prefixPartial 12 352806) = some ⟨12, 2, 0, 1204454, 352806, 2405, 65536⟩ := by
  decide +kernel

theorem context_12_352806_1204454 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352806 ⟨1204454, by decide⟩ :=
  accepted_of_selected 12 352806 ⟨1204454, by decide⟩ ⟨12, 2, 0, 1204454, 352806, 2405, 65536⟩
    (by decide) selected_cut_43905

theorem selected_cut_43906 : selected 9 ⟨1204504, by decide⟩
    (prefixPartial 12 352807) = some ⟨12, 2, 0, 1204504, 352807, 2965, 65536⟩ := by
  decide +kernel

theorem context_12_352807_1204504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352807 ⟨1204504, by decide⟩ :=
  accepted_of_selected 12 352807 ⟨1204504, by decide⟩ ⟨12, 2, 0, 1204504, 352807, 2965, 65536⟩
    (by decide) selected_cut_43906

theorem unmarked_context_11_88201_1204505 : frontier 10 ⟨1204505, by decide⟩
    (prefixCache 11 88201) (prefixPartial 11 88201) = false := by
  decide +kernel

theorem node_context_11_88201_1204505 : EJMOriginalGlobalDAGData.nodes 10 ⟨1204505, by decide⟩ =
    .split (coordinate 11) (![⟨1204364, by decide⟩,⟨1204408, by decide⟩,⟨1204454, by decide⟩,⟨1204504, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88201_1204505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88201 ⟨1204505, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88201
    ⟨1204505, by decide⟩ (by decide) (![⟨1204364, by decide⟩,⟨1204408, by decide⟩,⟨1204454, by decide⟩,⟨1204504, by decide⟩]) unmarked_context_11_88201_1204505 node_context_11_88201_1204505
  intro a
  fin_cases a
  · exact context_12_352804_1204364
  · exact context_12_352805_1204408
  · exact context_12_352806_1204454
  · exact context_12_352807_1204504

theorem selected_cut_43907 : selected 9 ⟨242157, by decide⟩
    (prefixPartial 12 352808) = some ⟨12, 1, 0, 242157, 352808, 1, 65536⟩ := by
  decide +kernel

theorem context_12_352808_242157 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352808 ⟨242157, by decide⟩ :=
  accepted_of_selected 12 352808 ⟨242157, by decide⟩ ⟨12, 1, 0, 242157, 352808, 1, 65536⟩
    (by decide) selected_cut_43907

theorem selected_cut_43908 : selected 9 ⟨1204551, by decide⟩
    (prefixPartial 12 352809) = some ⟨12, 2, 0, 1204551, 352809, 2497, 65536⟩ := by
  decide +kernel

theorem context_12_352809_1204551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352809 ⟨1204551, by decide⟩ :=
  accepted_of_selected 12 352809 ⟨1204551, by decide⟩ ⟨12, 2, 0, 1204551, 352809, 2497, 65536⟩
    (by decide) selected_cut_43908

theorem selected_cut_43909 : selected 9 ⟨474208, by decide⟩
    (prefixPartial 12 352810) = some ⟨12, 1, 0, 474208, 352810, 1, 65536⟩ := by
  decide +kernel

theorem context_12_352810_474208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352810 ⟨474208, by decide⟩ :=
  accepted_of_selected 12 352810 ⟨474208, by decide⟩ ⟨12, 1, 0, 474208, 352810, 1, 65536⟩
    (by decide) selected_cut_43909

theorem selected_cut_43910 : selected 9 ⟨1204607, by decide⟩
    (prefixPartial 12 352811) = some ⟨12, 2, 0, 1204607, 352811, 2853, 65536⟩ := by
  decide +kernel

theorem context_12_352811_1204607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352811 ⟨1204607, by decide⟩ :=
  accepted_of_selected 12 352811 ⟨1204607, by decide⟩ ⟨12, 2, 0, 1204607, 352811, 2853, 65536⟩
    (by decide) selected_cut_43910

theorem unmarked_context_11_88202_1204608 : frontier 10 ⟨1204608, by decide⟩
    (prefixCache 11 88202) (prefixPartial 11 88202) = false := by
  decide +kernel

theorem node_context_11_88202_1204608 : EJMOriginalGlobalDAGData.nodes 10 ⟨1204608, by decide⟩ =
    .split (coordinate 11) (![⟨242157, by decide⟩,⟨1204551, by decide⟩,⟨474208, by decide⟩,⟨1204607, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88202_1204608 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88202 ⟨1204608, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88202
    ⟨1204608, by decide⟩ (by decide) (![⟨242157, by decide⟩,⟨1204551, by decide⟩,⟨474208, by decide⟩,⟨1204607, by decide⟩]) unmarked_context_11_88202_1204608 node_context_11_88202_1204608
  intro a
  fin_cases a
  · exact context_12_352808_242157
  · exact context_12_352809_1204551
  · exact context_12_352810_474208
  · exact context_12_352811_1204607

theorem selected_cut_43911 : selected 9 ⟨1204668, by decide⟩
    (prefixPartial 12 352812) = some ⟨12, 2, 0, 1204668, 352812, 3057, 65536⟩ := by
  decide +kernel

theorem context_12_352812_1204668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352812 ⟨1204668, by decide⟩ :=
  accepted_of_selected 12 352812 ⟨1204668, by decide⟩ ⟨12, 2, 0, 1204668, 352812, 3057, 65536⟩
    (by decide) selected_cut_43911

theorem selected_cut_43912 : selected 9 ⟨1204709, by decide⟩
    (prefixPartial 12 352813) = some ⟨12, 2, 0, 1204709, 352813, 2481, 65536⟩ := by
  decide +kernel

theorem context_12_352813_1204709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352813 ⟨1204709, by decide⟩ :=
  accepted_of_selected 12 352813 ⟨1204709, by decide⟩ ⟨12, 2, 0, 1204709, 352813, 2481, 65536⟩
    (by decide) selected_cut_43912

theorem selected_cut_43913 : selected 9 ⟨1204751, by decide⟩
    (prefixPartial 12 352814) = some ⟨12, 2, 0, 1204751, 352814, 2333, 65536⟩ := by
  decide +kernel

theorem context_12_352814_1204751 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352814 ⟨1204751, by decide⟩ :=
  accepted_of_selected 12 352814 ⟨1204751, by decide⟩ ⟨12, 2, 0, 1204751, 352814, 2333, 65536⟩
    (by decide) selected_cut_43913

theorem selected_cut_43914 : selected 9 ⟨1204796, by decide⟩
    (prefixPartial 12 352815) = some ⟨12, 2, 0, 1204796, 352815, 2597, 65536⟩ := by
  decide +kernel

theorem context_12_352815_1204796 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352815 ⟨1204796, by decide⟩ :=
  accepted_of_selected 12 352815 ⟨1204796, by decide⟩ ⟨12, 2, 0, 1204796, 352815, 2597, 65536⟩
    (by decide) selected_cut_43914

theorem unmarked_context_11_88203_1204797 : frontier 10 ⟨1204797, by decide⟩
    (prefixCache 11 88203) (prefixPartial 11 88203) = false := by
  decide +kernel

theorem node_context_11_88203_1204797 : EJMOriginalGlobalDAGData.nodes 10 ⟨1204797, by decide⟩ =
    .split (coordinate 11) (![⟨1204668, by decide⟩,⟨1204709, by decide⟩,⟨1204751, by decide⟩,⟨1204796, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88203_1204797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88203 ⟨1204797, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88203
    ⟨1204797, by decide⟩ (by decide) (![⟨1204668, by decide⟩,⟨1204709, by decide⟩,⟨1204751, by decide⟩,⟨1204796, by decide⟩]) unmarked_context_11_88203_1204797 node_context_11_88203_1204797
  intro a
  fin_cases a
  · exact context_12_352812_1204668
  · exact context_12_352813_1204709
  · exact context_12_352814_1204751
  · exact context_12_352815_1204796

theorem unmarked_context_10_22050_1204798 : frontier 11 ⟨1204798, by decide⟩
    (prefixCache 10 22050) (prefixPartial 10 22050) = false := by
  decide +kernel

theorem node_context_10_22050_1204798 : EJMOriginalGlobalDAGData.nodes 11 ⟨1204798, by decide⟩ =
    .split (coordinate 10) (![⟨1204293, by decide⟩,⟨1204505, by decide⟩,⟨1204608, by decide⟩,⟨1204797, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22050_1204798 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22050 ⟨1204798, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22050
    ⟨1204798, by decide⟩ (by decide) (![⟨1204293, by decide⟩,⟨1204505, by decide⟩,⟨1204608, by decide⟩,⟨1204797, by decide⟩]) unmarked_context_10_22050_1204798 node_context_10_22050_1204798
  intro a
  fin_cases a
  · exact context_11_88200_1204293
  · exact context_11_88201_1204505
  · exact context_11_88202_1204608
  · exact context_11_88203_1204797

theorem selected_cut_43915 : selected 9 ⟨1187656, by decide⟩
    (prefixPartial 12 352816) = some ⟨12, 1, 0, 1187656, 352816, 1, 65536⟩ := by
  decide +kernel

theorem context_12_352816_1187656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352816 ⟨1187656, by decide⟩ :=
  accepted_of_selected 12 352816 ⟨1187656, by decide⟩ ⟨12, 1, 0, 1187656, 352816, 1, 65536⟩
    (by decide) selected_cut_43915

theorem selected_cut_43916 : selected 9 ⟨1204828, by decide⟩
    (prefixPartial 12 352817) = some ⟨12, 2, 0, 1204828, 352817, 2141, 65536⟩ := by
  decide +kernel

theorem context_12_352817_1204828 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352817 ⟨1204828, by decide⟩ :=
  accepted_of_selected 12 352817 ⟨1204828, by decide⟩ ⟨12, 2, 0, 1204828, 352817, 2141, 65536⟩
    (by decide) selected_cut_43916

theorem selected_cut_43917 : selected 9 ⟨1204860, by decide⟩
    (prefixPartial 12 352818) = some ⟨12, 2, 0, 1204860, 352818, 2065, 65536⟩ := by
  decide +kernel

theorem context_12_352818_1204860 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352818 ⟨1204860, by decide⟩ :=
  accepted_of_selected 12 352818 ⟨1204860, by decide⟩ ⟨12, 2, 0, 1204860, 352818, 2065, 65536⟩
    (by decide) selected_cut_43917

theorem selected_cut_43918 : selected 9 ⟨1204899, by decide⟩
    (prefixPartial 12 352819) = some ⟨12, 2, 0, 1204899, 352819, 2525, 65536⟩ := by
  decide +kernel

theorem context_12_352819_1204899 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352819 ⟨1204899, by decide⟩ :=
  accepted_of_selected 12 352819 ⟨1204899, by decide⟩ ⟨12, 2, 0, 1204899, 352819, 2525, 65536⟩
    (by decide) selected_cut_43918

theorem unmarked_context_11_88204_1204900 : frontier 10 ⟨1204900, by decide⟩
    (prefixCache 11 88204) (prefixPartial 11 88204) = false := by
  decide +kernel

theorem node_context_11_88204_1204900 : EJMOriginalGlobalDAGData.nodes 10 ⟨1204900, by decide⟩ =
    .split (coordinate 11) (![⟨1187656, by decide⟩,⟨1204828, by decide⟩,⟨1204860, by decide⟩,⟨1204899, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88204_1204900 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88204 ⟨1204900, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88204
    ⟨1204900, by decide⟩ (by decide) (![⟨1187656, by decide⟩,⟨1204828, by decide⟩,⟨1204860, by decide⟩,⟨1204899, by decide⟩]) unmarked_context_11_88204_1204900 node_context_11_88204_1204900
  intro a
  fin_cases a
  · exact context_12_352816_1187656
  · exact context_12_352817_1204828
  · exact context_12_352818_1204860
  · exact context_12_352819_1204899

theorem selected_cut_43919 : selected 9 ⟨1204952, by decide⟩
    (prefixPartial 12 352820) = some ⟨12, 2, 0, 1204952, 352820, 2681, 65536⟩ := by
  decide +kernel

theorem context_12_352820_1204952 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352820 ⟨1204952, by decide⟩ :=
  accepted_of_selected 12 352820 ⟨1204952, by decide⟩ ⟨12, 2, 0, 1204952, 352820, 2681, 65536⟩
    (by decide) selected_cut_43919

theorem selected_cut_43920 : selected 9 ⟨1204989, by decide⟩
    (prefixPartial 12 352821) = some ⟨12, 2, 0, 1204989, 352821, 2237, 65536⟩ := by
  decide +kernel

theorem context_12_352821_1204989 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352821 ⟨1204989, by decide⟩ :=
  accepted_of_selected 12 352821 ⟨1204989, by decide⟩ ⟨12, 2, 0, 1204989, 352821, 2237, 65536⟩
    (by decide) selected_cut_43920

theorem selected_cut_43921 : selected 9 ⟨1205018, by decide⟩
    (prefixPartial 12 352822) = some ⟨12, 2, 0, 1205018, 352822, 2109, 65536⟩ := by
  decide +kernel

theorem context_12_352822_1205018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352822 ⟨1205018, by decide⟩ :=
  accepted_of_selected 12 352822 ⟨1205018, by decide⟩ ⟨12, 2, 0, 1205018, 352822, 2109, 65536⟩
    (by decide) selected_cut_43921

theorem selected_cut_43922 : selected 9 ⟨1205062, by decide⟩
    (prefixPartial 12 352823) = some ⟨12, 2, 0, 1205062, 352823, 2417, 65536⟩ := by
  decide +kernel

theorem context_12_352823_1205062 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352823 ⟨1205062, by decide⟩ :=
  accepted_of_selected 12 352823 ⟨1205062, by decide⟩ ⟨12, 2, 0, 1205062, 352823, 2417, 65536⟩
    (by decide) selected_cut_43922

theorem unmarked_context_11_88205_1205063 : frontier 10 ⟨1205063, by decide⟩
    (prefixCache 11 88205) (prefixPartial 11 88205) = false := by
  decide +kernel

theorem node_context_11_88205_1205063 : EJMOriginalGlobalDAGData.nodes 10 ⟨1205063, by decide⟩ =
    .split (coordinate 11) (![⟨1204952, by decide⟩,⟨1204989, by decide⟩,⟨1205018, by decide⟩,⟨1205062, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88205_1205063 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88205 ⟨1205063, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88205
    ⟨1205063, by decide⟩ (by decide) (![⟨1204952, by decide⟩,⟨1204989, by decide⟩,⟨1205018, by decide⟩,⟨1205062, by decide⟩]) unmarked_context_11_88205_1205063 node_context_11_88205_1205063
  intro a
  fin_cases a
  · exact context_12_352820_1204952
  · exact context_12_352821_1204989
  · exact context_12_352822_1205018
  · exact context_12_352823_1205062

theorem selected_cut_43923 : selected 9 ⟨1205108, by decide⟩
    (prefixPartial 12 352824) = some ⟨12, 2, 0, 1205108, 352824, 2581, 65536⟩ := by
  decide +kernel

theorem context_12_352824_1205108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352824 ⟨1205108, by decide⟩ :=
  accepted_of_selected 12 352824 ⟨1205108, by decide⟩ ⟨12, 2, 0, 1205108, 352824, 2581, 65536⟩
    (by decide) selected_cut_43923

theorem selected_cut_43924 : selected 9 ⟨1205148, by decide⟩
    (prefixPartial 12 352825) = some ⟨12, 2, 0, 1205148, 352825, 2261, 65536⟩ := by
  decide +kernel

theorem context_12_352825_1205148 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352825 ⟨1205148, by decide⟩ :=
  accepted_of_selected 12 352825 ⟨1205148, by decide⟩ ⟨12, 2, 0, 1205148, 352825, 2261, 65536⟩
    (by decide) selected_cut_43924

theorem selected_cut_43925 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 352826) = some ⟨12, 1, 0, 893903, 352826, 1, 65536⟩ := by
  decide +kernel

theorem context_12_352826_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352826 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 352826 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 352826, 1, 65536⟩
    (by decide) selected_cut_43925

theorem selected_cut_43926 : selected 9 ⟨1205201, by decide⟩
    (prefixPartial 12 352827) = some ⟨12, 2, 0, 1205201, 352827, 2477, 65536⟩ := by
  decide +kernel

theorem context_12_352827_1205201 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352827 ⟨1205201, by decide⟩ :=
  accepted_of_selected 12 352827 ⟨1205201, by decide⟩ ⟨12, 2, 0, 1205201, 352827, 2477, 65536⟩
    (by decide) selected_cut_43926

theorem unmarked_context_11_88206_1205202 : frontier 10 ⟨1205202, by decide⟩
    (prefixCache 11 88206) (prefixPartial 11 88206) = false := by
  decide +kernel

theorem node_context_11_88206_1205202 : EJMOriginalGlobalDAGData.nodes 10 ⟨1205202, by decide⟩ =
    .split (coordinate 11) (![⟨1205108, by decide⟩,⟨1205148, by decide⟩,⟨893903, by decide⟩,⟨1205201, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88206_1205202 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88206 ⟨1205202, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88206
    ⟨1205202, by decide⟩ (by decide) (![⟨1205108, by decide⟩,⟨1205148, by decide⟩,⟨893903, by decide⟩,⟨1205201, by decide⟩]) unmarked_context_11_88206_1205202 node_context_11_88206_1205202
  intro a
  fin_cases a
  · exact context_12_352824_1205108
  · exact context_12_352825_1205148
  · exact context_12_352826_893903
  · exact context_12_352827_1205201

theorem selected_cut_43927 : selected 9 ⟨1205240, by decide⟩
    (prefixPartial 12 352828) = some ⟨12, 2, 0, 1205240, 352828, 2141, 65536⟩ := by
  decide +kernel

theorem context_12_352828_1205240 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352828 ⟨1205240, by decide⟩ :=
  accepted_of_selected 12 352828 ⟨1205240, by decide⟩ ⟨12, 2, 0, 1205240, 352828, 2141, 65536⟩
    (by decide) selected_cut_43927

theorem selected_cut_43928 : selected 9 ⟨1205267, by decide⟩
    (prefixPartial 12 352829) = some ⟨12, 2, 0, 1205267, 352829, 1865, 65536⟩ := by
  decide +kernel

theorem context_12_352829_1205267 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352829 ⟨1205267, by decide⟩ :=
  accepted_of_selected 12 352829 ⟨1205267, by decide⟩ ⟨12, 2, 0, 1205267, 352829, 1865, 65536⟩
    (by decide) selected_cut_43928

theorem selected_cut_43929 : selected 9 ⟨1205294, by decide⟩
    (prefixPartial 12 352830) = some ⟨12, 2, 0, 1205294, 352830, 1833, 65536⟩ := by
  decide +kernel

theorem context_12_352830_1205294 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352830 ⟨1205294, by decide⟩ :=
  accepted_of_selected 12 352830 ⟨1205294, by decide⟩ ⟨12, 2, 0, 1205294, 352830, 1833, 65536⟩
    (by decide) selected_cut_43929

theorem selected_cut_43930 : selected 9 ⟨607719, by decide⟩
    (prefixPartial 12 352831) = some ⟨12, 1, 0, 607719, 352831, 1, 65536⟩ := by
  decide +kernel

theorem context_12_352831_607719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352831 ⟨607719, by decide⟩ :=
  accepted_of_selected 12 352831 ⟨607719, by decide⟩ ⟨12, 1, 0, 607719, 352831, 1, 65536⟩
    (by decide) selected_cut_43930

theorem unmarked_context_11_88207_1205295 : frontier 10 ⟨1205295, by decide⟩
    (prefixCache 11 88207) (prefixPartial 11 88207) = false := by
  decide +kernel

theorem node_context_11_88207_1205295 : EJMOriginalGlobalDAGData.nodes 10 ⟨1205295, by decide⟩ =
    .split (coordinate 11) (![⟨1205240, by decide⟩,⟨1205267, by decide⟩,⟨1205294, by decide⟩,⟨607719, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88207_1205295 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88207 ⟨1205295, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88207
    ⟨1205295, by decide⟩ (by decide) (![⟨1205240, by decide⟩,⟨1205267, by decide⟩,⟨1205294, by decide⟩,⟨607719, by decide⟩]) unmarked_context_11_88207_1205295 node_context_11_88207_1205295
  intro a
  fin_cases a
  · exact context_12_352828_1205240
  · exact context_12_352829_1205267
  · exact context_12_352830_1205294
  · exact context_12_352831_607719

theorem unmarked_context_10_22051_1205296 : frontier 11 ⟨1205296, by decide⟩
    (prefixCache 10 22051) (prefixPartial 10 22051) = false := by
  decide +kernel

theorem node_context_10_22051_1205296 : EJMOriginalGlobalDAGData.nodes 11 ⟨1205296, by decide⟩ =
    .split (coordinate 10) (![⟨1204900, by decide⟩,⟨1205063, by decide⟩,⟨1205202, by decide⟩,⟨1205295, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22051_1205296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22051 ⟨1205296, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22051
    ⟨1205296, by decide⟩ (by decide) (![⟨1204900, by decide⟩,⟨1205063, by decide⟩,⟨1205202, by decide⟩,⟨1205295, by decide⟩]) unmarked_context_10_22051_1205296 node_context_10_22051_1205296
  intro a
  fin_cases a
  · exact context_11_88204_1204900
  · exact context_11_88205_1205063
  · exact context_11_88206_1205202
  · exact context_11_88207_1205295

theorem unmarked_context_9_5512_1205297 : frontier 12 ⟨1205297, by decide⟩
    (prefixCache 9 5512) (prefixPartial 9 5512) = false := by
  decide +kernel

theorem node_context_9_5512_1205297 : EJMOriginalGlobalDAGData.nodes 12 ⟨1205297, by decide⟩ =
    .split (coordinate 9) (![⟨1203622, by decide⟩,⟨1204169, by decide⟩,⟨1204798, by decide⟩,⟨1205296, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5512_1205297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5512 ⟨1205297, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5512
    ⟨1205297, by decide⟩ (by decide) (![⟨1203622, by decide⟩,⟨1204169, by decide⟩,⟨1204798, by decide⟩,⟨1205296, by decide⟩]) unmarked_context_9_5512_1205297 node_context_9_5512_1205297
  intro a
  fin_cases a
  · exact context_10_22048_1203622
  · exact context_10_22049_1204169
  · exact context_10_22050_1204798
  · exact context_10_22051_1205296

theorem selected_cut_43931 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 88208) = some ⟨11, 1, 0, 907917, 88208, 1, 262144⟩ := by
  decide +kernel

theorem context_11_88208_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88208 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 88208 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 88208, 1, 262144⟩
    (by decide) selected_cut_43931

theorem selected_cut_43932 : selected 9 ⟨1205329, by decide⟩
    (prefixPartial 12 352836) = some ⟨12, 2, 0, 1205329, 352836, 1693, 65536⟩ := by
  decide +kernel

theorem context_12_352836_1205329 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352836 ⟨1205329, by decide⟩ :=
  accepted_of_selected 12 352836 ⟨1205329, by decide⟩ ⟨12, 2, 0, 1205329, 352836, 1693, 65536⟩
    (by decide) selected_cut_43932

theorem selected_cut_43933 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 352837) = some ⟨12, 1, 0, 896706, 352837, 1, 65536⟩ := by
  decide +kernel

theorem context_12_352837_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352837 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 352837 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 352837, 1, 65536⟩
    (by decide) selected_cut_43933

theorem selected_cut_43934 : selected 9 ⟨1205352, by decide⟩
    (prefixPartial 12 352838) = some ⟨12, 2, 0, 1205352, 352838, 1497, 65536⟩ := by
  decide +kernel

theorem context_12_352838_1205352 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352838 ⟨1205352, by decide⟩ :=
  accepted_of_selected 12 352838 ⟨1205352, by decide⟩ ⟨12, 2, 0, 1205352, 352838, 1497, 65536⟩
    (by decide) selected_cut_43934

theorem selected_cut_43935 : selected 9 ⟨1205383, by decide⟩
    (prefixPartial 12 352839) = some ⟨12, 2, 0, 1205383, 352839, 1657, 65536⟩ := by
  decide +kernel

theorem context_12_352839_1205383 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352839 ⟨1205383, by decide⟩ :=
  accepted_of_selected 12 352839 ⟨1205383, by decide⟩ ⟨12, 2, 0, 1205383, 352839, 1657, 65536⟩
    (by decide) selected_cut_43935

theorem unmarked_context_11_88209_1205384 : frontier 10 ⟨1205384, by decide⟩
    (prefixCache 11 88209) (prefixPartial 11 88209) = false := by
  decide +kernel

theorem node_context_11_88209_1205384 : EJMOriginalGlobalDAGData.nodes 10 ⟨1205384, by decide⟩ =
    .split (coordinate 11) (![⟨1205329, by decide⟩,⟨896706, by decide⟩,⟨1205352, by decide⟩,⟨1205383, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88209_1205384 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88209 ⟨1205384, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88209
    ⟨1205384, by decide⟩ (by decide) (![⟨1205329, by decide⟩,⟨896706, by decide⟩,⟨1205352, by decide⟩,⟨1205383, by decide⟩]) unmarked_context_11_88209_1205384 node_context_11_88209_1205384
  intro a
  fin_cases a
  · exact context_12_352836_1205329
  · exact context_12_352837_896706
  · exact context_12_352838_1205352
  · exact context_12_352839_1205383

theorem selected_cut_43936 : selected 10 ⟨1205451, by decide⟩
    (prefixPartial 11 88210) = some ⟨11, 2, 0, 1205451, 88210, 3625, 262144⟩ := by
  decide +kernel

theorem context_11_88210_1205451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88210 ⟨1205451, by decide⟩ :=
  accepted_of_selected 11 88210 ⟨1205451, by decide⟩ ⟨11, 2, 0, 1205451, 88210, 3625, 262144⟩
    (by decide) selected_cut_43936

theorem selected_cut_43937 : selected 9 ⟨1205481, by decide⟩
    (prefixPartial 12 352844) = some ⟨12, 2, 0, 1205481, 352844, 1637, 65536⟩ := by
  decide +kernel

theorem context_12_352844_1205481 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352844 ⟨1205481, by decide⟩ :=
  accepted_of_selected 12 352844 ⟨1205481, by decide⟩ ⟨12, 2, 0, 1205481, 352844, 1637, 65536⟩
    (by decide) selected_cut_43937

theorem selected_cut_43938 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 352845) = some ⟨12, 1, 0, 896706, 352845, 1, 65536⟩ := by
  decide +kernel

theorem context_12_352845_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352845 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 352845 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 352845, 1, 65536⟩
    (by decide) selected_cut_43938

theorem selected_cut_43939 : selected 9 ⟨1205506, by decide⟩
    (prefixPartial 12 352846) = some ⟨12, 2, 0, 1205506, 352846, 1489, 65536⟩ := by
  decide +kernel

theorem context_12_352846_1205506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352846 ⟨1205506, by decide⟩ :=
  accepted_of_selected 12 352846 ⟨1205506, by decide⟩ ⟨12, 2, 0, 1205506, 352846, 1489, 65536⟩
    (by decide) selected_cut_43939

theorem selected_cut_43940 : selected 9 ⟨1205529, by decide⟩
    (prefixPartial 12 352847) = some ⟨12, 2, 0, 1205529, 352847, 1529, 65536⟩ := by
  decide +kernel

theorem context_12_352847_1205529 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352847 ⟨1205529, by decide⟩ :=
  accepted_of_selected 12 352847 ⟨1205529, by decide⟩ ⟨12, 2, 0, 1205529, 352847, 1529, 65536⟩
    (by decide) selected_cut_43940

theorem unmarked_context_11_88211_1205530 : frontier 10 ⟨1205530, by decide⟩
    (prefixCache 11 88211) (prefixPartial 11 88211) = false := by
  decide +kernel

theorem node_context_11_88211_1205530 : EJMOriginalGlobalDAGData.nodes 10 ⟨1205530, by decide⟩ =
    .split (coordinate 11) (![⟨1205481, by decide⟩,⟨896706, by decide⟩,⟨1205506, by decide⟩,⟨1205529, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88211_1205530 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88211 ⟨1205530, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88211
    ⟨1205530, by decide⟩ (by decide) (![⟨1205481, by decide⟩,⟨896706, by decide⟩,⟨1205506, by decide⟩,⟨1205529, by decide⟩]) unmarked_context_11_88211_1205530 node_context_11_88211_1205530
  intro a
  fin_cases a
  · exact context_12_352844_1205481
  · exact context_12_352845_896706
  · exact context_12_352846_1205506
  · exact context_12_352847_1205529

theorem unmarked_context_10_22052_1205531 : frontier 11 ⟨1205531, by decide⟩
    (prefixCache 10 22052) (prefixPartial 10 22052) = false := by
  decide +kernel

theorem node_context_10_22052_1205531 : EJMOriginalGlobalDAGData.nodes 11 ⟨1205531, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨1205384, by decide⟩,⟨1205451, by decide⟩,⟨1205530, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22052_1205531 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22052 ⟨1205531, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22052
    ⟨1205531, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨1205384, by decide⟩,⟨1205451, by decide⟩,⟨1205530, by decide⟩]) unmarked_context_10_22052_1205531 node_context_10_22052_1205531
  intro a
  fin_cases a
  · exact context_11_88208_907917
  · exact context_11_88209_1205384
  · exact context_11_88210_1205451
  · exact context_11_88211_1205530

theorem selected_cut_43941 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 22053) = some ⟨10, 1, 0, 893098, 22053, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_22053_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22053 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 22053 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 22053, 1, 1048576⟩
    (by decide) selected_cut_43941

theorem selected_cut_43942 : selected 10 ⟨1205577, by decide⟩
    (prefixPartial 11 88216) = some ⟨11, 2, 0, 1205577, 88216, 2917, 262144⟩ := by
  decide +kernel

theorem context_11_88216_1205577 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88216 ⟨1205577, by decide⟩ :=
  accepted_of_selected 11 88216 ⟨1205577, by decide⟩ ⟨11, 2, 0, 1205577, 88216, 2917, 262144⟩
    (by decide) selected_cut_43942

theorem selected_cut_43943 : selected 9 ⟨1205606, by decide⟩
    (prefixPartial 12 352868) = some ⟨12, 2, 0, 1205606, 352868, 1653, 65536⟩ := by
  decide +kernel

theorem context_12_352868_1205606 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352868 ⟨1205606, by decide⟩ :=
  accepted_of_selected 12 352868 ⟨1205606, by decide⟩ ⟨12, 2, 0, 1205606, 352868, 1653, 65536⟩
    (by decide) selected_cut_43943

theorem selected_cut_43944 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 352869) = some ⟨12, 1, 0, 896706, 352869, 1, 65536⟩ := by
  decide +kernel

theorem context_12_352869_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352869 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 352869 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 352869, 1, 65536⟩
    (by decide) selected_cut_43944

theorem selected_cut_43945 : selected 9 ⟨1205621, by decide⟩
    (prefixPartial 12 352870) = some ⟨12, 2, 0, 1205621, 352870, 1277, 65536⟩ := by
  decide +kernel

theorem context_12_352870_1205621 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352870 ⟨1205621, by decide⟩ :=
  accepted_of_selected 12 352870 ⟨1205621, by decide⟩ ⟨12, 2, 0, 1205621, 352870, 1277, 65536⟩
    (by decide) selected_cut_43945

theorem selected_cut_43946 : selected 9 ⟨1205649, by decide⟩
    (prefixPartial 12 352871) = some ⟨12, 2, 0, 1205649, 352871, 1573, 65536⟩ := by
  decide +kernel

theorem context_12_352871_1205649 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352871 ⟨1205649, by decide⟩ :=
  accepted_of_selected 12 352871 ⟨1205649, by decide⟩ ⟨12, 2, 0, 1205649, 352871, 1573, 65536⟩
    (by decide) selected_cut_43946

theorem unmarked_context_11_88217_1205650 : frontier 10 ⟨1205650, by decide⟩
    (prefixCache 11 88217) (prefixPartial 11 88217) = false := by
  decide +kernel

theorem node_context_11_88217_1205650 : EJMOriginalGlobalDAGData.nodes 10 ⟨1205650, by decide⟩ =
    .split (coordinate 11) (![⟨1205606, by decide⟩,⟨896706, by decide⟩,⟨1205621, by decide⟩,⟨1205649, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88217_1205650 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88217 ⟨1205650, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88217
    ⟨1205650, by decide⟩ (by decide) (![⟨1205606, by decide⟩,⟨896706, by decide⟩,⟨1205621, by decide⟩,⟨1205649, by decide⟩]) unmarked_context_11_88217_1205650 node_context_11_88217_1205650
  intro a
  fin_cases a
  · exact context_12_352868_1205606
  · exact context_12_352869_896706
  · exact context_12_352870_1205621
  · exact context_12_352871_1205649

theorem selected_cut_43947 : selected 10 ⟨1205678, by decide⟩
    (prefixPartial 11 88218) = some ⟨11, 2, 0, 1205678, 88218, 1525, 262144⟩ := by
  decide +kernel

theorem context_11_88218_1205678 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88218 ⟨1205678, by decide⟩ :=
  accepted_of_selected 11 88218 ⟨1205678, by decide⟩ ⟨11, 2, 0, 1205678, 88218, 1525, 262144⟩
    (by decide) selected_cut_43947

theorem selected_cut_43948 : selected 9 ⟨1205717, by decide⟩
    (prefixPartial 12 352876) = some ⟨12, 2, 0, 1205717, 352876, 1693, 65536⟩ := by
  decide +kernel

theorem context_12_352876_1205717 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352876 ⟨1205717, by decide⟩ :=
  accepted_of_selected 12 352876 ⟨1205717, by decide⟩ ⟨12, 2, 0, 1205717, 352876, 1693, 65536⟩
    (by decide) selected_cut_43948

theorem selected_cut_43949 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 352877) = some ⟨12, 1, 0, 896706, 352877, 1, 65536⟩ := by
  decide +kernel

theorem context_12_352877_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352877 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 352877 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 352877, 1, 65536⟩
    (by decide) selected_cut_43949

theorem selected_cut_43950 : selected 9 ⟨1205738, by decide⟩
    (prefixPartial 12 352878) = some ⟨12, 2, 0, 1205738, 352878, 1285, 65536⟩ := by
  decide +kernel

theorem context_12_352878_1205738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352878 ⟨1205738, by decide⟩ :=
  accepted_of_selected 12 352878 ⟨1205738, by decide⟩ ⟨12, 2, 0, 1205738, 352878, 1285, 65536⟩
    (by decide) selected_cut_43950

theorem selected_cut_43951 : selected 9 ⟨1205767, by decide⟩
    (prefixPartial 12 352879) = some ⟨12, 2, 0, 1205767, 352879, 1533, 65536⟩ := by
  decide +kernel

theorem context_12_352879_1205767 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352879 ⟨1205767, by decide⟩ :=
  accepted_of_selected 12 352879 ⟨1205767, by decide⟩ ⟨12, 2, 0, 1205767, 352879, 1533, 65536⟩
    (by decide) selected_cut_43951

theorem unmarked_context_11_88219_1205768 : frontier 10 ⟨1205768, by decide⟩
    (prefixCache 11 88219) (prefixPartial 11 88219) = false := by
  decide +kernel

theorem node_context_11_88219_1205768 : EJMOriginalGlobalDAGData.nodes 10 ⟨1205768, by decide⟩ =
    .split (coordinate 11) (![⟨1205717, by decide⟩,⟨896706, by decide⟩,⟨1205738, by decide⟩,⟨1205767, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88219_1205768 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88219 ⟨1205768, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88219
    ⟨1205768, by decide⟩ (by decide) (![⟨1205717, by decide⟩,⟨896706, by decide⟩,⟨1205738, by decide⟩,⟨1205767, by decide⟩]) unmarked_context_11_88219_1205768 node_context_11_88219_1205768
  intro a
  fin_cases a
  · exact context_12_352876_1205717
  · exact context_12_352877_896706
  · exact context_12_352878_1205738
  · exact context_12_352879_1205767

theorem unmarked_context_10_22054_1205769 : frontier 11 ⟨1205769, by decide⟩
    (prefixCache 10 22054) (prefixPartial 10 22054) = false := by
  decide +kernel

theorem node_context_10_22054_1205769 : EJMOriginalGlobalDAGData.nodes 11 ⟨1205769, by decide⟩ =
    .split (coordinate 10) (![⟨1205577, by decide⟩,⟨1205650, by decide⟩,⟨1205678, by decide⟩,⟨1205768, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22054_1205769 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22054 ⟨1205769, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22054
    ⟨1205769, by decide⟩ (by decide) (![⟨1205577, by decide⟩,⟨1205650, by decide⟩,⟨1205678, by decide⟩,⟨1205768, by decide⟩]) unmarked_context_10_22054_1205769 node_context_10_22054_1205769
  intro a
  fin_cases a
  · exact context_11_88216_1205577
  · exact context_11_88217_1205650
  · exact context_11_88218_1205678
  · exact context_11_88219_1205768

theorem selected_cut_43952 : selected 10 ⟨1205820, by decide⟩
    (prefixPartial 11 88220) = some ⟨11, 2, 0, 1205820, 88220, 3769, 262144⟩ := by
  decide +kernel

theorem context_11_88220_1205820 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88220 ⟨1205820, by decide⟩ :=
  accepted_of_selected 11 88220 ⟨1205820, by decide⟩ ⟨11, 2, 0, 1205820, 88220, 3769, 262144⟩
    (by decide) selected_cut_43952

theorem selected_cut_43953 : selected 10 ⟨1205871, by decide⟩
    (prefixPartial 11 88221) = some ⟨11, 2, 0, 1205871, 88221, 3593, 262144⟩ := by
  decide +kernel

theorem context_11_88221_1205871 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88221 ⟨1205871, by decide⟩ :=
  accepted_of_selected 11 88221 ⟨1205871, by decide⟩ ⟨11, 2, 0, 1205871, 88221, 3593, 262144⟩
    (by decide) selected_cut_43953

theorem selected_cut_43954 : selected 10 ⟨1205906, by decide⟩
    (prefixPartial 11 88222) = some ⟨11, 2, 0, 1205906, 88222, 2429, 262144⟩ := by
  decide +kernel

theorem context_11_88222_1205906 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88222 ⟨1205906, by decide⟩ :=
  accepted_of_selected 11 88222 ⟨1205906, by decide⟩ ⟨11, 2, 0, 1205906, 88222, 2429, 262144⟩
    (by decide) selected_cut_43954

theorem selected_cut_43955 : selected 10 ⟨1205937, by decide⟩
    (prefixPartial 11 88223) = some ⟨11, 2, 0, 1205937, 88223, 2245, 262144⟩ := by
  decide +kernel

theorem context_11_88223_1205937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88223 ⟨1205937, by decide⟩ :=
  accepted_of_selected 11 88223 ⟨1205937, by decide⟩ ⟨11, 2, 0, 1205937, 88223, 2245, 262144⟩
    (by decide) selected_cut_43955

theorem unmarked_context_10_22055_1205938 : frontier 11 ⟨1205938, by decide⟩
    (prefixCache 10 22055) (prefixPartial 10 22055) = false := by
  decide +kernel

theorem node_context_10_22055_1205938 : EJMOriginalGlobalDAGData.nodes 11 ⟨1205938, by decide⟩ =
    .split (coordinate 10) (![⟨1205820, by decide⟩,⟨1205871, by decide⟩,⟨1205906, by decide⟩,⟨1205937, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22055_1205938 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22055 ⟨1205938, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22055
    ⟨1205938, by decide⟩ (by decide) (![⟨1205820, by decide⟩,⟨1205871, by decide⟩,⟨1205906, by decide⟩,⟨1205937, by decide⟩]) unmarked_context_10_22055_1205938 node_context_10_22055_1205938
  intro a
  fin_cases a
  · exact context_11_88220_1205820
  · exact context_11_88221_1205871
  · exact context_11_88222_1205906
  · exact context_11_88223_1205937

theorem unmarked_context_9_5513_1205939 : frontier 12 ⟨1205939, by decide⟩
    (prefixCache 9 5513) (prefixPartial 9 5513) = false := by
  decide +kernel

theorem node_context_9_5513_1205939 : EJMOriginalGlobalDAGData.nodes 12 ⟨1205939, by decide⟩ =
    .split (coordinate 9) (![⟨1205531, by decide⟩,⟨893098, by decide⟩,⟨1205769, by decide⟩,⟨1205938, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5513_1205939 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5513 ⟨1205939, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5513
    ⟨1205939, by decide⟩ (by decide) (![⟨1205531, by decide⟩,⟨893098, by decide⟩,⟨1205769, by decide⟩,⟨1205938, by decide⟩]) unmarked_context_9_5513_1205939 node_context_9_5513_1205939
  intro a
  fin_cases a
  · exact context_10_22052_1205531
  · exact context_10_22053_893098
  · exact context_10_22054_1205769
  · exact context_10_22055_1205938

theorem selected_cut_43956 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 88224) = some ⟨11, 1, 0, 907917, 88224, 1, 262144⟩ := by
  decide +kernel

theorem context_11_88224_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88224 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 88224 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 88224, 1, 262144⟩
    (by decide) selected_cut_43956

theorem selected_cut_43957 : selected 10 ⟨1205998, by decide⟩
    (prefixPartial 11 88225) = some ⟨11, 2, 0, 1205998, 88225, 2805, 262144⟩ := by
  decide +kernel

theorem context_11_88225_1205998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88225 ⟨1205998, by decide⟩ :=
  accepted_of_selected 11 88225 ⟨1205998, by decide⟩ ⟨11, 2, 0, 1205998, 88225, 2805, 262144⟩
    (by decide) selected_cut_43957

theorem selected_cut_43958 : selected 10 ⟨1206066, by decide⟩
    (prefixPartial 11 88226) = some ⟨11, 2, 0, 1206066, 88226, 4013, 262144⟩ := by
  decide +kernel

theorem context_11_88226_1206066 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88226 ⟨1206066, by decide⟩ :=
  accepted_of_selected 11 88226 ⟨1206066, by decide⟩ ⟨11, 2, 0, 1206066, 88226, 4013, 262144⟩
    (by decide) selected_cut_43958

theorem selected_cut_43959 : selected 9 ⟨1206088, by decide⟩
    (prefixPartial 12 352908) = some ⟨12, 2, 0, 1206088, 352908, 1277, 65536⟩ := by
  decide +kernel

theorem context_12_352908_1206088 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352908 ⟨1206088, by decide⟩ :=
  accepted_of_selected 12 352908 ⟨1206088, by decide⟩ ⟨12, 2, 0, 1206088, 352908, 1277, 65536⟩
    (by decide) selected_cut_43959

theorem selected_cut_43960 : selected 9 ⟨1206108, by decide⟩
    (prefixPartial 12 352909) = some ⟨12, 2, 0, 1206108, 352909, 1117, 65536⟩ := by
  decide +kernel

theorem context_12_352909_1206108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352909 ⟨1206108, by decide⟩ :=
  accepted_of_selected 12 352909 ⟨1206108, by decide⟩ ⟨12, 2, 0, 1206108, 352909, 1117, 65536⟩
    (by decide) selected_cut_43960

theorem selected_cut_43961 : selected 9 ⟨1206130, by decide⟩
    (prefixPartial 12 352910) = some ⟨12, 2, 0, 1206130, 352910, 1153, 65536⟩ := by
  decide +kernel

theorem context_12_352910_1206130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352910 ⟨1206130, by decide⟩ :=
  accepted_of_selected 12 352910 ⟨1206130, by decide⟩ ⟨12, 2, 0, 1206130, 352910, 1153, 65536⟩
    (by decide) selected_cut_43961

theorem selected_cut_43962 : selected 9 ⟨1206151, by decide⟩
    (prefixPartial 12 352911) = some ⟨12, 2, 0, 1206151, 352911, 1197, 65536⟩ := by
  decide +kernel

theorem context_12_352911_1206151 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352911 ⟨1206151, by decide⟩ :=
  accepted_of_selected 12 352911 ⟨1206151, by decide⟩ ⟨12, 2, 0, 1206151, 352911, 1197, 65536⟩
    (by decide) selected_cut_43962

theorem unmarked_context_11_88227_1206152 : frontier 10 ⟨1206152, by decide⟩
    (prefixCache 11 88227) (prefixPartial 11 88227) = false := by
  decide +kernel

theorem node_context_11_88227_1206152 : EJMOriginalGlobalDAGData.nodes 10 ⟨1206152, by decide⟩ =
    .split (coordinate 11) (![⟨1206088, by decide⟩,⟨1206108, by decide⟩,⟨1206130, by decide⟩,⟨1206151, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88227_1206152 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88227 ⟨1206152, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88227
    ⟨1206152, by decide⟩ (by decide) (![⟨1206088, by decide⟩,⟨1206108, by decide⟩,⟨1206130, by decide⟩,⟨1206151, by decide⟩]) unmarked_context_11_88227_1206152 node_context_11_88227_1206152
  intro a
  fin_cases a
  · exact context_12_352908_1206088
  · exact context_12_352909_1206108
  · exact context_12_352910_1206130
  · exact context_12_352911_1206151

theorem unmarked_context_10_22056_1206153 : frontier 11 ⟨1206153, by decide⟩
    (prefixCache 10 22056) (prefixPartial 10 22056) = false := by
  decide +kernel

theorem node_context_10_22056_1206153 : EJMOriginalGlobalDAGData.nodes 11 ⟨1206153, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨1205998, by decide⟩,⟨1206066, by decide⟩,⟨1206152, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22056_1206153 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22056 ⟨1206153, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22056
    ⟨1206153, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨1205998, by decide⟩,⟨1206066, by decide⟩,⟨1206152, by decide⟩]) unmarked_context_10_22056_1206153 node_context_10_22056_1206153
  intro a
  fin_cases a
  · exact context_11_88224_907917
  · exact context_11_88225_1205998
  · exact context_11_88226_1206066
  · exact context_11_88227_1206152

theorem selected_cut_43963 : selected 10 ⟨1206221, by decide⟩
    (prefixPartial 11 88228) = some ⟨11, 2, 0, 1206221, 88228, 3517, 262144⟩ := by
  decide +kernel

theorem context_11_88228_1206221 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88228 ⟨1206221, by decide⟩ :=
  accepted_of_selected 11 88228 ⟨1206221, by decide⟩ ⟨11, 2, 0, 1206221, 88228, 3517, 262144⟩
    (by decide) selected_cut_43963

theorem selected_cut_43964 : selected 10 ⟨1206269, by decide⟩
    (prefixPartial 11 88229) = some ⟨11, 2, 0, 1206269, 88229, 2485, 262144⟩ := by
  decide +kernel

theorem context_11_88229_1206269 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88229 ⟨1206269, by decide⟩ :=
  accepted_of_selected 11 88229 ⟨1206269, by decide⟩ ⟨11, 2, 0, 1206269, 88229, 2485, 262144⟩
    (by decide) selected_cut_43964

theorem selected_cut_43965 : selected 10 ⟨1206328, by decide⟩
    (prefixPartial 11 88230) = some ⟨11, 2, 0, 1206328, 88230, 3457, 262144⟩ := by
  decide +kernel

theorem context_11_88230_1206328 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88230 ⟨1206328, by decide⟩ :=
  accepted_of_selected 11 88230 ⟨1206328, by decide⟩ ⟨11, 2, 0, 1206328, 88230, 3457, 262144⟩
    (by decide) selected_cut_43965

theorem selected_cut_43966 : selected 9 ⟨1206352, by decide⟩
    (prefixPartial 12 352924) = some ⟨12, 2, 0, 1206352, 352924, 1197, 65536⟩ := by
  decide +kernel

theorem context_12_352924_1206352 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352924 ⟨1206352, by decide⟩ :=
  accepted_of_selected 12 352924 ⟨1206352, by decide⟩ ⟨12, 2, 0, 1206352, 352924, 1197, 65536⟩
    (by decide) selected_cut_43966

theorem selected_cut_43967 : selected 9 ⟨1206369, by decide⟩
    (prefixPartial 12 352925) = some ⟨12, 2, 0, 1206369, 352925, 1113, 65536⟩ := by
  decide +kernel

theorem context_12_352925_1206369 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352925 ⟨1206369, by decide⟩ :=
  accepted_of_selected 12 352925 ⟨1206369, by decide⟩ ⟨12, 2, 0, 1206369, 352925, 1113, 65536⟩
    (by decide) selected_cut_43967

theorem selected_cut_43968 : selected 9 ⟨1206397, by decide⟩
    (prefixPartial 12 352926) = some ⟨12, 2, 0, 1206397, 352926, 1085, 65536⟩ := by
  decide +kernel

theorem context_12_352926_1206397 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352926 ⟨1206397, by decide⟩ :=
  accepted_of_selected 12 352926 ⟨1206397, by decide⟩ ⟨12, 2, 0, 1206397, 352926, 1085, 65536⟩
    (by decide) selected_cut_43968

theorem selected_cut_43969 : selected 9 ⟨1206420, by decide⟩
    (prefixPartial 12 352927) = some ⟨12, 2, 0, 1206420, 352927, 1161, 65536⟩ := by
  decide +kernel

theorem context_12_352927_1206420 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 352927 ⟨1206420, by decide⟩ :=
  accepted_of_selected 12 352927 ⟨1206420, by decide⟩ ⟨12, 2, 0, 1206420, 352927, 1161, 65536⟩
    (by decide) selected_cut_43969

theorem unmarked_context_11_88231_1206421 : frontier 10 ⟨1206421, by decide⟩
    (prefixCache 11 88231) (prefixPartial 11 88231) = false := by
  decide +kernel

theorem node_context_11_88231_1206421 : EJMOriginalGlobalDAGData.nodes 10 ⟨1206421, by decide⟩ =
    .split (coordinate 11) (![⟨1206352, by decide⟩,⟨1206369, by decide⟩,⟨1206397, by decide⟩,⟨1206420, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88231_1206421 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88231 ⟨1206421, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88231
    ⟨1206421, by decide⟩ (by decide) (![⟨1206352, by decide⟩,⟨1206369, by decide⟩,⟨1206397, by decide⟩,⟨1206420, by decide⟩]) unmarked_context_11_88231_1206421 node_context_11_88231_1206421
  intro a
  fin_cases a
  · exact context_12_352924_1206352
  · exact context_12_352925_1206369
  · exact context_12_352926_1206397
  · exact context_12_352927_1206420

theorem unmarked_context_10_22057_1206422 : frontier 11 ⟨1206422, by decide⟩
    (prefixCache 10 22057) (prefixPartial 10 22057) = false := by
  decide +kernel

theorem node_context_10_22057_1206422 : EJMOriginalGlobalDAGData.nodes 11 ⟨1206422, by decide⟩ =
    .split (coordinate 10) (![⟨1206221, by decide⟩,⟨1206269, by decide⟩,⟨1206328, by decide⟩,⟨1206421, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22057_1206422 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22057 ⟨1206422, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22057
    ⟨1206422, by decide⟩ (by decide) (![⟨1206221, by decide⟩,⟨1206269, by decide⟩,⟨1206328, by decide⟩,⟨1206421, by decide⟩]) unmarked_context_10_22057_1206422 node_context_10_22057_1206422
  intro a
  fin_cases a
  · exact context_11_88228_1206221
  · exact context_11_88229_1206269
  · exact context_11_88230_1206328
  · exact context_11_88231_1206421

theorem selected_cut_43970 : selected 10 ⟨1206453, by decide⟩
    (prefixPartial 11 88232) = some ⟨11, 2, 0, 1206453, 88232, 1705, 262144⟩ := by
  decide +kernel

theorem context_11_88232_1206453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88232 ⟨1206453, by decide⟩ :=
  accepted_of_selected 11 88232 ⟨1206453, by decide⟩ ⟨11, 2, 0, 1206453, 88232, 1705, 262144⟩
    (by decide) selected_cut_43970

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
