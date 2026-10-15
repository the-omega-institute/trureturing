/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover479
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_46082 : selected 10 ⟨1283168, by decide⟩
    (prefixPartial 11 92432) = some ⟨11, 1, 0, 1283168, 92432, 1, 262144⟩ := by
  decide +kernel

theorem context_11_92432_1283168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92432 ⟨1283168, by decide⟩ :=
  accepted_of_selected 11 92432 ⟨1283168, by decide⟩ ⟨11, 1, 0, 1283168, 92432, 1, 262144⟩
    (by decide) selected_cut_46082

theorem selected_cut_46083 : selected 9 ⟨1283218, by decide⟩
    (prefixPartial 12 369732) = some ⟨12, 2, 0, 1283218, 369732, 1921, 65536⟩ := by
  decide +kernel

theorem context_12_369732_1283218 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369732 ⟨1283218, by decide⟩ :=
  accepted_of_selected 12 369732 ⟨1283218, by decide⟩ ⟨12, 2, 0, 1283218, 369732, 1921, 65536⟩
    (by decide) selected_cut_46083

theorem selected_cut_46084 : selected 9 ⟨692443, by decide⟩
    (prefixPartial 12 369733) = some ⟨12, 1, 0, 692443, 369733, 1, 65536⟩ := by
  decide +kernel

theorem context_12_369733_692443 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369733 ⟨692443, by decide⟩ :=
  accepted_of_selected 12 369733 ⟨692443, by decide⟩ ⟨12, 1, 0, 692443, 369733, 1, 65536⟩
    (by decide) selected_cut_46084

theorem selected_cut_46085 : selected 9 ⟨1283263, by decide⟩
    (prefixPartial 12 369734) = some ⟨12, 2, 0, 1283263, 369734, 1809, 65536⟩ := by
  decide +kernel

theorem context_12_369734_1283263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369734 ⟨1283263, by decide⟩ :=
  accepted_of_selected 12 369734 ⟨1283263, by decide⟩ ⟨12, 2, 0, 1283263, 369734, 1809, 65536⟩
    (by decide) selected_cut_46085

theorem selected_cut_46086 : selected 9 ⟨1283311, by decide⟩
    (prefixPartial 12 369735) = some ⟨12, 2, 0, 1283311, 369735, 2013, 65536⟩ := by
  decide +kernel

theorem context_12_369735_1283311 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369735 ⟨1283311, by decide⟩ :=
  accepted_of_selected 12 369735 ⟨1283311, by decide⟩ ⟨12, 2, 0, 1283311, 369735, 2013, 65536⟩
    (by decide) selected_cut_46086

theorem unmarked_context_11_92433_1283312 : frontier 10 ⟨1283312, by decide⟩
    (prefixCache 11 92433) (prefixPartial 11 92433) = false := by
  decide +kernel

theorem node_context_11_92433_1283312 : EJMOriginalGlobalDAGData.nodes 10 ⟨1283312, by decide⟩ =
    .split (coordinate 11) (![⟨1283218, by decide⟩,⟨692443, by decide⟩,⟨1283263, by decide⟩,⟨1283311, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92433_1283312 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92433 ⟨1283312, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92433
    ⟨1283312, by decide⟩ (by decide) (![⟨1283218, by decide⟩,⟨692443, by decide⟩,⟨1283263, by decide⟩,⟨1283311, by decide⟩]) unmarked_context_11_92433_1283312 node_context_11_92433_1283312
  intro a
  fin_cases a
  · exact context_12_369732_1283218
  · exact context_12_369733_692443
  · exact context_12_369734_1283263
  · exact context_12_369735_1283311

theorem selected_cut_46087 : selected 10 ⟨1283400, by decide⟩
    (prefixPartial 11 92434) = some ⟨11, 2, 0, 1283400, 92434, 3805, 262144⟩ := by
  decide +kernel

theorem context_11_92434_1283400 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92434 ⟨1283400, by decide⟩ :=
  accepted_of_selected 11 92434 ⟨1283400, by decide⟩ ⟨11, 2, 0, 1283400, 92434, 3805, 262144⟩
    (by decide) selected_cut_46087

theorem selected_cut_46088 : selected 9 ⟨1283440, by decide⟩
    (prefixPartial 12 369740) = some ⟨12, 2, 0, 1283440, 369740, 1913, 65536⟩ := by
  decide +kernel

theorem context_12_369740_1283440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369740 ⟨1283440, by decide⟩ :=
  accepted_of_selected 12 369740 ⟨1283440, by decide⟩ ⟨12, 2, 0, 1283440, 369740, 1913, 65536⟩
    (by decide) selected_cut_46088

theorem selected_cut_46089 : selected 9 ⟨1283463, by decide⟩
    (prefixPartial 12 369741) = some ⟨12, 2, 0, 1283463, 369741, 1477, 65536⟩ := by
  decide +kernel

theorem context_12_369741_1283463 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369741 ⟨1283463, by decide⟩ :=
  accepted_of_selected 12 369741 ⟨1283463, by decide⟩ ⟨12, 2, 0, 1283463, 369741, 1477, 65536⟩
    (by decide) selected_cut_46089

theorem selected_cut_46090 : selected 9 ⟨1283512, by decide⟩
    (prefixPartial 12 369742) = some ⟨12, 2, 0, 1283512, 369742, 1933, 65536⟩ := by
  decide +kernel

theorem context_12_369742_1283512 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369742 ⟨1283512, by decide⟩ :=
  accepted_of_selected 12 369742 ⟨1283512, by decide⟩ ⟨12, 2, 0, 1283512, 369742, 1933, 65536⟩
    (by decide) selected_cut_46090

theorem selected_cut_46091 : selected 9 ⟨1283553, by decide⟩
    (prefixPartial 12 369743) = some ⟨12, 2, 0, 1283553, 369743, 2017, 65536⟩ := by
  decide +kernel

theorem context_12_369743_1283553 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369743 ⟨1283553, by decide⟩ :=
  accepted_of_selected 12 369743 ⟨1283553, by decide⟩ ⟨12, 2, 0, 1283553, 369743, 2017, 65536⟩
    (by decide) selected_cut_46091

theorem unmarked_context_11_92435_1283554 : frontier 10 ⟨1283554, by decide⟩
    (prefixCache 11 92435) (prefixPartial 11 92435) = false := by
  decide +kernel

theorem node_context_11_92435_1283554 : EJMOriginalGlobalDAGData.nodes 10 ⟨1283554, by decide⟩ =
    .split (coordinate 11) (![⟨1283440, by decide⟩,⟨1283463, by decide⟩,⟨1283512, by decide⟩,⟨1283553, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92435_1283554 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92435 ⟨1283554, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92435
    ⟨1283554, by decide⟩ (by decide) (![⟨1283440, by decide⟩,⟨1283463, by decide⟩,⟨1283512, by decide⟩,⟨1283553, by decide⟩]) unmarked_context_11_92435_1283554 node_context_11_92435_1283554
  intro a
  fin_cases a
  · exact context_12_369740_1283440
  · exact context_12_369741_1283463
  · exact context_12_369742_1283512
  · exact context_12_369743_1283553

theorem unmarked_context_10_23108_1283555 : frontier 11 ⟨1283555, by decide⟩
    (prefixCache 10 23108) (prefixPartial 10 23108) = false := by
  decide +kernel

theorem node_context_10_23108_1283555 : EJMOriginalGlobalDAGData.nodes 11 ⟨1283555, by decide⟩ =
    .split (coordinate 10) (![⟨1283168, by decide⟩,⟨1283312, by decide⟩,⟨1283400, by decide⟩,⟨1283554, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23108_1283555 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23108 ⟨1283555, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23108
    ⟨1283555, by decide⟩ (by decide) (![⟨1283168, by decide⟩,⟨1283312, by decide⟩,⟨1283400, by decide⟩,⟨1283554, by decide⟩]) unmarked_context_10_23108_1283555 node_context_10_23108_1283555
  intro a
  fin_cases a
  · exact context_11_92432_1283168
  · exact context_11_92433_1283312
  · exact context_11_92434_1283400
  · exact context_11_92435_1283554

theorem selected_cut_46092 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 23109) = some ⟨10, 1, 0, 893098, 23109, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_23109_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23109 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 23109 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 23109, 1, 1048576⟩
    (by decide) selected_cut_46092

theorem selected_cut_46093 : selected 10 ⟨1283629, by decide⟩
    (prefixPartial 11 92440) = some ⟨11, 2, 0, 1283629, 92440, 3225, 262144⟩ := by
  decide +kernel

theorem context_11_92440_1283629 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92440 ⟨1283629, by decide⟩ :=
  accepted_of_selected 11 92440 ⟨1283629, by decide⟩ ⟨11, 2, 0, 1283629, 92440, 3225, 262144⟩
    (by decide) selected_cut_46093

theorem selected_cut_46094 : selected 9 ⟨1283665, by decide⟩
    (prefixPartial 12 369764) = some ⟨12, 2, 0, 1283665, 369764, 1673, 65536⟩ := by
  decide +kernel

theorem context_12_369764_1283665 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369764 ⟨1283665, by decide⟩ :=
  accepted_of_selected 12 369764 ⟨1283665, by decide⟩ ⟨12, 2, 0, 1283665, 369764, 1673, 65536⟩
    (by decide) selected_cut_46094

theorem selected_cut_46095 : selected 9 ⟨1256866, by decide⟩
    (prefixPartial 12 369765) = some ⟨12, 1, 0, 1256866, 369765, 1, 65536⟩ := by
  decide +kernel

theorem context_12_369765_1256866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369765 ⟨1256866, by decide⟩ :=
  accepted_of_selected 12 369765 ⟨1256866, by decide⟩ ⟨12, 1, 0, 1256866, 369765, 1, 65536⟩
    (by decide) selected_cut_46095

theorem selected_cut_46096 : selected 9 ⟨1283697, by decide⟩
    (prefixPartial 12 369766) = some ⟨12, 2, 0, 1283697, 369766, 1545, 65536⟩ := by
  decide +kernel

theorem context_12_369766_1283697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369766 ⟨1283697, by decide⟩ :=
  accepted_of_selected 12 369766 ⟨1283697, by decide⟩ ⟨12, 2, 0, 1283697, 369766, 1545, 65536⟩
    (by decide) selected_cut_46096

theorem selected_cut_46097 : selected 9 ⟨1283735, by decide⟩
    (prefixPartial 12 369767) = some ⟨12, 2, 0, 1283735, 369767, 1737, 65536⟩ := by
  decide +kernel

theorem context_12_369767_1283735 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369767 ⟨1283735, by decide⟩ :=
  accepted_of_selected 12 369767 ⟨1283735, by decide⟩ ⟨12, 2, 0, 1283735, 369767, 1737, 65536⟩
    (by decide) selected_cut_46097

theorem unmarked_context_11_92441_1283736 : frontier 10 ⟨1283736, by decide⟩
    (prefixCache 11 92441) (prefixPartial 11 92441) = false := by
  decide +kernel

theorem node_context_11_92441_1283736 : EJMOriginalGlobalDAGData.nodes 10 ⟨1283736, by decide⟩ =
    .split (coordinate 11) (![⟨1283665, by decide⟩,⟨1256866, by decide⟩,⟨1283697, by decide⟩,⟨1283735, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92441_1283736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92441 ⟨1283736, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92441
    ⟨1283736, by decide⟩ (by decide) (![⟨1283665, by decide⟩,⟨1256866, by decide⟩,⟨1283697, by decide⟩,⟨1283735, by decide⟩]) unmarked_context_11_92441_1283736 node_context_11_92441_1283736
  intro a
  fin_cases a
  · exact context_12_369764_1283665
  · exact context_12_369765_1256866
  · exact context_12_369766_1283697
  · exact context_12_369767_1283735

theorem selected_cut_46098 : selected 10 ⟨1283737, by decide⟩
    (prefixPartial 11 92442) = some ⟨11, 1, 0, 1283737, 92442, 1, 262144⟩ := by
  decide +kernel

theorem context_11_92442_1283737 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92442 ⟨1283737, by decide⟩ :=
  accepted_of_selected 11 92442 ⟨1283737, by decide⟩ ⟨11, 1, 0, 1283737, 92442, 1, 262144⟩
    (by decide) selected_cut_46098

theorem selected_cut_46099 : selected 9 ⟨1283772, by decide⟩
    (prefixPartial 12 369772) = some ⟨12, 2, 0, 1283772, 369772, 1645, 65536⟩ := by
  decide +kernel

theorem context_12_369772_1283772 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369772 ⟨1283772, by decide⟩ :=
  accepted_of_selected 12 369772 ⟨1283772, by decide⟩ ⟨12, 2, 0, 1283772, 369772, 1645, 65536⟩
    (by decide) selected_cut_46099

theorem selected_cut_46100 : selected 9 ⟨1256866, by decide⟩
    (prefixPartial 12 369773) = some ⟨12, 1, 0, 1256866, 369773, 1, 65536⟩ := by
  decide +kernel

theorem context_12_369773_1256866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369773 ⟨1256866, by decide⟩ :=
  accepted_of_selected 12 369773 ⟨1256866, by decide⟩ ⟨12, 1, 0, 1256866, 369773, 1, 65536⟩
    (by decide) selected_cut_46100

theorem selected_cut_46101 : selected 9 ⟨1283817, by decide⟩
    (prefixPartial 12 369774) = some ⟨12, 2, 0, 1283817, 369774, 1673, 65536⟩ := by
  decide +kernel

theorem context_12_369774_1283817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369774 ⟨1283817, by decide⟩ :=
  accepted_of_selected 12 369774 ⟨1283817, by decide⟩ ⟨12, 2, 0, 1283817, 369774, 1673, 65536⟩
    (by decide) selected_cut_46101

theorem selected_cut_46102 : selected 9 ⟨1283862, by decide⟩
    (prefixPartial 12 369775) = some ⟨12, 2, 0, 1283862, 369775, 1757, 65536⟩ := by
  decide +kernel

theorem context_12_369775_1283862 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369775 ⟨1283862, by decide⟩ :=
  accepted_of_selected 12 369775 ⟨1283862, by decide⟩ ⟨12, 2, 0, 1283862, 369775, 1757, 65536⟩
    (by decide) selected_cut_46102

theorem unmarked_context_11_92443_1283863 : frontier 10 ⟨1283863, by decide⟩
    (prefixCache 11 92443) (prefixPartial 11 92443) = false := by
  decide +kernel

theorem node_context_11_92443_1283863 : EJMOriginalGlobalDAGData.nodes 10 ⟨1283863, by decide⟩ =
    .split (coordinate 11) (![⟨1283772, by decide⟩,⟨1256866, by decide⟩,⟨1283817, by decide⟩,⟨1283862, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92443_1283863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92443 ⟨1283863, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92443
    ⟨1283863, by decide⟩ (by decide) (![⟨1283772, by decide⟩,⟨1256866, by decide⟩,⟨1283817, by decide⟩,⟨1283862, by decide⟩]) unmarked_context_11_92443_1283863 node_context_11_92443_1283863
  intro a
  fin_cases a
  · exact context_12_369772_1283772
  · exact context_12_369773_1256866
  · exact context_12_369774_1283817
  · exact context_12_369775_1283862

theorem unmarked_context_10_23110_1283864 : frontier 11 ⟨1283864, by decide⟩
    (prefixCache 10 23110) (prefixPartial 10 23110) = false := by
  decide +kernel

theorem node_context_10_23110_1283864 : EJMOriginalGlobalDAGData.nodes 11 ⟨1283864, by decide⟩ =
    .split (coordinate 10) (![⟨1283629, by decide⟩,⟨1283736, by decide⟩,⟨1283737, by decide⟩,⟨1283863, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23110_1283864 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23110 ⟨1283864, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23110
    ⟨1283864, by decide⟩ (by decide) (![⟨1283629, by decide⟩,⟨1283736, by decide⟩,⟨1283737, by decide⟩,⟨1283863, by decide⟩]) unmarked_context_10_23110_1283864 node_context_10_23110_1283864
  intro a
  fin_cases a
  · exact context_11_92440_1283629
  · exact context_11_92441_1283736
  · exact context_11_92442_1283737
  · exact context_11_92443_1283863

theorem selected_cut_46103 : selected 10 ⟨1283950, by decide⟩
    (prefixPartial 11 92444) = some ⟨11, 2, 0, 1283950, 92444, 4093, 262144⟩ := by
  decide +kernel

theorem context_11_92444_1283950 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92444 ⟨1283950, by decide⟩ :=
  accepted_of_selected 11 92444 ⟨1283950, by decide⟩ ⟨11, 2, 0, 1283950, 92444, 4093, 262144⟩
    (by decide) selected_cut_46103

theorem selected_cut_46104 : selected 10 ⟨1284035, by decide⟩
    (prefixPartial 11 92445) = some ⟨11, 2, 0, 1284035, 92445, 4053, 262144⟩ := by
  decide +kernel

theorem context_11_92445_1284035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92445 ⟨1284035, by decide⟩ :=
  accepted_of_selected 11 92445 ⟨1284035, by decide⟩ ⟨11, 2, 0, 1284035, 92445, 4053, 262144⟩
    (by decide) selected_cut_46104

theorem selected_cut_46105 : selected 9 ⟨1284066, by decide⟩
    (prefixPartial 12 369784) = some ⟨12, 2, 0, 1284066, 369784, 1257, 65536⟩ := by
  decide +kernel

theorem context_12_369784_1284066 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369784 ⟨1284066, by decide⟩ :=
  accepted_of_selected 12 369784 ⟨1284066, by decide⟩ ⟨12, 2, 0, 1284066, 369784, 1257, 65536⟩
    (by decide) selected_cut_46105

theorem selected_cut_46106 : selected 9 ⟨1284079, by decide⟩
    (prefixPartial 12 369785) = some ⟨12, 2, 0, 1284079, 369785, 1013, 65536⟩ := by
  decide +kernel

theorem context_12_369785_1284079 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369785 ⟨1284079, by decide⟩ :=
  accepted_of_selected 12 369785 ⟨1284079, by decide⟩ ⟨12, 2, 0, 1284079, 369785, 1013, 65536⟩
    (by decide) selected_cut_46106

theorem selected_cut_46107 : selected 9 ⟨1284101, by decide⟩
    (prefixPartial 12 369786) = some ⟨12, 2, 0, 1284101, 369786, 1145, 65536⟩ := by
  decide +kernel

theorem context_12_369786_1284101 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369786 ⟨1284101, by decide⟩ :=
  accepted_of_selected 12 369786 ⟨1284101, by decide⟩ ⟨12, 2, 0, 1284101, 369786, 1145, 65536⟩
    (by decide) selected_cut_46107

theorem selected_cut_46108 : selected 9 ⟨1284136, by decide⟩
    (prefixPartial 12 369787) = some ⟨12, 2, 0, 1284136, 369787, 1361, 65536⟩ := by
  decide +kernel

theorem context_12_369787_1284136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369787 ⟨1284136, by decide⟩ :=
  accepted_of_selected 12 369787 ⟨1284136, by decide⟩ ⟨12, 2, 0, 1284136, 369787, 1361, 65536⟩
    (by decide) selected_cut_46108

theorem unmarked_context_11_92446_1284137 : frontier 10 ⟨1284137, by decide⟩
    (prefixCache 11 92446) (prefixPartial 11 92446) = false := by
  decide +kernel

theorem node_context_11_92446_1284137 : EJMOriginalGlobalDAGData.nodes 10 ⟨1284137, by decide⟩ =
    .split (coordinate 11) (![⟨1284066, by decide⟩,⟨1284079, by decide⟩,⟨1284101, by decide⟩,⟨1284136, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92446_1284137 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92446 ⟨1284137, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92446
    ⟨1284137, by decide⟩ (by decide) (![⟨1284066, by decide⟩,⟨1284079, by decide⟩,⟨1284101, by decide⟩,⟨1284136, by decide⟩]) unmarked_context_11_92446_1284137 node_context_11_92446_1284137
  intro a
  fin_cases a
  · exact context_12_369784_1284066
  · exact context_12_369785_1284079
  · exact context_12_369786_1284101
  · exact context_12_369787_1284136

theorem selected_cut_46109 : selected 10 ⟨1284138, by decide⟩
    (prefixPartial 11 92447) = some ⟨11, 1, 0, 1284138, 92447, 1, 262144⟩ := by
  decide +kernel

theorem context_11_92447_1284138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92447 ⟨1284138, by decide⟩ :=
  accepted_of_selected 11 92447 ⟨1284138, by decide⟩ ⟨11, 1, 0, 1284138, 92447, 1, 262144⟩
    (by decide) selected_cut_46109

theorem unmarked_context_10_23111_1284139 : frontier 11 ⟨1284139, by decide⟩
    (prefixCache 10 23111) (prefixPartial 10 23111) = false := by
  decide +kernel

theorem node_context_10_23111_1284139 : EJMOriginalGlobalDAGData.nodes 11 ⟨1284139, by decide⟩ =
    .split (coordinate 10) (![⟨1283950, by decide⟩,⟨1284035, by decide⟩,⟨1284137, by decide⟩,⟨1284138, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23111_1284139 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23111 ⟨1284139, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23111
    ⟨1284139, by decide⟩ (by decide) (![⟨1283950, by decide⟩,⟨1284035, by decide⟩,⟨1284137, by decide⟩,⟨1284138, by decide⟩]) unmarked_context_10_23111_1284139 node_context_10_23111_1284139
  intro a
  fin_cases a
  · exact context_11_92444_1283950
  · exact context_11_92445_1284035
  · exact context_11_92446_1284137
  · exact context_11_92447_1284138

theorem unmarked_context_9_5777_1284140 : frontier 12 ⟨1284140, by decide⟩
    (prefixCache 9 5777) (prefixPartial 9 5777) = false := by
  decide +kernel

theorem node_context_9_5777_1284140 : EJMOriginalGlobalDAGData.nodes 12 ⟨1284140, by decide⟩ =
    .split (coordinate 9) (![⟨1283555, by decide⟩,⟨893098, by decide⟩,⟨1283864, by decide⟩,⟨1284139, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5777_1284140 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5777 ⟨1284140, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5777
    ⟨1284140, by decide⟩ (by decide) (![⟨1283555, by decide⟩,⟨893098, by decide⟩,⟨1283864, by decide⟩,⟨1284139, by decide⟩]) unmarked_context_9_5777_1284140 node_context_9_5777_1284140
  intro a
  fin_cases a
  · exact context_10_23108_1283555
  · exact context_10_23109_893098
  · exact context_10_23110_1283864
  · exact context_10_23111_1284139

theorem selected_cut_46110 : selected 10 ⟨1284161, by decide⟩
    (prefixPartial 11 92448) = some ⟨11, 2, 0, 1284161, 92448, 1081, 262144⟩ := by
  decide +kernel

theorem context_11_92448_1284161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92448 ⟨1284161, by decide⟩ :=
  accepted_of_selected 11 92448 ⟨1284161, by decide⟩ ⟨11, 2, 0, 1284161, 92448, 1081, 262144⟩
    (by decide) selected_cut_46110

theorem selected_cut_46111 : selected 10 ⟨1284202, by decide⟩
    (prefixPartial 11 92449) = some ⟨11, 2, 0, 1284202, 92449, 2173, 262144⟩ := by
  decide +kernel

theorem context_11_92449_1284202 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92449 ⟨1284202, by decide⟩ :=
  accepted_of_selected 11 92449 ⟨1284202, by decide⟩ ⟨11, 2, 0, 1284202, 92449, 2173, 262144⟩
    (by decide) selected_cut_46111

theorem selected_cut_46112 : selected 10 ⟨1284246, by decide⟩
    (prefixPartial 11 92450) = some ⟨11, 2, 0, 1284246, 92450, 3037, 262144⟩ := by
  decide +kernel

theorem context_11_92450_1284246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92450 ⟨1284246, by decide⟩ :=
  accepted_of_selected 11 92450 ⟨1284246, by decide⟩ ⟨11, 2, 0, 1284246, 92450, 3037, 262144⟩
    (by decide) selected_cut_46112

theorem selected_cut_46113 : selected 10 ⟨1284289, by decide⟩
    (prefixPartial 11 92451) = some ⟨11, 2, 0, 1284289, 92451, 2737, 262144⟩ := by
  decide +kernel

theorem context_11_92451_1284289 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92451 ⟨1284289, by decide⟩ :=
  accepted_of_selected 11 92451 ⟨1284289, by decide⟩ ⟨11, 2, 0, 1284289, 92451, 2737, 262144⟩
    (by decide) selected_cut_46113

theorem unmarked_context_10_23112_1284290 : frontier 11 ⟨1284290, by decide⟩
    (prefixCache 10 23112) (prefixPartial 10 23112) = false := by
  decide +kernel

theorem node_context_10_23112_1284290 : EJMOriginalGlobalDAGData.nodes 11 ⟨1284290, by decide⟩ =
    .split (coordinate 10) (![⟨1284161, by decide⟩,⟨1284202, by decide⟩,⟨1284246, by decide⟩,⟨1284289, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23112_1284290 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23112 ⟨1284290, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23112
    ⟨1284290, by decide⟩ (by decide) (![⟨1284161, by decide⟩,⟨1284202, by decide⟩,⟨1284246, by decide⟩,⟨1284289, by decide⟩]) unmarked_context_10_23112_1284290 node_context_10_23112_1284290
  intro a
  fin_cases a
  · exact context_11_92448_1284161
  · exact context_11_92449_1284202
  · exact context_11_92450_1284246
  · exact context_11_92451_1284289

theorem selected_cut_46114 : selected 10 ⟨1284309, by decide⟩
    (prefixPartial 11 92452) = some ⟨11, 2, 0, 1284309, 92452, 1489, 262144⟩ := by
  decide +kernel

theorem context_11_92452_1284309 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92452 ⟨1284309, by decide⟩ :=
  accepted_of_selected 11 92452 ⟨1284309, by decide⟩ ⟨11, 2, 0, 1284309, 92452, 1489, 262144⟩
    (by decide) selected_cut_46114

theorem selected_cut_46115 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 92453) = some ⟨11, 1, 0, 892405, 92453, 1, 262144⟩ := by
  decide +kernel

theorem context_11_92453_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92453 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 92453 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 92453, 1, 262144⟩
    (by decide) selected_cut_46115

theorem selected_cut_46116 : selected 10 ⟨1284341, by decide⟩
    (prefixPartial 11 92454) = some ⟨11, 2, 0, 1284341, 92454, 2241, 262144⟩ := by
  decide +kernel

theorem context_11_92454_1284341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92454 ⟨1284341, by decide⟩ :=
  accepted_of_selected 11 92454 ⟨1284341, by decide⟩ ⟨11, 2, 0, 1284341, 92454, 2241, 262144⟩
    (by decide) selected_cut_46116

theorem selected_cut_46117 : selected 10 ⟨1284374, by decide⟩
    (prefixPartial 11 92455) = some ⟨11, 2, 0, 1284374, 92455, 2161, 262144⟩ := by
  decide +kernel

theorem context_11_92455_1284374 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92455 ⟨1284374, by decide⟩ :=
  accepted_of_selected 11 92455 ⟨1284374, by decide⟩ ⟨11, 2, 0, 1284374, 92455, 2161, 262144⟩
    (by decide) selected_cut_46117

theorem unmarked_context_10_23113_1284375 : frontier 11 ⟨1284375, by decide⟩
    (prefixCache 10 23113) (prefixPartial 10 23113) = false := by
  decide +kernel

theorem node_context_10_23113_1284375 : EJMOriginalGlobalDAGData.nodes 11 ⟨1284375, by decide⟩ =
    .split (coordinate 10) (![⟨1284309, by decide⟩,⟨892405, by decide⟩,⟨1284341, by decide⟩,⟨1284374, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23113_1284375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23113 ⟨1284375, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23113
    ⟨1284375, by decide⟩ (by decide) (![⟨1284309, by decide⟩,⟨892405, by decide⟩,⟨1284341, by decide⟩,⟨1284374, by decide⟩]) unmarked_context_10_23113_1284375 node_context_10_23113_1284375
  intro a
  fin_cases a
  · exact context_11_92452_1284309
  · exact context_11_92453_892405
  · exact context_11_92454_1284341
  · exact context_11_92455_1284374

theorem selected_cut_46118 : selected 11 ⟨1284414, by decide⟩
    (prefixPartial 10 23114) = some ⟨10, 2, 0, 1284414, 23114, 2309, 1048576⟩ := by
  decide +kernel

theorem context_10_23114_1284414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23114 ⟨1284414, by decide⟩ :=
  accepted_of_selected 10 23114 ⟨1284414, by decide⟩ ⟨10, 2, 0, 1284414, 23114, 2309, 1048576⟩
    (by decide) selected_cut_46118

theorem selected_cut_46119 : selected 10 ⟨1284431, by decide⟩
    (prefixPartial 11 92460) = some ⟨11, 2, 0, 1284431, 92460, 1121, 262144⟩ := by
  decide +kernel

theorem context_11_92460_1284431 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92460 ⟨1284431, by decide⟩ :=
  accepted_of_selected 11 92460 ⟨1284431, by decide⟩ ⟨11, 2, 0, 1284431, 92460, 1121, 262144⟩
    (by decide) selected_cut_46119

theorem selected_cut_46120 : selected 10 ⟨1284457, by decide⟩
    (prefixPartial 11 92461) = some ⟨11, 2, 0, 1284457, 92461, 1653, 262144⟩ := by
  decide +kernel

theorem context_11_92461_1284457 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92461 ⟨1284457, by decide⟩ :=
  accepted_of_selected 11 92461 ⟨1284457, by decide⟩ ⟨11, 2, 0, 1284457, 92461, 1653, 262144⟩
    (by decide) selected_cut_46120

theorem selected_cut_46121 : selected 10 ⟨1284478, by decide⟩
    (prefixPartial 11 92462) = some ⟨11, 2, 0, 1284478, 92462, 1521, 262144⟩ := by
  decide +kernel

theorem context_11_92462_1284478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92462 ⟨1284478, by decide⟩ :=
  accepted_of_selected 11 92462 ⟨1284478, by decide⟩ ⟨11, 2, 0, 1284478, 92462, 1521, 262144⟩
    (by decide) selected_cut_46121

theorem selected_cut_46122 : selected 10 ⟨1284494, by decide⟩
    (prefixPartial 11 92463) = some ⟨11, 2, 0, 1284494, 92463, 817, 262144⟩ := by
  decide +kernel

theorem context_11_92463_1284494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92463 ⟨1284494, by decide⟩ :=
  accepted_of_selected 11 92463 ⟨1284494, by decide⟩ ⟨11, 2, 0, 1284494, 92463, 817, 262144⟩
    (by decide) selected_cut_46122

theorem unmarked_context_10_23115_1284495 : frontier 11 ⟨1284495, by decide⟩
    (prefixCache 10 23115) (prefixPartial 10 23115) = false := by
  decide +kernel

theorem node_context_10_23115_1284495 : EJMOriginalGlobalDAGData.nodes 11 ⟨1284495, by decide⟩ =
    .split (coordinate 10) (![⟨1284431, by decide⟩,⟨1284457, by decide⟩,⟨1284478, by decide⟩,⟨1284494, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23115_1284495 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23115 ⟨1284495, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23115
    ⟨1284495, by decide⟩ (by decide) (![⟨1284431, by decide⟩,⟨1284457, by decide⟩,⟨1284478, by decide⟩,⟨1284494, by decide⟩]) unmarked_context_10_23115_1284495 node_context_10_23115_1284495
  intro a
  fin_cases a
  · exact context_11_92460_1284431
  · exact context_11_92461_1284457
  · exact context_11_92462_1284478
  · exact context_11_92463_1284494

theorem unmarked_context_9_5778_1284496 : frontier 12 ⟨1284496, by decide⟩
    (prefixCache 9 5778) (prefixPartial 9 5778) = false := by
  decide +kernel

theorem node_context_9_5778_1284496 : EJMOriginalGlobalDAGData.nodes 12 ⟨1284496, by decide⟩ =
    .split (coordinate 9) (![⟨1284290, by decide⟩,⟨1284375, by decide⟩,⟨1284414, by decide⟩,⟨1284495, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5778_1284496 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5778 ⟨1284496, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5778
    ⟨1284496, by decide⟩ (by decide) (![⟨1284290, by decide⟩,⟨1284375, by decide⟩,⟨1284414, by decide⟩,⟨1284495, by decide⟩]) unmarked_context_9_5778_1284496 node_context_9_5778_1284496
  intro a
  fin_cases a
  · exact context_10_23112_1284290
  · exact context_10_23113_1284375
  · exact context_10_23114_1284414
  · exact context_10_23115_1284495

theorem selected_cut_46123 : selected 10 ⟨1284506, by decide⟩
    (prefixPartial 11 92464) = some ⟨11, 2, 0, 1284506, 92464, 909, 262144⟩ := by
  decide +kernel

theorem context_11_92464_1284506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92464 ⟨1284506, by decide⟩ :=
  accepted_of_selected 11 92464 ⟨1284506, by decide⟩ ⟨11, 2, 0, 1284506, 92464, 909, 262144⟩
    (by decide) selected_cut_46123

theorem selected_cut_46124 : selected 10 ⟨1284525, by decide⟩
    (prefixPartial 11 92465) = some ⟨11, 2, 0, 1284525, 92465, 1229, 262144⟩ := by
  decide +kernel

theorem context_11_92465_1284525 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92465 ⟨1284525, by decide⟩ :=
  accepted_of_selected 11 92465 ⟨1284525, by decide⟩ ⟨11, 2, 0, 1284525, 92465, 1229, 262144⟩
    (by decide) selected_cut_46124

theorem selected_cut_46125 : selected 10 ⟨1284551, by decide⟩
    (prefixPartial 11 92466) = some ⟨11, 2, 0, 1284551, 92466, 1537, 262144⟩ := by
  decide +kernel

theorem context_11_92466_1284551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92466 ⟨1284551, by decide⟩ :=
  accepted_of_selected 11 92466 ⟨1284551, by decide⟩ ⟨11, 2, 0, 1284551, 92466, 1537, 262144⟩
    (by decide) selected_cut_46125

theorem selected_cut_46126 : selected 10 ⟨1284572, by decide⟩
    (prefixPartial 11 92467) = some ⟨11, 2, 0, 1284572, 92467, 1129, 262144⟩ := by
  decide +kernel

theorem context_11_92467_1284572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92467 ⟨1284572, by decide⟩ :=
  accepted_of_selected 11 92467 ⟨1284572, by decide⟩ ⟨11, 2, 0, 1284572, 92467, 1129, 262144⟩
    (by decide) selected_cut_46126

theorem unmarked_context_10_23116_1284573 : frontier 11 ⟨1284573, by decide⟩
    (prefixCache 10 23116) (prefixPartial 10 23116) = false := by
  decide +kernel

theorem node_context_10_23116_1284573 : EJMOriginalGlobalDAGData.nodes 11 ⟨1284573, by decide⟩ =
    .split (coordinate 10) (![⟨1284506, by decide⟩,⟨1284525, by decide⟩,⟨1284551, by decide⟩,⟨1284572, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23116_1284573 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23116 ⟨1284573, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23116
    ⟨1284573, by decide⟩ (by decide) (![⟨1284506, by decide⟩,⟨1284525, by decide⟩,⟨1284551, by decide⟩,⟨1284572, by decide⟩]) unmarked_context_10_23116_1284573 node_context_10_23116_1284573
  intro a
  fin_cases a
  · exact context_11_92464_1284506
  · exact context_11_92465_1284525
  · exact context_11_92466_1284551
  · exact context_11_92467_1284572

theorem selected_cut_46127 : selected 11 ⟨1284622, by decide⟩
    (prefixPartial 10 23117) = some ⟨10, 2, 0, 1284622, 23117, 2577, 1048576⟩ := by
  decide +kernel

theorem context_10_23117_1284622 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23117 ⟨1284622, by decide⟩ :=
  accepted_of_selected 10 23117 ⟨1284622, by decide⟩ ⟨10, 2, 0, 1284622, 23117, 2577, 1048576⟩
    (by decide) selected_cut_46127

theorem selected_cut_46128 : selected 11 ⟨1284671, by decide⟩
    (prefixPartial 10 23118) = some ⟨10, 2, 0, 1284671, 23118, 1633, 1048576⟩ := by
  decide +kernel

theorem context_10_23118_1284671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23118 ⟨1284671, by decide⟩ :=
  accepted_of_selected 10 23118 ⟨1284671, by decide⟩ ⟨10, 2, 0, 1284671, 23118, 1633, 1048576⟩
    (by decide) selected_cut_46128

theorem selected_cut_46129 : selected 11 ⟨1284680, by decide⟩
    (prefixPartial 10 23119) = some ⟨10, 2, 0, 1284680, 23119, 209, 1048576⟩ := by
  decide +kernel

theorem context_10_23119_1284680 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23119 ⟨1284680, by decide⟩ :=
  accepted_of_selected 10 23119 ⟨1284680, by decide⟩ ⟨10, 2, 0, 1284680, 23119, 209, 1048576⟩
    (by decide) selected_cut_46129

theorem unmarked_context_9_5779_1284681 : frontier 12 ⟨1284681, by decide⟩
    (prefixCache 9 5779) (prefixPartial 9 5779) = false := by
  decide +kernel

theorem node_context_9_5779_1284681 : EJMOriginalGlobalDAGData.nodes 12 ⟨1284681, by decide⟩ =
    .split (coordinate 9) (![⟨1284573, by decide⟩,⟨1284622, by decide⟩,⟨1284671, by decide⟩,⟨1284680, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5779_1284681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5779 ⟨1284681, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5779
    ⟨1284681, by decide⟩ (by decide) (![⟨1284573, by decide⟩,⟨1284622, by decide⟩,⟨1284671, by decide⟩,⟨1284680, by decide⟩]) unmarked_context_9_5779_1284681 node_context_9_5779_1284681
  intro a
  fin_cases a
  · exact context_10_23116_1284573
  · exact context_10_23117_1284622
  · exact context_10_23118_1284671
  · exact context_10_23119_1284680

theorem unmarked_context_8_1444_1284682 : frontier 13 ⟨1284682, by decide⟩
    (prefixCache 8 1444) (prefixPartial 8 1444) = false := by
  decide +kernel

theorem node_context_8_1444_1284682 : EJMOriginalGlobalDAGData.nodes 13 ⟨1284682, by decide⟩ =
    .split (coordinate 8) (![⟨1283167, by decide⟩,⟨1284140, by decide⟩,⟨1284496, by decide⟩,⟨1284681, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1444_1284682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1444 ⟨1284682, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1444
    ⟨1284682, by decide⟩ (by decide) (![⟨1283167, by decide⟩,⟨1284140, by decide⟩,⟨1284496, by decide⟩,⟨1284681, by decide⟩]) unmarked_context_8_1444_1284682 node_context_8_1444_1284682
  intro a
  fin_cases a
  · exact context_9_5776_1283167
  · exact context_9_5777_1284140
  · exact context_9_5778_1284496
  · exact context_9_5779_1284681

theorem selected_cut_46130 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 92480) = some ⟨11, 1, 0, 434745, 92480, 1, 262144⟩ := by
  decide +kernel

theorem context_11_92480_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92480 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 92480 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 92480, 1, 262144⟩
    (by decide) selected_cut_46130

theorem selected_cut_46131 : selected 10 ⟨167448, by decide⟩
    (prefixPartial 11 92481) = some ⟨11, 1, 0, 167448, 92481, 1, 262144⟩ := by
  decide +kernel

theorem context_11_92481_167448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92481 ⟨167448, by decide⟩ :=
  accepted_of_selected 11 92481 ⟨167448, by decide⟩ ⟨11, 1, 0, 167448, 92481, 1, 262144⟩
    (by decide) selected_cut_46131

theorem selected_cut_46132 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 369928) = some ⟨12, 1, 0, 448748, 369928, 1, 65536⟩ := by
  decide +kernel

theorem context_12_369928_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369928 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 369928 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 369928, 1, 65536⟩
    (by decide) selected_cut_46132

theorem selected_cut_46133 : selected 9 ⟨1284740, by decide⟩
    (prefixPartial 12 369929) = some ⟨12, 2, 0, 1284740, 369929, 2569, 65536⟩ := by
  decide +kernel

theorem context_12_369929_1284740 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369929 ⟨1284740, by decide⟩ :=
  accepted_of_selected 12 369929 ⟨1284740, by decide⟩ ⟨12, 2, 0, 1284740, 369929, 2569, 65536⟩
    (by decide) selected_cut_46133

theorem selected_cut_46134 : selected 9 ⟨1284808, by decide⟩
    (prefixPartial 12 369930) = some ⟨12, 2, 0, 1284808, 369930, 2753, 65536⟩ := by
  decide +kernel

theorem context_12_369930_1284808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369930 ⟨1284808, by decide⟩ :=
  accepted_of_selected 12 369930 ⟨1284808, by decide⟩ ⟨12, 2, 0, 1284808, 369930, 2753, 65536⟩
    (by decide) selected_cut_46134

theorem selected_cut_46135 : selected 9 ⟨1284884, by decide⟩
    (prefixPartial 12 369931) = some ⟨12, 2, 0, 1284884, 369931, 3137, 65536⟩ := by
  decide +kernel

theorem context_12_369931_1284884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369931 ⟨1284884, by decide⟩ :=
  accepted_of_selected 12 369931 ⟨1284884, by decide⟩ ⟨12, 2, 0, 1284884, 369931, 3137, 65536⟩
    (by decide) selected_cut_46135

theorem unmarked_context_11_92482_1284885 : frontier 10 ⟨1284885, by decide⟩
    (prefixCache 11 92482) (prefixPartial 11 92482) = false := by
  decide +kernel

theorem node_context_11_92482_1284885 : EJMOriginalGlobalDAGData.nodes 10 ⟨1284885, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1284740, by decide⟩,⟨1284808, by decide⟩,⟨1284884, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92482_1284885 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92482 ⟨1284885, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92482
    ⟨1284885, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1284740, by decide⟩,⟨1284808, by decide⟩,⟨1284884, by decide⟩]) unmarked_context_11_92482_1284885 node_context_11_92482_1284885
  intro a
  fin_cases a
  · exact context_12_369928_448748
  · exact context_12_369929_1284740
  · exact context_12_369930_1284808
  · exact context_12_369931_1284884

theorem selected_cut_46136 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 369932) = some ⟨12, 1, 0, 448748, 369932, 1, 65536⟩ := by
  decide +kernel

theorem context_12_369932_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369932 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 369932 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 369932, 1, 65536⟩
    (by decide) selected_cut_46136

theorem selected_cut_46137 : selected 9 ⟨1284928, by decide⟩
    (prefixPartial 12 369933) = some ⟨12, 2, 0, 1284928, 369933, 2493, 65536⟩ := by
  decide +kernel

theorem context_12_369933_1284928 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369933 ⟨1284928, by decide⟩ :=
  accepted_of_selected 12 369933 ⟨1284928, by decide⟩ ⟨12, 2, 0, 1284928, 369933, 2493, 65536⟩
    (by decide) selected_cut_46137

theorem selected_cut_46138 : selected 9 ⟨1284982, by decide⟩
    (prefixPartial 12 369934) = some ⟨12, 2, 0, 1284982, 369934, 2573, 65536⟩ := by
  decide +kernel

theorem context_12_369934_1284982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369934 ⟨1284982, by decide⟩ :=
  accepted_of_selected 12 369934 ⟨1284982, by decide⟩ ⟨12, 2, 0, 1284982, 369934, 2573, 65536⟩
    (by decide) selected_cut_46138

theorem selected_cut_46139 : selected 9 ⟨1285052, by decide⟩
    (prefixPartial 12 369935) = some ⟨12, 2, 0, 1285052, 369935, 3229, 65536⟩ := by
  decide +kernel

theorem context_12_369935_1285052 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369935 ⟨1285052, by decide⟩ :=
  accepted_of_selected 12 369935 ⟨1285052, by decide⟩ ⟨12, 2, 0, 1285052, 369935, 3229, 65536⟩
    (by decide) selected_cut_46139

theorem unmarked_context_11_92483_1285053 : frontier 10 ⟨1285053, by decide⟩
    (prefixCache 11 92483) (prefixPartial 11 92483) = false := by
  decide +kernel

theorem node_context_11_92483_1285053 : EJMOriginalGlobalDAGData.nodes 10 ⟨1285053, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1284928, by decide⟩,⟨1284982, by decide⟩,⟨1285052, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92483_1285053 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92483 ⟨1285053, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92483
    ⟨1285053, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1284928, by decide⟩,⟨1284982, by decide⟩,⟨1285052, by decide⟩]) unmarked_context_11_92483_1285053 node_context_11_92483_1285053
  intro a
  fin_cases a
  · exact context_12_369932_448748
  · exact context_12_369933_1284928
  · exact context_12_369934_1284982
  · exact context_12_369935_1285052

theorem unmarked_context_10_23120_1285054 : frontier 11 ⟨1285054, by decide⟩
    (prefixCache 10 23120) (prefixPartial 10 23120) = false := by
  decide +kernel

theorem node_context_10_23120_1285054 : EJMOriginalGlobalDAGData.nodes 11 ⟨1285054, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨167448, by decide⟩,⟨1284885, by decide⟩,⟨1285053, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23120_1285054 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23120 ⟨1285054, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23120
    ⟨1285054, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨167448, by decide⟩,⟨1284885, by decide⟩,⟨1285053, by decide⟩]) unmarked_context_10_23120_1285054 node_context_10_23120_1285054
  intro a
  fin_cases a
  · exact context_11_92480_434745
  · exact context_11_92481_167448
  · exact context_11_92482_1284885
  · exact context_11_92483_1285053

theorem selected_cut_46140 : selected 9 ⟨815337, by decide⟩
    (prefixPartial 12 369936) = some ⟨12, 1, 0, 815337, 369936, 1, 65536⟩ := by
  decide +kernel

theorem context_12_369936_815337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369936 ⟨815337, by decide⟩ :=
  accepted_of_selected 12 369936 ⟨815337, by decide⟩ ⟨12, 1, 0, 815337, 369936, 1, 65536⟩
    (by decide) selected_cut_46140

theorem selected_cut_46141 : selected 9 ⟨1285102, by decide⟩
    (prefixPartial 12 369937) = some ⟨12, 2, 0, 1285102, 369937, 2277, 65536⟩ := by
  decide +kernel

theorem context_12_369937_1285102 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369937 ⟨1285102, by decide⟩ :=
  accepted_of_selected 12 369937 ⟨1285102, by decide⟩ ⟨12, 2, 0, 1285102, 369937, 2277, 65536⟩
    (by decide) selected_cut_46141

theorem selected_cut_46142 : selected 9 ⟨1285143, by decide⟩
    (prefixPartial 12 369938) = some ⟨12, 2, 0, 1285143, 369938, 2309, 65536⟩ := by
  decide +kernel

theorem context_12_369938_1285143 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369938 ⟨1285143, by decide⟩ :=
  accepted_of_selected 12 369938 ⟨1285143, by decide⟩ ⟨12, 2, 0, 1285143, 369938, 2309, 65536⟩
    (by decide) selected_cut_46142

theorem selected_cut_46143 : selected 9 ⟨1285204, by decide⟩
    (prefixPartial 12 369939) = some ⟨12, 2, 0, 1285204, 369939, 2805, 65536⟩ := by
  decide +kernel

theorem context_12_369939_1285204 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369939 ⟨1285204, by decide⟩ :=
  accepted_of_selected 12 369939 ⟨1285204, by decide⟩ ⟨12, 2, 0, 1285204, 369939, 2805, 65536⟩
    (by decide) selected_cut_46143

theorem unmarked_context_11_92484_1285205 : frontier 10 ⟨1285205, by decide⟩
    (prefixCache 11 92484) (prefixPartial 11 92484) = false := by
  decide +kernel

theorem node_context_11_92484_1285205 : EJMOriginalGlobalDAGData.nodes 10 ⟨1285205, by decide⟩ =
    .split (coordinate 11) (![⟨815337, by decide⟩,⟨1285102, by decide⟩,⟨1285143, by decide⟩,⟨1285204, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92484_1285205 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92484 ⟨1285205, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92484
    ⟨1285205, by decide⟩ (by decide) (![⟨815337, by decide⟩,⟨1285102, by decide⟩,⟨1285143, by decide⟩,⟨1285204, by decide⟩]) unmarked_context_11_92484_1285205 node_context_11_92484_1285205
  intro a
  fin_cases a
  · exact context_12_369936_815337
  · exact context_12_369937_1285102
  · exact context_12_369938_1285143
  · exact context_12_369939_1285204

theorem selected_cut_46144 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 92485) = some ⟨11, 1, 0, 892405, 92485, 1, 262144⟩ := by
  decide +kernel

theorem context_11_92485_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92485 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 92485 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 92485, 1, 262144⟩
    (by decide) selected_cut_46144

theorem selected_cut_46145 : selected 9 ⟨1285257, by decide⟩
    (prefixPartial 12 369944) = some ⟨12, 2, 0, 1285257, 369944, 2449, 65536⟩ := by
  decide +kernel

theorem context_12_369944_1285257 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369944 ⟨1285257, by decide⟩ :=
  accepted_of_selected 12 369944 ⟨1285257, by decide⟩ ⟨12, 2, 0, 1285257, 369944, 2449, 65536⟩
    (by decide) selected_cut_46145

theorem selected_cut_46146 : selected 9 ⟨1285292, by decide⟩
    (prefixPartial 12 369945) = some ⟨12, 2, 0, 1285292, 369945, 2009, 65536⟩ := by
  decide +kernel

theorem context_12_369945_1285292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369945 ⟨1285292, by decide⟩ :=
  accepted_of_selected 12 369945 ⟨1285292, by decide⟩ ⟨12, 2, 0, 1285292, 369945, 2009, 65536⟩
    (by decide) selected_cut_46146

theorem selected_cut_46147 : selected 9 ⟨660636, by decide⟩
    (prefixPartial 12 369946) = some ⟨12, 1, 0, 660636, 369946, 1, 65536⟩ := by
  decide +kernel

theorem context_12_369946_660636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369946 ⟨660636, by decide⟩ :=
  accepted_of_selected 12 369946 ⟨660636, by decide⟩ ⟨12, 1, 0, 660636, 369946, 1, 65536⟩
    (by decide) selected_cut_46147

theorem selected_cut_46148 : selected 9 ⟨1285351, by decide⟩
    (prefixPartial 12 369947) = some ⟨12, 2, 0, 1285351, 369947, 2665, 65536⟩ := by
  decide +kernel

theorem context_12_369947_1285351 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369947 ⟨1285351, by decide⟩ :=
  accepted_of_selected 12 369947 ⟨1285351, by decide⟩ ⟨12, 2, 0, 1285351, 369947, 2665, 65536⟩
    (by decide) selected_cut_46148

theorem unmarked_context_11_92486_1285352 : frontier 10 ⟨1285352, by decide⟩
    (prefixCache 11 92486) (prefixPartial 11 92486) = false := by
  decide +kernel

theorem node_context_11_92486_1285352 : EJMOriginalGlobalDAGData.nodes 10 ⟨1285352, by decide⟩ =
    .split (coordinate 11) (![⟨1285257, by decide⟩,⟨1285292, by decide⟩,⟨660636, by decide⟩,⟨1285351, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92486_1285352 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92486 ⟨1285352, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92486
    ⟨1285352, by decide⟩ (by decide) (![⟨1285257, by decide⟩,⟨1285292, by decide⟩,⟨660636, by decide⟩,⟨1285351, by decide⟩]) unmarked_context_11_92486_1285352 node_context_11_92486_1285352
  intro a
  fin_cases a
  · exact context_12_369944_1285257
  · exact context_12_369945_1285292
  · exact context_12_369946_660636
  · exact context_12_369947_1285351

theorem selected_cut_46149 : selected 9 ⟨1285402, by decide⟩
    (prefixPartial 12 369948) = some ⟨12, 2, 0, 1285402, 369948, 2617, 65536⟩ := by
  decide +kernel

theorem context_12_369948_1285402 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369948 ⟨1285402, by decide⟩ :=
  accepted_of_selected 12 369948 ⟨1285402, by decide⟩ ⟨12, 2, 0, 1285402, 369948, 2617, 65536⟩
    (by decide) selected_cut_46149

theorem selected_cut_46150 : selected 9 ⟨1285439, by decide⟩
    (prefixPartial 12 369949) = some ⟨12, 2, 0, 1285439, 369949, 2093, 65536⟩ := by
  decide +kernel

theorem context_12_369949_1285439 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369949 ⟨1285439, by decide⟩ :=
  accepted_of_selected 12 369949 ⟨1285439, by decide⟩ ⟨12, 2, 0, 1285439, 369949, 2093, 65536⟩
    (by decide) selected_cut_46150

theorem selected_cut_46151 : selected 9 ⟨1285488, by decide⟩
    (prefixPartial 12 369950) = some ⟨12, 2, 0, 1285488, 369950, 2341, 65536⟩ := by
  decide +kernel

theorem context_12_369950_1285488 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369950 ⟨1285488, by decide⟩ :=
  accepted_of_selected 12 369950 ⟨1285488, by decide⟩ ⟨12, 2, 0, 1285488, 369950, 2341, 65536⟩
    (by decide) selected_cut_46151

theorem selected_cut_46152 : selected 9 ⟨757807, by decide⟩
    (prefixPartial 12 369951) = some ⟨12, 1, 0, 757807, 369951, 1, 65536⟩ := by
  decide +kernel

theorem context_12_369951_757807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369951 ⟨757807, by decide⟩ :=
  accepted_of_selected 12 369951 ⟨757807, by decide⟩ ⟨12, 1, 0, 757807, 369951, 1, 65536⟩
    (by decide) selected_cut_46152

theorem unmarked_context_11_92487_1285489 : frontier 10 ⟨1285489, by decide⟩
    (prefixCache 11 92487) (prefixPartial 11 92487) = false := by
  decide +kernel

theorem node_context_11_92487_1285489 : EJMOriginalGlobalDAGData.nodes 10 ⟨1285489, by decide⟩ =
    .split (coordinate 11) (![⟨1285402, by decide⟩,⟨1285439, by decide⟩,⟨1285488, by decide⟩,⟨757807, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92487_1285489 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92487 ⟨1285489, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92487
    ⟨1285489, by decide⟩ (by decide) (![⟨1285402, by decide⟩,⟨1285439, by decide⟩,⟨1285488, by decide⟩,⟨757807, by decide⟩]) unmarked_context_11_92487_1285489 node_context_11_92487_1285489
  intro a
  fin_cases a
  · exact context_12_369948_1285402
  · exact context_12_369949_1285439
  · exact context_12_369950_1285488
  · exact context_12_369951_757807

theorem unmarked_context_10_23121_1285490 : frontier 11 ⟨1285490, by decide⟩
    (prefixCache 10 23121) (prefixPartial 10 23121) = false := by
  decide +kernel

theorem node_context_10_23121_1285490 : EJMOriginalGlobalDAGData.nodes 11 ⟨1285490, by decide⟩ =
    .split (coordinate 10) (![⟨1285205, by decide⟩,⟨892405, by decide⟩,⟨1285352, by decide⟩,⟨1285489, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23121_1285490 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23121 ⟨1285490, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23121
    ⟨1285490, by decide⟩ (by decide) (![⟨1285205, by decide⟩,⟨892405, by decide⟩,⟨1285352, by decide⟩,⟨1285489, by decide⟩]) unmarked_context_10_23121_1285490 node_context_10_23121_1285490
  intro a
  fin_cases a
  · exact context_11_92484_1285205
  · exact context_11_92485_892405
  · exact context_11_92486_1285352
  · exact context_11_92487_1285489

theorem selected_cut_46153 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 369952) = some ⟨12, 1, 0, 435790, 369952, 1, 65536⟩ := by
  decide +kernel

theorem context_12_369952_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369952 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 369952 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 369952, 1, 65536⟩
    (by decide) selected_cut_46153

theorem selected_cut_46154 : selected 9 ⟨1285534, by decide⟩
    (prefixPartial 12 369953) = some ⟨12, 2, 0, 1285534, 369953, 2381, 65536⟩ := by
  decide +kernel

theorem context_12_369953_1285534 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369953 ⟨1285534, by decide⟩ :=
  accepted_of_selected 12 369953 ⟨1285534, by decide⟩ ⟨12, 2, 0, 1285534, 369953, 2381, 65536⟩
    (by decide) selected_cut_46154

theorem selected_cut_46155 : selected 9 ⟨1285578, by decide⟩
    (prefixPartial 12 369954) = some ⟨12, 2, 0, 1285578, 369954, 2289, 65536⟩ := by
  decide +kernel

theorem context_12_369954_1285578 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369954 ⟨1285578, by decide⟩ :=
  accepted_of_selected 12 369954 ⟨1285578, by decide⟩ ⟨12, 2, 0, 1285578, 369954, 2289, 65536⟩
    (by decide) selected_cut_46155

theorem selected_cut_46156 : selected 9 ⟨1285631, by decide⟩
    (prefixPartial 12 369955) = some ⟨12, 2, 0, 1285631, 369955, 2789, 65536⟩ := by
  decide +kernel

theorem context_12_369955_1285631 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369955 ⟨1285631, by decide⟩ :=
  accepted_of_selected 12 369955 ⟨1285631, by decide⟩ ⟨12, 2, 0, 1285631, 369955, 2789, 65536⟩
    (by decide) selected_cut_46156

theorem unmarked_context_11_92488_1285632 : frontier 10 ⟨1285632, by decide⟩
    (prefixCache 11 92488) (prefixPartial 11 92488) = false := by
  decide +kernel

theorem node_context_11_92488_1285632 : EJMOriginalGlobalDAGData.nodes 10 ⟨1285632, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨1285534, by decide⟩,⟨1285578, by decide⟩,⟨1285631, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92488_1285632 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92488 ⟨1285632, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92488
    ⟨1285632, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨1285534, by decide⟩,⟨1285578, by decide⟩,⟨1285631, by decide⟩]) unmarked_context_11_92488_1285632 node_context_11_92488_1285632
  intro a
  fin_cases a
  · exact context_12_369952_435790
  · exact context_12_369953_1285534
  · exact context_12_369954_1285578
  · exact context_12_369955_1285631

theorem selected_cut_46157 : selected 9 ⟨1285696, by decide⟩
    (prefixPartial 12 369956) = some ⟨12, 2, 0, 1285696, 369956, 2885, 65536⟩ := by
  decide +kernel

theorem context_12_369956_1285696 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369956 ⟨1285696, by decide⟩ :=
  accepted_of_selected 12 369956 ⟨1285696, by decide⟩ ⟨12, 2, 0, 1285696, 369956, 2885, 65536⟩
    (by decide) selected_cut_46157

theorem selected_cut_46158 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 369957) = some ⟨12, 1, 0, 891951, 369957, 1, 65536⟩ := by
  decide +kernel

theorem context_12_369957_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369957 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 369957 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 369957, 1, 65536⟩
    (by decide) selected_cut_46158

theorem selected_cut_46159 : selected 9 ⟨1285738, by decide⟩
    (prefixPartial 12 369958) = some ⟨12, 2, 0, 1285738, 369958, 2149, 65536⟩ := by
  decide +kernel

theorem context_12_369958_1285738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369958 ⟨1285738, by decide⟩ :=
  accepted_of_selected 12 369958 ⟨1285738, by decide⟩ ⟨12, 2, 0, 1285738, 369958, 2149, 65536⟩
    (by decide) selected_cut_46159

theorem selected_cut_46160 : selected 9 ⟨1285792, by decide⟩
    (prefixPartial 12 369959) = some ⟨12, 2, 0, 1285792, 369959, 2673, 65536⟩ := by
  decide +kernel

theorem context_12_369959_1285792 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369959 ⟨1285792, by decide⟩ :=
  accepted_of_selected 12 369959 ⟨1285792, by decide⟩ ⟨12, 2, 0, 1285792, 369959, 2673, 65536⟩
    (by decide) selected_cut_46160

theorem unmarked_context_11_92489_1285793 : frontier 10 ⟨1285793, by decide⟩
    (prefixCache 11 92489) (prefixPartial 11 92489) = false := by
  decide +kernel

theorem node_context_11_92489_1285793 : EJMOriginalGlobalDAGData.nodes 10 ⟨1285793, by decide⟩ =
    .split (coordinate 11) (![⟨1285696, by decide⟩,⟨891951, by decide⟩,⟨1285738, by decide⟩,⟨1285792, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92489_1285793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92489 ⟨1285793, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92489
    ⟨1285793, by decide⟩ (by decide) (![⟨1285696, by decide⟩,⟨891951, by decide⟩,⟨1285738, by decide⟩,⟨1285792, by decide⟩]) unmarked_context_11_92489_1285793 node_context_11_92489_1285793
  intro a
  fin_cases a
  · exact context_12_369956_1285696
  · exact context_12_369957_891951
  · exact context_12_369958_1285738
  · exact context_12_369959_1285792

theorem selected_cut_46161 : selected 10 ⟨1285837, by decide⟩
    (prefixPartial 11 92490) = some ⟨11, 2, 0, 1285837, 92490, 2525, 262144⟩ := by
  decide +kernel

theorem context_11_92490_1285837 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92490 ⟨1285837, by decide⟩ :=
  accepted_of_selected 11 92490 ⟨1285837, by decide⟩ ⟨11, 2, 0, 1285837, 92490, 2525, 262144⟩
    (by decide) selected_cut_46161

theorem selected_cut_46162 : selected 9 ⟨1285885, by decide⟩
    (prefixPartial 12 369964) = some ⟨12, 2, 0, 1285885, 369964, 2641, 65536⟩ := by
  decide +kernel

theorem context_12_369964_1285885 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369964 ⟨1285885, by decide⟩ :=
  accepted_of_selected 12 369964 ⟨1285885, by decide⟩ ⟨12, 2, 0, 1285885, 369964, 2641, 65536⟩
    (by decide) selected_cut_46162

theorem selected_cut_46163 : selected 9 ⟨1285932, by decide⟩
    (prefixPartial 12 369965) = some ⟨12, 2, 0, 1285932, 369965, 2241, 65536⟩ := by
  decide +kernel

theorem context_12_369965_1285932 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369965 ⟨1285932, by decide⟩ :=
  accepted_of_selected 12 369965 ⟨1285932, by decide⟩ ⟨12, 2, 0, 1285932, 369965, 2241, 65536⟩
    (by decide) selected_cut_46163

theorem selected_cut_46164 : selected 9 ⟨1285970, by decide⟩
    (prefixPartial 12 369966) = some ⟨12, 2, 0, 1285970, 369966, 2193, 65536⟩ := by
  decide +kernel

theorem context_12_369966_1285970 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369966 ⟨1285970, by decide⟩ :=
  accepted_of_selected 12 369966 ⟨1285970, by decide⟩ ⟨12, 2, 0, 1285970, 369966, 2193, 65536⟩
    (by decide) selected_cut_46164

theorem selected_cut_46165 : selected 9 ⟨1286028, by decide⟩
    (prefixPartial 12 369967) = some ⟨12, 2, 0, 1286028, 369967, 2817, 65536⟩ := by
  decide +kernel

theorem context_12_369967_1286028 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369967 ⟨1286028, by decide⟩ :=
  accepted_of_selected 12 369967 ⟨1286028, by decide⟩ ⟨12, 2, 0, 1286028, 369967, 2817, 65536⟩
    (by decide) selected_cut_46165

theorem unmarked_context_11_92491_1286029 : frontier 10 ⟨1286029, by decide⟩
    (prefixCache 11 92491) (prefixPartial 11 92491) = false := by
  decide +kernel

theorem node_context_11_92491_1286029 : EJMOriginalGlobalDAGData.nodes 10 ⟨1286029, by decide⟩ =
    .split (coordinate 11) (![⟨1285885, by decide⟩,⟨1285932, by decide⟩,⟨1285970, by decide⟩,⟨1286028, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92491_1286029 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92491 ⟨1286029, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92491
    ⟨1286029, by decide⟩ (by decide) (![⟨1285885, by decide⟩,⟨1285932, by decide⟩,⟨1285970, by decide⟩,⟨1286028, by decide⟩]) unmarked_context_11_92491_1286029 node_context_11_92491_1286029
  intro a
  fin_cases a
  · exact context_12_369964_1285885
  · exact context_12_369965_1285932
  · exact context_12_369966_1285970
  · exact context_12_369967_1286028

theorem unmarked_context_10_23122_1286030 : frontier 11 ⟨1286030, by decide⟩
    (prefixCache 10 23122) (prefixPartial 10 23122) = false := by
  decide +kernel

theorem node_context_10_23122_1286030 : EJMOriginalGlobalDAGData.nodes 11 ⟨1286030, by decide⟩ =
    .split (coordinate 10) (![⟨1285632, by decide⟩,⟨1285793, by decide⟩,⟨1285837, by decide⟩,⟨1286029, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23122_1286030 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23122 ⟨1286030, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23122
    ⟨1286030, by decide⟩ (by decide) (![⟨1285632, by decide⟩,⟨1285793, by decide⟩,⟨1285837, by decide⟩,⟨1286029, by decide⟩]) unmarked_context_10_23122_1286030 node_context_10_23122_1286030
  intro a
  fin_cases a
  · exact context_11_92488_1285632
  · exact context_11_92489_1285793
  · exact context_11_92490_1285837
  · exact context_11_92491_1286029

theorem selected_cut_46166 : selected 9 ⟨1255011, by decide⟩
    (prefixPartial 12 369968) = some ⟨12, 1, 0, 1255011, 369968, 1, 65536⟩ := by
  decide +kernel

theorem context_12_369968_1255011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369968 ⟨1255011, by decide⟩ :=
  accepted_of_selected 12 369968 ⟨1255011, by decide⟩ ⟨12, 1, 0, 1255011, 369968, 1, 65536⟩
    (by decide) selected_cut_46166

theorem selected_cut_46167 : selected 9 ⟨1286063, by decide⟩
    (prefixPartial 12 369969) = some ⟨12, 2, 0, 1286063, 369969, 1973, 65536⟩ := by
  decide +kernel

theorem context_12_369969_1286063 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369969 ⟨1286063, by decide⟩ :=
  accepted_of_selected 12 369969 ⟨1286063, by decide⟩ ⟨12, 2, 0, 1286063, 369969, 1973, 65536⟩
    (by decide) selected_cut_46167

theorem selected_cut_46168 : selected 9 ⟨1286099, by decide⟩
    (prefixPartial 12 369970) = some ⟨12, 2, 0, 1286099, 369970, 1925, 65536⟩ := by
  decide +kernel

theorem context_12_369970_1286099 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369970 ⟨1286099, by decide⟩ :=
  accepted_of_selected 12 369970 ⟨1286099, by decide⟩ ⟨12, 2, 0, 1286099, 369970, 1925, 65536⟩
    (by decide) selected_cut_46168

theorem selected_cut_46169 : selected 9 ⟨1286145, by decide⟩
    (prefixPartial 12 369971) = some ⟨12, 2, 0, 1286145, 369971, 2393, 65536⟩ := by
  decide +kernel

theorem context_12_369971_1286145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369971 ⟨1286145, by decide⟩ :=
  accepted_of_selected 12 369971 ⟨1286145, by decide⟩ ⟨12, 2, 0, 1286145, 369971, 2393, 65536⟩
    (by decide) selected_cut_46169

theorem unmarked_context_11_92492_1286146 : frontier 10 ⟨1286146, by decide⟩
    (prefixCache 11 92492) (prefixPartial 11 92492) = false := by
  decide +kernel

theorem node_context_11_92492_1286146 : EJMOriginalGlobalDAGData.nodes 10 ⟨1286146, by decide⟩ =
    .split (coordinate 11) (![⟨1255011, by decide⟩,⟨1286063, by decide⟩,⟨1286099, by decide⟩,⟨1286145, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92492_1286146 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92492 ⟨1286146, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92492
    ⟨1286146, by decide⟩ (by decide) (![⟨1255011, by decide⟩,⟨1286063, by decide⟩,⟨1286099, by decide⟩,⟨1286145, by decide⟩]) unmarked_context_11_92492_1286146 node_context_11_92492_1286146
  intro a
  fin_cases a
  · exact context_12_369968_1255011
  · exact context_12_369969_1286063
  · exact context_12_369970_1286099
  · exact context_12_369971_1286145

theorem selected_cut_46170 : selected 9 ⟨1286190, by decide⟩
    (prefixPartial 12 369972) = some ⟨12, 2, 0, 1286190, 369972, 2229, 65536⟩ := by
  decide +kernel

theorem context_12_369972_1286190 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369972 ⟨1286190, by decide⟩ :=
  accepted_of_selected 12 369972 ⟨1286190, by decide⟩ ⟨12, 2, 0, 1286190, 369972, 2229, 65536⟩
    (by decide) selected_cut_46170

theorem selected_cut_46171 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 369973) = some ⟨12, 1, 0, 891951, 369973, 1, 65536⟩ := by
  decide +kernel

theorem context_12_369973_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369973 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 369973 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 369973, 1, 65536⟩
    (by decide) selected_cut_46171

theorem selected_cut_46172 : selected 9 ⟨1286226, by decide⟩
    (prefixPartial 12 369974) = some ⟨12, 2, 0, 1286226, 369974, 1809, 65536⟩ := by
  decide +kernel

theorem context_12_369974_1286226 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369974 ⟨1286226, by decide⟩ :=
  accepted_of_selected 12 369974 ⟨1286226, by decide⟩ ⟨12, 2, 0, 1286226, 369974, 1809, 65536⟩
    (by decide) selected_cut_46172

theorem selected_cut_46173 : selected 9 ⟨1286267, by decide⟩
    (prefixPartial 12 369975) = some ⟨12, 2, 0, 1286267, 369975, 1993, 65536⟩ := by
  decide +kernel

theorem context_12_369975_1286267 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369975 ⟨1286267, by decide⟩ :=
  accepted_of_selected 12 369975 ⟨1286267, by decide⟩ ⟨12, 2, 0, 1286267, 369975, 1993, 65536⟩
    (by decide) selected_cut_46173

theorem unmarked_context_11_92493_1286268 : frontier 10 ⟨1286268, by decide⟩
    (prefixCache 11 92493) (prefixPartial 11 92493) = false := by
  decide +kernel

theorem node_context_11_92493_1286268 : EJMOriginalGlobalDAGData.nodes 10 ⟨1286268, by decide⟩ =
    .split (coordinate 11) (![⟨1286190, by decide⟩,⟨891951, by decide⟩,⟨1286226, by decide⟩,⟨1286267, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92493_1286268 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92493 ⟨1286268, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92493
    ⟨1286268, by decide⟩ (by decide) (![⟨1286190, by decide⟩,⟨891951, by decide⟩,⟨1286226, by decide⟩,⟨1286267, by decide⟩]) unmarked_context_11_92493_1286268 node_context_11_92493_1286268
  intro a
  fin_cases a
  · exact context_12_369972_1286190
  · exact context_12_369973_891951
  · exact context_12_369974_1286226
  · exact context_12_369975_1286267

theorem selected_cut_46174 : selected 9 ⟨1286305, by decide⟩
    (prefixPartial 12 369976) = some ⟨12, 2, 0, 1286305, 369976, 1965, 65536⟩ := by
  decide +kernel

theorem context_12_369976_1286305 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369976 ⟨1286305, by decide⟩ :=
  accepted_of_selected 12 369976 ⟨1286305, by decide⟩ ⟨12, 2, 0, 1286305, 369976, 1965, 65536⟩
    (by decide) selected_cut_46174

theorem selected_cut_46175 : selected 9 ⟨1286334, by decide⟩
    (prefixPartial 12 369977) = some ⟨12, 2, 0, 1286334, 369977, 1657, 65536⟩ := by
  decide +kernel

theorem context_12_369977_1286334 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369977 ⟨1286334, by decide⟩ :=
  accepted_of_selected 12 369977 ⟨1286334, by decide⟩ ⟨12, 2, 0, 1286334, 369977, 1657, 65536⟩
    (by decide) selected_cut_46175

theorem selected_cut_46176 : selected 9 ⟨1286365, by decide⟩
    (prefixPartial 12 369978) = some ⟨12, 2, 0, 1286365, 369978, 1673, 65536⟩ := by
  decide +kernel

theorem context_12_369978_1286365 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369978 ⟨1286365, by decide⟩ :=
  accepted_of_selected 12 369978 ⟨1286365, by decide⟩ ⟨12, 2, 0, 1286365, 369978, 1673, 65536⟩
    (by decide) selected_cut_46176

theorem selected_cut_46177 : selected 9 ⟨1286406, by decide⟩
    (prefixPartial 12 369979) = some ⟨12, 2, 0, 1286406, 369979, 1913, 65536⟩ := by
  decide +kernel

theorem context_12_369979_1286406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 369979 ⟨1286406, by decide⟩ :=
  accepted_of_selected 12 369979 ⟨1286406, by decide⟩ ⟨12, 2, 0, 1286406, 369979, 1913, 65536⟩
    (by decide) selected_cut_46177

theorem unmarked_context_11_92494_1286407 : frontier 10 ⟨1286407, by decide⟩
    (prefixCache 11 92494) (prefixPartial 11 92494) = false := by
  decide +kernel

theorem node_context_11_92494_1286407 : EJMOriginalGlobalDAGData.nodes 10 ⟨1286407, by decide⟩ =
    .split (coordinate 11) (![⟨1286305, by decide⟩,⟨1286334, by decide⟩,⟨1286365, by decide⟩,⟨1286406, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92494_1286407 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92494 ⟨1286407, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92494
    ⟨1286407, by decide⟩ (by decide) (![⟨1286305, by decide⟩,⟨1286334, by decide⟩,⟨1286365, by decide⟩,⟨1286406, by decide⟩]) unmarked_context_11_92494_1286407 node_context_11_92494_1286407
  intro a
  fin_cases a
  · exact context_12_369976_1286305
  · exact context_12_369977_1286334
  · exact context_12_369978_1286365
  · exact context_12_369979_1286406

theorem selected_cut_46178 : selected 10 ⟨1286472, by decide⟩
    (prefixPartial 11 92495) = some ⟨11, 2, 0, 1286472, 92495, 3509, 262144⟩ := by
  decide +kernel

theorem context_11_92495_1286472 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92495 ⟨1286472, by decide⟩ :=
  accepted_of_selected 11 92495 ⟨1286472, by decide⟩ ⟨11, 2, 0, 1286472, 92495, 3509, 262144⟩
    (by decide) selected_cut_46178

theorem unmarked_context_10_23123_1286473 : frontier 11 ⟨1286473, by decide⟩
    (prefixCache 10 23123) (prefixPartial 10 23123) = false := by
  decide +kernel

theorem node_context_10_23123_1286473 : EJMOriginalGlobalDAGData.nodes 11 ⟨1286473, by decide⟩ =
    .split (coordinate 10) (![⟨1286146, by decide⟩,⟨1286268, by decide⟩,⟨1286407, by decide⟩,⟨1286472, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23123_1286473 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23123 ⟨1286473, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23123
    ⟨1286473, by decide⟩ (by decide) (![⟨1286146, by decide⟩,⟨1286268, by decide⟩,⟨1286407, by decide⟩,⟨1286472, by decide⟩]) unmarked_context_10_23123_1286473 node_context_10_23123_1286473
  intro a
  fin_cases a
  · exact context_11_92492_1286146
  · exact context_11_92493_1286268
  · exact context_11_92494_1286407
  · exact context_11_92495_1286472

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
