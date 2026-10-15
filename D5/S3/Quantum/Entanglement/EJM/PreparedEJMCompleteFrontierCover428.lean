/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover427
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_41090 : selected 9 ⟨1121797, by decide⟩
    (prefixPartial 12 333956) = some ⟨12, 2, 0, 1121797, 333956, 1201, 65536⟩ := by
  decide +kernel

theorem context_12_333956_1121797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333956 ⟨1121797, by decide⟩ :=
  accepted_of_selected 12 333956 ⟨1121797, by decide⟩ ⟨12, 2, 0, 1121797, 333956, 1201, 65536⟩
    (by decide) selected_cut_41090

theorem selected_cut_41091 : selected 9 ⟨1121832, by decide⟩
    (prefixPartial 12 333957) = some ⟨12, 2, 0, 1121832, 333957, 1589, 65536⟩ := by
  decide +kernel

theorem context_12_333957_1121832 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333957 ⟨1121832, by decide⟩ :=
  accepted_of_selected 12 333957 ⟨1121832, by decide⟩ ⟨12, 2, 0, 1121832, 333957, 1589, 65536⟩
    (by decide) selected_cut_41091

theorem selected_cut_41092 : selected 9 ⟨1121852, by decide⟩
    (prefixPartial 12 333958) = some ⟨12, 2, 0, 1121852, 333958, 1393, 65536⟩ := by
  decide +kernel

theorem context_12_333958_1121852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333958 ⟨1121852, by decide⟩ :=
  accepted_of_selected 12 333958 ⟨1121852, by decide⟩ ⟨12, 2, 0, 1121852, 333958, 1393, 65536⟩
    (by decide) selected_cut_41092

theorem selected_cut_41093 : selected 9 ⟨1121871, by decide⟩
    (prefixPartial 12 333959) = some ⟨12, 2, 0, 1121871, 333959, 1409, 65536⟩ := by
  decide +kernel

theorem context_12_333959_1121871 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333959 ⟨1121871, by decide⟩ :=
  accepted_of_selected 12 333959 ⟨1121871, by decide⟩ ⟨12, 2, 0, 1121871, 333959, 1409, 65536⟩
    (by decide) selected_cut_41093

theorem unmarked_context_11_83489_1121872 : frontier 10 ⟨1121872, by decide⟩
    (prefixCache 11 83489) (prefixPartial 11 83489) = false := by
  decide +kernel

theorem node_context_11_83489_1121872 : EJMOriginalGlobalDAGData.nodes 10 ⟨1121872, by decide⟩ =
    .split (coordinate 11) (![⟨1121797, by decide⟩,⟨1121832, by decide⟩,⟨1121852, by decide⟩,⟨1121871, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83489_1121872 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83489 ⟨1121872, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83489
    ⟨1121872, by decide⟩ (by decide) (![⟨1121797, by decide⟩,⟨1121832, by decide⟩,⟨1121852, by decide⟩,⟨1121871, by decide⟩]) unmarked_context_11_83489_1121872 node_context_11_83489_1121872
  intro a
  fin_cases a
  · exact context_12_333956_1121797
  · exact context_12_333957_1121832
  · exact context_12_333958_1121852
  · exact context_12_333959_1121871

theorem selected_cut_41094 : selected 10 ⟨1121931, by decide⟩
    (prefixPartial 11 83490) = some ⟨11, 2, 0, 1121931, 83490, 3621, 262144⟩ := by
  decide +kernel

theorem context_11_83490_1121931 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83490 ⟨1121931, by decide⟩ :=
  accepted_of_selected 11 83490 ⟨1121931, by decide⟩ ⟨11, 2, 0, 1121931, 83490, 3621, 262144⟩
    (by decide) selected_cut_41094

theorem selected_cut_41095 : selected 9 ⟨1121948, by decide⟩
    (prefixPartial 12 333964) = some ⟨12, 2, 0, 1121948, 333964, 1041, 65536⟩ := by
  decide +kernel

theorem context_12_333964_1121948 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333964 ⟨1121948, by decide⟩ :=
  accepted_of_selected 12 333964 ⟨1121948, by decide⟩ ⟨12, 2, 0, 1121948, 333964, 1041, 65536⟩
    (by decide) selected_cut_41095

theorem selected_cut_41096 : selected 9 ⟨1121962, by decide⟩
    (prefixPartial 12 333965) = some ⟨12, 2, 0, 1121962, 333965, 1233, 65536⟩ := by
  decide +kernel

theorem context_12_333965_1121962 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333965 ⟨1121962, by decide⟩ :=
  accepted_of_selected 12 333965 ⟨1121962, by decide⟩ ⟨12, 2, 0, 1121962, 333965, 1233, 65536⟩
    (by decide) selected_cut_41096

theorem selected_cut_41097 : selected 9 ⟨1121982, by decide⟩
    (prefixPartial 12 333966) = some ⟨12, 2, 0, 1121982, 333966, 1305, 65536⟩ := by
  decide +kernel

theorem context_12_333966_1121982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333966 ⟨1121982, by decide⟩ :=
  accepted_of_selected 12 333966 ⟨1121982, by decide⟩ ⟨12, 2, 0, 1121982, 333966, 1305, 65536⟩
    (by decide) selected_cut_41097

theorem selected_cut_41098 : selected 9 ⟨1121992, by decide⟩
    (prefixPartial 12 333967) = some ⟨12, 2, 0, 1121992, 333967, 1165, 65536⟩ := by
  decide +kernel

theorem context_12_333967_1121992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 333967 ⟨1121992, by decide⟩ :=
  accepted_of_selected 12 333967 ⟨1121992, by decide⟩ ⟨12, 2, 0, 1121992, 333967, 1165, 65536⟩
    (by decide) selected_cut_41098

theorem unmarked_context_11_83491_1121993 : frontier 10 ⟨1121993, by decide⟩
    (prefixCache 11 83491) (prefixPartial 11 83491) = false := by
  decide +kernel

theorem node_context_11_83491_1121993 : EJMOriginalGlobalDAGData.nodes 10 ⟨1121993, by decide⟩ =
    .split (coordinate 11) (![⟨1121948, by decide⟩,⟨1121962, by decide⟩,⟨1121982, by decide⟩,⟨1121992, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83491_1121993 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83491 ⟨1121993, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83491
    ⟨1121993, by decide⟩ (by decide) (![⟨1121948, by decide⟩,⟨1121962, by decide⟩,⟨1121982, by decide⟩,⟨1121992, by decide⟩]) unmarked_context_11_83491_1121993 node_context_11_83491_1121993
  intro a
  fin_cases a
  · exact context_12_333964_1121948
  · exact context_12_333965_1121962
  · exact context_12_333966_1121982
  · exact context_12_333967_1121992

theorem unmarked_context_10_20872_1121994 : frontier 11 ⟨1121994, by decide⟩
    (prefixCache 10 20872) (prefixPartial 10 20872) = false := by
  decide +kernel

theorem node_context_10_20872_1121994 : EJMOriginalGlobalDAGData.nodes 11 ⟨1121994, by decide⟩ =
    .split (coordinate 10) (![⟨1121776, by decide⟩,⟨1121872, by decide⟩,⟨1121931, by decide⟩,⟨1121993, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_20872_1121994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20872 ⟨1121994, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 20872
    ⟨1121994, by decide⟩ (by decide) (![⟨1121776, by decide⟩,⟨1121872, by decide⟩,⟨1121931, by decide⟩,⟨1121993, by decide⟩]) unmarked_context_10_20872_1121994 node_context_10_20872_1121994
  intro a
  fin_cases a
  · exact context_11_83488_1121776
  · exact context_11_83489_1121872
  · exact context_11_83490_1121931
  · exact context_11_83491_1121993

theorem selected_cut_41099 : selected 10 ⟨1122053, by decide⟩
    (prefixPartial 11 83492) = some ⟨11, 2, 0, 1122053, 83492, 3585, 262144⟩ := by
  decide +kernel

theorem context_11_83492_1122053 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83492 ⟨1122053, by decide⟩ :=
  accepted_of_selected 11 83492 ⟨1122053, by decide⟩ ⟨11, 2, 0, 1122053, 83492, 3585, 262144⟩
    (by decide) selected_cut_41099

theorem selected_cut_41100 : selected 10 ⟨1122106, by decide⟩
    (prefixPartial 11 83493) = some ⟨11, 2, 0, 1122106, 83493, 3337, 262144⟩ := by
  decide +kernel

theorem context_11_83493_1122106 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83493 ⟨1122106, by decide⟩ :=
  accepted_of_selected 11 83493 ⟨1122106, by decide⟩ ⟨11, 2, 0, 1122106, 83493, 3337, 262144⟩
    (by decide) selected_cut_41100

theorem selected_cut_41101 : selected 10 ⟨1122152, by decide⟩
    (prefixPartial 11 83494) = some ⟨11, 2, 0, 1122152, 83494, 3121, 262144⟩ := by
  decide +kernel

theorem context_11_83494_1122152 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83494 ⟨1122152, by decide⟩ :=
  accepted_of_selected 11 83494 ⟨1122152, by decide⟩ ⟨11, 2, 0, 1122152, 83494, 3121, 262144⟩
    (by decide) selected_cut_41101

theorem selected_cut_41102 : selected 10 ⟨1122211, by decide⟩
    (prefixPartial 11 83495) = some ⟨11, 2, 0, 1122211, 83495, 4009, 262144⟩ := by
  decide +kernel

theorem context_11_83495_1122211 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83495 ⟨1122211, by decide⟩ :=
  accepted_of_selected 11 83495 ⟨1122211, by decide⟩ ⟨11, 2, 0, 1122211, 83495, 4009, 262144⟩
    (by decide) selected_cut_41102

theorem unmarked_context_10_20873_1122212 : frontier 11 ⟨1122212, by decide⟩
    (prefixCache 10 20873) (prefixPartial 10 20873) = false := by
  decide +kernel

theorem node_context_10_20873_1122212 : EJMOriginalGlobalDAGData.nodes 11 ⟨1122212, by decide⟩ =
    .split (coordinate 10) (![⟨1122053, by decide⟩,⟨1122106, by decide⟩,⟨1122152, by decide⟩,⟨1122211, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_20873_1122212 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20873 ⟨1122212, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 20873
    ⟨1122212, by decide⟩ (by decide) (![⟨1122053, by decide⟩,⟨1122106, by decide⟩,⟨1122152, by decide⟩,⟨1122211, by decide⟩]) unmarked_context_10_20873_1122212 node_context_10_20873_1122212
  intro a
  fin_cases a
  · exact context_11_83492_1122053
  · exact context_11_83493_1122106
  · exact context_11_83494_1122152
  · exact context_11_83495_1122211

theorem selected_cut_41103 : selected 10 ⟨1122245, by decide⟩
    (prefixPartial 11 83496) = some ⟨11, 2, 0, 1122245, 83496, 2121, 262144⟩ := by
  decide +kernel

theorem context_11_83496_1122245 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83496 ⟨1122245, by decide⟩ :=
  accepted_of_selected 11 83496 ⟨1122245, by decide⟩ ⟨11, 2, 0, 1122245, 83496, 2121, 262144⟩
    (by decide) selected_cut_41103

theorem selected_cut_41104 : selected 10 ⟨1122298, by decide⟩
    (prefixPartial 11 83497) = some ⟨11, 2, 0, 1122298, 83497, 3053, 262144⟩ := by
  decide +kernel

theorem context_11_83497_1122298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83497 ⟨1122298, by decide⟩ :=
  accepted_of_selected 11 83497 ⟨1122298, by decide⟩ ⟨11, 2, 0, 1122298, 83497, 3053, 262144⟩
    (by decide) selected_cut_41104

theorem selected_cut_41105 : selected 10 ⟨1109453, by decide⟩
    (prefixPartial 11 83498) = some ⟨11, 1, 0, 1109453, 83498, 1, 262144⟩ := by
  decide +kernel

theorem context_11_83498_1109453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83498 ⟨1109453, by decide⟩ :=
  accepted_of_selected 11 83498 ⟨1109453, by decide⟩ ⟨11, 1, 0, 1109453, 83498, 1, 262144⟩
    (by decide) selected_cut_41105

theorem selected_cut_41106 : selected 10 ⟨1122337, by decide⟩
    (prefixPartial 11 83499) = some ⟨11, 2, 0, 1122337, 83499, 2501, 262144⟩ := by
  decide +kernel

theorem context_11_83499_1122337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83499 ⟨1122337, by decide⟩ :=
  accepted_of_selected 11 83499 ⟨1122337, by decide⟩ ⟨11, 2, 0, 1122337, 83499, 2501, 262144⟩
    (by decide) selected_cut_41106

theorem unmarked_context_10_20874_1122338 : frontier 11 ⟨1122338, by decide⟩
    (prefixCache 10 20874) (prefixPartial 10 20874) = false := by
  decide +kernel

theorem node_context_10_20874_1122338 : EJMOriginalGlobalDAGData.nodes 11 ⟨1122338, by decide⟩ =
    .split (coordinate 10) (![⟨1122245, by decide⟩,⟨1122298, by decide⟩,⟨1109453, by decide⟩,⟨1122337, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_20874_1122338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20874 ⟨1122338, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 20874
    ⟨1122338, by decide⟩ (by decide) (![⟨1122245, by decide⟩,⟨1122298, by decide⟩,⟨1109453, by decide⟩,⟨1122337, by decide⟩]) unmarked_context_10_20874_1122338 node_context_10_20874_1122338
  intro a
  fin_cases a
  · exact context_11_83496_1122245
  · exact context_11_83497_1122298
  · exact context_11_83498_1109453
  · exact context_11_83499_1122337

theorem selected_cut_41107 : selected 10 ⟨1122384, by decide⟩
    (prefixPartial 11 83500) = some ⟨11, 2, 0, 1122384, 83500, 2777, 262144⟩ := by
  decide +kernel

theorem context_11_83500_1122384 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83500 ⟨1122384, by decide⟩ :=
  accepted_of_selected 11 83500 ⟨1122384, by decide⟩ ⟨11, 2, 0, 1122384, 83500, 2777, 262144⟩
    (by decide) selected_cut_41107

theorem selected_cut_41108 : selected 10 ⟨1122445, by decide⟩
    (prefixPartial 11 83501) = some ⟨11, 2, 0, 1122445, 83501, 3437, 262144⟩ := by
  decide +kernel

theorem context_11_83501_1122445 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83501 ⟨1122445, by decide⟩ :=
  accepted_of_selected 11 83501 ⟨1122445, by decide⟩ ⟨11, 2, 0, 1122445, 83501, 3437, 262144⟩
    (by decide) selected_cut_41108

theorem selected_cut_41109 : selected 10 ⟨1122488, by decide⟩
    (prefixPartial 11 83502) = some ⟨11, 2, 0, 1122488, 83502, 2313, 262144⟩ := by
  decide +kernel

theorem context_11_83502_1122488 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83502 ⟨1122488, by decide⟩ :=
  accepted_of_selected 11 83502 ⟨1122488, by decide⟩ ⟨11, 2, 0, 1122488, 83502, 2313, 262144⟩
    (by decide) selected_cut_41109

theorem selected_cut_41110 : selected 10 ⟨1122529, by decide⟩
    (prefixPartial 11 83503) = some ⟨11, 2, 0, 1122529, 83503, 2125, 262144⟩ := by
  decide +kernel

theorem context_11_83503_1122529 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83503 ⟨1122529, by decide⟩ :=
  accepted_of_selected 11 83503 ⟨1122529, by decide⟩ ⟨11, 2, 0, 1122529, 83503, 2125, 262144⟩
    (by decide) selected_cut_41110

theorem unmarked_context_10_20875_1122530 : frontier 11 ⟨1122530, by decide⟩
    (prefixCache 10 20875) (prefixPartial 10 20875) = false := by
  decide +kernel

theorem node_context_10_20875_1122530 : EJMOriginalGlobalDAGData.nodes 11 ⟨1122530, by decide⟩ =
    .split (coordinate 10) (![⟨1122384, by decide⟩,⟨1122445, by decide⟩,⟨1122488, by decide⟩,⟨1122529, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_20875_1122530 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20875 ⟨1122530, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 20875
    ⟨1122530, by decide⟩ (by decide) (![⟨1122384, by decide⟩,⟨1122445, by decide⟩,⟨1122488, by decide⟩,⟨1122529, by decide⟩]) unmarked_context_10_20875_1122530 node_context_10_20875_1122530
  intro a
  fin_cases a
  · exact context_11_83500_1122384
  · exact context_11_83501_1122445
  · exact context_11_83502_1122488
  · exact context_11_83503_1122529

theorem unmarked_context_9_5218_1122531 : frontier 12 ⟨1122531, by decide⟩
    (prefixCache 9 5218) (prefixPartial 9 5218) = false := by
  decide +kernel

theorem node_context_9_5218_1122531 : EJMOriginalGlobalDAGData.nodes 12 ⟨1122531, by decide⟩ =
    .split (coordinate 9) (![⟨1121994, by decide⟩,⟨1122212, by decide⟩,⟨1122338, by decide⟩,⟨1122530, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5218_1122531 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5218 ⟨1122531, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5218
    ⟨1122531, by decide⟩ (by decide) (![⟨1121994, by decide⟩,⟨1122212, by decide⟩,⟨1122338, by decide⟩,⟨1122530, by decide⟩]) unmarked_context_9_5218_1122531 node_context_9_5218_1122531
  intro a
  fin_cases a
  · exact context_10_20872_1121994
  · exact context_10_20873_1122212
  · exact context_10_20874_1122338
  · exact context_10_20875_1122530

theorem selected_cut_41111 : selected 10 ⟨1122544, by decide⟩
    (prefixPartial 11 83504) = some ⟨11, 2, 0, 1122544, 83504, 1449, 262144⟩ := by
  decide +kernel

theorem context_11_83504_1122544 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83504 ⟨1122544, by decide⟩ :=
  accepted_of_selected 11 83504 ⟨1122544, by decide⟩ ⟨11, 2, 0, 1122544, 83504, 1449, 262144⟩
    (by decide) selected_cut_41111

theorem selected_cut_41112 : selected 10 ⟨1122568, by decide⟩
    (prefixPartial 11 83505) = some ⟨11, 2, 0, 1122568, 83505, 1897, 262144⟩ := by
  decide +kernel

theorem context_11_83505_1122568 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83505 ⟨1122568, by decide⟩ :=
  accepted_of_selected 11 83505 ⟨1122568, by decide⟩ ⟨11, 2, 0, 1122568, 83505, 1897, 262144⟩
    (by decide) selected_cut_41112

theorem selected_cut_41113 : selected 10 ⟨1122588, by decide⟩
    (prefixPartial 11 83506) = some ⟨11, 2, 0, 1122588, 83506, 1549, 262144⟩ := by
  decide +kernel

theorem context_11_83506_1122588 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83506 ⟨1122588, by decide⟩ :=
  accepted_of_selected 11 83506 ⟨1122588, by decide⟩ ⟨11, 2, 0, 1122588, 83506, 1549, 262144⟩
    (by decide) selected_cut_41113

theorem selected_cut_41114 : selected 10 ⟨1122611, by decide⟩
    (prefixPartial 11 83507) = some ⟨11, 2, 0, 1122611, 83507, 1293, 262144⟩ := by
  decide +kernel

theorem context_11_83507_1122611 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83507 ⟨1122611, by decide⟩ :=
  accepted_of_selected 11 83507 ⟨1122611, by decide⟩ ⟨11, 2, 0, 1122611, 83507, 1293, 262144⟩
    (by decide) selected_cut_41114

theorem unmarked_context_10_20876_1122612 : frontier 11 ⟨1122612, by decide⟩
    (prefixCache 10 20876) (prefixPartial 10 20876) = false := by
  decide +kernel

theorem node_context_10_20876_1122612 : EJMOriginalGlobalDAGData.nodes 11 ⟨1122612, by decide⟩ =
    .split (coordinate 10) (![⟨1122544, by decide⟩,⟨1122568, by decide⟩,⟨1122588, by decide⟩,⟨1122611, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_20876_1122612 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20876 ⟨1122612, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 20876
    ⟨1122612, by decide⟩ (by decide) (![⟨1122544, by decide⟩,⟨1122568, by decide⟩,⟨1122588, by decide⟩,⟨1122611, by decide⟩]) unmarked_context_10_20876_1122612 node_context_10_20876_1122612
  intro a
  fin_cases a
  · exact context_11_83504_1122544
  · exact context_11_83505_1122568
  · exact context_11_83506_1122588
  · exact context_11_83507_1122611

theorem selected_cut_41115 : selected 11 ⟨1122670, by decide⟩
    (prefixPartial 10 20877) = some ⟨10, 2, 0, 1122670, 20877, 3685, 1048576⟩ := by
  decide +kernel

theorem context_10_20877_1122670 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20877 ⟨1122670, by decide⟩ :=
  accepted_of_selected 10 20877 ⟨1122670, by decide⟩ ⟨10, 2, 0, 1122670, 20877, 3685, 1048576⟩
    (by decide) selected_cut_41115

theorem selected_cut_41116 : selected 11 ⟨1122709, by decide⟩
    (prefixPartial 10 20878) = some ⟨10, 2, 0, 1122709, 20878, 1593, 1048576⟩ := by
  decide +kernel

theorem context_10_20878_1122709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20878 ⟨1122709, by decide⟩ :=
  accepted_of_selected 10 20878 ⟨1122709, by decide⟩ ⟨10, 2, 0, 1122709, 20878, 1593, 1048576⟩
    (by decide) selected_cut_41116

theorem selected_cut_41117 : selected 11 ⟨1122738, by decide⟩
    (prefixPartial 10 20879) = some ⟨10, 2, 0, 1122738, 20879, 509, 1048576⟩ := by
  decide +kernel

theorem context_10_20879_1122738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20879 ⟨1122738, by decide⟩ :=
  accepted_of_selected 10 20879 ⟨1122738, by decide⟩ ⟨10, 2, 0, 1122738, 20879, 509, 1048576⟩
    (by decide) selected_cut_41117

theorem unmarked_context_9_5219_1122739 : frontier 12 ⟨1122739, by decide⟩
    (prefixCache 9 5219) (prefixPartial 9 5219) = false := by
  decide +kernel

theorem node_context_9_5219_1122739 : EJMOriginalGlobalDAGData.nodes 12 ⟨1122739, by decide⟩ =
    .split (coordinate 9) (![⟨1122612, by decide⟩,⟨1122670, by decide⟩,⟨1122709, by decide⟩,⟨1122738, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5219_1122739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5219 ⟨1122739, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5219
    ⟨1122739, by decide⟩ (by decide) (![⟨1122612, by decide⟩,⟨1122670, by decide⟩,⟨1122709, by decide⟩,⟨1122738, by decide⟩]) unmarked_context_9_5219_1122739 node_context_9_5219_1122739
  intro a
  fin_cases a
  · exact context_10_20876_1122612
  · exact context_10_20877_1122670
  · exact context_10_20878_1122709
  · exact context_10_20879_1122738

theorem unmarked_context_8_1304_1122740 : frontier 13 ⟨1122740, by decide⟩
    (prefixCache 8 1304) (prefixPartial 8 1304) = false := by
  decide +kernel

theorem node_context_8_1304_1122740 : EJMOriginalGlobalDAGData.nodes 13 ⟨1122740, by decide⟩ =
    .split (coordinate 8) (![⟨1120585, by decide⟩,⟨1121689, by decide⟩,⟨1122531, by decide⟩,⟨1122739, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1304_1122740 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1304 ⟨1122740, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1304
    ⟨1122740, by decide⟩ (by decide) (![⟨1120585, by decide⟩,⟨1121689, by decide⟩,⟨1122531, by decide⟩,⟨1122739, by decide⟩]) unmarked_context_8_1304_1122740 node_context_8_1304_1122740
  intro a
  fin_cases a
  · exact context_9_5216_1120585
  · exact context_9_5217_1121689
  · exact context_9_5218_1122531
  · exact context_9_5219_1122739

theorem selected_cut_41118 : selected 13 ⟨1109534, by decide⟩
    (prefixPartial 8 1305) = some ⟨8, 1, 0, 1109534, 1305, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_1305_1109534 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1305 ⟨1109534, by decide⟩ :=
  accepted_of_selected 8 1305 ⟨1109534, by decide⟩ ⟨8, 1, 0, 1109534, 1305, 1, 16777216⟩
    (by decide) selected_cut_41118

theorem selected_cut_41119 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 83584) = some ⟨11, 1, 0, 434745, 83584, 1, 262144⟩ := by
  decide +kernel

theorem context_11_83584_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83584 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 83584 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 83584, 1, 262144⟩
    (by decide) selected_cut_41119

theorem selected_cut_41120 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 334340) = some ⟨12, 1, 0, 448748, 334340, 1, 65536⟩ := by
  decide +kernel

theorem context_12_334340_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334340 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 334340 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 334340, 1, 65536⟩
    (by decide) selected_cut_41120

theorem selected_cut_41121 : selected 8 ⟨1122812, by decide⟩
    (prefixPartial 13 1337364) = some ⟨13, 2, 0, 1122812, 1337364, 1981, 16384⟩ := by
  decide +kernel

theorem context_13_1337364_1122812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1337364 ⟨1122812, by decide⟩ :=
  accepted_of_selected 13 1337364 ⟨1122812, by decide⟩ ⟨13, 2, 0, 1122812, 1337364, 1981, 16384⟩
    (by decide) selected_cut_41121

theorem selected_cut_41122 : selected 8 ⟨1122834, by decide⟩
    (prefixPartial 13 1337365) = some ⟨13, 2, 0, 1122834, 1337365, 1109, 16384⟩ := by
  decide +kernel

theorem context_13_1337365_1122834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1337365 ⟨1122834, by decide⟩ :=
  accepted_of_selected 13 1337365 ⟨1122834, by decide⟩ ⟨13, 2, 0, 1122834, 1337365, 1109, 16384⟩
    (by decide) selected_cut_41122

theorem selected_cut_41123 : selected 8 ⟨1122858, by decide⟩
    (prefixPartial 13 1337366) = some ⟨13, 2, 0, 1122858, 1337366, 1025, 16384⟩ := by
  decide +kernel

theorem context_13_1337366_1122858 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1337366 ⟨1122858, by decide⟩ :=
  accepted_of_selected 13 1337366 ⟨1122858, by decide⟩ ⟨13, 2, 0, 1122858, 1337366, 1025, 16384⟩
    (by decide) selected_cut_41123

theorem selected_cut_41124 : selected 8 ⟨1122879, by decide⟩
    (prefixPartial 13 1337367) = some ⟨13, 2, 0, 1122879, 1337367, 773, 16384⟩ := by
  decide +kernel

theorem context_13_1337367_1122879 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1337367 ⟨1122879, by decide⟩ :=
  accepted_of_selected 13 1337367 ⟨1122879, by decide⟩ ⟨13, 2, 0, 1122879, 1337367, 773, 16384⟩
    (by decide) selected_cut_41124

theorem unmarked_context_12_334341_1122880 : frontier 9 ⟨1122880, by decide⟩
    (prefixCache 12 334341) (prefixPartial 12 334341) = false := by
  decide +kernel

theorem node_context_12_334341_1122880 : EJMOriginalGlobalDAGData.nodes 9 ⟨1122880, by decide⟩ =
    .split (coordinate 12) (![⟨1122812, by decide⟩,⟨1122834, by decide⟩,⟨1122858, by decide⟩,⟨1122879, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_334341_1122880 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334341 ⟨1122880, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 334341
    ⟨1122880, by decide⟩ (by decide) (![⟨1122812, by decide⟩,⟨1122834, by decide⟩,⟨1122858, by decide⟩,⟨1122879, by decide⟩]) unmarked_context_12_334341_1122880 node_context_12_334341_1122880
  intro a
  fin_cases a
  · exact context_13_1337364_1122812
  · exact context_13_1337365_1122834
  · exact context_13_1337366_1122858
  · exact context_13_1337367_1122879

theorem selected_cut_41125 : selected 9 ⟨1122970, by decide⟩
    (prefixPartial 12 334342) = some ⟨12, 2, 0, 1122970, 334342, 3925, 65536⟩ := by
  decide +kernel

theorem context_12_334342_1122970 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334342 ⟨1122970, by decide⟩ :=
  accepted_of_selected 12 334342 ⟨1122970, by decide⟩ ⟨12, 2, 0, 1122970, 334342, 3925, 65536⟩
    (by decide) selected_cut_41125

theorem selected_cut_41126 : selected 9 ⟨1123068, by decide⟩
    (prefixPartial 12 334343) = some ⟨12, 2, 0, 1123068, 334343, 3925, 65536⟩ := by
  decide +kernel

theorem context_12_334343_1123068 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334343 ⟨1123068, by decide⟩ :=
  accepted_of_selected 12 334343 ⟨1123068, by decide⟩ ⟨12, 2, 0, 1123068, 334343, 3925, 65536⟩
    (by decide) selected_cut_41126

theorem unmarked_context_11_83585_1123069 : frontier 10 ⟨1123069, by decide⟩
    (prefixCache 11 83585) (prefixPartial 11 83585) = false := by
  decide +kernel

theorem node_context_11_83585_1123069 : EJMOriginalGlobalDAGData.nodes 10 ⟨1123069, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1122880, by decide⟩,⟨1122970, by decide⟩,⟨1123068, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83585_1123069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83585 ⟨1123069, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83585
    ⟨1123069, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1122880, by decide⟩,⟨1122970, by decide⟩,⟨1123068, by decide⟩]) unmarked_context_11_83585_1123069 node_context_11_83585_1123069
  intro a
  fin_cases a
  · exact context_12_334340_448748
  · exact context_12_334341_1122880
  · exact context_12_334342_1122970
  · exact context_12_334343_1123068

theorem selected_cut_41127 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 334344) = some ⟨12, 1, 0, 448748, 334344, 1, 65536⟩ := by
  decide +kernel

theorem context_12_334344_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334344 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 334344 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 334344, 1, 65536⟩
    (by decide) selected_cut_41127

theorem selected_cut_41128 : selected 9 ⟨1123140, by decide⟩
    (prefixPartial 12 334345) = some ⟨12, 2, 0, 1123140, 334345, 3493, 65536⟩ := by
  decide +kernel

theorem context_12_334345_1123140 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334345 ⟨1123140, by decide⟩ :=
  accepted_of_selected 12 334345 ⟨1123140, by decide⟩ ⟨12, 2, 0, 1123140, 334345, 3493, 65536⟩
    (by decide) selected_cut_41128

theorem selected_cut_41129 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 334346) = some ⟨12, 1, 0, 893903, 334346, 1, 65536⟩ := by
  decide +kernel

theorem context_12_334346_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334346 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 334346 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 334346, 1, 65536⟩
    (by decide) selected_cut_41129

theorem selected_cut_41130 : selected 9 ⟨1123220, by decide⟩
    (prefixPartial 12 334347) = some ⟨12, 2, 0, 1123220, 334347, 3453, 65536⟩ := by
  decide +kernel

theorem context_12_334347_1123220 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334347 ⟨1123220, by decide⟩ :=
  accepted_of_selected 12 334347 ⟨1123220, by decide⟩ ⟨12, 2, 0, 1123220, 334347, 3453, 65536⟩
    (by decide) selected_cut_41130

theorem unmarked_context_11_83586_1123221 : frontier 10 ⟨1123221, by decide⟩
    (prefixCache 11 83586) (prefixPartial 11 83586) = false := by
  decide +kernel

theorem node_context_11_83586_1123221 : EJMOriginalGlobalDAGData.nodes 10 ⟨1123221, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1123140, by decide⟩,⟨893903, by decide⟩,⟨1123220, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83586_1123221 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83586 ⟨1123221, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83586
    ⟨1123221, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1123140, by decide⟩,⟨893903, by decide⟩,⟨1123220, by decide⟩]) unmarked_context_11_83586_1123221 node_context_11_83586_1123221
  intro a
  fin_cases a
  · exact context_12_334344_448748
  · exact context_12_334345_1123140
  · exact context_12_334346_893903
  · exact context_12_334347_1123220

theorem selected_cut_41131 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 334348) = some ⟨12, 1, 0, 448748, 334348, 1, 65536⟩ := by
  decide +kernel

theorem context_12_334348_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334348 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 334348 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 334348, 1, 65536⟩
    (by decide) selected_cut_41131

theorem selected_cut_41132 : selected 9 ⟨1123301, by decide⟩
    (prefixPartial 12 334349) = some ⟨12, 2, 0, 1123301, 334349, 3461, 65536⟩ := by
  decide +kernel

theorem context_12_334349_1123301 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334349 ⟨1123301, by decide⟩ :=
  accepted_of_selected 12 334349 ⟨1123301, by decide⟩ ⟨12, 2, 0, 1123301, 334349, 3461, 65536⟩
    (by decide) selected_cut_41132

theorem selected_cut_41133 : selected 9 ⟨1123382, by decide⟩
    (prefixPartial 12 334350) = some ⟨12, 2, 0, 1123382, 334350, 3757, 65536⟩ := by
  decide +kernel

theorem context_12_334350_1123382 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334350 ⟨1123382, by decide⟩ :=
  accepted_of_selected 12 334350 ⟨1123382, by decide⟩ ⟨12, 2, 0, 1123382, 334350, 3757, 65536⟩
    (by decide) selected_cut_41133

theorem selected_cut_41134 : selected 9 ⟨1123453, by decide⟩
    (prefixPartial 12 334351) = some ⟨12, 2, 0, 1123453, 334351, 3101, 65536⟩ := by
  decide +kernel

theorem context_12_334351_1123453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334351 ⟨1123453, by decide⟩ :=
  accepted_of_selected 12 334351 ⟨1123453, by decide⟩ ⟨12, 2, 0, 1123453, 334351, 3101, 65536⟩
    (by decide) selected_cut_41134

theorem unmarked_context_11_83587_1123454 : frontier 10 ⟨1123454, by decide⟩
    (prefixCache 11 83587) (prefixPartial 11 83587) = false := by
  decide +kernel

theorem node_context_11_83587_1123454 : EJMOriginalGlobalDAGData.nodes 10 ⟨1123454, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1123301, by decide⟩,⟨1123382, by decide⟩,⟨1123453, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83587_1123454 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83587 ⟨1123454, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83587
    ⟨1123454, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1123301, by decide⟩,⟨1123382, by decide⟩,⟨1123453, by decide⟩]) unmarked_context_11_83587_1123454 node_context_11_83587_1123454
  intro a
  fin_cases a
  · exact context_12_334348_448748
  · exact context_12_334349_1123301
  · exact context_12_334350_1123382
  · exact context_12_334351_1123453

theorem unmarked_context_10_20896_1123455 : frontier 11 ⟨1123455, by decide⟩
    (prefixCache 10 20896) (prefixPartial 10 20896) = false := by
  decide +kernel

theorem node_context_10_20896_1123455 : EJMOriginalGlobalDAGData.nodes 11 ⟨1123455, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨1123069, by decide⟩,⟨1123221, by decide⟩,⟨1123454, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_20896_1123455 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20896 ⟨1123455, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 20896
    ⟨1123455, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨1123069, by decide⟩,⟨1123221, by decide⟩,⟨1123454, by decide⟩]) unmarked_context_10_20896_1123455 node_context_10_20896_1123455
  intro a
  fin_cases a
  · exact context_11_83584_434745
  · exact context_11_83585_1123069
  · exact context_11_83586_1123221
  · exact context_11_83587_1123454

theorem selected_cut_41135 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 334352) = some ⟨12, 1, 0, 1108174, 334352, 1, 65536⟩ := by
  decide +kernel

theorem context_12_334352_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334352 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 334352 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 334352, 1, 65536⟩
    (by decide) selected_cut_41135

theorem selected_cut_41136 : selected 9 ⟨1123536, by decide⟩
    (prefixPartial 12 334353) = some ⟨12, 2, 0, 1123536, 334353, 3453, 65536⟩ := by
  decide +kernel

theorem context_12_334353_1123536 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334353 ⟨1123536, by decide⟩ :=
  accepted_of_selected 12 334353 ⟨1123536, by decide⟩ ⟨12, 2, 0, 1123536, 334353, 3453, 65536⟩
    (by decide) selected_cut_41136

theorem selected_cut_41137 : selected 9 ⟨1123618, by decide⟩
    (prefixPartial 12 334354) = some ⟨12, 2, 0, 1123618, 334354, 3805, 65536⟩ := by
  decide +kernel

theorem context_12_334354_1123618 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334354 ⟨1123618, by decide⟩ :=
  accepted_of_selected 12 334354 ⟨1123618, by decide⟩ ⟨12, 2, 0, 1123618, 334354, 3805, 65536⟩
    (by decide) selected_cut_41137

theorem selected_cut_41138 : selected 9 ⟨1123709, by decide⟩
    (prefixPartial 12 334355) = some ⟨12, 2, 0, 1123709, 334355, 4037, 65536⟩ := by
  decide +kernel

theorem context_12_334355_1123709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334355 ⟨1123709, by decide⟩ :=
  accepted_of_selected 12 334355 ⟨1123709, by decide⟩ ⟨12, 2, 0, 1123709, 334355, 4037, 65536⟩
    (by decide) selected_cut_41138

theorem unmarked_context_11_83588_1123710 : frontier 10 ⟨1123710, by decide⟩
    (prefixCache 11 83588) (prefixPartial 11 83588) = false := by
  decide +kernel

theorem node_context_11_83588_1123710 : EJMOriginalGlobalDAGData.nodes 10 ⟨1123710, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1123536, by decide⟩,⟨1123618, by decide⟩,⟨1123709, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83588_1123710 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83588 ⟨1123710, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83588
    ⟨1123710, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1123536, by decide⟩,⟨1123618, by decide⟩,⟨1123709, by decide⟩]) unmarked_context_11_83588_1123710 node_context_11_83588_1123710
  intro a
  fin_cases a
  · exact context_12_334352_1108174
  · exact context_12_334353_1123536
  · exact context_12_334354_1123618
  · exact context_12_334355_1123709

theorem selected_cut_41139 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 334356) = some ⟨12, 1, 0, 1108174, 334356, 1, 65536⟩ := by
  decide +kernel

theorem context_12_334356_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334356 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 334356 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 334356, 1, 65536⟩
    (by decide) selected_cut_41139

theorem selected_cut_41140 : selected 9 ⟨1118965, by decide⟩
    (prefixPartial 12 334357) = some ⟨12, 1, 0, 1118965, 334357, 1, 65536⟩ := by
  decide +kernel

theorem context_12_334357_1118965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334357 ⟨1118965, by decide⟩ :=
  accepted_of_selected 12 334357 ⟨1118965, by decide⟩ ⟨12, 1, 0, 1118965, 334357, 1, 65536⟩
    (by decide) selected_cut_41140

theorem selected_cut_41141 : selected 9 ⟨1123795, by decide⟩
    (prefixPartial 12 334358) = some ⟨12, 2, 0, 1123795, 334358, 3621, 65536⟩ := by
  decide +kernel

theorem context_12_334358_1123795 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334358 ⟨1123795, by decide⟩ :=
  accepted_of_selected 12 334358 ⟨1123795, by decide⟩ ⟨12, 2, 0, 1123795, 334358, 3621, 65536⟩
    (by decide) selected_cut_41141

theorem selected_cut_41142 : selected 9 ⟨1123867, by decide⟩
    (prefixPartial 12 334359) = some ⟨12, 2, 0, 1123867, 334359, 3697, 65536⟩ := by
  decide +kernel

theorem context_12_334359_1123867 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334359 ⟨1123867, by decide⟩ :=
  accepted_of_selected 12 334359 ⟨1123867, by decide⟩ ⟨12, 2, 0, 1123867, 334359, 3697, 65536⟩
    (by decide) selected_cut_41142

theorem unmarked_context_11_83589_1123868 : frontier 10 ⟨1123868, by decide⟩
    (prefixCache 11 83589) (prefixPartial 11 83589) = false := by
  decide +kernel

theorem node_context_11_83589_1123868 : EJMOriginalGlobalDAGData.nodes 10 ⟨1123868, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1118965, by decide⟩,⟨1123795, by decide⟩,⟨1123867, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83589_1123868 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83589 ⟨1123868, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83589
    ⟨1123868, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1118965, by decide⟩,⟨1123795, by decide⟩,⟨1123867, by decide⟩]) unmarked_context_11_83589_1123868 node_context_11_83589_1123868
  intro a
  fin_cases a
  · exact context_12_334356_1108174
  · exact context_12_334357_1118965
  · exact context_12_334358_1123795
  · exact context_12_334359_1123867

theorem selected_cut_41143 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 334360) = some ⟨12, 1, 0, 1108174, 334360, 1, 65536⟩ := by
  decide +kernel

theorem context_12_334360_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334360 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 334360 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 334360, 1, 65536⟩
    (by decide) selected_cut_41143

theorem selected_cut_41144 : selected 9 ⟨1123926, by decide⟩
    (prefixPartial 12 334361) = some ⟨12, 2, 0, 1123926, 334361, 2913, 65536⟩ := by
  decide +kernel

theorem context_12_334361_1123926 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334361 ⟨1123926, by decide⟩ :=
  accepted_of_selected 12 334361 ⟨1123926, by decide⟩ ⟨12, 2, 0, 1123926, 334361, 2913, 65536⟩
    (by decide) selected_cut_41144

theorem selected_cut_41145 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 334362) = some ⟨12, 1, 0, 893903, 334362, 1, 65536⟩ := by
  decide +kernel

theorem context_12_334362_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334362 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 334362 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 334362, 1, 65536⟩
    (by decide) selected_cut_41145

theorem selected_cut_41146 : selected 9 ⟨1124010, by decide⟩
    (prefixPartial 12 334363) = some ⟨12, 2, 0, 1124010, 334363, 3377, 65536⟩ := by
  decide +kernel

theorem context_12_334363_1124010 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334363 ⟨1124010, by decide⟩ :=
  accepted_of_selected 12 334363 ⟨1124010, by decide⟩ ⟨12, 2, 0, 1124010, 334363, 3377, 65536⟩
    (by decide) selected_cut_41146

theorem unmarked_context_11_83590_1124011 : frontier 10 ⟨1124011, by decide⟩
    (prefixCache 11 83590) (prefixPartial 11 83590) = false := by
  decide +kernel

theorem node_context_11_83590_1124011 : EJMOriginalGlobalDAGData.nodes 10 ⟨1124011, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1123926, by decide⟩,⟨893903, by decide⟩,⟨1124010, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83590_1124011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83590 ⟨1124011, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83590
    ⟨1124011, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1123926, by decide⟩,⟨893903, by decide⟩,⟨1124010, by decide⟩]) unmarked_context_11_83590_1124011 node_context_11_83590_1124011
  intro a
  fin_cases a
  · exact context_12_334360_1108174
  · exact context_12_334361_1123926
  · exact context_12_334362_893903
  · exact context_12_334363_1124010

theorem selected_cut_41147 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 334364) = some ⟨12, 1, 0, 1108174, 334364, 1, 65536⟩ := by
  decide +kernel

theorem context_12_334364_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334364 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 334364 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 334364, 1, 65536⟩
    (by decide) selected_cut_41147

theorem selected_cut_41148 : selected 9 ⟨1124064, by decide⟩
    (prefixPartial 12 334365) = some ⟨12, 2, 0, 1124064, 334365, 2801, 65536⟩ := by
  decide +kernel

theorem context_12_334365_1124064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334365 ⟨1124064, by decide⟩ :=
  accepted_of_selected 12 334365 ⟨1124064, by decide⟩ ⟨12, 2, 0, 1124064, 334365, 2801, 65536⟩
    (by decide) selected_cut_41148

theorem selected_cut_41149 : selected 9 ⟨1124138, by decide⟩
    (prefixPartial 12 334366) = some ⟨12, 2, 0, 1124138, 334366, 3457, 65536⟩ := by
  decide +kernel

theorem context_12_334366_1124138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334366 ⟨1124138, by decide⟩ :=
  accepted_of_selected 12 334366 ⟨1124138, by decide⟩ ⟨12, 2, 0, 1124138, 334366, 3457, 65536⟩
    (by decide) selected_cut_41149

theorem selected_cut_41150 : selected 9 ⟨1124195, by decide⟩
    (prefixPartial 12 334367) = some ⟨12, 2, 0, 1124195, 334367, 2857, 65536⟩ := by
  decide +kernel

theorem context_12_334367_1124195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334367 ⟨1124195, by decide⟩ :=
  accepted_of_selected 12 334367 ⟨1124195, by decide⟩ ⟨12, 2, 0, 1124195, 334367, 2857, 65536⟩
    (by decide) selected_cut_41150

theorem unmarked_context_11_83591_1124196 : frontier 10 ⟨1124196, by decide⟩
    (prefixCache 11 83591) (prefixPartial 11 83591) = false := by
  decide +kernel

theorem node_context_11_83591_1124196 : EJMOriginalGlobalDAGData.nodes 10 ⟨1124196, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1124064, by decide⟩,⟨1124138, by decide⟩,⟨1124195, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83591_1124196 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83591 ⟨1124196, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83591
    ⟨1124196, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1124064, by decide⟩,⟨1124138, by decide⟩,⟨1124195, by decide⟩]) unmarked_context_11_83591_1124196 node_context_11_83591_1124196
  intro a
  fin_cases a
  · exact context_12_334364_1108174
  · exact context_12_334365_1124064
  · exact context_12_334366_1124138
  · exact context_12_334367_1124195

theorem unmarked_context_10_20897_1124197 : frontier 11 ⟨1124197, by decide⟩
    (prefixCache 10 20897) (prefixPartial 10 20897) = false := by
  decide +kernel

theorem node_context_10_20897_1124197 : EJMOriginalGlobalDAGData.nodes 11 ⟨1124197, by decide⟩ =
    .split (coordinate 10) (![⟨1123710, by decide⟩,⟨1123868, by decide⟩,⟨1124011, by decide⟩,⟨1124196, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_20897_1124197 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20897 ⟨1124197, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 20897
    ⟨1124197, by decide⟩ (by decide) (![⟨1123710, by decide⟩,⟨1123868, by decide⟩,⟨1124011, by decide⟩,⟨1124196, by decide⟩]) unmarked_context_10_20897_1124197 node_context_10_20897_1124197
  intro a
  fin_cases a
  · exact context_11_83588_1123710
  · exact context_11_83589_1123868
  · exact context_11_83590_1124011
  · exact context_11_83591_1124196

theorem selected_cut_41151 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 334368) = some ⟨12, 1, 0, 1108174, 334368, 1, 65536⟩ := by
  decide +kernel

theorem context_12_334368_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334368 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 334368 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 334368, 1, 65536⟩
    (by decide) selected_cut_41151

theorem selected_cut_41152 : selected 9 ⟨1124267, by decide⟩
    (prefixPartial 12 334369) = some ⟨12, 2, 0, 1124267, 334369, 3369, 65536⟩ := by
  decide +kernel

theorem context_12_334369_1124267 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334369 ⟨1124267, by decide⟩ :=
  accepted_of_selected 12 334369 ⟨1124267, by decide⟩ ⟨12, 2, 0, 1124267, 334369, 3369, 65536⟩
    (by decide) selected_cut_41152

theorem selected_cut_41153 : selected 9 ⟨1124338, by decide⟩
    (prefixPartial 12 334370) = some ⟨12, 2, 0, 1124338, 334370, 3405, 65536⟩ := by
  decide +kernel

theorem context_12_334370_1124338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334370 ⟨1124338, by decide⟩ :=
  accepted_of_selected 12 334370 ⟨1124338, by decide⟩ ⟨12, 2, 0, 1124338, 334370, 3405, 65536⟩
    (by decide) selected_cut_41153

theorem selected_cut_41154 : selected 9 ⟨1124424, by decide⟩
    (prefixPartial 12 334371) = some ⟨12, 2, 0, 1124424, 334371, 3797, 65536⟩ := by
  decide +kernel

theorem context_12_334371_1124424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334371 ⟨1124424, by decide⟩ :=
  accepted_of_selected 12 334371 ⟨1124424, by decide⟩ ⟨12, 2, 0, 1124424, 334371, 3797, 65536⟩
    (by decide) selected_cut_41154

theorem unmarked_context_11_83592_1124425 : frontier 10 ⟨1124425, by decide⟩
    (prefixCache 11 83592) (prefixPartial 11 83592) = false := by
  decide +kernel

theorem node_context_11_83592_1124425 : EJMOriginalGlobalDAGData.nodes 10 ⟨1124425, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1124267, by decide⟩,⟨1124338, by decide⟩,⟨1124424, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83592_1124425 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83592 ⟨1124425, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83592
    ⟨1124425, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1124267, by decide⟩,⟨1124338, by decide⟩,⟨1124424, by decide⟩]) unmarked_context_11_83592_1124425 node_context_11_83592_1124425
  intro a
  fin_cases a
  · exact context_12_334368_1108174
  · exact context_12_334369_1124267
  · exact context_12_334370_1124338
  · exact context_12_334371_1124424

theorem selected_cut_41155 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 334372) = some ⟨12, 1, 0, 1108174, 334372, 1, 65536⟩ := by
  decide +kernel

theorem context_12_334372_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334372 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 334372 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 334372, 1, 65536⟩
    (by decide) selected_cut_41155

theorem selected_cut_41156 : selected 9 ⟨1124503, by decide⟩
    (prefixPartial 12 334373) = some ⟨12, 2, 0, 1124503, 334373, 3593, 65536⟩ := by
  decide +kernel

theorem context_12_334373_1124503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334373 ⟨1124503, by decide⟩ :=
  accepted_of_selected 12 334373 ⟨1124503, by decide⟩ ⟨12, 2, 0, 1124503, 334373, 3593, 65536⟩
    (by decide) selected_cut_41156

theorem selected_cut_41157 : selected 9 ⟨1124566, by decide⟩
    (prefixPartial 12 334374) = some ⟨12, 2, 0, 1124566, 334374, 2781, 65536⟩ := by
  decide +kernel

theorem context_12_334374_1124566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334374 ⟨1124566, by decide⟩ :=
  accepted_of_selected 12 334374 ⟨1124566, by decide⟩ ⟨12, 2, 0, 1124566, 334374, 2781, 65536⟩
    (by decide) selected_cut_41157

theorem selected_cut_41158 : selected 9 ⟨1124637, by decide⟩
    (prefixPartial 12 334375) = some ⟨12, 2, 0, 1124637, 334375, 2945, 65536⟩ := by
  decide +kernel

theorem context_12_334375_1124637 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334375 ⟨1124637, by decide⟩ :=
  accepted_of_selected 12 334375 ⟨1124637, by decide⟩ ⟨12, 2, 0, 1124637, 334375, 2945, 65536⟩
    (by decide) selected_cut_41158

theorem unmarked_context_11_83593_1124638 : frontier 10 ⟨1124638, by decide⟩
    (prefixCache 11 83593) (prefixPartial 11 83593) = false := by
  decide +kernel

theorem node_context_11_83593_1124638 : EJMOriginalGlobalDAGData.nodes 10 ⟨1124638, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1124503, by decide⟩,⟨1124566, by decide⟩,⟨1124637, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83593_1124638 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83593 ⟨1124638, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83593
    ⟨1124638, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1124503, by decide⟩,⟨1124566, by decide⟩,⟨1124637, by decide⟩]) unmarked_context_11_83593_1124638 node_context_11_83593_1124638
  intro a
  fin_cases a
  · exact context_12_334372_1108174
  · exact context_12_334373_1124503
  · exact context_12_334374_1124566
  · exact context_12_334375_1124637

theorem selected_cut_41159 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 83594) = some ⟨11, 1, 0, 900587, 83594, 1, 262144⟩ := by
  decide +kernel

theorem context_11_83594_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83594 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 83594 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 83594, 1, 262144⟩
    (by decide) selected_cut_41159

theorem selected_cut_41160 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 334380) = some ⟨12, 1, 0, 1108174, 334380, 1, 65536⟩ := by
  decide +kernel

theorem context_12_334380_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334380 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 334380 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 334380, 1, 65536⟩
    (by decide) selected_cut_41160

theorem selected_cut_41161 : selected 9 ⟨1124689, by decide⟩
    (prefixPartial 12 334381) = some ⟨12, 2, 0, 1124689, 334381, 2789, 65536⟩ := by
  decide +kernel

theorem context_12_334381_1124689 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334381 ⟨1124689, by decide⟩ :=
  accepted_of_selected 12 334381 ⟨1124689, by decide⟩ ⟨12, 2, 0, 1124689, 334381, 2789, 65536⟩
    (by decide) selected_cut_41161

theorem selected_cut_41162 : selected 9 ⟨1124751, by decide⟩
    (prefixPartial 12 334382) = some ⟨12, 2, 0, 1124751, 334382, 3029, 65536⟩ := by
  decide +kernel

theorem context_12_334382_1124751 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334382 ⟨1124751, by decide⟩ :=
  accepted_of_selected 12 334382 ⟨1124751, by decide⟩ ⟨12, 2, 0, 1124751, 334382, 3029, 65536⟩
    (by decide) selected_cut_41162

theorem selected_cut_41163 : selected 9 ⟨1124801, by decide⟩
    (prefixPartial 12 334383) = some ⟨12, 2, 0, 1124801, 334383, 2665, 65536⟩ := by
  decide +kernel

theorem context_12_334383_1124801 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334383 ⟨1124801, by decide⟩ :=
  accepted_of_selected 12 334383 ⟨1124801, by decide⟩ ⟨12, 2, 0, 1124801, 334383, 2665, 65536⟩
    (by decide) selected_cut_41163

theorem unmarked_context_11_83595_1124802 : frontier 10 ⟨1124802, by decide⟩
    (prefixCache 11 83595) (prefixPartial 11 83595) = false := by
  decide +kernel

theorem node_context_11_83595_1124802 : EJMOriginalGlobalDAGData.nodes 10 ⟨1124802, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1124689, by decide⟩,⟨1124751, by decide⟩,⟨1124801, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83595_1124802 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83595 ⟨1124802, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83595
    ⟨1124802, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1124689, by decide⟩,⟨1124751, by decide⟩,⟨1124801, by decide⟩]) unmarked_context_11_83595_1124802 node_context_11_83595_1124802
  intro a
  fin_cases a
  · exact context_12_334380_1108174
  · exact context_12_334381_1124689
  · exact context_12_334382_1124751
  · exact context_12_334383_1124801

theorem unmarked_context_10_20898_1124803 : frontier 11 ⟨1124803, by decide⟩
    (prefixCache 10 20898) (prefixPartial 10 20898) = false := by
  decide +kernel

theorem node_context_10_20898_1124803 : EJMOriginalGlobalDAGData.nodes 11 ⟨1124803, by decide⟩ =
    .split (coordinate 10) (![⟨1124425, by decide⟩,⟨1124638, by decide⟩,⟨900587, by decide⟩,⟨1124802, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_20898_1124803 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20898 ⟨1124803, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 20898
    ⟨1124803, by decide⟩ (by decide) (![⟨1124425, by decide⟩,⟨1124638, by decide⟩,⟨900587, by decide⟩,⟨1124802, by decide⟩]) unmarked_context_10_20898_1124803 node_context_10_20898_1124803
  intro a
  fin_cases a
  · exact context_11_83592_1124425
  · exact context_11_83593_1124638
  · exact context_11_83594_900587
  · exact context_11_83595_1124802

theorem selected_cut_41164 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 334384) = some ⟨12, 1, 0, 1108174, 334384, 1, 65536⟩ := by
  decide +kernel

theorem context_12_334384_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334384 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 334384 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 334384, 1, 65536⟩
    (by decide) selected_cut_41164

theorem selected_cut_41165 : selected 9 ⟨1124874, by decide⟩
    (prefixPartial 12 334385) = some ⟨12, 2, 0, 1124874, 334385, 3245, 65536⟩ := by
  decide +kernel

theorem context_12_334385_1124874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334385 ⟨1124874, by decide⟩ :=
  accepted_of_selected 12 334385 ⟨1124874, by decide⟩ ⟨12, 2, 0, 1124874, 334385, 3245, 65536⟩
    (by decide) selected_cut_41165

theorem selected_cut_41166 : selected 9 ⟨1124943, by decide⟩
    (prefixPartial 12 334386) = some ⟨12, 2, 0, 1124943, 334386, 3373, 65536⟩ := by
  decide +kernel

theorem context_12_334386_1124943 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334386 ⟨1124943, by decide⟩ :=
  accepted_of_selected 12 334386 ⟨1124943, by decide⟩ ⟨12, 2, 0, 1124943, 334386, 3373, 65536⟩
    (by decide) selected_cut_41166

theorem selected_cut_41167 : selected 9 ⟨1125016, by decide⟩
    (prefixPartial 12 334387) = some ⟨12, 2, 0, 1125016, 334387, 3617, 65536⟩ := by
  decide +kernel

theorem context_12_334387_1125016 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334387 ⟨1125016, by decide⟩ :=
  accepted_of_selected 12 334387 ⟨1125016, by decide⟩ ⟨12, 2, 0, 1125016, 334387, 3617, 65536⟩
    (by decide) selected_cut_41167

theorem unmarked_context_11_83596_1125017 : frontier 10 ⟨1125017, by decide⟩
    (prefixCache 11 83596) (prefixPartial 11 83596) = false := by
  decide +kernel

theorem node_context_11_83596_1125017 : EJMOriginalGlobalDAGData.nodes 10 ⟨1125017, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1124874, by decide⟩,⟨1124943, by decide⟩,⟨1125016, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83596_1125017 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83596 ⟨1125017, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83596
    ⟨1125017, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1124874, by decide⟩,⟨1124943, by decide⟩,⟨1125016, by decide⟩]) unmarked_context_11_83596_1125017 node_context_11_83596_1125017
  intro a
  fin_cases a
  · exact context_12_334384_1108174
  · exact context_12_334385_1124874
  · exact context_12_334386_1124943
  · exact context_12_334387_1125016

theorem selected_cut_41168 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 334388) = some ⟨12, 1, 0, 1108174, 334388, 1, 65536⟩ := by
  decide +kernel

theorem context_12_334388_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334388 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 334388 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 334388, 1, 65536⟩
    (by decide) selected_cut_41168

theorem selected_cut_41169 : selected 9 ⟨1125089, by decide⟩
    (prefixPartial 12 334389) = some ⟨12, 2, 0, 1125089, 334389, 3529, 65536⟩ := by
  decide +kernel

theorem context_12_334389_1125089 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334389 ⟨1125089, by decide⟩ :=
  accepted_of_selected 12 334389 ⟨1125089, by decide⟩ ⟨12, 2, 0, 1125089, 334389, 3529, 65536⟩
    (by decide) selected_cut_41169

theorem selected_cut_41170 : selected 9 ⟨1125143, by decide⟩
    (prefixPartial 12 334390) = some ⟨12, 2, 0, 1125143, 334390, 3001, 65536⟩ := by
  decide +kernel

theorem context_12_334390_1125143 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334390 ⟨1125143, by decide⟩ :=
  accepted_of_selected 12 334390 ⟨1125143, by decide⟩ ⟨12, 2, 0, 1125143, 334390, 3001, 65536⟩
    (by decide) selected_cut_41170

theorem selected_cut_41171 : selected 9 ⟨1125195, by decide⟩
    (prefixPartial 12 334391) = some ⟨12, 2, 0, 1125195, 334391, 2841, 65536⟩ := by
  decide +kernel

theorem context_12_334391_1125195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334391 ⟨1125195, by decide⟩ :=
  accepted_of_selected 12 334391 ⟨1125195, by decide⟩ ⟨12, 2, 0, 1125195, 334391, 2841, 65536⟩
    (by decide) selected_cut_41171

theorem unmarked_context_11_83597_1125196 : frontier 10 ⟨1125196, by decide⟩
    (prefixCache 11 83597) (prefixPartial 11 83597) = false := by
  decide +kernel

theorem node_context_11_83597_1125196 : EJMOriginalGlobalDAGData.nodes 10 ⟨1125196, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1125089, by decide⟩,⟨1125143, by decide⟩,⟨1125195, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83597_1125196 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83597 ⟨1125196, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83597
    ⟨1125196, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1125089, by decide⟩,⟨1125143, by decide⟩,⟨1125195, by decide⟩]) unmarked_context_11_83597_1125196 node_context_11_83597_1125196
  intro a
  fin_cases a
  · exact context_12_334388_1108174
  · exact context_12_334389_1125089
  · exact context_12_334390_1125143
  · exact context_12_334391_1125195

theorem selected_cut_41172 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 334392) = some ⟨12, 1, 0, 1108174, 334392, 1, 65536⟩ := by
  decide +kernel

theorem context_12_334392_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334392 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 334392 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 334392, 1, 65536⟩
    (by decide) selected_cut_41172

theorem selected_cut_41173 : selected 9 ⟨1125245, by decide⟩
    (prefixPartial 12 334393) = some ⟨12, 2, 0, 1125245, 334393, 2613, 65536⟩ := by
  decide +kernel

theorem context_12_334393_1125245 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334393 ⟨1125245, by decide⟩ :=
  accepted_of_selected 12 334393 ⟨1125245, by decide⟩ ⟨12, 2, 0, 1125245, 334393, 2613, 65536⟩
    (by decide) selected_cut_41173

theorem selected_cut_41174 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 334394) = some ⟨12, 1, 0, 893903, 334394, 1, 65536⟩ := by
  decide +kernel

theorem context_12_334394_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334394 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 334394 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 334394, 1, 65536⟩
    (by decide) selected_cut_41174

theorem selected_cut_41175 : selected 9 ⟨1125319, by decide⟩
    (prefixPartial 12 334395) = some ⟨12, 2, 0, 1125319, 334395, 3157, 65536⟩ := by
  decide +kernel

theorem context_12_334395_1125319 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334395 ⟨1125319, by decide⟩ :=
  accepted_of_selected 12 334395 ⟨1125319, by decide⟩ ⟨12, 2, 0, 1125319, 334395, 3157, 65536⟩
    (by decide) selected_cut_41175

theorem unmarked_context_11_83598_1125320 : frontier 10 ⟨1125320, by decide⟩
    (prefixCache 11 83598) (prefixPartial 11 83598) = false := by
  decide +kernel

theorem node_context_11_83598_1125320 : EJMOriginalGlobalDAGData.nodes 10 ⟨1125320, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1125245, by decide⟩,⟨893903, by decide⟩,⟨1125319, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83598_1125320 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83598 ⟨1125320, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83598
    ⟨1125320, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1125245, by decide⟩,⟨893903, by decide⟩,⟨1125319, by decide⟩]) unmarked_context_11_83598_1125320 node_context_11_83598_1125320
  intro a
  fin_cases a
  · exact context_12_334392_1108174
  · exact context_12_334393_1125245
  · exact context_12_334394_893903
  · exact context_12_334395_1125319

theorem selected_cut_41176 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 334396) = some ⟨12, 1, 0, 1108174, 334396, 1, 65536⟩ := by
  decide +kernel

theorem context_12_334396_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334396 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 334396 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 334396, 1, 65536⟩
    (by decide) selected_cut_41176

theorem selected_cut_41177 : selected 9 ⟨1125359, by decide⟩
    (prefixPartial 12 334397) = some ⟨12, 2, 0, 1125359, 334397, 2565, 65536⟩ := by
  decide +kernel

theorem context_12_334397_1125359 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334397 ⟨1125359, by decide⟩ :=
  accepted_of_selected 12 334397 ⟨1125359, by decide⟩ ⟨12, 2, 0, 1125359, 334397, 2565, 65536⟩
    (by decide) selected_cut_41177

theorem selected_cut_41178 : selected 9 ⟨1125416, by decide⟩
    (prefixPartial 12 334398) = some ⟨12, 2, 0, 1125416, 334398, 2917, 65536⟩ := by
  decide +kernel

theorem context_12_334398_1125416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334398 ⟨1125416, by decide⟩ :=
  accepted_of_selected 12 334398 ⟨1125416, by decide⟩ ⟨12, 2, 0, 1125416, 334398, 2917, 65536⟩
    (by decide) selected_cut_41178

theorem selected_cut_41179 : selected 9 ⟨1120582, by decide⟩
    (prefixPartial 12 334399) = some ⟨12, 1, 0, 1120582, 334399, 1, 65536⟩ := by
  decide +kernel

theorem context_12_334399_1120582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334399 ⟨1120582, by decide⟩ :=
  accepted_of_selected 12 334399 ⟨1120582, by decide⟩ ⟨12, 1, 0, 1120582, 334399, 1, 65536⟩
    (by decide) selected_cut_41179

theorem unmarked_context_11_83599_1125417 : frontier 10 ⟨1125417, by decide⟩
    (prefixCache 11 83599) (prefixPartial 11 83599) = false := by
  decide +kernel

theorem node_context_11_83599_1125417 : EJMOriginalGlobalDAGData.nodes 10 ⟨1125417, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1125359, by decide⟩,⟨1125416, by decide⟩,⟨1120582, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83599_1125417 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83599 ⟨1125417, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83599
    ⟨1125417, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1125359, by decide⟩,⟨1125416, by decide⟩,⟨1120582, by decide⟩]) unmarked_context_11_83599_1125417 node_context_11_83599_1125417
  intro a
  fin_cases a
  · exact context_12_334396_1108174
  · exact context_12_334397_1125359
  · exact context_12_334398_1125416
  · exact context_12_334399_1120582

theorem unmarked_context_10_20899_1125418 : frontier 11 ⟨1125418, by decide⟩
    (prefixCache 10 20899) (prefixPartial 10 20899) = false := by
  decide +kernel

theorem node_context_10_20899_1125418 : EJMOriginalGlobalDAGData.nodes 11 ⟨1125418, by decide⟩ =
    .split (coordinate 10) (![⟨1125017, by decide⟩,⟨1125196, by decide⟩,⟨1125320, by decide⟩,⟨1125417, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_20899_1125418 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20899 ⟨1125418, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 20899
    ⟨1125418, by decide⟩ (by decide) (![⟨1125017, by decide⟩,⟨1125196, by decide⟩,⟨1125320, by decide⟩,⟨1125417, by decide⟩]) unmarked_context_10_20899_1125418 node_context_10_20899_1125418
  intro a
  fin_cases a
  · exact context_11_83596_1125017
  · exact context_11_83597_1125196
  · exact context_11_83598_1125320
  · exact context_11_83599_1125417

theorem unmarked_context_9_5224_1125419 : frontier 12 ⟨1125419, by decide⟩
    (prefixCache 9 5224) (prefixPartial 9 5224) = false := by
  decide +kernel

theorem node_context_9_5224_1125419 : EJMOriginalGlobalDAGData.nodes 12 ⟨1125419, by decide⟩ =
    .split (coordinate 9) (![⟨1123455, by decide⟩,⟨1124197, by decide⟩,⟨1124803, by decide⟩,⟨1125418, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5224_1125419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5224 ⟨1125419, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5224
    ⟨1125419, by decide⟩ (by decide) (![⟨1123455, by decide⟩,⟨1124197, by decide⟩,⟨1124803, by decide⟩,⟨1125418, by decide⟩]) unmarked_context_9_5224_1125419 node_context_9_5224_1125419
  intro a
  fin_cases a
  · exact context_10_20896_1123455
  · exact context_10_20897_1124197
  · exact context_10_20898_1124803
  · exact context_10_20899_1125418

theorem selected_cut_41180 : selected 9 ⟨1120586, by decide⟩
    (prefixPartial 12 334400) = some ⟨12, 1, 0, 1120586, 334400, 1, 65536⟩ := by
  decide +kernel

theorem context_12_334400_1120586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334400 ⟨1120586, by decide⟩ :=
  accepted_of_selected 12 334400 ⟨1120586, by decide⟩ ⟨12, 1, 0, 1120586, 334400, 1, 65536⟩
    (by decide) selected_cut_41180

theorem selected_cut_41181 : selected 9 ⟨1125454, by decide⟩
    (prefixPartial 12 334401) = some ⟨12, 2, 0, 1125454, 334401, 1049, 65536⟩ := by
  decide +kernel

theorem context_12_334401_1125454 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334401 ⟨1125454, by decide⟩ :=
  accepted_of_selected 12 334401 ⟨1125454, by decide⟩ ⟨12, 2, 0, 1125454, 334401, 1049, 65536⟩
    (by decide) selected_cut_41181

theorem selected_cut_41182 : selected 9 ⟨1125499, by decide⟩
    (prefixPartial 12 334402) = some ⟨12, 2, 0, 1125499, 334402, 2593, 65536⟩ := by
  decide +kernel

theorem context_12_334402_1125499 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334402 ⟨1125499, by decide⟩ :=
  accepted_of_selected 12 334402 ⟨1125499, by decide⟩ ⟨12, 2, 0, 1125499, 334402, 2593, 65536⟩
    (by decide) selected_cut_41182

theorem selected_cut_41183 : selected 9 ⟨1125545, by decide⟩
    (prefixPartial 12 334403) = some ⟨12, 2, 0, 1125545, 334403, 2741, 65536⟩ := by
  decide +kernel

theorem context_12_334403_1125545 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334403 ⟨1125545, by decide⟩ :=
  accepted_of_selected 12 334403 ⟨1125545, by decide⟩ ⟨12, 2, 0, 1125545, 334403, 2741, 65536⟩
    (by decide) selected_cut_41183

theorem unmarked_context_11_83600_1125546 : frontier 10 ⟨1125546, by decide⟩
    (prefixCache 11 83600) (prefixPartial 11 83600) = false := by
  decide +kernel

theorem node_context_11_83600_1125546 : EJMOriginalGlobalDAGData.nodes 10 ⟨1125546, by decide⟩ =
    .split (coordinate 11) (![⟨1120586, by decide⟩,⟨1125454, by decide⟩,⟨1125499, by decide⟩,⟨1125545, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83600_1125546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83600 ⟨1125546, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83600
    ⟨1125546, by decide⟩ (by decide) (![⟨1120586, by decide⟩,⟨1125454, by decide⟩,⟨1125499, by decide⟩,⟨1125545, by decide⟩]) unmarked_context_11_83600_1125546 node_context_11_83600_1125546
  intro a
  fin_cases a
  · exact context_12_334400_1120586
  · exact context_12_334401_1125454
  · exact context_12_334402_1125499
  · exact context_12_334403_1125545

theorem selected_cut_41184 : selected 9 ⟨1125580, by decide⟩
    (prefixPartial 12 334404) = some ⟨12, 2, 0, 1125580, 334404, 2257, 65536⟩ := by
  decide +kernel

theorem context_12_334404_1125580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334404 ⟨1125580, by decide⟩ :=
  accepted_of_selected 12 334404 ⟨1125580, by decide⟩ ⟨12, 2, 0, 1125580, 334404, 2257, 65536⟩
    (by decide) selected_cut_41184

theorem selected_cut_41185 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 334405) = some ⟨12, 1, 0, 170504, 334405, 1, 65536⟩ := by
  decide +kernel

theorem context_12_334405_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334405 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 334405 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 334405, 1, 65536⟩
    (by decide) selected_cut_41185

theorem selected_cut_41186 : selected 9 ⟨1125616, by decide⟩
    (prefixPartial 12 334406) = some ⟨12, 2, 0, 1125616, 334406, 2545, 65536⟩ := by
  decide +kernel

theorem context_12_334406_1125616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 334406 ⟨1125616, by decide⟩ :=
  accepted_of_selected 12 334406 ⟨1125616, by decide⟩ ⟨12, 2, 0, 1125616, 334406, 2545, 65536⟩
    (by decide) selected_cut_41186

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
