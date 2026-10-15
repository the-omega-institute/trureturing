/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover214
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_20643 : selected 8 ⟨528683, by decide⟩
    (prefixPartial 13 296301) = some ⟨13, 2, 0, 528683, 296301, 1605, 16384⟩ := by
  decide +kernel

theorem context_13_296301_528683 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296301 ⟨528683, by decide⟩ :=
  accepted_of_selected 13 296301 ⟨528683, by decide⟩ ⟨13, 2, 0, 528683, 296301, 1605, 16384⟩
    (by decide) selected_cut_20643

theorem selected_cut_20644 : selected 8 ⟨528699, by decide⟩
    (prefixPartial 13 296302) = some ⟨13, 2, 0, 528699, 296302, 2085, 16384⟩ := by
  decide +kernel

theorem context_13_296302_528699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296302 ⟨528699, by decide⟩ :=
  accepted_of_selected 13 296302 ⟨528699, by decide⟩ ⟨13, 2, 0, 528699, 296302, 2085, 16384⟩
    (by decide) selected_cut_20644

theorem selected_cut_20645 : selected 8 ⟨528706, by decide⟩
    (prefixPartial 13 296303) = some ⟨13, 2, 0, 528706, 296303, 845, 16384⟩ := by
  decide +kernel

theorem context_13_296303_528706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296303 ⟨528706, by decide⟩ :=
  accepted_of_selected 13 296303 ⟨528706, by decide⟩ ⟨13, 2, 0, 528706, 296303, 845, 16384⟩
    (by decide) selected_cut_20645

theorem unmarked_context_12_74075_528707 : frontier 9 ⟨528707, by decide⟩
    (prefixCache 12 74075) (prefixPartial 12 74075) = false := by
  decide +kernel

theorem node_context_12_74075_528707 : EJMOriginalGlobalDAGData.nodes 9 ⟨528707, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨528683, by decide⟩,⟨528699, by decide⟩,⟨528706, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74075_528707 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74075 ⟨528707, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74075
    ⟨528707, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨528683, by decide⟩,⟨528699, by decide⟩,⟨528706, by decide⟩]) unmarked_context_12_74075_528707 node_context_12_74075_528707
  intro a
  fin_cases a
  · exact context_13_296300_3444
  · exact context_13_296301_528683
  · exact context_13_296302_528699
  · exact context_13_296303_528706

theorem unmarked_context_11_18518_528708 : frontier 10 ⟨528708, by decide⟩
    (prefixCache 11 18518) (prefixPartial 11 18518) = false := by
  decide +kernel

theorem node_context_11_18518_528708 : EJMOriginalGlobalDAGData.nodes 10 ⟨528708, by decide⟩ =
    .split (coordinate 11) (![⟨528576, by decide⟩,⟨528621, by decide⟩,⟨528668, by decide⟩,⟨528707, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18518_528708 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18518 ⟨528708, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18518
    ⟨528708, by decide⟩ (by decide) (![⟨528576, by decide⟩,⟨528621, by decide⟩,⟨528668, by decide⟩,⟨528707, by decide⟩]) unmarked_context_11_18518_528708 node_context_11_18518_528708
  intro a
  fin_cases a
  · exact context_12_74072_528576
  · exact context_12_74073_528621
  · exact context_12_74074_528668
  · exact context_12_74075_528707

theorem selected_cut_20646 : selected 9 ⟨528753, by decide⟩
    (prefixPartial 12 74076) = some ⟨12, 2, 0, 528753, 74076, 3877, 65536⟩ := by
  decide +kernel

theorem context_12_74076_528753 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74076 ⟨528753, by decide⟩ :=
  accepted_of_selected 12 74076 ⟨528753, by decide⟩ ⟨12, 2, 0, 528753, 74076, 3877, 65536⟩
    (by decide) selected_cut_20646

theorem selected_cut_20647 : selected 9 ⟨528793, by decide⟩
    (prefixPartial 12 74077) = some ⟨12, 2, 0, 528793, 74077, 4049, 65536⟩ := by
  decide +kernel

theorem context_12_74077_528793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74077 ⟨528793, by decide⟩ :=
  accepted_of_selected 12 74077 ⟨528793, by decide⟩ ⟨12, 2, 0, 528793, 74077, 4049, 65536⟩
    (by decide) selected_cut_20647

theorem selected_cut_20648 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 296312) = some ⟨13, 1, 0, 3444, 296312, 1, 16384⟩ := by
  decide +kernel

theorem context_13_296312_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296312 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 296312 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 296312, 1, 16384⟩
    (by decide) selected_cut_20648

theorem selected_cut_20649 : selected 8 ⟨528809, by decide⟩
    (prefixPartial 13 296313) = some ⟨13, 2, 0, 528809, 296313, 1589, 16384⟩ := by
  decide +kernel

theorem context_13_296313_528809 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296313 ⟨528809, by decide⟩ :=
  accepted_of_selected 13 296313 ⟨528809, by decide⟩ ⟨13, 2, 0, 528809, 296313, 1589, 16384⟩
    (by decide) selected_cut_20649

theorem selected_cut_20650 : selected 8 ⟨528829, by decide⟩
    (prefixPartial 13 296314) = some ⟨13, 2, 0, 528829, 296314, 1593, 16384⟩ := by
  decide +kernel

theorem context_13_296314_528829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296314 ⟨528829, by decide⟩ :=
  accepted_of_selected 13 296314 ⟨528829, by decide⟩ ⟨13, 2, 0, 528829, 296314, 1593, 16384⟩
    (by decide) selected_cut_20650

theorem selected_cut_20651 : selected 8 ⟨528834, by decide⟩
    (prefixPartial 13 296315) = some ⟨13, 2, 0, 528834, 296315, 1149, 16384⟩ := by
  decide +kernel

theorem context_13_296315_528834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296315 ⟨528834, by decide⟩ :=
  accepted_of_selected 13 296315 ⟨528834, by decide⟩ ⟨13, 2, 0, 528834, 296315, 1149, 16384⟩
    (by decide) selected_cut_20651

theorem unmarked_context_12_74078_528835 : frontier 9 ⟨528835, by decide⟩
    (prefixCache 12 74078) (prefixPartial 12 74078) = false := by
  decide +kernel

theorem node_context_12_74078_528835 : EJMOriginalGlobalDAGData.nodes 9 ⟨528835, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨528809, by decide⟩,⟨528829, by decide⟩,⟨528834, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74078_528835 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74078 ⟨528835, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74078
    ⟨528835, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨528809, by decide⟩,⟨528829, by decide⟩,⟨528834, by decide⟩]) unmarked_context_12_74078_528835 node_context_12_74078_528835
  intro a
  fin_cases a
  · exact context_13_296312_3444
  · exact context_13_296313_528809
  · exact context_13_296314_528829
  · exact context_13_296315_528834

theorem selected_cut_20652 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 296316) = some ⟨13, 1, 0, 3444, 296316, 1, 16384⟩ := by
  decide +kernel

theorem context_13_296316_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296316 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 296316 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 296316, 1, 16384⟩
    (by decide) selected_cut_20652

theorem selected_cut_20653 : selected 8 ⟨528848, by decide⟩
    (prefixPartial 13 296317) = some ⟨13, 2, 0, 528848, 296317, 1565, 16384⟩ := by
  decide +kernel

theorem context_13_296317_528848 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296317 ⟨528848, by decide⟩ :=
  accepted_of_selected 13 296317 ⟨528848, by decide⟩ ⟨13, 2, 0, 528848, 296317, 1565, 16384⟩
    (by decide) selected_cut_20653

theorem selected_cut_20654 : selected 8 ⟨528870, by decide⟩
    (prefixPartial 13 296318) = some ⟨13, 2, 0, 528870, 296318, 1885, 16384⟩ := by
  decide +kernel

theorem context_13_296318_528870 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296318 ⟨528870, by decide⟩ :=
  accepted_of_selected 13 296318 ⟨528870, by decide⟩ ⟨13, 2, 0, 528870, 296318, 1885, 16384⟩
    (by decide) selected_cut_20654

theorem selected_cut_20655 : selected 8 ⟨528876, by decide⟩
    (prefixPartial 13 296319) = some ⟨13, 2, 0, 528876, 296319, 1021, 16384⟩ := by
  decide +kernel

theorem context_13_296319_528876 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296319 ⟨528876, by decide⟩ :=
  accepted_of_selected 13 296319 ⟨528876, by decide⟩ ⟨13, 2, 0, 528876, 296319, 1021, 16384⟩
    (by decide) selected_cut_20655

theorem unmarked_context_12_74079_528877 : frontier 9 ⟨528877, by decide⟩
    (prefixCache 12 74079) (prefixPartial 12 74079) = false := by
  decide +kernel

theorem node_context_12_74079_528877 : EJMOriginalGlobalDAGData.nodes 9 ⟨528877, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨528848, by decide⟩,⟨528870, by decide⟩,⟨528876, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74079_528877 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74079 ⟨528877, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74079
    ⟨528877, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨528848, by decide⟩,⟨528870, by decide⟩,⟨528876, by decide⟩]) unmarked_context_12_74079_528877 node_context_12_74079_528877
  intro a
  fin_cases a
  · exact context_13_296316_3444
  · exact context_13_296317_528848
  · exact context_13_296318_528870
  · exact context_13_296319_528876

theorem unmarked_context_11_18519_528878 : frontier 10 ⟨528878, by decide⟩
    (prefixCache 11 18519) (prefixPartial 11 18519) = false := by
  decide +kernel

theorem node_context_11_18519_528878 : EJMOriginalGlobalDAGData.nodes 10 ⟨528878, by decide⟩ =
    .split (coordinate 11) (![⟨528753, by decide⟩,⟨528793, by decide⟩,⟨528835, by decide⟩,⟨528877, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18519_528878 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18519 ⟨528878, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18519
    ⟨528878, by decide⟩ (by decide) (![⟨528753, by decide⟩,⟨528793, by decide⟩,⟨528835, by decide⟩,⟨528877, by decide⟩]) unmarked_context_11_18519_528878 node_context_11_18519_528878
  intro a
  fin_cases a
  · exact context_12_74076_528753
  · exact context_12_74077_528793
  · exact context_12_74078_528835
  · exact context_12_74079_528877

theorem unmarked_context_10_4629_528879 : frontier 11 ⟨528879, by decide⟩
    (prefixCache 10 4629) (prefixPartial 10 4629) = false := by
  decide +kernel

theorem node_context_10_4629_528879 : EJMOriginalGlobalDAGData.nodes 11 ⟨528879, by decide⟩ =
    .split (coordinate 10) (![⟨528412, by decide⟩,⟨528531, by decide⟩,⟨528708, by decide⟩,⟨528878, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4629_528879 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4629 ⟨528879, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4629
    ⟨528879, by decide⟩ (by decide) (![⟨528412, by decide⟩,⟨528531, by decide⟩,⟨528708, by decide⟩,⟨528878, by decide⟩]) unmarked_context_10_4629_528879 node_context_10_4629_528879
  intro a
  fin_cases a
  · exact context_11_18516_528412
  · exact context_11_18517_528531
  · exact context_11_18518_528708
  · exact context_11_18519_528878

theorem selected_cut_20656 : selected 9 ⟨528922, by decide⟩
    (prefixPartial 12 74080) = some ⟨12, 2, 0, 528922, 74080, 3141, 65536⟩ := by
  decide +kernel

theorem context_12_74080_528922 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74080 ⟨528922, by decide⟩ :=
  accepted_of_selected 12 74080 ⟨528922, by decide⟩ ⟨12, 2, 0, 528922, 74080, 3141, 65536⟩
    (by decide) selected_cut_20656

theorem selected_cut_20657 : selected 9 ⟨528964, by decide⟩
    (prefixPartial 12 74081) = some ⟨12, 2, 0, 528964, 74081, 3541, 65536⟩ := by
  decide +kernel

theorem context_12_74081_528964 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74081 ⟨528964, by decide⟩ :=
  accepted_of_selected 12 74081 ⟨528964, by decide⟩ ⟨12, 2, 0, 528964, 74081, 3541, 65536⟩
    (by decide) selected_cut_20657

theorem selected_cut_20658 : selected 9 ⟨529003, by decide⟩
    (prefixPartial 12 74082) = some ⟨12, 2, 0, 529003, 74082, 3573, 65536⟩ := by
  decide +kernel

theorem context_12_74082_529003 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74082 ⟨529003, by decide⟩ :=
  accepted_of_selected 12 74082 ⟨529003, by decide⟩ ⟨12, 2, 0, 529003, 74082, 3573, 65536⟩
    (by decide) selected_cut_20658

theorem selected_cut_20659 : selected 9 ⟨529049, by decide⟩
    (prefixPartial 12 74083) = some ⟨12, 2, 0, 529049, 74083, 3929, 65536⟩ := by
  decide +kernel

theorem context_12_74083_529049 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74083 ⟨529049, by decide⟩ :=
  accepted_of_selected 12 74083 ⟨529049, by decide⟩ ⟨12, 2, 0, 529049, 74083, 3929, 65536⟩
    (by decide) selected_cut_20659

theorem unmarked_context_11_18520_529050 : frontier 10 ⟨529050, by decide⟩
    (prefixCache 11 18520) (prefixPartial 11 18520) = false := by
  decide +kernel

theorem node_context_11_18520_529050 : EJMOriginalGlobalDAGData.nodes 10 ⟨529050, by decide⟩ =
    .split (coordinate 11) (![⟨528922, by decide⟩,⟨528964, by decide⟩,⟨529003, by decide⟩,⟨529049, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18520_529050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18520 ⟨529050, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18520
    ⟨529050, by decide⟩ (by decide) (![⟨528922, by decide⟩,⟨528964, by decide⟩,⟨529003, by decide⟩,⟨529049, by decide⟩]) unmarked_context_11_18520_529050 node_context_11_18520_529050
  intro a
  fin_cases a
  · exact context_12_74080_528922
  · exact context_12_74081_528964
  · exact context_12_74082_529003
  · exact context_12_74083_529049

theorem selected_cut_20660 : selected 9 ⟨529087, by decide⟩
    (prefixPartial 12 74084) = some ⟨12, 2, 0, 529087, 74084, 2849, 65536⟩ := by
  decide +kernel

theorem context_12_74084_529087 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74084 ⟨529087, by decide⟩ :=
  accepted_of_selected 12 74084 ⟨529087, by decide⟩ ⟨12, 2, 0, 529087, 74084, 2849, 65536⟩
    (by decide) selected_cut_20660

theorem selected_cut_20661 : selected 9 ⟨441672, by decide⟩
    (prefixPartial 12 74085) = some ⟨12, 1, 0, 441672, 74085, 1, 65536⟩ := by
  decide +kernel

theorem context_12_74085_441672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74085 ⟨441672, by decide⟩ :=
  accepted_of_selected 12 74085 ⟨441672, by decide⟩ ⟨12, 1, 0, 441672, 74085, 1, 65536⟩
    (by decide) selected_cut_20661

theorem selected_cut_20662 : selected 9 ⟨529124, by decide⟩
    (prefixPartial 12 74086) = some ⟨12, 2, 0, 529124, 74086, 3213, 65536⟩ := by
  decide +kernel

theorem context_12_74086_529124 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74086 ⟨529124, by decide⟩ :=
  accepted_of_selected 12 74086 ⟨529124, by decide⟩ ⟨12, 2, 0, 529124, 74086, 3213, 65536⟩
    (by decide) selected_cut_20662

theorem selected_cut_20663 : selected 9 ⟨529164, by decide⟩
    (prefixPartial 12 74087) = some ⟨12, 2, 0, 529164, 74087, 3729, 65536⟩ := by
  decide +kernel

theorem context_12_74087_529164 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74087 ⟨529164, by decide⟩ :=
  accepted_of_selected 12 74087 ⟨529164, by decide⟩ ⟨12, 2, 0, 529164, 74087, 3729, 65536⟩
    (by decide) selected_cut_20663

theorem unmarked_context_11_18521_529165 : frontier 10 ⟨529165, by decide⟩
    (prefixCache 11 18521) (prefixPartial 11 18521) = false := by
  decide +kernel

theorem node_context_11_18521_529165 : EJMOriginalGlobalDAGData.nodes 10 ⟨529165, by decide⟩ =
    .split (coordinate 11) (![⟨529087, by decide⟩,⟨441672, by decide⟩,⟨529124, by decide⟩,⟨529164, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18521_529165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18521 ⟨529165, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18521
    ⟨529165, by decide⟩ (by decide) (![⟨529087, by decide⟩,⟨441672, by decide⟩,⟨529124, by decide⟩,⟨529164, by decide⟩]) unmarked_context_11_18521_529165 node_context_11_18521_529165
  intro a
  fin_cases a
  · exact context_12_74084_529087
  · exact context_12_74085_441672
  · exact context_12_74086_529124
  · exact context_12_74087_529164

theorem selected_cut_20664 : selected 9 ⟨529208, by decide⟩
    (prefixPartial 12 74088) = some ⟨12, 2, 0, 529208, 74088, 3497, 65536⟩ := by
  decide +kernel

theorem context_12_74088_529208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74088 ⟨529208, by decide⟩ :=
  accepted_of_selected 12 74088 ⟨529208, by decide⟩ ⟨12, 2, 0, 529208, 74088, 3497, 65536⟩
    (by decide) selected_cut_20664

theorem selected_cut_20665 : selected 9 ⟨529259, by decide⟩
    (prefixPartial 12 74089) = some ⟨12, 2, 0, 529259, 74089, 3985, 65536⟩ := by
  decide +kernel

theorem context_12_74089_529259 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74089 ⟨529259, by decide⟩ :=
  accepted_of_selected 12 74089 ⟨529259, by decide⟩ ⟨12, 2, 0, 529259, 74089, 3985, 65536⟩
    (by decide) selected_cut_20665

theorem selected_cut_20666 : selected 9 ⟨529294, by decide⟩
    (prefixPartial 12 74090) = some ⟨12, 2, 0, 529294, 74090, 3609, 65536⟩ := by
  decide +kernel

theorem context_12_74090_529294 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74090 ⟨529294, by decide⟩ :=
  accepted_of_selected 12 74090 ⟨529294, by decide⟩ ⟨12, 2, 0, 529294, 74090, 3609, 65536⟩
    (by decide) selected_cut_20666

theorem selected_cut_20667 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 296364) = some ⟨13, 1, 0, 3444, 296364, 1, 16384⟩ := by
  decide +kernel

theorem context_13_296364_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296364 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 296364 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 296364, 1, 16384⟩
    (by decide) selected_cut_20667

theorem selected_cut_20668 : selected 8 ⟨529305, by decide⟩
    (prefixPartial 13 296365) = some ⟨13, 2, 0, 529305, 296365, 909, 16384⟩ := by
  decide +kernel

theorem context_13_296365_529305 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296365 ⟨529305, by decide⟩ :=
  accepted_of_selected 13 296365 ⟨529305, by decide⟩ ⟨13, 2, 0, 529305, 296365, 909, 16384⟩
    (by decide) selected_cut_20668

theorem selected_cut_20669 : selected 8 ⟨529338, by decide⟩
    (prefixPartial 13 296366) = some ⟨13, 2, 0, 529338, 296366, 2257, 16384⟩ := by
  decide +kernel

theorem context_13_296366_529338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296366 ⟨529338, by decide⟩ :=
  accepted_of_selected 13 296366 ⟨529338, by decide⟩ ⟨13, 2, 0, 529338, 296366, 2257, 16384⟩
    (by decide) selected_cut_20669

theorem selected_cut_20670 : selected 8 ⟨529345, by decide⟩
    (prefixPartial 13 296367) = some ⟨13, 2, 0, 529345, 296367, 1025, 16384⟩ := by
  decide +kernel

theorem context_13_296367_529345 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296367 ⟨529345, by decide⟩ :=
  accepted_of_selected 13 296367 ⟨529345, by decide⟩ ⟨13, 2, 0, 529345, 296367, 1025, 16384⟩
    (by decide) selected_cut_20670

theorem unmarked_context_12_74091_529346 : frontier 9 ⟨529346, by decide⟩
    (prefixCache 12 74091) (prefixPartial 12 74091) = false := by
  decide +kernel

theorem node_context_12_74091_529346 : EJMOriginalGlobalDAGData.nodes 9 ⟨529346, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨529305, by decide⟩,⟨529338, by decide⟩,⟨529345, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74091_529346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74091 ⟨529346, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74091
    ⟨529346, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨529305, by decide⟩,⟨529338, by decide⟩,⟨529345, by decide⟩]) unmarked_context_12_74091_529346 node_context_12_74091_529346
  intro a
  fin_cases a
  · exact context_13_296364_3444
  · exact context_13_296365_529305
  · exact context_13_296366_529338
  · exact context_13_296367_529345

theorem unmarked_context_11_18522_529347 : frontier 10 ⟨529347, by decide⟩
    (prefixCache 11 18522) (prefixPartial 11 18522) = false := by
  decide +kernel

theorem node_context_11_18522_529347 : EJMOriginalGlobalDAGData.nodes 10 ⟨529347, by decide⟩ =
    .split (coordinate 11) (![⟨529208, by decide⟩,⟨529259, by decide⟩,⟨529294, by decide⟩,⟨529346, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18522_529347 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18522 ⟨529347, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18522
    ⟨529347, by decide⟩ (by decide) (![⟨529208, by decide⟩,⟨529259, by decide⟩,⟨529294, by decide⟩,⟨529346, by decide⟩]) unmarked_context_11_18522_529347 node_context_11_18522_529347
  intro a
  fin_cases a
  · exact context_12_74088_529208
  · exact context_12_74089_529259
  · exact context_12_74090_529294
  · exact context_12_74091_529346

theorem selected_cut_20671 : selected 9 ⟨529391, by decide⟩
    (prefixPartial 12 74092) = some ⟨12, 2, 0, 529391, 74092, 3545, 65536⟩ := by
  decide +kernel

theorem context_12_74092_529391 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74092 ⟨529391, by decide⟩ :=
  accepted_of_selected 12 74092 ⟨529391, by decide⟩ ⟨12, 2, 0, 529391, 74092, 3545, 65536⟩
    (by decide) selected_cut_20671

theorem selected_cut_20672 : selected 9 ⟨529424, by decide⟩
    (prefixPartial 12 74093) = some ⟨12, 2, 0, 529424, 74093, 3689, 65536⟩ := by
  decide +kernel

theorem context_12_74093_529424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74093 ⟨529424, by decide⟩ :=
  accepted_of_selected 12 74093 ⟨529424, by decide⟩ ⟨12, 2, 0, 529424, 74093, 3689, 65536⟩
    (by decide) selected_cut_20672

theorem selected_cut_20673 : selected 9 ⟨529459, by decide⟩
    (prefixPartial 12 74094) = some ⟨12, 2, 0, 529459, 74094, 3545, 65536⟩ := by
  decide +kernel

theorem context_12_74094_529459 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74094 ⟨529459, by decide⟩ :=
  accepted_of_selected 12 74094 ⟨529459, by decide⟩ ⟨12, 2, 0, 529459, 74094, 3545, 65536⟩
    (by decide) selected_cut_20673

theorem selected_cut_20674 : selected 9 ⟨529499, by decide⟩
    (prefixPartial 12 74095) = some ⟨12, 2, 0, 529499, 74095, 3961, 65536⟩ := by
  decide +kernel

theorem context_12_74095_529499 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74095 ⟨529499, by decide⟩ :=
  accepted_of_selected 12 74095 ⟨529499, by decide⟩ ⟨12, 2, 0, 529499, 74095, 3961, 65536⟩
    (by decide) selected_cut_20674

theorem unmarked_context_11_18523_529500 : frontier 10 ⟨529500, by decide⟩
    (prefixCache 11 18523) (prefixPartial 11 18523) = false := by
  decide +kernel

theorem node_context_11_18523_529500 : EJMOriginalGlobalDAGData.nodes 10 ⟨529500, by decide⟩ =
    .split (coordinate 11) (![⟨529391, by decide⟩,⟨529424, by decide⟩,⟨529459, by decide⟩,⟨529499, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18523_529500 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18523 ⟨529500, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18523
    ⟨529500, by decide⟩ (by decide) (![⟨529391, by decide⟩,⟨529424, by decide⟩,⟨529459, by decide⟩,⟨529499, by decide⟩]) unmarked_context_11_18523_529500 node_context_11_18523_529500
  intro a
  fin_cases a
  · exact context_12_74092_529391
  · exact context_12_74093_529424
  · exact context_12_74094_529459
  · exact context_12_74095_529499

theorem unmarked_context_10_4630_529501 : frontier 11 ⟨529501, by decide⟩
    (prefixCache 10 4630) (prefixPartial 10 4630) = false := by
  decide +kernel

theorem node_context_10_4630_529501 : EJMOriginalGlobalDAGData.nodes 11 ⟨529501, by decide⟩ =
    .split (coordinate 10) (![⟨529050, by decide⟩,⟨529165, by decide⟩,⟨529347, by decide⟩,⟨529500, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4630_529501 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4630 ⟨529501, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4630
    ⟨529501, by decide⟩ (by decide) (![⟨529050, by decide⟩,⟨529165, by decide⟩,⟨529347, by decide⟩,⟨529500, by decide⟩]) unmarked_context_10_4630_529501 node_context_10_4630_529501
  intro a
  fin_cases a
  · exact context_11_18520_529050
  · exact context_11_18521_529165
  · exact context_11_18522_529347
  · exact context_11_18523_529500

theorem selected_cut_20675 : selected 9 ⟨529536, by decide⟩
    (prefixPartial 12 74096) = some ⟨12, 2, 0, 529536, 74096, 3049, 65536⟩ := by
  decide +kernel

theorem context_12_74096_529536 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74096 ⟨529536, by decide⟩ :=
  accepted_of_selected 12 74096 ⟨529536, by decide⟩ ⟨12, 2, 0, 529536, 74096, 3049, 65536⟩
    (by decide) selected_cut_20675

theorem selected_cut_20676 : selected 9 ⟨529571, by decide⟩
    (prefixPartial 12 74097) = some ⟨12, 2, 0, 529571, 74097, 3381, 65536⟩ := by
  decide +kernel

theorem context_12_74097_529571 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74097 ⟨529571, by decide⟩ :=
  accepted_of_selected 12 74097 ⟨529571, by decide⟩ ⟨12, 2, 0, 529571, 74097, 3381, 65536⟩
    (by decide) selected_cut_20676

theorem selected_cut_20677 : selected 9 ⟨529607, by decide⟩
    (prefixPartial 12 74098) = some ⟨12, 2, 0, 529607, 74098, 3465, 65536⟩ := by
  decide +kernel

theorem context_12_74098_529607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74098 ⟨529607, by decide⟩ :=
  accepted_of_selected 12 74098 ⟨529607, by decide⟩ ⟨12, 2, 0, 529607, 74098, 3465, 65536⟩
    (by decide) selected_cut_20677

theorem selected_cut_20678 : selected 9 ⟨529646, by decide⟩
    (prefixPartial 12 74099) = some ⟨12, 2, 0, 529646, 74099, 3529, 65536⟩ := by
  decide +kernel

theorem context_12_74099_529646 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74099 ⟨529646, by decide⟩ :=
  accepted_of_selected 12 74099 ⟨529646, by decide⟩ ⟨12, 2, 0, 529646, 74099, 3529, 65536⟩
    (by decide) selected_cut_20678

theorem unmarked_context_11_18524_529647 : frontier 10 ⟨529647, by decide⟩
    (prefixCache 11 18524) (prefixPartial 11 18524) = false := by
  decide +kernel

theorem node_context_11_18524_529647 : EJMOriginalGlobalDAGData.nodes 10 ⟨529647, by decide⟩ =
    .split (coordinate 11) (![⟨529536, by decide⟩,⟨529571, by decide⟩,⟨529607, by decide⟩,⟨529646, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18524_529647 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18524 ⟨529647, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18524
    ⟨529647, by decide⟩ (by decide) (![⟨529536, by decide⟩,⟨529571, by decide⟩,⟨529607, by decide⟩,⟨529646, by decide⟩]) unmarked_context_11_18524_529647 node_context_11_18524_529647
  intro a
  fin_cases a
  · exact context_12_74096_529536
  · exact context_12_74097_529571
  · exact context_12_74098_529607
  · exact context_12_74099_529646

theorem selected_cut_20679 : selected 9 ⟨529680, by decide⟩
    (prefixPartial 12 74100) = some ⟨12, 2, 0, 529680, 74100, 2697, 65536⟩ := by
  decide +kernel

theorem context_12_74100_529680 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74100 ⟨529680, by decide⟩ :=
  accepted_of_selected 12 74100 ⟨529680, by decide⟩ ⟨12, 2, 0, 529680, 74100, 2697, 65536⟩
    (by decide) selected_cut_20679

theorem selected_cut_20680 : selected 9 ⟨441672, by decide⟩
    (prefixPartial 12 74101) = some ⟨12, 1, 0, 441672, 74101, 1, 65536⟩ := by
  decide +kernel

theorem context_12_74101_441672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74101 ⟨441672, by decide⟩ :=
  accepted_of_selected 12 74101 ⟨441672, by decide⟩ ⟨12, 1, 0, 441672, 74101, 1, 65536⟩
    (by decide) selected_cut_20680

theorem selected_cut_20681 : selected 9 ⟨529715, by decide⟩
    (prefixPartial 12 74102) = some ⟨12, 2, 0, 529715, 74102, 3081, 65536⟩ := by
  decide +kernel

theorem context_12_74102_529715 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74102 ⟨529715, by decide⟩ :=
  accepted_of_selected 12 74102 ⟨529715, by decide⟩ ⟨12, 2, 0, 529715, 74102, 3081, 65536⟩
    (by decide) selected_cut_20681

theorem selected_cut_20682 : selected 9 ⟨529751, by decide⟩
    (prefixPartial 12 74103) = some ⟨12, 2, 0, 529751, 74103, 3237, 65536⟩ := by
  decide +kernel

theorem context_12_74103_529751 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74103 ⟨529751, by decide⟩ :=
  accepted_of_selected 12 74103 ⟨529751, by decide⟩ ⟨12, 2, 0, 529751, 74103, 3237, 65536⟩
    (by decide) selected_cut_20682

theorem unmarked_context_11_18525_529752 : frontier 10 ⟨529752, by decide⟩
    (prefixCache 11 18525) (prefixPartial 11 18525) = false := by
  decide +kernel

theorem node_context_11_18525_529752 : EJMOriginalGlobalDAGData.nodes 10 ⟨529752, by decide⟩ =
    .split (coordinate 11) (![⟨529680, by decide⟩,⟨441672, by decide⟩,⟨529715, by decide⟩,⟨529751, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18525_529752 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18525 ⟨529752, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18525
    ⟨529752, by decide⟩ (by decide) (![⟨529680, by decide⟩,⟨441672, by decide⟩,⟨529715, by decide⟩,⟨529751, by decide⟩]) unmarked_context_11_18525_529752 node_context_11_18525_529752
  intro a
  fin_cases a
  · exact context_12_74100_529680
  · exact context_12_74101_441672
  · exact context_12_74102_529715
  · exact context_12_74103_529751

theorem selected_cut_20683 : selected 9 ⟨529801, by decide⟩
    (prefixPartial 12 74104) = some ⟨12, 2, 0, 529801, 74104, 3269, 65536⟩ := by
  decide +kernel

theorem context_12_74104_529801 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74104 ⟨529801, by decide⟩ :=
  accepted_of_selected 12 74104 ⟨529801, by decide⟩ ⟨12, 2, 0, 529801, 74104, 3269, 65536⟩
    (by decide) selected_cut_20683

theorem selected_cut_20684 : selected 9 ⟨529844, by decide⟩
    (prefixPartial 12 74105) = some ⟨12, 2, 0, 529844, 74105, 3753, 65536⟩ := by
  decide +kernel

theorem context_12_74105_529844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74105 ⟨529844, by decide⟩ :=
  accepted_of_selected 12 74105 ⟨529844, by decide⟩ ⟨12, 2, 0, 529844, 74105, 3753, 65536⟩
    (by decide) selected_cut_20684

theorem selected_cut_20685 : selected 9 ⟨529880, by decide⟩
    (prefixPartial 12 74106) = some ⟨12, 2, 0, 529880, 74106, 3285, 65536⟩ := by
  decide +kernel

theorem context_12_74106_529880 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74106 ⟨529880, by decide⟩ :=
  accepted_of_selected 12 74106 ⟨529880, by decide⟩ ⟨12, 2, 0, 529880, 74106, 3285, 65536⟩
    (by decide) selected_cut_20685

theorem selected_cut_20686 : selected 9 ⟨529928, by decide⟩
    (prefixPartial 12 74107) = some ⟨12, 2, 0, 529928, 74107, 3457, 65536⟩ := by
  decide +kernel

theorem context_12_74107_529928 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74107 ⟨529928, by decide⟩ :=
  accepted_of_selected 12 74107 ⟨529928, by decide⟩ ⟨12, 2, 0, 529928, 74107, 3457, 65536⟩
    (by decide) selected_cut_20686

theorem unmarked_context_11_18526_529929 : frontier 10 ⟨529929, by decide⟩
    (prefixCache 11 18526) (prefixPartial 11 18526) = false := by
  decide +kernel

theorem node_context_11_18526_529929 : EJMOriginalGlobalDAGData.nodes 10 ⟨529929, by decide⟩ =
    .split (coordinate 11) (![⟨529801, by decide⟩,⟨529844, by decide⟩,⟨529880, by decide⟩,⟨529928, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18526_529929 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18526 ⟨529929, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18526
    ⟨529929, by decide⟩ (by decide) (![⟨529801, by decide⟩,⟨529844, by decide⟩,⟨529880, by decide⟩,⟨529928, by decide⟩]) unmarked_context_11_18526_529929 node_context_11_18526_529929
  intro a
  fin_cases a
  · exact context_12_74104_529801
  · exact context_12_74105_529844
  · exact context_12_74106_529880
  · exact context_12_74107_529928

theorem selected_cut_20687 : selected 9 ⟨529963, by decide⟩
    (prefixPartial 12 74108) = some ⟨12, 2, 0, 529963, 74108, 3145, 65536⟩ := by
  decide +kernel

theorem context_12_74108_529963 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74108 ⟨529963, by decide⟩ :=
  accepted_of_selected 12 74108 ⟨529963, by decide⟩ ⟨12, 2, 0, 529963, 74108, 3145, 65536⟩
    (by decide) selected_cut_20687

theorem selected_cut_20688 : selected 9 ⟨529988, by decide⟩
    (prefixPartial 12 74109) = some ⟨12, 2, 0, 529988, 74109, 3409, 65536⟩ := by
  decide +kernel

theorem context_12_74109_529988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74109 ⟨529988, by decide⟩ :=
  accepted_of_selected 12 74109 ⟨529988, by decide⟩ ⟨12, 2, 0, 529988, 74109, 3409, 65536⟩
    (by decide) selected_cut_20688

theorem selected_cut_20689 : selected 9 ⟨530014, by decide⟩
    (prefixPartial 12 74110) = some ⟨12, 2, 0, 530014, 74110, 3237, 65536⟩ := by
  decide +kernel

theorem context_12_74110_530014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74110 ⟨530014, by decide⟩ :=
  accepted_of_selected 12 74110 ⟨530014, by decide⟩ ⟨12, 2, 0, 530014, 74110, 3237, 65536⟩
    (by decide) selected_cut_20689

theorem selected_cut_20690 : selected 9 ⟨530057, by decide⟩
    (prefixPartial 12 74111) = some ⟨12, 2, 0, 530057, 74111, 3369, 65536⟩ := by
  decide +kernel

theorem context_12_74111_530057 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74111 ⟨530057, by decide⟩ :=
  accepted_of_selected 12 74111 ⟨530057, by decide⟩ ⟨12, 2, 0, 530057, 74111, 3369, 65536⟩
    (by decide) selected_cut_20690

theorem unmarked_context_11_18527_530058 : frontier 10 ⟨530058, by decide⟩
    (prefixCache 11 18527) (prefixPartial 11 18527) = false := by
  decide +kernel

theorem node_context_11_18527_530058 : EJMOriginalGlobalDAGData.nodes 10 ⟨530058, by decide⟩ =
    .split (coordinate 11) (![⟨529963, by decide⟩,⟨529988, by decide⟩,⟨530014, by decide⟩,⟨530057, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18527_530058 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18527 ⟨530058, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18527
    ⟨530058, by decide⟩ (by decide) (![⟨529963, by decide⟩,⟨529988, by decide⟩,⟨530014, by decide⟩,⟨530057, by decide⟩]) unmarked_context_11_18527_530058 node_context_11_18527_530058
  intro a
  fin_cases a
  · exact context_12_74108_529963
  · exact context_12_74109_529988
  · exact context_12_74110_530014
  · exact context_12_74111_530057

theorem unmarked_context_10_4631_530059 : frontier 11 ⟨530059, by decide⟩
    (prefixCache 10 4631) (prefixPartial 10 4631) = false := by
  decide +kernel

theorem node_context_10_4631_530059 : EJMOriginalGlobalDAGData.nodes 11 ⟨530059, by decide⟩ =
    .split (coordinate 10) (![⟨529647, by decide⟩,⟨529752, by decide⟩,⟨529929, by decide⟩,⟨530058, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4631_530059 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4631 ⟨530059, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4631
    ⟨530059, by decide⟩ (by decide) (![⟨529647, by decide⟩,⟨529752, by decide⟩,⟨529929, by decide⟩,⟨530058, by decide⟩]) unmarked_context_10_4631_530059 node_context_10_4631_530059
  intro a
  fin_cases a
  · exact context_11_18524_529647
  · exact context_11_18525_529752
  · exact context_11_18526_529929
  · exact context_11_18527_530058

theorem unmarked_context_9_1157_530060 : frontier 12 ⟨530060, by decide⟩
    (prefixCache 9 1157) (prefixPartial 9 1157) = false := by
  decide +kernel

theorem node_context_9_1157_530060 : EJMOriginalGlobalDAGData.nodes 12 ⟨530060, by decide⟩ =
    .split (coordinate 9) (![⟨528222, by decide⟩,⟨528879, by decide⟩,⟨529501, by decide⟩,⟨530059, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1157_530060 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1157 ⟨530060, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1157
    ⟨530060, by decide⟩ (by decide) (![⟨528222, by decide⟩,⟨528879, by decide⟩,⟨529501, by decide⟩,⟨530059, by decide⟩]) unmarked_context_9_1157_530060 node_context_9_1157_530060
  intro a
  fin_cases a
  · exact context_10_4628_528222
  · exact context_10_4629_528879
  · exact context_10_4630_529501
  · exact context_10_4631_530059

theorem selected_cut_20691 : selected 9 ⟨530061, by decide⟩
    (prefixPartial 12 74112) = some ⟨12, 1, 0, 530061, 74112, 1, 65536⟩ := by
  decide +kernel

theorem context_12_74112_530061 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74112 ⟨530061, by decide⟩ :=
  accepted_of_selected 12 74112 ⟨530061, by decide⟩ ⟨12, 1, 0, 530061, 74112, 1, 65536⟩
    (by decide) selected_cut_20691

theorem selected_cut_20692 : selected 9 ⟨530091, by decide⟩
    (prefixPartial 12 74113) = some ⟨12, 2, 0, 530091, 74113, 2573, 65536⟩ := by
  decide +kernel

theorem context_12_74113_530091 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74113 ⟨530091, by decide⟩ :=
  accepted_of_selected 12 74113 ⟨530091, by decide⟩ ⟨12, 2, 0, 530091, 74113, 2573, 65536⟩
    (by decide) selected_cut_20692

theorem selected_cut_20693 : selected 9 ⟨530061, by decide⟩
    (prefixPartial 12 74114) = some ⟨12, 1, 0, 530061, 74114, 1, 65536⟩ := by
  decide +kernel

theorem context_12_74114_530061 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74114 ⟨530061, by decide⟩ :=
  accepted_of_selected 12 74114 ⟨530061, by decide⟩ ⟨12, 1, 0, 530061, 74114, 1, 65536⟩
    (by decide) selected_cut_20693

theorem selected_cut_20694 : selected 9 ⟨530128, by decide⟩
    (prefixPartial 12 74115) = some ⟨12, 2, 0, 530128, 74115, 3005, 65536⟩ := by
  decide +kernel

theorem context_12_74115_530128 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74115 ⟨530128, by decide⟩ :=
  accepted_of_selected 12 74115 ⟨530128, by decide⟩ ⟨12, 2, 0, 530128, 74115, 3005, 65536⟩
    (by decide) selected_cut_20694

theorem unmarked_context_11_18528_530129 : frontier 10 ⟨530129, by decide⟩
    (prefixCache 11 18528) (prefixPartial 11 18528) = false := by
  decide +kernel

theorem node_context_11_18528_530129 : EJMOriginalGlobalDAGData.nodes 10 ⟨530129, by decide⟩ =
    .split (coordinate 11) (![⟨530061, by decide⟩,⟨530091, by decide⟩,⟨530061, by decide⟩,⟨530128, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18528_530129 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18528 ⟨530129, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18528
    ⟨530129, by decide⟩ (by decide) (![⟨530061, by decide⟩,⟨530091, by decide⟩,⟨530061, by decide⟩,⟨530128, by decide⟩]) unmarked_context_11_18528_530129 node_context_11_18528_530129
  intro a
  fin_cases a
  · exact context_12_74112_530061
  · exact context_12_74113_530091
  · exact context_12_74114_530061
  · exact context_12_74115_530128

theorem selected_cut_20695 : selected 9 ⟨530148, by decide⟩
    (prefixPartial 12 74116) = some ⟨12, 2, 0, 530148, 74116, 1681, 65536⟩ := by
  decide +kernel

theorem context_12_74116_530148 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74116 ⟨530148, by decide⟩ :=
  accepted_of_selected 12 74116 ⟨530148, by decide⟩ ⟨12, 2, 0, 530148, 74116, 1681, 65536⟩
    (by decide) selected_cut_20695

theorem selected_cut_20696 : selected 9 ⟨530179, by decide⟩
    (prefixPartial 12 74117) = some ⟨12, 2, 0, 530179, 74117, 3109, 65536⟩ := by
  decide +kernel

theorem context_12_74117_530179 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74117 ⟨530179, by decide⟩ :=
  accepted_of_selected 12 74117 ⟨530179, by decide⟩ ⟨12, 2, 0, 530179, 74117, 3109, 65536⟩
    (by decide) selected_cut_20696

theorem selected_cut_20697 : selected 9 ⟨530205, by decide⟩
    (prefixPartial 12 74118) = some ⟨12, 2, 0, 530205, 74118, 1893, 65536⟩ := by
  decide +kernel

theorem context_12_74118_530205 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74118 ⟨530205, by decide⟩ :=
  accepted_of_selected 12 74118 ⟨530205, by decide⟩ ⟨12, 2, 0, 530205, 74118, 1893, 65536⟩
    (by decide) selected_cut_20697

theorem selected_cut_20698 : selected 9 ⟨530229, by decide⟩
    (prefixPartial 12 74119) = some ⟨12, 2, 0, 530229, 74119, 1937, 65536⟩ := by
  decide +kernel

theorem context_12_74119_530229 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74119 ⟨530229, by decide⟩ :=
  accepted_of_selected 12 74119 ⟨530229, by decide⟩ ⟨12, 2, 0, 530229, 74119, 1937, 65536⟩
    (by decide) selected_cut_20698

theorem unmarked_context_11_18529_530230 : frontier 10 ⟨530230, by decide⟩
    (prefixCache 11 18529) (prefixPartial 11 18529) = false := by
  decide +kernel

theorem node_context_11_18529_530230 : EJMOriginalGlobalDAGData.nodes 10 ⟨530230, by decide⟩ =
    .split (coordinate 11) (![⟨530148, by decide⟩,⟨530179, by decide⟩,⟨530205, by decide⟩,⟨530229, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18529_530230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18529 ⟨530230, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18529
    ⟨530230, by decide⟩ (by decide) (![⟨530148, by decide⟩,⟨530179, by decide⟩,⟨530205, by decide⟩,⟨530229, by decide⟩]) unmarked_context_11_18529_530230 node_context_11_18529_530230
  intro a
  fin_cases a
  · exact context_12_74116_530148
  · exact context_12_74117_530179
  · exact context_12_74118_530205
  · exact context_12_74119_530229

theorem selected_cut_20699 : selected 9 ⟨530253, by decide⟩
    (prefixPartial 12 74120) = some ⟨12, 2, 0, 530253, 74120, 2069, 65536⟩ := by
  decide +kernel

theorem context_12_74120_530253 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74120 ⟨530253, by decide⟩ :=
  accepted_of_selected 12 74120 ⟨530253, by decide⟩ ⟨12, 2, 0, 530253, 74120, 2069, 65536⟩
    (by decide) selected_cut_20699

theorem selected_cut_20700 : selected 9 ⟨530285, by decide⟩
    (prefixPartial 12 74121) = some ⟨12, 2, 0, 530285, 74121, 2201, 65536⟩ := by
  decide +kernel

theorem context_12_74121_530285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74121 ⟨530285, by decide⟩ :=
  accepted_of_selected 12 74121 ⟨530285, by decide⟩ ⟨12, 2, 0, 530285, 74121, 2201, 65536⟩
    (by decide) selected_cut_20700

theorem selected_cut_20701 : selected 9 ⟨530317, by decide⟩
    (prefixPartial 12 74122) = some ⟨12, 2, 0, 530317, 74122, 2137, 65536⟩ := by
  decide +kernel

theorem context_12_74122_530317 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74122 ⟨530317, by decide⟩ :=
  accepted_of_selected 12 74122 ⟨530317, by decide⟩ ⟨12, 2, 0, 530317, 74122, 2137, 65536⟩
    (by decide) selected_cut_20701

theorem selected_cut_20702 : selected 9 ⟨530343, by decide⟩
    (prefixPartial 12 74123) = some ⟨12, 2, 0, 530343, 74123, 2229, 65536⟩ := by
  decide +kernel

theorem context_12_74123_530343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74123 ⟨530343, by decide⟩ :=
  accepted_of_selected 12 74123 ⟨530343, by decide⟩ ⟨12, 2, 0, 530343, 74123, 2229, 65536⟩
    (by decide) selected_cut_20702

theorem unmarked_context_11_18530_530344 : frontier 10 ⟨530344, by decide⟩
    (prefixCache 11 18530) (prefixPartial 11 18530) = false := by
  decide +kernel

theorem node_context_11_18530_530344 : EJMOriginalGlobalDAGData.nodes 10 ⟨530344, by decide⟩ =
    .split (coordinate 11) (![⟨530253, by decide⟩,⟨530285, by decide⟩,⟨530317, by decide⟩,⟨530343, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18530_530344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18530 ⟨530344, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18530
    ⟨530344, by decide⟩ (by decide) (![⟨530253, by decide⟩,⟨530285, by decide⟩,⟨530317, by decide⟩,⟨530343, by decide⟩]) unmarked_context_11_18530_530344 node_context_11_18530_530344
  intro a
  fin_cases a
  · exact context_12_74120_530253
  · exact context_12_74121_530285
  · exact context_12_74122_530317
  · exact context_12_74123_530343

theorem selected_cut_20703 : selected 9 ⟨530365, by decide⟩
    (prefixPartial 12 74124) = some ⟨12, 2, 0, 530365, 74124, 1777, 65536⟩ := by
  decide +kernel

theorem context_12_74124_530365 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74124 ⟨530365, by decide⟩ :=
  accepted_of_selected 12 74124 ⟨530365, by decide⟩ ⟨12, 2, 0, 530365, 74124, 1777, 65536⟩
    (by decide) selected_cut_20703

theorem selected_cut_20704 : selected 9 ⟨530389, by decide⟩
    (prefixPartial 12 74125) = some ⟨12, 2, 0, 530389, 74125, 1793, 65536⟩ := by
  decide +kernel

theorem context_12_74125_530389 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74125 ⟨530389, by decide⟩ :=
  accepted_of_selected 12 74125 ⟨530389, by decide⟩ ⟨12, 2, 0, 530389, 74125, 1793, 65536⟩
    (by decide) selected_cut_20704

theorem selected_cut_20705 : selected 9 ⟨530416, by decide⟩
    (prefixPartial 12 74126) = some ⟨12, 2, 0, 530416, 74126, 1989, 65536⟩ := by
  decide +kernel

theorem context_12_74126_530416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74126 ⟨530416, by decide⟩ :=
  accepted_of_selected 12 74126 ⟨530416, by decide⟩ ⟨12, 2, 0, 530416, 74126, 1989, 65536⟩
    (by decide) selected_cut_20705

theorem selected_cut_20706 : selected 9 ⟨530447, by decide⟩
    (prefixPartial 12 74127) = some ⟨12, 2, 0, 530447, 74127, 2017, 65536⟩ := by
  decide +kernel

theorem context_12_74127_530447 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74127 ⟨530447, by decide⟩ :=
  accepted_of_selected 12 74127 ⟨530447, by decide⟩ ⟨12, 2, 0, 530447, 74127, 2017, 65536⟩
    (by decide) selected_cut_20706

theorem unmarked_context_11_18531_530448 : frontier 10 ⟨530448, by decide⟩
    (prefixCache 11 18531) (prefixPartial 11 18531) = false := by
  decide +kernel

theorem node_context_11_18531_530448 : EJMOriginalGlobalDAGData.nodes 10 ⟨530448, by decide⟩ =
    .split (coordinate 11) (![⟨530365, by decide⟩,⟨530389, by decide⟩,⟨530416, by decide⟩,⟨530447, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18531_530448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18531 ⟨530448, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18531
    ⟨530448, by decide⟩ (by decide) (![⟨530365, by decide⟩,⟨530389, by decide⟩,⟨530416, by decide⟩,⟨530447, by decide⟩]) unmarked_context_11_18531_530448 node_context_11_18531_530448
  intro a
  fin_cases a
  · exact context_12_74124_530365
  · exact context_12_74125_530389
  · exact context_12_74126_530416
  · exact context_12_74127_530447

theorem unmarked_context_10_4632_530449 : frontier 11 ⟨530449, by decide⟩
    (prefixCache 10 4632) (prefixPartial 10 4632) = false := by
  decide +kernel

theorem node_context_10_4632_530449 : EJMOriginalGlobalDAGData.nodes 11 ⟨530449, by decide⟩ =
    .split (coordinate 10) (![⟨530129, by decide⟩,⟨530230, by decide⟩,⟨530344, by decide⟩,⟨530448, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4632_530449 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4632 ⟨530449, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4632
    ⟨530449, by decide⟩ (by decide) (![⟨530129, by decide⟩,⟨530230, by decide⟩,⟨530344, by decide⟩,⟨530448, by decide⟩]) unmarked_context_10_4632_530449 node_context_10_4632_530449
  intro a
  fin_cases a
  · exact context_11_18528_530129
  · exact context_11_18529_530230
  · exact context_11_18530_530344
  · exact context_11_18531_530448

theorem selected_cut_20707 : selected 9 ⟨530470, by decide⟩
    (prefixPartial 12 74128) = some ⟨12, 2, 0, 530470, 74128, 1753, 65536⟩ := by
  decide +kernel

theorem context_12_74128_530470 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74128 ⟨530470, by decide⟩ :=
  accepted_of_selected 12 74128 ⟨530470, by decide⟩ ⟨12, 2, 0, 530470, 74128, 1753, 65536⟩
    (by decide) selected_cut_20707

theorem selected_cut_20708 : selected 9 ⟨530492, by decide⟩
    (prefixPartial 12 74129) = some ⟨12, 2, 0, 530492, 74129, 1933, 65536⟩ := by
  decide +kernel

theorem context_12_74129_530492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74129 ⟨530492, by decide⟩ :=
  accepted_of_selected 12 74129 ⟨530492, by decide⟩ ⟨12, 2, 0, 530492, 74129, 1933, 65536⟩
    (by decide) selected_cut_20708

theorem selected_cut_20709 : selected 9 ⟨530517, by decide⟩
    (prefixPartial 12 74130) = some ⟨12, 2, 0, 530517, 74130, 2073, 65536⟩ := by
  decide +kernel

theorem context_12_74130_530517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74130 ⟨530517, by decide⟩ :=
  accepted_of_selected 12 74130 ⟨530517, by decide⟩ ⟨12, 2, 0, 530517, 74130, 2073, 65536⟩
    (by decide) selected_cut_20709

theorem selected_cut_20710 : selected 9 ⟨530539, by decide⟩
    (prefixPartial 12 74131) = some ⟨12, 2, 0, 530539, 74131, 2061, 65536⟩ := by
  decide +kernel

theorem context_12_74131_530539 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74131 ⟨530539, by decide⟩ :=
  accepted_of_selected 12 74131 ⟨530539, by decide⟩ ⟨12, 2, 0, 530539, 74131, 2061, 65536⟩
    (by decide) selected_cut_20710

theorem unmarked_context_11_18532_530540 : frontier 10 ⟨530540, by decide⟩
    (prefixCache 11 18532) (prefixPartial 11 18532) = false := by
  decide +kernel

theorem node_context_11_18532_530540 : EJMOriginalGlobalDAGData.nodes 10 ⟨530540, by decide⟩ =
    .split (coordinate 11) (![⟨530470, by decide⟩,⟨530492, by decide⟩,⟨530517, by decide⟩,⟨530539, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18532_530540 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18532 ⟨530540, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18532
    ⟨530540, by decide⟩ (by decide) (![⟨530470, by decide⟩,⟨530492, by decide⟩,⟨530517, by decide⟩,⟨530539, by decide⟩]) unmarked_context_11_18532_530540 node_context_11_18532_530540
  intro a
  fin_cases a
  · exact context_12_74128_530470
  · exact context_12_74129_530492
  · exact context_12_74130_530517
  · exact context_12_74131_530539

theorem selected_cut_20711 : selected 9 ⟨530562, by decide⟩
    (prefixPartial 12 74132) = some ⟨12, 2, 0, 530562, 74132, 1993, 65536⟩ := by
  decide +kernel

theorem context_12_74132_530562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74132 ⟨530562, by decide⟩ :=
  accepted_of_selected 12 74132 ⟨530562, by decide⟩ ⟨12, 2, 0, 530562, 74132, 1993, 65536⟩
    (by decide) selected_cut_20711

theorem selected_cut_20712 : selected 9 ⟨439069, by decide⟩
    (prefixPartial 12 74133) = some ⟨12, 1, 0, 439069, 74133, 1, 65536⟩ := by
  decide +kernel

theorem context_12_74133_439069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74133 ⟨439069, by decide⟩ :=
  accepted_of_selected 12 74133 ⟨439069, by decide⟩ ⟨12, 1, 0, 439069, 74133, 1, 65536⟩
    (by decide) selected_cut_20712

theorem selected_cut_20713 : selected 9 ⟨530582, by decide⟩
    (prefixPartial 12 74134) = some ⟨12, 2, 0, 530582, 74134, 2217, 65536⟩ := by
  decide +kernel

theorem context_12_74134_530582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74134 ⟨530582, by decide⟩ :=
  accepted_of_selected 12 74134 ⟨530582, by decide⟩ ⟨12, 2, 0, 530582, 74134, 2217, 65536⟩
    (by decide) selected_cut_20713

theorem selected_cut_20714 : selected 9 ⟨530604, by decide⟩
    (prefixPartial 12 74135) = some ⟨12, 2, 0, 530604, 74135, 2209, 65536⟩ := by
  decide +kernel

theorem context_12_74135_530604 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74135 ⟨530604, by decide⟩ :=
  accepted_of_selected 12 74135 ⟨530604, by decide⟩ ⟨12, 2, 0, 530604, 74135, 2209, 65536⟩
    (by decide) selected_cut_20714

theorem unmarked_context_11_18533_530605 : frontier 10 ⟨530605, by decide⟩
    (prefixCache 11 18533) (prefixPartial 11 18533) = false := by
  decide +kernel

theorem node_context_11_18533_530605 : EJMOriginalGlobalDAGData.nodes 10 ⟨530605, by decide⟩ =
    .split (coordinate 11) (![⟨530562, by decide⟩,⟨439069, by decide⟩,⟨530582, by decide⟩,⟨530604, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18533_530605 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18533 ⟨530605, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18533
    ⟨530605, by decide⟩ (by decide) (![⟨530562, by decide⟩,⟨439069, by decide⟩,⟨530582, by decide⟩,⟨530604, by decide⟩]) unmarked_context_11_18533_530605 node_context_11_18533_530605
  intro a
  fin_cases a
  · exact context_12_74132_530562
  · exact context_12_74133_439069
  · exact context_12_74134_530582
  · exact context_12_74135_530604

theorem selected_cut_20715 : selected 9 ⟨530626, by decide⟩
    (prefixPartial 12 74136) = some ⟨12, 2, 0, 530626, 74136, 1721, 65536⟩ := by
  decide +kernel

theorem context_12_74136_530626 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74136 ⟨530626, by decide⟩ :=
  accepted_of_selected 12 74136 ⟨530626, by decide⟩ ⟨12, 2, 0, 530626, 74136, 1721, 65536⟩
    (by decide) selected_cut_20715

theorem selected_cut_20716 : selected 9 ⟨530648, by decide⟩
    (prefixPartial 12 74137) = some ⟨12, 2, 0, 530648, 74137, 1925, 65536⟩ := by
  decide +kernel

theorem context_12_74137_530648 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74137 ⟨530648, by decide⟩ :=
  accepted_of_selected 12 74137 ⟨530648, by decide⟩ ⟨12, 2, 0, 530648, 74137, 1925, 65536⟩
    (by decide) selected_cut_20716

theorem selected_cut_20717 : selected 9 ⟨530669, by decide⟩
    (prefixPartial 12 74138) = some ⟨12, 2, 0, 530669, 74138, 1777, 65536⟩ := by
  decide +kernel

theorem context_12_74138_530669 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74138 ⟨530669, by decide⟩ :=
  accepted_of_selected 12 74138 ⟨530669, by decide⟩ ⟨12, 2, 0, 530669, 74138, 1777, 65536⟩
    (by decide) selected_cut_20717

theorem selected_cut_20718 : selected 9 ⟨530693, by decide⟩
    (prefixPartial 12 74139) = some ⟨12, 2, 0, 530693, 74139, 1837, 65536⟩ := by
  decide +kernel

theorem context_12_74139_530693 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74139 ⟨530693, by decide⟩ :=
  accepted_of_selected 12 74139 ⟨530693, by decide⟩ ⟨12, 2, 0, 530693, 74139, 1837, 65536⟩
    (by decide) selected_cut_20718

theorem unmarked_context_11_18534_530694 : frontier 10 ⟨530694, by decide⟩
    (prefixCache 11 18534) (prefixPartial 11 18534) = false := by
  decide +kernel

theorem node_context_11_18534_530694 : EJMOriginalGlobalDAGData.nodes 10 ⟨530694, by decide⟩ =
    .split (coordinate 11) (![⟨530626, by decide⟩,⟨530648, by decide⟩,⟨530669, by decide⟩,⟨530693, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18534_530694 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18534 ⟨530694, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18534
    ⟨530694, by decide⟩ (by decide) (![⟨530626, by decide⟩,⟨530648, by decide⟩,⟨530669, by decide⟩,⟨530693, by decide⟩]) unmarked_context_11_18534_530694 node_context_11_18534_530694
  intro a
  fin_cases a
  · exact context_12_74136_530626
  · exact context_12_74137_530648
  · exact context_12_74138_530669
  · exact context_12_74139_530693

theorem selected_cut_20719 : selected 9 ⟨530714, by decide⟩
    (prefixPartial 12 74140) = some ⟨12, 2, 0, 530714, 74140, 1801, 65536⟩ := by
  decide +kernel

theorem context_12_74140_530714 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74140 ⟨530714, by decide⟩ :=
  accepted_of_selected 12 74140 ⟨530714, by decide⟩ ⟨12, 2, 0, 530714, 74140, 1801, 65536⟩
    (by decide) selected_cut_20719

theorem selected_cut_20720 : selected 9 ⟨530734, by decide⟩
    (prefixPartial 12 74141) = some ⟨12, 2, 0, 530734, 74141, 1853, 65536⟩ := by
  decide +kernel

theorem context_12_74141_530734 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74141 ⟨530734, by decide⟩ :=
  accepted_of_selected 12 74141 ⟨530734, by decide⟩ ⟨12, 2, 0, 530734, 74141, 1853, 65536⟩
    (by decide) selected_cut_20720

theorem selected_cut_20721 : selected 9 ⟨530756, by decide⟩
    (prefixPartial 12 74142) = some ⟨12, 2, 0, 530756, 74142, 1913, 65536⟩ := by
  decide +kernel

theorem context_12_74142_530756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74142 ⟨530756, by decide⟩ :=
  accepted_of_selected 12 74142 ⟨530756, by decide⟩ ⟨12, 2, 0, 530756, 74142, 1913, 65536⟩
    (by decide) selected_cut_20721

theorem selected_cut_20722 : selected 9 ⟨530772, by decide⟩
    (prefixPartial 12 74143) = some ⟨12, 2, 0, 530772, 74143, 1901, 65536⟩ := by
  decide +kernel

theorem context_12_74143_530772 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74143 ⟨530772, by decide⟩ :=
  accepted_of_selected 12 74143 ⟨530772, by decide⟩ ⟨12, 2, 0, 530772, 74143, 1901, 65536⟩
    (by decide) selected_cut_20722

theorem unmarked_context_11_18535_530773 : frontier 10 ⟨530773, by decide⟩
    (prefixCache 11 18535) (prefixPartial 11 18535) = false := by
  decide +kernel

theorem node_context_11_18535_530773 : EJMOriginalGlobalDAGData.nodes 10 ⟨530773, by decide⟩ =
    .split (coordinate 11) (![⟨530714, by decide⟩,⟨530734, by decide⟩,⟨530756, by decide⟩,⟨530772, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18535_530773 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18535 ⟨530773, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18535
    ⟨530773, by decide⟩ (by decide) (![⟨530714, by decide⟩,⟨530734, by decide⟩,⟨530756, by decide⟩,⟨530772, by decide⟩]) unmarked_context_11_18535_530773 node_context_11_18535_530773
  intro a
  fin_cases a
  · exact context_12_74140_530714
  · exact context_12_74141_530734
  · exact context_12_74142_530756
  · exact context_12_74143_530772

theorem unmarked_context_10_4633_530774 : frontier 11 ⟨530774, by decide⟩
    (prefixCache 10 4633) (prefixPartial 10 4633) = false := by
  decide +kernel

theorem node_context_10_4633_530774 : EJMOriginalGlobalDAGData.nodes 11 ⟨530774, by decide⟩ =
    .split (coordinate 10) (![⟨530540, by decide⟩,⟨530605, by decide⟩,⟨530694, by decide⟩,⟨530773, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4633_530774 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4633 ⟨530774, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4633
    ⟨530774, by decide⟩ (by decide) (![⟨530540, by decide⟩,⟨530605, by decide⟩,⟨530694, by decide⟩,⟨530773, by decide⟩]) unmarked_context_10_4633_530774 node_context_10_4633_530774
  intro a
  fin_cases a
  · exact context_11_18532_530540
  · exact context_11_18533_530605
  · exact context_11_18534_530694
  · exact context_11_18535_530773

theorem selected_cut_20723 : selected 9 ⟨530788, by decide⟩
    (prefixPartial 12 74144) = some ⟨12, 2, 0, 530788, 74144, 1289, 65536⟩ := by
  decide +kernel

theorem context_12_74144_530788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74144 ⟨530788, by decide⟩ :=
  accepted_of_selected 12 74144 ⟨530788, by decide⟩ ⟨12, 2, 0, 530788, 74144, 1289, 65536⟩
    (by decide) selected_cut_20723

theorem selected_cut_20724 : selected 9 ⟨530804, by decide⟩
    (prefixPartial 12 74145) = some ⟨12, 2, 0, 530804, 74145, 1405, 65536⟩ := by
  decide +kernel

theorem context_12_74145_530804 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74145 ⟨530804, by decide⟩ :=
  accepted_of_selected 12 74145 ⟨530804, by decide⟩ ⟨12, 2, 0, 530804, 74145, 1405, 65536⟩
    (by decide) selected_cut_20724

theorem selected_cut_20725 : selected 9 ⟨530822, by decide⟩
    (prefixPartial 12 74146) = some ⟨12, 2, 0, 530822, 74146, 1393, 65536⟩ := by
  decide +kernel

theorem context_12_74146_530822 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74146 ⟨530822, by decide⟩ :=
  accepted_of_selected 12 74146 ⟨530822, by decide⟩ ⟨12, 2, 0, 530822, 74146, 1393, 65536⟩
    (by decide) selected_cut_20725

theorem selected_cut_20726 : selected 9 ⟨530839, by decide⟩
    (prefixPartial 12 74147) = some ⟨12, 2, 0, 530839, 74147, 1421, 65536⟩ := by
  decide +kernel

theorem context_12_74147_530839 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74147 ⟨530839, by decide⟩ :=
  accepted_of_selected 12 74147 ⟨530839, by decide⟩ ⟨12, 2, 0, 530839, 74147, 1421, 65536⟩
    (by decide) selected_cut_20726

theorem unmarked_context_11_18536_530840 : frontier 10 ⟨530840, by decide⟩
    (prefixCache 11 18536) (prefixPartial 11 18536) = false := by
  decide +kernel

theorem node_context_11_18536_530840 : EJMOriginalGlobalDAGData.nodes 10 ⟨530840, by decide⟩ =
    .split (coordinate 11) (![⟨530788, by decide⟩,⟨530804, by decide⟩,⟨530822, by decide⟩,⟨530839, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18536_530840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18536 ⟨530840, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18536
    ⟨530840, by decide⟩ (by decide) (![⟨530788, by decide⟩,⟨530804, by decide⟩,⟨530822, by decide⟩,⟨530839, by decide⟩]) unmarked_context_11_18536_530840 node_context_11_18536_530840
  intro a
  fin_cases a
  · exact context_12_74144_530788
  · exact context_12_74145_530804
  · exact context_12_74146_530822
  · exact context_12_74147_530839

theorem selected_cut_20727 : selected 9 ⟨530856, by decide⟩
    (prefixPartial 12 74148) = some ⟨12, 2, 0, 530856, 74148, 1369, 65536⟩ := by
  decide +kernel

theorem context_12_74148_530856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74148 ⟨530856, by decide⟩ :=
  accepted_of_selected 12 74148 ⟨530856, by decide⟩ ⟨12, 2, 0, 530856, 74148, 1369, 65536⟩
    (by decide) selected_cut_20727

theorem selected_cut_20728 : selected 9 ⟨530889, by decide⟩
    (prefixPartial 12 74149) = some ⟨12, 2, 0, 530889, 74149, 2341, 65536⟩ := by
  decide +kernel

theorem context_12_74149_530889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74149 ⟨530889, by decide⟩ :=
  accepted_of_selected 12 74149 ⟨530889, by decide⟩ ⟨12, 2, 0, 530889, 74149, 2341, 65536⟩
    (by decide) selected_cut_20728

theorem selected_cut_20729 : selected 9 ⟨530908, by decide⟩
    (prefixPartial 12 74150) = some ⟨12, 2, 0, 530908, 74150, 1489, 65536⟩ := by
  decide +kernel

theorem context_12_74150_530908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74150 ⟨530908, by decide⟩ :=
  accepted_of_selected 12 74150 ⟨530908, by decide⟩ ⟨12, 2, 0, 530908, 74150, 1489, 65536⟩
    (by decide) selected_cut_20729

theorem selected_cut_20730 : selected 9 ⟨530925, by decide⟩
    (prefixPartial 12 74151) = some ⟨12, 2, 0, 530925, 74151, 1553, 65536⟩ := by
  decide +kernel

theorem context_12_74151_530925 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74151 ⟨530925, by decide⟩ :=
  accepted_of_selected 12 74151 ⟨530925, by decide⟩ ⟨12, 2, 0, 530925, 74151, 1553, 65536⟩
    (by decide) selected_cut_20730

theorem unmarked_context_11_18537_530926 : frontier 10 ⟨530926, by decide⟩
    (prefixCache 11 18537) (prefixPartial 11 18537) = false := by
  decide +kernel

theorem node_context_11_18537_530926 : EJMOriginalGlobalDAGData.nodes 10 ⟨530926, by decide⟩ =
    .split (coordinate 11) (![⟨530856, by decide⟩,⟨530889, by decide⟩,⟨530908, by decide⟩,⟨530925, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18537_530926 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18537 ⟨530926, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18537
    ⟨530926, by decide⟩ (by decide) (![⟨530856, by decide⟩,⟨530889, by decide⟩,⟨530908, by decide⟩,⟨530925, by decide⟩]) unmarked_context_11_18537_530926 node_context_11_18537_530926
  intro a
  fin_cases a
  · exact context_12_74148_530856
  · exact context_12_74149_530889
  · exact context_12_74150_530908
  · exact context_12_74151_530925

theorem selected_cut_20731 : selected 9 ⟨530943, by decide⟩
    (prefixPartial 12 74152) = some ⟨12, 2, 0, 530943, 74152, 1401, 65536⟩ := by
  decide +kernel

theorem context_12_74152_530943 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74152 ⟨530943, by decide⟩ :=
  accepted_of_selected 12 74152 ⟨530943, by decide⟩ ⟨12, 2, 0, 530943, 74152, 1401, 65536⟩
    (by decide) selected_cut_20731

theorem selected_cut_20732 : selected 9 ⟨530960, by decide⟩
    (prefixPartial 12 74153) = some ⟨12, 2, 0, 530960, 74153, 1493, 65536⟩ := by
  decide +kernel

theorem context_12_74153_530960 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74153 ⟨530960, by decide⟩ :=
  accepted_of_selected 12 74153 ⟨530960, by decide⟩ ⟨12, 2, 0, 530960, 74153, 1493, 65536⟩
    (by decide) selected_cut_20732

theorem selected_cut_20733 : selected 9 ⟨530977, by decide⟩
    (prefixPartial 12 74154) = some ⟨12, 2, 0, 530977, 74154, 1349, 65536⟩ := by
  decide +kernel

theorem context_12_74154_530977 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74154 ⟨530977, by decide⟩ :=
  accepted_of_selected 12 74154 ⟨530977, by decide⟩ ⟨12, 2, 0, 530977, 74154, 1349, 65536⟩
    (by decide) selected_cut_20733

theorem selected_cut_20734 : selected 9 ⟨530996, by decide⟩
    (prefixPartial 12 74155) = some ⟨12, 2, 0, 530996, 74155, 1401, 65536⟩ := by
  decide +kernel

theorem context_12_74155_530996 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74155 ⟨530996, by decide⟩ :=
  accepted_of_selected 12 74155 ⟨530996, by decide⟩ ⟨12, 2, 0, 530996, 74155, 1401, 65536⟩
    (by decide) selected_cut_20734

theorem unmarked_context_11_18538_530997 : frontier 10 ⟨530997, by decide⟩
    (prefixCache 11 18538) (prefixPartial 11 18538) = false := by
  decide +kernel

theorem node_context_11_18538_530997 : EJMOriginalGlobalDAGData.nodes 10 ⟨530997, by decide⟩ =
    .split (coordinate 11) (![⟨530943, by decide⟩,⟨530960, by decide⟩,⟨530977, by decide⟩,⟨530996, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18538_530997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18538 ⟨530997, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18538
    ⟨530997, by decide⟩ (by decide) (![⟨530943, by decide⟩,⟨530960, by decide⟩,⟨530977, by decide⟩,⟨530996, by decide⟩]) unmarked_context_11_18538_530997 node_context_11_18538_530997
  intro a
  fin_cases a
  · exact context_12_74152_530943
  · exact context_12_74153_530960
  · exact context_12_74154_530977
  · exact context_12_74155_530996

theorem selected_cut_20735 : selected 9 ⟨531015, by decide⟩
    (prefixPartial 12 74156) = some ⟨12, 2, 0, 531015, 74156, 1341, 65536⟩ := by
  decide +kernel

theorem context_12_74156_531015 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74156 ⟨531015, by decide⟩ :=
  accepted_of_selected 12 74156 ⟨531015, by decide⟩ ⟨12, 2, 0, 531015, 74156, 1341, 65536⟩
    (by decide) selected_cut_20735

theorem selected_cut_20736 : selected 9 ⟨531028, by decide⟩
    (prefixPartial 12 74157) = some ⟨12, 2, 0, 531028, 74157, 1329, 65536⟩ := by
  decide +kernel

theorem context_12_74157_531028 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74157 ⟨531028, by decide⟩ :=
  accepted_of_selected 12 74157 ⟨531028, by decide⟩ ⟨12, 2, 0, 531028, 74157, 1329, 65536⟩
    (by decide) selected_cut_20736

theorem selected_cut_20737 : selected 9 ⟨531043, by decide⟩
    (prefixPartial 12 74158) = some ⟨12, 2, 0, 531043, 74158, 1365, 65536⟩ := by
  decide +kernel

theorem context_12_74158_531043 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74158 ⟨531043, by decide⟩ :=
  accepted_of_selected 12 74158 ⟨531043, by decide⟩ ⟨12, 2, 0, 531043, 74158, 1365, 65536⟩
    (by decide) selected_cut_20737

theorem selected_cut_20738 : selected 9 ⟨531057, by decide⟩
    (prefixPartial 12 74159) = some ⟨12, 2, 0, 531057, 74159, 1341, 65536⟩ := by
  decide +kernel

theorem context_12_74159_531057 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74159 ⟨531057, by decide⟩ :=
  accepted_of_selected 12 74159 ⟨531057, by decide⟩ ⟨12, 2, 0, 531057, 74159, 1341, 65536⟩
    (by decide) selected_cut_20738

theorem unmarked_context_11_18539_531058 : frontier 10 ⟨531058, by decide⟩
    (prefixCache 11 18539) (prefixPartial 11 18539) = false := by
  decide +kernel

theorem node_context_11_18539_531058 : EJMOriginalGlobalDAGData.nodes 10 ⟨531058, by decide⟩ =
    .split (coordinate 11) (![⟨531015, by decide⟩,⟨531028, by decide⟩,⟨531043, by decide⟩,⟨531057, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18539_531058 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18539 ⟨531058, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18539
    ⟨531058, by decide⟩ (by decide) (![⟨531015, by decide⟩,⟨531028, by decide⟩,⟨531043, by decide⟩,⟨531057, by decide⟩]) unmarked_context_11_18539_531058 node_context_11_18539_531058
  intro a
  fin_cases a
  · exact context_12_74156_531015
  · exact context_12_74157_531028
  · exact context_12_74158_531043
  · exact context_12_74159_531057

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
