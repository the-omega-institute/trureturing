/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover403
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_38787 : selected 8 ⟨1048598, by decide⟩
    (prefixPartial 13 1208343) = some ⟨13, 2, 0, 1048598, 1208343, 549, 16384⟩ := by
  decide +kernel

theorem context_13_1208343_1048598 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1208343 ⟨1048598, by decide⟩ :=
  accepted_of_selected 13 1208343 ⟨1048598, by decide⟩ ⟨13, 2, 0, 1048598, 1208343, 549, 16384⟩
    (by decide) selected_cut_38787

theorem unmarked_context_12_302085_1048599 : frontier 9 ⟨1048599, by decide⟩
    (prefixCache 12 302085) (prefixPartial 12 302085) = false := by
  decide +kernel

theorem node_context_12_302085_1048599 : EJMOriginalGlobalDAGData.nodes 9 ⟨1048599, by decide⟩ =
    .split (coordinate 12) (![⟨1048543, by decide⟩,⟨1048564, by decide⟩,⟨1048593, by decide⟩,⟨1048598, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_302085_1048599 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302085 ⟨1048599, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 302085
    ⟨1048599, by decide⟩ (by decide) (![⟨1048543, by decide⟩,⟨1048564, by decide⟩,⟨1048593, by decide⟩,⟨1048598, by decide⟩]) unmarked_context_12_302085_1048599 node_context_12_302085_1048599
  intro a
  fin_cases a
  · exact context_13_1208340_1048543
  · exact context_13_1208341_1048564
  · exact context_13_1208342_1048593
  · exact context_13_1208343_1048598

theorem selected_cut_38788 : selected 9 ⟨1048678, by decide⟩
    (prefixPartial 12 302086) = some ⟨12, 2, 0, 1048678, 302086, 4017, 65536⟩ := by
  decide +kernel

theorem context_12_302086_1048678 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302086 ⟨1048678, by decide⟩ :=
  accepted_of_selected 12 302086 ⟨1048678, by decide⟩ ⟨12, 2, 0, 1048678, 302086, 4017, 65536⟩
    (by decide) selected_cut_38788

theorem selected_cut_38789 : selected 8 ⟨1048704, by decide⟩
    (prefixPartial 13 1208348) = some ⟨13, 2, 0, 1048704, 1208348, 1425, 16384⟩ := by
  decide +kernel

theorem context_13_1208348_1048704 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1208348 ⟨1048704, by decide⟩ :=
  accepted_of_selected 13 1208348 ⟨1048704, by decide⟩ ⟨13, 2, 0, 1048704, 1208348, 1425, 16384⟩
    (by decide) selected_cut_38789

theorem selected_cut_38790 : selected 8 ⟨1048727, by decide⟩
    (prefixPartial 13 1208349) = some ⟨13, 2, 0, 1048727, 1208349, 1193, 16384⟩ := by
  decide +kernel

theorem context_13_1208349_1048727 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1208349 ⟨1048727, by decide⟩ :=
  accepted_of_selected 13 1208349 ⟨1048727, by decide⟩ ⟨13, 2, 0, 1048727, 1208349, 1193, 16384⟩
    (by decide) selected_cut_38790

theorem selected_cut_38791 : selected 8 ⟨1048754, by decide⟩
    (prefixPartial 13 1208350) = some ⟨13, 2, 0, 1048754, 1208350, 989, 16384⟩ := by
  decide +kernel

theorem context_13_1208350_1048754 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1208350 ⟨1048754, by decide⟩ :=
  accepted_of_selected 13 1208350 ⟨1048754, by decide⟩ ⟨13, 2, 0, 1048754, 1208350, 989, 16384⟩
    (by decide) selected_cut_38791

theorem selected_cut_38792 : selected 8 ⟨1048760, by decide⟩
    (prefixPartial 13 1208351) = some ⟨13, 2, 0, 1048760, 1208351, 633, 16384⟩ := by
  decide +kernel

theorem context_13_1208351_1048760 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1208351 ⟨1048760, by decide⟩ :=
  accepted_of_selected 13 1208351 ⟨1048760, by decide⟩ ⟨13, 2, 0, 1048760, 1208351, 633, 16384⟩
    (by decide) selected_cut_38792

theorem unmarked_context_12_302087_1048761 : frontier 9 ⟨1048761, by decide⟩
    (prefixCache 12 302087) (prefixPartial 12 302087) = false := by
  decide +kernel

theorem node_context_12_302087_1048761 : EJMOriginalGlobalDAGData.nodes 9 ⟨1048761, by decide⟩ =
    .split (coordinate 12) (![⟨1048704, by decide⟩,⟨1048727, by decide⟩,⟨1048754, by decide⟩,⟨1048760, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_302087_1048761 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302087 ⟨1048761, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 302087
    ⟨1048761, by decide⟩ (by decide) (![⟨1048704, by decide⟩,⟨1048727, by decide⟩,⟨1048754, by decide⟩,⟨1048760, by decide⟩]) unmarked_context_12_302087_1048761 node_context_12_302087_1048761
  intro a
  fin_cases a
  · exact context_13_1208348_1048704
  · exact context_13_1208349_1048727
  · exact context_13_1208350_1048754
  · exact context_13_1208351_1048760

theorem unmarked_context_11_75521_1048762 : frontier 10 ⟨1048762, by decide⟩
    (prefixCache 11 75521) (prefixPartial 11 75521) = false := by
  decide +kernel

theorem node_context_11_75521_1048762 : EJMOriginalGlobalDAGData.nodes 10 ⟨1048762, by decide⟩ =
    .split (coordinate 11) (![⟨1048498, by decide⟩,⟨1048599, by decide⟩,⟨1048678, by decide⟩,⟨1048761, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75521_1048762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75521 ⟨1048762, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75521
    ⟨1048762, by decide⟩ (by decide) (![⟨1048498, by decide⟩,⟨1048599, by decide⟩,⟨1048678, by decide⟩,⟨1048761, by decide⟩]) unmarked_context_11_75521_1048762 node_context_11_75521_1048762
  intro a
  fin_cases a
  · exact context_12_302084_1048498
  · exact context_12_302085_1048599
  · exact context_12_302086_1048678
  · exact context_12_302087_1048761

theorem selected_cut_38793 : selected 9 ⟨450498, by decide⟩
    (prefixPartial 12 302088) = some ⟨12, 1, 0, 450498, 302088, 1, 65536⟩ := by
  decide +kernel

theorem context_12_302088_450498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302088 ⟨450498, by decide⟩ :=
  accepted_of_selected 12 302088 ⟨450498, by decide⟩ ⟨12, 1, 0, 450498, 302088, 1, 65536⟩
    (by decide) selected_cut_38793

theorem selected_cut_38794 : selected 8 ⟨1048820, by decide⟩
    (prefixPartial 13 1208356) = some ⟨13, 2, 0, 1048820, 1208356, 2237, 16384⟩ := by
  decide +kernel

theorem context_13_1208356_1048820 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1208356 ⟨1048820, by decide⟩ :=
  accepted_of_selected 13 1208356 ⟨1048820, by decide⟩ ⟨13, 2, 0, 1048820, 1208356, 2237, 16384⟩
    (by decide) selected_cut_38794

theorem selected_cut_38795 : selected 8 ⟨1048840, by decide⟩
    (prefixPartial 13 1208357) = some ⟨13, 2, 0, 1048840, 1208357, 1049, 16384⟩ := by
  decide +kernel

theorem context_13_1208357_1048840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1208357 ⟨1048840, by decide⟩ :=
  accepted_of_selected 13 1208357 ⟨1048840, by decide⟩ ⟨13, 2, 0, 1048840, 1208357, 1049, 16384⟩
    (by decide) selected_cut_38795

theorem selected_cut_38796 : selected 8 ⟨1048860, by decide⟩
    (prefixPartial 13 1208358) = some ⟨13, 2, 0, 1048860, 1208358, 1105, 16384⟩ := by
  decide +kernel

theorem context_13_1208358_1048860 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1208358 ⟨1048860, by decide⟩ :=
  accepted_of_selected 13 1208358 ⟨1048860, by decide⟩ ⟨13, 2, 0, 1048860, 1208358, 1105, 16384⟩
    (by decide) selected_cut_38796

theorem selected_cut_38797 : selected 8 ⟨1048864, by decide⟩
    (prefixPartial 13 1208359) = some ⟨13, 2, 0, 1048864, 1208359, 537, 16384⟩ := by
  decide +kernel

theorem context_13_1208359_1048864 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1208359 ⟨1048864, by decide⟩ :=
  accepted_of_selected 13 1208359 ⟨1048864, by decide⟩ ⟨13, 2, 0, 1048864, 1208359, 537, 16384⟩
    (by decide) selected_cut_38797

theorem unmarked_context_12_302089_1048865 : frontier 9 ⟨1048865, by decide⟩
    (prefixCache 12 302089) (prefixPartial 12 302089) = false := by
  decide +kernel

theorem node_context_12_302089_1048865 : EJMOriginalGlobalDAGData.nodes 9 ⟨1048865, by decide⟩ =
    .split (coordinate 12) (![⟨1048820, by decide⟩,⟨1048840, by decide⟩,⟨1048860, by decide⟩,⟨1048864, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_302089_1048865 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302089 ⟨1048865, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 302089
    ⟨1048865, by decide⟩ (by decide) (![⟨1048820, by decide⟩,⟨1048840, by decide⟩,⟨1048860, by decide⟩,⟨1048864, by decide⟩]) unmarked_context_12_302089_1048865 node_context_12_302089_1048865
  intro a
  fin_cases a
  · exact context_13_1208356_1048820
  · exact context_13_1208357_1048840
  · exact context_13_1208358_1048860
  · exact context_13_1208359_1048864

theorem selected_cut_38798 : selected 8 ⟨1048903, by decide⟩
    (prefixPartial 13 1208360) = some ⟨13, 2, 0, 1048903, 1208360, 1717, 16384⟩ := by
  decide +kernel

theorem context_13_1208360_1048903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1208360 ⟨1048903, by decide⟩ :=
  accepted_of_selected 13 1208360 ⟨1048903, by decide⟩ ⟨13, 2, 0, 1048903, 1208360, 1717, 16384⟩
    (by decide) selected_cut_38798

theorem selected_cut_38799 : selected 8 ⟨1048920, by decide⟩
    (prefixPartial 13 1208361) = some ⟨13, 2, 0, 1048920, 1208361, 1033, 16384⟩ := by
  decide +kernel

theorem context_13_1208361_1048920 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1208361 ⟨1048920, by decide⟩ :=
  accepted_of_selected 13 1208361 ⟨1048920, by decide⟩ ⟨13, 2, 0, 1048920, 1208361, 1033, 16384⟩
    (by decide) selected_cut_38799

theorem selected_cut_38800 : selected 8 ⟨1048938, by decide⟩
    (prefixPartial 13 1208362) = some ⟨13, 2, 0, 1048938, 1208362, 901, 16384⟩ := by
  decide +kernel

theorem context_13_1208362_1048938 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1208362 ⟨1048938, by decide⟩ :=
  accepted_of_selected 13 1208362 ⟨1048938, by decide⟩ ⟨13, 2, 0, 1048938, 1208362, 901, 16384⟩
    (by decide) selected_cut_38800

theorem selected_cut_38801 : selected 8 ⟨1048939, by decide⟩
    (prefixPartial 13 1208363) = some ⟨13, 2, 0, 1048939, 1208363, 505, 16384⟩ := by
  decide +kernel

theorem context_13_1208363_1048939 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1208363 ⟨1048939, by decide⟩ :=
  accepted_of_selected 13 1208363 ⟨1048939, by decide⟩ ⟨13, 2, 0, 1048939, 1208363, 505, 16384⟩
    (by decide) selected_cut_38801

theorem unmarked_context_12_302090_1048940 : frontier 9 ⟨1048940, by decide⟩
    (prefixCache 12 302090) (prefixPartial 12 302090) = false := by
  decide +kernel

theorem node_context_12_302090_1048940 : EJMOriginalGlobalDAGData.nodes 9 ⟨1048940, by decide⟩ =
    .split (coordinate 12) (![⟨1048903, by decide⟩,⟨1048920, by decide⟩,⟨1048938, by decide⟩,⟨1048939, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_302090_1048940 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302090 ⟨1048940, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 302090
    ⟨1048940, by decide⟩ (by decide) (![⟨1048903, by decide⟩,⟨1048920, by decide⟩,⟨1048938, by decide⟩,⟨1048939, by decide⟩]) unmarked_context_12_302090_1048940 node_context_12_302090_1048940
  intro a
  fin_cases a
  · exact context_13_1208360_1048903
  · exact context_13_1208361_1048920
  · exact context_13_1208362_1048938
  · exact context_13_1208363_1048939

theorem selected_cut_38802 : selected 8 ⟨1048976, by decide⟩
    (prefixPartial 13 1208364) = some ⟨13, 2, 0, 1048976, 1208364, 1677, 16384⟩ := by
  decide +kernel

theorem context_13_1208364_1048976 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1208364 ⟨1048976, by decide⟩ :=
  accepted_of_selected 13 1208364 ⟨1048976, by decide⟩ ⟨13, 2, 0, 1048976, 1208364, 1677, 16384⟩
    (by decide) selected_cut_38802

theorem selected_cut_38803 : selected 8 ⟨1049000, by decide⟩
    (prefixPartial 13 1208365) = some ⟨13, 2, 0, 1049000, 1208365, 1217, 16384⟩ := by
  decide +kernel

theorem context_13_1208365_1049000 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1208365 ⟨1049000, by decide⟩ :=
  accepted_of_selected 13 1208365 ⟨1049000, by decide⟩ ⟨13, 2, 0, 1049000, 1208365, 1217, 16384⟩
    (by decide) selected_cut_38803

theorem selected_cut_38804 : selected 8 ⟨1049027, by decide⟩
    (prefixPartial 13 1208366) = some ⟨13, 2, 0, 1049027, 1208366, 1117, 16384⟩ := by
  decide +kernel

theorem context_13_1208366_1049027 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1208366 ⟨1049027, by decide⟩ :=
  accepted_of_selected 13 1208366 ⟨1049027, by decide⟩ ⟨13, 2, 0, 1049027, 1208366, 1117, 16384⟩
    (by decide) selected_cut_38804

theorem selected_cut_38805 : selected 8 ⟨1049037, by decide⟩
    (prefixPartial 13 1208367) = some ⟨13, 2, 0, 1049037, 1208367, 621, 16384⟩ := by
  decide +kernel

theorem context_13_1208367_1049037 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1208367 ⟨1049037, by decide⟩ :=
  accepted_of_selected 13 1208367 ⟨1049037, by decide⟩ ⟨13, 2, 0, 1049037, 1208367, 621, 16384⟩
    (by decide) selected_cut_38805

theorem unmarked_context_12_302091_1049038 : frontier 9 ⟨1049038, by decide⟩
    (prefixCache 12 302091) (prefixPartial 12 302091) = false := by
  decide +kernel

theorem node_context_12_302091_1049038 : EJMOriginalGlobalDAGData.nodes 9 ⟨1049038, by decide⟩ =
    .split (coordinate 12) (![⟨1048976, by decide⟩,⟨1049000, by decide⟩,⟨1049027, by decide⟩,⟨1049037, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_302091_1049038 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302091 ⟨1049038, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 302091
    ⟨1049038, by decide⟩ (by decide) (![⟨1048976, by decide⟩,⟨1049000, by decide⟩,⟨1049027, by decide⟩,⟨1049037, by decide⟩]) unmarked_context_12_302091_1049038 node_context_12_302091_1049038
  intro a
  fin_cases a
  · exact context_13_1208364_1048976
  · exact context_13_1208365_1049000
  · exact context_13_1208366_1049027
  · exact context_13_1208367_1049037

theorem unmarked_context_11_75522_1049039 : frontier 10 ⟨1049039, by decide⟩
    (prefixCache 11 75522) (prefixPartial 11 75522) = false := by
  decide +kernel

theorem node_context_11_75522_1049039 : EJMOriginalGlobalDAGData.nodes 10 ⟨1049039, by decide⟩ =
    .split (coordinate 11) (![⟨450498, by decide⟩,⟨1048865, by decide⟩,⟨1048940, by decide⟩,⟨1049038, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75522_1049039 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75522 ⟨1049039, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75522
    ⟨1049039, by decide⟩ (by decide) (![⟨450498, by decide⟩,⟨1048865, by decide⟩,⟨1048940, by decide⟩,⟨1049038, by decide⟩]) unmarked_context_11_75522_1049039 node_context_11_75522_1049039
  intro a
  fin_cases a
  · exact context_12_302088_450498
  · exact context_12_302089_1048865
  · exact context_12_302090_1048940
  · exact context_12_302091_1049038

theorem selected_cut_38806 : selected 9 ⟨1049108, by decide⟩
    (prefixPartial 12 302092) = some ⟨12, 2, 0, 1049108, 302092, 3861, 65536⟩ := by
  decide +kernel

theorem context_12_302092_1049108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302092 ⟨1049108, by decide⟩ :=
  accepted_of_selected 12 302092 ⟨1049108, by decide⟩ ⟨12, 2, 0, 1049108, 302092, 3861, 65536⟩
    (by decide) selected_cut_38806

theorem selected_cut_38807 : selected 8 ⟨1049154, by decide⟩
    (prefixPartial 13 1208372) = some ⟨13, 2, 0, 1049154, 1208372, 1845, 16384⟩ := by
  decide +kernel

theorem context_13_1208372_1049154 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1208372 ⟨1049154, by decide⟩ :=
  accepted_of_selected 13 1208372 ⟨1049154, by decide⟩ ⟨13, 2, 0, 1049154, 1208372, 1845, 16384⟩
    (by decide) selected_cut_38807

theorem selected_cut_38808 : selected 8 ⟨1049173, by decide⟩
    (prefixPartial 13 1208373) = some ⟨13, 2, 0, 1049173, 1208373, 1101, 16384⟩ := by
  decide +kernel

theorem context_13_1208373_1049173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1208373 ⟨1049173, by decide⟩ :=
  accepted_of_selected 13 1208373 ⟨1049173, by decide⟩ ⟨13, 2, 0, 1049173, 1208373, 1101, 16384⟩
    (by decide) selected_cut_38808

theorem selected_cut_38809 : selected 8 ⟨1049198, by decide⟩
    (prefixPartial 13 1208374) = some ⟨13, 2, 0, 1049198, 1208374, 1101, 16384⟩ := by
  decide +kernel

theorem context_13_1208374_1049198 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1208374 ⟨1049198, by decide⟩ :=
  accepted_of_selected 13 1208374 ⟨1049198, by decide⟩ ⟨13, 2, 0, 1049198, 1208374, 1101, 16384⟩
    (by decide) selected_cut_38809

theorem selected_cut_38810 : selected 8 ⟨1049206, by decide⟩
    (prefixPartial 13 1208375) = some ⟨13, 2, 0, 1049206, 1208375, 581, 16384⟩ := by
  decide +kernel

theorem context_13_1208375_1049206 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1208375 ⟨1049206, by decide⟩ :=
  accepted_of_selected 13 1208375 ⟨1049206, by decide⟩ ⟨13, 2, 0, 1049206, 1208375, 581, 16384⟩
    (by decide) selected_cut_38810

theorem unmarked_context_12_302093_1049207 : frontier 9 ⟨1049207, by decide⟩
    (prefixCache 12 302093) (prefixPartial 12 302093) = false := by
  decide +kernel

theorem node_context_12_302093_1049207 : EJMOriginalGlobalDAGData.nodes 9 ⟨1049207, by decide⟩ =
    .split (coordinate 12) (![⟨1049154, by decide⟩,⟨1049173, by decide⟩,⟨1049198, by decide⟩,⟨1049206, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_302093_1049207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302093 ⟨1049207, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 302093
    ⟨1049207, by decide⟩ (by decide) (![⟨1049154, by decide⟩,⟨1049173, by decide⟩,⟨1049198, by decide⟩,⟨1049206, by decide⟩]) unmarked_context_12_302093_1049207 node_context_12_302093_1049207
  intro a
  fin_cases a
  · exact context_13_1208372_1049154
  · exact context_13_1208373_1049173
  · exact context_13_1208374_1049198
  · exact context_13_1208375_1049206

theorem selected_cut_38811 : selected 8 ⟨1049241, by decide⟩
    (prefixPartial 13 1208376) = some ⟨13, 2, 0, 1049241, 1208376, 1541, 16384⟩ := by
  decide +kernel

theorem context_13_1208376_1049241 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1208376 ⟨1049241, by decide⟩ :=
  accepted_of_selected 13 1208376 ⟨1049241, by decide⟩ ⟨13, 2, 0, 1049241, 1208376, 1541, 16384⟩
    (by decide) selected_cut_38811

theorem selected_cut_38812 : selected 8 ⟨1049258, by decide⟩
    (prefixPartial 13 1208377) = some ⟨13, 2, 0, 1049258, 1208377, 1101, 16384⟩ := by
  decide +kernel

theorem context_13_1208377_1049258 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1208377 ⟨1049258, by decide⟩ :=
  accepted_of_selected 13 1208377 ⟨1049258, by decide⟩ ⟨13, 2, 0, 1049258, 1208377, 1101, 16384⟩
    (by decide) selected_cut_38812

theorem selected_cut_38813 : selected 8 ⟨1049276, by decide⟩
    (prefixPartial 13 1208378) = some ⟨13, 2, 0, 1049276, 1208378, 941, 16384⟩ := by
  decide +kernel

theorem context_13_1208378_1049276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1208378 ⟨1049276, by decide⟩ :=
  accepted_of_selected 13 1208378 ⟨1049276, by decide⟩ ⟨13, 2, 0, 1049276, 1208378, 941, 16384⟩
    (by decide) selected_cut_38813

theorem selected_cut_38814 : selected 8 ⟨1049283, by decide⟩
    (prefixPartial 13 1208379) = some ⟨13, 2, 0, 1049283, 1208379, 589, 16384⟩ := by
  decide +kernel

theorem context_13_1208379_1049283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1208379 ⟨1049283, by decide⟩ :=
  accepted_of_selected 13 1208379 ⟨1049283, by decide⟩ ⟨13, 2, 0, 1049283, 1208379, 589, 16384⟩
    (by decide) selected_cut_38814

theorem unmarked_context_12_302094_1049284 : frontier 9 ⟨1049284, by decide⟩
    (prefixCache 12 302094) (prefixPartial 12 302094) = false := by
  decide +kernel

theorem node_context_12_302094_1049284 : EJMOriginalGlobalDAGData.nodes 9 ⟨1049284, by decide⟩ =
    .split (coordinate 12) (![⟨1049241, by decide⟩,⟨1049258, by decide⟩,⟨1049276, by decide⟩,⟨1049283, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_302094_1049284 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302094 ⟨1049284, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 302094
    ⟨1049284, by decide⟩ (by decide) (![⟨1049241, by decide⟩,⟨1049258, by decide⟩,⟨1049276, by decide⟩,⟨1049283, by decide⟩]) unmarked_context_12_302094_1049284 node_context_12_302094_1049284
  intro a
  fin_cases a
  · exact context_13_1208376_1049241
  · exact context_13_1208377_1049258
  · exact context_13_1208378_1049276
  · exact context_13_1208379_1049283

theorem selected_cut_38815 : selected 9 ⟨1049353, by decide⟩
    (prefixPartial 12 302095) = some ⟨12, 2, 0, 1049353, 302095, 3949, 65536⟩ := by
  decide +kernel

theorem context_12_302095_1049353 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302095 ⟨1049353, by decide⟩ :=
  accepted_of_selected 12 302095 ⟨1049353, by decide⟩ ⟨12, 2, 0, 1049353, 302095, 3949, 65536⟩
    (by decide) selected_cut_38815

theorem unmarked_context_11_75523_1049354 : frontier 10 ⟨1049354, by decide⟩
    (prefixCache 11 75523) (prefixPartial 11 75523) = false := by
  decide +kernel

theorem node_context_11_75523_1049354 : EJMOriginalGlobalDAGData.nodes 10 ⟨1049354, by decide⟩ =
    .split (coordinate 11) (![⟨1049108, by decide⟩,⟨1049207, by decide⟩,⟨1049284, by decide⟩,⟨1049353, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75523_1049354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75523 ⟨1049354, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75523
    ⟨1049354, by decide⟩ (by decide) (![⟨1049108, by decide⟩,⟨1049207, by decide⟩,⟨1049284, by decide⟩,⟨1049353, by decide⟩]) unmarked_context_11_75523_1049354 node_context_11_75523_1049354
  intro a
  fin_cases a
  · exact context_12_302092_1049108
  · exact context_12_302093_1049207
  · exact context_12_302094_1049284
  · exact context_12_302095_1049353

theorem unmarked_context_10_18880_1049355 : frontier 11 ⟨1049355, by decide⟩
    (prefixCache 10 18880) (prefixPartial 10 18880) = false := by
  decide +kernel

theorem node_context_10_18880_1049355 : EJMOriginalGlobalDAGData.nodes 11 ⟨1049355, by decide⟩ =
    .split (coordinate 10) (![⟨1048374, by decide⟩,⟨1048762, by decide⟩,⟨1049039, by decide⟩,⟨1049354, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18880_1049355 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18880 ⟨1049355, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18880
    ⟨1049355, by decide⟩ (by decide) (![⟨1048374, by decide⟩,⟨1048762, by decide⟩,⟨1049039, by decide⟩,⟨1049354, by decide⟩]) unmarked_context_10_18880_1049355 node_context_10_18880_1049355
  intro a
  fin_cases a
  · exact context_11_75520_1048374
  · exact context_11_75521_1048762
  · exact context_11_75522_1049039
  · exact context_11_75523_1049354

theorem selected_cut_38816 : selected 9 ⟨985390, by decide⟩
    (prefixPartial 12 302096) = some ⟨12, 1, 0, 985390, 302096, 1, 65536⟩ := by
  decide +kernel

theorem context_12_302096_985390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302096 ⟨985390, by decide⟩ :=
  accepted_of_selected 12 302096 ⟨985390, by decide⟩ ⟨12, 1, 0, 985390, 302096, 1, 65536⟩
    (by decide) selected_cut_38816

theorem selected_cut_38817 : selected 9 ⟨1049425, by decide⟩
    (prefixPartial 12 302097) = some ⟨12, 2, 0, 1049425, 302097, 3417, 65536⟩ := by
  decide +kernel

theorem context_12_302097_1049425 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302097 ⟨1049425, by decide⟩ :=
  accepted_of_selected 12 302097 ⟨1049425, by decide⟩ ⟨12, 2, 0, 1049425, 302097, 3417, 65536⟩
    (by decide) selected_cut_38817

theorem selected_cut_38818 : selected 9 ⟨1049472, by decide⟩
    (prefixPartial 12 302098) = some ⟨12, 2, 0, 1049472, 302098, 2953, 65536⟩ := by
  decide +kernel

theorem context_12_302098_1049472 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302098 ⟨1049472, by decide⟩ :=
  accepted_of_selected 12 302098 ⟨1049472, by decide⟩ ⟨12, 2, 0, 1049472, 302098, 2953, 65536⟩
    (by decide) selected_cut_38818

theorem selected_cut_38819 : selected 9 ⟨1049517, by decide⟩
    (prefixPartial 12 302099) = some ⟨12, 2, 0, 1049517, 302099, 3065, 65536⟩ := by
  decide +kernel

theorem context_12_302099_1049517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302099 ⟨1049517, by decide⟩ :=
  accepted_of_selected 12 302099 ⟨1049517, by decide⟩ ⟨12, 2, 0, 1049517, 302099, 3065, 65536⟩
    (by decide) selected_cut_38819

theorem unmarked_context_11_75524_1049518 : frontier 10 ⟨1049518, by decide⟩
    (prefixCache 11 75524) (prefixPartial 11 75524) = false := by
  decide +kernel

theorem node_context_11_75524_1049518 : EJMOriginalGlobalDAGData.nodes 10 ⟨1049518, by decide⟩ =
    .split (coordinate 11) (![⟨985390, by decide⟩,⟨1049425, by decide⟩,⟨1049472, by decide⟩,⟨1049517, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75524_1049518 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75524 ⟨1049518, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75524
    ⟨1049518, by decide⟩ (by decide) (![⟨985390, by decide⟩,⟨1049425, by decide⟩,⟨1049472, by decide⟩,⟨1049517, by decide⟩]) unmarked_context_11_75524_1049518 node_context_11_75524_1049518
  intro a
  fin_cases a
  · exact context_12_302096_985390
  · exact context_12_302097_1049425
  · exact context_12_302098_1049472
  · exact context_12_302099_1049517

theorem selected_cut_38820 : selected 9 ⟨1049577, by decide⟩
    (prefixPartial 12 302100) = some ⟨12, 2, 0, 1049577, 302100, 3009, 65536⟩ := by
  decide +kernel

theorem context_12_302100_1049577 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302100 ⟨1049577, by decide⟩ :=
  accepted_of_selected 12 302100 ⟨1049577, by decide⟩ ⟨12, 2, 0, 1049577, 302100, 3009, 65536⟩
    (by decide) selected_cut_38820

theorem selected_cut_38821 : selected 9 ⟨1049689, by decide⟩
    (prefixPartial 12 302101) = some ⟨12, 2, 0, 1049689, 302101, 1981, 65536⟩ := by
  decide +kernel

theorem context_12_302101_1049689 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302101 ⟨1049689, by decide⟩ :=
  accepted_of_selected 12 302101 ⟨1049689, by decide⟩ ⟨12, 2, 0, 1049689, 302101, 1981, 65536⟩
    (by decide) selected_cut_38821

theorem selected_cut_38822 : selected 9 ⟨1049740, by decide⟩
    (prefixPartial 12 302102) = some ⟨12, 2, 0, 1049740, 302102, 3137, 65536⟩ := by
  decide +kernel

theorem context_12_302102_1049740 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302102 ⟨1049740, by decide⟩ :=
  accepted_of_selected 12 302102 ⟨1049740, by decide⟩ ⟨12, 2, 0, 1049740, 302102, 3137, 65536⟩
    (by decide) selected_cut_38822

theorem selected_cut_38823 : selected 9 ⟨1049797, by decide⟩
    (prefixPartial 12 302103) = some ⟨12, 2, 0, 1049797, 302103, 3413, 65536⟩ := by
  decide +kernel

theorem context_12_302103_1049797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302103 ⟨1049797, by decide⟩ :=
  accepted_of_selected 12 302103 ⟨1049797, by decide⟩ ⟨12, 2, 0, 1049797, 302103, 3413, 65536⟩
    (by decide) selected_cut_38823

theorem unmarked_context_11_75525_1049798 : frontier 10 ⟨1049798, by decide⟩
    (prefixCache 11 75525) (prefixPartial 11 75525) = false := by
  decide +kernel

theorem node_context_11_75525_1049798 : EJMOriginalGlobalDAGData.nodes 10 ⟨1049798, by decide⟩ =
    .split (coordinate 11) (![⟨1049577, by decide⟩,⟨1049689, by decide⟩,⟨1049740, by decide⟩,⟨1049797, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75525_1049798 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75525 ⟨1049798, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75525
    ⟨1049798, by decide⟩ (by decide) (![⟨1049577, by decide⟩,⟨1049689, by decide⟩,⟨1049740, by decide⟩,⟨1049797, by decide⟩]) unmarked_context_11_75525_1049798 node_context_11_75525_1049798
  intro a
  fin_cases a
  · exact context_12_302100_1049577
  · exact context_12_302101_1049689
  · exact context_12_302102_1049740
  · exact context_12_302103_1049797

theorem selected_cut_38824 : selected 9 ⟨1049846, by decide⟩
    (prefixPartial 12 302104) = some ⟨12, 2, 0, 1049846, 302104, 3069, 65536⟩ := by
  decide +kernel

theorem context_12_302104_1049846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302104 ⟨1049846, by decide⟩ :=
  accepted_of_selected 12 302104 ⟨1049846, by decide⟩ ⟨12, 2, 0, 1049846, 302104, 3069, 65536⟩
    (by decide) selected_cut_38824

theorem selected_cut_38825 : selected 9 ⟨1049915, by decide⟩
    (prefixPartial 12 302105) = some ⟨12, 2, 0, 1049915, 302105, 3705, 65536⟩ := by
  decide +kernel

theorem context_12_302105_1049915 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302105 ⟨1049915, by decide⟩ :=
  accepted_of_selected 12 302105 ⟨1049915, by decide⟩ ⟨12, 2, 0, 1049915, 302105, 3705, 65536⟩
    (by decide) selected_cut_38825

theorem selected_cut_38826 : selected 9 ⟨1049965, by decide⟩
    (prefixPartial 12 302106) = some ⟨12, 2, 0, 1049965, 302106, 3145, 65536⟩ := by
  decide +kernel

theorem context_12_302106_1049965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302106 ⟨1049965, by decide⟩ :=
  accepted_of_selected 12 302106 ⟨1049965, by decide⟩ ⟨12, 2, 0, 1049965, 302106, 3145, 65536⟩
    (by decide) selected_cut_38826

theorem selected_cut_38827 : selected 9 ⟨1050036, by decide⟩
    (prefixPartial 12 302107) = some ⟨12, 2, 0, 1050036, 302107, 3697, 65536⟩ := by
  decide +kernel

theorem context_12_302107_1050036 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302107 ⟨1050036, by decide⟩ :=
  accepted_of_selected 12 302107 ⟨1050036, by decide⟩ ⟨12, 2, 0, 1050036, 302107, 3697, 65536⟩
    (by decide) selected_cut_38827

theorem unmarked_context_11_75526_1050037 : frontier 10 ⟨1050037, by decide⟩
    (prefixCache 11 75526) (prefixPartial 11 75526) = false := by
  decide +kernel

theorem node_context_11_75526_1050037 : EJMOriginalGlobalDAGData.nodes 10 ⟨1050037, by decide⟩ =
    .split (coordinate 11) (![⟨1049846, by decide⟩,⟨1049915, by decide⟩,⟨1049965, by decide⟩,⟨1050036, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75526_1050037 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75526 ⟨1050037, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75526
    ⟨1050037, by decide⟩ (by decide) (![⟨1049846, by decide⟩,⟨1049915, by decide⟩,⟨1049965, by decide⟩,⟨1050036, by decide⟩]) unmarked_context_11_75526_1050037 node_context_11_75526_1050037
  intro a
  fin_cases a
  · exact context_12_302104_1049846
  · exact context_12_302105_1049915
  · exact context_12_302106_1049965
  · exact context_12_302107_1050036

theorem selected_cut_38828 : selected 9 ⟨1050083, by decide⟩
    (prefixPartial 12 302108) = some ⟨12, 2, 0, 1050083, 302108, 2953, 65536⟩ := by
  decide +kernel

theorem context_12_302108_1050083 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302108 ⟨1050083, by decide⟩ :=
  accepted_of_selected 12 302108 ⟨1050083, by decide⟩ ⟨12, 2, 0, 1050083, 302108, 2953, 65536⟩
    (by decide) selected_cut_38828

theorem selected_cut_38829 : selected 9 ⟨1050152, by decide⟩
    (prefixPartial 12 302109) = some ⟨12, 2, 0, 1050152, 302109, 3681, 65536⟩ := by
  decide +kernel

theorem context_12_302109_1050152 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302109 ⟨1050152, by decide⟩ :=
  accepted_of_selected 12 302109 ⟨1050152, by decide⟩ ⟨12, 2, 0, 1050152, 302109, 3681, 65536⟩
    (by decide) selected_cut_38829

theorem selected_cut_38830 : selected 9 ⟨1050217, by decide⟩
    (prefixPartial 12 302110) = some ⟨12, 2, 0, 1050217, 302110, 3373, 65536⟩ := by
  decide +kernel

theorem context_12_302110_1050217 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302110 ⟨1050217, by decide⟩ :=
  accepted_of_selected 12 302110 ⟨1050217, by decide⟩ ⟨12, 2, 0, 1050217, 302110, 3373, 65536⟩
    (by decide) selected_cut_38830

theorem selected_cut_38831 : selected 9 ⟨1050282, by decide⟩
    (prefixPartial 12 302111) = some ⟨12, 2, 0, 1050282, 302111, 3405, 65536⟩ := by
  decide +kernel

theorem context_12_302111_1050282 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302111 ⟨1050282, by decide⟩ :=
  accepted_of_selected 12 302111 ⟨1050282, by decide⟩ ⟨12, 2, 0, 1050282, 302111, 3405, 65536⟩
    (by decide) selected_cut_38831

theorem unmarked_context_11_75527_1050283 : frontier 10 ⟨1050283, by decide⟩
    (prefixCache 11 75527) (prefixPartial 11 75527) = false := by
  decide +kernel

theorem node_context_11_75527_1050283 : EJMOriginalGlobalDAGData.nodes 10 ⟨1050283, by decide⟩ =
    .split (coordinate 11) (![⟨1050083, by decide⟩,⟨1050152, by decide⟩,⟨1050217, by decide⟩,⟨1050282, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75527_1050283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75527 ⟨1050283, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75527
    ⟨1050283, by decide⟩ (by decide) (![⟨1050083, by decide⟩,⟨1050152, by decide⟩,⟨1050217, by decide⟩,⟨1050282, by decide⟩]) unmarked_context_11_75527_1050283 node_context_11_75527_1050283
  intro a
  fin_cases a
  · exact context_12_302108_1050083
  · exact context_12_302109_1050152
  · exact context_12_302110_1050217
  · exact context_12_302111_1050282

theorem unmarked_context_10_18881_1050284 : frontier 11 ⟨1050284, by decide⟩
    (prefixCache 10 18881) (prefixPartial 10 18881) = false := by
  decide +kernel

theorem node_context_10_18881_1050284 : EJMOriginalGlobalDAGData.nodes 11 ⟨1050284, by decide⟩ =
    .split (coordinate 10) (![⟨1049518, by decide⟩,⟨1049798, by decide⟩,⟨1050037, by decide⟩,⟨1050283, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18881_1050284 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18881 ⟨1050284, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18881
    ⟨1050284, by decide⟩ (by decide) (![⟨1049518, by decide⟩,⟨1049798, by decide⟩,⟨1050037, by decide⟩,⟨1050283, by decide⟩]) unmarked_context_10_18881_1050284 node_context_10_18881_1050284
  intro a
  fin_cases a
  · exact context_11_75524_1049518
  · exact context_11_75525_1049798
  · exact context_11_75526_1050037
  · exact context_11_75527_1050283

theorem selected_cut_38832 : selected 9 ⟨985390, by decide⟩
    (prefixPartial 12 302112) = some ⟨12, 1, 0, 985390, 302112, 1, 65536⟩ := by
  decide +kernel

theorem context_12_302112_985390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302112 ⟨985390, by decide⟩ :=
  accepted_of_selected 12 302112 ⟨985390, by decide⟩ ⟨12, 1, 0, 985390, 302112, 1, 65536⟩
    (by decide) selected_cut_38832

theorem selected_cut_38833 : selected 9 ⟨1050349, by decide⟩
    (prefixPartial 12 302113) = some ⟨12, 2, 0, 1050349, 302113, 3473, 65536⟩ := by
  decide +kernel

theorem context_12_302113_1050349 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302113 ⟨1050349, by decide⟩ :=
  accepted_of_selected 12 302113 ⟨1050349, by decide⟩ ⟨12, 2, 0, 1050349, 302113, 3473, 65536⟩
    (by decide) selected_cut_38833

theorem selected_cut_38834 : selected 9 ⟨1050403, by decide⟩
    (prefixPartial 12 302114) = some ⟨12, 2, 0, 1050403, 302114, 3021, 65536⟩ := by
  decide +kernel

theorem context_12_302114_1050403 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302114 ⟨1050403, by decide⟩ :=
  accepted_of_selected 12 302114 ⟨1050403, by decide⟩ ⟨12, 2, 0, 1050403, 302114, 3021, 65536⟩
    (by decide) selected_cut_38834

theorem selected_cut_38835 : selected 9 ⟨1050455, by decide⟩
    (prefixPartial 12 302115) = some ⟨12, 2, 0, 1050455, 302115, 3145, 65536⟩ := by
  decide +kernel

theorem context_12_302115_1050455 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302115 ⟨1050455, by decide⟩ :=
  accepted_of_selected 12 302115 ⟨1050455, by decide⟩ ⟨12, 2, 0, 1050455, 302115, 3145, 65536⟩
    (by decide) selected_cut_38835

theorem unmarked_context_11_75528_1050456 : frontier 10 ⟨1050456, by decide⟩
    (prefixCache 11 75528) (prefixPartial 11 75528) = false := by
  decide +kernel

theorem node_context_11_75528_1050456 : EJMOriginalGlobalDAGData.nodes 10 ⟨1050456, by decide⟩ =
    .split (coordinate 11) (![⟨985390, by decide⟩,⟨1050349, by decide⟩,⟨1050403, by decide⟩,⟨1050455, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75528_1050456 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75528 ⟨1050456, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75528
    ⟨1050456, by decide⟩ (by decide) (![⟨985390, by decide⟩,⟨1050349, by decide⟩,⟨1050403, by decide⟩,⟨1050455, by decide⟩]) unmarked_context_11_75528_1050456 node_context_11_75528_1050456
  intro a
  fin_cases a
  · exact context_12_302112_985390
  · exact context_12_302113_1050349
  · exact context_12_302114_1050403
  · exact context_12_302115_1050455

theorem selected_cut_38836 : selected 9 ⟨1050514, by decide⟩
    (prefixPartial 12 302116) = some ⟨12, 2, 0, 1050514, 302116, 3185, 65536⟩ := by
  decide +kernel

theorem context_12_302116_1050514 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302116 ⟨1050514, by decide⟩ :=
  accepted_of_selected 12 302116 ⟨1050514, by decide⟩ ⟨12, 2, 0, 1050514, 302116, 3185, 65536⟩
    (by decide) selected_cut_38836

theorem selected_cut_38837 : selected 9 ⟨1050578, by decide⟩
    (prefixPartial 12 302117) = some ⟨12, 2, 0, 1050578, 302117, 3557, 65536⟩ := by
  decide +kernel

theorem context_12_302117_1050578 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302117 ⟨1050578, by decide⟩ :=
  accepted_of_selected 12 302117 ⟨1050578, by decide⟩ ⟨12, 2, 0, 1050578, 302117, 3557, 65536⟩
    (by decide) selected_cut_38837

theorem selected_cut_38838 : selected 9 ⟨1050637, by decide⟩
    (prefixPartial 12 302118) = some ⟨12, 2, 0, 1050637, 302118, 3229, 65536⟩ := by
  decide +kernel

theorem context_12_302118_1050637 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302118 ⟨1050637, by decide⟩ :=
  accepted_of_selected 12 302118 ⟨1050637, by decide⟩ ⟨12, 2, 0, 1050637, 302118, 3229, 65536⟩
    (by decide) selected_cut_38838

theorem selected_cut_38839 : selected 9 ⟨1050708, by decide⟩
    (prefixPartial 12 302119) = some ⟨12, 2, 0, 1050708, 302119, 3641, 65536⟩ := by
  decide +kernel

theorem context_12_302119_1050708 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302119 ⟨1050708, by decide⟩ :=
  accepted_of_selected 12 302119 ⟨1050708, by decide⟩ ⟨12, 2, 0, 1050708, 302119, 3641, 65536⟩
    (by decide) selected_cut_38839

theorem unmarked_context_11_75529_1050709 : frontier 10 ⟨1050709, by decide⟩
    (prefixCache 11 75529) (prefixPartial 11 75529) = false := by
  decide +kernel

theorem node_context_11_75529_1050709 : EJMOriginalGlobalDAGData.nodes 10 ⟨1050709, by decide⟩ =
    .split (coordinate 11) (![⟨1050514, by decide⟩,⟨1050578, by decide⟩,⟨1050637, by decide⟩,⟨1050708, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75529_1050709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75529 ⟨1050709, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75529
    ⟨1050709, by decide⟩ (by decide) (![⟨1050514, by decide⟩,⟨1050578, by decide⟩,⟨1050637, by decide⟩,⟨1050708, by decide⟩]) unmarked_context_11_75529_1050709 node_context_11_75529_1050709
  intro a
  fin_cases a
  · exact context_12_302116_1050514
  · exact context_12_302117_1050578
  · exact context_12_302118_1050637
  · exact context_12_302119_1050708

theorem selected_cut_38840 : selected 9 ⟨1050766, by decide⟩
    (prefixPartial 12 302120) = some ⟨12, 2, 0, 1050766, 302120, 3165, 65536⟩ := by
  decide +kernel

theorem context_12_302120_1050766 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302120 ⟨1050766, by decide⟩ :=
  accepted_of_selected 12 302120 ⟨1050766, by decide⟩ ⟨12, 2, 0, 1050766, 302120, 3165, 65536⟩
    (by decide) selected_cut_38840

theorem selected_cut_38841 : selected 9 ⟨1050837, by decide⟩
    (prefixPartial 12 302121) = some ⟨12, 2, 0, 1050837, 302121, 3753, 65536⟩ := by
  decide +kernel

theorem context_12_302121_1050837 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302121 ⟨1050837, by decide⟩ :=
  accepted_of_selected 12 302121 ⟨1050837, by decide⟩ ⟨12, 2, 0, 1050837, 302121, 3753, 65536⟩
    (by decide) selected_cut_38841

theorem selected_cut_38842 : selected 9 ⟨595504, by decide⟩
    (prefixPartial 12 302122) = some ⟨12, 1, 0, 595504, 302122, 1, 65536⟩ := by
  decide +kernel

theorem context_12_302122_595504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302122 ⟨595504, by decide⟩ :=
  accepted_of_selected 12 302122 ⟨595504, by decide⟩ ⟨12, 1, 0, 595504, 302122, 1, 65536⟩
    (by decide) selected_cut_38842

theorem selected_cut_38843 : selected 9 ⟨1050910, by decide⟩
    (prefixPartial 12 302123) = some ⟨12, 2, 0, 1050910, 302123, 3857, 65536⟩ := by
  decide +kernel

theorem context_12_302123_1050910 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302123 ⟨1050910, by decide⟩ :=
  accepted_of_selected 12 302123 ⟨1050910, by decide⟩ ⟨12, 2, 0, 1050910, 302123, 3857, 65536⟩
    (by decide) selected_cut_38843

theorem unmarked_context_11_75530_1050911 : frontier 10 ⟨1050911, by decide⟩
    (prefixCache 11 75530) (prefixPartial 11 75530) = false := by
  decide +kernel

theorem node_context_11_75530_1050911 : EJMOriginalGlobalDAGData.nodes 10 ⟨1050911, by decide⟩ =
    .split (coordinate 11) (![⟨1050766, by decide⟩,⟨1050837, by decide⟩,⟨595504, by decide⟩,⟨1050910, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75530_1050911 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75530 ⟨1050911, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75530
    ⟨1050911, by decide⟩ (by decide) (![⟨1050766, by decide⟩,⟨1050837, by decide⟩,⟨595504, by decide⟩,⟨1050910, by decide⟩]) unmarked_context_11_75530_1050911 node_context_11_75530_1050911
  intro a
  fin_cases a
  · exact context_12_302120_1050766
  · exact context_12_302121_1050837
  · exact context_12_302122_595504
  · exact context_12_302123_1050910

theorem selected_cut_38844 : selected 9 ⟨1050964, by decide⟩
    (prefixPartial 12 302124) = some ⟨12, 2, 0, 1050964, 302124, 2949, 65536⟩ := by
  decide +kernel

theorem context_12_302124_1050964 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302124 ⟨1050964, by decide⟩ :=
  accepted_of_selected 12 302124 ⟨1050964, by decide⟩ ⟨12, 2, 0, 1050964, 302124, 2949, 65536⟩
    (by decide) selected_cut_38844

theorem selected_cut_38845 : selected 9 ⟨1051023, by decide⟩
    (prefixPartial 12 302125) = some ⟨12, 2, 0, 1051023, 302125, 3525, 65536⟩ := by
  decide +kernel

theorem context_12_302125_1051023 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302125 ⟨1051023, by decide⟩ :=
  accepted_of_selected 12 302125 ⟨1051023, by decide⟩ ⟨12, 2, 0, 1051023, 302125, 3525, 65536⟩
    (by decide) selected_cut_38845

theorem selected_cut_38846 : selected 9 ⟨1051080, by decide⟩
    (prefixPartial 12 302126) = some ⟨12, 2, 0, 1051080, 302126, 3293, 65536⟩ := by
  decide +kernel

theorem context_12_302126_1051080 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302126 ⟨1051080, by decide⟩ :=
  accepted_of_selected 12 302126 ⟨1051080, by decide⟩ ⟨12, 2, 0, 1051080, 302126, 3293, 65536⟩
    (by decide) selected_cut_38846

theorem selected_cut_38847 : selected 9 ⟨1051134, by decide⟩
    (prefixPartial 12 302127) = some ⟨12, 2, 0, 1051134, 302127, 3369, 65536⟩ := by
  decide +kernel

theorem context_12_302127_1051134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302127 ⟨1051134, by decide⟩ :=
  accepted_of_selected 12 302127 ⟨1051134, by decide⟩ ⟨12, 2, 0, 1051134, 302127, 3369, 65536⟩
    (by decide) selected_cut_38847

theorem unmarked_context_11_75531_1051135 : frontier 10 ⟨1051135, by decide⟩
    (prefixCache 11 75531) (prefixPartial 11 75531) = false := by
  decide +kernel

theorem node_context_11_75531_1051135 : EJMOriginalGlobalDAGData.nodes 10 ⟨1051135, by decide⟩ =
    .split (coordinate 11) (![⟨1050964, by decide⟩,⟨1051023, by decide⟩,⟨1051080, by decide⟩,⟨1051134, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75531_1051135 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75531 ⟨1051135, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75531
    ⟨1051135, by decide⟩ (by decide) (![⟨1050964, by decide⟩,⟨1051023, by decide⟩,⟨1051080, by decide⟩,⟨1051134, by decide⟩]) unmarked_context_11_75531_1051135 node_context_11_75531_1051135
  intro a
  fin_cases a
  · exact context_12_302124_1050964
  · exact context_12_302125_1051023
  · exact context_12_302126_1051080
  · exact context_12_302127_1051134

theorem unmarked_context_10_18882_1051136 : frontier 11 ⟨1051136, by decide⟩
    (prefixCache 10 18882) (prefixPartial 10 18882) = false := by
  decide +kernel

theorem node_context_10_18882_1051136 : EJMOriginalGlobalDAGData.nodes 11 ⟨1051136, by decide⟩ =
    .split (coordinate 10) (![⟨1050456, by decide⟩,⟨1050709, by decide⟩,⟨1050911, by decide⟩,⟨1051135, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18882_1051136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18882 ⟨1051136, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18882
    ⟨1051136, by decide⟩ (by decide) (![⟨1050456, by decide⟩,⟨1050709, by decide⟩,⟨1050911, by decide⟩,⟨1051135, by decide⟩]) unmarked_context_10_18882_1051136 node_context_10_18882_1051136
  intro a
  fin_cases a
  · exact context_11_75528_1050456
  · exact context_11_75529_1050709
  · exact context_11_75530_1050911
  · exact context_11_75531_1051135

theorem selected_cut_38848 : selected 9 ⟨985390, by decide⟩
    (prefixPartial 12 302128) = some ⟨12, 1, 0, 985390, 302128, 1, 65536⟩ := by
  decide +kernel

theorem context_12_302128_985390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302128 ⟨985390, by decide⟩ :=
  accepted_of_selected 12 302128 ⟨985390, by decide⟩ ⟨12, 1, 0, 985390, 302128, 1, 65536⟩
    (by decide) selected_cut_38848

theorem selected_cut_38849 : selected 9 ⟨1051188, by decide⟩
    (prefixPartial 12 302129) = some ⟨12, 2, 0, 1051188, 302129, 3049, 65536⟩ := by
  decide +kernel

theorem context_12_302129_1051188 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302129 ⟨1051188, by decide⟩ :=
  accepted_of_selected 12 302129 ⟨1051188, by decide⟩ ⟨12, 2, 0, 1051188, 302129, 3049, 65536⟩
    (by decide) selected_cut_38849

theorem selected_cut_38850 : selected 9 ⟨1051229, by decide⟩
    (prefixPartial 12 302130) = some ⟨12, 2, 0, 1051229, 302130, 2537, 65536⟩ := by
  decide +kernel

theorem context_12_302130_1051229 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302130 ⟨1051229, by decide⟩ :=
  accepted_of_selected 12 302130 ⟨1051229, by decide⟩ ⟨12, 2, 0, 1051229, 302130, 2537, 65536⟩
    (by decide) selected_cut_38850

theorem selected_cut_38851 : selected 9 ⟨1051277, by decide⟩
    (prefixPartial 12 302131) = some ⟨12, 2, 0, 1051277, 302131, 2769, 65536⟩ := by
  decide +kernel

theorem context_12_302131_1051277 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302131 ⟨1051277, by decide⟩ :=
  accepted_of_selected 12 302131 ⟨1051277, by decide⟩ ⟨12, 2, 0, 1051277, 302131, 2769, 65536⟩
    (by decide) selected_cut_38851

theorem unmarked_context_11_75532_1051278 : frontier 10 ⟨1051278, by decide⟩
    (prefixCache 11 75532) (prefixPartial 11 75532) = false := by
  decide +kernel

theorem node_context_11_75532_1051278 : EJMOriginalGlobalDAGData.nodes 10 ⟨1051278, by decide⟩ =
    .split (coordinate 11) (![⟨985390, by decide⟩,⟨1051188, by decide⟩,⟨1051229, by decide⟩,⟨1051277, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75532_1051278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75532 ⟨1051278, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75532
    ⟨1051278, by decide⟩ (by decide) (![⟨985390, by decide⟩,⟨1051188, by decide⟩,⟨1051229, by decide⟩,⟨1051277, by decide⟩]) unmarked_context_11_75532_1051278 node_context_11_75532_1051278
  intro a
  fin_cases a
  · exact context_12_302128_985390
  · exact context_12_302129_1051188
  · exact context_12_302130_1051229
  · exact context_12_302131_1051277

theorem selected_cut_38852 : selected 9 ⟨1051335, by decide⟩
    (prefixPartial 12 302132) = some ⟨12, 2, 0, 1051335, 302132, 2909, 65536⟩ := by
  decide +kernel

theorem context_12_302132_1051335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302132 ⟨1051335, by decide⟩ :=
  accepted_of_selected 12 302132 ⟨1051335, by decide⟩ ⟨12, 2, 0, 1051335, 302132, 2909, 65536⟩
    (by decide) selected_cut_38852

theorem selected_cut_38853 : selected 9 ⟨1051387, by decide⟩
    (prefixPartial 12 302133) = some ⟨12, 2, 0, 1051387, 302133, 3257, 65536⟩ := by
  decide +kernel

theorem context_12_302133_1051387 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302133 ⟨1051387, by decide⟩ :=
  accepted_of_selected 12 302133 ⟨1051387, by decide⟩ ⟨12, 2, 0, 1051387, 302133, 3257, 65536⟩
    (by decide) selected_cut_38853

theorem selected_cut_38854 : selected 9 ⟨1051433, by decide⟩
    (prefixPartial 12 302134) = some ⟨12, 2, 0, 1051433, 302134, 3009, 65536⟩ := by
  decide +kernel

theorem context_12_302134_1051433 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302134 ⟨1051433, by decide⟩ :=
  accepted_of_selected 12 302134 ⟨1051433, by decide⟩ ⟨12, 2, 0, 1051433, 302134, 3009, 65536⟩
    (by decide) selected_cut_38854

theorem selected_cut_38855 : selected 9 ⟨1051491, by decide⟩
    (prefixPartial 12 302135) = some ⟨12, 2, 0, 1051491, 302135, 3281, 65536⟩ := by
  decide +kernel

theorem context_12_302135_1051491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302135 ⟨1051491, by decide⟩ :=
  accepted_of_selected 12 302135 ⟨1051491, by decide⟩ ⟨12, 2, 0, 1051491, 302135, 3281, 65536⟩
    (by decide) selected_cut_38855

theorem unmarked_context_11_75533_1051492 : frontier 10 ⟨1051492, by decide⟩
    (prefixCache 11 75533) (prefixPartial 11 75533) = false := by
  decide +kernel

theorem node_context_11_75533_1051492 : EJMOriginalGlobalDAGData.nodes 10 ⟨1051492, by decide⟩ =
    .split (coordinate 11) (![⟨1051335, by decide⟩,⟨1051387, by decide⟩,⟨1051433, by decide⟩,⟨1051491, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75533_1051492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75533 ⟨1051492, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75533
    ⟨1051492, by decide⟩ (by decide) (![⟨1051335, by decide⟩,⟨1051387, by decide⟩,⟨1051433, by decide⟩,⟨1051491, by decide⟩]) unmarked_context_11_75533_1051492 node_context_11_75533_1051492
  intro a
  fin_cases a
  · exact context_12_302132_1051335
  · exact context_12_302133_1051387
  · exact context_12_302134_1051433
  · exact context_12_302135_1051491

theorem selected_cut_38856 : selected 9 ⟨1051529, by decide⟩
    (prefixPartial 12 302136) = some ⟨12, 2, 0, 1051529, 302136, 2573, 65536⟩ := by
  decide +kernel

theorem context_12_302136_1051529 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302136 ⟨1051529, by decide⟩ :=
  accepted_of_selected 12 302136 ⟨1051529, by decide⟩ ⟨12, 2, 0, 1051529, 302136, 2573, 65536⟩
    (by decide) selected_cut_38856

theorem selected_cut_38857 : selected 9 ⟨1051575, by decide⟩
    (prefixPartial 12 302137) = some ⟨12, 2, 0, 1051575, 302137, 3037, 65536⟩ := by
  decide +kernel

theorem context_12_302137_1051575 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302137 ⟨1051575, by decide⟩ :=
  accepted_of_selected 12 302137 ⟨1051575, by decide⟩ ⟨12, 2, 0, 1051575, 302137, 3037, 65536⟩
    (by decide) selected_cut_38857

theorem selected_cut_38858 : selected 9 ⟨1051619, by decide⟩
    (prefixPartial 12 302138) = some ⟨12, 2, 0, 1051619, 302138, 2641, 65536⟩ := by
  decide +kernel

theorem context_12_302138_1051619 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302138 ⟨1051619, by decide⟩ :=
  accepted_of_selected 12 302138 ⟨1051619, by decide⟩ ⟨12, 2, 0, 1051619, 302138, 2641, 65536⟩
    (by decide) selected_cut_38858

theorem selected_cut_38859 : selected 9 ⟨1051677, by decide⟩
    (prefixPartial 12 302139) = some ⟨12, 2, 0, 1051677, 302139, 3065, 65536⟩ := by
  decide +kernel

theorem context_12_302139_1051677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302139 ⟨1051677, by decide⟩ :=
  accepted_of_selected 12 302139 ⟨1051677, by decide⟩ ⟨12, 2, 0, 1051677, 302139, 3065, 65536⟩
    (by decide) selected_cut_38859

theorem unmarked_context_11_75534_1051678 : frontier 10 ⟨1051678, by decide⟩
    (prefixCache 11 75534) (prefixPartial 11 75534) = false := by
  decide +kernel

theorem node_context_11_75534_1051678 : EJMOriginalGlobalDAGData.nodes 10 ⟨1051678, by decide⟩ =
    .split (coordinate 11) (![⟨1051529, by decide⟩,⟨1051575, by decide⟩,⟨1051619, by decide⟩,⟨1051677, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75534_1051678 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75534 ⟨1051678, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75534
    ⟨1051678, by decide⟩ (by decide) (![⟨1051529, by decide⟩,⟨1051575, by decide⟩,⟨1051619, by decide⟩,⟨1051677, by decide⟩]) unmarked_context_11_75534_1051678 node_context_11_75534_1051678
  intro a
  fin_cases a
  · exact context_12_302136_1051529
  · exact context_12_302137_1051575
  · exact context_12_302138_1051619
  · exact context_12_302139_1051677

theorem selected_cut_38860 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 75535) = some ⟨11, 1, 0, 977886, 75535, 1, 262144⟩ := by
  decide +kernel

theorem context_11_75535_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75535 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 75535 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 75535, 1, 262144⟩
    (by decide) selected_cut_38860

theorem unmarked_context_10_18883_1051679 : frontier 11 ⟨1051679, by decide⟩
    (prefixCache 10 18883) (prefixPartial 10 18883) = false := by
  decide +kernel

theorem node_context_10_18883_1051679 : EJMOriginalGlobalDAGData.nodes 11 ⟨1051679, by decide⟩ =
    .split (coordinate 10) (![⟨1051278, by decide⟩,⟨1051492, by decide⟩,⟨1051678, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18883_1051679 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18883 ⟨1051679, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18883
    ⟨1051679, by decide⟩ (by decide) (![⟨1051278, by decide⟩,⟨1051492, by decide⟩,⟨1051678, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_18883_1051679 node_context_10_18883_1051679
  intro a
  fin_cases a
  · exact context_11_75532_1051278
  · exact context_11_75533_1051492
  · exact context_11_75534_1051678
  · exact context_11_75535_977886

theorem unmarked_context_9_4720_1051680 : frontier 12 ⟨1051680, by decide⟩
    (prefixCache 9 4720) (prefixPartial 9 4720) = false := by
  decide +kernel

theorem node_context_9_4720_1051680 : EJMOriginalGlobalDAGData.nodes 12 ⟨1051680, by decide⟩ =
    .split (coordinate 9) (![⟨1049355, by decide⟩,⟨1050284, by decide⟩,⟨1051136, by decide⟩,⟨1051679, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4720_1051680 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4720 ⟨1051680, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4720
    ⟨1051680, by decide⟩ (by decide) (![⟨1049355, by decide⟩,⟨1050284, by decide⟩,⟨1051136, by decide⟩,⟨1051679, by decide⟩]) unmarked_context_9_4720_1051680 node_context_9_4720_1051680
  intro a
  fin_cases a
  · exact context_10_18880_1049355
  · exact context_10_18881_1050284
  · exact context_10_18882_1051136
  · exact context_10_18883_1051679

theorem selected_cut_38861 : selected 9 ⟨1051681, by decide⟩
    (prefixPartial 12 302144) = some ⟨12, 1, 0, 1051681, 302144, 1, 65536⟩ := by
  decide +kernel

theorem context_12_302144_1051681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302144 ⟨1051681, by decide⟩ :=
  accepted_of_selected 12 302144 ⟨1051681, by decide⟩ ⟨12, 1, 0, 1051681, 302144, 1, 65536⟩
    (by decide) selected_cut_38861

theorem selected_cut_38862 : selected 9 ⟨1051723, by decide⟩
    (prefixPartial 12 302145) = some ⟨12, 2, 0, 1051723, 302145, 2305, 65536⟩ := by
  decide +kernel

theorem context_12_302145_1051723 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302145 ⟨1051723, by decide⟩ :=
  accepted_of_selected 12 302145 ⟨1051723, by decide⟩ ⟨12, 2, 0, 1051723, 302145, 2305, 65536⟩
    (by decide) selected_cut_38862

theorem selected_cut_38863 : selected 9 ⟨1051756, by decide⟩
    (prefixPartial 12 302146) = some ⟨12, 2, 0, 1051756, 302146, 2073, 65536⟩ := by
  decide +kernel

theorem context_12_302146_1051756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302146 ⟨1051756, by decide⟩ :=
  accepted_of_selected 12 302146 ⟨1051756, by decide⟩ ⟨12, 2, 0, 1051756, 302146, 2073, 65536⟩
    (by decide) selected_cut_38863

theorem selected_cut_38864 : selected 9 ⟨1051796, by decide⟩
    (prefixPartial 12 302147) = some ⟨12, 2, 0, 1051796, 302147, 2077, 65536⟩ := by
  decide +kernel

theorem context_12_302147_1051796 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302147 ⟨1051796, by decide⟩ :=
  accepted_of_selected 12 302147 ⟨1051796, by decide⟩ ⟨12, 2, 0, 1051796, 302147, 2077, 65536⟩
    (by decide) selected_cut_38864

theorem unmarked_context_11_75536_1051797 : frontier 10 ⟨1051797, by decide⟩
    (prefixCache 11 75536) (prefixPartial 11 75536) = false := by
  decide +kernel

theorem node_context_11_75536_1051797 : EJMOriginalGlobalDAGData.nodes 10 ⟨1051797, by decide⟩ =
    .split (coordinate 11) (![⟨1051681, by decide⟩,⟨1051723, by decide⟩,⟨1051756, by decide⟩,⟨1051796, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75536_1051797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75536 ⟨1051797, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75536
    ⟨1051797, by decide⟩ (by decide) (![⟨1051681, by decide⟩,⟨1051723, by decide⟩,⟨1051756, by decide⟩,⟨1051796, by decide⟩]) unmarked_context_11_75536_1051797 node_context_11_75536_1051797
  intro a
  fin_cases a
  · exact context_12_302144_1051681
  · exact context_12_302145_1051723
  · exact context_12_302146_1051756
  · exact context_12_302147_1051796

theorem selected_cut_38865 : selected 9 ⟨1051851, by decide⟩
    (prefixPartial 12 302148) = some ⟨12, 2, 0, 1051851, 302148, 2373, 65536⟩ := by
  decide +kernel

theorem context_12_302148_1051851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302148 ⟨1051851, by decide⟩ :=
  accepted_of_selected 12 302148 ⟨1051851, by decide⟩ ⟨12, 2, 0, 1051851, 302148, 2373, 65536⟩
    (by decide) selected_cut_38865

theorem selected_cut_38866 : selected 9 ⟨1051906, by decide⟩
    (prefixPartial 12 302149) = some ⟨12, 2, 0, 1051906, 302149, 1257, 65536⟩ := by
  decide +kernel

theorem context_12_302149_1051906 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302149 ⟨1051906, by decide⟩ :=
  accepted_of_selected 12 302149 ⟨1051906, by decide⟩ ⟨12, 2, 0, 1051906, 302149, 1257, 65536⟩
    (by decide) selected_cut_38866

theorem selected_cut_38867 : selected 9 ⟨1051938, by decide⟩
    (prefixPartial 12 302150) = some ⟨12, 2, 0, 1051938, 302150, 2309, 65536⟩ := by
  decide +kernel

theorem context_12_302150_1051938 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302150 ⟨1051938, by decide⟩ :=
  accepted_of_selected 12 302150 ⟨1051938, by decide⟩ ⟨12, 2, 0, 1051938, 302150, 2309, 65536⟩
    (by decide) selected_cut_38867

theorem selected_cut_38868 : selected 9 ⟨1051981, by decide⟩
    (prefixPartial 12 302151) = some ⟨12, 2, 0, 1051981, 302151, 2277, 65536⟩ := by
  decide +kernel

theorem context_12_302151_1051981 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302151 ⟨1051981, by decide⟩ :=
  accepted_of_selected 12 302151 ⟨1051981, by decide⟩ ⟨12, 2, 0, 1051981, 302151, 2277, 65536⟩
    (by decide) selected_cut_38868

theorem unmarked_context_11_75537_1051982 : frontier 10 ⟨1051982, by decide⟩
    (prefixCache 11 75537) (prefixPartial 11 75537) = false := by
  decide +kernel

theorem node_context_11_75537_1051982 : EJMOriginalGlobalDAGData.nodes 10 ⟨1051982, by decide⟩ =
    .split (coordinate 11) (![⟨1051851, by decide⟩,⟨1051906, by decide⟩,⟨1051938, by decide⟩,⟨1051981, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75537_1051982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75537 ⟨1051982, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75537
    ⟨1051982, by decide⟩ (by decide) (![⟨1051851, by decide⟩,⟨1051906, by decide⟩,⟨1051938, by decide⟩,⟨1051981, by decide⟩]) unmarked_context_11_75537_1051982 node_context_11_75537_1051982
  intro a
  fin_cases a
  · exact context_12_302148_1051851
  · exact context_12_302149_1051906
  · exact context_12_302150_1051938
  · exact context_12_302151_1051981

theorem selected_cut_38869 : selected 9 ⟨1052030, by decide⟩
    (prefixPartial 12 302152) = some ⟨12, 2, 0, 1052030, 302152, 2557, 65536⟩ := by
  decide +kernel

theorem context_12_302152_1052030 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302152 ⟨1052030, by decide⟩ :=
  accepted_of_selected 12 302152 ⟨1052030, by decide⟩ ⟨12, 2, 0, 1052030, 302152, 2557, 65536⟩
    (by decide) selected_cut_38869

theorem selected_cut_38870 : selected 9 ⟨1052083, by decide⟩
    (prefixPartial 12 302153) = some ⟨12, 2, 0, 1052083, 302153, 2593, 65536⟩ := by
  decide +kernel

theorem context_12_302153_1052083 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302153 ⟨1052083, by decide⟩ :=
  accepted_of_selected 12 302153 ⟨1052083, by decide⟩ ⟨12, 2, 0, 1052083, 302153, 2593, 65536⟩
    (by decide) selected_cut_38870

theorem selected_cut_38871 : selected 9 ⟨1052126, by decide⟩
    (prefixPartial 12 302154) = some ⟨12, 2, 0, 1052126, 302154, 2465, 65536⟩ := by
  decide +kernel

theorem context_12_302154_1052126 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302154 ⟨1052126, by decide⟩ :=
  accepted_of_selected 12 302154 ⟨1052126, by decide⟩ ⟨12, 2, 0, 1052126, 302154, 2465, 65536⟩
    (by decide) selected_cut_38871

theorem selected_cut_38872 : selected 9 ⟨1052170, by decide⟩
    (prefixPartial 12 302155) = some ⟨12, 2, 0, 1052170, 302155, 2601, 65536⟩ := by
  decide +kernel

theorem context_12_302155_1052170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302155 ⟨1052170, by decide⟩ :=
  accepted_of_selected 12 302155 ⟨1052170, by decide⟩ ⟨12, 2, 0, 1052170, 302155, 2601, 65536⟩
    (by decide) selected_cut_38872

theorem unmarked_context_11_75538_1052171 : frontier 10 ⟨1052171, by decide⟩
    (prefixCache 11 75538) (prefixPartial 11 75538) = false := by
  decide +kernel

theorem node_context_11_75538_1052171 : EJMOriginalGlobalDAGData.nodes 10 ⟨1052171, by decide⟩ =
    .split (coordinate 11) (![⟨1052030, by decide⟩,⟨1052083, by decide⟩,⟨1052126, by decide⟩,⟨1052170, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75538_1052171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75538 ⟨1052171, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75538
    ⟨1052171, by decide⟩ (by decide) (![⟨1052030, by decide⟩,⟨1052083, by decide⟩,⟨1052126, by decide⟩,⟨1052170, by decide⟩]) unmarked_context_11_75538_1052171 node_context_11_75538_1052171
  intro a
  fin_cases a
  · exact context_12_302152_1052030
  · exact context_12_302153_1052083
  · exact context_12_302154_1052126
  · exact context_12_302155_1052170

theorem selected_cut_38873 : selected 9 ⟨1052212, by decide⟩
    (prefixPartial 12 302156) = some ⟨12, 2, 0, 1052212, 302156, 2265, 65536⟩ := by
  decide +kernel

theorem context_12_302156_1052212 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302156 ⟨1052212, by decide⟩ :=
  accepted_of_selected 12 302156 ⟨1052212, by decide⟩ ⟨12, 2, 0, 1052212, 302156, 2265, 65536⟩
    (by decide) selected_cut_38873

theorem selected_cut_38874 : selected 9 ⟨1052250, by decide⟩
    (prefixPartial 12 302157) = some ⟨12, 2, 0, 1052250, 302157, 2257, 65536⟩ := by
  decide +kernel

theorem context_12_302157_1052250 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302157 ⟨1052250, by decide⟩ :=
  accepted_of_selected 12 302157 ⟨1052250, by decide⟩ ⟨12, 2, 0, 1052250, 302157, 2257, 65536⟩
    (by decide) selected_cut_38874

theorem selected_cut_38875 : selected 9 ⟨1052288, by decide⟩
    (prefixPartial 12 302158) = some ⟨12, 2, 0, 1052288, 302158, 2313, 65536⟩ := by
  decide +kernel

theorem context_12_302158_1052288 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302158 ⟨1052288, by decide⟩ :=
  accepted_of_selected 12 302158 ⟨1052288, by decide⟩ ⟨12, 2, 0, 1052288, 302158, 2313, 65536⟩
    (by decide) selected_cut_38875

theorem selected_cut_38876 : selected 9 ⟨1052327, by decide⟩
    (prefixPartial 12 302159) = some ⟨12, 2, 0, 1052327, 302159, 2105, 65536⟩ := by
  decide +kernel

theorem context_12_302159_1052327 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302159 ⟨1052327, by decide⟩ :=
  accepted_of_selected 12 302159 ⟨1052327, by decide⟩ ⟨12, 2, 0, 1052327, 302159, 2105, 65536⟩
    (by decide) selected_cut_38876

theorem unmarked_context_11_75539_1052328 : frontier 10 ⟨1052328, by decide⟩
    (prefixCache 11 75539) (prefixPartial 11 75539) = false := by
  decide +kernel

theorem node_context_11_75539_1052328 : EJMOriginalGlobalDAGData.nodes 10 ⟨1052328, by decide⟩ =
    .split (coordinate 11) (![⟨1052212, by decide⟩,⟨1052250, by decide⟩,⟨1052288, by decide⟩,⟨1052327, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75539_1052328 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75539 ⟨1052328, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75539
    ⟨1052328, by decide⟩ (by decide) (![⟨1052212, by decide⟩,⟨1052250, by decide⟩,⟨1052288, by decide⟩,⟨1052327, by decide⟩]) unmarked_context_11_75539_1052328 node_context_11_75539_1052328
  intro a
  fin_cases a
  · exact context_12_302156_1052212
  · exact context_12_302157_1052250
  · exact context_12_302158_1052288
  · exact context_12_302159_1052327

theorem unmarked_context_10_18884_1052329 : frontier 11 ⟨1052329, by decide⟩
    (prefixCache 10 18884) (prefixPartial 10 18884) = false := by
  decide +kernel

theorem node_context_10_18884_1052329 : EJMOriginalGlobalDAGData.nodes 11 ⟨1052329, by decide⟩ =
    .split (coordinate 10) (![⟨1051797, by decide⟩,⟨1051982, by decide⟩,⟨1052171, by decide⟩,⟨1052328, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18884_1052329 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18884 ⟨1052329, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18884
    ⟨1052329, by decide⟩ (by decide) (![⟨1051797, by decide⟩,⟨1051982, by decide⟩,⟨1052171, by decide⟩,⟨1052328, by decide⟩]) unmarked_context_10_18884_1052329 node_context_10_18884_1052329
  intro a
  fin_cases a
  · exact context_11_75536_1051797
  · exact context_11_75537_1051982
  · exact context_11_75538_1052171
  · exact context_11_75539_1052328

theorem selected_cut_38877 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 18885) = some ⟨10, 1, 0, 893098, 18885, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_18885_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18885 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 18885 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 18885, 1, 1048576⟩
    (by decide) selected_cut_38877

theorem selected_cut_38878 : selected 9 ⟨985390, by decide⟩
    (prefixPartial 12 302176) = some ⟨12, 1, 0, 985390, 302176, 1, 65536⟩ := by
  decide +kernel

theorem context_12_302176_985390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302176 ⟨985390, by decide⟩ :=
  accepted_of_selected 12 302176 ⟨985390, by decide⟩ ⟨12, 1, 0, 985390, 302176, 1, 65536⟩
    (by decide) selected_cut_38878

theorem selected_cut_38879 : selected 9 ⟨1052360, by decide⟩
    (prefixPartial 12 302177) = some ⟨12, 2, 0, 1052360, 302177, 1977, 65536⟩ := by
  decide +kernel

theorem context_12_302177_1052360 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302177 ⟨1052360, by decide⟩ :=
  accepted_of_selected 12 302177 ⟨1052360, by decide⟩ ⟨12, 2, 0, 1052360, 302177, 1977, 65536⟩
    (by decide) selected_cut_38879

theorem selected_cut_38880 : selected 9 ⟨1052387, by decide⟩
    (prefixPartial 12 302178) = some ⟨12, 2, 0, 1052387, 302178, 1733, 65536⟩ := by
  decide +kernel

theorem context_12_302178_1052387 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302178 ⟨1052387, by decide⟩ :=
  accepted_of_selected 12 302178 ⟨1052387, by decide⟩ ⟨12, 2, 0, 1052387, 302178, 1733, 65536⟩
    (by decide) selected_cut_38880

theorem selected_cut_38881 : selected 9 ⟨1052412, by decide⟩
    (prefixPartial 12 302179) = some ⟨12, 2, 0, 1052412, 302179, 1701, 65536⟩ := by
  decide +kernel

theorem context_12_302179_1052412 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302179 ⟨1052412, by decide⟩ :=
  accepted_of_selected 12 302179 ⟨1052412, by decide⟩ ⟨12, 2, 0, 1052412, 302179, 1701, 65536⟩
    (by decide) selected_cut_38881

theorem unmarked_context_11_75544_1052413 : frontier 10 ⟨1052413, by decide⟩
    (prefixCache 11 75544) (prefixPartial 11 75544) = false := by
  decide +kernel

theorem node_context_11_75544_1052413 : EJMOriginalGlobalDAGData.nodes 10 ⟨1052413, by decide⟩ =
    .split (coordinate 11) (![⟨985390, by decide⟩,⟨1052360, by decide⟩,⟨1052387, by decide⟩,⟨1052412, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75544_1052413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75544 ⟨1052413, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75544
    ⟨1052413, by decide⟩ (by decide) (![⟨985390, by decide⟩,⟨1052360, by decide⟩,⟨1052387, by decide⟩,⟨1052412, by decide⟩]) unmarked_context_11_75544_1052413 node_context_11_75544_1052413
  intro a
  fin_cases a
  · exact context_12_302176_985390
  · exact context_12_302177_1052360
  · exact context_12_302178_1052387
  · exact context_12_302179_1052412

theorem selected_cut_38882 : selected 9 ⟨1052439, by decide⟩
    (prefixPartial 12 302180) = some ⟨12, 2, 0, 1052439, 302180, 1865, 65536⟩ := by
  decide +kernel

theorem context_12_302180_1052439 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302180 ⟨1052439, by decide⟩ :=
  accepted_of_selected 12 302180 ⟨1052439, by decide⟩ ⟨12, 2, 0, 1052439, 302180, 1865, 65536⟩
    (by decide) selected_cut_38882

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
