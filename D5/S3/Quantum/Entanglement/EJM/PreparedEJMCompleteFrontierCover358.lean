/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover357
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_34372 : selected 8 ⟨888835, by decide⟩
    (prefixPartial 13 452821) = some ⟨13, 2, 0, 888835, 452821, 2201, 16384⟩ := by
  decide +kernel

theorem context_13_452821_888835 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452821 ⟨888835, by decide⟩ :=
  accepted_of_selected 13 452821 ⟨888835, by decide⟩ ⟨13, 2, 0, 888835, 452821, 2201, 16384⟩
    (by decide) selected_cut_34372

theorem selected_cut_34373 : selected 8 ⟨888852, by decide⟩
    (prefixPartial 13 452822) = some ⟨13, 2, 0, 888852, 452822, 733, 16384⟩ := by
  decide +kernel

theorem context_13_452822_888852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452822 ⟨888852, by decide⟩ :=
  accepted_of_selected 13 452822 ⟨888852, by decide⟩ ⟨13, 2, 0, 888852, 452822, 733, 16384⟩
    (by decide) selected_cut_34373

theorem selected_cut_34374 : selected 8 ⟨888858, by decide⟩
    (prefixPartial 13 452823) = some ⟨13, 2, 0, 888858, 452823, 733, 16384⟩ := by
  decide +kernel

theorem context_13_452823_888858 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 452823 ⟨888858, by decide⟩ :=
  accepted_of_selected 13 452823 ⟨888858, by decide⟩ ⟨13, 2, 0, 888858, 452823, 733, 16384⟩
    (by decide) selected_cut_34374

theorem unmarked_context_12_113205_888859 : frontier 9 ⟨888859, by decide⟩
    (prefixCache 12 113205) (prefixPartial 12 113205) = false := by
  decide +kernel

theorem node_context_12_113205_888859 : EJMOriginalGlobalDAGData.nodes 9 ⟨888859, by decide⟩ =
    .split (coordinate 12) (![⟨888783, by decide⟩,⟨888835, by decide⟩,⟨888852, by decide⟩,⟨888858, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_113205_888859 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113205 ⟨888859, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 113205
    ⟨888859, by decide⟩ (by decide) (![⟨888783, by decide⟩,⟨888835, by decide⟩,⟨888852, by decide⟩,⟨888858, by decide⟩]) unmarked_context_12_113205_888859 node_context_12_113205_888859
  intro a
  fin_cases a
  · exact context_13_452820_888783
  · exact context_13_452821_888835
  · exact context_13_452822_888852
  · exact context_13_452823_888858

theorem selected_cut_34375 : selected 9 ⟨888945, by decide⟩
    (prefixPartial 12 113206) = some ⟨12, 2, 0, 888945, 113206, 3557, 65536⟩ := by
  decide +kernel

theorem context_12_113206_888945 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113206 ⟨888945, by decide⟩ :=
  accepted_of_selected 12 113206 ⟨888945, by decide⟩ ⟨12, 2, 0, 888945, 113206, 3557, 65536⟩
    (by decide) selected_cut_34375

theorem selected_cut_34376 : selected 9 ⟨889027, by decide⟩
    (prefixPartial 12 113207) = some ⟨12, 2, 0, 889027, 113207, 3873, 65536⟩ := by
  decide +kernel

theorem context_12_113207_889027 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113207 ⟨889027, by decide⟩ :=
  accepted_of_selected 12 113207 ⟨889027, by decide⟩ ⟨12, 2, 0, 889027, 113207, 3873, 65536⟩
    (by decide) selected_cut_34376

theorem unmarked_context_11_28301_889028 : frontier 10 ⟨889028, by decide⟩
    (prefixCache 11 28301) (prefixPartial 11 28301) = false := by
  decide +kernel

theorem node_context_11_28301_889028 : EJMOriginalGlobalDAGData.nodes 10 ⟨889028, by decide⟩ =
    .split (coordinate 11) (![⟨888765, by decide⟩,⟨888859, by decide⟩,⟨888945, by decide⟩,⟨889027, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28301_889028 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28301 ⟨889028, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28301
    ⟨889028, by decide⟩ (by decide) (![⟨888765, by decide⟩,⟨888859, by decide⟩,⟨888945, by decide⟩,⟨889027, by decide⟩]) unmarked_context_11_28301_889028 node_context_11_28301_889028
  intro a
  fin_cases a
  · exact context_12_113204_888765
  · exact context_12_113205_888859
  · exact context_12_113206_888945
  · exact context_12_113207_889027

theorem selected_cut_34377 : selected 9 ⟨889097, by decide⟩
    (prefixPartial 12 113208) = some ⟨12, 2, 0, 889097, 113208, 3173, 65536⟩ := by
  decide +kernel

theorem context_12_113208_889097 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113208 ⟨889097, by decide⟩ :=
  accepted_of_selected 12 113208 ⟨889097, by decide⟩ ⟨12, 2, 0, 889097, 113208, 3173, 65536⟩
    (by decide) selected_cut_34377

theorem selected_cut_34378 : selected 9 ⟨889177, by decide⟩
    (prefixPartial 12 113209) = some ⟨12, 2, 0, 889177, 113209, 3741, 65536⟩ := by
  decide +kernel

theorem context_12_113209_889177 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113209 ⟨889177, by decide⟩ :=
  accepted_of_selected 12 113209 ⟨889177, by decide⟩ ⟨12, 2, 0, 889177, 113209, 3741, 65536⟩
    (by decide) selected_cut_34378

theorem selected_cut_34379 : selected 9 ⟨662655, by decide⟩
    (prefixPartial 12 113210) = some ⟨12, 1, 0, 662655, 113210, 1, 65536⟩ := by
  decide +kernel

theorem context_12_113210_662655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113210 ⟨662655, by decide⟩ :=
  accepted_of_selected 12 113210 ⟨662655, by decide⟩ ⟨12, 1, 0, 662655, 113210, 1, 65536⟩
    (by decide) selected_cut_34379

theorem selected_cut_34380 : selected 9 ⟨889236, by decide⟩
    (prefixPartial 12 113211) = some ⟨12, 2, 0, 889236, 113211, 3237, 65536⟩ := by
  decide +kernel

theorem context_12_113211_889236 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113211 ⟨889236, by decide⟩ :=
  accepted_of_selected 12 113211 ⟨889236, by decide⟩ ⟨12, 2, 0, 889236, 113211, 3237, 65536⟩
    (by decide) selected_cut_34380

theorem unmarked_context_11_28302_889237 : frontier 10 ⟨889237, by decide⟩
    (prefixCache 11 28302) (prefixPartial 11 28302) = false := by
  decide +kernel

theorem node_context_11_28302_889237 : EJMOriginalGlobalDAGData.nodes 10 ⟨889237, by decide⟩ =
    .split (coordinate 11) (![⟨889097, by decide⟩,⟨889177, by decide⟩,⟨662655, by decide⟩,⟨889236, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28302_889237 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28302 ⟨889237, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28302
    ⟨889237, by decide⟩ (by decide) (![⟨889097, by decide⟩,⟨889177, by decide⟩,⟨662655, by decide⟩,⟨889236, by decide⟩]) unmarked_context_11_28302_889237 node_context_11_28302_889237
  intro a
  fin_cases a
  · exact context_12_113208_889097
  · exact context_12_113209_889177
  · exact context_12_113210_662655
  · exact context_12_113211_889236

theorem selected_cut_34381 : selected 9 ⟨889299, by decide⟩
    (prefixPartial 12 113212) = some ⟨12, 2, 0, 889299, 113212, 3485, 65536⟩ := by
  decide +kernel

theorem context_12_113212_889299 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113212 ⟨889299, by decide⟩ :=
  accepted_of_selected 12 113212 ⟨889299, by decide⟩ ⟨12, 2, 0, 889299, 113212, 3485, 65536⟩
    (by decide) selected_cut_34381

theorem selected_cut_34382 : selected 9 ⟨889366, by decide⟩
    (prefixPartial 12 113213) = some ⟨12, 2, 0, 889366, 113213, 3737, 65536⟩ := by
  decide +kernel

theorem context_12_113213_889366 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113213 ⟨889366, by decide⟩ :=
  accepted_of_selected 12 113213 ⟨889366, by decide⟩ ⟨12, 2, 0, 889366, 113213, 3737, 65536⟩
    (by decide) selected_cut_34382

theorem selected_cut_34383 : selected 9 ⟨889419, by decide⟩
    (prefixPartial 12 113214) = some ⟨12, 2, 0, 889419, 113214, 3101, 65536⟩ := by
  decide +kernel

theorem context_12_113214_889419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113214 ⟨889419, by decide⟩ :=
  accepted_of_selected 12 113214 ⟨889419, by decide⟩ ⟨12, 2, 0, 889419, 113214, 3101, 65536⟩
    (by decide) selected_cut_34383

theorem selected_cut_34384 : selected 9 ⟨889473, by decide⟩
    (prefixPartial 12 113215) = some ⟨12, 2, 0, 889473, 113215, 3161, 65536⟩ := by
  decide +kernel

theorem context_12_113215_889473 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113215 ⟨889473, by decide⟩ :=
  accepted_of_selected 12 113215 ⟨889473, by decide⟩ ⟨12, 2, 0, 889473, 113215, 3161, 65536⟩
    (by decide) selected_cut_34384

theorem unmarked_context_11_28303_889474 : frontier 10 ⟨889474, by decide⟩
    (prefixCache 11 28303) (prefixPartial 11 28303) = false := by
  decide +kernel

theorem node_context_11_28303_889474 : EJMOriginalGlobalDAGData.nodes 10 ⟨889474, by decide⟩ =
    .split (coordinate 11) (![⟨889299, by decide⟩,⟨889366, by decide⟩,⟨889419, by decide⟩,⟨889473, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28303_889474 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28303 ⟨889474, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28303
    ⟨889474, by decide⟩ (by decide) (![⟨889299, by decide⟩,⟨889366, by decide⟩,⟨889419, by decide⟩,⟨889473, by decide⟩]) unmarked_context_11_28303_889474 node_context_11_28303_889474
  intro a
  fin_cases a
  · exact context_12_113212_889299
  · exact context_12_113213_889366
  · exact context_12_113214_889419
  · exact context_12_113215_889473

theorem unmarked_context_10_7075_889475 : frontier 11 ⟨889475, by decide⟩
    (prefixCache 10 7075) (prefixPartial 10 7075) = false := by
  decide +kernel

theorem node_context_10_7075_889475 : EJMOriginalGlobalDAGData.nodes 11 ⟨889475, by decide⟩ =
    .split (coordinate 10) (![⟨888664, by decide⟩,⟨889028, by decide⟩,⟨889237, by decide⟩,⟨889474, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_7075_889475 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 7075 ⟨889475, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 7075
    ⟨889475, by decide⟩ (by decide) (![⟨888664, by decide⟩,⟨889028, by decide⟩,⟨889237, by decide⟩,⟨889474, by decide⟩]) unmarked_context_10_7075_889475 node_context_10_7075_889475
  intro a
  fin_cases a
  · exact context_11_28300_888664
  · exact context_11_28301_889028
  · exact context_11_28302_889237
  · exact context_11_28303_889474

theorem unmarked_context_9_1768_889476 : frontier 12 ⟨889476, by decide⟩
    (prefixCache 9 1768) (prefixPartial 9 1768) = false := by
  decide +kernel

theorem node_context_9_1768_889476 : EJMOriginalGlobalDAGData.nodes 12 ⟨889476, by decide⟩ =
    .split (coordinate 9) (![⟨885215, by decide⟩,⟨886970, by decide⟩,⟨888284, by decide⟩,⟨889475, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1768_889476 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1768 ⟨889476, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1768
    ⟨889476, by decide⟩ (by decide) (![⟨885215, by decide⟩,⟨886970, by decide⟩,⟨888284, by decide⟩,⟨889475, by decide⟩]) unmarked_context_9_1768_889476 node_context_9_1768_889476
  intro a
  fin_cases a
  · exact context_10_7072_885215
  · exact context_10_7073_886970
  · exact context_10_7074_888284
  · exact context_10_7075_889475

theorem selected_cut_34385 : selected 11 ⟨875478, by decide⟩
    (prefixPartial 10 7076) = some ⟨10, 1, 0, 875478, 7076, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_7076_875478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 7076 ⟨875478, by decide⟩ :=
  accepted_of_selected 10 7076 ⟨875478, by decide⟩ ⟨10, 1, 0, 875478, 7076, 1, 1048576⟩
    (by decide) selected_cut_34385

theorem selected_cut_34386 : selected 9 ⟨889558, by decide⟩
    (prefixPartial 12 113232) = some ⟨12, 2, 0, 889558, 113232, 3589, 65536⟩ := by
  decide +kernel

theorem context_12_113232_889558 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113232 ⟨889558, by decide⟩ :=
  accepted_of_selected 12 113232 ⟨889558, by decide⟩ ⟨12, 2, 0, 889558, 113232, 3589, 65536⟩
    (by decide) selected_cut_34386

theorem selected_cut_34387 : selected 9 ⟨889632, by decide⟩
    (prefixPartial 12 113233) = some ⟨12, 2, 0, 889632, 113233, 3805, 65536⟩ := by
  decide +kernel

theorem context_12_113233_889632 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113233 ⟨889632, by decide⟩ :=
  accepted_of_selected 12 113233 ⟨889632, by decide⟩ ⟨12, 2, 0, 889632, 113233, 3805, 65536⟩
    (by decide) selected_cut_34387

theorem selected_cut_34388 : selected 9 ⟨889685, by decide⟩
    (prefixPartial 12 113234) = some ⟨12, 2, 0, 889685, 113234, 3137, 65536⟩ := by
  decide +kernel

theorem context_12_113234_889685 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113234 ⟨889685, by decide⟩ :=
  accepted_of_selected 12 113234 ⟨889685, by decide⟩ ⟨12, 2, 0, 889685, 113234, 3137, 65536⟩
    (by decide) selected_cut_34388

theorem selected_cut_34389 : selected 9 ⟨889767, by decide⟩
    (prefixPartial 12 113235) = some ⟨12, 2, 0, 889767, 113235, 3581, 65536⟩ := by
  decide +kernel

theorem context_12_113235_889767 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113235 ⟨889767, by decide⟩ :=
  accepted_of_selected 12 113235 ⟨889767, by decide⟩ ⟨12, 2, 0, 889767, 113235, 3581, 65536⟩
    (by decide) selected_cut_34389

theorem unmarked_context_11_28308_889768 : frontier 10 ⟨889768, by decide⟩
    (prefixCache 11 28308) (prefixPartial 11 28308) = false := by
  decide +kernel

theorem node_context_11_28308_889768 : EJMOriginalGlobalDAGData.nodes 10 ⟨889768, by decide⟩ =
    .split (coordinate 11) (![⟨889558, by decide⟩,⟨889632, by decide⟩,⟨889685, by decide⟩,⟨889767, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28308_889768 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28308 ⟨889768, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28308
    ⟨889768, by decide⟩ (by decide) (![⟨889558, by decide⟩,⟨889632, by decide⟩,⟨889685, by decide⟩,⟨889767, by decide⟩]) unmarked_context_11_28308_889768 node_context_11_28308_889768
  intro a
  fin_cases a
  · exact context_12_113232_889558
  · exact context_12_113233_889632
  · exact context_12_113234_889685
  · exact context_12_113235_889767

theorem selected_cut_34390 : selected 9 ⟨889827, by decide⟩
    (prefixPartial 12 113236) = some ⟨12, 2, 0, 889827, 113236, 2965, 65536⟩ := by
  decide +kernel

theorem context_12_113236_889827 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113236 ⟨889827, by decide⟩ :=
  accepted_of_selected 12 113236 ⟨889827, by decide⟩ ⟨12, 2, 0, 889827, 113236, 2965, 65536⟩
    (by decide) selected_cut_34390

theorem selected_cut_34391 : selected 9 ⟨889889, by decide⟩
    (prefixPartial 12 113237) = some ⟨12, 2, 0, 889889, 113237, 2825, 65536⟩ := by
  decide +kernel

theorem context_12_113237_889889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113237 ⟨889889, by decide⟩ :=
  accepted_of_selected 12 113237 ⟨889889, by decide⟩ ⟨12, 2, 0, 889889, 113237, 2825, 65536⟩
    (by decide) selected_cut_34391

theorem selected_cut_34392 : selected 9 ⟨889942, by decide⟩
    (prefixPartial 12 113238) = some ⟨12, 2, 0, 889942, 113238, 2597, 65536⟩ := by
  decide +kernel

theorem context_12_113238_889942 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113238 ⟨889942, by decide⟩ :=
  accepted_of_selected 12 113238 ⟨889942, by decide⟩ ⟨12, 2, 0, 889942, 113238, 2597, 65536⟩
    (by decide) selected_cut_34392

theorem selected_cut_34393 : selected 9 ⟨890003, by decide⟩
    (prefixPartial 12 113239) = some ⟨12, 2, 0, 890003, 113239, 2809, 65536⟩ := by
  decide +kernel

theorem context_12_113239_890003 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113239 ⟨890003, by decide⟩ :=
  accepted_of_selected 12 113239 ⟨890003, by decide⟩ ⟨12, 2, 0, 890003, 113239, 2809, 65536⟩
    (by decide) selected_cut_34393

theorem unmarked_context_11_28309_890004 : frontier 10 ⟨890004, by decide⟩
    (prefixCache 11 28309) (prefixPartial 11 28309) = false := by
  decide +kernel

theorem node_context_11_28309_890004 : EJMOriginalGlobalDAGData.nodes 10 ⟨890004, by decide⟩ =
    .split (coordinate 11) (![⟨889827, by decide⟩,⟨889889, by decide⟩,⟨889942, by decide⟩,⟨890003, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28309_890004 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28309 ⟨890004, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28309
    ⟨890004, by decide⟩ (by decide) (![⟨889827, by decide⟩,⟨889889, by decide⟩,⟨889942, by decide⟩,⟨890003, by decide⟩]) unmarked_context_11_28309_890004 node_context_11_28309_890004
  intro a
  fin_cases a
  · exact context_12_113236_889827
  · exact context_12_113237_889889
  · exact context_12_113238_889942
  · exact context_12_113239_890003

theorem selected_cut_34394 : selected 9 ⟨890050, by decide⟩
    (prefixPartial 12 113240) = some ⟨12, 2, 0, 890050, 113240, 2565, 65536⟩ := by
  decide +kernel

theorem context_12_113240_890050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113240 ⟨890050, by decide⟩ :=
  accepted_of_selected 12 113240 ⟨890050, by decide⟩ ⟨12, 2, 0, 890050, 113240, 2565, 65536⟩
    (by decide) selected_cut_34394

theorem selected_cut_34395 : selected 9 ⟨890092, by decide⟩
    (prefixPartial 12 113241) = some ⟨12, 2, 0, 890092, 113241, 2709, 65536⟩ := by
  decide +kernel

theorem context_12_113241_890092 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113241 ⟨890092, by decide⟩ :=
  accepted_of_selected 12 113241 ⟨890092, by decide⟩ ⟨12, 2, 0, 890092, 113241, 2709, 65536⟩
    (by decide) selected_cut_34395

theorem selected_cut_34396 : selected 9 ⟨660636, by decide⟩
    (prefixPartial 12 113242) = some ⟨12, 1, 0, 660636, 113242, 1, 65536⟩ := by
  decide +kernel

theorem context_12_113242_660636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113242 ⟨660636, by decide⟩ :=
  accepted_of_selected 12 113242 ⟨660636, by decide⟩ ⟨12, 1, 0, 660636, 113242, 1, 65536⟩
    (by decide) selected_cut_34396

theorem selected_cut_34397 : selected 9 ⟨890134, by decide⟩
    (prefixPartial 12 113243) = some ⟨12, 2, 0, 890134, 113243, 2461, 65536⟩ := by
  decide +kernel

theorem context_12_113243_890134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113243 ⟨890134, by decide⟩ :=
  accepted_of_selected 12 113243 ⟨890134, by decide⟩ ⟨12, 2, 0, 890134, 113243, 2461, 65536⟩
    (by decide) selected_cut_34397

theorem unmarked_context_11_28310_890135 : frontier 10 ⟨890135, by decide⟩
    (prefixCache 11 28310) (prefixPartial 11 28310) = false := by
  decide +kernel

theorem node_context_11_28310_890135 : EJMOriginalGlobalDAGData.nodes 10 ⟨890135, by decide⟩ =
    .split (coordinate 11) (![⟨890050, by decide⟩,⟨890092, by decide⟩,⟨660636, by decide⟩,⟨890134, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28310_890135 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28310 ⟨890135, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28310
    ⟨890135, by decide⟩ (by decide) (![⟨890050, by decide⟩,⟨890092, by decide⟩,⟨660636, by decide⟩,⟨890134, by decide⟩]) unmarked_context_11_28310_890135 node_context_11_28310_890135
  intro a
  fin_cases a
  · exact context_12_113240_890050
  · exact context_12_113241_890092
  · exact context_12_113242_660636
  · exact context_12_113243_890134

theorem selected_cut_34398 : selected 9 ⟨890218, by decide⟩
    (prefixPartial 12 113244) = some ⟨12, 2, 0, 890218, 113244, 2937, 65536⟩ := by
  decide +kernel

theorem context_12_113244_890218 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113244 ⟨890218, by decide⟩ :=
  accepted_of_selected 12 113244 ⟨890218, by decide⟩ ⟨12, 2, 0, 890218, 113244, 2937, 65536⟩
    (by decide) selected_cut_34398

theorem selected_cut_34399 : selected 9 ⟨890285, by decide⟩
    (prefixPartial 12 113245) = some ⟨12, 2, 0, 890285, 113245, 2893, 65536⟩ := by
  decide +kernel

theorem context_12_113245_890285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113245 ⟨890285, by decide⟩ :=
  accepted_of_selected 12 113245 ⟨890285, by decide⟩ ⟨12, 2, 0, 890285, 113245, 2893, 65536⟩
    (by decide) selected_cut_34399

theorem selected_cut_34400 : selected 9 ⟨890324, by decide⟩
    (prefixPartial 12 113246) = some ⟨12, 2, 0, 890324, 113246, 2413, 65536⟩ := by
  decide +kernel

theorem context_12_113246_890324 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113246 ⟨890324, by decide⟩ :=
  accepted_of_selected 12 113246 ⟨890324, by decide⟩ ⟨12, 2, 0, 890324, 113246, 2413, 65536⟩
    (by decide) selected_cut_34400

theorem selected_cut_34401 : selected 9 ⟨890376, by decide⟩
    (prefixPartial 12 113247) = some ⟨12, 2, 0, 890376, 113247, 2565, 65536⟩ := by
  decide +kernel

theorem context_12_113247_890376 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113247 ⟨890376, by decide⟩ :=
  accepted_of_selected 12 113247 ⟨890376, by decide⟩ ⟨12, 2, 0, 890376, 113247, 2565, 65536⟩
    (by decide) selected_cut_34401

theorem unmarked_context_11_28311_890377 : frontier 10 ⟨890377, by decide⟩
    (prefixCache 11 28311) (prefixPartial 11 28311) = false := by
  decide +kernel

theorem node_context_11_28311_890377 : EJMOriginalGlobalDAGData.nodes 10 ⟨890377, by decide⟩ =
    .split (coordinate 11) (![⟨890218, by decide⟩,⟨890285, by decide⟩,⟨890324, by decide⟩,⟨890376, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28311_890377 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28311 ⟨890377, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28311
    ⟨890377, by decide⟩ (by decide) (![⟨890218, by decide⟩,⟨890285, by decide⟩,⟨890324, by decide⟩,⟨890376, by decide⟩]) unmarked_context_11_28311_890377 node_context_11_28311_890377
  intro a
  fin_cases a
  · exact context_12_113244_890218
  · exact context_12_113245_890285
  · exact context_12_113246_890324
  · exact context_12_113247_890376

theorem unmarked_context_10_7077_890378 : frontier 11 ⟨890378, by decide⟩
    (prefixCache 10 7077) (prefixPartial 10 7077) = false := by
  decide +kernel

theorem node_context_10_7077_890378 : EJMOriginalGlobalDAGData.nodes 11 ⟨890378, by decide⟩ =
    .split (coordinate 10) (![⟨889768, by decide⟩,⟨890004, by decide⟩,⟨890135, by decide⟩,⟨890377, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_7077_890378 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 7077 ⟨890378, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 7077
    ⟨890378, by decide⟩ (by decide) (![⟨889768, by decide⟩,⟨890004, by decide⟩,⟨890135, by decide⟩,⟨890377, by decide⟩]) unmarked_context_10_7077_890378 node_context_10_7077_890378
  intro a
  fin_cases a
  · exact context_11_28308_889768
  · exact context_11_28309_890004
  · exact context_11_28310_890135
  · exact context_11_28311_890377

theorem selected_cut_34402 : selected 9 ⟨890439, by decide⟩
    (prefixPartial 12 113248) = some ⟨12, 2, 0, 890439, 113248, 2173, 65536⟩ := by
  decide +kernel

theorem context_12_113248_890439 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113248 ⟨890439, by decide⟩ :=
  accepted_of_selected 12 113248 ⟨890439, by decide⟩ ⟨12, 2, 0, 890439, 113248, 2173, 65536⟩
    (by decide) selected_cut_34402

theorem selected_cut_34403 : selected 9 ⟨890485, by decide⟩
    (prefixPartial 12 113249) = some ⟨12, 2, 0, 890485, 113249, 2049, 65536⟩ := by
  decide +kernel

theorem context_12_113249_890485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113249 ⟨890485, by decide⟩ :=
  accepted_of_selected 12 113249 ⟨890485, by decide⟩ ⟨12, 2, 0, 890485, 113249, 2049, 65536⟩
    (by decide) selected_cut_34403

theorem selected_cut_34404 : selected 9 ⟨890519, by decide⟩
    (prefixPartial 12 113250) = some ⟨12, 2, 0, 890519, 113250, 1705, 65536⟩ := by
  decide +kernel

theorem context_12_113250_890519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113250 ⟨890519, by decide⟩ :=
  accepted_of_selected 12 113250 ⟨890519, by decide⟩ ⟨12, 2, 0, 890519, 113250, 1705, 65536⟩
    (by decide) selected_cut_34404

theorem selected_cut_34405 : selected 9 ⟨890556, by decide⟩
    (prefixPartial 12 113251) = some ⟨12, 2, 0, 890556, 113251, 1921, 65536⟩ := by
  decide +kernel

theorem context_12_113251_890556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113251 ⟨890556, by decide⟩ :=
  accepted_of_selected 12 113251 ⟨890556, by decide⟩ ⟨12, 2, 0, 890556, 113251, 1921, 65536⟩
    (by decide) selected_cut_34405

theorem unmarked_context_11_28312_890557 : frontier 10 ⟨890557, by decide⟩
    (prefixCache 11 28312) (prefixPartial 11 28312) = false := by
  decide +kernel

theorem node_context_11_28312_890557 : EJMOriginalGlobalDAGData.nodes 10 ⟨890557, by decide⟩ =
    .split (coordinate 11) (![⟨890439, by decide⟩,⟨890485, by decide⟩,⟨890519, by decide⟩,⟨890556, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28312_890557 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28312 ⟨890557, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28312
    ⟨890557, by decide⟩ (by decide) (![⟨890439, by decide⟩,⟨890485, by decide⟩,⟨890519, by decide⟩,⟨890556, by decide⟩]) unmarked_context_11_28312_890557 node_context_11_28312_890557
  intro a
  fin_cases a
  · exact context_12_113248_890439
  · exact context_12_113249_890485
  · exact context_12_113250_890519
  · exact context_12_113251_890556

theorem selected_cut_34406 : selected 9 ⟨890610, by decide⟩
    (prefixPartial 12 113252) = some ⟨12, 2, 0, 890610, 113252, 1945, 65536⟩ := by
  decide +kernel

theorem context_12_113252_890610 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113252 ⟨890610, by decide⟩ :=
  accepted_of_selected 12 113252 ⟨890610, by decide⟩ ⟨12, 2, 0, 890610, 113252, 1945, 65536⟩
    (by decide) selected_cut_34406

theorem selected_cut_34407 : selected 9 ⟨890644, by decide⟩
    (prefixPartial 12 113253) = some ⟨12, 2, 0, 890644, 113253, 1761, 65536⟩ := by
  decide +kernel

theorem context_12_113253_890644 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113253 ⟨890644, by decide⟩ :=
  accepted_of_selected 12 113253 ⟨890644, by decide⟩ ⟨12, 2, 0, 890644, 113253, 1761, 65536⟩
    (by decide) selected_cut_34407

theorem selected_cut_34408 : selected 9 ⟨890677, by decide⟩
    (prefixPartial 12 113254) = some ⟨12, 2, 0, 890677, 113254, 1449, 65536⟩ := by
  decide +kernel

theorem context_12_113254_890677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113254 ⟨890677, by decide⟩ :=
  accepted_of_selected 12 113254 ⟨890677, by decide⟩ ⟨12, 2, 0, 890677, 113254, 1449, 65536⟩
    (by decide) selected_cut_34408

theorem selected_cut_34409 : selected 9 ⟨890712, by decide⟩
    (prefixPartial 12 113255) = some ⟨12, 2, 0, 890712, 113255, 1597, 65536⟩ := by
  decide +kernel

theorem context_12_113255_890712 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113255 ⟨890712, by decide⟩ :=
  accepted_of_selected 12 113255 ⟨890712, by decide⟩ ⟨12, 2, 0, 890712, 113255, 1597, 65536⟩
    (by decide) selected_cut_34409

theorem unmarked_context_11_28313_890713 : frontier 10 ⟨890713, by decide⟩
    (prefixCache 11 28313) (prefixPartial 11 28313) = false := by
  decide +kernel

theorem node_context_11_28313_890713 : EJMOriginalGlobalDAGData.nodes 10 ⟨890713, by decide⟩ =
    .split (coordinate 11) (![⟨890610, by decide⟩,⟨890644, by decide⟩,⟨890677, by decide⟩,⟨890712, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28313_890713 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28313 ⟨890713, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28313
    ⟨890713, by decide⟩ (by decide) (![⟨890610, by decide⟩,⟨890644, by decide⟩,⟨890677, by decide⟩,⟨890712, by decide⟩]) unmarked_context_11_28313_890713 node_context_11_28313_890713
  intro a
  fin_cases a
  · exact context_12_113252_890610
  · exact context_12_113253_890644
  · exact context_12_113254_890677
  · exact context_12_113255_890712

theorem selected_cut_34410 : selected 10 ⟨883048, by decide⟩
    (prefixPartial 11 28314) = some ⟨11, 2, 0, 883048, 28314, 5, 262144⟩ := by
  decide +kernel

theorem context_11_28314_883048 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28314 ⟨883048, by decide⟩ :=
  accepted_of_selected 11 28314 ⟨883048, by decide⟩ ⟨11, 2, 0, 883048, 28314, 5, 262144⟩
    (by decide) selected_cut_34410

theorem selected_cut_34411 : selected 9 ⟨890757, by decide⟩
    (prefixPartial 12 113260) = some ⟨12, 2, 0, 890757, 113260, 1805, 65536⟩ := by
  decide +kernel

theorem context_12_113260_890757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113260 ⟨890757, by decide⟩ :=
  accepted_of_selected 12 113260 ⟨890757, by decide⟩ ⟨12, 2, 0, 890757, 113260, 1805, 65536⟩
    (by decide) selected_cut_34411

theorem selected_cut_34412 : selected 9 ⟨890790, by decide⟩
    (prefixPartial 12 113261) = some ⟨12, 2, 0, 890790, 113261, 1649, 65536⟩ := by
  decide +kernel

theorem context_12_113261_890790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113261 ⟨890790, by decide⟩ :=
  accepted_of_selected 12 113261 ⟨890790, by decide⟩ ⟨12, 2, 0, 890790, 113261, 1649, 65536⟩
    (by decide) selected_cut_34412

theorem selected_cut_34413 : selected 9 ⟨890817, by decide⟩
    (prefixPartial 12 113262) = some ⟨12, 2, 0, 890817, 113262, 1345, 65536⟩ := by
  decide +kernel

theorem context_12_113262_890817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113262 ⟨890817, by decide⟩ :=
  accepted_of_selected 12 113262 ⟨890817, by decide⟩ ⟨12, 2, 0, 890817, 113262, 1345, 65536⟩
    (by decide) selected_cut_34413

theorem selected_cut_34414 : selected 9 ⟨890844, by decide⟩
    (prefixPartial 12 113263) = some ⟨12, 2, 0, 890844, 113263, 1473, 65536⟩ := by
  decide +kernel

theorem context_12_113263_890844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113263 ⟨890844, by decide⟩ :=
  accepted_of_selected 12 113263 ⟨890844, by decide⟩ ⟨12, 2, 0, 890844, 113263, 1473, 65536⟩
    (by decide) selected_cut_34414

theorem unmarked_context_11_28315_890845 : frontier 10 ⟨890845, by decide⟩
    (prefixCache 11 28315) (prefixPartial 11 28315) = false := by
  decide +kernel

theorem node_context_11_28315_890845 : EJMOriginalGlobalDAGData.nodes 10 ⟨890845, by decide⟩ =
    .split (coordinate 11) (![⟨890757, by decide⟩,⟨890790, by decide⟩,⟨890817, by decide⟩,⟨890844, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28315_890845 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28315 ⟨890845, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28315
    ⟨890845, by decide⟩ (by decide) (![⟨890757, by decide⟩,⟨890790, by decide⟩,⟨890817, by decide⟩,⟨890844, by decide⟩]) unmarked_context_11_28315_890845 node_context_11_28315_890845
  intro a
  fin_cases a
  · exact context_12_113260_890757
  · exact context_12_113261_890790
  · exact context_12_113262_890817
  · exact context_12_113263_890844

theorem unmarked_context_10_7078_890846 : frontier 11 ⟨890846, by decide⟩
    (prefixCache 10 7078) (prefixPartial 10 7078) = false := by
  decide +kernel

theorem node_context_10_7078_890846 : EJMOriginalGlobalDAGData.nodes 11 ⟨890846, by decide⟩ =
    .split (coordinate 10) (![⟨890557, by decide⟩,⟨890713, by decide⟩,⟨883048, by decide⟩,⟨890845, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_7078_890846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 7078 ⟨890846, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 7078
    ⟨890846, by decide⟩ (by decide) (![⟨890557, by decide⟩,⟨890713, by decide⟩,⟨883048, by decide⟩,⟨890845, by decide⟩]) unmarked_context_10_7078_890846 node_context_10_7078_890846
  intro a
  fin_cases a
  · exact context_11_28312_890557
  · exact context_11_28313_890713
  · exact context_11_28314_883048
  · exact context_11_28315_890845

theorem selected_cut_34415 : selected 9 ⟨890889, by decide⟩
    (prefixPartial 12 113264) = some ⟨12, 2, 0, 890889, 113264, 761, 65536⟩ := by
  decide +kernel

theorem context_12_113264_890889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113264 ⟨890889, by decide⟩ :=
  accepted_of_selected 12 113264 ⟨890889, by decide⟩ ⟨12, 2, 0, 890889, 113264, 761, 65536⟩
    (by decide) selected_cut_34415

theorem selected_cut_34416 : selected 9 ⟨890919, by decide⟩
    (prefixPartial 12 113265) = some ⟨12, 2, 0, 890919, 113265, 1265, 65536⟩ := by
  decide +kernel

theorem context_12_113265_890919 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113265 ⟨890919, by decide⟩ :=
  accepted_of_selected 12 113265 ⟨890919, by decide⟩ ⟨12, 2, 0, 890919, 113265, 1265, 65536⟩
    (by decide) selected_cut_34416

theorem selected_cut_34417 : selected 9 ⟨890945, by decide⟩
    (prefixPartial 12 113266) = some ⟨12, 2, 0, 890945, 113266, 1077, 65536⟩ := by
  decide +kernel

theorem context_12_113266_890945 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113266 ⟨890945, by decide⟩ :=
  accepted_of_selected 12 113266 ⟨890945, by decide⟩ ⟨12, 2, 0, 890945, 113266, 1077, 65536⟩
    (by decide) selected_cut_34417

theorem selected_cut_34418 : selected 9 ⟨890975, by decide⟩
    (prefixPartial 12 113267) = some ⟨12, 2, 0, 890975, 113267, 1145, 65536⟩ := by
  decide +kernel

theorem context_12_113267_890975 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 113267 ⟨890975, by decide⟩ :=
  accepted_of_selected 12 113267 ⟨890975, by decide⟩ ⟨12, 2, 0, 890975, 113267, 1145, 65536⟩
    (by decide) selected_cut_34418

theorem unmarked_context_11_28316_890976 : frontier 10 ⟨890976, by decide⟩
    (prefixCache 11 28316) (prefixPartial 11 28316) = false := by
  decide +kernel

theorem node_context_11_28316_890976 : EJMOriginalGlobalDAGData.nodes 10 ⟨890976, by decide⟩ =
    .split (coordinate 11) (![⟨890889, by decide⟩,⟨890919, by decide⟩,⟨890945, by decide⟩,⟨890975, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_28316_890976 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28316 ⟨890976, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 28316
    ⟨890976, by decide⟩ (by decide) (![⟨890889, by decide⟩,⟨890919, by decide⟩,⟨890945, by decide⟩,⟨890975, by decide⟩]) unmarked_context_11_28316_890976 node_context_11_28316_890976
  intro a
  fin_cases a
  · exact context_12_113264_890889
  · exact context_12_113265_890919
  · exact context_12_113266_890945
  · exact context_12_113267_890975

theorem selected_cut_34419 : selected 10 ⟨891056, by decide⟩
    (prefixPartial 11 28317) = some ⟨11, 2, 0, 891056, 28317, 2665, 262144⟩ := by
  decide +kernel

theorem context_11_28317_891056 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28317 ⟨891056, by decide⟩ :=
  accepted_of_selected 11 28317 ⟨891056, by decide⟩ ⟨11, 2, 0, 891056, 28317, 2665, 262144⟩
    (by decide) selected_cut_34419

theorem selected_cut_34420 : selected 10 ⟨891082, by decide⟩
    (prefixPartial 11 28318) = some ⟨11, 2, 0, 891082, 28318, 965, 262144⟩ := by
  decide +kernel

theorem context_11_28318_891082 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28318 ⟨891082, by decide⟩ :=
  accepted_of_selected 11 28318 ⟨891082, by decide⟩ ⟨11, 2, 0, 891082, 28318, 965, 262144⟩
    (by decide) selected_cut_34420

theorem selected_cut_34421 : selected 10 ⟨891103, by decide⟩
    (prefixPartial 11 28319) = some ⟨11, 2, 0, 891103, 28319, 641, 262144⟩ := by
  decide +kernel

theorem context_11_28319_891103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28319 ⟨891103, by decide⟩ :=
  accepted_of_selected 11 28319 ⟨891103, by decide⟩ ⟨11, 2, 0, 891103, 28319, 641, 262144⟩
    (by decide) selected_cut_34421

theorem unmarked_context_10_7079_891104 : frontier 11 ⟨891104, by decide⟩
    (prefixCache 10 7079) (prefixPartial 10 7079) = false := by
  decide +kernel

theorem node_context_10_7079_891104 : EJMOriginalGlobalDAGData.nodes 11 ⟨891104, by decide⟩ =
    .split (coordinate 10) (![⟨890976, by decide⟩,⟨891056, by decide⟩,⟨891082, by decide⟩,⟨891103, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_7079_891104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 7079 ⟨891104, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 7079
    ⟨891104, by decide⟩ (by decide) (![⟨890976, by decide⟩,⟨891056, by decide⟩,⟨891082, by decide⟩,⟨891103, by decide⟩]) unmarked_context_10_7079_891104 node_context_10_7079_891104
  intro a
  fin_cases a
  · exact context_11_28316_890976
  · exact context_11_28317_891056
  · exact context_11_28318_891082
  · exact context_11_28319_891103

theorem unmarked_context_9_1769_891105 : frontier 12 ⟨891105, by decide⟩
    (prefixCache 9 1769) (prefixPartial 9 1769) = false := by
  decide +kernel

theorem node_context_9_1769_891105 : EJMOriginalGlobalDAGData.nodes 12 ⟨891105, by decide⟩ =
    .split (coordinate 9) (![⟨875478, by decide⟩,⟨890378, by decide⟩,⟨890846, by decide⟩,⟨891104, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1769_891105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1769 ⟨891105, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1769
    ⟨891105, by decide⟩ (by decide) (![⟨875478, by decide⟩,⟨890378, by decide⟩,⟨890846, by decide⟩,⟨891104, by decide⟩]) unmarked_context_9_1769_891105 node_context_9_1769_891105
  intro a
  fin_cases a
  · exact context_10_7076_875478
  · exact context_10_7077_890378
  · exact context_10_7078_890846
  · exact context_10_7079_891104

theorem selected_cut_34422 : selected 11 ⟨875478, by decide⟩
    (prefixPartial 10 7080) = some ⟨10, 1, 0, 875478, 7080, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_7080_875478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 7080 ⟨875478, by decide⟩ :=
  accepted_of_selected 10 7080 ⟨875478, by decide⟩ ⟨10, 1, 0, 875478, 7080, 1, 1048576⟩
    (by decide) selected_cut_34422

theorem selected_cut_34423 : selected 10 ⟨891229, by decide⟩
    (prefixPartial 11 28324) = some ⟨11, 2, 0, 891229, 28324, 3073, 262144⟩ := by
  decide +kernel

theorem context_11_28324_891229 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28324 ⟨891229, by decide⟩ :=
  accepted_of_selected 11 28324 ⟨891229, by decide⟩ ⟨11, 2, 0, 891229, 28324, 3073, 262144⟩
    (by decide) selected_cut_34423

theorem selected_cut_34424 : selected 10 ⟨891312, by decide⟩
    (prefixPartial 11 28325) = some ⟨11, 2, 0, 891312, 28325, 2373, 262144⟩ := by
  decide +kernel

theorem context_11_28325_891312 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28325 ⟨891312, by decide⟩ :=
  accepted_of_selected 11 28325 ⟨891312, by decide⟩ ⟨11, 2, 0, 891312, 28325, 2373, 262144⟩
    (by decide) selected_cut_34424

theorem selected_cut_34425 : selected 10 ⟨891389, by decide⟩
    (prefixPartial 11 28326) = some ⟨11, 2, 0, 891389, 28326, 1977, 262144⟩ := by
  decide +kernel

theorem context_11_28326_891389 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28326 ⟨891389, by decide⟩ :=
  accepted_of_selected 11 28326 ⟨891389, by decide⟩ ⟨11, 2, 0, 891389, 28326, 1977, 262144⟩
    (by decide) selected_cut_34425

theorem selected_cut_34426 : selected 10 ⟨891457, by decide⟩
    (prefixPartial 11 28327) = some ⟨11, 2, 0, 891457, 28327, 1821, 262144⟩ := by
  decide +kernel

theorem context_11_28327_891457 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 28327 ⟨891457, by decide⟩ :=
  accepted_of_selected 11 28327 ⟨891457, by decide⟩ ⟨11, 2, 0, 891457, 28327, 1821, 262144⟩
    (by decide) selected_cut_34426

theorem unmarked_context_10_7081_891458 : frontier 11 ⟨891458, by decide⟩
    (prefixCache 10 7081) (prefixPartial 10 7081) = false := by
  decide +kernel

theorem node_context_10_7081_891458 : EJMOriginalGlobalDAGData.nodes 11 ⟨891458, by decide⟩ =
    .split (coordinate 10) (![⟨891229, by decide⟩,⟨891312, by decide⟩,⟨891389, by decide⟩,⟨891457, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_7081_891458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 7081 ⟨891458, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 7081
    ⟨891458, by decide⟩ (by decide) (![⟨891229, by decide⟩,⟨891312, by decide⟩,⟨891389, by decide⟩,⟨891457, by decide⟩]) unmarked_context_10_7081_891458 node_context_10_7081_891458
  intro a
  fin_cases a
  · exact context_11_28324_891229
  · exact context_11_28325_891312
  · exact context_11_28326_891389
  · exact context_11_28327_891457

theorem selected_cut_34427 : selected 11 ⟨891507, by decide⟩
    (prefixPartial 10 7082) = some ⟨10, 2, 0, 891507, 7082, 1489, 1048576⟩ := by
  decide +kernel

theorem context_10_7082_891507 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 7082 ⟨891507, by decide⟩ :=
  accepted_of_selected 10 7082 ⟨891507, by decide⟩ ⟨10, 2, 0, 891507, 7082, 1489, 1048576⟩
    (by decide) selected_cut_34427

theorem selected_cut_34428 : selected 11 ⟨875478, by decide⟩
    (prefixPartial 10 7083) = some ⟨10, 1, 0, 875478, 7083, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_7083_875478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 7083 ⟨875478, by decide⟩ :=
  accepted_of_selected 10 7083 ⟨875478, by decide⟩ ⟨10, 1, 0, 875478, 7083, 1, 1048576⟩
    (by decide) selected_cut_34428

theorem unmarked_context_9_1770_891508 : frontier 12 ⟨891508, by decide⟩
    (prefixCache 9 1770) (prefixPartial 9 1770) = false := by
  decide +kernel

theorem node_context_9_1770_891508 : EJMOriginalGlobalDAGData.nodes 12 ⟨891508, by decide⟩ =
    .split (coordinate 9) (![⟨875478, by decide⟩,⟨891458, by decide⟩,⟨891507, by decide⟩,⟨875478, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1770_891508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1770 ⟨891508, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1770
    ⟨891508, by decide⟩ (by decide) (![⟨875478, by decide⟩,⟨891458, by decide⟩,⟨891507, by decide⟩,⟨875478, by decide⟩]) unmarked_context_9_1770_891508 node_context_9_1770_891508
  intro a
  fin_cases a
  · exact context_10_7080_875478
  · exact context_10_7081_891458
  · exact context_10_7082_891507
  · exact context_10_7083_875478

theorem selected_cut_34429 : selected 12 ⟨891577, by decide⟩
    (prefixPartial 9 1771) = some ⟨9, 2, 0, 891577, 1771, 1093, 4194304⟩ := by
  decide +kernel

theorem context_9_1771_891577 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1771 ⟨891577, by decide⟩ :=
  accepted_of_selected 9 1771 ⟨891577, by decide⟩ ⟨9, 2, 0, 891577, 1771, 1093, 4194304⟩
    (by decide) selected_cut_34429

theorem unmarked_context_8_442_891578 : frontier 13 ⟨891578, by decide⟩
    (prefixCache 8 442) (prefixPartial 8 442) = false := by
  decide +kernel

theorem node_context_8_442_891578 : EJMOriginalGlobalDAGData.nodes 13 ⟨891578, by decide⟩ =
    .split (coordinate 8) (![⟨889476, by decide⟩,⟨891105, by decide⟩,⟨891508, by decide⟩,⟨891577, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_442_891578 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 442 ⟨891578, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 442
    ⟨891578, by decide⟩ (by decide) (![⟨889476, by decide⟩,⟨891105, by decide⟩,⟨891508, by decide⟩,⟨891577, by decide⟩]) unmarked_context_8_442_891578 node_context_8_442_891578
  intro a
  fin_cases a
  · exact context_9_1768_889476
  · exact context_9_1769_891105
  · exact context_9_1770_891508
  · exact context_9_1771_891577

theorem selected_cut_34430 : selected 13 ⟨891579, by decide⟩
    (prefixPartial 8 443) = some ⟨8, 1, 0, 891579, 443, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_443_891579 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 443 ⟨891579, by decide⟩ :=
  accepted_of_selected 8 443 ⟨891579, by decide⟩ ⟨8, 1, 0, 891579, 443, 1, 16777216⟩
    (by decide) selected_cut_34430

theorem unmarked_context_7_110_891580 : frontier 14 ⟨891580, by decide⟩
    (prefixCache 7 110) (prefixPartial 7 110) = false := by
  decide +kernel

theorem node_context_7_110_891580 : EJMOriginalGlobalDAGData.nodes 14 ⟨891580, by decide⟩ =
    .split (coordinate 7) (![⟨878224, by decide⟩,⟨884723, by decide⟩,⟨891578, by decide⟩,⟨891579, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_110_891580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 110 ⟨891580, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 110
    ⟨891580, by decide⟩ (by decide) (![⟨878224, by decide⟩,⟨884723, by decide⟩,⟨891578, by decide⟩,⟨891579, by decide⟩]) unmarked_context_7_110_891580 node_context_7_110_891580
  intro a
  fin_cases a
  · exact context_8_440_878224
  · exact context_8_441_884723
  · exact context_8_442_891578
  · exact context_8_443_891579

theorem selected_cut_34431 : selected 14 ⟨870854, by decide⟩
    (prefixPartial 7 111) = some ⟨7, 1, 0, 870854, 111, 1, 67108864⟩ := by
  decide +kernel

theorem context_7_111_870854 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 111 ⟨870854, by decide⟩ :=
  accepted_of_selected 7 111 ⟨870854, by decide⟩ ⟨7, 1, 0, 870854, 111, 1, 67108864⟩
    (by decide) selected_cut_34431

theorem unmarked_context_6_27_891581 : frontier 15 ⟨891581, by decide⟩
    (prefixCache 6 27) (prefixPartial 6 27) = false := by
  decide +kernel

theorem node_context_6_27_891581 : EJMOriginalGlobalDAGData.nodes 15 ⟨891581, by decide⟩ =
    .split (coordinate 6) (![⟨870854, by decide⟩,⟨870855, by decide⟩,⟨891580, by decide⟩,⟨870854, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_6_27_891581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 27 ⟨891581, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 6 27
    ⟨891581, by decide⟩ (by decide) (![⟨870854, by decide⟩,⟨870855, by decide⟩,⟨891580, by decide⟩,⟨870854, by decide⟩]) unmarked_context_6_27_891581 node_context_6_27_891581
  intro a
  fin_cases a
  · exact context_7_108_870854
  · exact context_7_109_870855
  · exact context_7_110_891580
  · exact context_7_111_870854

theorem unmarked_context_5_6_891582 : frontier 16 ⟨891582, by decide⟩
    (prefixCache 5 6) (prefixPartial 5 6) = false := by
  decide +kernel

theorem node_context_5_6_891582 : EJMOriginalGlobalDAGData.nodes 16 ⟨891582, by decide⟩ =
    .split (coordinate 5) (![⟨434744, by decide⟩,⟨814759, by decide⟩,⟨870853, by decide⟩,⟨891581, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_5_6_891582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 5 6 ⟨891582, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 5 6
    ⟨891582, by decide⟩ (by decide) (![⟨434744, by decide⟩,⟨814759, by decide⟩,⟨870853, by decide⟩,⟨891581, by decide⟩]) unmarked_context_5_6_891582 node_context_5_6_891582
  intro a
  fin_cases a
  · exact context_6_24_434744
  · exact context_6_25_814759
  · exact context_6_26_870853
  · exact context_6_27_891581

theorem selected_cut_34432 : selected 16 ⟨434742, by decide⟩
    (prefixPartial 5 7) = some ⟨5, 1, 0, 434742, 7, 1, 1073741824⟩ := by
  decide +kernel

theorem context_5_7_434742 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 5 7 ⟨434742, by decide⟩ :=
  accepted_of_selected 5 7 ⟨434742, by decide⟩ ⟨5, 1, 0, 434742, 7, 1, 1073741824⟩
    (by decide) selected_cut_34432

theorem unmarked_context_4_1_891583 : frontier 17 ⟨891583, by decide⟩
    (prefixCache 4 1) (prefixPartial 4 1) = false := by
  decide +kernel

theorem node_context_4_1_891583 : EJMOriginalGlobalDAGData.nodes 17 ⟨891583, by decide⟩ =
    .split (coordinate 4) (![⟨640026, by decide⟩,⟨763589, by decide⟩,⟨891582, by decide⟩,⟨434742, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_4_1_891583 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 4 1 ⟨891583, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 4 1
    ⟨891583, by decide⟩ (by decide) (![⟨640026, by decide⟩,⟨763589, by decide⟩,⟨891582, by decide⟩,⟨434742, by decide⟩]) unmarked_context_4_1_891583 node_context_4_1_891583
  intro a
  fin_cases a
  · exact context_5_4_640026
  · exact context_5_5_763589
  · exact context_5_6_891582
  · exact context_5_7_434742

theorem selected_cut_34433 : selected 17 ⟨891584, by decide⟩
    (prefixPartial 4 2) = some ⟨4, 1, 0, 891584, 2, 1, 4294967296⟩ := by
  decide +kernel

theorem context_4_2_891584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 4 2 ⟨891584, by decide⟩ :=
  accepted_of_selected 4 2 ⟨891584, by decide⟩ ⟨4, 1, 0, 891584, 2, 1, 4294967296⟩
    (by decide) selected_cut_34433

theorem selected_cut_34434 : selected 17 ⟨891585, by decide⟩
    (prefixPartial 4 3) = some ⟨4, 1, 0, 891585, 3, 1, 4294967296⟩ := by
  decide +kernel

theorem context_4_3_891585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 4 3 ⟨891585, by decide⟩ :=
  accepted_of_selected 4 3 ⟨891585, by decide⟩ ⟨4, 1, 0, 891585, 3, 1, 4294967296⟩
    (by decide) selected_cut_34434

theorem unmarked_context_3_0_891586 : frontier 18 ⟨891586, by decide⟩
    (prefixCache 3 0) (prefixPartial 3 0) = false := by
  decide +kernel

theorem node_context_3_0_891586 : EJMOriginalGlobalDAGData.nodes 18 ⟨891586, by decide⟩ =
    .split (coordinate 3) (![⟨434743, by decide⟩,⟨891583, by decide⟩,⟨891584, by decide⟩,⟨891585, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_3_0_891586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 3 0 ⟨891586, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 3 0
    ⟨891586, by decide⟩ (by decide) (![⟨434743, by decide⟩,⟨891583, by decide⟩,⟨891584, by decide⟩,⟨891585, by decide⟩]) unmarked_context_3_0_891586 node_context_3_0_891586
  intro a
  fin_cases a
  · exact context_4_0_434743
  · exact context_4_1_891583
  · exact context_4_2_891584
  · exact context_4_3_891585

theorem selected_cut_34435 : selected 16 ⟨891587, by decide⟩
    (prefixPartial 5 16) = some ⟨5, 1, 0, 891587, 16, 1, 1073741824⟩ := by
  decide +kernel

theorem context_5_16_891587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 5 16 ⟨891587, by decide⟩ :=
  accepted_of_selected 5 16 ⟨891587, by decide⟩ ⟨5, 1, 0, 891587, 16, 1, 1073741824⟩
    (by decide) selected_cut_34435

theorem selected_cut_34436 : selected 14 ⟨116316, by decide⟩
    (prefixPartial 7 272) = some ⟨7, 1, 0, 116316, 272, 1, 67108864⟩ := by
  decide +kernel

theorem context_7_272_116316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 272 ⟨116316, by decide⟩ :=
  accepted_of_selected 7 272 ⟨116316, by decide⟩ ⟨7, 1, 0, 116316, 272, 1, 67108864⟩
    (by decide) selected_cut_34436

theorem selected_cut_34437 : selected 13 ⟨14300, by decide⟩
    (prefixPartial 8 1092) = some ⟨8, 1, 0, 14300, 1092, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_1092_14300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1092 ⟨14300, by decide⟩ :=
  accepted_of_selected 8 1092 ⟨14300, by decide⟩ ⟨8, 1, 0, 14300, 1092, 1, 16777216⟩
    (by decide) selected_cut_34437

theorem selected_cut_34438 : selected 9 ⟨891677, by decide⟩
    (prefixPartial 12 279808) = some ⟨12, 2, 0, 891677, 279808, 765, 65536⟩ := by
  decide +kernel

theorem context_12_279808_891677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 279808 ⟨891677, by decide⟩ :=
  accepted_of_selected 12 279808 ⟨891677, by decide⟩ ⟨12, 2, 0, 891677, 279808, 765, 65536⟩
    (by decide) selected_cut_34438

theorem selected_cut_34439 : selected 9 ⟨891781, by decide⟩
    (prefixPartial 12 279809) = some ⟨12, 2, 0, 891781, 279809, 1569, 65536⟩ := by
  decide +kernel

theorem context_12_279809_891781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 279809 ⟨891781, by decide⟩ :=
  accepted_of_selected 12 279809 ⟨891781, by decide⟩ ⟨12, 2, 0, 891781, 279809, 1569, 65536⟩
    (by decide) selected_cut_34439

theorem selected_cut_34440 : selected 9 ⟨891949, by decide⟩
    (prefixPartial 12 279810) = some ⟨12, 2, 0, 891949, 279810, 3157, 65536⟩ := by
  decide +kernel

theorem context_12_279810_891949 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 279810 ⟨891949, by decide⟩ :=
  accepted_of_selected 12 279810 ⟨891949, by decide⟩ ⟨12, 2, 0, 891949, 279810, 3157, 65536⟩
    (by decide) selected_cut_34440

theorem selected_cut_34441 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 279811) = some ⟨12, 1, 0, 893, 279811, 1, 65536⟩ := by
  decide +kernel

theorem context_12_279811_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 279811 ⟨893, by decide⟩ :=
  accepted_of_selected 12 279811 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 279811, 1, 65536⟩
    (by decide) selected_cut_34441

theorem unmarked_context_11_69952_891950 : frontier 10 ⟨891950, by decide⟩
    (prefixCache 11 69952) (prefixPartial 11 69952) = false := by
  decide +kernel

theorem node_context_11_69952_891950 : EJMOriginalGlobalDAGData.nodes 10 ⟨891950, by decide⟩ =
    .split (coordinate 11) (![⟨891677, by decide⟩,⟨891781, by decide⟩,⟨891949, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_69952_891950 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 69952 ⟨891950, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 69952
    ⟨891950, by decide⟩ (by decide) (![⟨891677, by decide⟩,⟨891781, by decide⟩,⟨891949, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_69952_891950 node_context_11_69952_891950
  intro a
  fin_cases a
  · exact context_12_279808_891677
  · exact context_12_279809_891781
  · exact context_12_279810_891949
  · exact context_12_279811_893

theorem selected_cut_34442 : selected 10 ⟨892052, by decide⟩
    (prefixPartial 11 69953) = some ⟨11, 2, 0, 892052, 69953, 3217, 262144⟩ := by
  decide +kernel

theorem context_11_69953_892052 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 69953 ⟨892052, by decide⟩ :=
  accepted_of_selected 11 69953 ⟨892052, by decide⟩ ⟨11, 2, 0, 892052, 69953, 3217, 262144⟩
    (by decide) selected_cut_34442

theorem selected_cut_34443 : selected 10 ⟨892224, by decide⟩
    (prefixPartial 11 69954) = some ⟨11, 2, 0, 892224, 69954, 3845, 262144⟩ := by
  decide +kernel

theorem context_11_69954_892224 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 69954 ⟨892224, by decide⟩ :=
  accepted_of_selected 11 69954 ⟨892224, by decide⟩ ⟨11, 2, 0, 892224, 69954, 3845, 262144⟩
    (by decide) selected_cut_34443

theorem selected_cut_34444 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 69955) = some ⟨11, 1, 0, 1736, 69955, 1, 262144⟩ := by
  decide +kernel

theorem context_11_69955_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 69955 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 69955 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 69955, 1, 262144⟩
    (by decide) selected_cut_34444

theorem unmarked_context_10_17488_892225 : frontier 11 ⟨892225, by decide⟩
    (prefixCache 10 17488) (prefixPartial 10 17488) = false := by
  decide +kernel

theorem node_context_10_17488_892225 : EJMOriginalGlobalDAGData.nodes 11 ⟨892225, by decide⟩ =
    .split (coordinate 10) (![⟨891950, by decide⟩,⟨892052, by decide⟩,⟨892224, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17488_892225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17488 ⟨892225, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17488
    ⟨892225, by decide⟩ (by decide) (![⟨891950, by decide⟩,⟨892052, by decide⟩,⟨892224, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_17488_892225 node_context_10_17488_892225
  intro a
  fin_cases a
  · exact context_11_69952_891950
  · exact context_11_69953_892052
  · exact context_11_69954_892224
  · exact context_11_69955_1736

theorem selected_cut_34445 : selected 10 ⟨892404, by decide⟩
    (prefixPartial 11 69956) = some ⟨11, 2, 0, 892404, 69956, 3377, 262144⟩ := by
  decide +kernel

theorem context_11_69956_892404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 69956 ⟨892404, by decide⟩ :=
  accepted_of_selected 11 69956 ⟨892404, by decide⟩ ⟨11, 2, 0, 892404, 69956, 3377, 262144⟩
    (by decide) selected_cut_34445

theorem selected_cut_34446 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 69957) = some ⟨11, 1, 0, 892405, 69957, 1, 262144⟩ := by
  decide +kernel

theorem context_11_69957_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 69957 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 69957 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 69957, 1, 262144⟩
    (by decide) selected_cut_34446

theorem selected_cut_34447 : selected 9 ⟨1738, by decide⟩
    (prefixPartial 12 279832) = some ⟨12, 1, 0, 1738, 279832, 1, 65536⟩ := by
  decide +kernel

theorem context_12_279832_1738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 279832 ⟨1738, by decide⟩ :=
  accepted_of_selected 12 279832 ⟨1738, by decide⟩ ⟨12, 1, 0, 1738, 279832, 1, 65536⟩
    (by decide) selected_cut_34447

theorem selected_cut_34448 : selected 9 ⟨892466, by decide⟩
    (prefixPartial 12 279833) = some ⟨12, 2, 0, 892466, 279833, 1549, 65536⟩ := by
  decide +kernel

theorem context_12_279833_892466 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 279833 ⟨892466, by decide⟩ :=
  accepted_of_selected 12 279833 ⟨892466, by decide⟩ ⟨12, 2, 0, 892466, 279833, 1549, 65536⟩
    (by decide) selected_cut_34448

theorem selected_cut_34449 : selected 9 ⟨892541, by decide⟩
    (prefixPartial 12 279834) = some ⟨12, 2, 0, 892541, 279834, 2401, 65536⟩ := by
  decide +kernel

theorem context_12_279834_892541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 279834 ⟨892541, by decide⟩ :=
  accepted_of_selected 12 279834 ⟨892541, by decide⟩ ⟨12, 2, 0, 892541, 279834, 2401, 65536⟩
    (by decide) selected_cut_34449

theorem selected_cut_34450 : selected 9 ⟨892609, by decide⟩
    (prefixPartial 12 279835) = some ⟨12, 2, 0, 892609, 279835, 2209, 65536⟩ := by
  decide +kernel

theorem context_12_279835_892609 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 279835 ⟨892609, by decide⟩ :=
  accepted_of_selected 12 279835 ⟨892609, by decide⟩ ⟨12, 2, 0, 892609, 279835, 2209, 65536⟩
    (by decide) selected_cut_34450

theorem unmarked_context_11_69958_892610 : frontier 10 ⟨892610, by decide⟩
    (prefixCache 11 69958) (prefixPartial 11 69958) = false := by
  decide +kernel

theorem node_context_11_69958_892610 : EJMOriginalGlobalDAGData.nodes 10 ⟨892610, by decide⟩ =
    .split (coordinate 11) (![⟨1738, by decide⟩,⟨892466, by decide⟩,⟨892541, by decide⟩,⟨892609, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_69958_892610 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 69958 ⟨892610, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 69958
    ⟨892610, by decide⟩ (by decide) (![⟨1738, by decide⟩,⟨892466, by decide⟩,⟨892541, by decide⟩,⟨892609, by decide⟩]) unmarked_context_11_69958_892610 node_context_11_69958_892610
  intro a
  fin_cases a
  · exact context_12_279832_1738
  · exact context_12_279833_892466
  · exact context_12_279834_892541
  · exact context_12_279835_892609

theorem selected_cut_34451 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 69959) = some ⟨11, 1, 0, 1736, 69959, 1, 262144⟩ := by
  decide +kernel

theorem context_11_69959_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 69959 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 69959 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 69959, 1, 262144⟩
    (by decide) selected_cut_34451

theorem unmarked_context_10_17489_892611 : frontier 11 ⟨892611, by decide⟩
    (prefixCache 10 17489) (prefixPartial 10 17489) = false := by
  decide +kernel

theorem node_context_10_17489_892611 : EJMOriginalGlobalDAGData.nodes 11 ⟨892611, by decide⟩ =
    .split (coordinate 10) (![⟨892404, by decide⟩,⟨892405, by decide⟩,⟨892610, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17489_892611 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17489 ⟨892611, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17489
    ⟨892611, by decide⟩ (by decide) (![⟨892404, by decide⟩,⟨892405, by decide⟩,⟨892610, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_17489_892611 node_context_10_17489_892611
  intro a
  fin_cases a
  · exact context_11_69956_892404
  · exact context_11_69957_892405
  · exact context_11_69958_892610
  · exact context_11_69959_1736

theorem selected_cut_34452 : selected 10 ⟨892786, by decide⟩
    (prefixPartial 11 69960) = some ⟨11, 2, 0, 892786, 69960, 2913, 262144⟩ := by
  decide +kernel

theorem context_11_69960_892786 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 69960 ⟨892786, by decide⟩ :=
  accepted_of_selected 11 69960 ⟨892786, by decide⟩ ⟨11, 2, 0, 892786, 69960, 2913, 262144⟩
    (by decide) selected_cut_34452

theorem selected_cut_34453 : selected 10 ⟨892915, by decide⟩
    (prefixPartial 11 69961) = some ⟨11, 2, 0, 892915, 69961, 2645, 262144⟩ := by
  decide +kernel

theorem context_11_69961_892915 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 69961 ⟨892915, by decide⟩ :=
  accepted_of_selected 11 69961 ⟨892915, by decide⟩ ⟨11, 2, 0, 892915, 69961, 2645, 262144⟩
    (by decide) selected_cut_34453

theorem selected_cut_34454 : selected 10 ⟨893041, by decide⟩
    (prefixPartial 11 69962) = some ⟨11, 2, 0, 893041, 69962, 2613, 262144⟩ := by
  decide +kernel

theorem context_11_69962_893041 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 69962 ⟨893041, by decide⟩ :=
  accepted_of_selected 11 69962 ⟨893041, by decide⟩ ⟨11, 2, 0, 893041, 69962, 2613, 262144⟩
    (by decide) selected_cut_34454

theorem selected_cut_34455 : selected 10 ⟨893095, by decide⟩
    (prefixPartial 11 69963) = some ⟨11, 2, 0, 893095, 69963, 901, 262144⟩ := by
  decide +kernel

theorem context_11_69963_893095 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 69963 ⟨893095, by decide⟩ :=
  accepted_of_selected 11 69963 ⟨893095, by decide⟩ ⟨11, 2, 0, 893095, 69963, 901, 262144⟩
    (by decide) selected_cut_34455

theorem unmarked_context_10_17490_893096 : frontier 11 ⟨893096, by decide⟩
    (prefixCache 10 17490) (prefixPartial 10 17490) = false := by
  decide +kernel

theorem node_context_10_17490_893096 : EJMOriginalGlobalDAGData.nodes 11 ⟨893096, by decide⟩ =
    .split (coordinate 10) (![⟨892786, by decide⟩,⟨892915, by decide⟩,⟨893041, by decide⟩,⟨893095, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17490_893096 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17490 ⟨893096, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17490
    ⟨893096, by decide⟩ (by decide) (![⟨892786, by decide⟩,⟨892915, by decide⟩,⟨893041, by decide⟩,⟨893095, by decide⟩]) unmarked_context_10_17490_893096 node_context_10_17490_893096
  intro a
  fin_cases a
  · exact context_11_69960_892786
  · exact context_11_69961_892915
  · exact context_11_69962_893041
  · exact context_11_69963_893095

theorem selected_cut_34456 : selected 11 ⟨3440, by decide⟩
    (prefixPartial 10 17491) = some ⟨10, 1, 0, 3440, 17491, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_17491_3440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17491 ⟨3440, by decide⟩ :=
  accepted_of_selected 10 17491 ⟨3440, by decide⟩ ⟨10, 1, 0, 3440, 17491, 1, 1048576⟩
    (by decide) selected_cut_34456

theorem unmarked_context_9_4372_893097 : frontier 12 ⟨893097, by decide⟩
    (prefixCache 9 4372) (prefixPartial 9 4372) = false := by
  decide +kernel

theorem node_context_9_4372_893097 : EJMOriginalGlobalDAGData.nodes 12 ⟨893097, by decide⟩ =
    .split (coordinate 9) (![⟨892225, by decide⟩,⟨892611, by decide⟩,⟨893096, by decide⟩,⟨3440, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4372_893097 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4372 ⟨893097, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4372
    ⟨893097, by decide⟩ (by decide) (![⟨892225, by decide⟩,⟨892611, by decide⟩,⟨893096, by decide⟩,⟨3440, by decide⟩]) unmarked_context_9_4372_893097 node_context_9_4372_893097
  intro a
  fin_cases a
  · exact context_10_17488_892225
  · exact context_10_17489_892611
  · exact context_10_17490_893096
  · exact context_10_17491_3440

theorem selected_cut_34457 : selected 12 ⟨893282, by decide⟩
    (prefixPartial 9 4373) = some ⟨9, 2, 0, 893282, 4373, 2293, 4194304⟩ := by
  decide +kernel

theorem context_9_4373_893282 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4373 ⟨893282, by decide⟩ :=
  accepted_of_selected 9 4373 ⟨893282, by decide⟩ ⟨9, 2, 0, 893282, 4373, 2293, 4194304⟩
    (by decide) selected_cut_34457

theorem selected_cut_34458 : selected 12 ⟨893314, by decide⟩
    (prefixPartial 9 4374) = some ⟨9, 2, 0, 893314, 4374, 321, 4194304⟩ := by
  decide +kernel

theorem context_9_4374_893314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4374 ⟨893314, by decide⟩ :=
  accepted_of_selected 9 4374 ⟨893314, by decide⟩ ⟨9, 2, 0, 893314, 4374, 321, 4194304⟩
    (by decide) selected_cut_34458

theorem selected_cut_34459 : selected 12 ⟨4601, by decide⟩
    (prefixPartial 9 4375) = some ⟨9, 1, 0, 4601, 4375, 1, 4194304⟩ := by
  decide +kernel

theorem context_9_4375_4601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4375 ⟨4601, by decide⟩ :=
  accepted_of_selected 9 4375 ⟨4601, by decide⟩ ⟨9, 1, 0, 4601, 4375, 1, 4194304⟩
    (by decide) selected_cut_34459

theorem unmarked_context_8_1093_893315 : frontier 13 ⟨893315, by decide⟩
    (prefixCache 8 1093) (prefixPartial 8 1093) = false := by
  decide +kernel

theorem node_context_8_1093_893315 : EJMOriginalGlobalDAGData.nodes 13 ⟨893315, by decide⟩ =
    .split (coordinate 8) (![⟨893097, by decide⟩,⟨893282, by decide⟩,⟨893314, by decide⟩,⟨4601, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1093_893315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1093 ⟨893315, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1093
    ⟨893315, by decide⟩ (by decide) (![⟨893097, by decide⟩,⟨893282, by decide⟩,⟨893314, by decide⟩,⟨4601, by decide⟩]) unmarked_context_8_1093_893315 node_context_8_1093_893315
  intro a
  fin_cases a
  · exact context_9_4372_893097
  · exact context_9_4373_893282
  · exact context_9_4374_893314
  · exact context_9_4375_4601

theorem selected_cut_34460 : selected 9 ⟨893404, by decide⟩
    (prefixPartial 12 280064) = some ⟨12, 2, 0, 893404, 280064, 2269, 65536⟩ := by
  decide +kernel

theorem context_12_280064_893404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 280064 ⟨893404, by decide⟩ :=
  accepted_of_selected 12 280064 ⟨893404, by decide⟩ ⟨12, 2, 0, 893404, 280064, 2269, 65536⟩
    (by decide) selected_cut_34460

theorem selected_cut_34461 : selected 9 ⟨893499, by decide⟩
    (prefixPartial 12 280065) = some ⟨12, 2, 0, 893499, 280065, 3581, 65536⟩ := by
  decide +kernel

theorem context_12_280065_893499 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 280065 ⟨893499, by decide⟩ :=
  accepted_of_selected 12 280065 ⟨893499, by decide⟩ ⟨12, 2, 0, 893499, 280065, 3581, 65536⟩
    (by decide) selected_cut_34461

theorem selected_cut_34462 : selected 9 ⟨893599, by decide⟩
    (prefixPartial 12 280066) = some ⟨12, 2, 0, 893599, 280066, 3737, 65536⟩ := by
  decide +kernel

theorem context_12_280066_893599 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 280066 ⟨893599, by decide⟩ :=
  accepted_of_selected 12 280066 ⟨893599, by decide⟩ ⟨12, 2, 0, 893599, 280066, 3737, 65536⟩
    (by decide) selected_cut_34462

theorem selected_cut_34463 : selected 9 ⟨893692, by decide⟩
    (prefixPartial 12 280067) = some ⟨12, 2, 0, 893692, 280067, 3945, 65536⟩ := by
  decide +kernel

theorem context_12_280067_893692 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 280067 ⟨893692, by decide⟩ :=
  accepted_of_selected 12 280067 ⟨893692, by decide⟩ ⟨12, 2, 0, 893692, 280067, 3945, 65536⟩
    (by decide) selected_cut_34463

theorem unmarked_context_11_70016_893693 : frontier 10 ⟨893693, by decide⟩
    (prefixCache 11 70016) (prefixPartial 11 70016) = false := by
  decide +kernel

theorem node_context_11_70016_893693 : EJMOriginalGlobalDAGData.nodes 10 ⟨893693, by decide⟩ =
    .split (coordinate 11) (![⟨893404, by decide⟩,⟨893499, by decide⟩,⟨893599, by decide⟩,⟨893692, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70016_893693 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70016 ⟨893693, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70016
    ⟨893693, by decide⟩ (by decide) (![⟨893404, by decide⟩,⟨893499, by decide⟩,⟨893599, by decide⟩,⟨893692, by decide⟩]) unmarked_context_11_70016_893693 node_context_11_70016_893693
  intro a
  fin_cases a
  · exact context_12_280064_893404
  · exact context_12_280065_893499
  · exact context_12_280066_893599
  · exact context_12_280067_893692

theorem selected_cut_34464 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 280068) = some ⟨12, 1, 0, 895, 280068, 1, 65536⟩ := by
  decide +kernel

theorem context_12_280068_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 280068 ⟨895, by decide⟩ :=
  accepted_of_selected 12 280068 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 280068, 1, 65536⟩
    (by decide) selected_cut_34464

theorem selected_cut_34465 : selected 9 ⟨893744, by decide⟩
    (prefixPartial 12 280069) = some ⟨12, 2, 0, 893744, 280069, 1829, 65536⟩ := by
  decide +kernel

theorem context_12_280069_893744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 280069 ⟨893744, by decide⟩ :=
  accepted_of_selected 12 280069 ⟨893744, by decide⟩ ⟨12, 2, 0, 893744, 280069, 1829, 65536⟩
    (by decide) selected_cut_34465

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
