/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover367
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_35331 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 71322) = some ⟨11, 1, 0, 900587, 71322, 1, 262144⟩ := by
  decide +kernel

theorem context_11_71322_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71322 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 71322 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 71322, 1, 262144⟩
    (by decide) selected_cut_35331

theorem selected_cut_35332 : selected 10 ⟨927538, by decide⟩
    (prefixPartial 11 71323) = some ⟨11, 2, 0, 927538, 71323, 3605, 262144⟩ := by
  decide +kernel

theorem context_11_71323_927538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71323 ⟨927538, by decide⟩ :=
  accepted_of_selected 11 71323 ⟨927538, by decide⟩ ⟨11, 2, 0, 927538, 71323, 3605, 262144⟩
    (by decide) selected_cut_35332

theorem unmarked_context_10_17830_927539 : frontier 11 ⟨927539, by decide⟩
    (prefixCache 10 17830) (prefixPartial 10 17830) = false := by
  decide +kernel

theorem node_context_10_17830_927539 : EJMOriginalGlobalDAGData.nodes 11 ⟨927539, by decide⟩ =
    .split (coordinate 10) (![⟨927407, by decide⟩,⟨927453, by decide⟩,⟨900587, by decide⟩,⟨927538, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17830_927539 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17830 ⟨927539, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17830
    ⟨927539, by decide⟩ (by decide) (![⟨927407, by decide⟩,⟨927453, by decide⟩,⟨900587, by decide⟩,⟨927538, by decide⟩]) unmarked_context_10_17830_927539 node_context_10_17830_927539
  intro a
  fin_cases a
  · exact context_11_71320_927407
  · exact context_11_71321_927453
  · exact context_11_71322_900587
  · exact context_11_71323_927538

theorem selected_cut_35333 : selected 10 ⟨927575, by decide⟩
    (prefixPartial 11 71324) = some ⟨11, 2, 0, 927575, 71324, 1345, 262144⟩ := by
  decide +kernel

theorem context_11_71324_927575 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71324 ⟨927575, by decide⟩ :=
  accepted_of_selected 11 71324 ⟨927575, by decide⟩ ⟨11, 2, 0, 927575, 71324, 1345, 262144⟩
    (by decide) selected_cut_35333

theorem selected_cut_35334 : selected 10 ⟨927608, by decide⟩
    (prefixPartial 11 71325) = some ⟨11, 2, 0, 927608, 71325, 1145, 262144⟩ := by
  decide +kernel

theorem context_11_71325_927608 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71325 ⟨927608, by decide⟩ :=
  accepted_of_selected 11 71325 ⟨927608, by decide⟩ ⟨11, 2, 0, 927608, 71325, 1145, 262144⟩
    (by decide) selected_cut_35334

theorem selected_cut_35335 : selected 10 ⟨927657, by decide⟩
    (prefixPartial 11 71326) = some ⟨11, 2, 0, 927657, 71326, 1597, 262144⟩ := by
  decide +kernel

theorem context_11_71326_927657 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71326 ⟨927657, by decide⟩ :=
  accepted_of_selected 11 71326 ⟨927657, by decide⟩ ⟨11, 2, 0, 927657, 71326, 1597, 262144⟩
    (by decide) selected_cut_35335

theorem selected_cut_35336 : selected 10 ⟨927695, by decide⟩
    (prefixPartial 11 71327) = some ⟨11, 2, 0, 927695, 71327, 1465, 262144⟩ := by
  decide +kernel

theorem context_11_71327_927695 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71327 ⟨927695, by decide⟩ :=
  accepted_of_selected 11 71327 ⟨927695, by decide⟩ ⟨11, 2, 0, 927695, 71327, 1465, 262144⟩
    (by decide) selected_cut_35336

theorem unmarked_context_10_17831_927696 : frontier 11 ⟨927696, by decide⟩
    (prefixCache 10 17831) (prefixPartial 10 17831) = false := by
  decide +kernel

theorem node_context_10_17831_927696 : EJMOriginalGlobalDAGData.nodes 11 ⟨927696, by decide⟩ =
    .split (coordinate 10) (![⟨927575, by decide⟩,⟨927608, by decide⟩,⟨927657, by decide⟩,⟨927695, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17831_927696 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17831 ⟨927696, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17831
    ⟨927696, by decide⟩ (by decide) (![⟨927575, by decide⟩,⟨927608, by decide⟩,⟨927657, by decide⟩,⟨927695, by decide⟩]) unmarked_context_10_17831_927696 node_context_10_17831_927696
  intro a
  fin_cases a
  · exact context_11_71324_927575
  · exact context_11_71325_927608
  · exact context_11_71326_927657
  · exact context_11_71327_927695

theorem unmarked_context_9_4457_927697 : frontier 12 ⟨927697, by decide⟩
    (prefixCache 9 4457) (prefixPartial 9 4457) = false := by
  decide +kernel

theorem node_context_9_4457_927697 : EJMOriginalGlobalDAGData.nodes 12 ⟨927697, by decide⟩ =
    .split (coordinate 9) (![⟨927350, by decide⟩,⟨893098, by decide⟩,⟨927539, by decide⟩,⟨927696, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4457_927697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4457 ⟨927697, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4457
    ⟨927697, by decide⟩ (by decide) (![⟨927350, by decide⟩,⟨893098, by decide⟩,⟨927539, by decide⟩,⟨927696, by decide⟩]) unmarked_context_9_4457_927697 node_context_9_4457_927697
  intro a
  fin_cases a
  · exact context_10_17828_927350
  · exact context_10_17829_893098
  · exact context_10_17830_927539
  · exact context_10_17831_927696

theorem selected_cut_35337 : selected 9 ⟨927737, by decide⟩
    (prefixPartial 12 285312) = some ⟨12, 2, 0, 927737, 285312, 477, 65536⟩ := by
  decide +kernel

theorem context_12_285312_927737 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285312 ⟨927737, by decide⟩ :=
  accepted_of_selected 12 285312 ⟨927737, by decide⟩ ⟨12, 2, 0, 927737, 285312, 477, 65536⟩
    (by decide) selected_cut_35337

theorem selected_cut_35338 : selected 9 ⟨927759, by decide⟩
    (prefixPartial 12 285313) = some ⟨12, 2, 0, 927759, 285313, 1361, 65536⟩ := by
  decide +kernel

theorem context_12_285313_927759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285313 ⟨927759, by decide⟩ :=
  accepted_of_selected 12 285313 ⟨927759, by decide⟩ ⟨12, 2, 0, 927759, 285313, 1361, 65536⟩
    (by decide) selected_cut_35338

theorem selected_cut_35339 : selected 9 ⟨927778, by decide⟩
    (prefixPartial 12 285314) = some ⟨12, 2, 0, 927778, 285314, 1257, 65536⟩ := by
  decide +kernel

theorem context_12_285314_927778 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285314 ⟨927778, by decide⟩ :=
  accepted_of_selected 12 285314 ⟨927778, by decide⟩ ⟨12, 2, 0, 927778, 285314, 1257, 65536⟩
    (by decide) selected_cut_35339

theorem selected_cut_35340 : selected 9 ⟨927794, by decide⟩
    (prefixPartial 12 285315) = some ⟨12, 2, 0, 927794, 285315, 1297, 65536⟩ := by
  decide +kernel

theorem context_12_285315_927794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285315 ⟨927794, by decide⟩ :=
  accepted_of_selected 12 285315 ⟨927794, by decide⟩ ⟨12, 2, 0, 927794, 285315, 1297, 65536⟩
    (by decide) selected_cut_35340

theorem unmarked_context_11_71328_927795 : frontier 10 ⟨927795, by decide⟩
    (prefixCache 11 71328) (prefixPartial 11 71328) = false := by
  decide +kernel

theorem node_context_11_71328_927795 : EJMOriginalGlobalDAGData.nodes 10 ⟨927795, by decide⟩ =
    .split (coordinate 11) (![⟨927737, by decide⟩,⟨927759, by decide⟩,⟨927778, by decide⟩,⟨927794, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71328_927795 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71328 ⟨927795, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71328
    ⟨927795, by decide⟩ (by decide) (![⟨927737, by decide⟩,⟨927759, by decide⟩,⟨927778, by decide⟩,⟨927794, by decide⟩]) unmarked_context_11_71328_927795 node_context_11_71328_927795
  intro a
  fin_cases a
  · exact context_12_285312_927737
  · exact context_12_285313_927759
  · exact context_12_285314_927778
  · exact context_12_285315_927794

theorem selected_cut_35341 : selected 9 ⟨927823, by decide⟩
    (prefixPartial 12 285316) = some ⟨12, 2, 0, 927823, 285316, 1133, 65536⟩ := by
  decide +kernel

theorem context_12_285316_927823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285316 ⟨927823, by decide⟩ :=
  accepted_of_selected 12 285316 ⟨927823, by decide⟩ ⟨12, 2, 0, 927823, 285316, 1133, 65536⟩
    (by decide) selected_cut_35341

theorem selected_cut_35342 : selected 9 ⟨927847, by decide⟩
    (prefixPartial 12 285317) = some ⟨12, 2, 0, 927847, 285317, 1305, 65536⟩ := by
  decide +kernel

theorem context_12_285317_927847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285317 ⟨927847, by decide⟩ :=
  accepted_of_selected 12 285317 ⟨927847, by decide⟩ ⟨12, 2, 0, 927847, 285317, 1305, 65536⟩
    (by decide) selected_cut_35342

theorem selected_cut_35343 : selected 9 ⟨927860, by decide⟩
    (prefixPartial 12 285318) = some ⟨12, 2, 0, 927860, 285318, 1125, 65536⟩ := by
  decide +kernel

theorem context_12_285318_927860 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285318 ⟨927860, by decide⟩ :=
  accepted_of_selected 12 285318 ⟨927860, by decide⟩ ⟨12, 2, 0, 927860, 285318, 1125, 65536⟩
    (by decide) selected_cut_35343

theorem selected_cut_35344 : selected 9 ⟨927877, by decide⟩
    (prefixPartial 12 285319) = some ⟨12, 2, 0, 927877, 285319, 1177, 65536⟩ := by
  decide +kernel

theorem context_12_285319_927877 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285319 ⟨927877, by decide⟩ :=
  accepted_of_selected 12 285319 ⟨927877, by decide⟩ ⟨12, 2, 0, 927877, 285319, 1177, 65536⟩
    (by decide) selected_cut_35344

theorem unmarked_context_11_71329_927878 : frontier 10 ⟨927878, by decide⟩
    (prefixCache 11 71329) (prefixPartial 11 71329) = false := by
  decide +kernel

theorem node_context_11_71329_927878 : EJMOriginalGlobalDAGData.nodes 10 ⟨927878, by decide⟩ =
    .split (coordinate 11) (![⟨927823, by decide⟩,⟨927847, by decide⟩,⟨927860, by decide⟩,⟨927877, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71329_927878 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71329 ⟨927878, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71329
    ⟨927878, by decide⟩ (by decide) (![⟨927823, by decide⟩,⟨927847, by decide⟩,⟨927860, by decide⟩,⟨927877, by decide⟩]) unmarked_context_11_71329_927878 node_context_11_71329_927878
  intro a
  fin_cases a
  · exact context_12_285316_927823
  · exact context_12_285317_927847
  · exact context_12_285318_927860
  · exact context_12_285319_927877

theorem selected_cut_35345 : selected 10 ⟨927951, by decide⟩
    (prefixPartial 11 71330) = some ⟨11, 2, 0, 927951, 71330, 3569, 262144⟩ := by
  decide +kernel

theorem context_11_71330_927951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71330 ⟨927951, by decide⟩ :=
  accepted_of_selected 11 71330 ⟨927951, by decide⟩ ⟨11, 2, 0, 927951, 71330, 3569, 262144⟩
    (by decide) selected_cut_35345

theorem selected_cut_35346 : selected 9 ⟨927974, by decide⟩
    (prefixPartial 12 285324) = some ⟨12, 2, 0, 927974, 285324, 1165, 65536⟩ := by
  decide +kernel

theorem context_12_285324_927974 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285324 ⟨927974, by decide⟩ :=
  accepted_of_selected 12 285324 ⟨927974, by decide⟩ ⟨12, 2, 0, 927974, 285324, 1165, 65536⟩
    (by decide) selected_cut_35346

theorem selected_cut_35347 : selected 9 ⟨928004, by decide⟩
    (prefixPartial 12 285325) = some ⟨12, 2, 0, 928004, 285325, 1253, 65536⟩ := by
  decide +kernel

theorem context_12_285325_928004 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285325 ⟨928004, by decide⟩ :=
  accepted_of_selected 12 285325 ⟨928004, by decide⟩ ⟨12, 2, 0, 928004, 285325, 1253, 65536⟩
    (by decide) selected_cut_35347

theorem selected_cut_35348 : selected 9 ⟨928020, by decide⟩
    (prefixPartial 12 285326) = some ⟨12, 2, 0, 928020, 285326, 1117, 65536⟩ := by
  decide +kernel

theorem context_12_285326_928020 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285326 ⟨928020, by decide⟩ :=
  accepted_of_selected 12 285326 ⟨928020, by decide⟩ ⟨12, 2, 0, 928020, 285326, 1117, 65536⟩
    (by decide) selected_cut_35348

theorem selected_cut_35349 : selected 9 ⟨928041, by decide⟩
    (prefixPartial 12 285327) = some ⟨12, 2, 0, 928041, 285327, 1149, 65536⟩ := by
  decide +kernel

theorem context_12_285327_928041 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285327 ⟨928041, by decide⟩ :=
  accepted_of_selected 12 285327 ⟨928041, by decide⟩ ⟨12, 2, 0, 928041, 285327, 1149, 65536⟩
    (by decide) selected_cut_35349

theorem unmarked_context_11_71331_928042 : frontier 10 ⟨928042, by decide⟩
    (prefixCache 11 71331) (prefixPartial 11 71331) = false := by
  decide +kernel

theorem node_context_11_71331_928042 : EJMOriginalGlobalDAGData.nodes 10 ⟨928042, by decide⟩ =
    .split (coordinate 11) (![⟨927974, by decide⟩,⟨928004, by decide⟩,⟨928020, by decide⟩,⟨928041, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71331_928042 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71331 ⟨928042, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71331
    ⟨928042, by decide⟩ (by decide) (![⟨927974, by decide⟩,⟨928004, by decide⟩,⟨928020, by decide⟩,⟨928041, by decide⟩]) unmarked_context_11_71331_928042 node_context_11_71331_928042
  intro a
  fin_cases a
  · exact context_12_285324_927974
  · exact context_12_285325_928004
  · exact context_12_285326_928020
  · exact context_12_285327_928041

theorem unmarked_context_10_17832_928043 : frontier 11 ⟨928043, by decide⟩
    (prefixCache 10 17832) (prefixPartial 10 17832) = false := by
  decide +kernel

theorem node_context_10_17832_928043 : EJMOriginalGlobalDAGData.nodes 11 ⟨928043, by decide⟩ =
    .split (coordinate 10) (![⟨927795, by decide⟩,⟨927878, by decide⟩,⟨927951, by decide⟩,⟨928042, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17832_928043 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17832 ⟨928043, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17832
    ⟨928043, by decide⟩ (by decide) (![⟨927795, by decide⟩,⟨927878, by decide⟩,⟨927951, by decide⟩,⟨928042, by decide⟩]) unmarked_context_10_17832_928043 node_context_10_17832_928043
  intro a
  fin_cases a
  · exact context_11_71328_927795
  · exact context_11_71329_927878
  · exact context_11_71330_927951
  · exact context_11_71331_928042

theorem selected_cut_35350 : selected 10 ⟨928103, by decide⟩
    (prefixPartial 11 71332) = some ⟨11, 2, 0, 928103, 71332, 2797, 262144⟩ := by
  decide +kernel

theorem context_11_71332_928103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71332 ⟨928103, by decide⟩ :=
  accepted_of_selected 11 71332 ⟨928103, by decide⟩ ⟨11, 2, 0, 928103, 71332, 2797, 262144⟩
    (by decide) selected_cut_35350

theorem selected_cut_35351 : selected 10 ⟨928137, by decide⟩
    (prefixPartial 11 71333) = some ⟨11, 2, 0, 928137, 71333, 1789, 262144⟩ := by
  decide +kernel

theorem context_11_71333_928137 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71333 ⟨928137, by decide⟩ :=
  accepted_of_selected 11 71333 ⟨928137, by decide⟩ ⟨11, 2, 0, 928137, 71333, 1789, 262144⟩
    (by decide) selected_cut_35351

theorem selected_cut_35352 : selected 10 ⟨928171, by decide⟩
    (prefixPartial 11 71334) = some ⟨11, 2, 0, 928171, 71334, 1605, 262144⟩ := by
  decide +kernel

theorem context_11_71334_928171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71334 ⟨928171, by decide⟩ :=
  accepted_of_selected 11 71334 ⟨928171, by decide⟩ ⟨11, 2, 0, 928171, 71334, 1605, 262144⟩
    (by decide) selected_cut_35352

theorem selected_cut_35353 : selected 10 ⟨928220, by decide⟩
    (prefixPartial 11 71335) = some ⟨11, 2, 0, 928220, 71335, 2409, 262144⟩ := by
  decide +kernel

theorem context_11_71335_928220 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71335 ⟨928220, by decide⟩ :=
  accepted_of_selected 11 71335 ⟨928220, by decide⟩ ⟨11, 2, 0, 928220, 71335, 2409, 262144⟩
    (by decide) selected_cut_35353

theorem unmarked_context_10_17833_928221 : frontier 11 ⟨928221, by decide⟩
    (prefixCache 10 17833) (prefixPartial 10 17833) = false := by
  decide +kernel

theorem node_context_10_17833_928221 : EJMOriginalGlobalDAGData.nodes 11 ⟨928221, by decide⟩ =
    .split (coordinate 10) (![⟨928103, by decide⟩,⟨928137, by decide⟩,⟨928171, by decide⟩,⟨928220, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17833_928221 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17833 ⟨928221, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17833
    ⟨928221, by decide⟩ (by decide) (![⟨928103, by decide⟩,⟨928137, by decide⟩,⟨928171, by decide⟩,⟨928220, by decide⟩]) unmarked_context_10_17833_928221 node_context_10_17833_928221
  intro a
  fin_cases a
  · exact context_11_71332_928103
  · exact context_11_71333_928137
  · exact context_11_71334_928171
  · exact context_11_71335_928220

theorem selected_cut_35354 : selected 11 ⟨928287, by decide⟩
    (prefixPartial 10 17834) = some ⟨10, 2, 0, 928287, 17834, 3249, 1048576⟩ := by
  decide +kernel

theorem context_10_17834_928287 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17834 ⟨928287, by decide⟩ :=
  accepted_of_selected 10 17834 ⟨928287, by decide⟩ ⟨10, 2, 0, 928287, 17834, 3249, 1048576⟩
    (by decide) selected_cut_35354

theorem selected_cut_35355 : selected 11 ⟨928329, by decide⟩
    (prefixPartial 10 17835) = some ⟨10, 2, 0, 928329, 17835, 1697, 1048576⟩ := by
  decide +kernel

theorem context_10_17835_928329 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17835 ⟨928329, by decide⟩ :=
  accepted_of_selected 10 17835 ⟨928329, by decide⟩ ⟨10, 2, 0, 928329, 17835, 1697, 1048576⟩
    (by decide) selected_cut_35355

theorem unmarked_context_9_4458_928330 : frontier 12 ⟨928330, by decide⟩
    (prefixCache 9 4458) (prefixPartial 9 4458) = false := by
  decide +kernel

theorem node_context_9_4458_928330 : EJMOriginalGlobalDAGData.nodes 12 ⟨928330, by decide⟩ =
    .split (coordinate 9) (![⟨928043, by decide⟩,⟨928221, by decide⟩,⟨928287, by decide⟩,⟨928329, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4458_928330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4458 ⟨928330, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4458
    ⟨928330, by decide⟩ (by decide) (![⟨928043, by decide⟩,⟨928221, by decide⟩,⟨928287, by decide⟩,⟨928329, by decide⟩]) unmarked_context_9_4458_928330 node_context_9_4458_928330
  intro a
  fin_cases a
  · exact context_10_17832_928043
  · exact context_10_17833_928221
  · exact context_10_17834_928287
  · exact context_10_17835_928329

theorem selected_cut_35356 : selected 10 ⟨928394, by decide⟩
    (prefixPartial 11 71344) = some ⟨11, 2, 0, 928394, 71344, 3145, 262144⟩ := by
  decide +kernel

theorem context_11_71344_928394 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71344 ⟨928394, by decide⟩ :=
  accepted_of_selected 11 71344 ⟨928394, by decide⟩ ⟨11, 2, 0, 928394, 71344, 3145, 262144⟩
    (by decide) selected_cut_35356

theorem selected_cut_35357 : selected 10 ⟨928451, by decide⟩
    (prefixPartial 11 71345) = some ⟨11, 2, 0, 928451, 71345, 2569, 262144⟩ := by
  decide +kernel

theorem context_11_71345_928451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71345 ⟨928451, by decide⟩ :=
  accepted_of_selected 11 71345 ⟨928451, by decide⟩ ⟨11, 2, 0, 928451, 71345, 2569, 262144⟩
    (by decide) selected_cut_35357

theorem selected_cut_35358 : selected 10 ⟨928498, by decide⟩
    (prefixPartial 11 71346) = some ⟨11, 2, 0, 928498, 71346, 1733, 262144⟩ := by
  decide +kernel

theorem context_11_71346_928498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71346 ⟨928498, by decide⟩ :=
  accepted_of_selected 11 71346 ⟨928498, by decide⟩ ⟨11, 2, 0, 928498, 71346, 1733, 262144⟩
    (by decide) selected_cut_35358

theorem selected_cut_35359 : selected 10 ⟨928579, by decide⟩
    (prefixPartial 11 71347) = some ⟨11, 2, 0, 928579, 71347, 2265, 262144⟩ := by
  decide +kernel

theorem context_11_71347_928579 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71347 ⟨928579, by decide⟩ :=
  accepted_of_selected 11 71347 ⟨928579, by decide⟩ ⟨11, 2, 0, 928579, 71347, 2265, 262144⟩
    (by decide) selected_cut_35359

theorem unmarked_context_10_17836_928580 : frontier 11 ⟨928580, by decide⟩
    (prefixCache 10 17836) (prefixPartial 10 17836) = false := by
  decide +kernel

theorem node_context_10_17836_928580 : EJMOriginalGlobalDAGData.nodes 11 ⟨928580, by decide⟩ =
    .split (coordinate 10) (![⟨928394, by decide⟩,⟨928451, by decide⟩,⟨928498, by decide⟩,⟨928579, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17836_928580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17836 ⟨928580, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17836
    ⟨928580, by decide⟩ (by decide) (![⟨928394, by decide⟩,⟨928451, by decide⟩,⟨928498, by decide⟩,⟨928579, by decide⟩]) unmarked_context_10_17836_928580 node_context_10_17836_928580
  intro a
  fin_cases a
  · exact context_11_71344_928394
  · exact context_11_71345_928451
  · exact context_11_71346_928498
  · exact context_11_71347_928579

theorem selected_cut_35360 : selected 11 ⟨928672, by decide⟩
    (prefixPartial 10 17837) = some ⟨10, 2, 0, 928672, 17837, 2669, 1048576⟩ := by
  decide +kernel

theorem context_10_17837_928672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17837 ⟨928672, by decide⟩ :=
  accepted_of_selected 10 17837 ⟨928672, by decide⟩ ⟨10, 2, 0, 928672, 17837, 2669, 1048576⟩
    (by decide) selected_cut_35360

theorem selected_cut_35361 : selected 11 ⟨928708, by decide⟩
    (prefixPartial 10 17838) = some ⟨10, 2, 0, 928708, 17838, 649, 1048576⟩ := by
  decide +kernel

theorem context_10_17838_928708 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17838 ⟨928708, by decide⟩ :=
  accepted_of_selected 10 17838 ⟨928708, by decide⟩ ⟨10, 2, 0, 928708, 17838, 649, 1048576⟩
    (by decide) selected_cut_35361

theorem selected_cut_35362 : selected 11 ⟨928718, by decide⟩
    (prefixPartial 10 17839) = some ⟨10, 2, 0, 928718, 17839, 97, 1048576⟩ := by
  decide +kernel

theorem context_10_17839_928718 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17839 ⟨928718, by decide⟩ :=
  accepted_of_selected 10 17839 ⟨928718, by decide⟩ ⟨10, 2, 0, 928718, 17839, 97, 1048576⟩
    (by decide) selected_cut_35362

theorem unmarked_context_9_4459_928719 : frontier 12 ⟨928719, by decide⟩
    (prefixCache 9 4459) (prefixPartial 9 4459) = false := by
  decide +kernel

theorem node_context_9_4459_928719 : EJMOriginalGlobalDAGData.nodes 12 ⟨928719, by decide⟩ =
    .split (coordinate 9) (![⟨928580, by decide⟩,⟨928672, by decide⟩,⟨928708, by decide⟩,⟨928718, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4459_928719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4459 ⟨928719, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4459
    ⟨928719, by decide⟩ (by decide) (![⟨928580, by decide⟩,⟨928672, by decide⟩,⟨928708, by decide⟩,⟨928718, by decide⟩]) unmarked_context_9_4459_928719 node_context_9_4459_928719
  intro a
  fin_cases a
  · exact context_10_17836_928580
  · exact context_10_17837_928672
  · exact context_10_17838_928708
  · exact context_10_17839_928718

theorem unmarked_context_8_1114_928720 : frontier 13 ⟨928720, by decide⟩
    (prefixCache 8 1114) (prefixPartial 8 1114) = false := by
  decide +kernel

theorem node_context_8_1114_928720 : EJMOriginalGlobalDAGData.nodes 13 ⟨928720, by decide⟩ =
    .split (coordinate 8) (![⟨926817, by decide⟩,⟨927697, by decide⟩,⟨928330, by decide⟩,⟨928719, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1114_928720 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1114 ⟨928720, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1114
    ⟨928720, by decide⟩ (by decide) (![⟨926817, by decide⟩,⟨927697, by decide⟩,⟨928330, by decide⟩,⟨928719, by decide⟩]) unmarked_context_8_1114_928720 node_context_8_1114_928720
  intro a
  fin_cases a
  · exact context_9_4456_926817
  · exact context_9_4457_927697
  · exact context_9_4458_928330
  · exact context_9_4459_928719

theorem selected_cut_35363 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 285440) = some ⟨12, 1, 0, 34034, 285440, 1, 65536⟩ := by
  decide +kernel

theorem context_12_285440_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285440 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 285440 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 285440, 1, 65536⟩
    (by decide) selected_cut_35363

theorem selected_cut_35364 : selected 9 ⟨928783, by decide⟩
    (prefixPartial 12 285441) = some ⟨12, 2, 0, 928783, 285441, 3613, 65536⟩ := by
  decide +kernel

theorem context_12_285441_928783 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285441 ⟨928783, by decide⟩ :=
  accepted_of_selected 12 285441 ⟨928783, by decide⟩ ⟨12, 2, 0, 928783, 285441, 3613, 65536⟩
    (by decide) selected_cut_35364

theorem selected_cut_35365 : selected 9 ⟨928840, by decide⟩
    (prefixPartial 12 285442) = some ⟨12, 2, 0, 928840, 285442, 3761, 65536⟩ := by
  decide +kernel

theorem context_12_285442_928840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285442 ⟨928840, by decide⟩ :=
  accepted_of_selected 12 285442 ⟨928840, by decide⟩ ⟨12, 2, 0, 928840, 285442, 3761, 65536⟩
    (by decide) selected_cut_35365

theorem selected_cut_35366 : selected 9 ⟨928892, by decide⟩
    (prefixPartial 12 285443) = some ⟨12, 2, 0, 928892, 285443, 3485, 65536⟩ := by
  decide +kernel

theorem context_12_285443_928892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285443 ⟨928892, by decide⟩ :=
  accepted_of_selected 12 285443 ⟨928892, by decide⟩ ⟨12, 2, 0, 928892, 285443, 3485, 65536⟩
    (by decide) selected_cut_35366

theorem unmarked_context_11_71360_928893 : frontier 10 ⟨928893, by decide⟩
    (prefixCache 11 71360) (prefixPartial 11 71360) = false := by
  decide +kernel

theorem node_context_11_71360_928893 : EJMOriginalGlobalDAGData.nodes 10 ⟨928893, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨928783, by decide⟩,⟨928840, by decide⟩,⟨928892, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71360_928893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71360 ⟨928893, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71360
    ⟨928893, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨928783, by decide⟩,⟨928840, by decide⟩,⟨928892, by decide⟩]) unmarked_context_11_71360_928893 node_context_11_71360_928893
  intro a
  fin_cases a
  · exact context_12_285440_34034
  · exact context_12_285441_928783
  · exact context_12_285442_928840
  · exact context_12_285443_928892

theorem selected_cut_35367 : selected 9 ⟨928952, by decide⟩
    (prefixPartial 12 285444) = some ⟨12, 2, 0, 928952, 285444, 2065, 65536⟩ := by
  decide +kernel

theorem context_12_285444_928952 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285444 ⟨928952, by decide⟩ :=
  accepted_of_selected 12 285444 ⟨928952, by decide⟩ ⟨12, 2, 0, 928952, 285444, 2065, 65536⟩
    (by decide) selected_cut_35367

theorem selected_cut_35368 : selected 9 ⟨929007, by decide⟩
    (prefixPartial 12 285445) = some ⟨12, 2, 0, 929007, 285445, 3181, 65536⟩ := by
  decide +kernel

theorem context_12_285445_929007 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285445 ⟨929007, by decide⟩ :=
  accepted_of_selected 12 285445 ⟨929007, by decide⟩ ⟨12, 2, 0, 929007, 285445, 3181, 65536⟩
    (by decide) selected_cut_35368

theorem selected_cut_35369 : selected 9 ⟨929071, by decide⟩
    (prefixPartial 12 285446) = some ⟨12, 2, 0, 929071, 285446, 3221, 65536⟩ := by
  decide +kernel

theorem context_12_285446_929071 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285446 ⟨929071, by decide⟩ :=
  accepted_of_selected 12 285446 ⟨929071, by decide⟩ ⟨12, 2, 0, 929071, 285446, 3221, 65536⟩
    (by decide) selected_cut_35369

theorem selected_cut_35370 : selected 9 ⟨929118, by decide⟩
    (prefixPartial 12 285447) = some ⟨12, 2, 0, 929118, 285447, 3037, 65536⟩ := by
  decide +kernel

theorem context_12_285447_929118 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285447 ⟨929118, by decide⟩ :=
  accepted_of_selected 12 285447 ⟨929118, by decide⟩ ⟨12, 2, 0, 929118, 285447, 3037, 65536⟩
    (by decide) selected_cut_35370

theorem unmarked_context_11_71361_929119 : frontier 10 ⟨929119, by decide⟩
    (prefixCache 11 71361) (prefixPartial 11 71361) = false := by
  decide +kernel

theorem node_context_11_71361_929119 : EJMOriginalGlobalDAGData.nodes 10 ⟨929119, by decide⟩ =
    .split (coordinate 11) (![⟨928952, by decide⟩,⟨929007, by decide⟩,⟨929071, by decide⟩,⟨929118, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71361_929119 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71361 ⟨929119, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71361
    ⟨929119, by decide⟩ (by decide) (![⟨928952, by decide⟩,⟨929007, by decide⟩,⟨929071, by decide⟩,⟨929118, by decide⟩]) unmarked_context_11_71361_929119 node_context_11_71361_929119
  intro a
  fin_cases a
  · exact context_12_285444_928952
  · exact context_12_285445_929007
  · exact context_12_285446_929071
  · exact context_12_285447_929118

theorem selected_cut_35371 : selected 9 ⟨929203, by decide⟩
    (prefixPartial 12 285448) = some ⟨12, 2, 0, 929203, 285448, 3917, 65536⟩ := by
  decide +kernel

theorem context_12_285448_929203 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285448 ⟨929203, by decide⟩ :=
  accepted_of_selected 12 285448 ⟨929203, by decide⟩ ⟨12, 2, 0, 929203, 285448, 3917, 65536⟩
    (by decide) selected_cut_35371

theorem selected_cut_35372 : selected 9 ⟨929267, by decide⟩
    (prefixPartial 12 285449) = some ⟨12, 2, 0, 929267, 285449, 3529, 65536⟩ := by
  decide +kernel

theorem context_12_285449_929267 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285449 ⟨929267, by decide⟩ :=
  accepted_of_selected 12 285449 ⟨929267, by decide⟩ ⟨12, 2, 0, 929267, 285449, 3529, 65536⟩
    (by decide) selected_cut_35372

theorem selected_cut_35373 : selected 9 ⟨929335, by decide⟩
    (prefixPartial 12 285450) = some ⟨12, 2, 0, 929335, 285450, 3461, 65536⟩ := by
  decide +kernel

theorem context_12_285450_929335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285450 ⟨929335, by decide⟩ :=
  accepted_of_selected 12 285450 ⟨929335, by decide⟩ ⟨12, 2, 0, 929335, 285450, 3461, 65536⟩
    (by decide) selected_cut_35373

theorem selected_cut_35374 : selected 9 ⟨929400, by decide⟩
    (prefixPartial 12 285451) = some ⟨12, 2, 0, 929400, 285451, 3489, 65536⟩ := by
  decide +kernel

theorem context_12_285451_929400 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285451 ⟨929400, by decide⟩ :=
  accepted_of_selected 12 285451 ⟨929400, by decide⟩ ⟨12, 2, 0, 929400, 285451, 3489, 65536⟩
    (by decide) selected_cut_35374

theorem unmarked_context_11_71362_929401 : frontier 10 ⟨929401, by decide⟩
    (prefixCache 11 71362) (prefixPartial 11 71362) = false := by
  decide +kernel

theorem node_context_11_71362_929401 : EJMOriginalGlobalDAGData.nodes 10 ⟨929401, by decide⟩ =
    .split (coordinate 11) (![⟨929203, by decide⟩,⟨929267, by decide⟩,⟨929335, by decide⟩,⟨929400, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71362_929401 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71362 ⟨929401, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71362
    ⟨929401, by decide⟩ (by decide) (![⟨929203, by decide⟩,⟨929267, by decide⟩,⟨929335, by decide⟩,⟨929400, by decide⟩]) unmarked_context_11_71362_929401 node_context_11_71362_929401
  intro a
  fin_cases a
  · exact context_12_285448_929203
  · exact context_12_285449_929267
  · exact context_12_285450_929335
  · exact context_12_285451_929400

theorem selected_cut_35375 : selected 9 ⟨4596, by decide⟩
    (prefixPartial 12 285452) = some ⟨12, 1, 0, 4596, 285452, 1, 65536⟩ := by
  decide +kernel

theorem context_12_285452_4596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285452 ⟨4596, by decide⟩ :=
  accepted_of_selected 12 285452 ⟨4596, by decide⟩ ⟨12, 1, 0, 4596, 285452, 1, 65536⟩
    (by decide) selected_cut_35375

theorem selected_cut_35376 : selected 9 ⟨929450, by decide⟩
    (prefixPartial 12 285453) = some ⟨12, 2, 0, 929450, 285453, 3285, 65536⟩ := by
  decide +kernel

theorem context_12_285453_929450 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285453 ⟨929450, by decide⟩ :=
  accepted_of_selected 12 285453 ⟨929450, by decide⟩ ⟨12, 2, 0, 929450, 285453, 3285, 65536⟩
    (by decide) selected_cut_35376

theorem selected_cut_35377 : selected 9 ⟨929515, by decide⟩
    (prefixPartial 12 285454) = some ⟨12, 2, 0, 929515, 285454, 3509, 65536⟩ := by
  decide +kernel

theorem context_12_285454_929515 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285454 ⟨929515, by decide⟩ :=
  accepted_of_selected 12 285454 ⟨929515, by decide⟩ ⟨12, 2, 0, 929515, 285454, 3509, 65536⟩
    (by decide) selected_cut_35377

theorem selected_cut_35378 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 285455) = some ⟨12, 1, 0, 903806, 285455, 1, 65536⟩ := by
  decide +kernel

theorem context_12_285455_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285455 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 285455 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 285455, 1, 65536⟩
    (by decide) selected_cut_35378

theorem unmarked_context_11_71363_929516 : frontier 10 ⟨929516, by decide⟩
    (prefixCache 11 71363) (prefixPartial 11 71363) = false := by
  decide +kernel

theorem node_context_11_71363_929516 : EJMOriginalGlobalDAGData.nodes 10 ⟨929516, by decide⟩ =
    .split (coordinate 11) (![⟨4596, by decide⟩,⟨929450, by decide⟩,⟨929515, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71363_929516 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71363 ⟨929516, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71363
    ⟨929516, by decide⟩ (by decide) (![⟨4596, by decide⟩,⟨929450, by decide⟩,⟨929515, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_71363_929516 node_context_11_71363_929516
  intro a
  fin_cases a
  · exact context_12_285452_4596
  · exact context_12_285453_929450
  · exact context_12_285454_929515
  · exact context_12_285455_903806

theorem unmarked_context_10_17840_929517 : frontier 11 ⟨929517, by decide⟩
    (prefixCache 10 17840) (prefixPartial 10 17840) = false := by
  decide +kernel

theorem node_context_10_17840_929517 : EJMOriginalGlobalDAGData.nodes 11 ⟨929517, by decide⟩ =
    .split (coordinate 10) (![⟨928893, by decide⟩,⟨929119, by decide⟩,⟨929401, by decide⟩,⟨929516, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17840_929517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17840 ⟨929517, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17840
    ⟨929517, by decide⟩ (by decide) (![⟨928893, by decide⟩,⟨929119, by decide⟩,⟨929401, by decide⟩,⟨929516, by decide⟩]) unmarked_context_10_17840_929517 node_context_10_17840_929517
  intro a
  fin_cases a
  · exact context_11_71360_928893
  · exact context_11_71361_929119
  · exact context_11_71362_929401
  · exact context_11_71363_929516

theorem selected_cut_35379 : selected 9 ⟨106538, by decide⟩
    (prefixPartial 12 285456) = some ⟨12, 1, 0, 106538, 285456, 1, 65536⟩ := by
  decide +kernel

theorem context_12_285456_106538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285456 ⟨106538, by decide⟩ :=
  accepted_of_selected 12 285456 ⟨106538, by decide⟩ ⟨12, 1, 0, 106538, 285456, 1, 65536⟩
    (by decide) selected_cut_35379

theorem selected_cut_35380 : selected 9 ⟨929564, by decide⟩
    (prefixPartial 12 285457) = some ⟨12, 2, 0, 929564, 285457, 1949, 65536⟩ := by
  decide +kernel

theorem context_12_285457_929564 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285457 ⟨929564, by decide⟩ :=
  accepted_of_selected 12 285457 ⟨929564, by decide⟩ ⟨12, 2, 0, 929564, 285457, 1949, 65536⟩
    (by decide) selected_cut_35380

theorem selected_cut_35381 : selected 9 ⟨929624, by decide⟩
    (prefixPartial 12 285458) = some ⟨12, 2, 0, 929624, 285458, 3533, 65536⟩ := by
  decide +kernel

theorem context_12_285458_929624 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285458 ⟨929624, by decide⟩ :=
  accepted_of_selected 12 285458 ⟨929624, by decide⟩ ⟨12, 2, 0, 929624, 285458, 3533, 65536⟩
    (by decide) selected_cut_35381

theorem selected_cut_35382 : selected 9 ⟨929672, by decide⟩
    (prefixPartial 12 285459) = some ⟨12, 2, 0, 929672, 285459, 3161, 65536⟩ := by
  decide +kernel

theorem context_12_285459_929672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285459 ⟨929672, by decide⟩ :=
  accepted_of_selected 12 285459 ⟨929672, by decide⟩ ⟨12, 2, 0, 929672, 285459, 3161, 65536⟩
    (by decide) selected_cut_35382

theorem unmarked_context_11_71364_929673 : frontier 10 ⟨929673, by decide⟩
    (prefixCache 11 71364) (prefixPartial 11 71364) = false := by
  decide +kernel

theorem node_context_11_71364_929673 : EJMOriginalGlobalDAGData.nodes 10 ⟨929673, by decide⟩ =
    .split (coordinate 11) (![⟨106538, by decide⟩,⟨929564, by decide⟩,⟨929624, by decide⟩,⟨929672, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71364_929673 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71364 ⟨929673, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71364
    ⟨929673, by decide⟩ (by decide) (![⟨106538, by decide⟩,⟨929564, by decide⟩,⟨929624, by decide⟩,⟨929672, by decide⟩]) unmarked_context_11_71364_929673 node_context_11_71364_929673
  intro a
  fin_cases a
  · exact context_12_285456_106538
  · exact context_12_285457_929564
  · exact context_12_285458_929624
  · exact context_12_285459_929672

theorem selected_cut_35383 : selected 9 ⟨106538, by decide⟩
    (prefixPartial 12 285460) = some ⟨12, 1, 0, 106538, 285460, 1, 65536⟩ := by
  decide +kernel

theorem context_12_285460_106538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285460 ⟨106538, by decide⟩ :=
  accepted_of_selected 12 285460 ⟨106538, by decide⟩ ⟨12, 1, 0, 106538, 285460, 1, 65536⟩
    (by decide) selected_cut_35383

theorem selected_cut_35384 : selected 9 ⟨929709, by decide⟩
    (prefixPartial 12 285461) = some ⟨12, 2, 0, 929709, 285461, 1493, 65536⟩ := by
  decide +kernel

theorem context_12_285461_929709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285461 ⟨929709, by decide⟩ :=
  accepted_of_selected 12 285461 ⟨929709, by decide⟩ ⟨12, 2, 0, 929709, 285461, 1493, 65536⟩
    (by decide) selected_cut_35384

theorem selected_cut_35385 : selected 9 ⟨929755, by decide⟩
    (prefixPartial 12 285462) = some ⟨12, 2, 0, 929755, 285462, 2901, 65536⟩ := by
  decide +kernel

theorem context_12_285462_929755 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285462 ⟨929755, by decide⟩ :=
  accepted_of_selected 12 285462 ⟨929755, by decide⟩ ⟨12, 2, 0, 929755, 285462, 2901, 65536⟩
    (by decide) selected_cut_35385

theorem selected_cut_35386 : selected 9 ⟨929789, by decide⟩
    (prefixPartial 12 285463) = some ⟨12, 2, 0, 929789, 285463, 2569, 65536⟩ := by
  decide +kernel

theorem context_12_285463_929789 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285463 ⟨929789, by decide⟩ :=
  accepted_of_selected 12 285463 ⟨929789, by decide⟩ ⟨12, 2, 0, 929789, 285463, 2569, 65536⟩
    (by decide) selected_cut_35386

theorem unmarked_context_11_71365_929790 : frontier 10 ⟨929790, by decide⟩
    (prefixCache 11 71365) (prefixPartial 11 71365) = false := by
  decide +kernel

theorem node_context_11_71365_929790 : EJMOriginalGlobalDAGData.nodes 10 ⟨929790, by decide⟩ =
    .split (coordinate 11) (![⟨106538, by decide⟩,⟨929709, by decide⟩,⟨929755, by decide⟩,⟨929789, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71365_929790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71365 ⟨929790, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71365
    ⟨929790, by decide⟩ (by decide) (![⟨106538, by decide⟩,⟨929709, by decide⟩,⟨929755, by decide⟩,⟨929789, by decide⟩]) unmarked_context_11_71365_929790 node_context_11_71365_929790
  intro a
  fin_cases a
  · exact context_12_285460_106538
  · exact context_12_285461_929709
  · exact context_12_285462_929755
  · exact context_12_285463_929789

theorem selected_cut_35387 : selected 9 ⟨106538, by decide⟩
    (prefixPartial 12 285464) = some ⟨12, 1, 0, 106538, 285464, 1, 65536⟩ := by
  decide +kernel

theorem context_12_285464_106538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285464 ⟨106538, by decide⟩ :=
  accepted_of_selected 12 285464 ⟨106538, by decide⟩ ⟨12, 1, 0, 106538, 285464, 1, 65536⟩
    (by decide) selected_cut_35387

theorem selected_cut_35388 : selected 9 ⟨929843, by decide⟩
    (prefixPartial 12 285465) = some ⟨12, 2, 0, 929843, 285465, 3025, 65536⟩ := by
  decide +kernel

theorem context_12_285465_929843 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285465 ⟨929843, by decide⟩ :=
  accepted_of_selected 12 285465 ⟨929843, by decide⟩ ⟨12, 2, 0, 929843, 285465, 3025, 65536⟩
    (by decide) selected_cut_35388

theorem selected_cut_35389 : selected 9 ⟨929903, by decide⟩
    (prefixPartial 12 285466) = some ⟨12, 2, 0, 929903, 285466, 3233, 65536⟩ := by
  decide +kernel

theorem context_12_285466_929903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285466 ⟨929903, by decide⟩ :=
  accepted_of_selected 12 285466 ⟨929903, by decide⟩ ⟨12, 2, 0, 929903, 285466, 3233, 65536⟩
    (by decide) selected_cut_35389

theorem selected_cut_35390 : selected 9 ⟨929964, by decide⟩
    (prefixPartial 12 285467) = some ⟨12, 2, 0, 929964, 285467, 3145, 65536⟩ := by
  decide +kernel

theorem context_12_285467_929964 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285467 ⟨929964, by decide⟩ :=
  accepted_of_selected 12 285467 ⟨929964, by decide⟩ ⟨12, 2, 0, 929964, 285467, 3145, 65536⟩
    (by decide) selected_cut_35390

theorem unmarked_context_11_71366_929965 : frontier 10 ⟨929965, by decide⟩
    (prefixCache 11 71366) (prefixPartial 11 71366) = false := by
  decide +kernel

theorem node_context_11_71366_929965 : EJMOriginalGlobalDAGData.nodes 10 ⟨929965, by decide⟩ =
    .split (coordinate 11) (![⟨106538, by decide⟩,⟨929843, by decide⟩,⟨929903, by decide⟩,⟨929964, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71366_929965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71366 ⟨929965, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71366
    ⟨929965, by decide⟩ (by decide) (![⟨106538, by decide⟩,⟨929843, by decide⟩,⟨929903, by decide⟩,⟨929964, by decide⟩]) unmarked_context_11_71366_929965 node_context_11_71366_929965
  intro a
  fin_cases a
  · exact context_12_285464_106538
  · exact context_12_285465_929843
  · exact context_12_285466_929903
  · exact context_12_285467_929964

theorem selected_cut_35391 : selected 10 ⟨930034, by decide⟩
    (prefixPartial 11 71367) = some ⟨11, 2, 0, 930034, 71367, 3369, 262144⟩ := by
  decide +kernel

theorem context_11_71367_930034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71367 ⟨930034, by decide⟩ :=
  accepted_of_selected 11 71367 ⟨930034, by decide⟩ ⟨11, 2, 0, 930034, 71367, 3369, 262144⟩
    (by decide) selected_cut_35391

theorem unmarked_context_10_17841_930035 : frontier 11 ⟨930035, by decide⟩
    (prefixCache 10 17841) (prefixPartial 10 17841) = false := by
  decide +kernel

theorem node_context_10_17841_930035 : EJMOriginalGlobalDAGData.nodes 11 ⟨930035, by decide⟩ =
    .split (coordinate 10) (![⟨929673, by decide⟩,⟨929790, by decide⟩,⟨929965, by decide⟩,⟨930034, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17841_930035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17841 ⟨930035, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17841
    ⟨930035, by decide⟩ (by decide) (![⟨929673, by decide⟩,⟨929790, by decide⟩,⟨929965, by decide⟩,⟨930034, by decide⟩]) unmarked_context_10_17841_930035 node_context_10_17841_930035
  intro a
  fin_cases a
  · exact context_11_71364_929673
  · exact context_11_71365_929790
  · exact context_11_71366_929965
  · exact context_11_71367_930034

theorem selected_cut_35392 : selected 9 ⟨106538, by decide⟩
    (prefixPartial 12 285472) = some ⟨12, 1, 0, 106538, 285472, 1, 65536⟩ := by
  decide +kernel

theorem context_12_285472_106538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285472 ⟨106538, by decide⟩ :=
  accepted_of_selected 12 285472 ⟨106538, by decide⟩ ⟨12, 1, 0, 106538, 285472, 1, 65536⟩
    (by decide) selected_cut_35392

theorem selected_cut_35393 : selected 9 ⟨106538, by decide⟩
    (prefixPartial 12 285473) = some ⟨12, 1, 0, 106538, 285473, 1, 65536⟩ := by
  decide +kernel

theorem context_12_285473_106538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285473 ⟨106538, by decide⟩ :=
  accepted_of_selected 12 285473 ⟨106538, by decide⟩ ⟨12, 1, 0, 106538, 285473, 1, 65536⟩
    (by decide) selected_cut_35393

theorem selected_cut_35394 : selected 9 ⟨930089, by decide⟩
    (prefixPartial 12 285474) = some ⟨12, 2, 0, 930089, 285474, 3049, 65536⟩ := by
  decide +kernel

theorem context_12_285474_930089 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285474 ⟨930089, by decide⟩ :=
  accepted_of_selected 12 285474 ⟨930089, by decide⟩ ⟨12, 2, 0, 930089, 285474, 3049, 65536⟩
    (by decide) selected_cut_35394

theorem selected_cut_35395 : selected 9 ⟨930122, by decide⟩
    (prefixPartial 12 285475) = some ⟨12, 2, 0, 930122, 285475, 1473, 65536⟩ := by
  decide +kernel

theorem context_12_285475_930122 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285475 ⟨930122, by decide⟩ :=
  accepted_of_selected 12 285475 ⟨930122, by decide⟩ ⟨12, 2, 0, 930122, 285475, 1473, 65536⟩
    (by decide) selected_cut_35395

theorem unmarked_context_11_71368_930123 : frontier 10 ⟨930123, by decide⟩
    (prefixCache 11 71368) (prefixPartial 11 71368) = false := by
  decide +kernel

theorem node_context_11_71368_930123 : EJMOriginalGlobalDAGData.nodes 10 ⟨930123, by decide⟩ =
    .split (coordinate 11) (![⟨106538, by decide⟩,⟨106538, by decide⟩,⟨930089, by decide⟩,⟨930122, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71368_930123 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71368 ⟨930123, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71368
    ⟨930123, by decide⟩ (by decide) (![⟨106538, by decide⟩,⟨106538, by decide⟩,⟨930089, by decide⟩,⟨930122, by decide⟩]) unmarked_context_11_71368_930123 node_context_11_71368_930123
  intro a
  fin_cases a
  · exact context_12_285472_106538
  · exact context_12_285473_106538
  · exact context_12_285474_930089
  · exact context_12_285475_930122

theorem selected_cut_35396 : selected 10 ⟨930187, by decide⟩
    (prefixPartial 11 71369) = some ⟨11, 2, 0, 930187, 71369, 3529, 262144⟩ := by
  decide +kernel

theorem context_11_71369_930187 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71369 ⟨930187, by decide⟩ :=
  accepted_of_selected 11 71369 ⟨930187, by decide⟩ ⟨11, 2, 0, 930187, 71369, 3529, 262144⟩
    (by decide) selected_cut_35396

theorem selected_cut_35397 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 71370) = some ⟨11, 1, 0, 900587, 71370, 1, 262144⟩ := by
  decide +kernel

theorem context_11_71370_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71370 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 71370 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 71370, 1, 262144⟩
    (by decide) selected_cut_35397

theorem selected_cut_35398 : selected 10 ⟨930253, by decide⟩
    (prefixPartial 11 71371) = some ⟨11, 2, 0, 930253, 71371, 3209, 262144⟩ := by
  decide +kernel

theorem context_11_71371_930253 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71371 ⟨930253, by decide⟩ :=
  accepted_of_selected 11 71371 ⟨930253, by decide⟩ ⟨11, 2, 0, 930253, 71371, 3209, 262144⟩
    (by decide) selected_cut_35398

theorem unmarked_context_10_17842_930254 : frontier 11 ⟨930254, by decide⟩
    (prefixCache 10 17842) (prefixPartial 10 17842) = false := by
  decide +kernel

theorem node_context_10_17842_930254 : EJMOriginalGlobalDAGData.nodes 11 ⟨930254, by decide⟩ =
    .split (coordinate 10) (![⟨930123, by decide⟩,⟨930187, by decide⟩,⟨900587, by decide⟩,⟨930253, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17842_930254 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17842 ⟨930254, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17842
    ⟨930254, by decide⟩ (by decide) (![⟨930123, by decide⟩,⟨930187, by decide⟩,⟨900587, by decide⟩,⟨930253, by decide⟩]) unmarked_context_10_17842_930254 node_context_10_17842_930254
  intro a
  fin_cases a
  · exact context_11_71368_930123
  · exact context_11_71369_930187
  · exact context_11_71370_900587
  · exact context_11_71371_930253

theorem selected_cut_35399 : selected 10 ⟨930287, by decide⟩
    (prefixPartial 11 71372) = some ⟨11, 2, 0, 930287, 71372, 1789, 262144⟩ := by
  decide +kernel

theorem context_11_71372_930287 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71372 ⟨930287, by decide⟩ :=
  accepted_of_selected 11 71372 ⟨930287, by decide⟩ ⟨11, 2, 0, 930287, 71372, 1789, 262144⟩
    (by decide) selected_cut_35399

theorem selected_cut_35400 : selected 10 ⟨930314, by decide⟩
    (prefixPartial 11 71373) = some ⟨11, 2, 0, 930314, 71373, 1401, 262144⟩ := by
  decide +kernel

theorem context_11_71373_930314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71373 ⟨930314, by decide⟩ :=
  accepted_of_selected 11 71373 ⟨930314, by decide⟩ ⟨11, 2, 0, 930314, 71373, 1401, 262144⟩
    (by decide) selected_cut_35400

theorem selected_cut_35401 : selected 10 ⟨930378, by decide⟩
    (prefixPartial 11 71374) = some ⟨11, 2, 0, 930378, 71374, 2981, 262144⟩ := by
  decide +kernel

theorem context_11_71374_930378 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71374 ⟨930378, by decide⟩ :=
  accepted_of_selected 11 71374 ⟨930378, by decide⟩ ⟨11, 2, 0, 930378, 71374, 2981, 262144⟩
    (by decide) selected_cut_35401

theorem selected_cut_35402 : selected 10 ⟨109216, by decide⟩
    (prefixPartial 11 71375) = some ⟨11, 2, 0, 109216, 71375, 5, 262144⟩ := by
  decide +kernel

theorem context_11_71375_109216 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71375 ⟨109216, by decide⟩ :=
  accepted_of_selected 11 71375 ⟨109216, by decide⟩ ⟨11, 2, 0, 109216, 71375, 5, 262144⟩
    (by decide) selected_cut_35402

theorem unmarked_context_10_17843_930379 : frontier 11 ⟨930379, by decide⟩
    (prefixCache 10 17843) (prefixPartial 10 17843) = false := by
  decide +kernel

theorem node_context_10_17843_930379 : EJMOriginalGlobalDAGData.nodes 11 ⟨930379, by decide⟩ =
    .split (coordinate 10) (![⟨930287, by decide⟩,⟨930314, by decide⟩,⟨930378, by decide⟩,⟨109216, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17843_930379 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17843 ⟨930379, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17843
    ⟨930379, by decide⟩ (by decide) (![⟨930287, by decide⟩,⟨930314, by decide⟩,⟨930378, by decide⟩,⟨109216, by decide⟩]) unmarked_context_10_17843_930379 node_context_10_17843_930379
  intro a
  fin_cases a
  · exact context_11_71372_930287
  · exact context_11_71373_930314
  · exact context_11_71374_930378
  · exact context_11_71375_109216

theorem unmarked_context_9_4460_930380 : frontier 12 ⟨930380, by decide⟩
    (prefixCache 9 4460) (prefixPartial 9 4460) = false := by
  decide +kernel

theorem node_context_9_4460_930380 : EJMOriginalGlobalDAGData.nodes 12 ⟨930380, by decide⟩ =
    .split (coordinate 9) (![⟨929517, by decide⟩,⟨930035, by decide⟩,⟨930254, by decide⟩,⟨930379, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4460_930380 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4460 ⟨930380, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4460
    ⟨930380, by decide⟩ (by decide) (![⟨929517, by decide⟩,⟨930035, by decide⟩,⟨930254, by decide⟩,⟨930379, by decide⟩]) unmarked_context_9_4460_930380 node_context_9_4460_930380
  intro a
  fin_cases a
  · exact context_10_17840_929517
  · exact context_10_17841_930035
  · exact context_10_17842_930254
  · exact context_10_17843_930379

theorem selected_cut_35403 : selected 9 ⟨930412, by decide⟩
    (prefixPartial 12 285504) = some ⟨12, 2, 0, 930412, 285504, 1525, 65536⟩ := by
  decide +kernel

theorem context_12_285504_930412 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285504 ⟨930412, by decide⟩ :=
  accepted_of_selected 12 285504 ⟨930412, by decide⟩ ⟨12, 2, 0, 930412, 285504, 1525, 65536⟩
    (by decide) selected_cut_35403

theorem selected_cut_35404 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 285505) = some ⟨12, 1, 0, 896706, 285505, 1, 65536⟩ := by
  decide +kernel

theorem context_12_285505_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285505 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 285505 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 285505, 1, 65536⟩
    (by decide) selected_cut_35404

theorem selected_cut_35405 : selected 9 ⟨930450, by decide⟩
    (prefixPartial 12 285506) = some ⟨12, 2, 0, 930450, 285506, 2269, 65536⟩ := by
  decide +kernel

theorem context_12_285506_930450 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285506 ⟨930450, by decide⟩ :=
  accepted_of_selected 12 285506 ⟨930450, by decide⟩ ⟨12, 2, 0, 930450, 285506, 2269, 65536⟩
    (by decide) selected_cut_35405

theorem selected_cut_35406 : selected 9 ⟨930487, by decide⟩
    (prefixPartial 12 285507) = some ⟨12, 2, 0, 930487, 285507, 2117, 65536⟩ := by
  decide +kernel

theorem context_12_285507_930487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285507 ⟨930487, by decide⟩ :=
  accepted_of_selected 12 285507 ⟨930487, by decide⟩ ⟨12, 2, 0, 930487, 285507, 2117, 65536⟩
    (by decide) selected_cut_35406

theorem unmarked_context_11_71376_930488 : frontier 10 ⟨930488, by decide⟩
    (prefixCache 11 71376) (prefixPartial 11 71376) = false := by
  decide +kernel

theorem node_context_11_71376_930488 : EJMOriginalGlobalDAGData.nodes 10 ⟨930488, by decide⟩ =
    .split (coordinate 11) (![⟨930412, by decide⟩,⟨896706, by decide⟩,⟨930450, by decide⟩,⟨930487, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71376_930488 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71376 ⟨930488, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71376
    ⟨930488, by decide⟩ (by decide) (![⟨930412, by decide⟩,⟨896706, by decide⟩,⟨930450, by decide⟩,⟨930487, by decide⟩]) unmarked_context_11_71376_930488 node_context_11_71376_930488
  intro a
  fin_cases a
  · exact context_12_285504_930412
  · exact context_12_285505_896706
  · exact context_12_285506_930450
  · exact context_12_285507_930487

theorem selected_cut_35407 : selected 9 ⟨930519, by decide⟩
    (prefixPartial 12 285508) = some ⟨12, 2, 0, 930519, 285508, 1273, 65536⟩ := by
  decide +kernel

theorem context_12_285508_930519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285508 ⟨930519, by decide⟩ :=
  accepted_of_selected 12 285508 ⟨930519, by decide⟩ ⟨12, 2, 0, 930519, 285508, 1273, 65536⟩
    (by decide) selected_cut_35407

theorem selected_cut_35408 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 285509) = some ⟨12, 1, 0, 896706, 285509, 1, 65536⟩ := by
  decide +kernel

theorem context_12_285509_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285509 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 285509 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 285509, 1, 65536⟩
    (by decide) selected_cut_35408

theorem selected_cut_35409 : selected 9 ⟨930552, by decide⟩
    (prefixPartial 12 285510) = some ⟨12, 2, 0, 930552, 285510, 1801, 65536⟩ := by
  decide +kernel

theorem context_12_285510_930552 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285510 ⟨930552, by decide⟩ :=
  accepted_of_selected 12 285510 ⟨930552, by decide⟩ ⟨12, 2, 0, 930552, 285510, 1801, 65536⟩
    (by decide) selected_cut_35409

theorem selected_cut_35410 : selected 9 ⟨930582, by decide⟩
    (prefixPartial 12 285511) = some ⟨12, 2, 0, 930582, 285511, 1717, 65536⟩ := by
  decide +kernel

theorem context_12_285511_930582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285511 ⟨930582, by decide⟩ :=
  accepted_of_selected 12 285511 ⟨930582, by decide⟩ ⟨12, 2, 0, 930582, 285511, 1717, 65536⟩
    (by decide) selected_cut_35410

theorem unmarked_context_11_71377_930583 : frontier 10 ⟨930583, by decide⟩
    (prefixCache 11 71377) (prefixPartial 11 71377) = false := by
  decide +kernel

theorem node_context_11_71377_930583 : EJMOriginalGlobalDAGData.nodes 10 ⟨930583, by decide⟩ =
    .split (coordinate 11) (![⟨930519, by decide⟩,⟨896706, by decide⟩,⟨930552, by decide⟩,⟨930582, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71377_930583 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71377 ⟨930583, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71377
    ⟨930583, by decide⟩ (by decide) (![⟨930519, by decide⟩,⟨896706, by decide⟩,⟨930552, by decide⟩,⟨930582, by decide⟩]) unmarked_context_11_71377_930583 node_context_11_71377_930583
  intro a
  fin_cases a
  · exact context_12_285508_930519
  · exact context_12_285509_896706
  · exact context_12_285510_930552
  · exact context_12_285511_930582

theorem selected_cut_35411 : selected 9 ⟨930635, by decide⟩
    (prefixPartial 12 285512) = some ⟨12, 2, 0, 930635, 285512, 2521, 65536⟩ := by
  decide +kernel

theorem context_12_285512_930635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285512 ⟨930635, by decide⟩ :=
  accepted_of_selected 12 285512 ⟨930635, by decide⟩ ⟨12, 2, 0, 930635, 285512, 2521, 65536⟩
    (by decide) selected_cut_35411

theorem selected_cut_35412 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 285513) = some ⟨12, 1, 0, 896706, 285513, 1, 65536⟩ := by
  decide +kernel

theorem context_12_285513_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285513 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 285513 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 285513, 1, 65536⟩
    (by decide) selected_cut_35412

theorem selected_cut_35413 : selected 9 ⟨930681, by decide⟩
    (prefixPartial 12 285514) = some ⟨12, 2, 0, 930681, 285514, 2089, 65536⟩ := by
  decide +kernel

theorem context_12_285514_930681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285514 ⟨930681, by decide⟩ :=
  accepted_of_selected 12 285514 ⟨930681, by decide⟩ ⟨12, 2, 0, 930681, 285514, 2089, 65536⟩
    (by decide) selected_cut_35413

theorem selected_cut_35414 : selected 9 ⟨930728, by decide⟩
    (prefixPartial 12 285515) = some ⟨12, 2, 0, 930728, 285515, 2249, 65536⟩ := by
  decide +kernel

theorem context_12_285515_930728 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285515 ⟨930728, by decide⟩ :=
  accepted_of_selected 12 285515 ⟨930728, by decide⟩ ⟨12, 2, 0, 930728, 285515, 2249, 65536⟩
    (by decide) selected_cut_35414

theorem unmarked_context_11_71378_930729 : frontier 10 ⟨930729, by decide⟩
    (prefixCache 11 71378) (prefixPartial 11 71378) = false := by
  decide +kernel

theorem node_context_11_71378_930729 : EJMOriginalGlobalDAGData.nodes 10 ⟨930729, by decide⟩ =
    .split (coordinate 11) (![⟨930635, by decide⟩,⟨896706, by decide⟩,⟨930681, by decide⟩,⟨930728, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71378_930729 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71378 ⟨930729, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71378
    ⟨930729, by decide⟩ (by decide) (![⟨930635, by decide⟩,⟨896706, by decide⟩,⟨930681, by decide⟩,⟨930728, by decide⟩]) unmarked_context_11_71378_930729 node_context_11_71378_930729
  intro a
  fin_cases a
  · exact context_12_285512_930635
  · exact context_12_285513_896706
  · exact context_12_285514_930681
  · exact context_12_285515_930728

theorem selected_cut_35415 : selected 10 ⟨930773, by decide⟩
    (prefixPartial 11 71379) = some ⟨11, 2, 0, 930773, 71379, 2297, 262144⟩ := by
  decide +kernel

theorem context_11_71379_930773 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71379 ⟨930773, by decide⟩ :=
  accepted_of_selected 11 71379 ⟨930773, by decide⟩ ⟨11, 2, 0, 930773, 71379, 2297, 262144⟩
    (by decide) selected_cut_35415

theorem unmarked_context_10_17844_930774 : frontier 11 ⟨930774, by decide⟩
    (prefixCache 10 17844) (prefixPartial 10 17844) = false := by
  decide +kernel

theorem node_context_10_17844_930774 : EJMOriginalGlobalDAGData.nodes 11 ⟨930774, by decide⟩ =
    .split (coordinate 10) (![⟨930488, by decide⟩,⟨930583, by decide⟩,⟨930729, by decide⟩,⟨930773, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17844_930774 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17844 ⟨930774, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17844
    ⟨930774, by decide⟩ (by decide) (![⟨930488, by decide⟩,⟨930583, by decide⟩,⟨930729, by decide⟩,⟨930773, by decide⟩]) unmarked_context_10_17844_930774 node_context_10_17844_930774
  intro a
  fin_cases a
  · exact context_11_71376_930488
  · exact context_11_71377_930583
  · exact context_11_71378_930729
  · exact context_11_71379_930773

theorem selected_cut_35416 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 17845) = some ⟨10, 1, 0, 893098, 17845, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_17845_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17845 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 17845 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 17845, 1, 1048576⟩
    (by decide) selected_cut_35416

theorem selected_cut_35417 : selected 10 ⟨930819, by decide⟩
    (prefixPartial 11 71384) = some ⟨11, 2, 0, 930819, 71384, 2805, 262144⟩ := by
  decide +kernel

theorem context_11_71384_930819 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71384 ⟨930819, by decide⟩ :=
  accepted_of_selected 11 71384 ⟨930819, by decide⟩ ⟨11, 2, 0, 930819, 71384, 2805, 262144⟩
    (by decide) selected_cut_35417

theorem selected_cut_35418 : selected 10 ⟨930855, by decide⟩
    (prefixPartial 11 71385) = some ⟨11, 2, 0, 930855, 71385, 2285, 262144⟩ := by
  decide +kernel

theorem context_11_71385_930855 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71385 ⟨930855, by decide⟩ :=
  accepted_of_selected 11 71385 ⟨930855, by decide⟩ ⟨11, 2, 0, 930855, 71385, 2285, 262144⟩
    (by decide) selected_cut_35418

theorem selected_cut_35419 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 71386) = some ⟨11, 1, 0, 900587, 71386, 1, 262144⟩ := by
  decide +kernel

theorem context_11_71386_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71386 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 71386 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 71386, 1, 262144⟩
    (by decide) selected_cut_35419

theorem selected_cut_35420 : selected 10 ⟨930896, by decide⟩
    (prefixPartial 11 71387) = some ⟨11, 2, 0, 930896, 71387, 2177, 262144⟩ := by
  decide +kernel

theorem context_11_71387_930896 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71387 ⟨930896, by decide⟩ :=
  accepted_of_selected 11 71387 ⟨930896, by decide⟩ ⟨11, 2, 0, 930896, 71387, 2177, 262144⟩
    (by decide) selected_cut_35420

theorem unmarked_context_10_17846_930897 : frontier 11 ⟨930897, by decide⟩
    (prefixCache 10 17846) (prefixPartial 10 17846) = false := by
  decide +kernel

theorem node_context_10_17846_930897 : EJMOriginalGlobalDAGData.nodes 11 ⟨930897, by decide⟩ =
    .split (coordinate 10) (![⟨930819, by decide⟩,⟨930855, by decide⟩,⟨900587, by decide⟩,⟨930896, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17846_930897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17846 ⟨930897, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17846
    ⟨930897, by decide⟩ (by decide) (![⟨930819, by decide⟩,⟨930855, by decide⟩,⟨900587, by decide⟩,⟨930896, by decide⟩]) unmarked_context_10_17846_930897 node_context_10_17846_930897
  intro a
  fin_cases a
  · exact context_11_71384_930819
  · exact context_11_71385_930855
  · exact context_11_71386_900587
  · exact context_11_71387_930896

theorem selected_cut_35421 : selected 11 ⟨930974, by decide⟩
    (prefixPartial 10 17847) = some ⟨10, 2, 0, 930974, 17847, 3689, 1048576⟩ := by
  decide +kernel

theorem context_10_17847_930974 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17847 ⟨930974, by decide⟩ :=
  accepted_of_selected 10 17847 ⟨930974, by decide⟩ ⟨10, 2, 0, 930974, 17847, 3689, 1048576⟩
    (by decide) selected_cut_35421

theorem unmarked_context_9_4461_930975 : frontier 12 ⟨930975, by decide⟩
    (prefixCache 9 4461) (prefixPartial 9 4461) = false := by
  decide +kernel

theorem node_context_9_4461_930975 : EJMOriginalGlobalDAGData.nodes 12 ⟨930975, by decide⟩ =
    .split (coordinate 9) (![⟨930774, by decide⟩,⟨893098, by decide⟩,⟨930897, by decide⟩,⟨930974, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4461_930975 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4461 ⟨930975, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4461
    ⟨930975, by decide⟩ (by decide) (![⟨930774, by decide⟩,⟨893098, by decide⟩,⟨930897, by decide⟩,⟨930974, by decide⟩]) unmarked_context_9_4461_930975 node_context_9_4461_930975
  intro a
  fin_cases a
  · exact context_10_17844_930774
  · exact context_10_17845_893098
  · exact context_10_17846_930897
  · exact context_10_17847_930974

theorem selected_cut_35422 : selected 9 ⟨931001, by decide⟩
    (prefixPartial 12 285568) = some ⟨12, 2, 0, 931001, 285568, 1569, 65536⟩ := by
  decide +kernel

theorem context_12_285568_931001 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285568 ⟨931001, by decide⟩ :=
  accepted_of_selected 12 285568 ⟨931001, by decide⟩ ⟨12, 2, 0, 931001, 285568, 1569, 65536⟩
    (by decide) selected_cut_35422

theorem selected_cut_35423 : selected 9 ⟨931019, by decide⟩
    (prefixPartial 12 285569) = some ⟨12, 2, 0, 931019, 285569, 1357, 65536⟩ := by
  decide +kernel

theorem context_12_285569_931019 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285569 ⟨931019, by decide⟩ :=
  accepted_of_selected 12 285569 ⟨931019, by decide⟩ ⟨12, 2, 0, 931019, 285569, 1357, 65536⟩
    (by decide) selected_cut_35423

theorem selected_cut_35424 : selected 9 ⟨931040, by decide⟩
    (prefixPartial 12 285570) = some ⟨12, 2, 0, 931040, 285570, 1305, 65536⟩ := by
  decide +kernel

theorem context_12_285570_931040 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285570 ⟨931040, by decide⟩ :=
  accepted_of_selected 12 285570 ⟨931040, by decide⟩ ⟨12, 2, 0, 931040, 285570, 1305, 65536⟩
    (by decide) selected_cut_35424

theorem selected_cut_35425 : selected 9 ⟨931059, by decide⟩
    (prefixPartial 12 285571) = some ⟨12, 2, 0, 931059, 285571, 1209, 65536⟩ := by
  decide +kernel

theorem context_12_285571_931059 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285571 ⟨931059, by decide⟩ :=
  accepted_of_selected 12 285571 ⟨931059, by decide⟩ ⟨12, 2, 0, 931059, 285571, 1209, 65536⟩
    (by decide) selected_cut_35425

theorem unmarked_context_11_71392_931060 : frontier 10 ⟨931060, by decide⟩
    (prefixCache 11 71392) (prefixPartial 11 71392) = false := by
  decide +kernel

theorem node_context_11_71392_931060 : EJMOriginalGlobalDAGData.nodes 10 ⟨931060, by decide⟩ =
    .split (coordinate 11) (![⟨931001, by decide⟩,⟨931019, by decide⟩,⟨931040, by decide⟩,⟨931059, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_71392_931060 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 71392 ⟨931060, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 71392
    ⟨931060, by decide⟩ (by decide) (![⟨931001, by decide⟩,⟨931019, by decide⟩,⟨931040, by decide⟩,⟨931059, by decide⟩]) unmarked_context_11_71392_931060 node_context_11_71392_931060
  intro a
  fin_cases a
  · exact context_12_285568_931001
  · exact context_12_285569_931019
  · exact context_12_285570_931040
  · exact context_12_285571_931059

theorem selected_cut_35426 : selected 9 ⟨931082, by decide⟩
    (prefixPartial 12 285572) = some ⟨12, 2, 0, 931082, 285572, 1345, 65536⟩ := by
  decide +kernel

theorem context_12_285572_931082 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 285572 ⟨931082, by decide⟩ :=
  accepted_of_selected 12 285572 ⟨931082, by decide⟩ ⟨12, 2, 0, 931082, 285572, 1345, 65536⟩
    (by decide) selected_cut_35426

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
