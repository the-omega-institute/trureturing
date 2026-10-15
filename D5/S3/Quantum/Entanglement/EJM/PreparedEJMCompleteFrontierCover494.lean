/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover493
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_47427 : selected 9 ⟨1255011, by decide⟩
    (prefixPartial 12 373296) = some ⟨12, 1, 0, 1255011, 373296, 1, 65536⟩ := by
  decide +kernel

theorem context_12_373296_1255011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373296 ⟨1255011, by decide⟩ :=
  accepted_of_selected 12 373296 ⟨1255011, by decide⟩ ⟨12, 1, 0, 1255011, 373296, 1, 65536⟩
    (by decide) selected_cut_47427

theorem selected_cut_47428 : selected 9 ⟨1327272, by decide⟩
    (prefixPartial 12 373297) = some ⟨12, 2, 0, 1327272, 373297, 2361, 65536⟩ := by
  decide +kernel

theorem context_12_373297_1327272 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373297 ⟨1327272, by decide⟩ :=
  accepted_of_selected 12 373297 ⟨1327272, by decide⟩ ⟨12, 2, 0, 1327272, 373297, 2361, 65536⟩
    (by decide) selected_cut_47428

theorem selected_cut_47429 : selected 9 ⟨1327300, by decide⟩
    (prefixPartial 12 373298) = some ⟨12, 2, 0, 1327300, 373298, 2113, 65536⟩ := by
  decide +kernel

theorem context_12_373298_1327300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373298 ⟨1327300, by decide⟩ :=
  accepted_of_selected 12 373298 ⟨1327300, by decide⟩ ⟨12, 2, 0, 1327300, 373298, 2113, 65536⟩
    (by decide) selected_cut_47429

theorem selected_cut_47430 : selected 9 ⟨1327340, by decide⟩
    (prefixPartial 12 373299) = some ⟨12, 2, 0, 1327340, 373299, 2137, 65536⟩ := by
  decide +kernel

theorem context_12_373299_1327340 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373299 ⟨1327340, by decide⟩ :=
  accepted_of_selected 12 373299 ⟨1327340, by decide⟩ ⟨12, 2, 0, 1327340, 373299, 2137, 65536⟩
    (by decide) selected_cut_47430

theorem unmarked_context_11_93324_1327341 : frontier 10 ⟨1327341, by decide⟩
    (prefixCache 11 93324) (prefixPartial 11 93324) = false := by
  decide +kernel

theorem node_context_11_93324_1327341 : EJMOriginalGlobalDAGData.nodes 10 ⟨1327341, by decide⟩ =
    .split (coordinate 11) (![⟨1255011, by decide⟩,⟨1327272, by decide⟩,⟨1327300, by decide⟩,⟨1327340, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93324_1327341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93324 ⟨1327341, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93324
    ⟨1327341, by decide⟩ (by decide) (![⟨1255011, by decide⟩,⟨1327272, by decide⟩,⟨1327300, by decide⟩,⟨1327340, by decide⟩]) unmarked_context_11_93324_1327341 node_context_11_93324_1327341
  intro a
  fin_cases a
  · exact context_12_373296_1255011
  · exact context_12_373297_1327272
  · exact context_12_373298_1327300
  · exact context_12_373299_1327340

theorem selected_cut_47431 : selected 9 ⟨1327401, by decide⟩
    (prefixPartial 12 373300) = some ⟨12, 2, 0, 1327401, 373300, 2957, 65536⟩ := by
  decide +kernel

theorem context_12_373300_1327401 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373300 ⟨1327401, by decide⟩ :=
  accepted_of_selected 12 373300 ⟨1327401, by decide⟩ ⟨12, 2, 0, 1327401, 373300, 2957, 65536⟩
    (by decide) selected_cut_47431

theorem selected_cut_47432 : selected 9 ⟨1327447, by decide⟩
    (prefixPartial 12 373301) = some ⟨12, 2, 0, 1327447, 373301, 2653, 65536⟩ := by
  decide +kernel

theorem context_12_373301_1327447 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373301 ⟨1327447, by decide⟩ :=
  accepted_of_selected 12 373301 ⟨1327447, by decide⟩ ⟨12, 2, 0, 1327447, 373301, 2653, 65536⟩
    (by decide) selected_cut_47432

theorem selected_cut_47433 : selected 9 ⟨1327491, by decide⟩
    (prefixPartial 12 373302) = some ⟨12, 2, 0, 1327491, 373302, 2473, 65536⟩ := by
  decide +kernel

theorem context_12_373302_1327491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373302 ⟨1327491, by decide⟩ :=
  accepted_of_selected 12 373302 ⟨1327491, by decide⟩ ⟨12, 2, 0, 1327491, 373302, 2473, 65536⟩
    (by decide) selected_cut_47433

theorem selected_cut_47434 : selected 9 ⟨1327533, by decide⟩
    (prefixPartial 12 373303) = some ⟨12, 2, 0, 1327533, 373303, 2405, 65536⟩ := by
  decide +kernel

theorem context_12_373303_1327533 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373303 ⟨1327533, by decide⟩ :=
  accepted_of_selected 12 373303 ⟨1327533, by decide⟩ ⟨12, 2, 0, 1327533, 373303, 2405, 65536⟩
    (by decide) selected_cut_47434

theorem unmarked_context_11_93325_1327534 : frontier 10 ⟨1327534, by decide⟩
    (prefixCache 11 93325) (prefixPartial 11 93325) = false := by
  decide +kernel

theorem node_context_11_93325_1327534 : EJMOriginalGlobalDAGData.nodes 10 ⟨1327534, by decide⟩ =
    .split (coordinate 11) (![⟨1327401, by decide⟩,⟨1327447, by decide⟩,⟨1327491, by decide⟩,⟨1327533, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93325_1327534 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93325 ⟨1327534, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93325
    ⟨1327534, by decide⟩ (by decide) (![⟨1327401, by decide⟩,⟨1327447, by decide⟩,⟨1327491, by decide⟩,⟨1327533, by decide⟩]) unmarked_context_11_93325_1327534 node_context_11_93325_1327534
  intro a
  fin_cases a
  · exact context_12_373300_1327401
  · exact context_12_373301_1327447
  · exact context_12_373302_1327491
  · exact context_12_373303_1327533

theorem selected_cut_47435 : selected 9 ⟨994572, by decide⟩
    (prefixPartial 12 373304) = some ⟨12, 1, 0, 994572, 373304, 1, 65536⟩ := by
  decide +kernel

theorem context_12_373304_994572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373304 ⟨994572, by decide⟩ :=
  accepted_of_selected 12 373304 ⟨994572, by decide⟩ ⟨12, 1, 0, 994572, 373304, 1, 65536⟩
    (by decide) selected_cut_47435

theorem selected_cut_47436 : selected 9 ⟨1327568, by decide⟩
    (prefixPartial 12 373305) = some ⟨12, 2, 0, 1327568, 373305, 2201, 65536⟩ := by
  decide +kernel

theorem context_12_373305_1327568 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373305 ⟨1327568, by decide⟩ :=
  accepted_of_selected 12 373305 ⟨1327568, by decide⟩ ⟨12, 2, 0, 1327568, 373305, 2201, 65536⟩
    (by decide) selected_cut_47436

theorem selected_cut_47437 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 373306) = some ⟨12, 1, 0, 893903, 373306, 1, 65536⟩ := by
  decide +kernel

theorem context_12_373306_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373306 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 373306 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 373306, 1, 65536⟩
    (by decide) selected_cut_47437

theorem selected_cut_47438 : selected 9 ⟨1327603, by decide⟩
    (prefixPartial 12 373307) = some ⟨12, 2, 0, 1327603, 373307, 2213, 65536⟩ := by
  decide +kernel

theorem context_12_373307_1327603 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373307 ⟨1327603, by decide⟩ :=
  accepted_of_selected 12 373307 ⟨1327603, by decide⟩ ⟨12, 2, 0, 1327603, 373307, 2213, 65536⟩
    (by decide) selected_cut_47438

theorem unmarked_context_11_93326_1327604 : frontier 10 ⟨1327604, by decide⟩
    (prefixCache 11 93326) (prefixPartial 11 93326) = false := by
  decide +kernel

theorem node_context_11_93326_1327604 : EJMOriginalGlobalDAGData.nodes 10 ⟨1327604, by decide⟩ =
    .split (coordinate 11) (![⟨994572, by decide⟩,⟨1327568, by decide⟩,⟨893903, by decide⟩,⟨1327603, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93326_1327604 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93326 ⟨1327604, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93326
    ⟨1327604, by decide⟩ (by decide) (![⟨994572, by decide⟩,⟨1327568, by decide⟩,⟨893903, by decide⟩,⟨1327603, by decide⟩]) unmarked_context_11_93326_1327604 node_context_11_93326_1327604
  intro a
  fin_cases a
  · exact context_12_373304_994572
  · exact context_12_373305_1327568
  · exact context_12_373306_893903
  · exact context_12_373307_1327603

theorem selected_cut_47439 : selected 10 ⟨1327637, by decide⟩
    (prefixPartial 11 93327) = some ⟨11, 2, 0, 1327637, 93327, 1969, 262144⟩ := by
  decide +kernel

theorem context_11_93327_1327637 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93327 ⟨1327637, by decide⟩ :=
  accepted_of_selected 11 93327 ⟨1327637, by decide⟩ ⟨11, 2, 0, 1327637, 93327, 1969, 262144⟩
    (by decide) selected_cut_47439

theorem unmarked_context_10_23331_1327638 : frontier 11 ⟨1327638, by decide⟩
    (prefixCache 10 23331) (prefixPartial 10 23331) = false := by
  decide +kernel

theorem node_context_10_23331_1327638 : EJMOriginalGlobalDAGData.nodes 11 ⟨1327638, by decide⟩ =
    .split (coordinate 10) (![⟨1327341, by decide⟩,⟨1327534, by decide⟩,⟨1327604, by decide⟩,⟨1327637, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23331_1327638 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23331 ⟨1327638, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23331
    ⟨1327638, by decide⟩ (by decide) (![⟨1327341, by decide⟩,⟨1327534, by decide⟩,⟨1327604, by decide⟩,⟨1327637, by decide⟩]) unmarked_context_10_23331_1327638 node_context_10_23331_1327638
  intro a
  fin_cases a
  · exact context_11_93324_1327341
  · exact context_11_93325_1327534
  · exact context_11_93326_1327604
  · exact context_11_93327_1327637

theorem unmarked_context_9_5832_1327639 : frontier 12 ⟨1327639, by decide⟩
    (prefixCache 9 5832) (prefixPartial 9 5832) = false := by
  decide +kernel

theorem node_context_9_5832_1327639 : EJMOriginalGlobalDAGData.nodes 12 ⟨1327639, by decide⟩ =
    .split (coordinate 9) (![⟨1326372, by decide⟩,⟨1326838, by decide⟩,⟨1327231, by decide⟩,⟨1327638, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5832_1327639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5832 ⟨1327639, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5832
    ⟨1327639, by decide⟩ (by decide) (![⟨1326372, by decide⟩,⟨1326838, by decide⟩,⟨1327231, by decide⟩,⟨1327638, by decide⟩]) unmarked_context_9_5832_1327639 node_context_9_5832_1327639
  intro a
  fin_cases a
  · exact context_10_23328_1326372
  · exact context_10_23329_1326838
  · exact context_10_23330_1327231
  · exact context_10_23331_1327638

theorem selected_cut_47440 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 93328) = some ⟨11, 1, 0, 907917, 93328, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93328_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93328 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 93328 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 93328, 1, 262144⟩
    (by decide) selected_cut_47440

theorem selected_cut_47441 : selected 9 ⟨1327691, by decide⟩
    (prefixPartial 12 373316) = some ⟨12, 2, 0, 1327691, 373316, 2281, 65536⟩ := by
  decide +kernel

theorem context_12_373316_1327691 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373316 ⟨1327691, by decide⟩ :=
  accepted_of_selected 12 373316 ⟨1327691, by decide⟩ ⟨12, 2, 0, 1327691, 373316, 2281, 65536⟩
    (by decide) selected_cut_47441

theorem selected_cut_47442 : selected 9 ⟨1257136, by decide⟩
    (prefixPartial 12 373317) = some ⟨12, 1, 0, 1257136, 373317, 1, 65536⟩ := by
  decide +kernel

theorem context_12_373317_1257136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373317 ⟨1257136, by decide⟩ :=
  accepted_of_selected 12 373317 ⟨1257136, by decide⟩ ⟨12, 1, 0, 1257136, 373317, 1, 65536⟩
    (by decide) selected_cut_47442

theorem selected_cut_47443 : selected 9 ⟨1327729, by decide⟩
    (prefixPartial 12 373318) = some ⟨12, 2, 0, 1327729, 373318, 2041, 65536⟩ := by
  decide +kernel

theorem context_12_373318_1327729 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373318 ⟨1327729, by decide⟩ :=
  accepted_of_selected 12 373318 ⟨1327729, by decide⟩ ⟨12, 2, 0, 1327729, 373318, 2041, 65536⟩
    (by decide) selected_cut_47443

theorem selected_cut_47444 : selected 9 ⟨1327764, by decide⟩
    (prefixPartial 12 373319) = some ⟨12, 2, 0, 1327764, 373319, 1961, 65536⟩ := by
  decide +kernel

theorem context_12_373319_1327764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373319 ⟨1327764, by decide⟩ :=
  accepted_of_selected 12 373319 ⟨1327764, by decide⟩ ⟨12, 2, 0, 1327764, 373319, 1961, 65536⟩
    (by decide) selected_cut_47444

theorem unmarked_context_11_93329_1327765 : frontier 10 ⟨1327765, by decide⟩
    (prefixCache 11 93329) (prefixPartial 11 93329) = false := by
  decide +kernel

theorem node_context_11_93329_1327765 : EJMOriginalGlobalDAGData.nodes 10 ⟨1327765, by decide⟩ =
    .split (coordinate 11) (![⟨1327691, by decide⟩,⟨1257136, by decide⟩,⟨1327729, by decide⟩,⟨1327764, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93329_1327765 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93329 ⟨1327765, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93329
    ⟨1327765, by decide⟩ (by decide) (![⟨1327691, by decide⟩,⟨1257136, by decide⟩,⟨1327729, by decide⟩,⟨1327764, by decide⟩]) unmarked_context_11_93329_1327765 node_context_11_93329_1327765
  intro a
  fin_cases a
  · exact context_12_373316_1327691
  · exact context_12_373317_1257136
  · exact context_12_373318_1327729
  · exact context_12_373319_1327764

theorem selected_cut_47445 : selected 10 ⟨1327847, by decide⟩
    (prefixPartial 11 93330) = some ⟨11, 2, 0, 1327847, 93330, 4085, 262144⟩ := by
  decide +kernel

theorem context_11_93330_1327847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93330 ⟨1327847, by decide⟩ :=
  accepted_of_selected 11 93330 ⟨1327847, by decide⟩ ⟨11, 2, 0, 1327847, 93330, 4085, 262144⟩
    (by decide) selected_cut_47445

theorem selected_cut_47446 : selected 9 ⟨1327892, by decide⟩
    (prefixPartial 12 373324) = some ⟨12, 2, 0, 1327892, 373324, 2229, 65536⟩ := by
  decide +kernel

theorem context_12_373324_1327892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373324 ⟨1327892, by decide⟩ :=
  accepted_of_selected 12 373324 ⟨1327892, by decide⟩ ⟨12, 2, 0, 1327892, 373324, 2229, 65536⟩
    (by decide) selected_cut_47446

theorem selected_cut_47447 : selected 9 ⟨1327927, by decide⟩
    (prefixPartial 12 373325) = some ⟨12, 2, 0, 1327927, 373325, 2053, 65536⟩ := by
  decide +kernel

theorem context_12_373325_1327927 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373325 ⟨1327927, by decide⟩ :=
  accepted_of_selected 12 373325 ⟨1327927, by decide⟩ ⟨12, 2, 0, 1327927, 373325, 2053, 65536⟩
    (by decide) selected_cut_47447

theorem selected_cut_47448 : selected 9 ⟨1327957, by decide⟩
    (prefixPartial 12 373326) = some ⟨12, 2, 0, 1327957, 373326, 1833, 65536⟩ := by
  decide +kernel

theorem context_12_373326_1327957 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373326 ⟨1327957, by decide⟩ :=
  accepted_of_selected 12 373326 ⟨1327957, by decide⟩ ⟨12, 2, 0, 1327957, 373326, 1833, 65536⟩
    (by decide) selected_cut_47448

theorem selected_cut_47449 : selected 9 ⟨1327997, by decide⟩
    (prefixPartial 12 373327) = some ⟨12, 2, 0, 1327997, 373327, 1785, 65536⟩ := by
  decide +kernel

theorem context_12_373327_1327997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373327 ⟨1327997, by decide⟩ :=
  accepted_of_selected 12 373327 ⟨1327997, by decide⟩ ⟨12, 2, 0, 1327997, 373327, 1785, 65536⟩
    (by decide) selected_cut_47449

theorem unmarked_context_11_93331_1327998 : frontier 10 ⟨1327998, by decide⟩
    (prefixCache 11 93331) (prefixPartial 11 93331) = false := by
  decide +kernel

theorem node_context_11_93331_1327998 : EJMOriginalGlobalDAGData.nodes 10 ⟨1327998, by decide⟩ =
    .split (coordinate 11) (![⟨1327892, by decide⟩,⟨1327927, by decide⟩,⟨1327957, by decide⟩,⟨1327997, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93331_1327998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93331 ⟨1327998, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93331
    ⟨1327998, by decide⟩ (by decide) (![⟨1327892, by decide⟩,⟨1327927, by decide⟩,⟨1327957, by decide⟩,⟨1327997, by decide⟩]) unmarked_context_11_93331_1327998 node_context_11_93331_1327998
  intro a
  fin_cases a
  · exact context_12_373324_1327892
  · exact context_12_373325_1327927
  · exact context_12_373326_1327957
  · exact context_12_373327_1327997

theorem unmarked_context_10_23332_1327999 : frontier 11 ⟨1327999, by decide⟩
    (prefixCache 10 23332) (prefixPartial 10 23332) = false := by
  decide +kernel

theorem node_context_10_23332_1327999 : EJMOriginalGlobalDAGData.nodes 11 ⟨1327999, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨1327765, by decide⟩,⟨1327847, by decide⟩,⟨1327998, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23332_1327999 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23332 ⟨1327999, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23332
    ⟨1327999, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨1327765, by decide⟩,⟨1327847, by decide⟩,⟨1327998, by decide⟩]) unmarked_context_10_23332_1327999 node_context_10_23332_1327999
  intro a
  fin_cases a
  · exact context_11_93328_907917
  · exact context_11_93329_1327765
  · exact context_11_93330_1327847
  · exact context_11_93331_1327998

theorem selected_cut_47450 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 23333) = some ⟨10, 1, 0, 893098, 23333, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_23333_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23333 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 23333 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 23333, 1, 1048576⟩
    (by decide) selected_cut_47450

theorem selected_cut_47451 : selected 10 ⟨1328051, by decide⟩
    (prefixPartial 11 93336) = some ⟨11, 2, 0, 1328051, 93336, 2969, 262144⟩ := by
  decide +kernel

theorem context_11_93336_1328051 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93336 ⟨1328051, by decide⟩ :=
  accepted_of_selected 11 93336 ⟨1328051, by decide⟩ ⟨11, 2, 0, 1328051, 93336, 2969, 262144⟩
    (by decide) selected_cut_47451

theorem selected_cut_47452 : selected 9 ⟨1328081, by decide⟩
    (prefixPartial 12 373348) = some ⟨12, 2, 0, 1328081, 373348, 1837, 65536⟩ := by
  decide +kernel

theorem context_12_373348_1328081 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373348 ⟨1328081, by decide⟩ :=
  accepted_of_selected 12 373348 ⟨1328081, by decide⟩ ⟨12, 2, 0, 1328081, 373348, 1837, 65536⟩
    (by decide) selected_cut_47452

theorem selected_cut_47453 : selected 9 ⟨1256866, by decide⟩
    (prefixPartial 12 373349) = some ⟨12, 1, 0, 1256866, 373349, 1, 65536⟩ := by
  decide +kernel

theorem context_12_373349_1256866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373349 ⟨1256866, by decide⟩ :=
  accepted_of_selected 12 373349 ⟨1256866, by decide⟩ ⟨12, 1, 0, 1256866, 373349, 1, 65536⟩
    (by decide) selected_cut_47453

theorem selected_cut_47454 : selected 9 ⟨1328110, by decide⟩
    (prefixPartial 12 373350) = some ⟨12, 2, 0, 1328110, 373350, 1557, 65536⟩ := by
  decide +kernel

theorem context_12_373350_1328110 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373350 ⟨1328110, by decide⟩ :=
  accepted_of_selected 12 373350 ⟨1328110, by decide⟩ ⟨12, 2, 0, 1328110, 373350, 1557, 65536⟩
    (by decide) selected_cut_47454

theorem selected_cut_47455 : selected 9 ⟨1328139, by decide⟩
    (prefixPartial 12 373351) = some ⟨12, 2, 0, 1328139, 373351, 1557, 65536⟩ := by
  decide +kernel

theorem context_12_373351_1328139 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373351 ⟨1328139, by decide⟩ :=
  accepted_of_selected 12 373351 ⟨1328139, by decide⟩ ⟨12, 2, 0, 1328139, 373351, 1557, 65536⟩
    (by decide) selected_cut_47455

theorem unmarked_context_11_93337_1328140 : frontier 10 ⟨1328140, by decide⟩
    (prefixCache 11 93337) (prefixPartial 11 93337) = false := by
  decide +kernel

theorem node_context_11_93337_1328140 : EJMOriginalGlobalDAGData.nodes 10 ⟨1328140, by decide⟩ =
    .split (coordinate 11) (![⟨1328081, by decide⟩,⟨1256866, by decide⟩,⟨1328110, by decide⟩,⟨1328139, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93337_1328140 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93337 ⟨1328140, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93337
    ⟨1328140, by decide⟩ (by decide) (![⟨1328081, by decide⟩,⟨1256866, by decide⟩,⟨1328110, by decide⟩,⟨1328139, by decide⟩]) unmarked_context_11_93337_1328140 node_context_11_93337_1328140
  intro a
  fin_cases a
  · exact context_12_373348_1328081
  · exact context_12_373349_1256866
  · exact context_12_373350_1328110
  · exact context_12_373351_1328139

theorem selected_cut_47456 : selected 10 ⟨1328168, by decide⟩
    (prefixPartial 11 93338) = some ⟨11, 2, 0, 1328168, 93338, 1493, 262144⟩ := by
  decide +kernel

theorem context_11_93338_1328168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93338 ⟨1328168, by decide⟩ :=
  accepted_of_selected 11 93338 ⟨1328168, by decide⟩ ⟨11, 2, 0, 1328168, 93338, 1493, 262144⟩
    (by decide) selected_cut_47456

theorem selected_cut_47457 : selected 9 ⟨1328201, by decide⟩
    (prefixPartial 12 373356) = some ⟨12, 2, 0, 1328201, 373356, 1789, 65536⟩ := by
  decide +kernel

theorem context_12_373356_1328201 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373356 ⟨1328201, by decide⟩ :=
  accepted_of_selected 12 373356 ⟨1328201, by decide⟩ ⟨12, 2, 0, 1328201, 373356, 1789, 65536⟩
    (by decide) selected_cut_47457

theorem selected_cut_47458 : selected 9 ⟨1256866, by decide⟩
    (prefixPartial 12 373357) = some ⟨12, 1, 0, 1256866, 373357, 1, 65536⟩ := by
  decide +kernel

theorem context_12_373357_1256866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373357 ⟨1256866, by decide⟩ :=
  accepted_of_selected 12 373357 ⟨1256866, by decide⟩ ⟨12, 1, 0, 1256866, 373357, 1, 65536⟩
    (by decide) selected_cut_47458

theorem selected_cut_47459 : selected 9 ⟨1328231, by decide⟩
    (prefixPartial 12 373358) = some ⟨12, 2, 0, 1328231, 373358, 1461, 65536⟩ := by
  decide +kernel

theorem context_12_373358_1328231 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373358 ⟨1328231, by decide⟩ :=
  accepted_of_selected 12 373358 ⟨1328231, by decide⟩ ⟨12, 2, 0, 1328231, 373358, 1461, 65536⟩
    (by decide) selected_cut_47459

theorem selected_cut_47460 : selected 9 ⟨1328259, by decide⟩
    (prefixPartial 12 373359) = some ⟨12, 2, 0, 1328259, 373359, 1525, 65536⟩ := by
  decide +kernel

theorem context_12_373359_1328259 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373359 ⟨1328259, by decide⟩ :=
  accepted_of_selected 12 373359 ⟨1328259, by decide⟩ ⟨12, 2, 0, 1328259, 373359, 1525, 65536⟩
    (by decide) selected_cut_47460

theorem unmarked_context_11_93339_1328260 : frontier 10 ⟨1328260, by decide⟩
    (prefixCache 11 93339) (prefixPartial 11 93339) = false := by
  decide +kernel

theorem node_context_11_93339_1328260 : EJMOriginalGlobalDAGData.nodes 10 ⟨1328260, by decide⟩ =
    .split (coordinate 11) (![⟨1328201, by decide⟩,⟨1256866, by decide⟩,⟨1328231, by decide⟩,⟨1328259, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93339_1328260 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93339 ⟨1328260, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93339
    ⟨1328260, by decide⟩ (by decide) (![⟨1328201, by decide⟩,⟨1256866, by decide⟩,⟨1328231, by decide⟩,⟨1328259, by decide⟩]) unmarked_context_11_93339_1328260 node_context_11_93339_1328260
  intro a
  fin_cases a
  · exact context_12_373356_1328201
  · exact context_12_373357_1256866
  · exact context_12_373358_1328231
  · exact context_12_373359_1328259

theorem unmarked_context_10_23334_1328261 : frontier 11 ⟨1328261, by decide⟩
    (prefixCache 10 23334) (prefixPartial 10 23334) = false := by
  decide +kernel

theorem node_context_10_23334_1328261 : EJMOriginalGlobalDAGData.nodes 11 ⟨1328261, by decide⟩ =
    .split (coordinate 10) (![⟨1328051, by decide⟩,⟨1328140, by decide⟩,⟨1328168, by decide⟩,⟨1328260, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23334_1328261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23334 ⟨1328261, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23334
    ⟨1328261, by decide⟩ (by decide) (![⟨1328051, by decide⟩,⟨1328140, by decide⟩,⟨1328168, by decide⟩,⟨1328260, by decide⟩]) unmarked_context_10_23334_1328261 node_context_10_23334_1328261
  intro a
  fin_cases a
  · exact context_11_93336_1328051
  · exact context_11_93337_1328140
  · exact context_11_93338_1328168
  · exact context_11_93339_1328260

theorem selected_cut_47461 : selected 9 ⟨1328282, by decide⟩
    (prefixPartial 12 373360) = some ⟨12, 2, 0, 1328282, 373360, 1233, 65536⟩ := by
  decide +kernel

theorem context_12_373360_1328282 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373360 ⟨1328282, by decide⟩ :=
  accepted_of_selected 12 373360 ⟨1328282, by decide⟩ ⟨12, 2, 0, 1328282, 373360, 1233, 65536⟩
    (by decide) selected_cut_47461

theorem selected_cut_47462 : selected 9 ⟨1328304, by decide⟩
    (prefixPartial 12 373361) = some ⟨12, 2, 0, 1328304, 373361, 1205, 65536⟩ := by
  decide +kernel

theorem context_12_373361_1328304 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373361 ⟨1328304, by decide⟩ :=
  accepted_of_selected 12 373361 ⟨1328304, by decide⟩ ⟨12, 2, 0, 1328304, 373361, 1205, 65536⟩
    (by decide) selected_cut_47462

theorem selected_cut_47463 : selected 9 ⟨1328317, by decide⟩
    (prefixPartial 12 373362) = some ⟨12, 2, 0, 1328317, 373362, 1069, 65536⟩ := by
  decide +kernel

theorem context_12_373362_1328317 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373362 ⟨1328317, by decide⟩ :=
  accepted_of_selected 12 373362 ⟨1328317, by decide⟩ ⟨12, 2, 0, 1328317, 373362, 1069, 65536⟩
    (by decide) selected_cut_47463

theorem selected_cut_47464 : selected 9 ⟨1328336, by decide⟩
    (prefixPartial 12 373363) = some ⟨12, 2, 0, 1328336, 373363, 1173, 65536⟩ := by
  decide +kernel

theorem context_12_373363_1328336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373363 ⟨1328336, by decide⟩ :=
  accepted_of_selected 12 373363 ⟨1328336, by decide⟩ ⟨12, 2, 0, 1328336, 373363, 1173, 65536⟩
    (by decide) selected_cut_47464

theorem unmarked_context_11_93340_1328337 : frontier 10 ⟨1328337, by decide⟩
    (prefixCache 11 93340) (prefixPartial 11 93340) = false := by
  decide +kernel

theorem node_context_11_93340_1328337 : EJMOriginalGlobalDAGData.nodes 10 ⟨1328337, by decide⟩ =
    .split (coordinate 11) (![⟨1328282, by decide⟩,⟨1328304, by decide⟩,⟨1328317, by decide⟩,⟨1328336, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93340_1328337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93340 ⟨1328337, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93340
    ⟨1328337, by decide⟩ (by decide) (![⟨1328282, by decide⟩,⟨1328304, by decide⟩,⟨1328317, by decide⟩,⟨1328336, by decide⟩]) unmarked_context_11_93340_1328337 node_context_11_93340_1328337
  intro a
  fin_cases a
  · exact context_12_373360_1328282
  · exact context_12_373361_1328304
  · exact context_12_373362_1328317
  · exact context_12_373363_1328336

theorem selected_cut_47465 : selected 10 ⟨1328398, by decide⟩
    (prefixPartial 11 93341) = some ⟨11, 2, 0, 1328398, 93341, 3565, 262144⟩ := by
  decide +kernel

theorem context_11_93341_1328398 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93341 ⟨1328398, by decide⟩ :=
  accepted_of_selected 11 93341 ⟨1328398, by decide⟩ ⟨11, 2, 0, 1328398, 93341, 3565, 262144⟩
    (by decide) selected_cut_47465

theorem selected_cut_47466 : selected 10 ⟨1328449, by decide⟩
    (prefixPartial 11 93342) = some ⟨11, 2, 0, 1328449, 93342, 2357, 262144⟩ := by
  decide +kernel

theorem context_11_93342_1328449 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93342 ⟨1328449, by decide⟩ :=
  accepted_of_selected 11 93342 ⟨1328449, by decide⟩ ⟨11, 2, 0, 1328449, 93342, 2357, 262144⟩
    (by decide) selected_cut_47466

theorem selected_cut_47467 : selected 10 ⟨1328502, by decide⟩
    (prefixPartial 11 93343) = some ⟨11, 2, 0, 1328502, 93343, 3185, 262144⟩ := by
  decide +kernel

theorem context_11_93343_1328502 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93343 ⟨1328502, by decide⟩ :=
  accepted_of_selected 11 93343 ⟨1328502, by decide⟩ ⟨11, 2, 0, 1328502, 93343, 3185, 262144⟩
    (by decide) selected_cut_47467

theorem unmarked_context_10_23335_1328503 : frontier 11 ⟨1328503, by decide⟩
    (prefixCache 10 23335) (prefixPartial 10 23335) = false := by
  decide +kernel

theorem node_context_10_23335_1328503 : EJMOriginalGlobalDAGData.nodes 11 ⟨1328503, by decide⟩ =
    .split (coordinate 10) (![⟨1328337, by decide⟩,⟨1328398, by decide⟩,⟨1328449, by decide⟩,⟨1328502, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23335_1328503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23335 ⟨1328503, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23335
    ⟨1328503, by decide⟩ (by decide) (![⟨1328337, by decide⟩,⟨1328398, by decide⟩,⟨1328449, by decide⟩,⟨1328502, by decide⟩]) unmarked_context_10_23335_1328503 node_context_10_23335_1328503
  intro a
  fin_cases a
  · exact context_11_93340_1328337
  · exact context_11_93341_1328398
  · exact context_11_93342_1328449
  · exact context_11_93343_1328502

theorem unmarked_context_9_5833_1328504 : frontier 12 ⟨1328504, by decide⟩
    (prefixCache 9 5833) (prefixPartial 9 5833) = false := by
  decide +kernel

theorem node_context_9_5833_1328504 : EJMOriginalGlobalDAGData.nodes 12 ⟨1328504, by decide⟩ =
    .split (coordinate 9) (![⟨1327999, by decide⟩,⟨893098, by decide⟩,⟨1328261, by decide⟩,⟨1328503, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5833_1328504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5833 ⟨1328504, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5833
    ⟨1328504, by decide⟩ (by decide) (![⟨1327999, by decide⟩,⟨893098, by decide⟩,⟨1328261, by decide⟩,⟨1328503, by decide⟩]) unmarked_context_9_5833_1328504 node_context_9_5833_1328504
  intro a
  fin_cases a
  · exact context_10_23332_1327999
  · exact context_10_23333_893098
  · exact context_10_23334_1328261
  · exact context_10_23335_1328503

theorem selected_cut_47468 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 93344) = some ⟨11, 1, 0, 907917, 93344, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93344_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93344 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 93344 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 93344, 1, 262144⟩
    (by decide) selected_cut_47468

theorem selected_cut_47469 : selected 10 ⟨1328558, by decide⟩
    (prefixPartial 11 93345) = some ⟨11, 2, 0, 1328558, 93345, 2277, 262144⟩ := by
  decide +kernel

theorem context_11_93345_1328558 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93345 ⟨1328558, by decide⟩ :=
  accepted_of_selected 11 93345 ⟨1328558, by decide⟩ ⟨11, 2, 0, 1328558, 93345, 2277, 262144⟩
    (by decide) selected_cut_47469

theorem selected_cut_47470 : selected 10 ⟨1328618, by decide⟩
    (prefixPartial 11 93346) = some ⟨11, 2, 0, 1328618, 93346, 3041, 262144⟩ := by
  decide +kernel

theorem context_11_93346_1328618 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93346 ⟨1328618, by decide⟩ :=
  accepted_of_selected 11 93346 ⟨1328618, by decide⟩ ⟨11, 2, 0, 1328618, 93346, 3041, 262144⟩
    (by decide) selected_cut_47470

theorem selected_cut_47471 : selected 10 ⟨1328660, by decide⟩
    (prefixPartial 11 93347) = some ⟨11, 2, 0, 1328660, 93347, 2337, 262144⟩ := by
  decide +kernel

theorem context_11_93347_1328660 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93347 ⟨1328660, by decide⟩ :=
  accepted_of_selected 11 93347 ⟨1328660, by decide⟩ ⟨11, 2, 0, 1328660, 93347, 2337, 262144⟩
    (by decide) selected_cut_47471

theorem unmarked_context_10_23336_1328661 : frontier 11 ⟨1328661, by decide⟩
    (prefixCache 10 23336) (prefixPartial 10 23336) = false := by
  decide +kernel

theorem node_context_10_23336_1328661 : EJMOriginalGlobalDAGData.nodes 11 ⟨1328661, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨1328558, by decide⟩,⟨1328618, by decide⟩,⟨1328660, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23336_1328661 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23336 ⟨1328661, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23336
    ⟨1328661, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨1328558, by decide⟩,⟨1328618, by decide⟩,⟨1328660, by decide⟩]) unmarked_context_10_23336_1328661 node_context_10_23336_1328661
  intro a
  fin_cases a
  · exact context_11_93344_907917
  · exact context_11_93345_1328558
  · exact context_11_93346_1328618
  · exact context_11_93347_1328660

theorem selected_cut_47472 : selected 10 ⟨1328705, by decide⟩
    (prefixPartial 11 93348) = some ⟨11, 2, 0, 1328705, 93348, 2141, 262144⟩ := by
  decide +kernel

theorem context_11_93348_1328705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93348 ⟨1328705, by decide⟩ :=
  accepted_of_selected 11 93348 ⟨1328705, by decide⟩ ⟨11, 2, 0, 1328705, 93348, 2141, 262144⟩
    (by decide) selected_cut_47472

theorem selected_cut_47473 : selected 10 ⟨1328730, by decide⟩
    (prefixPartial 11 93349) = some ⟨11, 2, 0, 1328730, 93349, 1021, 262144⟩ := by
  decide +kernel

theorem context_11_93349_1328730 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93349 ⟨1328730, by decide⟩ :=
  accepted_of_selected 11 93349 ⟨1328730, by decide⟩ ⟨11, 2, 0, 1328730, 93349, 1021, 262144⟩
    (by decide) selected_cut_47473

theorem selected_cut_47474 : selected 10 ⟨1328777, by decide⟩
    (prefixPartial 11 93350) = some ⟨11, 2, 0, 1328777, 93350, 2485, 262144⟩ := by
  decide +kernel

theorem context_11_93350_1328777 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93350 ⟨1328777, by decide⟩ :=
  accepted_of_selected 11 93350 ⟨1328777, by decide⟩ ⟨11, 2, 0, 1328777, 93350, 2485, 262144⟩
    (by decide) selected_cut_47474

theorem selected_cut_47475 : selected 10 ⟨1328819, by decide⟩
    (prefixPartial 11 93351) = some ⟨11, 2, 0, 1328819, 93351, 1877, 262144⟩ := by
  decide +kernel

theorem context_11_93351_1328819 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93351 ⟨1328819, by decide⟩ :=
  accepted_of_selected 11 93351 ⟨1328819, by decide⟩ ⟨11, 2, 0, 1328819, 93351, 1877, 262144⟩
    (by decide) selected_cut_47475

theorem unmarked_context_10_23337_1328820 : frontier 11 ⟨1328820, by decide⟩
    (prefixCache 10 23337) (prefixPartial 10 23337) = false := by
  decide +kernel

theorem node_context_10_23337_1328820 : EJMOriginalGlobalDAGData.nodes 11 ⟨1328820, by decide⟩ =
    .split (coordinate 10) (![⟨1328705, by decide⟩,⟨1328730, by decide⟩,⟨1328777, by decide⟩,⟨1328819, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23337_1328820 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23337 ⟨1328820, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23337
    ⟨1328820, by decide⟩ (by decide) (![⟨1328705, by decide⟩,⟨1328730, by decide⟩,⟨1328777, by decide⟩,⟨1328819, by decide⟩]) unmarked_context_10_23337_1328820 node_context_10_23337_1328820
  intro a
  fin_cases a
  · exact context_11_93348_1328705
  · exact context_11_93349_1328730
  · exact context_11_93350_1328777
  · exact context_11_93351_1328819

theorem selected_cut_47476 : selected 11 ⟨1328850, by decide⟩
    (prefixPartial 10 23338) = some ⟨10, 2, 0, 1328850, 23338, 1397, 1048576⟩ := by
  decide +kernel

theorem context_10_23338_1328850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23338 ⟨1328850, by decide⟩ :=
  accepted_of_selected 10 23338 ⟨1328850, by decide⟩ ⟨10, 2, 0, 1328850, 23338, 1397, 1048576⟩
    (by decide) selected_cut_47476

theorem selected_cut_47477 : selected 10 ⟨1328870, by decide⟩
    (prefixPartial 11 93356) = some ⟨11, 2, 0, 1328870, 93356, 1273, 262144⟩ := by
  decide +kernel

theorem context_11_93356_1328870 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93356 ⟨1328870, by decide⟩ :=
  accepted_of_selected 11 93356 ⟨1328870, by decide⟩ ⟨11, 2, 0, 1328870, 93356, 1273, 262144⟩
    (by decide) selected_cut_47477

theorem selected_cut_47478 : selected 10 ⟨1328890, by decide⟩
    (prefixPartial 11 93357) = some ⟨11, 2, 0, 1328890, 93357, 1169, 262144⟩ := by
  decide +kernel

theorem context_11_93357_1328890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93357 ⟨1328890, by decide⟩ :=
  accepted_of_selected 11 93357 ⟨1328890, by decide⟩ ⟨11, 2, 0, 1328890, 93357, 1169, 262144⟩
    (by decide) selected_cut_47478

theorem selected_cut_47479 : selected 10 ⟨1328918, by decide⟩
    (prefixPartial 11 93358) = some ⟨11, 2, 0, 1328918, 93358, 1561, 262144⟩ := by
  decide +kernel

theorem context_11_93358_1328918 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93358 ⟨1328918, by decide⟩ :=
  accepted_of_selected 11 93358 ⟨1328918, by decide⟩ ⟨11, 2, 0, 1328918, 93358, 1561, 262144⟩
    (by decide) selected_cut_47479

theorem selected_cut_47480 : selected 10 ⟨1328930, by decide⟩
    (prefixPartial 11 93359) = some ⟨11, 2, 0, 1328930, 93359, 533, 262144⟩ := by
  decide +kernel

theorem context_11_93359_1328930 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93359 ⟨1328930, by decide⟩ :=
  accepted_of_selected 11 93359 ⟨1328930, by decide⟩ ⟨11, 2, 0, 1328930, 93359, 533, 262144⟩
    (by decide) selected_cut_47480

theorem unmarked_context_10_23339_1328931 : frontier 11 ⟨1328931, by decide⟩
    (prefixCache 10 23339) (prefixPartial 10 23339) = false := by
  decide +kernel

theorem node_context_10_23339_1328931 : EJMOriginalGlobalDAGData.nodes 11 ⟨1328931, by decide⟩ =
    .split (coordinate 10) (![⟨1328870, by decide⟩,⟨1328890, by decide⟩,⟨1328918, by decide⟩,⟨1328930, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23339_1328931 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23339 ⟨1328931, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23339
    ⟨1328931, by decide⟩ (by decide) (![⟨1328870, by decide⟩,⟨1328890, by decide⟩,⟨1328918, by decide⟩,⟨1328930, by decide⟩]) unmarked_context_10_23339_1328931 node_context_10_23339_1328931
  intro a
  fin_cases a
  · exact context_11_93356_1328870
  · exact context_11_93357_1328890
  · exact context_11_93358_1328918
  · exact context_11_93359_1328930

theorem unmarked_context_9_5834_1328932 : frontier 12 ⟨1328932, by decide⟩
    (prefixCache 9 5834) (prefixPartial 9 5834) = false := by
  decide +kernel

theorem node_context_9_5834_1328932 : EJMOriginalGlobalDAGData.nodes 12 ⟨1328932, by decide⟩ =
    .split (coordinate 9) (![⟨1328661, by decide⟩,⟨1328820, by decide⟩,⟨1328850, by decide⟩,⟨1328931, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5834_1328932 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5834 ⟨1328932, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5834
    ⟨1328932, by decide⟩ (by decide) (![⟨1328661, by decide⟩,⟨1328820, by decide⟩,⟨1328850, by decide⟩,⟨1328931, by decide⟩]) unmarked_context_9_5834_1328932 node_context_9_5834_1328932
  intro a
  fin_cases a
  · exact context_10_23336_1328661
  · exact context_10_23337_1328820
  · exact context_10_23338_1328850
  · exact context_10_23339_1328931

theorem selected_cut_47481 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 93360) = some ⟨11, 1, 0, 907917, 93360, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93360_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93360 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 93360 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 93360, 1, 262144⟩
    (by decide) selected_cut_47481

theorem selected_cut_47482 : selected 10 ⟨1328972, by decide⟩
    (prefixPartial 11 93361) = some ⟨11, 2, 0, 1328972, 93361, 2097, 262144⟩ := by
  decide +kernel

theorem context_11_93361_1328972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93361 ⟨1328972, by decide⟩ :=
  accepted_of_selected 11 93361 ⟨1328972, by decide⟩ ⟨11, 2, 0, 1328972, 93361, 2097, 262144⟩
    (by decide) selected_cut_47482

theorem selected_cut_47483 : selected 10 ⟨1328986, by decide⟩
    (prefixPartial 11 93362) = some ⟨11, 2, 0, 1328986, 93362, 729, 262144⟩ := by
  decide +kernel

theorem context_11_93362_1328986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93362 ⟨1328986, by decide⟩ :=
  accepted_of_selected 11 93362 ⟨1328986, by decide⟩ ⟨11, 2, 0, 1328986, 93362, 729, 262144⟩
    (by decide) selected_cut_47483

theorem selected_cut_47484 : selected 10 ⟨1329008, by decide⟩
    (prefixPartial 11 93363) = some ⟨11, 2, 0, 1329008, 93363, 1341, 262144⟩ := by
  decide +kernel

theorem context_11_93363_1329008 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93363 ⟨1329008, by decide⟩ :=
  accepted_of_selected 11 93363 ⟨1329008, by decide⟩ ⟨11, 2, 0, 1329008, 93363, 1341, 262144⟩
    (by decide) selected_cut_47484

theorem unmarked_context_10_23340_1329009 : frontier 11 ⟨1329009, by decide⟩
    (prefixCache 10 23340) (prefixPartial 10 23340) = false := by
  decide +kernel

theorem node_context_10_23340_1329009 : EJMOriginalGlobalDAGData.nodes 11 ⟨1329009, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨1328972, by decide⟩,⟨1328986, by decide⟩,⟨1329008, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23340_1329009 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23340 ⟨1329009, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23340
    ⟨1329009, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨1328972, by decide⟩,⟨1328986, by decide⟩,⟨1329008, by decide⟩]) unmarked_context_10_23340_1329009 node_context_10_23340_1329009
  intro a
  fin_cases a
  · exact context_11_93360_907917
  · exact context_11_93361_1328972
  · exact context_11_93362_1328986
  · exact context_11_93363_1329008

theorem selected_cut_47485 : selected 11 ⟨1329074, by decide⟩
    (prefixPartial 10 23341) = some ⟨10, 2, 0, 1329074, 23341, 3105, 1048576⟩ := by
  decide +kernel

theorem context_10_23341_1329074 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23341 ⟨1329074, by decide⟩ :=
  accepted_of_selected 10 23341 ⟨1329074, by decide⟩ ⟨10, 2, 0, 1329074, 23341, 3105, 1048576⟩
    (by decide) selected_cut_47485

theorem selected_cut_47486 : selected 11 ⟨1329105, by decide⟩
    (prefixPartial 10 23342) = some ⟨10, 2, 0, 1329105, 23342, 1301, 1048576⟩ := by
  decide +kernel

theorem context_10_23342_1329105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23342 ⟨1329105, by decide⟩ :=
  accepted_of_selected 10 23342 ⟨1329105, by decide⟩ ⟨10, 2, 0, 1329105, 23342, 1301, 1048576⟩
    (by decide) selected_cut_47486

theorem selected_cut_47487 : selected 11 ⟨1329125, by decide⟩
    (prefixPartial 10 23343) = some ⟨10, 2, 0, 1329125, 23343, 233, 1048576⟩ := by
  decide +kernel

theorem context_10_23343_1329125 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23343 ⟨1329125, by decide⟩ :=
  accepted_of_selected 10 23343 ⟨1329125, by decide⟩ ⟨10, 2, 0, 1329125, 23343, 233, 1048576⟩
    (by decide) selected_cut_47487

theorem unmarked_context_9_5835_1329126 : frontier 12 ⟨1329126, by decide⟩
    (prefixCache 9 5835) (prefixPartial 9 5835) = false := by
  decide +kernel

theorem node_context_9_5835_1329126 : EJMOriginalGlobalDAGData.nodes 12 ⟨1329126, by decide⟩ =
    .split (coordinate 9) (![⟨1329009, by decide⟩,⟨1329074, by decide⟩,⟨1329105, by decide⟩,⟨1329125, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5835_1329126 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5835 ⟨1329126, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5835
    ⟨1329126, by decide⟩ (by decide) (![⟨1329009, by decide⟩,⟨1329074, by decide⟩,⟨1329105, by decide⟩,⟨1329125, by decide⟩]) unmarked_context_9_5835_1329126 node_context_9_5835_1329126
  intro a
  fin_cases a
  · exact context_10_23340_1329009
  · exact context_10_23341_1329074
  · exact context_10_23342_1329105
  · exact context_10_23343_1329125

theorem unmarked_context_8_1458_1329127 : frontier 13 ⟨1329127, by decide⟩
    (prefixCache 8 1458) (prefixPartial 8 1458) = false := by
  decide +kernel

theorem node_context_8_1458_1329127 : EJMOriginalGlobalDAGData.nodes 13 ⟨1329127, by decide⟩ =
    .split (coordinate 8) (![⟨1327639, by decide⟩,⟨1328504, by decide⟩,⟨1328932, by decide⟩,⟨1329126, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1458_1329127 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1458 ⟨1329127, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1458
    ⟨1329127, by decide⟩ (by decide) (![⟨1327639, by decide⟩,⟨1328504, by decide⟩,⟨1328932, by decide⟩,⟨1329126, by decide⟩]) unmarked_context_8_1458_1329127 node_context_8_1458_1329127
  intro a
  fin_cases a
  · exact context_9_5832_1327639
  · exact context_9_5833_1328504
  · exact context_9_5834_1328932
  · exact context_9_5835_1329126

theorem selected_cut_47488 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 93376) = some ⟨11, 1, 0, 434745, 93376, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93376_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93376 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 93376 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 93376, 1, 262144⟩
    (by decide) selected_cut_47488

theorem selected_cut_47489 : selected 10 ⟨167448, by decide⟩
    (prefixPartial 11 93377) = some ⟨11, 1, 0, 167448, 93377, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93377_167448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93377 ⟨167448, by decide⟩ :=
  accepted_of_selected 11 93377 ⟨167448, by decide⟩ ⟨11, 1, 0, 167448, 93377, 1, 262144⟩
    (by decide) selected_cut_47489

theorem selected_cut_47490 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 373512) = some ⟨12, 1, 0, 448748, 373512, 1, 65536⟩ := by
  decide +kernel

theorem context_12_373512_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373512 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 373512 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 373512, 1, 65536⟩
    (by decide) selected_cut_47490

theorem selected_cut_47491 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 373513) = some ⟨12, 1, 0, 34034, 373513, 1, 65536⟩ := by
  decide +kernel

theorem context_12_373513_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373513 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 373513 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 373513, 1, 65536⟩
    (by decide) selected_cut_47491

theorem selected_cut_47492 : selected 9 ⟨1329181, by decide⟩
    (prefixPartial 12 373514) = some ⟨12, 2, 0, 1329181, 373514, 2577, 65536⟩ := by
  decide +kernel

theorem context_12_373514_1329181 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373514 ⟨1329181, by decide⟩ :=
  accepted_of_selected 12 373514 ⟨1329181, by decide⟩ ⟨12, 2, 0, 1329181, 373514, 2577, 65536⟩
    (by decide) selected_cut_47492

theorem selected_cut_47493 : selected 9 ⟨1329224, by decide⟩
    (prefixPartial 12 373515) = some ⟨12, 2, 0, 1329224, 373515, 2621, 65536⟩ := by
  decide +kernel

theorem context_12_373515_1329224 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373515 ⟨1329224, by decide⟩ :=
  accepted_of_selected 12 373515 ⟨1329224, by decide⟩ ⟨12, 2, 0, 1329224, 373515, 2621, 65536⟩
    (by decide) selected_cut_47493

theorem unmarked_context_11_93378_1329225 : frontier 10 ⟨1329225, by decide⟩
    (prefixCache 11 93378) (prefixPartial 11 93378) = false := by
  decide +kernel

theorem node_context_11_93378_1329225 : EJMOriginalGlobalDAGData.nodes 10 ⟨1329225, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1329181, by decide⟩,⟨1329224, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93378_1329225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93378 ⟨1329225, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93378
    ⟨1329225, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1329181, by decide⟩,⟨1329224, by decide⟩]) unmarked_context_11_93378_1329225 node_context_11_93378_1329225
  intro a
  fin_cases a
  · exact context_12_373512_448748
  · exact context_12_373513_34034
  · exact context_12_373514_1329181
  · exact context_12_373515_1329224

theorem selected_cut_47494 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 373516) = some ⟨12, 1, 0, 448748, 373516, 1, 65536⟩ := by
  decide +kernel

theorem context_12_373516_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373516 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 373516 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 373516, 1, 65536⟩
    (by decide) selected_cut_47494

theorem selected_cut_47495 : selected 9 ⟨1329288, by decide⟩
    (prefixPartial 12 373517) = some ⟨12, 2, 0, 1329288, 373517, 3137, 65536⟩ := by
  decide +kernel

theorem context_12_373517_1329288 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373517 ⟨1329288, by decide⟩ :=
  accepted_of_selected 12 373517 ⟨1329288, by decide⟩ ⟨12, 2, 0, 1329288, 373517, 3137, 65536⟩
    (by decide) selected_cut_47495

theorem selected_cut_47496 : selected 9 ⟨1329355, by decide⟩
    (prefixPartial 12 373518) = some ⟨12, 2, 0, 1329355, 373518, 2937, 65536⟩ := by
  decide +kernel

theorem context_12_373518_1329355 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373518 ⟨1329355, by decide⟩ :=
  accepted_of_selected 12 373518 ⟨1329355, by decide⟩ ⟨12, 2, 0, 1329355, 373518, 2937, 65536⟩
    (by decide) selected_cut_47496

theorem selected_cut_47497 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 373519) = some ⟨12, 1, 0, 903806, 373519, 1, 65536⟩ := by
  decide +kernel

theorem context_12_373519_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373519 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 373519 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 373519, 1, 65536⟩
    (by decide) selected_cut_47497

theorem unmarked_context_11_93379_1329356 : frontier 10 ⟨1329356, by decide⟩
    (prefixCache 11 93379) (prefixPartial 11 93379) = false := by
  decide +kernel

theorem node_context_11_93379_1329356 : EJMOriginalGlobalDAGData.nodes 10 ⟨1329356, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1329288, by decide⟩,⟨1329355, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93379_1329356 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93379 ⟨1329356, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93379
    ⟨1329356, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1329288, by decide⟩,⟨1329355, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_93379_1329356 node_context_11_93379_1329356
  intro a
  fin_cases a
  · exact context_12_373516_448748
  · exact context_12_373517_1329288
  · exact context_12_373518_1329355
  · exact context_12_373519_903806

theorem unmarked_context_10_23344_1329357 : frontier 11 ⟨1329357, by decide⟩
    (prefixCache 10 23344) (prefixPartial 10 23344) = false := by
  decide +kernel

theorem node_context_10_23344_1329357 : EJMOriginalGlobalDAGData.nodes 11 ⟨1329357, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨167448, by decide⟩,⟨1329225, by decide⟩,⟨1329356, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23344_1329357 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23344 ⟨1329357, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23344
    ⟨1329357, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨167448, by decide⟩,⟨1329225, by decide⟩,⟨1329356, by decide⟩]) unmarked_context_10_23344_1329357 node_context_10_23344_1329357
  intro a
  fin_cases a
  · exact context_11_93376_434745
  · exact context_11_93377_167448
  · exact context_11_93378_1329225
  · exact context_11_93379_1329356

theorem selected_cut_47498 : selected 9 ⟨1255011, by decide⟩
    (prefixPartial 12 373520) = some ⟨12, 1, 0, 1255011, 373520, 1, 65536⟩ := by
  decide +kernel

theorem context_12_373520_1255011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373520 ⟨1255011, by decide⟩ :=
  accepted_of_selected 12 373520 ⟨1255011, by decide⟩ ⟨12, 1, 0, 1255011, 373520, 1, 65536⟩
    (by decide) selected_cut_47498

theorem selected_cut_47499 : selected 9 ⟨1329411, by decide⟩
    (prefixPartial 12 373521) = some ⟨12, 2, 0, 1329411, 373521, 2533, 65536⟩ := by
  decide +kernel

theorem context_12_373521_1329411 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373521 ⟨1329411, by decide⟩ :=
  accepted_of_selected 12 373521 ⟨1329411, by decide⟩ ⟨12, 2, 0, 1329411, 373521, 2533, 65536⟩
    (by decide) selected_cut_47499

theorem selected_cut_47500 : selected 9 ⟨1329451, by decide⟩
    (prefixPartial 12 373522) = some ⟨12, 2, 0, 1329451, 373522, 2433, 65536⟩ := by
  decide +kernel

theorem context_12_373522_1329451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373522 ⟨1329451, by decide⟩ :=
  accepted_of_selected 12 373522 ⟨1329451, by decide⟩ ⟨12, 2, 0, 1329451, 373522, 2433, 65536⟩
    (by decide) selected_cut_47500

theorem selected_cut_47501 : selected 9 ⟨1329494, by decide⟩
    (prefixPartial 12 373523) = some ⟨12, 2, 0, 1329494, 373523, 2365, 65536⟩ := by
  decide +kernel

theorem context_12_373523_1329494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373523 ⟨1329494, by decide⟩ :=
  accepted_of_selected 12 373523 ⟨1329494, by decide⟩ ⟨12, 2, 0, 1329494, 373523, 2365, 65536⟩
    (by decide) selected_cut_47501

theorem unmarked_context_11_93380_1329495 : frontier 10 ⟨1329495, by decide⟩
    (prefixCache 11 93380) (prefixPartial 11 93380) = false := by
  decide +kernel

theorem node_context_11_93380_1329495 : EJMOriginalGlobalDAGData.nodes 10 ⟨1329495, by decide⟩ =
    .split (coordinate 11) (![⟨1255011, by decide⟩,⟨1329411, by decide⟩,⟨1329451, by decide⟩,⟨1329494, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93380_1329495 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93380 ⟨1329495, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93380
    ⟨1329495, by decide⟩ (by decide) (![⟨1255011, by decide⟩,⟨1329411, by decide⟩,⟨1329451, by decide⟩,⟨1329494, by decide⟩]) unmarked_context_11_93380_1329495 node_context_11_93380_1329495
  intro a
  fin_cases a
  · exact context_12_373520_1255011
  · exact context_12_373521_1329411
  · exact context_12_373522_1329451
  · exact context_12_373523_1329494

theorem selected_cut_47502 : selected 10 ⟨815620, by decide⟩
    (prefixPartial 11 93381) = some ⟨11, 1, 0, 815620, 93381, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93381_815620 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93381 ⟨815620, by decide⟩ :=
  accepted_of_selected 11 93381 ⟨815620, by decide⟩ ⟨11, 1, 0, 815620, 93381, 1, 262144⟩
    (by decide) selected_cut_47502

theorem selected_cut_47503 : selected 9 ⟨1329549, by decide⟩
    (prefixPartial 12 373528) = some ⟨12, 2, 0, 1329549, 373528, 3089, 65536⟩ := by
  decide +kernel

theorem context_12_373528_1329549 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373528 ⟨1329549, by decide⟩ :=
  accepted_of_selected 12 373528 ⟨1329549, by decide⟩ ⟨12, 2, 0, 1329549, 373528, 3089, 65536⟩
    (by decide) selected_cut_47503

theorem selected_cut_47504 : selected 9 ⟨1329596, by decide⟩
    (prefixPartial 12 373529) = some ⟨12, 2, 0, 1329596, 373529, 2709, 65536⟩ := by
  decide +kernel

theorem context_12_373529_1329596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373529 ⟨1329596, by decide⟩ :=
  accepted_of_selected 12 373529 ⟨1329596, by decide⟩ ⟨12, 2, 0, 1329596, 373529, 2709, 65536⟩
    (by decide) selected_cut_47504

theorem selected_cut_47505 : selected 9 ⟨1329636, by decide⟩
    (prefixPartial 12 373530) = some ⟨12, 2, 0, 1329636, 373530, 2565, 65536⟩ := by
  decide +kernel

theorem context_12_373530_1329636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373530 ⟨1329636, by decide⟩ :=
  accepted_of_selected 12 373530 ⟨1329636, by decide⟩ ⟨12, 2, 0, 1329636, 373530, 2565, 65536⟩
    (by decide) selected_cut_47505

theorem selected_cut_47506 : selected 9 ⟨1329682, by decide⟩
    (prefixPartial 12 373531) = some ⟨12, 2, 0, 1329682, 373531, 2681, 65536⟩ := by
  decide +kernel

theorem context_12_373531_1329682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373531 ⟨1329682, by decide⟩ :=
  accepted_of_selected 12 373531 ⟨1329682, by decide⟩ ⟨12, 2, 0, 1329682, 373531, 2681, 65536⟩
    (by decide) selected_cut_47506

theorem unmarked_context_11_93382_1329683 : frontier 10 ⟨1329683, by decide⟩
    (prefixCache 11 93382) (prefixPartial 11 93382) = false := by
  decide +kernel

theorem node_context_11_93382_1329683 : EJMOriginalGlobalDAGData.nodes 10 ⟨1329683, by decide⟩ =
    .split (coordinate 11) (![⟨1329549, by decide⟩,⟨1329596, by decide⟩,⟨1329636, by decide⟩,⟨1329682, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93382_1329683 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93382 ⟨1329683, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93382
    ⟨1329683, by decide⟩ (by decide) (![⟨1329549, by decide⟩,⟨1329596, by decide⟩,⟨1329636, by decide⟩,⟨1329682, by decide⟩]) unmarked_context_11_93382_1329683 node_context_11_93382_1329683
  intro a
  fin_cases a
  · exact context_12_373528_1329549
  · exact context_12_373529_1329596
  · exact context_12_373530_1329636
  · exact context_12_373531_1329682

theorem selected_cut_47507 : selected 9 ⟨1329738, by decide⟩
    (prefixPartial 12 373532) = some ⟨12, 2, 0, 1329738, 373532, 3009, 65536⟩ := by
  decide +kernel

theorem context_12_373532_1329738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373532 ⟨1329738, by decide⟩ :=
  accepted_of_selected 12 373532 ⟨1329738, by decide⟩ ⟨12, 2, 0, 1329738, 373532, 3009, 65536⟩
    (by decide) selected_cut_47507

theorem selected_cut_47508 : selected 9 ⟨1329787, by decide⟩
    (prefixPartial 12 373533) = some ⟨12, 2, 0, 1329787, 373533, 2817, 65536⟩ := by
  decide +kernel

theorem context_12_373533_1329787 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373533 ⟨1329787, by decide⟩ :=
  accepted_of_selected 12 373533 ⟨1329787, by decide⟩ ⟨12, 2, 0, 1329787, 373533, 2817, 65536⟩
    (by decide) selected_cut_47508

theorem selected_cut_47509 : selected 9 ⟨1329833, by decide⟩
    (prefixPartial 12 373534) = some ⟨12, 2, 0, 1329833, 373534, 2749, 65536⟩ := by
  decide +kernel

theorem context_12_373534_1329833 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373534 ⟨1329833, by decide⟩ :=
  accepted_of_selected 12 373534 ⟨1329833, by decide⟩ ⟨12, 2, 0, 1329833, 373534, 2749, 65536⟩
    (by decide) selected_cut_47509

theorem selected_cut_47510 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 373535) = some ⟨12, 1, 0, 903806, 373535, 1, 65536⟩ := by
  decide +kernel

theorem context_12_373535_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373535 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 373535 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 373535, 1, 65536⟩
    (by decide) selected_cut_47510

theorem unmarked_context_11_93383_1329834 : frontier 10 ⟨1329834, by decide⟩
    (prefixCache 11 93383) (prefixPartial 11 93383) = false := by
  decide +kernel

theorem node_context_11_93383_1329834 : EJMOriginalGlobalDAGData.nodes 10 ⟨1329834, by decide⟩ =
    .split (coordinate 11) (![⟨1329738, by decide⟩,⟨1329787, by decide⟩,⟨1329833, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93383_1329834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93383 ⟨1329834, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93383
    ⟨1329834, by decide⟩ (by decide) (![⟨1329738, by decide⟩,⟨1329787, by decide⟩,⟨1329833, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_93383_1329834 node_context_11_93383_1329834
  intro a
  fin_cases a
  · exact context_12_373532_1329738
  · exact context_12_373533_1329787
  · exact context_12_373534_1329833
  · exact context_12_373535_903806

theorem unmarked_context_10_23345_1329835 : frontier 11 ⟨1329835, by decide⟩
    (prefixCache 10 23345) (prefixPartial 10 23345) = false := by
  decide +kernel

theorem node_context_10_23345_1329835 : EJMOriginalGlobalDAGData.nodes 11 ⟨1329835, by decide⟩ =
    .split (coordinate 10) (![⟨1329495, by decide⟩,⟨815620, by decide⟩,⟨1329683, by decide⟩,⟨1329834, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23345_1329835 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23345 ⟨1329835, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23345
    ⟨1329835, by decide⟩ (by decide) (![⟨1329495, by decide⟩,⟨815620, by decide⟩,⟨1329683, by decide⟩,⟨1329834, by decide⟩]) unmarked_context_10_23345_1329835 node_context_10_23345_1329835
  intro a
  fin_cases a
  · exact context_11_93380_1329495
  · exact context_11_93381_815620
  · exact context_11_93382_1329683
  · exact context_11_93383_1329834

theorem selected_cut_47511 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 373536) = some ⟨12, 1, 0, 435790, 373536, 1, 65536⟩ := by
  decide +kernel

theorem context_12_373536_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373536 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 373536 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 373536, 1, 65536⟩
    (by decide) selected_cut_47511

theorem selected_cut_47512 : selected 9 ⟨1329878, by decide⟩
    (prefixPartial 12 373537) = some ⟨12, 2, 0, 1329878, 373537, 2329, 65536⟩ := by
  decide +kernel

theorem context_12_373537_1329878 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373537 ⟨1329878, by decide⟩ :=
  accepted_of_selected 12 373537 ⟨1329878, by decide⟩ ⟨12, 2, 0, 1329878, 373537, 2329, 65536⟩
    (by decide) selected_cut_47512

theorem selected_cut_47513 : selected 9 ⟨1329914, by decide⟩
    (prefixPartial 12 373538) = some ⟨12, 2, 0, 1329914, 373538, 2217, 65536⟩ := by
  decide +kernel

theorem context_12_373538_1329914 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373538 ⟨1329914, by decide⟩ :=
  accepted_of_selected 12 373538 ⟨1329914, by decide⟩ ⟨12, 2, 0, 1329914, 373538, 2217, 65536⟩
    (by decide) selected_cut_47513

theorem selected_cut_47514 : selected 9 ⟨1329949, by decide⟩
    (prefixPartial 12 373539) = some ⟨12, 2, 0, 1329949, 373539, 2045, 65536⟩ := by
  decide +kernel

theorem context_12_373539_1329949 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373539 ⟨1329949, by decide⟩ :=
  accepted_of_selected 12 373539 ⟨1329949, by decide⟩ ⟨12, 2, 0, 1329949, 373539, 2045, 65536⟩
    (by decide) selected_cut_47514

theorem unmarked_context_11_93384_1329950 : frontier 10 ⟨1329950, by decide⟩
    (prefixCache 11 93384) (prefixPartial 11 93384) = false := by
  decide +kernel

theorem node_context_11_93384_1329950 : EJMOriginalGlobalDAGData.nodes 10 ⟨1329950, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨1329878, by decide⟩,⟨1329914, by decide⟩,⟨1329949, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93384_1329950 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93384 ⟨1329950, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93384
    ⟨1329950, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨1329878, by decide⟩,⟨1329914, by decide⟩,⟨1329949, by decide⟩]) unmarked_context_11_93384_1329950 node_context_11_93384_1329950
  intro a
  fin_cases a
  · exact context_12_373536_435790
  · exact context_12_373537_1329878
  · exact context_12_373538_1329914
  · exact context_12_373539_1329949

theorem selected_cut_47515 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 373540) = some ⟨12, 1, 0, 435790, 373540, 1, 65536⟩ := by
  decide +kernel

theorem context_12_373540_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373540 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 373540 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 373540, 1, 65536⟩
    (by decide) selected_cut_47515

theorem selected_cut_47516 : selected 9 ⟨1330011, by decide⟩
    (prefixPartial 12 373541) = some ⟨12, 2, 0, 1330011, 373541, 3201, 65536⟩ := by
  decide +kernel

theorem context_12_373541_1330011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373541 ⟨1330011, by decide⟩ :=
  accepted_of_selected 12 373541 ⟨1330011, by decide⟩ ⟨12, 2, 0, 1330011, 373541, 3201, 65536⟩
    (by decide) selected_cut_47516

theorem selected_cut_47517 : selected 9 ⟨1330066, by decide⟩
    (prefixPartial 12 373542) = some ⟨12, 2, 0, 1330066, 373542, 3041, 65536⟩ := by
  decide +kernel

theorem context_12_373542_1330066 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373542 ⟨1330066, by decide⟩ :=
  accepted_of_selected 12 373542 ⟨1330066, by decide⟩ ⟨12, 2, 0, 1330066, 373542, 3041, 65536⟩
    (by decide) selected_cut_47517

theorem selected_cut_47518 : selected 9 ⟨1330118, by decide⟩
    (prefixPartial 12 373543) = some ⟨12, 2, 0, 1330118, 373543, 2697, 65536⟩ := by
  decide +kernel

theorem context_12_373543_1330118 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373543 ⟨1330118, by decide⟩ :=
  accepted_of_selected 12 373543 ⟨1330118, by decide⟩ ⟨12, 2, 0, 1330118, 373543, 2697, 65536⟩
    (by decide) selected_cut_47518

theorem unmarked_context_11_93385_1330119 : frontier 10 ⟨1330119, by decide⟩
    (prefixCache 11 93385) (prefixPartial 11 93385) = false := by
  decide +kernel

theorem node_context_11_93385_1330119 : EJMOriginalGlobalDAGData.nodes 10 ⟨1330119, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨1330011, by decide⟩,⟨1330066, by decide⟩,⟨1330118, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93385_1330119 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93385 ⟨1330119, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93385
    ⟨1330119, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨1330011, by decide⟩,⟨1330066, by decide⟩,⟨1330118, by decide⟩]) unmarked_context_11_93385_1330119 node_context_11_93385_1330119
  intro a
  fin_cases a
  · exact context_12_373540_435790
  · exact context_12_373541_1330011
  · exact context_12_373542_1330066
  · exact context_12_373543_1330118

theorem selected_cut_47519 : selected 10 ⟨1330155, by decide⟩
    (prefixPartial 11 93386) = some ⟨11, 2, 0, 1330155, 93386, 2173, 262144⟩ := by
  decide +kernel

theorem context_11_93386_1330155 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93386 ⟨1330155, by decide⟩ :=
  accepted_of_selected 11 93386 ⟨1330155, by decide⟩ ⟨11, 2, 0, 1330155, 93386, 2173, 262144⟩
    (by decide) selected_cut_47519

theorem selected_cut_47520 : selected 9 ⟨1330209, by decide⟩
    (prefixPartial 12 373548) = some ⟨12, 2, 0, 1330209, 373548, 2869, 65536⟩ := by
  decide +kernel

theorem context_12_373548_1330209 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373548 ⟨1330209, by decide⟩ :=
  accepted_of_selected 12 373548 ⟨1330209, by decide⟩ ⟨12, 2, 0, 1330209, 373548, 2869, 65536⟩
    (by decide) selected_cut_47520

theorem selected_cut_47521 : selected 9 ⟨1330267, by decide⟩
    (prefixPartial 12 373549) = some ⟨12, 2, 0, 1330267, 373549, 2685, 65536⟩ := by
  decide +kernel

theorem context_12_373549_1330267 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373549 ⟨1330267, by decide⟩ :=
  accepted_of_selected 12 373549 ⟨1330267, by decide⟩ ⟨12, 2, 0, 1330267, 373549, 2685, 65536⟩
    (by decide) selected_cut_47521

theorem selected_cut_47522 : selected 9 ⟨1330319, by decide⟩
    (prefixPartial 12 373550) = some ⟨12, 2, 0, 1330319, 373550, 2781, 65536⟩ := by
  decide +kernel

theorem context_12_373550_1330319 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373550 ⟨1330319, by decide⟩ :=
  accepted_of_selected 12 373550 ⟨1330319, by decide⟩ ⟨12, 2, 0, 1330319, 373550, 2781, 65536⟩
    (by decide) selected_cut_47522

theorem selected_cut_47523 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 373551) = some ⟨12, 1, 0, 903806, 373551, 1, 65536⟩ := by
  decide +kernel

theorem context_12_373551_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373551 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 373551 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 373551, 1, 65536⟩
    (by decide) selected_cut_47523

theorem unmarked_context_11_93387_1330320 : frontier 10 ⟨1330320, by decide⟩
    (prefixCache 11 93387) (prefixPartial 11 93387) = false := by
  decide +kernel

theorem node_context_11_93387_1330320 : EJMOriginalGlobalDAGData.nodes 10 ⟨1330320, by decide⟩ =
    .split (coordinate 11) (![⟨1330209, by decide⟩,⟨1330267, by decide⟩,⟨1330319, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93387_1330320 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93387 ⟨1330320, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93387
    ⟨1330320, by decide⟩ (by decide) (![⟨1330209, by decide⟩,⟨1330267, by decide⟩,⟨1330319, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_93387_1330320 node_context_11_93387_1330320
  intro a
  fin_cases a
  · exact context_12_373548_1330209
  · exact context_12_373549_1330267
  · exact context_12_373550_1330319
  · exact context_12_373551_903806

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
