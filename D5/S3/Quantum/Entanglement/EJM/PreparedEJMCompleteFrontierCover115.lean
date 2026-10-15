/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover114
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_11_6351_296531 : frontier 10 ⟨296531, by decide⟩
    (prefixCache 11 6351) (prefixPartial 11 6351) = false := by
  decide +kernel

theorem node_context_11_6351_296531 : EJMOriginalGlobalDAGData.nodes 10 ⟨296531, by decide⟩ =
    .split (coordinate 11) (![⟨296410, by decide⟩,⟨296473, by decide⟩,⟨296529, by decide⟩,⟨296530, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6351_296531 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6351 ⟨296531, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6351
    ⟨296531, by decide⟩ (by decide) (![⟨296410, by decide⟩,⟨296473, by decide⟩,⟨296529, by decide⟩,⟨296530, by decide⟩]) unmarked_context_11_6351_296531 node_context_11_6351_296531
  intro a
  fin_cases a
  · exact context_12_25404_296410
  · exact context_12_25405_296473
  · exact context_12_25406_296529
  · exact context_12_25407_296530

theorem unmarked_context_10_1587_296532 : frontier 11 ⟨296532, by decide⟩
    (prefixCache 10 1587) (prefixPartial 10 1587) = false := by
  decide +kernel

theorem node_context_10_1587_296532 : EJMOriginalGlobalDAGData.nodes 11 ⟨296532, by decide⟩ =
    .split (coordinate 10) (![⟨295862, by decide⟩,⟨296108, by decide⟩,⟨296354, by decide⟩,⟨296531, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1587_296532 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1587 ⟨296532, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1587
    ⟨296532, by decide⟩ (by decide) (![⟨295862, by decide⟩,⟨296108, by decide⟩,⟨296354, by decide⟩,⟨296531, by decide⟩]) unmarked_context_10_1587_296532 node_context_10_1587_296532
  intro a
  fin_cases a
  · exact context_11_6348_295862
  · exact context_11_6349_296108
  · exact context_11_6350_296354
  · exact context_11_6351_296531

theorem unmarked_context_9_396_296533 : frontier 12 ⟨296533, by decide⟩
    (prefixCache 9 396) (prefixPartial 9 396) = false := by
  decide +kernel

theorem node_context_9_396_296533 : EJMOriginalGlobalDAGData.nodes 12 ⟨296533, by decide⟩ =
    .split (coordinate 9) (![⟨293254, by decide⟩,⟨294573, by decide⟩,⟨295650, by decide⟩,⟨296532, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_396_296533 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 396 ⟨296533, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 396
    ⟨296533, by decide⟩ (by decide) (![⟨293254, by decide⟩,⟨294573, by decide⟩,⟨295650, by decide⟩,⟨296532, by decide⟩]) unmarked_context_9_396_296533 node_context_9_396_296533
  intro a
  fin_cases a
  · exact context_10_1584_293254
  · exact context_10_1585_294573
  · exact context_10_1586_295650
  · exact context_10_1587_296532

theorem selected_cut_11044 : selected 9 ⟨296534, by decide⟩
    (prefixPartial 12 25408) = some ⟨12, 1, 0, 296534, 25408, 1, 65536⟩ := by
  decide +kernel

theorem context_12_25408_296534 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25408 ⟨296534, by decide⟩ :=
  accepted_of_selected 12 25408 ⟨296534, by decide⟩ ⟨12, 1, 0, 296534, 25408, 1, 65536⟩
    (by decide) selected_cut_11044

theorem selected_cut_11045 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 101636) = some ⟨13, 1, 0, 3444, 101636, 1, 16384⟩ := by
  decide +kernel

theorem context_13_101636_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101636 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 101636 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 101636, 1, 16384⟩
    (by decide) selected_cut_11045

theorem selected_cut_11046 : selected 7 ⟨296570, by decide⟩
    (prefixPartial 14 406548) = some ⟨14, 2, 0, 296570, 406548, 1565, 4096⟩ := by
  decide +kernel

theorem context_14_406548_296570 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 406548 ⟨296570, by decide⟩ :=
  accepted_of_selected 14 406548 ⟨296570, by decide⟩ ⟨14, 2, 0, 296570, 406548, 1565, 4096⟩
    (by decide) selected_cut_11046

theorem selected_cut_11047 : selected 7 ⟨296590, by decide⟩
    (prefixPartial 14 406549) = some ⟨14, 2, 0, 296590, 406549, 881, 4096⟩ := by
  decide +kernel

theorem context_14_406549_296590 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 406549 ⟨296590, by decide⟩ :=
  accepted_of_selected 14 406549 ⟨296590, by decide⟩ ⟨14, 2, 0, 296590, 406549, 881, 4096⟩
    (by decide) selected_cut_11047

theorem selected_cut_11048 : selected 7 ⟨296621, by decide⟩
    (prefixPartial 14 406550) = some ⟨14, 2, 0, 296621, 406550, 1273, 4096⟩ := by
  decide +kernel

theorem context_14_406550_296621 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 406550 ⟨296621, by decide⟩ :=
  accepted_of_selected 14 406550 ⟨296621, by decide⟩ ⟨14, 2, 0, 296621, 406550, 1273, 4096⟩
    (by decide) selected_cut_11048

theorem selected_cut_11049 : selected 7 ⟨296649, by decide⟩
    (prefixPartial 14 406551) = some ⟨14, 2, 0, 296649, 406551, 1121, 4096⟩ := by
  decide +kernel

theorem context_14_406551_296649 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 406551 ⟨296649, by decide⟩ :=
  accepted_of_selected 14 406551 ⟨296649, by decide⟩ ⟨14, 2, 0, 296649, 406551, 1121, 4096⟩
    (by decide) selected_cut_11049

theorem unmarked_context_13_101637_296650 : frontier 8 ⟨296650, by decide⟩
    (prefixCache 13 101637) (prefixPartial 13 101637) = false := by
  decide +kernel

theorem node_context_13_101637_296650 : EJMOriginalGlobalDAGData.nodes 8 ⟨296650, by decide⟩ =
    .split (coordinate 13) (![⟨296570, by decide⟩,⟨296590, by decide⟩,⟨296621, by decide⟩,⟨296649, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_101637_296650 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101637 ⟨296650, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 101637
    ⟨296650, by decide⟩ (by decide) (![⟨296570, by decide⟩,⟨296590, by decide⟩,⟨296621, by decide⟩,⟨296649, by decide⟩]) unmarked_context_13_101637_296650 node_context_13_101637_296650
  intro a
  fin_cases a
  · exact context_14_406548_296570
  · exact context_14_406549_296590
  · exact context_14_406550_296621
  · exact context_14_406551_296649

theorem selected_cut_11050 : selected 8 ⟨296706, by decide⟩
    (prefixPartial 13 101638) = some ⟨13, 2, 0, 296706, 101638, 2885, 16384⟩ := by
  decide +kernel

theorem context_13_101638_296706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101638 ⟨296706, by decide⟩ :=
  accepted_of_selected 13 101638 ⟨296706, by decide⟩ ⟨13, 2, 0, 296706, 101638, 2885, 16384⟩
    (by decide) selected_cut_11050

theorem selected_cut_11051 : selected 8 ⟨296719, by decide⟩
    (prefixPartial 13 101639) = some ⟨13, 2, 0, 296719, 101639, 993, 16384⟩ := by
  decide +kernel

theorem context_13_101639_296719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101639 ⟨296719, by decide⟩ :=
  accepted_of_selected 13 101639 ⟨296719, by decide⟩ ⟨13, 2, 0, 296719, 101639, 993, 16384⟩
    (by decide) selected_cut_11051

theorem unmarked_context_12_25409_296720 : frontier 9 ⟨296720, by decide⟩
    (prefixCache 12 25409) (prefixPartial 12 25409) = false := by
  decide +kernel

theorem node_context_12_25409_296720 : EJMOriginalGlobalDAGData.nodes 9 ⟨296720, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨296650, by decide⟩,⟨296706, by decide⟩,⟨296719, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25409_296720 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25409 ⟨296720, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25409
    ⟨296720, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨296650, by decide⟩,⟨296706, by decide⟩,⟨296719, by decide⟩]) unmarked_context_12_25409_296720 node_context_12_25409_296720
  intro a
  fin_cases a
  · exact context_13_101636_3444
  · exact context_13_101637_296650
  · exact context_13_101638_296706
  · exact context_13_101639_296719

theorem selected_cut_11052 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 101640) = some ⟨13, 1, 0, 3444, 101640, 1, 16384⟩ := by
  decide +kernel

theorem context_13_101640_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101640 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 101640 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 101640, 1, 16384⟩
    (by decide) selected_cut_11052

theorem selected_cut_11053 : selected 8 ⟨296776, by decide⟩
    (prefixPartial 13 101641) = some ⟨13, 2, 0, 296776, 101641, 3469, 16384⟩ := by
  decide +kernel

theorem context_13_101641_296776 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101641 ⟨296776, by decide⟩ :=
  accepted_of_selected 13 101641 ⟨296776, by decide⟩ ⟨13, 2, 0, 296776, 101641, 3469, 16384⟩
    (by decide) selected_cut_11053

theorem selected_cut_11054 : selected 8 ⟨296809, by decide⟩
    (prefixPartial 13 101642) = some ⟨13, 2, 0, 296809, 101642, 2133, 16384⟩ := by
  decide +kernel

theorem context_13_101642_296809 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101642 ⟨296809, by decide⟩ :=
  accepted_of_selected 13 101642 ⟨296809, by decide⟩ ⟨13, 2, 0, 296809, 101642, 2133, 16384⟩
    (by decide) selected_cut_11054

theorem selected_cut_11055 : selected 8 ⟨296818, by decide⟩
    (prefixPartial 13 101643) = some ⟨13, 2, 0, 296818, 101643, 877, 16384⟩ := by
  decide +kernel

theorem context_13_101643_296818 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101643 ⟨296818, by decide⟩ :=
  accepted_of_selected 13 101643 ⟨296818, by decide⟩ ⟨13, 2, 0, 296818, 101643, 877, 16384⟩
    (by decide) selected_cut_11055

theorem unmarked_context_12_25410_296819 : frontier 9 ⟨296819, by decide⟩
    (prefixCache 12 25410) (prefixPartial 12 25410) = false := by
  decide +kernel

theorem node_context_12_25410_296819 : EJMOriginalGlobalDAGData.nodes 9 ⟨296819, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨296776, by decide⟩,⟨296809, by decide⟩,⟨296818, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25410_296819 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25410 ⟨296819, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25410
    ⟨296819, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨296776, by decide⟩,⟨296809, by decide⟩,⟨296818, by decide⟩]) unmarked_context_12_25410_296819 node_context_12_25410_296819
  intro a
  fin_cases a
  · exact context_13_101640_3444
  · exact context_13_101641_296776
  · exact context_13_101642_296809
  · exact context_13_101643_296818

theorem selected_cut_11056 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 101644) = some ⟨13, 1, 0, 3444, 101644, 1, 16384⟩ := by
  decide +kernel

theorem context_13_101644_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101644 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 101644 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 101644, 1, 16384⟩
    (by decide) selected_cut_11056

theorem selected_cut_11057 : selected 8 ⟨296873, by decide⟩
    (prefixPartial 13 101645) = some ⟨13, 2, 0, 296873, 101645, 3597, 16384⟩ := by
  decide +kernel

theorem context_13_101645_296873 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101645 ⟨296873, by decide⟩ :=
  accepted_of_selected 13 101645 ⟨296873, by decide⟩ ⟨13, 2, 0, 296873, 101645, 3597, 16384⟩
    (by decide) selected_cut_11057

theorem selected_cut_11058 : selected 8 ⟨296907, by decide⟩
    (prefixPartial 13 101646) = some ⟨13, 2, 0, 296907, 101646, 2241, 16384⟩ := by
  decide +kernel

theorem context_13_101646_296907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101646 ⟨296907, by decide⟩ :=
  accepted_of_selected 13 101646 ⟨296907, by decide⟩ ⟨13, 2, 0, 296907, 101646, 2241, 16384⟩
    (by decide) selected_cut_11058

theorem selected_cut_11059 : selected 8 ⟨296916, by decide⟩
    (prefixPartial 13 101647) = some ⟨13, 2, 0, 296916, 101647, 921, 16384⟩ := by
  decide +kernel

theorem context_13_101647_296916 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101647 ⟨296916, by decide⟩ :=
  accepted_of_selected 13 101647 ⟨296916, by decide⟩ ⟨13, 2, 0, 296916, 101647, 921, 16384⟩
    (by decide) selected_cut_11059

theorem unmarked_context_12_25411_296917 : frontier 9 ⟨296917, by decide⟩
    (prefixCache 12 25411) (prefixPartial 12 25411) = false := by
  decide +kernel

theorem node_context_12_25411_296917 : EJMOriginalGlobalDAGData.nodes 9 ⟨296917, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨296873, by decide⟩,⟨296907, by decide⟩,⟨296916, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25411_296917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25411 ⟨296917, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25411
    ⟨296917, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨296873, by decide⟩,⟨296907, by decide⟩,⟨296916, by decide⟩]) unmarked_context_12_25411_296917 node_context_12_25411_296917
  intro a
  fin_cases a
  · exact context_13_101644_3444
  · exact context_13_101645_296873
  · exact context_13_101646_296907
  · exact context_13_101647_296916

theorem unmarked_context_11_6352_296918 : frontier 10 ⟨296918, by decide⟩
    (prefixCache 11 6352) (prefixPartial 11 6352) = false := by
  decide +kernel

theorem node_context_11_6352_296918 : EJMOriginalGlobalDAGData.nodes 10 ⟨296918, by decide⟩ =
    .split (coordinate 11) (![⟨296534, by decide⟩,⟨296720, by decide⟩,⟨296819, by decide⟩,⟨296917, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6352_296918 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6352 ⟨296918, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6352
    ⟨296918, by decide⟩ (by decide) (![⟨296534, by decide⟩,⟨296720, by decide⟩,⟨296819, by decide⟩,⟨296917, by decide⟩]) unmarked_context_11_6352_296918 node_context_11_6352_296918
  intro a
  fin_cases a
  · exact context_12_25408_296534
  · exact context_12_25409_296720
  · exact context_12_25410_296819
  · exact context_12_25411_296917

theorem selected_cut_11060 : selected 9 ⟨296974, by decide⟩
    (prefixPartial 12 25412) = some ⟨12, 2, 0, 296974, 25412, 4061, 65536⟩ := by
  decide +kernel

theorem context_12_25412_296974 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25412 ⟨296974, by decide⟩ :=
  accepted_of_selected 12 25412 ⟨296974, by decide⟩ ⟨12, 2, 0, 296974, 25412, 4061, 65536⟩
    (by decide) selected_cut_11060

theorem selected_cut_11061 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 101652) = some ⟨13, 1, 0, 3444, 101652, 1, 16384⟩ := by
  decide +kernel

theorem context_13_101652_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101652 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 101652 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 101652, 1, 16384⟩
    (by decide) selected_cut_11061

theorem selected_cut_11062 : selected 8 ⟨297011, by decide⟩
    (prefixPartial 13 101653) = some ⟨13, 2, 0, 297011, 101653, 3013, 16384⟩ := by
  decide +kernel

theorem context_13_101653_297011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101653 ⟨297011, by decide⟩ :=
  accepted_of_selected 13 101653 ⟨297011, by decide⟩ ⟨13, 2, 0, 297011, 101653, 3013, 16384⟩
    (by decide) selected_cut_11062

theorem selected_cut_11063 : selected 8 ⟨297043, by decide⟩
    (prefixPartial 13 101654) = some ⟨13, 2, 0, 297043, 101654, 2093, 16384⟩ := by
  decide +kernel

theorem context_13_101654_297043 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101654 ⟨297043, by decide⟩ :=
  accepted_of_selected 13 101654 ⟨297043, by decide⟩ ⟨13, 2, 0, 297043, 101654, 2093, 16384⟩
    (by decide) selected_cut_11063

theorem selected_cut_11064 : selected 8 ⟨297051, by decide⟩
    (prefixPartial 13 101655) = some ⟨13, 2, 0, 297051, 101655, 845, 16384⟩ := by
  decide +kernel

theorem context_13_101655_297051 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101655 ⟨297051, by decide⟩ :=
  accepted_of_selected 13 101655 ⟨297051, by decide⟩ ⟨13, 2, 0, 297051, 101655, 845, 16384⟩
    (by decide) selected_cut_11064

theorem unmarked_context_12_25413_297052 : frontier 9 ⟨297052, by decide⟩
    (prefixCache 12 25413) (prefixPartial 12 25413) = false := by
  decide +kernel

theorem node_context_12_25413_297052 : EJMOriginalGlobalDAGData.nodes 9 ⟨297052, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨297011, by decide⟩,⟨297043, by decide⟩,⟨297051, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25413_297052 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25413 ⟨297052, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25413
    ⟨297052, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨297011, by decide⟩,⟨297043, by decide⟩,⟨297051, by decide⟩]) unmarked_context_12_25413_297052 node_context_12_25413_297052
  intro a
  fin_cases a
  · exact context_13_101652_3444
  · exact context_13_101653_297011
  · exact context_13_101654_297043
  · exact context_13_101655_297051

theorem selected_cut_11065 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 101656) = some ⟨13, 1, 0, 3444, 101656, 1, 16384⟩ := by
  decide +kernel

theorem context_13_101656_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101656 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 101656 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 101656, 1, 16384⟩
    (by decide) selected_cut_11065

theorem selected_cut_11066 : selected 8 ⟨297082, by decide⟩
    (prefixPartial 13 101657) = some ⟨13, 2, 0, 297082, 101657, 2477, 16384⟩ := by
  decide +kernel

theorem context_13_101657_297082 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101657 ⟨297082, by decide⟩ :=
  accepted_of_selected 13 101657 ⟨297082, by decide⟩ ⟨13, 2, 0, 297082, 101657, 2477, 16384⟩
    (by decide) selected_cut_11066

theorem selected_cut_11067 : selected 8 ⟨297105, by decide⟩
    (prefixPartial 13 101658) = some ⟨13, 2, 0, 297105, 101658, 1621, 16384⟩ := by
  decide +kernel

theorem context_13_101658_297105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101658 ⟨297105, by decide⟩ :=
  accepted_of_selected 13 101658 ⟨297105, by decide⟩ ⟨13, 2, 0, 297105, 101658, 1621, 16384⟩
    (by decide) selected_cut_11067

theorem selected_cut_11068 : selected 8 ⟨297112, by decide⟩
    (prefixPartial 13 101659) = some ⟨13, 2, 0, 297112, 101659, 801, 16384⟩ := by
  decide +kernel

theorem context_13_101659_297112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101659 ⟨297112, by decide⟩ :=
  accepted_of_selected 13 101659 ⟨297112, by decide⟩ ⟨13, 2, 0, 297112, 101659, 801, 16384⟩
    (by decide) selected_cut_11068

theorem unmarked_context_12_25414_297113 : frontier 9 ⟨297113, by decide⟩
    (prefixCache 12 25414) (prefixPartial 12 25414) = false := by
  decide +kernel

theorem node_context_12_25414_297113 : EJMOriginalGlobalDAGData.nodes 9 ⟨297113, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨297082, by decide⟩,⟨297105, by decide⟩,⟨297112, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25414_297113 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25414 ⟨297113, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25414
    ⟨297113, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨297082, by decide⟩,⟨297105, by decide⟩,⟨297112, by decide⟩]) unmarked_context_12_25414_297113 node_context_12_25414_297113
  intro a
  fin_cases a
  · exact context_13_101656_3444
  · exact context_13_101657_297082
  · exact context_13_101658_297105
  · exact context_13_101659_297112

theorem selected_cut_11069 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 101660) = some ⟨13, 1, 0, 3444, 101660, 1, 16384⟩ := by
  decide +kernel

theorem context_13_101660_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101660 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 101660 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 101660, 1, 16384⟩
    (by decide) selected_cut_11069

theorem selected_cut_11070 : selected 8 ⟨297144, by decide⟩
    (prefixPartial 13 101661) = some ⟨13, 2, 0, 297144, 101661, 2477, 16384⟩ := by
  decide +kernel

theorem context_13_101661_297144 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101661 ⟨297144, by decide⟩ :=
  accepted_of_selected 13 101661 ⟨297144, by decide⟩ ⟨13, 2, 0, 297144, 101661, 2477, 16384⟩
    (by decide) selected_cut_11070

theorem selected_cut_11071 : selected 8 ⟨297164, by decide⟩
    (prefixPartial 13 101662) = some ⟨13, 2, 0, 297164, 101662, 1765, 16384⟩ := by
  decide +kernel

theorem context_13_101662_297164 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101662 ⟨297164, by decide⟩ :=
  accepted_of_selected 13 101662 ⟨297164, by decide⟩ ⟨13, 2, 0, 297164, 101662, 1765, 16384⟩
    (by decide) selected_cut_11071

theorem selected_cut_11072 : selected 8 ⟨297172, by decide⟩
    (prefixPartial 13 101663) = some ⟨13, 2, 0, 297172, 101663, 805, 16384⟩ := by
  decide +kernel

theorem context_13_101663_297172 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101663 ⟨297172, by decide⟩ :=
  accepted_of_selected 13 101663 ⟨297172, by decide⟩ ⟨13, 2, 0, 297172, 101663, 805, 16384⟩
    (by decide) selected_cut_11072

theorem unmarked_context_12_25415_297173 : frontier 9 ⟨297173, by decide⟩
    (prefixCache 12 25415) (prefixPartial 12 25415) = false := by
  decide +kernel

theorem node_context_12_25415_297173 : EJMOriginalGlobalDAGData.nodes 9 ⟨297173, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨297144, by decide⟩,⟨297164, by decide⟩,⟨297172, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25415_297173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25415 ⟨297173, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25415
    ⟨297173, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨297144, by decide⟩,⟨297164, by decide⟩,⟨297172, by decide⟩]) unmarked_context_12_25415_297173 node_context_12_25415_297173
  intro a
  fin_cases a
  · exact context_13_101660_3444
  · exact context_13_101661_297144
  · exact context_13_101662_297164
  · exact context_13_101663_297172

theorem unmarked_context_11_6353_297174 : frontier 10 ⟨297174, by decide⟩
    (prefixCache 11 6353) (prefixPartial 11 6353) = false := by
  decide +kernel

theorem node_context_11_6353_297174 : EJMOriginalGlobalDAGData.nodes 10 ⟨297174, by decide⟩ =
    .split (coordinate 11) (![⟨296974, by decide⟩,⟨297052, by decide⟩,⟨297113, by decide⟩,⟨297173, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6353_297174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6353 ⟨297174, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6353
    ⟨297174, by decide⟩ (by decide) (![⟨296974, by decide⟩,⟨297052, by decide⟩,⟨297113, by decide⟩,⟨297173, by decide⟩]) unmarked_context_11_6353_297174 node_context_11_6353_297174
  intro a
  fin_cases a
  · exact context_12_25412_296974
  · exact context_12_25413_297052
  · exact context_12_25414_297113
  · exact context_12_25415_297173

theorem selected_cut_11073 : selected 9 ⟨297227, by decide⟩
    (prefixPartial 12 25416) = some ⟨12, 2, 0, 297227, 25416, 4041, 65536⟩ := by
  decide +kernel

theorem context_12_25416_297227 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25416 ⟨297227, by decide⟩ :=
  accepted_of_selected 12 25416 ⟨297227, by decide⟩ ⟨12, 2, 0, 297227, 25416, 4041, 65536⟩
    (by decide) selected_cut_11073

theorem selected_cut_11074 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 101668) = some ⟨13, 1, 0, 3444, 101668, 1, 16384⟩ := by
  decide +kernel

theorem context_13_101668_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101668 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 101668 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 101668, 1, 16384⟩
    (by decide) selected_cut_11074

theorem selected_cut_11075 : selected 8 ⟨297262, by decide⟩
    (prefixPartial 13 101669) = some ⟨13, 2, 0, 297262, 101669, 2633, 16384⟩ := by
  decide +kernel

theorem context_13_101669_297262 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101669 ⟨297262, by decide⟩ :=
  accepted_of_selected 13 101669 ⟨297262, by decide⟩ ⟨13, 2, 0, 297262, 101669, 2633, 16384⟩
    (by decide) selected_cut_11075

theorem selected_cut_11076 : selected 8 ⟨297295, by decide⟩
    (prefixPartial 13 101670) = some ⟨13, 2, 0, 297295, 101670, 2317, 16384⟩ := by
  decide +kernel

theorem context_13_101670_297295 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101670 ⟨297295, by decide⟩ :=
  accepted_of_selected 13 101670 ⟨297295, by decide⟩ ⟨13, 2, 0, 297295, 101670, 2317, 16384⟩
    (by decide) selected_cut_11076

theorem selected_cut_11077 : selected 8 ⟨297312, by decide⟩
    (prefixPartial 13 101671) = some ⟨13, 2, 0, 297312, 101671, 1049, 16384⟩ := by
  decide +kernel

theorem context_13_101671_297312 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101671 ⟨297312, by decide⟩ :=
  accepted_of_selected 13 101671 ⟨297312, by decide⟩ ⟨13, 2, 0, 297312, 101671, 1049, 16384⟩
    (by decide) selected_cut_11077

theorem unmarked_context_12_25417_297313 : frontier 9 ⟨297313, by decide⟩
    (prefixCache 12 25417) (prefixPartial 12 25417) = false := by
  decide +kernel

theorem node_context_12_25417_297313 : EJMOriginalGlobalDAGData.nodes 9 ⟨297313, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨297262, by decide⟩,⟨297295, by decide⟩,⟨297312, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25417_297313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25417 ⟨297313, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25417
    ⟨297313, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨297262, by decide⟩,⟨297295, by decide⟩,⟨297312, by decide⟩]) unmarked_context_12_25417_297313 node_context_12_25417_297313
  intro a
  fin_cases a
  · exact context_13_101668_3444
  · exact context_13_101669_297262
  · exact context_13_101670_297295
  · exact context_13_101671_297312

theorem selected_cut_11078 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 101672) = some ⟨13, 1, 0, 3444, 101672, 1, 16384⟩ := by
  decide +kernel

theorem context_13_101672_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101672 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 101672 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 101672, 1, 16384⟩
    (by decide) selected_cut_11078

theorem selected_cut_11079 : selected 8 ⟨297337, by decide⟩
    (prefixPartial 13 101673) = some ⟨13, 2, 0, 297337, 101673, 1957, 16384⟩ := by
  decide +kernel

theorem context_13_101673_297337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101673 ⟨297337, by decide⟩ :=
  accepted_of_selected 13 101673 ⟨297337, by decide⟩ ⟨13, 2, 0, 297337, 101673, 1957, 16384⟩
    (by decide) selected_cut_11079

theorem selected_cut_11080 : selected 8 ⟨297358, by decide⟩
    (prefixPartial 13 101674) = some ⟨13, 2, 0, 297358, 101674, 1865, 16384⟩ := by
  decide +kernel

theorem context_13_101674_297358 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101674 ⟨297358, by decide⟩ :=
  accepted_of_selected 13 101674 ⟨297358, by decide⟩ ⟨13, 2, 0, 297358, 101674, 1865, 16384⟩
    (by decide) selected_cut_11080

theorem selected_cut_11081 : selected 8 ⟨297366, by decide⟩
    (prefixPartial 13 101675) = some ⟨13, 2, 0, 297366, 101675, 785, 16384⟩ := by
  decide +kernel

theorem context_13_101675_297366 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101675 ⟨297366, by decide⟩ :=
  accepted_of_selected 13 101675 ⟨297366, by decide⟩ ⟨13, 2, 0, 297366, 101675, 785, 16384⟩
    (by decide) selected_cut_11081

theorem unmarked_context_12_25418_297367 : frontier 9 ⟨297367, by decide⟩
    (prefixCache 12 25418) (prefixPartial 12 25418) = false := by
  decide +kernel

theorem node_context_12_25418_297367 : EJMOriginalGlobalDAGData.nodes 9 ⟨297367, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨297337, by decide⟩,⟨297358, by decide⟩,⟨297366, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25418_297367 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25418 ⟨297367, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25418
    ⟨297367, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨297337, by decide⟩,⟨297358, by decide⟩,⟨297366, by decide⟩]) unmarked_context_12_25418_297367 node_context_12_25418_297367
  intro a
  fin_cases a
  · exact context_13_101672_3444
  · exact context_13_101673_297337
  · exact context_13_101674_297358
  · exact context_13_101675_297366

theorem selected_cut_11082 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 101676) = some ⟨13, 1, 0, 3444, 101676, 1, 16384⟩ := by
  decide +kernel

theorem context_13_101676_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101676 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 101676 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 101676, 1, 16384⟩
    (by decide) selected_cut_11082

theorem selected_cut_11083 : selected 8 ⟨297391, by decide⟩
    (prefixPartial 13 101677) = some ⟨13, 2, 0, 297391, 101677, 2157, 16384⟩ := by
  decide +kernel

theorem context_13_101677_297391 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101677 ⟨297391, by decide⟩ :=
  accepted_of_selected 13 101677 ⟨297391, by decide⟩ ⟨13, 2, 0, 297391, 101677, 2157, 16384⟩
    (by decide) selected_cut_11083

theorem selected_cut_11084 : selected 8 ⟨297409, by decide⟩
    (prefixPartial 13 101678) = some ⟨13, 2, 0, 297409, 101678, 1857, 16384⟩ := by
  decide +kernel

theorem context_13_101678_297409 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101678 ⟨297409, by decide⟩ :=
  accepted_of_selected 13 101678 ⟨297409, by decide⟩ ⟨13, 2, 0, 297409, 101678, 1857, 16384⟩
    (by decide) selected_cut_11084

theorem selected_cut_11085 : selected 8 ⟨297419, by decide⟩
    (prefixPartial 13 101679) = some ⟨13, 2, 0, 297419, 101679, 761, 16384⟩ := by
  decide +kernel

theorem context_13_101679_297419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101679 ⟨297419, by decide⟩ :=
  accepted_of_selected 13 101679 ⟨297419, by decide⟩ ⟨13, 2, 0, 297419, 101679, 761, 16384⟩
    (by decide) selected_cut_11085

theorem unmarked_context_12_25419_297420 : frontier 9 ⟨297420, by decide⟩
    (prefixCache 12 25419) (prefixPartial 12 25419) = false := by
  decide +kernel

theorem node_context_12_25419_297420 : EJMOriginalGlobalDAGData.nodes 9 ⟨297420, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨297391, by decide⟩,⟨297409, by decide⟩,⟨297419, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25419_297420 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25419 ⟨297420, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25419
    ⟨297420, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨297391, by decide⟩,⟨297409, by decide⟩,⟨297419, by decide⟩]) unmarked_context_12_25419_297420 node_context_12_25419_297420
  intro a
  fin_cases a
  · exact context_13_101676_3444
  · exact context_13_101677_297391
  · exact context_13_101678_297409
  · exact context_13_101679_297419

theorem unmarked_context_11_6354_297421 : frontier 10 ⟨297421, by decide⟩
    (prefixCache 11 6354) (prefixPartial 11 6354) = false := by
  decide +kernel

theorem node_context_11_6354_297421 : EJMOriginalGlobalDAGData.nodes 10 ⟨297421, by decide⟩ =
    .split (coordinate 11) (![⟨297227, by decide⟩,⟨297313, by decide⟩,⟨297367, by decide⟩,⟨297420, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6354_297421 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6354 ⟨297421, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6354
    ⟨297421, by decide⟩ (by decide) (![⟨297227, by decide⟩,⟨297313, by decide⟩,⟨297367, by decide⟩,⟨297420, by decide⟩]) unmarked_context_11_6354_297421 node_context_11_6354_297421
  intro a
  fin_cases a
  · exact context_12_25416_297227
  · exact context_12_25417_297313
  · exact context_12_25418_297367
  · exact context_12_25419_297420

theorem selected_cut_11086 : selected 9 ⟨297459, by decide⟩
    (prefixPartial 12 25420) = some ⟨12, 2, 0, 297459, 25420, 3009, 65536⟩ := by
  decide +kernel

theorem context_12_25420_297459 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25420 ⟨297459, by decide⟩ :=
  accepted_of_selected 12 25420 ⟨297459, by decide⟩ ⟨12, 2, 0, 297459, 25420, 3009, 65536⟩
    (by decide) selected_cut_11086

theorem selected_cut_11087 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 101684) = some ⟨13, 1, 0, 3444, 101684, 1, 16384⟩ := by
  decide +kernel

theorem context_13_101684_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101684 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 101684 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 101684, 1, 16384⟩
    (by decide) selected_cut_11087

theorem selected_cut_11088 : selected 8 ⟨297480, by decide⟩
    (prefixPartial 13 101685) = some ⟨13, 2, 0, 297480, 101685, 2109, 16384⟩ := by
  decide +kernel

theorem context_13_101685_297480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101685 ⟨297480, by decide⟩ :=
  accepted_of_selected 13 101685 ⟨297480, by decide⟩ ⟨13, 2, 0, 297480, 101685, 2109, 16384⟩
    (by decide) selected_cut_11088

theorem selected_cut_11089 : selected 8 ⟨297502, by decide⟩
    (prefixPartial 13 101686) = some ⟨13, 2, 0, 297502, 101686, 2017, 16384⟩ := by
  decide +kernel

theorem context_13_101686_297502 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101686 ⟨297502, by decide⟩ :=
  accepted_of_selected 13 101686 ⟨297502, by decide⟩ ⟨13, 2, 0, 297502, 101686, 2017, 16384⟩
    (by decide) selected_cut_11089

theorem selected_cut_11090 : selected 8 ⟨297511, by decide⟩
    (prefixPartial 13 101687) = some ⟨13, 2, 0, 297511, 101687, 857, 16384⟩ := by
  decide +kernel

theorem context_13_101687_297511 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101687 ⟨297511, by decide⟩ :=
  accepted_of_selected 13 101687 ⟨297511, by decide⟩ ⟨13, 2, 0, 297511, 101687, 857, 16384⟩
    (by decide) selected_cut_11090

theorem unmarked_context_12_25421_297512 : frontier 9 ⟨297512, by decide⟩
    (prefixCache 12 25421) (prefixPartial 12 25421) = false := by
  decide +kernel

theorem node_context_12_25421_297512 : EJMOriginalGlobalDAGData.nodes 9 ⟨297512, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨297480, by decide⟩,⟨297502, by decide⟩,⟨297511, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25421_297512 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25421 ⟨297512, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25421
    ⟨297512, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨297480, by decide⟩,⟨297502, by decide⟩,⟨297511, by decide⟩]) unmarked_context_12_25421_297512 node_context_12_25421_297512
  intro a
  fin_cases a
  · exact context_13_101684_3444
  · exact context_13_101685_297480
  · exact context_13_101686_297502
  · exact context_13_101687_297511

theorem selected_cut_11091 : selected 9 ⟨297560, by decide⟩
    (prefixPartial 12 25422) = some ⟨12, 2, 0, 297560, 25422, 3665, 65536⟩ := by
  decide +kernel

theorem context_12_25422_297560 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25422 ⟨297560, by decide⟩ :=
  accepted_of_selected 12 25422 ⟨297560, by decide⟩ ⟨12, 2, 0, 297560, 25422, 3665, 65536⟩
    (by decide) selected_cut_11091

theorem selected_cut_11092 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 101692) = some ⟨13, 1, 0, 3444, 101692, 1, 16384⟩ := by
  decide +kernel

theorem context_13_101692_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101692 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 101692 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 101692, 1, 16384⟩
    (by decide) selected_cut_11092

theorem selected_cut_11093 : selected 8 ⟨297597, by decide⟩
    (prefixPartial 13 101693) = some ⟨13, 2, 0, 297597, 101693, 2777, 16384⟩ := by
  decide +kernel

theorem context_13_101693_297597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101693 ⟨297597, by decide⟩ :=
  accepted_of_selected 13 101693 ⟨297597, by decide⟩ ⟨13, 2, 0, 297597, 101693, 2777, 16384⟩
    (by decide) selected_cut_11093

theorem selected_cut_11094 : selected 8 ⟨297629, by decide⟩
    (prefixPartial 13 101694) = some ⟨13, 2, 0, 297629, 101694, 2525, 16384⟩ := by
  decide +kernel

theorem context_13_101694_297629 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101694 ⟨297629, by decide⟩ :=
  accepted_of_selected 13 101694 ⟨297629, by decide⟩ ⟨13, 2, 0, 297629, 101694, 2525, 16384⟩
    (by decide) selected_cut_11094

theorem selected_cut_11095 : selected 8 ⟨297658, by decide⟩
    (prefixPartial 13 101695) = some ⟨13, 2, 0, 297658, 101695, 1345, 16384⟩ := by
  decide +kernel

theorem context_13_101695_297658 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101695 ⟨297658, by decide⟩ :=
  accepted_of_selected 13 101695 ⟨297658, by decide⟩ ⟨13, 2, 0, 297658, 101695, 1345, 16384⟩
    (by decide) selected_cut_11095

theorem unmarked_context_12_25423_297659 : frontier 9 ⟨297659, by decide⟩
    (prefixCache 12 25423) (prefixPartial 12 25423) = false := by
  decide +kernel

theorem node_context_12_25423_297659 : EJMOriginalGlobalDAGData.nodes 9 ⟨297659, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨297597, by decide⟩,⟨297629, by decide⟩,⟨297658, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25423_297659 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25423 ⟨297659, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25423
    ⟨297659, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨297597, by decide⟩,⟨297629, by decide⟩,⟨297658, by decide⟩]) unmarked_context_12_25423_297659 node_context_12_25423_297659
  intro a
  fin_cases a
  · exact context_13_101692_3444
  · exact context_13_101693_297597
  · exact context_13_101694_297629
  · exact context_13_101695_297658

theorem unmarked_context_11_6355_297660 : frontier 10 ⟨297660, by decide⟩
    (prefixCache 11 6355) (prefixPartial 11 6355) = false := by
  decide +kernel

theorem node_context_11_6355_297660 : EJMOriginalGlobalDAGData.nodes 10 ⟨297660, by decide⟩ =
    .split (coordinate 11) (![⟨297459, by decide⟩,⟨297512, by decide⟩,⟨297560, by decide⟩,⟨297659, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6355_297660 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6355 ⟨297660, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6355
    ⟨297660, by decide⟩ (by decide) (![⟨297459, by decide⟩,⟨297512, by decide⟩,⟨297560, by decide⟩,⟨297659, by decide⟩]) unmarked_context_11_6355_297660 node_context_11_6355_297660
  intro a
  fin_cases a
  · exact context_12_25420_297459
  · exact context_12_25421_297512
  · exact context_12_25422_297560
  · exact context_12_25423_297659

theorem unmarked_context_10_1588_297661 : frontier 11 ⟨297661, by decide⟩
    (prefixCache 10 1588) (prefixPartial 10 1588) = false := by
  decide +kernel

theorem node_context_10_1588_297661 : EJMOriginalGlobalDAGData.nodes 11 ⟨297661, by decide⟩ =
    .split (coordinate 10) (![⟨296918, by decide⟩,⟨297174, by decide⟩,⟨297421, by decide⟩,⟨297660, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1588_297661 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1588 ⟨297661, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1588
    ⟨297661, by decide⟩ (by decide) (![⟨296918, by decide⟩,⟨297174, by decide⟩,⟨297421, by decide⟩,⟨297660, by decide⟩]) unmarked_context_10_1588_297661 node_context_10_1588_297661
  intro a
  fin_cases a
  · exact context_11_6352_296918
  · exact context_11_6353_297174
  · exact context_11_6354_297421
  · exact context_11_6355_297660

theorem selected_cut_11096 : selected 9 ⟨297699, by decide⟩
    (prefixPartial 12 25424) = some ⟨12, 2, 0, 297699, 25424, 2841, 65536⟩ := by
  decide +kernel

theorem context_12_25424_297699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25424 ⟨297699, by decide⟩ :=
  accepted_of_selected 12 25424 ⟨297699, by decide⟩ ⟨12, 2, 0, 297699, 25424, 2841, 65536⟩
    (by decide) selected_cut_11096

theorem selected_cut_11097 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 25425) = some ⟨12, 1, 0, 170504, 25425, 1, 65536⟩ := by
  decide +kernel

theorem context_12_25425_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25425 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 25425 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 25425, 1, 65536⟩
    (by decide) selected_cut_11097

theorem selected_cut_11098 : selected 9 ⟨297747, by decide⟩
    (prefixPartial 12 25426) = some ⟨12, 2, 0, 297747, 25426, 3777, 65536⟩ := by
  decide +kernel

theorem context_12_25426_297747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25426 ⟨297747, by decide⟩ :=
  accepted_of_selected 12 25426 ⟨297747, by decide⟩ ⟨12, 2, 0, 297747, 25426, 3777, 65536⟩
    (by decide) selected_cut_11098

theorem selected_cut_11099 : selected 9 ⟨297794, by decide⟩
    (prefixPartial 12 25427) = some ⟨12, 2, 0, 297794, 25427, 3929, 65536⟩ := by
  decide +kernel

theorem context_12_25427_297794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25427 ⟨297794, by decide⟩ :=
  accepted_of_selected 12 25427 ⟨297794, by decide⟩ ⟨12, 2, 0, 297794, 25427, 3929, 65536⟩
    (by decide) selected_cut_11099

theorem unmarked_context_11_6356_297795 : frontier 10 ⟨297795, by decide⟩
    (prefixCache 11 6356) (prefixPartial 11 6356) = false := by
  decide +kernel

theorem node_context_11_6356_297795 : EJMOriginalGlobalDAGData.nodes 10 ⟨297795, by decide⟩ =
    .split (coordinate 11) (![⟨297699, by decide⟩,⟨170504, by decide⟩,⟨297747, by decide⟩,⟨297794, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6356_297795 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6356 ⟨297795, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6356
    ⟨297795, by decide⟩ (by decide) (![⟨297699, by decide⟩,⟨170504, by decide⟩,⟨297747, by decide⟩,⟨297794, by decide⟩]) unmarked_context_11_6356_297795 node_context_11_6356_297795
  intro a
  fin_cases a
  · exact context_12_25424_297699
  · exact context_12_25425_170504
  · exact context_12_25426_297747
  · exact context_12_25427_297794

theorem selected_cut_11100 : selected 9 ⟨297837, by decide⟩
    (prefixPartial 12 25428) = some ⟨12, 2, 0, 297837, 25428, 3245, 65536⟩ := by
  decide +kernel

theorem context_12_25428_297837 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25428 ⟨297837, by decide⟩ :=
  accepted_of_selected 12 25428 ⟨297837, by decide⟩ ⟨12, 2, 0, 297837, 25428, 3245, 65536⟩
    (by decide) selected_cut_11100

theorem selected_cut_11101 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 25429) = some ⟨12, 1, 0, 170504, 25429, 1, 65536⟩ := by
  decide +kernel

theorem context_12_25429_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25429 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 25429 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 25429, 1, 65536⟩
    (by decide) selected_cut_11101

theorem selected_cut_11102 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 101720) = some ⟨13, 1, 0, 3444, 101720, 1, 16384⟩ := by
  decide +kernel

theorem context_13_101720_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101720 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 101720 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 101720, 1, 16384⟩
    (by decide) selected_cut_11102

theorem selected_cut_11103 : selected 8 ⟨297862, by decide⟩
    (prefixPartial 13 101721) = some ⟨13, 2, 0, 297862, 101721, 1701, 16384⟩ := by
  decide +kernel

theorem context_13_101721_297862 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101721 ⟨297862, by decide⟩ :=
  accepted_of_selected 13 101721 ⟨297862, by decide⟩ ⟨13, 2, 0, 297862, 101721, 1701, 16384⟩
    (by decide) selected_cut_11103

theorem selected_cut_11104 : selected 8 ⟨297887, by decide⟩
    (prefixPartial 13 101722) = some ⟨13, 2, 0, 297887, 101722, 1565, 16384⟩ := by
  decide +kernel

theorem context_13_101722_297887 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101722 ⟨297887, by decide⟩ :=
  accepted_of_selected 13 101722 ⟨297887, by decide⟩ ⟨13, 2, 0, 297887, 101722, 1565, 16384⟩
    (by decide) selected_cut_11104

theorem selected_cut_11105 : selected 8 ⟨297895, by decide⟩
    (prefixPartial 13 101723) = some ⟨13, 2, 0, 297895, 101723, 857, 16384⟩ := by
  decide +kernel

theorem context_13_101723_297895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101723 ⟨297895, by decide⟩ :=
  accepted_of_selected 13 101723 ⟨297895, by decide⟩ ⟨13, 2, 0, 297895, 101723, 857, 16384⟩
    (by decide) selected_cut_11105

theorem unmarked_context_12_25430_297896 : frontier 9 ⟨297896, by decide⟩
    (prefixCache 12 25430) (prefixPartial 12 25430) = false := by
  decide +kernel

theorem node_context_12_25430_297896 : EJMOriginalGlobalDAGData.nodes 9 ⟨297896, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨297862, by decide⟩,⟨297887, by decide⟩,⟨297895, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25430_297896 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25430 ⟨297896, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25430
    ⟨297896, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨297862, by decide⟩,⟨297887, by decide⟩,⟨297895, by decide⟩]) unmarked_context_12_25430_297896 node_context_12_25430_297896
  intro a
  fin_cases a
  · exact context_13_101720_3444
  · exact context_13_101721_297862
  · exact context_13_101722_297887
  · exact context_13_101723_297895

theorem selected_cut_11106 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 101724) = some ⟨13, 1, 0, 3444, 101724, 1, 16384⟩ := by
  decide +kernel

theorem context_13_101724_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101724 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 101724 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 101724, 1, 16384⟩
    (by decide) selected_cut_11106

theorem selected_cut_11107 : selected 8 ⟨297912, by decide⟩
    (prefixPartial 13 101725) = some ⟨13, 2, 0, 297912, 101725, 1653, 16384⟩ := by
  decide +kernel

theorem context_13_101725_297912 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101725 ⟨297912, by decide⟩ :=
  accepted_of_selected 13 101725 ⟨297912, by decide⟩ ⟨13, 2, 0, 297912, 101725, 1653, 16384⟩
    (by decide) selected_cut_11107

theorem selected_cut_11108 : selected 8 ⟨297935, by decide⟩
    (prefixPartial 13 101726) = some ⟨13, 2, 0, 297935, 101726, 1845, 16384⟩ := by
  decide +kernel

theorem context_13_101726_297935 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101726 ⟨297935, by decide⟩ :=
  accepted_of_selected 13 101726 ⟨297935, by decide⟩ ⟨13, 2, 0, 297935, 101726, 1845, 16384⟩
    (by decide) selected_cut_11108

theorem selected_cut_11109 : selected 8 ⟨297944, by decide⟩
    (prefixPartial 13 101727) = some ⟨13, 2, 0, 297944, 101727, 817, 16384⟩ := by
  decide +kernel

theorem context_13_101727_297944 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101727 ⟨297944, by decide⟩ :=
  accepted_of_selected 13 101727 ⟨297944, by decide⟩ ⟨13, 2, 0, 297944, 101727, 817, 16384⟩
    (by decide) selected_cut_11109

theorem unmarked_context_12_25431_297945 : frontier 9 ⟨297945, by decide⟩
    (prefixCache 12 25431) (prefixPartial 12 25431) = false := by
  decide +kernel

theorem node_context_12_25431_297945 : EJMOriginalGlobalDAGData.nodes 9 ⟨297945, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨297912, by decide⟩,⟨297935, by decide⟩,⟨297944, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25431_297945 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25431 ⟨297945, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25431
    ⟨297945, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨297912, by decide⟩,⟨297935, by decide⟩,⟨297944, by decide⟩]) unmarked_context_12_25431_297945 node_context_12_25431_297945
  intro a
  fin_cases a
  · exact context_13_101724_3444
  · exact context_13_101725_297912
  · exact context_13_101726_297935
  · exact context_13_101727_297944

theorem unmarked_context_11_6357_297946 : frontier 10 ⟨297946, by decide⟩
    (prefixCache 11 6357) (prefixPartial 11 6357) = false := by
  decide +kernel

theorem node_context_11_6357_297946 : EJMOriginalGlobalDAGData.nodes 10 ⟨297946, by decide⟩ =
    .split (coordinate 11) (![⟨297837, by decide⟩,⟨170504, by decide⟩,⟨297896, by decide⟩,⟨297945, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6357_297946 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6357 ⟨297946, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6357
    ⟨297946, by decide⟩ (by decide) (![⟨297837, by decide⟩,⟨170504, by decide⟩,⟨297896, by decide⟩,⟨297945, by decide⟩]) unmarked_context_11_6357_297946 node_context_11_6357_297946
  intro a
  fin_cases a
  · exact context_12_25428_297837
  · exact context_12_25429_170504
  · exact context_12_25430_297896
  · exact context_12_25431_297945

theorem selected_cut_11110 : selected 9 ⟨297992, by decide⟩
    (prefixPartial 12 25432) = some ⟨12, 2, 0, 297992, 25432, 3145, 65536⟩ := by
  decide +kernel

theorem context_12_25432_297992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25432 ⟨297992, by decide⟩ :=
  accepted_of_selected 12 25432 ⟨297992, by decide⟩ ⟨12, 2, 0, 297992, 25432, 3145, 65536⟩
    (by decide) selected_cut_11110

theorem selected_cut_11111 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 101732) = some ⟨13, 1, 0, 3444, 101732, 1, 16384⟩ := by
  decide +kernel

theorem context_13_101732_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101732 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 101732 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 101732, 1, 16384⟩
    (by decide) selected_cut_11111

theorem selected_cut_11112 : selected 8 ⟨298018, by decide⟩
    (prefixPartial 13 101733) = some ⟨13, 2, 0, 298018, 101733, 1609, 16384⟩ := by
  decide +kernel

theorem context_13_101733_298018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101733 ⟨298018, by decide⟩ :=
  accepted_of_selected 13 101733 ⟨298018, by decide⟩ ⟨13, 2, 0, 298018, 101733, 1609, 16384⟩
    (by decide) selected_cut_11112

theorem selected_cut_11113 : selected 8 ⟨298071, by decide⟩
    (prefixPartial 13 101734) = some ⟨13, 2, 0, 298071, 101734, 2389, 16384⟩ := by
  decide +kernel

theorem context_13_101734_298071 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101734 ⟨298071, by decide⟩ :=
  accepted_of_selected 13 101734 ⟨298071, by decide⟩ ⟨13, 2, 0, 298071, 101734, 2389, 16384⟩
    (by decide) selected_cut_11113

theorem selected_cut_11114 : selected 8 ⟨298086, by decide⟩
    (prefixPartial 13 101735) = some ⟨13, 2, 0, 298086, 101735, 1045, 16384⟩ := by
  decide +kernel

theorem context_13_101735_298086 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101735 ⟨298086, by decide⟩ :=
  accepted_of_selected 13 101735 ⟨298086, by decide⟩ ⟨13, 2, 0, 298086, 101735, 1045, 16384⟩
    (by decide) selected_cut_11114

theorem unmarked_context_12_25433_298087 : frontier 9 ⟨298087, by decide⟩
    (prefixCache 12 25433) (prefixPartial 12 25433) = false := by
  decide +kernel

theorem node_context_12_25433_298087 : EJMOriginalGlobalDAGData.nodes 9 ⟨298087, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨298018, by decide⟩,⟨298071, by decide⟩,⟨298086, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25433_298087 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25433 ⟨298087, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25433
    ⟨298087, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨298018, by decide⟩,⟨298071, by decide⟩,⟨298086, by decide⟩]) unmarked_context_12_25433_298087 node_context_12_25433_298087
  intro a
  fin_cases a
  · exact context_13_101732_3444
  · exact context_13_101733_298018
  · exact context_13_101734_298071
  · exact context_13_101735_298086

theorem selected_cut_11115 : selected 9 ⟨298135, by decide⟩
    (prefixPartial 12 25434) = some ⟨12, 2, 0, 298135, 25434, 3533, 65536⟩ := by
  decide +kernel

theorem context_12_25434_298135 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25434 ⟨298135, by decide⟩ :=
  accepted_of_selected 12 25434 ⟨298135, by decide⟩ ⟨12, 2, 0, 298135, 25434, 3533, 65536⟩
    (by decide) selected_cut_11115

theorem selected_cut_11116 : selected 9 ⟨298183, by decide⟩
    (prefixPartial 12 25435) = some ⟨12, 2, 0, 298183, 25435, 3669, 65536⟩ := by
  decide +kernel

theorem context_12_25435_298183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25435 ⟨298183, by decide⟩ :=
  accepted_of_selected 12 25435 ⟨298183, by decide⟩ ⟨12, 2, 0, 298183, 25435, 3669, 65536⟩
    (by decide) selected_cut_11116

theorem unmarked_context_11_6358_298184 : frontier 10 ⟨298184, by decide⟩
    (prefixCache 11 6358) (prefixPartial 11 6358) = false := by
  decide +kernel

theorem node_context_11_6358_298184 : EJMOriginalGlobalDAGData.nodes 10 ⟨298184, by decide⟩ =
    .split (coordinate 11) (![⟨297992, by decide⟩,⟨298087, by decide⟩,⟨298135, by decide⟩,⟨298183, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6358_298184 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6358 ⟨298184, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6358
    ⟨298184, by decide⟩ (by decide) (![⟨297992, by decide⟩,⟨298087, by decide⟩,⟨298135, by decide⟩,⟨298183, by decide⟩]) unmarked_context_11_6358_298184 node_context_11_6358_298184
  intro a
  fin_cases a
  · exact context_12_25432_297992
  · exact context_12_25433_298087
  · exact context_12_25434_298135
  · exact context_12_25435_298183

theorem selected_cut_11117 : selected 9 ⟨298212, by decide⟩
    (prefixPartial 12 25436) = some ⟨12, 2, 0, 298212, 25436, 2529, 65536⟩ := by
  decide +kernel

theorem context_12_25436_298212 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25436 ⟨298212, by decide⟩ :=
  accepted_of_selected 12 25436 ⟨298212, by decide⟩ ⟨12, 2, 0, 298212, 25436, 2529, 65536⟩
    (by decide) selected_cut_11117

theorem selected_cut_11118 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 101748) = some ⟨13, 1, 0, 3444, 101748, 1, 16384⟩ := by
  decide +kernel

theorem context_13_101748_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101748 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 101748 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 101748, 1, 16384⟩
    (by decide) selected_cut_11118

theorem selected_cut_11119 : selected 8 ⟨298231, by decide⟩
    (prefixPartial 13 101749) = some ⟨13, 2, 0, 298231, 101749, 1349, 16384⟩ := by
  decide +kernel

theorem context_13_101749_298231 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101749 ⟨298231, by decide⟩ :=
  accepted_of_selected 13 101749 ⟨298231, by decide⟩ ⟨13, 2, 0, 298231, 101749, 1349, 16384⟩
    (by decide) selected_cut_11119

theorem selected_cut_11120 : selected 8 ⟨298256, by decide⟩
    (prefixPartial 13 101750) = some ⟨13, 2, 0, 298256, 101750, 2105, 16384⟩ := by
  decide +kernel

theorem context_13_101750_298256 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101750 ⟨298256, by decide⟩ :=
  accepted_of_selected 13 101750 ⟨298256, by decide⟩ ⟨13, 2, 0, 298256, 101750, 2105, 16384⟩
    (by decide) selected_cut_11120

theorem selected_cut_11121 : selected 8 ⟨298272, by decide⟩
    (prefixPartial 13 101751) = some ⟨13, 2, 0, 298272, 101751, 825, 16384⟩ := by
  decide +kernel

theorem context_13_101751_298272 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101751 ⟨298272, by decide⟩ :=
  accepted_of_selected 13 101751 ⟨298272, by decide⟩ ⟨13, 2, 0, 298272, 101751, 825, 16384⟩
    (by decide) selected_cut_11121

theorem unmarked_context_12_25437_298273 : frontier 9 ⟨298273, by decide⟩
    (prefixCache 12 25437) (prefixPartial 12 25437) = false := by
  decide +kernel

theorem node_context_12_25437_298273 : EJMOriginalGlobalDAGData.nodes 9 ⟨298273, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨298231, by decide⟩,⟨298256, by decide⟩,⟨298272, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25437_298273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25437 ⟨298273, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25437
    ⟨298273, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨298231, by decide⟩,⟨298256, by decide⟩,⟨298272, by decide⟩]) unmarked_context_12_25437_298273 node_context_12_25437_298273
  intro a
  fin_cases a
  · exact context_13_101748_3444
  · exact context_13_101749_298231
  · exact context_13_101750_298256
  · exact context_13_101751_298272

theorem selected_cut_11122 : selected 9 ⟨298310, by decide⟩
    (prefixPartial 12 25438) = some ⟨12, 2, 0, 298310, 25438, 2961, 65536⟩ := by
  decide +kernel

theorem context_12_25438_298310 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25438 ⟨298310, by decide⟩ :=
  accepted_of_selected 12 25438 ⟨298310, by decide⟩ ⟨12, 2, 0, 298310, 25438, 2961, 65536⟩
    (by decide) selected_cut_11122

theorem selected_cut_11123 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 101756) = some ⟨13, 1, 0, 3444, 101756, 1, 16384⟩ := by
  decide +kernel

theorem context_13_101756_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101756 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 101756 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 101756, 1, 16384⟩
    (by decide) selected_cut_11123

theorem selected_cut_11124 : selected 8 ⟨298341, by decide⟩
    (prefixPartial 13 101757) = some ⟨13, 2, 0, 298341, 101757, 1785, 16384⟩ := by
  decide +kernel

theorem context_13_101757_298341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101757 ⟨298341, by decide⟩ :=
  accepted_of_selected 13 101757 ⟨298341, by decide⟩ ⟨13, 2, 0, 298341, 101757, 1785, 16384⟩
    (by decide) selected_cut_11124

theorem selected_cut_11125 : selected 8 ⟨298385, by decide⟩
    (prefixPartial 13 101758) = some ⟨13, 2, 0, 298385, 101758, 2673, 16384⟩ := by
  decide +kernel

theorem context_13_101758_298385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101758 ⟨298385, by decide⟩ :=
  accepted_of_selected 13 101758 ⟨298385, by decide⟩ ⟨13, 2, 0, 298385, 101758, 2673, 16384⟩
    (by decide) selected_cut_11125

theorem selected_cut_11126 : selected 8 ⟨298409, by decide⟩
    (prefixPartial 13 101759) = some ⟨13, 2, 0, 298409, 101759, 1209, 16384⟩ := by
  decide +kernel

theorem context_13_101759_298409 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101759 ⟨298409, by decide⟩ :=
  accepted_of_selected 13 101759 ⟨298409, by decide⟩ ⟨13, 2, 0, 298409, 101759, 1209, 16384⟩
    (by decide) selected_cut_11126

theorem unmarked_context_12_25439_298410 : frontier 9 ⟨298410, by decide⟩
    (prefixCache 12 25439) (prefixPartial 12 25439) = false := by
  decide +kernel

theorem node_context_12_25439_298410 : EJMOriginalGlobalDAGData.nodes 9 ⟨298410, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨298341, by decide⟩,⟨298385, by decide⟩,⟨298409, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25439_298410 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25439 ⟨298410, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25439
    ⟨298410, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨298341, by decide⟩,⟨298385, by decide⟩,⟨298409, by decide⟩]) unmarked_context_12_25439_298410 node_context_12_25439_298410
  intro a
  fin_cases a
  · exact context_13_101756_3444
  · exact context_13_101757_298341
  · exact context_13_101758_298385
  · exact context_13_101759_298409

theorem unmarked_context_11_6359_298411 : frontier 10 ⟨298411, by decide⟩
    (prefixCache 11 6359) (prefixPartial 11 6359) = false := by
  decide +kernel

theorem node_context_11_6359_298411 : EJMOriginalGlobalDAGData.nodes 10 ⟨298411, by decide⟩ =
    .split (coordinate 11) (![⟨298212, by decide⟩,⟨298273, by decide⟩,⟨298310, by decide⟩,⟨298410, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6359_298411 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6359 ⟨298411, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6359
    ⟨298411, by decide⟩ (by decide) (![⟨298212, by decide⟩,⟨298273, by decide⟩,⟨298310, by decide⟩,⟨298410, by decide⟩]) unmarked_context_11_6359_298411 node_context_11_6359_298411
  intro a
  fin_cases a
  · exact context_12_25436_298212
  · exact context_12_25437_298273
  · exact context_12_25438_298310
  · exact context_12_25439_298410

theorem unmarked_context_10_1589_298412 : frontier 11 ⟨298412, by decide⟩
    (prefixCache 10 1589) (prefixPartial 10 1589) = false := by
  decide +kernel

theorem node_context_10_1589_298412 : EJMOriginalGlobalDAGData.nodes 11 ⟨298412, by decide⟩ =
    .split (coordinate 10) (![⟨297795, by decide⟩,⟨297946, by decide⟩,⟨298184, by decide⟩,⟨298411, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1589_298412 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1589 ⟨298412, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1589
    ⟨298412, by decide⟩ (by decide) (![⟨297795, by decide⟩,⟨297946, by decide⟩,⟨298184, by decide⟩,⟨298411, by decide⟩]) unmarked_context_10_1589_298412 node_context_10_1589_298412
  intro a
  fin_cases a
  · exact context_11_6356_297795
  · exact context_11_6357_297946
  · exact context_11_6358_298184
  · exact context_11_6359_298411

theorem selected_cut_11127 : selected 9 ⟨298440, by decide⟩
    (prefixPartial 12 25440) = some ⟨12, 2, 0, 298440, 25440, 2713, 65536⟩ := by
  decide +kernel

theorem context_12_25440_298440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25440 ⟨298440, by decide⟩ :=
  accepted_of_selected 12 25440 ⟨298440, by decide⟩ ⟨12, 2, 0, 298440, 25440, 2713, 65536⟩
    (by decide) selected_cut_11127

theorem selected_cut_11128 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 101764) = some ⟨13, 1, 0, 3444, 101764, 1, 16384⟩ := by
  decide +kernel

theorem context_13_101764_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101764 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 101764 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 101764, 1, 16384⟩
    (by decide) selected_cut_11128

theorem selected_cut_11129 : selected 8 ⟨298460, by decide⟩
    (prefixPartial 13 101765) = some ⟨13, 2, 0, 298460, 101765, 1725, 16384⟩ := by
  decide +kernel

theorem context_13_101765_298460 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101765 ⟨298460, by decide⟩ :=
  accepted_of_selected 13 101765 ⟨298460, by decide⟩ ⟨13, 2, 0, 298460, 101765, 1725, 16384⟩
    (by decide) selected_cut_11129

theorem selected_cut_11130 : selected 8 ⟨298488, by decide⟩
    (prefixPartial 13 101766) = some ⟨13, 2, 0, 298488, 101766, 1977, 16384⟩ := by
  decide +kernel

theorem context_13_101766_298488 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101766 ⟨298488, by decide⟩ :=
  accepted_of_selected 13 101766 ⟨298488, by decide⟩ ⟨13, 2, 0, 298488, 101766, 1977, 16384⟩
    (by decide) selected_cut_11130

theorem selected_cut_11131 : selected 8 ⟨298495, by decide⟩
    (prefixPartial 13 101767) = some ⟨13, 2, 0, 298495, 101767, 813, 16384⟩ := by
  decide +kernel

theorem context_13_101767_298495 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101767 ⟨298495, by decide⟩ :=
  accepted_of_selected 13 101767 ⟨298495, by decide⟩ ⟨13, 2, 0, 298495, 101767, 813, 16384⟩
    (by decide) selected_cut_11131

theorem unmarked_context_12_25441_298496 : frontier 9 ⟨298496, by decide⟩
    (prefixCache 12 25441) (prefixPartial 12 25441) = false := by
  decide +kernel

theorem node_context_12_25441_298496 : EJMOriginalGlobalDAGData.nodes 9 ⟨298496, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨298460, by decide⟩,⟨298488, by decide⟩,⟨298495, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25441_298496 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25441 ⟨298496, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25441
    ⟨298496, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨298460, by decide⟩,⟨298488, by decide⟩,⟨298495, by decide⟩]) unmarked_context_12_25441_298496 node_context_12_25441_298496
  intro a
  fin_cases a
  · exact context_13_101764_3444
  · exact context_13_101765_298460
  · exact context_13_101766_298488
  · exact context_13_101767_298495

theorem selected_cut_11132 : selected 9 ⟨298541, by decide⟩
    (prefixPartial 12 25442) = some ⟨12, 2, 0, 298541, 25442, 3437, 65536⟩ := by
  decide +kernel

theorem context_12_25442_298541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25442 ⟨298541, by decide⟩ :=
  accepted_of_selected 12 25442 ⟨298541, by decide⟩ ⟨12, 2, 0, 298541, 25442, 3437, 65536⟩
    (by decide) selected_cut_11132

theorem selected_cut_11133 : selected 9 ⟨298584, by decide⟩
    (prefixPartial 12 25443) = some ⟨12, 2, 0, 298584, 25443, 3433, 65536⟩ := by
  decide +kernel

theorem context_12_25443_298584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25443 ⟨298584, by decide⟩ :=
  accepted_of_selected 12 25443 ⟨298584, by decide⟩ ⟨12, 2, 0, 298584, 25443, 3433, 65536⟩
    (by decide) selected_cut_11133

theorem unmarked_context_11_6360_298585 : frontier 10 ⟨298585, by decide⟩
    (prefixCache 11 6360) (prefixPartial 11 6360) = false := by
  decide +kernel

theorem node_context_11_6360_298585 : EJMOriginalGlobalDAGData.nodes 10 ⟨298585, by decide⟩ =
    .split (coordinate 11) (![⟨298440, by decide⟩,⟨298496, by decide⟩,⟨298541, by decide⟩,⟨298584, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6360_298585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6360 ⟨298585, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6360
    ⟨298585, by decide⟩ (by decide) (![⟨298440, by decide⟩,⟨298496, by decide⟩,⟨298541, by decide⟩,⟨298584, by decide⟩]) unmarked_context_11_6360_298585 node_context_11_6360_298585
  intro a
  fin_cases a
  · exact context_12_25440_298440
  · exact context_12_25441_298496
  · exact context_12_25442_298541
  · exact context_12_25443_298584

theorem selected_cut_11134 : selected 9 ⟨298619, by decide⟩
    (prefixPartial 12 25444) = some ⟨12, 2, 0, 298619, 25444, 2937, 65536⟩ := by
  decide +kernel

theorem context_12_25444_298619 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25444 ⟨298619, by decide⟩ :=
  accepted_of_selected 12 25444 ⟨298619, by decide⟩ ⟨12, 2, 0, 298619, 25444, 2937, 65536⟩
    (by decide) selected_cut_11134

theorem selected_cut_11135 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 101780) = some ⟨13, 1, 0, 3444, 101780, 1, 16384⟩ := by
  decide +kernel

theorem context_13_101780_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101780 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 101780 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 101780, 1, 16384⟩
    (by decide) selected_cut_11135

theorem selected_cut_11136 : selected 8 ⟨298642, by decide⟩
    (prefixPartial 13 101781) = some ⟨13, 2, 0, 298642, 101781, 1545, 16384⟩ := by
  decide +kernel

theorem context_13_101781_298642 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101781 ⟨298642, by decide⟩ :=
  accepted_of_selected 13 101781 ⟨298642, by decide⟩ ⟨13, 2, 0, 298642, 101781, 1545, 16384⟩
    (by decide) selected_cut_11136

theorem selected_cut_11137 : selected 8 ⟨298677, by decide⟩
    (prefixPartial 13 101782) = some ⟨13, 2, 0, 298677, 101782, 2205, 16384⟩ := by
  decide +kernel

theorem context_13_101782_298677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101782 ⟨298677, by decide⟩ :=
  accepted_of_selected 13 101782 ⟨298677, by decide⟩ ⟨13, 2, 0, 298677, 101782, 2205, 16384⟩
    (by decide) selected_cut_11137

theorem selected_cut_11138 : selected 8 ⟨298688, by decide⟩
    (prefixPartial 13 101783) = some ⟨13, 2, 0, 298688, 101783, 937, 16384⟩ := by
  decide +kernel

theorem context_13_101783_298688 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 101783 ⟨298688, by decide⟩ :=
  accepted_of_selected 13 101783 ⟨298688, by decide⟩ ⟨13, 2, 0, 298688, 101783, 937, 16384⟩
    (by decide) selected_cut_11138

theorem unmarked_context_12_25445_298689 : frontier 9 ⟨298689, by decide⟩
    (prefixCache 12 25445) (prefixPartial 12 25445) = false := by
  decide +kernel

theorem node_context_12_25445_298689 : EJMOriginalGlobalDAGData.nodes 9 ⟨298689, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨298642, by decide⟩,⟨298677, by decide⟩,⟨298688, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25445_298689 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25445 ⟨298689, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25445
    ⟨298689, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨298642, by decide⟩,⟨298677, by decide⟩,⟨298688, by decide⟩]) unmarked_context_12_25445_298689 node_context_12_25445_298689
  intro a
  fin_cases a
  · exact context_13_101780_3444
  · exact context_13_101781_298642
  · exact context_13_101782_298677
  · exact context_13_101783_298688

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
