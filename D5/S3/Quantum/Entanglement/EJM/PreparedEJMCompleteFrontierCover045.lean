/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover044
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_04322 : selected 8 ⟨137540, by decide⟩
    (prefixPartial 13 73742) = some ⟨13, 2, 0, 137540, 73742, 2809, 16384⟩ := by
  decide +kernel

theorem context_13_73742_137540 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73742 ⟨137540, by decide⟩ :=
  accepted_of_selected 13 73742 ⟨137540, by decide⟩ ⟨13, 2, 0, 137540, 73742, 2809, 16384⟩
    (by decide) selected_cut_04322

theorem selected_cut_04323 : selected 8 ⟨137560, by decide⟩
    (prefixPartial 13 73743) = some ⟨13, 2, 0, 137560, 73743, 1225, 16384⟩ := by
  decide +kernel

theorem context_13_73743_137560 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73743 ⟨137560, by decide⟩ :=
  accepted_of_selected 13 73743 ⟨137560, by decide⟩ ⟨13, 2, 0, 137560, 73743, 1225, 16384⟩
    (by decide) selected_cut_04323

theorem unmarked_context_12_18435_137561 : frontier 9 ⟨137561, by decide⟩
    (prefixCache 12 18435) (prefixPartial 12 18435) = false := by
  decide +kernel

theorem node_context_12_18435_137561 : EJMOriginalGlobalDAGData.nodes 9 ⟨137561, by decide⟩ =
    .split (coordinate 12) (![⟨137352, by decide⟩,⟨137477, by decide⟩,⟨137540, by decide⟩,⟨137560, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18435_137561 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18435 ⟨137561, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18435
    ⟨137561, by decide⟩ (by decide) (![⟨137352, by decide⟩,⟨137477, by decide⟩,⟨137540, by decide⟩,⟨137560, by decide⟩]) unmarked_context_12_18435_137561 node_context_12_18435_137561
  intro a
  fin_cases a
  · exact context_13_73740_137352
  · exact context_13_73741_137477
  · exact context_13_73742_137540
  · exact context_13_73743_137560

theorem unmarked_context_11_4608_137562 : frontier 10 ⟨137562, by decide⟩
    (prefixCache 11 4608) (prefixPartial 11 4608) = false := by
  decide +kernel

theorem node_context_11_4608_137562 : EJMOriginalGlobalDAGData.nodes 10 ⟨137562, by decide⟩ =
    .split (coordinate 11) (![⟨136570, by decide⟩,⟨136904, by decide⟩,⟨137222, by decide⟩,⟨137561, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4608_137562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4608 ⟨137562, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4608
    ⟨137562, by decide⟩ (by decide) (![⟨136570, by decide⟩,⟨136904, by decide⟩,⟨137222, by decide⟩,⟨137561, by decide⟩]) unmarked_context_11_4608_137562 node_context_11_4608_137562
  intro a
  fin_cases a
  · exact context_12_18432_136570
  · exact context_12_18433_136904
  · exact context_12_18434_137222
  · exact context_12_18435_137561

theorem selected_cut_04324 : selected 9 ⟨4595, by decide⟩
    (prefixPartial 12 18436) = some ⟨12, 1, 0, 4595, 18436, 1, 65536⟩ := by
  decide +kernel

theorem context_12_18436_4595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18436 ⟨4595, by decide⟩ :=
  accepted_of_selected 12 18436 ⟨4595, by decide⟩ ⟨12, 1, 0, 4595, 18436, 1, 65536⟩
    (by decide) selected_cut_04324

theorem selected_cut_04325 : selected 7 ⟨137596, by decide⟩
    (prefixPartial 14 294992) = some ⟨14, 2, 0, 137596, 294992, 1373, 4096⟩ := by
  decide +kernel

theorem context_14_294992_137596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 294992 ⟨137596, by decide⟩ :=
  accepted_of_selected 14 294992 ⟨137596, by decide⟩ ⟨14, 2, 0, 137596, 294992, 1373, 4096⟩
    (by decide) selected_cut_04325

theorem selected_cut_04326 : selected 7 ⟨137622, by decide⟩
    (prefixPartial 14 294993) = some ⟨14, 2, 0, 137622, 294993, 1609, 4096⟩ := by
  decide +kernel

theorem context_14_294993_137622 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 294993 ⟨137622, by decide⟩ :=
  accepted_of_selected 14 294993 ⟨137622, by decide⟩ ⟨14, 2, 0, 137622, 294993, 1609, 4096⟩
    (by decide) selected_cut_04326

theorem selected_cut_04327 : selected 7 ⟨137656, by decide⟩
    (prefixPartial 14 294994) = some ⟨14, 2, 0, 137656, 294994, 1573, 4096⟩ := by
  decide +kernel

theorem context_14_294994_137656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 294994 ⟨137656, by decide⟩ :=
  accepted_of_selected 14 294994 ⟨137656, by decide⟩ ⟨14, 2, 0, 137656, 294994, 1573, 4096⟩
    (by decide) selected_cut_04327

theorem selected_cut_04328 : selected 7 ⟨137687, by decide⟩
    (prefixPartial 14 294995) = some ⟨14, 2, 0, 137687, 294995, 1417, 4096⟩ := by
  decide +kernel

theorem context_14_294995_137687 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 294995 ⟨137687, by decide⟩ :=
  accepted_of_selected 14 294995 ⟨137687, by decide⟩ ⟨14, 2, 0, 137687, 294995, 1417, 4096⟩
    (by decide) selected_cut_04328

theorem unmarked_context_13_73748_137688 : frontier 8 ⟨137688, by decide⟩
    (prefixCache 13 73748) (prefixPartial 13 73748) = false := by
  decide +kernel

theorem node_context_13_73748_137688 : EJMOriginalGlobalDAGData.nodes 8 ⟨137688, by decide⟩ =
    .split (coordinate 13) (![⟨137596, by decide⟩,⟨137622, by decide⟩,⟨137656, by decide⟩,⟨137687, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_73748_137688 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73748 ⟨137688, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 73748
    ⟨137688, by decide⟩ (by decide) (![⟨137596, by decide⟩,⟨137622, by decide⟩,⟨137656, by decide⟩,⟨137687, by decide⟩]) unmarked_context_13_73748_137688 node_context_13_73748_137688
  intro a
  fin_cases a
  · exact context_14_294992_137596
  · exact context_14_294993_137622
  · exact context_14_294994_137656
  · exact context_14_294995_137687

theorem selected_cut_04329 : selected 7 ⟨137712, by decide⟩
    (prefixPartial 14 294996) = some ⟨14, 2, 0, 137712, 294996, 1117, 4096⟩ := by
  decide +kernel

theorem context_14_294996_137712 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 294996 ⟨137712, by decide⟩ :=
  accepted_of_selected 14 294996 ⟨137712, by decide⟩ ⟨14, 2, 0, 137712, 294996, 1117, 4096⟩
    (by decide) selected_cut_04329

theorem selected_cut_04330 : selected 7 ⟨137758, by decide⟩
    (prefixPartial 14 294997) = some ⟨14, 2, 0, 137758, 294997, 1437, 4096⟩ := by
  decide +kernel

theorem context_14_294997_137758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 294997 ⟨137758, by decide⟩ :=
  accepted_of_selected 14 294997 ⟨137758, by decide⟩ ⟨14, 2, 0, 137758, 294997, 1437, 4096⟩
    (by decide) selected_cut_04330

theorem selected_cut_04331 : selected 7 ⟨137788, by decide⟩
    (prefixPartial 14 294998) = some ⟨14, 2, 0, 137788, 294998, 1457, 4096⟩ := by
  decide +kernel

theorem context_14_294998_137788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 294998 ⟨137788, by decide⟩ :=
  accepted_of_selected 14 294998 ⟨137788, by decide⟩ ⟨14, 2, 0, 137788, 294998, 1457, 4096⟩
    (by decide) selected_cut_04331

theorem selected_cut_04332 : selected 7 ⟨137816, by decide⟩
    (prefixPartial 14 294999) = some ⟨14, 2, 0, 137816, 294999, 1237, 4096⟩ := by
  decide +kernel

theorem context_14_294999_137816 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 294999 ⟨137816, by decide⟩ :=
  accepted_of_selected 14 294999 ⟨137816, by decide⟩ ⟨14, 2, 0, 137816, 294999, 1237, 4096⟩
    (by decide) selected_cut_04332

theorem unmarked_context_13_73749_137817 : frontier 8 ⟨137817, by decide⟩
    (prefixCache 13 73749) (prefixPartial 13 73749) = false := by
  decide +kernel

theorem node_context_13_73749_137817 : EJMOriginalGlobalDAGData.nodes 8 ⟨137817, by decide⟩ =
    .split (coordinate 13) (![⟨137712, by decide⟩,⟨137758, by decide⟩,⟨137788, by decide⟩,⟨137816, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_73749_137817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73749 ⟨137817, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 73749
    ⟨137817, by decide⟩ (by decide) (![⟨137712, by decide⟩,⟨137758, by decide⟩,⟨137788, by decide⟩,⟨137816, by decide⟩]) unmarked_context_13_73749_137817 node_context_13_73749_137817
  intro a
  fin_cases a
  · exact context_14_294996_137712
  · exact context_14_294997_137758
  · exact context_14_294998_137788
  · exact context_14_294999_137816

theorem selected_cut_04333 : selected 8 ⟨137897, by decide⟩
    (prefixPartial 13 73750) = some ⟨13, 2, 0, 137897, 73750, 3381, 16384⟩ := by
  decide +kernel

theorem context_13_73750_137897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73750 ⟨137897, by decide⟩ :=
  accepted_of_selected 13 73750 ⟨137897, by decide⟩ ⟨13, 2, 0, 137897, 73750, 3381, 16384⟩
    (by decide) selected_cut_04333

theorem selected_cut_04334 : selected 8 ⟨137925, by decide⟩
    (prefixPartial 13 73751) = some ⟨13, 2, 0, 137925, 73751, 1605, 16384⟩ := by
  decide +kernel

theorem context_13_73751_137925 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73751 ⟨137925, by decide⟩ :=
  accepted_of_selected 13 73751 ⟨137925, by decide⟩ ⟨13, 2, 0, 137925, 73751, 1605, 16384⟩
    (by decide) selected_cut_04334

theorem unmarked_context_12_18437_137926 : frontier 9 ⟨137926, by decide⟩
    (prefixCache 12 18437) (prefixPartial 12 18437) = false := by
  decide +kernel

theorem node_context_12_18437_137926 : EJMOriginalGlobalDAGData.nodes 9 ⟨137926, by decide⟩ =
    .split (coordinate 12) (![⟨137688, by decide⟩,⟨137817, by decide⟩,⟨137897, by decide⟩,⟨137925, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18437_137926 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18437 ⟨137926, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18437
    ⟨137926, by decide⟩ (by decide) (![⟨137688, by decide⟩,⟨137817, by decide⟩,⟨137897, by decide⟩,⟨137925, by decide⟩]) unmarked_context_12_18437_137926 node_context_12_18437_137926
  intro a
  fin_cases a
  · exact context_13_73748_137688
  · exact context_13_73749_137817
  · exact context_13_73750_137897
  · exact context_13_73751_137925

theorem selected_cut_04335 : selected 7 ⟨137956, by decide⟩
    (prefixPartial 14 295008) = some ⟨14, 2, 0, 137956, 295008, 753, 4096⟩ := by
  decide +kernel

theorem context_14_295008_137956 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 295008 ⟨137956, by decide⟩ :=
  accepted_of_selected 14 295008 ⟨137956, by decide⟩ ⟨14, 2, 0, 137956, 295008, 753, 4096⟩
    (by decide) selected_cut_04335

theorem selected_cut_04336 : selected 7 ⟨137997, by decide⟩
    (prefixPartial 14 295009) = some ⟨14, 2, 0, 137997, 295009, 1741, 4096⟩ := by
  decide +kernel

theorem context_14_295009_137997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 295009 ⟨137997, by decide⟩ :=
  accepted_of_selected 14 295009 ⟨137997, by decide⟩ ⟨14, 2, 0, 137997, 295009, 1741, 4096⟩
    (by decide) selected_cut_04336

theorem selected_cut_04337 : selected 7 ⟨138043, by decide⟩
    (prefixPartial 14 295010) = some ⟨14, 2, 0, 138043, 295010, 1681, 4096⟩ := by
  decide +kernel

theorem context_14_295010_138043 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 295010 ⟨138043, by decide⟩ :=
  accepted_of_selected 14 295010 ⟨138043, by decide⟩ ⟨14, 2, 0, 138043, 295010, 1681, 4096⟩
    (by decide) selected_cut_04337

theorem selected_cut_04338 : selected 7 ⟨138084, by decide⟩
    (prefixPartial 14 295011) = some ⟨14, 2, 0, 138084, 295011, 1425, 4096⟩ := by
  decide +kernel

theorem context_14_295011_138084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 295011 ⟨138084, by decide⟩ :=
  accepted_of_selected 14 295011 ⟨138084, by decide⟩ ⟨14, 2, 0, 138084, 295011, 1425, 4096⟩
    (by decide) selected_cut_04338

theorem unmarked_context_13_73752_138085 : frontier 8 ⟨138085, by decide⟩
    (prefixCache 13 73752) (prefixPartial 13 73752) = false := by
  decide +kernel

theorem node_context_13_73752_138085 : EJMOriginalGlobalDAGData.nodes 8 ⟨138085, by decide⟩ =
    .split (coordinate 13) (![⟨137956, by decide⟩,⟨137997, by decide⟩,⟨138043, by decide⟩,⟨138084, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_73752_138085 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73752 ⟨138085, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 73752
    ⟨138085, by decide⟩ (by decide) (![⟨137956, by decide⟩,⟨137997, by decide⟩,⟨138043, by decide⟩,⟨138084, by decide⟩]) unmarked_context_13_73752_138085 node_context_13_73752_138085
  intro a
  fin_cases a
  · exact context_14_295008_137956
  · exact context_14_295009_137997
  · exact context_14_295010_138043
  · exact context_14_295011_138084

theorem selected_cut_04339 : selected 8 ⟨138219, by decide⟩
    (prefixPartial 13 73753) = some ⟨13, 2, 0, 138219, 73753, 3505, 16384⟩ := by
  decide +kernel

theorem context_13_73753_138219 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73753 ⟨138219, by decide⟩ :=
  accepted_of_selected 13 73753 ⟨138219, by decide⟩ ⟨13, 2, 0, 138219, 73753, 3505, 16384⟩
    (by decide) selected_cut_04339

theorem selected_cut_04340 : selected 8 ⟨138275, by decide⟩
    (prefixPartial 13 73754) = some ⟨13, 2, 0, 138275, 73754, 1045, 16384⟩ := by
  decide +kernel

theorem context_13_73754_138275 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73754 ⟨138275, by decide⟩ :=
  accepted_of_selected 13 73754 ⟨138275, by decide⟩ ⟨13, 2, 0, 138275, 73754, 1045, 16384⟩
    (by decide) selected_cut_04340

theorem selected_cut_04341 : selected 8 ⟨138283, by decide⟩
    (prefixPartial 13 73755) = some ⟨13, 2, 0, 138283, 73755, 161, 16384⟩ := by
  decide +kernel

theorem context_13_73755_138283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73755 ⟨138283, by decide⟩ :=
  accepted_of_selected 13 73755 ⟨138283, by decide⟩ ⟨13, 2, 0, 138283, 73755, 161, 16384⟩
    (by decide) selected_cut_04341

theorem unmarked_context_12_18438_138284 : frontier 9 ⟨138284, by decide⟩
    (prefixCache 12 18438) (prefixPartial 12 18438) = false := by
  decide +kernel

theorem node_context_12_18438_138284 : EJMOriginalGlobalDAGData.nodes 9 ⟨138284, by decide⟩ =
    .split (coordinate 12) (![⟨138085, by decide⟩,⟨138219, by decide⟩,⟨138275, by decide⟩,⟨138283, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18438_138284 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18438 ⟨138284, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18438
    ⟨138284, by decide⟩ (by decide) (![⟨138085, by decide⟩,⟨138219, by decide⟩,⟨138275, by decide⟩,⟨138283, by decide⟩]) unmarked_context_12_18438_138284 node_context_12_18438_138284
  intro a
  fin_cases a
  · exact context_13_73752_138085
  · exact context_13_73753_138219
  · exact context_13_73754_138275
  · exact context_13_73755_138283

theorem selected_cut_04342 : selected 7 ⟨138316, by decide⟩
    (prefixPartial 14 295024) = some ⟨14, 2, 0, 138316, 295024, 1085, 4096⟩ := by
  decide +kernel

theorem context_14_295024_138316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 295024 ⟨138316, by decide⟩ :=
  accepted_of_selected 14 295024 ⟨138316, by decide⟩ ⟨14, 2, 0, 138316, 295024, 1085, 4096⟩
    (by decide) selected_cut_04342

theorem selected_cut_04343 : selected 7 ⟨138359, by decide⟩
    (prefixPartial 14 295025) = some ⟨14, 2, 0, 138359, 295025, 1949, 4096⟩ := by
  decide +kernel

theorem context_14_295025_138359 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 295025 ⟨138359, by decide⟩ :=
  accepted_of_selected 14 295025 ⟨138359, by decide⟩ ⟨14, 2, 0, 138359, 295025, 1949, 4096⟩
    (by decide) selected_cut_04343

theorem selected_cut_04344 : selected 7 ⟨138404, by decide⟩
    (prefixPartial 14 295026) = some ⟨14, 2, 0, 138404, 295026, 2081, 4096⟩ := by
  decide +kernel

theorem context_14_295026_138404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 295026 ⟨138404, by decide⟩ :=
  accepted_of_selected 14 295026 ⟨138404, by decide⟩ ⟨14, 2, 0, 138404, 295026, 2081, 4096⟩
    (by decide) selected_cut_04344

theorem selected_cut_04345 : selected 7 ⟨138440, by decide⟩
    (prefixPartial 14 295027) = some ⟨14, 2, 0, 138440, 295027, 1605, 4096⟩ := by
  decide +kernel

theorem context_14_295027_138440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 295027 ⟨138440, by decide⟩ :=
  accepted_of_selected 14 295027 ⟨138440, by decide⟩ ⟨14, 2, 0, 138440, 295027, 1605, 4096⟩
    (by decide) selected_cut_04345

theorem unmarked_context_13_73756_138441 : frontier 8 ⟨138441, by decide⟩
    (prefixCache 13 73756) (prefixPartial 13 73756) = false := by
  decide +kernel

theorem node_context_13_73756_138441 : EJMOriginalGlobalDAGData.nodes 8 ⟨138441, by decide⟩ =
    .split (coordinate 13) (![⟨138316, by decide⟩,⟨138359, by decide⟩,⟨138404, by decide⟩,⟨138440, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_73756_138441 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73756 ⟨138441, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 73756
    ⟨138441, by decide⟩ (by decide) (![⟨138316, by decide⟩,⟨138359, by decide⟩,⟨138404, by decide⟩,⟨138440, by decide⟩]) unmarked_context_13_73756_138441 node_context_13_73756_138441
  intro a
  fin_cases a
  · exact context_14_295024_138316
  · exact context_14_295025_138359
  · exact context_14_295026_138404
  · exact context_14_295027_138440

theorem selected_cut_04346 : selected 7 ⟨138478, by decide⟩
    (prefixPartial 14 295028) = some ⟨14, 2, 0, 138478, 295028, 1669, 4096⟩ := by
  decide +kernel

theorem context_14_295028_138478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 295028 ⟨138478, by decide⟩ :=
  accepted_of_selected 14 295028 ⟨138478, by decide⟩ ⟨14, 2, 0, 138478, 295028, 1669, 4096⟩
    (by decide) selected_cut_04346

theorem selected_cut_04347 : selected 7 ⟨138533, by decide⟩
    (prefixPartial 14 295029) = some ⟨14, 2, 0, 138533, 295029, 1873, 4096⟩ := by
  decide +kernel

theorem context_14_295029_138533 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 295029 ⟨138533, by decide⟩ :=
  accepted_of_selected 14 295029 ⟨138533, by decide⟩ ⟨14, 2, 0, 138533, 295029, 1873, 4096⟩
    (by decide) selected_cut_04347

theorem selected_cut_04348 : selected 7 ⟨138583, by decide⟩
    (prefixPartial 14 295030) = some ⟨14, 2, 0, 138583, 295030, 1905, 4096⟩ := by
  decide +kernel

theorem context_14_295030_138583 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 295030 ⟨138583, by decide⟩ :=
  accepted_of_selected 14 295030 ⟨138583, by decide⟩ ⟨14, 2, 0, 138583, 295030, 1905, 4096⟩
    (by decide) selected_cut_04348

theorem selected_cut_04349 : selected 7 ⟨138619, by decide⟩
    (prefixPartial 14 295031) = some ⟨14, 2, 0, 138619, 295031, 1405, 4096⟩ := by
  decide +kernel

theorem context_14_295031_138619 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 295031 ⟨138619, by decide⟩ :=
  accepted_of_selected 14 295031 ⟨138619, by decide⟩ ⟨14, 2, 0, 138619, 295031, 1405, 4096⟩
    (by decide) selected_cut_04349

theorem unmarked_context_13_73757_138620 : frontier 8 ⟨138620, by decide⟩
    (prefixCache 13 73757) (prefixPartial 13 73757) = false := by
  decide +kernel

theorem node_context_13_73757_138620 : EJMOriginalGlobalDAGData.nodes 8 ⟨138620, by decide⟩ =
    .split (coordinate 13) (![⟨138478, by decide⟩,⟨138533, by decide⟩,⟨138583, by decide⟩,⟨138619, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_73757_138620 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73757 ⟨138620, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 73757
    ⟨138620, by decide⟩ (by decide) (![⟨138478, by decide⟩,⟨138533, by decide⟩,⟨138583, by decide⟩,⟨138619, by decide⟩]) unmarked_context_13_73757_138620 node_context_13_73757_138620
  intro a
  fin_cases a
  · exact context_14_295028_138478
  · exact context_14_295029_138533
  · exact context_14_295030_138583
  · exact context_14_295031_138619

theorem selected_cut_04350 : selected 8 ⟨138732, by decide⟩
    (prefixPartial 13 73758) = some ⟨13, 2, 0, 138732, 73758, 3289, 16384⟩ := by
  decide +kernel

theorem context_13_73758_138732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73758 ⟨138732, by decide⟩ :=
  accepted_of_selected 13 73758 ⟨138732, by decide⟩ ⟨13, 2, 0, 138732, 73758, 3289, 16384⟩
    (by decide) selected_cut_04350

theorem selected_cut_04351 : selected 8 ⟨138762, by decide⟩
    (prefixPartial 13 73759) = some ⟨13, 2, 0, 138762, 73759, 1541, 16384⟩ := by
  decide +kernel

theorem context_13_73759_138762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73759 ⟨138762, by decide⟩ :=
  accepted_of_selected 13 73759 ⟨138762, by decide⟩ ⟨13, 2, 0, 138762, 73759, 1541, 16384⟩
    (by decide) selected_cut_04351

theorem unmarked_context_12_18439_138763 : frontier 9 ⟨138763, by decide⟩
    (prefixCache 12 18439) (prefixPartial 12 18439) = false := by
  decide +kernel

theorem node_context_12_18439_138763 : EJMOriginalGlobalDAGData.nodes 9 ⟨138763, by decide⟩ =
    .split (coordinate 12) (![⟨138441, by decide⟩,⟨138620, by decide⟩,⟨138732, by decide⟩,⟨138762, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18439_138763 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18439 ⟨138763, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18439
    ⟨138763, by decide⟩ (by decide) (![⟨138441, by decide⟩,⟨138620, by decide⟩,⟨138732, by decide⟩,⟨138762, by decide⟩]) unmarked_context_12_18439_138763 node_context_12_18439_138763
  intro a
  fin_cases a
  · exact context_13_73756_138441
  · exact context_13_73757_138620
  · exact context_13_73758_138732
  · exact context_13_73759_138762

theorem unmarked_context_11_4609_138764 : frontier 10 ⟨138764, by decide⟩
    (prefixCache 11 4609) (prefixPartial 11 4609) = false := by
  decide +kernel

theorem node_context_11_4609_138764 : EJMOriginalGlobalDAGData.nodes 10 ⟨138764, by decide⟩ =
    .split (coordinate 11) (![⟨4595, by decide⟩,⟨137926, by decide⟩,⟨138284, by decide⟩,⟨138763, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4609_138764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4609 ⟨138764, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4609
    ⟨138764, by decide⟩ (by decide) (![⟨4595, by decide⟩,⟨137926, by decide⟩,⟨138284, by decide⟩,⟨138763, by decide⟩]) unmarked_context_11_4609_138764 node_context_11_4609_138764
  intro a
  fin_cases a
  · exact context_12_18436_4595
  · exact context_12_18437_137926
  · exact context_12_18438_138284
  · exact context_12_18439_138763

theorem selected_cut_04352 : selected 9 ⟨4595, by decide⟩
    (prefixPartial 12 18440) = some ⟨12, 1, 0, 4595, 18440, 1, 65536⟩ := by
  decide +kernel

theorem context_12_18440_4595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18440 ⟨4595, by decide⟩ :=
  accepted_of_selected 12 18440 ⟨4595, by decide⟩ ⟨12, 1, 0, 4595, 18440, 1, 65536⟩
    (by decide) selected_cut_04352

theorem selected_cut_04353 : selected 7 ⟨138781, by decide⟩
    (prefixPartial 14 295056) = some ⟨14, 2, 0, 138781, 295056, 501, 4096⟩ := by
  decide +kernel

theorem context_14_295056_138781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 295056 ⟨138781, by decide⟩ :=
  accepted_of_selected 14 295056 ⟨138781, by decide⟩ ⟨14, 2, 0, 138781, 295056, 501, 4096⟩
    (by decide) selected_cut_04353

theorem selected_cut_04354 : selected 7 ⟨138824, by decide⟩
    (prefixPartial 14 295057) = some ⟨14, 2, 0, 138824, 295057, 1845, 4096⟩ := by
  decide +kernel

theorem context_14_295057_138824 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 295057 ⟨138824, by decide⟩ :=
  accepted_of_selected 14 295057 ⟨138824, by decide⟩ ⟨14, 2, 0, 138824, 295057, 1845, 4096⟩
    (by decide) selected_cut_04354

theorem selected_cut_04355 : selected 7 ⟨138870, by decide⟩
    (prefixPartial 14 295058) = some ⟨14, 2, 0, 138870, 295058, 1693, 4096⟩ := by
  decide +kernel

theorem context_14_295058_138870 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 295058 ⟨138870, by decide⟩ :=
  accepted_of_selected 14 295058 ⟨138870, by decide⟩ ⟨14, 2, 0, 138870, 295058, 1693, 4096⟩
    (by decide) selected_cut_04355

theorem selected_cut_04356 : selected 7 ⟨138914, by decide⟩
    (prefixPartial 14 295059) = some ⟨14, 2, 0, 138914, 295059, 1457, 4096⟩ := by
  decide +kernel

theorem context_14_295059_138914 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 295059 ⟨138914, by decide⟩ :=
  accepted_of_selected 14 295059 ⟨138914, by decide⟩ ⟨14, 2, 0, 138914, 295059, 1457, 4096⟩
    (by decide) selected_cut_04356

theorem unmarked_context_13_73764_138915 : frontier 8 ⟨138915, by decide⟩
    (prefixCache 13 73764) (prefixPartial 13 73764) = false := by
  decide +kernel

theorem node_context_13_73764_138915 : EJMOriginalGlobalDAGData.nodes 8 ⟨138915, by decide⟩ =
    .split (coordinate 13) (![⟨138781, by decide⟩,⟨138824, by decide⟩,⟨138870, by decide⟩,⟨138914, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_73764_138915 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73764 ⟨138915, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 73764
    ⟨138915, by decide⟩ (by decide) (![⟨138781, by decide⟩,⟨138824, by decide⟩,⟨138870, by decide⟩,⟨138914, by decide⟩]) unmarked_context_13_73764_138915 node_context_13_73764_138915
  intro a
  fin_cases a
  · exact context_14_295056_138781
  · exact context_14_295057_138824
  · exact context_14_295058_138870
  · exact context_14_295059_138914

theorem selected_cut_04357 : selected 8 ⟨139035, by decide⟩
    (prefixPartial 13 73765) = some ⟨13, 2, 0, 139035, 73765, 3225, 16384⟩ := by
  decide +kernel

theorem context_13_73765_139035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73765 ⟨139035, by decide⟩ :=
  accepted_of_selected 13 73765 ⟨139035, by decide⟩ ⟨13, 2, 0, 139035, 73765, 3225, 16384⟩
    (by decide) selected_cut_04357

theorem selected_cut_04358 : selected 8 ⟨139076, by decide⟩
    (prefixPartial 13 73766) = some ⟨13, 2, 0, 139076, 73766, 801, 16384⟩ := by
  decide +kernel

theorem context_13_73766_139076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73766 ⟨139076, by decide⟩ :=
  accepted_of_selected 13 73766 ⟨139076, by decide⟩ ⟨13, 2, 0, 139076, 73766, 801, 16384⟩
    (by decide) selected_cut_04358

theorem selected_cut_04359 : selected 8 ⟨139081, by decide⟩
    (prefixPartial 13 73767) = some ⟨13, 2, 0, 139081, 73767, 165, 16384⟩ := by
  decide +kernel

theorem context_13_73767_139081 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73767 ⟨139081, by decide⟩ :=
  accepted_of_selected 13 73767 ⟨139081, by decide⟩ ⟨13, 2, 0, 139081, 73767, 165, 16384⟩
    (by decide) selected_cut_04359

theorem unmarked_context_12_18441_139082 : frontier 9 ⟨139082, by decide⟩
    (prefixCache 12 18441) (prefixPartial 12 18441) = false := by
  decide +kernel

theorem node_context_12_18441_139082 : EJMOriginalGlobalDAGData.nodes 9 ⟨139082, by decide⟩ =
    .split (coordinate 12) (![⟨138915, by decide⟩,⟨139035, by decide⟩,⟨139076, by decide⟩,⟨139081, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18441_139082 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18441 ⟨139082, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18441
    ⟨139082, by decide⟩ (by decide) (![⟨138915, by decide⟩,⟨139035, by decide⟩,⟨139076, by decide⟩,⟨139081, by decide⟩]) unmarked_context_12_18441_139082 node_context_12_18441_139082
  intro a
  fin_cases a
  · exact context_13_73764_138915
  · exact context_13_73765_139035
  · exact context_13_73766_139076
  · exact context_13_73767_139081

theorem selected_cut_04360 : selected 9 ⟨4595, by decide⟩
    (prefixPartial 12 18442) = some ⟨12, 1, 0, 4595, 18442, 1, 65536⟩ := by
  decide +kernel

theorem context_12_18442_4595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18442 ⟨4595, by decide⟩ :=
  accepted_of_selected 12 18442 ⟨4595, by decide⟩ ⟨12, 1, 0, 4595, 18442, 1, 65536⟩
    (by decide) selected_cut_04360

theorem selected_cut_04361 : selected 7 ⟨139099, by decide⟩
    (prefixPartial 14 295088) = some ⟨14, 2, 0, 139099, 295088, 541, 4096⟩ := by
  decide +kernel

theorem context_14_295088_139099 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 295088 ⟨139099, by decide⟩ :=
  accepted_of_selected 14 295088 ⟨139099, by decide⟩ ⟨14, 2, 0, 139099, 295088, 541, 4096⟩
    (by decide) selected_cut_04361

theorem selected_cut_04362 : selected 7 ⟨139142, by decide⟩
    (prefixPartial 14 295089) = some ⟨14, 2, 0, 139142, 295089, 1845, 4096⟩ := by
  decide +kernel

theorem context_14_295089_139142 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 295089 ⟨139142, by decide⟩ :=
  accepted_of_selected 14 295089 ⟨139142, by decide⟩ ⟨14, 2, 0, 139142, 295089, 1845, 4096⟩
    (by decide) selected_cut_04362

theorem selected_cut_04363 : selected 7 ⟨139184, by decide⟩
    (prefixPartial 14 295090) = some ⟨14, 2, 0, 139184, 295090, 1897, 4096⟩ := by
  decide +kernel

theorem context_14_295090_139184 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 295090 ⟨139184, by decide⟩ :=
  accepted_of_selected 14 295090 ⟨139184, by decide⟩ ⟨14, 2, 0, 139184, 295090, 1897, 4096⟩
    (by decide) selected_cut_04363

theorem selected_cut_04364 : selected 7 ⟨139217, by decide⟩
    (prefixPartial 14 295091) = some ⟨14, 2, 0, 139217, 295091, 1581, 4096⟩ := by
  decide +kernel

theorem context_14_295091_139217 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 295091 ⟨139217, by decide⟩ :=
  accepted_of_selected 14 295091 ⟨139217, by decide⟩ ⟨14, 2, 0, 139217, 295091, 1581, 4096⟩
    (by decide) selected_cut_04364

theorem unmarked_context_13_73772_139218 : frontier 8 ⟨139218, by decide⟩
    (prefixCache 13 73772) (prefixPartial 13 73772) = false := by
  decide +kernel

theorem node_context_13_73772_139218 : EJMOriginalGlobalDAGData.nodes 8 ⟨139218, by decide⟩ =
    .split (coordinate 13) (![⟨139099, by decide⟩,⟨139142, by decide⟩,⟨139184, by decide⟩,⟨139217, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_73772_139218 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73772 ⟨139218, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 73772
    ⟨139218, by decide⟩ (by decide) (![⟨139099, by decide⟩,⟨139142, by decide⟩,⟨139184, by decide⟩,⟨139217, by decide⟩]) unmarked_context_13_73772_139218 node_context_13_73772_139218
  intro a
  fin_cases a
  · exact context_14_295088_139099
  · exact context_14_295089_139142
  · exact context_14_295090_139184
  · exact context_14_295091_139217

theorem selected_cut_04365 : selected 7 ⟨139264, by decide⟩
    (prefixPartial 14 295092) = some ⟨14, 2, 0, 139264, 295092, 1809, 4096⟩ := by
  decide +kernel

theorem context_14_295092_139264 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 295092 ⟨139264, by decide⟩ :=
  accepted_of_selected 14 295092 ⟨139264, by decide⟩ ⟨14, 2, 0, 139264, 295092, 1809, 4096⟩
    (by decide) selected_cut_04365

theorem selected_cut_04366 : selected 7 ⟨139321, by decide⟩
    (prefixPartial 14 295093) = some ⟨14, 2, 0, 139321, 295093, 2033, 4096⟩ := by
  decide +kernel

theorem context_14_295093_139321 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 295093 ⟨139321, by decide⟩ :=
  accepted_of_selected 14 295093 ⟨139321, by decide⟩ ⟨14, 2, 0, 139321, 295093, 2033, 4096⟩
    (by decide) selected_cut_04366

theorem selected_cut_04367 : selected 7 ⟨139368, by decide⟩
    (prefixPartial 14 295094) = some ⟨14, 2, 0, 139368, 295094, 1821, 4096⟩ := by
  decide +kernel

theorem context_14_295094_139368 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 295094 ⟨139368, by decide⟩ :=
  accepted_of_selected 14 295094 ⟨139368, by decide⟩ ⟨14, 2, 0, 139368, 295094, 1821, 4096⟩
    (by decide) selected_cut_04367

theorem selected_cut_04368 : selected 7 ⟨139408, by decide⟩
    (prefixPartial 14 295095) = some ⟨14, 2, 0, 139408, 295095, 1537, 4096⟩ := by
  decide +kernel

theorem context_14_295095_139408 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 295095 ⟨139408, by decide⟩ :=
  accepted_of_selected 14 295095 ⟨139408, by decide⟩ ⟨14, 2, 0, 139408, 295095, 1537, 4096⟩
    (by decide) selected_cut_04368

theorem unmarked_context_13_73773_139409 : frontier 8 ⟨139409, by decide⟩
    (prefixCache 13 73773) (prefixPartial 13 73773) = false := by
  decide +kernel

theorem node_context_13_73773_139409 : EJMOriginalGlobalDAGData.nodes 8 ⟨139409, by decide⟩ =
    .split (coordinate 13) (![⟨139264, by decide⟩,⟨139321, by decide⟩,⟨139368, by decide⟩,⟨139408, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_73773_139409 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73773 ⟨139409, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 73773
    ⟨139409, by decide⟩ (by decide) (![⟨139264, by decide⟩,⟨139321, by decide⟩,⟨139368, by decide⟩,⟨139408, by decide⟩]) unmarked_context_13_73773_139409 node_context_13_73773_139409
  intro a
  fin_cases a
  · exact context_14_295092_139264
  · exact context_14_295093_139321
  · exact context_14_295094_139368
  · exact context_14_295095_139408

theorem selected_cut_04369 : selected 8 ⟨139481, by decide⟩
    (prefixPartial 13 73774) = some ⟨13, 2, 0, 139481, 73774, 2701, 16384⟩ := by
  decide +kernel

theorem context_13_73774_139481 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73774 ⟨139481, by decide⟩ :=
  accepted_of_selected 13 73774 ⟨139481, by decide⟩ ⟨13, 2, 0, 139481, 73774, 2701, 16384⟩
    (by decide) selected_cut_04369

theorem selected_cut_04370 : selected 8 ⟨139528, by decide⟩
    (prefixPartial 13 73775) = some ⟨13, 2, 0, 139528, 73775, 1445, 16384⟩ := by
  decide +kernel

theorem context_13_73775_139528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73775 ⟨139528, by decide⟩ :=
  accepted_of_selected 13 73775 ⟨139528, by decide⟩ ⟨13, 2, 0, 139528, 73775, 1445, 16384⟩
    (by decide) selected_cut_04370

theorem unmarked_context_12_18443_139529 : frontier 9 ⟨139529, by decide⟩
    (prefixCache 12 18443) (prefixPartial 12 18443) = false := by
  decide +kernel

theorem node_context_12_18443_139529 : EJMOriginalGlobalDAGData.nodes 9 ⟨139529, by decide⟩ =
    .split (coordinate 12) (![⟨139218, by decide⟩,⟨139409, by decide⟩,⟨139481, by decide⟩,⟨139528, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18443_139529 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18443 ⟨139529, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18443
    ⟨139529, by decide⟩ (by decide) (![⟨139218, by decide⟩,⟨139409, by decide⟩,⟨139481, by decide⟩,⟨139528, by decide⟩]) unmarked_context_12_18443_139529 node_context_12_18443_139529
  intro a
  fin_cases a
  · exact context_13_73772_139218
  · exact context_13_73773_139409
  · exact context_13_73774_139481
  · exact context_13_73775_139528

theorem unmarked_context_11_4610_139530 : frontier 10 ⟨139530, by decide⟩
    (prefixCache 11 4610) (prefixPartial 11 4610) = false := by
  decide +kernel

theorem node_context_11_4610_139530 : EJMOriginalGlobalDAGData.nodes 10 ⟨139530, by decide⟩ =
    .split (coordinate 11) (![⟨4595, by decide⟩,⟨139082, by decide⟩,⟨4595, by decide⟩,⟨139529, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4610_139530 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4610 ⟨139530, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4610
    ⟨139530, by decide⟩ (by decide) (![⟨4595, by decide⟩,⟨139082, by decide⟩,⟨4595, by decide⟩,⟨139529, by decide⟩]) unmarked_context_11_4610_139530 node_context_11_4610_139530
  intro a
  fin_cases a
  · exact context_12_18440_4595
  · exact context_12_18441_139082
  · exact context_12_18442_4595
  · exact context_12_18443_139529

theorem selected_cut_04371 : selected 9 ⟨4595, by decide⟩
    (prefixPartial 12 18444) = some ⟨12, 1, 0, 4595, 18444, 1, 65536⟩ := by
  decide +kernel

theorem context_12_18444_4595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18444 ⟨4595, by decide⟩ :=
  accepted_of_selected 12 18444 ⟨4595, by decide⟩ ⟨12, 1, 0, 4595, 18444, 1, 65536⟩
    (by decide) selected_cut_04371

theorem selected_cut_04372 : selected 9 ⟨4595, by decide⟩
    (prefixPartial 12 18445) = some ⟨12, 1, 0, 4595, 18445, 1, 65536⟩ := by
  decide +kernel

theorem context_12_18445_4595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18445 ⟨4595, by decide⟩ :=
  accepted_of_selected 12 18445 ⟨4595, by decide⟩ ⟨12, 1, 0, 4595, 18445, 1, 65536⟩
    (by decide) selected_cut_04372

theorem selected_cut_04373 : selected 9 ⟨4595, by decide⟩
    (prefixPartial 12 18446) = some ⟨12, 1, 0, 4595, 18446, 1, 65536⟩ := by
  decide +kernel

theorem context_12_18446_4595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18446 ⟨4595, by decide⟩ :=
  accepted_of_selected 12 18446 ⟨4595, by decide⟩ ⟨12, 1, 0, 4595, 18446, 1, 65536⟩
    (by decide) selected_cut_04373

theorem selected_cut_04374 : selected 7 ⟨139536, by decide⟩
    (prefixPartial 14 295152) = some ⟨14, 2, 0, 139536, 295152, 117, 4096⟩ := by
  decide +kernel

theorem context_14_295152_139536 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 295152 ⟨139536, by decide⟩ :=
  accepted_of_selected 14 295152 ⟨139536, by decide⟩ ⟨14, 2, 0, 139536, 295152, 117, 4096⟩
    (by decide) selected_cut_04374

theorem selected_cut_04375 : selected 7 ⟨139579, by decide⟩
    (prefixPartial 14 295153) = some ⟨14, 2, 0, 139579, 295153, 1561, 4096⟩ := by
  decide +kernel

theorem context_14_295153_139579 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 295153 ⟨139579, by decide⟩ :=
  accepted_of_selected 14 295153 ⟨139579, by decide⟩ ⟨14, 2, 0, 139579, 295153, 1561, 4096⟩
    (by decide) selected_cut_04375

theorem selected_cut_04376 : selected 7 ⟨139629, by decide⟩
    (prefixPartial 14 295154) = some ⟨14, 2, 0, 139629, 295154, 1581, 4096⟩ := by
  decide +kernel

theorem context_14_295154_139629 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 295154 ⟨139629, by decide⟩ :=
  accepted_of_selected 14 295154 ⟨139629, by decide⟩ ⟨14, 2, 0, 139629, 295154, 1581, 4096⟩
    (by decide) selected_cut_04376

theorem selected_cut_04377 : selected 7 ⟨139662, by decide⟩
    (prefixPartial 14 295155) = some ⟨14, 2, 0, 139662, 295155, 1173, 4096⟩ := by
  decide +kernel

theorem context_14_295155_139662 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 295155 ⟨139662, by decide⟩ :=
  accepted_of_selected 14 295155 ⟨139662, by decide⟩ ⟨14, 2, 0, 139662, 295155, 1173, 4096⟩
    (by decide) selected_cut_04377

theorem unmarked_context_13_73788_139663 : frontier 8 ⟨139663, by decide⟩
    (prefixCache 13 73788) (prefixPartial 13 73788) = false := by
  decide +kernel

theorem node_context_13_73788_139663 : EJMOriginalGlobalDAGData.nodes 8 ⟨139663, by decide⟩ =
    .split (coordinate 13) (![⟨139536, by decide⟩,⟨139579, by decide⟩,⟨139629, by decide⟩,⟨139662, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_73788_139663 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73788 ⟨139663, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 73788
    ⟨139663, by decide⟩ (by decide) (![⟨139536, by decide⟩,⟨139579, by decide⟩,⟨139629, by decide⟩,⟨139662, by decide⟩]) unmarked_context_13_73788_139663 node_context_13_73788_139663
  intro a
  fin_cases a
  · exact context_14_295152_139536
  · exact context_14_295153_139579
  · exact context_14_295154_139629
  · exact context_14_295155_139662

theorem selected_cut_04378 : selected 8 ⟨139786, by decide⟩
    (prefixPartial 13 73789) = some ⟨13, 2, 0, 139786, 73789, 3157, 16384⟩ := by
  decide +kernel

theorem context_13_73789_139786 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73789 ⟨139786, by decide⟩ :=
  accepted_of_selected 13 73789 ⟨139786, by decide⟩ ⟨13, 2, 0, 139786, 73789, 3157, 16384⟩
    (by decide) selected_cut_04378

theorem selected_cut_04379 : selected 8 ⟨139837, by decide⟩
    (prefixPartial 13 73790) = some ⟨13, 2, 0, 139837, 73790, 765, 16384⟩ := by
  decide +kernel

theorem context_13_73790_139837 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73790 ⟨139837, by decide⟩ :=
  accepted_of_selected 13 73790 ⟨139837, by decide⟩ ⟨13, 2, 0, 139837, 73790, 765, 16384⟩
    (by decide) selected_cut_04379

theorem selected_cut_04380 : selected 8 ⟨139842, by decide⟩
    (prefixPartial 13 73791) = some ⟨13, 2, 0, 139842, 73791, 145, 16384⟩ := by
  decide +kernel

theorem context_13_73791_139842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73791 ⟨139842, by decide⟩ :=
  accepted_of_selected 13 73791 ⟨139842, by decide⟩ ⟨13, 2, 0, 139842, 73791, 145, 16384⟩
    (by decide) selected_cut_04380

theorem unmarked_context_12_18447_139843 : frontier 9 ⟨139843, by decide⟩
    (prefixCache 12 18447) (prefixPartial 12 18447) = false := by
  decide +kernel

theorem node_context_12_18447_139843 : EJMOriginalGlobalDAGData.nodes 9 ⟨139843, by decide⟩ =
    .split (coordinate 12) (![⟨139663, by decide⟩,⟨139786, by decide⟩,⟨139837, by decide⟩,⟨139842, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18447_139843 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18447 ⟨139843, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18447
    ⟨139843, by decide⟩ (by decide) (![⟨139663, by decide⟩,⟨139786, by decide⟩,⟨139837, by decide⟩,⟨139842, by decide⟩]) unmarked_context_12_18447_139843 node_context_12_18447_139843
  intro a
  fin_cases a
  · exact context_13_73788_139663
  · exact context_13_73789_139786
  · exact context_13_73790_139837
  · exact context_13_73791_139842

theorem unmarked_context_11_4611_139844 : frontier 10 ⟨139844, by decide⟩
    (prefixCache 11 4611) (prefixPartial 11 4611) = false := by
  decide +kernel

theorem node_context_11_4611_139844 : EJMOriginalGlobalDAGData.nodes 10 ⟨139844, by decide⟩ =
    .split (coordinate 11) (![⟨4595, by decide⟩,⟨4595, by decide⟩,⟨4595, by decide⟩,⟨139843, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4611_139844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4611 ⟨139844, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4611
    ⟨139844, by decide⟩ (by decide) (![⟨4595, by decide⟩,⟨4595, by decide⟩,⟨4595, by decide⟩,⟨139843, by decide⟩]) unmarked_context_11_4611_139844 node_context_11_4611_139844
  intro a
  fin_cases a
  · exact context_12_18444_4595
  · exact context_12_18445_4595
  · exact context_12_18446_4595
  · exact context_12_18447_139843

theorem unmarked_context_10_1152_139845 : frontier 11 ⟨139845, by decide⟩
    (prefixCache 10 1152) (prefixPartial 10 1152) = false := by
  decide +kernel

theorem node_context_10_1152_139845 : EJMOriginalGlobalDAGData.nodes 11 ⟨139845, by decide⟩ =
    .split (coordinate 10) (![⟨137562, by decide⟩,⟨138764, by decide⟩,⟨139530, by decide⟩,⟨139844, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1152_139845 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1152 ⟨139845, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1152
    ⟨139845, by decide⟩ (by decide) (![⟨137562, by decide⟩,⟨138764, by decide⟩,⟨139530, by decide⟩,⟨139844, by decide⟩]) unmarked_context_10_1152_139845 node_context_10_1152_139845
  intro a
  fin_cases a
  · exact context_11_4608_137562
  · exact context_11_4609_138764
  · exact context_11_4610_139530
  · exact context_11_4611_139844

theorem selected_cut_04381 : selected 9 ⟨118489, by decide⟩
    (prefixPartial 12 18448) = some ⟨12, 1, 0, 118489, 18448, 1, 65536⟩ := by
  decide +kernel

theorem context_12_18448_118489 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18448 ⟨118489, by decide⟩ :=
  accepted_of_selected 12 18448 ⟨118489, by decide⟩ ⟨12, 1, 0, 118489, 18448, 1, 65536⟩
    (by decide) selected_cut_04381

theorem selected_cut_04382 : selected 8 ⟨139894, by decide⟩
    (prefixPartial 13 73796) = some ⟨13, 2, 0, 139894, 73796, 2589, 16384⟩ := by
  decide +kernel

theorem context_13_73796_139894 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73796 ⟨139894, by decide⟩ :=
  accepted_of_selected 13 73796 ⟨139894, by decide⟩ ⟨13, 2, 0, 139894, 73796, 2589, 16384⟩
    (by decide) selected_cut_04382

theorem selected_cut_04383 : selected 8 ⟨139947, by decide⟩
    (prefixPartial 13 73797) = some ⟨13, 2, 0, 139947, 73797, 2349, 16384⟩ := by
  decide +kernel

theorem context_13_73797_139947 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73797 ⟨139947, by decide⟩ :=
  accepted_of_selected 13 73797 ⟨139947, by decide⟩ ⟨13, 2, 0, 139947, 73797, 2349, 16384⟩
    (by decide) selected_cut_04383

theorem selected_cut_04384 : selected 8 ⟨140000, by decide⟩
    (prefixPartial 13 73798) = some ⟨13, 2, 0, 140000, 73798, 1973, 16384⟩ := by
  decide +kernel

theorem context_13_73798_140000 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73798 ⟨140000, by decide⟩ :=
  accepted_of_selected 13 73798 ⟨140000, by decide⟩ ⟨13, 2, 0, 140000, 73798, 1973, 16384⟩
    (by decide) selected_cut_04384

theorem selected_cut_04385 : selected 8 ⟨140013, by decide⟩
    (prefixPartial 13 73799) = some ⟨13, 2, 0, 140013, 73799, 961, 16384⟩ := by
  decide +kernel

theorem context_13_73799_140013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73799 ⟨140013, by decide⟩ :=
  accepted_of_selected 13 73799 ⟨140013, by decide⟩ ⟨13, 2, 0, 140013, 73799, 961, 16384⟩
    (by decide) selected_cut_04385

theorem unmarked_context_12_18449_140014 : frontier 9 ⟨140014, by decide⟩
    (prefixCache 12 18449) (prefixPartial 12 18449) = false := by
  decide +kernel

theorem node_context_12_18449_140014 : EJMOriginalGlobalDAGData.nodes 9 ⟨140014, by decide⟩ =
    .split (coordinate 12) (![⟨139894, by decide⟩,⟨139947, by decide⟩,⟨140000, by decide⟩,⟨140013, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18449_140014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18449 ⟨140014, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18449
    ⟨140014, by decide⟩ (by decide) (![⟨139894, by decide⟩,⟨139947, by decide⟩,⟨140000, by decide⟩,⟨140013, by decide⟩]) unmarked_context_12_18449_140014 node_context_12_18449_140014
  intro a
  fin_cases a
  · exact context_13_73796_139894
  · exact context_13_73797_139947
  · exact context_13_73798_140000
  · exact context_13_73799_140013

theorem selected_cut_04386 : selected 8 ⟨140072, by decide⟩
    (prefixPartial 13 73800) = some ⟨13, 2, 0, 140072, 73800, 2513, 16384⟩ := by
  decide +kernel

theorem context_13_73800_140072 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73800 ⟨140072, by decide⟩ :=
  accepted_of_selected 13 73800 ⟨140072, by decide⟩ ⟨13, 2, 0, 140072, 73800, 2513, 16384⟩
    (by decide) selected_cut_04386

theorem selected_cut_04387 : selected 8 ⟨140172, by decide⟩
    (prefixPartial 13 73801) = some ⟨13, 2, 0, 140172, 73801, 1801, 16384⟩ := by
  decide +kernel

theorem context_13_73801_140172 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73801 ⟨140172, by decide⟩ :=
  accepted_of_selected 13 73801 ⟨140172, by decide⟩ ⟨13, 2, 0, 140172, 73801, 1801, 16384⟩
    (by decide) selected_cut_04387

theorem selected_cut_04388 : selected 8 ⟨140216, by decide⟩
    (prefixPartial 13 73802) = some ⟨13, 2, 0, 140216, 73802, 793, 16384⟩ := by
  decide +kernel

theorem context_13_73802_140216 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73802 ⟨140216, by decide⟩ :=
  accepted_of_selected 13 73802 ⟨140216, by decide⟩ ⟨13, 2, 0, 140216, 73802, 793, 16384⟩
    (by decide) selected_cut_04388

theorem selected_cut_04389 : selected 8 ⟨140243, by decide⟩
    (prefixPartial 13 73803) = some ⟨13, 2, 0, 140243, 73803, 217, 16384⟩ := by
  decide +kernel

theorem context_13_73803_140243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73803 ⟨140243, by decide⟩ :=
  accepted_of_selected 13 73803 ⟨140243, by decide⟩ ⟨13, 2, 0, 140243, 73803, 217, 16384⟩
    (by decide) selected_cut_04389

theorem unmarked_context_12_18450_140244 : frontier 9 ⟨140244, by decide⟩
    (prefixCache 12 18450) (prefixPartial 12 18450) = false := by
  decide +kernel

theorem node_context_12_18450_140244 : EJMOriginalGlobalDAGData.nodes 9 ⟨140244, by decide⟩ =
    .split (coordinate 12) (![⟨140072, by decide⟩,⟨140172, by decide⟩,⟨140216, by decide⟩,⟨140243, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18450_140244 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18450 ⟨140244, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18450
    ⟨140244, by decide⟩ (by decide) (![⟨140072, by decide⟩,⟨140172, by decide⟩,⟨140216, by decide⟩,⟨140243, by decide⟩]) unmarked_context_12_18450_140244 node_context_12_18450_140244
  intro a
  fin_cases a
  · exact context_13_73800_140072
  · exact context_13_73801_140172
  · exact context_13_73802_140216
  · exact context_13_73803_140243

theorem selected_cut_04390 : selected 8 ⟨140301, by decide⟩
    (prefixPartial 13 73804) = some ⟨13, 2, 0, 140301, 73804, 2745, 16384⟩ := by
  decide +kernel

theorem context_13_73804_140301 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73804 ⟨140301, by decide⟩ :=
  accepted_of_selected 13 73804 ⟨140301, by decide⟩ ⟨13, 2, 0, 140301, 73804, 2745, 16384⟩
    (by decide) selected_cut_04390

theorem selected_cut_04391 : selected 8 ⟨140365, by decide⟩
    (prefixPartial 13 73805) = some ⟨13, 2, 0, 140365, 73805, 2821, 16384⟩ := by
  decide +kernel

theorem context_13_73805_140365 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73805 ⟨140365, by decide⟩ :=
  accepted_of_selected 13 73805 ⟨140365, by decide⟩ ⟨13, 2, 0, 140365, 73805, 2821, 16384⟩
    (by decide) selected_cut_04391

theorem selected_cut_04392 : selected 8 ⟨140398, by decide⟩
    (prefixPartial 13 73806) = some ⟨13, 2, 0, 140398, 73806, 1821, 16384⟩ := by
  decide +kernel

theorem context_13_73806_140398 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73806 ⟨140398, by decide⟩ :=
  accepted_of_selected 13 73806 ⟨140398, by decide⟩ ⟨13, 2, 0, 140398, 73806, 1821, 16384⟩
    (by decide) selected_cut_04392

theorem selected_cut_04393 : selected 8 ⟨140415, by decide⟩
    (prefixPartial 13 73807) = some ⟨13, 2, 0, 140415, 73807, 853, 16384⟩ := by
  decide +kernel

theorem context_13_73807_140415 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73807 ⟨140415, by decide⟩ :=
  accepted_of_selected 13 73807 ⟨140415, by decide⟩ ⟨13, 2, 0, 140415, 73807, 853, 16384⟩
    (by decide) selected_cut_04393

theorem unmarked_context_12_18451_140416 : frontier 9 ⟨140416, by decide⟩
    (prefixCache 12 18451) (prefixPartial 12 18451) = false := by
  decide +kernel

theorem node_context_12_18451_140416 : EJMOriginalGlobalDAGData.nodes 9 ⟨140416, by decide⟩ =
    .split (coordinate 12) (![⟨140301, by decide⟩,⟨140365, by decide⟩,⟨140398, by decide⟩,⟨140415, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18451_140416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18451 ⟨140416, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18451
    ⟨140416, by decide⟩ (by decide) (![⟨140301, by decide⟩,⟨140365, by decide⟩,⟨140398, by decide⟩,⟨140415, by decide⟩]) unmarked_context_12_18451_140416 node_context_12_18451_140416
  intro a
  fin_cases a
  · exact context_13_73804_140301
  · exact context_13_73805_140365
  · exact context_13_73806_140398
  · exact context_13_73807_140415

theorem unmarked_context_11_4612_140417 : frontier 10 ⟨140417, by decide⟩
    (prefixCache 11 4612) (prefixPartial 11 4612) = false := by
  decide +kernel

theorem node_context_11_4612_140417 : EJMOriginalGlobalDAGData.nodes 10 ⟨140417, by decide⟩ =
    .split (coordinate 11) (![⟨118489, by decide⟩,⟨140014, by decide⟩,⟨140244, by decide⟩,⟨140416, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4612_140417 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4612 ⟨140417, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4612
    ⟨140417, by decide⟩ (by decide) (![⟨118489, by decide⟩,⟨140014, by decide⟩,⟨140244, by decide⟩,⟨140416, by decide⟩]) unmarked_context_11_4612_140417 node_context_11_4612_140417
  intro a
  fin_cases a
  · exact context_12_18448_118489
  · exact context_12_18449_140014
  · exact context_12_18450_140244
  · exact context_12_18451_140416

theorem selected_cut_04394 : selected 8 ⟨140459, by decide⟩
    (prefixPartial 13 73808) = some ⟨13, 2, 0, 140459, 73808, 1593, 16384⟩ := by
  decide +kernel

theorem context_13_73808_140459 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73808 ⟨140459, by decide⟩ :=
  accepted_of_selected 13 73808 ⟨140459, by decide⟩ ⟨13, 2, 0, 140459, 73808, 1593, 16384⟩
    (by decide) selected_cut_04394

theorem selected_cut_04395 : selected 8 ⟨140545, by decide⟩
    (prefixPartial 13 73809) = some ⟨13, 2, 0, 140545, 73809, 2305, 16384⟩ := by
  decide +kernel

theorem context_13_73809_140545 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73809 ⟨140545, by decide⟩ :=
  accepted_of_selected 13 73809 ⟨140545, by decide⟩ ⟨13, 2, 0, 140545, 73809, 2305, 16384⟩
    (by decide) selected_cut_04395

theorem selected_cut_04396 : selected 8 ⟨140571, by decide⟩
    (prefixPartial 13 73810) = some ⟨13, 2, 0, 140571, 73810, 785, 16384⟩ := by
  decide +kernel

theorem context_13_73810_140571 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73810 ⟨140571, by decide⟩ :=
  accepted_of_selected 13 73810 ⟨140571, by decide⟩ ⟨13, 2, 0, 140571, 73810, 785, 16384⟩
    (by decide) selected_cut_04396

theorem selected_cut_04397 : selected 8 ⟨140590, by decide⟩
    (prefixPartial 13 73811) = some ⟨13, 2, 0, 140590, 73811, 277, 16384⟩ := by
  decide +kernel

theorem context_13_73811_140590 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73811 ⟨140590, by decide⟩ :=
  accepted_of_selected 13 73811 ⟨140590, by decide⟩ ⟨13, 2, 0, 140590, 73811, 277, 16384⟩
    (by decide) selected_cut_04397

theorem unmarked_context_12_18452_140591 : frontier 9 ⟨140591, by decide⟩
    (prefixCache 12 18452) (prefixPartial 12 18452) = false := by
  decide +kernel

theorem node_context_12_18452_140591 : EJMOriginalGlobalDAGData.nodes 9 ⟨140591, by decide⟩ =
    .split (coordinate 12) (![⟨140459, by decide⟩,⟨140545, by decide⟩,⟨140571, by decide⟩,⟨140590, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18452_140591 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18452 ⟨140591, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18452
    ⟨140591, by decide⟩ (by decide) (![⟨140459, by decide⟩,⟨140545, by decide⟩,⟨140571, by decide⟩,⟨140590, by decide⟩]) unmarked_context_12_18452_140591 node_context_12_18452_140591
  intro a
  fin_cases a
  · exact context_13_73808_140459
  · exact context_13_73809_140545
  · exact context_13_73810_140571
  · exact context_13_73811_140590

theorem selected_cut_04398 : selected 8 ⟨140637, by decide⟩
    (prefixPartial 13 73812) = some ⟨13, 2, 0, 140637, 73812, 2137, 16384⟩ := by
  decide +kernel

theorem context_13_73812_140637 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73812 ⟨140637, by decide⟩ :=
  accepted_of_selected 13 73812 ⟨140637, by decide⟩ ⟨13, 2, 0, 140637, 73812, 2137, 16384⟩
    (by decide) selected_cut_04398

theorem selected_cut_04399 : selected 8 ⟨140685, by decide⟩
    (prefixPartial 13 73813) = some ⟨13, 2, 0, 140685, 73813, 2365, 16384⟩ := by
  decide +kernel

theorem context_13_73813_140685 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73813 ⟨140685, by decide⟩ :=
  accepted_of_selected 13 73813 ⟨140685, by decide⟩ ⟨13, 2, 0, 140685, 73813, 2365, 16384⟩
    (by decide) selected_cut_04399

theorem selected_cut_04400 : selected 8 ⟨140716, by decide⟩
    (prefixPartial 13 73814) = some ⟨13, 2, 0, 140716, 73814, 1837, 16384⟩ := by
  decide +kernel

theorem context_13_73814_140716 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73814 ⟨140716, by decide⟩ :=
  accepted_of_selected 13 73814 ⟨140716, by decide⟩ ⟨13, 2, 0, 140716, 73814, 1837, 16384⟩
    (by decide) selected_cut_04400

theorem selected_cut_04401 : selected 8 ⟨140728, by decide⟩
    (prefixPartial 13 73815) = some ⟨13, 2, 0, 140728, 73815, 997, 16384⟩ := by
  decide +kernel

theorem context_13_73815_140728 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73815 ⟨140728, by decide⟩ :=
  accepted_of_selected 13 73815 ⟨140728, by decide⟩ ⟨13, 2, 0, 140728, 73815, 997, 16384⟩
    (by decide) selected_cut_04401

theorem unmarked_context_12_18453_140729 : frontier 9 ⟨140729, by decide⟩
    (prefixCache 12 18453) (prefixPartial 12 18453) = false := by
  decide +kernel

theorem node_context_12_18453_140729 : EJMOriginalGlobalDAGData.nodes 9 ⟨140729, by decide⟩ =
    .split (coordinate 12) (![⟨140637, by decide⟩,⟨140685, by decide⟩,⟨140716, by decide⟩,⟨140728, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18453_140729 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18453 ⟨140729, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18453
    ⟨140729, by decide⟩ (by decide) (![⟨140637, by decide⟩,⟨140685, by decide⟩,⟨140716, by decide⟩,⟨140728, by decide⟩]) unmarked_context_12_18453_140729 node_context_12_18453_140729
  intro a
  fin_cases a
  · exact context_13_73812_140637
  · exact context_13_73813_140685
  · exact context_13_73814_140716
  · exact context_13_73815_140728

theorem selected_cut_04402 : selected 8 ⟨140772, by decide⟩
    (prefixPartial 13 73816) = some ⟨13, 2, 0, 140772, 73816, 2549, 16384⟩ := by
  decide +kernel

theorem context_13_73816_140772 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73816 ⟨140772, by decide⟩ :=
  accepted_of_selected 13 73816 ⟨140772, by decide⟩ ⟨13, 2, 0, 140772, 73816, 2549, 16384⟩
    (by decide) selected_cut_04402

theorem selected_cut_04403 : selected 8 ⟨140832, by decide⟩
    (prefixPartial 13 73817) = some ⟨13, 2, 0, 140832, 73817, 3093, 16384⟩ := by
  decide +kernel

theorem context_13_73817_140832 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73817 ⟨140832, by decide⟩ :=
  accepted_of_selected 13 73817 ⟨140832, by decide⟩ ⟨13, 2, 0, 140832, 73817, 3093, 16384⟩
    (by decide) selected_cut_04403

theorem selected_cut_04404 : selected 8 ⟨140857, by decide⟩
    (prefixPartial 13 73818) = some ⟨13, 2, 0, 140857, 73818, 1809, 16384⟩ := by
  decide +kernel

theorem context_13_73818_140857 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73818 ⟨140857, by decide⟩ :=
  accepted_of_selected 13 73818 ⟨140857, by decide⟩ ⟨13, 2, 0, 140857, 73818, 1809, 16384⟩
    (by decide) selected_cut_04404

theorem selected_cut_04405 : selected 8 ⟨140868, by decide⟩
    (prefixPartial 13 73819) = some ⟨13, 2, 0, 140868, 73819, 1113, 16384⟩ := by
  decide +kernel

theorem context_13_73819_140868 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73819 ⟨140868, by decide⟩ :=
  accepted_of_selected 13 73819 ⟨140868, by decide⟩ ⟨13, 2, 0, 140868, 73819, 1113, 16384⟩
    (by decide) selected_cut_04405

theorem unmarked_context_12_18454_140869 : frontier 9 ⟨140869, by decide⟩
    (prefixCache 12 18454) (prefixPartial 12 18454) = false := by
  decide +kernel

theorem node_context_12_18454_140869 : EJMOriginalGlobalDAGData.nodes 9 ⟨140869, by decide⟩ =
    .split (coordinate 12) (![⟨140772, by decide⟩,⟨140832, by decide⟩,⟨140857, by decide⟩,⟨140868, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18454_140869 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18454 ⟨140869, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18454
    ⟨140869, by decide⟩ (by decide) (![⟨140772, by decide⟩,⟨140832, by decide⟩,⟨140857, by decide⟩,⟨140868, by decide⟩]) unmarked_context_12_18454_140869 node_context_12_18454_140869
  intro a
  fin_cases a
  · exact context_13_73816_140772
  · exact context_13_73817_140832
  · exact context_13_73818_140857
  · exact context_13_73819_140868

theorem selected_cut_04406 : selected 8 ⟨140913, by decide⟩
    (prefixPartial 13 73820) = some ⟨13, 2, 0, 140913, 73820, 2569, 16384⟩ := by
  decide +kernel

theorem context_13_73820_140913 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73820 ⟨140913, by decide⟩ :=
  accepted_of_selected 13 73820 ⟨140913, by decide⟩ ⟨13, 2, 0, 140913, 73820, 2569, 16384⟩
    (by decide) selected_cut_04406

theorem selected_cut_04407 : selected 8 ⟨140985, by decide⟩
    (prefixPartial 13 73821) = some ⟨13, 2, 0, 140985, 73821, 3085, 16384⟩ := by
  decide +kernel

theorem context_13_73821_140985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73821 ⟨140985, by decide⟩ :=
  accepted_of_selected 13 73821 ⟨140985, by decide⟩ ⟨13, 2, 0, 140985, 73821, 3085, 16384⟩
    (by decide) selected_cut_04407

theorem selected_cut_04408 : selected 8 ⟨141015, by decide⟩
    (prefixPartial 13 73822) = some ⟨13, 2, 0, 141015, 73822, 1769, 16384⟩ := by
  decide +kernel

theorem context_13_73822_141015 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73822 ⟨141015, by decide⟩ :=
  accepted_of_selected 13 73822 ⟨141015, by decide⟩ ⟨13, 2, 0, 141015, 73822, 1769, 16384⟩
    (by decide) selected_cut_04408

theorem selected_cut_04409 : selected 8 ⟨141030, by decide⟩
    (prefixPartial 13 73823) = some ⟨13, 2, 0, 141030, 73823, 965, 16384⟩ := by
  decide +kernel

theorem context_13_73823_141030 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73823 ⟨141030, by decide⟩ :=
  accepted_of_selected 13 73823 ⟨141030, by decide⟩ ⟨13, 2, 0, 141030, 73823, 965, 16384⟩
    (by decide) selected_cut_04409

theorem unmarked_context_12_18455_141031 : frontier 9 ⟨141031, by decide⟩
    (prefixCache 12 18455) (prefixPartial 12 18455) = false := by
  decide +kernel

theorem node_context_12_18455_141031 : EJMOriginalGlobalDAGData.nodes 9 ⟨141031, by decide⟩ =
    .split (coordinate 12) (![⟨140913, by decide⟩,⟨140985, by decide⟩,⟨141015, by decide⟩,⟨141030, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18455_141031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18455 ⟨141031, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18455
    ⟨141031, by decide⟩ (by decide) (![⟨140913, by decide⟩,⟨140985, by decide⟩,⟨141015, by decide⟩,⟨141030, by decide⟩]) unmarked_context_12_18455_141031 node_context_12_18455_141031
  intro a
  fin_cases a
  · exact context_13_73820_140913
  · exact context_13_73821_140985
  · exact context_13_73822_141015
  · exact context_13_73823_141030

theorem unmarked_context_11_4613_141032 : frontier 10 ⟨141032, by decide⟩
    (prefixCache 11 4613) (prefixPartial 11 4613) = false := by
  decide +kernel

theorem node_context_11_4613_141032 : EJMOriginalGlobalDAGData.nodes 10 ⟨141032, by decide⟩ =
    .split (coordinate 11) (![⟨140591, by decide⟩,⟨140729, by decide⟩,⟨140869, by decide⟩,⟨141031, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4613_141032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4613 ⟨141032, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4613
    ⟨141032, by decide⟩ (by decide) (![⟨140591, by decide⟩,⟨140729, by decide⟩,⟨140869, by decide⟩,⟨141031, by decide⟩]) unmarked_context_11_4613_141032 node_context_11_4613_141032
  intro a
  fin_cases a
  · exact context_12_18452_140591
  · exact context_12_18453_140729
  · exact context_12_18454_140869
  · exact context_12_18455_141031

theorem selected_cut_04410 : selected 8 ⟨141061, by decide⟩
    (prefixPartial 13 73824) = some ⟨13, 2, 0, 141061, 73824, 1365, 16384⟩ := by
  decide +kernel

theorem context_13_73824_141061 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73824 ⟨141061, by decide⟩ :=
  accepted_of_selected 13 73824 ⟨141061, by decide⟩ ⟨13, 2, 0, 141061, 73824, 1365, 16384⟩
    (by decide) selected_cut_04410

theorem selected_cut_04411 : selected 8 ⟨141130, by decide⟩
    (prefixPartial 13 73825) = some ⟨13, 2, 0, 141130, 73825, 3225, 16384⟩ := by
  decide +kernel

theorem context_13_73825_141130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73825 ⟨141130, by decide⟩ :=
  accepted_of_selected 13 73825 ⟨141130, by decide⟩ ⟨13, 2, 0, 141130, 73825, 3225, 16384⟩
    (by decide) selected_cut_04411

theorem selected_cut_04412 : selected 8 ⟨141151, by decide⟩
    (prefixPartial 13 73826) = some ⟨13, 2, 0, 141151, 73826, 1449, 16384⟩ := by
  decide +kernel

theorem context_13_73826_141151 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73826 ⟨141151, by decide⟩ :=
  accepted_of_selected 13 73826 ⟨141151, by decide⟩ ⟨13, 2, 0, 141151, 73826, 1449, 16384⟩
    (by decide) selected_cut_04412

theorem selected_cut_04413 : selected 8 ⟨141161, by decide⟩
    (prefixPartial 13 73827) = some ⟨13, 2, 0, 141161, 73827, 981, 16384⟩ := by
  decide +kernel

theorem context_13_73827_141161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73827 ⟨141161, by decide⟩ :=
  accepted_of_selected 13 73827 ⟨141161, by decide⟩ ⟨13, 2, 0, 141161, 73827, 981, 16384⟩
    (by decide) selected_cut_04413

theorem unmarked_context_12_18456_141162 : frontier 9 ⟨141162, by decide⟩
    (prefixCache 12 18456) (prefixPartial 12 18456) = false := by
  decide +kernel

theorem node_context_12_18456_141162 : EJMOriginalGlobalDAGData.nodes 9 ⟨141162, by decide⟩ =
    .split (coordinate 12) (![⟨141061, by decide⟩,⟨141130, by decide⟩,⟨141151, by decide⟩,⟨141161, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18456_141162 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18456 ⟨141162, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18456
    ⟨141162, by decide⟩ (by decide) (![⟨141061, by decide⟩,⟨141130, by decide⟩,⟨141151, by decide⟩,⟨141161, by decide⟩]) unmarked_context_12_18456_141162 node_context_12_18456_141162
  intro a
  fin_cases a
  · exact context_13_73824_141061
  · exact context_13_73825_141130
  · exact context_13_73826_141151
  · exact context_13_73827_141161

theorem selected_cut_04414 : selected 8 ⟨141197, by decide⟩
    (prefixPartial 13 73828) = some ⟨13, 2, 0, 141197, 73828, 2113, 16384⟩ := by
  decide +kernel

theorem context_13_73828_141197 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73828 ⟨141197, by decide⟩ :=
  accepted_of_selected 13 73828 ⟨141197, by decide⟩ ⟨13, 2, 0, 141197, 73828, 2113, 16384⟩
    (by decide) selected_cut_04414

theorem selected_cut_04415 : selected 8 ⟨141252, by decide⟩
    (prefixPartial 13 73829) = some ⟨13, 2, 0, 141252, 73829, 2925, 16384⟩ := by
  decide +kernel

theorem context_13_73829_141252 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73829 ⟨141252, by decide⟩ :=
  accepted_of_selected 13 73829 ⟨141252, by decide⟩ ⟨13, 2, 0, 141252, 73829, 2925, 16384⟩
    (by decide) selected_cut_04415

theorem selected_cut_04416 : selected 8 ⟨141272, by decide⟩
    (prefixPartial 13 73830) = some ⟨13, 2, 0, 141272, 73830, 1617, 16384⟩ := by
  decide +kernel

theorem context_13_73830_141272 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73830 ⟨141272, by decide⟩ :=
  accepted_of_selected 13 73830 ⟨141272, by decide⟩ ⟨13, 2, 0, 141272, 73830, 1617, 16384⟩
    (by decide) selected_cut_04416

theorem selected_cut_04417 : selected 8 ⟨141279, by decide⟩
    (prefixPartial 13 73831) = some ⟨13, 2, 0, 141279, 73831, 1069, 16384⟩ := by
  decide +kernel

theorem context_13_73831_141279 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73831 ⟨141279, by decide⟩ :=
  accepted_of_selected 13 73831 ⟨141279, by decide⟩ ⟨13, 2, 0, 141279, 73831, 1069, 16384⟩
    (by decide) selected_cut_04417

theorem unmarked_context_12_18457_141280 : frontier 9 ⟨141280, by decide⟩
    (prefixCache 12 18457) (prefixPartial 12 18457) = false := by
  decide +kernel

theorem node_context_12_18457_141280 : EJMOriginalGlobalDAGData.nodes 9 ⟨141280, by decide⟩ =
    .split (coordinate 12) (![⟨141197, by decide⟩,⟨141252, by decide⟩,⟨141272, by decide⟩,⟨141279, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18457_141280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18457 ⟨141280, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18457
    ⟨141280, by decide⟩ (by decide) (![⟨141197, by decide⟩,⟨141252, by decide⟩,⟨141272, by decide⟩,⟨141279, by decide⟩]) unmarked_context_12_18457_141280 node_context_12_18457_141280
  intro a
  fin_cases a
  · exact context_13_73828_141197
  · exact context_13_73829_141252
  · exact context_13_73830_141272
  · exact context_13_73831_141279

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
