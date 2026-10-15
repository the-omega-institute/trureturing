/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover523
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_50307 : selected 9 ⟨1415033, by decide⟩
    (prefixPartial 12 424464) = some ⟨12, 1, 0, 1415033, 424464, 1, 65536⟩ := by
  decide +kernel

theorem context_12_424464_1415033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424464 ⟨1415033, by decide⟩ :=
  accepted_of_selected 12 424464 ⟨1415033, by decide⟩ ⟨12, 1, 0, 1415033, 424464, 1, 65536⟩
    (by decide) selected_cut_50307

theorem selected_cut_50308 : selected 9 ⟨1435515, by decide⟩
    (prefixPartial 12 424465) = some ⟨12, 2, 0, 1435515, 424465, 2621, 65536⟩ := by
  decide +kernel

theorem context_12_424465_1435515 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424465 ⟨1435515, by decide⟩ :=
  accepted_of_selected 12 424465 ⟨1435515, by decide⟩ ⟨12, 2, 0, 1435515, 424465, 2621, 65536⟩
    (by decide) selected_cut_50308

theorem selected_cut_50309 : selected 9 ⟨1435583, by decide⟩
    (prefixPartial 12 424466) = some ⟨12, 2, 0, 1435583, 424466, 2745, 65536⟩ := by
  decide +kernel

theorem context_12_424466_1435583 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424466 ⟨1435583, by decide⟩ :=
  accepted_of_selected 12 424466 ⟨1435583, by decide⟩ ⟨12, 2, 0, 1435583, 424466, 2745, 65536⟩
    (by decide) selected_cut_50309

theorem selected_cut_50310 : selected 9 ⟨1435648, by decide⟩
    (prefixPartial 12 424467) = some ⟨12, 2, 0, 1435648, 424467, 2985, 65536⟩ := by
  decide +kernel

theorem context_12_424467_1435648 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424467 ⟨1435648, by decide⟩ :=
  accepted_of_selected 12 424467 ⟨1435648, by decide⟩ ⟨12, 2, 0, 1435648, 424467, 2985, 65536⟩
    (by decide) selected_cut_50310

theorem unmarked_context_11_106116_1435649 : frontier 10 ⟨1435649, by decide⟩
    (prefixCache 11 106116) (prefixPartial 11 106116) = false := by
  decide +kernel

theorem node_context_11_106116_1435649 : EJMOriginalGlobalDAGData.nodes 10 ⟨1435649, by decide⟩ =
    .split (coordinate 11) (![⟨1415033, by decide⟩,⟨1435515, by decide⟩,⟨1435583, by decide⟩,⟨1435648, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_106116_1435649 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106116 ⟨1435649, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 106116
    ⟨1435649, by decide⟩ (by decide) (![⟨1415033, by decide⟩,⟨1435515, by decide⟩,⟨1435583, by decide⟩,⟨1435648, by decide⟩]) unmarked_context_11_106116_1435649 node_context_11_106116_1435649
  intro a
  fin_cases a
  · exact context_12_424464_1415033
  · exact context_12_424465_1435515
  · exact context_12_424466_1435583
  · exact context_12_424467_1435648

theorem selected_cut_50311 : selected 10 ⟨1192826, by decide⟩
    (prefixPartial 11 106117) = some ⟨11, 1, 0, 1192826, 106117, 1, 262144⟩ := by
  decide +kernel

theorem context_11_106117_1192826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106117 ⟨1192826, by decide⟩ :=
  accepted_of_selected 11 106117 ⟨1192826, by decide⟩ ⟨11, 1, 0, 1192826, 106117, 1, 262144⟩
    (by decide) selected_cut_50311

theorem selected_cut_50312 : selected 9 ⟨1415033, by decide⟩
    (prefixPartial 12 424472) = some ⟨12, 1, 0, 1415033, 424472, 1, 65536⟩ := by
  decide +kernel

theorem context_12_424472_1415033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424472 ⟨1415033, by decide⟩ :=
  accepted_of_selected 12 424472 ⟨1415033, by decide⟩ ⟨12, 1, 0, 1415033, 424472, 1, 65536⟩
    (by decide) selected_cut_50312

theorem selected_cut_50313 : selected 9 ⟨1435701, by decide⟩
    (prefixPartial 12 424473) = some ⟨12, 2, 0, 1435701, 424473, 2117, 65536⟩ := by
  decide +kernel

theorem context_12_424473_1435701 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424473 ⟨1435701, by decide⟩ :=
  accepted_of_selected 12 424473 ⟨1435701, by decide⟩ ⟨12, 2, 0, 1435701, 424473, 2117, 65536⟩
    (by decide) selected_cut_50313

theorem selected_cut_50314 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 424474) = some ⟨12, 1, 0, 893903, 424474, 1, 65536⟩ := by
  decide +kernel

theorem context_12_424474_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424474 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 424474 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 424474, 1, 65536⟩
    (by decide) selected_cut_50314

theorem selected_cut_50315 : selected 9 ⟨1435758, by decide⟩
    (prefixPartial 12 424475) = some ⟨12, 2, 0, 1435758, 424475, 2317, 65536⟩ := by
  decide +kernel

theorem context_12_424475_1435758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424475 ⟨1435758, by decide⟩ :=
  accepted_of_selected 12 424475 ⟨1435758, by decide⟩ ⟨12, 2, 0, 1435758, 424475, 2317, 65536⟩
    (by decide) selected_cut_50315

theorem unmarked_context_11_106118_1435759 : frontier 10 ⟨1435759, by decide⟩
    (prefixCache 11 106118) (prefixPartial 11 106118) = false := by
  decide +kernel

theorem node_context_11_106118_1435759 : EJMOriginalGlobalDAGData.nodes 10 ⟨1435759, by decide⟩ =
    .split (coordinate 11) (![⟨1415033, by decide⟩,⟨1435701, by decide⟩,⟨893903, by decide⟩,⟨1435758, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_106118_1435759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106118 ⟨1435759, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 106118
    ⟨1435759, by decide⟩ (by decide) (![⟨1415033, by decide⟩,⟨1435701, by decide⟩,⟨893903, by decide⟩,⟨1435758, by decide⟩]) unmarked_context_11_106118_1435759 node_context_11_106118_1435759
  intro a
  fin_cases a
  · exact context_12_424472_1415033
  · exact context_12_424473_1435701
  · exact context_12_424474_893903
  · exact context_12_424475_1435758

theorem selected_cut_50316 : selected 9 ⟨1415033, by decide⟩
    (prefixPartial 12 424476) = some ⟨12, 1, 0, 1415033, 424476, 1, 65536⟩ := by
  decide +kernel

theorem context_12_424476_1415033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424476 ⟨1415033, by decide⟩ :=
  accepted_of_selected 12 424476 ⟨1415033, by decide⟩ ⟨12, 1, 0, 1415033, 424476, 1, 65536⟩
    (by decide) selected_cut_50316

theorem selected_cut_50317 : selected 9 ⟨1435827, by decide⟩
    (prefixPartial 12 424477) = some ⟨12, 2, 0, 1435827, 424477, 2565, 65536⟩ := by
  decide +kernel

theorem context_12_424477_1435827 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424477 ⟨1435827, by decide⟩ :=
  accepted_of_selected 12 424477 ⟨1435827, by decide⟩ ⟨12, 2, 0, 1435827, 424477, 2565, 65536⟩
    (by decide) selected_cut_50317

theorem selected_cut_50318 : selected 9 ⟨1435901, by decide⟩
    (prefixPartial 12 424478) = some ⟨12, 2, 0, 1435901, 424478, 2817, 65536⟩ := by
  decide +kernel

theorem context_12_424478_1435901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424478 ⟨1435901, by decide⟩ :=
  accepted_of_selected 12 424478 ⟨1435901, by decide⟩ ⟨12, 2, 0, 1435901, 424478, 2817, 65536⟩
    (by decide) selected_cut_50318

theorem selected_cut_50319 : selected 9 ⟨1436004, by decide⟩
    (prefixPartial 12 424479) = some ⟨12, 2, 0, 1436004, 424479, 1737, 65536⟩ := by
  decide +kernel

theorem context_12_424479_1436004 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424479 ⟨1436004, by decide⟩ :=
  accepted_of_selected 12 424479 ⟨1436004, by decide⟩ ⟨12, 2, 0, 1436004, 424479, 1737, 65536⟩
    (by decide) selected_cut_50319

theorem unmarked_context_11_106119_1436005 : frontier 10 ⟨1436005, by decide⟩
    (prefixCache 11 106119) (prefixPartial 11 106119) = false := by
  decide +kernel

theorem node_context_11_106119_1436005 : EJMOriginalGlobalDAGData.nodes 10 ⟨1436005, by decide⟩ =
    .split (coordinate 11) (![⟨1415033, by decide⟩,⟨1435827, by decide⟩,⟨1435901, by decide⟩,⟨1436004, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_106119_1436005 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106119 ⟨1436005, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 106119
    ⟨1436005, by decide⟩ (by decide) (![⟨1415033, by decide⟩,⟨1435827, by decide⟩,⟨1435901, by decide⟩,⟨1436004, by decide⟩]) unmarked_context_11_106119_1436005 node_context_11_106119_1436005
  intro a
  fin_cases a
  · exact context_12_424476_1415033
  · exact context_12_424477_1435827
  · exact context_12_424478_1435901
  · exact context_12_424479_1436004

theorem unmarked_context_10_26529_1436006 : frontier 11 ⟨1436006, by decide⟩
    (prefixCache 10 26529) (prefixPartial 10 26529) = false := by
  decide +kernel

theorem node_context_10_26529_1436006 : EJMOriginalGlobalDAGData.nodes 11 ⟨1436006, by decide⟩ =
    .split (coordinate 10) (![⟨1435649, by decide⟩,⟨1192826, by decide⟩,⟨1435759, by decide⟩,⟨1436005, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26529_1436006 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26529 ⟨1436006, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26529
    ⟨1436006, by decide⟩ (by decide) (![⟨1435649, by decide⟩,⟨1192826, by decide⟩,⟨1435759, by decide⟩,⟨1436005, by decide⟩]) unmarked_context_10_26529_1436006 node_context_10_26529_1436006
  intro a
  fin_cases a
  · exact context_11_106116_1435649
  · exact context_11_106117_1192826
  · exact context_11_106118_1435759
  · exact context_11_106119_1436005

theorem selected_cut_50320 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 424480) = some ⟨12, 1, 0, 435160, 424480, 1, 65536⟩ := by
  decide +kernel

theorem context_12_424480_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424480 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 424480 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 424480, 1, 65536⟩
    (by decide) selected_cut_50320

theorem selected_cut_50321 : selected 9 ⟨1436081, by decide⟩
    (prefixPartial 12 424481) = some ⟨12, 2, 0, 1436081, 424481, 2281, 65536⟩ := by
  decide +kernel

theorem context_12_424481_1436081 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424481 ⟨1436081, by decide⟩ :=
  accepted_of_selected 12 424481 ⟨1436081, by decide⟩ ⟨12, 2, 0, 1436081, 424481, 2281, 65536⟩
    (by decide) selected_cut_50321

theorem selected_cut_50322 : selected 9 ⟨1436144, by decide⟩
    (prefixPartial 12 424482) = some ⟨12, 2, 0, 1436144, 424482, 2173, 65536⟩ := by
  decide +kernel

theorem context_12_424482_1436144 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424482 ⟨1436144, by decide⟩ :=
  accepted_of_selected 12 424482 ⟨1436144, by decide⟩ ⟨12, 2, 0, 1436144, 424482, 2173, 65536⟩
    (by decide) selected_cut_50322

theorem selected_cut_50323 : selected 9 ⟨1436205, by decide⟩
    (prefixPartial 12 424483) = some ⟨12, 2, 0, 1436205, 424483, 2301, 65536⟩ := by
  decide +kernel

theorem context_12_424483_1436205 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424483 ⟨1436205, by decide⟩ :=
  accepted_of_selected 12 424483 ⟨1436205, by decide⟩ ⟨12, 2, 0, 1436205, 424483, 2301, 65536⟩
    (by decide) selected_cut_50323

theorem unmarked_context_11_106120_1436206 : frontier 10 ⟨1436206, by decide⟩
    (prefixCache 11 106120) (prefixPartial 11 106120) = false := by
  decide +kernel

theorem node_context_11_106120_1436206 : EJMOriginalGlobalDAGData.nodes 10 ⟨1436206, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨1436081, by decide⟩,⟨1436144, by decide⟩,⟨1436205, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_106120_1436206 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106120 ⟨1436206, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 106120
    ⟨1436206, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨1436081, by decide⟩,⟨1436144, by decide⟩,⟨1436205, by decide⟩]) unmarked_context_11_106120_1436206 node_context_11_106120_1436206
  intro a
  fin_cases a
  · exact context_12_424480_435160
  · exact context_12_424481_1436081
  · exact context_12_424482_1436144
  · exact context_12_424483_1436205

theorem selected_cut_50324 : selected 10 ⟨1436310, by decide⟩
    (prefixPartial 11 106121) = some ⟨11, 2, 0, 1436310, 106121, 3713, 262144⟩ := by
  decide +kernel

theorem context_11_106121_1436310 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106121 ⟨1436310, by decide⟩ :=
  accepted_of_selected 11 106121 ⟨1436310, by decide⟩ ⟨11, 2, 0, 1436310, 106121, 3713, 262144⟩
    (by decide) selected_cut_50324

theorem selected_cut_50325 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 106122) = some ⟨11, 1, 0, 900587, 106122, 1, 262144⟩ := by
  decide +kernel

theorem context_11_106122_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106122 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 106122 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 106122, 1, 262144⟩
    (by decide) selected_cut_50325

theorem selected_cut_50326 : selected 9 ⟨1436371, by decide⟩
    (prefixPartial 12 424492) = some ⟨12, 2, 0, 1436371, 424492, 1573, 65536⟩ := by
  decide +kernel

theorem context_12_424492_1436371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424492 ⟨1436371, by decide⟩ :=
  accepted_of_selected 12 424492 ⟨1436371, by decide⟩ ⟨12, 2, 0, 1436371, 424492, 1573, 65536⟩
    (by decide) selected_cut_50326

theorem selected_cut_50327 : selected 9 ⟨1436427, by decide⟩
    (prefixPartial 12 424493) = some ⟨12, 2, 0, 1436427, 424493, 2109, 65536⟩ := by
  decide +kernel

theorem context_12_424493_1436427 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424493 ⟨1436427, by decide⟩ :=
  accepted_of_selected 12 424493 ⟨1436427, by decide⟩ ⟨12, 2, 0, 1436427, 424493, 2109, 65536⟩
    (by decide) selected_cut_50327

theorem selected_cut_50328 : selected 9 ⟨1436483, by decide⟩
    (prefixPartial 12 424494) = some ⟨12, 2, 0, 1436483, 424494, 2193, 65536⟩ := by
  decide +kernel

theorem context_12_424494_1436483 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424494 ⟨1436483, by decide⟩ :=
  accepted_of_selected 12 424494 ⟨1436483, by decide⟩ ⟨12, 2, 0, 1436483, 424494, 2193, 65536⟩
    (by decide) selected_cut_50328

theorem selected_cut_50329 : selected 9 ⟨1387722, by decide⟩
    (prefixPartial 12 424495) = some ⟨12, 1, 0, 1387722, 424495, 1, 65536⟩ := by
  decide +kernel

theorem context_12_424495_1387722 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424495 ⟨1387722, by decide⟩ :=
  accepted_of_selected 12 424495 ⟨1387722, by decide⟩ ⟨12, 1, 0, 1387722, 424495, 1, 65536⟩
    (by decide) selected_cut_50329

theorem unmarked_context_11_106123_1436484 : frontier 10 ⟨1436484, by decide⟩
    (prefixCache 11 106123) (prefixPartial 11 106123) = false := by
  decide +kernel

theorem node_context_11_106123_1436484 : EJMOriginalGlobalDAGData.nodes 10 ⟨1436484, by decide⟩ =
    .split (coordinate 11) (![⟨1436371, by decide⟩,⟨1436427, by decide⟩,⟨1436483, by decide⟩,⟨1387722, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_106123_1436484 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106123 ⟨1436484, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 106123
    ⟨1436484, by decide⟩ (by decide) (![⟨1436371, by decide⟩,⟨1436427, by decide⟩,⟨1436483, by decide⟩,⟨1387722, by decide⟩]) unmarked_context_11_106123_1436484 node_context_11_106123_1436484
  intro a
  fin_cases a
  · exact context_12_424492_1436371
  · exact context_12_424493_1436427
  · exact context_12_424494_1436483
  · exact context_12_424495_1387722

theorem unmarked_context_10_26530_1436485 : frontier 11 ⟨1436485, by decide⟩
    (prefixCache 10 26530) (prefixPartial 10 26530) = false := by
  decide +kernel

theorem node_context_10_26530_1436485 : EJMOriginalGlobalDAGData.nodes 11 ⟨1436485, by decide⟩ =
    .split (coordinate 10) (![⟨1436206, by decide⟩,⟨1436310, by decide⟩,⟨900587, by decide⟩,⟨1436484, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26530_1436485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26530 ⟨1436485, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26530
    ⟨1436485, by decide⟩ (by decide) (![⟨1436206, by decide⟩,⟨1436310, by decide⟩,⟨900587, by decide⟩,⟨1436484, by decide⟩]) unmarked_context_10_26530_1436485 node_context_10_26530_1436485
  intro a
  fin_cases a
  · exact context_11_106120_1436206
  · exact context_11_106121_1436310
  · exact context_11_106122_900587
  · exact context_11_106123_1436484

theorem selected_cut_50330 : selected 9 ⟨1416143, by decide⟩
    (prefixPartial 12 424496) = some ⟨12, 1, 0, 1416143, 424496, 1, 65536⟩ := by
  decide +kernel

theorem context_12_424496_1416143 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424496 ⟨1416143, by decide⟩ :=
  accepted_of_selected 12 424496 ⟨1416143, by decide⟩ ⟨12, 1, 0, 1416143, 424496, 1, 65536⟩
    (by decide) selected_cut_50330

theorem selected_cut_50331 : selected 9 ⟨1436538, by decide⟩
    (prefixPartial 12 424497) = some ⟨12, 2, 0, 1436538, 424497, 1989, 65536⟩ := by
  decide +kernel

theorem context_12_424497_1436538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424497 ⟨1436538, by decide⟩ :=
  accepted_of_selected 12 424497 ⟨1436538, by decide⟩ ⟨12, 2, 0, 1436538, 424497, 1989, 65536⟩
    (by decide) selected_cut_50331

theorem selected_cut_50332 : selected 9 ⟨1436584, by decide⟩
    (prefixPartial 12 424498) = some ⟨12, 2, 0, 1436584, 424498, 1849, 65536⟩ := by
  decide +kernel

theorem context_12_424498_1436584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424498 ⟨1436584, by decide⟩ :=
  accepted_of_selected 12 424498 ⟨1436584, by decide⟩ ⟨12, 2, 0, 1436584, 424498, 1849, 65536⟩
    (by decide) selected_cut_50332

theorem selected_cut_50333 : selected 9 ⟨1436632, by decide⟩
    (prefixPartial 12 424499) = some ⟨12, 2, 0, 1436632, 424499, 1909, 65536⟩ := by
  decide +kernel

theorem context_12_424499_1436632 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424499 ⟨1436632, by decide⟩ :=
  accepted_of_selected 12 424499 ⟨1436632, by decide⟩ ⟨12, 2, 0, 1436632, 424499, 1909, 65536⟩
    (by decide) selected_cut_50333

theorem unmarked_context_11_106124_1436633 : frontier 10 ⟨1436633, by decide⟩
    (prefixCache 11 106124) (prefixPartial 11 106124) = false := by
  decide +kernel

theorem node_context_11_106124_1436633 : EJMOriginalGlobalDAGData.nodes 10 ⟨1436633, by decide⟩ =
    .split (coordinate 11) (![⟨1416143, by decide⟩,⟨1436538, by decide⟩,⟨1436584, by decide⟩,⟨1436632, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_106124_1436633 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106124 ⟨1436633, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 106124
    ⟨1436633, by decide⟩ (by decide) (![⟨1416143, by decide⟩,⟨1436538, by decide⟩,⟨1436584, by decide⟩,⟨1436632, by decide⟩]) unmarked_context_11_106124_1436633 node_context_11_106124_1436633
  intro a
  fin_cases a
  · exact context_12_424496_1416143
  · exact context_12_424497_1436538
  · exact context_12_424498_1436584
  · exact context_12_424499_1436632

theorem selected_cut_50334 : selected 10 ⟨1436715, by decide⟩
    (prefixPartial 11 106125) = some ⟨11, 2, 0, 1436715, 106125, 3089, 262144⟩ := by
  decide +kernel

theorem context_11_106125_1436715 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106125 ⟨1436715, by decide⟩ :=
  accepted_of_selected 11 106125 ⟨1436715, by decide⟩ ⟨11, 2, 0, 1436715, 106125, 3089, 262144⟩
    (by decide) selected_cut_50334

theorem selected_cut_50335 : selected 9 ⟨1436758, by decide⟩
    (prefixPartial 12 424504) = some ⟨12, 2, 0, 1436758, 424504, 1477, 65536⟩ := by
  decide +kernel

theorem context_12_424504_1436758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424504 ⟨1436758, by decide⟩ :=
  accepted_of_selected 12 424504 ⟨1436758, by decide⟩ ⟨12, 2, 0, 1436758, 424504, 1477, 65536⟩
    (by decide) selected_cut_50335

theorem selected_cut_50336 : selected 9 ⟨1436793, by decide⟩
    (prefixPartial 12 424505) = some ⟨12, 2, 0, 1436793, 424505, 1477, 65536⟩ := by
  decide +kernel

theorem context_12_424505_1436793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424505 ⟨1436793, by decide⟩ :=
  accepted_of_selected 12 424505 ⟨1436793, by decide⟩ ⟨12, 2, 0, 1436793, 424505, 1477, 65536⟩
    (by decide) selected_cut_50336

theorem selected_cut_50337 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 424506) = some ⟨12, 1, 0, 893903, 424506, 1, 65536⟩ := by
  decide +kernel

theorem context_12_424506_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424506 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 424506 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 424506, 1, 65536⟩
    (by decide) selected_cut_50337

theorem selected_cut_50338 : selected 9 ⟨1436821, by decide⟩
    (prefixPartial 12 424507) = some ⟨12, 2, 0, 1436821, 424507, 1377, 65536⟩ := by
  decide +kernel

theorem context_12_424507_1436821 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424507 ⟨1436821, by decide⟩ :=
  accepted_of_selected 12 424507 ⟨1436821, by decide⟩ ⟨12, 2, 0, 1436821, 424507, 1377, 65536⟩
    (by decide) selected_cut_50338

theorem unmarked_context_11_106126_1436822 : frontier 10 ⟨1436822, by decide⟩
    (prefixCache 11 106126) (prefixPartial 11 106126) = false := by
  decide +kernel

theorem node_context_11_106126_1436822 : EJMOriginalGlobalDAGData.nodes 10 ⟨1436822, by decide⟩ =
    .split (coordinate 11) (![⟨1436758, by decide⟩,⟨1436793, by decide⟩,⟨893903, by decide⟩,⟨1436821, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_106126_1436822 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106126 ⟨1436822, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 106126
    ⟨1436822, by decide⟩ (by decide) (![⟨1436758, by decide⟩,⟨1436793, by decide⟩,⟨893903, by decide⟩,⟨1436821, by decide⟩]) unmarked_context_11_106126_1436822 node_context_11_106126_1436822
  intro a
  fin_cases a
  · exact context_12_424504_1436758
  · exact context_12_424505_1436793
  · exact context_12_424506_893903
  · exact context_12_424507_1436821

theorem selected_cut_50339 : selected 10 ⟨1436887, by decide⟩
    (prefixPartial 11 106127) = some ⟨11, 2, 0, 1436887, 106127, 733, 262144⟩ := by
  decide +kernel

theorem context_11_106127_1436887 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106127 ⟨1436887, by decide⟩ :=
  accepted_of_selected 11 106127 ⟨1436887, by decide⟩ ⟨11, 2, 0, 1436887, 106127, 733, 262144⟩
    (by decide) selected_cut_50339

theorem unmarked_context_10_26531_1436888 : frontier 11 ⟨1436888, by decide⟩
    (prefixCache 10 26531) (prefixPartial 10 26531) = false := by
  decide +kernel

theorem node_context_10_26531_1436888 : EJMOriginalGlobalDAGData.nodes 11 ⟨1436888, by decide⟩ =
    .split (coordinate 10) (![⟨1436633, by decide⟩,⟨1436715, by decide⟩,⟨1436822, by decide⟩,⟨1436887, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26531_1436888 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26531 ⟨1436888, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26531
    ⟨1436888, by decide⟩ (by decide) (![⟨1436633, by decide⟩,⟨1436715, by decide⟩,⟨1436822, by decide⟩,⟨1436887, by decide⟩]) unmarked_context_10_26531_1436888 node_context_10_26531_1436888
  intro a
  fin_cases a
  · exact context_11_106124_1436633
  · exact context_11_106125_1436715
  · exact context_11_106126_1436822
  · exact context_11_106127_1436887

theorem unmarked_context_9_6632_1436889 : frontier 12 ⟨1436889, by decide⟩
    (prefixCache 9 6632) (prefixPartial 9 6632) = false := by
  decide +kernel

theorem node_context_9_6632_1436889 : EJMOriginalGlobalDAGData.nodes 12 ⟨1436889, by decide⟩ =
    .split (coordinate 9) (![⟨1435442, by decide⟩,⟨1436006, by decide⟩,⟨1436485, by decide⟩,⟨1436888, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6632_1436889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6632 ⟨1436889, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6632
    ⟨1436889, by decide⟩ (by decide) (![⟨1435442, by decide⟩,⟨1436006, by decide⟩,⟨1436485, by decide⟩,⟨1436888, by decide⟩]) unmarked_context_9_6632_1436889 node_context_9_6632_1436889
  intro a
  fin_cases a
  · exact context_10_26528_1435442
  · exact context_10_26529_1436006
  · exact context_10_26530_1436485
  · exact context_10_26531_1436888

theorem selected_cut_50340 : selected 10 ⟨1436930, by decide⟩
    (prefixPartial 11 106128) = some ⟨11, 2, 0, 1436930, 106128, 1613, 262144⟩ := by
  decide +kernel

theorem context_11_106128_1436930 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106128 ⟨1436930, by decide⟩ :=
  accepted_of_selected 11 106128 ⟨1436930, by decide⟩ ⟨11, 2, 0, 1436930, 106128, 1613, 262144⟩
    (by decide) selected_cut_50340

theorem selected_cut_50341 : selected 10 ⟨1437030, by decide⟩
    (prefixPartial 11 106129) = some ⟨11, 2, 0, 1437030, 106129, 3845, 262144⟩ := by
  decide +kernel

theorem context_11_106129_1437030 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106129 ⟨1437030, by decide⟩ :=
  accepted_of_selected 11 106129 ⟨1437030, by decide⟩ ⟨11, 2, 0, 1437030, 106129, 3845, 262144⟩
    (by decide) selected_cut_50341

theorem selected_cut_50342 : selected 10 ⟨1437095, by decide⟩
    (prefixPartial 11 106130) = some ⟨11, 2, 0, 1437095, 106130, 2445, 262144⟩ := by
  decide +kernel

theorem context_11_106130_1437095 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106130 ⟨1437095, by decide⟩ :=
  accepted_of_selected 11 106130 ⟨1437095, by decide⟩ ⟨11, 2, 0, 1437095, 106130, 2445, 262144⟩
    (by decide) selected_cut_50342

theorem selected_cut_50343 : selected 9 ⟨1437131, by decide⟩
    (prefixPartial 12 424524) = some ⟨12, 2, 0, 1437131, 424524, 1497, 65536⟩ := by
  decide +kernel

theorem context_12_424524_1437131 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424524 ⟨1437131, by decide⟩ :=
  accepted_of_selected 12 424524 ⟨1437131, by decide⟩ ⟨12, 2, 0, 1437131, 424524, 1497, 65536⟩
    (by decide) selected_cut_50343

theorem selected_cut_50344 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 424525) = some ⟨12, 1, 0, 896706, 424525, 1, 65536⟩ := by
  decide +kernel

theorem context_12_424525_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424525 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 424525 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 424525, 1, 65536⟩
    (by decide) selected_cut_50344

theorem selected_cut_50345 : selected 9 ⟨1437162, by decide⟩
    (prefixPartial 12 424526) = some ⟨12, 2, 0, 1437162, 424526, 1353, 65536⟩ := by
  decide +kernel

theorem context_12_424526_1437162 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424526 ⟨1437162, by decide⟩ :=
  accepted_of_selected 12 424526 ⟨1437162, by decide⟩ ⟨12, 2, 0, 1437162, 424526, 1353, 65536⟩
    (by decide) selected_cut_50345

theorem selected_cut_50346 : selected 9 ⟨1437191, by decide⟩
    (prefixPartial 12 424527) = some ⟨12, 2, 0, 1437191, 424527, 1261, 65536⟩ := by
  decide +kernel

theorem context_12_424527_1437191 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424527 ⟨1437191, by decide⟩ :=
  accepted_of_selected 12 424527 ⟨1437191, by decide⟩ ⟨12, 2, 0, 1437191, 424527, 1261, 65536⟩
    (by decide) selected_cut_50346

theorem unmarked_context_11_106131_1437192 : frontier 10 ⟨1437192, by decide⟩
    (prefixCache 11 106131) (prefixPartial 11 106131) = false := by
  decide +kernel

theorem node_context_11_106131_1437192 : EJMOriginalGlobalDAGData.nodes 10 ⟨1437192, by decide⟩ =
    .split (coordinate 11) (![⟨1437131, by decide⟩,⟨896706, by decide⟩,⟨1437162, by decide⟩,⟨1437191, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_106131_1437192 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106131 ⟨1437192, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 106131
    ⟨1437192, by decide⟩ (by decide) (![⟨1437131, by decide⟩,⟨896706, by decide⟩,⟨1437162, by decide⟩,⟨1437191, by decide⟩]) unmarked_context_11_106131_1437192 node_context_11_106131_1437192
  intro a
  fin_cases a
  · exact context_12_424524_1437131
  · exact context_12_424525_896706
  · exact context_12_424526_1437162
  · exact context_12_424527_1437191

theorem unmarked_context_10_26532_1437193 : frontier 11 ⟨1437193, by decide⟩
    (prefixCache 10 26532) (prefixPartial 10 26532) = false := by
  decide +kernel

theorem node_context_10_26532_1437193 : EJMOriginalGlobalDAGData.nodes 11 ⟨1437193, by decide⟩ =
    .split (coordinate 10) (![⟨1436930, by decide⟩,⟨1437030, by decide⟩,⟨1437095, by decide⟩,⟨1437192, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26532_1437193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26532 ⟨1437193, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26532
    ⟨1437193, by decide⟩ (by decide) (![⟨1436930, by decide⟩,⟨1437030, by decide⟩,⟨1437095, by decide⟩,⟨1437192, by decide⟩]) unmarked_context_10_26532_1437193 node_context_10_26532_1437193
  intro a
  fin_cases a
  · exact context_11_106128_1436930
  · exact context_11_106129_1437030
  · exact context_11_106130_1437095
  · exact context_11_106131_1437192

theorem selected_cut_50347 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 26533) = some ⟨10, 1, 0, 893098, 26533, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_26533_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26533 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 26533 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 26533, 1, 1048576⟩
    (by decide) selected_cut_50347

theorem selected_cut_50348 : selected 10 ⟨1437238, by decide⟩
    (prefixPartial 11 106136) = some ⟨11, 2, 0, 1437238, 106136, 2193, 262144⟩ := by
  decide +kernel

theorem context_11_106136_1437238 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106136 ⟨1437238, by decide⟩ :=
  accepted_of_selected 11 106136 ⟨1437238, by decide⟩ ⟨11, 2, 0, 1437238, 106136, 2193, 262144⟩
    (by decide) selected_cut_50348

theorem selected_cut_50349 : selected 10 ⟨1437310, by decide⟩
    (prefixPartial 11 106137) = some ⟨11, 2, 0, 1437310, 106137, 2845, 262144⟩ := by
  decide +kernel

theorem context_11_106137_1437310 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106137 ⟨1437310, by decide⟩ :=
  accepted_of_selected 11 106137 ⟨1437310, by decide⟩ ⟨11, 2, 0, 1437310, 106137, 2845, 262144⟩
    (by decide) selected_cut_50349

theorem selected_cut_50350 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 106138) = some ⟨11, 1, 0, 900587, 106138, 1, 262144⟩ := by
  decide +kernel

theorem context_11_106138_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106138 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 106138 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 106138, 1, 262144⟩
    (by decide) selected_cut_50350

theorem selected_cut_50351 : selected 10 ⟨1437361, by decide⟩
    (prefixPartial 11 106139) = some ⟨11, 2, 0, 1437361, 106139, 2113, 262144⟩ := by
  decide +kernel

theorem context_11_106139_1437361 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106139 ⟨1437361, by decide⟩ :=
  accepted_of_selected 11 106139 ⟨1437361, by decide⟩ ⟨11, 2, 0, 1437361, 106139, 2113, 262144⟩
    (by decide) selected_cut_50351

theorem unmarked_context_10_26534_1437362 : frontier 11 ⟨1437362, by decide⟩
    (prefixCache 10 26534) (prefixPartial 10 26534) = false := by
  decide +kernel

theorem node_context_10_26534_1437362 : EJMOriginalGlobalDAGData.nodes 11 ⟨1437362, by decide⟩ =
    .split (coordinate 10) (![⟨1437238, by decide⟩,⟨1437310, by decide⟩,⟨900587, by decide⟩,⟨1437361, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26534_1437362 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26534 ⟨1437362, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26534
    ⟨1437362, by decide⟩ (by decide) (![⟨1437238, by decide⟩,⟨1437310, by decide⟩,⟨900587, by decide⟩,⟨1437361, by decide⟩]) unmarked_context_10_26534_1437362 node_context_10_26534_1437362
  intro a
  fin_cases a
  · exact context_11_106136_1437238
  · exact context_11_106137_1437310
  · exact context_11_106138_900587
  · exact context_11_106139_1437361

theorem selected_cut_50352 : selected 10 ⟨1437425, by decide⟩
    (prefixPartial 11 106140) = some ⟨11, 2, 0, 1437425, 106140, 2821, 262144⟩ := by
  decide +kernel

theorem context_11_106140_1437425 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106140 ⟨1437425, by decide⟩ :=
  accepted_of_selected 11 106140 ⟨1437425, by decide⟩ ⟨11, 2, 0, 1437425, 106140, 2821, 262144⟩
    (by decide) selected_cut_50352

theorem selected_cut_50353 : selected 10 ⟨1437482, by decide⟩
    (prefixPartial 11 106141) = some ⟨11, 2, 0, 1437482, 106141, 2301, 262144⟩ := by
  decide +kernel

theorem context_11_106141_1437482 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106141 ⟨1437482, by decide⟩ :=
  accepted_of_selected 11 106141 ⟨1437482, by decide⟩ ⟨11, 2, 0, 1437482, 106141, 2301, 262144⟩
    (by decide) selected_cut_50353

theorem selected_cut_50354 : selected 10 ⟨1437520, by decide⟩
    (prefixPartial 11 106142) = some ⟨11, 2, 0, 1437520, 106142, 1309, 262144⟩ := by
  decide +kernel

theorem context_11_106142_1437520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106142 ⟨1437520, by decide⟩ :=
  accepted_of_selected 11 106142 ⟨1437520, by decide⟩ ⟨11, 2, 0, 1437520, 106142, 1309, 262144⟩
    (by decide) selected_cut_50354

theorem selected_cut_50355 : selected 10 ⟨1437539, by decide⟩
    (prefixPartial 11 106143) = some ⟨11, 2, 0, 1437539, 106143, 749, 262144⟩ := by
  decide +kernel

theorem context_11_106143_1437539 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106143 ⟨1437539, by decide⟩ :=
  accepted_of_selected 11 106143 ⟨1437539, by decide⟩ ⟨11, 2, 0, 1437539, 106143, 749, 262144⟩
    (by decide) selected_cut_50355

theorem unmarked_context_10_26535_1437540 : frontier 11 ⟨1437540, by decide⟩
    (prefixCache 10 26535) (prefixPartial 10 26535) = false := by
  decide +kernel

theorem node_context_10_26535_1437540 : EJMOriginalGlobalDAGData.nodes 11 ⟨1437540, by decide⟩ =
    .split (coordinate 10) (![⟨1437425, by decide⟩,⟨1437482, by decide⟩,⟨1437520, by decide⟩,⟨1437539, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26535_1437540 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26535 ⟨1437540, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26535
    ⟨1437540, by decide⟩ (by decide) (![⟨1437425, by decide⟩,⟨1437482, by decide⟩,⟨1437520, by decide⟩,⟨1437539, by decide⟩]) unmarked_context_10_26535_1437540 node_context_10_26535_1437540
  intro a
  fin_cases a
  · exact context_11_106140_1437425
  · exact context_11_106141_1437482
  · exact context_11_106142_1437520
  · exact context_11_106143_1437539

theorem unmarked_context_9_6633_1437541 : frontier 12 ⟨1437541, by decide⟩
    (prefixCache 9 6633) (prefixPartial 9 6633) = false := by
  decide +kernel

theorem node_context_9_6633_1437541 : EJMOriginalGlobalDAGData.nodes 12 ⟨1437541, by decide⟩ =
    .split (coordinate 9) (![⟨1437193, by decide⟩,⟨893098, by decide⟩,⟨1437362, by decide⟩,⟨1437540, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6633_1437541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6633 ⟨1437541, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6633
    ⟨1437541, by decide⟩ (by decide) (![⟨1437193, by decide⟩,⟨893098, by decide⟩,⟨1437362, by decide⟩,⟨1437540, by decide⟩]) unmarked_context_9_6633_1437541 node_context_9_6633_1437541
  intro a
  fin_cases a
  · exact context_10_26532_1437193
  · exact context_10_26533_893098
  · exact context_10_26534_1437362
  · exact context_10_26535_1437540

theorem selected_cut_50356 : selected 10 ⟨1375697, by decide⟩
    (prefixPartial 11 106144) = some ⟨11, 1, 0, 1375697, 106144, 1, 262144⟩ := by
  decide +kernel

theorem context_11_106144_1375697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106144 ⟨1375697, by decide⟩ :=
  accepted_of_selected 11 106144 ⟨1375697, by decide⟩ ⟨11, 1, 0, 1375697, 106144, 1, 262144⟩
    (by decide) selected_cut_50356

theorem selected_cut_50357 : selected 10 ⟨1437585, by decide⟩
    (prefixPartial 11 106145) = some ⟨11, 2, 0, 1437585, 106145, 1713, 262144⟩ := by
  decide +kernel

theorem context_11_106145_1437585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106145 ⟨1437585, by decide⟩ :=
  accepted_of_selected 11 106145 ⟨1437585, by decide⟩ ⟨11, 2, 0, 1437585, 106145, 1713, 262144⟩
    (by decide) selected_cut_50357

theorem selected_cut_50358 : selected 10 ⟨1437634, by decide⟩
    (prefixPartial 11 106146) = some ⟨11, 2, 0, 1437634, 106146, 2061, 262144⟩ := by
  decide +kernel

theorem context_11_106146_1437634 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106146 ⟨1437634, by decide⟩ :=
  accepted_of_selected 11 106146 ⟨1437634, by decide⟩ ⟨11, 2, 0, 1437634, 106146, 2061, 262144⟩
    (by decide) selected_cut_50358

theorem selected_cut_50359 : selected 10 ⟨1437679, by decide⟩
    (prefixPartial 11 106147) = some ⟨11, 2, 0, 1437679, 106147, 1573, 262144⟩ := by
  decide +kernel

theorem context_11_106147_1437679 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106147 ⟨1437679, by decide⟩ :=
  accepted_of_selected 11 106147 ⟨1437679, by decide⟩ ⟨11, 2, 0, 1437679, 106147, 1573, 262144⟩
    (by decide) selected_cut_50359

theorem unmarked_context_10_26536_1437680 : frontier 11 ⟨1437680, by decide⟩
    (prefixCache 10 26536) (prefixPartial 10 26536) = false := by
  decide +kernel

theorem node_context_10_26536_1437680 : EJMOriginalGlobalDAGData.nodes 11 ⟨1437680, by decide⟩ =
    .split (coordinate 10) (![⟨1375697, by decide⟩,⟨1437585, by decide⟩,⟨1437634, by decide⟩,⟨1437679, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26536_1437680 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26536 ⟨1437680, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26536
    ⟨1437680, by decide⟩ (by decide) (![⟨1375697, by decide⟩,⟨1437585, by decide⟩,⟨1437634, by decide⟩,⟨1437679, by decide⟩]) unmarked_context_10_26536_1437680 node_context_10_26536_1437680
  intro a
  fin_cases a
  · exact context_11_106144_1375697
  · exact context_11_106145_1437585
  · exact context_11_106146_1437634
  · exact context_11_106147_1437679

theorem selected_cut_50360 : selected 11 ⟨1437764, by decide⟩
    (prefixPartial 10 26537) = some ⟨10, 2, 0, 1437764, 26537, 4037, 1048576⟩ := by
  decide +kernel

theorem context_10_26537_1437764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26537 ⟨1437764, by decide⟩ :=
  accepted_of_selected 10 26537 ⟨1437764, by decide⟩ ⟨10, 2, 0, 1437764, 26537, 4037, 1048576⟩
    (by decide) selected_cut_50360

theorem selected_cut_50361 : selected 11 ⟨1432895, by decide⟩
    (prefixPartial 10 26538) = some ⟨10, 2, 0, 1432895, 26538, 5, 1048576⟩ := by
  decide +kernel

theorem context_10_26538_1432895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26538 ⟨1432895, by decide⟩ :=
  accepted_of_selected 10 26538 ⟨1432895, by decide⟩ ⟨10, 2, 0, 1432895, 26538, 5, 1048576⟩
    (by decide) selected_cut_50361

theorem selected_cut_50362 : selected 11 ⟨1437839, by decide⟩
    (prefixPartial 10 26539) = some ⟨10, 2, 0, 1437839, 26539, 2973, 1048576⟩ := by
  decide +kernel

theorem context_10_26539_1437839 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26539 ⟨1437839, by decide⟩ :=
  accepted_of_selected 10 26539 ⟨1437839, by decide⟩ ⟨10, 2, 0, 1437839, 26539, 2973, 1048576⟩
    (by decide) selected_cut_50362

theorem unmarked_context_9_6634_1437840 : frontier 12 ⟨1437840, by decide⟩
    (prefixCache 9 6634) (prefixPartial 9 6634) = false := by
  decide +kernel

theorem node_context_9_6634_1437840 : EJMOriginalGlobalDAGData.nodes 12 ⟨1437840, by decide⟩ =
    .split (coordinate 9) (![⟨1437680, by decide⟩,⟨1437764, by decide⟩,⟨1432895, by decide⟩,⟨1437839, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6634_1437840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6634 ⟨1437840, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6634
    ⟨1437840, by decide⟩ (by decide) (![⟨1437680, by decide⟩,⟨1437764, by decide⟩,⟨1432895, by decide⟩,⟨1437839, by decide⟩]) unmarked_context_9_6634_1437840 node_context_9_6634_1437840
  intro a
  fin_cases a
  · exact context_10_26536_1437680
  · exact context_10_26537_1437764
  · exact context_10_26538_1432895
  · exact context_10_26539_1437839

theorem selected_cut_50363 : selected 11 ⟨1437917, by decide⟩
    (prefixPartial 10 26540) = some ⟨10, 2, 0, 1437917, 26540, 2629, 1048576⟩ := by
  decide +kernel

theorem context_10_26540_1437917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26540 ⟨1437917, by decide⟩ :=
  accepted_of_selected 10 26540 ⟨1437917, by decide⟩ ⟨10, 2, 0, 1437917, 26540, 2629, 1048576⟩
    (by decide) selected_cut_50363

theorem selected_cut_50364 : selected 11 ⟨1437962, by decide⟩
    (prefixPartial 10 26541) = some ⟨10, 2, 0, 1437962, 26541, 1401, 1048576⟩ := by
  decide +kernel

theorem context_10_26541_1437962 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26541 ⟨1437962, by decide⟩ :=
  accepted_of_selected 10 26541 ⟨1437962, by decide⟩ ⟨10, 2, 0, 1437962, 26541, 1401, 1048576⟩
    (by decide) selected_cut_50364

theorem selected_cut_50365 : selected 11 ⟨1437984, by decide⟩
    (prefixPartial 10 26542) = some ⟨10, 2, 0, 1437984, 26542, 653, 1048576⟩ := by
  decide +kernel

theorem context_10_26542_1437984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26542 ⟨1437984, by decide⟩ :=
  accepted_of_selected 10 26542 ⟨1437984, by decide⟩ ⟨10, 2, 0, 1437984, 26542, 653, 1048576⟩
    (by decide) selected_cut_50365

theorem selected_cut_50366 : selected 11 ⟨1435278, by decide⟩
    (prefixPartial 10 26543) = some ⟨10, 2, 0, 1435278, 26543, 41, 1048576⟩ := by
  decide +kernel

theorem context_10_26543_1435278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26543 ⟨1435278, by decide⟩ :=
  accepted_of_selected 10 26543 ⟨1435278, by decide⟩ ⟨10, 2, 0, 1435278, 26543, 41, 1048576⟩
    (by decide) selected_cut_50366

theorem unmarked_context_9_6635_1437985 : frontier 12 ⟨1437985, by decide⟩
    (prefixCache 9 6635) (prefixPartial 9 6635) = false := by
  decide +kernel

theorem node_context_9_6635_1437985 : EJMOriginalGlobalDAGData.nodes 12 ⟨1437985, by decide⟩ =
    .split (coordinate 9) (![⟨1437917, by decide⟩,⟨1437962, by decide⟩,⟨1437984, by decide⟩,⟨1435278, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6635_1437985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6635 ⟨1437985, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6635
    ⟨1437985, by decide⟩ (by decide) (![⟨1437917, by decide⟩,⟨1437962, by decide⟩,⟨1437984, by decide⟩,⟨1435278, by decide⟩]) unmarked_context_9_6635_1437985 node_context_9_6635_1437985
  intro a
  fin_cases a
  · exact context_10_26540_1437917
  · exact context_10_26541_1437962
  · exact context_10_26542_1437984
  · exact context_10_26543_1435278

theorem unmarked_context_8_1658_1437986 : frontier 13 ⟨1437986, by decide⟩
    (prefixCache 8 1658) (prefixPartial 8 1658) = false := by
  decide +kernel

theorem node_context_8_1658_1437986 : EJMOriginalGlobalDAGData.nodes 13 ⟨1437986, by decide⟩ =
    .split (coordinate 8) (![⟨1436889, by decide⟩,⟨1437541, by decide⟩,⟨1437840, by decide⟩,⟨1437985, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1658_1437986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1658 ⟨1437986, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1658
    ⟨1437986, by decide⟩ (by decide) (![⟨1436889, by decide⟩,⟨1437541, by decide⟩,⟨1437840, by decide⟩,⟨1437985, by decide⟩]) unmarked_context_8_1658_1437986 node_context_8_1658_1437986
  intro a
  fin_cases a
  · exact context_9_6632_1436889
  · exact context_9_6633_1437541
  · exact context_9_6634_1437840
  · exact context_9_6635_1437985

theorem selected_cut_50367 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 106176) = some ⟨11, 1, 0, 434745, 106176, 1, 262144⟩ := by
  decide +kernel

theorem context_11_106176_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106176 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 106176 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 106176, 1, 262144⟩
    (by decide) selected_cut_50367

theorem selected_cut_50368 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 106177) = some ⟨11, 1, 0, 434745, 106177, 1, 262144⟩ := by
  decide +kernel

theorem context_11_106177_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106177 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 106177 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 106177, 1, 262144⟩
    (by decide) selected_cut_50368

theorem selected_cut_50369 : selected 10 ⟨1438052, by decide⟩
    (prefixPartial 11 106178) = some ⟨11, 2, 0, 1438052, 106178, 2181, 262144⟩ := by
  decide +kernel

theorem context_11_106178_1438052 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106178 ⟨1438052, by decide⟩ :=
  accepted_of_selected 11 106178 ⟨1438052, by decide⟩ ⟨11, 2, 0, 1438052, 106178, 2181, 262144⟩
    (by decide) selected_cut_50369

theorem selected_cut_50370 : selected 10 ⟨1438142, by decide⟩
    (prefixPartial 11 106179) = some ⟨11, 2, 0, 1438142, 106179, 2897, 262144⟩ := by
  decide +kernel

theorem context_11_106179_1438142 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106179 ⟨1438142, by decide⟩ :=
  accepted_of_selected 11 106179 ⟨1438142, by decide⟩ ⟨11, 2, 0, 1438142, 106179, 2897, 262144⟩
    (by decide) selected_cut_50370

theorem unmarked_context_10_26544_1438143 : frontier 11 ⟨1438143, by decide⟩
    (prefixCache 10 26544) (prefixPartial 10 26544) = false := by
  decide +kernel

theorem node_context_10_26544_1438143 : EJMOriginalGlobalDAGData.nodes 11 ⟨1438143, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨434745, by decide⟩,⟨1438052, by decide⟩,⟨1438142, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26544_1438143 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26544 ⟨1438143, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26544
    ⟨1438143, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨434745, by decide⟩,⟨1438052, by decide⟩,⟨1438142, by decide⟩]) unmarked_context_10_26544_1438143 node_context_10_26544_1438143
  intro a
  fin_cases a
  · exact context_11_106176_434745
  · exact context_11_106177_434745
  · exact context_11_106178_1438052
  · exact context_11_106179_1438142

theorem selected_cut_50371 : selected 9 ⟨1415033, by decide⟩
    (prefixPartial 12 424720) = some ⟨12, 1, 0, 1415033, 424720, 1, 65536⟩ := by
  decide +kernel

theorem context_12_424720_1415033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424720 ⟨1415033, by decide⟩ :=
  accepted_of_selected 12 424720 ⟨1415033, by decide⟩ ⟨12, 1, 0, 1415033, 424720, 1, 65536⟩
    (by decide) selected_cut_50371

theorem selected_cut_50372 : selected 9 ⟨1438200, by decide⟩
    (prefixPartial 12 424721) = some ⟨12, 2, 0, 1438200, 424721, 2301, 65536⟩ := by
  decide +kernel

theorem context_12_424721_1438200 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424721 ⟨1438200, by decide⟩ :=
  accepted_of_selected 12 424721 ⟨1438200, by decide⟩ ⟨12, 2, 0, 1438200, 424721, 2301, 65536⟩
    (by decide) selected_cut_50372

theorem selected_cut_50373 : selected 9 ⟨1438251, by decide⟩
    (prefixPartial 12 424722) = some ⟨12, 2, 0, 1438251, 424722, 2517, 65536⟩ := by
  decide +kernel

theorem context_12_424722_1438251 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424722 ⟨1438251, by decide⟩ :=
  accepted_of_selected 12 424722 ⟨1438251, by decide⟩ ⟨12, 2, 0, 1438251, 424722, 2517, 65536⟩
    (by decide) selected_cut_50373

theorem selected_cut_50374 : selected 9 ⟨1438304, by decide⟩
    (prefixPartial 12 424723) = some ⟨12, 2, 0, 1438304, 424723, 2365, 65536⟩ := by
  decide +kernel

theorem context_12_424723_1438304 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424723 ⟨1438304, by decide⟩ :=
  accepted_of_selected 12 424723 ⟨1438304, by decide⟩ ⟨12, 2, 0, 1438304, 424723, 2365, 65536⟩
    (by decide) selected_cut_50374

theorem unmarked_context_11_106180_1438305 : frontier 10 ⟨1438305, by decide⟩
    (prefixCache 11 106180) (prefixPartial 11 106180) = false := by
  decide +kernel

theorem node_context_11_106180_1438305 : EJMOriginalGlobalDAGData.nodes 10 ⟨1438305, by decide⟩ =
    .split (coordinate 11) (![⟨1415033, by decide⟩,⟨1438200, by decide⟩,⟨1438251, by decide⟩,⟨1438304, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_106180_1438305 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106180 ⟨1438305, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 106180
    ⟨1438305, by decide⟩ (by decide) (![⟨1415033, by decide⟩,⟨1438200, by decide⟩,⟨1438251, by decide⟩,⟨1438304, by decide⟩]) unmarked_context_11_106180_1438305 node_context_11_106180_1438305
  intro a
  fin_cases a
  · exact context_12_424720_1415033
  · exact context_12_424721_1438200
  · exact context_12_424722_1438251
  · exact context_12_424723_1438304

theorem selected_cut_50375 : selected 10 ⟨1192826, by decide⟩
    (prefixPartial 11 106181) = some ⟨11, 1, 0, 1192826, 106181, 1, 262144⟩ := by
  decide +kernel

theorem context_11_106181_1192826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106181 ⟨1192826, by decide⟩ :=
  accepted_of_selected 11 106181 ⟨1192826, by decide⟩ ⟨11, 1, 0, 1192826, 106181, 1, 262144⟩
    (by decide) selected_cut_50375

theorem selected_cut_50376 : selected 9 ⟨1415033, by decide⟩
    (prefixPartial 12 424728) = some ⟨12, 1, 0, 1415033, 424728, 1, 65536⟩ := by
  decide +kernel

theorem context_12_424728_1415033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424728 ⟨1415033, by decide⟩ :=
  accepted_of_selected 12 424728 ⟨1415033, by decide⟩ ⟨12, 1, 0, 1415033, 424728, 1, 65536⟩
    (by decide) selected_cut_50376

theorem selected_cut_50377 : selected 9 ⟨1438357, by decide⟩
    (prefixPartial 12 424729) = some ⟨12, 2, 0, 1438357, 424729, 2149, 65536⟩ := by
  decide +kernel

theorem context_12_424729_1438357 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424729 ⟨1438357, by decide⟩ :=
  accepted_of_selected 12 424729 ⟨1438357, by decide⟩ ⟨12, 2, 0, 1438357, 424729, 2149, 65536⟩
    (by decide) selected_cut_50377

theorem selected_cut_50378 : selected 9 ⟨1438358, by decide⟩
    (prefixPartial 12 424730) = some ⟨12, 1, 0, 1438358, 424730, 1, 65536⟩ := by
  decide +kernel

theorem context_12_424730_1438358 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424730 ⟨1438358, by decide⟩ :=
  accepted_of_selected 12 424730 ⟨1438358, by decide⟩ ⟨12, 1, 0, 1438358, 424730, 1, 65536⟩
    (by decide) selected_cut_50378

theorem selected_cut_50379 : selected 9 ⟨1438406, by decide⟩
    (prefixPartial 12 424731) = some ⟨12, 2, 0, 1438406, 424731, 2081, 65536⟩ := by
  decide +kernel

theorem context_12_424731_1438406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424731 ⟨1438406, by decide⟩ :=
  accepted_of_selected 12 424731 ⟨1438406, by decide⟩ ⟨12, 2, 0, 1438406, 424731, 2081, 65536⟩
    (by decide) selected_cut_50379

theorem unmarked_context_11_106182_1438407 : frontier 10 ⟨1438407, by decide⟩
    (prefixCache 11 106182) (prefixPartial 11 106182) = false := by
  decide +kernel

theorem node_context_11_106182_1438407 : EJMOriginalGlobalDAGData.nodes 10 ⟨1438407, by decide⟩ =
    .split (coordinate 11) (![⟨1415033, by decide⟩,⟨1438357, by decide⟩,⟨1438358, by decide⟩,⟨1438406, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_106182_1438407 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106182 ⟨1438407, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 106182
    ⟨1438407, by decide⟩ (by decide) (![⟨1415033, by decide⟩,⟨1438357, by decide⟩,⟨1438358, by decide⟩,⟨1438406, by decide⟩]) unmarked_context_11_106182_1438407 node_context_11_106182_1438407
  intro a
  fin_cases a
  · exact context_12_424728_1415033
  · exact context_12_424729_1438357
  · exact context_12_424730_1438358
  · exact context_12_424731_1438406

theorem selected_cut_50380 : selected 9 ⟨1415033, by decide⟩
    (prefixPartial 12 424732) = some ⟨12, 1, 0, 1415033, 424732, 1, 65536⟩ := by
  decide +kernel

theorem context_12_424732_1415033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424732 ⟨1415033, by decide⟩ :=
  accepted_of_selected 12 424732 ⟨1415033, by decide⟩ ⟨12, 1, 0, 1415033, 424732, 1, 65536⟩
    (by decide) selected_cut_50380

theorem selected_cut_50381 : selected 9 ⟨1438453, by decide⟩
    (prefixPartial 12 424733) = some ⟨12, 2, 0, 1438453, 424733, 2157, 65536⟩ := by
  decide +kernel

theorem context_12_424733_1438453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424733 ⟨1438453, by decide⟩ :=
  accepted_of_selected 12 424733 ⟨1438453, by decide⟩ ⟨12, 2, 0, 1438453, 424733, 2157, 65536⟩
    (by decide) selected_cut_50381

theorem selected_cut_50382 : selected 9 ⟨1438508, by decide⟩
    (prefixPartial 12 424734) = some ⟨12, 2, 0, 1438508, 424734, 2509, 65536⟩ := by
  decide +kernel

theorem context_12_424734_1438508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424734 ⟨1438508, by decide⟩ :=
  accepted_of_selected 12 424734 ⟨1438508, by decide⟩ ⟨12, 2, 0, 1438508, 424734, 2509, 65536⟩
    (by decide) selected_cut_50382

theorem selected_cut_50383 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 424735) = some ⟨12, 1, 0, 903806, 424735, 1, 65536⟩ := by
  decide +kernel

theorem context_12_424735_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424735 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 424735 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 424735, 1, 65536⟩
    (by decide) selected_cut_50383

theorem unmarked_context_11_106183_1438509 : frontier 10 ⟨1438509, by decide⟩
    (prefixCache 11 106183) (prefixPartial 11 106183) = false := by
  decide +kernel

theorem node_context_11_106183_1438509 : EJMOriginalGlobalDAGData.nodes 10 ⟨1438509, by decide⟩ =
    .split (coordinate 11) (![⟨1415033, by decide⟩,⟨1438453, by decide⟩,⟨1438508, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_106183_1438509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106183 ⟨1438509, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 106183
    ⟨1438509, by decide⟩ (by decide) (![⟨1415033, by decide⟩,⟨1438453, by decide⟩,⟨1438508, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_106183_1438509 node_context_11_106183_1438509
  intro a
  fin_cases a
  · exact context_12_424732_1415033
  · exact context_12_424733_1438453
  · exact context_12_424734_1438508
  · exact context_12_424735_903806

theorem unmarked_context_10_26545_1438510 : frontier 11 ⟨1438510, by decide⟩
    (prefixCache 10 26545) (prefixPartial 10 26545) = false := by
  decide +kernel

theorem node_context_10_26545_1438510 : EJMOriginalGlobalDAGData.nodes 11 ⟨1438510, by decide⟩ =
    .split (coordinate 10) (![⟨1438305, by decide⟩,⟨1192826, by decide⟩,⟨1438407, by decide⟩,⟨1438509, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26545_1438510 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26545 ⟨1438510, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26545
    ⟨1438510, by decide⟩ (by decide) (![⟨1438305, by decide⟩,⟨1192826, by decide⟩,⟨1438407, by decide⟩,⟨1438509, by decide⟩]) unmarked_context_10_26545_1438510 node_context_10_26545_1438510
  intro a
  fin_cases a
  · exact context_11_106180_1438305
  · exact context_11_106181_1192826
  · exact context_11_106182_1438407
  · exact context_11_106183_1438509

theorem selected_cut_50384 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 424736) = some ⟨12, 1, 0, 435160, 424736, 1, 65536⟩ := by
  decide +kernel

theorem context_12_424736_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424736 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 424736 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 424736, 1, 65536⟩
    (by decide) selected_cut_50384

theorem selected_cut_50385 : selected 9 ⟨1438551, by decide⟩
    (prefixPartial 12 424737) = some ⟨12, 2, 0, 1438551, 424737, 1985, 65536⟩ := by
  decide +kernel

theorem context_12_424737_1438551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424737 ⟨1438551, by decide⟩ :=
  accepted_of_selected 12 424737 ⟨1438551, by decide⟩ ⟨12, 2, 0, 1438551, 424737, 1985, 65536⟩
    (by decide) selected_cut_50385

theorem selected_cut_50386 : selected 9 ⟨1438599, by decide⟩
    (prefixPartial 12 424738) = some ⟨12, 2, 0, 1438599, 424738, 2117, 65536⟩ := by
  decide +kernel

theorem context_12_424738_1438599 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424738 ⟨1438599, by decide⟩ :=
  accepted_of_selected 12 424738 ⟨1438599, by decide⟩ ⟨12, 2, 0, 1438599, 424738, 2117, 65536⟩
    (by decide) selected_cut_50386

theorem selected_cut_50387 : selected 9 ⟨1438641, by decide⟩
    (prefixPartial 12 424739) = some ⟨12, 2, 0, 1438641, 424739, 1801, 65536⟩ := by
  decide +kernel

theorem context_12_424739_1438641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424739 ⟨1438641, by decide⟩ :=
  accepted_of_selected 12 424739 ⟨1438641, by decide⟩ ⟨12, 2, 0, 1438641, 424739, 1801, 65536⟩
    (by decide) selected_cut_50387

theorem unmarked_context_11_106184_1438642 : frontier 10 ⟨1438642, by decide⟩
    (prefixCache 11 106184) (prefixPartial 11 106184) = false := by
  decide +kernel

theorem node_context_11_106184_1438642 : EJMOriginalGlobalDAGData.nodes 10 ⟨1438642, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨1438551, by decide⟩,⟨1438599, by decide⟩,⟨1438641, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_106184_1438642 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106184 ⟨1438642, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 106184
    ⟨1438642, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨1438551, by decide⟩,⟨1438599, by decide⟩,⟨1438641, by decide⟩]) unmarked_context_11_106184_1438642 node_context_11_106184_1438642
  intro a
  fin_cases a
  · exact context_12_424736_435160
  · exact context_12_424737_1438551
  · exact context_12_424738_1438599
  · exact context_12_424739_1438641

theorem selected_cut_50388 : selected 10 ⟨1438703, by decide⟩
    (prefixPartial 11 106185) = some ⟨11, 2, 0, 1438703, 106185, 3241, 262144⟩ := by
  decide +kernel

theorem context_11_106185_1438703 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106185 ⟨1438703, by decide⟩ :=
  accepted_of_selected 11 106185 ⟨1438703, by decide⟩ ⟨11, 2, 0, 1438703, 106185, 3241, 262144⟩
    (by decide) selected_cut_50388

theorem selected_cut_50389 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 106186) = some ⟨11, 1, 0, 900587, 106186, 1, 262144⟩ := by
  decide +kernel

theorem context_11_106186_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106186 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 106186 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 106186, 1, 262144⟩
    (by decide) selected_cut_50389

theorem selected_cut_50390 : selected 9 ⟨1438742, by decide⟩
    (prefixPartial 12 424748) = some ⟨12, 2, 0, 1438742, 424748, 1797, 65536⟩ := by
  decide +kernel

theorem context_12_424748_1438742 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424748 ⟨1438742, by decide⟩ :=
  accepted_of_selected 12 424748 ⟨1438742, by decide⟩ ⟨12, 2, 0, 1438742, 424748, 1797, 65536⟩
    (by decide) selected_cut_50390

theorem selected_cut_50391 : selected 9 ⟨1438779, by decide⟩
    (prefixPartial 12 424749) = some ⟨12, 2, 0, 1438779, 424749, 1673, 65536⟩ := by
  decide +kernel

theorem context_12_424749_1438779 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424749 ⟨1438779, by decide⟩ :=
  accepted_of_selected 12 424749 ⟨1438779, by decide⟩ ⟨12, 2, 0, 1438779, 424749, 1673, 65536⟩
    (by decide) selected_cut_50391

theorem selected_cut_50392 : selected 9 ⟨1438819, by decide⟩
    (prefixPartial 12 424750) = some ⟨12, 2, 0, 1438819, 424750, 2021, 65536⟩ := by
  decide +kernel

theorem context_12_424750_1438819 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424750 ⟨1438819, by decide⟩ :=
  accepted_of_selected 12 424750 ⟨1438819, by decide⟩ ⟨12, 2, 0, 1438819, 424750, 2021, 65536⟩
    (by decide) selected_cut_50392

theorem selected_cut_50393 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 424751) = some ⟨12, 1, 0, 903806, 424751, 1, 65536⟩ := by
  decide +kernel

theorem context_12_424751_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424751 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 424751 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 424751, 1, 65536⟩
    (by decide) selected_cut_50393

theorem unmarked_context_11_106187_1438820 : frontier 10 ⟨1438820, by decide⟩
    (prefixCache 11 106187) (prefixPartial 11 106187) = false := by
  decide +kernel

theorem node_context_11_106187_1438820 : EJMOriginalGlobalDAGData.nodes 10 ⟨1438820, by decide⟩ =
    .split (coordinate 11) (![⟨1438742, by decide⟩,⟨1438779, by decide⟩,⟨1438819, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_106187_1438820 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106187 ⟨1438820, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 106187
    ⟨1438820, by decide⟩ (by decide) (![⟨1438742, by decide⟩,⟨1438779, by decide⟩,⟨1438819, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_106187_1438820 node_context_11_106187_1438820
  intro a
  fin_cases a
  · exact context_12_424748_1438742
  · exact context_12_424749_1438779
  · exact context_12_424750_1438819
  · exact context_12_424751_903806

theorem unmarked_context_10_26546_1438821 : frontier 11 ⟨1438821, by decide⟩
    (prefixCache 10 26546) (prefixPartial 10 26546) = false := by
  decide +kernel

theorem node_context_10_26546_1438821 : EJMOriginalGlobalDAGData.nodes 11 ⟨1438821, by decide⟩ =
    .split (coordinate 10) (![⟨1438642, by decide⟩,⟨1438703, by decide⟩,⟨900587, by decide⟩,⟨1438820, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26546_1438821 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26546 ⟨1438821, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26546
    ⟨1438821, by decide⟩ (by decide) (![⟨1438642, by decide⟩,⟨1438703, by decide⟩,⟨900587, by decide⟩,⟨1438820, by decide⟩]) unmarked_context_10_26546_1438821 node_context_10_26546_1438821
  intro a
  fin_cases a
  · exact context_11_106184_1438642
  · exact context_11_106185_1438703
  · exact context_11_106186_900587
  · exact context_11_106187_1438820

theorem selected_cut_50394 : selected 9 ⟨1416143, by decide⟩
    (prefixPartial 12 424752) = some ⟨12, 1, 0, 1416143, 424752, 1, 65536⟩ := by
  decide +kernel

theorem context_12_424752_1416143 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424752 ⟨1416143, by decide⟩ :=
  accepted_of_selected 12 424752 ⟨1416143, by decide⟩ ⟨12, 1, 0, 1416143, 424752, 1, 65536⟩
    (by decide) selected_cut_50394

theorem selected_cut_50395 : selected 9 ⟨1438857, by decide⟩
    (prefixPartial 12 424753) = some ⟨12, 2, 0, 1438857, 424753, 1745, 65536⟩ := by
  decide +kernel

theorem context_12_424753_1438857 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424753 ⟨1438857, by decide⟩ :=
  accepted_of_selected 12 424753 ⟨1438857, by decide⟩ ⟨12, 2, 0, 1438857, 424753, 1745, 65536⟩
    (by decide) selected_cut_50395

theorem selected_cut_50396 : selected 9 ⟨1438896, by decide⟩
    (prefixPartial 12 424754) = some ⟨12, 2, 0, 1438896, 424754, 1909, 65536⟩ := by
  decide +kernel

theorem context_12_424754_1438896 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424754 ⟨1438896, by decide⟩ :=
  accepted_of_selected 12 424754 ⟨1438896, by decide⟩ ⟨12, 2, 0, 1438896, 424754, 1909, 65536⟩
    (by decide) selected_cut_50396

theorem selected_cut_50397 : selected 9 ⟨1438935, by decide⟩
    (prefixPartial 12 424755) = some ⟨12, 2, 0, 1438935, 424755, 1637, 65536⟩ := by
  decide +kernel

theorem context_12_424755_1438935 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 424755 ⟨1438935, by decide⟩ :=
  accepted_of_selected 12 424755 ⟨1438935, by decide⟩ ⟨12, 2, 0, 1438935, 424755, 1637, 65536⟩
    (by decide) selected_cut_50397

theorem unmarked_context_11_106188_1438936 : frontier 10 ⟨1438936, by decide⟩
    (prefixCache 11 106188) (prefixPartial 11 106188) = false := by
  decide +kernel

theorem node_context_11_106188_1438936 : EJMOriginalGlobalDAGData.nodes 10 ⟨1438936, by decide⟩ =
    .split (coordinate 11) (![⟨1416143, by decide⟩,⟨1438857, by decide⟩,⟨1438896, by decide⟩,⟨1438935, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_106188_1438936 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106188 ⟨1438936, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 106188
    ⟨1438936, by decide⟩ (by decide) (![⟨1416143, by decide⟩,⟨1438857, by decide⟩,⟨1438896, by decide⟩,⟨1438935, by decide⟩]) unmarked_context_11_106188_1438936 node_context_11_106188_1438936
  intro a
  fin_cases a
  · exact context_12_424752_1416143
  · exact context_12_424753_1438857
  · exact context_12_424754_1438896
  · exact context_12_424755_1438935

theorem selected_cut_50398 : selected 10 ⟨1439008, by decide⟩
    (prefixPartial 11 106189) = some ⟨11, 2, 0, 1439008, 106189, 2973, 262144⟩ := by
  decide +kernel

theorem context_11_106189_1439008 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106189 ⟨1439008, by decide⟩ :=
  accepted_of_selected 11 106189 ⟨1439008, by decide⟩ ⟨11, 2, 0, 1439008, 106189, 2973, 262144⟩
    (by decide) selected_cut_50398

theorem selected_cut_50399 : selected 10 ⟨1439108, by decide⟩
    (prefixPartial 11 106190) = some ⟨11, 2, 0, 1439108, 106190, 3565, 262144⟩ := by
  decide +kernel

theorem context_11_106190_1439108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106190 ⟨1439108, by decide⟩ :=
  accepted_of_selected 11 106190 ⟨1439108, by decide⟩ ⟨11, 2, 0, 1439108, 106190, 3565, 262144⟩
    (by decide) selected_cut_50399

theorem selected_cut_50400 : selected 10 ⟨1439110, by decide⟩
    (prefixPartial 11 106191) = some ⟨11, 2, 0, 1439110, 106191, 5, 262144⟩ := by
  decide +kernel

theorem context_11_106191_1439110 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106191 ⟨1439110, by decide⟩ :=
  accepted_of_selected 11 106191 ⟨1439110, by decide⟩ ⟨11, 2, 0, 1439110, 106191, 5, 262144⟩
    (by decide) selected_cut_50400

theorem unmarked_context_10_26547_1439111 : frontier 11 ⟨1439111, by decide⟩
    (prefixCache 10 26547) (prefixPartial 10 26547) = false := by
  decide +kernel

theorem node_context_10_26547_1439111 : EJMOriginalGlobalDAGData.nodes 11 ⟨1439111, by decide⟩ =
    .split (coordinate 10) (![⟨1438936, by decide⟩,⟨1439008, by decide⟩,⟨1439108, by decide⟩,⟨1439110, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26547_1439111 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26547 ⟨1439111, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26547
    ⟨1439111, by decide⟩ (by decide) (![⟨1438936, by decide⟩,⟨1439008, by decide⟩,⟨1439108, by decide⟩,⟨1439110, by decide⟩]) unmarked_context_10_26547_1439111 node_context_10_26547_1439111
  intro a
  fin_cases a
  · exact context_11_106188_1438936
  · exact context_11_106189_1439008
  · exact context_11_106190_1439108
  · exact context_11_106191_1439110

theorem unmarked_context_9_6636_1439112 : frontier 12 ⟨1439112, by decide⟩
    (prefixCache 9 6636) (prefixPartial 9 6636) = false := by
  decide +kernel

theorem node_context_9_6636_1439112 : EJMOriginalGlobalDAGData.nodes 12 ⟨1439112, by decide⟩ =
    .split (coordinate 9) (![⟨1438143, by decide⟩,⟨1438510, by decide⟩,⟨1438821, by decide⟩,⟨1439111, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6636_1439112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6636 ⟨1439112, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6636
    ⟨1439112, by decide⟩ (by decide) (![⟨1438143, by decide⟩,⟨1438510, by decide⟩,⟨1438821, by decide⟩,⟨1439111, by decide⟩]) unmarked_context_9_6636_1439112 node_context_9_6636_1439112
  intro a
  fin_cases a
  · exact context_10_26544_1438143
  · exact context_10_26545_1438510
  · exact context_10_26546_1438821
  · exact context_10_26547_1439111

theorem selected_cut_50401 : selected 10 ⟨1439148, by decide⟩
    (prefixPartial 11 106192) = some ⟨11, 2, 0, 1439148, 106192, 1421, 262144⟩ := by
  decide +kernel

theorem context_11_106192_1439148 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106192 ⟨1439148, by decide⟩ :=
  accepted_of_selected 11 106192 ⟨1439148, by decide⟩ ⟨11, 2, 0, 1439148, 106192, 1421, 262144⟩
    (by decide) selected_cut_50401

theorem selected_cut_50402 : selected 10 ⟨1439225, by decide⟩
    (prefixPartial 11 106193) = some ⟨11, 2, 0, 1439225, 106193, 3609, 262144⟩ := by
  decide +kernel

theorem context_11_106193_1439225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106193 ⟨1439225, by decide⟩ :=
  accepted_of_selected 11 106193 ⟨1439225, by decide⟩ ⟨11, 2, 0, 1439225, 106193, 3609, 262144⟩
    (by decide) selected_cut_50402

theorem selected_cut_50403 : selected 10 ⟨1439290, by decide⟩
    (prefixPartial 11 106194) = some ⟨11, 2, 0, 1439290, 106194, 2425, 262144⟩ := by
  decide +kernel

theorem context_11_106194_1439290 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 106194 ⟨1439290, by decide⟩ :=
  accepted_of_selected 11 106194 ⟨1439290, by decide⟩ ⟨11, 2, 0, 1439290, 106194, 2425, 262144⟩
    (by decide) selected_cut_50403

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
