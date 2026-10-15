/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover441
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_11_84495_1159814 : frontier 10 ⟨1159814, by decide⟩
    (prefixCache 11 84495) (prefixPartial 11 84495) = false := by
  decide +kernel

theorem node_context_11_84495_1159814 : EJMOriginalGlobalDAGData.nodes 10 ⟨1159814, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1159781, by decide⟩,⟨1159813, by decide⟩,⟨1120582, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84495_1159814 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84495 ⟨1159814, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84495
    ⟨1159814, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1159781, by decide⟩,⟨1159813, by decide⟩,⟨1120582, by decide⟩]) unmarked_context_11_84495_1159814 node_context_11_84495_1159814
  intro a
  fin_cases a
  · exact context_12_337980_1108174
  · exact context_12_337981_1159781
  · exact context_12_337982_1159813
  · exact context_12_337983_1120582

theorem unmarked_context_10_21123_1159815 : frontier 11 ⟨1159815, by decide⟩
    (prefixCache 10 21123) (prefixPartial 10 21123) = false := by
  decide +kernel

theorem node_context_10_21123_1159815 : EJMOriginalGlobalDAGData.nodes 11 ⟨1159815, by decide⟩ =
    .split (coordinate 10) (![⟨1159497, by decide⟩,⟨1159639, by decide⟩,⟨1159750, by decide⟩,⟨1159814, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21123_1159815 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21123 ⟨1159815, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21123
    ⟨1159815, by decide⟩ (by decide) (![⟨1159497, by decide⟩,⟨1159639, by decide⟩,⟨1159750, by decide⟩,⟨1159814, by decide⟩]) unmarked_context_10_21123_1159815 node_context_10_21123_1159815
  intro a
  fin_cases a
  · exact context_11_84492_1159497
  · exact context_11_84493_1159639
  · exact context_11_84494_1159750
  · exact context_11_84495_1159814

theorem unmarked_context_9_5280_1159816 : frontier 12 ⟨1159816, by decide⟩
    (prefixCache 9 5280) (prefixPartial 9 5280) = false := by
  decide +kernel

theorem node_context_9_5280_1159816 : EJMOriginalGlobalDAGData.nodes 12 ⟨1159816, by decide⟩ =
    .split (coordinate 9) (![⟨1158471, by decide⟩,⟨1158954, by decide⟩,⟨1159370, by decide⟩,⟨1159815, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5280_1159816 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5280 ⟨1159816, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5280
    ⟨1159816, by decide⟩ (by decide) (![⟨1158471, by decide⟩,⟨1158954, by decide⟩,⟨1159370, by decide⟩,⟨1159815, by decide⟩]) unmarked_context_9_5280_1159816 node_context_9_5280_1159816
  intro a
  fin_cases a
  · exact context_10_21120_1158471
  · exact context_10_21121_1158954
  · exact context_10_21122_1159370
  · exact context_10_21123_1159815

theorem selected_cut_42436 : selected 10 ⟨1159893, by decide⟩
    (prefixPartial 11 84496) = some ⟨11, 2, 0, 1159893, 84496, 2957, 262144⟩ := by
  decide +kernel

theorem context_11_84496_1159893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84496 ⟨1159893, by decide⟩ :=
  accepted_of_selected 11 84496 ⟨1159893, by decide⟩ ⟨11, 2, 0, 1159893, 84496, 2957, 262144⟩
    (by decide) selected_cut_42436

theorem selected_cut_42437 : selected 9 ⟨1159913, by decide⟩
    (prefixPartial 12 337988) = some ⟨12, 2, 0, 1159913, 337988, 1697, 65536⟩ := by
  decide +kernel

theorem context_12_337988_1159913 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337988 ⟨1159913, by decide⟩ :=
  accepted_of_selected 12 337988 ⟨1159913, by decide⟩ ⟨12, 2, 0, 1159913, 337988, 1697, 65536⟩
    (by decide) selected_cut_42437

theorem selected_cut_42438 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 337989) = some ⟨12, 1, 0, 170504, 337989, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337989_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337989 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 337989 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 337989, 1, 65536⟩
    (by decide) selected_cut_42438

theorem selected_cut_42439 : selected 9 ⟨1159936, by decide⟩
    (prefixPartial 12 337990) = some ⟨12, 2, 0, 1159936, 337990, 1901, 65536⟩ := by
  decide +kernel

theorem context_12_337990_1159936 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337990 ⟨1159936, by decide⟩ :=
  accepted_of_selected 12 337990 ⟨1159936, by decide⟩ ⟨12, 2, 0, 1159936, 337990, 1901, 65536⟩
    (by decide) selected_cut_42439

theorem selected_cut_42440 : selected 9 ⟨1159964, by decide⟩
    (prefixPartial 12 337991) = some ⟨12, 2, 0, 1159964, 337991, 2025, 65536⟩ := by
  decide +kernel

theorem context_12_337991_1159964 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337991 ⟨1159964, by decide⟩ :=
  accepted_of_selected 12 337991 ⟨1159964, by decide⟩ ⟨12, 2, 0, 1159964, 337991, 2025, 65536⟩
    (by decide) selected_cut_42440

theorem unmarked_context_11_84497_1159965 : frontier 10 ⟨1159965, by decide⟩
    (prefixCache 11 84497) (prefixPartial 11 84497) = false := by
  decide +kernel

theorem node_context_11_84497_1159965 : EJMOriginalGlobalDAGData.nodes 10 ⟨1159965, by decide⟩ =
    .split (coordinate 11) (![⟨1159913, by decide⟩,⟨170504, by decide⟩,⟨1159936, by decide⟩,⟨1159964, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84497_1159965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84497 ⟨1159965, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84497
    ⟨1159965, by decide⟩ (by decide) (![⟨1159913, by decide⟩,⟨170504, by decide⟩,⟨1159936, by decide⟩,⟨1159964, by decide⟩]) unmarked_context_11_84497_1159965 node_context_11_84497_1159965
  intro a
  fin_cases a
  · exact context_12_337988_1159913
  · exact context_12_337989_170504
  · exact context_12_337990_1159936
  · exact context_12_337991_1159964

theorem selected_cut_42441 : selected 10 ⟨1160016, by decide⟩
    (prefixPartial 11 84498) = some ⟨11, 2, 0, 1160016, 84498, 3297, 262144⟩ := by
  decide +kernel

theorem context_11_84498_1160016 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84498 ⟨1160016, by decide⟩ :=
  accepted_of_selected 11 84498 ⟨1160016, by decide⟩ ⟨11, 2, 0, 1160016, 84498, 3297, 262144⟩
    (by decide) selected_cut_42441

theorem selected_cut_42442 : selected 9 ⟨1160033, by decide⟩
    (prefixPartial 12 337996) = some ⟨12, 2, 0, 1160033, 337996, 1477, 65536⟩ := by
  decide +kernel

theorem context_12_337996_1160033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337996 ⟨1160033, by decide⟩ :=
  accepted_of_selected 12 337996 ⟨1160033, by decide⟩ ⟨12, 2, 0, 1160033, 337996, 1477, 65536⟩
    (by decide) selected_cut_42442

theorem selected_cut_42443 : selected 9 ⟨320864, by decide⟩
    (prefixPartial 12 337997) = some ⟨12, 1, 0, 320864, 337997, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337997_320864 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337997 ⟨320864, by decide⟩ :=
  accepted_of_selected 12 337997 ⟨320864, by decide⟩ ⟨12, 1, 0, 320864, 337997, 1, 65536⟩
    (by decide) selected_cut_42443

theorem selected_cut_42444 : selected 9 ⟨1160053, by decide⟩
    (prefixPartial 12 337998) = some ⟨12, 2, 0, 1160053, 337998, 1669, 65536⟩ := by
  decide +kernel

theorem context_12_337998_1160053 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337998 ⟨1160053, by decide⟩ :=
  accepted_of_selected 12 337998 ⟨1160053, by decide⟩ ⟨12, 2, 0, 1160053, 337998, 1669, 65536⟩
    (by decide) selected_cut_42444

theorem selected_cut_42445 : selected 9 ⟨1160076, by decide⟩
    (prefixPartial 12 337999) = some ⟨12, 2, 0, 1160076, 337999, 1709, 65536⟩ := by
  decide +kernel

theorem context_12_337999_1160076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337999 ⟨1160076, by decide⟩ :=
  accepted_of_selected 12 337999 ⟨1160076, by decide⟩ ⟨12, 2, 0, 1160076, 337999, 1709, 65536⟩
    (by decide) selected_cut_42445

theorem unmarked_context_11_84499_1160077 : frontier 10 ⟨1160077, by decide⟩
    (prefixCache 11 84499) (prefixPartial 11 84499) = false := by
  decide +kernel

theorem node_context_11_84499_1160077 : EJMOriginalGlobalDAGData.nodes 10 ⟨1160077, by decide⟩ =
    .split (coordinate 11) (![⟨1160033, by decide⟩,⟨320864, by decide⟩,⟨1160053, by decide⟩,⟨1160076, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84499_1160077 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84499 ⟨1160077, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84499
    ⟨1160077, by decide⟩ (by decide) (![⟨1160033, by decide⟩,⟨320864, by decide⟩,⟨1160053, by decide⟩,⟨1160076, by decide⟩]) unmarked_context_11_84499_1160077 node_context_11_84499_1160077
  intro a
  fin_cases a
  · exact context_12_337996_1160033
  · exact context_12_337997_320864
  · exact context_12_337998_1160053
  · exact context_12_337999_1160076

theorem unmarked_context_10_21124_1160078 : frontier 11 ⟨1160078, by decide⟩
    (prefixCache 10 21124) (prefixPartial 10 21124) = false := by
  decide +kernel

theorem node_context_10_21124_1160078 : EJMOriginalGlobalDAGData.nodes 11 ⟨1160078, by decide⟩ =
    .split (coordinate 10) (![⟨1159893, by decide⟩,⟨1159965, by decide⟩,⟨1160016, by decide⟩,⟨1160077, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21124_1160078 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21124 ⟨1160078, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21124
    ⟨1160078, by decide⟩ (by decide) (![⟨1159893, by decide⟩,⟨1159965, by decide⟩,⟨1160016, by decide⟩,⟨1160077, by decide⟩]) unmarked_context_10_21124_1160078 node_context_10_21124_1160078
  intro a
  fin_cases a
  · exact context_11_84496_1159893
  · exact context_11_84497_1159965
  · exact context_11_84498_1160016
  · exact context_11_84499_1160077

theorem selected_cut_42446 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 21125) = some ⟨10, 1, 0, 893098, 21125, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_21125_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21125 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 21125 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 21125, 1, 1048576⟩
    (by decide) selected_cut_42446

theorem selected_cut_42447 : selected 9 ⟨985390, by decide⟩
    (prefixPartial 12 338016) = some ⟨12, 1, 0, 985390, 338016, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338016_985390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338016 ⟨985390, by decide⟩ :=
  accepted_of_selected 12 338016 ⟨985390, by decide⟩ ⟨12, 1, 0, 985390, 338016, 1, 65536⟩
    (by decide) selected_cut_42447

theorem selected_cut_42448 : selected 9 ⟨1160101, by decide⟩
    (prefixPartial 12 338017) = some ⟨12, 2, 0, 1160101, 338017, 1569, 65536⟩ := by
  decide +kernel

theorem context_12_338017_1160101 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338017 ⟨1160101, by decide⟩ :=
  accepted_of_selected 12 338017 ⟨1160101, by decide⟩ ⟨12, 2, 0, 1160101, 338017, 1569, 65536⟩
    (by decide) selected_cut_42448

theorem selected_cut_42449 : selected 9 ⟨1160123, by decide⟩
    (prefixPartial 12 338018) = some ⟨12, 2, 0, 1160123, 338018, 1589, 65536⟩ := by
  decide +kernel

theorem context_12_338018_1160123 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338018 ⟨1160123, by decide⟩ :=
  accepted_of_selected 12 338018 ⟨1160123, by decide⟩ ⟨12, 2, 0, 1160123, 338018, 1589, 65536⟩
    (by decide) selected_cut_42449

theorem selected_cut_42450 : selected 9 ⟨1160146, by decide⟩
    (prefixPartial 12 338019) = some ⟨12, 2, 0, 1160146, 338019, 1597, 65536⟩ := by
  decide +kernel

theorem context_12_338019_1160146 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338019 ⟨1160146, by decide⟩ :=
  accepted_of_selected 12 338019 ⟨1160146, by decide⟩ ⟨12, 2, 0, 1160146, 338019, 1597, 65536⟩
    (by decide) selected_cut_42450

theorem unmarked_context_11_84504_1160147 : frontier 10 ⟨1160147, by decide⟩
    (prefixCache 11 84504) (prefixPartial 11 84504) = false := by
  decide +kernel

theorem node_context_11_84504_1160147 : EJMOriginalGlobalDAGData.nodes 10 ⟨1160147, by decide⟩ =
    .split (coordinate 11) (![⟨985390, by decide⟩,⟨1160101, by decide⟩,⟨1160123, by decide⟩,⟨1160146, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84504_1160147 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84504 ⟨1160147, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84504
    ⟨1160147, by decide⟩ (by decide) (![⟨985390, by decide⟩,⟨1160101, by decide⟩,⟨1160123, by decide⟩,⟨1160146, by decide⟩]) unmarked_context_11_84504_1160147 node_context_11_84504_1160147
  intro a
  fin_cases a
  · exact context_12_338016_985390
  · exact context_12_338017_1160101
  · exact context_12_338018_1160123
  · exact context_12_338019_1160146

theorem selected_cut_42451 : selected 9 ⟨1160170, by decide⟩
    (prefixPartial 12 338020) = some ⟨12, 2, 0, 1160170, 338020, 1613, 65536⟩ := by
  decide +kernel

theorem context_12_338020_1160170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338020 ⟨1160170, by decide⟩ :=
  accepted_of_selected 12 338020 ⟨1160170, by decide⟩ ⟨12, 2, 0, 1160170, 338020, 1613, 65536⟩
    (by decide) selected_cut_42451

theorem selected_cut_42452 : selected 9 ⟨642794, by decide⟩
    (prefixPartial 12 338021) = some ⟨12, 1, 0, 642794, 338021, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338021_642794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338021 ⟨642794, by decide⟩ :=
  accepted_of_selected 12 338021 ⟨642794, by decide⟩ ⟨12, 1, 0, 642794, 338021, 1, 65536⟩
    (by decide) selected_cut_42452

theorem selected_cut_42453 : selected 9 ⟨1160197, by decide⟩
    (prefixPartial 12 338022) = some ⟨12, 2, 0, 1160197, 338022, 1609, 65536⟩ := by
  decide +kernel

theorem context_12_338022_1160197 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338022 ⟨1160197, by decide⟩ :=
  accepted_of_selected 12 338022 ⟨1160197, by decide⟩ ⟨12, 2, 0, 1160197, 338022, 1609, 65536⟩
    (by decide) selected_cut_42453

theorem selected_cut_42454 : selected 9 ⟨1160229, by decide⟩
    (prefixPartial 12 338023) = some ⟨12, 2, 0, 1160229, 338023, 1741, 65536⟩ := by
  decide +kernel

theorem context_12_338023_1160229 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338023 ⟨1160229, by decide⟩ :=
  accepted_of_selected 12 338023 ⟨1160229, by decide⟩ ⟨12, 2, 0, 1160229, 338023, 1741, 65536⟩
    (by decide) selected_cut_42454

theorem unmarked_context_11_84505_1160230 : frontier 10 ⟨1160230, by decide⟩
    (prefixCache 11 84505) (prefixPartial 11 84505) = false := by
  decide +kernel

theorem node_context_11_84505_1160230 : EJMOriginalGlobalDAGData.nodes 10 ⟨1160230, by decide⟩ =
    .split (coordinate 11) (![⟨1160170, by decide⟩,⟨642794, by decide⟩,⟨1160197, by decide⟩,⟨1160229, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84505_1160230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84505 ⟨1160230, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84505
    ⟨1160230, by decide⟩ (by decide) (![⟨1160170, by decide⟩,⟨642794, by decide⟩,⟨1160197, by decide⟩,⟨1160229, by decide⟩]) unmarked_context_11_84505_1160230 node_context_11_84505_1160230
  intro a
  fin_cases a
  · exact context_12_338020_1160170
  · exact context_12_338021_642794
  · exact context_12_338022_1160197
  · exact context_12_338023_1160229

theorem selected_cut_42455 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 84506) = some ⟨11, 1, 0, 900587, 84506, 1, 262144⟩ := by
  decide +kernel

theorem context_11_84506_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84506 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 84506 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 84506, 1, 262144⟩
    (by decide) selected_cut_42455

theorem selected_cut_42456 : selected 9 ⟨1160249, by decide⟩
    (prefixPartial 12 338028) = some ⟨12, 2, 0, 1160249, 338028, 1313, 65536⟩ := by
  decide +kernel

theorem context_12_338028_1160249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338028 ⟨1160249, by decide⟩ :=
  accepted_of_selected 12 338028 ⟨1160249, by decide⟩ ⟨12, 2, 0, 1160249, 338028, 1313, 65536⟩
    (by decide) selected_cut_42456

theorem selected_cut_42457 : selected 9 ⟨1160267, by decide⟩
    (prefixPartial 12 338029) = some ⟨12, 2, 0, 1160267, 338029, 1381, 65536⟩ := by
  decide +kernel

theorem context_12_338029_1160267 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338029 ⟨1160267, by decide⟩ :=
  accepted_of_selected 12 338029 ⟨1160267, by decide⟩ ⟨12, 2, 0, 1160267, 338029, 1381, 65536⟩
    (by decide) selected_cut_42457

theorem selected_cut_42458 : selected 9 ⟨1160284, by decide⟩
    (prefixPartial 12 338030) = some ⟨12, 2, 0, 1160284, 338030, 1441, 65536⟩ := by
  decide +kernel

theorem context_12_338030_1160284 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338030 ⟨1160284, by decide⟩ :=
  accepted_of_selected 12 338030 ⟨1160284, by decide⟩ ⟨12, 2, 0, 1160284, 338030, 1441, 65536⟩
    (by decide) selected_cut_42458

theorem selected_cut_42459 : selected 9 ⟨1160299, by decide⟩
    (prefixPartial 12 338031) = some ⟨12, 2, 0, 1160299, 338031, 1365, 65536⟩ := by
  decide +kernel

theorem context_12_338031_1160299 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338031 ⟨1160299, by decide⟩ :=
  accepted_of_selected 12 338031 ⟨1160299, by decide⟩ ⟨12, 2, 0, 1160299, 338031, 1365, 65536⟩
    (by decide) selected_cut_42459

theorem unmarked_context_11_84507_1160300 : frontier 10 ⟨1160300, by decide⟩
    (prefixCache 11 84507) (prefixPartial 11 84507) = false := by
  decide +kernel

theorem node_context_11_84507_1160300 : EJMOriginalGlobalDAGData.nodes 10 ⟨1160300, by decide⟩ =
    .split (coordinate 11) (![⟨1160249, by decide⟩,⟨1160267, by decide⟩,⟨1160284, by decide⟩,⟨1160299, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84507_1160300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84507 ⟨1160300, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84507
    ⟨1160300, by decide⟩ (by decide) (![⟨1160249, by decide⟩,⟨1160267, by decide⟩,⟨1160284, by decide⟩,⟨1160299, by decide⟩]) unmarked_context_11_84507_1160300 node_context_11_84507_1160300
  intro a
  fin_cases a
  · exact context_12_338028_1160249
  · exact context_12_338029_1160267
  · exact context_12_338030_1160284
  · exact context_12_338031_1160299

theorem unmarked_context_10_21126_1160301 : frontier 11 ⟨1160301, by decide⟩
    (prefixCache 10 21126) (prefixPartial 10 21126) = false := by
  decide +kernel

theorem node_context_10_21126_1160301 : EJMOriginalGlobalDAGData.nodes 11 ⟨1160301, by decide⟩ =
    .split (coordinate 10) (![⟨1160147, by decide⟩,⟨1160230, by decide⟩,⟨900587, by decide⟩,⟨1160300, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21126_1160301 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21126 ⟨1160301, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21126
    ⟨1160301, by decide⟩ (by decide) (![⟨1160147, by decide⟩,⟨1160230, by decide⟩,⟨900587, by decide⟩,⟨1160300, by decide⟩]) unmarked_context_10_21126_1160301 node_context_10_21126_1160301
  intro a
  fin_cases a
  · exact context_11_84504_1160147
  · exact context_11_84505_1160230
  · exact context_11_84506_900587
  · exact context_11_84507_1160300

theorem selected_cut_42460 : selected 9 ⟨985390, by decide⟩
    (prefixPartial 12 338032) = some ⟨12, 1, 0, 985390, 338032, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338032_985390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338032 ⟨985390, by decide⟩ :=
  accepted_of_selected 12 338032 ⟨985390, by decide⟩ ⟨12, 1, 0, 985390, 338032, 1, 65536⟩
    (by decide) selected_cut_42460

theorem selected_cut_42461 : selected 9 ⟨1160325, by decide⟩
    (prefixPartial 12 338033) = some ⟨12, 2, 0, 1160325, 338033, 1701, 65536⟩ := by
  decide +kernel

theorem context_12_338033_1160325 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338033 ⟨1160325, by decide⟩ :=
  accepted_of_selected 12 338033 ⟨1160325, by decide⟩ ⟨12, 2, 0, 1160325, 338033, 1701, 65536⟩
    (by decide) selected_cut_42461

theorem selected_cut_42462 : selected 9 ⟨1160357, by decide⟩
    (prefixPartial 12 338034) = some ⟨12, 2, 0, 1160357, 338034, 1841, 65536⟩ := by
  decide +kernel

theorem context_12_338034_1160357 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338034 ⟨1160357, by decide⟩ :=
  accepted_of_selected 12 338034 ⟨1160357, by decide⟩ ⟨12, 2, 0, 1160357, 338034, 1841, 65536⟩
    (by decide) selected_cut_42462

theorem selected_cut_42463 : selected 9 ⟨1160391, by decide⟩
    (prefixPartial 12 338035) = some ⟨12, 2, 0, 1160391, 338035, 1901, 65536⟩ := by
  decide +kernel

theorem context_12_338035_1160391 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338035 ⟨1160391, by decide⟩ :=
  accepted_of_selected 12 338035 ⟨1160391, by decide⟩ ⟨12, 2, 0, 1160391, 338035, 1901, 65536⟩
    (by decide) selected_cut_42463

theorem unmarked_context_11_84508_1160392 : frontier 10 ⟨1160392, by decide⟩
    (prefixCache 11 84508) (prefixPartial 11 84508) = false := by
  decide +kernel

theorem node_context_11_84508_1160392 : EJMOriginalGlobalDAGData.nodes 10 ⟨1160392, by decide⟩ =
    .split (coordinate 11) (![⟨985390, by decide⟩,⟨1160325, by decide⟩,⟨1160357, by decide⟩,⟨1160391, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84508_1160392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84508 ⟨1160392, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84508
    ⟨1160392, by decide⟩ (by decide) (![⟨985390, by decide⟩,⟨1160325, by decide⟩,⟨1160357, by decide⟩,⟨1160391, by decide⟩]) unmarked_context_11_84508_1160392 node_context_11_84508_1160392
  intro a
  fin_cases a
  · exact context_12_338032_985390
  · exact context_12_338033_1160325
  · exact context_12_338034_1160357
  · exact context_12_338035_1160391

theorem selected_cut_42464 : selected 9 ⟨1160416, by decide⟩
    (prefixPartial 12 338036) = some ⟨12, 2, 0, 1160416, 338036, 1637, 65536⟩ := by
  decide +kernel

theorem context_12_338036_1160416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338036 ⟨1160416, by decide⟩ :=
  accepted_of_selected 12 338036 ⟨1160416, by decide⟩ ⟨12, 2, 0, 1160416, 338036, 1637, 65536⟩
    (by decide) selected_cut_42464

theorem selected_cut_42465 : selected 9 ⟨642794, by decide⟩
    (prefixPartial 12 338037) = some ⟨12, 1, 0, 642794, 338037, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338037_642794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338037 ⟨642794, by decide⟩ :=
  accepted_of_selected 12 338037 ⟨642794, by decide⟩ ⟨12, 1, 0, 642794, 338037, 1, 65536⟩
    (by decide) selected_cut_42465

theorem selected_cut_42466 : selected 9 ⟨1160439, by decide⟩
    (prefixPartial 12 338038) = some ⟨12, 2, 0, 1160439, 338038, 1745, 65536⟩ := by
  decide +kernel

theorem context_12_338038_1160439 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338038 ⟨1160439, by decide⟩ :=
  accepted_of_selected 12 338038 ⟨1160439, by decide⟩ ⟨12, 2, 0, 1160439, 338038, 1745, 65536⟩
    (by decide) selected_cut_42466

theorem selected_cut_42467 : selected 9 ⟨1160473, by decide⟩
    (prefixPartial 12 338039) = some ⟨12, 2, 0, 1160473, 338039, 1933, 65536⟩ := by
  decide +kernel

theorem context_12_338039_1160473 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338039 ⟨1160473, by decide⟩ :=
  accepted_of_selected 12 338039 ⟨1160473, by decide⟩ ⟨12, 2, 0, 1160473, 338039, 1933, 65536⟩
    (by decide) selected_cut_42467

theorem unmarked_context_11_84509_1160474 : frontier 10 ⟨1160474, by decide⟩
    (prefixCache 11 84509) (prefixPartial 11 84509) = false := by
  decide +kernel

theorem node_context_11_84509_1160474 : EJMOriginalGlobalDAGData.nodes 10 ⟨1160474, by decide⟩ =
    .split (coordinate 11) (![⟨1160416, by decide⟩,⟨642794, by decide⟩,⟨1160439, by decide⟩,⟨1160473, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84509_1160474 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84509 ⟨1160474, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84509
    ⟨1160474, by decide⟩ (by decide) (![⟨1160416, by decide⟩,⟨642794, by decide⟩,⟨1160439, by decide⟩,⟨1160473, by decide⟩]) unmarked_context_11_84509_1160474 node_context_11_84509_1160474
  intro a
  fin_cases a
  · exact context_12_338036_1160416
  · exact context_12_338037_642794
  · exact context_12_338038_1160439
  · exact context_12_338039_1160473

theorem selected_cut_42468 : selected 9 ⟨1160492, by decide⟩
    (prefixPartial 12 338040) = some ⟨12, 2, 0, 1160492, 338040, 1321, 65536⟩ := by
  decide +kernel

theorem context_12_338040_1160492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338040 ⟨1160492, by decide⟩ :=
  accepted_of_selected 12 338040 ⟨1160492, by decide⟩ ⟨12, 2, 0, 1160492, 338040, 1321, 65536⟩
    (by decide) selected_cut_42468

theorem selected_cut_42469 : selected 9 ⟨1160508, by decide⟩
    (prefixPartial 12 338041) = some ⟨12, 2, 0, 1160508, 338041, 1429, 65536⟩ := by
  decide +kernel

theorem context_12_338041_1160508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338041 ⟨1160508, by decide⟩ :=
  accepted_of_selected 12 338041 ⟨1160508, by decide⟩ ⟨12, 2, 0, 1160508, 338041, 1429, 65536⟩
    (by decide) selected_cut_42469

theorem selected_cut_42470 : selected 9 ⟨1160529, by decide⟩
    (prefixPartial 12 338042) = some ⟨12, 2, 0, 1160529, 338042, 1481, 65536⟩ := by
  decide +kernel

theorem context_12_338042_1160529 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338042 ⟨1160529, by decide⟩ :=
  accepted_of_selected 12 338042 ⟨1160529, by decide⟩ ⟨12, 2, 0, 1160529, 338042, 1481, 65536⟩
    (by decide) selected_cut_42470

theorem selected_cut_42471 : selected 9 ⟨1160555, by decide⟩
    (prefixPartial 12 338043) = some ⟨12, 2, 0, 1160555, 338043, 1617, 65536⟩ := by
  decide +kernel

theorem context_12_338043_1160555 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338043 ⟨1160555, by decide⟩ :=
  accepted_of_selected 12 338043 ⟨1160555, by decide⟩ ⟨12, 2, 0, 1160555, 338043, 1617, 65536⟩
    (by decide) selected_cut_42471

theorem unmarked_context_11_84510_1160556 : frontier 10 ⟨1160556, by decide⟩
    (prefixCache 11 84510) (prefixPartial 11 84510) = false := by
  decide +kernel

theorem node_context_11_84510_1160556 : EJMOriginalGlobalDAGData.nodes 10 ⟨1160556, by decide⟩ =
    .split (coordinate 11) (![⟨1160492, by decide⟩,⟨1160508, by decide⟩,⟨1160529, by decide⟩,⟨1160555, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84510_1160556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84510 ⟨1160556, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84510
    ⟨1160556, by decide⟩ (by decide) (![⟨1160492, by decide⟩,⟨1160508, by decide⟩,⟨1160529, by decide⟩,⟨1160555, by decide⟩]) unmarked_context_11_84510_1160556 node_context_11_84510_1160556
  intro a
  fin_cases a
  · exact context_12_338040_1160492
  · exact context_12_338041_1160508
  · exact context_12_338042_1160529
  · exact context_12_338043_1160555

theorem selected_cut_42472 : selected 10 ⟨1160606, by decide⟩
    (prefixPartial 11 84511) = some ⟨11, 2, 0, 1160606, 84511, 3873, 262144⟩ := by
  decide +kernel

theorem context_11_84511_1160606 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84511 ⟨1160606, by decide⟩ :=
  accepted_of_selected 11 84511 ⟨1160606, by decide⟩ ⟨11, 2, 0, 1160606, 84511, 3873, 262144⟩
    (by decide) selected_cut_42472

theorem unmarked_context_10_21127_1160607 : frontier 11 ⟨1160607, by decide⟩
    (prefixCache 10 21127) (prefixPartial 10 21127) = false := by
  decide +kernel

theorem node_context_10_21127_1160607 : EJMOriginalGlobalDAGData.nodes 11 ⟨1160607, by decide⟩ =
    .split (coordinate 10) (![⟨1160392, by decide⟩,⟨1160474, by decide⟩,⟨1160556, by decide⟩,⟨1160606, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21127_1160607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21127 ⟨1160607, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21127
    ⟨1160607, by decide⟩ (by decide) (![⟨1160392, by decide⟩,⟨1160474, by decide⟩,⟨1160556, by decide⟩,⟨1160606, by decide⟩]) unmarked_context_10_21127_1160607 node_context_10_21127_1160607
  intro a
  fin_cases a
  · exact context_11_84508_1160392
  · exact context_11_84509_1160474
  · exact context_11_84510_1160556
  · exact context_11_84511_1160606

theorem unmarked_context_9_5281_1160608 : frontier 12 ⟨1160608, by decide⟩
    (prefixCache 9 5281) (prefixPartial 9 5281) = false := by
  decide +kernel

theorem node_context_9_5281_1160608 : EJMOriginalGlobalDAGData.nodes 12 ⟨1160608, by decide⟩ =
    .split (coordinate 9) (![⟨1160078, by decide⟩,⟨893098, by decide⟩,⟨1160301, by decide⟩,⟨1160607, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5281_1160608 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5281 ⟨1160608, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5281
    ⟨1160608, by decide⟩ (by decide) (![⟨1160078, by decide⟩,⟨893098, by decide⟩,⟨1160301, by decide⟩,⟨1160607, by decide⟩]) unmarked_context_9_5281_1160608 node_context_9_5281_1160608
  intro a
  fin_cases a
  · exact context_10_21124_1160078
  · exact context_10_21125_893098
  · exact context_10_21126_1160301
  · exact context_10_21127_1160607

theorem selected_cut_42473 : selected 10 ⟨1160647, by decide⟩
    (prefixPartial 11 84512) = some ⟨11, 2, 0, 1160647, 84512, 2625, 262144⟩ := by
  decide +kernel

theorem context_11_84512_1160647 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84512 ⟨1160647, by decide⟩ :=
  accepted_of_selected 11 84512 ⟨1160647, by decide⟩ ⟨11, 2, 0, 1160647, 84512, 2625, 262144⟩
    (by decide) selected_cut_42473

theorem selected_cut_42474 : selected 9 ⟨1160663, by decide⟩
    (prefixPartial 12 338052) = some ⟨12, 2, 0, 1160663, 338052, 1113, 65536⟩ := by
  decide +kernel

theorem context_12_338052_1160663 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338052 ⟨1160663, by decide⟩ :=
  accepted_of_selected 12 338052 ⟨1160663, by decide⟩ ⟨12, 2, 0, 1160663, 338052, 1113, 65536⟩
    (by decide) selected_cut_42474

theorem selected_cut_42475 : selected 9 ⟨1160682, by decide⟩
    (prefixPartial 12 338053) = some ⟨12, 2, 0, 1160682, 338053, 1297, 65536⟩ := by
  decide +kernel

theorem context_12_338053_1160682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338053 ⟨1160682, by decide⟩ :=
  accepted_of_selected 12 338053 ⟨1160682, by decide⟩ ⟨12, 2, 0, 1160682, 338053, 1297, 65536⟩
    (by decide) selected_cut_42475

theorem selected_cut_42476 : selected 9 ⟨1160699, by decide⟩
    (prefixPartial 12 338054) = some ⟨12, 2, 0, 1160699, 338054, 1305, 65536⟩ := by
  decide +kernel

theorem context_12_338054_1160699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338054 ⟨1160699, by decide⟩ :=
  accepted_of_selected 12 338054 ⟨1160699, by decide⟩ ⟨12, 2, 0, 1160699, 338054, 1305, 65536⟩
    (by decide) selected_cut_42476

theorem selected_cut_42477 : selected 9 ⟨1160720, by decide⟩
    (prefixPartial 12 338055) = some ⟨12, 2, 0, 1160720, 338055, 1337, 65536⟩ := by
  decide +kernel

theorem context_12_338055_1160720 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338055 ⟨1160720, by decide⟩ :=
  accepted_of_selected 12 338055 ⟨1160720, by decide⟩ ⟨12, 2, 0, 1160720, 338055, 1337, 65536⟩
    (by decide) selected_cut_42477

theorem unmarked_context_11_84513_1160721 : frontier 10 ⟨1160721, by decide⟩
    (prefixCache 11 84513) (prefixPartial 11 84513) = false := by
  decide +kernel

theorem node_context_11_84513_1160721 : EJMOriginalGlobalDAGData.nodes 10 ⟨1160721, by decide⟩ =
    .split (coordinate 11) (![⟨1160663, by decide⟩,⟨1160682, by decide⟩,⟨1160699, by decide⟩,⟨1160720, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84513_1160721 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84513 ⟨1160721, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84513
    ⟨1160721, by decide⟩ (by decide) (![⟨1160663, by decide⟩,⟨1160682, by decide⟩,⟨1160699, by decide⟩,⟨1160720, by decide⟩]) unmarked_context_11_84513_1160721 node_context_11_84513_1160721
  intro a
  fin_cases a
  · exact context_12_338052_1160663
  · exact context_12_338053_1160682
  · exact context_12_338054_1160699
  · exact context_12_338055_1160720

theorem selected_cut_42478 : selected 10 ⟨1160768, by decide⟩
    (prefixPartial 11 84514) = some ⟨11, 2, 0, 1160768, 84514, 3341, 262144⟩ := by
  decide +kernel

theorem context_11_84514_1160768 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84514 ⟨1160768, by decide⟩ :=
  accepted_of_selected 11 84514 ⟨1160768, by decide⟩ ⟨11, 2, 0, 1160768, 84514, 3341, 262144⟩
    (by decide) selected_cut_42478

theorem selected_cut_42479 : selected 9 ⟨1160776, by decide⟩
    (prefixPartial 12 338060) = some ⟨12, 2, 0, 1160776, 338060, 965, 65536⟩ := by
  decide +kernel

theorem context_12_338060_1160776 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338060 ⟨1160776, by decide⟩ :=
  accepted_of_selected 12 338060 ⟨1160776, by decide⟩ ⟨12, 2, 0, 1160776, 338060, 965, 65536⟩
    (by decide) selected_cut_42479

theorem selected_cut_42480 : selected 9 ⟨1160794, by decide⟩
    (prefixPartial 12 338061) = some ⟨12, 2, 0, 1160794, 338061, 1249, 65536⟩ := by
  decide +kernel

theorem context_12_338061_1160794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338061 ⟨1160794, by decide⟩ :=
  accepted_of_selected 12 338061 ⟨1160794, by decide⟩ ⟨12, 2, 0, 1160794, 338061, 1249, 65536⟩
    (by decide) selected_cut_42480

theorem selected_cut_42481 : selected 9 ⟨1160808, by decide⟩
    (prefixPartial 12 338062) = some ⟨12, 2, 0, 1160808, 338062, 1129, 65536⟩ := by
  decide +kernel

theorem context_12_338062_1160808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338062 ⟨1160808, by decide⟩ :=
  accepted_of_selected 12 338062 ⟨1160808, by decide⟩ ⟨12, 2, 0, 1160808, 338062, 1129, 65536⟩
    (by decide) selected_cut_42481

theorem selected_cut_42482 : selected 9 ⟨1160828, by decide⟩
    (prefixPartial 12 338063) = some ⟨12, 2, 0, 1160828, 338063, 1209, 65536⟩ := by
  decide +kernel

theorem context_12_338063_1160828 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338063 ⟨1160828, by decide⟩ :=
  accepted_of_selected 12 338063 ⟨1160828, by decide⟩ ⟨12, 2, 0, 1160828, 338063, 1209, 65536⟩
    (by decide) selected_cut_42482

theorem unmarked_context_11_84515_1160829 : frontier 10 ⟨1160829, by decide⟩
    (prefixCache 11 84515) (prefixPartial 11 84515) = false := by
  decide +kernel

theorem node_context_11_84515_1160829 : EJMOriginalGlobalDAGData.nodes 10 ⟨1160829, by decide⟩ =
    .split (coordinate 11) (![⟨1160776, by decide⟩,⟨1160794, by decide⟩,⟨1160808, by decide⟩,⟨1160828, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84515_1160829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84515 ⟨1160829, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84515
    ⟨1160829, by decide⟩ (by decide) (![⟨1160776, by decide⟩,⟨1160794, by decide⟩,⟨1160808, by decide⟩,⟨1160828, by decide⟩]) unmarked_context_11_84515_1160829 node_context_11_84515_1160829
  intro a
  fin_cases a
  · exact context_12_338060_1160776
  · exact context_12_338061_1160794
  · exact context_12_338062_1160808
  · exact context_12_338063_1160828

theorem unmarked_context_10_21128_1160830 : frontier 11 ⟨1160830, by decide⟩
    (prefixCache 10 21128) (prefixPartial 10 21128) = false := by
  decide +kernel

theorem node_context_10_21128_1160830 : EJMOriginalGlobalDAGData.nodes 11 ⟨1160830, by decide⟩ =
    .split (coordinate 10) (![⟨1160647, by decide⟩,⟨1160721, by decide⟩,⟨1160768, by decide⟩,⟨1160829, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21128_1160830 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21128 ⟨1160830, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21128
    ⟨1160830, by decide⟩ (by decide) (![⟨1160647, by decide⟩,⟨1160721, by decide⟩,⟨1160768, by decide⟩,⟨1160829, by decide⟩]) unmarked_context_10_21128_1160830 node_context_10_21128_1160830
  intro a
  fin_cases a
  · exact context_11_84512_1160647
  · exact context_11_84513_1160721
  · exact context_11_84514_1160768
  · exact context_11_84515_1160829

theorem selected_cut_42483 : selected 10 ⟨1160881, by decide⟩
    (prefixPartial 11 84516) = some ⟨11, 2, 0, 1160881, 84516, 3537, 262144⟩ := by
  decide +kernel

theorem context_11_84516_1160881 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84516 ⟨1160881, by decide⟩ :=
  accepted_of_selected 11 84516 ⟨1160881, by decide⟩ ⟨11, 2, 0, 1160881, 84516, 3537, 262144⟩
    (by decide) selected_cut_42483

theorem selected_cut_42484 : selected 10 ⟨1160921, by decide⟩
    (prefixPartial 11 84517) = some ⟨11, 2, 0, 1160921, 84517, 2193, 262144⟩ := by
  decide +kernel

theorem context_11_84517_1160921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84517 ⟨1160921, by decide⟩ :=
  accepted_of_selected 11 84517 ⟨1160921, by decide⟩ ⟨11, 2, 0, 1160921, 84517, 2193, 262144⟩
    (by decide) selected_cut_42484

theorem selected_cut_42485 : selected 10 ⟨1160973, by decide⟩
    (prefixPartial 11 84518) = some ⟨11, 2, 0, 1160973, 84518, 2861, 262144⟩ := by
  decide +kernel

theorem context_11_84518_1160973 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84518 ⟨1160973, by decide⟩ :=
  accepted_of_selected 11 84518 ⟨1160973, by decide⟩ ⟨11, 2, 0, 1160973, 84518, 2861, 262144⟩
    (by decide) selected_cut_42485

theorem selected_cut_42486 : selected 10 ⟨1161029, by decide⟩
    (prefixPartial 11 84519) = some ⟨11, 2, 0, 1161029, 84519, 3685, 262144⟩ := by
  decide +kernel

theorem context_11_84519_1161029 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84519 ⟨1161029, by decide⟩ :=
  accepted_of_selected 11 84519 ⟨1161029, by decide⟩ ⟨11, 2, 0, 1161029, 84519, 3685, 262144⟩
    (by decide) selected_cut_42486

theorem unmarked_context_10_21129_1161030 : frontier 11 ⟨1161030, by decide⟩
    (prefixCache 10 21129) (prefixPartial 10 21129) = false := by
  decide +kernel

theorem node_context_10_21129_1161030 : EJMOriginalGlobalDAGData.nodes 11 ⟨1161030, by decide⟩ =
    .split (coordinate 10) (![⟨1160881, by decide⟩,⟨1160921, by decide⟩,⟨1160973, by decide⟩,⟨1161029, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21129_1161030 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21129 ⟨1161030, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21129
    ⟨1161030, by decide⟩ (by decide) (![⟨1160881, by decide⟩,⟨1160921, by decide⟩,⟨1160973, by decide⟩,⟨1161029, by decide⟩]) unmarked_context_10_21129_1161030 node_context_10_21129_1161030
  intro a
  fin_cases a
  · exact context_11_84516_1160881
  · exact context_11_84517_1160921
  · exact context_11_84518_1160973
  · exact context_11_84519_1161029

theorem selected_cut_42487 : selected 10 ⟨1161051, by decide⟩
    (prefixPartial 11 84520) = some ⟨11, 2, 0, 1161051, 84520, 1633, 262144⟩ := by
  decide +kernel

theorem context_11_84520_1161051 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84520 ⟨1161051, by decide⟩ :=
  accepted_of_selected 11 84520 ⟨1161051, by decide⟩ ⟨11, 2, 0, 1161051, 84520, 1633, 262144⟩
    (by decide) selected_cut_42487

theorem selected_cut_42488 : selected 10 ⟨1161088, by decide⟩
    (prefixPartial 11 84521) = some ⟨11, 2, 0, 1161088, 84521, 1769, 262144⟩ := by
  decide +kernel

theorem context_11_84521_1161088 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84521 ⟨1161088, by decide⟩ :=
  accepted_of_selected 11 84521 ⟨1161088, by decide⟩ ⟨11, 2, 0, 1161088, 84521, 1769, 262144⟩
    (by decide) selected_cut_42488

theorem selected_cut_42489 : selected 10 ⟨1109453, by decide⟩
    (prefixPartial 11 84522) = some ⟨11, 1, 0, 1109453, 84522, 1, 262144⟩ := by
  decide +kernel

theorem context_11_84522_1109453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84522 ⟨1109453, by decide⟩ :=
  accepted_of_selected 11 84522 ⟨1109453, by decide⟩ ⟨11, 1, 0, 1109453, 84522, 1, 262144⟩
    (by decide) selected_cut_42489

theorem selected_cut_42490 : selected 10 ⟨1161122, by decide⟩
    (prefixPartial 11 84523) = some ⟨11, 2, 0, 1161122, 84523, 2361, 262144⟩ := by
  decide +kernel

theorem context_11_84523_1161122 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84523 ⟨1161122, by decide⟩ :=
  accepted_of_selected 11 84523 ⟨1161122, by decide⟩ ⟨11, 2, 0, 1161122, 84523, 2361, 262144⟩
    (by decide) selected_cut_42490

theorem unmarked_context_10_21130_1161123 : frontier 11 ⟨1161123, by decide⟩
    (prefixCache 10 21130) (prefixPartial 10 21130) = false := by
  decide +kernel

theorem node_context_10_21130_1161123 : EJMOriginalGlobalDAGData.nodes 11 ⟨1161123, by decide⟩ =
    .split (coordinate 10) (![⟨1161051, by decide⟩,⟨1161088, by decide⟩,⟨1109453, by decide⟩,⟨1161122, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21130_1161123 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21130 ⟨1161123, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21130
    ⟨1161123, by decide⟩ (by decide) (![⟨1161051, by decide⟩,⟨1161088, by decide⟩,⟨1109453, by decide⟩,⟨1161122, by decide⟩]) unmarked_context_10_21130_1161123 node_context_10_21130_1161123
  intro a
  fin_cases a
  · exact context_11_84520_1161051
  · exact context_11_84521_1161088
  · exact context_11_84522_1109453
  · exact context_11_84523_1161122

theorem selected_cut_42491 : selected 10 ⟨1161160, by decide⟩
    (prefixPartial 11 84524) = some ⟨11, 2, 0, 1161160, 84524, 2521, 262144⟩ := by
  decide +kernel

theorem context_11_84524_1161160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84524 ⟨1161160, by decide⟩ :=
  accepted_of_selected 11 84524 ⟨1161160, by decide⟩ ⟨11, 2, 0, 1161160, 84524, 2521, 262144⟩
    (by decide) selected_cut_42491

theorem selected_cut_42492 : selected 10 ⟨1161220, by decide⟩
    (prefixPartial 11 84525) = some ⟨11, 2, 0, 1161220, 84525, 3317, 262144⟩ := by
  decide +kernel

theorem context_11_84525_1161220 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84525 ⟨1161220, by decide⟩ :=
  accepted_of_selected 11 84525 ⟨1161220, by decide⟩ ⟨11, 2, 0, 1161220, 84525, 3317, 262144⟩
    (by decide) selected_cut_42492

theorem selected_cut_42493 : selected 10 ⟨1161252, by decide⟩
    (prefixPartial 11 84526) = some ⟨11, 2, 0, 1161252, 84526, 1917, 262144⟩ := by
  decide +kernel

theorem context_11_84526_1161252 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84526 ⟨1161252, by decide⟩ :=
  accepted_of_selected 11 84526 ⟨1161252, by decide⟩ ⟨11, 2, 0, 1161252, 84526, 1917, 262144⟩
    (by decide) selected_cut_42493

theorem selected_cut_42494 : selected 10 ⟨1161278, by decide⟩
    (prefixPartial 11 84527) = some ⟨11, 2, 0, 1161278, 84527, 1769, 262144⟩ := by
  decide +kernel

theorem context_11_84527_1161278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84527 ⟨1161278, by decide⟩ :=
  accepted_of_selected 11 84527 ⟨1161278, by decide⟩ ⟨11, 2, 0, 1161278, 84527, 1769, 262144⟩
    (by decide) selected_cut_42494

theorem unmarked_context_10_21131_1161279 : frontier 11 ⟨1161279, by decide⟩
    (prefixCache 10 21131) (prefixPartial 10 21131) = false := by
  decide +kernel

theorem node_context_10_21131_1161279 : EJMOriginalGlobalDAGData.nodes 11 ⟨1161279, by decide⟩ =
    .split (coordinate 10) (![⟨1161160, by decide⟩,⟨1161220, by decide⟩,⟨1161252, by decide⟩,⟨1161278, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21131_1161279 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21131 ⟨1161279, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21131
    ⟨1161279, by decide⟩ (by decide) (![⟨1161160, by decide⟩,⟨1161220, by decide⟩,⟨1161252, by decide⟩,⟨1161278, by decide⟩]) unmarked_context_10_21131_1161279 node_context_10_21131_1161279
  intro a
  fin_cases a
  · exact context_11_84524_1161160
  · exact context_11_84525_1161220
  · exact context_11_84526_1161252
  · exact context_11_84527_1161278

theorem unmarked_context_9_5282_1161280 : frontier 12 ⟨1161280, by decide⟩
    (prefixCache 9 5282) (prefixPartial 9 5282) = false := by
  decide +kernel

theorem node_context_9_5282_1161280 : EJMOriginalGlobalDAGData.nodes 12 ⟨1161280, by decide⟩ =
    .split (coordinate 9) (![⟨1160830, by decide⟩,⟨1161030, by decide⟩,⟨1161123, by decide⟩,⟨1161279, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5282_1161280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5282 ⟨1161280, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5282
    ⟨1161280, by decide⟩ (by decide) (![⟨1160830, by decide⟩,⟨1161030, by decide⟩,⟨1161123, by decide⟩,⟨1161279, by decide⟩]) unmarked_context_9_5282_1161280 node_context_9_5282_1161280
  intro a
  fin_cases a
  · exact context_10_21128_1160830
  · exact context_10_21129_1161030
  · exact context_10_21130_1161123
  · exact context_10_21131_1161279

theorem selected_cut_42495 : selected 10 ⟨1161297, by decide⟩
    (prefixPartial 11 84528) = some ⟨11, 2, 0, 1161297, 84528, 1581, 262144⟩ := by
  decide +kernel

theorem context_11_84528_1161297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84528 ⟨1161297, by decide⟩ :=
  accepted_of_selected 11 84528 ⟨1161297, by decide⟩ ⟨11, 2, 0, 1161297, 84528, 1581, 262144⟩
    (by decide) selected_cut_42495

theorem selected_cut_42496 : selected 10 ⟨1161319, by decide⟩
    (prefixPartial 11 84529) = some ⟨11, 2, 0, 1161319, 84529, 1861, 262144⟩ := by
  decide +kernel

theorem context_11_84529_1161319 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84529 ⟨1161319, by decide⟩ :=
  accepted_of_selected 11 84529 ⟨1161319, by decide⟩ ⟨11, 2, 0, 1161319, 84529, 1861, 262144⟩
    (by decide) selected_cut_42496

theorem selected_cut_42497 : selected 10 ⟨1161334, by decide⟩
    (prefixPartial 11 84530) = some ⟨11, 2, 0, 1161334, 84530, 1197, 262144⟩ := by
  decide +kernel

theorem context_11_84530_1161334 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84530 ⟨1161334, by decide⟩ :=
  accepted_of_selected 11 84530 ⟨1161334, by decide⟩ ⟨11, 2, 0, 1161334, 84530, 1197, 262144⟩
    (by decide) selected_cut_42497

theorem selected_cut_42498 : selected 10 ⟨1161352, by decide⟩
    (prefixPartial 11 84531) = some ⟨11, 2, 0, 1161352, 84531, 1289, 262144⟩ := by
  decide +kernel

theorem context_11_84531_1161352 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84531 ⟨1161352, by decide⟩ :=
  accepted_of_selected 11 84531 ⟨1161352, by decide⟩ ⟨11, 2, 0, 1161352, 84531, 1289, 262144⟩
    (by decide) selected_cut_42498

theorem unmarked_context_10_21132_1161353 : frontier 11 ⟨1161353, by decide⟩
    (prefixCache 10 21132) (prefixPartial 10 21132) = false := by
  decide +kernel

theorem node_context_10_21132_1161353 : EJMOriginalGlobalDAGData.nodes 11 ⟨1161353, by decide⟩ =
    .split (coordinate 10) (![⟨1161297, by decide⟩,⟨1161319, by decide⟩,⟨1161334, by decide⟩,⟨1161352, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21132_1161353 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21132 ⟨1161353, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21132
    ⟨1161353, by decide⟩ (by decide) (![⟨1161297, by decide⟩,⟨1161319, by decide⟩,⟨1161334, by decide⟩,⟨1161352, by decide⟩]) unmarked_context_10_21132_1161353 node_context_10_21132_1161353
  intro a
  fin_cases a
  · exact context_11_84528_1161297
  · exact context_11_84529_1161319
  · exact context_11_84530_1161334
  · exact context_11_84531_1161352

theorem selected_cut_42499 : selected 11 ⟨1161398, by decide⟩
    (prefixPartial 10 21133) = some ⟨10, 2, 0, 1161398, 21133, 3797, 1048576⟩ := by
  decide +kernel

theorem context_10_21133_1161398 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21133 ⟨1161398, by decide⟩ :=
  accepted_of_selected 10 21133 ⟨1161398, by decide⟩ ⟨10, 2, 0, 1161398, 21133, 3797, 1048576⟩
    (by decide) selected_cut_42499

theorem selected_cut_42500 : selected 11 ⟨1161427, by decide⟩
    (prefixPartial 10 21134) = some ⟨10, 2, 0, 1161427, 21134, 1565, 1048576⟩ := by
  decide +kernel

theorem context_10_21134_1161427 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21134 ⟨1161427, by decide⟩ :=
  accepted_of_selected 10 21134 ⟨1161427, by decide⟩ ⟨10, 2, 0, 1161427, 21134, 1565, 1048576⟩
    (by decide) selected_cut_42500

theorem selected_cut_42501 : selected 11 ⟨1161433, by decide⟩
    (prefixPartial 10 21135) = some ⟨10, 2, 0, 1161433, 21135, 493, 1048576⟩ := by
  decide +kernel

theorem context_10_21135_1161433 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21135 ⟨1161433, by decide⟩ :=
  accepted_of_selected 10 21135 ⟨1161433, by decide⟩ ⟨10, 2, 0, 1161433, 21135, 493, 1048576⟩
    (by decide) selected_cut_42501

theorem unmarked_context_9_5283_1161434 : frontier 12 ⟨1161434, by decide⟩
    (prefixCache 9 5283) (prefixPartial 9 5283) = false := by
  decide +kernel

theorem node_context_9_5283_1161434 : EJMOriginalGlobalDAGData.nodes 12 ⟨1161434, by decide⟩ =
    .split (coordinate 9) (![⟨1161353, by decide⟩,⟨1161398, by decide⟩,⟨1161427, by decide⟩,⟨1161433, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5283_1161434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5283 ⟨1161434, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5283
    ⟨1161434, by decide⟩ (by decide) (![⟨1161353, by decide⟩,⟨1161398, by decide⟩,⟨1161427, by decide⟩,⟨1161433, by decide⟩]) unmarked_context_9_5283_1161434 node_context_9_5283_1161434
  intro a
  fin_cases a
  · exact context_10_21132_1161353
  · exact context_10_21133_1161398
  · exact context_10_21134_1161427
  · exact context_10_21135_1161433

theorem unmarked_context_8_1320_1161435 : frontier 13 ⟨1161435, by decide⟩
    (prefixCache 8 1320) (prefixPartial 8 1320) = false := by
  decide +kernel

theorem node_context_8_1320_1161435 : EJMOriginalGlobalDAGData.nodes 13 ⟨1161435, by decide⟩ =
    .split (coordinate 8) (![⟨1159816, by decide⟩,⟨1160608, by decide⟩,⟨1161280, by decide⟩,⟨1161434, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1320_1161435 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1320 ⟨1161435, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1320
    ⟨1161435, by decide⟩ (by decide) (![⟨1159816, by decide⟩,⟨1160608, by decide⟩,⟨1161280, by decide⟩,⟨1161434, by decide⟩]) unmarked_context_8_1320_1161435 node_context_8_1320_1161435
  intro a
  fin_cases a
  · exact context_9_5280_1159816
  · exact context_9_5281_1160608
  · exact context_9_5282_1161280
  · exact context_9_5283_1161434

theorem selected_cut_42502 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 84544) = some ⟨11, 1, 0, 434745, 84544, 1, 262144⟩ := by
  decide +kernel

theorem context_11_84544_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84544 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 84544 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 84544, 1, 262144⟩
    (by decide) selected_cut_42502

theorem selected_cut_42503 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 338180) = some ⟨12, 1, 0, 448748, 338180, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338180_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338180 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 338180 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 338180, 1, 65536⟩
    (by decide) selected_cut_42503

theorem selected_cut_42504 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 338181) = some ⟨12, 1, 0, 34034, 338181, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338181_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338181 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 338181 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 338181, 1, 65536⟩
    (by decide) selected_cut_42504

theorem selected_cut_42505 : selected 9 ⟨1161480, by decide⟩
    (prefixPartial 12 338182) = some ⟨12, 2, 0, 1161480, 338182, 2569, 65536⟩ := by
  decide +kernel

theorem context_12_338182_1161480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338182 ⟨1161480, by decide⟩ :=
  accepted_of_selected 12 338182 ⟨1161480, by decide⟩ ⟨12, 2, 0, 1161480, 338182, 2569, 65536⟩
    (by decide) selected_cut_42505

theorem selected_cut_42506 : selected 9 ⟨1161523, by decide⟩
    (prefixPartial 12 338183) = some ⟨12, 2, 0, 1161523, 338183, 2657, 65536⟩ := by
  decide +kernel

theorem context_12_338183_1161523 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338183 ⟨1161523, by decide⟩ :=
  accepted_of_selected 12 338183 ⟨1161523, by decide⟩ ⟨12, 2, 0, 1161523, 338183, 2657, 65536⟩
    (by decide) selected_cut_42506

theorem unmarked_context_11_84545_1161524 : frontier 10 ⟨1161524, by decide⟩
    (prefixCache 11 84545) (prefixPartial 11 84545) = false := by
  decide +kernel

theorem node_context_11_84545_1161524 : EJMOriginalGlobalDAGData.nodes 10 ⟨1161524, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1161480, by decide⟩,⟨1161523, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84545_1161524 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84545 ⟨1161524, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84545
    ⟨1161524, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1161480, by decide⟩,⟨1161523, by decide⟩]) unmarked_context_11_84545_1161524 node_context_11_84545_1161524
  intro a
  fin_cases a
  · exact context_12_338180_448748
  · exact context_12_338181_34034
  · exact context_12_338182_1161480
  · exact context_12_338183_1161523

theorem selected_cut_42507 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 338184) = some ⟨12, 1, 0, 448748, 338184, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338184_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338184 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 338184 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 338184, 1, 65536⟩
    (by decide) selected_cut_42507

theorem selected_cut_42508 : selected 9 ⟨1161578, by decide⟩
    (prefixPartial 12 338185) = some ⟨12, 2, 0, 1161578, 338185, 2829, 65536⟩ := by
  decide +kernel

theorem context_12_338185_1161578 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338185 ⟨1161578, by decide⟩ :=
  accepted_of_selected 12 338185 ⟨1161578, by decide⟩ ⟨12, 2, 0, 1161578, 338185, 2829, 65536⟩
    (by decide) selected_cut_42508

theorem selected_cut_42509 : selected 9 ⟨1161621, by decide⟩
    (prefixPartial 12 338186) = some ⟨12, 2, 0, 1161621, 338186, 2477, 65536⟩ := by
  decide +kernel

theorem context_12_338186_1161621 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338186 ⟨1161621, by decide⟩ :=
  accepted_of_selected 12 338186 ⟨1161621, by decide⟩ ⟨12, 2, 0, 1161621, 338186, 2477, 65536⟩
    (by decide) selected_cut_42509

theorem selected_cut_42510 : selected 9 ⟨1161656, by decide⟩
    (prefixPartial 12 338187) = some ⟨12, 2, 0, 1161656, 338187, 2365, 65536⟩ := by
  decide +kernel

theorem context_12_338187_1161656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338187 ⟨1161656, by decide⟩ :=
  accepted_of_selected 12 338187 ⟨1161656, by decide⟩ ⟨12, 2, 0, 1161656, 338187, 2365, 65536⟩
    (by decide) selected_cut_42510

theorem unmarked_context_11_84546_1161657 : frontier 10 ⟨1161657, by decide⟩
    (prefixCache 11 84546) (prefixPartial 11 84546) = false := by
  decide +kernel

theorem node_context_11_84546_1161657 : EJMOriginalGlobalDAGData.nodes 10 ⟨1161657, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1161578, by decide⟩,⟨1161621, by decide⟩,⟨1161656, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84546_1161657 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84546 ⟨1161657, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84546
    ⟨1161657, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1161578, by decide⟩,⟨1161621, by decide⟩,⟨1161656, by decide⟩]) unmarked_context_11_84546_1161657 node_context_11_84546_1161657
  intro a
  fin_cases a
  · exact context_12_338184_448748
  · exact context_12_338185_1161578
  · exact context_12_338186_1161621
  · exact context_12_338187_1161656

theorem selected_cut_42511 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 338188) = some ⟨12, 1, 0, 448748, 338188, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338188_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338188 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 338188 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 338188, 1, 65536⟩
    (by decide) selected_cut_42511

theorem selected_cut_42512 : selected 9 ⟨1161691, by decide⟩
    (prefixPartial 12 338189) = some ⟨12, 2, 0, 1161691, 338189, 2581, 65536⟩ := by
  decide +kernel

theorem context_12_338189_1161691 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338189 ⟨1161691, by decide⟩ :=
  accepted_of_selected 12 338189 ⟨1161691, by decide⟩ ⟨12, 2, 0, 1161691, 338189, 2581, 65536⟩
    (by decide) selected_cut_42512

theorem selected_cut_42513 : selected 9 ⟨1161729, by decide⟩
    (prefixPartial 12 338190) = some ⟨12, 2, 0, 1161729, 338190, 2433, 65536⟩ := by
  decide +kernel

theorem context_12_338190_1161729 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338190 ⟨1161729, by decide⟩ :=
  accepted_of_selected 12 338190 ⟨1161729, by decide⟩ ⟨12, 2, 0, 1161729, 338190, 2433, 65536⟩
    (by decide) selected_cut_42513

theorem selected_cut_42514 : selected 9 ⟨1161764, by decide⟩
    (prefixPartial 12 338191) = some ⟨12, 2, 0, 1161764, 338191, 2465, 65536⟩ := by
  decide +kernel

theorem context_12_338191_1161764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338191 ⟨1161764, by decide⟩ :=
  accepted_of_selected 12 338191 ⟨1161764, by decide⟩ ⟨12, 2, 0, 1161764, 338191, 2465, 65536⟩
    (by decide) selected_cut_42514

theorem unmarked_context_11_84547_1161765 : frontier 10 ⟨1161765, by decide⟩
    (prefixCache 11 84547) (prefixPartial 11 84547) = false := by
  decide +kernel

theorem node_context_11_84547_1161765 : EJMOriginalGlobalDAGData.nodes 10 ⟨1161765, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1161691, by decide⟩,⟨1161729, by decide⟩,⟨1161764, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84547_1161765 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84547 ⟨1161765, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84547
    ⟨1161765, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1161691, by decide⟩,⟨1161729, by decide⟩,⟨1161764, by decide⟩]) unmarked_context_11_84547_1161765 node_context_11_84547_1161765
  intro a
  fin_cases a
  · exact context_12_338188_448748
  · exact context_12_338189_1161691
  · exact context_12_338190_1161729
  · exact context_12_338191_1161764

theorem unmarked_context_10_21136_1161766 : frontier 11 ⟨1161766, by decide⟩
    (prefixCache 10 21136) (prefixPartial 10 21136) = false := by
  decide +kernel

theorem node_context_10_21136_1161766 : EJMOriginalGlobalDAGData.nodes 11 ⟨1161766, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨1161524, by decide⟩,⟨1161657, by decide⟩,⟨1161765, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21136_1161766 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21136 ⟨1161766, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21136
    ⟨1161766, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨1161524, by decide⟩,⟨1161657, by decide⟩,⟨1161765, by decide⟩]) unmarked_context_10_21136_1161766 node_context_10_21136_1161766
  intro a
  fin_cases a
  · exact context_11_84544_434745
  · exact context_11_84545_1161524
  · exact context_11_84546_1161657
  · exact context_11_84547_1161765

theorem selected_cut_42515 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 338192) = some ⟨12, 1, 0, 1108174, 338192, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338192_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338192 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 338192 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 338192, 1, 65536⟩
    (by decide) selected_cut_42515

theorem selected_cut_42516 : selected 9 ⟨1161823, by decide⟩
    (prefixPartial 12 338193) = some ⟨12, 2, 0, 1161823, 338193, 2989, 65536⟩ := by
  decide +kernel

theorem context_12_338193_1161823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338193 ⟨1161823, by decide⟩ :=
  accepted_of_selected 12 338193 ⟨1161823, by decide⟩ ⟨12, 2, 0, 1161823, 338193, 2989, 65536⟩
    (by decide) selected_cut_42516

theorem selected_cut_42517 : selected 9 ⟨1161867, by decide⟩
    (prefixPartial 12 338194) = some ⟨12, 2, 0, 1161867, 338194, 2785, 65536⟩ := by
  decide +kernel

theorem context_12_338194_1161867 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338194 ⟨1161867, by decide⟩ :=
  accepted_of_selected 12 338194 ⟨1161867, by decide⟩ ⟨12, 2, 0, 1161867, 338194, 2785, 65536⟩
    (by decide) selected_cut_42517

theorem selected_cut_42518 : selected 9 ⟨1161913, by decide⟩
    (prefixPartial 12 338195) = some ⟨12, 2, 0, 1161913, 338195, 2689, 65536⟩ := by
  decide +kernel

theorem context_12_338195_1161913 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338195 ⟨1161913, by decide⟩ :=
  accepted_of_selected 12 338195 ⟨1161913, by decide⟩ ⟨12, 2, 0, 1161913, 338195, 2689, 65536⟩
    (by decide) selected_cut_42518

theorem unmarked_context_11_84548_1161914 : frontier 10 ⟨1161914, by decide⟩
    (prefixCache 11 84548) (prefixPartial 11 84548) = false := by
  decide +kernel

theorem node_context_11_84548_1161914 : EJMOriginalGlobalDAGData.nodes 10 ⟨1161914, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1161823, by decide⟩,⟨1161867, by decide⟩,⟨1161913, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84548_1161914 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84548 ⟨1161914, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84548
    ⟨1161914, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1161823, by decide⟩,⟨1161867, by decide⟩,⟨1161913, by decide⟩]) unmarked_context_11_84548_1161914 node_context_11_84548_1161914
  intro a
  fin_cases a
  · exact context_12_338192_1108174
  · exact context_12_338193_1161823
  · exact context_12_338194_1161867
  · exact context_12_338195_1161913

theorem selected_cut_42519 : selected 10 ⟨1161962, by decide⟩
    (prefixPartial 11 84549) = some ⟨11, 2, 0, 1161962, 84549, 2657, 262144⟩ := by
  decide +kernel

theorem context_11_84549_1161962 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84549 ⟨1161962, by decide⟩ :=
  accepted_of_selected 11 84549 ⟨1161962, by decide⟩ ⟨11, 2, 0, 1161962, 84549, 2657, 262144⟩
    (by decide) selected_cut_42519

theorem selected_cut_42520 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 338200) = some ⟨12, 1, 0, 1108174, 338200, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338200_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338200 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 338200 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 338200, 1, 65536⟩
    (by decide) selected_cut_42520

theorem selected_cut_42521 : selected 9 ⟨1162002, by decide⟩
    (prefixPartial 12 338201) = some ⟨12, 2, 0, 1162002, 338201, 2453, 65536⟩ := by
  decide +kernel

theorem context_12_338201_1162002 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338201 ⟨1162002, by decide⟩ :=
  accepted_of_selected 12 338201 ⟨1162002, by decide⟩ ⟨12, 2, 0, 1162002, 338201, 2453, 65536⟩
    (by decide) selected_cut_42521

theorem selected_cut_42522 : selected 9 ⟨1162066, by decide⟩
    (prefixPartial 12 338202) = some ⟨12, 2, 0, 1162066, 338202, 1501, 65536⟩ := by
  decide +kernel

theorem context_12_338202_1162066 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338202 ⟨1162066, by decide⟩ :=
  accepted_of_selected 12 338202 ⟨1162066, by decide⟩ ⟨12, 2, 0, 1162066, 338202, 1501, 65536⟩
    (by decide) selected_cut_42522

theorem selected_cut_42523 : selected 9 ⟨1162091, by decide⟩
    (prefixPartial 12 338203) = some ⟨12, 2, 0, 1162091, 338203, 2245, 65536⟩ := by
  decide +kernel

theorem context_12_338203_1162091 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338203 ⟨1162091, by decide⟩ :=
  accepted_of_selected 12 338203 ⟨1162091, by decide⟩ ⟨12, 2, 0, 1162091, 338203, 2245, 65536⟩
    (by decide) selected_cut_42523

theorem unmarked_context_11_84550_1162092 : frontier 10 ⟨1162092, by decide⟩
    (prefixCache 11 84550) (prefixPartial 11 84550) = false := by
  decide +kernel

theorem node_context_11_84550_1162092 : EJMOriginalGlobalDAGData.nodes 10 ⟨1162092, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1162002, by decide⟩,⟨1162066, by decide⟩,⟨1162091, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84550_1162092 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84550 ⟨1162092, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84550
    ⟨1162092, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1162002, by decide⟩,⟨1162066, by decide⟩,⟨1162091, by decide⟩]) unmarked_context_11_84550_1162092 node_context_11_84550_1162092
  intro a
  fin_cases a
  · exact context_12_338200_1108174
  · exact context_12_338201_1162002
  · exact context_12_338202_1162066
  · exact context_12_338203_1162091

theorem selected_cut_42524 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 338204) = some ⟨12, 1, 0, 1108174, 338204, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338204_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338204 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 338204 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 338204, 1, 65536⟩
    (by decide) selected_cut_42524

theorem selected_cut_42525 : selected 9 ⟨1162117, by decide⟩
    (prefixPartial 12 338205) = some ⟨12, 2, 0, 1162117, 338205, 2217, 65536⟩ := by
  decide +kernel

theorem context_12_338205_1162117 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338205 ⟨1162117, by decide⟩ :=
  accepted_of_selected 12 338205 ⟨1162117, by decide⟩ ⟨12, 2, 0, 1162117, 338205, 2217, 65536⟩
    (by decide) selected_cut_42525

theorem selected_cut_42526 : selected 9 ⟨1162145, by decide⟩
    (prefixPartial 12 338206) = some ⟨12, 2, 0, 1162145, 338206, 2305, 65536⟩ := by
  decide +kernel

theorem context_12_338206_1162145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338206 ⟨1162145, by decide⟩ :=
  accepted_of_selected 12 338206 ⟨1162145, by decide⟩ ⟨12, 2, 0, 1162145, 338206, 2305, 65536⟩
    (by decide) selected_cut_42526

theorem selected_cut_42527 : selected 9 ⟨1162181, by decide⟩
    (prefixPartial 12 338207) = some ⟨12, 2, 0, 1162181, 338207, 2289, 65536⟩ := by
  decide +kernel

theorem context_12_338207_1162181 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338207 ⟨1162181, by decide⟩ :=
  accepted_of_selected 12 338207 ⟨1162181, by decide⟩ ⟨12, 2, 0, 1162181, 338207, 2289, 65536⟩
    (by decide) selected_cut_42527

theorem unmarked_context_11_84551_1162182 : frontier 10 ⟨1162182, by decide⟩
    (prefixCache 11 84551) (prefixPartial 11 84551) = false := by
  decide +kernel

theorem node_context_11_84551_1162182 : EJMOriginalGlobalDAGData.nodes 10 ⟨1162182, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1162117, by decide⟩,⟨1162145, by decide⟩,⟨1162181, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84551_1162182 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84551 ⟨1162182, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84551
    ⟨1162182, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1162117, by decide⟩,⟨1162145, by decide⟩,⟨1162181, by decide⟩]) unmarked_context_11_84551_1162182 node_context_11_84551_1162182
  intro a
  fin_cases a
  · exact context_12_338204_1108174
  · exact context_12_338205_1162117
  · exact context_12_338206_1162145
  · exact context_12_338207_1162181

theorem unmarked_context_10_21137_1162183 : frontier 11 ⟨1162183, by decide⟩
    (prefixCache 10 21137) (prefixPartial 10 21137) = false := by
  decide +kernel

theorem node_context_10_21137_1162183 : EJMOriginalGlobalDAGData.nodes 11 ⟨1162183, by decide⟩ =
    .split (coordinate 10) (![⟨1161914, by decide⟩,⟨1161962, by decide⟩,⟨1162092, by decide⟩,⟨1162182, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21137_1162183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21137 ⟨1162183, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21137
    ⟨1162183, by decide⟩ (by decide) (![⟨1161914, by decide⟩,⟨1161962, by decide⟩,⟨1162092, by decide⟩,⟨1162182, by decide⟩]) unmarked_context_10_21137_1162183 node_context_10_21137_1162183
  intro a
  fin_cases a
  · exact context_11_84548_1161914
  · exact context_11_84549_1161962
  · exact context_11_84550_1162092
  · exact context_11_84551_1162182

theorem selected_cut_42528 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 338208) = some ⟨12, 1, 0, 1108174, 338208, 1, 65536⟩ := by
  decide +kernel

theorem context_12_338208_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338208 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 338208 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 338208, 1, 65536⟩
    (by decide) selected_cut_42528

theorem selected_cut_42529 : selected 9 ⟨1162226, by decide⟩
    (prefixPartial 12 338209) = some ⟨12, 2, 0, 1162226, 338209, 2501, 65536⟩ := by
  decide +kernel

theorem context_12_338209_1162226 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338209 ⟨1162226, by decide⟩ :=
  accepted_of_selected 12 338209 ⟨1162226, by decide⟩ ⟨12, 2, 0, 1162226, 338209, 2501, 65536⟩
    (by decide) selected_cut_42529

theorem selected_cut_42530 : selected 9 ⟨1162257, by decide⟩
    (prefixPartial 12 338210) = some ⟨12, 2, 0, 1162257, 338210, 2117, 65536⟩ := by
  decide +kernel

theorem context_12_338210_1162257 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 338210 ⟨1162257, by decide⟩ :=
  accepted_of_selected 12 338210 ⟨1162257, by decide⟩ ⟨12, 2, 0, 1162257, 338210, 2117, 65536⟩
    (by decide) selected_cut_42530

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
