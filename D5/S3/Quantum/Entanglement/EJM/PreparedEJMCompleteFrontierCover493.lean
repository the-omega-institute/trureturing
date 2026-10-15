/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover492
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_47331 : selected 9 ⟨1324328, by decide⟩
    (prefixPartial 12 373026) = some ⟨12, 2, 0, 1324328, 373026, 1941, 65536⟩ := by
  decide +kernel

theorem context_12_373026_1324328 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373026 ⟨1324328, by decide⟩ :=
  accepted_of_selected 12 373026 ⟨1324328, by decide⟩ ⟨12, 2, 0, 1324328, 373026, 1941, 65536⟩
    (by decide) selected_cut_47331

theorem selected_cut_47332 : selected 9 ⟨1324358, by decide⟩
    (prefixPartial 12 373027) = some ⟨12, 2, 0, 1324358, 373027, 1973, 65536⟩ := by
  decide +kernel

theorem context_12_373027_1324358 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373027 ⟨1324358, by decide⟩ :=
  accepted_of_selected 12 373027 ⟨1324358, by decide⟩ ⟨12, 2, 0, 1324358, 373027, 1973, 65536⟩
    (by decide) selected_cut_47332

theorem unmarked_context_11_93256_1324359 : frontier 10 ⟨1324359, by decide⟩
    (prefixCache 11 93256) (prefixPartial 11 93256) = false := by
  decide +kernel

theorem node_context_11_93256_1324359 : EJMOriginalGlobalDAGData.nodes 10 ⟨1324359, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨1324304, by decide⟩,⟨1324328, by decide⟩,⟨1324358, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93256_1324359 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93256 ⟨1324359, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93256
    ⟨1324359, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨1324304, by decide⟩,⟨1324328, by decide⟩,⟨1324358, by decide⟩]) unmarked_context_11_93256_1324359 node_context_11_93256_1324359
  intro a
  fin_cases a
  · exact context_12_373024_435790
  · exact context_12_373025_1324304
  · exact context_12_373026_1324328
  · exact context_12_373027_1324358

theorem selected_cut_47333 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 373028) = some ⟨12, 1, 0, 435790, 373028, 1, 65536⟩ := by
  decide +kernel

theorem context_12_373028_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373028 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 373028 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 373028, 1, 65536⟩
    (by decide) selected_cut_47333

theorem selected_cut_47334 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 373029) = some ⟨12, 1, 0, 891951, 373029, 1, 65536⟩ := by
  decide +kernel

theorem context_12_373029_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373029 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 373029 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 373029, 1, 65536⟩
    (by decide) selected_cut_47334

theorem selected_cut_47335 : selected 9 ⟨1324398, by decide⟩
    (prefixPartial 12 373030) = some ⟨12, 2, 0, 1324398, 373030, 2537, 65536⟩ := by
  decide +kernel

theorem context_12_373030_1324398 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373030 ⟨1324398, by decide⟩ :=
  accepted_of_selected 12 373030 ⟨1324398, by decide⟩ ⟨12, 2, 0, 1324398, 373030, 2537, 65536⟩
    (by decide) selected_cut_47335

theorem selected_cut_47336 : selected 9 ⟨1324444, by decide⟩
    (prefixPartial 12 373031) = some ⟨12, 2, 0, 1324444, 373031, 2533, 65536⟩ := by
  decide +kernel

theorem context_12_373031_1324444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373031 ⟨1324444, by decide⟩ :=
  accepted_of_selected 12 373031 ⟨1324444, by decide⟩ ⟨12, 2, 0, 1324444, 373031, 2533, 65536⟩
    (by decide) selected_cut_47336

theorem unmarked_context_11_93257_1324445 : frontier 10 ⟨1324445, by decide⟩
    (prefixCache 11 93257) (prefixPartial 11 93257) = false := by
  decide +kernel

theorem node_context_11_93257_1324445 : EJMOriginalGlobalDAGData.nodes 10 ⟨1324445, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨891951, by decide⟩,⟨1324398, by decide⟩,⟨1324444, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93257_1324445 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93257 ⟨1324445, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93257
    ⟨1324445, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨891951, by decide⟩,⟨1324398, by decide⟩,⟨1324444, by decide⟩]) unmarked_context_11_93257_1324445 node_context_11_93257_1324445
  intro a
  fin_cases a
  · exact context_12_373028_435790
  · exact context_12_373029_891951
  · exact context_12_373030_1324398
  · exact context_12_373031_1324444

theorem selected_cut_47337 : selected 10 ⟨1324475, by decide⟩
    (prefixPartial 11 93258) = some ⟨11, 2, 0, 1324475, 93258, 2073, 262144⟩ := by
  decide +kernel

theorem context_11_93258_1324475 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93258 ⟨1324475, by decide⟩ :=
  accepted_of_selected 11 93258 ⟨1324475, by decide⟩ ⟨11, 2, 0, 1324475, 93258, 2073, 262144⟩
    (by decide) selected_cut_47337

theorem selected_cut_47338 : selected 9 ⟨1324520, by decide⟩
    (prefixPartial 12 373036) = some ⟨12, 2, 0, 1324520, 373036, 2549, 65536⟩ := by
  decide +kernel

theorem context_12_373036_1324520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373036 ⟨1324520, by decide⟩ :=
  accepted_of_selected 12 373036 ⟨1324520, by decide⟩ ⟨12, 2, 0, 1324520, 373036, 2549, 65536⟩
    (by decide) selected_cut_47338

theorem selected_cut_47339 : selected 9 ⟨1324584, by decide⟩
    (prefixPartial 12 373037) = some ⟨12, 2, 0, 1324584, 373037, 2745, 65536⟩ := by
  decide +kernel

theorem context_12_373037_1324584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373037 ⟨1324584, by decide⟩ :=
  accepted_of_selected 12 373037 ⟨1324584, by decide⟩ ⟨12, 2, 0, 1324584, 373037, 2745, 65536⟩
    (by decide) selected_cut_47339

theorem selected_cut_47340 : selected 9 ⟨1324623, by decide⟩
    (prefixPartial 12 373038) = some ⟨12, 2, 0, 1324623, 373038, 2325, 65536⟩ := by
  decide +kernel

theorem context_12_373038_1324623 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373038 ⟨1324623, by decide⟩ :=
  accepted_of_selected 12 373038 ⟨1324623, by decide⟩ ⟨12, 2, 0, 1324623, 373038, 2325, 65536⟩
    (by decide) selected_cut_47340

theorem selected_cut_47341 : selected 9 ⟨1324666, by decide⟩
    (prefixPartial 12 373039) = some ⟨12, 2, 0, 1324666, 373039, 2345, 65536⟩ := by
  decide +kernel

theorem context_12_373039_1324666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373039 ⟨1324666, by decide⟩ :=
  accepted_of_selected 12 373039 ⟨1324666, by decide⟩ ⟨12, 2, 0, 1324666, 373039, 2345, 65536⟩
    (by decide) selected_cut_47341

theorem unmarked_context_11_93259_1324667 : frontier 10 ⟨1324667, by decide⟩
    (prefixCache 11 93259) (prefixPartial 11 93259) = false := by
  decide +kernel

theorem node_context_11_93259_1324667 : EJMOriginalGlobalDAGData.nodes 10 ⟨1324667, by decide⟩ =
    .split (coordinate 11) (![⟨1324520, by decide⟩,⟨1324584, by decide⟩,⟨1324623, by decide⟩,⟨1324666, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93259_1324667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93259 ⟨1324667, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93259
    ⟨1324667, by decide⟩ (by decide) (![⟨1324520, by decide⟩,⟨1324584, by decide⟩,⟨1324623, by decide⟩,⟨1324666, by decide⟩]) unmarked_context_11_93259_1324667 node_context_11_93259_1324667
  intro a
  fin_cases a
  · exact context_12_373036_1324520
  · exact context_12_373037_1324584
  · exact context_12_373038_1324623
  · exact context_12_373039_1324666

theorem unmarked_context_10_23314_1324668 : frontier 11 ⟨1324668, by decide⟩
    (prefixCache 10 23314) (prefixPartial 10 23314) = false := by
  decide +kernel

theorem node_context_10_23314_1324668 : EJMOriginalGlobalDAGData.nodes 11 ⟨1324668, by decide⟩ =
    .split (coordinate 10) (![⟨1324359, by decide⟩,⟨1324445, by decide⟩,⟨1324475, by decide⟩,⟨1324667, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23314_1324668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23314 ⟨1324668, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23314
    ⟨1324668, by decide⟩ (by decide) (![⟨1324359, by decide⟩,⟨1324445, by decide⟩,⟨1324475, by decide⟩,⟨1324667, by decide⟩]) unmarked_context_10_23314_1324668 node_context_10_23314_1324668
  intro a
  fin_cases a
  · exact context_11_93256_1324359
  · exact context_11_93257_1324445
  · exact context_11_93258_1324475
  · exact context_11_93259_1324667

theorem selected_cut_47342 : selected 9 ⟨1255011, by decide⟩
    (prefixPartial 12 373040) = some ⟨12, 1, 0, 1255011, 373040, 1, 65536⟩ := by
  decide +kernel

theorem context_12_373040_1255011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373040 ⟨1255011, by decide⟩ :=
  accepted_of_selected 12 373040 ⟨1255011, by decide⟩ ⟨12, 1, 0, 1255011, 373040, 1, 65536⟩
    (by decide) selected_cut_47342

theorem selected_cut_47343 : selected 9 ⟨1324697, by decide⟩
    (prefixPartial 12 373041) = some ⟨12, 2, 0, 1324697, 373041, 1881, 65536⟩ := by
  decide +kernel

theorem context_12_373041_1324697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373041 ⟨1324697, by decide⟩ :=
  accepted_of_selected 12 373041 ⟨1324697, by decide⟩ ⟨12, 2, 0, 1324697, 373041, 1881, 65536⟩
    (by decide) selected_cut_47343

theorem selected_cut_47344 : selected 9 ⟨1324722, by decide⟩
    (prefixPartial 12 373042) = some ⟨12, 2, 0, 1324722, 373042, 1649, 65536⟩ := by
  decide +kernel

theorem context_12_373042_1324722 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373042 ⟨1324722, by decide⟩ :=
  accepted_of_selected 12 373042 ⟨1324722, by decide⟩ ⟨12, 2, 0, 1324722, 373042, 1649, 65536⟩
    (by decide) selected_cut_47344

theorem selected_cut_47345 : selected 9 ⟨1324750, by decide⟩
    (prefixPartial 12 373043) = some ⟨12, 2, 0, 1324750, 373043, 1673, 65536⟩ := by
  decide +kernel

theorem context_12_373043_1324750 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373043 ⟨1324750, by decide⟩ :=
  accepted_of_selected 12 373043 ⟨1324750, by decide⟩ ⟨12, 2, 0, 1324750, 373043, 1673, 65536⟩
    (by decide) selected_cut_47345

theorem unmarked_context_11_93260_1324751 : frontier 10 ⟨1324751, by decide⟩
    (prefixCache 11 93260) (prefixPartial 11 93260) = false := by
  decide +kernel

theorem node_context_11_93260_1324751 : EJMOriginalGlobalDAGData.nodes 10 ⟨1324751, by decide⟩ =
    .split (coordinate 11) (![⟨1255011, by decide⟩,⟨1324697, by decide⟩,⟨1324722, by decide⟩,⟨1324750, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93260_1324751 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93260 ⟨1324751, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93260
    ⟨1324751, by decide⟩ (by decide) (![⟨1255011, by decide⟩,⟨1324697, by decide⟩,⟨1324722, by decide⟩,⟨1324750, by decide⟩]) unmarked_context_11_93260_1324751 node_context_11_93260_1324751
  intro a
  fin_cases a
  · exact context_12_373040_1255011
  · exact context_12_373041_1324697
  · exact context_12_373042_1324722
  · exact context_12_373043_1324750

theorem selected_cut_47346 : selected 9 ⟨1324789, by decide⟩
    (prefixPartial 12 373044) = some ⟨12, 2, 0, 1324789, 373044, 2249, 65536⟩ := by
  decide +kernel

theorem context_12_373044_1324789 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373044 ⟨1324789, by decide⟩ :=
  accepted_of_selected 12 373044 ⟨1324789, by decide⟩ ⟨12, 2, 0, 1324789, 373044, 2249, 65536⟩
    (by decide) selected_cut_47346

theorem selected_cut_47347 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 373045) = some ⟨12, 1, 0, 891951, 373045, 1, 65536⟩ := by
  decide +kernel

theorem context_12_373045_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373045 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 373045 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 373045, 1, 65536⟩
    (by decide) selected_cut_47347

theorem selected_cut_47348 : selected 9 ⟨1324817, by decide⟩
    (prefixPartial 12 373046) = some ⟨12, 2, 0, 1324817, 373046, 2045, 65536⟩ := by
  decide +kernel

theorem context_12_373046_1324817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373046 ⟨1324817, by decide⟩ :=
  accepted_of_selected 12 373046 ⟨1324817, by decide⟩ ⟨12, 2, 0, 1324817, 373046, 2045, 65536⟩
    (by decide) selected_cut_47348

theorem selected_cut_47349 : selected 9 ⟨1324847, by decide⟩
    (prefixPartial 12 373047) = some ⟨12, 2, 0, 1324847, 373047, 1909, 65536⟩ := by
  decide +kernel

theorem context_12_373047_1324847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373047 ⟨1324847, by decide⟩ :=
  accepted_of_selected 12 373047 ⟨1324847, by decide⟩ ⟨12, 2, 0, 1324847, 373047, 1909, 65536⟩
    (by decide) selected_cut_47349

theorem unmarked_context_11_93261_1324848 : frontier 10 ⟨1324848, by decide⟩
    (prefixCache 11 93261) (prefixPartial 11 93261) = false := by
  decide +kernel

theorem node_context_11_93261_1324848 : EJMOriginalGlobalDAGData.nodes 10 ⟨1324848, by decide⟩ =
    .split (coordinate 11) (![⟨1324789, by decide⟩,⟨891951, by decide⟩,⟨1324817, by decide⟩,⟨1324847, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93261_1324848 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93261 ⟨1324848, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93261
    ⟨1324848, by decide⟩ (by decide) (![⟨1324789, by decide⟩,⟨891951, by decide⟩,⟨1324817, by decide⟩,⟨1324847, by decide⟩]) unmarked_context_11_93261_1324848 node_context_11_93261_1324848
  intro a
  fin_cases a
  · exact context_12_373044_1324789
  · exact context_12_373045_891951
  · exact context_12_373046_1324817
  · exact context_12_373047_1324847

theorem selected_cut_47350 : selected 9 ⟨1324877, by decide⟩
    (prefixPartial 12 373048) = some ⟨12, 2, 0, 1324877, 373048, 1773, 65536⟩ := by
  decide +kernel

theorem context_12_373048_1324877 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373048 ⟨1324877, by decide⟩ :=
  accepted_of_selected 12 373048 ⟨1324877, by decide⟩ ⟨12, 2, 0, 1324877, 373048, 1773, 65536⟩
    (by decide) selected_cut_47350

theorem selected_cut_47351 : selected 9 ⟨1324908, by decide⟩
    (prefixPartial 12 373049) = some ⟨12, 2, 0, 1324908, 373049, 1901, 65536⟩ := by
  decide +kernel

theorem context_12_373049_1324908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373049 ⟨1324908, by decide⟩ :=
  accepted_of_selected 12 373049 ⟨1324908, by decide⟩ ⟨12, 2, 0, 1324908, 373049, 1901, 65536⟩
    (by decide) selected_cut_47351

theorem selected_cut_47352 : selected 9 ⟨1324935, by decide⟩
    (prefixPartial 12 373050) = some ⟨12, 2, 0, 1324935, 373050, 1889, 65536⟩ := by
  decide +kernel

theorem context_12_373050_1324935 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373050 ⟨1324935, by decide⟩ :=
  accepted_of_selected 12 373050 ⟨1324935, by decide⟩ ⟨12, 2, 0, 1324935, 373050, 1889, 65536⟩
    (by decide) selected_cut_47352

theorem selected_cut_47353 : selected 9 ⟨1324958, by decide⟩
    (prefixPartial 12 373051) = some ⟨12, 2, 0, 1324958, 373051, 1701, 65536⟩ := by
  decide +kernel

theorem context_12_373051_1324958 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373051 ⟨1324958, by decide⟩ :=
  accepted_of_selected 12 373051 ⟨1324958, by decide⟩ ⟨12, 2, 0, 1324958, 373051, 1701, 65536⟩
    (by decide) selected_cut_47353

theorem unmarked_context_11_93262_1324959 : frontier 10 ⟨1324959, by decide⟩
    (prefixCache 11 93262) (prefixPartial 11 93262) = false := by
  decide +kernel

theorem node_context_11_93262_1324959 : EJMOriginalGlobalDAGData.nodes 10 ⟨1324959, by decide⟩ =
    .split (coordinate 11) (![⟨1324877, by decide⟩,⟨1324908, by decide⟩,⟨1324935, by decide⟩,⟨1324958, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93262_1324959 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93262 ⟨1324959, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93262
    ⟨1324959, by decide⟩ (by decide) (![⟨1324877, by decide⟩,⟨1324908, by decide⟩,⟨1324935, by decide⟩,⟨1324958, by decide⟩]) unmarked_context_11_93262_1324959 node_context_11_93262_1324959
  intro a
  fin_cases a
  · exact context_12_373048_1324877
  · exact context_12_373049_1324908
  · exact context_12_373050_1324935
  · exact context_12_373051_1324958

theorem selected_cut_47354 : selected 10 ⟨1324985, by decide⟩
    (prefixPartial 11 93263) = some ⟨11, 2, 0, 1324985, 93263, 1705, 262144⟩ := by
  decide +kernel

theorem context_11_93263_1324985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93263 ⟨1324985, by decide⟩ :=
  accepted_of_selected 11 93263 ⟨1324985, by decide⟩ ⟨11, 2, 0, 1324985, 93263, 1705, 262144⟩
    (by decide) selected_cut_47354

theorem unmarked_context_10_23315_1324986 : frontier 11 ⟨1324986, by decide⟩
    (prefixCache 10 23315) (prefixPartial 10 23315) = false := by
  decide +kernel

theorem node_context_10_23315_1324986 : EJMOriginalGlobalDAGData.nodes 11 ⟨1324986, by decide⟩ =
    .split (coordinate 10) (![⟨1324751, by decide⟩,⟨1324848, by decide⟩,⟨1324959, by decide⟩,⟨1324985, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23315_1324986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23315 ⟨1324986, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23315
    ⟨1324986, by decide⟩ (by decide) (![⟨1324751, by decide⟩,⟨1324848, by decide⟩,⟨1324959, by decide⟩,⟨1324985, by decide⟩]) unmarked_context_10_23315_1324986 node_context_10_23315_1324986
  intro a
  fin_cases a
  · exact context_11_93260_1324751
  · exact context_11_93261_1324848
  · exact context_11_93262_1324959
  · exact context_11_93263_1324985

theorem unmarked_context_9_5828_1324987 : frontier 12 ⟨1324987, by decide⟩
    (prefixCache 9 5828) (prefixPartial 9 5828) = false := by
  decide +kernel

theorem node_context_9_5828_1324987 : EJMOriginalGlobalDAGData.nodes 12 ⟨1324987, by decide⟩ =
    .split (coordinate 9) (![⟨1323966, by decide⟩,⟨1324264, by decide⟩,⟨1324668, by decide⟩,⟨1324986, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5828_1324987 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5828 ⟨1324987, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5828
    ⟨1324987, by decide⟩ (by decide) (![⟨1323966, by decide⟩,⟨1324264, by decide⟩,⟨1324668, by decide⟩,⟨1324986, by decide⟩]) unmarked_context_9_5828_1324987 node_context_9_5828_1324987
  intro a
  fin_cases a
  · exact context_10_23312_1323966
  · exact context_10_23313_1324264
  · exact context_10_23314_1324668
  · exact context_10_23315_1324986

theorem selected_cut_47355 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 93264) = some ⟨11, 1, 0, 907917, 93264, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93264_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93264 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 93264 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 93264, 1, 262144⟩
    (by decide) selected_cut_47355

theorem selected_cut_47356 : selected 9 ⟨1325018, by decide⟩
    (prefixPartial 12 373060) = some ⟨12, 2, 0, 1325018, 373060, 1753, 65536⟩ := by
  decide +kernel

theorem context_12_373060_1325018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373060 ⟨1325018, by decide⟩ :=
  accepted_of_selected 12 373060 ⟨1325018, by decide⟩ ⟨12, 2, 0, 1325018, 373060, 1753, 65536⟩
    (by decide) selected_cut_47356

theorem selected_cut_47357 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 373061) = some ⟨12, 1, 0, 891951, 373061, 1, 65536⟩ := by
  decide +kernel

theorem context_12_373061_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373061 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 373061 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 373061, 1, 65536⟩
    (by decide) selected_cut_47357

theorem selected_cut_47358 : selected 9 ⟨1325046, by decide⟩
    (prefixPartial 12 373062) = some ⟨12, 2, 0, 1325046, 373062, 1505, 65536⟩ := by
  decide +kernel

theorem context_12_373062_1325046 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373062 ⟨1325046, by decide⟩ :=
  accepted_of_selected 12 373062 ⟨1325046, by decide⟩ ⟨12, 2, 0, 1325046, 373062, 1505, 65536⟩
    (by decide) selected_cut_47358

theorem selected_cut_47359 : selected 9 ⟨1325073, by decide⟩
    (prefixPartial 12 373063) = some ⟨12, 2, 0, 1325073, 373063, 1509, 65536⟩ := by
  decide +kernel

theorem context_12_373063_1325073 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373063 ⟨1325073, by decide⟩ :=
  accepted_of_selected 12 373063 ⟨1325073, by decide⟩ ⟨12, 2, 0, 1325073, 373063, 1509, 65536⟩
    (by decide) selected_cut_47359

theorem unmarked_context_11_93265_1325074 : frontier 10 ⟨1325074, by decide⟩
    (prefixCache 11 93265) (prefixPartial 11 93265) = false := by
  decide +kernel

theorem node_context_11_93265_1325074 : EJMOriginalGlobalDAGData.nodes 10 ⟨1325074, by decide⟩ =
    .split (coordinate 11) (![⟨1325018, by decide⟩,⟨891951, by decide⟩,⟨1325046, by decide⟩,⟨1325073, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93265_1325074 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93265 ⟨1325074, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93265
    ⟨1325074, by decide⟩ (by decide) (![⟨1325018, by decide⟩,⟨891951, by decide⟩,⟨1325046, by decide⟩,⟨1325073, by decide⟩]) unmarked_context_11_93265_1325074 node_context_11_93265_1325074
  intro a
  fin_cases a
  · exact context_12_373060_1325018
  · exact context_12_373061_891951
  · exact context_12_373062_1325046
  · exact context_12_373063_1325073

theorem selected_cut_47360 : selected 10 ⟨1325138, by decide⟩
    (prefixPartial 11 93266) = some ⟨11, 2, 0, 1325138, 93266, 3233, 262144⟩ := by
  decide +kernel

theorem context_11_93266_1325138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93266 ⟨1325138, by decide⟩ :=
  accepted_of_selected 11 93266 ⟨1325138, by decide⟩ ⟨11, 2, 0, 1325138, 93266, 3233, 262144⟩
    (by decide) selected_cut_47360

theorem selected_cut_47361 : selected 9 ⟨1325162, by decide⟩
    (prefixPartial 12 373068) = some ⟨12, 2, 0, 1325162, 373068, 1593, 65536⟩ := by
  decide +kernel

theorem context_12_373068_1325162 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373068 ⟨1325162, by decide⟩ :=
  accepted_of_selected 12 373068 ⟨1325162, by decide⟩ ⟨12, 2, 0, 1325162, 373068, 1593, 65536⟩
    (by decide) selected_cut_47361

theorem selected_cut_47362 : selected 9 ⟨1325195, by decide⟩
    (prefixPartial 12 373069) = some ⟨12, 2, 0, 1325195, 373069, 1673, 65536⟩ := by
  decide +kernel

theorem context_12_373069_1325195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373069 ⟨1325195, by decide⟩ :=
  accepted_of_selected 12 373069 ⟨1325195, by decide⟩ ⟨12, 2, 0, 1325195, 373069, 1673, 65536⟩
    (by decide) selected_cut_47362

theorem selected_cut_47363 : selected 9 ⟨1325221, by decide⟩
    (prefixPartial 12 373070) = some ⟨12, 2, 0, 1325221, 373070, 1477, 65536⟩ := by
  decide +kernel

theorem context_12_373070_1325221 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373070 ⟨1325221, by decide⟩ :=
  accepted_of_selected 12 373070 ⟨1325221, by decide⟩ ⟨12, 2, 0, 1325221, 373070, 1477, 65536⟩
    (by decide) selected_cut_47363

theorem selected_cut_47364 : selected 9 ⟨1325244, by decide⟩
    (prefixPartial 12 373071) = some ⟨12, 2, 0, 1325244, 373071, 1453, 65536⟩ := by
  decide +kernel

theorem context_12_373071_1325244 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373071 ⟨1325244, by decide⟩ :=
  accepted_of_selected 12 373071 ⟨1325244, by decide⟩ ⟨12, 2, 0, 1325244, 373071, 1453, 65536⟩
    (by decide) selected_cut_47364

theorem unmarked_context_11_93267_1325245 : frontier 10 ⟨1325245, by decide⟩
    (prefixCache 11 93267) (prefixPartial 11 93267) = false := by
  decide +kernel

theorem node_context_11_93267_1325245 : EJMOriginalGlobalDAGData.nodes 10 ⟨1325245, by decide⟩ =
    .split (coordinate 11) (![⟨1325162, by decide⟩,⟨1325195, by decide⟩,⟨1325221, by decide⟩,⟨1325244, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93267_1325245 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93267 ⟨1325245, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93267
    ⟨1325245, by decide⟩ (by decide) (![⟨1325162, by decide⟩,⟨1325195, by decide⟩,⟨1325221, by decide⟩,⟨1325244, by decide⟩]) unmarked_context_11_93267_1325245 node_context_11_93267_1325245
  intro a
  fin_cases a
  · exact context_12_373068_1325162
  · exact context_12_373069_1325195
  · exact context_12_373070_1325221
  · exact context_12_373071_1325244

theorem unmarked_context_10_23316_1325246 : frontier 11 ⟨1325246, by decide⟩
    (prefixCache 10 23316) (prefixPartial 10 23316) = false := by
  decide +kernel

theorem node_context_10_23316_1325246 : EJMOriginalGlobalDAGData.nodes 11 ⟨1325246, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨1325074, by decide⟩,⟨1325138, by decide⟩,⟨1325245, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23316_1325246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23316 ⟨1325246, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23316
    ⟨1325246, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨1325074, by decide⟩,⟨1325138, by decide⟩,⟨1325245, by decide⟩]) unmarked_context_10_23316_1325246 node_context_10_23316_1325246
  intro a
  fin_cases a
  · exact context_11_93264_907917
  · exact context_11_93265_1325074
  · exact context_11_93266_1325138
  · exact context_11_93267_1325245

theorem selected_cut_47365 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 23317) = some ⟨10, 1, 0, 893098, 23317, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_23317_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23317 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 23317 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 23317, 1, 1048576⟩
    (by decide) selected_cut_47365

theorem selected_cut_47366 : selected 10 ⟨1325282, by decide⟩
    (prefixPartial 11 93272) = some ⟨11, 2, 0, 1325282, 93272, 2385, 262144⟩ := by
  decide +kernel

theorem context_11_93272_1325282 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93272 ⟨1325282, by decide⟩ :=
  accepted_of_selected 11 93272 ⟨1325282, by decide⟩ ⟨11, 2, 0, 1325282, 93272, 2385, 262144⟩
    (by decide) selected_cut_47366

theorem selected_cut_47367 : selected 9 ⟨1325313, by decide⟩
    (prefixPartial 12 373092) = some ⟨12, 2, 0, 1325313, 373092, 1609, 65536⟩ := by
  decide +kernel

theorem context_12_373092_1325313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373092 ⟨1325313, by decide⟩ :=
  accepted_of_selected 12 373092 ⟨1325313, by decide⟩ ⟨12, 2, 0, 1325313, 373092, 1609, 65536⟩
    (by decide) selected_cut_47367

theorem selected_cut_47368 : selected 9 ⟨1256866, by decide⟩
    (prefixPartial 12 373093) = some ⟨12, 1, 0, 1256866, 373093, 1, 65536⟩ := by
  decide +kernel

theorem context_12_373093_1256866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373093 ⟨1256866, by decide⟩ :=
  accepted_of_selected 12 373093 ⟨1256866, by decide⟩ ⟨12, 1, 0, 1256866, 373093, 1, 65536⟩
    (by decide) selected_cut_47368

theorem selected_cut_47369 : selected 9 ⟨1325333, by decide⟩
    (prefixPartial 12 373094) = some ⟨12, 2, 0, 1325333, 373094, 1361, 65536⟩ := by
  decide +kernel

theorem context_12_373094_1325333 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373094 ⟨1325333, by decide⟩ :=
  accepted_of_selected 12 373094 ⟨1325333, by decide⟩ ⟨12, 2, 0, 1325333, 373094, 1361, 65536⟩
    (by decide) selected_cut_47369

theorem selected_cut_47370 : selected 9 ⟨1325354, by decide⟩
    (prefixPartial 12 373095) = some ⟨12, 2, 0, 1325354, 373095, 1381, 65536⟩ := by
  decide +kernel

theorem context_12_373095_1325354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373095 ⟨1325354, by decide⟩ :=
  accepted_of_selected 12 373095 ⟨1325354, by decide⟩ ⟨12, 2, 0, 1325354, 373095, 1381, 65536⟩
    (by decide) selected_cut_47370

theorem unmarked_context_11_93273_1325355 : frontier 10 ⟨1325355, by decide⟩
    (prefixCache 11 93273) (prefixPartial 11 93273) = false := by
  decide +kernel

theorem node_context_11_93273_1325355 : EJMOriginalGlobalDAGData.nodes 10 ⟨1325355, by decide⟩ =
    .split (coordinate 11) (![⟨1325313, by decide⟩,⟨1256866, by decide⟩,⟨1325333, by decide⟩,⟨1325354, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93273_1325355 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93273 ⟨1325355, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93273
    ⟨1325355, by decide⟩ (by decide) (![⟨1325313, by decide⟩,⟨1256866, by decide⟩,⟨1325333, by decide⟩,⟨1325354, by decide⟩]) unmarked_context_11_93273_1325355 node_context_11_93273_1325355
  intro a
  fin_cases a
  · exact context_12_373092_1325313
  · exact context_12_373093_1256866
  · exact context_12_373094_1325333
  · exact context_12_373095_1325354

theorem selected_cut_47371 : selected 10 ⟨1325376, by decide⟩
    (prefixPartial 11 93274) = some ⟨11, 2, 0, 1325376, 93274, 1289, 262144⟩ := by
  decide +kernel

theorem context_11_93274_1325376 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93274 ⟨1325376, by decide⟩ :=
  accepted_of_selected 11 93274 ⟨1325376, by decide⟩ ⟨11, 2, 0, 1325376, 93274, 1289, 262144⟩
    (by decide) selected_cut_47371

theorem selected_cut_47372 : selected 10 ⟨1325430, by decide⟩
    (prefixPartial 11 93275) = some ⟨11, 2, 0, 1325430, 93275, 2853, 262144⟩ := by
  decide +kernel

theorem context_11_93275_1325430 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93275 ⟨1325430, by decide⟩ :=
  accepted_of_selected 11 93275 ⟨1325430, by decide⟩ ⟨11, 2, 0, 1325430, 93275, 2853, 262144⟩
    (by decide) selected_cut_47372

theorem unmarked_context_10_23318_1325431 : frontier 11 ⟨1325431, by decide⟩
    (prefixCache 10 23318) (prefixPartial 10 23318) = false := by
  decide +kernel

theorem node_context_10_23318_1325431 : EJMOriginalGlobalDAGData.nodes 11 ⟨1325431, by decide⟩ =
    .split (coordinate 10) (![⟨1325282, by decide⟩,⟨1325355, by decide⟩,⟨1325376, by decide⟩,⟨1325430, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23318_1325431 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23318 ⟨1325431, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23318
    ⟨1325431, by decide⟩ (by decide) (![⟨1325282, by decide⟩,⟨1325355, by decide⟩,⟨1325376, by decide⟩,⟨1325430, by decide⟩]) unmarked_context_10_23318_1325431 node_context_10_23318_1325431
  intro a
  fin_cases a
  · exact context_11_93272_1325282
  · exact context_11_93273_1325355
  · exact context_11_93274_1325376
  · exact context_11_93275_1325430

theorem selected_cut_47373 : selected 10 ⟨1325495, by decide⟩
    (prefixPartial 11 93276) = some ⟨11, 2, 0, 1325495, 93276, 3561, 262144⟩ := by
  decide +kernel

theorem context_11_93276_1325495 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93276 ⟨1325495, by decide⟩ :=
  accepted_of_selected 11 93276 ⟨1325495, by decide⟩ ⟨11, 2, 0, 1325495, 93276, 3561, 262144⟩
    (by decide) selected_cut_47373

theorem selected_cut_47374 : selected 10 ⟨1325554, by decide⟩
    (prefixPartial 11 93277) = some ⟨11, 2, 0, 1325554, 93277, 3397, 262144⟩ := by
  decide +kernel

theorem context_11_93277_1325554 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93277 ⟨1325554, by decide⟩ :=
  accepted_of_selected 11 93277 ⟨1325554, by decide⟩ ⟨11, 2, 0, 1325554, 93277, 3397, 262144⟩
    (by decide) selected_cut_47374

theorem selected_cut_47375 : selected 10 ⟨1325594, by decide⟩
    (prefixPartial 11 93278) = some ⟨11, 2, 0, 1325594, 93278, 2225, 262144⟩ := by
  decide +kernel

theorem context_11_93278_1325594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93278 ⟨1325594, by decide⟩ :=
  accepted_of_selected 11 93278 ⟨1325594, by decide⟩ ⟨11, 2, 0, 1325594, 93278, 2225, 262144⟩
    (by decide) selected_cut_47375

theorem selected_cut_47376 : selected 10 ⟨1325629, by decide⟩
    (prefixPartial 11 93279) = some ⟨11, 2, 0, 1325629, 93279, 2133, 262144⟩ := by
  decide +kernel

theorem context_11_93279_1325629 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93279 ⟨1325629, by decide⟩ :=
  accepted_of_selected 11 93279 ⟨1325629, by decide⟩ ⟨11, 2, 0, 1325629, 93279, 2133, 262144⟩
    (by decide) selected_cut_47376

theorem unmarked_context_10_23319_1325630 : frontier 11 ⟨1325630, by decide⟩
    (prefixCache 10 23319) (prefixPartial 10 23319) = false := by
  decide +kernel

theorem node_context_10_23319_1325630 : EJMOriginalGlobalDAGData.nodes 11 ⟨1325630, by decide⟩ =
    .split (coordinate 10) (![⟨1325495, by decide⟩,⟨1325554, by decide⟩,⟨1325594, by decide⟩,⟨1325629, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23319_1325630 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23319 ⟨1325630, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23319
    ⟨1325630, by decide⟩ (by decide) (![⟨1325495, by decide⟩,⟨1325554, by decide⟩,⟨1325594, by decide⟩,⟨1325629, by decide⟩]) unmarked_context_10_23319_1325630 node_context_10_23319_1325630
  intro a
  fin_cases a
  · exact context_11_93276_1325495
  · exact context_11_93277_1325554
  · exact context_11_93278_1325594
  · exact context_11_93279_1325629

theorem unmarked_context_9_5829_1325631 : frontier 12 ⟨1325631, by decide⟩
    (prefixCache 9 5829) (prefixPartial 9 5829) = false := by
  decide +kernel

theorem node_context_9_5829_1325631 : EJMOriginalGlobalDAGData.nodes 12 ⟨1325631, by decide⟩ =
    .split (coordinate 9) (![⟨1325246, by decide⟩,⟨893098, by decide⟩,⟨1325431, by decide⟩,⟨1325630, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5829_1325631 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5829 ⟨1325631, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5829
    ⟨1325631, by decide⟩ (by decide) (![⟨1325246, by decide⟩,⟨893098, by decide⟩,⟨1325431, by decide⟩,⟨1325630, by decide⟩]) unmarked_context_9_5829_1325631 node_context_9_5829_1325631
  intro a
  fin_cases a
  · exact context_10_23316_1325246
  · exact context_10_23317_893098
  · exact context_10_23318_1325431
  · exact context_10_23319_1325630

theorem selected_cut_47377 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 93280) = some ⟨11, 1, 0, 907917, 93280, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93280_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93280 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 93280 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 93280, 1, 262144⟩
    (by decide) selected_cut_47377

theorem selected_cut_47378 : selected 10 ⟨1325664, by decide⟩
    (prefixPartial 11 93281) = some ⟨11, 2, 0, 1325664, 93281, 2077, 262144⟩ := by
  decide +kernel

theorem context_11_93281_1325664 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93281 ⟨1325664, by decide⟩ :=
  accepted_of_selected 11 93281 ⟨1325664, by decide⟩ ⟨11, 2, 0, 1325664, 93281, 2077, 262144⟩
    (by decide) selected_cut_47378

theorem selected_cut_47379 : selected 10 ⟨1325710, by decide⟩
    (prefixPartial 11 93282) = some ⟨11, 2, 0, 1325710, 93282, 3061, 262144⟩ := by
  decide +kernel

theorem context_11_93282_1325710 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93282 ⟨1325710, by decide⟩ :=
  accepted_of_selected 11 93282 ⟨1325710, by decide⟩ ⟨11, 2, 0, 1325710, 93282, 3061, 262144⟩
    (by decide) selected_cut_47379

theorem selected_cut_47380 : selected 10 ⟨1325747, by decide⟩
    (prefixPartial 11 93283) = some ⟨11, 2, 0, 1325747, 93283, 2869, 262144⟩ := by
  decide +kernel

theorem context_11_93283_1325747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93283 ⟨1325747, by decide⟩ :=
  accepted_of_selected 11 93283 ⟨1325747, by decide⟩ ⟨11, 2, 0, 1325747, 93283, 2869, 262144⟩
    (by decide) selected_cut_47380

theorem unmarked_context_10_23320_1325748 : frontier 11 ⟨1325748, by decide⟩
    (prefixCache 10 23320) (prefixPartial 10 23320) = false := by
  decide +kernel

theorem node_context_10_23320_1325748 : EJMOriginalGlobalDAGData.nodes 11 ⟨1325748, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨1325664, by decide⟩,⟨1325710, by decide⟩,⟨1325747, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23320_1325748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23320 ⟨1325748, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23320
    ⟨1325748, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨1325664, by decide⟩,⟨1325710, by decide⟩,⟨1325747, by decide⟩]) unmarked_context_10_23320_1325748 node_context_10_23320_1325748
  intro a
  fin_cases a
  · exact context_11_93280_907917
  · exact context_11_93281_1325664
  · exact context_11_93282_1325710
  · exact context_11_93283_1325747

theorem selected_cut_47381 : selected 10 ⟨1325775, by decide⟩
    (prefixPartial 11 93284) = some ⟨11, 2, 0, 1325775, 93284, 1693, 262144⟩ := by
  decide +kernel

theorem context_11_93284_1325775 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93284 ⟨1325775, by decide⟩ :=
  accepted_of_selected 11 93284 ⟨1325775, by decide⟩ ⟨11, 2, 0, 1325775, 93284, 1693, 262144⟩
    (by decide) selected_cut_47381

theorem selected_cut_47382 : selected 10 ⟨1325786, by decide⟩
    (prefixPartial 11 93285) = some ⟨11, 2, 0, 1325786, 93285, 773, 262144⟩ := by
  decide +kernel

theorem context_11_93285_1325786 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93285 ⟨1325786, by decide⟩ :=
  accepted_of_selected 11 93285 ⟨1325786, by decide⟩ ⟨11, 2, 0, 1325786, 93285, 773, 262144⟩
    (by decide) selected_cut_47382

theorem selected_cut_47383 : selected 10 ⟨1325817, by decide⟩
    (prefixPartial 11 93286) = some ⟨11, 2, 0, 1325817, 93286, 2309, 262144⟩ := by
  decide +kernel

theorem context_11_93286_1325817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93286 ⟨1325817, by decide⟩ :=
  accepted_of_selected 11 93286 ⟨1325817, by decide⟩ ⟨11, 2, 0, 1325817, 93286, 2309, 262144⟩
    (by decide) selected_cut_47383

theorem selected_cut_47384 : selected 10 ⟨1325850, by decide⟩
    (prefixPartial 11 93287) = some ⟨11, 2, 0, 1325850, 93287, 2133, 262144⟩ := by
  decide +kernel

theorem context_11_93287_1325850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93287 ⟨1325850, by decide⟩ :=
  accepted_of_selected 11 93287 ⟨1325850, by decide⟩ ⟨11, 2, 0, 1325850, 93287, 2133, 262144⟩
    (by decide) selected_cut_47384

theorem unmarked_context_10_23321_1325851 : frontier 11 ⟨1325851, by decide⟩
    (prefixCache 10 23321) (prefixPartial 10 23321) = false := by
  decide +kernel

theorem node_context_10_23321_1325851 : EJMOriginalGlobalDAGData.nodes 11 ⟨1325851, by decide⟩ =
    .split (coordinate 10) (![⟨1325775, by decide⟩,⟨1325786, by decide⟩,⟨1325817, by decide⟩,⟨1325850, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23321_1325851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23321 ⟨1325851, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23321
    ⟨1325851, by decide⟩ (by decide) (![⟨1325775, by decide⟩,⟨1325786, by decide⟩,⟨1325817, by decide⟩,⟨1325850, by decide⟩]) unmarked_context_10_23321_1325851 node_context_10_23321_1325851
  intro a
  fin_cases a
  · exact context_11_93284_1325775
  · exact context_11_93285_1325786
  · exact context_11_93286_1325817
  · exact context_11_93287_1325850

theorem selected_cut_47385 : selected 11 ⟨1325895, by decide⟩
    (prefixPartial 10 23322) = some ⟨10, 2, 0, 1325895, 23322, 2717, 1048576⟩ := by
  decide +kernel

theorem context_10_23322_1325895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23322 ⟨1325895, by decide⟩ :=
  accepted_of_selected 10 23322 ⟨1325895, by decide⟩ ⟨10, 2, 0, 1325895, 23322, 2717, 1048576⟩
    (by decide) selected_cut_47385

theorem selected_cut_47386 : selected 10 ⟨1325918, by decide⟩
    (prefixPartial 11 93292) = some ⟨11, 2, 0, 1325918, 93292, 1517, 262144⟩ := by
  decide +kernel

theorem context_11_93292_1325918 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93292 ⟨1325918, by decide⟩ :=
  accepted_of_selected 11 93292 ⟨1325918, by decide⟩ ⟨11, 2, 0, 1325918, 93292, 1517, 262144⟩
    (by decide) selected_cut_47386

theorem selected_cut_47387 : selected 10 ⟨1325932, by decide⟩
    (prefixPartial 11 93293) = some ⟨11, 2, 0, 1325932, 93293, 965, 262144⟩ := by
  decide +kernel

theorem context_11_93293_1325932 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93293 ⟨1325932, by decide⟩ :=
  accepted_of_selected 11 93293 ⟨1325932, by decide⟩ ⟨11, 2, 0, 1325932, 93293, 965, 262144⟩
    (by decide) selected_cut_47387

theorem selected_cut_47388 : selected 10 ⟨1325951, by decide⟩
    (prefixPartial 11 93294) = some ⟨11, 2, 0, 1325951, 93294, 1397, 262144⟩ := by
  decide +kernel

theorem context_11_93294_1325951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93294 ⟨1325951, by decide⟩ :=
  accepted_of_selected 11 93294 ⟨1325951, by decide⟩ ⟨11, 2, 0, 1325951, 93294, 1397, 262144⟩
    (by decide) selected_cut_47388

theorem selected_cut_47389 : selected 10 ⟨1325960, by decide⟩
    (prefixPartial 11 93295) = some ⟨11, 2, 0, 1325960, 93295, 877, 262144⟩ := by
  decide +kernel

theorem context_11_93295_1325960 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93295 ⟨1325960, by decide⟩ :=
  accepted_of_selected 11 93295 ⟨1325960, by decide⟩ ⟨11, 2, 0, 1325960, 93295, 877, 262144⟩
    (by decide) selected_cut_47389

theorem unmarked_context_10_23323_1325961 : frontier 11 ⟨1325961, by decide⟩
    (prefixCache 10 23323) (prefixPartial 10 23323) = false := by
  decide +kernel

theorem node_context_10_23323_1325961 : EJMOriginalGlobalDAGData.nodes 11 ⟨1325961, by decide⟩ =
    .split (coordinate 10) (![⟨1325918, by decide⟩,⟨1325932, by decide⟩,⟨1325951, by decide⟩,⟨1325960, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23323_1325961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23323 ⟨1325961, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23323
    ⟨1325961, by decide⟩ (by decide) (![⟨1325918, by decide⟩,⟨1325932, by decide⟩,⟨1325951, by decide⟩,⟨1325960, by decide⟩]) unmarked_context_10_23323_1325961 node_context_10_23323_1325961
  intro a
  fin_cases a
  · exact context_11_93292_1325918
  · exact context_11_93293_1325932
  · exact context_11_93294_1325951
  · exact context_11_93295_1325960

theorem unmarked_context_9_5830_1325962 : frontier 12 ⟨1325962, by decide⟩
    (prefixCache 9 5830) (prefixPartial 9 5830) = false := by
  decide +kernel

theorem node_context_9_5830_1325962 : EJMOriginalGlobalDAGData.nodes 12 ⟨1325962, by decide⟩ =
    .split (coordinate 9) (![⟨1325748, by decide⟩,⟨1325851, by decide⟩,⟨1325895, by decide⟩,⟨1325961, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5830_1325962 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5830 ⟨1325962, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5830
    ⟨1325962, by decide⟩ (by decide) (![⟨1325748, by decide⟩,⟨1325851, by decide⟩,⟨1325895, by decide⟩,⟨1325961, by decide⟩]) unmarked_context_9_5830_1325962 node_context_9_5830_1325962
  intro a
  fin_cases a
  · exact context_10_23320_1325748
  · exact context_10_23321_1325851
  · exact context_10_23322_1325895
  · exact context_10_23323_1325961

theorem selected_cut_47390 : selected 11 ⟨1326025, by decide⟩
    (prefixPartial 10 23324) = some ⟨10, 2, 0, 1326025, 23324, 3989, 1048576⟩ := by
  decide +kernel

theorem context_10_23324_1326025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23324 ⟨1326025, by decide⟩ :=
  accepted_of_selected 10 23324 ⟨1326025, by decide⟩ ⟨10, 2, 0, 1326025, 23324, 3989, 1048576⟩
    (by decide) selected_cut_47390

theorem selected_cut_47391 : selected 11 ⟨1326077, by decide⟩
    (prefixPartial 10 23325) = some ⟨10, 2, 0, 1326077, 23325, 2577, 1048576⟩ := by
  decide +kernel

theorem context_10_23325_1326077 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23325 ⟨1326077, by decide⟩ :=
  accepted_of_selected 10 23325 ⟨1326077, by decide⟩ ⟨10, 2, 0, 1326077, 23325, 2577, 1048576⟩
    (by decide) selected_cut_47391

theorem selected_cut_47392 : selected 11 ⟨1326112, by decide⟩
    (prefixPartial 10 23326) = some ⟨10, 2, 0, 1326112, 23326, 1633, 1048576⟩ := by
  decide +kernel

theorem context_10_23326_1326112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23326 ⟨1326112, by decide⟩ :=
  accepted_of_selected 10 23326 ⟨1326112, by decide⟩ ⟨10, 2, 0, 1326112, 23326, 1633, 1048576⟩
    (by decide) selected_cut_47392

theorem selected_cut_47393 : selected 11 ⟨1326117, by decide⟩
    (prefixPartial 10 23327) = some ⟨10, 2, 0, 1326117, 23327, 305, 1048576⟩ := by
  decide +kernel

theorem context_10_23327_1326117 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23327 ⟨1326117, by decide⟩ :=
  accepted_of_selected 10 23327 ⟨1326117, by decide⟩ ⟨10, 2, 0, 1326117, 23327, 305, 1048576⟩
    (by decide) selected_cut_47393

theorem unmarked_context_9_5831_1326118 : frontier 12 ⟨1326118, by decide⟩
    (prefixCache 9 5831) (prefixPartial 9 5831) = false := by
  decide +kernel

theorem node_context_9_5831_1326118 : EJMOriginalGlobalDAGData.nodes 12 ⟨1326118, by decide⟩ =
    .split (coordinate 9) (![⟨1326025, by decide⟩,⟨1326077, by decide⟩,⟨1326112, by decide⟩,⟨1326117, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5831_1326118 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5831 ⟨1326118, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5831
    ⟨1326118, by decide⟩ (by decide) (![⟨1326025, by decide⟩,⟨1326077, by decide⟩,⟨1326112, by decide⟩,⟨1326117, by decide⟩]) unmarked_context_9_5831_1326118 node_context_9_5831_1326118
  intro a
  fin_cases a
  · exact context_10_23324_1326025
  · exact context_10_23325_1326077
  · exact context_10_23326_1326112
  · exact context_10_23327_1326117

theorem unmarked_context_8_1457_1326119 : frontier 13 ⟨1326119, by decide⟩
    (prefixCache 8 1457) (prefixPartial 8 1457) = false := by
  decide +kernel

theorem node_context_8_1457_1326119 : EJMOriginalGlobalDAGData.nodes 13 ⟨1326119, by decide⟩ =
    .split (coordinate 8) (![⟨1324987, by decide⟩,⟨1325631, by decide⟩,⟨1325962, by decide⟩,⟨1326118, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1457_1326119 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1457 ⟨1326119, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1457
    ⟨1326119, by decide⟩ (by decide) (![⟨1324987, by decide⟩,⟨1325631, by decide⟩,⟨1325962, by decide⟩,⟨1326118, by decide⟩]) unmarked_context_8_1457_1326119 node_context_8_1457_1326119
  intro a
  fin_cases a
  · exact context_9_5828_1324987
  · exact context_9_5829_1325631
  · exact context_9_5830_1325962
  · exact context_9_5831_1326118

theorem selected_cut_47394 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 93312) = some ⟨11, 1, 0, 434745, 93312, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93312_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93312 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 93312 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 93312, 1, 262144⟩
    (by decide) selected_cut_47394

theorem selected_cut_47395 : selected 10 ⟨167448, by decide⟩
    (prefixPartial 11 93313) = some ⟨11, 1, 0, 167448, 93313, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93313_167448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93313 ⟨167448, by decide⟩ :=
  accepted_of_selected 11 93313 ⟨167448, by decide⟩ ⟨11, 1, 0, 167448, 93313, 1, 262144⟩
    (by decide) selected_cut_47395

theorem selected_cut_47396 : selected 10 ⟨1326178, by decide⟩
    (prefixPartial 11 93314) = some ⟨11, 2, 0, 1326178, 93314, 2925, 262144⟩ := by
  decide +kernel

theorem context_11_93314_1326178 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93314 ⟨1326178, by decide⟩ :=
  accepted_of_selected 11 93314 ⟨1326178, by decide⟩ ⟨11, 2, 0, 1326178, 93314, 2925, 262144⟩
    (by decide) selected_cut_47396

theorem selected_cut_47397 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 373260) = some ⟨12, 1, 0, 448748, 373260, 1, 65536⟩ := by
  decide +kernel

theorem context_12_373260_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373260 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 373260 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 373260, 1, 65536⟩
    (by decide) selected_cut_47397

theorem selected_cut_47398 : selected 9 ⟨1326255, by decide⟩
    (prefixPartial 12 373261) = some ⟨12, 2, 0, 1326255, 373261, 3541, 65536⟩ := by
  decide +kernel

theorem context_12_373261_1326255 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373261 ⟨1326255, by decide⟩ :=
  accepted_of_selected 12 373261 ⟨1326255, by decide⟩ ⟨12, 2, 0, 1326255, 373261, 3541, 65536⟩
    (by decide) selected_cut_47398

theorem selected_cut_47399 : selected 9 ⟨1326313, by decide⟩
    (prefixPartial 12 373262) = some ⟨12, 2, 0, 1326313, 373262, 3133, 65536⟩ := by
  decide +kernel

theorem context_12_373262_1326313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373262 ⟨1326313, by decide⟩ :=
  accepted_of_selected 12 373262 ⟨1326313, by decide⟩ ⟨12, 2, 0, 1326313, 373262, 3133, 65536⟩
    (by decide) selected_cut_47399

theorem selected_cut_47400 : selected 9 ⟨1326370, by decide⟩
    (prefixPartial 12 373263) = some ⟨12, 2, 0, 1326370, 373263, 2949, 65536⟩ := by
  decide +kernel

theorem context_12_373263_1326370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373263 ⟨1326370, by decide⟩ :=
  accepted_of_selected 12 373263 ⟨1326370, by decide⟩ ⟨12, 2, 0, 1326370, 373263, 2949, 65536⟩
    (by decide) selected_cut_47400

theorem unmarked_context_11_93315_1326371 : frontier 10 ⟨1326371, by decide⟩
    (prefixCache 11 93315) (prefixPartial 11 93315) = false := by
  decide +kernel

theorem node_context_11_93315_1326371 : EJMOriginalGlobalDAGData.nodes 10 ⟨1326371, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1326255, by decide⟩,⟨1326313, by decide⟩,⟨1326370, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93315_1326371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93315 ⟨1326371, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93315
    ⟨1326371, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1326255, by decide⟩,⟨1326313, by decide⟩,⟨1326370, by decide⟩]) unmarked_context_11_93315_1326371 node_context_11_93315_1326371
  intro a
  fin_cases a
  · exact context_12_373260_448748
  · exact context_12_373261_1326255
  · exact context_12_373262_1326313
  · exact context_12_373263_1326370

theorem unmarked_context_10_23328_1326372 : frontier 11 ⟨1326372, by decide⟩
    (prefixCache 10 23328) (prefixPartial 10 23328) = false := by
  decide +kernel

theorem node_context_10_23328_1326372 : EJMOriginalGlobalDAGData.nodes 11 ⟨1326372, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨167448, by decide⟩,⟨1326178, by decide⟩,⟨1326371, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23328_1326372 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23328 ⟨1326372, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23328
    ⟨1326372, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨167448, by decide⟩,⟨1326178, by decide⟩,⟨1326371, by decide⟩]) unmarked_context_10_23328_1326372 node_context_10_23328_1326372
  intro a
  fin_cases a
  · exact context_11_93312_434745
  · exact context_11_93313_167448
  · exact context_11_93314_1326178
  · exact context_11_93315_1326371

theorem selected_cut_47401 : selected 9 ⟨1255011, by decide⟩
    (prefixPartial 12 373264) = some ⟨12, 1, 0, 1255011, 373264, 1, 65536⟩ := by
  decide +kernel

theorem context_12_373264_1255011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373264 ⟨1255011, by decide⟩ :=
  accepted_of_selected 12 373264 ⟨1255011, by decide⟩ ⟨12, 1, 0, 1255011, 373264, 1, 65536⟩
    (by decide) selected_cut_47401

theorem selected_cut_47402 : selected 9 ⟨1326423, by decide⟩
    (prefixPartial 12 373265) = some ⟨12, 2, 0, 1326423, 373265, 3065, 65536⟩ := by
  decide +kernel

theorem context_12_373265_1326423 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373265 ⟨1326423, by decide⟩ :=
  accepted_of_selected 12 373265 ⟨1326423, by decide⟩ ⟨12, 2, 0, 1326423, 373265, 3065, 65536⟩
    (by decide) selected_cut_47402

theorem selected_cut_47403 : selected 9 ⟨1326472, by decide⟩
    (prefixPartial 12 373266) = some ⟨12, 2, 0, 1326472, 373266, 2545, 65536⟩ := by
  decide +kernel

theorem context_12_373266_1326472 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373266 ⟨1326472, by decide⟩ :=
  accepted_of_selected 12 373266 ⟨1326472, by decide⟩ ⟨12, 2, 0, 1326472, 373266, 2545, 65536⟩
    (by decide) selected_cut_47403

theorem selected_cut_47404 : selected 9 ⟨1326519, by decide⟩
    (prefixPartial 12 373267) = some ⟨12, 2, 0, 1326519, 373267, 2957, 65536⟩ := by
  decide +kernel

theorem context_12_373267_1326519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373267 ⟨1326519, by decide⟩ :=
  accepted_of_selected 12 373267 ⟨1326519, by decide⟩ ⟨12, 2, 0, 1326519, 373267, 2957, 65536⟩
    (by decide) selected_cut_47404

theorem unmarked_context_11_93316_1326520 : frontier 10 ⟨1326520, by decide⟩
    (prefixCache 11 93316) (prefixPartial 11 93316) = false := by
  decide +kernel

theorem node_context_11_93316_1326520 : EJMOriginalGlobalDAGData.nodes 10 ⟨1326520, by decide⟩ =
    .split (coordinate 11) (![⟨1255011, by decide⟩,⟨1326423, by decide⟩,⟨1326472, by decide⟩,⟨1326519, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93316_1326520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93316 ⟨1326520, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93316
    ⟨1326520, by decide⟩ (by decide) (![⟨1255011, by decide⟩,⟨1326423, by decide⟩,⟨1326472, by decide⟩,⟨1326519, by decide⟩]) unmarked_context_11_93316_1326520 node_context_11_93316_1326520
  intro a
  fin_cases a
  · exact context_12_373264_1255011
  · exact context_12_373265_1326423
  · exact context_12_373266_1326472
  · exact context_12_373267_1326519

theorem selected_cut_47405 : selected 10 ⟨815620, by decide⟩
    (prefixPartial 11 93317) = some ⟨11, 1, 0, 815620, 93317, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93317_815620 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93317 ⟨815620, by decide⟩ :=
  accepted_of_selected 11 93317 ⟨815620, by decide⟩ ⟨11, 1, 0, 815620, 93317, 1, 262144⟩
    (by decide) selected_cut_47405

theorem selected_cut_47406 : selected 9 ⟨994572, by decide⟩
    (prefixPartial 12 373272) = some ⟨12, 1, 0, 994572, 373272, 1, 65536⟩ := by
  decide +kernel

theorem context_12_373272_994572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373272 ⟨994572, by decide⟩ :=
  accepted_of_selected 12 373272 ⟨994572, by decide⟩ ⟨12, 1, 0, 994572, 373272, 1, 65536⟩
    (by decide) selected_cut_47406

theorem selected_cut_47407 : selected 9 ⟨1326564, by decide⟩
    (prefixPartial 12 373273) = some ⟨12, 2, 0, 1326564, 373273, 2989, 65536⟩ := by
  decide +kernel

theorem context_12_373273_1326564 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373273 ⟨1326564, by decide⟩ :=
  accepted_of_selected 12 373273 ⟨1326564, by decide⟩ ⟨12, 2, 0, 1326564, 373273, 2989, 65536⟩
    (by decide) selected_cut_47407

theorem selected_cut_47408 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 373274) = some ⟨12, 1, 0, 893903, 373274, 1, 65536⟩ := by
  decide +kernel

theorem context_12_373274_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373274 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 373274 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 373274, 1, 65536⟩
    (by decide) selected_cut_47408

theorem selected_cut_47409 : selected 9 ⟨1326614, by decide⟩
    (prefixPartial 12 373275) = some ⟨12, 2, 0, 1326614, 373275, 3097, 65536⟩ := by
  decide +kernel

theorem context_12_373275_1326614 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373275 ⟨1326614, by decide⟩ :=
  accepted_of_selected 12 373275 ⟨1326614, by decide⟩ ⟨12, 2, 0, 1326614, 373275, 3097, 65536⟩
    (by decide) selected_cut_47409

theorem unmarked_context_11_93318_1326615 : frontier 10 ⟨1326615, by decide⟩
    (prefixCache 11 93318) (prefixPartial 11 93318) = false := by
  decide +kernel

theorem node_context_11_93318_1326615 : EJMOriginalGlobalDAGData.nodes 10 ⟨1326615, by decide⟩ =
    .split (coordinate 11) (![⟨994572, by decide⟩,⟨1326564, by decide⟩,⟨893903, by decide⟩,⟨1326614, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93318_1326615 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93318 ⟨1326615, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93318
    ⟨1326615, by decide⟩ (by decide) (![⟨994572, by decide⟩,⟨1326564, by decide⟩,⟨893903, by decide⟩,⟨1326614, by decide⟩]) unmarked_context_11_93318_1326615 node_context_11_93318_1326615
  intro a
  fin_cases a
  · exact context_12_373272_994572
  · exact context_12_373273_1326564
  · exact context_12_373274_893903
  · exact context_12_373275_1326614

theorem selected_cut_47410 : selected 9 ⟨1326676, by decide⟩
    (prefixPartial 12 373276) = some ⟨12, 2, 0, 1326676, 373276, 3437, 65536⟩ := by
  decide +kernel

theorem context_12_373276_1326676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373276 ⟨1326676, by decide⟩ :=
  accepted_of_selected 12 373276 ⟨1326676, by decide⟩ ⟨12, 2, 0, 1326676, 373276, 3437, 65536⟩
    (by decide) selected_cut_47410

theorem selected_cut_47411 : selected 9 ⟨1326740, by decide⟩
    (prefixPartial 12 373277) = some ⟨12, 2, 0, 1326740, 373277, 3321, 65536⟩ := by
  decide +kernel

theorem context_12_373277_1326740 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373277 ⟨1326740, by decide⟩ :=
  accepted_of_selected 12 373277 ⟨1326740, by decide⟩ ⟨12, 2, 0, 1326740, 373277, 3321, 65536⟩
    (by decide) selected_cut_47411

theorem selected_cut_47412 : selected 9 ⟨1326785, by decide⟩
    (prefixPartial 12 373278) = some ⟨12, 2, 0, 1326785, 373278, 2897, 65536⟩ := by
  decide +kernel

theorem context_12_373278_1326785 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373278 ⟨1326785, by decide⟩ :=
  accepted_of_selected 12 373278 ⟨1326785, by decide⟩ ⟨12, 2, 0, 1326785, 373278, 2897, 65536⟩
    (by decide) selected_cut_47412

theorem selected_cut_47413 : selected 9 ⟨1326836, by decide⟩
    (prefixPartial 12 373279) = some ⟨12, 2, 0, 1326836, 373279, 3101, 65536⟩ := by
  decide +kernel

theorem context_12_373279_1326836 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373279 ⟨1326836, by decide⟩ :=
  accepted_of_selected 12 373279 ⟨1326836, by decide⟩ ⟨12, 2, 0, 1326836, 373279, 3101, 65536⟩
    (by decide) selected_cut_47413

theorem unmarked_context_11_93319_1326837 : frontier 10 ⟨1326837, by decide⟩
    (prefixCache 11 93319) (prefixPartial 11 93319) = false := by
  decide +kernel

theorem node_context_11_93319_1326837 : EJMOriginalGlobalDAGData.nodes 10 ⟨1326837, by decide⟩ =
    .split (coordinate 11) (![⟨1326676, by decide⟩,⟨1326740, by decide⟩,⟨1326785, by decide⟩,⟨1326836, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93319_1326837 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93319 ⟨1326837, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93319
    ⟨1326837, by decide⟩ (by decide) (![⟨1326676, by decide⟩,⟨1326740, by decide⟩,⟨1326785, by decide⟩,⟨1326836, by decide⟩]) unmarked_context_11_93319_1326837 node_context_11_93319_1326837
  intro a
  fin_cases a
  · exact context_12_373276_1326676
  · exact context_12_373277_1326740
  · exact context_12_373278_1326785
  · exact context_12_373279_1326836

theorem unmarked_context_10_23329_1326838 : frontier 11 ⟨1326838, by decide⟩
    (prefixCache 10 23329) (prefixPartial 10 23329) = false := by
  decide +kernel

theorem node_context_10_23329_1326838 : EJMOriginalGlobalDAGData.nodes 11 ⟨1326838, by decide⟩ =
    .split (coordinate 10) (![⟨1326520, by decide⟩,⟨815620, by decide⟩,⟨1326615, by decide⟩,⟨1326837, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23329_1326838 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23329 ⟨1326838, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23329
    ⟨1326838, by decide⟩ (by decide) (![⟨1326520, by decide⟩,⟨815620, by decide⟩,⟨1326615, by decide⟩,⟨1326837, by decide⟩]) unmarked_context_10_23329_1326838 node_context_10_23329_1326838
  intro a
  fin_cases a
  · exact context_11_93316_1326520
  · exact context_11_93317_815620
  · exact context_11_93318_1326615
  · exact context_11_93319_1326837

theorem selected_cut_47414 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 373280) = some ⟨12, 1, 0, 435790, 373280, 1, 65536⟩ := by
  decide +kernel

theorem context_12_373280_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373280 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 373280 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 373280, 1, 65536⟩
    (by decide) selected_cut_47414

theorem selected_cut_47415 : selected 9 ⟨1326881, by decide⟩
    (prefixPartial 12 373281) = some ⟨12, 2, 0, 1326881, 373281, 2621, 65536⟩ := by
  decide +kernel

theorem context_12_373281_1326881 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373281 ⟨1326881, by decide⟩ :=
  accepted_of_selected 12 373281 ⟨1326881, by decide⟩ ⟨12, 2, 0, 1326881, 373281, 2621, 65536⟩
    (by decide) selected_cut_47415

theorem selected_cut_47416 : selected 9 ⟨1326920, by decide⟩
    (prefixPartial 12 373282) = some ⟨12, 2, 0, 1326920, 373282, 2281, 65536⟩ := by
  decide +kernel

theorem context_12_373282_1326920 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373282 ⟨1326920, by decide⟩ :=
  accepted_of_selected 12 373282 ⟨1326920, by decide⟩ ⟨12, 2, 0, 1326920, 373282, 2281, 65536⟩
    (by decide) selected_cut_47416

theorem selected_cut_47417 : selected 9 ⟨1326961, by decide⟩
    (prefixPartial 12 373283) = some ⟨12, 2, 0, 1326961, 373283, 2353, 65536⟩ := by
  decide +kernel

theorem context_12_373283_1326961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373283 ⟨1326961, by decide⟩ :=
  accepted_of_selected 12 373283 ⟨1326961, by decide⟩ ⟨12, 2, 0, 1326961, 373283, 2353, 65536⟩
    (by decide) selected_cut_47417

theorem unmarked_context_11_93320_1326962 : frontier 10 ⟨1326962, by decide⟩
    (prefixCache 11 93320) (prefixPartial 11 93320) = false := by
  decide +kernel

theorem node_context_11_93320_1326962 : EJMOriginalGlobalDAGData.nodes 10 ⟨1326962, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨1326881, by decide⟩,⟨1326920, by decide⟩,⟨1326961, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93320_1326962 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93320 ⟨1326962, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93320
    ⟨1326962, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨1326881, by decide⟩,⟨1326920, by decide⟩,⟨1326961, by decide⟩]) unmarked_context_11_93320_1326962 node_context_11_93320_1326962
  intro a
  fin_cases a
  · exact context_12_373280_435790
  · exact context_12_373281_1326881
  · exact context_12_373282_1326920
  · exact context_12_373283_1326961

theorem selected_cut_47418 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 373284) = some ⟨12, 1, 0, 435790, 373284, 1, 65536⟩ := by
  decide +kernel

theorem context_12_373284_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373284 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 373284 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 373284, 1, 65536⟩
    (by decide) selected_cut_47418

theorem selected_cut_47419 : selected 9 ⟨365907, by decide⟩
    (prefixPartial 12 373285) = some ⟨12, 1, 0, 365907, 373285, 1, 65536⟩ := by
  decide +kernel

theorem context_12_373285_365907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373285 ⟨365907, by decide⟩ :=
  accepted_of_selected 12 373285 ⟨365907, by decide⟩ ⟨12, 1, 0, 365907, 373285, 1, 65536⟩
    (by decide) selected_cut_47419

theorem selected_cut_47420 : selected 9 ⟨1327016, by decide⟩
    (prefixPartial 12 373286) = some ⟨12, 2, 0, 1327016, 373286, 2969, 65536⟩ := by
  decide +kernel

theorem context_12_373286_1327016 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373286 ⟨1327016, by decide⟩ :=
  accepted_of_selected 12 373286 ⟨1327016, by decide⟩ ⟨12, 2, 0, 1327016, 373286, 2969, 65536⟩
    (by decide) selected_cut_47420

theorem selected_cut_47421 : selected 9 ⟨1327066, by decide⟩
    (prefixPartial 12 373287) = some ⟨12, 2, 0, 1327066, 373287, 2861, 65536⟩ := by
  decide +kernel

theorem context_12_373287_1327066 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373287 ⟨1327066, by decide⟩ :=
  accepted_of_selected 12 373287 ⟨1327066, by decide⟩ ⟨12, 2, 0, 1327066, 373287, 2861, 65536⟩
    (by decide) selected_cut_47421

theorem unmarked_context_11_93321_1327067 : frontier 10 ⟨1327067, by decide⟩
    (prefixCache 11 93321) (prefixPartial 11 93321) = false := by
  decide +kernel

theorem node_context_11_93321_1327067 : EJMOriginalGlobalDAGData.nodes 10 ⟨1327067, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨365907, by decide⟩,⟨1327016, by decide⟩,⟨1327066, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93321_1327067 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93321 ⟨1327067, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93321
    ⟨1327067, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨365907, by decide⟩,⟨1327016, by decide⟩,⟨1327066, by decide⟩]) unmarked_context_11_93321_1327067 node_context_11_93321_1327067
  intro a
  fin_cases a
  · exact context_12_373284_435790
  · exact context_12_373285_365907
  · exact context_12_373286_1327016
  · exact context_12_373287_1327066

theorem selected_cut_47422 : selected 10 ⟨1327068, by decide⟩
    (prefixPartial 11 93322) = some ⟨11, 2, 0, 1327068, 93322, 5, 262144⟩ := by
  decide +kernel

theorem context_11_93322_1327068 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93322 ⟨1327068, by decide⟩ :=
  accepted_of_selected 11 93322 ⟨1327068, by decide⟩ ⟨11, 2, 0, 1327068, 93322, 5, 262144⟩
    (by decide) selected_cut_47422

theorem selected_cut_47423 : selected 9 ⟨1327115, by decide⟩
    (prefixPartial 12 373292) = some ⟨12, 2, 0, 1327115, 373292, 2953, 65536⟩ := by
  decide +kernel

theorem context_12_373292_1327115 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373292 ⟨1327115, by decide⟩ :=
  accepted_of_selected 12 373292 ⟨1327115, by decide⟩ ⟨12, 2, 0, 1327115, 373292, 2953, 65536⟩
    (by decide) selected_cut_47423

theorem selected_cut_47424 : selected 9 ⟨1327184, by decide⟩
    (prefixPartial 12 373293) = some ⟨12, 2, 0, 1327184, 373293, 2953, 65536⟩ := by
  decide +kernel

theorem context_12_373293_1327184 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373293 ⟨1327184, by decide⟩ :=
  accepted_of_selected 12 373293 ⟨1327184, by decide⟩ ⟨12, 2, 0, 1327184, 373293, 2953, 65536⟩
    (by decide) selected_cut_47424

theorem selected_cut_47425 : selected 9 ⟨1327229, by decide⟩
    (prefixPartial 12 373294) = some ⟨12, 2, 0, 1327229, 373294, 2521, 65536⟩ := by
  decide +kernel

theorem context_12_373294_1327229 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373294 ⟨1327229, by decide⟩ :=
  accepted_of_selected 12 373294 ⟨1327229, by decide⟩ ⟨12, 2, 0, 1327229, 373294, 2521, 65536⟩
    (by decide) selected_cut_47425

theorem selected_cut_47426 : selected 9 ⟨265052, by decide⟩
    (prefixPartial 12 373295) = some ⟨12, 1, 0, 265052, 373295, 1, 65536⟩ := by
  decide +kernel

theorem context_12_373295_265052 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 373295 ⟨265052, by decide⟩ :=
  accepted_of_selected 12 373295 ⟨265052, by decide⟩ ⟨12, 1, 0, 265052, 373295, 1, 65536⟩
    (by decide) selected_cut_47426

theorem unmarked_context_11_93323_1327230 : frontier 10 ⟨1327230, by decide⟩
    (prefixCache 11 93323) (prefixPartial 11 93323) = false := by
  decide +kernel

theorem node_context_11_93323_1327230 : EJMOriginalGlobalDAGData.nodes 10 ⟨1327230, by decide⟩ =
    .split (coordinate 11) (![⟨1327115, by decide⟩,⟨1327184, by decide⟩,⟨1327229, by decide⟩,⟨265052, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93323_1327230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93323 ⟨1327230, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93323
    ⟨1327230, by decide⟩ (by decide) (![⟨1327115, by decide⟩,⟨1327184, by decide⟩,⟨1327229, by decide⟩,⟨265052, by decide⟩]) unmarked_context_11_93323_1327230 node_context_11_93323_1327230
  intro a
  fin_cases a
  · exact context_12_373292_1327115
  · exact context_12_373293_1327184
  · exact context_12_373294_1327229
  · exact context_12_373295_265052

theorem unmarked_context_10_23330_1327231 : frontier 11 ⟨1327231, by decide⟩
    (prefixCache 10 23330) (prefixPartial 10 23330) = false := by
  decide +kernel

theorem node_context_10_23330_1327231 : EJMOriginalGlobalDAGData.nodes 11 ⟨1327231, by decide⟩ =
    .split (coordinate 10) (![⟨1326962, by decide⟩,⟨1327067, by decide⟩,⟨1327068, by decide⟩,⟨1327230, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23330_1327231 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23330 ⟨1327231, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23330
    ⟨1327231, by decide⟩ (by decide) (![⟨1326962, by decide⟩,⟨1327067, by decide⟩,⟨1327068, by decide⟩,⟨1327230, by decide⟩]) unmarked_context_10_23330_1327231 node_context_10_23330_1327231
  intro a
  fin_cases a
  · exact context_11_93320_1326962
  · exact context_11_93321_1327067
  · exact context_11_93322_1327068
  · exact context_11_93323_1327230

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
