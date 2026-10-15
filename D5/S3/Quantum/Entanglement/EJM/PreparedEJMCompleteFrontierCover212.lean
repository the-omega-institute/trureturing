/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover211
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_20354 : selected 9 ⟨522481, by decide⟩
    (prefixPartial 12 73829) = some ⟨12, 2, 0, 522481, 73829, 2393, 65536⟩ := by
  decide +kernel

theorem context_12_73829_522481 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73829 ⟨522481, by decide⟩ :=
  accepted_of_selected 12 73829 ⟨522481, by decide⟩ ⟨12, 2, 0, 522481, 73829, 2393, 65536⟩
    (by decide) selected_cut_20354

theorem selected_cut_20355 : selected 9 ⟨522549, by decide⟩
    (prefixPartial 12 73830) = some ⟨12, 2, 0, 522549, 73830, 1573, 65536⟩ := by
  decide +kernel

theorem context_12_73830_522549 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73830 ⟨522549, by decide⟩ :=
  accepted_of_selected 12 73830 ⟨522549, by decide⟩ ⟨12, 2, 0, 522549, 73830, 1573, 65536⟩
    (by decide) selected_cut_20355

theorem selected_cut_20356 : selected 9 ⟨522606, by decide⟩
    (prefixPartial 12 73831) = some ⟨12, 2, 0, 522606, 73831, 2509, 65536⟩ := by
  decide +kernel

theorem context_12_73831_522606 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73831 ⟨522606, by decide⟩ :=
  accepted_of_selected 12 73831 ⟨522606, by decide⟩ ⟨12, 2, 0, 522606, 73831, 2509, 65536⟩
    (by decide) selected_cut_20356

theorem unmarked_context_11_18457_522607 : frontier 10 ⟨522607, by decide⟩
    (prefixCache 11 18457) (prefixPartial 11 18457) = false := by
  decide +kernel

theorem node_context_11_18457_522607 : EJMOriginalGlobalDAGData.nodes 10 ⟨522607, by decide⟩ =
    .split (coordinate 11) (![⟨4595, by decide⟩,⟨522481, by decide⟩,⟨522549, by decide⟩,⟨522606, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18457_522607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18457 ⟨522607, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18457
    ⟨522607, by decide⟩ (by decide) (![⟨4595, by decide⟩,⟨522481, by decide⟩,⟨522549, by decide⟩,⟨522606, by decide⟩]) unmarked_context_11_18457_522607 node_context_11_18457_522607
  intro a
  fin_cases a
  · exact context_12_73828_4595
  · exact context_12_73829_522481
  · exact context_12_73830_522549
  · exact context_12_73831_522606

theorem selected_cut_20357 : selected 10 ⟨522684, by decide⟩
    (prefixPartial 11 18458) = some ⟨11, 2, 0, 522684, 18458, 4061, 262144⟩ := by
  decide +kernel

theorem context_11_18458_522684 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18458 ⟨522684, by decide⟩ :=
  accepted_of_selected 11 18458 ⟨522684, by decide⟩ ⟨11, 2, 0, 522684, 18458, 4061, 262144⟩
    (by decide) selected_cut_20357

theorem selected_cut_20358 : selected 10 ⟨522720, by decide⟩
    (prefixPartial 11 18459) = some ⟨11, 2, 0, 522720, 18459, 1433, 262144⟩ := by
  decide +kernel

theorem context_11_18459_522720 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18459 ⟨522720, by decide⟩ :=
  accepted_of_selected 11 18459 ⟨522720, by decide⟩ ⟨11, 2, 0, 522720, 18459, 1433, 262144⟩
    (by decide) selected_cut_20358

theorem unmarked_context_10_4614_522721 : frontier 11 ⟨522721, by decide⟩
    (prefixCache 10 4614) (prefixPartial 10 4614) = false := by
  decide +kernel

theorem node_context_10_4614_522721 : EJMOriginalGlobalDAGData.nodes 11 ⟨522721, by decide⟩ =
    .split (coordinate 10) (![⟨522439, by decide⟩,⟨522607, by decide⟩,⟨522684, by decide⟩,⟨522720, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4614_522721 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4614 ⟨522721, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4614
    ⟨522721, by decide⟩ (by decide) (![⟨522439, by decide⟩,⟨522607, by decide⟩,⟨522684, by decide⟩,⟨522720, by decide⟩]) unmarked_context_10_4614_522721 node_context_10_4614_522721
  intro a
  fin_cases a
  · exact context_11_18456_522439
  · exact context_11_18457_522607
  · exact context_11_18458_522684
  · exact context_11_18459_522720

theorem selected_cut_20359 : selected 9 ⟨522821, by decide⟩
    (prefixPartial 12 73840) = some ⟨12, 2, 0, 522821, 73840, 953, 65536⟩ := by
  decide +kernel

theorem context_12_73840_522821 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73840 ⟨522821, by decide⟩ :=
  accepted_of_selected 12 73840 ⟨522821, by decide⟩ ⟨12, 2, 0, 522821, 73840, 953, 65536⟩
    (by decide) selected_cut_20359

theorem selected_cut_20360 : selected 9 ⟨522852, by decide⟩
    (prefixPartial 12 73841) = some ⟨12, 2, 0, 522852, 73841, 2069, 65536⟩ := by
  decide +kernel

theorem context_12_73841_522852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73841 ⟨522852, by decide⟩ :=
  accepted_of_selected 12 73841 ⟨522852, by decide⟩ ⟨12, 2, 0, 522852, 73841, 2069, 65536⟩
    (by decide) selected_cut_20360

theorem selected_cut_20361 : selected 9 ⟨522882, by decide⟩
    (prefixPartial 12 73842) = some ⟨12, 2, 0, 522882, 73842, 1949, 65536⟩ := by
  decide +kernel

theorem context_12_73842_522882 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73842 ⟨522882, by decide⟩ :=
  accepted_of_selected 12 73842 ⟨522882, by decide⟩ ⟨12, 2, 0, 522882, 73842, 1949, 65536⟩
    (by decide) selected_cut_20361

theorem selected_cut_20362 : selected 9 ⟨522917, by decide⟩
    (prefixPartial 12 73843) = some ⟨12, 2, 0, 522917, 73843, 1965, 65536⟩ := by
  decide +kernel

theorem context_12_73843_522917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73843 ⟨522917, by decide⟩ :=
  accepted_of_selected 12 73843 ⟨522917, by decide⟩ ⟨12, 2, 0, 522917, 73843, 1965, 65536⟩
    (by decide) selected_cut_20362

theorem unmarked_context_11_18460_522918 : frontier 10 ⟨522918, by decide⟩
    (prefixCache 11 18460) (prefixPartial 11 18460) = false := by
  decide +kernel

theorem node_context_11_18460_522918 : EJMOriginalGlobalDAGData.nodes 10 ⟨522918, by decide⟩ =
    .split (coordinate 11) (![⟨522821, by decide⟩,⟨522852, by decide⟩,⟨522882, by decide⟩,⟨522917, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18460_522918 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18460 ⟨522918, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18460
    ⟨522918, by decide⟩ (by decide) (![⟨522821, by decide⟩,⟨522852, by decide⟩,⟨522882, by decide⟩,⟨522917, by decide⟩]) unmarked_context_11_18460_522918 node_context_11_18460_522918
  intro a
  fin_cases a
  · exact context_12_73840_522821
  · exact context_12_73841_522852
  · exact context_12_73842_522882
  · exact context_12_73843_522917

theorem selected_cut_20363 : selected 9 ⟨522953, by decide⟩
    (prefixPartial 12 73844) = some ⟨12, 2, 0, 522953, 73844, 1733, 65536⟩ := by
  decide +kernel

theorem context_12_73844_522953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73844 ⟨522953, by decide⟩ :=
  accepted_of_selected 12 73844 ⟨522953, by decide⟩ ⟨12, 2, 0, 522953, 73844, 1733, 65536⟩
    (by decide) selected_cut_20363

theorem selected_cut_20364 : selected 9 ⟨522984, by decide⟩
    (prefixPartial 12 73845) = some ⟨12, 2, 0, 522984, 73845, 2025, 65536⟩ := by
  decide +kernel

theorem context_12_73845_522984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73845 ⟨522984, by decide⟩ :=
  accepted_of_selected 12 73845 ⟨522984, by decide⟩ ⟨12, 2, 0, 522984, 73845, 2025, 65536⟩
    (by decide) selected_cut_20364

theorem selected_cut_20365 : selected 9 ⟨523030, by decide⟩
    (prefixPartial 12 73846) = some ⟨12, 2, 0, 523030, 73846, 2013, 65536⟩ := by
  decide +kernel

theorem context_12_73846_523030 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73846 ⟨523030, by decide⟩ :=
  accepted_of_selected 12 73846 ⟨523030, by decide⟩ ⟨12, 2, 0, 523030, 73846, 2013, 65536⟩
    (by decide) selected_cut_20365

theorem selected_cut_20366 : selected 9 ⟨523078, by decide⟩
    (prefixPartial 12 73847) = some ⟨12, 2, 0, 523078, 73847, 2045, 65536⟩ := by
  decide +kernel

theorem context_12_73847_523078 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73847 ⟨523078, by decide⟩ :=
  accepted_of_selected 12 73847 ⟨523078, by decide⟩ ⟨12, 2, 0, 523078, 73847, 2045, 65536⟩
    (by decide) selected_cut_20366

theorem unmarked_context_11_18461_523079 : frontier 10 ⟨523079, by decide⟩
    (prefixCache 11 18461) (prefixPartial 11 18461) = false := by
  decide +kernel

theorem node_context_11_18461_523079 : EJMOriginalGlobalDAGData.nodes 10 ⟨523079, by decide⟩ =
    .split (coordinate 11) (![⟨522953, by decide⟩,⟨522984, by decide⟩,⟨523030, by decide⟩,⟨523078, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18461_523079 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18461 ⟨523079, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18461
    ⟨523079, by decide⟩ (by decide) (![⟨522953, by decide⟩,⟨522984, by decide⟩,⟨523030, by decide⟩,⟨523078, by decide⟩]) unmarked_context_11_18461_523079 node_context_11_18461_523079
  intro a
  fin_cases a
  · exact context_12_73844_522953
  · exact context_12_73845_522984
  · exact context_12_73846_523030
  · exact context_12_73847_523078

theorem selected_cut_20367 : selected 9 ⟨523109, by decide⟩
    (prefixPartial 12 73848) = some ⟨12, 2, 0, 523109, 73848, 1665, 65536⟩ := by
  decide +kernel

theorem context_12_73848_523109 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73848 ⟨523109, by decide⟩ :=
  accepted_of_selected 12 73848 ⟨523109, by decide⟩ ⟨12, 2, 0, 523109, 73848, 1665, 65536⟩
    (by decide) selected_cut_20367

theorem selected_cut_20368 : selected 9 ⟨523169, by decide⟩
    (prefixPartial 12 73849) = some ⟨12, 2, 0, 523169, 73849, 2089, 65536⟩ := by
  decide +kernel

theorem context_12_73849_523169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73849 ⟨523169, by decide⟩ :=
  accepted_of_selected 12 73849 ⟨523169, by decide⟩ ⟨12, 2, 0, 523169, 73849, 2089, 65536⟩
    (by decide) selected_cut_20368

theorem selected_cut_20369 : selected 9 ⟨523199, by decide⟩
    (prefixPartial 12 73850) = some ⟨12, 2, 0, 523199, 73850, 1805, 65536⟩ := by
  decide +kernel

theorem context_12_73850_523199 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73850 ⟨523199, by decide⟩ :=
  accepted_of_selected 12 73850 ⟨523199, by decide⟩ ⟨12, 2, 0, 523199, 73850, 1805, 65536⟩
    (by decide) selected_cut_20369

theorem selected_cut_20370 : selected 9 ⟨523237, by decide⟩
    (prefixPartial 12 73851) = some ⟨12, 2, 0, 523237, 73851, 1817, 65536⟩ := by
  decide +kernel

theorem context_12_73851_523237 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73851 ⟨523237, by decide⟩ :=
  accepted_of_selected 12 73851 ⟨523237, by decide⟩ ⟨12, 2, 0, 523237, 73851, 1817, 65536⟩
    (by decide) selected_cut_20370

theorem unmarked_context_11_18462_523238 : frontier 10 ⟨523238, by decide⟩
    (prefixCache 11 18462) (prefixPartial 11 18462) = false := by
  decide +kernel

theorem node_context_11_18462_523238 : EJMOriginalGlobalDAGData.nodes 10 ⟨523238, by decide⟩ =
    .split (coordinate 11) (![⟨523109, by decide⟩,⟨523169, by decide⟩,⟨523199, by decide⟩,⟨523237, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18462_523238 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18462 ⟨523238, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18462
    ⟨523238, by decide⟩ (by decide) (![⟨523109, by decide⟩,⟨523169, by decide⟩,⟨523199, by decide⟩,⟨523237, by decide⟩]) unmarked_context_11_18462_523238 node_context_11_18462_523238
  intro a
  fin_cases a
  · exact context_12_73848_523109
  · exact context_12_73849_523169
  · exact context_12_73850_523199
  · exact context_12_73851_523237

theorem selected_cut_20371 : selected 9 ⟨523265, by decide⟩
    (prefixPartial 12 73852) = some ⟨12, 2, 0, 523265, 73852, 1393, 65536⟩ := by
  decide +kernel

theorem context_12_73852_523265 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73852 ⟨523265, by decide⟩ :=
  accepted_of_selected 12 73852 ⟨523265, by decide⟩ ⟨12, 2, 0, 523265, 73852, 1393, 65536⟩
    (by decide) selected_cut_20371

theorem selected_cut_20372 : selected 9 ⟨523303, by decide⟩
    (prefixPartial 12 73853) = some ⟨12, 2, 0, 523303, 73853, 1713, 65536⟩ := by
  decide +kernel

theorem context_12_73853_523303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73853 ⟨523303, by decide⟩ :=
  accepted_of_selected 12 73853 ⟨523303, by decide⟩ ⟨12, 2, 0, 523303, 73853, 1713, 65536⟩
    (by decide) selected_cut_20372

theorem selected_cut_20373 : selected 9 ⟨523342, by decide⟩
    (prefixPartial 12 73854) = some ⟨12, 2, 0, 523342, 73854, 1629, 65536⟩ := by
  decide +kernel

theorem context_12_73854_523342 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73854 ⟨523342, by decide⟩ :=
  accepted_of_selected 12 73854 ⟨523342, by decide⟩ ⟨12, 2, 0, 523342, 73854, 1629, 65536⟩
    (by decide) selected_cut_20373

theorem selected_cut_20374 : selected 9 ⟨523384, by decide⟩
    (prefixPartial 12 73855) = some ⟨12, 2, 0, 523384, 73855, 1553, 65536⟩ := by
  decide +kernel

theorem context_12_73855_523384 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73855 ⟨523384, by decide⟩ :=
  accepted_of_selected 12 73855 ⟨523384, by decide⟩ ⟨12, 2, 0, 523384, 73855, 1553, 65536⟩
    (by decide) selected_cut_20374

theorem unmarked_context_11_18463_523385 : frontier 10 ⟨523385, by decide⟩
    (prefixCache 11 18463) (prefixPartial 11 18463) = false := by
  decide +kernel

theorem node_context_11_18463_523385 : EJMOriginalGlobalDAGData.nodes 10 ⟨523385, by decide⟩ =
    .split (coordinate 11) (![⟨523265, by decide⟩,⟨523303, by decide⟩,⟨523342, by decide⟩,⟨523384, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18463_523385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18463 ⟨523385, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18463
    ⟨523385, by decide⟩ (by decide) (![⟨523265, by decide⟩,⟨523303, by decide⟩,⟨523342, by decide⟩,⟨523384, by decide⟩]) unmarked_context_11_18463_523385 node_context_11_18463_523385
  intro a
  fin_cases a
  · exact context_12_73852_523265
  · exact context_12_73853_523303
  · exact context_12_73854_523342
  · exact context_12_73855_523384

theorem unmarked_context_10_4615_523386 : frontier 11 ⟨523386, by decide⟩
    (prefixCache 10 4615) (prefixPartial 10 4615) = false := by
  decide +kernel

theorem node_context_10_4615_523386 : EJMOriginalGlobalDAGData.nodes 11 ⟨523386, by decide⟩ =
    .split (coordinate 10) (![⟨522918, by decide⟩,⟨523079, by decide⟩,⟨523238, by decide⟩,⟨523385, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4615_523386 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4615 ⟨523386, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4615
    ⟨523386, by decide⟩ (by decide) (![⟨522918, by decide⟩,⟨523079, by decide⟩,⟨523238, by decide⟩,⟨523385, by decide⟩]) unmarked_context_10_4615_523386 node_context_10_4615_523386
  intro a
  fin_cases a
  · exact context_11_18460_522918
  · exact context_11_18461_523079
  · exact context_11_18462_523238
  · exact context_11_18463_523385

theorem unmarked_context_9_1153_523387 : frontier 12 ⟨523387, by decide⟩
    (prefixCache 9 1153) (prefixPartial 9 1153) = false := by
  decide +kernel

theorem node_context_9_1153_523387 : EJMOriginalGlobalDAGData.nodes 12 ⟨523387, by decide⟩ =
    .split (coordinate 9) (![⟨145424, by decide⟩,⟨522227, by decide⟩,⟨522721, by decide⟩,⟨523386, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1153_523387 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1153 ⟨523387, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1153
    ⟨523387, by decide⟩ (by decide) (![⟨145424, by decide⟩,⟨522227, by decide⟩,⟨522721, by decide⟩,⟨523386, by decide⟩]) unmarked_context_9_1153_523387 node_context_9_1153_523387
  intro a
  fin_cases a
  · exact context_10_4612_145424
  · exact context_10_4613_522227
  · exact context_10_4614_522721
  · exact context_10_4615_523386

theorem selected_cut_20375 : selected 11 ⟨145424, by decide⟩
    (prefixPartial 10 4616) = some ⟨10, 1, 0, 145424, 4616, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_4616_145424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4616 ⟨145424, by decide⟩ :=
  accepted_of_selected 10 4616 ⟨145424, by decide⟩ ⟨10, 1, 0, 145424, 4616, 1, 1048576⟩
    (by decide) selected_cut_20375

theorem selected_cut_20376 : selected 10 ⟨523479, by decide⟩
    (prefixPartial 11 18468) = some ⟨11, 2, 0, 523479, 18468, 3325, 262144⟩ := by
  decide +kernel

theorem context_11_18468_523479 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18468 ⟨523479, by decide⟩ :=
  accepted_of_selected 11 18468 ⟨523479, by decide⟩ ⟨11, 2, 0, 523479, 18468, 3325, 262144⟩
    (by decide) selected_cut_20376

theorem selected_cut_20377 : selected 10 ⟨523544, by decide⟩
    (prefixPartial 11 18469) = some ⟨11, 2, 0, 523544, 18469, 2833, 262144⟩ := by
  decide +kernel

theorem context_11_18469_523544 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18469 ⟨523544, by decide⟩ :=
  accepted_of_selected 11 18469 ⟨523544, by decide⟩ ⟨11, 2, 0, 523544, 18469, 2833, 262144⟩
    (by decide) selected_cut_20377

theorem selected_cut_20378 : selected 10 ⟨523595, by decide⟩
    (prefixPartial 11 18470) = some ⟨11, 2, 0, 523595, 18470, 1577, 262144⟩ := by
  decide +kernel

theorem context_11_18470_523595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18470 ⟨523595, by decide⟩ :=
  accepted_of_selected 11 18470 ⟨523595, by decide⟩ ⟨11, 2, 0, 523595, 18470, 1577, 262144⟩
    (by decide) selected_cut_20378

theorem selected_cut_20379 : selected 10 ⟨523607, by decide⟩
    (prefixPartial 11 18471) = some ⟨11, 2, 0, 523607, 18471, 517, 262144⟩ := by
  decide +kernel

theorem context_11_18471_523607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18471 ⟨523607, by decide⟩ :=
  accepted_of_selected 11 18471 ⟨523607, by decide⟩ ⟨11, 2, 0, 523607, 18471, 517, 262144⟩
    (by decide) selected_cut_20379

theorem unmarked_context_10_4617_523608 : frontier 11 ⟨523608, by decide⟩
    (prefixCache 10 4617) (prefixPartial 10 4617) = false := by
  decide +kernel

theorem node_context_10_4617_523608 : EJMOriginalGlobalDAGData.nodes 11 ⟨523608, by decide⟩ =
    .split (coordinate 10) (![⟨523479, by decide⟩,⟨523544, by decide⟩,⟨523595, by decide⟩,⟨523607, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4617_523608 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4617 ⟨523608, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4617
    ⟨523608, by decide⟩ (by decide) (![⟨523479, by decide⟩,⟨523544, by decide⟩,⟨523595, by decide⟩,⟨523607, by decide⟩]) unmarked_context_10_4617_523608 node_context_10_4617_523608
  intro a
  fin_cases a
  · exact context_11_18468_523479
  · exact context_11_18469_523544
  · exact context_11_18470_523595
  · exact context_11_18471_523607

theorem selected_cut_20380 : selected 11 ⟨145424, by decide⟩
    (prefixPartial 10 4618) = some ⟨10, 1, 0, 145424, 4618, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_4618_145424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4618 ⟨145424, by decide⟩ :=
  accepted_of_selected 10 4618 ⟨145424, by decide⟩ ⟨10, 1, 0, 145424, 4618, 1, 1048576⟩
    (by decide) selected_cut_20380

theorem selected_cut_20381 : selected 10 ⟨523684, by decide⟩
    (prefixPartial 11 18476) = some ⟨11, 2, 0, 523684, 18476, 2209, 262144⟩ := by
  decide +kernel

theorem context_11_18476_523684 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18476 ⟨523684, by decide⟩ :=
  accepted_of_selected 11 18476 ⟨523684, by decide⟩ ⟨11, 2, 0, 523684, 18476, 2209, 262144⟩
    (by decide) selected_cut_20381

theorem selected_cut_20382 : selected 10 ⟨523740, by decide⟩
    (prefixPartial 11 18477) = some ⟨11, 2, 0, 523740, 18477, 2565, 262144⟩ := by
  decide +kernel

theorem context_11_18477_523740 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18477 ⟨523740, by decide⟩ :=
  accepted_of_selected 11 18477 ⟨523740, by decide⟩ ⟨11, 2, 0, 523740, 18477, 2565, 262144⟩
    (by decide) selected_cut_20382

theorem selected_cut_20383 : selected 10 ⟨523800, by decide⟩
    (prefixPartial 11 18478) = some ⟨11, 2, 0, 523800, 18478, 1913, 262144⟩ := by
  decide +kernel

theorem context_11_18478_523800 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18478 ⟨523800, by decide⟩ :=
  accepted_of_selected 11 18478 ⟨523800, by decide⟩ ⟨11, 2, 0, 523800, 18478, 1913, 262144⟩
    (by decide) selected_cut_20383

theorem selected_cut_20384 : selected 10 ⟨523826, by decide⟩
    (prefixPartial 11 18479) = some ⟨11, 2, 0, 523826, 18479, 1145, 262144⟩ := by
  decide +kernel

theorem context_11_18479_523826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18479 ⟨523826, by decide⟩ :=
  accepted_of_selected 11 18479 ⟨523826, by decide⟩ ⟨11, 2, 0, 523826, 18479, 1145, 262144⟩
    (by decide) selected_cut_20384

theorem unmarked_context_10_4619_523827 : frontier 11 ⟨523827, by decide⟩
    (prefixCache 10 4619) (prefixPartial 10 4619) = false := by
  decide +kernel

theorem node_context_10_4619_523827 : EJMOriginalGlobalDAGData.nodes 11 ⟨523827, by decide⟩ =
    .split (coordinate 10) (![⟨523684, by decide⟩,⟨523740, by decide⟩,⟨523800, by decide⟩,⟨523826, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4619_523827 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4619 ⟨523827, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4619
    ⟨523827, by decide⟩ (by decide) (![⟨523684, by decide⟩,⟨523740, by decide⟩,⟨523800, by decide⟩,⟨523826, by decide⟩]) unmarked_context_10_4619_523827 node_context_10_4619_523827
  intro a
  fin_cases a
  · exact context_11_18476_523684
  · exact context_11_18477_523740
  · exact context_11_18478_523800
  · exact context_11_18479_523826

theorem unmarked_context_9_1154_523828 : frontier 12 ⟨523828, by decide⟩
    (prefixCache 9 1154) (prefixPartial 9 1154) = false := by
  decide +kernel

theorem node_context_9_1154_523828 : EJMOriginalGlobalDAGData.nodes 12 ⟨523828, by decide⟩ =
    .split (coordinate 9) (![⟨145424, by decide⟩,⟨523608, by decide⟩,⟨145424, by decide⟩,⟨523827, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1154_523828 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1154 ⟨523828, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1154
    ⟨523828, by decide⟩ (by decide) (![⟨145424, by decide⟩,⟨523608, by decide⟩,⟨145424, by decide⟩,⟨523827, by decide⟩]) unmarked_context_9_1154_523828 node_context_9_1154_523828
  intro a
  fin_cases a
  · exact context_10_4616_145424
  · exact context_10_4617_523608
  · exact context_10_4618_145424
  · exact context_10_4619_523827

theorem selected_cut_20385 : selected 12 ⟨523864, by decide⟩
    (prefixPartial 9 1155) = some ⟨9, 2, 0, 523864, 1155, 845, 4194304⟩ := by
  decide +kernel

theorem context_9_1155_523864 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1155 ⟨523864, by decide⟩ :=
  accepted_of_selected 9 1155 ⟨523864, by decide⟩ ⟨9, 2, 0, 523864, 1155, 845, 4194304⟩
    (by decide) selected_cut_20385

theorem unmarked_context_8_288_523865 : frontier 13 ⟨523865, by decide⟩
    (prefixCache 8 288) (prefixPartial 8 288) = false := by
  decide +kernel

theorem node_context_8_288_523865 : EJMOriginalGlobalDAGData.nodes 13 ⟨523865, by decide⟩ =
    .split (coordinate 8) (![⟨521273, by decide⟩,⟨523387, by decide⟩,⟨523828, by decide⟩,⟨523864, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_288_523865 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 288 ⟨523865, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 288
    ⟨523865, by decide⟩ (by decide) (![⟨521273, by decide⟩,⟨523387, by decide⟩,⟨523828, by decide⟩,⟨523864, by decide⟩]) unmarked_context_8_288_523865 node_context_8_288_523865
  intro a
  fin_cases a
  · exact context_9_1152_521273
  · exact context_9_1153_523387
  · exact context_9_1154_523828
  · exact context_9_1155_523864

theorem selected_cut_20386 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 18496) = some ⟨11, 1, 0, 434745, 18496, 1, 262144⟩ := by
  decide +kernel

theorem context_11_18496_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18496 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 18496 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 18496, 1, 262144⟩
    (by decide) selected_cut_20386

theorem selected_cut_20387 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 73988) = some ⟨12, 1, 0, 448748, 73988, 1, 65536⟩ := by
  decide +kernel

theorem context_12_73988_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73988 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 73988 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 73988, 1, 65536⟩
    (by decide) selected_cut_20387

theorem selected_cut_20388 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 73989) = some ⟨12, 1, 0, 34034, 73989, 1, 65536⟩ := by
  decide +kernel

theorem context_12_73989_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73989 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 73989 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 73989, 1, 65536⟩
    (by decide) selected_cut_20388

theorem selected_cut_20389 : selected 9 ⟨523996, by decide⟩
    (prefixPartial 12 73990) = some ⟨12, 2, 0, 523996, 73990, 3921, 65536⟩ := by
  decide +kernel

theorem context_12_73990_523996 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73990 ⟨523996, by decide⟩ :=
  accepted_of_selected 12 73990 ⟨523996, by decide⟩ ⟨12, 2, 0, 523996, 73990, 3921, 65536⟩
    (by decide) selected_cut_20389

theorem selected_cut_20390 : selected 8 ⟨524064, by decide⟩
    (prefixPartial 13 295964) = some ⟨13, 2, 0, 524064, 295964, 2089, 16384⟩ := by
  decide +kernel

theorem context_13_295964_524064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 295964 ⟨524064, by decide⟩ :=
  accepted_of_selected 13 295964 ⟨524064, by decide⟩ ⟨13, 2, 0, 524064, 295964, 2089, 16384⟩
    (by decide) selected_cut_20390

theorem selected_cut_20391 : selected 8 ⟨524106, by decide⟩
    (prefixPartial 13 295965) = some ⟨13, 2, 0, 524106, 295965, 1317, 16384⟩ := by
  decide +kernel

theorem context_13_295965_524106 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 295965 ⟨524106, by decide⟩ :=
  accepted_of_selected 13 295965 ⟨524106, by decide⟩ ⟨13, 2, 0, 524106, 295965, 1317, 16384⟩
    (by decide) selected_cut_20391

theorem selected_cut_20392 : selected 8 ⟨524124, by decide⟩
    (prefixPartial 13 295966) = some ⟨13, 2, 0, 524124, 295966, 597, 16384⟩ := by
  decide +kernel

theorem context_13_295966_524124 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 295966 ⟨524124, by decide⟩ :=
  accepted_of_selected 13 295966 ⟨524124, by decide⟩ ⟨13, 2, 0, 524124, 295966, 597, 16384⟩
    (by decide) selected_cut_20392

theorem selected_cut_20393 : selected 8 ⟨524129, by decide⟩
    (prefixPartial 13 295967) = some ⟨13, 2, 0, 524129, 295967, 117, 16384⟩ := by
  decide +kernel

theorem context_13_295967_524129 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 295967 ⟨524129, by decide⟩ :=
  accepted_of_selected 13 295967 ⟨524129, by decide⟩ ⟨13, 2, 0, 524129, 295967, 117, 16384⟩
    (by decide) selected_cut_20393

theorem unmarked_context_12_73991_524130 : frontier 9 ⟨524130, by decide⟩
    (prefixCache 12 73991) (prefixPartial 12 73991) = false := by
  decide +kernel

theorem node_context_12_73991_524130 : EJMOriginalGlobalDAGData.nodes 9 ⟨524130, by decide⟩ =
    .split (coordinate 12) (![⟨524064, by decide⟩,⟨524106, by decide⟩,⟨524124, by decide⟩,⟨524129, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_73991_524130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73991 ⟨524130, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 73991
    ⟨524130, by decide⟩ (by decide) (![⟨524064, by decide⟩,⟨524106, by decide⟩,⟨524124, by decide⟩,⟨524129, by decide⟩]) unmarked_context_12_73991_524130 node_context_12_73991_524130
  intro a
  fin_cases a
  · exact context_13_295964_524064
  · exact context_13_295965_524106
  · exact context_13_295966_524124
  · exact context_13_295967_524129

theorem unmarked_context_11_18497_524131 : frontier 10 ⟨524131, by decide⟩
    (prefixCache 11 18497) (prefixPartial 11 18497) = false := by
  decide +kernel

theorem node_context_11_18497_524131 : EJMOriginalGlobalDAGData.nodes 10 ⟨524131, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨523996, by decide⟩,⟨524130, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18497_524131 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18497 ⟨524131, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18497
    ⟨524131, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨523996, by decide⟩,⟨524130, by decide⟩]) unmarked_context_11_18497_524131 node_context_11_18497_524131
  intro a
  fin_cases a
  · exact context_12_73988_448748
  · exact context_12_73989_34034
  · exact context_12_73990_523996
  · exact context_12_73991_524130

theorem selected_cut_20394 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 73992) = some ⟨12, 1, 0, 448748, 73992, 1, 65536⟩ := by
  decide +kernel

theorem context_12_73992_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73992 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 73992 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 73992, 1, 65536⟩
    (by decide) selected_cut_20394

theorem selected_cut_20395 : selected 8 ⟨524211, by decide⟩
    (prefixPartial 13 295972) = some ⟨13, 2, 0, 524211, 295972, 2801, 16384⟩ := by
  decide +kernel

theorem context_13_295972_524211 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 295972 ⟨524211, by decide⟩ :=
  accepted_of_selected 13 295972 ⟨524211, by decide⟩ ⟨13, 2, 0, 524211, 295972, 2801, 16384⟩
    (by decide) selected_cut_20395

theorem selected_cut_20396 : selected 8 ⟨524248, by decide⟩
    (prefixPartial 13 295973) = some ⟨13, 2, 0, 524248, 295973, 2253, 16384⟩ := by
  decide +kernel

theorem context_13_295973_524248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 295973 ⟨524248, by decide⟩ :=
  accepted_of_selected 13 295973 ⟨524248, by decide⟩ ⟨13, 2, 0, 524248, 295973, 2253, 16384⟩
    (by decide) selected_cut_20396

theorem selected_cut_20397 : selected 8 ⟨524286, by decide⟩
    (prefixPartial 13 295974) = some ⟨13, 2, 0, 524286, 295974, 2309, 16384⟩ := by
  decide +kernel

theorem context_13_295974_524286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 295974 ⟨524286, by decide⟩ :=
  accepted_of_selected 13 295974 ⟨524286, by decide⟩ ⟨13, 2, 0, 524286, 295974, 2309, 16384⟩
    (by decide) selected_cut_20397

theorem selected_cut_20398 : selected 8 ⟨524300, by decide⟩
    (prefixPartial 13 295975) = some ⟨13, 2, 0, 524300, 295975, 1069, 16384⟩ := by
  decide +kernel

theorem context_13_295975_524300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 295975 ⟨524300, by decide⟩ :=
  accepted_of_selected 13 295975 ⟨524300, by decide⟩ ⟨13, 2, 0, 524300, 295975, 1069, 16384⟩
    (by decide) selected_cut_20398

theorem unmarked_context_12_73993_524301 : frontier 9 ⟨524301, by decide⟩
    (prefixCache 12 73993) (prefixPartial 12 73993) = false := by
  decide +kernel

theorem node_context_12_73993_524301 : EJMOriginalGlobalDAGData.nodes 9 ⟨524301, by decide⟩ =
    .split (coordinate 12) (![⟨524211, by decide⟩,⟨524248, by decide⟩,⟨524286, by decide⟩,⟨524300, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_73993_524301 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73993 ⟨524301, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 73993
    ⟨524301, by decide⟩ (by decide) (![⟨524211, by decide⟩,⟨524248, by decide⟩,⟨524286, by decide⟩,⟨524300, by decide⟩]) unmarked_context_12_73993_524301 node_context_12_73993_524301
  intro a
  fin_cases a
  · exact context_13_295972_524211
  · exact context_13_295973_524248
  · exact context_13_295974_524286
  · exact context_13_295975_524300

theorem selected_cut_20399 : selected 9 ⟨524302, by decide⟩
    (prefixPartial 12 73994) = some ⟨12, 1, 0, 524302, 73994, 1, 65536⟩ := by
  decide +kernel

theorem context_12_73994_524302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73994 ⟨524302, by decide⟩ :=
  accepted_of_selected 12 73994 ⟨524302, by decide⟩ ⟨12, 1, 0, 524302, 73994, 1, 65536⟩
    (by decide) selected_cut_20399

theorem selected_cut_20400 : selected 8 ⟨524364, by decide⟩
    (prefixPartial 13 295980) = some ⟨13, 2, 0, 524364, 295980, 2509, 16384⟩ := by
  decide +kernel

theorem context_13_295980_524364 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 295980 ⟨524364, by decide⟩ :=
  accepted_of_selected 13 295980 ⟨524364, by decide⟩ ⟨13, 2, 0, 524364, 295980, 2509, 16384⟩
    (by decide) selected_cut_20400

theorem selected_cut_20401 : selected 8 ⟨524395, by decide⟩
    (prefixPartial 13 295981) = some ⟨13, 2, 0, 524395, 295981, 2653, 16384⟩ := by
  decide +kernel

theorem context_13_295981_524395 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 295981 ⟨524395, by decide⟩ :=
  accepted_of_selected 13 295981 ⟨524395, by decide⟩ ⟨13, 2, 0, 524395, 295981, 2653, 16384⟩
    (by decide) selected_cut_20401

theorem selected_cut_20402 : selected 8 ⟨524422, by decide⟩
    (prefixPartial 13 295982) = some ⟨13, 2, 0, 524422, 295982, 2213, 16384⟩ := by
  decide +kernel

theorem context_13_295982_524422 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 295982 ⟨524422, by decide⟩ :=
  accepted_of_selected 13 295982 ⟨524422, by decide⟩ ⟨13, 2, 0, 524422, 295982, 2213, 16384⟩
    (by decide) selected_cut_20402

theorem selected_cut_20403 : selected 8 ⟨524430, by decide⟩
    (prefixPartial 13 295983) = some ⟨13, 2, 0, 524430, 295983, 985, 16384⟩ := by
  decide +kernel

theorem context_13_295983_524430 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 295983 ⟨524430, by decide⟩ :=
  accepted_of_selected 13 295983 ⟨524430, by decide⟩ ⟨13, 2, 0, 524430, 295983, 985, 16384⟩
    (by decide) selected_cut_20403

theorem unmarked_context_12_73995_524431 : frontier 9 ⟨524431, by decide⟩
    (prefixCache 12 73995) (prefixPartial 12 73995) = false := by
  decide +kernel

theorem node_context_12_73995_524431 : EJMOriginalGlobalDAGData.nodes 9 ⟨524431, by decide⟩ =
    .split (coordinate 12) (![⟨524364, by decide⟩,⟨524395, by decide⟩,⟨524422, by decide⟩,⟨524430, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_73995_524431 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73995 ⟨524431, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 73995
    ⟨524431, by decide⟩ (by decide) (![⟨524364, by decide⟩,⟨524395, by decide⟩,⟨524422, by decide⟩,⟨524430, by decide⟩]) unmarked_context_12_73995_524431 node_context_12_73995_524431
  intro a
  fin_cases a
  · exact context_13_295980_524364
  · exact context_13_295981_524395
  · exact context_13_295982_524422
  · exact context_13_295983_524430

theorem unmarked_context_11_18498_524432 : frontier 10 ⟨524432, by decide⟩
    (prefixCache 11 18498) (prefixPartial 11 18498) = false := by
  decide +kernel

theorem node_context_11_18498_524432 : EJMOriginalGlobalDAGData.nodes 10 ⟨524432, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨524301, by decide⟩,⟨524302, by decide⟩,⟨524431, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18498_524432 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18498 ⟨524432, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18498
    ⟨524432, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨524301, by decide⟩,⟨524302, by decide⟩,⟨524431, by decide⟩]) unmarked_context_11_18498_524432 node_context_11_18498_524432
  intro a
  fin_cases a
  · exact context_12_73992_448748
  · exact context_12_73993_524301
  · exact context_12_73994_524302
  · exact context_12_73995_524431

theorem selected_cut_20404 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 73996) = some ⟨12, 1, 0, 448748, 73996, 1, 65536⟩ := by
  decide +kernel

theorem context_12_73996_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73996 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 73996 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 73996, 1, 65536⟩
    (by decide) selected_cut_20404

theorem selected_cut_20405 : selected 8 ⟨524464, by decide⟩
    (prefixPartial 13 295988) = some ⟨13, 2, 0, 524464, 295988, 1273, 16384⟩ := by
  decide +kernel

theorem context_13_295988_524464 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 295988 ⟨524464, by decide⟩ :=
  accepted_of_selected 13 295988 ⟨524464, by decide⟩ ⟨13, 2, 0, 524464, 295988, 1273, 16384⟩
    (by decide) selected_cut_20405

theorem selected_cut_20406 : selected 8 ⟨524486, by decide⟩
    (prefixPartial 13 295989) = some ⟨13, 2, 0, 524486, 295989, 1201, 16384⟩ := by
  decide +kernel

theorem context_13_295989_524486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 295989 ⟨524486, by decide⟩ :=
  accepted_of_selected 13 295989 ⟨524486, by decide⟩ ⟨13, 2, 0, 524486, 295989, 1201, 16384⟩
    (by decide) selected_cut_20406

theorem selected_cut_20407 : selected 8 ⟨524539, by decide⟩
    (prefixPartial 13 295990) = some ⟨13, 2, 0, 524539, 295990, 1737, 16384⟩ := by
  decide +kernel

theorem context_13_295990_524539 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 295990 ⟨524539, by decide⟩ :=
  accepted_of_selected 13 295990 ⟨524539, by decide⟩ ⟨13, 2, 0, 524539, 295990, 1737, 16384⟩
    (by decide) selected_cut_20407

theorem selected_cut_20408 : selected 8 ⟨265883, by decide⟩
    (prefixPartial 13 295991) = some ⟨13, 1, 0, 265883, 295991, 1, 16384⟩ := by
  decide +kernel

theorem context_13_295991_265883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 295991 ⟨265883, by decide⟩ :=
  accepted_of_selected 13 295991 ⟨265883, by decide⟩ ⟨13, 1, 0, 265883, 295991, 1, 16384⟩
    (by decide) selected_cut_20408

theorem unmarked_context_12_73997_524540 : frontier 9 ⟨524540, by decide⟩
    (prefixCache 12 73997) (prefixPartial 12 73997) = false := by
  decide +kernel

theorem node_context_12_73997_524540 : EJMOriginalGlobalDAGData.nodes 9 ⟨524540, by decide⟩ =
    .split (coordinate 12) (![⟨524464, by decide⟩,⟨524486, by decide⟩,⟨524539, by decide⟩,⟨265883, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_73997_524540 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73997 ⟨524540, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 73997
    ⟨524540, by decide⟩ (by decide) (![⟨524464, by decide⟩,⟨524486, by decide⟩,⟨524539, by decide⟩,⟨265883, by decide⟩]) unmarked_context_12_73997_524540 node_context_12_73997_524540
  intro a
  fin_cases a
  · exact context_13_295988_524464
  · exact context_13_295989_524486
  · exact context_13_295990_524539
  · exact context_13_295991_265883

theorem selected_cut_20409 : selected 8 ⟨524586, by decide⟩
    (prefixPartial 13 295992) = some ⟨13, 2, 0, 524586, 295992, 2253, 16384⟩ := by
  decide +kernel

theorem context_13_295992_524586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 295992 ⟨524586, by decide⟩ :=
  accepted_of_selected 13 295992 ⟨524586, by decide⟩ ⟨13, 2, 0, 524586, 295992, 2253, 16384⟩
    (by decide) selected_cut_20409

theorem selected_cut_20410 : selected 8 ⟨524617, by decide⟩
    (prefixPartial 13 295993) = some ⟨13, 2, 0, 524617, 295993, 2509, 16384⟩ := by
  decide +kernel

theorem context_13_295993_524617 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 295993 ⟨524617, by decide⟩ :=
  accepted_of_selected 13 295993 ⟨524617, by decide⟩ ⟨13, 2, 0, 524617, 295993, 2509, 16384⟩
    (by decide) selected_cut_20410

theorem selected_cut_20411 : selected 8 ⟨524638, by decide⟩
    (prefixPartial 13 295994) = some ⟨13, 2, 0, 524638, 295994, 1801, 16384⟩ := by
  decide +kernel

theorem context_13_295994_524638 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 295994 ⟨524638, by decide⟩ :=
  accepted_of_selected 13 295994 ⟨524638, by decide⟩ ⟨13, 2, 0, 524638, 295994, 1801, 16384⟩
    (by decide) selected_cut_20411

theorem selected_cut_20412 : selected 8 ⟨524647, by decide⟩
    (prefixPartial 13 295995) = some ⟨13, 2, 0, 524647, 295995, 1165, 16384⟩ := by
  decide +kernel

theorem context_13_295995_524647 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 295995 ⟨524647, by decide⟩ :=
  accepted_of_selected 13 295995 ⟨524647, by decide⟩ ⟨13, 2, 0, 524647, 295995, 1165, 16384⟩
    (by decide) selected_cut_20412

theorem unmarked_context_12_73998_524648 : frontier 9 ⟨524648, by decide⟩
    (prefixCache 12 73998) (prefixPartial 12 73998) = false := by
  decide +kernel

theorem node_context_12_73998_524648 : EJMOriginalGlobalDAGData.nodes 9 ⟨524648, by decide⟩ =
    .split (coordinate 12) (![⟨524586, by decide⟩,⟨524617, by decide⟩,⟨524638, by decide⟩,⟨524647, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_73998_524648 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73998 ⟨524648, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 73998
    ⟨524648, by decide⟩ (by decide) (![⟨524586, by decide⟩,⟨524617, by decide⟩,⟨524638, by decide⟩,⟨524647, by decide⟩]) unmarked_context_12_73998_524648 node_context_12_73998_524648
  intro a
  fin_cases a
  · exact context_13_295992_524586
  · exact context_13_295993_524617
  · exact context_13_295994_524638
  · exact context_13_295995_524647

theorem selected_cut_20413 : selected 9 ⟨518278, by decide⟩
    (prefixPartial 12 73999) = some ⟨12, 1, 0, 518278, 73999, 1, 65536⟩ := by
  decide +kernel

theorem context_12_73999_518278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 73999 ⟨518278, by decide⟩ :=
  accepted_of_selected 12 73999 ⟨518278, by decide⟩ ⟨12, 1, 0, 518278, 73999, 1, 65536⟩
    (by decide) selected_cut_20413

theorem unmarked_context_11_18499_524649 : frontier 10 ⟨524649, by decide⟩
    (prefixCache 11 18499) (prefixPartial 11 18499) = false := by
  decide +kernel

theorem node_context_11_18499_524649 : EJMOriginalGlobalDAGData.nodes 10 ⟨524649, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨524540, by decide⟩,⟨524648, by decide⟩,⟨518278, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18499_524649 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18499 ⟨524649, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18499
    ⟨524649, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨524540, by decide⟩,⟨524648, by decide⟩,⟨518278, by decide⟩]) unmarked_context_11_18499_524649 node_context_11_18499_524649
  intro a
  fin_cases a
  · exact context_12_73996_448748
  · exact context_12_73997_524540
  · exact context_12_73998_524648
  · exact context_12_73999_518278

theorem unmarked_context_10_4624_524650 : frontier 11 ⟨524650, by decide⟩
    (prefixCache 10 4624) (prefixPartial 10 4624) = false := by
  decide +kernel

theorem node_context_10_4624_524650 : EJMOriginalGlobalDAGData.nodes 11 ⟨524650, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨524131, by decide⟩,⟨524432, by decide⟩,⟨524649, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4624_524650 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4624 ⟨524650, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4624
    ⟨524650, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨524131, by decide⟩,⟨524432, by decide⟩,⟨524649, by decide⟩]) unmarked_context_10_4624_524650 node_context_10_4624_524650
  intro a
  fin_cases a
  · exact context_11_18496_434745
  · exact context_11_18497_524131
  · exact context_11_18498_524432
  · exact context_11_18499_524649

theorem selected_cut_20414 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 74000) = some ⟨12, 1, 0, 435160, 74000, 1, 65536⟩ := by
  decide +kernel

theorem context_12_74000_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74000 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 74000 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 74000, 1, 65536⟩
    (by decide) selected_cut_20414

theorem selected_cut_20415 : selected 8 ⟨524673, by decide⟩
    (prefixPartial 13 296004) = some ⟨13, 2, 0, 524673, 296004, 1405, 16384⟩ := by
  decide +kernel

theorem context_13_296004_524673 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296004 ⟨524673, by decide⟩ :=
  accepted_of_selected 13 296004 ⟨524673, by decide⟩ ⟨13, 2, 0, 524673, 296004, 1405, 16384⟩
    (by decide) selected_cut_20415

theorem selected_cut_20416 : selected 8 ⟨524693, by decide⟩
    (prefixPartial 13 296005) = some ⟨13, 2, 0, 524693, 296005, 1417, 16384⟩ := by
  decide +kernel

theorem context_13_296005_524693 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296005 ⟨524693, by decide⟩ :=
  accepted_of_selected 13 296005 ⟨524693, by decide⟩ ⟨13, 2, 0, 524693, 296005, 1417, 16384⟩
    (by decide) selected_cut_20416

theorem selected_cut_20417 : selected 8 ⟨524710, by decide⟩
    (prefixPartial 13 296006) = some ⟨13, 2, 0, 524710, 296006, 1249, 16384⟩ := by
  decide +kernel

theorem context_13_296006_524710 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296006 ⟨524710, by decide⟩ :=
  accepted_of_selected 13 296006 ⟨524710, by decide⟩ ⟨13, 2, 0, 524710, 296006, 1249, 16384⟩
    (by decide) selected_cut_20417

theorem selected_cut_20418 : selected 8 ⟨524717, by decide⟩
    (prefixPartial 13 296007) = some ⟨13, 2, 0, 524717, 296007, 693, 16384⟩ := by
  decide +kernel

theorem context_13_296007_524717 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296007 ⟨524717, by decide⟩ :=
  accepted_of_selected 13 296007 ⟨524717, by decide⟩ ⟨13, 2, 0, 524717, 296007, 693, 16384⟩
    (by decide) selected_cut_20418

theorem unmarked_context_12_74001_524718 : frontier 9 ⟨524718, by decide⟩
    (prefixCache 12 74001) (prefixPartial 12 74001) = false := by
  decide +kernel

theorem node_context_12_74001_524718 : EJMOriginalGlobalDAGData.nodes 9 ⟨524718, by decide⟩ =
    .split (coordinate 12) (![⟨524673, by decide⟩,⟨524693, by decide⟩,⟨524710, by decide⟩,⟨524717, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74001_524718 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74001 ⟨524718, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74001
    ⟨524718, by decide⟩ (by decide) (![⟨524673, by decide⟩,⟨524693, by decide⟩,⟨524710, by decide⟩,⟨524717, by decide⟩]) unmarked_context_12_74001_524718 node_context_12_74001_524718
  intro a
  fin_cases a
  · exact context_13_296004_524673
  · exact context_13_296005_524693
  · exact context_13_296006_524710
  · exact context_13_296007_524717

theorem selected_cut_20419 : selected 8 ⟨524737, by decide⟩
    (prefixPartial 13 296008) = some ⟨13, 2, 0, 524737, 296008, 1341, 16384⟩ := by
  decide +kernel

theorem context_13_296008_524737 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296008 ⟨524737, by decide⟩ :=
  accepted_of_selected 13 296008 ⟨524737, by decide⟩ ⟨13, 2, 0, 524737, 296008, 1341, 16384⟩
    (by decide) selected_cut_20419

theorem selected_cut_20420 : selected 8 ⟨524760, by decide⟩
    (prefixPartial 13 296009) = some ⟨13, 2, 0, 524760, 296009, 1853, 16384⟩ := by
  decide +kernel

theorem context_13_296009_524760 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296009 ⟨524760, by decide⟩ :=
  accepted_of_selected 13 296009 ⟨524760, by decide⟩ ⟨13, 2, 0, 524760, 296009, 1853, 16384⟩
    (by decide) selected_cut_20420

theorem selected_cut_20421 : selected 8 ⟨524774, by decide⟩
    (prefixPartial 13 296010) = some ⟨13, 2, 0, 524774, 296010, 949, 16384⟩ := by
  decide +kernel

theorem context_13_296010_524774 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296010 ⟨524774, by decide⟩ :=
  accepted_of_selected 13 296010 ⟨524774, by decide⟩ ⟨13, 2, 0, 524774, 296010, 949, 16384⟩
    (by decide) selected_cut_20421

theorem selected_cut_20422 : selected 8 ⟨524781, by decide⟩
    (prefixPartial 13 296011) = some ⟨13, 2, 0, 524781, 296011, 729, 16384⟩ := by
  decide +kernel

theorem context_13_296011_524781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296011 ⟨524781, by decide⟩ :=
  accepted_of_selected 13 296011 ⟨524781, by decide⟩ ⟨13, 2, 0, 524781, 296011, 729, 16384⟩
    (by decide) selected_cut_20422

theorem unmarked_context_12_74002_524782 : frontier 9 ⟨524782, by decide⟩
    (prefixCache 12 74002) (prefixPartial 12 74002) = false := by
  decide +kernel

theorem node_context_12_74002_524782 : EJMOriginalGlobalDAGData.nodes 9 ⟨524782, by decide⟩ =
    .split (coordinate 12) (![⟨524737, by decide⟩,⟨524760, by decide⟩,⟨524774, by decide⟩,⟨524781, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74002_524782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74002 ⟨524782, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74002
    ⟨524782, by decide⟩ (by decide) (![⟨524737, by decide⟩,⟨524760, by decide⟩,⟨524774, by decide⟩,⟨524781, by decide⟩]) unmarked_context_12_74002_524782 node_context_12_74002_524782
  intro a
  fin_cases a
  · exact context_13_296008_524737
  · exact context_13_296009_524760
  · exact context_13_296010_524774
  · exact context_13_296011_524781

theorem selected_cut_20423 : selected 8 ⟨524803, by decide⟩
    (prefixPartial 13 296012) = some ⟨13, 2, 0, 524803, 296012, 1461, 16384⟩ := by
  decide +kernel

theorem context_13_296012_524803 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296012 ⟨524803, by decide⟩ :=
  accepted_of_selected 13 296012 ⟨524803, by decide⟩ ⟨13, 2, 0, 524803, 296012, 1461, 16384⟩
    (by decide) selected_cut_20423

theorem selected_cut_20424 : selected 8 ⟨524826, by decide⟩
    (prefixPartial 13 296013) = some ⟨13, 2, 0, 524826, 296013, 2013, 16384⟩ := by
  decide +kernel

theorem context_13_296013_524826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296013 ⟨524826, by decide⟩ :=
  accepted_of_selected 13 296013 ⟨524826, by decide⟩ ⟨13, 2, 0, 524826, 296013, 2013, 16384⟩
    (by decide) selected_cut_20424

theorem selected_cut_20425 : selected 8 ⟨524841, by decide⟩
    (prefixPartial 13 296014) = some ⟨13, 2, 0, 524841, 296014, 1173, 16384⟩ := by
  decide +kernel

theorem context_13_296014_524841 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296014 ⟨524841, by decide⟩ :=
  accepted_of_selected 13 296014 ⟨524841, by decide⟩ ⟨13, 2, 0, 524841, 296014, 1173, 16384⟩
    (by decide) selected_cut_20425

theorem selected_cut_20426 : selected 8 ⟨524845, by decide⟩
    (prefixPartial 13 296015) = some ⟨13, 2, 0, 524845, 296015, 633, 16384⟩ := by
  decide +kernel

theorem context_13_296015_524845 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296015 ⟨524845, by decide⟩ :=
  accepted_of_selected 13 296015 ⟨524845, by decide⟩ ⟨13, 2, 0, 524845, 296015, 633, 16384⟩
    (by decide) selected_cut_20426

theorem unmarked_context_12_74003_524846 : frontier 9 ⟨524846, by decide⟩
    (prefixCache 12 74003) (prefixPartial 12 74003) = false := by
  decide +kernel

theorem node_context_12_74003_524846 : EJMOriginalGlobalDAGData.nodes 9 ⟨524846, by decide⟩ =
    .split (coordinate 12) (![⟨524803, by decide⟩,⟨524826, by decide⟩,⟨524841, by decide⟩,⟨524845, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74003_524846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74003 ⟨524846, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74003
    ⟨524846, by decide⟩ (by decide) (![⟨524803, by decide⟩,⟨524826, by decide⟩,⟨524841, by decide⟩,⟨524845, by decide⟩]) unmarked_context_12_74003_524846 node_context_12_74003_524846
  intro a
  fin_cases a
  · exact context_13_296012_524803
  · exact context_13_296013_524826
  · exact context_13_296014_524841
  · exact context_13_296015_524845

theorem unmarked_context_11_18500_524847 : frontier 10 ⟨524847, by decide⟩
    (prefixCache 11 18500) (prefixPartial 11 18500) = false := by
  decide +kernel

theorem node_context_11_18500_524847 : EJMOriginalGlobalDAGData.nodes 10 ⟨524847, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨524718, by decide⟩,⟨524782, by decide⟩,⟨524846, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18500_524847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18500 ⟨524847, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18500
    ⟨524847, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨524718, by decide⟩,⟨524782, by decide⟩,⟨524846, by decide⟩]) unmarked_context_11_18500_524847 node_context_11_18500_524847
  intro a
  fin_cases a
  · exact context_12_74000_435160
  · exact context_12_74001_524718
  · exact context_12_74002_524782
  · exact context_12_74003_524846

theorem selected_cut_20427 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 74004) = some ⟨12, 1, 0, 435160, 74004, 1, 65536⟩ := by
  decide +kernel

theorem context_12_74004_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74004 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 74004 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 74004, 1, 65536⟩
    (by decide) selected_cut_20427

theorem selected_cut_20428 : selected 9 ⟨439069, by decide⟩
    (prefixPartial 12 74005) = some ⟨12, 1, 0, 439069, 74005, 1, 65536⟩ := by
  decide +kernel

theorem context_12_74005_439069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74005 ⟨439069, by decide⟩ :=
  accepted_of_selected 12 74005 ⟨439069, by decide⟩ ⟨12, 1, 0, 439069, 74005, 1, 65536⟩
    (by decide) selected_cut_20428

theorem selected_cut_20429 : selected 8 ⟨524884, by decide⟩
    (prefixPartial 13 296024) = some ⟨13, 2, 0, 524884, 296024, 1505, 16384⟩ := by
  decide +kernel

theorem context_13_296024_524884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296024 ⟨524884, by decide⟩ :=
  accepted_of_selected 13 296024 ⟨524884, by decide⟩ ⟨13, 2, 0, 524884, 296024, 1505, 16384⟩
    (by decide) selected_cut_20429

theorem selected_cut_20430 : selected 8 ⟨524908, by decide⟩
    (prefixPartial 13 296025) = some ⟨13, 2, 0, 524908, 296025, 1993, 16384⟩ := by
  decide +kernel

theorem context_13_296025_524908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296025 ⟨524908, by decide⟩ :=
  accepted_of_selected 13 296025 ⟨524908, by decide⟩ ⟨13, 2, 0, 524908, 296025, 1993, 16384⟩
    (by decide) selected_cut_20430

theorem selected_cut_20431 : selected 8 ⟨524925, by decide⟩
    (prefixPartial 13 296026) = some ⟨13, 2, 0, 524925, 296026, 1257, 16384⟩ := by
  decide +kernel

theorem context_13_296026_524925 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296026 ⟨524925, by decide⟩ :=
  accepted_of_selected 13 296026 ⟨524925, by decide⟩ ⟨13, 2, 0, 524925, 296026, 1257, 16384⟩
    (by decide) selected_cut_20431

theorem selected_cut_20432 : selected 8 ⟨524932, by decide⟩
    (prefixPartial 13 296027) = some ⟨13, 2, 0, 524932, 296027, 853, 16384⟩ := by
  decide +kernel

theorem context_13_296027_524932 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296027 ⟨524932, by decide⟩ :=
  accepted_of_selected 13 296027 ⟨524932, by decide⟩ ⟨13, 2, 0, 524932, 296027, 853, 16384⟩
    (by decide) selected_cut_20432

theorem unmarked_context_12_74006_524933 : frontier 9 ⟨524933, by decide⟩
    (prefixCache 12 74006) (prefixPartial 12 74006) = false := by
  decide +kernel

theorem node_context_12_74006_524933 : EJMOriginalGlobalDAGData.nodes 9 ⟨524933, by decide⟩ =
    .split (coordinate 12) (![⟨524884, by decide⟩,⟨524908, by decide⟩,⟨524925, by decide⟩,⟨524932, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74006_524933 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74006 ⟨524933, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74006
    ⟨524933, by decide⟩ (by decide) (![⟨524884, by decide⟩,⟨524908, by decide⟩,⟨524925, by decide⟩,⟨524932, by decide⟩]) unmarked_context_12_74006_524933 node_context_12_74006_524933
  intro a
  fin_cases a
  · exact context_13_296024_524884
  · exact context_13_296025_524908
  · exact context_13_296026_524925
  · exact context_13_296027_524932

theorem selected_cut_20433 : selected 8 ⟨524969, by decide⟩
    (prefixPartial 13 296028) = some ⟨13, 2, 0, 524969, 296028, 1661, 16384⟩ := by
  decide +kernel

theorem context_13_296028_524969 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296028 ⟨524969, by decide⟩ :=
  accepted_of_selected 13 296028 ⟨524969, by decide⟩ ⟨13, 2, 0, 524969, 296028, 1661, 16384⟩
    (by decide) selected_cut_20433

theorem selected_cut_20434 : selected 8 ⟨524994, by decide⟩
    (prefixPartial 13 296029) = some ⟨13, 2, 0, 524994, 296029, 2205, 16384⟩ := by
  decide +kernel

theorem context_13_296029_524994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296029 ⟨524994, by decide⟩ :=
  accepted_of_selected 13 296029 ⟨524994, by decide⟩ ⟨13, 2, 0, 524994, 296029, 2205, 16384⟩
    (by decide) selected_cut_20434

theorem selected_cut_20435 : selected 8 ⟨525012, by decide⟩
    (prefixPartial 13 296030) = some ⟨13, 2, 0, 525012, 296030, 1649, 16384⟩ := by
  decide +kernel

theorem context_13_296030_525012 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296030 ⟨525012, by decide⟩ :=
  accepted_of_selected 13 296030 ⟨525012, by decide⟩ ⟨13, 2, 0, 525012, 296030, 1649, 16384⟩
    (by decide) selected_cut_20435

theorem selected_cut_20436 : selected 8 ⟨525020, by decide⟩
    (prefixPartial 13 296031) = some ⟨13, 2, 0, 525020, 296031, 641, 16384⟩ := by
  decide +kernel

theorem context_13_296031_525020 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296031 ⟨525020, by decide⟩ :=
  accepted_of_selected 13 296031 ⟨525020, by decide⟩ ⟨13, 2, 0, 525020, 296031, 641, 16384⟩
    (by decide) selected_cut_20436

theorem unmarked_context_12_74007_525021 : frontier 9 ⟨525021, by decide⟩
    (prefixCache 12 74007) (prefixPartial 12 74007) = false := by
  decide +kernel

theorem node_context_12_74007_525021 : EJMOriginalGlobalDAGData.nodes 9 ⟨525021, by decide⟩ =
    .split (coordinate 12) (![⟨524969, by decide⟩,⟨524994, by decide⟩,⟨525012, by decide⟩,⟨525020, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74007_525021 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74007 ⟨525021, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74007
    ⟨525021, by decide⟩ (by decide) (![⟨524969, by decide⟩,⟨524994, by decide⟩,⟨525012, by decide⟩,⟨525020, by decide⟩]) unmarked_context_12_74007_525021 node_context_12_74007_525021
  intro a
  fin_cases a
  · exact context_13_296028_524969
  · exact context_13_296029_524994
  · exact context_13_296030_525012
  · exact context_13_296031_525020

theorem unmarked_context_11_18501_525022 : frontier 10 ⟨525022, by decide⟩
    (prefixCache 11 18501) (prefixPartial 11 18501) = false := by
  decide +kernel

theorem node_context_11_18501_525022 : EJMOriginalGlobalDAGData.nodes 10 ⟨525022, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨439069, by decide⟩,⟨524933, by decide⟩,⟨525021, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18501_525022 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18501 ⟨525022, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18501
    ⟨525022, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨439069, by decide⟩,⟨524933, by decide⟩,⟨525021, by decide⟩]) unmarked_context_11_18501_525022 node_context_11_18501_525022
  intro a
  fin_cases a
  · exact context_12_74004_435160
  · exact context_12_74005_439069
  · exact context_12_74006_524933
  · exact context_12_74007_525021

theorem selected_cut_20437 : selected 8 ⟨525049, by decide⟩
    (prefixPartial 13 296032) = some ⟨13, 2, 0, 525049, 296032, 1721, 16384⟩ := by
  decide +kernel

theorem context_13_296032_525049 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296032 ⟨525049, by decide⟩ :=
  accepted_of_selected 13 296032 ⟨525049, by decide⟩ ⟨13, 2, 0, 525049, 296032, 1721, 16384⟩
    (by decide) selected_cut_20437

theorem selected_cut_20438 : selected 8 ⟨525077, by decide⟩
    (prefixPartial 13 296033) = some ⟨13, 2, 0, 525077, 296033, 2825, 16384⟩ := by
  decide +kernel

theorem context_13_296033_525077 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296033 ⟨525077, by decide⟩ :=
  accepted_of_selected 13 296033 ⟨525077, by decide⟩ ⟨13, 2, 0, 525077, 296033, 2825, 16384⟩
    (by decide) selected_cut_20438

theorem selected_cut_20439 : selected 8 ⟨525095, by decide⟩
    (prefixPartial 13 296034) = some ⟨13, 2, 0, 525095, 296034, 1789, 16384⟩ := by
  decide +kernel

theorem context_13_296034_525095 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296034 ⟨525095, by decide⟩ :=
  accepted_of_selected 13 296034 ⟨525095, by decide⟩ ⟨13, 2, 0, 525095, 296034, 1789, 16384⟩
    (by decide) selected_cut_20439

theorem selected_cut_20440 : selected 8 ⟨525101, by decide⟩
    (prefixPartial 13 296035) = some ⟨13, 2, 0, 525101, 296035, 849, 16384⟩ := by
  decide +kernel

theorem context_13_296035_525101 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296035 ⟨525101, by decide⟩ :=
  accepted_of_selected 13 296035 ⟨525101, by decide⟩ ⟨13, 2, 0, 525101, 296035, 849, 16384⟩
    (by decide) selected_cut_20440

theorem unmarked_context_12_74008_525102 : frontier 9 ⟨525102, by decide⟩
    (prefixCache 12 74008) (prefixPartial 12 74008) = false := by
  decide +kernel

theorem node_context_12_74008_525102 : EJMOriginalGlobalDAGData.nodes 9 ⟨525102, by decide⟩ =
    .split (coordinate 12) (![⟨525049, by decide⟩,⟨525077, by decide⟩,⟨525095, by decide⟩,⟨525101, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74008_525102 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74008 ⟨525102, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74008
    ⟨525102, by decide⟩ (by decide) (![⟨525049, by decide⟩,⟨525077, by decide⟩,⟨525095, by decide⟩,⟨525101, by decide⟩]) unmarked_context_12_74008_525102 node_context_12_74008_525102
  intro a
  fin_cases a
  · exact context_13_296032_525049
  · exact context_13_296033_525077
  · exact context_13_296034_525095
  · exact context_13_296035_525101

theorem selected_cut_20441 : selected 8 ⟨525132, by decide⟩
    (prefixPartial 13 296036) = some ⟨13, 2, 0, 525132, 296036, 1641, 16384⟩ := by
  decide +kernel

theorem context_13_296036_525132 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296036 ⟨525132, by decide⟩ :=
  accepted_of_selected 13 296036 ⟨525132, by decide⟩ ⟨13, 2, 0, 525132, 296036, 1641, 16384⟩
    (by decide) selected_cut_20441

theorem selected_cut_20442 : selected 8 ⟨525157, by decide⟩
    (prefixPartial 13 296037) = some ⟨13, 2, 0, 525157, 296037, 1465, 16384⟩ := by
  decide +kernel

theorem context_13_296037_525157 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296037 ⟨525157, by decide⟩ :=
  accepted_of_selected 13 296037 ⟨525157, by decide⟩ ⟨13, 2, 0, 525157, 296037, 1465, 16384⟩
    (by decide) selected_cut_20442

theorem selected_cut_20443 : selected 8 ⟨525176, by decide⟩
    (prefixPartial 13 296038) = some ⟨13, 2, 0, 525176, 296038, 1617, 16384⟩ := by
  decide +kernel

theorem context_13_296038_525176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296038 ⟨525176, by decide⟩ :=
  accepted_of_selected 13 296038 ⟨525176, by decide⟩ ⟨13, 2, 0, 525176, 296038, 1617, 16384⟩
    (by decide) selected_cut_20443

theorem selected_cut_20444 : selected 8 ⟨525183, by decide⟩
    (prefixPartial 13 296039) = some ⟨13, 2, 0, 525183, 296039, 757, 16384⟩ := by
  decide +kernel

theorem context_13_296039_525183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296039 ⟨525183, by decide⟩ :=
  accepted_of_selected 13 296039 ⟨525183, by decide⟩ ⟨13, 2, 0, 525183, 296039, 757, 16384⟩
    (by decide) selected_cut_20444

theorem unmarked_context_12_74009_525184 : frontier 9 ⟨525184, by decide⟩
    (prefixCache 12 74009) (prefixPartial 12 74009) = false := by
  decide +kernel

theorem node_context_12_74009_525184 : EJMOriginalGlobalDAGData.nodes 9 ⟨525184, by decide⟩ =
    .split (coordinate 12) (![⟨525132, by decide⟩,⟨525157, by decide⟩,⟨525176, by decide⟩,⟨525183, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74009_525184 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74009 ⟨525184, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74009
    ⟨525184, by decide⟩ (by decide) (![⟨525132, by decide⟩,⟨525157, by decide⟩,⟨525176, by decide⟩,⟨525183, by decide⟩]) unmarked_context_12_74009_525184 node_context_12_74009_525184
  intro a
  fin_cases a
  · exact context_13_296036_525132
  · exact context_13_296037_525157
  · exact context_13_296038_525176
  · exact context_13_296039_525183

theorem selected_cut_20445 : selected 8 ⟨525206, by decide⟩
    (prefixPartial 13 296040) = some ⟨13, 2, 0, 525206, 296040, 1405, 16384⟩ := by
  decide +kernel

theorem context_13_296040_525206 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296040 ⟨525206, by decide⟩ :=
  accepted_of_selected 13 296040 ⟨525206, by decide⟩ ⟨13, 2, 0, 525206, 296040, 1405, 16384⟩
    (by decide) selected_cut_20445

theorem selected_cut_20446 : selected 8 ⟨525229, by decide⟩
    (prefixPartial 13 296041) = some ⟨13, 2, 0, 525229, 296041, 1925, 16384⟩ := by
  decide +kernel

theorem context_13_296041_525229 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296041 ⟨525229, by decide⟩ :=
  accepted_of_selected 13 296041 ⟨525229, by decide⟩ ⟨13, 2, 0, 525229, 296041, 1925, 16384⟩
    (by decide) selected_cut_20446

theorem selected_cut_20447 : selected 8 ⟨525245, by decide⟩
    (prefixPartial 13 296042) = some ⟨13, 2, 0, 525245, 296042, 1105, 16384⟩ := by
  decide +kernel

theorem context_13_296042_525245 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296042 ⟨525245, by decide⟩ :=
  accepted_of_selected 13 296042 ⟨525245, by decide⟩ ⟨13, 2, 0, 525245, 296042, 1105, 16384⟩
    (by decide) selected_cut_20447

theorem selected_cut_20448 : selected 8 ⟨525251, by decide⟩
    (prefixPartial 13 296043) = some ⟨13, 2, 0, 525251, 296043, 713, 16384⟩ := by
  decide +kernel

theorem context_13_296043_525251 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296043 ⟨525251, by decide⟩ :=
  accepted_of_selected 13 296043 ⟨525251, by decide⟩ ⟨13, 2, 0, 525251, 296043, 713, 16384⟩
    (by decide) selected_cut_20448

theorem unmarked_context_12_74010_525252 : frontier 9 ⟨525252, by decide⟩
    (prefixCache 12 74010) (prefixPartial 12 74010) = false := by
  decide +kernel

theorem node_context_12_74010_525252 : EJMOriginalGlobalDAGData.nodes 9 ⟨525252, by decide⟩ =
    .split (coordinate 12) (![⟨525206, by decide⟩,⟨525229, by decide⟩,⟨525245, by decide⟩,⟨525251, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74010_525252 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74010 ⟨525252, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74010
    ⟨525252, by decide⟩ (by decide) (![⟨525206, by decide⟩,⟨525229, by decide⟩,⟨525245, by decide⟩,⟨525251, by decide⟩]) unmarked_context_12_74010_525252 node_context_12_74010_525252
  intro a
  fin_cases a
  · exact context_13_296040_525206
  · exact context_13_296041_525229
  · exact context_13_296042_525245
  · exact context_13_296043_525251

theorem selected_cut_20449 : selected 8 ⟨525277, by decide⟩
    (prefixPartial 13 296044) = some ⟨13, 2, 0, 525277, 296044, 1489, 16384⟩ := by
  decide +kernel

theorem context_13_296044_525277 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296044 ⟨525277, by decide⟩ :=
  accepted_of_selected 13 296044 ⟨525277, by decide⟩ ⟨13, 2, 0, 525277, 296044, 1489, 16384⟩
    (by decide) selected_cut_20449

theorem selected_cut_20450 : selected 8 ⟨525301, by decide⟩
    (prefixPartial 13 296045) = some ⟨13, 2, 0, 525301, 296045, 2153, 16384⟩ := by
  decide +kernel

theorem context_13_296045_525301 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 296045 ⟨525301, by decide⟩ :=
  accepted_of_selected 13 296045 ⟨525301, by decide⟩ ⟨13, 2, 0, 525301, 296045, 2153, 16384⟩
    (by decide) selected_cut_20450

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
