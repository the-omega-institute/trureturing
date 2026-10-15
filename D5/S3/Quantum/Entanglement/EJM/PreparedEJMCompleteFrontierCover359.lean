/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover358
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_34466 : selected 9 ⟨893814, by decide⟩
    (prefixPartial 12 280070) = some ⟨12, 2, 0, 893814, 280070, 3249, 65536⟩ := by
  decide +kernel

theorem context_12_280070_893814 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 280070 ⟨893814, by decide⟩ :=
  accepted_of_selected 12 280070 ⟨893814, by decide⟩ ⟨12, 2, 0, 893814, 280070, 3249, 65536⟩
    (by decide) selected_cut_34466

theorem selected_cut_34467 : selected 9 ⟨893901, by decide⟩
    (prefixPartial 12 280071) = some ⟨12, 2, 0, 893901, 280071, 3521, 65536⟩ := by
  decide +kernel

theorem context_12_280071_893901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 280071 ⟨893901, by decide⟩ :=
  accepted_of_selected 12 280071 ⟨893901, by decide⟩ ⟨12, 2, 0, 893901, 280071, 3521, 65536⟩
    (by decide) selected_cut_34467

theorem unmarked_context_11_70017_893902 : frontier 10 ⟨893902, by decide⟩
    (prefixCache 11 70017) (prefixPartial 11 70017) = false := by
  decide +kernel

theorem node_context_11_70017_893902 : EJMOriginalGlobalDAGData.nodes 10 ⟨893902, by decide⟩ =
    .split (coordinate 11) (![⟨895, by decide⟩,⟨893744, by decide⟩,⟨893814, by decide⟩,⟨893901, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70017_893902 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70017 ⟨893902, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70017
    ⟨893902, by decide⟩ (by decide) (![⟨895, by decide⟩,⟨893744, by decide⟩,⟨893814, by decide⟩,⟨893901, by decide⟩]) unmarked_context_11_70017_893902 node_context_11_70017_893902
  intro a
  fin_cases a
  · exact context_12_280068_895
  · exact context_12_280069_893744
  · exact context_12_280070_893814
  · exact context_12_280071_893901

theorem selected_cut_34468 : selected 10 ⟨894000, by decide⟩
    (prefixPartial 11 70018) = some ⟨11, 2, 0, 894000, 70018, 3741, 262144⟩ := by
  decide +kernel

theorem context_11_70018_894000 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70018 ⟨894000, by decide⟩ :=
  accepted_of_selected 11 70018 ⟨894000, by decide⟩ ⟨11, 2, 0, 894000, 70018, 3741, 262144⟩
    (by decide) selected_cut_34468

theorem selected_cut_34469 : selected 10 ⟨894067, by decide⟩
    (prefixPartial 11 70019) = some ⟨11, 2, 0, 894067, 70019, 2237, 262144⟩ := by
  decide +kernel

theorem context_11_70019_894067 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70019 ⟨894067, by decide⟩ :=
  accepted_of_selected 11 70019 ⟨894067, by decide⟩ ⟨11, 2, 0, 894067, 70019, 2237, 262144⟩
    (by decide) selected_cut_34469

theorem unmarked_context_10_17504_894068 : frontier 11 ⟨894068, by decide⟩
    (prefixCache 10 17504) (prefixPartial 10 17504) = false := by
  decide +kernel

theorem node_context_10_17504_894068 : EJMOriginalGlobalDAGData.nodes 11 ⟨894068, by decide⟩ =
    .split (coordinate 10) (![⟨893693, by decide⟩,⟨893902, by decide⟩,⟨894000, by decide⟩,⟨894067, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17504_894068 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17504 ⟨894068, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17504
    ⟨894068, by decide⟩ (by decide) (![⟨893693, by decide⟩,⟨893902, by decide⟩,⟨894000, by decide⟩,⟨894067, by decide⟩]) unmarked_context_10_17504_894068 node_context_10_17504_894068
  intro a
  fin_cases a
  · exact context_11_70016_893693
  · exact context_11_70017_893902
  · exact context_11_70018_894000
  · exact context_11_70019_894067

theorem selected_cut_34470 : selected 9 ⟨894178, by decide⟩
    (prefixPartial 12 280080) = some ⟨12, 2, 0, 894178, 280080, 3821, 65536⟩ := by
  decide +kernel

theorem context_12_280080_894178 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 280080 ⟨894178, by decide⟩ :=
  accepted_of_selected 12 280080 ⟨894178, by decide⟩ ⟨12, 2, 0, 894178, 280080, 3821, 65536⟩
    (by decide) selected_cut_34470

theorem selected_cut_34471 : selected 9 ⟨894257, by decide⟩
    (prefixPartial 12 280081) = some ⟨12, 2, 0, 894257, 280081, 3585, 65536⟩ := by
  decide +kernel

theorem context_12_280081_894257 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 280081 ⟨894257, by decide⟩ :=
  accepted_of_selected 12 280081 ⟨894257, by decide⟩ ⟨12, 2, 0, 894257, 280081, 3585, 65536⟩
    (by decide) selected_cut_34471

theorem selected_cut_34472 : selected 9 ⟨894339, by decide⟩
    (prefixPartial 12 280082) = some ⟨12, 2, 0, 894339, 280082, 3641, 65536⟩ := by
  decide +kernel

theorem context_12_280082_894339 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 280082 ⟨894339, by decide⟩ :=
  accepted_of_selected 12 280082 ⟨894339, by decide⟩ ⟨12, 2, 0, 894339, 280082, 3641, 65536⟩
    (by decide) selected_cut_34472

theorem selected_cut_34473 : selected 9 ⟨894426, by decide⟩
    (prefixPartial 12 280083) = some ⟨12, 2, 0, 894426, 280083, 4077, 65536⟩ := by
  decide +kernel

theorem context_12_280083_894426 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 280083 ⟨894426, by decide⟩ :=
  accepted_of_selected 12 280083 ⟨894426, by decide⟩ ⟨12, 2, 0, 894426, 280083, 4077, 65536⟩
    (by decide) selected_cut_34473

theorem unmarked_context_11_70020_894427 : frontier 10 ⟨894427, by decide⟩
    (prefixCache 11 70020) (prefixPartial 11 70020) = false := by
  decide +kernel

theorem node_context_11_70020_894427 : EJMOriginalGlobalDAGData.nodes 10 ⟨894427, by decide⟩ =
    .split (coordinate 11) (![⟨894178, by decide⟩,⟨894257, by decide⟩,⟨894339, by decide⟩,⟨894426, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70020_894427 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70020 ⟨894427, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70020
    ⟨894427, by decide⟩ (by decide) (![⟨894178, by decide⟩,⟨894257, by decide⟩,⟨894339, by decide⟩,⟨894426, by decide⟩]) unmarked_context_11_70020_894427 node_context_11_70020_894427
  intro a
  fin_cases a
  · exact context_12_280080_894178
  · exact context_12_280081_894257
  · exact context_12_280082_894339
  · exact context_12_280083_894426

theorem selected_cut_34474 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 70021) = some ⟨11, 1, 0, 892405, 70021, 1, 262144⟩ := by
  decide +kernel

theorem context_11_70021_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70021 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 70021 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 70021, 1, 262144⟩
    (by decide) selected_cut_34474

theorem selected_cut_34475 : selected 9 ⟨894505, by decide⟩
    (prefixPartial 12 280088) = some ⟨12, 2, 0, 894505, 280088, 3357, 65536⟩ := by
  decide +kernel

theorem context_12_280088_894505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 280088 ⟨894505, by decide⟩ :=
  accepted_of_selected 12 280088 ⟨894505, by decide⟩ ⟨12, 2, 0, 894505, 280088, 3357, 65536⟩
    (by decide) selected_cut_34475

theorem selected_cut_34476 : selected 9 ⟨894566, by decide⟩
    (prefixPartial 12 280089) = some ⟨12, 2, 0, 894566, 280089, 3005, 65536⟩ := by
  decide +kernel

theorem context_12_280089_894566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 280089 ⟨894566, by decide⟩ :=
  accepted_of_selected 12 280089 ⟨894566, by decide⟩ ⟨12, 2, 0, 894566, 280089, 3005, 65536⟩
    (by decide) selected_cut_34476

theorem selected_cut_34477 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 280090) = some ⟨12, 1, 0, 893903, 280090, 1, 65536⟩ := by
  decide +kernel

theorem context_12_280090_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 280090 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 280090 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 280090, 1, 65536⟩
    (by decide) selected_cut_34477

theorem selected_cut_34478 : selected 9 ⟨894649, by decide⟩
    (prefixPartial 12 280091) = some ⟨12, 2, 0, 894649, 280091, 3909, 65536⟩ := by
  decide +kernel

theorem context_12_280091_894649 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 280091 ⟨894649, by decide⟩ :=
  accepted_of_selected 12 280091 ⟨894649, by decide⟩ ⟨12, 2, 0, 894649, 280091, 3909, 65536⟩
    (by decide) selected_cut_34478

theorem unmarked_context_11_70022_894650 : frontier 10 ⟨894650, by decide⟩
    (prefixCache 11 70022) (prefixPartial 11 70022) = false := by
  decide +kernel

theorem node_context_11_70022_894650 : EJMOriginalGlobalDAGData.nodes 10 ⟨894650, by decide⟩ =
    .split (coordinate 11) (![⟨894505, by decide⟩,⟨894566, by decide⟩,⟨893903, by decide⟩,⟨894649, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70022_894650 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70022 ⟨894650, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70022
    ⟨894650, by decide⟩ (by decide) (![⟨894505, by decide⟩,⟨894566, by decide⟩,⟨893903, by decide⟩,⟨894649, by decide⟩]) unmarked_context_11_70022_894650 node_context_11_70022_894650
  intro a
  fin_cases a
  · exact context_12_280088_894505
  · exact context_12_280089_894566
  · exact context_12_280090_893903
  · exact context_12_280091_894649

theorem selected_cut_34479 : selected 9 ⟨894732, by decide⟩
    (prefixPartial 12 280092) = some ⟨12, 2, 0, 894732, 280092, 3621, 65536⟩ := by
  decide +kernel

theorem context_12_280092_894732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 280092 ⟨894732, by decide⟩ :=
  accepted_of_selected 12 280092 ⟨894732, by decide⟩ ⟨12, 2, 0, 894732, 280092, 3621, 65536⟩
    (by decide) selected_cut_34479

theorem selected_cut_34480 : selected 9 ⟨894791, by decide⟩
    (prefixPartial 12 280093) = some ⟨12, 2, 0, 894791, 280093, 3197, 65536⟩ := by
  decide +kernel

theorem context_12_280093_894791 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 280093 ⟨894791, by decide⟩ :=
  accepted_of_selected 12 280093 ⟨894791, by decide⟩ ⟨12, 2, 0, 894791, 280093, 3197, 65536⟩
    (by decide) selected_cut_34480

theorem selected_cut_34481 : selected 9 ⟨894870, by decide⟩
    (prefixPartial 12 280094) = some ⟨12, 2, 0, 894870, 280094, 3617, 65536⟩ := by
  decide +kernel

theorem context_12_280094_894870 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 280094 ⟨894870, by decide⟩ :=
  accepted_of_selected 12 280094 ⟨894870, by decide⟩ ⟨12, 2, 0, 894870, 280094, 3617, 65536⟩
    (by decide) selected_cut_34481

theorem selected_cut_34482 : selected 9 ⟨894949, by decide⟩
    (prefixPartial 12 280095) = some ⟨12, 2, 0, 894949, 280095, 3741, 65536⟩ := by
  decide +kernel

theorem context_12_280095_894949 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 280095 ⟨894949, by decide⟩ :=
  accepted_of_selected 12 280095 ⟨894949, by decide⟩ ⟨12, 2, 0, 894949, 280095, 3741, 65536⟩
    (by decide) selected_cut_34482

theorem unmarked_context_11_70023_894950 : frontier 10 ⟨894950, by decide⟩
    (prefixCache 11 70023) (prefixPartial 11 70023) = false := by
  decide +kernel

theorem node_context_11_70023_894950 : EJMOriginalGlobalDAGData.nodes 10 ⟨894950, by decide⟩ =
    .split (coordinate 11) (![⟨894732, by decide⟩,⟨894791, by decide⟩,⟨894870, by decide⟩,⟨894949, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70023_894950 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70023 ⟨894950, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70023
    ⟨894950, by decide⟩ (by decide) (![⟨894732, by decide⟩,⟨894791, by decide⟩,⟨894870, by decide⟩,⟨894949, by decide⟩]) unmarked_context_11_70023_894950 node_context_11_70023_894950
  intro a
  fin_cases a
  · exact context_12_280092_894732
  · exact context_12_280093_894791
  · exact context_12_280094_894870
  · exact context_12_280095_894949

theorem unmarked_context_10_17505_894951 : frontier 11 ⟨894951, by decide⟩
    (prefixCache 10 17505) (prefixPartial 10 17505) = false := by
  decide +kernel

theorem node_context_10_17505_894951 : EJMOriginalGlobalDAGData.nodes 11 ⟨894951, by decide⟩ =
    .split (coordinate 10) (![⟨894427, by decide⟩,⟨892405, by decide⟩,⟨894650, by decide⟩,⟨894950, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17505_894951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17505 ⟨894951, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17505
    ⟨894951, by decide⟩ (by decide) (![⟨894427, by decide⟩,⟨892405, by decide⟩,⟨894650, by decide⟩,⟨894950, by decide⟩]) unmarked_context_10_17505_894951 node_context_10_17505_894951
  intro a
  fin_cases a
  · exact context_11_70020_894427
  · exact context_11_70021_892405
  · exact context_11_70022_894650
  · exact context_11_70023_894950

theorem selected_cut_34483 : selected 9 ⟨895040, by decide⟩
    (prefixPartial 12 280096) = some ⟨12, 2, 0, 895040, 280096, 3193, 65536⟩ := by
  decide +kernel

theorem context_12_280096_895040 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 280096 ⟨895040, by decide⟩ :=
  accepted_of_selected 12 280096 ⟨895040, by decide⟩ ⟨12, 2, 0, 895040, 280096, 3193, 65536⟩
    (by decide) selected_cut_34483

theorem selected_cut_34484 : selected 9 ⟨895114, by decide⟩
    (prefixPartial 12 280097) = some ⟨12, 2, 0, 895114, 280097, 3293, 65536⟩ := by
  decide +kernel

theorem context_12_280097_895114 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 280097 ⟨895114, by decide⟩ :=
  accepted_of_selected 12 280097 ⟨895114, by decide⟩ ⟨12, 2, 0, 895114, 280097, 3293, 65536⟩
    (by decide) selected_cut_34484

theorem selected_cut_34485 : selected 9 ⟨895191, by decide⟩
    (prefixPartial 12 280098) = some ⟨12, 2, 0, 895191, 280098, 3409, 65536⟩ := by
  decide +kernel

theorem context_12_280098_895191 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 280098 ⟨895191, by decide⟩ :=
  accepted_of_selected 12 280098 ⟨895191, by decide⟩ ⟨12, 2, 0, 895191, 280098, 3409, 65536⟩
    (by decide) selected_cut_34485

theorem selected_cut_34486 : selected 9 ⟨895269, by decide⟩
    (prefixPartial 12 280099) = some ⟨12, 2, 0, 895269, 280099, 3461, 65536⟩ := by
  decide +kernel

theorem context_12_280099_895269 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 280099 ⟨895269, by decide⟩ :=
  accepted_of_selected 12 280099 ⟨895269, by decide⟩ ⟨12, 2, 0, 895269, 280099, 3461, 65536⟩
    (by decide) selected_cut_34486

theorem unmarked_context_11_70024_895270 : frontier 10 ⟨895270, by decide⟩
    (prefixCache 11 70024) (prefixPartial 11 70024) = false := by
  decide +kernel

theorem node_context_11_70024_895270 : EJMOriginalGlobalDAGData.nodes 10 ⟨895270, by decide⟩ =
    .split (coordinate 11) (![⟨895040, by decide⟩,⟨895114, by decide⟩,⟨895191, by decide⟩,⟨895269, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70024_895270 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70024 ⟨895270, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70024
    ⟨895270, by decide⟩ (by decide) (![⟨895040, by decide⟩,⟨895114, by decide⟩,⟨895191, by decide⟩,⟨895269, by decide⟩]) unmarked_context_11_70024_895270 node_context_11_70024_895270
  intro a
  fin_cases a
  · exact context_12_280096_895040
  · exact context_12_280097_895114
  · exact context_12_280098_895191
  · exact context_12_280099_895269

theorem selected_cut_34487 : selected 9 ⟨895334, by decide⟩
    (prefixPartial 12 280100) = some ⟨12, 2, 0, 895334, 280100, 2893, 65536⟩ := by
  decide +kernel

theorem context_12_280100_895334 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 280100 ⟨895334, by decide⟩ :=
  accepted_of_selected 12 280100 ⟨895334, by decide⟩ ⟨12, 2, 0, 895334, 280100, 2893, 65536⟩
    (by decide) selected_cut_34487

theorem selected_cut_34488 : selected 9 ⟨895383, by decide⟩
    (prefixPartial 12 280101) = some ⟨12, 2, 0, 895383, 280101, 2473, 65536⟩ := by
  decide +kernel

theorem context_12_280101_895383 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 280101 ⟨895383, by decide⟩ :=
  accepted_of_selected 12 280101 ⟨895383, by decide⟩ ⟨12, 2, 0, 895383, 280101, 2473, 65536⟩
    (by decide) selected_cut_34488

theorem selected_cut_34489 : selected 9 ⟨895448, by decide⟩
    (prefixPartial 12 280102) = some ⟨12, 2, 0, 895448, 280102, 2901, 65536⟩ := by
  decide +kernel

theorem context_12_280102_895448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 280102 ⟨895448, by decide⟩ :=
  accepted_of_selected 12 280102 ⟨895448, by decide⟩ ⟨12, 2, 0, 895448, 280102, 2901, 65536⟩
    (by decide) selected_cut_34489

theorem selected_cut_34490 : selected 9 ⟨895500, by decide⟩
    (prefixPartial 12 280103) = some ⟨12, 2, 0, 895500, 280103, 2913, 65536⟩ := by
  decide +kernel

theorem context_12_280103_895500 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 280103 ⟨895500, by decide⟩ :=
  accepted_of_selected 12 280103 ⟨895500, by decide⟩ ⟨12, 2, 0, 895500, 280103, 2913, 65536⟩
    (by decide) selected_cut_34490

theorem unmarked_context_11_70025_895501 : frontier 10 ⟨895501, by decide⟩
    (prefixCache 11 70025) (prefixPartial 11 70025) = false := by
  decide +kernel

theorem node_context_11_70025_895501 : EJMOriginalGlobalDAGData.nodes 10 ⟨895501, by decide⟩ =
    .split (coordinate 11) (![⟨895334, by decide⟩,⟨895383, by decide⟩,⟨895448, by decide⟩,⟨895500, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70025_895501 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70025 ⟨895501, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70025
    ⟨895501, by decide⟩ (by decide) (![⟨895334, by decide⟩,⟨895383, by decide⟩,⟨895448, by decide⟩,⟨895500, by decide⟩]) unmarked_context_11_70025_895501 node_context_11_70025_895501
  intro a
  fin_cases a
  · exact context_12_280100_895334
  · exact context_12_280101_895383
  · exact context_12_280102_895448
  · exact context_12_280103_895500

theorem selected_cut_34491 : selected 9 ⟨895558, by decide⟩
    (prefixPartial 12 280104) = some ⟨12, 2, 0, 895558, 280104, 2693, 65536⟩ := by
  decide +kernel

theorem context_12_280104_895558 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 280104 ⟨895558, by decide⟩ :=
  accepted_of_selected 12 280104 ⟨895558, by decide⟩ ⟨12, 2, 0, 895558, 280104, 2693, 65536⟩
    (by decide) selected_cut_34491

theorem selected_cut_34492 : selected 9 ⟨895606, by decide⟩
    (prefixPartial 12 280105) = some ⟨12, 2, 0, 895606, 280105, 2453, 65536⟩ := by
  decide +kernel

theorem context_12_280105_895606 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 280105 ⟨895606, by decide⟩ :=
  accepted_of_selected 12 280105 ⟨895606, by decide⟩ ⟨12, 2, 0, 895606, 280105, 2453, 65536⟩
    (by decide) selected_cut_34492

theorem selected_cut_34493 : selected 9 ⟨661671, by decide⟩
    (prefixPartial 12 280106) = some ⟨12, 1, 0, 661671, 280106, 1, 65536⟩ := by
  decide +kernel

theorem context_12_280106_661671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 280106 ⟨661671, by decide⟩ :=
  accepted_of_selected 12 280106 ⟨661671, by decide⟩ ⟨12, 1, 0, 661671, 280106, 1, 65536⟩
    (by decide) selected_cut_34493

theorem selected_cut_34494 : selected 9 ⟨895666, by decide⟩
    (prefixPartial 12 280107) = some ⟨12, 2, 0, 895666, 280107, 2997, 65536⟩ := by
  decide +kernel

theorem context_12_280107_895666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 280107 ⟨895666, by decide⟩ :=
  accepted_of_selected 12 280107 ⟨895666, by decide⟩ ⟨12, 2, 0, 895666, 280107, 2997, 65536⟩
    (by decide) selected_cut_34494

theorem unmarked_context_11_70026_895667 : frontier 10 ⟨895667, by decide⟩
    (prefixCache 11 70026) (prefixPartial 11 70026) = false := by
  decide +kernel

theorem node_context_11_70026_895667 : EJMOriginalGlobalDAGData.nodes 10 ⟨895667, by decide⟩ =
    .split (coordinate 11) (![⟨895558, by decide⟩,⟨895606, by decide⟩,⟨661671, by decide⟩,⟨895666, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70026_895667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70026 ⟨895667, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70026
    ⟨895667, by decide⟩ (by decide) (![⟨895558, by decide⟩,⟨895606, by decide⟩,⟨661671, by decide⟩,⟨895666, by decide⟩]) unmarked_context_11_70026_895667 node_context_11_70026_895667
  intro a
  fin_cases a
  · exact context_12_280104_895558
  · exact context_12_280105_895606
  · exact context_12_280106_661671
  · exact context_12_280107_895666

theorem selected_cut_34495 : selected 9 ⟨895730, by decide⟩
    (prefixPartial 12 280108) = some ⟨12, 2, 0, 895730, 280108, 2813, 65536⟩ := by
  decide +kernel

theorem context_12_280108_895730 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 280108 ⟨895730, by decide⟩ :=
  accepted_of_selected 12 280108 ⟨895730, by decide⟩ ⟨12, 2, 0, 895730, 280108, 2813, 65536⟩
    (by decide) selected_cut_34495

theorem selected_cut_34496 : selected 9 ⟨895776, by decide⟩
    (prefixPartial 12 280109) = some ⟨12, 2, 0, 895776, 280109, 2469, 65536⟩ := by
  decide +kernel

theorem context_12_280109_895776 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 280109 ⟨895776, by decide⟩ :=
  accepted_of_selected 12 280109 ⟨895776, by decide⟩ ⟨12, 2, 0, 895776, 280109, 2469, 65536⟩
    (by decide) selected_cut_34496

theorem selected_cut_34497 : selected 9 ⟨895832, by decide⟩
    (prefixPartial 12 280110) = some ⟨12, 2, 0, 895832, 280110, 2797, 65536⟩ := by
  decide +kernel

theorem context_12_280110_895832 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 280110 ⟨895832, by decide⟩ :=
  accepted_of_selected 12 280110 ⟨895832, by decide⟩ ⟨12, 2, 0, 895832, 280110, 2797, 65536⟩
    (by decide) selected_cut_34497

theorem selected_cut_34498 : selected 9 ⟨895881, by decide⟩
    (prefixPartial 12 280111) = some ⟨12, 2, 0, 895881, 280111, 2717, 65536⟩ := by
  decide +kernel

theorem context_12_280111_895881 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 280111 ⟨895881, by decide⟩ :=
  accepted_of_selected 12 280111 ⟨895881, by decide⟩ ⟨12, 2, 0, 895881, 280111, 2717, 65536⟩
    (by decide) selected_cut_34498

theorem unmarked_context_11_70027_895882 : frontier 10 ⟨895882, by decide⟩
    (prefixCache 11 70027) (prefixPartial 11 70027) = false := by
  decide +kernel

theorem node_context_11_70027_895882 : EJMOriginalGlobalDAGData.nodes 10 ⟨895882, by decide⟩ =
    .split (coordinate 11) (![⟨895730, by decide⟩,⟨895776, by decide⟩,⟨895832, by decide⟩,⟨895881, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70027_895882 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70027 ⟨895882, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70027
    ⟨895882, by decide⟩ (by decide) (![⟨895730, by decide⟩,⟨895776, by decide⟩,⟨895832, by decide⟩,⟨895881, by decide⟩]) unmarked_context_11_70027_895882 node_context_11_70027_895882
  intro a
  fin_cases a
  · exact context_12_280108_895730
  · exact context_12_280109_895776
  · exact context_12_280110_895832
  · exact context_12_280111_895881

theorem unmarked_context_10_17506_895883 : frontier 11 ⟨895883, by decide⟩
    (prefixCache 10 17506) (prefixPartial 10 17506) = false := by
  decide +kernel

theorem node_context_10_17506_895883 : EJMOriginalGlobalDAGData.nodes 11 ⟨895883, by decide⟩ =
    .split (coordinate 10) (![⟨895270, by decide⟩,⟨895501, by decide⟩,⟨895667, by decide⟩,⟨895882, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17506_895883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17506 ⟨895883, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17506
    ⟨895883, by decide⟩ (by decide) (![⟨895270, by decide⟩,⟨895501, by decide⟩,⟨895667, by decide⟩,⟨895882, by decide⟩]) unmarked_context_10_17506_895883 node_context_10_17506_895883
  intro a
  fin_cases a
  · exact context_11_70024_895270
  · exact context_11_70025_895501
  · exact context_11_70026_895667
  · exact context_11_70027_895882

theorem selected_cut_34499 : selected 9 ⟨895958, by decide⟩
    (prefixPartial 12 280112) = some ⟨12, 2, 0, 895958, 280112, 2573, 65536⟩ := by
  decide +kernel

theorem context_12_280112_895958 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 280112 ⟨895958, by decide⟩ :=
  accepted_of_selected 12 280112 ⟨895958, by decide⟩ ⟨12, 2, 0, 895958, 280112, 2573, 65536⟩
    (by decide) selected_cut_34499

theorem selected_cut_34500 : selected 9 ⟨896010, by decide⟩
    (prefixPartial 12 280113) = some ⟨12, 2, 0, 896010, 280113, 2477, 65536⟩ := by
  decide +kernel

theorem context_12_280113_896010 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 280113 ⟨896010, by decide⟩ :=
  accepted_of_selected 12 280113 ⟨896010, by decide⟩ ⟨12, 2, 0, 896010, 280113, 2477, 65536⟩
    (by decide) selected_cut_34500

theorem selected_cut_34501 : selected 9 ⟨896084, by decide⟩
    (prefixPartial 12 280114) = some ⟨12, 2, 0, 896084, 280114, 2537, 65536⟩ := by
  decide +kernel

theorem context_12_280114_896084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 280114 ⟨896084, by decide⟩ :=
  accepted_of_selected 12 280114 ⟨896084, by decide⟩ ⟨12, 2, 0, 896084, 280114, 2537, 65536⟩
    (by decide) selected_cut_34501

theorem selected_cut_34502 : selected 9 ⟨896151, by decide⟩
    (prefixPartial 12 280115) = some ⟨12, 2, 0, 896151, 280115, 2849, 65536⟩ := by
  decide +kernel

theorem context_12_280115_896151 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 280115 ⟨896151, by decide⟩ :=
  accepted_of_selected 12 280115 ⟨896151, by decide⟩ ⟨12, 2, 0, 896151, 280115, 2849, 65536⟩
    (by decide) selected_cut_34502

theorem unmarked_context_11_70028_896152 : frontier 10 ⟨896152, by decide⟩
    (prefixCache 11 70028) (prefixPartial 11 70028) = false := by
  decide +kernel

theorem node_context_11_70028_896152 : EJMOriginalGlobalDAGData.nodes 10 ⟨896152, by decide⟩ =
    .split (coordinate 11) (![⟨895958, by decide⟩,⟨896010, by decide⟩,⟨896084, by decide⟩,⟨896151, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70028_896152 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70028 ⟨896152, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70028
    ⟨896152, by decide⟩ (by decide) (![⟨895958, by decide⟩,⟨896010, by decide⟩,⟨896084, by decide⟩,⟨896151, by decide⟩]) unmarked_context_11_70028_896152 node_context_11_70028_896152
  intro a
  fin_cases a
  · exact context_12_280112_895958
  · exact context_12_280113_896010
  · exact context_12_280114_896084
  · exact context_12_280115_896151

theorem selected_cut_34503 : selected 9 ⟨896199, by decide⟩
    (prefixPartial 12 280116) = some ⟨12, 2, 0, 896199, 280116, 2241, 65536⟩ := by
  decide +kernel

theorem context_12_280116_896199 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 280116 ⟨896199, by decide⟩ :=
  accepted_of_selected 12 280116 ⟨896199, by decide⟩ ⟨12, 2, 0, 896199, 280116, 2241, 65536⟩
    (by decide) selected_cut_34503

theorem selected_cut_34504 : selected 9 ⟨896237, by decide⟩
    (prefixPartial 12 280117) = some ⟨12, 2, 0, 896237, 280117, 1929, 65536⟩ := by
  decide +kernel

theorem context_12_280117_896237 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 280117 ⟨896237, by decide⟩ :=
  accepted_of_selected 12 280117 ⟨896237, by decide⟩ ⟨12, 2, 0, 896237, 280117, 1929, 65536⟩
    (by decide) selected_cut_34504

theorem selected_cut_34505 : selected 9 ⟨896288, by decide⟩
    (prefixPartial 12 280118) = some ⟨12, 2, 0, 896288, 280118, 2105, 65536⟩ := by
  decide +kernel

theorem context_12_280118_896288 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 280118 ⟨896288, by decide⟩ :=
  accepted_of_selected 12 280118 ⟨896288, by decide⟩ ⟨12, 2, 0, 896288, 280118, 2105, 65536⟩
    (by decide) selected_cut_34505

theorem selected_cut_34506 : selected 9 ⟨896341, by decide⟩
    (prefixPartial 12 280119) = some ⟨12, 2, 0, 896341, 280119, 2309, 65536⟩ := by
  decide +kernel

theorem context_12_280119_896341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 280119 ⟨896341, by decide⟩ :=
  accepted_of_selected 12 280119 ⟨896341, by decide⟩ ⟨12, 2, 0, 896341, 280119, 2309, 65536⟩
    (by decide) selected_cut_34506

theorem unmarked_context_11_70029_896342 : frontier 10 ⟨896342, by decide⟩
    (prefixCache 11 70029) (prefixPartial 11 70029) = false := by
  decide +kernel

theorem node_context_11_70029_896342 : EJMOriginalGlobalDAGData.nodes 10 ⟨896342, by decide⟩ =
    .split (coordinate 11) (![⟨896199, by decide⟩,⟨896237, by decide⟩,⟨896288, by decide⟩,⟨896341, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70029_896342 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70029 ⟨896342, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70029
    ⟨896342, by decide⟩ (by decide) (![⟨896199, by decide⟩,⟨896237, by decide⟩,⟨896288, by decide⟩,⟨896341, by decide⟩]) unmarked_context_11_70029_896342 node_context_11_70029_896342
  intro a
  fin_cases a
  · exact context_12_280116_896199
  · exact context_12_280117_896237
  · exact context_12_280118_896288
  · exact context_12_280119_896341

theorem selected_cut_34507 : selected 9 ⟨896391, by decide⟩
    (prefixPartial 12 280120) = some ⟨12, 2, 0, 896391, 280120, 2109, 65536⟩ := by
  decide +kernel

theorem context_12_280120_896391 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 280120 ⟨896391, by decide⟩ :=
  accepted_of_selected 12 280120 ⟨896391, by decide⟩ ⟨12, 2, 0, 896391, 280120, 2109, 65536⟩
    (by decide) selected_cut_34507

theorem selected_cut_34508 : selected 9 ⟨896427, by decide⟩
    (prefixPartial 12 280121) = some ⟨12, 2, 0, 896427, 280121, 1833, 65536⟩ := by
  decide +kernel

theorem context_12_280121_896427 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 280121 ⟨896427, by decide⟩ :=
  accepted_of_selected 12 280121 ⟨896427, by decide⟩ ⟨12, 2, 0, 896427, 280121, 1833, 65536⟩
    (by decide) selected_cut_34508

theorem selected_cut_34509 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 280122) = some ⟨12, 1, 0, 893903, 280122, 1, 65536⟩ := by
  decide +kernel

theorem context_12_280122_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 280122 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 280122 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 280122, 1, 65536⟩
    (by decide) selected_cut_34509

theorem selected_cut_34510 : selected 9 ⟨896479, by decide⟩
    (prefixPartial 12 280123) = some ⟨12, 2, 0, 896479, 280123, 2401, 65536⟩ := by
  decide +kernel

theorem context_12_280123_896479 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 280123 ⟨896479, by decide⟩ :=
  accepted_of_selected 12 280123 ⟨896479, by decide⟩ ⟨12, 2, 0, 896479, 280123, 2401, 65536⟩
    (by decide) selected_cut_34510

theorem unmarked_context_11_70030_896480 : frontier 10 ⟨896480, by decide⟩
    (prefixCache 11 70030) (prefixPartial 11 70030) = false := by
  decide +kernel

theorem node_context_11_70030_896480 : EJMOriginalGlobalDAGData.nodes 10 ⟨896480, by decide⟩ =
    .split (coordinate 11) (![⟨896391, by decide⟩,⟨896427, by decide⟩,⟨893903, by decide⟩,⟨896479, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70030_896480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70030 ⟨896480, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70030
    ⟨896480, by decide⟩ (by decide) (![⟨896391, by decide⟩,⟨896427, by decide⟩,⟨893903, by decide⟩,⟨896479, by decide⟩]) unmarked_context_11_70030_896480 node_context_11_70030_896480
  intro a
  fin_cases a
  · exact context_12_280120_896391
  · exact context_12_280121_896427
  · exact context_12_280122_893903
  · exact context_12_280123_896479

theorem selected_cut_34511 : selected 9 ⟨896527, by decide⟩
    (prefixPartial 12 280124) = some ⟨12, 2, 0, 896527, 280124, 2153, 65536⟩ := by
  decide +kernel

theorem context_12_280124_896527 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 280124 ⟨896527, by decide⟩ :=
  accepted_of_selected 12 280124 ⟨896527, by decide⟩ ⟨12, 2, 0, 896527, 280124, 2153, 65536⟩
    (by decide) selected_cut_34511

theorem selected_cut_34512 : selected 9 ⟨896561, by decide⟩
    (prefixPartial 12 280125) = some ⟨12, 2, 0, 896561, 280125, 1757, 65536⟩ := by
  decide +kernel

theorem context_12_280125_896561 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 280125 ⟨896561, by decide⟩ :=
  accepted_of_selected 12 280125 ⟨896561, by decide⟩ ⟨12, 2, 0, 896561, 280125, 1757, 65536⟩
    (by decide) selected_cut_34512

theorem selected_cut_34513 : selected 9 ⟨896602, by decide⟩
    (prefixPartial 12 280126) = some ⟨12, 2, 0, 896602, 280126, 2069, 65536⟩ := by
  decide +kernel

theorem context_12_280126_896602 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 280126 ⟨896602, by decide⟩ :=
  accepted_of_selected 12 280126 ⟨896602, by decide⟩ ⟨12, 2, 0, 896602, 280126, 2069, 65536⟩
    (by decide) selected_cut_34513

theorem selected_cut_34514 : selected 9 ⟨896639, by decide⟩
    (prefixPartial 12 280127) = some ⟨12, 2, 0, 896639, 280127, 2137, 65536⟩ := by
  decide +kernel

theorem context_12_280127_896639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 280127 ⟨896639, by decide⟩ :=
  accepted_of_selected 12 280127 ⟨896639, by decide⟩ ⟨12, 2, 0, 896639, 280127, 2137, 65536⟩
    (by decide) selected_cut_34514

theorem unmarked_context_11_70031_896640 : frontier 10 ⟨896640, by decide⟩
    (prefixCache 11 70031) (prefixPartial 11 70031) = false := by
  decide +kernel

theorem node_context_11_70031_896640 : EJMOriginalGlobalDAGData.nodes 10 ⟨896640, by decide⟩ =
    .split (coordinate 11) (![⟨896527, by decide⟩,⟨896561, by decide⟩,⟨896602, by decide⟩,⟨896639, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70031_896640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70031 ⟨896640, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70031
    ⟨896640, by decide⟩ (by decide) (![⟨896527, by decide⟩,⟨896561, by decide⟩,⟨896602, by decide⟩,⟨896639, by decide⟩]) unmarked_context_11_70031_896640 node_context_11_70031_896640
  intro a
  fin_cases a
  · exact context_12_280124_896527
  · exact context_12_280125_896561
  · exact context_12_280126_896602
  · exact context_12_280127_896639

theorem unmarked_context_10_17507_896641 : frontier 11 ⟨896641, by decide⟩
    (prefixCache 10 17507) (prefixPartial 10 17507) = false := by
  decide +kernel

theorem node_context_10_17507_896641 : EJMOriginalGlobalDAGData.nodes 11 ⟨896641, by decide⟩ =
    .split (coordinate 10) (![⟨896152, by decide⟩,⟨896342, by decide⟩,⟨896480, by decide⟩,⟨896640, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17507_896641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17507 ⟨896641, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17507
    ⟨896641, by decide⟩ (by decide) (![⟨896152, by decide⟩,⟨896342, by decide⟩,⟨896480, by decide⟩,⟨896640, by decide⟩]) unmarked_context_10_17507_896641 node_context_10_17507_896641
  intro a
  fin_cases a
  · exact context_11_70028_896152
  · exact context_11_70029_896342
  · exact context_11_70030_896480
  · exact context_11_70031_896640

theorem unmarked_context_9_4376_896642 : frontier 12 ⟨896642, by decide⟩
    (prefixCache 9 4376) (prefixPartial 9 4376) = false := by
  decide +kernel

theorem node_context_9_4376_896642 : EJMOriginalGlobalDAGData.nodes 12 ⟨896642, by decide⟩ =
    .split (coordinate 9) (![⟨894068, by decide⟩,⟨894951, by decide⟩,⟨895883, by decide⟩,⟨896641, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4376_896642 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4376 ⟨896642, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4376
    ⟨896642, by decide⟩ (by decide) (![⟨894068, by decide⟩,⟨894951, by decide⟩,⟨895883, by decide⟩,⟨896641, by decide⟩]) unmarked_context_9_4376_896642 node_context_9_4376_896642
  intro a
  fin_cases a
  · exact context_10_17504_894068
  · exact context_10_17505_894951
  · exact context_10_17506_895883
  · exact context_10_17507_896641

theorem selected_cut_34515 : selected 11 ⟨3442, by decide⟩
    (prefixPartial 10 17508) = some ⟨10, 1, 0, 3442, 17508, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_17508_3442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17508 ⟨3442, by decide⟩ :=
  accepted_of_selected 10 17508 ⟨3442, by decide⟩ ⟨10, 1, 0, 3442, 17508, 1, 1048576⟩
    (by decide) selected_cut_34515

theorem selected_cut_34516 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 17509) = some ⟨10, 1, 0, 893098, 17509, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_17509_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17509 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 17509 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 17509, 1, 1048576⟩
    (by decide) selected_cut_34516

theorem selected_cut_34517 : selected 9 ⟨896705, by decide⟩
    (prefixPartial 12 280160) = some ⟨12, 2, 0, 896705, 280160, 1789, 65536⟩ := by
  decide +kernel

theorem context_12_280160_896705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 280160 ⟨896705, by decide⟩ :=
  accepted_of_selected 12 280160 ⟨896705, by decide⟩ ⟨12, 2, 0, 896705, 280160, 1789, 65536⟩
    (by decide) selected_cut_34517

theorem selected_cut_34518 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 280161) = some ⟨12, 1, 0, 896706, 280161, 1, 65536⟩ := by
  decide +kernel

theorem context_12_280161_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 280161 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 280161 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 280161, 1, 65536⟩
    (by decide) selected_cut_34518

theorem selected_cut_34519 : selected 9 ⟨896761, by decide⟩
    (prefixPartial 12 280162) = some ⟨12, 2, 0, 896761, 280162, 1809, 65536⟩ := by
  decide +kernel

theorem context_12_280162_896761 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 280162 ⟨896761, by decide⟩ :=
  accepted_of_selected 12 280162 ⟨896761, by decide⟩ ⟨12, 2, 0, 896761, 280162, 1809, 65536⟩
    (by decide) selected_cut_34519

theorem selected_cut_34520 : selected 9 ⟨896811, by decide⟩
    (prefixPartial 12 280163) = some ⟨12, 2, 0, 896811, 280163, 2037, 65536⟩ := by
  decide +kernel

theorem context_12_280163_896811 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 280163 ⟨896811, by decide⟩ :=
  accepted_of_selected 12 280163 ⟨896811, by decide⟩ ⟨12, 2, 0, 896811, 280163, 2037, 65536⟩
    (by decide) selected_cut_34520

theorem unmarked_context_11_70040_896812 : frontier 10 ⟨896812, by decide⟩
    (prefixCache 11 70040) (prefixPartial 11 70040) = false := by
  decide +kernel

theorem node_context_11_70040_896812 : EJMOriginalGlobalDAGData.nodes 10 ⟨896812, by decide⟩ =
    .split (coordinate 11) (![⟨896705, by decide⟩,⟨896706, by decide⟩,⟨896761, by decide⟩,⟨896811, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70040_896812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70040 ⟨896812, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70040
    ⟨896812, by decide⟩ (by decide) (![⟨896705, by decide⟩,⟨896706, by decide⟩,⟨896761, by decide⟩,⟨896811, by decide⟩]) unmarked_context_11_70040_896812 node_context_11_70040_896812
  intro a
  fin_cases a
  · exact context_12_280160_896705
  · exact context_12_280161_896706
  · exact context_12_280162_896761
  · exact context_12_280163_896811

theorem selected_cut_34521 : selected 9 ⟨896847, by decide⟩
    (prefixPartial 12 280164) = some ⟨12, 2, 0, 896847, 280164, 1557, 65536⟩ := by
  decide +kernel

theorem context_12_280164_896847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 280164 ⟨896847, by decide⟩ :=
  accepted_of_selected 12 280164 ⟨896847, by decide⟩ ⟨12, 2, 0, 896847, 280164, 1557, 65536⟩
    (by decide) selected_cut_34521

theorem selected_cut_34522 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 280165) = some ⟨12, 1, 0, 896706, 280165, 1, 65536⟩ := by
  decide +kernel

theorem context_12_280165_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 280165 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 280165 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 280165, 1, 65536⟩
    (by decide) selected_cut_34522

theorem selected_cut_34523 : selected 9 ⟨896890, by decide⟩
    (prefixPartial 12 280166) = some ⟨12, 2, 0, 896890, 280166, 1545, 65536⟩ := by
  decide +kernel

theorem context_12_280166_896890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 280166 ⟨896890, by decide⟩ :=
  accepted_of_selected 12 280166 ⟨896890, by decide⟩ ⟨12, 2, 0, 896890, 280166, 1545, 65536⟩
    (by decide) selected_cut_34523

theorem selected_cut_34524 : selected 9 ⟨896926, by decide⟩
    (prefixPartial 12 280167) = some ⟨12, 2, 0, 896926, 280167, 1561, 65536⟩ := by
  decide +kernel

theorem context_12_280167_896926 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 280167 ⟨896926, by decide⟩ :=
  accepted_of_selected 12 280167 ⟨896926, by decide⟩ ⟨12, 2, 0, 896926, 280167, 1561, 65536⟩
    (by decide) selected_cut_34524

theorem unmarked_context_11_70041_896927 : frontier 10 ⟨896927, by decide⟩
    (prefixCache 11 70041) (prefixPartial 11 70041) = false := by
  decide +kernel

theorem node_context_11_70041_896927 : EJMOriginalGlobalDAGData.nodes 10 ⟨896927, by decide⟩ =
    .split (coordinate 11) (![⟨896847, by decide⟩,⟨896706, by decide⟩,⟨896890, by decide⟩,⟨896926, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70041_896927 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70041 ⟨896927, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70041
    ⟨896927, by decide⟩ (by decide) (![⟨896847, by decide⟩,⟨896706, by decide⟩,⟨896890, by decide⟩,⟨896926, by decide⟩]) unmarked_context_11_70041_896927 node_context_11_70041_896927
  intro a
  fin_cases a
  · exact context_12_280164_896847
  · exact context_12_280165_896706
  · exact context_12_280166_896890
  · exact context_12_280167_896926

theorem selected_cut_34525 : selected 10 ⟨897000, by decide⟩
    (prefixPartial 11 70042) = some ⟨11, 2, 0, 897000, 70042, 3105, 262144⟩ := by
  decide +kernel

theorem context_11_70042_897000 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70042 ⟨897000, by decide⟩ :=
  accepted_of_selected 11 70042 ⟨897000, by decide⟩ ⟨11, 2, 0, 897000, 70042, 3105, 262144⟩
    (by decide) selected_cut_34525

theorem selected_cut_34526 : selected 9 ⟨897029, by decide⟩
    (prefixPartial 12 280172) = some ⟨12, 2, 0, 897029, 280172, 1645, 65536⟩ := by
  decide +kernel

theorem context_12_280172_897029 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 280172 ⟨897029, by decide⟩ :=
  accepted_of_selected 12 280172 ⟨897029, by decide⟩ ⟨12, 2, 0, 897029, 280172, 1645, 65536⟩
    (by decide) selected_cut_34526

theorem selected_cut_34527 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 280173) = some ⟨12, 1, 0, 896706, 280173, 1, 65536⟩ := by
  decide +kernel

theorem context_12_280173_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 280173 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 280173 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 280173, 1, 65536⟩
    (by decide) selected_cut_34527

theorem selected_cut_34528 : selected 9 ⟨897065, by decide⟩
    (prefixPartial 12 280174) = some ⟨12, 2, 0, 897065, 280174, 1589, 65536⟩ := by
  decide +kernel

theorem context_12_280174_897065 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 280174 ⟨897065, by decide⟩ :=
  accepted_of_selected 12 280174 ⟨897065, by decide⟩ ⟨12, 2, 0, 897065, 280174, 1589, 65536⟩
    (by decide) selected_cut_34528

theorem selected_cut_34529 : selected 9 ⟨897096, by decide⟩
    (prefixPartial 12 280175) = some ⟨12, 2, 0, 897096, 280175, 1609, 65536⟩ := by
  decide +kernel

theorem context_12_280175_897096 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 280175 ⟨897096, by decide⟩ :=
  accepted_of_selected 12 280175 ⟨897096, by decide⟩ ⟨12, 2, 0, 897096, 280175, 1609, 65536⟩
    (by decide) selected_cut_34529

theorem unmarked_context_11_70043_897097 : frontier 10 ⟨897097, by decide⟩
    (prefixCache 11 70043) (prefixPartial 11 70043) = false := by
  decide +kernel

theorem node_context_11_70043_897097 : EJMOriginalGlobalDAGData.nodes 10 ⟨897097, by decide⟩ =
    .split (coordinate 11) (![⟨897029, by decide⟩,⟨896706, by decide⟩,⟨897065, by decide⟩,⟨897096, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70043_897097 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70043 ⟨897097, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70043
    ⟨897097, by decide⟩ (by decide) (![⟨897029, by decide⟩,⟨896706, by decide⟩,⟨897065, by decide⟩,⟨897096, by decide⟩]) unmarked_context_11_70043_897097 node_context_11_70043_897097
  intro a
  fin_cases a
  · exact context_12_280172_897029
  · exact context_12_280173_896706
  · exact context_12_280174_897065
  · exact context_12_280175_897096

theorem unmarked_context_10_17510_897098 : frontier 11 ⟨897098, by decide⟩
    (prefixCache 10 17510) (prefixPartial 10 17510) = false := by
  decide +kernel

theorem node_context_10_17510_897098 : EJMOriginalGlobalDAGData.nodes 11 ⟨897098, by decide⟩ =
    .split (coordinate 10) (![⟨896812, by decide⟩,⟨896927, by decide⟩,⟨897000, by decide⟩,⟨897097, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17510_897098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17510 ⟨897098, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17510
    ⟨897098, by decide⟩ (by decide) (![⟨896812, by decide⟩,⟨896927, by decide⟩,⟨897000, by decide⟩,⟨897097, by decide⟩]) unmarked_context_10_17510_897098 node_context_10_17510_897098
  intro a
  fin_cases a
  · exact context_11_70040_896812
  · exact context_11_70041_896927
  · exact context_11_70042_897000
  · exact context_11_70043_897097

theorem selected_cut_34530 : selected 10 ⟨897195, by decide⟩
    (prefixPartial 11 70044) = some ⟨11, 2, 0, 897195, 70044, 3945, 262144⟩ := by
  decide +kernel

theorem context_11_70044_897195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70044 ⟨897195, by decide⟩ :=
  accepted_of_selected 11 70044 ⟨897195, by decide⟩ ⟨11, 2, 0, 897195, 70044, 3945, 262144⟩
    (by decide) selected_cut_34530

theorem selected_cut_34531 : selected 10 ⟨897264, by decide⟩
    (prefixPartial 11 70045) = some ⟨11, 2, 0, 897264, 70045, 3249, 262144⟩ := by
  decide +kernel

theorem context_11_70045_897264 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70045 ⟨897264, by decide⟩ :=
  accepted_of_selected 11 70045 ⟨897264, by decide⟩ ⟨11, 2, 0, 897264, 70045, 3249, 262144⟩
    (by decide) selected_cut_34531

theorem selected_cut_34532 : selected 10 ⟨897306, by decide⟩
    (prefixPartial 11 70046) = some ⟨11, 2, 0, 897306, 70046, 2069, 262144⟩ := by
  decide +kernel

theorem context_11_70046_897306 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70046 ⟨897306, by decide⟩ :=
  accepted_of_selected 11 70046 ⟨897306, by decide⟩ ⟨11, 2, 0, 897306, 70046, 2069, 262144⟩
    (by decide) selected_cut_34532

theorem selected_cut_34533 : selected 10 ⟨897361, by decide⟩
    (prefixPartial 11 70047) = some ⟨11, 2, 0, 897361, 70047, 3169, 262144⟩ := by
  decide +kernel

theorem context_11_70047_897361 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70047 ⟨897361, by decide⟩ :=
  accepted_of_selected 11 70047 ⟨897361, by decide⟩ ⟨11, 2, 0, 897361, 70047, 3169, 262144⟩
    (by decide) selected_cut_34533

theorem unmarked_context_10_17511_897362 : frontier 11 ⟨897362, by decide⟩
    (prefixCache 10 17511) (prefixPartial 10 17511) = false := by
  decide +kernel

theorem node_context_10_17511_897362 : EJMOriginalGlobalDAGData.nodes 11 ⟨897362, by decide⟩ =
    .split (coordinate 10) (![⟨897195, by decide⟩,⟨897264, by decide⟩,⟨897306, by decide⟩,⟨897361, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17511_897362 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17511 ⟨897362, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17511
    ⟨897362, by decide⟩ (by decide) (![⟨897195, by decide⟩,⟨897264, by decide⟩,⟨897306, by decide⟩,⟨897361, by decide⟩]) unmarked_context_10_17511_897362 node_context_10_17511_897362
  intro a
  fin_cases a
  · exact context_11_70044_897195
  · exact context_11_70045_897264
  · exact context_11_70046_897306
  · exact context_11_70047_897361

theorem unmarked_context_9_4377_897363 : frontier 12 ⟨897363, by decide⟩
    (prefixCache 9 4377) (prefixPartial 9 4377) = false := by
  decide +kernel

theorem node_context_9_4377_897363 : EJMOriginalGlobalDAGData.nodes 12 ⟨897363, by decide⟩ =
    .split (coordinate 9) (![⟨3442, by decide⟩,⟨893098, by decide⟩,⟨897098, by decide⟩,⟨897362, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4377_897363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4377 ⟨897363, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4377
    ⟨897363, by decide⟩ (by decide) (![⟨3442, by decide⟩,⟨893098, by decide⟩,⟨897098, by decide⟩,⟨897362, by decide⟩]) unmarked_context_9_4377_897363 node_context_9_4377_897363
  intro a
  fin_cases a
  · exact context_10_17508_3442
  · exact context_10_17509_893098
  · exact context_10_17510_897098
  · exact context_10_17511_897362

theorem selected_cut_34534 : selected 11 ⟨3442, by decide⟩
    (prefixPartial 10 17512) = some ⟨10, 1, 0, 3442, 17512, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_17512_3442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17512 ⟨3442, by decide⟩ :=
  accepted_of_selected 10 17512 ⟨3442, by decide⟩ ⟨10, 1, 0, 3442, 17512, 1, 1048576⟩
    (by decide) selected_cut_34534

theorem selected_cut_34535 : selected 11 ⟨3442, by decide⟩
    (prefixPartial 10 17513) = some ⟨10, 1, 0, 3442, 17513, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_17513_3442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17513 ⟨3442, by decide⟩ :=
  accepted_of_selected 10 17513 ⟨3442, by decide⟩ ⟨10, 1, 0, 3442, 17513, 1, 1048576⟩
    (by decide) selected_cut_34535

theorem selected_cut_34536 : selected 10 ⟨897412, by decide⟩
    (prefixPartial 11 70056) = some ⟨11, 2, 0, 897412, 70056, 2677, 262144⟩ := by
  decide +kernel

theorem context_11_70056_897412 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70056 ⟨897412, by decide⟩ :=
  accepted_of_selected 11 70056 ⟨897412, by decide⟩ ⟨11, 2, 0, 897412, 70056, 2677, 262144⟩
    (by decide) selected_cut_34536

theorem selected_cut_34537 : selected 10 ⟨897440, by decide⟩
    (prefixPartial 11 70057) = some ⟨11, 2, 0, 897440, 70057, 1673, 262144⟩ := by
  decide +kernel

theorem context_11_70057_897440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70057 ⟨897440, by decide⟩ :=
  accepted_of_selected 11 70057 ⟨897440, by decide⟩ ⟨11, 2, 0, 897440, 70057, 1673, 262144⟩
    (by decide) selected_cut_34537

theorem selected_cut_34538 : selected 10 ⟨897452, by decide⟩
    (prefixPartial 11 70058) = some ⟨11, 2, 0, 897452, 70058, 601, 262144⟩ := by
  decide +kernel

theorem context_11_70058_897452 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70058 ⟨897452, by decide⟩ :=
  accepted_of_selected 11 70058 ⟨897452, by decide⟩ ⟨11, 2, 0, 897452, 70058, 601, 262144⟩
    (by decide) selected_cut_34538

theorem selected_cut_34539 : selected 10 ⟨897463, by decide⟩
    (prefixPartial 11 70059) = some ⟨11, 2, 0, 897463, 70059, 381, 262144⟩ := by
  decide +kernel

theorem context_11_70059_897463 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70059 ⟨897463, by decide⟩ :=
  accepted_of_selected 11 70059 ⟨897463, by decide⟩ ⟨11, 2, 0, 897463, 70059, 381, 262144⟩
    (by decide) selected_cut_34539

theorem unmarked_context_10_17514_897464 : frontier 11 ⟨897464, by decide⟩
    (prefixCache 10 17514) (prefixPartial 10 17514) = false := by
  decide +kernel

theorem node_context_10_17514_897464 : EJMOriginalGlobalDAGData.nodes 11 ⟨897464, by decide⟩ =
    .split (coordinate 10) (![⟨897412, by decide⟩,⟨897440, by decide⟩,⟨897452, by decide⟩,⟨897463, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17514_897464 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17514 ⟨897464, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17514
    ⟨897464, by decide⟩ (by decide) (![⟨897412, by decide⟩,⟨897440, by decide⟩,⟨897452, by decide⟩,⟨897463, by decide⟩]) unmarked_context_10_17514_897464 node_context_10_17514_897464
  intro a
  fin_cases a
  · exact context_11_70056_897412
  · exact context_11_70057_897440
  · exact context_11_70058_897452
  · exact context_11_70059_897463

theorem selected_cut_34540 : selected 10 ⟨897506, by decide⟩
    (prefixPartial 11 70060) = some ⟨11, 2, 0, 897506, 70060, 2161, 262144⟩ := by
  decide +kernel

theorem context_11_70060_897506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70060 ⟨897506, by decide⟩ :=
  accepted_of_selected 11 70060 ⟨897506, by decide⟩ ⟨11, 2, 0, 897506, 70060, 2161, 262144⟩
    (by decide) selected_cut_34540

theorem selected_cut_34541 : selected 10 ⟨897546, by decide⟩
    (prefixPartial 11 70061) = some ⟨11, 2, 0, 897546, 70061, 1741, 262144⟩ := by
  decide +kernel

theorem context_11_70061_897546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70061 ⟨897546, by decide⟩ :=
  accepted_of_selected 11 70061 ⟨897546, by decide⟩ ⟨11, 2, 0, 897546, 70061, 1741, 262144⟩
    (by decide) selected_cut_34541

theorem selected_cut_34542 : selected 10 ⟨897570, by decide⟩
    (prefixPartial 11 70062) = some ⟨11, 2, 0, 897570, 70062, 1009, 262144⟩ := by
  decide +kernel

theorem context_11_70062_897570 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70062 ⟨897570, by decide⟩ :=
  accepted_of_selected 11 70062 ⟨897570, by decide⟩ ⟨11, 2, 0, 897570, 70062, 1009, 262144⟩
    (by decide) selected_cut_34542

theorem selected_cut_34543 : selected 10 ⟨897593, by decide⟩
    (prefixPartial 11 70063) = some ⟨11, 2, 0, 897593, 70063, 969, 262144⟩ := by
  decide +kernel

theorem context_11_70063_897593 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70063 ⟨897593, by decide⟩ :=
  accepted_of_selected 11 70063 ⟨897593, by decide⟩ ⟨11, 2, 0, 897593, 70063, 969, 262144⟩
    (by decide) selected_cut_34543

theorem unmarked_context_10_17515_897594 : frontier 11 ⟨897594, by decide⟩
    (prefixCache 10 17515) (prefixPartial 10 17515) = false := by
  decide +kernel

theorem node_context_10_17515_897594 : EJMOriginalGlobalDAGData.nodes 11 ⟨897594, by decide⟩ =
    .split (coordinate 10) (![⟨897506, by decide⟩,⟨897546, by decide⟩,⟨897570, by decide⟩,⟨897593, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17515_897594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17515 ⟨897594, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17515
    ⟨897594, by decide⟩ (by decide) (![⟨897506, by decide⟩,⟨897546, by decide⟩,⟨897570, by decide⟩,⟨897593, by decide⟩]) unmarked_context_10_17515_897594 node_context_10_17515_897594
  intro a
  fin_cases a
  · exact context_11_70060_897506
  · exact context_11_70061_897546
  · exact context_11_70062_897570
  · exact context_11_70063_897593

theorem unmarked_context_9_4378_897595 : frontier 12 ⟨897595, by decide⟩
    (prefixCache 9 4378) (prefixPartial 9 4378) = false := by
  decide +kernel

theorem node_context_9_4378_897595 : EJMOriginalGlobalDAGData.nodes 12 ⟨897595, by decide⟩ =
    .split (coordinate 9) (![⟨3442, by decide⟩,⟨3442, by decide⟩,⟨897464, by decide⟩,⟨897594, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4378_897595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4378 ⟨897595, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4378
    ⟨897595, by decide⟩ (by decide) (![⟨3442, by decide⟩,⟨3442, by decide⟩,⟨897464, by decide⟩,⟨897594, by decide⟩]) unmarked_context_9_4378_897595 node_context_9_4378_897595
  intro a
  fin_cases a
  · exact context_10_17512_3442
  · exact context_10_17513_3442
  · exact context_10_17514_897464
  · exact context_10_17515_897594

theorem selected_cut_34544 : selected 12 ⟨897635, by decide⟩
    (prefixPartial 9 4379) = some ⟨9, 2, 0, 897635, 4379, 697, 4194304⟩ := by
  decide +kernel

theorem context_9_4379_897635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4379 ⟨897635, by decide⟩ :=
  accepted_of_selected 9 4379 ⟨897635, by decide⟩ ⟨9, 2, 0, 897635, 4379, 697, 4194304⟩
    (by decide) selected_cut_34544

theorem unmarked_context_8_1094_897636 : frontier 13 ⟨897636, by decide⟩
    (prefixCache 8 1094) (prefixPartial 8 1094) = false := by
  decide +kernel

theorem node_context_8_1094_897636 : EJMOriginalGlobalDAGData.nodes 13 ⟨897636, by decide⟩ =
    .split (coordinate 8) (![⟨896642, by decide⟩,⟨897363, by decide⟩,⟨897595, by decide⟩,⟨897635, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1094_897636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1094 ⟨897636, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1094
    ⟨897636, by decide⟩ (by decide) (![⟨896642, by decide⟩,⟨897363, by decide⟩,⟨897595, by decide⟩,⟨897635, by decide⟩]) unmarked_context_8_1094_897636 node_context_8_1094_897636
  intro a
  fin_cases a
  · exact context_9_4376_896642
  · exact context_9_4377_897363
  · exact context_9_4378_897595
  · exact context_9_4379_897635

theorem selected_cut_34545 : selected 13 ⟨14298, by decide⟩
    (prefixPartial 8 1095) = some ⟨8, 1, 0, 14298, 1095, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_1095_14298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1095 ⟨14298, by decide⟩ :=
  accepted_of_selected 8 1095 ⟨14298, by decide⟩ ⟨8, 1, 0, 14298, 1095, 1, 16777216⟩
    (by decide) selected_cut_34545

theorem unmarked_context_7_273_897637 : frontier 14 ⟨897637, by decide⟩
    (prefixCache 7 273) (prefixPartial 7 273) = false := by
  decide +kernel

theorem node_context_7_273_897637 : EJMOriginalGlobalDAGData.nodes 14 ⟨897637, by decide⟩ =
    .split (coordinate 7) (![⟨14300, by decide⟩,⟨893315, by decide⟩,⟨897636, by decide⟩,⟨14298, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_273_897637 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 273 ⟨897637, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 273
    ⟨897637, by decide⟩ (by decide) (![⟨14300, by decide⟩,⟨893315, by decide⟩,⟨897636, by decide⟩,⟨14298, by decide⟩]) unmarked_context_7_273_897637 node_context_7_273_897637
  intro a
  fin_cases a
  · exact context_8_1092_14300
  · exact context_8_1093_893315
  · exact context_8_1094_897636
  · exact context_8_1095_14298

theorem selected_cut_34546 : selected 13 ⟨14300, by decide⟩
    (prefixPartial 8 1096) = some ⟨8, 1, 0, 14300, 1096, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_1096_14300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1096 ⟨14300, by decide⟩ :=
  accepted_of_selected 8 1096 ⟨14300, by decide⟩ ⟨8, 1, 0, 14300, 1096, 1, 16777216⟩
    (by decide) selected_cut_34546

theorem selected_cut_34547 : selected 13 ⟨14300, by decide⟩
    (prefixPartial 8 1097) = some ⟨8, 1, 0, 14300, 1097, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_1097_14300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1097 ⟨14300, by decide⟩ :=
  accepted_of_selected 8 1097 ⟨14300, by decide⟩ ⟨8, 1, 0, 14300, 1097, 1, 16777216⟩
    (by decide) selected_cut_34547

theorem selected_cut_34548 : selected 9 ⟨897832, by decide⟩
    (prefixPartial 12 281088) = some ⟨12, 2, 0, 897832, 281088, 2097, 65536⟩ := by
  decide +kernel

theorem context_12_281088_897832 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281088 ⟨897832, by decide⟩ :=
  accepted_of_selected 12 281088 ⟨897832, by decide⟩ ⟨12, 2, 0, 897832, 281088, 2097, 65536⟩
    (by decide) selected_cut_34548

theorem selected_cut_34549 : selected 8 ⟨897904, by decide⟩
    (prefixPartial 13 1124356) = some ⟨13, 2, 0, 897904, 1124356, 1989, 16384⟩ := by
  decide +kernel

theorem context_13_1124356_897904 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1124356 ⟨897904, by decide⟩ :=
  accepted_of_selected 13 1124356 ⟨897904, by decide⟩ ⟨13, 2, 0, 897904, 1124356, 1989, 16384⟩
    (by decide) selected_cut_34549

theorem selected_cut_34550 : selected 8 ⟨897938, by decide⟩
    (prefixPartial 13 1124357) = some ⟨13, 2, 0, 897938, 1124357, 829, 16384⟩ := by
  decide +kernel

theorem context_13_1124357_897938 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1124357 ⟨897938, by decide⟩ :=
  accepted_of_selected 13 1124357 ⟨897938, by decide⟩ ⟨13, 2, 0, 897938, 1124357, 829, 16384⟩
    (by decide) selected_cut_34550

theorem selected_cut_34551 : selected 8 ⟨897985, by decide⟩
    (prefixPartial 13 1124358) = some ⟨13, 2, 0, 897985, 1124358, 1093, 16384⟩ := by
  decide +kernel

theorem context_13_1124358_897985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1124358 ⟨897985, by decide⟩ :=
  accepted_of_selected 13 1124358 ⟨897985, by decide⟩ ⟨13, 2, 0, 897985, 1124358, 1093, 16384⟩
    (by decide) selected_cut_34551

theorem selected_cut_34552 : selected 8 ⟨898005, by decide⟩
    (prefixPartial 13 1124359) = some ⟨13, 2, 0, 898005, 1124359, 653, 16384⟩ := by
  decide +kernel

theorem context_13_1124359_898005 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1124359 ⟨898005, by decide⟩ :=
  accepted_of_selected 13 1124359 ⟨898005, by decide⟩ ⟨13, 2, 0, 898005, 1124359, 653, 16384⟩
    (by decide) selected_cut_34552

theorem unmarked_context_12_281089_898006 : frontier 9 ⟨898006, by decide⟩
    (prefixCache 12 281089) (prefixPartial 12 281089) = false := by
  decide +kernel

theorem node_context_12_281089_898006 : EJMOriginalGlobalDAGData.nodes 9 ⟨898006, by decide⟩ =
    .split (coordinate 12) (![⟨897904, by decide⟩,⟨897938, by decide⟩,⟨897985, by decide⟩,⟨898005, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_281089_898006 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281089 ⟨898006, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 281089
    ⟨898006, by decide⟩ (by decide) (![⟨897904, by decide⟩,⟨897938, by decide⟩,⟨897985, by decide⟩,⟨898005, by decide⟩]) unmarked_context_12_281089_898006 node_context_12_281089_898006
  intro a
  fin_cases a
  · exact context_13_1124356_897904
  · exact context_13_1124357_897938
  · exact context_13_1124358_897985
  · exact context_13_1124359_898005

theorem selected_cut_34553 : selected 9 ⟨898007, by decide⟩
    (prefixPartial 12 281090) = some ⟨12, 1, 0, 898007, 281090, 1, 65536⟩ := by
  decide +kernel

theorem context_12_281090_898007 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281090 ⟨898007, by decide⟩ :=
  accepted_of_selected 12 281090 ⟨898007, by decide⟩ ⟨12, 1, 0, 898007, 281090, 1, 65536⟩
    (by decide) selected_cut_34553

theorem selected_cut_34554 : selected 9 ⟨898147, by decide⟩
    (prefixPartial 12 281091) = some ⟨12, 2, 0, 898147, 281091, 3393, 65536⟩ := by
  decide +kernel

theorem context_12_281091_898147 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281091 ⟨898147, by decide⟩ :=
  accepted_of_selected 12 281091 ⟨898147, by decide⟩ ⟨12, 2, 0, 898147, 281091, 3393, 65536⟩
    (by decide) selected_cut_34554

theorem unmarked_context_11_70272_898148 : frontier 10 ⟨898148, by decide⟩
    (prefixCache 11 70272) (prefixPartial 11 70272) = false := by
  decide +kernel

theorem node_context_11_70272_898148 : EJMOriginalGlobalDAGData.nodes 10 ⟨898148, by decide⟩ =
    .split (coordinate 11) (![⟨897832, by decide⟩,⟨898006, by decide⟩,⟨898007, by decide⟩,⟨898147, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70272_898148 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70272 ⟨898148, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70272
    ⟨898148, by decide⟩ (by decide) (![⟨897832, by decide⟩,⟨898006, by decide⟩,⟨898007, by decide⟩,⟨898147, by decide⟩]) unmarked_context_11_70272_898148 node_context_11_70272_898148
  intro a
  fin_cases a
  · exact context_12_281088_897832
  · exact context_12_281089_898006
  · exact context_12_281090_898007
  · exact context_12_281091_898147

theorem selected_cut_34555 : selected 9 ⟨898284, by decide⟩
    (prefixPartial 12 281092) = some ⟨12, 2, 0, 898284, 281092, 3121, 65536⟩ := by
  decide +kernel

theorem context_12_281092_898284 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281092 ⟨898284, by decide⟩ :=
  accepted_of_selected 12 281092 ⟨898284, by decide⟩ ⟨12, 2, 0, 898284, 281092, 3121, 65536⟩
    (by decide) selected_cut_34555

theorem selected_cut_34556 : selected 9 ⟨898384, by decide⟩
    (prefixPartial 12 281093) = some ⟨12, 2, 0, 898384, 281093, 3993, 65536⟩ := by
  decide +kernel

theorem context_12_281093_898384 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281093 ⟨898384, by decide⟩ :=
  accepted_of_selected 12 281093 ⟨898384, by decide⟩ ⟨12, 2, 0, 898384, 281093, 3993, 65536⟩
    (by decide) selected_cut_34556

theorem selected_cut_34557 : selected 8 ⟨898425, by decide⟩
    (prefixPartial 13 1124376) = some ⟨13, 2, 0, 898425, 1124376, 1441, 16384⟩ := by
  decide +kernel

theorem context_13_1124376_898425 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1124376 ⟨898425, by decide⟩ :=
  accepted_of_selected 13 1124376 ⟨898425, by decide⟩ ⟨13, 2, 0, 898425, 1124376, 1441, 16384⟩
    (by decide) selected_cut_34557

theorem selected_cut_34558 : selected 8 ⟨898454, by decide⟩
    (prefixPartial 13 1124377) = some ⟨13, 2, 0, 898454, 1124377, 833, 16384⟩ := by
  decide +kernel

theorem context_13_1124377_898454 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1124377 ⟨898454, by decide⟩ :=
  accepted_of_selected 13 1124377 ⟨898454, by decide⟩ ⟨13, 2, 0, 898454, 1124377, 833, 16384⟩
    (by decide) selected_cut_34558

theorem selected_cut_34559 : selected 8 ⟨898490, by decide⟩
    (prefixPartial 13 1124378) = some ⟨13, 2, 0, 898490, 1124378, 1289, 16384⟩ := by
  decide +kernel

theorem context_13_1124378_898490 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1124378 ⟨898490, by decide⟩ :=
  accepted_of_selected 13 1124378 ⟨898490, by decide⟩ ⟨13, 2, 0, 898490, 1124378, 1289, 16384⟩
    (by decide) selected_cut_34559

theorem selected_cut_34560 : selected 8 ⟨898502, by decide⟩
    (prefixPartial 13 1124379) = some ⟨13, 2, 0, 898502, 1124379, 725, 16384⟩ := by
  decide +kernel

theorem context_13_1124379_898502 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1124379 ⟨898502, by decide⟩ :=
  accepted_of_selected 13 1124379 ⟨898502, by decide⟩ ⟨13, 2, 0, 898502, 1124379, 725, 16384⟩
    (by decide) selected_cut_34560

theorem unmarked_context_12_281094_898503 : frontier 9 ⟨898503, by decide⟩
    (prefixCache 12 281094) (prefixPartial 12 281094) = false := by
  decide +kernel

theorem node_context_12_281094_898503 : EJMOriginalGlobalDAGData.nodes 9 ⟨898503, by decide⟩ =
    .split (coordinate 12) (![⟨898425, by decide⟩,⟨898454, by decide⟩,⟨898490, by decide⟩,⟨898502, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_281094_898503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281094 ⟨898503, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 281094
    ⟨898503, by decide⟩ (by decide) (![⟨898425, by decide⟩,⟨898454, by decide⟩,⟨898490, by decide⟩,⟨898502, by decide⟩]) unmarked_context_12_281094_898503 node_context_12_281094_898503
  intro a
  fin_cases a
  · exact context_13_1124376_898425
  · exact context_13_1124377_898454
  · exact context_13_1124378_898490
  · exact context_13_1124379_898502

theorem selected_cut_34561 : selected 8 ⟨898553, by decide⟩
    (prefixPartial 13 1124380) = some ⟨13, 2, 0, 898553, 1124380, 1689, 16384⟩ := by
  decide +kernel

theorem context_13_1124380_898553 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1124380 ⟨898553, by decide⟩ :=
  accepted_of_selected 13 1124380 ⟨898553, by decide⟩ ⟨13, 2, 0, 898553, 1124380, 1689, 16384⟩
    (by decide) selected_cut_34561

theorem selected_cut_34562 : selected 8 ⟨898578, by decide⟩
    (prefixPartial 13 1124381) = some ⟨13, 2, 0, 898578, 1124381, 945, 16384⟩ := by
  decide +kernel

theorem context_13_1124381_898578 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1124381 ⟨898578, by decide⟩ :=
  accepted_of_selected 13 1124381 ⟨898578, by decide⟩ ⟨13, 2, 0, 898578, 1124381, 945, 16384⟩
    (by decide) selected_cut_34562

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
