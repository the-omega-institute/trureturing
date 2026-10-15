/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover306
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_29476 : selected 9 ⟨743941, by decide⟩
    (prefixPartial 12 93547) = some ⟨12, 2, 0, 743941, 93547, 3273, 65536⟩ := by
  decide +kernel

theorem context_12_93547_743941 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93547 ⟨743941, by decide⟩ :=
  accepted_of_selected 12 93547 ⟨743941, by decide⟩ ⟨12, 2, 0, 743941, 93547, 3273, 65536⟩
    (by decide) selected_cut_29476

theorem unmarked_context_11_23386_743942 : frontier 10 ⟨743942, by decide⟩
    (prefixCache 11 23386) (prefixPartial 11 23386) = false := by
  decide +kernel

theorem node_context_11_23386_743942 : EJMOriginalGlobalDAGData.nodes 10 ⟨743942, by decide⟩ =
    .split (coordinate 11) (![⟨743849, by decide⟩,⟨691709, by decide⟩,⟨743897, by decide⟩,⟨743941, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23386_743942 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23386 ⟨743942, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23386
    ⟨743942, by decide⟩ (by decide) (![⟨743849, by decide⟩,⟨691709, by decide⟩,⟨743897, by decide⟩,⟨743941, by decide⟩]) unmarked_context_11_23386_743942 node_context_11_23386_743942
  intro a
  fin_cases a
  · exact context_12_93544_743849
  · exact context_12_93545_691709
  · exact context_12_93546_743897
  · exact context_12_93547_743941

theorem selected_cut_29477 : selected 9 ⟨743974, by decide⟩
    (prefixPartial 12 93548) = some ⟨12, 2, 0, 743974, 93548, 3069, 65536⟩ := by
  decide +kernel

theorem context_12_93548_743974 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93548 ⟨743974, by decide⟩ :=
  accepted_of_selected 12 93548 ⟨743974, by decide⟩ ⟨12, 2, 0, 743974, 93548, 3069, 65536⟩
    (by decide) selected_cut_29477

theorem selected_cut_29478 : selected 9 ⟨691822, by decide⟩
    (prefixPartial 12 93549) = some ⟨12, 1, 0, 691822, 93549, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93549_691822 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93549 ⟨691822, by decide⟩ :=
  accepted_of_selected 12 93549 ⟨691822, by decide⟩ ⟨12, 1, 0, 691822, 93549, 1, 65536⟩
    (by decide) selected_cut_29478

theorem selected_cut_29479 : selected 9 ⟨744011, by decide⟩
    (prefixPartial 12 93550) = some ⟨12, 2, 0, 744011, 93550, 2949, 65536⟩ := by
  decide +kernel

theorem context_12_93550_744011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93550 ⟨744011, by decide⟩ :=
  accepted_of_selected 12 93550 ⟨744011, by decide⟩ ⟨12, 2, 0, 744011, 93550, 2949, 65536⟩
    (by decide) selected_cut_29479

theorem selected_cut_29480 : selected 9 ⟨744050, by decide⟩
    (prefixPartial 12 93551) = some ⟨12, 2, 0, 744050, 93551, 3181, 65536⟩ := by
  decide +kernel

theorem context_12_93551_744050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93551 ⟨744050, by decide⟩ :=
  accepted_of_selected 12 93551 ⟨744050, by decide⟩ ⟨12, 2, 0, 744050, 93551, 3181, 65536⟩
    (by decide) selected_cut_29480

theorem unmarked_context_11_23387_744051 : frontier 10 ⟨744051, by decide⟩
    (prefixCache 11 23387) (prefixPartial 11 23387) = false := by
  decide +kernel

theorem node_context_11_23387_744051 : EJMOriginalGlobalDAGData.nodes 10 ⟨744051, by decide⟩ =
    .split (coordinate 11) (![⟨743974, by decide⟩,⟨691822, by decide⟩,⟨744011, by decide⟩,⟨744050, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23387_744051 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23387 ⟨744051, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23387
    ⟨744051, by decide⟩ (by decide) (![⟨743974, by decide⟩,⟨691822, by decide⟩,⟨744011, by decide⟩,⟨744050, by decide⟩]) unmarked_context_11_23387_744051 node_context_11_23387_744051
  intro a
  fin_cases a
  · exact context_12_93548_743974
  · exact context_12_93549_691822
  · exact context_12_93550_744011
  · exact context_12_93551_744050

theorem unmarked_context_10_5846_744052 : frontier 11 ⟨744052, by decide⟩
    (prefixCache 10 5846) (prefixPartial 10 5846) = false := by
  decide +kernel

theorem node_context_10_5846_744052 : EJMOriginalGlobalDAGData.nodes 11 ⟨744052, by decide⟩ =
    .split (coordinate 10) (![⟨743681, by decide⟩,⟨743807, by decide⟩,⟨743942, by decide⟩,⟨744051, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5846_744052 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5846 ⟨744052, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5846
    ⟨744052, by decide⟩ (by decide) (![⟨743681, by decide⟩,⟨743807, by decide⟩,⟨743942, by decide⟩,⟨744051, by decide⟩]) unmarked_context_10_5846_744052 node_context_10_5846_744052
  intro a
  fin_cases a
  · exact context_11_23384_743681
  · exact context_11_23385_743807
  · exact context_11_23386_743942
  · exact context_11_23387_744051

theorem selected_cut_29481 : selected 9 ⟨744094, by decide⟩
    (prefixPartial 12 93552) = some ⟨12, 2, 0, 744094, 93552, 3293, 65536⟩ := by
  decide +kernel

theorem context_12_93552_744094 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93552 ⟨744094, by decide⟩ :=
  accepted_of_selected 12 93552 ⟨744094, by decide⟩ ⟨12, 2, 0, 744094, 93552, 3293, 65536⟩
    (by decide) selected_cut_29481

theorem selected_cut_29482 : selected 9 ⟨126884, by decide⟩
    (prefixPartial 12 93553) = some ⟨12, 1, 0, 126884, 93553, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93553_126884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93553 ⟨126884, by decide⟩ :=
  accepted_of_selected 12 93553 ⟨126884, by decide⟩ ⟨12, 1, 0, 126884, 93553, 1, 65536⟩
    (by decide) selected_cut_29482

theorem selected_cut_29483 : selected 9 ⟨744137, by decide⟩
    (prefixPartial 12 93554) = some ⟨12, 2, 0, 744137, 93554, 3405, 65536⟩ := by
  decide +kernel

theorem context_12_93554_744137 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93554 ⟨744137, by decide⟩ :=
  accepted_of_selected 12 93554 ⟨744137, by decide⟩ ⟨12, 2, 0, 744137, 93554, 3405, 65536⟩
    (by decide) selected_cut_29483

theorem selected_cut_29484 : selected 9 ⟨744184, by decide⟩
    (prefixPartial 12 93555) = some ⟨12, 2, 0, 744184, 93555, 3597, 65536⟩ := by
  decide +kernel

theorem context_12_93555_744184 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93555 ⟨744184, by decide⟩ :=
  accepted_of_selected 12 93555 ⟨744184, by decide⟩ ⟨12, 2, 0, 744184, 93555, 3597, 65536⟩
    (by decide) selected_cut_29484

theorem unmarked_context_11_23388_744185 : frontier 10 ⟨744185, by decide⟩
    (prefixCache 11 23388) (prefixPartial 11 23388) = false := by
  decide +kernel

theorem node_context_11_23388_744185 : EJMOriginalGlobalDAGData.nodes 10 ⟨744185, by decide⟩ =
    .split (coordinate 11) (![⟨744094, by decide⟩,⟨126884, by decide⟩,⟨744137, by decide⟩,⟨744184, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23388_744185 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23388 ⟨744185, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23388
    ⟨744185, by decide⟩ (by decide) (![⟨744094, by decide⟩,⟨126884, by decide⟩,⟨744137, by decide⟩,⟨744184, by decide⟩]) unmarked_context_11_23388_744185 node_context_11_23388_744185
  intro a
  fin_cases a
  · exact context_12_93552_744094
  · exact context_12_93553_126884
  · exact context_12_93554_744137
  · exact context_12_93555_744184

theorem selected_cut_29485 : selected 9 ⟨744220, by decide⟩
    (prefixPartial 12 93556) = some ⟨12, 2, 0, 744220, 93556, 2481, 65536⟩ := by
  decide +kernel

theorem context_12_93556_744220 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93556 ⟨744220, by decide⟩ :=
  accepted_of_selected 12 93556 ⟨744220, by decide⟩ ⟨12, 2, 0, 744220, 93556, 2481, 65536⟩
    (by decide) selected_cut_29485

theorem selected_cut_29486 : selected 9 ⟨410616, by decide⟩
    (prefixPartial 12 93557) = some ⟨12, 1, 0, 410616, 93557, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93557_410616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93557 ⟨410616, by decide⟩ :=
  accepted_of_selected 12 93557 ⟨410616, by decide⟩ ⟨12, 1, 0, 410616, 93557, 1, 65536⟩
    (by decide) selected_cut_29486

theorem selected_cut_29487 : selected 9 ⟨744252, by decide⟩
    (prefixPartial 12 93558) = some ⟨12, 2, 0, 744252, 93558, 2457, 65536⟩ := by
  decide +kernel

theorem context_12_93558_744252 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93558 ⟨744252, by decide⟩ :=
  accepted_of_selected 12 93558 ⟨744252, by decide⟩ ⟨12, 2, 0, 744252, 93558, 2457, 65536⟩
    (by decide) selected_cut_29487

theorem selected_cut_29488 : selected 9 ⟨744285, by decide⟩
    (prefixPartial 12 93559) = some ⟨12, 2, 0, 744285, 93559, 2773, 65536⟩ := by
  decide +kernel

theorem context_12_93559_744285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93559 ⟨744285, by decide⟩ :=
  accepted_of_selected 12 93559 ⟨744285, by decide⟩ ⟨12, 2, 0, 744285, 93559, 2773, 65536⟩
    (by decide) selected_cut_29488

theorem unmarked_context_11_23389_744286 : frontier 10 ⟨744286, by decide⟩
    (prefixCache 11 23389) (prefixPartial 11 23389) = false := by
  decide +kernel

theorem node_context_11_23389_744286 : EJMOriginalGlobalDAGData.nodes 10 ⟨744286, by decide⟩ =
    .split (coordinate 11) (![⟨744220, by decide⟩,⟨410616, by decide⟩,⟨744252, by decide⟩,⟨744285, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23389_744286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23389 ⟨744286, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23389
    ⟨744286, by decide⟩ (by decide) (![⟨744220, by decide⟩,⟨410616, by decide⟩,⟨744252, by decide⟩,⟨744285, by decide⟩]) unmarked_context_11_23389_744286 node_context_11_23389_744286
  intro a
  fin_cases a
  · exact context_12_93556_744220
  · exact context_12_93557_410616
  · exact context_12_93558_744252
  · exact context_12_93559_744285

theorem selected_cut_29489 : selected 9 ⟨744329, by decide⟩
    (prefixPartial 12 93560) = some ⟨12, 2, 0, 744329, 93560, 2833, 65536⟩ := by
  decide +kernel

theorem context_12_93560_744329 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93560 ⟨744329, by decide⟩ :=
  accepted_of_selected 12 93560 ⟨744329, by decide⟩ ⟨12, 2, 0, 744329, 93560, 2833, 65536⟩
    (by decide) selected_cut_29489

theorem selected_cut_29490 : selected 9 ⟨691709, by decide⟩
    (prefixPartial 12 93561) = some ⟨12, 1, 0, 691709, 93561, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93561_691709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93561 ⟨691709, by decide⟩ :=
  accepted_of_selected 12 93561 ⟨691709, by decide⟩ ⟨12, 1, 0, 691709, 93561, 1, 65536⟩
    (by decide) selected_cut_29490

theorem selected_cut_29491 : selected 9 ⟨744364, by decide⟩
    (prefixPartial 12 93562) = some ⟨12, 2, 0, 744364, 93562, 2637, 65536⟩ := by
  decide +kernel

theorem context_12_93562_744364 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93562 ⟨744364, by decide⟩ :=
  accepted_of_selected 12 93562 ⟨744364, by decide⟩ ⟨12, 2, 0, 744364, 93562, 2637, 65536⟩
    (by decide) selected_cut_29491

theorem selected_cut_29492 : selected 9 ⟨744402, by decide⟩
    (prefixPartial 12 93563) = some ⟨12, 2, 0, 744402, 93563, 2929, 65536⟩ := by
  decide +kernel

theorem context_12_93563_744402 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93563 ⟨744402, by decide⟩ :=
  accepted_of_selected 12 93563 ⟨744402, by decide⟩ ⟨12, 2, 0, 744402, 93563, 2929, 65536⟩
    (by decide) selected_cut_29492

theorem unmarked_context_11_23390_744403 : frontier 10 ⟨744403, by decide⟩
    (prefixCache 11 23390) (prefixPartial 11 23390) = false := by
  decide +kernel

theorem node_context_11_23390_744403 : EJMOriginalGlobalDAGData.nodes 10 ⟨744403, by decide⟩ =
    .split (coordinate 11) (![⟨744329, by decide⟩,⟨691709, by decide⟩,⟨744364, by decide⟩,⟨744402, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23390_744403 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23390 ⟨744403, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23390
    ⟨744403, by decide⟩ (by decide) (![⟨744329, by decide⟩,⟨691709, by decide⟩,⟨744364, by decide⟩,⟨744402, by decide⟩]) unmarked_context_11_23390_744403 node_context_11_23390_744403
  intro a
  fin_cases a
  · exact context_12_93560_744329
  · exact context_12_93561_691709
  · exact context_12_93562_744364
  · exact context_12_93563_744402

theorem selected_cut_29493 : selected 9 ⟨744452, by decide⟩
    (prefixPartial 12 93564) = some ⟨12, 2, 0, 744452, 93564, 3169, 65536⟩ := by
  decide +kernel

theorem context_12_93564_744452 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93564 ⟨744452, by decide⟩ :=
  accepted_of_selected 12 93564 ⟨744452, by decide⟩ ⟨12, 2, 0, 744452, 93564, 3169, 65536⟩
    (by decide) selected_cut_29493

theorem selected_cut_29494 : selected 9 ⟨408930, by decide⟩
    (prefixPartial 12 93565) = some ⟨12, 1, 0, 408930, 93565, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93565_408930 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93565 ⟨408930, by decide⟩ :=
  accepted_of_selected 12 93565 ⟨408930, by decide⟩ ⟨12, 1, 0, 408930, 93565, 1, 65536⟩
    (by decide) selected_cut_29494

theorem selected_cut_29495 : selected 9 ⟨744491, by decide⟩
    (prefixPartial 12 93566) = some ⟨12, 2, 0, 744491, 93566, 3069, 65536⟩ := by
  decide +kernel

theorem context_12_93566_744491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93566 ⟨744491, by decide⟩ :=
  accepted_of_selected 12 93566 ⟨744491, by decide⟩ ⟨12, 2, 0, 744491, 93566, 3069, 65536⟩
    (by decide) selected_cut_29495

theorem selected_cut_29496 : selected 9 ⟨607719, by decide⟩
    (prefixPartial 12 93567) = some ⟨12, 1, 0, 607719, 93567, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93567_607719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93567 ⟨607719, by decide⟩ :=
  accepted_of_selected 12 93567 ⟨607719, by decide⟩ ⟨12, 1, 0, 607719, 93567, 1, 65536⟩
    (by decide) selected_cut_29496

theorem unmarked_context_11_23391_744492 : frontier 10 ⟨744492, by decide⟩
    (prefixCache 11 23391) (prefixPartial 11 23391) = false := by
  decide +kernel

theorem node_context_11_23391_744492 : EJMOriginalGlobalDAGData.nodes 10 ⟨744492, by decide⟩ =
    .split (coordinate 11) (![⟨744452, by decide⟩,⟨408930, by decide⟩,⟨744491, by decide⟩,⟨607719, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23391_744492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23391 ⟨744492, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23391
    ⟨744492, by decide⟩ (by decide) (![⟨744452, by decide⟩,⟨408930, by decide⟩,⟨744491, by decide⟩,⟨607719, by decide⟩]) unmarked_context_11_23391_744492 node_context_11_23391_744492
  intro a
  fin_cases a
  · exact context_12_93564_744452
  · exact context_12_93565_408930
  · exact context_12_93566_744491
  · exact context_12_93567_607719

theorem unmarked_context_10_5847_744493 : frontier 11 ⟨744493, by decide⟩
    (prefixCache 10 5847) (prefixPartial 10 5847) = false := by
  decide +kernel

theorem node_context_10_5847_744493 : EJMOriginalGlobalDAGData.nodes 11 ⟨744493, by decide⟩ =
    .split (coordinate 10) (![⟨744185, by decide⟩,⟨744286, by decide⟩,⟨744403, by decide⟩,⟨744492, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5847_744493 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5847 ⟨744493, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5847
    ⟨744493, by decide⟩ (by decide) (![⟨744185, by decide⟩,⟨744286, by decide⟩,⟨744403, by decide⟩,⟨744492, by decide⟩]) unmarked_context_10_5847_744493 node_context_10_5847_744493
  intro a
  fin_cases a
  · exact context_11_23388_744185
  · exact context_11_23389_744286
  · exact context_11_23390_744403
  · exact context_11_23391_744492

theorem unmarked_context_9_1461_744494 : frontier 12 ⟨744494, by decide⟩
    (prefixCache 9 1461) (prefixPartial 9 1461) = false := by
  decide +kernel

theorem node_context_9_1461_744494 : EJMOriginalGlobalDAGData.nodes 12 ⟨744494, by decide⟩ =
    .split (coordinate 9) (![⟨743016, by decide⟩,⟨743538, by decide⟩,⟨744052, by decide⟩,⟨744493, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1461_744494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1461 ⟨744494, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1461
    ⟨744494, by decide⟩ (by decide) (![⟨743016, by decide⟩,⟨743538, by decide⟩,⟨744052, by decide⟩,⟨744493, by decide⟩]) unmarked_context_9_1461_744494 node_context_9_1461_744494
  intro a
  fin_cases a
  · exact context_10_5844_743016
  · exact context_10_5845_743538
  · exact context_10_5846_744052
  · exact context_10_5847_744493

theorem selected_cut_29497 : selected 9 ⟨744524, by decide⟩
    (prefixPartial 12 93568) = some ⟨12, 2, 0, 744524, 93568, 2657, 65536⟩ := by
  decide +kernel

theorem context_12_93568_744524 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93568 ⟨744524, by decide⟩ :=
  accepted_of_selected 12 93568 ⟨744524, by decide⟩ ⟨12, 2, 0, 744524, 93568, 2657, 65536⟩
    (by decide) selected_cut_29497

theorem selected_cut_29498 : selected 9 ⟨744550, by decide⟩
    (prefixPartial 12 93569) = some ⟨12, 2, 0, 744550, 93569, 2353, 65536⟩ := by
  decide +kernel

theorem context_12_93569_744550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93569 ⟨744550, by decide⟩ :=
  accepted_of_selected 12 93569 ⟨744550, by decide⟩ ⟨12, 2, 0, 744550, 93569, 2353, 65536⟩
    (by decide) selected_cut_29498

theorem selected_cut_29499 : selected 9 ⟨744582, by decide⟩
    (prefixPartial 12 93570) = some ⟨12, 2, 0, 744582, 93570, 2833, 65536⟩ := by
  decide +kernel

theorem context_12_93570_744582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93570 ⟨744582, by decide⟩ :=
  accepted_of_selected 12 93570 ⟨744582, by decide⟩ ⟨12, 2, 0, 744582, 93570, 2833, 65536⟩
    (by decide) selected_cut_29499

theorem selected_cut_29500 : selected 9 ⟨744616, by decide⟩
    (prefixPartial 12 93571) = some ⟨12, 2, 0, 744616, 93571, 2985, 65536⟩ := by
  decide +kernel

theorem context_12_93571_744616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93571 ⟨744616, by decide⟩ :=
  accepted_of_selected 12 93571 ⟨744616, by decide⟩ ⟨12, 2, 0, 744616, 93571, 2985, 65536⟩
    (by decide) selected_cut_29500

theorem unmarked_context_11_23392_744617 : frontier 10 ⟨744617, by decide⟩
    (prefixCache 11 23392) (prefixPartial 11 23392) = false := by
  decide +kernel

theorem node_context_11_23392_744617 : EJMOriginalGlobalDAGData.nodes 10 ⟨744617, by decide⟩ =
    .split (coordinate 11) (![⟨744524, by decide⟩,⟨744550, by decide⟩,⟨744582, by decide⟩,⟨744616, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23392_744617 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23392 ⟨744617, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23392
    ⟨744617, by decide⟩ (by decide) (![⟨744524, by decide⟩,⟨744550, by decide⟩,⟨744582, by decide⟩,⟨744616, by decide⟩]) unmarked_context_11_23392_744617 node_context_11_23392_744617
  intro a
  fin_cases a
  · exact context_12_93568_744524
  · exact context_12_93569_744550
  · exact context_12_93570_744582
  · exact context_12_93571_744616

theorem selected_cut_29501 : selected 9 ⟨744646, by decide⟩
    (prefixPartial 12 93572) = some ⟨12, 2, 0, 744646, 93572, 2181, 65536⟩ := by
  decide +kernel

theorem context_12_93572_744646 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93572 ⟨744646, by decide⟩ :=
  accepted_of_selected 12 93572 ⟨744646, by decide⟩ ⟨12, 2, 0, 744646, 93572, 2181, 65536⟩
    (by decide) selected_cut_29501

theorem selected_cut_29502 : selected 9 ⟨721771, by decide⟩
    (prefixPartial 12 93573) = some ⟨12, 1, 0, 721771, 93573, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93573_721771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93573 ⟨721771, by decide⟩ :=
  accepted_of_selected 12 93573 ⟨721771, by decide⟩ ⟨12, 1, 0, 721771, 93573, 1, 65536⟩
    (by decide) selected_cut_29502

theorem selected_cut_29503 : selected 9 ⟨744677, by decide⟩
    (prefixPartial 12 93574) = some ⟨12, 2, 0, 744677, 93574, 2229, 65536⟩ := by
  decide +kernel

theorem context_12_93574_744677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93574 ⟨744677, by decide⟩ :=
  accepted_of_selected 12 93574 ⟨744677, by decide⟩ ⟨12, 2, 0, 744677, 93574, 2229, 65536⟩
    (by decide) selected_cut_29503

theorem selected_cut_29504 : selected 9 ⟨744711, by decide⟩
    (prefixPartial 12 93575) = some ⟨12, 2, 0, 744711, 93575, 2473, 65536⟩ := by
  decide +kernel

theorem context_12_93575_744711 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93575 ⟨744711, by decide⟩ :=
  accepted_of_selected 12 93575 ⟨744711, by decide⟩ ⟨12, 2, 0, 744711, 93575, 2473, 65536⟩
    (by decide) selected_cut_29504

theorem unmarked_context_11_23393_744712 : frontier 10 ⟨744712, by decide⟩
    (prefixCache 11 23393) (prefixPartial 11 23393) = false := by
  decide +kernel

theorem node_context_11_23393_744712 : EJMOriginalGlobalDAGData.nodes 10 ⟨744712, by decide⟩ =
    .split (coordinate 11) (![⟨744646, by decide⟩,⟨721771, by decide⟩,⟨744677, by decide⟩,⟨744711, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23393_744712 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23393 ⟨744712, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23393
    ⟨744712, by decide⟩ (by decide) (![⟨744646, by decide⟩,⟨721771, by decide⟩,⟨744677, by decide⟩,⟨744711, by decide⟩]) unmarked_context_11_23393_744712 node_context_11_23393_744712
  intro a
  fin_cases a
  · exact context_12_93572_744646
  · exact context_12_93573_721771
  · exact context_12_93574_744677
  · exact context_12_93575_744711

theorem selected_cut_29505 : selected 9 ⟨744747, by decide⟩
    (prefixPartial 12 93576) = some ⟨12, 2, 0, 744747, 93576, 2669, 65536⟩ := by
  decide +kernel

theorem context_12_93576_744747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93576 ⟨744747, by decide⟩ :=
  accepted_of_selected 12 93576 ⟨744747, by decide⟩ ⟨12, 2, 0, 744747, 93576, 2669, 65536⟩
    (by decide) selected_cut_29505

theorem selected_cut_29506 : selected 9 ⟨744783, by decide⟩
    (prefixPartial 12 93577) = some ⟨12, 2, 0, 744783, 93577, 2429, 65536⟩ := by
  decide +kernel

theorem context_12_93577_744783 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93577 ⟨744783, by decide⟩ :=
  accepted_of_selected 12 93577 ⟨744783, by decide⟩ ⟨12, 2, 0, 744783, 93577, 2429, 65536⟩
    (by decide) selected_cut_29506

theorem selected_cut_29507 : selected 9 ⟨744818, by decide⟩
    (prefixPartial 12 93578) = some ⟨12, 2, 0, 744818, 93578, 2493, 65536⟩ := by
  decide +kernel

theorem context_12_93578_744818 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93578 ⟨744818, by decide⟩ :=
  accepted_of_selected 12 93578 ⟨744818, by decide⟩ ⟨12, 2, 0, 744818, 93578, 2493, 65536⟩
    (by decide) selected_cut_29507

theorem selected_cut_29508 : selected 9 ⟨744861, by decide⟩
    (prefixPartial 12 93579) = some ⟨12, 2, 0, 744861, 93579, 2657, 65536⟩ := by
  decide +kernel

theorem context_12_93579_744861 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93579 ⟨744861, by decide⟩ :=
  accepted_of_selected 12 93579 ⟨744861, by decide⟩ ⟨12, 2, 0, 744861, 93579, 2657, 65536⟩
    (by decide) selected_cut_29508

theorem unmarked_context_11_23394_744862 : frontier 10 ⟨744862, by decide⟩
    (prefixCache 11 23394) (prefixPartial 11 23394) = false := by
  decide +kernel

theorem node_context_11_23394_744862 : EJMOriginalGlobalDAGData.nodes 10 ⟨744862, by decide⟩ =
    .split (coordinate 11) (![⟨744747, by decide⟩,⟨744783, by decide⟩,⟨744818, by decide⟩,⟨744861, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23394_744862 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23394 ⟨744862, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23394
    ⟨744862, by decide⟩ (by decide) (![⟨744747, by decide⟩,⟨744783, by decide⟩,⟨744818, by decide⟩,⟨744861, by decide⟩]) unmarked_context_11_23394_744862 node_context_11_23394_744862
  intro a
  fin_cases a
  · exact context_12_93576_744747
  · exact context_12_93577_744783
  · exact context_12_93578_744818
  · exact context_12_93579_744861

theorem selected_cut_29509 : selected 9 ⟨744891, by decide⟩
    (prefixPartial 12 93580) = some ⟨12, 2, 0, 744891, 93580, 2157, 65536⟩ := by
  decide +kernel

theorem context_12_93580_744891 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93580 ⟨744891, by decide⟩ :=
  accepted_of_selected 12 93580 ⟨744891, by decide⟩ ⟨12, 2, 0, 744891, 93580, 2157, 65536⟩
    (by decide) selected_cut_29509

theorem selected_cut_29510 : selected 9 ⟨744919, by decide⟩
    (prefixPartial 12 93581) = some ⟨12, 2, 0, 744919, 93581, 1829, 65536⟩ := by
  decide +kernel

theorem context_12_93581_744919 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93581 ⟨744919, by decide⟩ :=
  accepted_of_selected 12 93581 ⟨744919, by decide⟩ ⟨12, 2, 0, 744919, 93581, 1829, 65536⟩
    (by decide) selected_cut_29510

theorem selected_cut_29511 : selected 9 ⟨744945, by decide⟩
    (prefixPartial 12 93582) = some ⟨12, 2, 0, 744945, 93582, 2137, 65536⟩ := by
  decide +kernel

theorem context_12_93582_744945 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93582 ⟨744945, by decide⟩ :=
  accepted_of_selected 12 93582 ⟨744945, by decide⟩ ⟨12, 2, 0, 744945, 93582, 2137, 65536⟩
    (by decide) selected_cut_29511

theorem selected_cut_29512 : selected 9 ⟨744975, by decide⟩
    (prefixPartial 12 93583) = some ⟨12, 2, 0, 744975, 93583, 2301, 65536⟩ := by
  decide +kernel

theorem context_12_93583_744975 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93583 ⟨744975, by decide⟩ :=
  accepted_of_selected 12 93583 ⟨744975, by decide⟩ ⟨12, 2, 0, 744975, 93583, 2301, 65536⟩
    (by decide) selected_cut_29512

theorem unmarked_context_11_23395_744976 : frontier 10 ⟨744976, by decide⟩
    (prefixCache 11 23395) (prefixPartial 11 23395) = false := by
  decide +kernel

theorem node_context_11_23395_744976 : EJMOriginalGlobalDAGData.nodes 10 ⟨744976, by decide⟩ =
    .split (coordinate 11) (![⟨744891, by decide⟩,⟨744919, by decide⟩,⟨744945, by decide⟩,⟨744975, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23395_744976 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23395 ⟨744976, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23395
    ⟨744976, by decide⟩ (by decide) (![⟨744891, by decide⟩,⟨744919, by decide⟩,⟨744945, by decide⟩,⟨744975, by decide⟩]) unmarked_context_11_23395_744976 node_context_11_23395_744976
  intro a
  fin_cases a
  · exact context_12_93580_744891
  · exact context_12_93581_744919
  · exact context_12_93582_744945
  · exact context_12_93583_744975

theorem unmarked_context_10_5848_744977 : frontier 11 ⟨744977, by decide⟩
    (prefixCache 10 5848) (prefixPartial 10 5848) = false := by
  decide +kernel

theorem node_context_10_5848_744977 : EJMOriginalGlobalDAGData.nodes 11 ⟨744977, by decide⟩ =
    .split (coordinate 10) (![⟨744617, by decide⟩,⟨744712, by decide⟩,⟨744862, by decide⟩,⟨744976, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5848_744977 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5848 ⟨744977, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5848
    ⟨744977, by decide⟩ (by decide) (![⟨744617, by decide⟩,⟨744712, by decide⟩,⟨744862, by decide⟩,⟨744976, by decide⟩]) unmarked_context_10_5848_744977 node_context_10_5848_744977
  intro a
  fin_cases a
  · exact context_11_23392_744617
  · exact context_11_23393_744712
  · exact context_11_23394_744862
  · exact context_11_23395_744976

theorem selected_cut_29513 : selected 9 ⟨745000, by decide⟩
    (prefixPartial 12 93584) = some ⟨12, 2, 0, 745000, 93584, 2057, 65536⟩ := by
  decide +kernel

theorem context_12_93584_745000 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93584 ⟨745000, by decide⟩ :=
  accepted_of_selected 12 93584 ⟨745000, by decide⟩ ⟨12, 2, 0, 745000, 93584, 2057, 65536⟩
    (by decide) selected_cut_29513

theorem selected_cut_29514 : selected 9 ⟨745024, by decide⟩
    (prefixPartial 12 93585) = some ⟨12, 2, 0, 745024, 93585, 2149, 65536⟩ := by
  decide +kernel

theorem context_12_93585_745024 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93585 ⟨745024, by decide⟩ :=
  accepted_of_selected 12 93585 ⟨745024, by decide⟩ ⟨12, 2, 0, 745024, 93585, 2149, 65536⟩
    (by decide) selected_cut_29514

theorem selected_cut_29515 : selected 9 ⟨745054, by decide⟩
    (prefixPartial 12 93586) = some ⟨12, 2, 0, 745054, 93586, 2325, 65536⟩ := by
  decide +kernel

theorem context_12_93586_745054 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93586 ⟨745054, by decide⟩ :=
  accepted_of_selected 12 93586 ⟨745054, by decide⟩ ⟨12, 2, 0, 745054, 93586, 2325, 65536⟩
    (by decide) selected_cut_29515

theorem selected_cut_29516 : selected 9 ⟨745085, by decide⟩
    (prefixPartial 12 93587) = some ⟨12, 2, 0, 745085, 93587, 2453, 65536⟩ := by
  decide +kernel

theorem context_12_93587_745085 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93587 ⟨745085, by decide⟩ :=
  accepted_of_selected 12 93587 ⟨745085, by decide⟩ ⟨12, 2, 0, 745085, 93587, 2453, 65536⟩
    (by decide) selected_cut_29516

theorem unmarked_context_11_23396_745086 : frontier 10 ⟨745086, by decide⟩
    (prefixCache 11 23396) (prefixPartial 11 23396) = false := by
  decide +kernel

theorem node_context_11_23396_745086 : EJMOriginalGlobalDAGData.nodes 10 ⟨745086, by decide⟩ =
    .split (coordinate 11) (![⟨745000, by decide⟩,⟨745024, by decide⟩,⟨745054, by decide⟩,⟨745085, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23396_745086 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23396 ⟨745086, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23396
    ⟨745086, by decide⟩ (by decide) (![⟨745000, by decide⟩,⟨745024, by decide⟩,⟨745054, by decide⟩,⟨745085, by decide⟩]) unmarked_context_11_23396_745086 node_context_11_23396_745086
  intro a
  fin_cases a
  · exact context_12_93584_745000
  · exact context_12_93585_745024
  · exact context_12_93586_745054
  · exact context_12_93587_745085

theorem selected_cut_29517 : selected 9 ⟨745108, by decide⟩
    (prefixPartial 12 93588) = some ⟨12, 2, 0, 745108, 93588, 1733, 65536⟩ := by
  decide +kernel

theorem context_12_93588_745108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93588 ⟨745108, by decide⟩ :=
  accepted_of_selected 12 93588 ⟨745108, by decide⟩ ⟨12, 2, 0, 745108, 93588, 1733, 65536⟩
    (by decide) selected_cut_29517

theorem selected_cut_29518 : selected 9 ⟨439069, by decide⟩
    (prefixPartial 12 93589) = some ⟨12, 1, 0, 439069, 93589, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93589_439069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93589 ⟨439069, by decide⟩ :=
  accepted_of_selected 12 93589 ⟨439069, by decide⟩ ⟨12, 1, 0, 439069, 93589, 1, 65536⟩
    (by decide) selected_cut_29518

theorem selected_cut_29519 : selected 9 ⟨745130, by decide⟩
    (prefixPartial 12 93590) = some ⟨12, 2, 0, 745130, 93590, 1837, 65536⟩ := by
  decide +kernel

theorem context_12_93590_745130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93590 ⟨745130, by decide⟩ :=
  accepted_of_selected 12 93590 ⟨745130, by decide⟩ ⟨12, 2, 0, 745130, 93590, 1837, 65536⟩
    (by decide) selected_cut_29519

theorem selected_cut_29520 : selected 9 ⟨745151, by decide⟩
    (prefixPartial 12 93591) = some ⟨12, 2, 0, 745151, 93591, 1997, 65536⟩ := by
  decide +kernel

theorem context_12_93591_745151 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93591 ⟨745151, by decide⟩ :=
  accepted_of_selected 12 93591 ⟨745151, by decide⟩ ⟨12, 2, 0, 745151, 93591, 1997, 65536⟩
    (by decide) selected_cut_29520

theorem unmarked_context_11_23397_745152 : frontier 10 ⟨745152, by decide⟩
    (prefixCache 11 23397) (prefixPartial 11 23397) = false := by
  decide +kernel

theorem node_context_11_23397_745152 : EJMOriginalGlobalDAGData.nodes 10 ⟨745152, by decide⟩ =
    .split (coordinate 11) (![⟨745108, by decide⟩,⟨439069, by decide⟩,⟨745130, by decide⟩,⟨745151, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23397_745152 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23397 ⟨745152, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23397
    ⟨745152, by decide⟩ (by decide) (![⟨745108, by decide⟩,⟨439069, by decide⟩,⟨745130, by decide⟩,⟨745151, by decide⟩]) unmarked_context_11_23397_745152 node_context_11_23397_745152
  intro a
  fin_cases a
  · exact context_12_93588_745108
  · exact context_12_93589_439069
  · exact context_12_93590_745130
  · exact context_12_93591_745151

theorem selected_cut_29521 : selected 9 ⟨745176, by decide⟩
    (prefixPartial 12 93592) = some ⟨12, 2, 0, 745176, 93592, 1893, 65536⟩ := by
  decide +kernel

theorem context_12_93592_745176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93592 ⟨745176, by decide⟩ :=
  accepted_of_selected 12 93592 ⟨745176, by decide⟩ ⟨12, 2, 0, 745176, 93592, 1893, 65536⟩
    (by decide) selected_cut_29521

theorem selected_cut_29522 : selected 9 ⟨745199, by decide⟩
    (prefixPartial 12 93593) = some ⟨12, 2, 0, 745199, 93593, 1893, 65536⟩ := by
  decide +kernel

theorem context_12_93593_745199 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93593 ⟨745199, by decide⟩ :=
  accepted_of_selected 12 93593 ⟨745199, by decide⟩ ⟨12, 2, 0, 745199, 93593, 1893, 65536⟩
    (by decide) selected_cut_29522

theorem selected_cut_29523 : selected 9 ⟨745226, by decide⟩
    (prefixPartial 12 93594) = some ⟨12, 2, 0, 745226, 93594, 1841, 65536⟩ := by
  decide +kernel

theorem context_12_93594_745226 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93594 ⟨745226, by decide⟩ :=
  accepted_of_selected 12 93594 ⟨745226, by decide⟩ ⟨12, 2, 0, 745226, 93594, 1841, 65536⟩
    (by decide) selected_cut_29523

theorem selected_cut_29524 : selected 9 ⟨745253, by decide⟩
    (prefixPartial 12 93595) = some ⟨12, 2, 0, 745253, 93595, 1961, 65536⟩ := by
  decide +kernel

theorem context_12_93595_745253 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93595 ⟨745253, by decide⟩ :=
  accepted_of_selected 12 93595 ⟨745253, by decide⟩ ⟨12, 2, 0, 745253, 93595, 1961, 65536⟩
    (by decide) selected_cut_29524

theorem unmarked_context_11_23398_745254 : frontier 10 ⟨745254, by decide⟩
    (prefixCache 11 23398) (prefixPartial 11 23398) = false := by
  decide +kernel

theorem node_context_11_23398_745254 : EJMOriginalGlobalDAGData.nodes 10 ⟨745254, by decide⟩ =
    .split (coordinate 11) (![⟨745176, by decide⟩,⟨745199, by decide⟩,⟨745226, by decide⟩,⟨745253, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23398_745254 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23398 ⟨745254, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23398
    ⟨745254, by decide⟩ (by decide) (![⟨745176, by decide⟩,⟨745199, by decide⟩,⟨745226, by decide⟩,⟨745253, by decide⟩]) unmarked_context_11_23398_745254 node_context_11_23398_745254
  intro a
  fin_cases a
  · exact context_12_93592_745176
  · exact context_12_93593_745199
  · exact context_12_93594_745226
  · exact context_12_93595_745253

theorem selected_cut_29525 : selected 9 ⟨745274, by decide⟩
    (prefixPartial 12 93596) = some ⟨12, 2, 0, 745274, 93596, 1593, 65536⟩ := by
  decide +kernel

theorem context_12_93596_745274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93596 ⟨745274, by decide⟩ :=
  accepted_of_selected 12 93596 ⟨745274, by decide⟩ ⟨12, 2, 0, 745274, 93596, 1593, 65536⟩
    (by decide) selected_cut_29525

theorem selected_cut_29526 : selected 9 ⟨745291, by decide⟩
    (prefixPartial 12 93597) = some ⟨12, 2, 0, 745291, 93597, 1525, 65536⟩ := by
  decide +kernel

theorem context_12_93597_745291 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93597 ⟨745291, by decide⟩ :=
  accepted_of_selected 12 93597 ⟨745291, by decide⟩ ⟨12, 2, 0, 745291, 93597, 1525, 65536⟩
    (by decide) selected_cut_29526

theorem selected_cut_29527 : selected 9 ⟨745313, by decide⟩
    (prefixPartial 12 93598) = some ⟨12, 2, 0, 745313, 93598, 1725, 65536⟩ := by
  decide +kernel

theorem context_12_93598_745313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93598 ⟨745313, by decide⟩ :=
  accepted_of_selected 12 93598 ⟨745313, by decide⟩ ⟨12, 2, 0, 745313, 93598, 1725, 65536⟩
    (by decide) selected_cut_29527

theorem selected_cut_29528 : selected 9 ⟨745335, by decide⟩
    (prefixPartial 12 93599) = some ⟨12, 2, 0, 745335, 93599, 1757, 65536⟩ := by
  decide +kernel

theorem context_12_93599_745335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93599 ⟨745335, by decide⟩ :=
  accepted_of_selected 12 93599 ⟨745335, by decide⟩ ⟨12, 2, 0, 745335, 93599, 1757, 65536⟩
    (by decide) selected_cut_29528

theorem unmarked_context_11_23399_745336 : frontier 10 ⟨745336, by decide⟩
    (prefixCache 11 23399) (prefixPartial 11 23399) = false := by
  decide +kernel

theorem node_context_11_23399_745336 : EJMOriginalGlobalDAGData.nodes 10 ⟨745336, by decide⟩ =
    .split (coordinate 11) (![⟨745274, by decide⟩,⟨745291, by decide⟩,⟨745313, by decide⟩,⟨745335, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23399_745336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23399 ⟨745336, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23399
    ⟨745336, by decide⟩ (by decide) (![⟨745274, by decide⟩,⟨745291, by decide⟩,⟨745313, by decide⟩,⟨745335, by decide⟩]) unmarked_context_11_23399_745336 node_context_11_23399_745336
  intro a
  fin_cases a
  · exact context_12_93596_745274
  · exact context_12_93597_745291
  · exact context_12_93598_745313
  · exact context_12_93599_745335

theorem unmarked_context_10_5849_745337 : frontier 11 ⟨745337, by decide⟩
    (prefixCache 10 5849) (prefixPartial 10 5849) = false := by
  decide +kernel

theorem node_context_10_5849_745337 : EJMOriginalGlobalDAGData.nodes 11 ⟨745337, by decide⟩ =
    .split (coordinate 10) (![⟨745086, by decide⟩,⟨745152, by decide⟩,⟨745254, by decide⟩,⟨745336, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5849_745337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5849 ⟨745337, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5849
    ⟨745337, by decide⟩ (by decide) (![⟨745086, by decide⟩,⟨745152, by decide⟩,⟨745254, by decide⟩,⟨745336, by decide⟩]) unmarked_context_10_5849_745337 node_context_10_5849_745337
  intro a
  fin_cases a
  · exact context_11_23396_745086
  · exact context_11_23397_745152
  · exact context_11_23398_745254
  · exact context_11_23399_745336

theorem selected_cut_29529 : selected 9 ⟨745355, by decide⟩
    (prefixPartial 12 93600) = some ⟨12, 2, 0, 745355, 93600, 1741, 65536⟩ := by
  decide +kernel

theorem context_12_93600_745355 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93600 ⟨745355, by decide⟩ :=
  accepted_of_selected 12 93600 ⟨745355, by decide⟩ ⟨12, 2, 0, 745355, 93600, 1741, 65536⟩
    (by decide) selected_cut_29529

theorem selected_cut_29530 : selected 9 ⟨745377, by decide⟩
    (prefixPartial 12 93601) = some ⟨12, 2, 0, 745377, 93601, 1549, 65536⟩ := by
  decide +kernel

theorem context_12_93601_745377 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93601 ⟨745377, by decide⟩ :=
  accepted_of_selected 12 93601 ⟨745377, by decide⟩ ⟨12, 2, 0, 745377, 93601, 1549, 65536⟩
    (by decide) selected_cut_29530

theorem selected_cut_29531 : selected 9 ⟨745400, by decide⟩
    (prefixPartial 12 93602) = some ⟨12, 2, 0, 745400, 93602, 1773, 65536⟩ := by
  decide +kernel

theorem context_12_93602_745400 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93602 ⟨745400, by decide⟩ :=
  accepted_of_selected 12 93602 ⟨745400, by decide⟩ ⟨12, 2, 0, 745400, 93602, 1773, 65536⟩
    (by decide) selected_cut_29531

theorem selected_cut_29532 : selected 9 ⟨745429, by decide⟩
    (prefixPartial 12 93603) = some ⟨12, 2, 0, 745429, 93603, 1897, 65536⟩ := by
  decide +kernel

theorem context_12_93603_745429 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93603 ⟨745429, by decide⟩ :=
  accepted_of_selected 12 93603 ⟨745429, by decide⟩ ⟨12, 2, 0, 745429, 93603, 1897, 65536⟩
    (by decide) selected_cut_29532

theorem unmarked_context_11_23400_745430 : frontier 10 ⟨745430, by decide⟩
    (prefixCache 11 23400) (prefixPartial 11 23400) = false := by
  decide +kernel

theorem node_context_11_23400_745430 : EJMOriginalGlobalDAGData.nodes 10 ⟨745430, by decide⟩ =
    .split (coordinate 11) (![⟨745355, by decide⟩,⟨745377, by decide⟩,⟨745400, by decide⟩,⟨745429, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23400_745430 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23400 ⟨745430, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23400
    ⟨745430, by decide⟩ (by decide) (![⟨745355, by decide⟩,⟨745377, by decide⟩,⟨745400, by decide⟩,⟨745429, by decide⟩]) unmarked_context_11_23400_745430 node_context_11_23400_745430
  intro a
  fin_cases a
  · exact context_12_93600_745355
  · exact context_12_93601_745377
  · exact context_12_93602_745400
  · exact context_12_93603_745429

theorem selected_cut_29533 : selected 9 ⟨745447, by decide⟩
    (prefixPartial 12 93604) = some ⟨12, 2, 0, 745447, 93604, 1437, 65536⟩ := by
  decide +kernel

theorem context_12_93604_745447 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93604 ⟨745447, by decide⟩ :=
  accepted_of_selected 12 93604 ⟨745447, by decide⟩ ⟨12, 2, 0, 745447, 93604, 1437, 65536⟩
    (by decide) selected_cut_29533

theorem selected_cut_29534 : selected 9 ⟨721771, by decide⟩
    (prefixPartial 12 93605) = some ⟨12, 1, 0, 721771, 93605, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93605_721771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93605 ⟨721771, by decide⟩ :=
  accepted_of_selected 12 93605 ⟨721771, by decide⟩ ⟨12, 1, 0, 721771, 93605, 1, 65536⟩
    (by decide) selected_cut_29534

theorem selected_cut_29535 : selected 9 ⟨745462, by decide⟩
    (prefixPartial 12 93606) = some ⟨12, 2, 0, 745462, 93606, 1385, 65536⟩ := by
  decide +kernel

theorem context_12_93606_745462 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93606 ⟨745462, by decide⟩ :=
  accepted_of_selected 12 93606 ⟨745462, by decide⟩ ⟨12, 2, 0, 745462, 93606, 1385, 65536⟩
    (by decide) selected_cut_29535

theorem selected_cut_29536 : selected 9 ⟨745486, by decide⟩
    (prefixPartial 12 93607) = some ⟨12, 2, 0, 745486, 93607, 1549, 65536⟩ := by
  decide +kernel

theorem context_12_93607_745486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93607 ⟨745486, by decide⟩ :=
  accepted_of_selected 12 93607 ⟨745486, by decide⟩ ⟨12, 2, 0, 745486, 93607, 1549, 65536⟩
    (by decide) selected_cut_29536

theorem unmarked_context_11_23401_745487 : frontier 10 ⟨745487, by decide⟩
    (prefixCache 11 23401) (prefixPartial 11 23401) = false := by
  decide +kernel

theorem node_context_11_23401_745487 : EJMOriginalGlobalDAGData.nodes 10 ⟨745487, by decide⟩ =
    .split (coordinate 11) (![⟨745447, by decide⟩,⟨721771, by decide⟩,⟨745462, by decide⟩,⟨745486, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23401_745487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23401 ⟨745487, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23401
    ⟨745487, by decide⟩ (by decide) (![⟨745447, by decide⟩,⟨721771, by decide⟩,⟨745462, by decide⟩,⟨745486, by decide⟩]) unmarked_context_11_23401_745487 node_context_11_23401_745487
  intro a
  fin_cases a
  · exact context_12_93604_745447
  · exact context_12_93605_721771
  · exact context_12_93606_745462
  · exact context_12_93607_745486

theorem selected_cut_29537 : selected 9 ⟨745507, by decide⟩
    (prefixPartial 12 93608) = some ⟨12, 2, 0, 745507, 93608, 1541, 65536⟩ := by
  decide +kernel

theorem context_12_93608_745507 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93608 ⟨745507, by decide⟩ :=
  accepted_of_selected 12 93608 ⟨745507, by decide⟩ ⟨12, 2, 0, 745507, 93608, 1541, 65536⟩
    (by decide) selected_cut_29537

theorem selected_cut_29538 : selected 9 ⟨745525, by decide⟩
    (prefixPartial 12 93609) = some ⟨12, 2, 0, 745525, 93609, 1437, 65536⟩ := by
  decide +kernel

theorem context_12_93609_745525 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93609 ⟨745525, by decide⟩ :=
  accepted_of_selected 12 93609 ⟨745525, by decide⟩ ⟨12, 2, 0, 745525, 93609, 1437, 65536⟩
    (by decide) selected_cut_29538

theorem selected_cut_29539 : selected 9 ⟨745541, by decide⟩
    (prefixPartial 12 93610) = some ⟨12, 2, 0, 745541, 93610, 1361, 65536⟩ := by
  decide +kernel

theorem context_12_93610_745541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93610 ⟨745541, by decide⟩ :=
  accepted_of_selected 12 93610 ⟨745541, by decide⟩ ⟨12, 2, 0, 745541, 93610, 1361, 65536⟩
    (by decide) selected_cut_29539

theorem selected_cut_29540 : selected 9 ⟨745559, by decide⟩
    (prefixPartial 12 93611) = some ⟨12, 2, 0, 745559, 93611, 1441, 65536⟩ := by
  decide +kernel

theorem context_12_93611_745559 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93611 ⟨745559, by decide⟩ :=
  accepted_of_selected 12 93611 ⟨745559, by decide⟩ ⟨12, 2, 0, 745559, 93611, 1441, 65536⟩
    (by decide) selected_cut_29540

theorem unmarked_context_11_23402_745560 : frontier 10 ⟨745560, by decide⟩
    (prefixCache 11 23402) (prefixPartial 11 23402) = false := by
  decide +kernel

theorem node_context_11_23402_745560 : EJMOriginalGlobalDAGData.nodes 10 ⟨745560, by decide⟩ =
    .split (coordinate 11) (![⟨745507, by decide⟩,⟨745525, by decide⟩,⟨745541, by decide⟩,⟨745559, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23402_745560 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23402 ⟨745560, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23402
    ⟨745560, by decide⟩ (by decide) (![⟨745507, by decide⟩,⟨745525, by decide⟩,⟨745541, by decide⟩,⟨745559, by decide⟩]) unmarked_context_11_23402_745560 node_context_11_23402_745560
  intro a
  fin_cases a
  · exact context_12_93608_745507
  · exact context_12_93609_745525
  · exact context_12_93610_745541
  · exact context_12_93611_745559

theorem selected_cut_29541 : selected 9 ⟨745577, by decide⟩
    (prefixPartial 12 93612) = some ⟨12, 2, 0, 745577, 93612, 1365, 65536⟩ := by
  decide +kernel

theorem context_12_93612_745577 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93612 ⟨745577, by decide⟩ :=
  accepted_of_selected 12 93612 ⟨745577, by decide⟩ ⟨12, 2, 0, 745577, 93612, 1365, 65536⟩
    (by decide) selected_cut_29541

theorem selected_cut_29542 : selected 9 ⟨745591, by decide⟩
    (prefixPartial 12 93613) = some ⟨12, 2, 0, 745591, 93613, 1081, 65536⟩ := by
  decide +kernel

theorem context_12_93613_745591 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93613 ⟨745591, by decide⟩ :=
  accepted_of_selected 12 93613 ⟨745591, by decide⟩ ⟨12, 2, 0, 745591, 93613, 1081, 65536⟩
    (by decide) selected_cut_29542

theorem selected_cut_29543 : selected 9 ⟨745607, by decide⟩
    (prefixPartial 12 93614) = some ⟨12, 2, 0, 745607, 93614, 1285, 65536⟩ := by
  decide +kernel

theorem context_12_93614_745607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93614 ⟨745607, by decide⟩ :=
  accepted_of_selected 12 93614 ⟨745607, by decide⟩ ⟨12, 2, 0, 745607, 93614, 1285, 65536⟩
    (by decide) selected_cut_29543

theorem selected_cut_29544 : selected 9 ⟨745620, by decide⟩
    (prefixPartial 12 93615) = some ⟨12, 2, 0, 745620, 93615, 1357, 65536⟩ := by
  decide +kernel

theorem context_12_93615_745620 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93615 ⟨745620, by decide⟩ :=
  accepted_of_selected 12 93615 ⟨745620, by decide⟩ ⟨12, 2, 0, 745620, 93615, 1357, 65536⟩
    (by decide) selected_cut_29544

theorem unmarked_context_11_23403_745621 : frontier 10 ⟨745621, by decide⟩
    (prefixCache 11 23403) (prefixPartial 11 23403) = false := by
  decide +kernel

theorem node_context_11_23403_745621 : EJMOriginalGlobalDAGData.nodes 10 ⟨745621, by decide⟩ =
    .split (coordinate 11) (![⟨745577, by decide⟩,⟨745591, by decide⟩,⟨745607, by decide⟩,⟨745620, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23403_745621 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23403 ⟨745621, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23403
    ⟨745621, by decide⟩ (by decide) (![⟨745577, by decide⟩,⟨745591, by decide⟩,⟨745607, by decide⟩,⟨745620, by decide⟩]) unmarked_context_11_23403_745621 node_context_11_23403_745621
  intro a
  fin_cases a
  · exact context_12_93612_745577
  · exact context_12_93613_745591
  · exact context_12_93614_745607
  · exact context_12_93615_745620

theorem unmarked_context_10_5850_745622 : frontier 11 ⟨745622, by decide⟩
    (prefixCache 10 5850) (prefixPartial 10 5850) = false := by
  decide +kernel

theorem node_context_10_5850_745622 : EJMOriginalGlobalDAGData.nodes 11 ⟨745622, by decide⟩ =
    .split (coordinate 10) (![⟨745430, by decide⟩,⟨745487, by decide⟩,⟨745560, by decide⟩,⟨745621, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5850_745622 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5850 ⟨745622, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5850
    ⟨745622, by decide⟩ (by decide) (![⟨745430, by decide⟩,⟨745487, by decide⟩,⟨745560, by decide⟩,⟨745621, by decide⟩]) unmarked_context_10_5850_745622 node_context_10_5850_745622
  intro a
  fin_cases a
  · exact context_11_23400_745430
  · exact context_11_23401_745487
  · exact context_11_23402_745560
  · exact context_11_23403_745621

theorem selected_cut_29545 : selected 9 ⟨745637, by decide⟩
    (prefixPartial 12 93616) = some ⟨12, 2, 0, 745637, 93616, 1297, 65536⟩ := by
  decide +kernel

theorem context_12_93616_745637 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93616 ⟨745637, by decide⟩ :=
  accepted_of_selected 12 93616 ⟨745637, by decide⟩ ⟨12, 2, 0, 745637, 93616, 1297, 65536⟩
    (by decide) selected_cut_29545

theorem selected_cut_29546 : selected 9 ⟨745654, by decide⟩
    (prefixPartial 12 93617) = some ⟨12, 2, 0, 745654, 93617, 1221, 65536⟩ := by
  decide +kernel

theorem context_12_93617_745654 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93617 ⟨745654, by decide⟩ :=
  accepted_of_selected 12 93617 ⟨745654, by decide⟩ ⟨12, 2, 0, 745654, 93617, 1221, 65536⟩
    (by decide) selected_cut_29546

theorem selected_cut_29547 : selected 9 ⟨745671, by decide⟩
    (prefixPartial 12 93618) = some ⟨12, 2, 0, 745671, 93618, 1297, 65536⟩ := by
  decide +kernel

theorem context_12_93618_745671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93618 ⟨745671, by decide⟩ :=
  accepted_of_selected 12 93618 ⟨745671, by decide⟩ ⟨12, 2, 0, 745671, 93618, 1297, 65536⟩
    (by decide) selected_cut_29547

theorem selected_cut_29548 : selected 9 ⟨745699, by decide⟩
    (prefixPartial 12 93619) = some ⟨12, 2, 0, 745699, 93619, 1397, 65536⟩ := by
  decide +kernel

theorem context_12_93619_745699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93619 ⟨745699, by decide⟩ :=
  accepted_of_selected 12 93619 ⟨745699, by decide⟩ ⟨12, 2, 0, 745699, 93619, 1397, 65536⟩
    (by decide) selected_cut_29548

theorem unmarked_context_11_23404_745700 : frontier 10 ⟨745700, by decide⟩
    (prefixCache 11 23404) (prefixPartial 11 23404) = false := by
  decide +kernel

theorem node_context_11_23404_745700 : EJMOriginalGlobalDAGData.nodes 10 ⟨745700, by decide⟩ =
    .split (coordinate 11) (![⟨745637, by decide⟩,⟨745654, by decide⟩,⟨745671, by decide⟩,⟨745699, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23404_745700 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23404 ⟨745700, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23404
    ⟨745700, by decide⟩ (by decide) (![⟨745637, by decide⟩,⟨745654, by decide⟩,⟨745671, by decide⟩,⟨745699, by decide⟩]) unmarked_context_11_23404_745700 node_context_11_23404_745700
  intro a
  fin_cases a
  · exact context_12_93616_745637
  · exact context_12_93617_745654
  · exact context_12_93618_745671
  · exact context_12_93619_745699

theorem selected_cut_29549 : selected 10 ⟨745739, by decide⟩
    (prefixPartial 11 23405) = some ⟨11, 2, 0, 745739, 23405, 3025, 262144⟩ := by
  decide +kernel

theorem context_11_23405_745739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23405 ⟨745739, by decide⟩ :=
  accepted_of_selected 11 23405 ⟨745739, by decide⟩ ⟨11, 2, 0, 745739, 23405, 3025, 262144⟩
    (by decide) selected_cut_29549

theorem selected_cut_29550 : selected 10 ⟨745799, by decide⟩
    (prefixPartial 11 23406) = some ⟨11, 2, 0, 745799, 23406, 3989, 262144⟩ := by
  decide +kernel

theorem context_11_23406_745799 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23406 ⟨745799, by decide⟩ :=
  accepted_of_selected 11 23406 ⟨745799, by decide⟩ ⟨11, 2, 0, 745799, 23406, 3989, 262144⟩
    (by decide) selected_cut_29550

theorem selected_cut_29551 : selected 10 ⟨745834, by decide⟩
    (prefixPartial 11 23407) = some ⟨11, 2, 0, 745834, 23407, 2441, 262144⟩ := by
  decide +kernel

theorem context_11_23407_745834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23407 ⟨745834, by decide⟩ :=
  accepted_of_selected 11 23407 ⟨745834, by decide⟩ ⟨11, 2, 0, 745834, 23407, 2441, 262144⟩
    (by decide) selected_cut_29551

theorem unmarked_context_10_5851_745835 : frontier 11 ⟨745835, by decide⟩
    (prefixCache 10 5851) (prefixPartial 10 5851) = false := by
  decide +kernel

theorem node_context_10_5851_745835 : EJMOriginalGlobalDAGData.nodes 11 ⟨745835, by decide⟩ =
    .split (coordinate 10) (![⟨745700, by decide⟩,⟨745739, by decide⟩,⟨745799, by decide⟩,⟨745834, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5851_745835 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5851 ⟨745835, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5851
    ⟨745835, by decide⟩ (by decide) (![⟨745700, by decide⟩,⟨745739, by decide⟩,⟨745799, by decide⟩,⟨745834, by decide⟩]) unmarked_context_10_5851_745835 node_context_10_5851_745835
  intro a
  fin_cases a
  · exact context_11_23404_745700
  · exact context_11_23405_745739
  · exact context_11_23406_745799
  · exact context_11_23407_745834

theorem unmarked_context_9_1462_745836 : frontier 12 ⟨745836, by decide⟩
    (prefixCache 9 1462) (prefixPartial 9 1462) = false := by
  decide +kernel

theorem node_context_9_1462_745836 : EJMOriginalGlobalDAGData.nodes 12 ⟨745836, by decide⟩ =
    .split (coordinate 9) (![⟨744977, by decide⟩,⟨745337, by decide⟩,⟨745622, by decide⟩,⟨745835, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1462_745836 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1462 ⟨745836, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1462
    ⟨745836, by decide⟩ (by decide) (![⟨744977, by decide⟩,⟨745337, by decide⟩,⟨745622, by decide⟩,⟨745835, by decide⟩]) unmarked_context_9_1462_745836 node_context_9_1462_745836
  intro a
  fin_cases a
  · exact context_10_5848_744977
  · exact context_10_5849_745337
  · exact context_10_5850_745622
  · exact context_10_5851_745835

theorem selected_cut_29552 : selected 10 ⟨745874, by decide⟩
    (prefixPartial 11 23408) = some ⟨11, 2, 0, 745874, 23408, 3817, 262144⟩ := by
  decide +kernel

theorem context_11_23408_745874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23408 ⟨745874, by decide⟩ :=
  accepted_of_selected 11 23408 ⟨745874, by decide⟩ ⟨11, 2, 0, 745874, 23408, 3817, 262144⟩
    (by decide) selected_cut_29552

theorem selected_cut_29553 : selected 10 ⟨745895, by decide⟩
    (prefixPartial 11 23409) = some ⟨11, 2, 0, 745895, 23409, 2377, 262144⟩ := by
  decide +kernel

theorem context_11_23409_745895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23409 ⟨745895, by decide⟩ :=
  accepted_of_selected 11 23409 ⟨745895, by decide⟩ ⟨11, 2, 0, 745895, 23409, 2377, 262144⟩
    (by decide) selected_cut_29553

theorem selected_cut_29554 : selected 10 ⟨745919, by decide⟩
    (prefixPartial 11 23410) = some ⟨11, 2, 0, 745919, 23410, 3249, 262144⟩ := by
  decide +kernel

theorem context_11_23410_745919 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23410 ⟨745919, by decide⟩ :=
  accepted_of_selected 11 23410 ⟨745919, by decide⟩ ⟨11, 2, 0, 745919, 23410, 3249, 262144⟩
    (by decide) selected_cut_29554

theorem selected_cut_29555 : selected 10 ⟨745948, by decide⟩
    (prefixPartial 11 23411) = some ⟨11, 2, 0, 745948, 23411, 3081, 262144⟩ := by
  decide +kernel

theorem context_11_23411_745948 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23411 ⟨745948, by decide⟩ :=
  accepted_of_selected 11 23411 ⟨745948, by decide⟩ ⟨11, 2, 0, 745948, 23411, 3081, 262144⟩
    (by decide) selected_cut_29555

theorem unmarked_context_10_5852_745949 : frontier 11 ⟨745949, by decide⟩
    (prefixCache 10 5852) (prefixPartial 10 5852) = false := by
  decide +kernel

theorem node_context_10_5852_745949 : EJMOriginalGlobalDAGData.nodes 11 ⟨745949, by decide⟩ =
    .split (coordinate 10) (![⟨745874, by decide⟩,⟨745895, by decide⟩,⟨745919, by decide⟩,⟨745948, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5852_745949 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5852 ⟨745949, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5852
    ⟨745949, by decide⟩ (by decide) (![⟨745874, by decide⟩,⟨745895, by decide⟩,⟨745919, by decide⟩,⟨745948, by decide⟩]) unmarked_context_10_5852_745949 node_context_10_5852_745949
  intro a
  fin_cases a
  · exact context_11_23408_745874
  · exact context_11_23409_745895
  · exact context_11_23410_745919
  · exact context_11_23411_745948

theorem selected_cut_29556 : selected 10 ⟨745972, by decide⟩
    (prefixPartial 11 23412) = some ⟨11, 2, 0, 745972, 23412, 2497, 262144⟩ := by
  decide +kernel

theorem context_11_23412_745972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23412 ⟨745972, by decide⟩ :=
  accepted_of_selected 11 23412 ⟨745972, by decide⟩ ⟨11, 2, 0, 745972, 23412, 2497, 262144⟩
    (by decide) selected_cut_29556

theorem selected_cut_29557 : selected 10 ⟨745988, by decide⟩
    (prefixPartial 11 23413) = some ⟨11, 2, 0, 745988, 23413, 1465, 262144⟩ := by
  decide +kernel

theorem context_11_23413_745988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23413 ⟨745988, by decide⟩ :=
  accepted_of_selected 11 23413 ⟨745988, by decide⟩ ⟨11, 2, 0, 745988, 23413, 1465, 262144⟩
    (by decide) selected_cut_29557

theorem selected_cut_29558 : selected 10 ⟨746006, by decide⟩
    (prefixPartial 11 23414) = some ⟨11, 2, 0, 746006, 23414, 1953, 262144⟩ := by
  decide +kernel

theorem context_11_23414_746006 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23414 ⟨746006, by decide⟩ :=
  accepted_of_selected 11 23414 ⟨746006, by decide⟩ ⟨11, 2, 0, 746006, 23414, 1953, 262144⟩
    (by decide) selected_cut_29558

theorem selected_cut_29559 : selected 10 ⟨746028, by decide⟩
    (prefixPartial 11 23415) = some ⟨11, 2, 0, 746028, 23415, 1713, 262144⟩ := by
  decide +kernel

theorem context_11_23415_746028 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23415 ⟨746028, by decide⟩ :=
  accepted_of_selected 11 23415 ⟨746028, by decide⟩ ⟨11, 2, 0, 746028, 23415, 1713, 262144⟩
    (by decide) selected_cut_29559

theorem unmarked_context_10_5853_746029 : frontier 11 ⟨746029, by decide⟩
    (prefixCache 10 5853) (prefixPartial 10 5853) = false := by
  decide +kernel

theorem node_context_10_5853_746029 : EJMOriginalGlobalDAGData.nodes 11 ⟨746029, by decide⟩ =
    .split (coordinate 10) (![⟨745972, by decide⟩,⟨745988, by decide⟩,⟨746006, by decide⟩,⟨746028, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5853_746029 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5853 ⟨746029, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5853
    ⟨746029, by decide⟩ (by decide) (![⟨745972, by decide⟩,⟨745988, by decide⟩,⟨746006, by decide⟩,⟨746028, by decide⟩]) unmarked_context_10_5853_746029 node_context_10_5853_746029
  intro a
  fin_cases a
  · exact context_11_23412_745972
  · exact context_11_23413_745988
  · exact context_11_23414_746006
  · exact context_11_23415_746028

theorem selected_cut_29560 : selected 10 ⟨746047, by decide⟩
    (prefixPartial 11 23416) = some ⟨11, 2, 0, 746047, 23416, 1521, 262144⟩ := by
  decide +kernel

theorem context_11_23416_746047 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23416 ⟨746047, by decide⟩ :=
  accepted_of_selected 11 23416 ⟨746047, by decide⟩ ⟨11, 2, 0, 746047, 23416, 1521, 262144⟩
    (by decide) selected_cut_29560

theorem selected_cut_29561 : selected 10 ⟨746057, by decide⟩
    (prefixPartial 11 23417) = some ⟨11, 2, 0, 746057, 23417, 949, 262144⟩ := by
  decide +kernel

theorem context_11_23417_746057 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23417 ⟨746057, by decide⟩ :=
  accepted_of_selected 11 23417 ⟨746057, by decide⟩ ⟨11, 2, 0, 746057, 23417, 949, 262144⟩
    (by decide) selected_cut_29561

theorem selected_cut_29562 : selected 10 ⟨746070, by decide⟩
    (prefixPartial 11 23418) = some ⟨11, 2, 0, 746070, 23418, 1069, 262144⟩ := by
  decide +kernel

theorem context_11_23418_746070 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23418 ⟨746070, by decide⟩ :=
  accepted_of_selected 11 23418 ⟨746070, by decide⟩ ⟨11, 2, 0, 746070, 23418, 1069, 262144⟩
    (by decide) selected_cut_29562

theorem selected_cut_29563 : selected 10 ⟨746080, by decide⟩
    (prefixPartial 11 23419) = some ⟨11, 2, 0, 746080, 23419, 813, 262144⟩ := by
  decide +kernel

theorem context_11_23419_746080 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23419 ⟨746080, by decide⟩ :=
  accepted_of_selected 11 23419 ⟨746080, by decide⟩ ⟨11, 2, 0, 746080, 23419, 813, 262144⟩
    (by decide) selected_cut_29563

theorem unmarked_context_10_5854_746081 : frontier 11 ⟨746081, by decide⟩
    (prefixCache 10 5854) (prefixPartial 10 5854) = false := by
  decide +kernel

theorem node_context_10_5854_746081 : EJMOriginalGlobalDAGData.nodes 11 ⟨746081, by decide⟩ =
    .split (coordinate 10) (![⟨746047, by decide⟩,⟨746057, by decide⟩,⟨746070, by decide⟩,⟨746080, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5854_746081 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5854 ⟨746081, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5854
    ⟨746081, by decide⟩ (by decide) (![⟨746047, by decide⟩,⟨746057, by decide⟩,⟨746070, by decide⟩,⟨746080, by decide⟩]) unmarked_context_10_5854_746081 node_context_10_5854_746081
  intro a
  fin_cases a
  · exact context_11_23416_746047
  · exact context_11_23417_746057
  · exact context_11_23418_746070
  · exact context_11_23419_746080

theorem selected_cut_29564 : selected 11 ⟨746103, by decide⟩
    (prefixPartial 10 5855) = some ⟨10, 2, 0, 746103, 5855, 1025, 1048576⟩ := by
  decide +kernel

theorem context_10_5855_746103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5855 ⟨746103, by decide⟩ :=
  accepted_of_selected 10 5855 ⟨746103, by decide⟩ ⟨10, 2, 0, 746103, 5855, 1025, 1048576⟩
    (by decide) selected_cut_29564

theorem unmarked_context_9_1463_746104 : frontier 12 ⟨746104, by decide⟩
    (prefixCache 9 1463) (prefixPartial 9 1463) = false := by
  decide +kernel

theorem node_context_9_1463_746104 : EJMOriginalGlobalDAGData.nodes 12 ⟨746104, by decide⟩ =
    .split (coordinate 9) (![⟨745949, by decide⟩,⟨746029, by decide⟩,⟨746081, by decide⟩,⟨746103, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1463_746104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1463 ⟨746104, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1463
    ⟨746104, by decide⟩ (by decide) (![⟨745949, by decide⟩,⟨746029, by decide⟩,⟨746081, by decide⟩,⟨746103, by decide⟩]) unmarked_context_9_1463_746104 node_context_9_1463_746104
  intro a
  fin_cases a
  · exact context_10_5852_745949
  · exact context_10_5853_746029
  · exact context_10_5854_746081
  · exact context_10_5855_746103

theorem unmarked_context_8_365_746105 : frontier 13 ⟨746105, by decide⟩
    (prefixCache 8 365) (prefixPartial 8 365) = false := by
  decide +kernel

theorem node_context_8_365_746105 : EJMOriginalGlobalDAGData.nodes 13 ⟨746105, by decide⟩ =
    .split (coordinate 8) (![⟨742417, by decide⟩,⟨744494, by decide⟩,⟨745836, by decide⟩,⟨746104, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_365_746105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 365 ⟨746105, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 365
    ⟨746105, by decide⟩ (by decide) (![⟨742417, by decide⟩,⟨744494, by decide⟩,⟨745836, by decide⟩,⟨746104, by decide⟩]) unmarked_context_8_365_746105 node_context_8_365_746105
  intro a
  fin_cases a
  · exact context_9_1460_742417
  · exact context_9_1461_744494
  · exact context_9_1462_745836
  · exact context_9_1463_746104

theorem selected_cut_29565 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 23424) = some ⟨11, 1, 0, 434745, 23424, 1, 262144⟩ := by
  decide +kernel

theorem context_11_23424_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23424 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 23424 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 23424, 1, 262144⟩
    (by decide) selected_cut_29565

theorem selected_cut_29566 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 93700) = some ⟨12, 1, 0, 448748, 93700, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93700_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93700 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 93700 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 93700, 1, 65536⟩
    (by decide) selected_cut_29566

theorem selected_cut_29567 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 93701) = some ⟨12, 1, 0, 34034, 93701, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93701_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93701 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 93701 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 93701, 1, 65536⟩
    (by decide) selected_cut_29567

theorem selected_cut_29568 : selected 8 ⟨746181, by decide⟩
    (prefixPartial 13 374808) = some ⟨13, 2, 0, 746181, 374808, 2953, 16384⟩ := by
  decide +kernel

theorem context_13_374808_746181 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374808 ⟨746181, by decide⟩ :=
  accepted_of_selected 13 374808 ⟨746181, by decide⟩ ⟨13, 2, 0, 746181, 374808, 2953, 16384⟩
    (by decide) selected_cut_29568

theorem selected_cut_29569 : selected 8 ⟨746234, by decide⟩
    (prefixPartial 13 374809) = some ⟨13, 2, 0, 746234, 374809, 2389, 16384⟩ := by
  decide +kernel

theorem context_13_374809_746234 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374809 ⟨746234, by decide⟩ :=
  accepted_of_selected 13 374809 ⟨746234, by decide⟩ ⟨13, 2, 0, 746234, 374809, 2389, 16384⟩
    (by decide) selected_cut_29569

theorem selected_cut_29570 : selected 8 ⟨746255, by decide⟩
    (prefixPartial 13 374810) = some ⟨13, 2, 0, 746255, 374810, 1845, 16384⟩ := by
  decide +kernel

theorem context_13_374810_746255 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374810 ⟨746255, by decide⟩ :=
  accepted_of_selected 13 374810 ⟨746255, by decide⟩ ⟨13, 2, 0, 746255, 374810, 1845, 16384⟩
    (by decide) selected_cut_29570

theorem selected_cut_29571 : selected 8 ⟨746265, by decide⟩
    (prefixPartial 13 374811) = some ⟨13, 2, 0, 746265, 374811, 1081, 16384⟩ := by
  decide +kernel

theorem context_13_374811_746265 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374811 ⟨746265, by decide⟩ :=
  accepted_of_selected 13 374811 ⟨746265, by decide⟩ ⟨13, 2, 0, 746265, 374811, 1081, 16384⟩
    (by decide) selected_cut_29571

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
