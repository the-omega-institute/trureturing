/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover097
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_09411 : selected 8 ⟨259804, by decide⟩
    (prefixPartial 13 93513) = some ⟨13, 2, 0, 259804, 93513, 2769, 16384⟩ := by
  decide +kernel

theorem context_13_93513_259804 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93513 ⟨259804, by decide⟩ :=
  accepted_of_selected 13 93513 ⟨259804, by decide⟩ ⟨13, 2, 0, 259804, 93513, 2769, 16384⟩
    (by decide) selected_cut_09411

theorem selected_cut_09412 : selected 8 ⟨259842, by decide⟩
    (prefixPartial 13 93514) = some ⟨13, 2, 0, 259842, 93514, 2069, 16384⟩ := by
  decide +kernel

theorem context_13_93514_259842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93514 ⟨259842, by decide⟩ :=
  accepted_of_selected 13 93514 ⟨259842, by decide⟩ ⟨13, 2, 0, 259842, 93514, 2069, 16384⟩
    (by decide) selected_cut_09412

theorem selected_cut_09413 : selected 8 ⟨259856, by decide⟩
    (prefixPartial 13 93515) = some ⟨13, 2, 0, 259856, 93515, 789, 16384⟩ := by
  decide +kernel

theorem context_13_93515_259856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93515 ⟨259856, by decide⟩ :=
  accepted_of_selected 13 93515 ⟨259856, by decide⟩ ⟨13, 2, 0, 259856, 93515, 789, 16384⟩
    (by decide) selected_cut_09413

theorem unmarked_context_12_23378_259857 : frontier 9 ⟨259857, by decide⟩
    (prefixCache 12 23378) (prefixPartial 12 23378) = false := by
  decide +kernel

theorem node_context_12_23378_259857 : EJMOriginalGlobalDAGData.nodes 9 ⟨259857, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨259804, by decide⟩,⟨259842, by decide⟩,⟨259856, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23378_259857 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23378 ⟨259857, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23378
    ⟨259857, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨259804, by decide⟩,⟨259842, by decide⟩,⟨259856, by decide⟩]) unmarked_context_12_23378_259857 node_context_12_23378_259857
  intro a
  fin_cases a
  · exact context_13_93512_3444
  · exact context_13_93513_259804
  · exact context_13_93514_259842
  · exact context_13_93515_259856

theorem selected_cut_09414 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 93516) = some ⟨13, 1, 0, 3444, 93516, 1, 16384⟩ := by
  decide +kernel

theorem context_13_93516_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93516 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 93516 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 93516, 1, 16384⟩
    (by decide) selected_cut_09414

theorem selected_cut_09415 : selected 8 ⟨259890, by decide⟩
    (prefixPartial 13 93517) = some ⟨13, 2, 0, 259890, 93517, 2389, 16384⟩ := by
  decide +kernel

theorem context_13_93517_259890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93517 ⟨259890, by decide⟩ :=
  accepted_of_selected 13 93517 ⟨259890, by decide⟩ ⟨13, 2, 0, 259890, 93517, 2389, 16384⟩
    (by decide) selected_cut_09415

theorem selected_cut_09416 : selected 8 ⟨259918, by decide⟩
    (prefixPartial 13 93518) = some ⟨13, 2, 0, 259918, 93518, 2053, 16384⟩ := by
  decide +kernel

theorem context_13_93518_259918 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93518 ⟨259918, by decide⟩ :=
  accepted_of_selected 13 93518 ⟨259918, by decide⟩ ⟨13, 2, 0, 259918, 93518, 2053, 16384⟩
    (by decide) selected_cut_09416

theorem selected_cut_09417 : selected 8 ⟨259926, by decide⟩
    (prefixPartial 13 93519) = some ⟨13, 2, 0, 259926, 93519, 705, 16384⟩ := by
  decide +kernel

theorem context_13_93519_259926 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93519 ⟨259926, by decide⟩ :=
  accepted_of_selected 13 93519 ⟨259926, by decide⟩ ⟨13, 2, 0, 259926, 93519, 705, 16384⟩
    (by decide) selected_cut_09417

theorem unmarked_context_12_23379_259927 : frontier 9 ⟨259927, by decide⟩
    (prefixCache 12 23379) (prefixPartial 12 23379) = false := by
  decide +kernel

theorem node_context_12_23379_259927 : EJMOriginalGlobalDAGData.nodes 9 ⟨259927, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨259890, by decide⟩,⟨259918, by decide⟩,⟨259926, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23379_259927 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23379 ⟨259927, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23379
    ⟨259927, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨259890, by decide⟩,⟨259918, by decide⟩,⟨259926, by decide⟩]) unmarked_context_12_23379_259927 node_context_12_23379_259927
  intro a
  fin_cases a
  · exact context_13_93516_3444
  · exact context_13_93517_259890
  · exact context_13_93518_259918
  · exact context_13_93519_259926

theorem unmarked_context_11_5844_259928 : frontier 10 ⟨259928, by decide⟩
    (prefixCache 11 5844) (prefixPartial 11 5844) = false := by
  decide +kernel

theorem node_context_11_5844_259928 : EJMOriginalGlobalDAGData.nodes 10 ⟨259928, by decide⟩ =
    .split (coordinate 11) (![⟨259657, by decide⟩,⟨259743, by decide⟩,⟨259857, by decide⟩,⟨259927, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5844_259928 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5844 ⟨259928, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5844
    ⟨259928, by decide⟩ (by decide) (![⟨259657, by decide⟩,⟨259743, by decide⟩,⟨259857, by decide⟩,⟨259927, by decide⟩]) unmarked_context_11_5844_259928 node_context_11_5844_259928
  intro a
  fin_cases a
  · exact context_12_23376_259657
  · exact context_12_23377_259743
  · exact context_12_23378_259857
  · exact context_12_23379_259927

theorem selected_cut_09418 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 93520) = some ⟨13, 1, 0, 3444, 93520, 1, 16384⟩ := by
  decide +kernel

theorem context_13_93520_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93520 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 93520 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 93520, 1, 16384⟩
    (by decide) selected_cut_09418

theorem selected_cut_09419 : selected 8 ⟨259953, by decide⟩
    (prefixPartial 13 93521) = some ⟨13, 2, 0, 259953, 93521, 1909, 16384⟩ := by
  decide +kernel

theorem context_13_93521_259953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93521 ⟨259953, by decide⟩ :=
  accepted_of_selected 13 93521 ⟨259953, by decide⟩ ⟨13, 2, 0, 259953, 93521, 1909, 16384⟩
    (by decide) selected_cut_09419

theorem selected_cut_09420 : selected 8 ⟨259971, by decide⟩
    (prefixPartial 13 93522) = some ⟨13, 2, 0, 259971, 93522, 1453, 16384⟩ := by
  decide +kernel

theorem context_13_93522_259971 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93522 ⟨259971, by decide⟩ :=
  accepted_of_selected 13 93522 ⟨259971, by decide⟩ ⟨13, 2, 0, 259971, 93522, 1453, 16384⟩
    (by decide) selected_cut_09420

theorem selected_cut_09421 : selected 8 ⟨259982, by decide⟩
    (prefixPartial 13 93523) = some ⟨13, 2, 0, 259982, 93523, 969, 16384⟩ := by
  decide +kernel

theorem context_13_93523_259982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93523 ⟨259982, by decide⟩ :=
  accepted_of_selected 13 93523 ⟨259982, by decide⟩ ⟨13, 2, 0, 259982, 93523, 969, 16384⟩
    (by decide) selected_cut_09421

theorem unmarked_context_12_23380_259983 : frontier 9 ⟨259983, by decide⟩
    (prefixCache 12 23380) (prefixPartial 12 23380) = false := by
  decide +kernel

theorem node_context_12_23380_259983 : EJMOriginalGlobalDAGData.nodes 9 ⟨259983, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨259953, by decide⟩,⟨259971, by decide⟩,⟨259982, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23380_259983 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23380 ⟨259983, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23380
    ⟨259983, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨259953, by decide⟩,⟨259971, by decide⟩,⟨259982, by decide⟩]) unmarked_context_12_23380_259983 node_context_12_23380_259983
  intro a
  fin_cases a
  · exact context_13_93520_3444
  · exact context_13_93521_259953
  · exact context_13_93522_259971
  · exact context_13_93523_259982

theorem selected_cut_09422 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 23381) = some ⟨12, 1, 0, 170504, 23381, 1, 65536⟩ := by
  decide +kernel

theorem context_12_23381_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23381 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 23381 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 23381, 1, 65536⟩
    (by decide) selected_cut_09422

theorem selected_cut_09423 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 93528) = some ⟨13, 1, 0, 3444, 93528, 1, 16384⟩ := by
  decide +kernel

theorem context_13_93528_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93528 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 93528 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 93528, 1, 16384⟩
    (by decide) selected_cut_09423

theorem selected_cut_09424 : selected 8 ⟨260012, by decide⟩
    (prefixPartial 13 93529) = some ⟨13, 2, 0, 260012, 93529, 2145, 16384⟩ := by
  decide +kernel

theorem context_13_93529_260012 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93529 ⟨260012, by decide⟩ :=
  accepted_of_selected 13 93529 ⟨260012, by decide⟩ ⟨13, 2, 0, 260012, 93529, 2145, 16384⟩
    (by decide) selected_cut_09424

theorem selected_cut_09425 : selected 8 ⟨260036, by decide⟩
    (prefixPartial 13 93530) = some ⟨13, 2, 0, 260036, 93530, 1965, 16384⟩ := by
  decide +kernel

theorem context_13_93530_260036 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93530 ⟨260036, by decide⟩ :=
  accepted_of_selected 13 93530 ⟨260036, by decide⟩ ⟨13, 2, 0, 260036, 93530, 1965, 16384⟩
    (by decide) selected_cut_09425

theorem selected_cut_09426 : selected 8 ⟨260044, by decide⟩
    (prefixPartial 13 93531) = some ⟨13, 2, 0, 260044, 93531, 1021, 16384⟩ := by
  decide +kernel

theorem context_13_93531_260044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93531 ⟨260044, by decide⟩ :=
  accepted_of_selected 13 93531 ⟨260044, by decide⟩ ⟨13, 2, 0, 260044, 93531, 1021, 16384⟩
    (by decide) selected_cut_09426

theorem unmarked_context_12_23382_260045 : frontier 9 ⟨260045, by decide⟩
    (prefixCache 12 23382) (prefixPartial 12 23382) = false := by
  decide +kernel

theorem node_context_12_23382_260045 : EJMOriginalGlobalDAGData.nodes 9 ⟨260045, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨260012, by decide⟩,⟨260036, by decide⟩,⟨260044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23382_260045 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23382 ⟨260045, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23382
    ⟨260045, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨260012, by decide⟩,⟨260036, by decide⟩,⟨260044, by decide⟩]) unmarked_context_12_23382_260045 node_context_12_23382_260045
  intro a
  fin_cases a
  · exact context_13_93528_3444
  · exact context_13_93529_260012
  · exact context_13_93530_260036
  · exact context_13_93531_260044

theorem selected_cut_09427 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 93532) = some ⟨13, 1, 0, 3444, 93532, 1, 16384⟩ := by
  decide +kernel

theorem context_13_93532_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93532 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 93532 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 93532, 1, 16384⟩
    (by decide) selected_cut_09427

theorem selected_cut_09428 : selected 8 ⟨260064, by decide⟩
    (prefixPartial 13 93533) = some ⟨13, 2, 0, 260064, 93533, 1869, 16384⟩ := by
  decide +kernel

theorem context_13_93533_260064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93533 ⟨260064, by decide⟩ :=
  accepted_of_selected 13 93533 ⟨260064, by decide⟩ ⟨13, 2, 0, 260064, 93533, 1869, 16384⟩
    (by decide) selected_cut_09428

theorem selected_cut_09429 : selected 8 ⟨260082, by decide⟩
    (prefixPartial 13 93534) = some ⟨13, 2, 0, 260082, 93534, 1797, 16384⟩ := by
  decide +kernel

theorem context_13_93534_260082 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93534 ⟨260082, by decide⟩ :=
  accepted_of_selected 13 93534 ⟨260082, by decide⟩ ⟨13, 2, 0, 260082, 93534, 1797, 16384⟩
    (by decide) selected_cut_09429

theorem selected_cut_09430 : selected 8 ⟨260094, by decide⟩
    (prefixPartial 13 93535) = some ⟨13, 2, 0, 260094, 93535, 857, 16384⟩ := by
  decide +kernel

theorem context_13_93535_260094 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93535 ⟨260094, by decide⟩ :=
  accepted_of_selected 13 93535 ⟨260094, by decide⟩ ⟨13, 2, 0, 260094, 93535, 857, 16384⟩
    (by decide) selected_cut_09430

theorem unmarked_context_12_23383_260095 : frontier 9 ⟨260095, by decide⟩
    (prefixCache 12 23383) (prefixPartial 12 23383) = false := by
  decide +kernel

theorem node_context_12_23383_260095 : EJMOriginalGlobalDAGData.nodes 9 ⟨260095, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨260064, by decide⟩,⟨260082, by decide⟩,⟨260094, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23383_260095 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23383 ⟨260095, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23383
    ⟨260095, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨260064, by decide⟩,⟨260082, by decide⟩,⟨260094, by decide⟩]) unmarked_context_12_23383_260095 node_context_12_23383_260095
  intro a
  fin_cases a
  · exact context_13_93532_3444
  · exact context_13_93533_260064
  · exact context_13_93534_260082
  · exact context_13_93535_260094

theorem unmarked_context_11_5845_260096 : frontier 10 ⟨260096, by decide⟩
    (prefixCache 11 5845) (prefixPartial 11 5845) = false := by
  decide +kernel

theorem node_context_11_5845_260096 : EJMOriginalGlobalDAGData.nodes 10 ⟨260096, by decide⟩ =
    .split (coordinate 11) (![⟨259983, by decide⟩,⟨170504, by decide⟩,⟨260045, by decide⟩,⟨260095, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5845_260096 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5845 ⟨260096, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5845
    ⟨260096, by decide⟩ (by decide) (![⟨259983, by decide⟩,⟨170504, by decide⟩,⟨260045, by decide⟩,⟨260095, by decide⟩]) unmarked_context_11_5845_260096 node_context_11_5845_260096
  intro a
  fin_cases a
  · exact context_12_23380_259983
  · exact context_12_23381_170504
  · exact context_12_23382_260045
  · exact context_12_23383_260095

theorem selected_cut_09431 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 93536) = some ⟨13, 1, 0, 3444, 93536, 1, 16384⟩ := by
  decide +kernel

theorem context_13_93536_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93536 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 93536 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 93536, 1, 16384⟩
    (by decide) selected_cut_09431

theorem selected_cut_09432 : selected 8 ⟨260114, by decide⟩
    (prefixPartial 13 93537) = some ⟨13, 2, 0, 260114, 93537, 1689, 16384⟩ := by
  decide +kernel

theorem context_13_93537_260114 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93537 ⟨260114, by decide⟩ :=
  accepted_of_selected 13 93537 ⟨260114, by decide⟩ ⟨13, 2, 0, 260114, 93537, 1689, 16384⟩
    (by decide) selected_cut_09432

theorem selected_cut_09433 : selected 8 ⟨260140, by decide⟩
    (prefixPartial 13 93538) = some ⟨13, 2, 0, 260140, 93538, 2049, 16384⟩ := by
  decide +kernel

theorem context_13_93538_260140 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93538 ⟨260140, by decide⟩ :=
  accepted_of_selected 13 93538 ⟨260140, by decide⟩ ⟨13, 2, 0, 260140, 93538, 2049, 16384⟩
    (by decide) selected_cut_09433

theorem selected_cut_09434 : selected 8 ⟨260151, by decide⟩
    (prefixPartial 13 93539) = some ⟨13, 2, 0, 260151, 93539, 925, 16384⟩ := by
  decide +kernel

theorem context_13_93539_260151 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93539 ⟨260151, by decide⟩ :=
  accepted_of_selected 13 93539 ⟨260151, by decide⟩ ⟨13, 2, 0, 260151, 93539, 925, 16384⟩
    (by decide) selected_cut_09434

theorem unmarked_context_12_23384_260152 : frontier 9 ⟨260152, by decide⟩
    (prefixCache 12 23384) (prefixPartial 12 23384) = false := by
  decide +kernel

theorem node_context_12_23384_260152 : EJMOriginalGlobalDAGData.nodes 9 ⟨260152, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨260114, by decide⟩,⟨260140, by decide⟩,⟨260151, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23384_260152 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23384 ⟨260152, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23384
    ⟨260152, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨260114, by decide⟩,⟨260140, by decide⟩,⟨260151, by decide⟩]) unmarked_context_12_23384_260152 node_context_12_23384_260152
  intro a
  fin_cases a
  · exact context_13_93536_3444
  · exact context_13_93537_260114
  · exact context_13_93538_260140
  · exact context_13_93539_260151

theorem selected_cut_09435 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 93540) = some ⟨13, 1, 0, 3444, 93540, 1, 16384⟩ := by
  decide +kernel

theorem context_13_93540_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93540 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 93540 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 93540, 1, 16384⟩
    (by decide) selected_cut_09435

theorem selected_cut_09436 : selected 8 ⟨260198, by decide⟩
    (prefixPartial 13 93541) = some ⟨13, 2, 0, 260198, 93541, 2497, 16384⟩ := by
  decide +kernel

theorem context_13_93541_260198 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93541 ⟨260198, by decide⟩ :=
  accepted_of_selected 13 93541 ⟨260198, by decide⟩ ⟨13, 2, 0, 260198, 93541, 2497, 16384⟩
    (by decide) selected_cut_09436

theorem selected_cut_09437 : selected 8 ⟨260263, by decide⟩
    (prefixPartial 13 93542) = some ⟨13, 2, 0, 260263, 93542, 2849, 16384⟩ := by
  decide +kernel

theorem context_13_93542_260263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93542 ⟨260263, by decide⟩ :=
  accepted_of_selected 13 93542 ⟨260263, by decide⟩ ⟨13, 2, 0, 260263, 93542, 2849, 16384⟩
    (by decide) selected_cut_09437

theorem selected_cut_09438 : selected 8 ⟨260292, by decide⟩
    (prefixPartial 13 93543) = some ⟨13, 2, 0, 260292, 93543, 1193, 16384⟩ := by
  decide +kernel

theorem context_13_93543_260292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93543 ⟨260292, by decide⟩ :=
  accepted_of_selected 13 93543 ⟨260292, by decide⟩ ⟨13, 2, 0, 260292, 93543, 1193, 16384⟩
    (by decide) selected_cut_09438

theorem unmarked_context_12_23385_260293 : frontier 9 ⟨260293, by decide⟩
    (prefixCache 12 23385) (prefixPartial 12 23385) = false := by
  decide +kernel

theorem node_context_12_23385_260293 : EJMOriginalGlobalDAGData.nodes 9 ⟨260293, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨260198, by decide⟩,⟨260263, by decide⟩,⟨260292, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23385_260293 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23385 ⟨260293, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23385
    ⟨260293, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨260198, by decide⟩,⟨260263, by decide⟩,⟨260292, by decide⟩]) unmarked_context_12_23385_260293 node_context_12_23385_260293
  intro a
  fin_cases a
  · exact context_13_93540_3444
  · exact context_13_93541_260198
  · exact context_13_93542_260263
  · exact context_13_93543_260292

theorem selected_cut_09439 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 93544) = some ⟨13, 1, 0, 3444, 93544, 1, 16384⟩ := by
  decide +kernel

theorem context_13_93544_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93544 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 93544 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 93544, 1, 16384⟩
    (by decide) selected_cut_09439

theorem selected_cut_09440 : selected 8 ⟨260320, by decide⟩
    (prefixPartial 13 93545) = some ⟨13, 2, 0, 260320, 93545, 1905, 16384⟩ := by
  decide +kernel

theorem context_13_93545_260320 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93545 ⟨260320, by decide⟩ :=
  accepted_of_selected 13 93545 ⟨260320, by decide⟩ ⟨13, 2, 0, 260320, 93545, 1905, 16384⟩
    (by decide) selected_cut_09440

theorem selected_cut_09441 : selected 8 ⟨260378, by decide⟩
    (prefixPartial 13 93546) = some ⟨13, 2, 0, 260378, 93546, 2677, 16384⟩ := by
  decide +kernel

theorem context_13_93546_260378 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93546 ⟨260378, by decide⟩ :=
  accepted_of_selected 13 93546 ⟨260378, by decide⟩ ⟨13, 2, 0, 260378, 93546, 2677, 16384⟩
    (by decide) selected_cut_09441

theorem selected_cut_09442 : selected 8 ⟨260385, by decide⟩
    (prefixPartial 13 93547) = some ⟨13, 2, 0, 260385, 93547, 885, 16384⟩ := by
  decide +kernel

theorem context_13_93547_260385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93547 ⟨260385, by decide⟩ :=
  accepted_of_selected 13 93547 ⟨260385, by decide⟩ ⟨13, 2, 0, 260385, 93547, 885, 16384⟩
    (by decide) selected_cut_09442

theorem unmarked_context_12_23386_260386 : frontier 9 ⟨260386, by decide⟩
    (prefixCache 12 23386) (prefixPartial 12 23386) = false := by
  decide +kernel

theorem node_context_12_23386_260386 : EJMOriginalGlobalDAGData.nodes 9 ⟨260386, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨260320, by decide⟩,⟨260378, by decide⟩,⟨260385, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23386_260386 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23386 ⟨260386, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23386
    ⟨260386, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨260320, by decide⟩,⟨260378, by decide⟩,⟨260385, by decide⟩]) unmarked_context_12_23386_260386 node_context_12_23386_260386
  intro a
  fin_cases a
  · exact context_13_93544_3444
  · exact context_13_93545_260320
  · exact context_13_93546_260378
  · exact context_13_93547_260385

theorem selected_cut_09443 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 93548) = some ⟨13, 1, 0, 3444, 93548, 1, 16384⟩ := by
  decide +kernel

theorem context_13_93548_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93548 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 93548 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 93548, 1, 16384⟩
    (by decide) selected_cut_09443

theorem selected_cut_09444 : selected 8 ⟨260406, by decide⟩
    (prefixPartial 13 93549) = some ⟨13, 2, 0, 260406, 93549, 1773, 16384⟩ := by
  decide +kernel

theorem context_13_93549_260406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93549 ⟨260406, by decide⟩ :=
  accepted_of_selected 13 93549 ⟨260406, by decide⟩ ⟨13, 2, 0, 260406, 93549, 1773, 16384⟩
    (by decide) selected_cut_09444

theorem selected_cut_09445 : selected 8 ⟨260441, by decide⟩
    (prefixPartial 13 93550) = some ⟨13, 2, 0, 260441, 93550, 2429, 16384⟩ := by
  decide +kernel

theorem context_13_93550_260441 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93550 ⟨260441, by decide⟩ :=
  accepted_of_selected 13 93550 ⟨260441, by decide⟩ ⟨13, 2, 0, 260441, 93550, 2429, 16384⟩
    (by decide) selected_cut_09445

theorem selected_cut_09446 : selected 8 ⟨260448, by decide⟩
    (prefixPartial 13 93551) = some ⟨13, 2, 0, 260448, 93551, 861, 16384⟩ := by
  decide +kernel

theorem context_13_93551_260448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93551 ⟨260448, by decide⟩ :=
  accepted_of_selected 13 93551 ⟨260448, by decide⟩ ⟨13, 2, 0, 260448, 93551, 861, 16384⟩
    (by decide) selected_cut_09446

theorem unmarked_context_12_23387_260449 : frontier 9 ⟨260449, by decide⟩
    (prefixCache 12 23387) (prefixPartial 12 23387) = false := by
  decide +kernel

theorem node_context_12_23387_260449 : EJMOriginalGlobalDAGData.nodes 9 ⟨260449, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨260406, by decide⟩,⟨260441, by decide⟩,⟨260448, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23387_260449 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23387 ⟨260449, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23387
    ⟨260449, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨260406, by decide⟩,⟨260441, by decide⟩,⟨260448, by decide⟩]) unmarked_context_12_23387_260449 node_context_12_23387_260449
  intro a
  fin_cases a
  · exact context_13_93548_3444
  · exact context_13_93549_260406
  · exact context_13_93550_260441
  · exact context_13_93551_260448

theorem unmarked_context_11_5846_260450 : frontier 10 ⟨260450, by decide⟩
    (prefixCache 11 5846) (prefixPartial 11 5846) = false := by
  decide +kernel

theorem node_context_11_5846_260450 : EJMOriginalGlobalDAGData.nodes 10 ⟨260450, by decide⟩ =
    .split (coordinate 11) (![⟨260152, by decide⟩,⟨260293, by decide⟩,⟨260386, by decide⟩,⟨260449, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5846_260450 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5846 ⟨260450, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5846
    ⟨260450, by decide⟩ (by decide) (![⟨260152, by decide⟩,⟨260293, by decide⟩,⟨260386, by decide⟩,⟨260449, by decide⟩]) unmarked_context_11_5846_260450 node_context_11_5846_260450
  intro a
  fin_cases a
  · exact context_12_23384_260152
  · exact context_12_23385_260293
  · exact context_12_23386_260386
  · exact context_12_23387_260449

theorem selected_cut_09447 : selected 9 ⟨260500, by decide⟩
    (prefixPartial 12 23388) = some ⟨12, 2, 0, 260500, 23388, 3717, 65536⟩ := by
  decide +kernel

theorem context_12_23388_260500 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23388 ⟨260500, by decide⟩ :=
  accepted_of_selected 12 23388 ⟨260500, by decide⟩ ⟨12, 2, 0, 260500, 23388, 3717, 65536⟩
    (by decide) selected_cut_09447

theorem selected_cut_09448 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 93556) = some ⟨13, 1, 0, 3444, 93556, 1, 16384⟩ := by
  decide +kernel

theorem context_13_93556_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93556 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 93556 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 93556, 1, 16384⟩
    (by decide) selected_cut_09448

theorem selected_cut_09449 : selected 8 ⟨260539, by decide⟩
    (prefixPartial 13 93557) = some ⟨13, 2, 0, 260539, 93557, 2053, 16384⟩ := by
  decide +kernel

theorem context_13_93557_260539 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93557 ⟨260539, by decide⟩ :=
  accepted_of_selected 13 93557 ⟨260539, by decide⟩ ⟨13, 2, 0, 260539, 93557, 2053, 16384⟩
    (by decide) selected_cut_09449

theorem selected_cut_09450 : selected 8 ⟨260567, by decide⟩
    (prefixPartial 13 93558) = some ⟨13, 2, 0, 260567, 93558, 2237, 16384⟩ := by
  decide +kernel

theorem context_13_93558_260567 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93558 ⟨260567, by decide⟩ :=
  accepted_of_selected 13 93558 ⟨260567, by decide⟩ ⟨13, 2, 0, 260567, 93558, 2237, 16384⟩
    (by decide) selected_cut_09450

theorem selected_cut_09451 : selected 8 ⟨260590, by decide⟩
    (prefixPartial 13 93559) = some ⟨13, 2, 0, 260590, 93559, 989, 16384⟩ := by
  decide +kernel

theorem context_13_93559_260590 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93559 ⟨260590, by decide⟩ :=
  accepted_of_selected 13 93559 ⟨260590, by decide⟩ ⟨13, 2, 0, 260590, 93559, 989, 16384⟩
    (by decide) selected_cut_09451

theorem unmarked_context_12_23389_260591 : frontier 9 ⟨260591, by decide⟩
    (prefixCache 12 23389) (prefixPartial 12 23389) = false := by
  decide +kernel

theorem node_context_12_23389_260591 : EJMOriginalGlobalDAGData.nodes 9 ⟨260591, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨260539, by decide⟩,⟨260567, by decide⟩,⟨260590, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23389_260591 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23389 ⟨260591, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23389
    ⟨260591, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨260539, by decide⟩,⟨260567, by decide⟩,⟨260590, by decide⟩]) unmarked_context_12_23389_260591 node_context_12_23389_260591
  intro a
  fin_cases a
  · exact context_13_93556_3444
  · exact context_13_93557_260539
  · exact context_13_93558_260567
  · exact context_13_93559_260590

theorem selected_cut_09452 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 93560) = some ⟨13, 1, 0, 3444, 93560, 1, 16384⟩ := by
  decide +kernel

theorem context_13_93560_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93560 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 93560 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 93560, 1, 16384⟩
    (by decide) selected_cut_09452

theorem selected_cut_09453 : selected 8 ⟨260618, by decide⟩
    (prefixPartial 13 93561) = some ⟨13, 2, 0, 260618, 93561, 1677, 16384⟩ := by
  decide +kernel

theorem context_13_93561_260618 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93561 ⟨260618, by decide⟩ :=
  accepted_of_selected 13 93561 ⟨260618, by decide⟩ ⟨13, 2, 0, 260618, 93561, 1677, 16384⟩
    (by decide) selected_cut_09453

theorem selected_cut_09454 : selected 8 ⟨260645, by decide⟩
    (prefixPartial 13 93562) = some ⟨13, 2, 0, 260645, 93562, 1997, 16384⟩ := by
  decide +kernel

theorem context_13_93562_260645 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93562 ⟨260645, by decide⟩ :=
  accepted_of_selected 13 93562 ⟨260645, by decide⟩ ⟨13, 2, 0, 260645, 93562, 1997, 16384⟩
    (by decide) selected_cut_09454

theorem selected_cut_09455 : selected 8 ⟨260655, by decide⟩
    (prefixPartial 13 93563) = some ⟨13, 2, 0, 260655, 93563, 877, 16384⟩ := by
  decide +kernel

theorem context_13_93563_260655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93563 ⟨260655, by decide⟩ :=
  accepted_of_selected 13 93563 ⟨260655, by decide⟩ ⟨13, 2, 0, 260655, 93563, 877, 16384⟩
    (by decide) selected_cut_09455

theorem unmarked_context_12_23390_260656 : frontier 9 ⟨260656, by decide⟩
    (prefixCache 12 23390) (prefixPartial 12 23390) = false := by
  decide +kernel

theorem node_context_12_23390_260656 : EJMOriginalGlobalDAGData.nodes 9 ⟨260656, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨260618, by decide⟩,⟨260645, by decide⟩,⟨260655, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23390_260656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23390 ⟨260656, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23390
    ⟨260656, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨260618, by decide⟩,⟨260645, by decide⟩,⟨260655, by decide⟩]) unmarked_context_12_23390_260656 node_context_12_23390_260656
  intro a
  fin_cases a
  · exact context_13_93560_3444
  · exact context_13_93561_260618
  · exact context_13_93562_260645
  · exact context_13_93563_260655

theorem selected_cut_09456 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 93564) = some ⟨13, 1, 0, 3444, 93564, 1, 16384⟩ := by
  decide +kernel

theorem context_13_93564_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93564 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 93564 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 93564, 1, 16384⟩
    (by decide) selected_cut_09456

theorem selected_cut_09457 : selected 8 ⟨260715, by decide⟩
    (prefixPartial 13 93565) = some ⟨13, 2, 0, 260715, 93565, 2445, 16384⟩ := by
  decide +kernel

theorem context_13_93565_260715 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93565 ⟨260715, by decide⟩ :=
  accepted_of_selected 13 93565 ⟨260715, by decide⟩ ⟨13, 2, 0, 260715, 93565, 2445, 16384⟩
    (by decide) selected_cut_09457

theorem selected_cut_09458 : selected 8 ⟨260777, by decide⟩
    (prefixPartial 13 93566) = some ⟨13, 2, 0, 260777, 93566, 3013, 16384⟩ := by
  decide +kernel

theorem context_13_93566_260777 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93566 ⟨260777, by decide⟩ :=
  accepted_of_selected 13 93566 ⟨260777, by decide⟩ ⟨13, 2, 0, 260777, 93566, 3013, 16384⟩
    (by decide) selected_cut_09458

theorem selected_cut_09459 : selected 8 ⟨260808, by decide⟩
    (prefixPartial 13 93567) = some ⟨13, 2, 0, 260808, 93567, 1205, 16384⟩ := by
  decide +kernel

theorem context_13_93567_260808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93567 ⟨260808, by decide⟩ :=
  accepted_of_selected 13 93567 ⟨260808, by decide⟩ ⟨13, 2, 0, 260808, 93567, 1205, 16384⟩
    (by decide) selected_cut_09459

theorem unmarked_context_12_23391_260809 : frontier 9 ⟨260809, by decide⟩
    (prefixCache 12 23391) (prefixPartial 12 23391) = false := by
  decide +kernel

theorem node_context_12_23391_260809 : EJMOriginalGlobalDAGData.nodes 9 ⟨260809, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨260715, by decide⟩,⟨260777, by decide⟩,⟨260808, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23391_260809 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23391 ⟨260809, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23391
    ⟨260809, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨260715, by decide⟩,⟨260777, by decide⟩,⟨260808, by decide⟩]) unmarked_context_12_23391_260809 node_context_12_23391_260809
  intro a
  fin_cases a
  · exact context_13_93564_3444
  · exact context_13_93565_260715
  · exact context_13_93566_260777
  · exact context_13_93567_260808

theorem unmarked_context_11_5847_260810 : frontier 10 ⟨260810, by decide⟩
    (prefixCache 11 5847) (prefixPartial 11 5847) = false := by
  decide +kernel

theorem node_context_11_5847_260810 : EJMOriginalGlobalDAGData.nodes 10 ⟨260810, by decide⟩ =
    .split (coordinate 11) (![⟨260500, by decide⟩,⟨260591, by decide⟩,⟨260656, by decide⟩,⟨260809, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5847_260810 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5847 ⟨260810, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5847
    ⟨260810, by decide⟩ (by decide) (![⟨260500, by decide⟩,⟨260591, by decide⟩,⟨260656, by decide⟩,⟨260809, by decide⟩]) unmarked_context_11_5847_260810 node_context_11_5847_260810
  intro a
  fin_cases a
  · exact context_12_23388_260500
  · exact context_12_23389_260591
  · exact context_12_23390_260656
  · exact context_12_23391_260809

theorem unmarked_context_10_1461_260811 : frontier 11 ⟨260811, by decide⟩
    (prefixCache 10 1461) (prefixPartial 10 1461) = false := by
  decide +kernel

theorem node_context_10_1461_260811 : EJMOriginalGlobalDAGData.nodes 11 ⟨260811, by decide⟩ =
    .split (coordinate 10) (![⟨259928, by decide⟩,⟨260096, by decide⟩,⟨260450, by decide⟩,⟨260810, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1461_260811 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1461 ⟨260811, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1461
    ⟨260811, by decide⟩ (by decide) (![⟨259928, by decide⟩,⟨260096, by decide⟩,⟨260450, by decide⟩,⟨260810, by decide⟩]) unmarked_context_10_1461_260811 node_context_10_1461_260811
  intro a
  fin_cases a
  · exact context_11_5844_259928
  · exact context_11_5845_260096
  · exact context_11_5846_260450
  · exact context_11_5847_260810

theorem selected_cut_09460 : selected 9 ⟨260853, by decide⟩
    (prefixPartial 12 23392) = some ⟨12, 2, 0, 260853, 23392, 3941, 65536⟩ := by
  decide +kernel

theorem context_12_23392_260853 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23392 ⟨260853, by decide⟩ :=
  accepted_of_selected 12 23392 ⟨260853, by decide⟩ ⟨12, 2, 0, 260853, 23392, 3941, 65536⟩
    (by decide) selected_cut_09460

theorem selected_cut_09461 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 93572) = some ⟨13, 1, 0, 3444, 93572, 1, 16384⟩ := by
  decide +kernel

theorem context_13_93572_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93572 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 93572 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 93572, 1, 16384⟩
    (by decide) selected_cut_09461

theorem selected_cut_09462 : selected 8 ⟨260912, by decide⟩
    (prefixPartial 13 93573) = some ⟨13, 2, 0, 260912, 93573, 2289, 16384⟩ := by
  decide +kernel

theorem context_13_93573_260912 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93573 ⟨260912, by decide⟩ :=
  accepted_of_selected 13 93573 ⟨260912, by decide⟩ ⟨13, 2, 0, 260912, 93573, 2289, 16384⟩
    (by decide) selected_cut_09462

theorem selected_cut_09463 : selected 8 ⟨260939, by decide⟩
    (prefixPartial 13 93574) = some ⟨13, 2, 0, 260939, 93574, 2009, 16384⟩ := by
  decide +kernel

theorem context_13_93574_260939 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93574 ⟨260939, by decide⟩ :=
  accepted_of_selected 13 93574 ⟨260939, by decide⟩ ⟨13, 2, 0, 260939, 93574, 2009, 16384⟩
    (by decide) selected_cut_09463

theorem selected_cut_09464 : selected 8 ⟨260951, by decide⟩
    (prefixPartial 13 93575) = some ⟨13, 2, 0, 260951, 93575, 985, 16384⟩ := by
  decide +kernel

theorem context_13_93575_260951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93575 ⟨260951, by decide⟩ :=
  accepted_of_selected 13 93575 ⟨260951, by decide⟩ ⟨13, 2, 0, 260951, 93575, 985, 16384⟩
    (by decide) selected_cut_09464

theorem unmarked_context_12_23393_260952 : frontier 9 ⟨260952, by decide⟩
    (prefixCache 12 23393) (prefixPartial 12 23393) = false := by
  decide +kernel

theorem node_context_12_23393_260952 : EJMOriginalGlobalDAGData.nodes 9 ⟨260952, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨260912, by decide⟩,⟨260939, by decide⟩,⟨260951, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23393_260952 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23393 ⟨260952, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23393
    ⟨260952, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨260912, by decide⟩,⟨260939, by decide⟩,⟨260951, by decide⟩]) unmarked_context_12_23393_260952 node_context_12_23393_260952
  intro a
  fin_cases a
  · exact context_13_93572_3444
  · exact context_13_93573_260912
  · exact context_13_93574_260939
  · exact context_13_93575_260951

theorem selected_cut_09465 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 93576) = some ⟨13, 1, 0, 3444, 93576, 1, 16384⟩ := by
  decide +kernel

theorem context_13_93576_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93576 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 93576 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 93576, 1, 16384⟩
    (by decide) selected_cut_09465

theorem selected_cut_09466 : selected 8 ⟨260982, by decide⟩
    (prefixPartial 13 93577) = some ⟨13, 2, 0, 260982, 93577, 1765, 16384⟩ := by
  decide +kernel

theorem context_13_93577_260982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93577 ⟨260982, by decide⟩ :=
  accepted_of_selected 13 93577 ⟨260982, by decide⟩ ⟨13, 2, 0, 260982, 93577, 1765, 16384⟩
    (by decide) selected_cut_09466

theorem selected_cut_09467 : selected 8 ⟨261005, by decide⟩
    (prefixPartial 13 93578) = some ⟨13, 2, 0, 261005, 93578, 1721, 16384⟩ := by
  decide +kernel

theorem context_13_93578_261005 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93578 ⟨261005, by decide⟩ :=
  accepted_of_selected 13 93578 ⟨261005, by decide⟩ ⟨13, 2, 0, 261005, 93578, 1721, 16384⟩
    (by decide) selected_cut_09467

theorem selected_cut_09468 : selected 8 ⟨261011, by decide⟩
    (prefixPartial 13 93579) = some ⟨13, 2, 0, 261011, 93579, 773, 16384⟩ := by
  decide +kernel

theorem context_13_93579_261011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93579 ⟨261011, by decide⟩ :=
  accepted_of_selected 13 93579 ⟨261011, by decide⟩ ⟨13, 2, 0, 261011, 93579, 773, 16384⟩
    (by decide) selected_cut_09468

theorem unmarked_context_12_23394_261012 : frontier 9 ⟨261012, by decide⟩
    (prefixCache 12 23394) (prefixPartial 12 23394) = false := by
  decide +kernel

theorem node_context_12_23394_261012 : EJMOriginalGlobalDAGData.nodes 9 ⟨261012, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨260982, by decide⟩,⟨261005, by decide⟩,⟨261011, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23394_261012 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23394 ⟨261012, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23394
    ⟨261012, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨260982, by decide⟩,⟨261005, by decide⟩,⟨261011, by decide⟩]) unmarked_context_12_23394_261012 node_context_12_23394_261012
  intro a
  fin_cases a
  · exact context_13_93576_3444
  · exact context_13_93577_260982
  · exact context_13_93578_261005
  · exact context_13_93579_261011

theorem selected_cut_09469 : selected 9 ⟨261061, by decide⟩
    (prefixPartial 12 23395) = some ⟨12, 2, 0, 261061, 23395, 4057, 65536⟩ := by
  decide +kernel

theorem context_12_23395_261061 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23395 ⟨261061, by decide⟩ :=
  accepted_of_selected 12 23395 ⟨261061, by decide⟩ ⟨12, 2, 0, 261061, 23395, 4057, 65536⟩
    (by decide) selected_cut_09469

theorem unmarked_context_11_5848_261062 : frontier 10 ⟨261062, by decide⟩
    (prefixCache 11 5848) (prefixPartial 11 5848) = false := by
  decide +kernel

theorem node_context_11_5848_261062 : EJMOriginalGlobalDAGData.nodes 10 ⟨261062, by decide⟩ =
    .split (coordinate 11) (![⟨260853, by decide⟩,⟨260952, by decide⟩,⟨261012, by decide⟩,⟨261061, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5848_261062 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5848 ⟨261062, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5848
    ⟨261062, by decide⟩ (by decide) (![⟨260853, by decide⟩,⟨260952, by decide⟩,⟨261012, by decide⟩,⟨261061, by decide⟩]) unmarked_context_11_5848_261062 node_context_11_5848_261062
  intro a
  fin_cases a
  · exact context_12_23392_260853
  · exact context_12_23393_260952
  · exact context_12_23394_261012
  · exact context_12_23395_261061

theorem selected_cut_09470 : selected 9 ⟨261101, by decide⟩
    (prefixPartial 12 23396) = some ⟨12, 2, 0, 261101, 23396, 3801, 65536⟩ := by
  decide +kernel

theorem context_12_23396_261101 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23396 ⟨261101, by decide⟩ :=
  accepted_of_selected 12 23396 ⟨261101, by decide⟩ ⟨12, 2, 0, 261101, 23396, 3801, 65536⟩
    (by decide) selected_cut_09470

theorem selected_cut_09471 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 93588) = some ⟨13, 1, 0, 3444, 93588, 1, 16384⟩ := by
  decide +kernel

theorem context_13_93588_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93588 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 93588 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 93588, 1, 16384⟩
    (by decide) selected_cut_09471

theorem selected_cut_09472 : selected 8 ⟨261140, by decide⟩
    (prefixPartial 13 93589) = some ⟨13, 2, 0, 261140, 93589, 1849, 16384⟩ := by
  decide +kernel

theorem context_13_93589_261140 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93589 ⟨261140, by decide⟩ :=
  accepted_of_selected 13 93589 ⟨261140, by decide⟩ ⟨13, 2, 0, 261140, 93589, 1849, 16384⟩
    (by decide) selected_cut_09472

theorem selected_cut_09473 : selected 8 ⟨261168, by decide⟩
    (prefixPartial 13 93590) = some ⟨13, 2, 0, 261168, 93590, 2033, 16384⟩ := by
  decide +kernel

theorem context_13_93590_261168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93590 ⟨261168, by decide⟩ :=
  accepted_of_selected 13 93590 ⟨261168, by decide⟩ ⟨13, 2, 0, 261168, 93590, 2033, 16384⟩
    (by decide) selected_cut_09473

theorem selected_cut_09474 : selected 8 ⟨261194, by decide⟩
    (prefixPartial 13 93591) = some ⟨13, 2, 0, 261194, 93591, 1121, 16384⟩ := by
  decide +kernel

theorem context_13_93591_261194 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93591 ⟨261194, by decide⟩ :=
  accepted_of_selected 13 93591 ⟨261194, by decide⟩ ⟨13, 2, 0, 261194, 93591, 1121, 16384⟩
    (by decide) selected_cut_09474

theorem unmarked_context_12_23397_261195 : frontier 9 ⟨261195, by decide⟩
    (prefixCache 12 23397) (prefixPartial 12 23397) = false := by
  decide +kernel

theorem node_context_12_23397_261195 : EJMOriginalGlobalDAGData.nodes 9 ⟨261195, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨261140, by decide⟩,⟨261168, by decide⟩,⟨261194, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23397_261195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23397 ⟨261195, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23397
    ⟨261195, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨261140, by decide⟩,⟨261168, by decide⟩,⟨261194, by decide⟩]) unmarked_context_12_23397_261195 node_context_12_23397_261195
  intro a
  fin_cases a
  · exact context_13_93588_3444
  · exact context_13_93589_261140
  · exact context_13_93590_261168
  · exact context_13_93591_261194

theorem selected_cut_09475 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 93592) = some ⟨13, 1, 0, 3444, 93592, 1, 16384⟩ := by
  decide +kernel

theorem context_13_93592_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93592 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 93592 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 93592, 1, 16384⟩
    (by decide) selected_cut_09475

theorem selected_cut_09476 : selected 8 ⟨261214, by decide⟩
    (prefixPartial 13 93593) = some ⟨13, 2, 0, 261214, 93593, 1377, 16384⟩ := by
  decide +kernel

theorem context_13_93593_261214 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93593 ⟨261214, by decide⟩ :=
  accepted_of_selected 13 93593 ⟨261214, by decide⟩ ⟨13, 2, 0, 261214, 93593, 1377, 16384⟩
    (by decide) selected_cut_09476

theorem selected_cut_09477 : selected 8 ⟨261232, by decide⟩
    (prefixPartial 13 93594) = some ⟨13, 2, 0, 261232, 93594, 1765, 16384⟩ := by
  decide +kernel

theorem context_13_93594_261232 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93594 ⟨261232, by decide⟩ :=
  accepted_of_selected 13 93594 ⟨261232, by decide⟩ ⟨13, 2, 0, 261232, 93594, 1765, 16384⟩
    (by decide) selected_cut_09477

theorem selected_cut_09478 : selected 8 ⟨261243, by decide⟩
    (prefixPartial 13 93595) = some ⟨13, 2, 0, 261243, 93595, 1017, 16384⟩ := by
  decide +kernel

theorem context_13_93595_261243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93595 ⟨261243, by decide⟩ :=
  accepted_of_selected 13 93595 ⟨261243, by decide⟩ ⟨13, 2, 0, 261243, 93595, 1017, 16384⟩
    (by decide) selected_cut_09478

theorem unmarked_context_12_23398_261244 : frontier 9 ⟨261244, by decide⟩
    (prefixCache 12 23398) (prefixPartial 12 23398) = false := by
  decide +kernel

theorem node_context_12_23398_261244 : EJMOriginalGlobalDAGData.nodes 9 ⟨261244, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨261214, by decide⟩,⟨261232, by decide⟩,⟨261243, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23398_261244 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23398 ⟨261244, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23398
    ⟨261244, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨261214, by decide⟩,⟨261232, by decide⟩,⟨261243, by decide⟩]) unmarked_context_12_23398_261244 node_context_12_23398_261244
  intro a
  fin_cases a
  · exact context_13_93592_3444
  · exact context_13_93593_261214
  · exact context_13_93594_261232
  · exact context_13_93595_261243

theorem selected_cut_09479 : selected 9 ⟨261282, by decide⟩
    (prefixPartial 12 23399) = some ⟨12, 2, 0, 261282, 23399, 3781, 65536⟩ := by
  decide +kernel

theorem context_12_23399_261282 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23399 ⟨261282, by decide⟩ :=
  accepted_of_selected 12 23399 ⟨261282, by decide⟩ ⟨12, 2, 0, 261282, 23399, 3781, 65536⟩
    (by decide) selected_cut_09479

theorem unmarked_context_11_5849_261283 : frontier 10 ⟨261283, by decide⟩
    (prefixCache 11 5849) (prefixPartial 11 5849) = false := by
  decide +kernel

theorem node_context_11_5849_261283 : EJMOriginalGlobalDAGData.nodes 10 ⟨261283, by decide⟩ =
    .split (coordinate 11) (![⟨261101, by decide⟩,⟨261195, by decide⟩,⟨261244, by decide⟩,⟨261282, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5849_261283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5849 ⟨261283, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5849
    ⟨261283, by decide⟩ (by decide) (![⟨261101, by decide⟩,⟨261195, by decide⟩,⟨261244, by decide⟩,⟨261282, by decide⟩]) unmarked_context_11_5849_261283 node_context_11_5849_261283
  intro a
  fin_cases a
  · exact context_12_23396_261101
  · exact context_12_23397_261195
  · exact context_12_23398_261244
  · exact context_12_23399_261282

theorem selected_cut_09480 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 93600) = some ⟨13, 1, 0, 3444, 93600, 1, 16384⟩ := by
  decide +kernel

theorem context_13_93600_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93600 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 93600 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 93600, 1, 16384⟩
    (by decide) selected_cut_09480

theorem selected_cut_09481 : selected 8 ⟨261313, by decide⟩
    (prefixPartial 13 93601) = some ⟨13, 2, 0, 261313, 93601, 1525, 16384⟩ := by
  decide +kernel

theorem context_13_93601_261313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93601 ⟨261313, by decide⟩ :=
  accepted_of_selected 13 93601 ⟨261313, by decide⟩ ⟨13, 2, 0, 261313, 93601, 1525, 16384⟩
    (by decide) selected_cut_09481

theorem selected_cut_09482 : selected 8 ⟨261347, by decide⟩
    (prefixPartial 13 93602) = some ⟨13, 2, 0, 261347, 93602, 2261, 16384⟩ := by
  decide +kernel

theorem context_13_93602_261347 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93602 ⟨261347, by decide⟩ :=
  accepted_of_selected 13 93602 ⟨261347, by decide⟩ ⟨13, 2, 0, 261347, 93602, 2261, 16384⟩
    (by decide) selected_cut_09482

theorem selected_cut_09483 : selected 8 ⟨261385, by decide⟩
    (prefixPartial 13 93603) = some ⟨13, 2, 0, 261385, 93603, 1365, 16384⟩ := by
  decide +kernel

theorem context_13_93603_261385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93603 ⟨261385, by decide⟩ :=
  accepted_of_selected 13 93603 ⟨261385, by decide⟩ ⟨13, 2, 0, 261385, 93603, 1365, 16384⟩
    (by decide) selected_cut_09483

theorem unmarked_context_12_23400_261386 : frontier 9 ⟨261386, by decide⟩
    (prefixCache 12 23400) (prefixPartial 12 23400) = false := by
  decide +kernel

theorem node_context_12_23400_261386 : EJMOriginalGlobalDAGData.nodes 9 ⟨261386, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨261313, by decide⟩,⟨261347, by decide⟩,⟨261385, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23400_261386 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23400 ⟨261386, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23400
    ⟨261386, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨261313, by decide⟩,⟨261347, by decide⟩,⟨261385, by decide⟩]) unmarked_context_12_23400_261386 node_context_12_23400_261386
  intro a
  fin_cases a
  · exact context_13_93600_3444
  · exact context_13_93601_261313
  · exact context_13_93602_261347
  · exact context_13_93603_261385

theorem selected_cut_09484 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 93604) = some ⟨13, 1, 0, 3444, 93604, 1, 16384⟩ := by
  decide +kernel

theorem context_13_93604_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93604 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 93604 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 93604, 1, 16384⟩
    (by decide) selected_cut_09484

theorem selected_cut_09485 : selected 8 ⟨261441, by decide⟩
    (prefixPartial 13 93605) = some ⟨13, 2, 0, 261441, 93605, 2317, 16384⟩ := by
  decide +kernel

theorem context_13_93605_261441 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93605 ⟨261441, by decide⟩ :=
  accepted_of_selected 13 93605 ⟨261441, by decide⟩ ⟨13, 2, 0, 261441, 93605, 2317, 16384⟩
    (by decide) selected_cut_09485

theorem selected_cut_09486 : selected 8 ⟨261537, by decide⟩
    (prefixPartial 13 93606) = some ⟨13, 2, 0, 261537, 93606, 3417, 16384⟩ := by
  decide +kernel

theorem context_13_93606_261537 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93606 ⟨261537, by decide⟩ :=
  accepted_of_selected 13 93606 ⟨261537, by decide⟩ ⟨13, 2, 0, 261537, 93606, 3417, 16384⟩
    (by decide) selected_cut_09486

theorem selected_cut_09487 : selected 8 ⟨261627, by decide⟩
    (prefixPartial 13 93607) = some ⟨13, 2, 0, 261627, 93607, 1805, 16384⟩ := by
  decide +kernel

theorem context_13_93607_261627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93607 ⟨261627, by decide⟩ :=
  accepted_of_selected 13 93607 ⟨261627, by decide⟩ ⟨13, 2, 0, 261627, 93607, 1805, 16384⟩
    (by decide) selected_cut_09487

theorem unmarked_context_12_23401_261628 : frontier 9 ⟨261628, by decide⟩
    (prefixCache 12 23401) (prefixPartial 12 23401) = false := by
  decide +kernel

theorem node_context_12_23401_261628 : EJMOriginalGlobalDAGData.nodes 9 ⟨261628, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨261441, by decide⟩,⟨261537, by decide⟩,⟨261627, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23401_261628 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23401 ⟨261628, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23401
    ⟨261628, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨261441, by decide⟩,⟨261537, by decide⟩,⟨261627, by decide⟩]) unmarked_context_12_23401_261628 node_context_12_23401_261628
  intro a
  fin_cases a
  · exact context_13_93604_3444
  · exact context_13_93605_261441
  · exact context_13_93606_261537
  · exact context_13_93607_261627

theorem selected_cut_09488 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 93608) = some ⟨13, 1, 0, 3444, 93608, 1, 16384⟩ := by
  decide +kernel

theorem context_13_93608_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93608 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 93608 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 93608, 1, 16384⟩
    (by decide) selected_cut_09488

theorem selected_cut_09489 : selected 8 ⟨261668, by decide⟩
    (prefixPartial 13 93609) = some ⟨13, 2, 0, 261668, 93609, 1569, 16384⟩ := by
  decide +kernel

theorem context_13_93609_261668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93609 ⟨261668, by decide⟩ :=
  accepted_of_selected 13 93609 ⟨261668, by decide⟩ ⟨13, 2, 0, 261668, 93609, 1569, 16384⟩
    (by decide) selected_cut_09489

theorem selected_cut_09490 : selected 8 ⟨261706, by decide⟩
    (prefixPartial 13 93610) = some ⟨13, 2, 0, 261706, 93610, 2593, 16384⟩ := by
  decide +kernel

theorem context_13_93610_261706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93610 ⟨261706, by decide⟩ :=
  accepted_of_selected 13 93610 ⟨261706, by decide⟩ ⟨13, 2, 0, 261706, 93610, 2593, 16384⟩
    (by decide) selected_cut_09490

theorem selected_cut_09491 : selected 8 ⟨261722, by decide⟩
    (prefixPartial 13 93611) = some ⟨13, 2, 0, 261722, 93611, 1205, 16384⟩ := by
  decide +kernel

theorem context_13_93611_261722 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93611 ⟨261722, by decide⟩ :=
  accepted_of_selected 13 93611 ⟨261722, by decide⟩ ⟨13, 2, 0, 261722, 93611, 1205, 16384⟩
    (by decide) selected_cut_09491

theorem unmarked_context_12_23402_261723 : frontier 9 ⟨261723, by decide⟩
    (prefixCache 12 23402) (prefixPartial 12 23402) = false := by
  decide +kernel

theorem node_context_12_23402_261723 : EJMOriginalGlobalDAGData.nodes 9 ⟨261723, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨261668, by decide⟩,⟨261706, by decide⟩,⟨261722, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23402_261723 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23402 ⟨261723, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23402
    ⟨261723, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨261668, by decide⟩,⟨261706, by decide⟩,⟨261722, by decide⟩]) unmarked_context_12_23402_261723 node_context_12_23402_261723
  intro a
  fin_cases a
  · exact context_13_93608_3444
  · exact context_13_93609_261668
  · exact context_13_93610_261706
  · exact context_13_93611_261722

theorem selected_cut_09492 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 93612) = some ⟨13, 1, 0, 3444, 93612, 1, 16384⟩ := by
  decide +kernel

theorem context_13_93612_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93612 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 93612 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 93612, 1, 16384⟩
    (by decide) selected_cut_09492

theorem selected_cut_09493 : selected 8 ⟨261749, by decide⟩
    (prefixPartial 13 93613) = some ⟨13, 2, 0, 261749, 93613, 1341, 16384⟩ := by
  decide +kernel

theorem context_13_93613_261749 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93613 ⟨261749, by decide⟩ :=
  accepted_of_selected 13 93613 ⟨261749, by decide⟩ ⟨13, 2, 0, 261749, 93613, 1341, 16384⟩
    (by decide) selected_cut_09493

theorem selected_cut_09494 : selected 8 ⟨261793, by decide⟩
    (prefixPartial 13 93614) = some ⟨13, 2, 0, 261793, 93614, 2665, 16384⟩ := by
  decide +kernel

theorem context_13_93614_261793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93614 ⟨261793, by decide⟩ :=
  accepted_of_selected 13 93614 ⟨261793, by decide⟩ ⟨13, 2, 0, 261793, 93614, 2665, 16384⟩
    (by decide) selected_cut_09494

theorem selected_cut_09495 : selected 8 ⟨261807, by decide⟩
    (prefixPartial 13 93615) = some ⟨13, 2, 0, 261807, 93615, 1217, 16384⟩ := by
  decide +kernel

theorem context_13_93615_261807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93615 ⟨261807, by decide⟩ :=
  accepted_of_selected 13 93615 ⟨261807, by decide⟩ ⟨13, 2, 0, 261807, 93615, 1217, 16384⟩
    (by decide) selected_cut_09495

theorem unmarked_context_12_23403_261808 : frontier 9 ⟨261808, by decide⟩
    (prefixCache 12 23403) (prefixPartial 12 23403) = false := by
  decide +kernel

theorem node_context_12_23403_261808 : EJMOriginalGlobalDAGData.nodes 9 ⟨261808, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨261749, by decide⟩,⟨261793, by decide⟩,⟨261807, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23403_261808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23403 ⟨261808, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23403
    ⟨261808, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨261749, by decide⟩,⟨261793, by decide⟩,⟨261807, by decide⟩]) unmarked_context_12_23403_261808 node_context_12_23403_261808
  intro a
  fin_cases a
  · exact context_13_93612_3444
  · exact context_13_93613_261749
  · exact context_13_93614_261793
  · exact context_13_93615_261807

theorem unmarked_context_11_5850_261809 : frontier 10 ⟨261809, by decide⟩
    (prefixCache 11 5850) (prefixPartial 11 5850) = false := by
  decide +kernel

theorem node_context_11_5850_261809 : EJMOriginalGlobalDAGData.nodes 10 ⟨261809, by decide⟩ =
    .split (coordinate 11) (![⟨261386, by decide⟩,⟨261628, by decide⟩,⟨261723, by decide⟩,⟨261808, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5850_261809 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5850 ⟨261809, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5850
    ⟨261809, by decide⟩ (by decide) (![⟨261386, by decide⟩,⟨261628, by decide⟩,⟨261723, by decide⟩,⟨261808, by decide⟩]) unmarked_context_11_5850_261809 node_context_11_5850_261809
  intro a
  fin_cases a
  · exact context_12_23400_261386
  · exact context_12_23401_261628
  · exact context_12_23402_261723
  · exact context_12_23403_261808

theorem selected_cut_09496 : selected 9 ⟨261846, by decide⟩
    (prefixPartial 12 23404) = some ⟨12, 2, 0, 261846, 23404, 3289, 65536⟩ := by
  decide +kernel

theorem context_12_23404_261846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23404 ⟨261846, by decide⟩ :=
  accepted_of_selected 12 23404 ⟨261846, by decide⟩ ⟨12, 2, 0, 261846, 23404, 3289, 65536⟩
    (by decide) selected_cut_09496

theorem selected_cut_09497 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 93620) = some ⟨13, 1, 0, 3444, 93620, 1, 16384⟩ := by
  decide +kernel

theorem context_13_93620_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93620 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 93620 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 93620, 1, 16384⟩
    (by decide) selected_cut_09497

theorem selected_cut_09498 : selected 8 ⟨261868, by decide⟩
    (prefixPartial 13 93621) = some ⟨13, 2, 0, 261868, 93621, 1193, 16384⟩ := by
  decide +kernel

theorem context_13_93621_261868 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93621 ⟨261868, by decide⟩ :=
  accepted_of_selected 13 93621 ⟨261868, by decide⟩ ⟨13, 2, 0, 261868, 93621, 1193, 16384⟩
    (by decide) selected_cut_09498

theorem selected_cut_09499 : selected 8 ⟨261902, by decide⟩
    (prefixPartial 13 93622) = some ⟨13, 2, 0, 261902, 93622, 2273, 16384⟩ := by
  decide +kernel

theorem context_13_93622_261902 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93622 ⟨261902, by decide⟩ :=
  accepted_of_selected 13 93622 ⟨261902, by decide⟩ ⟨13, 2, 0, 261902, 93622, 2273, 16384⟩
    (by decide) selected_cut_09499

theorem selected_cut_09500 : selected 8 ⟨261920, by decide⟩
    (prefixPartial 13 93623) = some ⟨13, 2, 0, 261920, 93623, 1145, 16384⟩ := by
  decide +kernel

theorem context_13_93623_261920 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93623 ⟨261920, by decide⟩ :=
  accepted_of_selected 13 93623 ⟨261920, by decide⟩ ⟨13, 2, 0, 261920, 93623, 1145, 16384⟩
    (by decide) selected_cut_09500

theorem unmarked_context_12_23405_261921 : frontier 9 ⟨261921, by decide⟩
    (prefixCache 12 23405) (prefixPartial 12 23405) = false := by
  decide +kernel

theorem node_context_12_23405_261921 : EJMOriginalGlobalDAGData.nodes 9 ⟨261921, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨261868, by decide⟩,⟨261902, by decide⟩,⟨261920, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23405_261921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23405 ⟨261921, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23405
    ⟨261921, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨261868, by decide⟩,⟨261902, by decide⟩,⟨261920, by decide⟩]) unmarked_context_12_23405_261921 node_context_12_23405_261921
  intro a
  fin_cases a
  · exact context_13_93620_3444
  · exact context_13_93621_261868
  · exact context_13_93622_261902
  · exact context_13_93623_261920

theorem selected_cut_09501 : selected 9 ⟨261973, by decide⟩
    (prefixPartial 12 23406) = some ⟨12, 2, 0, 261973, 23406, 3717, 65536⟩ := by
  decide +kernel

theorem context_12_23406_261973 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23406 ⟨261973, by decide⟩ :=
  accepted_of_selected 12 23406 ⟨261973, by decide⟩ ⟨12, 2, 0, 261973, 23406, 3717, 65536⟩
    (by decide) selected_cut_09501

theorem selected_cut_09502 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 93628) = some ⟨13, 1, 0, 3444, 93628, 1, 16384⟩ := by
  decide +kernel

theorem context_13_93628_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93628 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 93628 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 93628, 1, 16384⟩
    (by decide) selected_cut_09502

theorem selected_cut_09503 : selected 8 ⟨261998, by decide⟩
    (prefixPartial 13 93629) = some ⟨13, 2, 0, 261998, 93629, 1161, 16384⟩ := by
  decide +kernel

theorem context_13_93629_261998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93629 ⟨261998, by decide⟩ :=
  accepted_of_selected 13 93629 ⟨261998, by decide⟩ ⟨13, 2, 0, 261998, 93629, 1161, 16384⟩
    (by decide) selected_cut_09503

theorem selected_cut_09504 : selected 8 ⟨262068, by decide⟩
    (prefixPartial 13 93630) = some ⟨13, 2, 0, 262068, 93630, 3021, 16384⟩ := by
  decide +kernel

theorem context_13_93630_262068 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93630 ⟨262068, by decide⟩ :=
  accepted_of_selected 13 93630 ⟨262068, by decide⟩ ⟨13, 2, 0, 262068, 93630, 3021, 16384⟩
    (by decide) selected_cut_09504

theorem selected_cut_09505 : selected 8 ⟨262107, by decide⟩
    (prefixPartial 13 93631) = some ⟨13, 2, 0, 262107, 93631, 1437, 16384⟩ := by
  decide +kernel

theorem context_13_93631_262107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 93631 ⟨262107, by decide⟩ :=
  accepted_of_selected 13 93631 ⟨262107, by decide⟩ ⟨13, 2, 0, 262107, 93631, 1437, 16384⟩
    (by decide) selected_cut_09505

theorem unmarked_context_12_23407_262108 : frontier 9 ⟨262108, by decide⟩
    (prefixCache 12 23407) (prefixPartial 12 23407) = false := by
  decide +kernel

theorem node_context_12_23407_262108 : EJMOriginalGlobalDAGData.nodes 9 ⟨262108, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨261998, by decide⟩,⟨262068, by decide⟩,⟨262107, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_23407_262108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23407 ⟨262108, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 23407
    ⟨262108, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨261998, by decide⟩,⟨262068, by decide⟩,⟨262107, by decide⟩]) unmarked_context_12_23407_262108 node_context_12_23407_262108
  intro a
  fin_cases a
  · exact context_13_93628_3444
  · exact context_13_93629_261998
  · exact context_13_93630_262068
  · exact context_13_93631_262107

theorem unmarked_context_11_5851_262109 : frontier 10 ⟨262109, by decide⟩
    (prefixCache 11 5851) (prefixPartial 11 5851) = false := by
  decide +kernel

theorem node_context_11_5851_262109 : EJMOriginalGlobalDAGData.nodes 10 ⟨262109, by decide⟩ =
    .split (coordinate 11) (![⟨261846, by decide⟩,⟨261921, by decide⟩,⟨261973, by decide⟩,⟨262108, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5851_262109 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5851 ⟨262109, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5851
    ⟨262109, by decide⟩ (by decide) (![⟨261846, by decide⟩,⟨261921, by decide⟩,⟨261973, by decide⟩,⟨262108, by decide⟩]) unmarked_context_11_5851_262109 node_context_11_5851_262109
  intro a
  fin_cases a
  · exact context_12_23404_261846
  · exact context_12_23405_261921
  · exact context_12_23406_261973
  · exact context_12_23407_262108

theorem unmarked_context_10_1462_262110 : frontier 11 ⟨262110, by decide⟩
    (prefixCache 10 1462) (prefixPartial 10 1462) = false := by
  decide +kernel

theorem node_context_10_1462_262110 : EJMOriginalGlobalDAGData.nodes 11 ⟨262110, by decide⟩ =
    .split (coordinate 10) (![⟨261062, by decide⟩,⟨261283, by decide⟩,⟨261809, by decide⟩,⟨262109, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1462_262110 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1462 ⟨262110, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1462
    ⟨262110, by decide⟩ (by decide) (![⟨261062, by decide⟩,⟨261283, by decide⟩,⟨261809, by decide⟩,⟨262109, by decide⟩]) unmarked_context_10_1462_262110 node_context_10_1462_262110
  intro a
  fin_cases a
  · exact context_11_5848_261062
  · exact context_11_5849_261283
  · exact context_11_5850_261809
  · exact context_11_5851_262109

theorem selected_cut_09506 : selected 9 ⟨262154, by decide⟩
    (prefixPartial 12 23408) = some ⟨12, 2, 0, 262154, 23408, 3165, 65536⟩ := by
  decide +kernel

theorem context_12_23408_262154 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 23408 ⟨262154, by decide⟩ :=
  accepted_of_selected 12 23408 ⟨262154, by decide⟩ ⟨12, 2, 0, 262154, 23408, 3165, 65536⟩
    (by decide) selected_cut_09506

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
