/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover360
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_34658 : selected 9 ⟨106538, by decide⟩
    (prefixPartial 12 281360) = some ⟨12, 1, 0, 106538, 281360, 1, 65536⟩ := by
  decide +kernel

theorem context_12_281360_106538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281360 ⟨106538, by decide⟩ :=
  accepted_of_selected 12 281360 ⟨106538, by decide⟩ ⟨12, 1, 0, 106538, 281360, 1, 65536⟩
    (by decide) selected_cut_34658

theorem selected_cut_34659 : selected 9 ⟨903869, by decide⟩
    (prefixPartial 12 281361) = some ⟨12, 2, 0, 903869, 281361, 2189, 65536⟩ := by
  decide +kernel

theorem context_12_281361_903869 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281361 ⟨903869, by decide⟩ :=
  accepted_of_selected 12 281361 ⟨903869, by decide⟩ ⟨12, 2, 0, 903869, 281361, 2189, 65536⟩
    (by decide) selected_cut_34659

theorem selected_cut_34660 : selected 9 ⟨903951, by decide⟩
    (prefixPartial 12 281362) = some ⟨12, 2, 0, 903951, 281362, 4073, 65536⟩ := by
  decide +kernel

theorem context_12_281362_903951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281362 ⟨903951, by decide⟩ :=
  accepted_of_selected 12 281362 ⟨903951, by decide⟩ ⟨12, 2, 0, 903951, 281362, 4073, 65536⟩
    (by decide) selected_cut_34660

theorem selected_cut_34661 : selected 9 ⟨904020, by decide⟩
    (prefixPartial 12 281363) = some ⟨12, 2, 0, 904020, 281363, 3781, 65536⟩ := by
  decide +kernel

theorem context_12_281363_904020 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281363 ⟨904020, by decide⟩ :=
  accepted_of_selected 12 281363 ⟨904020, by decide⟩ ⟨12, 2, 0, 904020, 281363, 3781, 65536⟩
    (by decide) selected_cut_34661

theorem unmarked_context_11_70340_904021 : frontier 10 ⟨904021, by decide⟩
    (prefixCache 11 70340) (prefixPartial 11 70340) = false := by
  decide +kernel

theorem node_context_11_70340_904021 : EJMOriginalGlobalDAGData.nodes 10 ⟨904021, by decide⟩ =
    .split (coordinate 11) (![⟨106538, by decide⟩,⟨903869, by decide⟩,⟨903951, by decide⟩,⟨904020, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70340_904021 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70340 ⟨904021, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70340
    ⟨904021, by decide⟩ (by decide) (![⟨106538, by decide⟩,⟨903869, by decide⟩,⟨903951, by decide⟩,⟨904020, by decide⟩]) unmarked_context_11_70340_904021 node_context_11_70340_904021
  intro a
  fin_cases a
  · exact context_12_281360_106538
  · exact context_12_281361_903869
  · exact context_12_281362_903951
  · exact context_12_281363_904020

theorem selected_cut_34662 : selected 9 ⟨106538, by decide⟩
    (prefixPartial 12 281364) = some ⟨12, 1, 0, 106538, 281364, 1, 65536⟩ := by
  decide +kernel

theorem context_12_281364_106538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281364 ⟨106538, by decide⟩ :=
  accepted_of_selected 12 281364 ⟨106538, by decide⟩ ⟨12, 1, 0, 106538, 281364, 1, 65536⟩
    (by decide) selected_cut_34662

theorem selected_cut_34663 : selected 9 ⟨904073, by decide⟩
    (prefixPartial 12 281365) = some ⟨12, 2, 0, 904073, 281365, 1833, 65536⟩ := by
  decide +kernel

theorem context_12_281365_904073 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281365 ⟨904073, by decide⟩ :=
  accepted_of_selected 12 281365 ⟨904073, by decide⟩ ⟨12, 2, 0, 904073, 281365, 1833, 65536⟩
    (by decide) selected_cut_34663

theorem selected_cut_34664 : selected 9 ⟨904136, by decide⟩
    (prefixPartial 12 281366) = some ⟨12, 2, 0, 904136, 281366, 3409, 65536⟩ := by
  decide +kernel

theorem context_12_281366_904136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281366 ⟨904136, by decide⟩ :=
  accepted_of_selected 12 281366 ⟨904136, by decide⟩ ⟨12, 2, 0, 904136, 281366, 3409, 65536⟩
    (by decide) selected_cut_34664

theorem selected_cut_34665 : selected 9 ⟨904193, by decide⟩
    (prefixPartial 12 281367) = some ⟨12, 2, 0, 904193, 281367, 3229, 65536⟩ := by
  decide +kernel

theorem context_12_281367_904193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281367 ⟨904193, by decide⟩ :=
  accepted_of_selected 12 281367 ⟨904193, by decide⟩ ⟨12, 2, 0, 904193, 281367, 3229, 65536⟩
    (by decide) selected_cut_34665

theorem unmarked_context_11_70341_904194 : frontier 10 ⟨904194, by decide⟩
    (prefixCache 11 70341) (prefixPartial 11 70341) = false := by
  decide +kernel

theorem node_context_11_70341_904194 : EJMOriginalGlobalDAGData.nodes 10 ⟨904194, by decide⟩ =
    .split (coordinate 11) (![⟨106538, by decide⟩,⟨904073, by decide⟩,⟨904136, by decide⟩,⟨904193, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70341_904194 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70341 ⟨904194, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70341
    ⟨904194, by decide⟩ (by decide) (![⟨106538, by decide⟩,⟨904073, by decide⟩,⟨904136, by decide⟩,⟨904193, by decide⟩]) unmarked_context_11_70341_904194 node_context_11_70341_904194
  intro a
  fin_cases a
  · exact context_12_281364_106538
  · exact context_12_281365_904073
  · exact context_12_281366_904136
  · exact context_12_281367_904193

theorem selected_cut_34666 : selected 9 ⟨106538, by decide⟩
    (prefixPartial 12 281368) = some ⟨12, 1, 0, 106538, 281368, 1, 65536⟩ := by
  decide +kernel

theorem context_12_281368_106538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281368 ⟨106538, by decide⟩ :=
  accepted_of_selected 12 281368 ⟨106538, by decide⟩ ⟨12, 1, 0, 106538, 281368, 1, 65536⟩
    (by decide) selected_cut_34666

theorem selected_cut_34667 : selected 9 ⟨904257, by decide⟩
    (prefixPartial 12 281369) = some ⟨12, 2, 0, 904257, 281369, 3193, 65536⟩ := by
  decide +kernel

theorem context_12_281369_904257 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281369 ⟨904257, by decide⟩ :=
  accepted_of_selected 12 281369 ⟨904257, by decide⟩ ⟨12, 2, 0, 904257, 281369, 3193, 65536⟩
    (by decide) selected_cut_34667

theorem selected_cut_34668 : selected 9 ⟨904319, by decide⟩
    (prefixPartial 12 281370) = some ⟨12, 2, 0, 904319, 281370, 3525, 65536⟩ := by
  decide +kernel

theorem context_12_281370_904319 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281370 ⟨904319, by decide⟩ :=
  accepted_of_selected 12 281370 ⟨904319, by decide⟩ ⟨12, 2, 0, 904319, 281370, 3525, 65536⟩
    (by decide) selected_cut_34668

theorem selected_cut_34669 : selected 9 ⟨904400, by decide⟩
    (prefixPartial 12 281371) = some ⟨12, 2, 0, 904400, 281371, 3473, 65536⟩ := by
  decide +kernel

theorem context_12_281371_904400 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281371 ⟨904400, by decide⟩ :=
  accepted_of_selected 12 281371 ⟨904400, by decide⟩ ⟨12, 2, 0, 904400, 281371, 3473, 65536⟩
    (by decide) selected_cut_34669

theorem unmarked_context_11_70342_904401 : frontier 10 ⟨904401, by decide⟩
    (prefixCache 11 70342) (prefixPartial 11 70342) = false := by
  decide +kernel

theorem node_context_11_70342_904401 : EJMOriginalGlobalDAGData.nodes 10 ⟨904401, by decide⟩ =
    .split (coordinate 11) (![⟨106538, by decide⟩,⟨904257, by decide⟩,⟨904319, by decide⟩,⟨904400, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70342_904401 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70342 ⟨904401, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70342
    ⟨904401, by decide⟩ (by decide) (![⟨106538, by decide⟩,⟨904257, by decide⟩,⟨904319, by decide⟩,⟨904400, by decide⟩]) unmarked_context_11_70342_904401 node_context_11_70342_904401
  intro a
  fin_cases a
  · exact context_12_281368_106538
  · exact context_12_281369_904257
  · exact context_12_281370_904319
  · exact context_12_281371_904400

theorem selected_cut_34670 : selected 10 ⟨904458, by decide⟩
    (prefixPartial 11 70343) = some ⟨11, 2, 0, 904458, 70343, 3385, 262144⟩ := by
  decide +kernel

theorem context_11_70343_904458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70343 ⟨904458, by decide⟩ :=
  accepted_of_selected 11 70343 ⟨904458, by decide⟩ ⟨11, 2, 0, 904458, 70343, 3385, 262144⟩
    (by decide) selected_cut_34670

theorem unmarked_context_10_17585_904459 : frontier 11 ⟨904459, by decide⟩
    (prefixCache 10 17585) (prefixPartial 10 17585) = false := by
  decide +kernel

theorem node_context_10_17585_904459 : EJMOriginalGlobalDAGData.nodes 11 ⟨904459, by decide⟩ =
    .split (coordinate 10) (![⟨904021, by decide⟩,⟨904194, by decide⟩,⟨904401, by decide⟩,⟨904458, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17585_904459 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17585 ⟨904459, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17585
    ⟨904459, by decide⟩ (by decide) (![⟨904021, by decide⟩,⟨904194, by decide⟩,⟨904401, by decide⟩,⟨904458, by decide⟩]) unmarked_context_10_17585_904459 node_context_10_17585_904459
  intro a
  fin_cases a
  · exact context_11_70340_904021
  · exact context_11_70341_904194
  · exact context_11_70342_904401
  · exact context_11_70343_904458

theorem selected_cut_34671 : selected 9 ⟨106538, by decide⟩
    (prefixPartial 12 281376) = some ⟨12, 1, 0, 106538, 281376, 1, 65536⟩ := by
  decide +kernel

theorem context_12_281376_106538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281376 ⟨106538, by decide⟩ :=
  accepted_of_selected 12 281376 ⟨106538, by decide⟩ ⟨12, 1, 0, 106538, 281376, 1, 65536⟩
    (by decide) selected_cut_34671

theorem selected_cut_34672 : selected 9 ⟨106538, by decide⟩
    (prefixPartial 12 281377) = some ⟨12, 1, 0, 106538, 281377, 1, 65536⟩ := by
  decide +kernel

theorem context_12_281377_106538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281377 ⟨106538, by decide⟩ :=
  accepted_of_selected 12 281377 ⟨106538, by decide⟩ ⟨12, 1, 0, 106538, 281377, 1, 65536⟩
    (by decide) selected_cut_34672

theorem selected_cut_34673 : selected 9 ⟨904534, by decide⟩
    (prefixPartial 12 281378) = some ⟨12, 2, 0, 904534, 281378, 3177, 65536⟩ := by
  decide +kernel

theorem context_12_281378_904534 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281378 ⟨904534, by decide⟩ :=
  accepted_of_selected 12 281378 ⟨904534, by decide⟩ ⟨12, 2, 0, 904534, 281378, 3177, 65536⟩
    (by decide) selected_cut_34673

theorem selected_cut_34674 : selected 9 ⟨904580, by decide⟩
    (prefixPartial 12 281379) = some ⟨12, 2, 0, 904580, 281379, 1729, 65536⟩ := by
  decide +kernel

theorem context_12_281379_904580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281379 ⟨904580, by decide⟩ :=
  accepted_of_selected 12 281379 ⟨904580, by decide⟩ ⟨12, 2, 0, 904580, 281379, 1729, 65536⟩
    (by decide) selected_cut_34674

theorem unmarked_context_11_70344_904581 : frontier 10 ⟨904581, by decide⟩
    (prefixCache 11 70344) (prefixPartial 11 70344) = false := by
  decide +kernel

theorem node_context_11_70344_904581 : EJMOriginalGlobalDAGData.nodes 10 ⟨904581, by decide⟩ =
    .split (coordinate 11) (![⟨106538, by decide⟩,⟨106538, by decide⟩,⟨904534, by decide⟩,⟨904580, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70344_904581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70344 ⟨904581, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70344
    ⟨904581, by decide⟩ (by decide) (![⟨106538, by decide⟩,⟨106538, by decide⟩,⟨904534, by decide⟩,⟨904580, by decide⟩]) unmarked_context_11_70344_904581 node_context_11_70344_904581
  intro a
  fin_cases a
  · exact context_12_281376_106538
  · exact context_12_281377_106538
  · exact context_12_281378_904534
  · exact context_12_281379_904580

theorem selected_cut_34675 : selected 9 ⟨106538, by decide⟩
    (prefixPartial 12 281380) = some ⟨12, 1, 0, 106538, 281380, 1, 65536⟩ := by
  decide +kernel

theorem context_12_281380_106538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281380 ⟨106538, by decide⟩ :=
  accepted_of_selected 12 281380 ⟨106538, by decide⟩ ⟨12, 1, 0, 106538, 281380, 1, 65536⟩
    (by decide) selected_cut_34675

theorem selected_cut_34676 : selected 9 ⟨106538, by decide⟩
    (prefixPartial 12 281381) = some ⟨12, 1, 0, 106538, 281381, 1, 65536⟩ := by
  decide +kernel

theorem context_12_281381_106538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281381 ⟨106538, by decide⟩ :=
  accepted_of_selected 12 281381 ⟨106538, by decide⟩ ⟨12, 1, 0, 106538, 281381, 1, 65536⟩
    (by decide) selected_cut_34676

theorem selected_cut_34677 : selected 9 ⟨904646, by decide⟩
    (prefixPartial 12 281382) = some ⟨12, 2, 0, 904646, 281382, 3013, 65536⟩ := by
  decide +kernel

theorem context_12_281382_904646 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281382 ⟨904646, by decide⟩ :=
  accepted_of_selected 12 281382 ⟨904646, by decide⟩ ⟨12, 2, 0, 904646, 281382, 3013, 65536⟩
    (by decide) selected_cut_34677

theorem selected_cut_34678 : selected 9 ⟨904691, by decide⟩
    (prefixPartial 12 281383) = some ⟨12, 2, 0, 904691, 281383, 1693, 65536⟩ := by
  decide +kernel

theorem context_12_281383_904691 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281383 ⟨904691, by decide⟩ :=
  accepted_of_selected 12 281383 ⟨904691, by decide⟩ ⟨12, 2, 0, 904691, 281383, 1693, 65536⟩
    (by decide) selected_cut_34678

theorem unmarked_context_11_70345_904692 : frontier 10 ⟨904692, by decide⟩
    (prefixCache 11 70345) (prefixPartial 11 70345) = false := by
  decide +kernel

theorem node_context_11_70345_904692 : EJMOriginalGlobalDAGData.nodes 10 ⟨904692, by decide⟩ =
    .split (coordinate 11) (![⟨106538, by decide⟩,⟨106538, by decide⟩,⟨904646, by decide⟩,⟨904691, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70345_904692 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70345 ⟨904692, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70345
    ⟨904692, by decide⟩ (by decide) (![⟨106538, by decide⟩,⟨106538, by decide⟩,⟨904646, by decide⟩,⟨904691, by decide⟩]) unmarked_context_11_70345_904692 node_context_11_70345_904692
  intro a
  fin_cases a
  · exact context_12_281380_106538
  · exact context_12_281381_106538
  · exact context_12_281382_904646
  · exact context_12_281383_904691

theorem selected_cut_34679 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 70346) = some ⟨11, 1, 0, 900587, 70346, 1, 262144⟩ := by
  decide +kernel

theorem context_11_70346_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70346 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 70346 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 70346, 1, 262144⟩
    (by decide) selected_cut_34679

theorem selected_cut_34680 : selected 10 ⟨904764, by decide⟩
    (prefixPartial 11 70347) = some ⟨11, 2, 0, 904764, 70347, 3357, 262144⟩ := by
  decide +kernel

theorem context_11_70347_904764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70347 ⟨904764, by decide⟩ :=
  accepted_of_selected 11 70347 ⟨904764, by decide⟩ ⟨11, 2, 0, 904764, 70347, 3357, 262144⟩
    (by decide) selected_cut_34680

theorem unmarked_context_10_17586_904765 : frontier 11 ⟨904765, by decide⟩
    (prefixCache 10 17586) (prefixPartial 10 17586) = false := by
  decide +kernel

theorem node_context_10_17586_904765 : EJMOriginalGlobalDAGData.nodes 11 ⟨904765, by decide⟩ =
    .split (coordinate 10) (![⟨904581, by decide⟩,⟨904692, by decide⟩,⟨900587, by decide⟩,⟨904764, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17586_904765 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17586 ⟨904765, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17586
    ⟨904765, by decide⟩ (by decide) (![⟨904581, by decide⟩,⟨904692, by decide⟩,⟨900587, by decide⟩,⟨904764, by decide⟩]) unmarked_context_10_17586_904765 node_context_10_17586_904765
  intro a
  fin_cases a
  · exact context_11_70344_904581
  · exact context_11_70345_904692
  · exact context_11_70346_900587
  · exact context_11_70347_904764

theorem selected_cut_34681 : selected 10 ⟨904809, by decide⟩
    (prefixPartial 11 70348) = some ⟨11, 2, 0, 904809, 70348, 1857, 262144⟩ := by
  decide +kernel

theorem context_11_70348_904809 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70348 ⟨904809, by decide⟩ :=
  accepted_of_selected 11 70348 ⟨904809, by decide⟩ ⟨11, 2, 0, 904809, 70348, 1857, 262144⟩
    (by decide) selected_cut_34681

theorem selected_cut_34682 : selected 10 ⟨904853, by decide⟩
    (prefixPartial 11 70349) = some ⟨11, 2, 0, 904853, 70349, 1773, 262144⟩ := by
  decide +kernel

theorem context_11_70349_904853 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70349 ⟨904853, by decide⟩ :=
  accepted_of_selected 11 70349 ⟨904853, by decide⟩ ⟨11, 2, 0, 904853, 70349, 1773, 262144⟩
    (by decide) selected_cut_34682

theorem selected_cut_34683 : selected 10 ⟨904924, by decide⟩
    (prefixPartial 11 70350) = some ⟨11, 2, 0, 904924, 70350, 3233, 262144⟩ := by
  decide +kernel

theorem context_11_70350_904924 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70350 ⟨904924, by decide⟩ :=
  accepted_of_selected 11 70350 ⟨904924, by decide⟩ ⟨11, 2, 0, 904924, 70350, 3233, 262144⟩
    (by decide) selected_cut_34683

theorem selected_cut_34684 : selected 10 ⟨109216, by decide⟩
    (prefixPartial 11 70351) = some ⟨11, 2, 0, 109216, 70351, 5, 262144⟩ := by
  decide +kernel

theorem context_11_70351_109216 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70351 ⟨109216, by decide⟩ :=
  accepted_of_selected 11 70351 ⟨109216, by decide⟩ ⟨11, 2, 0, 109216, 70351, 5, 262144⟩
    (by decide) selected_cut_34684

theorem unmarked_context_10_17587_904925 : frontier 11 ⟨904925, by decide⟩
    (prefixCache 10 17587) (prefixPartial 10 17587) = false := by
  decide +kernel

theorem node_context_10_17587_904925 : EJMOriginalGlobalDAGData.nodes 11 ⟨904925, by decide⟩ =
    .split (coordinate 10) (![⟨904809, by decide⟩,⟨904853, by decide⟩,⟨904924, by decide⟩,⟨109216, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17587_904925 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17587 ⟨904925, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17587
    ⟨904925, by decide⟩ (by decide) (![⟨904809, by decide⟩,⟨904853, by decide⟩,⟨904924, by decide⟩,⟨109216, by decide⟩]) unmarked_context_10_17587_904925 node_context_10_17587_904925
  intro a
  fin_cases a
  · exact context_11_70348_904809
  · exact context_11_70349_904853
  · exact context_11_70350_904924
  · exact context_11_70351_109216

theorem unmarked_context_9_4396_904926 : frontier 12 ⟨904926, by decide⟩
    (prefixCache 9 4396) (prefixPartial 9 4396) = false := by
  decide +kernel

theorem node_context_9_4396_904926 : EJMOriginalGlobalDAGData.nodes 12 ⟨904926, by decide⟩ =
    .split (coordinate 9) (![⟨903808, by decide⟩,⟨904459, by decide⟩,⟨904765, by decide⟩,⟨904925, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4396_904926 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4396 ⟨904926, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4396
    ⟨904926, by decide⟩ (by decide) (![⟨903808, by decide⟩,⟨904459, by decide⟩,⟨904765, by decide⟩,⟨904925, by decide⟩]) unmarked_context_9_4396_904926 node_context_9_4396_904926
  intro a
  fin_cases a
  · exact context_10_17584_903808
  · exact context_10_17585_904459
  · exact context_10_17586_904765
  · exact context_10_17587_904925

theorem selected_cut_34685 : selected 9 ⟨904964, by decide⟩
    (prefixPartial 12 281408) = some ⟨12, 2, 0, 904964, 281408, 1625, 65536⟩ := by
  decide +kernel

theorem context_12_281408_904964 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281408 ⟨904964, by decide⟩ :=
  accepted_of_selected 12 281408 ⟨904964, by decide⟩ ⟨12, 2, 0, 904964, 281408, 1625, 65536⟩
    (by decide) selected_cut_34685

theorem selected_cut_34686 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 281409) = some ⟨12, 1, 0, 896706, 281409, 1, 65536⟩ := by
  decide +kernel

theorem context_12_281409_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281409 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 281409 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 281409, 1, 65536⟩
    (by decide) selected_cut_34686

theorem selected_cut_34687 : selected 9 ⟨905013, by decide⟩
    (prefixPartial 12 281410) = some ⟨12, 2, 0, 905013, 281410, 2477, 65536⟩ := by
  decide +kernel

theorem context_12_281410_905013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281410 ⟨905013, by decide⟩ :=
  accepted_of_selected 12 281410 ⟨905013, by decide⟩ ⟨12, 2, 0, 905013, 281410, 2477, 65536⟩
    (by decide) selected_cut_34687

theorem selected_cut_34688 : selected 9 ⟨905069, by decide⟩
    (prefixPartial 12 281411) = some ⟨12, 2, 0, 905069, 281411, 2313, 65536⟩ := by
  decide +kernel

theorem context_12_281411_905069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281411 ⟨905069, by decide⟩ :=
  accepted_of_selected 12 281411 ⟨905069, by decide⟩ ⟨12, 2, 0, 905069, 281411, 2313, 65536⟩
    (by decide) selected_cut_34688

theorem unmarked_context_11_70352_905070 : frontier 10 ⟨905070, by decide⟩
    (prefixCache 11 70352) (prefixPartial 11 70352) = false := by
  decide +kernel

theorem node_context_11_70352_905070 : EJMOriginalGlobalDAGData.nodes 10 ⟨905070, by decide⟩ =
    .split (coordinate 11) (![⟨904964, by decide⟩,⟨896706, by decide⟩,⟨905013, by decide⟩,⟨905069, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70352_905070 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70352 ⟨905070, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70352
    ⟨905070, by decide⟩ (by decide) (![⟨904964, by decide⟩,⟨896706, by decide⟩,⟨905013, by decide⟩,⟨905069, by decide⟩]) unmarked_context_11_70352_905070 node_context_11_70352_905070
  intro a
  fin_cases a
  · exact context_12_281408_904964
  · exact context_12_281409_896706
  · exact context_12_281410_905013
  · exact context_12_281411_905069

theorem selected_cut_34689 : selected 9 ⟨905111, by decide⟩
    (prefixPartial 12 281412) = some ⟨12, 2, 0, 905111, 281412, 1673, 65536⟩ := by
  decide +kernel

theorem context_12_281412_905111 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281412 ⟨905111, by decide⟩ :=
  accepted_of_selected 12 281412 ⟨905111, by decide⟩ ⟨12, 2, 0, 905111, 281412, 1673, 65536⟩
    (by decide) selected_cut_34689

theorem selected_cut_34690 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 281413) = some ⟨12, 1, 0, 896706, 281413, 1, 65536⟩ := by
  decide +kernel

theorem context_12_281413_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281413 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 281413 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 281413, 1, 65536⟩
    (by decide) selected_cut_34690

theorem selected_cut_34691 : selected 9 ⟨905155, by decide⟩
    (prefixPartial 12 281414) = some ⟨12, 2, 0, 905155, 281414, 2309, 65536⟩ := by
  decide +kernel

theorem context_12_281414_905155 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281414 ⟨905155, by decide⟩ :=
  accepted_of_selected 12 281414 ⟨905155, by decide⟩ ⟨12, 2, 0, 905155, 281414, 2309, 65536⟩
    (by decide) selected_cut_34691

theorem selected_cut_34692 : selected 9 ⟨905201, by decide⟩
    (prefixPartial 12 281415) = some ⟨12, 2, 0, 905201, 281415, 2349, 65536⟩ := by
  decide +kernel

theorem context_12_281415_905201 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281415 ⟨905201, by decide⟩ :=
  accepted_of_selected 12 281415 ⟨905201, by decide⟩ ⟨12, 2, 0, 905201, 281415, 2349, 65536⟩
    (by decide) selected_cut_34692

theorem unmarked_context_11_70353_905202 : frontier 10 ⟨905202, by decide⟩
    (prefixCache 11 70353) (prefixPartial 11 70353) = false := by
  decide +kernel

theorem node_context_11_70353_905202 : EJMOriginalGlobalDAGData.nodes 10 ⟨905202, by decide⟩ =
    .split (coordinate 11) (![⟨905111, by decide⟩,⟨896706, by decide⟩,⟨905155, by decide⟩,⟨905201, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70353_905202 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70353 ⟨905202, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70353
    ⟨905202, by decide⟩ (by decide) (![⟨905111, by decide⟩,⟨896706, by decide⟩,⟨905155, by decide⟩,⟨905201, by decide⟩]) unmarked_context_11_70353_905202 node_context_11_70353_905202
  intro a
  fin_cases a
  · exact context_12_281412_905111
  · exact context_12_281413_896706
  · exact context_12_281414_905155
  · exact context_12_281415_905201

theorem selected_cut_34693 : selected 9 ⟨905253, by decide⟩
    (prefixPartial 12 281416) = some ⟨12, 2, 0, 905253, 281416, 2461, 65536⟩ := by
  decide +kernel

theorem context_12_281416_905253 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281416 ⟨905253, by decide⟩ :=
  accepted_of_selected 12 281416 ⟨905253, by decide⟩ ⟨12, 2, 0, 905253, 281416, 2461, 65536⟩
    (by decide) selected_cut_34693

theorem selected_cut_34694 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 281417) = some ⟨12, 1, 0, 896706, 281417, 1, 65536⟩ := by
  decide +kernel

theorem context_12_281417_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281417 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 281417 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 281417, 1, 65536⟩
    (by decide) selected_cut_34694

theorem selected_cut_34695 : selected 9 ⟨905297, by decide⟩
    (prefixPartial 12 281418) = some ⟨12, 2, 0, 905297, 281418, 2153, 65536⟩ := by
  decide +kernel

theorem context_12_281418_905297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281418 ⟨905297, by decide⟩ :=
  accepted_of_selected 12 281418 ⟨905297, by decide⟩ ⟨12, 2, 0, 905297, 281418, 2153, 65536⟩
    (by decide) selected_cut_34695

theorem selected_cut_34696 : selected 9 ⟨905356, by decide⟩
    (prefixPartial 12 281419) = some ⟨12, 2, 0, 905356, 281419, 2353, 65536⟩ := by
  decide +kernel

theorem context_12_281419_905356 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281419 ⟨905356, by decide⟩ :=
  accepted_of_selected 12 281419 ⟨905356, by decide⟩ ⟨12, 2, 0, 905356, 281419, 2353, 65536⟩
    (by decide) selected_cut_34696

theorem unmarked_context_11_70354_905357 : frontier 10 ⟨905357, by decide⟩
    (prefixCache 11 70354) (prefixPartial 11 70354) = false := by
  decide +kernel

theorem node_context_11_70354_905357 : EJMOriginalGlobalDAGData.nodes 10 ⟨905357, by decide⟩ =
    .split (coordinate 11) (![⟨905253, by decide⟩,⟨896706, by decide⟩,⟨905297, by decide⟩,⟨905356, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70354_905357 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70354 ⟨905357, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70354
    ⟨905357, by decide⟩ (by decide) (![⟨905253, by decide⟩,⟨896706, by decide⟩,⟨905297, by decide⟩,⟨905356, by decide⟩]) unmarked_context_11_70354_905357 node_context_11_70354_905357
  intro a
  fin_cases a
  · exact context_12_281416_905253
  · exact context_12_281417_896706
  · exact context_12_281418_905297
  · exact context_12_281419_905356

theorem selected_cut_34697 : selected 10 ⟨905414, by decide⟩
    (prefixPartial 11 70355) = some ⟨11, 2, 0, 905414, 70355, 2349, 262144⟩ := by
  decide +kernel

theorem context_11_70355_905414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70355 ⟨905414, by decide⟩ :=
  accepted_of_selected 11 70355 ⟨905414, by decide⟩ ⟨11, 2, 0, 905414, 70355, 2349, 262144⟩
    (by decide) selected_cut_34697

theorem unmarked_context_10_17588_905415 : frontier 11 ⟨905415, by decide⟩
    (prefixCache 10 17588) (prefixPartial 10 17588) = false := by
  decide +kernel

theorem node_context_10_17588_905415 : EJMOriginalGlobalDAGData.nodes 11 ⟨905415, by decide⟩ =
    .split (coordinate 10) (![⟨905070, by decide⟩,⟨905202, by decide⟩,⟨905357, by decide⟩,⟨905414, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17588_905415 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17588 ⟨905415, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17588
    ⟨905415, by decide⟩ (by decide) (![⟨905070, by decide⟩,⟨905202, by decide⟩,⟨905357, by decide⟩,⟨905414, by decide⟩]) unmarked_context_10_17588_905415 node_context_10_17588_905415
  intro a
  fin_cases a
  · exact context_11_70352_905070
  · exact context_11_70353_905202
  · exact context_11_70354_905357
  · exact context_11_70355_905414

theorem selected_cut_34698 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 17589) = some ⟨10, 1, 0, 893098, 17589, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_17589_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17589 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 17589 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 17589, 1, 1048576⟩
    (by decide) selected_cut_34698

theorem selected_cut_34699 : selected 10 ⟨905473, by decide⟩
    (prefixPartial 11 70360) = some ⟨11, 2, 0, 905473, 70360, 3225, 262144⟩ := by
  decide +kernel

theorem context_11_70360_905473 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70360 ⟨905473, by decide⟩ :=
  accepted_of_selected 11 70360 ⟨905473, by decide⟩ ⟨11, 2, 0, 905473, 70360, 3225, 262144⟩
    (by decide) selected_cut_34699

theorem selected_cut_34700 : selected 10 ⟨905535, by decide⟩
    (prefixPartial 11 70361) = some ⟨11, 2, 0, 905535, 70361, 3113, 262144⟩ := by
  decide +kernel

theorem context_11_70361_905535 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70361 ⟨905535, by decide⟩ :=
  accepted_of_selected 11 70361 ⟨905535, by decide⟩ ⟨11, 2, 0, 905535, 70361, 3113, 262144⟩
    (by decide) selected_cut_34700

theorem selected_cut_34701 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 70362) = some ⟨11, 1, 0, 900587, 70362, 1, 262144⟩ := by
  decide +kernel

theorem context_11_70362_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70362 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 70362 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 70362, 1, 262144⟩
    (by decide) selected_cut_34701

theorem selected_cut_34702 : selected 10 ⟨905588, by decide⟩
    (prefixPartial 11 70363) = some ⟨11, 2, 0, 905588, 70363, 2349, 262144⟩ := by
  decide +kernel

theorem context_11_70363_905588 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70363 ⟨905588, by decide⟩ :=
  accepted_of_selected 11 70363 ⟨905588, by decide⟩ ⟨11, 2, 0, 905588, 70363, 2349, 262144⟩
    (by decide) selected_cut_34702

theorem unmarked_context_10_17590_905589 : frontier 11 ⟨905589, by decide⟩
    (prefixCache 10 17590) (prefixPartial 10 17590) = false := by
  decide +kernel

theorem node_context_10_17590_905589 : EJMOriginalGlobalDAGData.nodes 11 ⟨905589, by decide⟩ =
    .split (coordinate 10) (![⟨905473, by decide⟩,⟨905535, by decide⟩,⟨900587, by decide⟩,⟨905588, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17590_905589 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17590 ⟨905589, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17590
    ⟨905589, by decide⟩ (by decide) (![⟨905473, by decide⟩,⟨905535, by decide⟩,⟨900587, by decide⟩,⟨905588, by decide⟩]) unmarked_context_10_17590_905589 node_context_10_17590_905589
  intro a
  fin_cases a
  · exact context_11_70360_905473
  · exact context_11_70361_905535
  · exact context_11_70362_900587
  · exact context_11_70363_905588

theorem selected_cut_34703 : selected 10 ⟨905613, by decide⟩
    (prefixPartial 11 70364) = some ⟨11, 2, 0, 905613, 70364, 1249, 262144⟩ := by
  decide +kernel

theorem context_11_70364_905613 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70364 ⟨905613, by decide⟩ :=
  accepted_of_selected 11 70364 ⟨905613, by decide⟩ ⟨11, 2, 0, 905613, 70364, 1249, 262144⟩
    (by decide) selected_cut_34703

theorem selected_cut_34704 : selected 10 ⟨905634, by decide⟩
    (prefixPartial 11 70365) = some ⟨11, 2, 0, 905634, 70365, 1101, 262144⟩ := by
  decide +kernel

theorem context_11_70365_905634 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70365 ⟨905634, by decide⟩ :=
  accepted_of_selected 11 70365 ⟨905634, by decide⟩ ⟨11, 2, 0, 905634, 70365, 1101, 262144⟩
    (by decide) selected_cut_34704

theorem selected_cut_34705 : selected 10 ⟨905680, by decide⟩
    (prefixPartial 11 70366) = some ⟨11, 2, 0, 905680, 70366, 2065, 262144⟩ := by
  decide +kernel

theorem context_11_70366_905680 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70366 ⟨905680, by decide⟩ :=
  accepted_of_selected 11 70366 ⟨905680, by decide⟩ ⟨11, 2, 0, 905680, 70366, 2065, 262144⟩
    (by decide) selected_cut_34705

theorem selected_cut_34706 : selected 10 ⟨109216, by decide⟩
    (prefixPartial 11 70367) = some ⟨11, 2, 0, 109216, 70367, 5, 262144⟩ := by
  decide +kernel

theorem context_11_70367_109216 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70367 ⟨109216, by decide⟩ :=
  accepted_of_selected 11 70367 ⟨109216, by decide⟩ ⟨11, 2, 0, 109216, 70367, 5, 262144⟩
    (by decide) selected_cut_34706

theorem unmarked_context_10_17591_905681 : frontier 11 ⟨905681, by decide⟩
    (prefixCache 10 17591) (prefixPartial 10 17591) = false := by
  decide +kernel

theorem node_context_10_17591_905681 : EJMOriginalGlobalDAGData.nodes 11 ⟨905681, by decide⟩ =
    .split (coordinate 10) (![⟨905613, by decide⟩,⟨905634, by decide⟩,⟨905680, by decide⟩,⟨109216, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17591_905681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17591 ⟨905681, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17591
    ⟨905681, by decide⟩ (by decide) (![⟨905613, by decide⟩,⟨905634, by decide⟩,⟨905680, by decide⟩,⟨109216, by decide⟩]) unmarked_context_10_17591_905681 node_context_10_17591_905681
  intro a
  fin_cases a
  · exact context_11_70364_905613
  · exact context_11_70365_905634
  · exact context_11_70366_905680
  · exact context_11_70367_109216

theorem unmarked_context_9_4397_905682 : frontier 12 ⟨905682, by decide⟩
    (prefixCache 9 4397) (prefixPartial 9 4397) = false := by
  decide +kernel

theorem node_context_9_4397_905682 : EJMOriginalGlobalDAGData.nodes 12 ⟨905682, by decide⟩ =
    .split (coordinate 9) (![⟨905415, by decide⟩,⟨893098, by decide⟩,⟨905589, by decide⟩,⟨905681, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4397_905682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4397 ⟨905682, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4397
    ⟨905682, by decide⟩ (by decide) (![⟨905415, by decide⟩,⟨893098, by decide⟩,⟨905589, by decide⟩,⟨905681, by decide⟩]) unmarked_context_9_4397_905682 node_context_9_4397_905682
  intro a
  fin_cases a
  · exact context_10_17588_905415
  · exact context_10_17589_893098
  · exact context_10_17590_905589
  · exact context_10_17591_905681

theorem selected_cut_34707 : selected 9 ⟨905706, by decide⟩
    (prefixPartial 12 281472) = some ⟨12, 2, 0, 905706, 281472, 1653, 65536⟩ := by
  decide +kernel

theorem context_12_281472_905706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281472 ⟨905706, by decide⟩ :=
  accepted_of_selected 12 281472 ⟨905706, by decide⟩ ⟨12, 2, 0, 905706, 281472, 1653, 65536⟩
    (by decide) selected_cut_34707

theorem selected_cut_34708 : selected 9 ⟨905730, by decide⟩
    (prefixPartial 12 281473) = some ⟨12, 2, 0, 905730, 281473, 1549, 65536⟩ := by
  decide +kernel

theorem context_12_281473_905730 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281473 ⟨905730, by decide⟩ :=
  accepted_of_selected 12 281473 ⟨905730, by decide⟩ ⟨12, 2, 0, 905730, 281473, 1549, 65536⟩
    (by decide) selected_cut_34708

theorem selected_cut_34709 : selected 9 ⟨905751, by decide⟩
    (prefixPartial 12 281474) = some ⟨12, 2, 0, 905751, 281474, 1541, 65536⟩ := by
  decide +kernel

theorem context_12_281474_905751 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281474 ⟨905751, by decide⟩ :=
  accepted_of_selected 12 281474 ⟨905751, by decide⟩ ⟨12, 2, 0, 905751, 281474, 1541, 65536⟩
    (by decide) selected_cut_34709

theorem selected_cut_34710 : selected 9 ⟨905769, by decide⟩
    (prefixPartial 12 281475) = some ⟨12, 2, 0, 905769, 281475, 1337, 65536⟩ := by
  decide +kernel

theorem context_12_281475_905769 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281475 ⟨905769, by decide⟩ :=
  accepted_of_selected 12 281475 ⟨905769, by decide⟩ ⟨12, 2, 0, 905769, 281475, 1337, 65536⟩
    (by decide) selected_cut_34710

theorem unmarked_context_11_70368_905770 : frontier 10 ⟨905770, by decide⟩
    (prefixCache 11 70368) (prefixPartial 11 70368) = false := by
  decide +kernel

theorem node_context_11_70368_905770 : EJMOriginalGlobalDAGData.nodes 10 ⟨905770, by decide⟩ =
    .split (coordinate 11) (![⟨905706, by decide⟩,⟨905730, by decide⟩,⟨905751, by decide⟩,⟨905769, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70368_905770 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70368 ⟨905770, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70368
    ⟨905770, by decide⟩ (by decide) (![⟨905706, by decide⟩,⟨905730, by decide⟩,⟨905751, by decide⟩,⟨905769, by decide⟩]) unmarked_context_11_70368_905770 node_context_11_70368_905770
  intro a
  fin_cases a
  · exact context_12_281472_905706
  · exact context_12_281473_905730
  · exact context_12_281474_905751
  · exact context_12_281475_905769

theorem selected_cut_34711 : selected 9 ⟨905801, by decide⟩
    (prefixPartial 12 281476) = some ⟨12, 2, 0, 905801, 281476, 1765, 65536⟩ := by
  decide +kernel

theorem context_12_281476_905801 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281476 ⟨905801, by decide⟩ :=
  accepted_of_selected 12 281476 ⟨905801, by decide⟩ ⟨12, 2, 0, 905801, 281476, 1765, 65536⟩
    (by decide) selected_cut_34711

theorem selected_cut_34712 : selected 9 ⟨905827, by decide⟩
    (prefixPartial 12 281477) = some ⟨12, 2, 0, 905827, 281477, 1537, 65536⟩ := by
  decide +kernel

theorem context_12_281477_905827 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281477 ⟨905827, by decide⟩ :=
  accepted_of_selected 12 281477 ⟨905827, by decide⟩ ⟨12, 2, 0, 905827, 281477, 1537, 65536⟩
    (by decide) selected_cut_34712

theorem selected_cut_34713 : selected 9 ⟨905852, by decide⟩
    (prefixPartial 12 281478) = some ⟨12, 2, 0, 905852, 281478, 1561, 65536⟩ := by
  decide +kernel

theorem context_12_281478_905852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281478 ⟨905852, by decide⟩ :=
  accepted_of_selected 12 281478 ⟨905852, by decide⟩ ⟨12, 2, 0, 905852, 281478, 1561, 65536⟩
    (by decide) selected_cut_34713

theorem selected_cut_34714 : selected 9 ⟨905875, by decide⟩
    (prefixPartial 12 281479) = some ⟨12, 2, 0, 905875, 281479, 1513, 65536⟩ := by
  decide +kernel

theorem context_12_281479_905875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281479 ⟨905875, by decide⟩ :=
  accepted_of_selected 12 281479 ⟨905875, by decide⟩ ⟨12, 2, 0, 905875, 281479, 1513, 65536⟩
    (by decide) selected_cut_34714

theorem unmarked_context_11_70369_905876 : frontier 10 ⟨905876, by decide⟩
    (prefixCache 11 70369) (prefixPartial 11 70369) = false := by
  decide +kernel

theorem node_context_11_70369_905876 : EJMOriginalGlobalDAGData.nodes 10 ⟨905876, by decide⟩ =
    .split (coordinate 11) (![⟨905801, by decide⟩,⟨905827, by decide⟩,⟨905852, by decide⟩,⟨905875, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70369_905876 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70369 ⟨905876, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70369
    ⟨905876, by decide⟩ (by decide) (![⟨905801, by decide⟩,⟨905827, by decide⟩,⟨905852, by decide⟩,⟨905875, by decide⟩]) unmarked_context_11_70369_905876 node_context_11_70369_905876
  intro a
  fin_cases a
  · exact context_12_281476_905801
  · exact context_12_281477_905827
  · exact context_12_281478_905852
  · exact context_12_281479_905875

theorem selected_cut_34715 : selected 9 ⟨905911, by decide⟩
    (prefixPartial 12 281480) = some ⟨12, 2, 0, 905911, 281480, 1705, 65536⟩ := by
  decide +kernel

theorem context_12_281480_905911 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281480 ⟨905911, by decide⟩ :=
  accepted_of_selected 12 281480 ⟨905911, by decide⟩ ⟨12, 2, 0, 905911, 281480, 1705, 65536⟩
    (by decide) selected_cut_34715

theorem selected_cut_34716 : selected 9 ⟨905936, by decide⟩
    (prefixPartial 12 281481) = some ⟨12, 2, 0, 905936, 281481, 1365, 65536⟩ := by
  decide +kernel

theorem context_12_281481_905936 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281481 ⟨905936, by decide⟩ :=
  accepted_of_selected 12 281481 ⟨905936, by decide⟩ ⟨12, 2, 0, 905936, 281481, 1365, 65536⟩
    (by decide) selected_cut_34716

theorem selected_cut_34717 : selected 9 ⟨905964, by decide⟩
    (prefixPartial 12 281482) = some ⟨12, 2, 0, 905964, 281482, 1393, 65536⟩ := by
  decide +kernel

theorem context_12_281482_905964 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281482 ⟨905964, by decide⟩ :=
  accepted_of_selected 12 281482 ⟨905964, by decide⟩ ⟨12, 2, 0, 905964, 281482, 1393, 65536⟩
    (by decide) selected_cut_34717

theorem selected_cut_34718 : selected 9 ⟨905994, by decide⟩
    (prefixPartial 12 281483) = some ⟨12, 2, 0, 905994, 281483, 1377, 65536⟩ := by
  decide +kernel

theorem context_12_281483_905994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281483 ⟨905994, by decide⟩ :=
  accepted_of_selected 12 281483 ⟨905994, by decide⟩ ⟨12, 2, 0, 905994, 281483, 1377, 65536⟩
    (by decide) selected_cut_34718

theorem unmarked_context_11_70370_905995 : frontier 10 ⟨905995, by decide⟩
    (prefixCache 11 70370) (prefixPartial 11 70370) = false := by
  decide +kernel

theorem node_context_11_70370_905995 : EJMOriginalGlobalDAGData.nodes 10 ⟨905995, by decide⟩ =
    .split (coordinate 11) (![⟨905911, by decide⟩,⟨905936, by decide⟩,⟨905964, by decide⟩,⟨905994, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70370_905995 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70370 ⟨905995, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70370
    ⟨905995, by decide⟩ (by decide) (![⟨905911, by decide⟩,⟨905936, by decide⟩,⟨905964, by decide⟩,⟨905994, by decide⟩]) unmarked_context_11_70370_905995 node_context_11_70370_905995
  intro a
  fin_cases a
  · exact context_12_281480_905911
  · exact context_12_281481_905936
  · exact context_12_281482_905964
  · exact context_12_281483_905994

theorem selected_cut_34719 : selected 9 ⟨906023, by decide⟩
    (prefixPartial 12 281484) = some ⟨12, 2, 0, 906023, 281484, 1589, 65536⟩ := by
  decide +kernel

theorem context_12_281484_906023 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281484 ⟨906023, by decide⟩ :=
  accepted_of_selected 12 281484 ⟨906023, by decide⟩ ⟨12, 2, 0, 906023, 281484, 1589, 65536⟩
    (by decide) selected_cut_34719

theorem selected_cut_34720 : selected 9 ⟨906052, by decide⟩
    (prefixPartial 12 281485) = some ⟨12, 2, 0, 906052, 281485, 1397, 65536⟩ := by
  decide +kernel

theorem context_12_281485_906052 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281485 ⟨906052, by decide⟩ :=
  accepted_of_selected 12 281485 ⟨906052, by decide⟩ ⟨12, 2, 0, 906052, 281485, 1397, 65536⟩
    (by decide) selected_cut_34720

theorem selected_cut_34721 : selected 9 ⟨906079, by decide⟩
    (prefixPartial 12 281486) = some ⟨12, 2, 0, 906079, 281486, 1377, 65536⟩ := by
  decide +kernel

theorem context_12_281486_906079 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281486 ⟨906079, by decide⟩ :=
  accepted_of_selected 12 281486 ⟨906079, by decide⟩ ⟨12, 2, 0, 906079, 281486, 1377, 65536⟩
    (by decide) selected_cut_34721

theorem selected_cut_34722 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 281487) = some ⟨12, 1, 0, 903806, 281487, 1, 65536⟩ := by
  decide +kernel

theorem context_12_281487_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281487 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 281487 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 281487, 1, 65536⟩
    (by decide) selected_cut_34722

theorem unmarked_context_11_70371_906080 : frontier 10 ⟨906080, by decide⟩
    (prefixCache 11 70371) (prefixPartial 11 70371) = false := by
  decide +kernel

theorem node_context_11_70371_906080 : EJMOriginalGlobalDAGData.nodes 10 ⟨906080, by decide⟩ =
    .split (coordinate 11) (![⟨906023, by decide⟩,⟨906052, by decide⟩,⟨906079, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70371_906080 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70371 ⟨906080, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70371
    ⟨906080, by decide⟩ (by decide) (![⟨906023, by decide⟩,⟨906052, by decide⟩,⟨906079, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_70371_906080 node_context_11_70371_906080
  intro a
  fin_cases a
  · exact context_12_281484_906023
  · exact context_12_281485_906052
  · exact context_12_281486_906079
  · exact context_12_281487_903806

theorem unmarked_context_10_17592_906081 : frontier 11 ⟨906081, by decide⟩
    (prefixCache 10 17592) (prefixPartial 10 17592) = false := by
  decide +kernel

theorem node_context_10_17592_906081 : EJMOriginalGlobalDAGData.nodes 11 ⟨906081, by decide⟩ =
    .split (coordinate 10) (![⟨905770, by decide⟩,⟨905876, by decide⟩,⟨905995, by decide⟩,⟨906080, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17592_906081 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17592 ⟨906081, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17592
    ⟨906081, by decide⟩ (by decide) (![⟨905770, by decide⟩,⟨905876, by decide⟩,⟨905995, by decide⟩,⟨906080, by decide⟩]) unmarked_context_10_17592_906081 node_context_10_17592_906081
  intro a
  fin_cases a
  · exact context_11_70368_905770
  · exact context_11_70369_905876
  · exact context_11_70370_905995
  · exact context_11_70371_906080

theorem selected_cut_34723 : selected 9 ⟨906108, by decide⟩
    (prefixPartial 12 281488) = some ⟨12, 2, 0, 906108, 281488, 1257, 65536⟩ := by
  decide +kernel

theorem context_12_281488_906108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281488 ⟨906108, by decide⟩ :=
  accepted_of_selected 12 281488 ⟨906108, by decide⟩ ⟨12, 2, 0, 906108, 281488, 1257, 65536⟩
    (by decide) selected_cut_34723

theorem selected_cut_34724 : selected 9 ⟨906134, by decide⟩
    (prefixPartial 12 281489) = some ⟨12, 2, 0, 906134, 281489, 1245, 65536⟩ := by
  decide +kernel

theorem context_12_281489_906134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281489 ⟨906134, by decide⟩ :=
  accepted_of_selected 12 281489 ⟨906134, by decide⟩ ⟨12, 2, 0, 906134, 281489, 1245, 65536⟩
    (by decide) selected_cut_34724

theorem selected_cut_34725 : selected 9 ⟨906161, by decide⟩
    (prefixPartial 12 281490) = some ⟨12, 2, 0, 906161, 281490, 1393, 65536⟩ := by
  decide +kernel

theorem context_12_281490_906161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281490 ⟨906161, by decide⟩ :=
  accepted_of_selected 12 281490 ⟨906161, by decide⟩ ⟨12, 2, 0, 906161, 281490, 1393, 65536⟩
    (by decide) selected_cut_34725

theorem selected_cut_34726 : selected 9 ⟨906182, by decide⟩
    (prefixPartial 12 281491) = some ⟨12, 2, 0, 906182, 281491, 1137, 65536⟩ := by
  decide +kernel

theorem context_12_281491_906182 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281491 ⟨906182, by decide⟩ :=
  accepted_of_selected 12 281491 ⟨906182, by decide⟩ ⟨12, 2, 0, 906182, 281491, 1137, 65536⟩
    (by decide) selected_cut_34726

theorem unmarked_context_11_70372_906183 : frontier 10 ⟨906183, by decide⟩
    (prefixCache 11 70372) (prefixPartial 11 70372) = false := by
  decide +kernel

theorem node_context_11_70372_906183 : EJMOriginalGlobalDAGData.nodes 10 ⟨906183, by decide⟩ =
    .split (coordinate 11) (![⟨906108, by decide⟩,⟨906134, by decide⟩,⟨906161, by decide⟩,⟨906182, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70372_906183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70372 ⟨906183, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70372
    ⟨906183, by decide⟩ (by decide) (![⟨906108, by decide⟩,⟨906134, by decide⟩,⟨906161, by decide⟩,⟨906182, by decide⟩]) unmarked_context_11_70372_906183 node_context_11_70372_906183
  intro a
  fin_cases a
  · exact context_12_281488_906108
  · exact context_12_281489_906134
  · exact context_12_281490_906161
  · exact context_12_281491_906182

theorem selected_cut_34727 : selected 9 ⟨906209, by decide⟩
    (prefixPartial 12 281492) = some ⟨12, 2, 0, 906209, 281492, 1145, 65536⟩ := by
  decide +kernel

theorem context_12_281492_906209 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281492 ⟨906209, by decide⟩ :=
  accepted_of_selected 12 281492 ⟨906209, by decide⟩ ⟨12, 2, 0, 906209, 281492, 1145, 65536⟩
    (by decide) selected_cut_34727

theorem selected_cut_34728 : selected 9 ⟨906226, by decide⟩
    (prefixPartial 12 281493) = some ⟨12, 2, 0, 906226, 281493, 1001, 65536⟩ := by
  decide +kernel

theorem context_12_281493_906226 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281493 ⟨906226, by decide⟩ :=
  accepted_of_selected 12 281493 ⟨906226, by decide⟩ ⟨12, 2, 0, 906226, 281493, 1001, 65536⟩
    (by decide) selected_cut_34728

theorem selected_cut_34729 : selected 9 ⟨906251, by decide⟩
    (prefixPartial 12 281494) = some ⟨12, 2, 0, 906251, 281494, 1109, 65536⟩ := by
  decide +kernel

theorem context_12_281494_906251 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281494 ⟨906251, by decide⟩ :=
  accepted_of_selected 12 281494 ⟨906251, by decide⟩ ⟨12, 2, 0, 906251, 281494, 1109, 65536⟩
    (by decide) selected_cut_34729

theorem selected_cut_34730 : selected 9 ⟨906273, by decide⟩
    (prefixPartial 12 281495) = some ⟨12, 2, 0, 906273, 281495, 1053, 65536⟩ := by
  decide +kernel

theorem context_12_281495_906273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281495 ⟨906273, by decide⟩ :=
  accepted_of_selected 12 281495 ⟨906273, by decide⟩ ⟨12, 2, 0, 906273, 281495, 1053, 65536⟩
    (by decide) selected_cut_34730

theorem unmarked_context_11_70373_906274 : frontier 10 ⟨906274, by decide⟩
    (prefixCache 11 70373) (prefixPartial 11 70373) = false := by
  decide +kernel

theorem node_context_11_70373_906274 : EJMOriginalGlobalDAGData.nodes 10 ⟨906274, by decide⟩ =
    .split (coordinate 11) (![⟨906209, by decide⟩,⟨906226, by decide⟩,⟨906251, by decide⟩,⟨906273, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70373_906274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70373 ⟨906274, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70373
    ⟨906274, by decide⟩ (by decide) (![⟨906209, by decide⟩,⟨906226, by decide⟩,⟨906251, by decide⟩,⟨906273, by decide⟩]) unmarked_context_11_70373_906274 node_context_11_70373_906274
  intro a
  fin_cases a
  · exact context_12_281492_906209
  · exact context_12_281493_906226
  · exact context_12_281494_906251
  · exact context_12_281495_906273

theorem selected_cut_34731 : selected 9 ⟨906297, by decide⟩
    (prefixPartial 12 281496) = some ⟨12, 2, 0, 906297, 281496, 1089, 65536⟩ := by
  decide +kernel

theorem context_12_281496_906297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281496 ⟨906297, by decide⟩ :=
  accepted_of_selected 12 281496 ⟨906297, by decide⟩ ⟨12, 2, 0, 906297, 281496, 1089, 65536⟩
    (by decide) selected_cut_34731

theorem selected_cut_34732 : selected 9 ⟨906323, by decide⟩
    (prefixPartial 12 281497) = some ⟨12, 2, 0, 906323, 281497, 1009, 65536⟩ := by
  decide +kernel

theorem context_12_281497_906323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281497 ⟨906323, by decide⟩ :=
  accepted_of_selected 12 281497 ⟨906323, by decide⟩ ⟨12, 2, 0, 906323, 281497, 1009, 65536⟩
    (by decide) selected_cut_34732

theorem selected_cut_34733 : selected 9 ⟨906344, by decide⟩
    (prefixPartial 12 281498) = some ⟨12, 2, 0, 906344, 281498, 1013, 65536⟩ := by
  decide +kernel

theorem context_12_281498_906344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281498 ⟨906344, by decide⟩ :=
  accepted_of_selected 12 281498 ⟨906344, by decide⟩ ⟨12, 2, 0, 906344, 281498, 1013, 65536⟩
    (by decide) selected_cut_34733

theorem selected_cut_34734 : selected 9 ⟨906363, by decide⟩
    (prefixPartial 12 281499) = some ⟨12, 2, 0, 906363, 281499, 989, 65536⟩ := by
  decide +kernel

theorem context_12_281499_906363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 281499 ⟨906363, by decide⟩ :=
  accepted_of_selected 12 281499 ⟨906363, by decide⟩ ⟨12, 2, 0, 906363, 281499, 989, 65536⟩
    (by decide) selected_cut_34734

theorem unmarked_context_11_70374_906364 : frontier 10 ⟨906364, by decide⟩
    (prefixCache 11 70374) (prefixPartial 11 70374) = false := by
  decide +kernel

theorem node_context_11_70374_906364 : EJMOriginalGlobalDAGData.nodes 10 ⟨906364, by decide⟩ =
    .split (coordinate 11) (![⟨906297, by decide⟩,⟨906323, by decide⟩,⟨906344, by decide⟩,⟨906363, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70374_906364 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70374 ⟨906364, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70374
    ⟨906364, by decide⟩ (by decide) (![⟨906297, by decide⟩,⟨906323, by decide⟩,⟨906344, by decide⟩,⟨906363, by decide⟩]) unmarked_context_11_70374_906364 node_context_11_70374_906364
  intro a
  fin_cases a
  · exact context_12_281496_906297
  · exact context_12_281497_906323
  · exact context_12_281498_906344
  · exact context_12_281499_906363

theorem selected_cut_34735 : selected 10 ⟨906430, by decide⟩
    (prefixPartial 11 70375) = some ⟨11, 2, 0, 906430, 70375, 2817, 262144⟩ := by
  decide +kernel

theorem context_11_70375_906430 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70375 ⟨906430, by decide⟩ :=
  accepted_of_selected 11 70375 ⟨906430, by decide⟩ ⟨11, 2, 0, 906430, 70375, 2817, 262144⟩
    (by decide) selected_cut_34735

theorem unmarked_context_10_17593_906431 : frontier 11 ⟨906431, by decide⟩
    (prefixCache 10 17593) (prefixPartial 10 17593) = false := by
  decide +kernel

theorem node_context_10_17593_906431 : EJMOriginalGlobalDAGData.nodes 11 ⟨906431, by decide⟩ =
    .split (coordinate 10) (![⟨906183, by decide⟩,⟨906274, by decide⟩,⟨906364, by decide⟩,⟨906430, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17593_906431 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17593 ⟨906431, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17593
    ⟨906431, by decide⟩ (by decide) (![⟨906183, by decide⟩,⟨906274, by decide⟩,⟨906364, by decide⟩,⟨906430, by decide⟩]) unmarked_context_10_17593_906431 node_context_10_17593_906431
  intro a
  fin_cases a
  · exact context_11_70372_906183
  · exact context_11_70373_906274
  · exact context_11_70374_906364
  · exact context_11_70375_906430

theorem selected_cut_34736 : selected 10 ⟨906498, by decide⟩
    (prefixPartial 11 70376) = some ⟨11, 2, 0, 906498, 70376, 2697, 262144⟩ := by
  decide +kernel

theorem context_11_70376_906498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70376 ⟨906498, by decide⟩ :=
  accepted_of_selected 11 70376 ⟨906498, by decide⟩ ⟨11, 2, 0, 906498, 70376, 2697, 262144⟩
    (by decide) selected_cut_34736

theorem selected_cut_34737 : selected 10 ⟨906565, by decide⟩
    (prefixPartial 11 70377) = some ⟨11, 2, 0, 906565, 70377, 2693, 262144⟩ := by
  decide +kernel

theorem context_11_70377_906565 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70377 ⟨906565, by decide⟩ :=
  accepted_of_selected 11 70377 ⟨906565, by decide⟩ ⟨11, 2, 0, 906565, 70377, 2693, 262144⟩
    (by decide) selected_cut_34737

theorem selected_cut_34738 : selected 10 ⟨906566, by decide⟩
    (prefixPartial 11 70378) = some ⟨11, 1, 0, 906566, 70378, 1, 262144⟩ := by
  decide +kernel

theorem context_11_70378_906566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70378 ⟨906566, by decide⟩ :=
  accepted_of_selected 11 70378 ⟨906566, by decide⟩ ⟨11, 1, 0, 906566, 70378, 1, 262144⟩
    (by decide) selected_cut_34738

theorem selected_cut_34739 : selected 10 ⟨906617, by decide⟩
    (prefixPartial 11 70379) = some ⟨11, 2, 0, 906617, 70379, 1729, 262144⟩ := by
  decide +kernel

theorem context_11_70379_906617 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70379 ⟨906617, by decide⟩ :=
  accepted_of_selected 11 70379 ⟨906617, by decide⟩ ⟨11, 2, 0, 906617, 70379, 1729, 262144⟩
    (by decide) selected_cut_34739

theorem unmarked_context_10_17594_906618 : frontier 11 ⟨906618, by decide⟩
    (prefixCache 10 17594) (prefixPartial 10 17594) = false := by
  decide +kernel

theorem node_context_10_17594_906618 : EJMOriginalGlobalDAGData.nodes 11 ⟨906618, by decide⟩ =
    .split (coordinate 10) (![⟨906498, by decide⟩,⟨906565, by decide⟩,⟨906566, by decide⟩,⟨906617, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17594_906618 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17594 ⟨906618, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17594
    ⟨906618, by decide⟩ (by decide) (![⟨906498, by decide⟩,⟨906565, by decide⟩,⟨906566, by decide⟩,⟨906617, by decide⟩]) unmarked_context_10_17594_906618 node_context_10_17594_906618
  intro a
  fin_cases a
  · exact context_11_70376_906498
  · exact context_11_70377_906565
  · exact context_11_70378_906566
  · exact context_11_70379_906617

theorem selected_cut_34740 : selected 10 ⟨906679, by decide⟩
    (prefixPartial 11 70380) = some ⟨11, 2, 0, 906679, 70380, 2165, 262144⟩ := by
  decide +kernel

theorem context_11_70380_906679 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70380 ⟨906679, by decide⟩ :=
  accepted_of_selected 11 70380 ⟨906679, by decide⟩ ⟨11, 2, 0, 906679, 70380, 2165, 262144⟩
    (by decide) selected_cut_34740

theorem selected_cut_34741 : selected 10 ⟨906720, by decide⟩
    (prefixPartial 11 70381) = some ⟨11, 2, 0, 906720, 70381, 1665, 262144⟩ := by
  decide +kernel

theorem context_11_70381_906720 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70381 ⟨906720, by decide⟩ :=
  accepted_of_selected 11 70381 ⟨906720, by decide⟩ ⟨11, 2, 0, 906720, 70381, 1665, 262144⟩
    (by decide) selected_cut_34741

theorem selected_cut_34742 : selected 10 ⟨906755, by decide⟩
    (prefixPartial 11 70382) = some ⟨11, 2, 0, 906755, 70382, 1129, 262144⟩ := by
  decide +kernel

theorem context_11_70382_906755 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70382 ⟨906755, by decide⟩ :=
  accepted_of_selected 11 70382 ⟨906755, by decide⟩ ⟨11, 2, 0, 906755, 70382, 1129, 262144⟩
    (by decide) selected_cut_34742

theorem selected_cut_34743 : selected 10 ⟨906774, by decide⟩
    (prefixPartial 11 70383) = some ⟨11, 2, 0, 906774, 70383, 473, 262144⟩ := by
  decide +kernel

theorem context_11_70383_906774 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70383 ⟨906774, by decide⟩ :=
  accepted_of_selected 11 70383 ⟨906774, by decide⟩ ⟨11, 2, 0, 906774, 70383, 473, 262144⟩
    (by decide) selected_cut_34743

theorem unmarked_context_10_17595_906775 : frontier 11 ⟨906775, by decide⟩
    (prefixCache 10 17595) (prefixPartial 10 17595) = false := by
  decide +kernel

theorem node_context_10_17595_906775 : EJMOriginalGlobalDAGData.nodes 11 ⟨906775, by decide⟩ =
    .split (coordinate 10) (![⟨906679, by decide⟩,⟨906720, by decide⟩,⟨906755, by decide⟩,⟨906774, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_17595_906775 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 17595 ⟨906775, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 17595
    ⟨906775, by decide⟩ (by decide) (![⟨906679, by decide⟩,⟨906720, by decide⟩,⟨906755, by decide⟩,⟨906774, by decide⟩]) unmarked_context_10_17595_906775 node_context_10_17595_906775
  intro a
  fin_cases a
  · exact context_11_70380_906679
  · exact context_11_70381_906720
  · exact context_11_70382_906755
  · exact context_11_70383_906774

theorem unmarked_context_9_4398_906776 : frontier 12 ⟨906776, by decide⟩
    (prefixCache 9 4398) (prefixPartial 9 4398) = false := by
  decide +kernel

theorem node_context_9_4398_906776 : EJMOriginalGlobalDAGData.nodes 12 ⟨906776, by decide⟩ =
    .split (coordinate 9) (![⟨906081, by decide⟩,⟨906431, by decide⟩,⟨906618, by decide⟩,⟨906775, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4398_906776 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4398 ⟨906776, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4398
    ⟨906776, by decide⟩ (by decide) (![⟨906081, by decide⟩,⟨906431, by decide⟩,⟨906618, by decide⟩,⟨906775, by decide⟩]) unmarked_context_9_4398_906776 node_context_9_4398_906776
  intro a
  fin_cases a
  · exact context_10_17592_906081
  · exact context_10_17593_906431
  · exact context_10_17594_906618
  · exact context_10_17595_906775

theorem selected_cut_34744 : selected 12 ⟨116309, by decide⟩
    (prefixPartial 9 4399) = some ⟨9, 1, 0, 116309, 4399, 1, 4194304⟩ := by
  decide +kernel

theorem context_9_4399_116309 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4399 ⟨116309, by decide⟩ :=
  accepted_of_selected 9 4399 ⟨116309, by decide⟩ ⟨9, 1, 0, 116309, 4399, 1, 4194304⟩
    (by decide) selected_cut_34744

theorem unmarked_context_8_1099_906777 : frontier 13 ⟨906777, by decide⟩
    (prefixCache 8 1099) (prefixPartial 8 1099) = false := by
  decide +kernel

theorem node_context_8_1099_906777 : EJMOriginalGlobalDAGData.nodes 13 ⟨906777, by decide⟩ =
    .split (coordinate 8) (![⟨904926, by decide⟩,⟨905682, by decide⟩,⟨906776, by decide⟩,⟨116309, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1099_906777 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1099 ⟨906777, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1099
    ⟨906777, by decide⟩ (by decide) (![⟨904926, by decide⟩,⟨905682, by decide⟩,⟨906776, by decide⟩,⟨116309, by decide⟩]) unmarked_context_8_1099_906777 node_context_8_1099_906777
  intro a
  fin_cases a
  · exact context_9_4396_904926
  · exact context_9_4397_905682
  · exact context_9_4398_906776
  · exact context_9_4399_116309

theorem unmarked_context_7_274_906778 : frontier 14 ⟨906778, by decide⟩
    (prefixCache 7 274) (prefixPartial 7 274) = false := by
  decide +kernel

theorem node_context_7_274_906778 : EJMOriginalGlobalDAGData.nodes 14 ⟨906778, by decide⟩ =
    .split (coordinate 7) (![⟨14300, by decide⟩,⟨14300, by decide⟩,⟨902808, by decide⟩,⟨906777, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_274_906778 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 274 ⟨906778, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 274
    ⟨906778, by decide⟩ (by decide) (![⟨14300, by decide⟩,⟨14300, by decide⟩,⟨902808, by decide⟩,⟨906777, by decide⟩]) unmarked_context_7_274_906778 node_context_7_274_906778
  intro a
  fin_cases a
  · exact context_8_1096_14300
  · exact context_8_1097_14300
  · exact context_8_1098_902808
  · exact context_8_1099_906777

theorem selected_cut_34745 : selected 14 ⟨34032, by decide⟩
    (prefixPartial 7 275) = some ⟨7, 1, 0, 34032, 275, 1, 67108864⟩ := by
  decide +kernel

theorem context_7_275_34032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 275 ⟨34032, by decide⟩ :=
  accepted_of_selected 7 275 ⟨34032, by decide⟩ ⟨7, 1, 0, 34032, 275, 1, 67108864⟩
    (by decide) selected_cut_34745

theorem unmarked_context_6_68_906779 : frontier 15 ⟨906779, by decide⟩
    (prefixCache 6 68) (prefixPartial 6 68) = false := by
  decide +kernel

theorem node_context_6_68_906779 : EJMOriginalGlobalDAGData.nodes 15 ⟨906779, by decide⟩ =
    .split (coordinate 6) (![⟨116316, by decide⟩,⟨897637, by decide⟩,⟨906778, by decide⟩,⟨34032, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_6_68_906779 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 68 ⟨906779, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 6 68
    ⟨906779, by decide⟩ (by decide) (![⟨116316, by decide⟩,⟨897637, by decide⟩,⟨906778, by decide⟩,⟨34032, by decide⟩]) unmarked_context_6_68_906779 node_context_6_68_906779
  intro a
  fin_cases a
  · exact context_7_272_116316
  · exact context_7_273_897637
  · exact context_7_274_906778
  · exact context_7_275_34032

theorem selected_cut_34746 : selected 10 ⟨167448, by decide⟩
    (prefixPartial 11 70656) = some ⟨11, 1, 0, 167448, 70656, 1, 262144⟩ := by
  decide +kernel

theorem context_11_70656_167448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70656 ⟨167448, by decide⟩ :=
  accepted_of_selected 11 70656 ⟨167448, by decide⟩ ⟨11, 1, 0, 167448, 70656, 1, 262144⟩
    (by decide) selected_cut_34746

theorem selected_cut_34747 : selected 9 ⟨906842, by decide⟩
    (prefixPartial 12 282628) = some ⟨12, 2, 0, 906842, 282628, 1097, 65536⟩ := by
  decide +kernel

theorem context_12_282628_906842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282628 ⟨906842, by decide⟩ :=
  accepted_of_selected 12 282628 ⟨906842, by decide⟩ ⟨12, 2, 0, 906842, 282628, 1097, 65536⟩
    (by decide) selected_cut_34747

theorem selected_cut_34748 : selected 9 ⟨906879, by decide⟩
    (prefixPartial 12 282629) = some ⟨12, 2, 0, 906879, 282629, 1229, 65536⟩ := by
  decide +kernel

theorem context_12_282629_906879 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282629 ⟨906879, by decide⟩ :=
  accepted_of_selected 12 282629 ⟨906879, by decide⟩ ⟨12, 2, 0, 906879, 282629, 1229, 65536⟩
    (by decide) selected_cut_34748

theorem selected_cut_34749 : selected 9 ⟨906964, by decide⟩
    (prefixPartial 12 282630) = some ⟨12, 2, 0, 906964, 282630, 2685, 65536⟩ := by
  decide +kernel

theorem context_12_282630_906964 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282630 ⟨906964, by decide⟩ :=
  accepted_of_selected 12 282630 ⟨906964, by decide⟩ ⟨12, 2, 0, 906964, 282630, 2685, 65536⟩
    (by decide) selected_cut_34749

theorem selected_cut_34750 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 282631) = some ⟨12, 1, 0, 893, 282631, 1, 65536⟩ := by
  decide +kernel

theorem context_12_282631_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282631 ⟨893, by decide⟩ :=
  accepted_of_selected 12 282631 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 282631, 1, 65536⟩
    (by decide) selected_cut_34750

theorem unmarked_context_11_70657_906965 : frontier 10 ⟨906965, by decide⟩
    (prefixCache 11 70657) (prefixPartial 11 70657) = false := by
  decide +kernel

theorem node_context_11_70657_906965 : EJMOriginalGlobalDAGData.nodes 10 ⟨906965, by decide⟩ =
    .split (coordinate 11) (![⟨906842, by decide⟩,⟨906879, by decide⟩,⟨906964, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_70657_906965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 70657 ⟨906965, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 70657
    ⟨906965, by decide⟩ (by decide) (![⟨906842, by decide⟩,⟨906879, by decide⟩,⟨906964, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_70657_906965 node_context_11_70657_906965
  intro a
  fin_cases a
  · exact context_12_282628_906842
  · exact context_12_282629_906879
  · exact context_12_282630_906964
  · exact context_12_282631_893

theorem selected_cut_34751 : selected 9 ⟨907055, by decide⟩
    (prefixPartial 12 282632) = some ⟨12, 2, 0, 907055, 282632, 2169, 65536⟩ := by
  decide +kernel

theorem context_12_282632_907055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282632 ⟨907055, by decide⟩ :=
  accepted_of_selected 12 282632 ⟨907055, by decide⟩ ⟨12, 2, 0, 907055, 282632, 2169, 65536⟩
    (by decide) selected_cut_34751

theorem selected_cut_34752 : selected 9 ⟨907123, by decide⟩
    (prefixPartial 12 282633) = some ⟨12, 2, 0, 907123, 282633, 2857, 65536⟩ := by
  decide +kernel

theorem context_12_282633_907123 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282633 ⟨907123, by decide⟩ :=
  accepted_of_selected 12 282633 ⟨907123, by decide⟩ ⟨12, 2, 0, 907123, 282633, 2857, 65536⟩
    (by decide) selected_cut_34752

theorem selected_cut_34753 : selected 9 ⟨907186, by decide⟩
    (prefixPartial 12 282634) = some ⟨12, 2, 0, 907186, 282634, 2813, 65536⟩ := by
  decide +kernel

theorem context_12_282634_907186 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 282634 ⟨907186, by decide⟩ :=
  accepted_of_selected 12 282634 ⟨907186, by decide⟩ ⟨12, 2, 0, 907186, 282634, 2813, 65536⟩
    (by decide) selected_cut_34753

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
