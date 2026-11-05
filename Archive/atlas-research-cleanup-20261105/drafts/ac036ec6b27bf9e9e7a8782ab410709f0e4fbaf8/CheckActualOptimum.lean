import D5.S3.Combinatorics.CircularWords.ActualCycleMeanLowerBound

set_option autoImplicit false
open D5.S3.Combinatorics.CircularWords
open CircularDeletionTransport UniformCycleAttainment ActualCycleMeanLowerBound
open D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound
open D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization

variable {α : Type} [DecidableEq α]
noncomputable section

-- Exact actual-model optimum: lower for every terminating zero-error history
-- policy, and an explicit history-only policy attaining that bound on ALL cycles.
example {A : Finset α} (hA : 4 ≤ A.card)
    (x z y : Query A) (hxz : x.val ≠ z.val) (hxy : x.val ≠ y.val)
    (hzy : z.val ≠ y.val) :
    (∀ {L : Type} (p : History A → Sum (Query A) L)
      (tr : Cycle α → History A) (lab : Cycle α → L),
      (∀ C ∈ carrier A, ∃ n, execute (read A) p n [] C = some (tr C,lab C)) →
      ∀ output : L → Cycle α, (∀ C ∈ carrier A, output (lab C) = C) →
      2 + 2 / (A.card - 1 : ℚ) ≤
        ((∑ C ∈ carrier A, (tr C).length : Nat) : ℚ) / ((carrier A).card : ℚ)) ∧
    (∃ (p : History A → Sum (Query A) (History A))
        (tr : Cycle α → History A) (output : History A → Cycle α),
      (∀ C ∈ carrier A, execute (read A) p 4 [] C = some (tr C,tr C)) ∧
      (∀ C ∈ carrier A, output (tr C) = C) ∧
      ((∑ C ∈ carrier A, (tr C).length : Nat) : ℚ) / ((carrier A).card : ℚ) =
        2 + 2 / (A.card - 1 : ℚ)) := by
  constructor
  · intro L p tr lab runs output correct
    exact actual_history_lower_bound hA p tr lab runs output correct
  · refine ⟨attainingPolicy A x z y,
      runPassiveProtocol (read A) (attainingProtocol A x z y),
      decode A (Finset.card_pos.mp (by omega)), ?_, ?_, ?_⟩
    · intro C _
      exact attainingPolicy_execute A x z y C
    · intro C hC
      exact attainingProtocol_correct hA x z y hxz hxy hzy hC
    · exact actual_cycle_attaining_mean hA x z y hxz

#check @rooted_gap_second_law
#check @pair_branch_exact
#check @ambiguous_card
#check @attainingProtocol_correct
#check @attainingPolicy_execute
#check @actual_cycle_attaining_mean
#check @firstFiberEquiv
#check @repeated_paired
#check @distinct_paired
#check @actual_paired_bound
#check @actual_history_lower_bound
#print axioms rooted_gap_second_law
#print axioms pair_branch_exact
#print axioms ambiguous_card
#print axioms attainingProtocol_correct
#print axioms attainingPolicy_execute
#print axioms actual_cycle_attaining_mean
#print axioms firstFiberEquiv
#print axioms realized_first_size
#print axioms repeated_paired
#print axioms distinct_paired
#print axioms actual_paired_bound
#print axioms actual_history_lower_bound

-- Complete public theorem closure inventory for the selected new modules.
#print axioms D5.S3.Combinatorics.CircularWords.PairedDeletionFiber.erase_pair_classification
#print axioms D5.S3.Combinatorics.CircularWords.PairedDeletionFiber.adjacentSwapAt_unique
#print axioms D5.S3.Combinatorics.CircularWords.PairedDeletionFiber.paired_fiber_iff_at_root
#print axioms D5.S3.Combinatorics.CircularWords.PairedDeletionFiber.paired_fiber_iff
#print axioms D5.S3.Combinatorics.CircularWords.PairedDeletionFiber.pair_fiber_at_most_two
#print axioms D5.S3.Combinatorics.CircularWords.PairedDeletionFiber.exists_nontrivial_alternative_iff_cyclicAdjacent
#print axioms D5.S3.Combinatorics.CircularWords.SingleDeletionFiberCount.deletion_fiber_card
#print axioms D5.S3.ConceptDynamics.Experiment.TwoQueryAmbiguityCost.exact_tree_queries
#print axioms D5.S3.ConceptDynamics.Experiment.TwoQueryAmbiguityCost.first_branch_cost
#print axioms D5.S3.ConceptDynamics.Experiment.TwoQueryAmbiguityCost.sum_first_fibres
#print axioms D5.S3.ConceptDynamics.Experiment.TwoQueryAmbiguityCost.mean_of_total
#print axioms D5.S3.ConceptDynamics.Experiment.TwoQueryAmbiguityCost.tree_two_query_cost
#print axioms D5.S3.ConceptDynamics.Experiment.TwoQueryAmbiguityCost.history_two_query_cost
#print axioms D5.S3.Combinatorics.CircularWords.UniformCycleAttainment.mem_carrier_legal
#print axioms D5.S3.Combinatorics.CircularWords.UniformCycleAttainment.legal_mem_carrier
#print axioms D5.S3.Combinatorics.CircularWords.UniformCycleAttainment.carrier_card
#print axioms D5.S3.Combinatorics.CircularWords.UniformCycleAttainment.carrier_nonempty
#print axioms D5.S3.Combinatorics.CircularWords.UniformCycleAttainment.filter_rotate_root
#print axioms D5.S3.Combinatorics.CircularWords.UniformCycleAttainment.secondGap_root_formula
#print axioms D5.S3.Combinatorics.CircularWords.UniformCycleAttainment.rooted_gap_second_law
#print axioms D5.S3.Combinatorics.CircularWords.UniformCycleAttainment.legal_residual_root
#print axioms D5.S3.Combinatorics.CircularWords.UniformCycleAttainment.rooted_gap_second_certificate
#print axioms D5.S3.Combinatorics.CircularWords.UniformCycleAttainment.slot_fiber_zero_card
#print axioms D5.S3.Combinatorics.CircularWords.UniformCycleAttainment.gap_second_fiber_card
#print axioms D5.S3.Combinatorics.CircularWords.UniformCycleAttainment.slot_fiber_other_card
#print axioms D5.S3.Combinatorics.CircularWords.UniformCycleAttainment.firstLift_card
#print axioms D5.S3.Combinatorics.CircularWords.UniformCycleAttainment.pairLift_atMostTwo
#print axioms D5.S3.Combinatorics.CircularWords.UniformCycleAttainment.pair_branch_exact
#print axioms D5.S3.Combinatorics.CircularWords.UniformCycleAttainment.candidate_mem_of_carrier
#print axioms D5.S3.Combinatorics.CircularWords.UniformCycleAttainment.mem_pair_candidates
#print axioms D5.S3.Combinatorics.CircularWords.UniformCycleAttainment.pair_candidates_card
#print axioms D5.S3.Combinatorics.CircularWords.UniformCycleAttainment.decoder_eq_of_candidate_singleton
#print axioms D5.S3.Combinatorics.CircularWords.UniformCycleAttainment.candidateSet_singleton_of_three
#print axioms D5.S3.Combinatorics.CircularWords.UniformCycleAttainment.pair_or_three_decode
#print axioms D5.S3.Combinatorics.CircularWords.UniformCycleAttainment.attainingProtocol_run_length
#print axioms D5.S3.Combinatorics.CircularWords.UniformCycleAttainment.attainingProtocol_correct
#print axioms D5.S3.Combinatorics.CircularWords.UniformCycleAttainment.delete_legal
#print axioms D5.S3.Combinatorics.CircularWords.UniformCycleAttainment.every_first_residual_realized
#print axioms D5.S3.Combinatorics.CircularWords.UniformCycleAttainment.first_residual_image
#print axioms D5.S3.Combinatorics.CircularWords.UniformCycleAttainment.ambiguous_subset
#print axioms D5.S3.Combinatorics.CircularWords.UniformCycleAttainment.ambiguous_first_fiber_card
#print axioms D5.S3.Combinatorics.CircularWords.UniformCycleAttainment.residual_carrier_card
#print axioms D5.S3.Combinatorics.CircularWords.UniformCycleAttainment.ambiguous_card
#print axioms D5.S3.Combinatorics.CircularWords.UniformCycleAttainment.branch_count_certificate
#print axioms D5.S3.Combinatorics.CircularWords.UniformCycleAttainment.third_query_iff_ambiguous
#print axioms D5.S3.Combinatorics.CircularWords.UniformCycleAttainment.third_query_count
#print axioms D5.S3.Combinatorics.CircularWords.UniformCycleAttainment.factorial_ratio_mean
#print axioms D5.S3.Combinatorics.CircularWords.UniformCycleAttainment.exact_mean_from_branch_certificate
#print axioms D5.S3.Combinatorics.CircularWords.UniformCycleAttainment.actual_cycle_attaining_mean
#print axioms D5.S3.Combinatorics.CircularWords.UniformCycleAttainment.attainingPolicy_execute
#print axioms D5.S3.Combinatorics.CircularWords.ActualCycleMeanLowerBound.realized_first_legal
#print axioms D5.S3.Combinatorics.CircularWords.ActualCycleMeanLowerBound.realized_first_size
#print axioms D5.S3.Combinatorics.CircularWords.ActualCycleMeanLowerBound.repeated_paired
#print axioms D5.S3.Combinatorics.CircularWords.ActualCycleMeanLowerBound.distinct_paired
#print axioms D5.S3.Combinatorics.CircularWords.ActualCycleMeanLowerBound.actual_paired_bound
#print axioms D5.S3.Combinatorics.CircularWords.ActualCycleMeanLowerBound.actual_history_lower_bound
