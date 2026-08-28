/- GID: D5/S3/Observer/Budget/AdaptiveEarlyStoppingLimits
   generality: G
   mirror-B: D5/B/S3/Observer/Budget/AdaptiveEarlyStoppingLimits
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Adaptive depth keeps the clog bound; one experiment has at most B outputs. -/
/- Library-search audit trail (2026-08-25):
   * Repository search found the exact average-case result
     `expected_experiment_count_lt_two`; it is imported and not reproved.
   * Repository search found the adaptive worst-case result
     `worst_case_depth_information_lower_bound`. Its `AdaptiveProtocol.leaf`
     constructor is available at every remaining budget, so it already permits
     early stopping. The positive-branching premise is needed for its leaf-count
     proof, but `Nat.clog_zero_left` removes it from the final logarithmic bound.
   * Pinned Mathlib supplies `Finset.card_le_card`, `Fintype.card_fin`,
     `Nat.clog_zero_left`, `Nat.clog_pow`, and `Nat.find_min'`.
   * Existing named audits cover zero depth, empty and singleton states, unary
     branching, and constant readouts; the concrete specializations below reuse them. -/

import D5.S3.ConceptDynamics.ExperimentDesign.AdaptiveEarlyStopping
import D5.S3.Observer.Budget.WorstCaseDepthInformationLowerBound

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Budget.AdaptiveEarlyStoppingLimits

open D5.S3.ConceptDynamics.ExperimentDesign.AdaptiveEarlyStopping
open D5.S3.Observer.Budget.WorstCaseDepthInformationLowerBound

universe u v

/-- The coordinate questions on the full `B`-ary transcript state space. -/
def coordinateReadout (B h : Nat) :
    ((Fin h -> Fin B) -> Fin B) -> (Fin h -> Fin B) -> Fin B :=
  id

/-- The answers actually attained by one experiment on a finite state space. -/
def singleExperimentOutputs {State : Type u} [Fintype State] {B : Nat}
    (question : State -> Fin B) : Finset (Fin B) :=
  Finset.univ.image question

/-- Early stopping is already allowed by `AdaptiveProtocol`, so the same
worst-case information lower bound applies. The next theorem gives a tight family. -/
theorem adaptive_worst_case_depth_information_lower_bound
    {Question : Type v} {State : Type u} [Fintype State] {B : Nat}
    (readout : Question -> State -> Fin B)
    (identifiable : exists depth, ExactAtDepth readout depth) :
    Nat.clog B (Fintype.card State) <=
      adaptiveIdentificationDepth readout identifiable := by
  by_cases hB : 1 <= B
  · exact worst_case_depth_information_lower_bound readout hB identifiable
  · have hBzero : B = 0 := by omega
    subst B
    simp
#print axioms adaptive_worst_case_depth_information_lower_bound

/-- For `B > 1`, the full transcript state space attains the lower bound at
every depth, so the worst-case bound is genuinely tight on this family. -/
theorem adaptive_worst_case_depth_lower_bound_is_tight
    (B h : Nat) (hB : 1 < B) :
    exists identifiable : exists depth, ExactAtDepth (coordinateReadout B h) depth,
      adaptiveIdentificationDepth (coordinateReadout B h) identifiable = h := by
  classical
  have exactAtH : ExactAtDepth (coordinateReadout B h) h := by
    simpa [coordinateReadout] using (full_transcript_space_attains_leaf_bound B h).2
  let identifiable : exists depth, ExactAtDepth (coordinateReadout B h) depth :=
    ⟨h, exactAtH⟩
  refine ⟨identifiable, Nat.le_antisymm ?_ ?_⟩
  · exact Nat.find_min' identifiable exactAtH
  · have lower := adaptive_worst_case_depth_information_lower_bound
      (coordinateReadout B h) identifiable
    simpa [Nat.clog_pow B h hB] using lower
#print axioms adaptive_worst_case_depth_lower_bound_is_tight

/-- The premise `1 < B` in the tightness theorem is necessary: with unary
answers and nominal depth one, the singleton transcript space is identified at depth zero. -/
theorem branching_gt_one_is_necessary_for_positive_depth_tightness :
    let readout := coordinateReadout 1 1
    exists identifiable : exists depth, ExactAtDepth readout depth,
      adaptiveIdentificationDepth readout identifiable = 0 ∧
        adaptiveIdentificationDepth readout identifiable ≠ 1 := by
  classical
  let readout := coordinateReadout 1 1
  have exactAtZero : ExactAtDepth readout 0 := by
    refine ⟨AdaptiveProtocol.leaf, trivial, ?_⟩
    intro left right _sameTranscript
    exact Subsingleton.elim left right
  let identifiable : exists depth, ExactAtDepth readout depth := ⟨0, exactAtZero⟩
  have depthZero : adaptiveIdentificationDepth readout identifiable = 0 := by
    apply Nat.eq_zero_of_le_zero
    exact Nat.find_min' identifiable exactAtZero
  refine ⟨identifiable, depthZero, ?_⟩
  change adaptiveIdentificationDepth readout identifiable ≠ 1
  simp [depthZero]
#print axioms branching_gt_one_is_necessary_for_positive_depth_tightness

/-- Since every query returns `Fin B` by definition, one experiment attains at
most `B` distinct answers. Adaptivity changes later questions, not this alphabet. -/
theorem single_experiment_output_count_le
    {State : Type u} [Fintype State] {B : Nat} (question : State -> Fin B) :
    (singleExperimentOutputs question).card <= B := by
  calc
    (singleExperimentOutputs question).card <=
        (Finset.univ : Finset (Fin B)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = B := by simp
#print axioms single_experiment_output_count_le

/-- The one-experiment bound is exact: the identity experiment realizes every
answer, including the empty alphabet when `B = 0`. -/
theorem identity_experiment_attains_output_bound (B : Nat) :
    (singleExperimentOutputs (id : Fin B -> Fin B)).card = B := by
  simp [singleExperimentOutputs]
#print axioms identity_experiment_attains_output_bound

/-- Empty states with `B = 0` attain no answers, while a constant unary
experiment on a singleton state attains exactly one answer. -/
theorem single_experiment_degenerate_audit :
    (singleExperimentOutputs (B := 0)
      (fun state : Empty => Empty.elim state)).card = 0 ∧
    (singleExperimentOutputs (B := 1)
      (fun _state : Unit => (0 : Fin 1))).card = 1 := by
  simp [singleExperimentOutputs]
#print axioms single_experiment_degenerate_audit

/-- Concrete protocol audits: empty and singleton states are exact at depth
zero, unary upper logarithm is zero, and a constant binary readout never identifies Bool. -/
theorem protocol_degenerate_audit :
    let emptyReadout : Unit -> Empty -> Fin 1 :=
      fun _question state => Empty.elim state
    let singletonReadout : Unit -> Unit -> Fin 1 :=
      fun _question _state => 0
    ExactAtDepth emptyReadout 0 ∧
      ExactAtDepth singletonReadout 0 ∧
        Nat.clog 1 (Fintype.card Unit) = 0 ∧
          forall depth,
            ¬ExactAtDepth (fun _ : Unit => fun _ : Bool => (0 : Fin 2)) depth := by
  dsimp
  have depths := empty_and_singleton_depth_zero_audit
    (fun _question : Unit => fun state : Empty => Empty.elim state)
    (fun _question : Unit => fun _state : Unit => (0 : Fin 1))
  exact ⟨depths.1, depths.2.1, by simp, constant_zero_readout_not_exact_on_bool⟩
#print axioms protocol_degenerate_audit

/-- In the concrete three-model example, concentrating on a branch that does
not stop early executes both experiments, so adaptive and static counts coincide. -/
theorem all_experiments_required_has_no_average_saving :
    expectedExperimentCount (PMF.pure M_0) = 2 :=
  error_probability_lt_one_is_necessary.2.1
#print axioms all_experiments_required_has_no_average_saving

end D5.S3.Observer.Budget.AdaptiveEarlyStoppingLimits
