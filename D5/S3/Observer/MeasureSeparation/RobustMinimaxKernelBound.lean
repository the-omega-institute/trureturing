/- GID: D5/S3/Observer/MeasureSeparation/RobustMinimaxKernelBound
   generality: G
   mirror-B: D5/B/S3/Observer/MeasureSeparation/RobustMinimaxKernelBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Robust defs, a fragile witness, and kernel bounds cover degenerate cases. -/

import D5.S3.Observer.MeasureSeparation.FactorizedTranscriptKernelBarrier
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/- Library-search audit trail (2026-08-25):
   * Repository searches inspected `FactorizedTranscriptKernelBarrier` and
     `HorizontalSaturationSeparation`; both headers say `generality: G`.
   * The first module supplies transcript-law equality on a factorized fiber and is imported.
     The second concerns language expansion, not numeric decision risk, so it is not imported.
   * `KernelTranscriptInvariance`, `InterventionFamilyTranscriptObstruction`, Le Cam bounds,
     and the FPOD Section 249 source were inspected; none states both numeric bounds below.
   * Pinned Mathlib searches covered `ProbabilityTheory.Kernel`, `PMF`, `iInf`, `iSup`,
     `Finset.inf'`, `Measure.map`, and `ProbabilityTheory.minimaxRisk`.
     PMF normalization and complete-lattice `iSup` are used; the other hits do not expose the
     required argmin policy set, robust set update, or exact common-kernel bounds.
   * Primality has no role: `prime` is only the source's interface name. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace D5.S3.Observer.MeasureSeparation.RobustMinimaxKernelBound

open D5.S3.Observer.MeasureSeparation.FactorizedTranscriptKernelBarrier

/-- The supremum of one policy's extended-nonnegative costs over the allowed models. -/
noncomputable def worstCaseCost {Model Policy : Type*}
    (models : Set Model) (cost : Model -> Policy -> ENNReal) (policy : Policy) : ENNReal :=
  ⨆ model : models, cost model.1 policy

/-- FPOD 249.1: the exact argmin set of policies for the model-wise worst-case cost. -/
noncomputable def minimaxPolicies {Model Policy : Type*}
    (models : Set Model) (cost : Model -> Policy -> ENNReal) : Set Policy :=
  {policy | forall candidate,
    worstCaseCost models cost policy <= worstCaseCost models cost candidate}

/-- FPOD 249.2 in the discrete setting: update every current PMF under every allowed model. -/
def robustBeliefUpdate {Model State Experiment Observation : Type*}
    (models : Set Model)
    (bayesUpdate : Experiment -> Model -> PMF State -> Observation -> PMF State)
    (experiment : Experiment) (observation : Observation)
    (beliefs : Set (PMF State)) : Set (PMF State) :=
  {posterior | exists prior, prior ∈ beliefs ∧
    exists model, model ∈ models ∧
      posterior = bayesUpdate experiment model prior observation}

/-- Under binary zero-one loss, the error is the mass assigned to the opposite label. -/
def binaryError (decisionLaw : PMF Bool) (truth : Bool) : ENNReal :=
  decisionLaw (!truth)

/-- False is the fragile interface, true the robust one; false is the nominal model. -/
def fragilityWitnessChannel (interface model state : Bool) : Real :=
  if interface then
    if state then 1 else 0
  else if model then
    0
  else if state then
    1 / 1000
  else
    0

/-- Unit cost exactly when the selected interface is blind under the selected model. -/
def fragilityBlindRisk (interface model : Bool) : ENNReal :=
  if fragilityWitnessChannel interface model false =
      fragilityWitnessChannel interface model true then 1 else 0

/-- A law-level classifier that exactly distinguishes the two Boolean Dirac laws. -/
noncomputable def separatedDiracClassifier (law : ProbabilityMeasure Bool) : PMF Bool :=
  by
    classical
    exact if law = diracProba false then PMF.pure false else PMF.pure true

private theorem boolean_pmf_total (law : PMF Bool) :
    law false + law true = 1 := by
  simpa only [tsum_fintype, Fintype.sum_bool, add_comm] using PMF.tsum_coe law

private theorem complementary_probability_bounds
    (first second weight : ENNReal) (total : first + second = 1) :
    (1 / 2 : ENNReal) <= max first second ∧
      min weight (1 - weight) <=
        weight * first + (1 - weight) * second := by
  constructor
  · by_contra belowHalf
    have maxBelow : max first second < (1 / 2 : ENNReal) := lt_of_not_ge belowHalf
    have firstBelow : first < (1 / 2 : ENNReal) :=
      (le_max_left first second).trans_lt maxBelow
    have secondBelow : second < (1 / 2 : ENNReal) :=
      (le_max_right first second).trans_lt maxBelow
    have sumBelow : first + second < (1 / 2 : ENNReal) + 1 / 2 :=
      ENNReal.add_lt_add firstBelow secondBelow
    rw [total] at sumBelow
    rw [ENNReal.add_halves] at sumBelow
    exact (lt_irrefl 1 sumBelow)
  · rcases le_total weight (1 - weight) with lightWeight | heavyWeight
    · rw [min_eq_left lightWeight]
      calc
        weight = weight * (first + second) := by rw [total, mul_one]
        _ = weight * first + weight * second := by rw [mul_add]
        _ <= weight * first + (1 - weight) * second :=
          add_le_add le_rfl (mul_le_mul_right' lightWeight second)
    · rw [min_eq_right heavyWeight]
      calc
        1 - weight = (1 - weight) * (first + second) := by rw [total, mul_one]
        _ = (1 - weight) * first + (1 - weight) * second := by rw [mul_add]
        _ <= weight * first + (1 - weight) * second :=
          add_le_add (mul_le_mul_right' heavyWeight first) le_rfl

private theorem separated_dirac_classifier_zero_errors :
    binaryError
        (separatedDiracClassifier (distinguishingBooleanTranscriptKernel false)) false = 0 ∧
      binaryError
        (separatedDiracClassifier (distinguishingBooleanTranscriptKernel true)) true = 0 := by
  have differentDirac : diracProba true ≠ diracProba false := by
    intro equalDirac
    exact Bool.false_ne_true (injective_diracProba equalDirac).symm
  simp [binaryError, separatedDiracClassifier, distinguishingBooleanTranscriptKernel,
    differentDirac]

/-- FPOD 249.1 principle witness: a `1/1000` misspecification blinds the nominally separating
interface, while the other interface separates under both models and is minimax-optimal. -/
theorem fragile_interface_not_minimax :
    (forall state,
      |fragilityWitnessChannel false false state -
        fragilityWitnessChannel false true state| <= (1 / 1000 : Real)) ∧
      fragilityWitnessChannel false false false ≠
        fragilityWitnessChannel false false true ∧
      fragilityWitnessChannel false true false =
        fragilityWitnessChannel false true true ∧
      (forall model,
        fragilityWitnessChannel true model false ≠
          fragilityWitnessChannel true model true) ∧
      false ∉ minimaxPolicies Set.univ
        (fun model interface => fragilityBlindRisk interface model) := by
  refine ⟨?_, by norm_num [fragilityWitnessChannel], rfl, ?_, ?_⟩
  · intro state
    cases state <;> norm_num [fragilityWitnessChannel, abs_of_nonneg]
  · intro model
    cases model <;> norm_num [fragilityWitnessChannel]
  · intro fragileMinimax
    have compareWithRobust :
        worstCaseCost Set.univ
            (fun model interface => fragilityBlindRisk interface model) false <=
          worstCaseCost Set.univ
            (fun model interface => fragilityBlindRisk interface model) true :=
      fragileMinimax true
    have fragileWorst :
        worstCaseCost Set.univ
            (fun model interface => fragilityBlindRisk interface model) false = 1 := by
      apply le_antisymm
      · apply iSup_le
        rintro ⟨model, _⟩
        cases model <;> simp [fragilityBlindRisk, fragilityWitnessChannel]
      · apply le_iSup_of_le (⟨true, Set.mem_univ true⟩ : Set.univ)
        simp [fragilityBlindRisk, fragilityWitnessChannel]
    have robustWorst :
        worstCaseCost Set.univ
            (fun model interface => fragilityBlindRisk interface model) true = 0 := by
      apply le_antisymm
      · apply iSup_le
        rintro ⟨model, _⟩
        cases model <;> simp [fragilityBlindRisk, fragilityWitnessChannel]
      · exact bot_le
    rw [fragileWorst, robustWorst] at compareWithRobust
    norm_num at compareWithRobust
#print axioms fragile_interface_not_minimax

/-- FPOD 249.1: a factorized common transcript law forces both the one-half minimax error
bound and the `min a (1-a)` Bayes-risk bound for every law-level final classifier. -/
theorem common_kernel_minimax_lower_bounds
    {Interface Transcript : Type*} [MeasurableSpace Transcript]
    (q : Bool -> Interface) (transcript : TranscriptKernel Bool Transcript)
    (x y : Bool) (classifier : ProbabilityMeasure Transcript -> PMF Bool)
    (weight : ENNReal) (factorized : KernelFactorsThrough q transcript)
    (sameFiber : q x = q y) (distinct : x ≠ y) :
    (1 / 2 : ENNReal) <=
        max (binaryError (classifier (transcript x)) x)
          (binaryError (classifier (transcript y)) y) ∧
      min weight (1 - weight) <=
        weight * binaryError (classifier (transcript x)) x +
          (1 - weight) * binaryError (classifier (transcript y)) y := by
  have sameTranscript : transcript x = transcript y :=
    factorized_transcript_kernel_eq_on_fiber q transcript x y factorized sameFiber
  have sameDecision : classifier (transcript x) = classifier (transcript y) :=
    congrArg classifier sameTranscript
  cases x <;> cases y
  · exact (distinct rfl).elim
  · simp only [binaryError, Bool.not_false, Bool.not_true]
    rw [← sameDecision]
    exact complementary_probability_bounds _ _ weight
      (by simpa [add_comm] using boolean_pmf_total (classifier (transcript false)))
  · simp only [binaryError, Bool.not_true, Bool.not_false]
    rw [← sameDecision]
    exact complementary_probability_bounds _ _ weight
      (boolean_pmf_total (classifier (transcript true)))
  · exact (distinct rfl).elim
#print axioms common_kernel_minimax_lower_bounds

/-- The transcript-factorization premise is necessary: equal constant-interface values coexist
with perfectly classifiable, unequal Dirac laws when factorization is removed. -/
theorem transcript_factorization_is_necessary_for_lower_bound :
    booleanInterface false = booleanInterface true ∧
      ¬KernelFactorsThrough booleanInterface distinguishingBooleanTranscriptKernel ∧
      ¬(1 / 2 : ENNReal) <=
        max
          (binaryError
            (separatedDiracClassifier (distinguishingBooleanTranscriptKernel false)) false)
          (binaryError
            (separatedDiracClassifier (distinguishingBooleanTranscriptKernel true)) true) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro factorized
    have equalLaws :=
      factorized_transcript_kernel_eq_on_fiber booleanInterface
        distinguishingBooleanTranscriptKernel false true factorized rfl
    change diracProba false = diracProba true at equalLaws
    exact Bool.false_ne_true (injective_diracProba equalLaws)
  · rw [separated_dirac_classifier_zero_errors.1,
      separated_dirac_classifier_zero_errors.2]
    norm_num
#print axioms transcript_factorization_is_necessary_for_lower_bound

/-- The same-fiber premise is necessary: the identity interface factors the two Dirac laws,
but places the two perfectly classifiable states in different fibers. -/
theorem same_fiber_is_necessary_for_lower_bound :
    KernelFactorsThrough id distinguishingBooleanTranscriptKernel ∧
      (id : Bool -> Bool) false ≠ id true ∧
      ¬(1 / 2 : ENNReal) <=
        max
          (binaryError
            (separatedDiracClassifier (distinguishingBooleanTranscriptKernel false)) false)
          (binaryError
            (separatedDiracClassifier (distinguishingBooleanTranscriptKernel true)) true) := by
  refine ⟨⟨distinguishingBooleanTranscriptKernel, rfl⟩, Bool.false_ne_true, ?_⟩
  rw [separated_dirac_classifier_zero_errors.1,
    separated_dirac_classifier_zero_errors.2]
  norm_num
#print axioms same_fiber_is_necessary_for_lower_bound

/-- Distinctness is necessary: at one repeated state, a constant transcript and correct constant
classifier satisfy the kernel premises but have zero error. -/
theorem distinct_states_is_necessary_for_lower_bound :
    KernelFactorsThrough booleanInterface constantBooleanTranscriptKernel ∧
      booleanInterface false = booleanInterface false ∧
      ¬(1 / 2 : ENNReal) <=
        max (binaryError (PMF.pure false) false) (binaryError (PMF.pure false) false) := by
  refine ⟨⟨fun _ => diracProba (), rfl⟩, rfl, ?_⟩
  simp [binaryError]
#print axioms distinct_states_is_necessary_for_lower_bound

/- Degenerate audit: an empty model type gives the empty supremum, so every policy is minimax. -/
example {Policy : Type*} (cost : Empty -> Policy -> ENNReal) :
    minimaxPolicies (Set.univ : Set Empty) cost = Set.univ := by
  ext policy
  simp [minimaxPolicies, worstCaseCost]

/- Degenerate audit: for a singleton model set, robust minimization is nominal minimization. -/
example {Policy : Type*} (cost : Unit -> Policy -> ENNReal) (policy : Policy) :
    policy ∈ minimaxPolicies (Set.univ : Set Unit) cost ↔
      forall candidate, cost () policy <= cost () candidate := by
  have worstCase_eq (candidate : Policy) :
      worstCaseCost (Set.univ : Set Unit) cost candidate = cost () candidate := by
    apply le_antisymm
    · apply iSup_le
      rintro ⟨model, _⟩
      cases model
      exact le_rfl
    · apply le_iSup_of_le (⟨(), Set.mem_univ ()⟩ : Set.univ)
      exact le_rfl
  simp only [minimaxPolicies, Set.mem_setOf_eq]
  constructor
  · intro minimizes candidate
    simpa only [worstCase_eq] using minimizes candidate
  · intro minimizes candidate
    simpa only [worstCase_eq] using minimizes candidate

/- Degenerate audit: no allowed models or no current beliefs yields no posterior. -/
example {Model State Experiment Observation : Type*}
    (bayesUpdate : Experiment -> Model -> PMF State -> Observation -> PMF State)
    (experiment : Experiment) (observation : Observation) (beliefs : Set (PMF State)) :
    robustBeliefUpdate ∅ bayesUpdate experiment observation beliefs = ∅ := by
  ext posterior
  simp [robustBeliefUpdate]

example {Model State Experiment Observation : Type*}
    (models : Set Model)
    (bayesUpdate : Experiment -> Model -> PMF State -> Observation -> PMF State)
    (experiment : Experiment) (observation : Observation) :
    robustBeliefUpdate models bayesUpdate experiment observation ∅ = ∅ := by
  ext posterior
  simp [robustBeliefUpdate]

/- Degenerate audit: a singleton uncertainty set is the image of its nominal Bayes update. -/
example {Model State Experiment Observation : Type*}
    (model : Model)
    (bayesUpdate : Experiment -> Model -> PMF State -> Observation -> PMF State)
    (experiment : Experiment) (observation : Observation) (beliefs : Set (PMF State)) :
    robustBeliefUpdate {model} bayesUpdate experiment observation beliefs =
      (fun prior => bayesUpdate experiment model prior observation) '' beliefs := by
  ext posterior
  simp [robustBeliefUpdate, eq_comm]

/- Degenerate audit: endpoint Bayes weights make the lower bound zero. -/
example (first second : ENNReal) :
    min 0 (1 - 0) <= 0 * first + (1 - 0) * second := by simp

example (first second : ENNReal) :
    min 1 (1 - 1) <= 1 * first + (1 - 1) * second := by simp

/- Degenerate audit: the common-kernel bound still holds for the empty transcript at `n = 0`. -/
example (classifier : ProbabilityMeasure (Fin 0 -> Unit) -> PMF Bool)
    (weight : ENNReal) :
    (1 / 2 : ENNReal) <=
        max
          (binaryError
            (classifier (iidRepetition 0 constantBooleanTranscriptKernel false)) false)
          (binaryError
            (classifier (iidRepetition 0 constantBooleanTranscriptKernel true)) true) ∧
      min weight (1 - weight) <=
        weight *
            binaryError
              (classifier (iidRepetition 0 constantBooleanTranscriptKernel false)) false +
          (1 - weight) *
            binaryError
              (classifier (iidRepetition 0 constantBooleanTranscriptKernel true)) true := by
  apply common_kernel_minimax_lower_bounds booleanInterface
    (iidRepetition 0 constantBooleanTranscriptKernel) false true classifier weight
  · apply iid_repetition_preserves_factorization
    exact ⟨fun _ => diracProba (), rfl⟩
  · rfl
  · exact Bool.false_ne_true

end D5.S3.Observer.MeasureSeparation.RobustMinimaxKernelBound
