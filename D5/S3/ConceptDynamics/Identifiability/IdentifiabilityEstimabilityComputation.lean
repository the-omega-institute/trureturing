/- GID: D5/S3/ConceptDynamics/Identifiability/IdentifiabilityEstimabilityComputation
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/Identifiability/IdentifiabilityEstimabilityComputation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Three inference layers separate, including zero-sample and finite-model audits. -/
/- Library-search audit trail (2026-08-29):
   * FPOD Section 281 was checked in `FORMAL_PRIME_OBSERVER_DYNAMICS.md`.
   * Pinned Mathlib supplies `Setoid.ker`, `Function.Injective`, `Filter.Tendsto`, and
     the classical `Computable` predicate; no `ComplexityClass` declaration was found.
   * `ExperimentIdentifiability.identifiable_tfae` and `Function.factorsThrough_iff`
     give factorization criteria, but neither defines the three FPOD notions together.
   * `ThreeLayerCausalObservationLanguage` uses the same canonical `Setoid.ker`, but its
     definitions are causal profiles rather than target-relative identifiability.
   * `InfiniteIdentificationFiniteInexactness` is the exact repository witness reused
     for infinite-law identification without finite-prefix exact recovery.
   * Searches for `Estimable`, the five layer predicates, and `ComplexityClass` found no
     existing declaration with the signatures below.
 -/

import D5.S3.ConceptDynamics.Experiment.InfiniteIdentificationFiniteInexactness

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Identifiability.IdentifiabilityEstimabilityComputation

open MeasureTheory
open D5.S3.ConceptDynamics.Experiment.InfiniteIdentificationFiniteInexactness

universe uModel uEvidence uTarget uSample uOmega uInput uOutput

noncomputable section

/-- FPOD Definition 281.1: exact evidence identifies a target when every evidence
fiber lies inside a target fiber. -/
def Identifiable {Model : Type uModel} {Evidence : Type uEvidence} {Target : Type uTarget}
    (evidence : Model -> Evidence) (target : Model -> Target) : Prop :=
  Setoid.ker evidence <= Setoid.ker target

/-- Exact zero-one-loss recovery, almost surely, at one specified sample size. -/
def FiniteSampleAccurateAt {Model : Type uModel} {Omega : Type uOmega}
    [MeasurableSpace Omega]
    {Target : Type uTarget} (Sample : Nat -> Type uSample)
    (law : Model -> Measure Omega) (readout : (n : Nat) -> Omega -> Sample n)
    (target : Model -> Target) (n : Nat) : Prop :=
  Exists fun estimator : Sample n -> Target =>
    forall model, ∀ᵐ omega ∂law model, estimator (readout n omega) = target model

/-- FPOD Definition 281.2, in a deliberately narrow faithful form: some positive finite
sample size has an almost-surely exact estimator, hence zero zero-one risk. -/
def Estimable {Model : Type uModel} {Omega : Type uOmega} [MeasurableSpace Omega]
    {Target : Type uTarget}
    (Sample : Nat -> Type uSample) (law : Model -> Measure Omega)
    (readout : (n : Nat) -> Omega -> Sample n) (target : Model -> Target) : Prop :=
  Exists fun n : Nat => 0 < n /\ FiniteSampleAccurateAt Sample law readout target n

/-- A registered formula computes the target from the exact evidence interface. -/
def IdentificationFormula {Model : Type uModel} {Evidence : Type uEvidence}
    {Target : Type uTarget} (evidence : Model -> Evidence) (target : Model -> Target)
    (formula : Evidence -> Target) : Prop :=
  forall model, formula (evidence model) = target model

/-- A registered algorithm agrees pointwise with the function it is meant to evaluate. -/
def AlgorithmImplements {Input : Type uInput} {Output : Type uOutput}
    (specification algorithm : Input -> Output) : Prop :=
  forall input, algorithm input = specification input

/-- A supplied resource model charges a registered algorithm no more than the budget. -/
def ComplexityBound {Input : Type uInput} {Output : Type uOutput}
    (cost : (Input -> Output) -> Input -> Nat) (algorithm : Input -> Output)
    (budget : Nat) : Prop :=
  forall input, cost algorithm input <= budget

/-- FPOD Definition 281.3, in a bounded-resource form: an evaluator is exact and its
supplied cost model stays within one explicit acceptable budget. -/
def Computable {Input : Type uInput} {Output : Type uOutput}
    (specification algorithm : Input -> Output)
    (cost : (Input -> Output) -> Input -> Nat) (budget : Nat) : Prop :=
  AlgorithmImplements specification algorithm /\ ComplexityBound cost algorithm budget

/-- Classify a complete transcript law by the probability-one event from the imported
infinite-product witness. -/
def lawClassifier (law : Measure (Nat -> Bool)) : Bool :=
  if law distinguishingEvent = 1 then true else false

/-- A noiseless one-observation Boolean statistical model. -/
def deterministicBoolLaw (model : Bool) : Measure Bool :=
  Measure.dirac model

/-- Every positive sample size exposes the same noiseless Boolean observation. -/
def deterministicBoolReadout (_n : Nat) : Bool -> Bool :=
  id

/-- The full evidence merges `none` with `some false`, but is injective on `some`. -/
def nonparametricEvidence : Option Bool -> Bool
  | none => false
  | some value => value

/-- The nonparametric target retains the entire optional Boolean model. -/
def nonparametricTarget : Option Bool -> Option Bool :=
  id

/-- The two-point parametric subclass is decoded by restoring the `some` constructor. -/
def parametricAlgorithm : Bool -> Option Bool :=
  some

private theorem stateLaw_identifiable :
    Identifiable stateLaw (id : Bool -> Bool) := by
  rcases infinite_identification_not_finite_exact_tomography with
    ⟨_, _, _, lowerProbability, upperProbability, _⟩
  intro first second sameLaw
  cases first <;> cases second
  · rfl
  · have sameProbability :=
      congrArg (fun law : Measure (Nat -> Bool) => law distinguishingEvent) sameLaw
    rw [lowerProbability, upperProbability] at sameProbability
    exact (zero_ne_one sameProbability).elim
  · have sameProbability :=
      congrArg (fun law : Measure (Nat -> Bool) => law distinguishingEvent) sameLaw
    rw [upperProbability, lowerProbability] at sameProbability
    exact (one_ne_zero sameProbability).elim
  · rfl

private theorem stateLaw_not_estimable :
    Not (Estimable (fun n => Fin n -> Bool) stateLaw finiteTranscript
      (id : Bool -> Bool)) := by
  rcases infinite_identification_not_finite_exact_tomography with
    ⟨_, _, _, _, _, noFiniteDecoder⟩
  rintro ⟨n, _positive, estimator, accurate⟩
  exact noFiniteDecoder ⟨n, estimator, accurate false, accurate true⟩

private theorem deterministicBool_estimable :
    Estimable (fun _ => Bool) deterministicBoolLaw deterministicBoolReadout
      (id : Bool -> Bool) := by
  refine ⟨1, by decide, id, ?_⟩
  intro model
  simp [deterministicBoolLaw, deterministicBoolReadout]

/-- Principle 281.1, first witness: complete laws identify the Boolean state while no
positive finite prefix has an almost-surely exact decoder. -/
theorem identifiable_not_finite_sample_accurate :
    Identifiable stateLaw (id : Bool -> Bool) /\
      Not (Estimable (fun n => Fin n -> Bool) stateLaw finiteTranscript
        (id : Bool -> Bool)) :=
  ⟨stateLaw_identifiable, stateLaw_not_estimable⟩
#print axioms identifiable_not_finite_sample_accurate

/-- Principle 281.1, second witness: a noiseless finite sample is exact, but the same
evaluator exceeds the declared positive resource budget in the supplied cost model. -/
theorem finite_sample_accurate_not_computable :
    Estimable (fun _ => Bool) deterministicBoolLaw deterministicBoolReadout
        (id : Bool -> Bool) /\
      Not (Computable (id : Bool -> Bool) id (fun _algorithm _input => 2) 1) := by
  refine ⟨deterministicBool_estimable, ?_⟩
  rintro ⟨_correct, bounded⟩
  have impossible := bounded false
  norm_num [ComplexityBound] at impossible
#print axioms finite_sample_accurate_not_computable

/-- Principle 281.1, reverse witness: an exact bounded algorithm works on the two-point
`some` subclass, while the target is not identifiable on the full `Option Bool` class. -/
theorem parametric_algorithm_not_nonparametric_identifiable :
    IdentificationFormula
        (fun value : Bool => nonparametricEvidence (some value))
        (fun value : Bool => nonparametricTarget (some value)) parametricAlgorithm /\
      Computable parametricAlgorithm parametricAlgorithm (fun _algorithm _input => 1) 1 /\
      Not (Identifiable nonparametricEvidence nonparametricTarget) := by
  refine ⟨?_, ?_, ?_⟩
  · intro value
    cases value <;> rfl
  · constructor
    · intro value
      rfl
    · intro value
      rfl
  · intro inclusion
    have impossible : (none : Option Bool) = some false :=
      inclusion (x := none) (y := some false) rfl
    simp at impossible
#print axioms parametric_algorithm_not_nonparametric_identifiable

/-- Principle 281.2, semantic-to-formula witness: a valid kernel theorem does not certify
an independently registered, incorrect candidate formula. -/
theorem semantic_kernel_does_not_certify_candidate_formula :
    Identifiable (id : Bool -> Bool) id /\
      Not (IdentificationFormula (id : Bool -> Bool) id Bool.not) := by
  constructor
  · intro _first _second same
    exact same
  · intro candidateCorrect
    have impossible := candidateCorrect false
    simp at impossible
#print axioms semantic_kernel_does_not_certify_candidate_formula

/-- Principle 281.2, formula-to-sampling witness: the complete-law classifier is an exact
identification formula, but no positive finite prefix supplies an exact sampling theorem. -/
theorem identification_formula_does_not_replace_sampling_theorem :
    IdentificationFormula stateLaw (id : Bool -> Bool) lawClassifier /\
      Not (Estimable (fun n => Fin n -> Bool) stateLaw finiteTranscript
        (id : Bool -> Bool)) := by
  rcases infinite_identification_not_finite_exact_tomography with
    ⟨_, _, _, lowerProbability, upperProbability, _⟩
  constructor
  · intro state
    cases state
    · simp [lawClassifier, lowerProbability]
    · simp [lawClassifier, upperProbability]
  · exact stateLaw_not_estimable
#print axioms identification_formula_does_not_replace_sampling_theorem

/-- Principle 281.2, sampling-to-algorithm witness: the one-sample identity estimator is
exact, while the separately registered Boolean-negation algorithm does not implement it. -/
theorem sampling_theorem_does_not_certify_candidate_algorithm :
    FiniteSampleAccurateAt (fun _ => Bool) deterministicBoolLaw
        deterministicBoolReadout (id : Bool -> Bool) 1 /\
      Not (AlgorithmImplements (id : Bool -> Bool) Bool.not) := by
  constructor
  · refine ⟨id, ?_⟩
    intro model
    simp [deterministicBoolLaw, deterministicBoolReadout]
  · intro algorithmCorrect
    have impossible := algorithmCorrect false
    simp at impossible
#print axioms sampling_theorem_does_not_certify_candidate_algorithm

/-- Principle 281.2, algorithm-to-complexity witness: identity implements identity, while
the supplied cost two exceeds the declared positive budget one. -/
theorem algorithm_does_not_replace_complexity_bound :
    AlgorithmImplements (id : Bool -> Bool) id /\
      Not (ComplexityBound
        (fun (_algorithm : Bool -> Bool) (_input : Bool) => 2) id 1) := by
  constructor
  · intro value
    rfl
  · intro bounded
    have impossible := bounded false
    norm_num at impossible
#print axioms algorithm_does_not_replace_complexity_bound

/- Degeneracy audit: equality of the evidence and target kernels makes identification
reflexive, including constant maps. -/
example {Model : Type uModel} {Evidence : Type uEvidence} {Target : Type uTarget}
    (evidence : Model -> Evidence) (target : Model -> Target)
    (sameKernel : Setoid.ker evidence = Setoid.ker target) :
    Identifiable evidence target := by
  rw [Identifiable, sameKernel]

example {Model : Type uModel} :
    Identifiable (fun _ : Model => ()) (fun _ : Model => ()) := by
  intro _first _second _same
  rfl

/- Empty carriers make the semantic implication vacuous. -/
example :
    Identifiable ((fun model : Empty => model.elim) : Empty -> Unit)
      ((fun model : Empty => model.elim) : Empty -> Bool) := by
  intro model
  exact model.elim

/- A one-point model and a finite two-point noiseless model can satisfy all three layers. -/
example :
    Identifiable (id : Unit -> Unit) id /\
      Estimable (fun _ => Unit) (fun _ : Unit => Measure.dirac ())
        (fun _ => id) id /\
      Computable (id : Unit -> Unit) id (fun _algorithm _input => 1) 1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro _first _second _same
    rfl
  · refine ⟨1, by decide, id, ?_⟩
    intro model
    simp
  · exact ⟨fun _ => rfl, fun _ => le_rfl⟩

example :
    Identifiable (id : Bool -> Bool) id /\
      Estimable (fun _ => Bool) deterministicBoolLaw deterministicBoolReadout id /\
      Computable (id : Bool -> Bool) id (fun _algorithm _input => 1) 1 := by
  refine ⟨?_, deterministicBool_estimable, ?_⟩
  · intro _first _second same
    exact same
  · exact ⟨fun _ => rfl, fun _ => le_rfl⟩

/- The imported overlap argument also rejects the zero-sample decoder, even though
`Estimable` excludes zero structurally by requiring a positive sample size. -/
example :
    Not (FiniteSampleAccurateAt (fun n => Fin n -> Bool) stateLaw finiteTranscript
      (id : Bool -> Bool) 0) := by
  rcases infinite_identification_not_finite_exact_tomography with
    ⟨_, _, _, _, _, noFiniteDecoder⟩
  rintro ⟨decoder, accurate⟩
  exact noFiniteDecoder ⟨0, decoder, accurate false, accurate true⟩

end

end D5.S3.ConceptDynamics.Identifiability.IdentifiabilityEstimabilityComputation
