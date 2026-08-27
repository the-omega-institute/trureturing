/- GID: D5/S3/Estimation/ExperimentCost/OutputStateRandomnessSeparation
   generality: G
   mirror-B: D5/B/S3/Estimation/ExperimentCost/OutputStateRandomnessSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Bool kernels separate state, output, and prior randomness, including zero cases. -/
/- Library-search audit trail (2026-08-25):
   * `SingleSampleLawNonimplication` concerns one coupled sample, not randomness sources.
   * `PointwiseAlmostEverywhereSeparation` concerns exact versus a.e. factorization.
   * `TranslationLossMonotonicity` concerns deterministic postprocessing of target defects.
   * `PositivePriorConditionalIndependence` concerns sufficiency under positive priors.
   * `BlackwellCostOrthogonality` uses measure kernels, but its cost order is unrelated.
   * Pinned Mathlib hits `PMF.pure_bind`, `PMF.bind_pure`, `PMF.bind_const`,
     `PMF.mem_support_pure_iff`, and `PMF.mem_support_uniformOfFintype` are used below.
   * No repository theorem packages the two output-state countermodels or three sources.
   * No prime parameter, primality assumption, natural index, or `n = 0` case occurs here.
-/

import Mathlib.Probability.Distributions.Uniform

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Estimation.ExperimentCost.OutputStateRandomnessSeparation

/-- A discrete law is nondegenerate when two distinct values lie in its support. -/
def NondegenerateLaw {A : Type*} (law : PMF A) : Prop :=
  ∃ left right, left ≠ right ∧ left ∈ law.support ∧ right ∈ law.support

/-- A finite-interface law assigns an output PMF to each input state. -/
abbrev DiscreteKernel (State Output : Type*) := State → PMF Output

/-- The output law obtained by sampling the state law and then the interface kernel. -/
def inducedOutputLaw {State Output : Type*}
    (stateLaw : PMF State) (kernel : DiscreteKernel State Output) : PMF Output :=
  stateLaw.bind kernel

/-- A minimal three-stage Boolean model: initial prior, state transition, and measurement. -/
structure BoolUncertaintyModel where
  prior : PMF Bool
  stateKernel : DiscreteKernel Bool Bool
  measurementKernel : DiscreteKernel Bool Bool

/-- Prior uncertainty means that the initial-state law is nondegenerate. -/
def PriorUncertainty (model : BoolUncertaintyModel) : Prop :=
  NondegenerateLaw model.prior

/-- State uncertainty means that some fixed initial state has a nondegenerate next-state law. -/
def StateUncertainty (model : BoolUncertaintyModel) : Prop :=
  ∃ initial, NondegenerateLaw (model.stateKernel initial)

/-- Measurement noise means that some fixed state has a nondegenerate measurement law. -/
def MeasurementNoise (model : BoolUncertaintyModel) : Prop :=
  ∃ state, NondegenerateLaw (model.measurementKernel state)

/-- The observable law produced by the prior, state kernel, and measurement kernel. -/
def observableLaw (model : BoolUncertaintyModel) : PMF Bool :=
  model.prior.bind fun initial =>
    (model.stateKernel initial).bind model.measurementKernel

/-- Only the state transition is random; the prior and measurement rows are Dirac. -/
def stateOnlyModel : BoolUncertaintyModel where
  prior := PMF.pure false
  stateKernel := fun _ => PMF.uniformOfFintype Bool
  measurementKernel := PMF.pure

/-- Only the measurement is random; the prior and state-transition rows are Dirac. -/
def measurementOnlyModel : BoolUncertaintyModel where
  prior := PMF.pure false
  stateKernel := PMF.pure
  measurementKernel := fun _ => PMF.uniformOfFintype Bool

/-- Only the prior is random; both kernels are identity-valued Dirac kernels. -/
def priorOnlyModel : BoolUncertaintyModel where
  prior := PMF.uniformOfFintype Bool
  stateKernel := PMF.pure
  measurementKernel := PMF.pure

/-- A model with a Dirac prior and deterministic state and measurement maps. -/
def deterministicModel
    (initial : Bool) (stateMap measurementMap : Bool → Bool) : BoolUncertaintyModel where
  prior := PMF.pure initial
  stateKernel := fun state => PMF.pure (stateMap state)
  measurementKernel := fun state => PMF.pure (measurementMap state)

private theorem fair_bool_law_nondegenerate :
    NondegenerateLaw (PMF.uniformOfFintype Bool) := by
  exact ⟨false, true, Bool.false_ne_true,
    PMF.mem_support_uniformOfFintype false,
    PMF.mem_support_uniformOfFintype true⟩

/-- A Dirac PMF has singleton support and is therefore degenerate. -/
theorem dirac_law_is_degenerate {A : Type*} (value : A) :
    ¬NondegenerateLaw (PMF.pure value) := by
  rintro ⟨left, right, distinct, leftSupport, rightSupport⟩
  have left_eq : left = value :=
    (PMF.mem_support_pure_iff value left).mp leftSupport
  have right_eq : right = value :=
    (PMF.mem_support_pure_iff value right).mp rightSupport
  exact distinct (left_eq.trans right_eq.symm)

#print axioms dirac_law_is_degenerate

/-- A Dirac state law and a fair interface row witness random output at a fixed state. -/
theorem fixed_state_random_output :
    ∃ (state : Bool) (stateLaw : PMF Bool) (kernel : DiscreteKernel Bool Bool),
      stateLaw = PMF.pure state ∧
        NondegenerateLaw (kernel state) ∧
        NondegenerateLaw (inducedOutputLaw stateLaw kernel) := by
  refine ⟨false, PMF.pure false, fun _ => PMF.uniformOfFintype Bool, rfl,
    fair_bool_law_nondegenerate, ?_⟩
  simpa [inducedOutputLaw] using fair_bool_law_nondegenerate

#print axioms fixed_state_random_output

/-- A fair state law and a constant Dirac kernel witness deterministic output. -/
theorem random_state_deterministic_output :
    ∃ (stateLaw : PMF Bool) (kernel : DiscreteKernel Bool Bool) (output : Bool),
      NondegenerateLaw stateLaw ∧
        (∀ state, kernel state = PMF.pure output) ∧
        inducedOutputLaw stateLaw kernel = PMF.pure output := by
  refine ⟨PMF.uniformOfFintype Bool, fun _ => PMF.pure false, false,
    fair_bool_law_nondegenerate, fun _ => rfl, ?_⟩
  simp [inducedOutputLaw]

#print axioms random_state_deterministic_output

/-- Random output does not imply a random state law, and a random state law does not imply
random output. The two implications are refuted by the preceding concrete witnesses. -/
theorem output_state_randomness_nonimplication :
    (¬∀ (stateLaw : PMF Bool) (kernel : DiscreteKernel Bool Bool),
      NondegenerateLaw (inducedOutputLaw stateLaw kernel) →
        NondegenerateLaw stateLaw) ∧
    (¬∀ (stateLaw : PMF Bool) (kernel : DiscreteKernel Bool Bool),
      NondegenerateLaw stateLaw →
        NondegenerateLaw (inducedOutputLaw stateLaw kernel)) := by
  constructor
  · intro implication
    obtain ⟨state, stateLaw, kernel, fixed, _, outputRandom⟩ :=
      fixed_state_random_output
    have stateRandom := implication stateLaw kernel outputRandom
    rw [fixed] at stateRandom
    exact dirac_law_is_degenerate state stateRandom
  · intro implication
    obtain ⟨stateLaw, kernel, output, stateRandom, _, outputLaw⟩ :=
      random_state_deterministic_output
    have outputRandom := implication stateLaw kernel stateRandom
    rw [outputLaw] at outputRandom
    exact dirac_law_is_degenerate output outputRandom

#print axioms output_state_randomness_nonimplication

/-- The three named Boolean models each contain exactly one of the three uncertainty sources. -/
theorem single_source_models_isolate_uncertainties :
    (StateUncertainty stateOnlyModel ∧
      ¬MeasurementNoise stateOnlyModel ∧
      ¬PriorUncertainty stateOnlyModel) ∧
    (¬StateUncertainty measurementOnlyModel ∧
      MeasurementNoise measurementOnlyModel ∧
      ¬PriorUncertainty measurementOnlyModel) ∧
    (¬StateUncertainty priorOnlyModel ∧
      ¬MeasurementNoise priorOnlyModel ∧
      PriorUncertainty priorOnlyModel) := by
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · change ∃ _ : Bool, NondegenerateLaw (PMF.uniformOfFintype Bool)
      exact ⟨false, fair_bool_law_nondegenerate⟩
    · change ¬∃ state : Bool, NondegenerateLaw (PMF.pure state)
      rintro ⟨state, random⟩
      exact dirac_law_is_degenerate state random
    · change ¬NondegenerateLaw (PMF.pure false)
      exact dirac_law_is_degenerate false
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · change ¬∃ state : Bool, NondegenerateLaw (PMF.pure state)
      rintro ⟨state, random⟩
      exact dirac_law_is_degenerate state random
    · change ∃ _ : Bool, NondegenerateLaw (PMF.uniformOfFintype Bool)
      exact ⟨false, fair_bool_law_nondegenerate⟩
    · change ¬NondegenerateLaw (PMF.pure false)
      exact dirac_law_is_degenerate false
  · refine ⟨?_, ?_, ?_⟩
    · change ¬∃ state : Bool, NondegenerateLaw (PMF.pure state)
      rintro ⟨state, random⟩
      exact dirac_law_is_degenerate state random
    · change ¬∃ state : Bool, NondegenerateLaw (PMF.pure state)
      rintro ⟨state, random⟩
      exact dirac_law_is_degenerate state random
    · change NondegenerateLaw (PMF.uniformOfFintype Bool)
      exact fair_bool_law_nondegenerate

#print axioms single_source_models_isolate_uncertainties

/-- All three single-source models induce the same fair Boolean observation law. -/
theorem single_source_models_observationally_equal :
    observableLaw stateOnlyModel = PMF.uniformOfFintype Bool ∧
      observableLaw measurementOnlyModel = PMF.uniformOfFintype Bool ∧
      observableLaw priorOnlyModel = PMF.uniformOfFintype Bool := by
  simp [observableLaw, stateOnlyModel, measurementOnlyModel, priorOnlyModel]

#print axioms single_source_models_observationally_equal

/-- Every directed implication between the three uncertainty predicates has a countermodel. -/
theorem uncertainty_sources_pairwise_do_not_imply :
    (¬∀ model, StateUncertainty model → MeasurementNoise model) ∧
    (¬∀ model, MeasurementNoise model → StateUncertainty model) ∧
    (¬∀ model, StateUncertainty model → PriorUncertainty model) ∧
    (¬∀ model, PriorUncertainty model → StateUncertainty model) ∧
    (¬∀ model, MeasurementNoise model → PriorUncertainty model) ∧
    (¬∀ model, PriorUncertainty model → MeasurementNoise model) := by
  have isolated := single_source_models_isolate_uncertainties
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro implication
    exact isolated.1.2.1 (implication stateOnlyModel isolated.1.1)
  · intro implication
    exact isolated.2.1.1 (implication measurementOnlyModel isolated.2.1.2.1)
  · intro implication
    exact isolated.1.2.2 (implication stateOnlyModel isolated.1.1)
  · intro implication
    exact isolated.2.2.1 (implication priorOnlyModel isolated.2.2.2.2)
  · intro implication
    exact isolated.2.1.2.2 (implication measurementOnlyModel isolated.2.1.2.1)
  · intro implication
    exact isolated.2.2.2.1 (implication priorOnlyModel isolated.2.2.2.2)

#print axioms uncertainty_sources_pairwise_do_not_imply

/-- No PMF exists on the empty carrier, since its total mass cannot equal one. -/
theorem empty_type_has_no_probability_law : ¬Nonempty (PMF Empty) := by
  rintro ⟨law⟩
  have totalMass := law.tsum_coe
  simpa using totalMass

#print axioms empty_type_has_no_probability_law

/-- Every singleton state law is degenerate, but its only kernel row can still be random. -/
theorem singleton_state_can_still_have_random_output :
    (∀ stateLaw : PMF PUnit, ¬NondegenerateLaw stateLaw) ∧
      ∃ kernel : DiscreteKernel PUnit Bool,
        NondegenerateLaw (kernel PUnit.unit) := by
  constructor
  · intro stateLaw
    rintro ⟨left, right, distinct, _, _⟩
    exact distinct (Subsingleton.elim left right)
  · exact ⟨fun _ => PMF.uniformOfFintype Bool, fair_bool_law_nondegenerate⟩

#print axioms singleton_state_can_still_have_random_output

/-- A deterministic kernel evaluated at a fixed state always returns a degenerate Dirac law. -/
theorem deterministic_kernel_cannot_witness_random_output
    {State Output : Type*} (state : State) (readout : State → Output) :
    ¬NondegenerateLaw ((fun x => PMF.pure (readout x)) state) := by
  simpa using dirac_law_is_degenerate (readout state)

#print axioms deterministic_kernel_cannot_witness_random_output

/-- If the prior and both kernels are Dirac, the observed law is the composed point mass. -/
theorem zero_uncertainty_observation_is_deterministic
    (initial : Bool) (stateMap measurementMap : Bool → Bool) :
    observableLaw (deterministicModel initial stateMap measurementMap) =
      PMF.pure (measurementMap (stateMap initial)) := by
  simp [observableLaw, deterministicModel]

#print axioms zero_uncertainty_observation_is_deterministic

/-- FPOD Principle 202.1: output and state randomness are mutually nonimplicative, and
state-transition, measurement, and prior uncertainty are pairwise nonimplicative even though
their isolated Boolean models have the same observable law. -/
theorem fpod_principle_202_1 :
    ((¬∀ (stateLaw : PMF Bool) (kernel : DiscreteKernel Bool Bool),
        NondegenerateLaw (inducedOutputLaw stateLaw kernel) →
          NondegenerateLaw stateLaw) ∧
      (¬∀ (stateLaw : PMF Bool) (kernel : DiscreteKernel Bool Bool),
        NondegenerateLaw stateLaw →
          NondegenerateLaw (inducedOutputLaw stateLaw kernel))) ∧
    ((StateUncertainty stateOnlyModel ∧
        ¬MeasurementNoise stateOnlyModel ∧
        ¬PriorUncertainty stateOnlyModel) ∧
      (¬StateUncertainty measurementOnlyModel ∧
        MeasurementNoise measurementOnlyModel ∧
        ¬PriorUncertainty measurementOnlyModel) ∧
      (¬StateUncertainty priorOnlyModel ∧
        ¬MeasurementNoise priorOnlyModel ∧
        PriorUncertainty priorOnlyModel)) ∧
    ((¬∀ model, StateUncertainty model → MeasurementNoise model) ∧
      (¬∀ model, MeasurementNoise model → StateUncertainty model) ∧
      (¬∀ model, StateUncertainty model → PriorUncertainty model) ∧
      (¬∀ model, PriorUncertainty model → StateUncertainty model) ∧
      (¬∀ model, MeasurementNoise model → PriorUncertainty model) ∧
      (¬∀ model, PriorUncertainty model → MeasurementNoise model)) ∧
    (observableLaw stateOnlyModel = PMF.uniformOfFintype Bool ∧
      observableLaw measurementOnlyModel = PMF.uniformOfFintype Bool ∧
      observableLaw priorOnlyModel = PMF.uniformOfFintype Bool) := by
  exact ⟨output_state_randomness_nonimplication,
    single_source_models_isolate_uncertainties,
    uncertainty_sources_pairwise_do_not_imply,
    single_source_models_observationally_equal⟩

#print axioms fpod_principle_202_1

section DegenerateAudit

-- Identity maps give the point mass at the fixed initial state.
example : observableLaw (deterministicModel false id id) = PMF.pure false := by
  simpa using zero_uncertainty_observation_is_deterministic false id id

-- Constant, including zero-valued, maps still give a point mass rather than random output.
example :
    observableLaw (deterministicModel true (fun _ => false) (fun _ => false)) =
      PMF.pure false := by
  simpa using zero_uncertainty_observation_is_deterministic
    true (fun _ => false) (fun _ => false)

end DegenerateAudit

/-!
Hypothesis audit, declaration by declaration:

* The twelve public theorems have no proposition-valued hypotheses or typeclass parameters.
* Generic carrier and function arguments in the Dirac and deterministic-kernel theorems are
  used in their conclusions and proofs; all Boolean model data are explicit named definitions.
* `empty_type_has_no_probability_law` rejects the empty carrier, while the PUnit theorem proves
  that singleton state randomness is impossible but interface randomness remains possible.
* Dirac priors remove prior uncertainty only; `measurementOnlyModel` proves measurement noise
  can remain, and `stateOnlyModel` proves state-transition uncertainty can remain.
* Dirac kernel rows cannot satisfy the fixed-state random-output conclusion. When all three
  sources are Dirac, `zero_uncertainty_observation_is_deterministic` gives a Dirac observation.
* Identity, constant, and zero-valued maps are instantiated above. There is no natural-number
  depth or sample parameter, and no prime parameter or primality hypothesis to audit.

No public theorem has a removable logical hypothesis or instance. Consequently no necessary
hypothesis exists for which the requested named counterexample theorem would apply.
-/

end D5.S3.Estimation.ExperimentCost.OutputStateRandomnessSeparation
