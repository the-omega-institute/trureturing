/- GID: D5/S3/ConceptDynamics/InterventionsExchange/RandomizationBridge
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InterventionsExchange/RandomizationBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Randomization equates conditional, potential, and do laws; zero mass breaks it. -/
/- Library-search audit trail (2026-08-25):
   * Six-way repository searches found the exact pointwise predecessor
     `factual_intervention_consistency`, which is reused below, but no law-level bridge.
   * Nearby hits are distribution-specific geometric and zeta conditioning theorems;
     causal, measure-theoretic, posterior/prior, and information-theoretic vocabulary
     searches found no equivalent generic declaration.
   * LeanSearch returned no payload for the natural-language conditioning query.
     Local name and body searches found `IndepFun.measure_inter_preimage_eq_mul`,
     `ae_cond_of_forall_mem`, `cond_apply`, `cond_eq_zero_of_meas_eq_zero`, and
     `Measure.map_congr`; these pinned-Mathlib declarations are used directly.
   * `iIndepFun.cond` preserves independence within a conditioned family; it does not
     identify a coordinate's conditioned law with its original law. -/

import D5.S3.ConceptDynamics.InterventionsExchange.FactualInterventionConsistency
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InterventionsExchange.RandomizationBridge

open MeasureTheory ProbabilityTheory
open D5.S3.ConceptDynamics.InterventionsExchange.FactualInterventionConsistency

noncomputable section

universe uU uX uY

/-- The event on which the factual treatment takes the queried value. -/
def treatmentEvent {U : Type uU} {X : Type uX}
    (treatment : U -> X) (x : X) : Set U :=
  treatment ⁻¹' {x}

/-- The observed outcome obtained by evaluating the shared mechanism at its treatment. -/
def factualOutcome {U : Type uU} {X : Type uX} {Y : Type uY}
    (outcome : U -> X -> Y) (treatment : U -> X) : U -> Y :=
  fun u => outcome u (treatment u)

/-- The potential outcome under the fixed treatment value `x`. -/
def potentialOutcome {U : Type uU} {X : Type uX} {Y : Type uY}
    (outcome : U -> X -> Y) (x : X) : U -> Y :=
  fun u => outcome u x

/-- The outcome of the perfect intervention fixing treatment to `x`. -/
def doOutcome {U : Type uU} {X : Type uX} {Y : Type uY}
    (outcome : U -> X -> Y) (x : X) : U -> Y :=
  potentialOutcome outcome x

/-- Random assignment means treatment is independent of the full potential-outcome process. -/
def RandomAssignment {U : Type uU} {X : Type uX} {Y : Type uY}
    [MeasurableSpace U] [MeasurableSpace X] [MeasurableSpace Y]
    (mu : Measure U) (treatment : U -> X) (outcome : U -> X -> Y) : Prop :=
  IndepFun treatment outcome mu

/-- Positivity at `x` means that the queried treatment fiber has strictly positive mass. -/
def TreatmentPositivity {U : Type uU} {X : Type uX}
    [MeasurableSpace U] (mu : Measure U) (treatment : U -> X) (x : X) : Prop :=
  0 < mu (treatmentEvent treatment x)

/-- The factual outcome law after conditioning on the queried treatment fiber. -/
def conditionalOutcomeLaw {U : Type uU} {X : Type uX} {Y : Type uY}
    [MeasurableSpace U] [MeasurableSpace Y]
    (mu : Measure U) (treatment : U -> X) (outcome : U -> X -> Y)
    (x : X) : Measure Y :=
  Measure.map (factualOutcome outcome treatment) (mu[|treatmentEvent treatment x])

/-- The unconditional law of the potential outcome at `x`. -/
def potentialOutcomeLaw {U : Type uU} {X : Type uX} {Y : Type uY}
    [MeasurableSpace U] [MeasurableSpace Y]
    (mu : Measure U) (outcome : U -> X -> Y) (x : X) : Measure Y :=
  Measure.map (potentialOutcome outcome x) mu

/-- The outcome law under the perfect intervention fixing treatment to `x`. -/
def doOutcomeLaw {U : Type uU} {X : Type uX} {Y : Type uY}
    [MeasurableSpace U] [MeasurableSpace Y]
    (mu : Measure U) (outcome : U -> X -> Y) (x : X) : Measure Y :=
  Measure.map (doOutcome outcome x) mu

/-- Consistency lifts the pointwise factual/potential equality to the conditioned laws. -/
theorem conditional_factual_law_eq_conditional_potential_law
    {U : Type uU} {X : Type uX} {Y : Type uY}
    [MeasurableSpace U] [MeasurableSpace Y] [MeasurableSpace X]
    [MeasurableSingletonClass X]
    (mu : Measure U) (treatment : U -> X) (outcome : U -> X -> Y) (x : X)
    (treatmentMeasurable : Measurable treatment) :
    conditionalOutcomeLaw mu treatment outcome x =
      Measure.map (potentialOutcome outcome x) (mu[|treatmentEvent treatment x]) := by
  apply Measure.map_congr
  apply ae_cond_of_forall_mem
  · exact treatmentMeasurable (measurableSet_singleton x)
  · intro u hu
    apply factual_intervention_consistency outcome treatment u x
    simpa only [treatmentEvent, Set.mem_preimage, Set.mem_singleton_iff] using hu

#print axioms conditional_factual_law_eq_conditional_potential_law

/-- Random assignment and positivity remove conditioning from a fixed potential-outcome law. -/
theorem random_assignment_preserves_potential_law
    {U : Type uU} {X : Type uX} {Y : Type uY}
    [MeasurableSpace U] [MeasurableSpace Y] [MeasurableSpace X]
    [MeasurableSingletonClass X]
    (mu : Measure U) [IsFiniteMeasure mu]
    (treatment : U -> X) (outcome : U -> X -> Y) (x : X)
    (treatmentMeasurable : Measurable treatment)
    (outcomeMeasurable : Measurable outcome)
    (randomAssignment : RandomAssignment mu treatment outcome)
    (positivity : TreatmentPositivity mu treatment x) :
    Measure.map (potentialOutcome outcome x) (mu[|treatmentEvent treatment x]) =
      potentialOutcomeLaw mu outcome x := by
  have hEvent : MeasurableSet (treatmentEvent treatment x) :=
    treatmentMeasurable (measurableSet_singleton x)
  have hPotential : Measurable (potentialOutcome outcome x) :=
    (measurable_pi_apply x).comp outcomeMeasurable
  have hIndep : IndepFun treatment (potentialOutcome outcome x) mu := by
    have hBase : IndepFun treatment outcome mu := randomAssignment
    change IndepFun (id ∘ treatment) ((fun f => f x) ∘ outcome) mu
    exact hBase.comp measurable_id (measurable_pi_apply x)
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply_of_aemeasurable hPotential.aemeasurable hs]
  rw [potentialOutcomeLaw, Measure.map_apply_of_aemeasurable hPotential.aemeasurable hs]
  rw [cond_apply hEvent]
  rw [treatmentEvent]
  rw [hIndep.measure_inter_preimage_eq_mul {x} s (measurableSet_singleton x) hs]
  change 0 < mu (treatment ⁻¹' {x}) at positivity
  rw [← mul_assoc, ENNReal.inv_mul_cancel positivity.ne' (measure_ne_top mu _), one_mul]

#print axioms random_assignment_preserves_potential_law

/-- Shared SCM intervention semantics identifies a potential law with its perfect-do law. -/
theorem potential_outcome_law_eq_do_outcome_law
    {U : Type uU} {X : Type uX} {Y : Type uY}
    [MeasurableSpace U] [MeasurableSpace Y]
    (mu : Measure U) (outcome : U -> X -> Y) (x : X) :
    potentialOutcomeLaw mu outcome x = doOutcomeLaw mu outcome x := by
  rfl

#print axioms potential_outcome_law_eq_do_outcome_law

/-- Random assignment, consistency, and positivity identify observational and intervention laws. -/
theorem randomization_bridge
    {U : Type uU} {X : Type uX} {Y : Type uY}
    [MeasurableSpace U] [MeasurableSpace Y] [MeasurableSpace X]
    [MeasurableSingletonClass X]
    (mu : Measure U) [IsFiniteMeasure mu]
    (treatment : U -> X) (outcome : U -> X -> Y) (x : X)
    (treatmentMeasurable : Measurable treatment)
    (outcomeMeasurable : Measurable outcome)
    (randomAssignment : RandomAssignment mu treatment outcome)
    (positivity : TreatmentPositivity mu treatment x) :
    conditionalOutcomeLaw mu treatment outcome x = potentialOutcomeLaw mu outcome x ∧
      potentialOutcomeLaw mu outcome x = doOutcomeLaw mu outcome x := by
  constructor
  · rw [conditional_factual_law_eq_conditional_potential_law mu treatment outcome x
      treatmentMeasurable]
    exact random_assignment_preserves_potential_law mu treatment outcome x treatmentMeasurable
      outcomeMeasurable randomAssignment positivity
  · exact potential_outcome_law_eq_do_outcome_law mu outcome x

#print axioms randomization_bridge

/-- With zero treatment mass, mathlib's conditional law is zero while the do law is not. -/
theorem positive_treatment_probability_is_necessary :
    let mu : Measure Bool := (PMF.uniformOfFintype Bool).toMeasure
    let treatment : Bool -> Bool := fun _ => false
    let outcome : Bool -> Bool -> Bool := fun _ _ => false
    RandomAssignment mu treatment outcome ∧
      ¬ TreatmentPositivity mu treatment true ∧
      conditionalOutcomeLaw mu treatment outcome true ≠
        potentialOutcomeLaw mu outcome true := by
  dsimp only
  constructor
  · exact indepFun_const_left false (fun _ : Bool => fun _ : Bool => false)
  constructor
  · simp [TreatmentPositivity, treatmentEvent]
  · intro hLaw
    have hAtUniv := congrArg (fun law : Measure Bool => law Set.univ) hLaw
    have hConditionalMass :
        conditionalOutcomeLaw (PMF.uniformOfFintype Bool).toMeasure
          (fun _ : Bool => false) (fun _ _ : Bool => false) true Set.univ = 0 := by
      simp [conditionalOutcomeLaw, treatmentEvent]
    have hPotentialMass :
        potentialOutcomeLaw (PMF.uniformOfFintype Bool).toMeasure
          (fun _ _ : Bool => false) true Set.univ = 1 := by
      change (Measure.map (fun _ : Bool => false)
        (PMF.uniformOfFintype Bool).toMeasure) Set.univ = 1
      rw [Measure.map_apply_of_aemeasurable measurable_const.aemeasurable MeasurableSet.univ]
      simpa only [Set.preimage_univ] using
        (measure_univ (μ := (PMF.uniformOfFintype Bool).toMeasure))
    rw [hConditionalMass, hPotentialMass] at hAtUniv
    exact zero_ne_one hAtUniv

#print axioms positive_treatment_probability_is_necessary

/-- Infinite treatment mass also breaks the bridge despite independence and strict positivity. -/
theorem finite_measure_is_necessary :
    let mu : Measure Unit := (⊤ : ENNReal) • Measure.dirac ()
    let treatment : Unit -> Unit := fun _ => ()
    let outcome : Unit -> Unit -> Unit := fun _ _ => ()
    mu Set.univ = ⊤ ∧ RandomAssignment mu treatment outcome ∧
      TreatmentPositivity mu treatment () ∧
      conditionalOutcomeLaw mu treatment outcome () ≠
        potentialOutcomeLaw mu outcome () := by
  dsimp only
  have hRandom :
      RandomAssignment ((⊤ : ENNReal) • Measure.dirac ()) (fun _ : Unit => ())
        (fun _ _ : Unit => ()) := by
    rw [RandomAssignment, indepFun_iff_measure_inter_preimage_eq_mul]
    intro s t hs ht
    by_cases hsMem : () ∈ s <;>
      by_cases htMem : (fun _ : Unit => ()) ∈ t <;>
      simp [hsMem, htMem]
  have hPositive :
      TreatmentPositivity ((⊤ : ENNReal) • Measure.dirac ())
        (fun _ : Unit => ()) () := by
    simp [TreatmentPositivity, treatmentEvent]
  have hLawNe :
      conditionalOutcomeLaw ((⊤ : ENNReal) • Measure.dirac ())
          (fun _ : Unit => ()) (fun _ _ : Unit => ()) () ≠
        potentialOutcomeLaw ((⊤ : ENNReal) • Measure.dirac ())
          (fun _ _ : Unit => ()) () := by
    intro hLaw
    have hAtUniv := congrArg (fun law : Measure Unit => law Set.univ) hLaw
    simp [conditionalOutcomeLaw, potentialOutcomeLaw, treatmentEvent,
      potentialOutcome] at hAtUniv
  exact ⟨by simp, hRandom, hPositive, hLawNe⟩

#print axioms finite_measure_is_necessary

/-- Correlated treatment and outcomes violate the bridge even on a positive treatment fiber. -/
theorem random_assignment_is_necessary :
    let mu : Measure Bool := (PMF.uniformOfFintype Bool).toMeasure
    let treatment : Bool -> Bool := id
    let outcome : Bool -> Bool -> Bool := fun u _ => u
    Measurable treatment ∧ Measurable outcome ∧
      TreatmentPositivity mu treatment true ∧
      ¬ RandomAssignment mu treatment outcome ∧
      conditionalOutcomeLaw mu treatment outcome true ≠
        potentialOutcomeLaw mu outcome true := by
  dsimp only
  have hTreatment : Measurable (id : Bool -> Bool) := measurable_id
  have hOutcome : Measurable (fun u : Bool => fun _ : Bool => u) := by fun_prop
  have hPositive :
      TreatmentPositivity (PMF.uniformOfFintype Bool).toMeasure id true := by
    simp [TreatmentPositivity, treatmentEvent, PMF.uniformOfFintype_apply,
      Fintype.card_bool]
  have hLawNe :
      conditionalOutcomeLaw (PMF.uniformOfFintype Bool).toMeasure id
          (fun u : Bool => fun _ : Bool => u) true ≠
        potentialOutcomeLaw (PMF.uniformOfFintype Bool).toMeasure
          (fun u : Bool => fun _ : Bool => u) true := by
    intro hLaw
    have hAtFalse := congrArg (fun law : Measure Bool => law {false}) hLaw
    change (Measure.map id
        ((PMF.uniformOfFintype Bool).toMeasure[|({true} : Set Bool)])) {false} =
      (Measure.map id (PMF.uniformOfFintype Bool).toMeasure) {false} at hAtFalse
    rw [Measure.map_apply_of_aemeasurable measurable_id.aemeasurable
      (measurableSet_singleton false)] at hAtFalse
    rw [cond_apply (measurableSet_singleton true)] at hAtFalse
    rw [Measure.map_apply_of_aemeasurable measurable_id.aemeasurable
      (measurableSet_singleton false)] at hAtFalse
    norm_num [PMF.toMeasure_apply_singleton, PMF.uniformOfFintype_apply,
      Fintype.card_bool] at hAtFalse
    exact ENNReal.inv_ne_zero.mpr (by norm_num) hAtFalse.symm
  refine ⟨hTreatment, hOutcome, hPositive, ?_, hLawNe⟩
  intro hRandom
  exact hLawNe (randomization_bridge (PMF.uniformOfFintype Bool).toMeasure id
    (fun u : Bool => fun _ : Bool => u) true hTreatment hOutcome hRandom hPositive).1

#print axioms random_assignment_is_necessary

/-- Empty sample spaces cannot satisfy positivity, regardless of the finite measure. -/
example (mu : Measure Empty) (treatment : Empty -> Unit) :
    ¬ TreatmentPositivity mu treatment () := by
  have hEmpty : treatment ⁻¹' {()} = ∅ := by
    ext u
    exact Empty.elim u
  simp [TreatmentPositivity, treatmentEvent, hEmpty]

/-- The bridge remains valid for singleton sample, treatment, and outcome types. -/
example :
    let mu : Measure Unit := Measure.dirac ()
    let treatment : Unit -> Unit := fun _ => ()
    let outcome : Unit -> Unit -> Unit := fun _ _ => ()
    conditionalOutcomeLaw mu treatment outcome () = potentialOutcomeLaw mu outcome () ∧
      potentialOutcomeLaw mu outcome () = doOutcomeLaw mu outcome () := by
  dsimp only
  apply randomization_bridge
  · exact measurable_const
  · exact measurable_const
  · exact indepFun_const_left () (fun _ : Unit => fun _ : Unit => ())
  · simp [TreatmentPositivity, treatmentEvent]

end

end D5.S3.ConceptDynamics.InterventionsExchange.RandomizationBridge
