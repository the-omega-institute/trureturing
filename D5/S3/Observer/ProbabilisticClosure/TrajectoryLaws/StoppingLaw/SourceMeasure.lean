/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SourceMeasure
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/StoppingLaw/SourceMeasure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The original iid spin and fair phase measure computes finite tree laws exactly. -/
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.SemanticNormalization
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.WitnessSharpness
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw.FiniteLawTransport
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.MeasureTheory.Measure.Real

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw

instance : MeasurableSpace Execution := ⊤
instance : MeasurableSingletonClass Execution := ⟨fun _ => trivial⟩
deriving instance Countable for Execution
deriving instance Countable for Observation
instance : MeasurableSpace Observation := ⊤
instance : MeasurableSingletonClass Observation := ⟨fun _ => trivial⟩

abbrev SourcePoint := Bool × Spins

def Bias.parameter (β : Bias) : unitInterval := ⟨β.p, β.pos.le, β.lt_one.le⟩

def spinMarginal (β : Bias) : Measure Bool :=
  bernoulliMeasure true false β.parameter

/-- Bernoulli(p) spins on all integer indices, without deleting separator coordinates. -/
def spinLaw (β : Bias) : Measure Spins := Measure.infinitePi (fun _ : ℤ => spinMarginal β)

def fairPhase : Measure Bool := bernoulliMeasure true false (⟨(1 : ℝ) / 2, by norm_num, by norm_num⟩ : unitInterval)

/-- The fair phase is independent of the entire iid integer spin family. -/
def sourceLaw (β : Bias) : Measure SourcePoint := fairPhase.prod (spinLaw β)

instance (β : Bias) : IsProbabilityMeasure (spinMarginal β) := by
  unfold spinMarginal; infer_instance
instance (β : Bias) : IsProbabilityMeasure (spinLaw β) := by
  unfold spinLaw; infer_instance
instance : IsProbabilityMeasure fairPhase := by unfold fairPhase; infer_instance
instance (β : Bias) : IsProbabilityMeasure (sourceLaw β) := by
  unfold sourceLaw; infer_instance

theorem spinMarginal_singleton (β : Bias) (s : Bool) :
    (spinMarginal β).real {s} = β.π s := by
  cases s <;> simp [spinMarginal, bernoulliMeasure_real_apply, Bias.parameter, Bias.π]

theorem fairPhase_singleton (φ : Bool) : fairPhase.real {φ} = 1 / 2 := by
  cases φ <;> norm_num [fairPhase, bernoulliMeasure_real_apply]

/-- A finite marginal is the positive weighted model used by the rigidity core. -/
theorem finiteSpinMeasure_mass (β : Bias) (V : Finset ℤ) (E : Set (V → Bool)) :
    (Measure.pi (fun _ : V => spinMarginal β)).real E = FiniteSpinLaw.mass β E := by
  classical
  let μ := Measure.pi (fun _ : V => spinMarginal β)
  have hs (σ : V → Bool) : μ.real {σ} = FiniteSpinLaw.weight β σ := by
    simp only [μ, measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod,
      FiniteSpinLaw.weight]
    exact Finset.prod_congr rfl (fun i _ => spinMarginal_singleton β (σ i))
  have he : (↑(Finset.univ.filter (fun σ : V → Bool => σ ∈ E)) : Set (V → Bool)) = E := by
    ext σ; simp
  calc
    μ.real E = ∑ σ ∈ Finset.univ.filter (fun σ : V → Bool => σ ∈ E), μ.real {σ} := by
      have hsum := sum_measureReal_singleton (μ := μ)
        (Finset.univ.filter (fun σ : V → Bool => σ ∈ E))
      rw [he] at hsum
      exact hsum.symm
    _ = FiniteSpinLaw.mass β E := by
      simp only [Finset.sum_filter, hs, FiniteSpinLaw.mass]
      apply Finset.sum_congr
      · ext σ; simp
      · intro σ _; rfl

/-- Arbitrary finite-support events have their exact original infinite-source mass. -/
theorem spinLaw_finite_event (β : Bias) (V : Finset ℤ) (E : Set Spins)
    (hE : ∀ S R, (∀ i ∈ V, S i = R i) → (S ∈ E ↔ R ∈ E)) :
    (spinLaw β).real E = SpinWindow.prob β V E := by
  let A : Set (V → Bool) := SpinWindow.extend V ⁻¹' E
  have he : E = V.restrict ⁻¹' A := by
    ext S
    apply hE S (SpinWindow.extend V (V.restrict S))
    intro i hi; simp [SpinWindow.extend, hi, Finset.restrict]
  have hm : MeasurableSet A := MeasurableSet.of_discrete
  calc
    (spinLaw β).real E = ((spinLaw β).map V.restrict).real A := by
      rw [map_measureReal_apply (V.measurable_restrict) hm]
      exact congrArg (spinLaw β).real he
    _ = (Measure.pi (fun _ : V => spinMarginal β)).real A := by
      rw [spinLaw, Measure.infinitePi_map_restrict]
    _ = SpinWindow.prob β V E := finiteSpinMeasure_mass β V A

theorem measurable_visible (φ : Bool) (t : ℤ) : Measurable (fun S : Spins => visible φ S t) := by
  unfold visible
  split_ifs
  · change Measurable (fun S : Spins => Bool.xor (S ((t - φ.toInt) / 2))
      (S ((t - φ.toInt) / 2 + 1)))
    exact (measurable_of_countable (fun p : Bool × Bool => Bool.xor p.1 p.2)).comp
      ((measurable_pi_apply (X := fun _ : ℤ => Bool) ((t - φ.toInt) / 2)).prodMk
        (measurable_pi_apply (X := fun _ : ℤ => Bool) ((t - φ.toInt) / 2 + 1)))
  · exact measurable_const

theorem measurable_hidden (φ : Bool) (t : ℤ) : Measurable (fun S : Spins => hidden φ S t) := by
  unfold hidden
  split_ifs <;> exact (measurable_of_countable _).comp (measurable_pi_apply _)

theorem ReadTree.measurable_source_run (T : ReadTree) (φ : Bool) :
    Measurable (fun S : Spins => T.run (visible φ S)) := by
  induction T with
  | leaf a => exact measurable_const
  | read t z o hz ho =>
    have hr : Measurable (fun S : Spins =>
        if visible φ S t then o.run (visible φ S) else z.run (visible φ S)) :=
      ho.ite ((measurable_visible φ t) (measurableSet_singleton true)) hz
    exact (measurable_of_countable (fun p : Bool × Execution =>
      p.2.prepend t p.1)).comp ((measurable_visible φ t).prodMk hr)

theorem measurable_observation (j : Bool) (T : ReadTree) :
    Measurable (fun z : SourcePoint => observation j z.1 T z.2) := by
  apply measurable_from_prod_countable_right
  intro φ
  exact (measurable_of_countable (fun p : Hidden × Execution =>
    (⟨p.1, p.2.output, p.2.returned, p.2.paid⟩ : Observation))).comp
      ((measurable_hidden φ j.toInt).prodMk (T.measurable_source_run φ))

/-- Averaging any measurable source event over the two original phases. -/
theorem sourceLaw_real_sections (β : Bias) (E : Set SourcePoint) (hE : MeasurableSet E) :
    (sourceLaw β).real E = (∑ φ : Bool, (spinLaw β).real {S | (φ, S) ∈ E}) / 2 := by
  have he : E = ⋃ φ : Bool, ({φ} ×ˢ {S | (φ, S) ∈ E}) := by ext z; simp
  have hd : Pairwise (fun φ ψ : Bool => Disjoint
      ({φ} ×ˢ {S | (φ, S) ∈ E}) ({ψ} ×ˢ {S | (ψ, S) ∈ E})) := by
    intro φ ψ hne
    exact Set.disjoint_left.mpr (by rintro z ⟨hφ, _⟩ ⟨hψ, _⟩; exact hne (hφ.symm.trans hψ))
  conv_lhs => rw [he]
  rw [measureReal_iUnion_fintype hd (fun φ =>
    (measurableSet_singleton φ).prod (measurable_prodMk_left hE))]
  simp only [sourceLaw, measureReal_prod_prod, fairPhase_singleton]
  rw [← Finset.mul_sum]
  ring

/-- The actual original (H_j,O,D,N) law, with all nonreturn depths retained. -/
theorem sourceLaw_observation (β : Bias) (j : Bool) (T : ReadTree) (z : Observation) :
    (sourceLaw β).real {s | observation j s.1 T s.2 = z} =
      fullMass β (lawWindow T) j T z := by
  rw [sourceLaw_real_sections β {s | observation j s.1 T s.2 = z}
    ((measurable_observation j T) (measurableSet_singleton z))]
  unfold fullMass
  congr 1
  apply Finset.sum_congr rfl
  intro φ _
  apply spinLaw_finite_event β (lawWindow T)
  intro S R h
  change observation j φ T S = z ↔ observation j φ T R = z
  rw [observation_eq_of_agree j φ T S R h]

/-- The same finite-support projection also preserves actual-read events. -/
theorem sourceLaw_remote (β : Bias) (j : Bool) (R : ℕ) (T : ReadTree) :
    (sourceLaw β).real {s | ∃ a ∈ (T.run (visible s.1 s.2)).record, Far j R a.1} =
      remoteMass β (lawWindow T) j R T := by
  have hm : Measurable (fun s : SourcePoint => T.run (visible s.1 s.2)) :=
    measurable_from_prod_countable_right (T.measurable_source_run)
  rw [sourceLaw_real_sections β {s | ∃ a ∈ (T.run (visible s.1 s.2)).record, Far j R a.1}
    (hm (MeasurableSet.of_discrete (s := {v : Execution | ∃ a ∈ v.record, Far j R a.1})))]
  unfold remoteMass
  congr 1
  apply Finset.sum_congr rfl
  intro φ _
  apply spinLaw_finite_event β (lawWindow T)
  intro S S' h
  have hr := T.source_run_eq_of_agree φ S S' (fun i hi => h i (Finset.mem_union_left _ hi))
  simp only [Set.mem_setOf_eq, hr, remoteEvent]

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.StoppingLaw
