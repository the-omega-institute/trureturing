/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalLawTrimming
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalLawTrimming
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The original and positive-support marked laws share one visible realization and trimmed endpoint law. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalMarkedLaw
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.PositiveSupportPresentation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory Function
open scoped BigOperators Matrix Classical
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkedPredictiveQuotient
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalMarkedLaw
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.PositiveSupportPresentation
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.UnifilarPairSurvival

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalLawTrimming
universe u
variable {H : Type u} [Fintype H] [MeasurableSpace H] [MeasurableSingletonClass H]

/-- One selected actual law on the positive stationary support. -/
def retainedLaw (θ : Presentation H) : ProbabilityMeasure (PathSpace (Positive θ)) :=
  Classical.choose (original_law (trim θ))

theorem inclusion_measurable (θ : Presentation H) : Measurable (includePath θ) := by
  exact (Measurable.of_eval fun t => measurable_subtype_coe.comp
    ((measurable_pi_apply t).comp measurable_fst)).prodMk measurable_snd

/-- The original law is the actual inclusion pushforward of the selected retained law. -/
def jointLaw (θ : Presentation H) : ProbabilityMeasure (PathSpace H) :=
  (retainedLaw θ).map (includePath θ)

/-- The visible marginal of that same original hidden/output law. -/
def visibleLaw (θ : Presentation H) : ProbabilityMeasure (ℤ → Bool) :=
  (jointLaw θ).map Prod.snd

/-- The endpoint class event on the original space. Ghost states have no retained
class; their event fibers are empty and have zero actual mass. -/
def retainedEndpoint (θ : Presentation H) (t : ℤ) (n : ℕ)
    (w : Fin n → Bool) (a : FutureClass (trim θ).matrix) : Set (PathSpace H) :=
  {z | (∀ k : Fin n, z.2 (t + (k.val : ℤ)) = w k) ∧
    ∃ i : Positive θ, z.1 (t + n) = i.val ∧ classOf (trim θ).matrix i = a}

/-- Positive-support trimming preserves one selected original integer-time law
and its visible marginal. Unifilarity is required only of the retained rows. -/
theorem same_law_trimming (θ : Presentation H) :
    HasOriginalCylinders (jointLaw θ : Measure (PathSpace H)) θ ∧
    HasOriginalCylinders (retainedLaw θ : Measure (PathSpace (Positive θ))) (trim θ) ∧
    (retainedLaw θ : Measure (PathSpace (Positive θ))).map (includePath θ) = jointLaw θ ∧
    (retainedLaw θ : Measure (PathSpace (Positive θ))).map Prod.snd = visibleLaw θ ∧
    (∀ a : ℤ, (retainedLaw θ : Measure (PathSpace (Positive θ))).map (shift a) = retainedLaw θ) ∧
    (∀ a : ℤ, (jointLaw θ : Measure (PathSpace H)).map (shift a) = jointLaw θ) ∧
    (∀ a : ℤ, (visibleLaw θ : Measure (ℤ → Bool)).map (fun z t => z (a + t)) =
      visibleLaw θ) ∧
    (∀ (t : ℤ) (n : ℕ) (w : Fin n → Bool),
      (visibleLaw θ : Measure (ℤ → Bool)).real (visibleCylinder t n w) =
        ∑ i, θ.initial i * futureMass θ.matrix i n w) ∧
    (∀ᵐ z ∂(visibleLaw θ : Measure (ℤ → Bool)),
      ∀ t : ℤ, ¬(z t = true ∧ z (t + 1) = true)) ∧
    ((trim θ).matrix true * (trim θ).matrix true = 0) ∧
    (∀ (hu : RowUnifilar (trim θ).matrix) (t : ℤ) (n : ℕ)
      (w : Fin n → Bool) (a : FutureClass (trim θ).matrix),
      (jointLaw θ : Measure (PathSpace H)).real (retainedEndpoint θ t n w a) =
        ∑ i : Positive θ, (trim θ).initial i *
          if endpoint (quotientSuccessor (trim θ).matrix) n (classOf (trim θ).matrix i) w = a
          then wordMass (quotientMass (trim θ).matrix) (quotientSuccessor (trim θ).matrix)
            n (classOf (trim θ).matrix i) w else 0) := by
  have hr := Classical.choose_spec (original_law (trim θ))
  change HasOriginalCylinders (retainedLaw θ : Measure (PathSpace (Positive θ))) (trim θ) ∧ _ at hr
  have hc : HasOriginalCylinders (jointLaw θ : Measure (PathSpace H)) θ := by
    change HasOriginalCylinders ((retainedLaw θ : Measure (PathSpace (Positive θ))).map
      (includePath θ)) θ
    exact include_cylinders θ (retainedLaw θ : Measure (PathSpace (Positive θ))) hr.1
  have hp : (retainedLaw θ : Measure (PathSpace (Positive θ))).map Prod.snd = (visibleLaw θ : Measure (ℤ → Bool)) := by
    change _ = ((retainedLaw θ : Measure (PathSpace (Positive θ))).map (includePath θ)).map Prod.snd
    rw [Measure.map_map measurable_snd (inclusion_measurable θ)]
    rfl
  have hs (a : ℤ) : (jointLaw θ : Measure (PathSpace H)).map (shift a) = jointLaw θ := by
    change ((retainedLaw θ : Measure (PathSpace (Positive θ))).map (includePath θ)).map (shift a) = _
    have hm : Measurable (shift (H := H) a) := by
      exact (Measurable.of_eval fun t => (measurable_pi_apply (a+t)).comp measurable_fst).prodMk
        (Measurable.of_eval fun t => (measurable_pi_apply (a+t)).comp measurable_snd)
    have hmr : Measurable (shift (H := Positive θ) a) := by
      exact (Measurable.of_eval fun t => (measurable_pi_apply (a+t)).comp measurable_fst).prodMk
        (Measurable.of_eval fun t => (measurable_pi_apply (a+t)).comp measurable_snd)
    rw [Measure.map_map hm (inclusion_measurable θ)]
    have he : shift a ∘ includePath θ = includePath θ ∘ shift a := rfl
    rw [he, ← Measure.map_map (inclusion_measurable θ) hmr]
    have hsr : (retainedLaw θ : Measure (PathSpace (Positive θ))).map (shift a) =
        (retainedLaw θ : Measure (PathSpace (Positive θ))) := hr.2.1 a
    rw [hsr]
    rfl
  have hv (a : ℤ) : (visibleLaw θ : Measure (ℤ → Bool)).map (fun z t => z (a+t)) = visibleLaw θ := by
    change ((jointLaw θ : Measure (PathSpace H)).map Prod.snd).map _ = _
    rw [Measure.map_map (by fun_prop) measurable_snd]
    have he : (fun z : ℤ → Bool => fun t => z (a+t)) ∘
        (Prod.snd : PathSpace H → ℤ → Bool) =
        (Prod.snd : PathSpace H → ℤ → Bool) ∘ shift (H := H) a := rfl
    rw [he, ← Measure.map_map measurable_snd (by
      exact (Measurable.of_eval fun t => (measurable_pi_apply (a+t)).comp measurable_fst).prodMk
        (Measurable.of_eval fun t => (measurable_pi_apply (a+t)).comp measurable_snd)), hs a]
    rfl
  refine ⟨hc,hr.1,rfl,hp,hr.2.1,hs,hv,?_,?_,trim_no11 θ,?_⟩
  · exact visible_masses θ (jointLaw θ : Measure (PathSpace H)) hc
  · exact visible_no11 θ (jointLaw θ : Measure (PathSpace H)) hc
  · intro hu t n w a
    have he : includePath θ ⁻¹' retainedEndpoint θ t n w a =
        endpointEvent (trim θ).matrix t n w a := by
      ext z
      simp only [Set.mem_preimage, retainedEndpoint, endpointEvent, Set.mem_ofPred_eq, includePath]
      constructor
      · rintro ⟨hw,i,hi,ha⟩
        exact ⟨hw, (congrArg (classOf (trim θ).matrix) (Subtype.ext hi)).trans ha⟩
      · rintro ⟨hw,ha⟩
        exact ⟨hw,z.1 (t+n),rfl,ha⟩
    have hm : MeasurableSet (retainedEndpoint θ t n w a) := by
      have hh : MeasurableSet {z : PathSpace H | ∃ i : Positive θ,
          z.1 (t+n) = i.val ∧ classOf (trim θ).matrix i = a} := by
        simp only [Set.ofPred_exists, Set.ofPred_and]
        exact MeasurableSet.iUnion fun i => ((measurableSet_singleton i.val).preimage
          ((measurable_pi_apply (t+n)).comp measurable_fst)).inter
          (if h : classOf (trim θ).matrix i = a then by simp [h] else by simp [h])
      change MeasurableSet ({z : PathSpace H | ∀ k : Fin n,
        z.2 (t + (k.val : ℤ)) = w k} ∩ _)
      have hw : MeasurableSet {z : PathSpace H | ∀ k : Fin n,
          z.2 (t + (k.val : ℤ)) = w k} := by
        simp only [Set.ofPred_forall]
        exact MeasurableSet.iInter fun k => (measurableSet_singleton (w k)).preimage
          ((measurable_pi_apply (t + k.val)).comp measurable_snd)
      exact hw.inter hh
    change (((retainedLaw θ : Measure (PathSpace (Positive θ))).map (includePath θ)) _).toReal = _
    rw [Measure.map_apply (inclusion_measurable θ) hm, he]
    exact actual_endpoint_mass ⟨Positive θ,inferInstance,trim θ⟩ hu
      (retainedLaw θ : Measure (PathSpace (Positive θ))) hr.1 t n w a

#print axioms same_law_trimming
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalLawTrimming
