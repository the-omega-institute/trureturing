/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ErasedExteriorFiltration
   generality: I
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ErasedExteriorFiltration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite erased-center windows generate the full exterior and preserve posterior guards. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalErasureComparison
import Mathlib.Probability.Martingale.Convergence

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory Function Set Filter
open scoped BigOperators Classical Topology
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalErasureComparison

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ErasedExteriorFiltration

/-- Equal-length observed blocks on both sides of the erased coordinate zero. -/
def window (r : ℕ) (z : ℤ → Bool) : (Fin r → Bool) × (Fin r → Bool) :=
  (leftWord r z,rightWord r z)

/-- The actual finite exterior information, with the center absent. -/
def field (r : ℕ) : MeasurableSpace (ℤ → Bool) := MeasurableSpace.comap (window r) inferInstance

private theorem field_succ (r : ℕ) : field r ≤ field (r+1) := by
  let g : ((Fin (r+1) → Bool) × (Fin (r+1) → Bool)) →
      ((Fin r → Bool) × (Fin r → Bool)) := fun w =>
        (fun k => w.1 k.succ,fun k => w.2 k.castSucc)
  have hg : Measurable g := by dsimp [g]; fun_prop
  have he : window r = g ∘ window (r+1) := by
    funext z
    apply Prod.ext <;> funext k
    · dsimp [window,leftWord,g]
      apply congrArg z
      push_cast
      omega
    · rfl
  exact MeasurableSpace.comap_le_comap_of_eq_comp _ hg he

/-- One increasing raw filtration on the common visible path space. -/
def information : Filtration ℕ (inferInstance : MeasurableSpace (ℤ → Bool)) where
  seq := field
  mono' := monotone_nat_of_le_succ field_succ
  le' r := (show Measurable (window r) by unfold window leftWord rightWord; fun_prop).comap_le

/-- The increasing finite exterior windows generate exactly the full retained exterior field. -/
theorem full_field : (⨆ r : ℕ, field r) = MeasurableSpace.comap exterior inferInstance := by
  apply le_antisymm
  · apply iSup_le
    intro r
    let g : ((ℕ → Bool) × (ℕ → Bool)) → ((Fin r → Bool) × (Fin r → Bool)) :=
      fun v => (fun k => v.1 (r-1-k.val),fun k => v.2 k.val)
    have hg : Measurable g := by dsimp [g]; fun_prop
    have he : window r = g ∘ exterior := by
      funext z
      apply Prod.ext <;> funext k
      · dsimp [window,leftWord,g,exterior,before]
        apply congrArg z
        have hk := k.isLt
        omega
      · dsimp [window,rightWord,g,exterior,after]
    exact MeasurableSpace.comap_le_comap_of_eq_comp _ hg he
  · have hL (n : ℕ) : @Measurable (ℤ → Bool) Bool (⨆ r, field r) inferInstance
        (fun z => before z n) := by
      have hm : Measurable[field (n+1)] (fun z => (window (n+1) z).1 0) :=
        ((measurable_pi_apply 0).comp measurable_fst).comp (Measurable.of_comap_le le_rfl)
      have hm' := hm.mono (le_iSup field (n+1)) le_rfl
      convert hm' using 1
      funext z
      dsimp [window,leftWord,before]
      congr 1
    have hR (n : ℕ) : @Measurable (ℤ → Bool) Bool (⨆ r, field r) inferInstance
        (fun z => after z n) := by
      have hm : Measurable[field (n+1)] (fun z => (window (n+1) z).2 (Fin.last n)) :=
        ((measurable_pi_apply (Fin.last n)).comp measurable_snd).comp (Measurable.of_comap_le le_rfl)
      exact hm.mono (le_iSup field (n+1)) le_rfl
    letI : MeasurableSpace (ℤ → Bool) := ⨆ r, field r
    have hmL : Measurable before := Measurable.of_eval hL
    have hmR : Measurable after := Measurable.of_eval hR
    exact (hmL.prodMk hmR).comap_le

/-- A positive event cannot retain a uniform strict posterior interval at all sufficiently
large finite fields when the same-law full exterior posterior is a binary target. This uses
actual almost-sure martingale convergence, with no pathwise change of radius or law. -/
private theorem no_binary_limit_with_guard {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ mΩ) (Y : Ω → ℝ) (hY : Integrable Y μ)
    (hYm : StronglyMeasurable[⨆ r, ℱ r] Y)
    (hbinary : ∀ᵐ z ∂μ, Y z = 0 ∨ Y z = 1)
    (G : Set Ω) (hG : 0 < μ G) (ε : ℝ) (hε : 0 < ε) (r₀ : ℕ)
    (hguard : ∀ r, r₀ ≤ r → ∀ᵐ z ∂μ, z ∈ G →
      ε ≤ (μ[Y | ℱ r]) z ∧ (μ[Y | ℱ r]) z ≤ 1-ε) : False := by
  have hc := hY.tendsto_ae_condExp (ℱ := ℱ) hYm
  have hg : ∀ᵐ z ∂μ, ∀ r, r₀ ≤ r → z ∈ G →
      ε ≤ (μ[Y | ℱ r]) z ∧ (μ[Y | ℱ r]) z ≤ 1-ε :=
    ae_all_iff.mpr fun r => by
      by_cases hr : r₀ ≤ r
      · exact (hguard r hr).mono fun z hz _ => hz
      · exact Eventually.of_forall fun _ h => (hr h).elim
  have hnot : ∀ᵐ z ∂μ, z ∉ G := by
    filter_upwards [hc,hg,hbinary] with z hc hg hb hz
    have hlow : ε ≤ Y z := ge_of_tendsto hc (eventually_atTop.mpr ⟨r₀,fun r hr => (hg r hr hz).1⟩)
    have hupp : Y z ≤ 1-ε := le_of_tendsto hc (eventually_atTop.mpr ⟨r₀,fun r hr => (hg r hr hz).2⟩)
    rcases hb with hb | hb <;> rw [hb] at hlow hupp <;> linarith
  have hz : μ G = 0 := by
    rw [ae_iff] at hnot
    convert hnot using 2
    ext z
    simp
  exact hG.ne' hz


/-- The native finite exterior posterior on the actual visible law of theta. -/
def finiteMean {H : Type*} [Fintype H] [MeasurableSpace H] [MeasurableSingletonClass H]
    (θ : D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkedPredictiveQuotient.Presentation H)
    (r : ℕ) : (ℤ → Bool) → ℝ :=
  bitPredictor (D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalLawTrimming.visibleLaw θ :
    Measure (ℤ → Bool)) (fun z => z 0) (window r) ∘ window r

/-- The closed strict interval of a uniform finite exterior guard cannot survive on any
positive event when the actual full erased-bit posterior equals X0. All finite and complete
conditional distributions here use the same actual visible law. -/
theorem no_uniform_exterior_guard {H : Type*} [Fintype H] [MeasurableSpace H]
    [MeasurableSingletonClass H]
    (θ : D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkedPredictiveQuotient.Presentation H)
    (hfull : fullMean θ =ᵐ[
      (D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalLawTrimming.visibleLaw θ : Measure (ℤ → Bool))]
      erasedBit)
    (G : Set (ℤ → Bool))
    (hG : 0 < (D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalLawTrimming.visibleLaw θ :
      Measure (ℤ → Bool)) G)
    (ε : ℝ) (hε : 0 < ε) (r₀ : ℕ) :
    ¬(∀ r, r₀ ≤ r → ∀ᵐ z ∂
      (D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalLawTrimming.visibleLaw θ : Measure (ℤ → Bool)),
      z ∈ G → ε ≤ finiteMean θ r z ∧ finiteMean θ r z ≤ 1-ε) := by
  let μ := (D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalLawTrimming.visibleLaw θ :
    Measure (ℤ → Bool))
  have hbit : Integrable erasedBit μ := by
    have he : erasedBit = {z : ℤ → Bool | z 0 = true}.indicator (fun _ => (1:ℝ)) := by
      funext z
      cases hx : z 0 <;> simp [erasedBit,hx]
    rw [he]
    exact (integrable_const 1).indicator ((measurableSet_singleton true).preimage (measurable_pi_apply 0))
  have hY : Integrable (fullMean θ) μ := hbit.congr hfull.symm
  have hYm : StronglyMeasurable[⨆ r : ℕ, information r] (fullMean θ) := by
    change StronglyMeasurable[⨆ r : ℕ, field r] (fullMean θ)
    rw [full_field]
    exact (ProbabilityTheory.measurable_condDistrib (measurableSet_singleton true)).ennreal_toReal.stronglyMeasurable
  have hbinary : ∀ᵐ z ∂μ, fullMean θ z = 0 ∨ fullMean θ z = 1 := hfull.mono fun z hz => by
    rw [hz]
    cases hx : z 0 <;> simp [erasedBit,hx]
  have hpost (r : ℕ) : finiteMean θ r =ᵐ[μ] μ[fullMean θ | field r] := by
    have hp := ProbabilityTheory.condDistrib_ae_eq_condExp
      (μ := μ) (show Measurable (window r) by unfold window leftWord rightWord; fun_prop)
      (measurable_pi_apply 0 : Measurable (fun z : ℤ → Bool => z 0)) (measurableSet_singleton true)
    have he : ((fun z : ℤ → Bool => z 0) ⁻¹' {true}).indicator (fun _ => (1:ℝ)) = erasedBit := by
      funext z
      cases hx : z 0 <;> simp [erasedBit,hx]
    rw [he] at hp
    exact hp.trans (condExp_congr_ae hfull.symm)
  intro hg
  apply no_binary_limit_with_guard μ information (fullMean θ) hY hYm hbinary G hG ε hε r₀
  intro r hr
  filter_upwards [hg r hr,hpost r] with z hz hp
  change z ∈ G → ε ≤ μ[fullMean θ | field r] z ∧ μ[fullMean θ | field r] z ≤ 1-ε
  simpa only [hp] using hz

#print axioms no_uniform_exterior_guard

#print axioms full_field
#print axioms no_binary_limit_with_guard
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ErasedExteriorFiltration
