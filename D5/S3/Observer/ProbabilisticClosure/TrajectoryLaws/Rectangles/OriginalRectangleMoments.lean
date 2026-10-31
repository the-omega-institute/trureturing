/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/OriginalRectangleMoments
   generality: I
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Rectangles/OriginalRectangleMoments
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original chronological rectangle occurrences pay squared contraction moments. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.Rectangles.OriginalRectangleOccurrence
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory ProbabilityTheory Function
open scoped BigOperators ENNReal Classical
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.MarkedPredictiveQuotient
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalMarkedLaw
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalFutureCylinders
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalRectangleOccurrence
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.PositiveRectangleMessages
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.PositiveRectangleLaw

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalRectangleMoments
universe u
variable {H : Type u} [Fintype H] [MeasurableSpace H] [MeasurableSingletonClass H]

/-- The state at the cut and every marked coordinate strictly before it. -/
def markedField (t : ℤ) : MeasurableSpace (PathSpace H) :=
  MeasurableSpace.comap (fun z => (state t z, past t z)) inferInstance

/-- One visible success in the original block beginning at d. -/
def blockSuccess (w : List Bool) (b : ℕ) (d : ℤ) : Set (PathSpace H) :=
  future d ⁻¹' success w b

/-- Successes in q consecutive original b-bit blocks, in chronological order. -/
def chronologicalCount (w : List Bool) (b : ℕ) (d : ℤ) (q : ℕ)
    (z : PathSpace H) : ℕ :=
  ∑ i ∈ Finset.range q, if z ∈ blockSuccess w b (d + (i : ℤ) * b) then 1 else 0

private theorem markedField_le (t : ℤ) :
    markedField (H := H) t ≤ inferInstance :=
  (show Measurable (fun z : PathSpace H => (state t z, past t z)) by
    unfold state past; fun_prop).comap_le

private theorem success_measurable (w : List Bool) (b : ℕ) :
    MeasurableSet (success w b) := by
  change MeasurableSet (OriginalFutureScreening.readPrefix b ⁻¹'
    {v : Fin b → Bool | w <:+: List.ofFn v})
  exact (Set.toFinite _).measurableSet.preimage (by
    unfold OriginalFutureScreening.readPrefix; fun_prop)

private theorem blockSuccess_measurable (w : List Bool) (b : ℕ) (d : ℤ) :
    MeasurableSet (blockSuccess (H := H) w b d) :=
  (success_measurable w b).preimage (by unfold future; fun_prop)

private theorem state_partition (J : Measure (PathSpace H)) (t : ℤ)
    (E : Set (PathSpace H)) : J E = ∑ h, J (E ∩ (state t ⁻¹' {h})) := by
  have hs (h : H) : MeasurableSet (state t ⁻¹' {h}) :=
    (measurableSet_singleton h).preimage (by unfold state; fun_prop)
  have he := sum_measure_preimage_singleton (μ := J.restrict E) Finset.univ
    (f := state t) (fun h _ => hs h)
  simpa only [Finset.coe_univ, Set.preimage_univ, Measure.restrict_apply_univ,
    Measure.restrict_apply (hs _), Set.inter_comm] using he.symm

private theorem occurrence_on_markedField (θ : Presentation H)
    (J : Measure (PathSpace H)) [IsProbabilityMeasure J] (hc : HasOriginalCylinders J θ)
    (w : List Bool) (R : Rectangle (product θ w)) (r : H) (hr : r ∈ R.rows)
    (a : ∀ h, LabelledRoute θ h r) (ha : ∀ h, (a h).length ≤ Fintype.card H)
    (t : ℤ) (A : Set (PathSpace H)) (hA : MeasurableSet[markedField t] A) :
    ENNReal.ofReal (selectedEpsilon θ w r a) * J A ≤
      J (A ∩ blockSuccess w (w.length + Fintype.card H) t) := by
  obtain ⟨B, hB, rfl⟩ := hA
  let E := (fun z : PathSpace H => (state t z, past t z)) ⁻¹' B
  have he (h : H) : E ∩ (state t ⁻¹' {h}) =
      (state t ⁻¹' {h}) ∩ (past t ⁻¹' ((fun p => (h,p)) ⁻¹' B)) := by
    ext z
    simp only [E, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hz,hh⟩
      exact ⟨hh, by simpa only [hh] using hz⟩
    · rintro ⟨hh,hz⟩
      exact ⟨by simpa only [hh] using hz,hh⟩
  change ENNReal.ofReal (selectedEpsilon θ w r a) * J E ≤ _
  rw [state_partition J t E, state_partition J t (E ∩ _), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro h _
  rw [Set.inter_right_comm E, he, he]
  exact (original_rectangle_occurrence θ J hc w R r hr a ha).2.2.2 t h _
    (hB.preimage (measurable_const.prodMk measurable_id))

private theorem condExp_indicator_lower {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (S : Set Ω) (hS : MeasurableSet S) (ε : ℝ) (hε : 0 ≤ ε)
    (hlower : ∀ A, MeasurableSet[m] A → ENNReal.ofReal ε * μ A ≤ μ (A ∩ S)) :
    ∀ᵐ z ∂μ, ε ≤ (μ[S.indicator (fun _ => (1 : ℝ)) | m]) z := by
  let f := S.indicator (fun _ => (1 : ℝ))
  have hf : Integrable f μ := (integrable_const 1).indicator hS
  let g : Ω → ℝ := fun z => (μ[f | m]) z - ε
  have hgm : StronglyMeasurable[m] g := stronglyMeasurable_condExp.sub stronglyMeasurable_const
  have hgi : Integrable g μ := integrable_condExp.sub (integrable_const ε)
  have hnonneg : 0 ≤ᵐ[μ.trim hm] g := by
    apply ae_nonneg_of_forall_setIntegral_nonneg_of_sigmaFinite
      (fun _ _ _ => (hgi.trim hm hgm).integrableOn)
    intro A hA _
    rw [← setIntegral_trim hm hgm hA]
    change 0 ≤ ∫ z in A, (μ[f | m]) z - ε ∂μ
    rw [integral_sub integrable_condExp.integrableOn (integrable_const ε),
      setIntegral_condExp hm hf hA, setIntegral_const, smul_eq_mul]
    have he : (∫ z in A, f z ∂μ) = μ.real (A ∩ S) := by
      simp only [f, setIntegral_indicator hS, setIntegral_const, smul_eq_mul, mul_one]
    rw [he, sub_nonneg]
    have hh := ENNReal.toReal_mono (measure_ne_top μ (A ∩ S)) (hlower A hA)
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hε, measureReal_def,
      mul_comm] using hh
  have hh := ae_le_of_ae_le_trim hnonneg
  exact hh.mono fun z hz => sub_nonneg.mp hz

/-- Complete marked-past occurrence gives the conditional probability lower bound
on the same original measure, also in the presence of null hidden fibers. -/
theorem marked_success_condExp (θ : Presentation H)
    (J : Measure (PathSpace H)) [IsProbabilityMeasure J] (hc : HasOriginalCylinders J θ)
    (w : List Bool) (R : Rectangle (product θ w)) (r : H) (hr : r ∈ R.rows)
    (a : ∀ h, LabelledRoute θ h r) (ha : ∀ h, (a h).length ≤ Fintype.card H) (t : ℤ) :
    ∀ᵐ z ∂J, selectedEpsilon θ w r a ≤
      (J[(blockSuccess w (w.length + Fintype.card H) t).indicator
        (fun _ => (1 : ℝ)) | markedField t]) z := by
  exact condExp_indicator_lower J (markedField t) (markedField_le t) _
    (blockSuccess_measurable w _ t)
    (selectedEpsilon θ w r a) (original_rectangle_occurrence θ J hc w R r hr a ha).1.le
    (occurrence_on_markedField θ J hc w R r hr a ha t)

private theorem conditional_payment {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (S : Set Ω) (hS : MeasurableSet S) (ε ρ : ℝ) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hlower : ∀ᵐ z ∂μ, ε ≤ (μ[S.indicator (fun _ => (1 : ℝ)) | m]) z) :
    ∀ᵐ z ∂μ, (μ[fun z => if z ∈ S then ρ^2 else 1 | m]) z ≤
      1 - ε * (1-ρ^2) := by
  let I := S.indicator (fun _ => (1 : ℝ))
  have hi : Integrable I μ := (integrable_const 1).indicator hS
  have he : (fun z => if z ∈ S then ρ^2 else 1) =
      (fun _ => (1 : ℝ)) - (1-ρ^2) • I := by
    ext z
    by_cases hz : z ∈ S <;> simp [I, hz] <;> ring
  rw [he]
  filter_upwards [condExp_sub (integrable_const 1) (hi.smul (1-ρ^2)) m,
    condExp_smul (μ := μ) (1-ρ^2) I m, hlower] with z hsub hmul hlo
  rw [hsub, hmul, condExp_const hm]
  have hsq : ρ^2 ≤ 1 := by
    simpa only [pow_two, mul_one] using
      (mul_le_mul hρ1 hρ1 hρ (by norm_num : (0 : ℝ) ≤ 1))
  have hfac : 0 ≤ 1-ρ^2 := sub_nonneg.mpr hsq
  change 1 - (1-ρ^2) * (μ[I | m]) z ≤ _
  nlinarith [mul_le_mul_of_nonneg_left hlo hfac]

private theorem earlier_block_measurable (w : List Bool) (b : ℕ) (d t : ℤ)
    (hdt : d + b ≤ t) : MeasurableSet[markedField (H := H) t] (blockSuccess w b d) := by
  let read : (H × (ℕ → H × Bool)) → (Fin b → Bool) :=
    fun p k => (p.2 ((t-d-1-k.val).toNat)).2
  have hm : Measurable read := by dsimp [read]; fun_prop
  have he : blockSuccess (H := H) w b d =
      (fun z => (state t z,past t z)) ⁻¹'
        (read ⁻¹' {v : Fin b → Bool | w <:+: List.ofFn v}) := by
    ext z
    change (w <:+: List.ofFn (OriginalFutureScreening.readPrefix b (future d z))) ↔ _
    have hread : read (state t z,past t z) =
        OriginalFutureScreening.readPrefix b (future d z) := by
      funext k
      dsimp [read,past,future,OriginalFutureScreening.readPrefix]
      congr 1
      have hk := k.isLt
      rw [Int.toNat_of_nonneg (by omega)]
      omega
    simp only [Set.mem_preimage, Set.mem_setOf_eq, hread]
  rw [he]
  exact ⟨_, (Set.toFinite _).measurableSet.preimage hm, rfl⟩

private def payment (w : List Bool) (b : ℕ) (d : ℤ) (ρ : ℝ) (q : ℕ)
    (z : PathSpace H) : ℝ :=
  ∏ i ∈ Finset.range q, if z ∈ blockSuccess w b (d+(i : ℤ)*b) then ρ^2 else 1

private theorem payment_bounds (w : List Bool) (b : ℕ) (d : ℤ) (ρ : ℝ)
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (q : ℕ) (z : PathSpace H) :
    0 ≤ payment w b d ρ q z ∧ payment w b d ρ q z ≤ 1 := by
  have hsq : ρ^2 ≤ 1 := by
    simpa only [pow_two, mul_one] using
      (mul_le_mul hρ1 hρ1 hρ (by norm_num : (0 : ℝ) ≤ 1))
  constructor
  · exact Finset.prod_nonneg fun i _ => by split_ifs <;> positivity
  · apply Finset.prod_le_one₀
    · intro i _
      split_ifs <;> positivity
    · intro i _
      split_ifs <;> nlinarith

private theorem payment_measurable (w : List Bool) (b : ℕ) (d : ℤ) (ρ : ℝ) (q : ℕ) :
    StronglyMeasurable (payment (H := H) w b d ρ q) := by
  unfold payment
  apply Finset.stronglyMeasurable_fun_prod
  intro i _
  exact StronglyMeasurable.ite (blockSuccess_measurable w b _)
    stronglyMeasurable_const stronglyMeasurable_const

private theorem payment_integrable (J : Measure (PathSpace H)) [IsProbabilityMeasure J]
    (w : List Bool) (b : ℕ) (d : ℤ) (ρ : ℝ) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (q : ℕ) :
    Integrable (payment w b d ρ q) J := by
  apply (integrable_const (μ := J) (1 : ℝ)).mono' (payment_measurable w b d ρ q).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (payment_bounds w b d ρ hρ hρ1 q z).1]
    exact (payment_bounds w b d ρ hρ hρ1 q z).2

private theorem payment_power (w : List Bool) (b : ℕ) (d : ℤ) (ρ : ℝ) (q : ℕ)
    (z : PathSpace H) : payment w b d ρ q z = ρ^(2 * chronologicalCount w b d q z) := by
  induction q with
  | zero => simp [payment,chronologicalCount]
  | succ q ih =>
    have hp : payment w b d ρ (q+1) z = payment w b d ρ q z *
        (if z ∈ blockSuccess w b (d+(q : ℤ)*b) then ρ^2 else 1) := by
      simp only [payment, Finset.prod_range_succ]
    rw [hp,ih]
    simp only [chronologicalCount, Finset.sum_range_succ]
    split_ifs <;> simp [Nat.mul_add,pow_add]

/-- The original occurrence estimate pays the squared count in chronological time.
The start d is arbitrary, so this applies to both left blocks and right blocks.
No independence or future-conditioned lower bound is assumed. -/
theorem chronological_success_moment (θ : Presentation H)
    (J : Measure (PathSpace H)) [IsProbabilityMeasure J] (hc : HasOriginalCylinders J θ)
    (w : List Bool) (R : Rectangle (product θ w)) (r : H) (hr : r ∈ R.rows)
    (a : ∀ h, LabelledRoute θ h r) (ha : ∀ h, (a h).length ≤ Fintype.card H)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (d : ℤ) (q : ℕ) :
    let b := w.length + Fintype.card H
    let η := 1 - selectedEpsilon θ w r a * (1-ρ^2)
    (∫ z, ρ^(2 * chronologicalCount w b d q z) ∂J) ≤ η^q := by
  let b := w.length + Fintype.card H
  let ε := selectedEpsilon θ w r a
  let η := 1-ε*(1-ρ^2)
  have hε := original_rectangle_occurrence θ J hc w R r hr a ha
  have hη : 0 ≤ η := by
    dsimp [η,ε]
    nlinarith [mul_nonneg hε.1.le (sq_nonneg ρ), hε.2.1]
  suffices hp : (∫ z, payment w b d ρ q z ∂J) ≤ η^q by
    simpa only [payment_power] using hp
  induction q with
  | zero => simp [payment]
  | succ q ih =>
    let t := d+(q : ℤ)*b
    let S := blockSuccess (H := H) w b t
    let V : PathSpace H → ℝ := fun z => if z ∈ S then ρ^2 else 1
    let U := payment (H := H) w b d ρ q
    have hU : Integrable U J := payment_integrable J w b d ρ hρ hρ1 q
    have hV : Integrable V J := by
      have he : V = (fun _ => (1 : ℝ)) -
          (1-ρ^2) • S.indicator (fun _ => (1 : ℝ)) := by
        ext z; by_cases hz : z ∈ S <;> simp [V,hz] <;> ring
      rw [he]
      exact (integrable_const 1).sub
        (((integrable_const 1).indicator (blockSuccess_measurable w b t)).smul _)
    have hUm : StronglyMeasurable[markedField t] U := by
      dsimp [U,payment]
      apply Finset.stronglyMeasurable_fun_prod
      intro i hi
      apply StronglyMeasurable.ite _ stronglyMeasurable_const stronglyMeasurable_const
      apply earlier_block_measurable w b _ t
      have hi' := Finset.mem_range.mp hi
      dsimp [t]
      have hb : 0 ≤ (b : ℤ) := Nat.cast_nonneg b
      have hm := mul_le_mul_of_nonneg_right (show (i : ℤ)+1 ≤ q by omega) hb
      nlinarith
    have hUV : Integrable (U * V) J :=
      hV.bdd_mul (hUm.mono (markedField_le t)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun z => by
          rw [Real.norm_eq_abs, abs_of_nonneg (payment_bounds w b d ρ hρ hρ1 q z).1]
          exact (payment_bounds w b d ρ hρ hρ1 q z).2)
    have hpay : ∀ᵐ z ∂J, (J[V | markedField t]) z ≤ η :=
      conditional_payment J (markedField t) (markedField_le t) S
        (blockSuccess_measurable w b t) ε ρ hρ hρ1
        (marked_success_condExp θ J hc w R r hr a ha t)
    have hUce : Integrable (fun z => U z * (J[V | markedField t]) z) J :=
      (integrable_condExp (μ := J) (m := markedField t) (f := U * V)).congr
        (condExp_mul_of_stronglyMeasurable_left hUm hUV hV)
    have he : (∫ z, payment w b d ρ (q+1) z ∂J) =
        ∫ z, U z * (J[V | markedField t]) z ∂J := by
      calc
        _ = ∫ z, U z * V z ∂J := by
          congr 1; funext z; simp only [payment, Finset.prod_range_succ]; rfl
        _ = ∫ z, (J[U * V | markedField t]) z ∂J :=
          (integral_condExp (markedField_le t)).symm
        _ = _ := integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hUm hUV hV)
    rw [he]
    calc
      _ ≤ ∫ z, U z * η ∂J := integral_mono_ae hUce (hU.mul_const η)
        (hpay.mono fun z hz => mul_le_mul_of_nonneg_left hz
          (payment_bounds w b d ρ hρ hρ1 q z).1)
      _ = (∫ z, U z ∂J) * η := integral_mul_const η U
      _ ≤ η^q * η := mul_le_mul_of_nonneg_right ih hη
      _ = η^(q+1) := (pow_succ η q).symm

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.OriginalRectangleMoments
