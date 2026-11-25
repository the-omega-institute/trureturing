/- GID: D5/S3/Analytic/Measure/NormalizedHolderEquality
   generality: G
   mirror-B: D5/B/S3/Analytic/Measure/NormalizedHolderEquality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Equality in finite normalized Holder for arbitrary measures and positive weights. -/

module

public import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-! # Equality in finite normalized Holder

The measure is arbitrary. Zero values and infinite values on null sets are allowed.
-/

@[expose] public section

open MeasureTheory Finset Filter
open scoped BigOperators ENNReal

noncomputable section
set_option autoImplicit false

namespace D5.S3.Analytic.Measure.NormalizedHolderEquality

private lemma constant_product {J : Type*} (s : Finset J) (w : J → ℝ)
    (hw : ∀ j ∈ s, 0 ≤ w j) (hs : ∑ j ∈ s, w j = 1)
    {z : ℝ≥0∞} (hz : z ≠ ∞) : (∏ j ∈ s, z ^ w j) = z := by
  have H : ∀ j ∈ s, z ^ w j = ENNReal.ofReal (z.toReal ^ w j) := by
    intro j hj
    rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (hw j hj),
      ENNReal.ofReal_toReal hz]
  rw [prod_congr rfl H]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun j hj => Real.rpow_nonneg ENNReal.toReal_nonneg _),
    ← Real.rpow_sum_of_nonneg ENNReal.toReal_nonneg hw, hs, Real.rpow_one,
    ENNReal.ofReal_toReal hz]

private lemma binary_equality {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f g : X → ℝ≥0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (hfi : ∫⁻ x, f x ∂μ = 1) (hgi : ∫⁻ x, g x ∂μ = 1) :
    (∫⁻ x, f x ^ a * g x ^ b ∂μ) = 1 ↔ f =ᵐ[μ] g := by
  have hconj : (1 / a).HolderConjugate (1 / b) := by
    apply Real.holderConjugate_iff.mpr
    constructor
    · rw [one_div, one_lt_inv₀ ha]
      linarith
    · simpa using hab
  have hfn : ∫⁻ x, (f x ^ a) ^ (1 / a) ∂μ = 1 := by
    simpa [← ENNReal.rpow_mul, ha.ne'] using hfi
  have hgn : ∫⁻ x, (g x ^ b) ^ (1 / b) ∂μ = 1 := by
    simpa [← ENNReal.rpow_mul, hb.ne'] using hgi
  have H := ENNReal.lintegral_mul_eq_one_iff_of_lintegral_rpow_eq_one hconj
    (hf.pow_const a) (hg.pow_const b) hfn hgn
  have hfe : (fun x => f x ^ a) ^ (1 / a) = f := by
    ext x
    simp [Pi.pow_apply, ← ENNReal.rpow_mul, ha.ne']
  have hge : (fun x => g x ^ b) ^ (1 / b) = g := by
    ext x
    simp [Pi.pow_apply, ← ENNReal.rpow_mul, hb.ne']
  rw [hfe, hge] at H
  exact H

private lemma equal_of_saturation {X J : Type*} [MeasurableSpace X] {μ : Measure X}
    (s : Finset J) (q : J → X → ℝ≥0∞) (w : J → ℝ)
    (hq : ∀ j ∈ s, AEMeasurable (q j) μ)
    (hi : ∀ j ∈ s, ∫⁻ x, q j x ∂μ = 1)
    (hw : ∀ j ∈ s, 0 < w j) (hs : ∑ j ∈ s, w j = 1)
    (he : ∫⁻ x, ∏ j ∈ s, q j x ^ w j ∂μ = 1) :
    ∀ j ∈ s, ∀ k ∈ s, q j =ᵐ[μ] q k := by
  classical
  induction s using Finset.induction generalizing w with
  | empty => simp at hs
  | insert i s his ih =>
    by_cases hempty : s = ∅
    · subst s
      simpa using (fun j (hj : j = i) k (hk : k = i) => by subst j; subst k; rfl :
        ∀ j, j = i → ∀ k, k = i → q j =ᵐ[μ] q k)
    have hspos : 0 < ∑ j ∈ s, w j :=
      sum_pos (fun j hj => hw j (mem_insert_of_mem hj)) (nonempty_iff_ne_empty.mpr hempty)
    have hsum : w i + ∑ j ∈ s, w j = 1 := by simpa [sum_insert his] using hs
    have hb : 0 < 1 - w i := by linarith
    let v : J → ℝ := fun j => w j / (1 - w i)
    have hv : ∑ j ∈ s, v j = 1 := by
      dsimp [v]
      rw [← sum_div]
      have : ∑ j ∈ s, w j = 1 - w i := by linarith
      rw [this, div_self hb.ne']
    have hvpos : ∀ j ∈ s, 0 < v j :=
      fun j hj => div_pos (hw j (mem_insert_of_mem hj)) hb
    let g : X → ℝ≥0∞ := fun x => ∏ j ∈ s, q j x ^ v j
    have hgm : AEMeasurable g μ :=
      s.aemeasurable_fun_prod fun j hj => (hq j (mem_insert_of_mem hj)).pow_const _
    have hgle : (∫⁻ x, g x ∂μ) ≤ 1 := by
      have H := ENNReal.lintegral_prod_norm_pow_le s
        (fun j hj => hq j (mem_insert_of_mem hj)) hv (fun j hj => (hvpos j hj).le)
      have Hprod : (∏ j ∈ s, (∫⁻ x, q j x ∂μ) ^ v j) = 1 := by
        apply prod_eq_one
        intro j hj
        rw [hi j (mem_insert_of_mem hj), ENNReal.one_rpow]
      simpa only [Hprod] using H
    have hsplit (x : X) : (∏ j ∈ insert i s, q j x ^ w j) =
        q i x ^ w i * g x ^ (1 - w i) := by
      simp [g, v, his, ← ENNReal.prod_rpow_of_nonneg hb.le, ← ENNReal.rpow_mul,
        div_mul_cancel₀ (h := hb.ne')]
    have hbinary : ∫⁻ x, q i x ^ w i * g x ^ (1 - w i) ∂μ = 1 := by
      simpa only [hsplit] using he
    have hbound : (1 : ℝ≥0∞) ≤ (∫⁻ x, g x ∂μ) ^ (1 - w i) := by
      have H := ENNReal.lintegral_mul_norm_pow_le (hq i (mem_insert_self ..)) hgm
        (hw i (mem_insert_self ..)).le hb.le (add_sub_cancel _ _)
      simpa [hi i (mem_insert_self ..), hbinary] using H
    have hgi : ∫⁻ x, g x ∂μ = 1 := by
      apply le_antisymm hgle
      have H : (1 : ℝ≥0∞) ^ (1 - w i) ≤ (∫⁻ x, g x ∂μ) ^ (1 - w i) := by
        simpa using hbound
      exact (ENNReal.rpow_le_rpow_iff hb).mp H
    have hrest := ih v (fun j hj => hq j (mem_insert_of_mem hj))
      (fun j hj => hi j (mem_insert_of_mem hj)) hvpos hv hgi
    have hig : q i =ᵐ[μ] g :=
      (binary_equality (hq i (mem_insert_self ..)) hgm (hw i (mem_insert_self ..)) hb
        (add_sub_cancel _ _) (hi i (mem_insert_self ..)) hgi).mp hbinary
    have hgi' : ∀ k ∈ s, g =ᵐ[μ] q k := by
      intro k hk
      have H : ∀ᵐ x ∂μ, ∀ j ∈ s, q j x = q k x := by
        exact (eventually_all_finset s).mpr fun j hj => hrest j hj k hk
      filter_upwards [H, ae_lt_top' (hq k (mem_insert_of_mem hk))
        (by rw [hi k (mem_insert_of_mem hk)]; exact ENNReal.one_ne_top)] with x hx hxt
      dsimp [g]
      rw [prod_congr rfl (fun j hj => congrArg (fun z : ℝ≥0∞ => z ^ v j) (hx j hj))]
      exact constant_product s v (fun j hj => (hvpos j hj).le) hv hxt.ne
    have hall : ∀ j ∈ insert i s, q j =ᵐ[μ] g := by
      intro j hj
      rcases mem_insert.mp hj with rfl | hj
      · exact hig
      · exact (hgi' j hj).symm
    intro j hj k hk
    exact (hall j hj).trans (hall k hk).symm

/-- For a finite family of unit-integral densities and strictly positive weights summing
 to one, the weighted product has integral one exactly when all densities agree almost
 everywhere. The measure need not be finite or sigma-finite. -/
theorem lintegral_prod_rpow_eq_one_iff {X J : Type*} [MeasurableSpace X] [Fintype J]
    (μ : Measure X) (q : J → X → ℝ≥0∞) (w : J → ℝ)
    (hq : ∀ j, AEMeasurable (q j) μ) (hi : ∀ j, ∫⁻ x, q j x ∂μ = 1)
    (hw : ∀ j, 0 < w j) (hs : ∑ j, w j = 1) :
    (∫⁻ x, ∏ j, q j x ^ w j ∂μ) = 1 ↔ ∀ j k, q j =ᵐ[μ] q k := by
  classical
  constructor
  · intro he j k
    exact equal_of_saturation univ q w (fun j _ => hq j) (fun j _ => hi j)
      (fun j _ => hw j) hs he j (mem_univ _) k (mem_univ _)
  · intro he
    have hn : Nonempty J := by
      by_contra H
      haveI : IsEmpty J := not_nonempty_iff.mp H
      simp at hs
    obtain ⟨k⟩ := hn
    have H : (fun x => ∏ j, q j x ^ w j) =ᵐ[μ] q k := by
      have H : ∀ᵐ x ∂μ, ∀ j, q j x = q k x := ae_all_iff.mpr fun j => he j k
      filter_upwards [H, ae_lt_top' (hq k)
        (by rw [hi k]; exact ENNReal.one_ne_top)] with x hx hxt
      simp_rw [hx]
      exact constant_product univ w (fun j _ => (hw j).le) hs hxt.ne
    exact (lintegral_congr_ae H).trans (hi k)

end D5.S3.Analytic.Measure.NormalizedHolderEquality
