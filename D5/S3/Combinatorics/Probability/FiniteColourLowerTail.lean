/- GID: D5/S3/Combinatorics/Probability/FiniteColourLowerTail
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Probability/FiniteColourLowerTail
   mirror-E: none(waiver:symbolic-probability-estimate)
   anchors: []
   utility: none
   digest: Actual-mean Chernoff bounds with mutual independence only inside finite colour fibres. -/

import Mathlib.Probability.Moments.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-! # Finite-colour mean-sensitive exponential and lower-tail estimates -/

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators ENNReal
noncomputable section
set_option autoImplicit false

namespace D5.S3.Combinatorics.Probability.FiniteColourLowerTail

private lemma sum_bounds {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    {P : Measure Ω} {X : I → Ω → ℝ}
    (hb : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Set.Icc (0 : ℝ) 1) :
    ∀ᵐ ω ∂P, (∑ i, X i ω) ∈ Set.Icc (0 : ℝ) (Fintype.card I) := by
  filter_upwards [ae_all_iff.2 hb] with ω hω
  constructor
  · exact sum_nonneg fun i _ => (hω i).1
  · simpa using sum_le_sum (s := (univ : Finset I)) (fun i _ => (hω i).2)

private lemma bounded_mgf {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hm : AEMeasurable X P) (hb : ∀ᵐ ω ∂P, X ω ∈ Set.Icc (0 : ℝ) 1)
    (t : ℝ) : mgf X P t ≤ Real.exp ((∫ ω, X ω ∂P) * (Real.exp t - 1)) := by
  have hi : Integrable X P := Integrable.of_mem_Icc 0 1 hm hb
  have he := integrable_exp_mul_of_mem_Icc (t := t) hm hb
  have hc : ∀ᵐ ω ∂P, Real.exp (t * X ω) ≤ 1 + X ω * (Real.exp t - 1) := by
    filter_upwards [hb] with ω hω
    have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ t)
      (sub_nonneg.mpr hω.2) hω.1 (by ring : 1 - X ω + X ω = 1)
    simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at h
    calc
      Real.exp (t * X ω) = Real.exp (X ω * t) := by rw [mul_comm]
      _ ≤ 1 - X ω + X ω * Real.exp t := h
      _ = _ := by ring
  calc
    mgf X P t ≤ ∫ ω, (1 + X ω * (Real.exp t - 1)) ∂P :=
      integral_mono_ae he ((integrable_const 1).add (hi.mul_const _)) hc
    _ = 1 + (∫ ω, X ω ∂P) * (Real.exp t - 1) := by
      rw [integral_add (integrable_const 1) (hi.mul_const _), integral_const,
        integral_mul_const]; simp
    _ ≤ _ := by
      simpa [add_comm] using Real.add_one_le_exp ((∫ ω, X ω ∂P) * (Real.exp t - 1))

/-- Finite-colour MGF aggregation, retaining the actual sum of expectations.
No independence between different colour fibres is assumed. -/
theorem mgf_sum_le {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : I → Ω → ℝ)
    (k : ℕ) (hk : 0 < k) (colour : I → Fin k)
    (hX : ∀ i, AEMeasurable (X i) P)
    (h01 : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Set.Icc (0 : ℝ) 1)
    (hWithin : ∀ j : Fin k,
      iIndepFun (fun i : {i : I // colour i = j} => X i.val) P)
    (t : ℝ) :
    mgf (fun ω => ∑ i, X i ω) P t ≤
      Real.exp (((∑ i, ∫ ω, X i ω ∂P) / (k : ℝ)) *
        (Real.exp ((k : ℝ) * t) - 1)) := by
  classical
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  let Y : Fin k → Ω → ℝ := fun j ω => ∑ i : {i : I // colour i = j}, X i.val ω
  let m : Fin k → ℝ := fun j => ∑ i : {i : I // colour i = j}, ∫ ω, X i.val ω ∂P
  have hy (j : Fin k) : AEMeasurable (Y j) P := by
    dsimp [Y]; exact Finset.aemeasurable_fun_sum _ (fun i _ => hX i.val)
  have sy (ω : Ω) : ∑ j, Y j ω = ∑ i, X i ω := Fintype.sum_fiberwise colour (fun i => X i ω)
  have sm : ∑ j, m j = ∑ i, ∫ ω, X i ω ∂P := Fintype.sum_fiberwise colour (fun i => ∫ ω, X i ω ∂P)
  have hs : AEMeasurable (fun ω => ∑ i, X i ω) P :=
    Finset.aemeasurable_fun_sum _ (fun i _ => hX i)
  have hi := integrable_exp_mul_of_mem_Icc (t := t) hs (sum_bounds h01)
  have hclass (j : Fin k) : mgf (Y j) P ((k : ℝ) * t) ≤
      Real.exp (m j * (Real.exp ((k : ℝ) * t) - 1)) := by
    have hh := (hWithin j).mgf_sum₀ (fun i => hX i.val)
      (univ : Finset {i : I // colour i = j}) (t := (k : ℝ) * t)
    have hfun : Y j = ∑ i ∈ (univ : Finset {i : I // colour i = j}), X i.val := by
      funext ω; simp [Y]
    rw [hfun, hh]
    calc
      _ ≤ ∏ i : {i : I // colour i = j},
          Real.exp ((∫ ω, X i.val ω ∂P) * (Real.exp ((k : ℝ) * t) - 1)) := by
        exact prod_le_prod₀ (fun i _ => mgf_nonneg) (fun i _ => bounded_mgf P
          (hX i.val) (h01 i.val) _)
      _ = _ := by rw [← Real.exp_sum]; congr 1; exact (sum_mul ..).symm
  let F : Fin k → Ω → ℝ≥0∞ := fun j ω => ENNReal.ofReal (Real.exp ((k : ℝ) * t * Y j ω))
  have hf (j : Fin k) : AEMeasurable (F j) P := ((hy j).const_mul _).exp.ennreal_ofReal
  have hroot (a : ℝ) : ENNReal.ofReal (Real.exp ((k : ℝ) * t * a)) ^ (k : ℝ)⁻¹ =
      ENNReal.ofReal (Real.exp (t * a)) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_nonneg _) (inv_nonneg.mpr hkR.le),
      ← Real.exp_mul]
    congr 2
    field_simp
  have hid (ω : Ω) : (∏ j, F j ω ^ (k : ℝ)⁻¹) =
      ENNReal.ofReal (Real.exp (t * ∑ i, X i ω)) := by
    simp_rw [F, hroot]
    rw [← ENNReal.ofReal_prod_of_nonneg (fun j _ => Real.exp_nonneg _), ← Real.exp_sum,
      ← mul_sum, sy]
  have holder := ENNReal.lintegral_prod_norm_pow_le
    (univ : Finset (Fin k)) (fun j _ => hf j)
    (p := fun _ => (k : ℝ)⁻¹) (by simp; field_simp) (fun _ _ => inv_nonneg.mpr hkR.le)
  apply (ENNReal.ofReal_le_ofReal_iff (Real.exp_nonneg _)).mp
  change ENNReal.ofReal (∫ ω, Real.exp (t * ∑ i, X i ω) ∂P) ≤ _
  rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall
    (fun ω => Real.exp_nonneg (t * ∑ i, X i ω)))]
  change (∫⁻ ω, ENNReal.ofReal (Real.exp (t * ∑ i, X i ω)) ∂P) ≤ _
  rw [← show (fun ω => ∏ j, F j ω ^ (k : ℝ)⁻¹) =
      (fun ω => ENNReal.ofReal (Real.exp (t * ∑ i, X i ω))) from funext hid]
  refine holder.trans ?_
  have hbound (j : Fin k) : (∫⁻ ω, F j ω ∂P) ≤
      ENNReal.ofReal (Real.exp (m j * (Real.exp ((k : ℝ) * t) - 1))) := by
    have hij := integrable_exp_mul_of_mem_Icc (t := (k : ℝ) * t) (hy j)
      (sum_bounds (fun i : {i : I // colour i = j} => h01 i.val))
    dsimp [F]
    rw [← ofReal_integral_eq_lintegral_ofReal hij
      (Filter.Eventually.of_forall (fun ω => Real.exp_nonneg _))]
    exact ENNReal.ofReal_le_ofReal (hclass j)
  calc
    _ ≤ ∏ j : Fin k, ENNReal.ofReal
        (Real.exp (m j * (Real.exp ((k : ℝ) * t) - 1))) ^ (k : ℝ)⁻¹ :=
      Finset.prod_le_prod (fun j _ => ENNReal.rpow_le_rpow (hbound j) (inv_nonneg.mpr hkR.le))
    _ = _ := by
      simp_rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_nonneg _) (inv_nonneg.mpr hkR.le),
        ← Real.exp_mul]
      rw [← ENNReal.ofReal_prod_of_nonneg (fun j _ => Real.exp_nonneg _), ← Real.exp_sum]
      congr 2
      rw [← sum_mul, ← sum_mul, sm]
      ring

private lemma exp_neg_quadratic {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-x) ≤ 1 - x + x ^ 2 / 2 := by
  apply image_le_of_deriv_right_le_deriv_boundary
    (f := fun y : ℝ => Real.exp (-y)) (f' := fun y => -Real.exp (-y))
    (B := fun y : ℝ => 1 - y + y ^ 2 / 2) (B' := fun y => -1 + y)
    (a := 0) (b := x) (by fun_prop) ?_ (by norm_num) (by fun_prop) ?_ ?_ ⟨hx, le_rfl⟩
  · intro y hy
    convert ((hasDerivAt_id y).neg.exp).hasDerivWithinAt using 1 <;> (try ext z) <;> simp
  · intro y hy
    convert (((hasDerivAt_const y 1).sub (hasDerivAt_id y)).add
      (((hasDerivAt_id y).pow 2).div_const 2)).hasDerivWithinAt using 1 <;> (try ext z) <;> simp
  · intro y hy
    have h := Real.add_one_le_exp (-y)
    linarith

/-- Mean-sensitive lower tail for an arbitrary probability space and deterministic finite
colouring. Empty index sets, empty fibres and zero means are included. -/
theorem lower_tail {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : I → Ω → ℝ)
    (k : ℕ) (hk : 0 < k) (colour : I → Fin k)
    (hX : ∀ i, AEMeasurable (X i) P)
    (h01 : ∀ i, ∀ᵐ ω ∂P, X i ω ∈ Set.Icc (0 : ℝ) 1)
    (hWithin : ∀ j : Fin k,
      iIndepFun (fun i : {i : I // colour i = j} => X i.val) P)
    (δ : ℝ) (hδ : 0 ≤ δ) :
    P.real {ω | (∑ i, X i ω) ≤ (1 - δ) * (∑ i, ∫ ω, X i ω ∂P)} ≤
      Real.exp (-(δ ^ 2 * (∑ i, ∫ ω, X i ω ∂P)) / (2 * (k : ℝ))) := by
  classical
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  let m : ℝ := ∑ i, ∫ ω, X i ω ∂P
  have hm : 0 ≤ m := sum_nonneg fun i _ => integral_nonneg_of_ae
    ((h01 i).mono fun _ h => h.1)
  have hs : AEMeasurable (fun ω => ∑ i, X i ω) P :=
    Finset.aemeasurable_fun_sum _ (fun i _ => hX i)
  have hi := integrable_exp_mul_of_mem_Icc (t := -δ / (k : ℝ)) hs (sum_bounds h01)
  have ht : -δ / (k : ℝ) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hδ) hkR.le
  have hz : (k : ℝ) * (-δ / (k : ℝ)) = -δ := by field_simp
  calc
    _ ≤ Real.exp (-(-δ / (k : ℝ)) * ((1 - δ) * m)) *
        mgf (fun ω => ∑ i, X i ω) P (-δ / (k : ℝ)) :=
      measure_le_le_exp_mul_mgf _ ht hi
    _ ≤ Real.exp (-(-δ / (k : ℝ)) * ((1 - δ) * m)) *
        Real.exp ((m / (k : ℝ)) * (Real.exp ((k : ℝ) * (-δ / (k : ℝ))) - 1)) :=
      mul_le_mul_of_nonneg_left (mgf_sum_le P X k hk colour hX h01 hWithin _)
        (Real.exp_nonneg _)
    _ ≤ _ := by
      rw [hz, ← Real.exp_add, Real.exp_le_exp]
      calc
        _ ≤ -(-δ / (k : ℝ)) * ((1 - δ) * m) +
            (m / (k : ℝ)) * ((1 - δ + δ ^ 2 / 2) - 1) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left
            (sub_le_sub_right (exp_neg_quadratic hδ) 1) (div_nonneg hm hkR.le))
        _ = _ := by dsimp [m]; ring

end D5.S3.Combinatorics.Probability.FiniteColourLowerTail
