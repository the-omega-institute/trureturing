/- GID: D5/S3/Arith/Lattices/Klartag/Tail/PaddedTail
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Tail/PaddedTail
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Lattice tail bounds along the matrix walk. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import Mathlib

namespace D5.S3.Arith.Lattices.Klartag

open MeasureTheory
open Filter
open Set
open Real
open ProbabilityTheory
open scoped ENNReal Topology NNReal

/-- `Φ(r) = min(1/2, e^{−r²/2}/(√(2π)·r))`, Klartag eq. (48). -/
noncomputable def Phi (r : ℝ) : ℝ := min (1 / 2) (Real.exp (-r ^ 2 / 2) / (Real.sqrt (2 * π) * r))

theorem Phi_le_half (r : ℝ) : Phi r ≤ 1 / 2 := min_le_left _ _

theorem Phi_nonneg {r : ℝ} (hr : 0 < r) : 0 ≤ Phi r := by
  refine le_min (by norm_num) (div_nonneg (Real.exp_nonneg _) ?_)
  exact mul_nonneg (Real.sqrt_nonneg _) hr.le

/-- `x ↦ x·e^{−x²/2}` integrates to `e^{−a²/2}` over `(a, ∞)`. -/
theorem integral_Ioi_mul_exp_neg_sq (a : ℝ) :
    ∫ x in Ioi a, x * Real.exp (-x ^ 2 / 2) = Real.exp (-a ^ 2 / 2) := by
  have hderiv : ∀ x : ℝ, HasDerivAt (fun y : ℝ => -Real.exp (-y ^ 2 / 2))
      (x * Real.exp (-x ^ 2 / 2)) x := by
    intro x
    have h1' : HasDerivAt (fun y : ℝ => -y ^ 2 / 2) (-(2 * x) / 2) x := by
      simpa using ((hasDerivAt_pow 2 x).neg).div_const 2
    have hval : -(2 * x) / 2 = -x := by ring
    rw [hval] at h1'
    have h2 : HasDerivAt (fun y : ℝ => Real.exp (-y ^ 2 / 2))
        (Real.exp (-x ^ 2 / 2) * (-x)) x := h1'.exp
    have h3 := h2.neg
    have heq : -(Real.exp (-x ^ 2 / 2) * (-x)) = x * Real.exp (-x ^ 2 / 2) := by ring
    rwa [heq] at h3
  have hint : IntegrableOn (fun x : ℝ => x * Real.exp (-x ^ 2 / 2)) (Ioi a) := by
    have h := integrable_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num)
    have hfun : (fun x : ℝ => x * Real.exp (-(1 / 2) * x ^ 2))
        = fun x : ℝ => x * Real.exp (-x ^ 2 / 2) := by
      funext x; congr 1; congr 1; ring
    rw [hfun] at h
    exact h.integrableOn
  have htend : Tendsto (fun x : ℝ => -Real.exp (-x ^ 2 / 2)) atTop (𝓝 0) := by
    have h : Tendsto (fun x : ℝ => x ^ 2 / 2) atTop atTop :=
      Filter.Tendsto.atTop_div_const (by norm_num) (tendsto_pow_atTop (by norm_num))
    have h2 := Real.tendsto_exp_neg_atTop_nhds_zero.comp h
    simpa [Function.comp_def, neg_div] using h2.neg
  have := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
    (f := fun y : ℝ => -Real.exp (-y ^ 2 / 2)) (a := a)
    (Continuous.continuousWithinAt (by fun_prop))
    (fun x _ => hderiv x) hint htend
  simpa using this

/-- `e^{−x²/2}` is integrable on any `(r, ∞)`. -/
theorem integrableOn_exp_neg_sq (r : ℝ) :
    IntegrableOn (fun x : ℝ => Real.exp (-x ^ 2 / 2)) (Ioi r) := by
  have h := integrable_exp_neg_mul_sq (b := 1 / 2) (by norm_num)
  have hfun : (fun x : ℝ => Real.exp (-(1 / 2) * x ^ 2))
      = fun x : ℝ => Real.exp (-x ^ 2 / 2) := by
    funext x; congr 1; ring
  rw [hfun] at h
  exact h.integrableOn

/-- **The Gaussian tail with its `1/r`** (Klartag eq. (49)):
`∫_r^∞ e^{−x²/2} dx ≤ (1/r)·e^{−r²/2}` for `r > 0`.

Proof (the paper's): on `(r, ∞)` we have `1 ≤ x/r`, so `e^{−x²/2} ≤ (x/r)·e^{−x²/2}`, and the
right-hand side integrates exactly.  **This is the step a Chernoff bound cannot reproduce**, and
losing it costs the `n²` (kill rule 2). -/
theorem gaussian_tail_le {r : ℝ} (hr : 0 < r) :
    ∫ x in Ioi r, Real.exp (-x ^ 2 / 2) ≤ Real.exp (-r ^ 2 / 2) / r := by
  have hxint : IntegrableOn (fun x : ℝ => x * Real.exp (-x ^ 2 / 2)) (Ioi r) := by
    have h := integrable_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num)
    have hfun : (fun x : ℝ => x * Real.exp (-(1 / 2) * x ^ 2))
        = fun x : ℝ => x * Real.exp (-x ^ 2 / 2) := by
      funext x; congr 1; congr 1; ring
    rw [hfun] at h
    exact h.integrableOn
  have heint := integrableOn_exp_neg_sq r
  have hcint : IntegrableOn (fun x : ℝ => r⁻¹ * (x * Real.exp (-x ^ 2 / 2))) (Ioi r) :=
    hxint.const_mul _
  have hmono : ∫ x in Ioi r, Real.exp (-x ^ 2 / 2)
      ≤ ∫ x in Ioi r, r⁻¹ * (x * Real.exp (-x ^ 2 / 2)) := by
    refine setIntegral_mono_on heint hcint measurableSet_Ioi (fun x hx => ?_)
    have hx' : r < x := hx
    have hpos : (0 : ℝ) < Real.exp (-x ^ 2 / 2) := Real.exp_pos _
    have h1 : (1 : ℝ) ≤ r⁻¹ * x := by rw [le_inv_mul_iff₀ hr]; linarith
    nlinarith [hpos, h1]
  calc ∫ x in Ioi r, Real.exp (-x ^ 2 / 2)
      ≤ ∫ x in Ioi r, r⁻¹ * (x * Real.exp (-x ^ 2 / 2)) := hmono
    _ = r⁻¹ * ∫ x in Ioi r, x * Real.exp (-x ^ 2 / 2) := by
        rw [MeasureTheory.integral_const_mul]
    _ = Real.exp (-r ^ 2 / 2) / r := by
        rw [integral_Ioi_mul_exp_neg_sq]; field_simp

/-- `P(Z ≥ r) ≤ e^{−r²/2}/(√(2π)·r)` for a standard Gaussian `Z` and `r > 0`. -/
theorem gaussianReal_Ici_le_tail {r : ℝ} (hr : 0 < r) :
    (gaussianReal 0 1) (Ici r)
      ≤ ENNReal.ofReal (Real.exp (-r ^ 2 / 2) / (Real.sqrt (2 * π) * r)) := by
  have hpdf : ∀ x : ℝ, gaussianPDFReal 0 1 x = (Real.sqrt (2 * π))⁻¹ * Real.exp (-x ^ 2 / 2) := by
    intro x; rw [gaussianPDFReal]; norm_num
  have heint := integrableOn_exp_neg_sq r
  rw [gaussianReal_apply_eq_integral 0 (by norm_num) (Ici r)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
  have hrw : ∫ x in Ioi r, gaussianPDFReal 0 1 x
      = (Real.sqrt (2 * π))⁻¹ * ∫ x in Ioi r, Real.exp (-x ^ 2 / 2) := by
    rw [← MeasureTheory.integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi (fun x _ => hpdf x)
  rw [hrw]
  have hs : (0 : ℝ) < Real.sqrt (2 * π) := Real.sqrt_pos.2 (by positivity)
  calc (Real.sqrt (2 * π))⁻¹ * ∫ x in Ioi r, Real.exp (-x ^ 2 / 2)
      ≤ (Real.sqrt (2 * π))⁻¹ * (Real.exp (-r ^ 2 / 2) / r) :=
        mul_le_mul_of_nonneg_left (gaussian_tail_le hr) (by positivity)
    _ = Real.exp (-r ^ 2 / 2) / (Real.sqrt (2 * π) * r) := by field_simp

/-- `P(Z ≥ 0) = 1/2` for a standard Gaussian, by symmetry. -/
theorem gaussianReal_Ici_zero : (gaussianReal 0 1) (Ici (0 : ℝ)) = ENNReal.ofReal (1 / 2) := by
  have hsing : (gaussianReal 0 1) {(0 : ℝ)} = 0 := by
    have := nullSingletonClass_gaussianReal (μ := (0 : ℝ)) (v := 1) (by norm_num)
    exact this.measure_singleton 0
  have hmapneg : (gaussianReal 0 1).map (fun x : ℝ => -x) = gaussianReal 0 1 := by
    simpa using gaussianReal_map_neg (μ := (0 : ℝ)) (v := 1)
  have hIic : (gaussianReal 0 1) (Iic (0 : ℝ)) = (gaussianReal 0 1) (Ici (0 : ℝ)) := by
    conv_lhs => rw [← hmapneg]
    rw [Measure.map_apply measurable_neg measurableSet_Iic]
    congr 1
    ext x
    simp
  have hIoi : (gaussianReal 0 1) (Ici (0 : ℝ)) = (gaussianReal 0 1) (Ioi (0 : ℝ)) := by
    have hunion : Ici (0 : ℝ) = Ioi (0 : ℝ) ∪ {(0 : ℝ)} := by
      ext x; simp [le_iff_lt_or_eq, eq_comm]
    rw [hunion]
    refine le_antisymm ?_ (measure_mono (by intro x hx; exact Or.inl hx))
    calc (gaussianReal 0 1) (Ioi (0:ℝ) ∪ {(0:ℝ)})
        ≤ (gaussianReal 0 1) (Ioi (0:ℝ)) + (gaussianReal 0 1) {(0:ℝ)} := measure_union_le _ _
      _ = (gaussianReal 0 1) (Ioi (0:ℝ)) := by rw [hsing, add_zero]
  have hcompl : (gaussianReal 0 1) (Iic (0 : ℝ)) + (gaussianReal 0 1) (Ioi (0 : ℝ)) = 1 := by
    have h := measure_add_measure_compl (μ := gaussianReal 0 1) (s := Iic (0 : ℝ))
      measurableSet_Iic
    rwa [compl_Iic, measure_univ] at h
  rw [hIic, hIoi] at hcompl
  have htwo : (2 : ℝ≥0∞) * (gaussianReal 0 1) (Ici (0 : ℝ)) = 1 := by
    rw [two_mul, hIoi]; exact hcompl
  have h2 : (gaussianReal 0 1) (Ici (0 : ℝ)) = 1 / 2 := by
    rw [ENNReal.eq_div_iff (by norm_num) (by norm_num)]; exact htwo
  rw [h2, show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
    ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)]
  norm_num

/-- `P(Z ≥ r) ≤ Φ(r)` for a standard Gaussian and `r > 0` — Klartag eq. (49). -/
theorem gaussianReal_Ici_le_Phi {r : ℝ} (hr : 0 < r) :
    (gaussianReal 0 1) (Ici r) ≤ ENNReal.ofReal (Phi r) := by
  rw [Phi]
  rcases le_total (1 / 2 : ℝ) (Real.exp (-r ^ 2 / 2) / (Real.sqrt (2 * π) * r)) with h | h
  · rw [min_eq_left h, ← gaussianReal_Ici_zero]
    exact measure_mono (Ici_subset_Ici.2 hr.le)
  · rw [min_eq_right h]
    exact gaussianReal_Ici_le_tail hr

/-- The same bound for a centred Gaussian of variance `σ²`: `P(Z ≥ a) ≤ Φ(a/σ)`. -/
theorem gaussianReal_Ici_le_Phi_var {σ a : ℝ} {v : ℝ≥0} (hσ : 0 < σ) (ha : 0 < a)
    (hv : (v : ℝ) = σ ^ 2) :
    (gaussianReal 0 v) (Ici a) ≤ ENNReal.ofReal (Phi (a / σ)) := by
  have hmap : (gaussianReal 0 1).map (fun x : ℝ => σ * x) = gaussianReal 0 v := by
    have h := gaussianReal_map_const_mul (μ := (0 : ℝ)) (v := 1) σ
    rw [mul_zero, mul_one] at h
    refine h.trans ?_
    congr 1
    apply NNReal.coe_injective
    simp [hv]
  rw [← hmap, Measure.map_apply (by fun_prop) measurableSet_Ici]
  have hset : (fun x : ℝ => σ * x) ⁻¹' Ici a = Ici (a / σ) := by
    ext x
    simp only [mem_preimage, mem_Ici]
    rw [mul_comm σ x, ← div_le_iff₀ hσ]
  rw [hset]
  exact gaussianReal_Ici_le_Phi (by positivity)

/-- **The padded-increment tail (Prop 4.1, discrete form).**

`hit` is the event `{∃ k ≤ N, M_k ≤ 0}` (the lattice point `x` becomes a contact point by time
`T`); `lev` is the event `{min_{k ≤ N} S̃_k ≤ −M₀}` for the *padded* walk `S̃`, whose increments
are i.i.d. `N(0, δ)` with `δ = h·|x|⁴`; `S` is the terminal value `S̃_N`, whose law is
`N(0, T·q²)` with `q = |x|²` (because `N·δ = T·|x|⁴`).

The two supplied inequalities are the two places the discrete argument replaces continuous time:

* `hsym` — conditional symmetry of the padding at the first passage time, replacing
  Dambis-Dubins-Schwartz (factor 2);
* `hlevy` — Lévy's maximal inequality for i.i.d. symmetric increments, replacing the reflection
  principle (factor 2).

The conclusion carries the constant **4** against the paper's 2: the discretisation costs exactly
one factor of 2, which moves only the universal constant `c` of Theorem 1.2 and **not** the `n²`
(the `n²` is fixed by `n²T/4 = 4 log n` against `e^{n²T/8} = n²`, and a constant in front of
`K_t(L)` is absorbed by `∫₀^T e^{n²t/8} dt ≤ (8/n²)·e^{n²T/8}`). -/
theorem padded_increment_tail {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hit lev : Set Ω} {S : Ω → ℝ} {M₀ T q : ℝ} {v : ℝ≥0}
    (hT : 0 < T) (hq : 0 < q) (hM₀ : 0 < M₀)
    (hv : (v : ℝ) = T * q ^ 2)
    (hS : Measurable S)
    (hsym : P hit ≤ 2 * P lev)
    (hlevy : P lev ≤ 2 * P (S ⁻¹' Ici M₀))
    (hlaw : P.map S = gaussianReal 0 v) :
    P hit ≤ ENNReal.ofReal (4 * Phi (M₀ / (Real.sqrt T * q))) := by
  have hσ : 0 < Real.sqrt T * q := by positivity
  have hvv : (v : ℝ) = (Real.sqrt T * q) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hT.le]; exact hv
  have hterm : P (S ⁻¹' Ici M₀) ≤ ENNReal.ofReal (Phi (M₀ / (Real.sqrt T * q))) := by
    rw [← Measure.map_apply hS measurableSet_Ici, hlaw]
    exact gaussianReal_Ici_le_Phi_var hσ hM₀ hvv
  have hchain : P hit ≤ 4 * P (S ⁻¹' Ici M₀) := by
    calc P hit ≤ 2 * P lev := hsym
      _ ≤ 2 * (2 * P (S ⁻¹' Ici M₀)) := by gcongr
      _ = 4 * P (S ⁻¹' Ici M₀) := by rw [← mul_assoc]; norm_num
  refine le_trans hchain ?_
  calc (4 : ℝ≥0∞) * P (S ⁻¹' Ici M₀)
      ≤ 4 * ENNReal.ofReal (Phi (M₀ / (Real.sqrt T * q))) := by gcongr
    _ = ENNReal.ofReal (4 * Phi (M₀ / (Real.sqrt T * q))) := by
        rw [ENNReal.ofReal_mul (by norm_num)]
        norm_num

end D5.S3.Arith.Lattices.Klartag
