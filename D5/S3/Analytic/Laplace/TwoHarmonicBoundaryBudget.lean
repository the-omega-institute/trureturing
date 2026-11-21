/- GID: D5/S3/Analytic/Laplace/TwoHarmonicBoundaryBudget
   generality: I
   mirror-B: D5/B/S3/Analytic/Laplace/TwoHarmonicBoundaryBudget
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Probability.Moments.ComplexMGF]
   utility: none
   digest: The three-point Gram form bounds the first two positive Laplace boundary harmonics. -/

import D5.S3.Analytic.Laplace.PositiveSpectralBudget

/-! A two-harmonic bound from three values of a positive Laplace boundary. -/

namespace D5.S3.Analytic.Laplace.TwoHarmonicBoundaryBudget

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ComplexConjugate ComplexOrder Topology

open D5.S3.Analytic.Laplace.PositiveSpectralBudget

private lemma lower_bound_of_quadratic {c : ℝ} {z₁ z₂ : ℂ}
    (h : ∀ (w : ℂ), ‖w‖ = 1 → ∀ u v : ℝ,
      0 ≤ (2 * u ^ 2 + v ^ 2) * c + 4 * u * v * (w * z₁).re +
        2 * u ^ 2 * (w ^ 2 * z₂).re) :
    (Real.sqrt (‖z₂‖ ^ 2 + 8 * ‖z₁‖ ^ 2) - ‖z₂‖) / 2 ≤ c := by
  by_cases hz : z₁ = 0
  · have hc : 0 ≤ c := by
      simpa using h 1 norm_one 0 1
    simpa [hz, Real.sqrt_sq (norm_nonneg z₂)] using hc
  let a := ‖z₁‖
  let b := ‖z₂‖
  have ha : 0 < a := norm_pos_iff.mpr hz
  let w : ℂ := -conj z₁ / (a : ℂ)
  have hw : ‖w‖ = 1 := by
    dsimp [w]
    rw [norm_div, norm_neg, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ha]
    exact div_self ha.ne'
  have hphase : w * z₁ = -(a : ℂ) := by
    have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
    have hnorm : conj z₁ * z₁ = (a : ℂ) ^ 2 := by
      simpa only [a, Complex.ofReal_pow] using Complex.conj_mul' z₁
    calc
      w * z₁ = -(conj z₁ * z₁) / (a : ℂ) := by
        dsimp [w]
        rw [div_mul_eq_mul_div₀, neg_mul]
      _ = -(a : ℂ) := by
        rw [hnorm]
        apply (div_eq_iff haC).2
        ring
  have hsecond : (w ^ 2 * z₂).re ≤ b := by
    calc
      _ ≤ ‖w ^ 2 * z₂‖ := Complex.re_le_norm _
      _ = b := by simp only [norm_mul, norm_pow, hw, one_pow, one_mul, b]
  let s := Real.sqrt (b ^ 2 + 8 * a ^ 2)
  let root := (s - b) / 2
  have hs : s ^ 2 = b ^ 2 + 8 * a ^ 2 := Real.sq_sqrt (by positivity)
  have hroot : root ^ 2 + b * root = 2 * a ^ 2 := by
    dsimp [root]
    linear_combination (1 / 4 : ℝ) * hs
  have hpoly := h w hw root (2 * a)
  rw [hphase, Complex.neg_re, Complex.ofReal_re] at hpoly
  have hupper := mul_le_mul_of_nonneg_left hsecond
    (show (0 : ℝ) ≤ 2 * root ^ 2 by positivity)
  have hweighted :
      4 * root * (2 * a) * a - 2 * root ^ 2 * b ≤ (2 * root ^ 2 + (2 * a) ^ 2) * c := by
    nlinarith only [hpoly, hupper]
  have hid :
      4 * root * (2 * a) * a - 2 * root ^ 2 * b = (2 * root ^ 2 + (2 * a) ^ 2) * root := by
    linear_combination (-2 * root) * hroot
  rw [hid] at hweighted
  have hpos : 0 < 2 * root ^ 2 + (2 * a) ^ 2 :=
    add_pos_of_nonneg_of_pos (by positivity) (pow_pos (mul_pos (by norm_num) ha) 2)
  change root ≤ c
  exact le_of_mul_le_mul_left hweighted hpos

/-- The positive Laplace boundary limits at zero, `γ`, and `2 * γ` bound
the two harmonic magnitudes in terms of the real part of the zero-frequency
limit. If the second harmonic vanishes, the lower bound is `√2 * ‖z₁‖`. -/
theorem two_harmonic_boundary_budget {μ : Measure ℝ} {γ : ℝ} {z₀ z₁ z₂ : ℂ}
    (hc : ∀ σ : ℝ, 0 < σ → Integrable (fun y : ℝ => Real.exp (-σ * y)) μ)
    (h₀ : Tendsto (fun σ : ℝ => (σ : ℂ) * complexMGF id μ (-(σ : ℂ)))
      (𝓝[>] 0) (𝓝 z₀))
    (h₁ : Tendsto (fun σ : ℝ => (σ : ℂ) *
      complexMGF id μ (-((σ : ℂ) + (γ : ℂ) * Complex.I))) (𝓝[>] 0) (𝓝 z₁))
    (h₂ : Tendsto (fun σ : ℝ => (σ : ℂ) *
      complexMGF id μ (-((σ : ℂ) + ((2 * γ : ℝ) : ℂ) * Complex.I)))
      (𝓝[>] 0) (𝓝 z₂)) :
    (Real.sqrt (‖z₂‖ ^ 2 + 8 * ‖z₁‖ ^ 2) - ‖z₂‖) / 2 ≤ z₀.re := by
  classical
  let F (t σ : ℝ) : ℂ :=
    (σ : ℂ) * complexMGF id μ (-((σ : ℂ) + (t : ℂ) * Complex.I))
  -- Only the values of L at the pairwise differences will be used.
  let L (t : ℝ) : ℂ :=
    if h : ∃ z : ℂ, Tendsto (F t) (𝓝[>] 0) (𝓝 z) then h.choose else 0
  have hvalue {t : ℝ} {z : ℂ} (h : Tendsto (F t) (𝓝[>] 0) (𝓝 z)) : L t = z := by
    have hex : ∃ y : ℂ, Tendsto (F t) (𝓝[>] 0) (𝓝 y) := ⟨z, h⟩
    dsimp only [L]
    rw [dif_pos hex]
    exact tendsto_nhds_unique hex.choose_spec h
  have hzero : Tendsto (F 0) (𝓝[>] 0) (𝓝 z₀) := by
    simpa only [F, Complex.ofReal_zero, zero_mul, add_zero] using h₀
  have hfirst : Tendsto (F γ) (𝓝[>] 0) (𝓝 z₁) := h₁
  have hsecond : Tendsto (F (2 * γ)) (𝓝[>] 0) (𝓝 z₂) := h₂
  have hnegFirst : Tendsto (F (-γ)) (𝓝[>] 0) (𝓝 (conj z₁)) :=
    boundary_limit_conjugate (t := γ) h₁
  have hnegSecond : Tendsto (F (-(2 * γ))) (𝓝[>] 0) (𝓝 (conj z₂)) :=
    boundary_limit_conjugate (t := 2 * γ) h₂
  have hL₀ := hvalue hzero
  have hL₁ := hvalue hfirst
  have hL₂ := hvalue hsecond
  have hLneg₁ := hvalue hnegFirst
  have hLneg₂ := hvalue hnegSecond
  let t : Fin 3 → ℝ := ![0, γ, 2 * γ]
  have hsub₁₂ : γ - 2 * γ = -γ := by ring
  have hsub₂₁ : 2 * γ - γ = γ := by ring
  have hdiff (j k : Fin 3) :
      Tendsto (F (t j - t k)) (𝓝[>] 0) (𝓝 (L (t j - t k))) := by
    fin_cases j <;> fin_cases k <;>
      simp only [t, Matrix.cons_val_zero', Matrix.cons_val_succ',
        sub_self, zero_sub, sub_zero, hsub₁₂, hsub₂₁, hL₀, hL₁, hL₂, hLneg₁, hLneg₂] <;>
      assumption
  apply lower_bound_of_quadratic
  intro w hw u v
  let coeff : Fin 3 → ℂ := ![(u : ℂ), (v : ℂ) * w, (u : ℂ) * w ^ 2]
  have hgram := boundary_positive_definite hc (L := L) t coeff hdiff
  have hwc : w * conj w = 1 := by
    simpa only [hw, Complex.ofReal_one, one_pow] using Complex.mul_conj' w
  have hw₂ : w ^ 2 * (conj w) ^ 2 = 1 := by
    rw [← mul_pow, hwc, one_pow]
  have hw₂₁ : w ^ 2 * conj w = w := by
    rw [pow_two, mul_assoc, hwc, mul_one]
  have hw₁₂ : w * (conj w) ^ 2 = conj w := by
    rw [pow_two, ← mul_assoc, hwc, one_mul]
  have hsum : (∑ j, ∑ k, coeff j * conj (coeff k) * L (t j - t k)) =
      ((2 * u ^ 2 + v ^ 2 : ℝ) : ℂ) * z₀ +
        ((2 * u * v : ℝ) : ℂ) * (w * z₁ + conj (w * z₁)) +
        ((u ^ 2 : ℝ) : ℂ) * (w ^ 2 * z₂ + conj (w ^ 2 * z₂)) := by
    simp only [Fin.sum_univ_three, coeff, t, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, sub_self, zero_sub, sub_zero,
      hsub₁₂, hsub₂₁, hL₀, hL₁, hL₂, hLneg₁, hLneg₂, map_mul, map_pow, Complex.conj_ofReal,
      Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_ofNat]
    linear_combination (v : ℂ) ^ 2 * z₀ * hwc + (u : ℂ) ^ 2 * z₀ * hw₂ +
      (u : ℂ) * (v : ℂ) * z₁ * hw₂₁ + (u : ℂ) * (v : ℂ) * conj z₁ * hw₁₂
  rw [hsum] at hgram
  have hreal := (Complex.nonneg_iff.mp hgram).1
  simp only [Complex.add_re, Complex.re_ofReal_mul, Complex.conj_re] at hreal
  convert hreal using 1 <;> ring


end D5.S3.Analytic.Laplace.TwoHarmonicBoundaryBudget
