/- GID: D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaFour
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaFour
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Replica-four constant, correction and remainder of Gaussian multi-entropy. -/

import D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ResidualLimit

/-!
# Replica order four for the `(m, 1, 1)` Gaussian state

At replica order four the sixteen Fourier modes collapse the tripartite product to
`P₃ = P_A P_B P_C ∏_v (1 + x (s + v) / 2)²`. For party sizes `(m, 1, 1)` this gives
`exp (24 GM₄) = ((3m+1)a² - m + 1)⁴ / ((m+1)(ma²+1)²(2ma² - m + 1)(a²+1)⁴)`,
the constant `K₄(m) = log ((3m+1)⁴ / (2m³(m+1))) / 24`, the first correction
`c₄(m) = -(29m² + 14m + 5) / (48 m (3m+1))` and the uniform remainder bound
`0 ≤ R₄ ≤ 1 / (8 a⁴)` for all `m ≥ 1` and `a ≥ 1`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Topology Set
open scoped BigOperators Matrix

namespace D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaFour

open GaussianMultiEntropyAsymptotic GaussianMultiEntropy.ResidualLimit

/-! ## Fourier weights at replica order four -/

theorem unitRoot_four : unitRoot 4 = Complex.I := by
  rw [unitRoot, show 2 * (Real.pi : ℂ) * Complex.I / ((4 : ℕ) : ℂ) =
    (Real.pi : ℂ) / 2 * Complex.I by push_cast; ring]
  exact Complex.exp_pi_div_two_mul_I

theorem tripartiteWeight_four (A B C : ℝ) (hN : A + B + C ≠ 0) (p q : ℕ) :
    tripartiteWeight 4 A B C p q = ((A + B + C) ^ 2 -
      Complex.normSq ((A : ℂ) * Complex.I ^ p + (B : ℂ) * Complex.I ^ q + (C : ℂ))) / 4 := by
  have h := one_sub_tripartiteEigenvalue 4 A B C hN p q
  rw [tripartiteEigenvalue, unitRoot_four] at h
  have hN2 : (A + B + C) ^ 2 ≠ 0 := pow_ne_zero 2 hN
  have h' := congrArg (fun y => y * (A + B + C) ^ 2 / 4) h
  rw [sub_mul, one_mul, div_mul_cancel₀ _ hN2, div_mul_cancel₀ _ hN2] at h'
  linarith

theorem cutWeight_four (u : ℝ) (hu : 0 ≤ u) (k : ℕ) :
    cutWeight 4 u k = ((u + 1) ^ 2 - Complex.normSq ((u : ℂ) * Complex.I ^ k + 1)) / 4 := by
  have hN : u + 1 ≠ 0 := ne_of_gt (by linarith)
  have h := one_sub_cycleEigenvalue 4 u 1 hN k
  rw [cycleEigenvalue, unitRoot_four, mul_one] at h
  have hN2 : (u + 1) ^ 2 ≠ 0 := pow_ne_zero 2 hN
  have h' := congrArg (fun y => y * (u + 1) ^ 2 / 4) h
  simp only [Complex.ofReal_one] at h'
  rw [sub_mul, one_mul, div_mul_cancel₀ _ hN2, div_mul_cancel₀ _ hN2] at h'
  linarith

theorem fin_four_vals : ((0 : Fin 4) : ℕ) = 0 ∧ ((1 : Fin 4) : ℕ) = 1 ∧ ((2 : Fin 4) : ℕ) = 2 ∧
    ((3 : Fin 4) : ℕ) = 3 := ⟨rfl, rfl, rfl, rfl⟩

theorem I_pow_three : Complex.I ^ 3 = -Complex.I := by
  rw [pow_succ, Complex.I_sq]
  ring

/-- The cut product at replica order four. -/
theorem cutProduct_four (u x : ℝ) (hu : 0 ≤ u) :
    cutProduct 4 u x = (1 + x * (u / 2)) ^ 2 * (1 + x * u) := by
  obtain ⟨h0, h1, h2, h3⟩ := fin_four_vals
  rw [cutProduct, Fin.prod_univ_four, h0, h1, h2, h3, cutWeight_four u hu,
    cutWeight_four u hu, cutWeight_four u hu, cutWeight_four u hu]
  simp only [pow_zero, pow_one, Complex.I_sq, I_pow_three, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im]
  ring

/-- The sixteen tripartite weights at replica order four. -/
theorem tripartiteWeight_four_table (A B C : ℝ) (hN : A + B + C ≠ 0) :
    tripartiteWeight 4 A B C 0 0 = 0 ∧
    tripartiteWeight 4 A B C 1 0 = A * (B + C) / 2 ∧
    tripartiteWeight 4 A B C 2 0 = A * (B + C) ∧
    tripartiteWeight 4 A B C 3 0 = A * (B + C) / 2 ∧
    tripartiteWeight 4 A B C 0 1 = B * (A + C) / 2 ∧
    tripartiteWeight 4 A B C 0 2 = B * (A + C) ∧
    tripartiteWeight 4 A B C 0 3 = B * (A + C) / 2 ∧
    tripartiteWeight 4 A B C 1 1 = C * (A + B) / 2 ∧
    tripartiteWeight 4 A B C 2 2 = C * (A + B) ∧
    tripartiteWeight 4 A B C 3 3 = C * (A + B) / 2 ∧
    tripartiteWeight 4 A B C 1 2 = (A * B + A * C + B * C + B * C) / 2 ∧
    tripartiteWeight 4 A B C 3 2 = (A * B + A * C + B * C + B * C) / 2 ∧
    tripartiteWeight 4 A B C 2 1 = (A * B + A * C + B * C + A * C) / 2 ∧
    tripartiteWeight 4 A B C 2 3 = (A * B + A * C + B * C + A * C) / 2 ∧
    tripartiteWeight 4 A B C 1 3 = (A * B + A * C + B * C + A * B) / 2 ∧
    tripartiteWeight 4 A B C 3 1 = (A * B + A * C + B * C + A * B) / 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [tripartiteWeight_four A B C hN] <;>
    simp only [pow_zero, pow_one, Complex.I_sq, I_pow_three, Complex.normSq_apply,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.neg_re, Complex.neg_im, mul_one, mul_neg] <;>
    ring

/-- The order-four product identity `P₃ = P_A P_B P_C ∏_v (1 + x (s + v) / 2)²`. -/
theorem tripartiteProduct_four (A B C x : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hN : A + B + C ≠ 0) :
    tripartiteProduct 4 A B C x =
      cutProduct 4 (A * (B + C)) x * cutProduct 4 (B * (A + C)) x *
        cutProduct 4 (C * (A + B)) x *
        ((1 + x * ((A * B + A * C + B * C + A * B) / 2)) ^ 2 *
          (1 + x * ((A * B + A * C + B * C + A * C) / 2)) ^ 2 *
          (1 + x * ((A * B + A * C + B * C + B * C) / 2)) ^ 2) := by
  obtain ⟨h0, h1, h2, h3⟩ := fin_four_vals
  obtain ⟨w00, w10, w20, w30, w01, w02, w03, w11, w22, w33, w12, w32, w21, w23, w13, w31⟩ :=
    tripartiteWeight_four_table A B C hN
  rw [cutProduct_four (A * (B + C)) x (by positivity), cutProduct_four (B * (A + C)) x
    (by positivity), cutProduct_four (C * (A + B)) x (by positivity), tripartiteProduct,
    Fintype.prod_prod_type]
  simp only [Fin.prod_univ_four, h0, h1, h2, h3, w00, w10, w20, w30, w01, w02, w03, w11, w22,
    w33, w12, w32, w21, w23, w13, w31, mul_zero, add_zero, one_mul]
  generalize 1 + x * (A * (B + C) / 2) = X₁
  generalize 1 + x * (A * (B + C)) = X₂
  generalize 1 + x * (B * (A + C) / 2) = X₃
  generalize 1 + x * (B * (A + C)) = X₄
  generalize 1 + x * (C * (A + B) / 2) = X₅
  generalize 1 + x * (C * (A + B)) = X₆
  generalize 1 + x * ((A * B + A * C + B * C + A * B) / 2) = Y₁
  generalize 1 + x * ((A * B + A * C + B * C + A * C) / 2) = Y₂
  generalize 1 + x * ((A * B + A * C + B * C + B * C) / 2) = Y₃
  ring

/-! ## The closed form for party sizes `(m, 1, 1)` -/

/-- The rational argument of `exp (24 GM₄)` for party sizes `(m, 1, 1)`. -/
def closedForm (m a : ℝ) : ℝ :=
  ((3 * m + 1) * a ^ 2 - m + 1) ^ 4 /
    ((m + 1) * (m * a ^ 2 + 1) ^ 2 * (2 * m * a ^ 2 - m + 1) * (a ^ 2 + 1) ^ 4)

theorem fourierGM_four_closed (m a : ℝ) (hm : 0 < m) (ha : 1 ≤ a) :
    fourierGM 4 m 1 1 a = Real.log (closedForm m a) / 24 := by
  have hx : 0 ≤ squeezing (m + 1 + 1) a := div_nonneg (by nlinarith) (by linarith)
  set x := squeezing (m + 1 + 1) a with hxdef
  have hP := tripartiteProduct_four m 1 1 x hm.le zero_le_one zero_le_one (by positivity)
  set PA := cutProduct 4 (m * (1 + 1)) x with hPA
  set PB := cutProduct 4 (1 * (m + 1)) x with hPB
  set Qv := (1 + x * ((m * 1 + m * 1 + 1 * 1 + m * 1) / 2)) ^ 2 *
    (1 + x * ((m * 1 + m * 1 + 1 * 1 + m * 1) / 2)) ^ 2 *
    (1 + x * ((m * 1 + m * 1 + 1 * 1 + 1 * 1) / 2)) ^ 2 with hQv
  have hA0 : 0 < PA := cutProduct_pos 4 _ x (by positivity) hx
  have hB0 : 0 < PB := cutProduct_pos 4 _ x (by positivity) hx
  have hQ0 : 0 < Qv := by
    have h1 : 0 < 1 + x * ((m * 1 + m * 1 + 1 * 1 + m * 1) / 2) := by positivity
    have h2 : 0 < 1 + x * ((m * 1 + m * 1 + 1 * 1 + 1 * 1) / 2) := by positivity
    positivity
  have hm1 : m + 1 ≠ 0 := ne_of_gt (by linarith)
  have ha2 : 1 ≤ a ^ 2 := by nlinarith
  have hma : m ≤ m * a ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left ha2 hm.le]
  have hx' : x = (a ^ 2 - 1) / (m + 1) := by
    rw [hxdef, squeezing]
    congr 1
    ring
  have f1 : 1 + x * (m * (1 + 1) / 2) = (m * a ^ 2 + 1) / (m + 1) := by
    rw [hx']; first | (field_simp; ring) | field_simp
  have f2 : 1 + x * (m * (1 + 1)) = (2 * m * a ^ 2 - m + 1) / (m + 1) := by
    rw [hx']; first | (field_simp; ring) | field_simp
  have f3 : 1 + x * (1 * (m + 1) / 2) = (a ^ 2 + 1) / 2 := by
    rw [hx']; first | (field_simp; ring) | field_simp
  have f4 : 1 + x * (1 * (m + 1)) = a ^ 2 := by
    rw [hx']; first | (field_simp; ring) | field_simp
  have f5 : 1 + x * ((m * 1 + m * 1 + 1 * 1 + m * 1) / 2) =
      ((3 * m + 1) * a ^ 2 - m + 1) / (2 * (m + 1)) := by
    rw [hx']; first | (field_simp; ring) | field_simp
  have f6 : 1 + x * ((m * 1 + m * 1 + 1 * 1 + 1 * 1) / 2) = a ^ 2 := by
    rw [hx']; first | (field_simp; ring) | field_simp
  have hcl : closedForm m a = Qv / (PA * PB * PB) := by
    rw [hQv, hPA, hPB, cutProduct_four (m * (1 + 1)) x (by positivity),
      cutProduct_four (1 * (m + 1)) x (by positivity), f1, f2, f3, f4, f5, f6, closedForm]
    have h1 : m * a ^ 2 + 1 ≠ 0 := by positivity
    have h2 : 2 * m * a ^ 2 - m + 1 ≠ 0 := ne_of_gt (by linarith)
    have h3 : a ^ 2 + 1 ≠ 0 := by positivity
    have h5 : a ≠ 0 := ne_of_gt (by linarith)
    field_simp
  have hAB : PA * PB ≠ 0 := (mul_pos hA0 hB0).ne'
  have hABB : PA * PB * PB ≠ 0 := (mul_pos (mul_pos hA0 hB0) hB0).ne'
  rw [fourierGM, ← hxdef, ← hPA, ← hPB, hP, hcl, Real.log_div hQ0.ne' hABB,
    Real.log_mul hABB hQ0.ne',
    Real.log_mul hAB hB0.ne', Real.log_mul hA0.ne' hB0.ne']
  push_cast
  ring

/-! ## Constant, first correction and remainder -/

/-- The replica-four constant `K₄(m) = log ((3m+1)⁴ / (2m³(m+1))) / 24`. -/
def K4 (m : ℝ) : ℝ := Real.log ((3 * m + 1) ^ 4 / (2 * m ^ 3 * (m + 1))) / 24

/-- The first correction `c₄(m) = -(29m² + 14m + 5) / (48 m (3m+1))`. -/
def c4 (m : ℝ) : ℝ := -(29 * m ^ 2 + 14 * m + 5) / (48 * m * (3 * m + 1))

/-- The logarithmic remainder `h(t)` with `r = (m-1)/(3m+1)`, `b = 1/m`, `s₀ = (m-1)/(2m)`. -/
def remainderLog (m t : ℝ) : ℝ :=
  4 * Real.log (1 - (m - 1) / (3 * m + 1) * t) - 2 * Real.log (1 + 1 / m * t) -
    Real.log (1 - (m - 1) / (2 * m) * t) - 4 * Real.log (1 + t)

theorem fourierGM_four_expansion (m a : ℝ) (hm : 1 ≤ m) (ha : 1 ≤ a) :
    fourierGM 4 m 1 1 a = -Real.log a / 4 + K4 m + remainderLog m (1 / a ^ 2) / 24 := by
  have hm0 : 0 < m := by linarith
  have ha0 : 0 < a := by linarith
  set t := 1 / a ^ 2 with htdef
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ 1 := by
    rw [htdef, div_le_one (by positivity)]
    nlinarith
  have hr : 0 < 1 - (m - 1) / (3 * m + 1) * t := by
    have : (m - 1) / (3 * m + 1) < 1 := by
      rw [div_lt_one (by linarith)]
      linarith
    nlinarith [div_nonneg (by linarith : (0 : ℝ) ≤ m - 1) (by linarith : (0 : ℝ) ≤ 3 * m + 1)]
  have hb : 0 < 1 + 1 / m * t := by positivity
  have hs : 0 < 1 - (m - 1) / (2 * m) * t := by
    have : (m - 1) / (2 * m) < 1 := by
      rw [div_lt_one (by linarith)]
      linarith
    nlinarith [div_nonneg (by linarith : (0 : ℝ) ≤ m - 1) (by linarith : (0 : ℝ) ≤ 2 * m)]
  have ht' : 0 < 1 + t := by linarith
  have hc : 0 < (3 * m + 1) ^ 4 / (2 * m ^ 3 * (m + 1)) := by positivity
  have hsplit : closedForm m a = (3 * m + 1) ^ 4 / (2 * m ^ 3 * (m + 1)) *
      ((1 - (m - 1) / (3 * m + 1) * t) ^ 4 /
        ((1 + 1 / m * t) ^ 2 * (1 - (m - 1) / (2 * m) * t) * (1 + t) ^ 4)) / a ^ 6 := by
    rw [closedForm, htdef]
    have h1 : 3 * m + 1 ≠ 0 := ne_of_gt (by linarith)
    have ha2 : 1 ≤ a ^ 2 := by nlinarith
    have hma : m ≤ m * a ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left ha2 hm0.le]
    have h2 : 2 * m * a ^ 2 - m + 1 ≠ 0 := ne_of_gt (by linarith)
    have h3 : m + 1 ≠ 0 := ne_of_gt (by linarith)
    have h4 : m * a ^ 2 + 1 ≠ 0 := by positivity
    have h5 : a ^ 2 + 1 ≠ 0 := by positivity
    have h6 : m ≠ 0 := hm0.ne'
    have h7 : a ≠ 0 := ha0.ne'
    field_simp
    ring
  have hden1 : 0 < (1 + 1 / m * t) ^ 2 * (1 - (m - 1) / (2 * m) * t) := by positivity
  have hden : 0 < (1 + 1 / m * t) ^ 2 * (1 - (m - 1) / (2 * m) * t) * (1 + t) ^ 4 := by
    positivity
  have hR : 0 < (1 - (m - 1) / (3 * m + 1) * t) ^ 4 /
      ((1 + 1 / m * t) ^ 2 * (1 - (m - 1) / (2 * m) * t) * (1 + t) ^ 4) := by positivity
  have hnum : 0 < (3 * m + 1) ^ 4 / (2 * m ^ 3 * (m + 1)) *
      ((1 - (m - 1) / (3 * m + 1) * t) ^ 4 /
        ((1 + 1 / m * t) ^ 2 * (1 - (m - 1) / (2 * m) * t) * (1 + t) ^ 4)) := mul_pos hc hR
  rw [fourierGM_four_closed m a hm0 ha, hsplit, Real.log_div hnum.ne' (pow_pos ha0 6).ne',
    Real.log_mul hc.ne' hR.ne', Real.log_div (pow_pos hr 4).ne' hden.ne',
    Real.log_mul hden1.ne' (pow_pos ht' 4).ne', Real.log_mul (pow_pos hb 2).ne' hs.ne',
    Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow, remainderLog, K4]
  push_cast
  ring

/-- Uniform second-order bounds for the logarithmic remainder on `[0, 1]`. -/
theorem log_remainder_bounds (r b s t : ℝ) (hr0 : 0 ≤ r) (hr : r < 1 / 3) (hb0 : 0 < b)
    (hb1 : b ≤ 1) (hs : s = (1 - b) / 2) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ (4 * Real.log (1 - r * t) - 2 * Real.log (1 + b * t) - Real.log (1 - s * t) -
        4 * Real.log (1 + t)) - (-4 * r - 2 * b + s - 4) * t ∧
      (4 * Real.log (1 - r * t) - 2 * Real.log (1 + b * t) - Real.log (1 - s * t) -
        4 * Real.log (1 + t)) - (-4 * r - 2 * b + s - 4) * t ≤ 3 * t ^ 2 := by
  have hs0 : 0 ≤ s := by rw [hs]; linarith
  have hs1 : s ≤ 1 / 2 := by rw [hs]; linarith
  set c := -4 * r - 2 * b + s - 4 with hcdef
  let φ : ℝ → ℝ := fun u => 4 * Real.log (1 - r * u) - 2 * Real.log (1 + b * u) -
    Real.log (1 - s * u) - 4 * Real.log (1 + u) - c * u
  let β : ℝ → ℝ := fun u => -(4 * r ^ 2 / (1 - r * u)) + 2 * b ^ 2 / (1 + b * u) +
    s ^ 2 / (1 - s * u) + 4 / (1 + u)
  have hpos : ∀ u ∈ Icc (0 : ℝ) 1, 0 < 1 - r * u ∧ 0 < 1 + b * u ∧ 0 < 1 - s * u ∧ 0 < 1 + u := by
    intro u hu
    obtain ⟨hu0, hu1⟩ := hu
    refine ⟨by nlinarith [mul_le_mul_of_nonneg_left hu1 hr0], by positivity,
      by nlinarith [mul_le_mul_of_nonneg_left hu1 hs0], by linarith⟩
  have hderiv : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt φ (u * β u) u := by
    intro u hu
    obtain ⟨h1, h2, h3, h4⟩ := hpos u hu
    have dA := (((hasDerivAt_id' u).const_mul r).const_sub 1).log h1.ne'
    have dB := (((hasDerivAt_id' u).const_mul b).const_add 1).log h2.ne'
    have dC := (((hasDerivAt_id' u).const_mul s).const_sub 1).log h3.ne'
    have dD := ((hasDerivAt_id' u).const_add 1).log h4.ne'
    have hall := ((((dA.const_mul 4).sub (dB.const_mul 2)).sub dC).sub (dD.const_mul 4)).sub
      ((hasDerivAt_id' u).const_mul c)
    refine hall.congr_deriv ?_
    have h1' := h1.ne'
    have h2' := h2.ne'
    have h3' := h3.ne'
    have h4' := h4.ne'
    have t1 : 4 * (-(r * 1) / (1 - r * u)) = -4 * r + u * (-(4 * r ^ 2 / (1 - r * u))) := by
      field_simp; ring
    have t2 : 2 * (b * 1 / (1 + b * u)) = 2 * b - u * (2 * b ^ 2 / (1 + b * u)) := by
      field_simp; ring
    have t3 : -(s * 1) / (1 - s * u) = -s - u * (s ^ 2 / (1 - s * u)) := by
      field_simp; ring
    have t4 : 4 * (1 / (1 + u)) = 4 - u * (4 / (1 + u)) := by
      field_simp; ring
    rw [t1, t2, t3, t4]
    simp only [β, hcdef]
    ring
  have hβ : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ β u ∧ β u ≤ 6 := by
    intro u hu
    obtain ⟨h1, h2, h3, h4⟩ := hpos u hu
    obtain ⟨hu0, hu1⟩ := hu
    have hA : 4 * r ^ 2 / (1 - r * u) ≤ 4 / (1 + u) := by
      rw [div_le_div_iff₀ h1 h4]
      nlinarith [mul_nonneg hr0 hu0, mul_le_mul_of_nonneg_left hu1 hr0,
        mul_le_mul_of_nonneg_left hu1 (sq_nonneg r), mul_self_nonneg r, mul_nonneg hr0 hr0]
    have hB : 0 ≤ 2 * b ^ 2 / (1 + b * u) := by positivity
    have hC : 0 ≤ s ^ 2 / (1 - s * u) := div_nonneg (sq_nonneg s) h3.le
    have hA' : 0 ≤ 4 * r ^ 2 / (1 - r * u) := div_nonneg (by positivity) h1.le
    have hB' : 2 * b ^ 2 / (1 + b * u) ≤ 2 * b ^ 2 :=
      div_le_self (by positivity) (by nlinarith [mul_nonneg hb0.le hu0])
    have hC' : s ^ 2 / (1 - s * u) ≤ s ^ 2 / (1 - s) :=
      div_le_div_of_nonneg_left (sq_nonneg s) (by linarith) (by nlinarith)
    have hD' : 4 / (1 + u) ≤ 4 := div_le_self (by norm_num) (by linarith)
    have hE : s ^ 2 / (1 - s) ≤ 2 - 2 * b ^ 2 := by
      rw [div_le_iff₀ (by linarith), hs]
      nlinarith [mul_nonneg (sub_nonneg.mpr hb1) hb0.le, sq_nonneg b,
        mul_nonneg (sub_nonneg.mpr hb1) (sq_nonneg b), mul_nonneg (sub_nonneg.mpr hb1)
          (sub_nonneg.mpr hb1)]
    simp only [β]
    constructor <;> linarith
  have hcont : ContinuousOn φ (Icc 0 1) :=
    fun u hu => (hderiv u hu).continuousAt.continuousWithinAt
  have hint : interior (Icc (0 : ℝ) 1) = Ioo 0 1 := interior_Icc
  have hmono : MonotoneOn φ (Icc 0 1) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1) hcont
      (fun u hu => (hderiv u (interior_subset hu)).hasDerivWithinAt) (fun u hu => ?_)
    rw [hint] at hu
    exact mul_nonneg hu.1.le (hβ u (Ioo_subset_Icc_self hu)).1
  let ψ : ℝ → ℝ := fun u => 3 * (u * u) - φ u
  have hderiv' : ∀ u ∈ Icc (0 : ℝ) 1, HasDerivAt ψ (u * (6 - β u)) u := by
    intro u hu
    have h := (((hasDerivAt_id' u).mul (hasDerivAt_id' u)).const_mul 3).sub (hderiv u hu)
    refine h.congr_deriv ?_
    ring
  have hcont' : ContinuousOn ψ (Icc 0 1) :=
    fun u hu => (hderiv' u hu).continuousAt.continuousWithinAt
  have hmono' : MonotoneOn ψ (Icc 0 1) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1) hcont'
      (fun u hu => (hderiv' u (interior_subset hu)).hasDerivWithinAt) (fun u hu => ?_)
    rw [hint] at hu
    exact mul_nonneg hu.1.le (by linarith [(hβ u (Ioo_subset_Icc_self hu)).2])
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_refl 0, zero_le_one⟩
  have htI : t ∈ Icc (0 : ℝ) 1 := ⟨ht0, ht1⟩
  have hφ0 : φ 0 = 0 := by simp [φ]
  have hψ0 : ψ 0 = 0 := by simp [ψ, hφ0]
  have hle := hmono h0 htI ht0
  have hle' := hmono' h0 htI ht0
  rw [hφ0] at hle
  rw [hψ0] at hle'
  simp only [φ, ψ] at hle hle'
  have htt : t ^ 2 = t * t := sq t
  constructor <;> linarith

/-- The replica-four expansion with the uniform remainder bound for party sizes `(m, 1, 1)`. -/
theorem fourierGM_four_remainder (m a : ℝ) (hm : 1 ≤ m) (ha : 1 ≤ a) :
    0 ≤ fourierGM 4 m 1 1 a - (-Real.log a / 4 + K4 m + c4 m / a ^ 2) ∧
      fourierGM 4 m 1 1 a - (-Real.log a / 4 + K4 m + c4 m / a ^ 2) ≤ 1 / (8 * a ^ 4) := by
  have hm0 : 0 < m := by linarith
  have ha0 : 0 < a := by linarith
  have ht0 : 0 ≤ 1 / a ^ 2 := by positivity
  have ht1 : 1 / a ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  have hr0 : 0 ≤ (m - 1) / (3 * m + 1) := div_nonneg (by linarith) (by linarith)
  have hr : (m - 1) / (3 * m + 1) < 1 / 3 := by
    rw [div_lt_iff₀ (by linarith)]
    linarith
  have hb0 : 0 < 1 / m := by positivity
  have hb1 : 1 / m ≤ 1 := by rw [div_le_one hm0]; exact hm
  have hm0' : m ≠ 0 := hm0.ne'
  have h3m : 3 * m + 1 ≠ 0 := ne_of_gt (by linarith)
  have hs : (m - 1) / (2 * m) = (1 - 1 / m) / 2 := by field_simp
  obtain ⟨hlo, hhi⟩ := log_remainder_bounds _ _ _ _ hr0 hr hb0 hb1 hs ht0 ht1
  have hc : 24 * c4 m = -4 * ((m - 1) / (3 * m + 1)) - 2 * (1 / m) + (m - 1) / (2 * m) - 4 := by
    rw [c4]
    field_simp
    ring
  have hexp := fourierGM_four_expansion m a hm ha
  have hR : fourierGM 4 m 1 1 a - (-Real.log a / 4 + K4 m + c4 m / a ^ 2) =
      (remainderLog m (1 / a ^ 2) -
        (-4 * ((m - 1) / (3 * m + 1)) - 2 * (1 / m) + (m - 1) / (2 * m) - 4) * (1 / a ^ 2)) /
        24 := by
    rw [hexp, ← hc]
    field_simp
    ring
  have hrem : remainderLog m (1 / a ^ 2) =
      4 * Real.log (1 - (m - 1) / (3 * m + 1) * (1 / a ^ 2)) -
        2 * Real.log (1 + 1 / m * (1 / a ^ 2)) -
        Real.log (1 - (m - 1) / (2 * m) * (1 / a ^ 2)) - 4 * Real.log (1 + 1 / a ^ 2) := rfl
  rw [hR, hrem]
  have h8 : 3 * (1 / a ^ 2) ^ 2 / 24 = 1 / (8 * a ^ 4) := by field_simp; ring
  constructor
  · exact div_nonneg hlo (by norm_num)
  · rw [← h8]
    exact div_le_div_of_nonneg_right hhi (by norm_num)

/-! ## Statements for the replica-integral genuine multi-entropy -/

/-- The closed form `exp (24 GM₄) = ((3m+1)a² - m + 1)⁴ / ((m+1)(ma²+1)²(2ma² - m + 1)(a²+1)⁴)`
for the genuine multi-entropy of the fully symmetric pure Gaussian state `(m, 1, 1)`. -/
theorem GM3_four_closed (m : ℕ) (hm : 1 ≤ m) (a : ℝ) (ha : 1 ≤ a) :
    GM3 4 m 1 1 a = Real.log (closedForm m a) / 24 := by
  rw [GM3_eq_fourierGM 4 m 1 1 (by norm_num) a ha (by omega) one_pos one_pos]
  push_cast
  exact fourierGM_four_closed m a (by exact_mod_cast hm) ha

/-- The replica-four law `GM₄ = -log a / 4 + K₄(m) + c₄(m) / a² + R₄` with
`0 ≤ R₄ ≤ 1 / (8 a⁴)`, for every integer `m ≥ 1` and real `a ≥ 1`. -/
theorem GM3_four_remainder (m : ℕ) (hm : 1 ≤ m) (a : ℝ) (ha : 1 ≤ a) :
    0 ≤ GM3 4 m 1 1 a - (-Real.log a / 4 + K4 m + c4 m / a ^ 2) ∧
      GM3 4 m 1 1 a - (-Real.log a / 4 + K4 m + c4 m / a ^ 2) ≤ 1 / (8 * a ^ 4) := by
  have hfour : GM3 4 m 1 1 a = fourierGM 4 m 1 1 a := by
    rw [GM3_four_closed m hm a ha, fourierGM_four_closed m a (by exact_mod_cast hm) ha]
  rw [hfour]
  exact fourierGM_four_remainder m a (by exact_mod_cast hm) ha

/-- The large-squeezing limit `GM₄ + log a / 4 → K₄(m)`. -/
theorem GM3_four_tendsto (m : ℕ) (hm : 1 ≤ m) :
    Tendsto (fun a : ℝ => GM3 4 m 1 1 a + ((4 : ℕ) - 2 : ℝ) / (2 * (4 : ℕ)) * Real.log a)
      atTop (𝓝 (K4 m)) := by
  have hc : Tendsto (fun a : ℝ => K4 m + c4 m / a ^ 2) atTop (𝓝 (K4 m)) := by
    simpa using (tendsto_const_nhds (x := K4 m)).add ((tendsto_const_nhds (x := c4 m)).div_atTop
      (tendsto_pow_atTop two_ne_zero : Tendsto (fun a : ℝ => a ^ 2) atTop atTop))
  have hu : Tendsto (fun a : ℝ => K4 m + c4 m / a ^ 2 + 1 / (8 * a ^ 4)) atTop (𝓝 (K4 m)) := by
    simpa using hc.add ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop
      ((tendsto_pow_atTop (by norm_num : (4 : ℕ) ≠ 0) : Tendsto (fun a : ℝ => a ^ 4) atTop
        atTop).const_mul_atTop (by norm_num : (0 : ℝ) < 8)))
  have e : ∀ a : ℝ, ((4 : ℕ) - 2 : ℝ) / (2 * (4 : ℕ)) * Real.log a = Real.log a / 4 := by
    intro a
    push_cast
    ring
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hc hu ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with a ha
    have h := (GM3_four_remainder m hm a ha).1
    linarith [e a]
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with a ha
    have h := (GM3_four_remainder m hm a ha).2
    linarith [e a]

/-- The residual-determinant constant at replica order four equals `K₄(m)`. -/
theorem residualConstant_four (m : ℕ) (hm : 1 ≤ m) : residualConstant 4 m 1 1 = K4 m := by
  have h := tendsto_nhds_unique
    (residual_determinant_limit 4 m 1 1 (by norm_num) (by omega) one_pos one_pos)
    (GM3_four_tendsto m hm)
  simpa using h

end D5.S3.Quantum.Entanglement.GaussianMultiEntropy.ReplicaFour
