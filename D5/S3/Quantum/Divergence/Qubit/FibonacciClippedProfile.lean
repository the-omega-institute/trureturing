/- GID: D5/S3/Quantum/Divergence/Qubit/FibonacciClippedProfile
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/Qubit/FibonacciClippedProfile
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A six-interval affine bound for the clipped Fibonacci qubit profile. -/

import D5.S3.Quantum.Divergence.Qubit.SignedProfile
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! The global positive-part profile bound for the Fibonacci pure qubit triple. -/

set_option autoImplicit false

noncomputable section

open Matrix
open scoped ComplexOrder MatrixOrder InnerProductSpace

namespace D5.S3.Quantum.Divergence.Qubit.FibonacciClippedProfile

open SignedProfile

private abbrev b (t : ℝ) := 66 * t - 88
private abbrev c (t : ℝ) := 15 * t - 25
private abbrev d (t : ℝ) := 28 - 12 * t
private abbrev w (t : ℝ) := 69 * t - 85

/-- Weights of the unnormalized Fibonacci contrast. -/
def weights (t : ℝ) : Fin 3 → ℝ := ![-b t, -c t, d t]

/-- Benchmark preparations, with the first two coinciding and the third orthogonal. -/
def benchmark : Fin 3 → Fin 2 → ℂ := ![![1, 0], ![1, 0], ![0, 1]]

/-- Endpoints of the six intervals of the profile certificate. -/
def timeCut : Fin 7 → ℝ := ![4 / 3, 113 / 81, 22 / 15, 5 / 3, 9 / 5, 2, 7 / 3]

/-- Six affine bounds in the overlap deficit of the first pair and the two other overlaps. -/
def envelope (i : Fin 6) (t X Y Z : ℝ) : ℝ :=
  ![b t ^ 2 / d t * X + b t * Z,
    -(b t * c t / w t) * X - (97 / 100 * (b t + c t)) * Y - c t * d t / w t * Z,
    -(b t * c t / w t) * X - b t * d t / w t * Y - c t * d t / w t * Z,
    -(53 / 55 * (b t * c t / w t)) * X - (24 / 25 * (b t * d t / w t)) * Y,
    -(53 / 55 * (b t * c t / w t)) * X - (d t - 53 / 55 * (b t * c t / w t)) * Y,
    -d t * X] i

private theorem normSq_inner (u v : Fin 2 → ℂ)
    (hu : star u ⬝ᵥ u = 1) (hv : star v ⬝ᵥ v = 1) :
    Complex.normSq (star u ⬝ᵥ v) ≤ 1 := by
  let U : EuclideanSpace ℂ (Fin 2) := WithLp.toLp 2 u
  let V : EuclideanSpace ℂ (Fin 2) := WithLp.toLp 2 v
  have inner (x y : Fin 2 → ℂ) :
      ⟪(WithLp.toLp 2 x : EuclideanSpace ℂ (Fin 2)), WithLp.toLp 2 y⟫_ℂ =
        star x ⬝ᵥ y := by
    simp [PiLp.inner_apply, dotProduct, mul_comm]
  have hU : ‖U‖ = 1 := by
    have h := norm_sq_eq_re_inner (𝕜 := ℂ) U
    rw [inner u u, hu] at h
    exact (sq_eq_sq₀ (norm_nonneg U) zero_le_one).mp (by simpa using h)
  have hV : ‖V‖ = 1 := by
    have h := norm_sq_eq_re_inner (𝕜 := ℂ) V
    rw [inner v v, hv] at h
    exact (sq_eq_sq₀ (norm_nonneg V) zero_le_one).mp (by simpa using h)
  have h := norm_inner_le_norm (𝕜 := ℂ) U V
  rw [hU, hV, one_mul, inner u v] at h
  rw [Complex.normSq_eq_norm_sq]
  simpa only [one_pow] using (sq_le_sq₀ (norm_nonneg _) zero_le_one).mpr h

private theorem sum_weights (t : ℝ) : ∑ i, weights t i = d t - (b t + c t) := by
  simp [weights, Fin.sum_univ_three]
  ring

private theorem gap_formula (t : ℝ) (ψ : Fin 3 → Fin 2 → ℂ) :
    gapSq (weights t) ψ = (w t) ^ 2 + 4 *
      (-(b t * c t) * (1 - overlap ψ 0 1) - b t * d t * overlap ψ 0 2 -
        c t * d t * overlap ψ 1 2) := by
  rw [gapSq, sum_weights, Finset.sum_filter, Fintype.sum_prod_type]
  simp [Fin.sum_univ_three, weights]
  ring

private theorem benchmark_unit (i : Fin 3) : star (benchmark i) ⬝ᵥ benchmark i = 1 := by
  fin_cases i <;> simp [benchmark, dotProduct, Fin.sum_univ_two]

private theorem benchmark_trace (t : ℝ) (hd : 0 ≤ d t) :
    (contrast (weights t) benchmark)⁺.trace.re = d t + max (-(b t + c t)) 0 := by
  rw [trace_posPart_contrast _ _ benchmark_unit, sum_weights, gap_formula]
  have hoverlaps :
      overlap benchmark 0 1 = 1 ∧ overlap benchmark 0 2 = 0 ∧ overlap benchmark 1 2 = 0 := by
    norm_num [overlap, benchmark, dotProduct, Fin.sum_univ_two]
  rw [hoverlaps.1, hoverlaps.2.1, hoverlaps.2.2]
  simp only [sub_self, mul_zero, add_zero, Real.sqrt_sq_eq_abs]
  rcases le_total 0 (b t + c t) with hp | hp
  · rw [max_eq_right (neg_nonpos.mpr hp), abs_of_nonneg (by dsimp [b, c, d, w]; linarith : 0 ≤ w t),
      max_eq_right (abs_le.mpr ⟨by dsimp [b, c, d, w]; linarith, by dsimp [b, c, d, w]; linarith⟩)]
    dsimp [b, c, d, w]
    ring
  · rw [max_eq_left (neg_nonneg.mpr hp),
      abs_of_nonneg (sub_nonneg.mpr (hp.trans hd)),
      max_eq_left (abs_le.mpr ⟨by dsimp [b, c, d, w]; linarith, by dsimp [b, c, d, w]; linarith⟩)]
    ring

private theorem early_bound (t : ℝ) (ψ : Fin 3 → Fin 2 → ℂ)
    (hψ : ∀ i, star (ψ i) ⬝ᵥ ψ i = 1)
    (ht₀ : 4 / 3 ≤ t) (ht₁ : t ≤ 113 / 81) :
    (contrast (weights t) ψ)⁺.trace.re - (contrast (weights t) benchmark)⁺.trace.re ≤
      envelope 0 t (1 - overlap ψ 0 1) (overlap ψ 0 2) (overlap ψ 1 2) := by
  let X := 1 - overlap ψ 0 1
  let Y := overlap ψ 0 2
  let Z := overlap ψ 1 2
  let p := -(b t + c t)
  let s := b t ^ 2 / d t * X + b t * Z
  have hX : 0 ≤ X := sub_nonneg.mpr (normSq_inner _ _ (hψ 0) (hψ 1))
  have hX₁ : X ≤ 1 := sub_le_self _ (Complex.normSq_nonneg _)
  have hY : 0 ≤ Y := Complex.normSq_nonneg _
  have hZ : 0 ≤ Z := Complex.normSq_nonneg _
  have hZ₁ : Z ≤ 1 := normSq_inner _ _ (hψ 1) (hψ 2)
  have hp : 0 ≤ p := by dsimp [p]; linarith
  have hb : 0 ≤ b t := by dsimp [b, c, d, w]; linarith
  have hd : 0 < d t := by dsimp [b, c, d, w]; linarith
  have hbd : b t ≤ d t := by dsimp [b, c, d, w]; linarith
  have hs₀ : 0 ≤ b t ^ 2 / d t * X :=
    mul_nonneg (div_nonneg (sq_nonneg _) hd.le) hX
  have hs : 0 ≤ s := add_nonneg hs₀ (mul_nonneg hb hZ)
  have hsd : s * d t = b t ^ 2 * X + b t * d t * Z := by
    dsimp only [s]
    calc
      _ = (b t ^ 2 / d t * d t) * X + b t * d t * Z := by ring
      _ = _ := by rw [div_mul_cancel₀ _ hd.ne']
  have hlinear : 0 ≤ s - b t * X + d t * (1 - Z) := by
    dsimp only [s]
    nlinarith only [hs₀, mul_nonneg hb (sub_nonneg.mpr hX₁),
      mul_nonneg (sub_nonneg.mpr hbd) (sub_nonneg.mpr hZ₁)]
  have hdet : (contrast (weights t) ψ).det.re =
      -(b t ^ 2 * X + b t * d t * Z) + b t * d t * Y + p * (d t * (1 - Z) - b t * X) := by
    have h := gapSq_eq_trace_det (weights t) ψ hψ
    rw [sum_weights, gap_formula] at h
    change w t ^ 2 + 4 * (-(b t * c t) * X - b t * d t * Y - c t * d t * Z) = _ at h
    dsimp [p, b, c, d, w] at h ⊢
    linarith only [h]
  have htrace : d t - (b t + c t) = d t + p := by dsimp [p]; ring
  have hroot : Real.sqrt (gapSq (weights t) ψ) ≤ d t + p + 2 * s := by
    apply (Real.sqrt_le_left (by linarith)).mpr
    rw [gapSq_eq_trace_det _ _ hψ, sum_weights, htrace, hdet]
    nlinarith only [hsd, sq_nonneg s, mul_nonneg hp hlinear, mul_nonneg (mul_nonneg hb hd.le) hY]
  rw [trace_posPart_contrast _ _ hψ, sum_weights, htrace, benchmark_trace t hd.le]
  change ((d t + p) + max |d t + p| _) / 2 - (d t + max p 0) ≤ s
  rw [abs_of_nonneg (add_nonneg hd.le hp), max_eq_left hp]
  have hmax := max_le (show d t + p ≤ d t + p + 2 * s by linarith) hroot
  linarith only [hmax]

private theorem clipped_le (t : ℝ) (ψ : Fin 3 → Fin 2 → ℂ)
    (hψ : ∀ i, star (ψ i) ⬝ᵥ ψ i = 1) {L : ℝ} (hd : 0 ≤ d t) (hp : 0 ≤ b t + c t)
    (hclip₁ : -(b t + c t) ≤ L) (hclip₂ : -d t ≤ L)
    (htan : -(b t * c t) * (1 - overlap ψ 0 1) - b t * d t * overlap ψ 0 2 -
      c t * d t * overlap ψ 1 2 ≤ w t * L) :
    (contrast (weights t) ψ)⁺.trace.re - (contrast (weights t) benchmark)⁺.trace.re ≤ L := by
  have habs : |d t - (b t + c t)| ≤ w t + 2 * L := by
    apply abs_le.mpr
    dsimp [b, c, d, w] at *
    constructor <;> linarith
  have hroot : Real.sqrt (gapSq (weights t) ψ) ≤ w t + 2 * L := by
    apply (Real.sqrt_le_left ((abs_nonneg _).trans habs)).mpr
    rw [gap_formula]
    nlinarith only [htan, sq_nonneg L]
  rw [trace_posPart_contrast _ _ hψ, sum_weights, benchmark_trace t hd,
    max_eq_right (neg_nonpos.mpr hp), add_zero]
  have hmax := max_le habs hroot
  dsimp [b, c, d, w] at *
  linarith only [hmax]

private theorem middle_bound (t : ℝ) (ψ : Fin 3 → Fin 2 → ℂ)
    (hψ : ∀ i, star (ψ i) ⬝ᵥ ψ i = 1)
    (ht₀ : 113 / 81 ≤ t) (ht₁ : t ≤ 5 / 3) {v : ℝ}
    (hv : 0 ≤ v) (hvw : v * w t ≤ b t * d t) (hvp : v ≤ b t + c t) :
    (contrast (weights t) ψ)⁺.trace.re - (contrast (weights t) benchmark)⁺.trace.re ≤
      -(b t * c t / w t) * (1 - overlap ψ 0 1) - v * overlap ψ 0 2 -
        c t * d t / w t * overlap ψ 1 2 := by
  have hb : 0 ≤ b t := by dsimp [b, c, d, w]; linarith
  have hc : c t ≤ 0 := by dsimp [b, c, d, w]; linarith
  have hd : 0 ≤ d t := by dsimp [b, c, d, w]; linarith
  have hw : 0 < w t := by dsimp [b, c, d, w]; linarith
  have hY : overlap ψ 0 2 ≤ 1 := normSq_inner _ _ (hψ 0) (hψ 2)
  have hY₀ : 0 ≤ overlap ψ 0 2 := Complex.normSq_nonneg _
  have hX : 0 ≤ 1 - overlap ψ 0 1 := sub_nonneg.mpr (normSq_inner _ _ (hψ 0) (hψ 1))
  have hZ : 0 ≤ overlap ψ 1 2 := Complex.normSq_nonneg _
  have hbw : b t ≤ w t := by dsimp [b, w]; linarith
  have hvd : v ≤ d t := (le_div_iff₀ hw).2 hvw |>.trans
    ((div_le_iff₀ hw).2 (by simpa only [mul_comm] using mul_le_mul_of_nonneg_right hbw hd))
  have hXterm := mul_nonneg (neg_nonneg.mpr (div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos hb hc) hw.le)) hX
  have hZterm := mul_nonneg (neg_nonneg.mpr (div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg hc hd) hw.le)) hZ
  have hvY := mul_le_mul_of_nonneg_left hY hv
  apply clipped_le t ψ hψ hd (hv.trans hvp)
  · linarith only [hvp, hXterm, hZterm, hvY]
  · linarith only [hvd, hXterm, hZterm, hvY]
  · have hscale :
        w t * (-(b t * c t / w t) * (1 - overlap ψ 0 1) - v * overlap ψ 0 2 -
            c t * d t / w t * overlap ψ 1 2) =
          -(b t * c t) * (1 - overlap ψ 0 1) - (v * w t) * overlap ψ 0 2 -
            c t * d t * overlap ψ 1 2 := by
      field_simp [hw.ne']
      <;> ring
    rw [hscale]
    linarith only [mul_le_mul_of_nonneg_right hvw hY₀]

private theorem late_bound (t : ℝ) (ψ : Fin 3 → Fin 2 → ℂ)
    (hψ : ∀ i, star (ψ i) ⬝ᵥ ψ i = 1)
    (ht₀ : 5 / 3 ≤ t) (ht₁ : t ≤ 7 / 3) {u v : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (huw : u * w t ≤ b t * c t)
    (hvw : v * w t ≤ b t * d t) (huv : u + v ≤ d t) :
    (contrast (weights t) ψ)⁺.trace.re - (contrast (weights t) benchmark)⁺.trace.re ≤
      -u * (1 - overlap ψ 0 1) - v * overlap ψ 0 2 := by
  have hc : 0 ≤ c t := by dsimp [b, c, d, w]; linarith
  have hd : 0 ≤ d t := by dsimp [b, c, d, w]; linarith
  have hw : 0 < w t := by dsimp [b, c, d, w]; linarith
  have hpd : d t ≤ b t + c t := by dsimp [b, c, d, w]; linarith
  have hX : 0 ≤ 1 - overlap ψ 0 1 := sub_nonneg.mpr (normSq_inner _ _ (hψ 0) (hψ 1))
  have hY : 0 ≤ overlap ψ 0 2 := Complex.normSq_nonneg _
  have hZ : 0 ≤ overlap ψ 1 2 := Complex.normSq_nonneg _
  have hX₁ : 1 - overlap ψ 0 1 ≤ 1 := sub_le_self _ (Complex.normSq_nonneg _)
  have hY₁ : overlap ψ 0 2 ≤ 1 := normSq_inner _ _ (hψ 0) (hψ 2)
  have hclip := add_le_add (mul_le_mul_of_nonneg_left hX₁ hu)
    (mul_le_mul_of_nonneg_left hY₁ hv)
  apply clipped_le t ψ hψ hd (hd.trans hpd)
  · linarith only [hclip, huv, hpd]
  · linarith only [hclip, huv]
  · nlinarith only [mul_le_mul_of_nonneg_right huw hX, mul_le_mul_of_nonneg_right hvw hY,
      mul_nonneg (mul_nonneg hc hd) hZ]

private theorem middle_first_sign (t : ℝ) (hl : 113 / 81 ≤ t) (hr : t ≤ 22 / 15) :
    (97 / 100 * (b t + c t)) * w t ≤ b t * d t := by
  have h := mul_nonneg (sub_nonneg.mpr hl) (sub_nonneg.mpr hr)
  dsimp [b, c, d, w]
  nlinarith only [h, hl, hr]

private theorem middle_second_sign (t : ℝ) (hl : 22 / 15 ≤ t) :
    b t * d t ≤ (b t + c t) * w t := by
  dsimp [b, c, d, w]
  nlinarith only [sq_nonneg (t - 22 / 15), hl]

private theorem late_first_x_sign (t : ℝ) (hl : 5 / 3 ≤ t) (hr : t ≤ 2) :
    53 / 55 * (b t * c t) ≤ d t * w t := by
  have h : 0 ≤ 18 * (2 - t) * (99 * t - 125) :=
    mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hr)) (by linarith)
  dsimp [b, c, d, w]
  nlinarith only [h]

private theorem late_first_sum_sign (t : ℝ) (hl : 5 / 3 ≤ t) (hr : t ≤ 9 / 5) :
    53 / 55 * (b t * c t) + 24 / 25 * (b t * d t) ≤ d t * w t := by
  have h := mul_nonneg (sub_nonneg.mpr hl) (sub_nonneg.mpr hr)
  dsimp [b, c, d, w]
  nlinarith only [h, hl, hr]

private theorem late_second_y_sign (t : ℝ) (hl : 9 / 5 ≤ t) :
    d t * w t ≤ 53 / 55 * (b t * c t) + b t * d t := by
  dsimp [b, c, d, w]
  nlinarith only [sq_nonneg (t - 9 / 5), hl]

private theorem late_third_sign (t : ℝ) (hl : 2 ≤ t) :
    d t * w t ≤ b t * c t := by
  dsimp [b, c, d, w]
  nlinarith only [sq_nonneg (t - 2), hl]

/-- The six rational affine envelopes bound the actual excess positive-part trace
on their entire closed intervals, for every unit triple including dependent preparations. -/
theorem excess_profile_le_envelope (ψ : Fin 3 → Fin 2 → ℂ)
    (hψ : ∀ i, star (ψ i) ⬝ᵥ ψ i = 1) (i : Fin 6) (t : ℝ)
    (ht : t ∈ Set.Icc (timeCut i.castSucc) (timeCut i.succ)) :
    (contrast (weights t) ψ)⁺.trace.re - (contrast (weights t) benchmark)⁺.trace.re ≤
      envelope i t (1 - overlap ψ 0 1) (overlap ψ 0 2) (overlap ψ 1 2) := by
  obtain ⟨hl, hr⟩ := ht
  fin_cases i
  · exact early_bound t ψ hψ hl hr
  · change 113 / 81 ≤ t at hl
    change t ≤ 22 / 15 at hr
    have hp : 0 ≤ b t + c t := by dsimp [b, c, d, w]; linarith
    exact middle_bound t ψ hψ hl (by linarith)
      (mul_nonneg (by norm_num) hp) (middle_first_sign t hl hr) (by linarith)
  · change 22 / 15 ≤ t at hl
    change t ≤ 5 / 3 at hr
    have hb : 0 ≤ b t := by dsimp [b, c, d, w]; linarith
    have hd : 0 ≤ d t := by dsimp [b, c, d, w]; linarith
    have hw : 0 < w t := by dsimp [b, c, d, w]; linarith
    exact middle_bound t ψ hψ (by linarith) hr (div_nonneg (mul_nonneg hb hd) hw.le)
      (by rw [div_mul_cancel₀ _ hw.ne']) ((div_le_iff₀ hw).2 (middle_second_sign t hl))
  · change 5 / 3 ≤ t at hl
    change t ≤ 9 / 5 at hr
    have hb : 0 ≤ b t := by dsimp [b, c, d, w]; linarith
    have hc : 0 ≤ c t := by dsimp [b, c, d, w]; linarith
    have hd : 0 ≤ d t := by dsimp [b, c, d, w]; linarith
    have hw : 0 < w t := by dsimp [b, c, d, w]; linarith
    have hbc := div_nonneg (mul_nonneg hb hc) hw.le
    have hbd := div_nonneg (mul_nonneg hb hd) hw.le
    apply late_bound t ψ hψ hl (by linarith)
      (mul_nonneg (by norm_num) hbc) (mul_nonneg (by norm_num) hbd)
    · rw [mul_assoc, div_mul_cancel₀ _ hw.ne']
      linarith only [mul_nonneg (mul_nonneg hb hc) (by norm_num : (0 : ℝ) ≤ 1 - 53 / 55)]
    · rw [mul_assoc, div_mul_cancel₀ _ hw.ne']
      linarith only [mul_nonneg (mul_nonneg hb hd) (by norm_num : (0 : ℝ) ≤ 1 - 24 / 25)]
    · rw [← mul_div_assoc, ← mul_div_assoc, ← add_div]
      exact (div_le_iff₀ hw).2 (late_first_sum_sign t hl hr)
  · change 9 / 5 ≤ t at hl
    change t ≤ 2 at hr
    have hb : 0 ≤ b t := by dsimp [b, c, d, w]; linarith
    have hc : 0 ≤ c t := by dsimp [b, c, d, w]; linarith
    have hw : 0 < w t := by dsimp [b, c, d, w]; linarith
    have hu := mul_nonneg (by norm_num : (0 : ℝ) ≤ 53 / 55)
      (div_nonneg (mul_nonneg hb hc) hw.le)
    apply late_bound t ψ hψ (by linarith) (by linarith) hu
    · rw [sub_nonneg, ← mul_div_assoc]
      exact (div_le_iff₀ hw).2 (late_first_x_sign t (by linarith) hr)
    · rw [mul_assoc, div_mul_cancel₀ _ hw.ne']
      linarith only [mul_nonneg (mul_nonneg hb hc) (by norm_num : (0 : ℝ) ≤ 1 - 53 / 55)]
    · rw [sub_mul, mul_assoc, div_mul_cancel₀ _ hw.ne']
      linarith only [late_second_y_sign t hl]
    · linarith only []
  · change 2 ≤ t at hl
    change t ≤ 7 / 3 at hr
    have hb : 0 ≤ b t := by dsimp [b, c, d, w]; linarith
    have hd : 0 ≤ d t := by dsimp [b, c, d, w]; linarith
    change _ ≤ -d t * (1 - overlap ψ 0 1)
    simpa only [neg_zero, zero_mul, sub_zero] using
      late_bound t ψ hψ (by linarith) hr hd (le_refl 0) (late_third_sign t hl)
        (by simpa only [zero_mul] using mul_nonneg hb hd) (by rw [add_zero])

#print axioms excess_profile_le_envelope

end D5.S3.Quantum.Divergence.Qubit.FibonacciClippedProfile
