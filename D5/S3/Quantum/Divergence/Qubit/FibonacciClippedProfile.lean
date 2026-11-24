/- GID: D5/S3/Quantum/Divergence/Qubit/FibonacciClippedProfile
   generality: I
   mirror-B: D5/B/S3/Quantum/Divergence/Qubit/FibonacciClippedProfile
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The clipped Fibonacci qubit profile bound and quantitative trace-log margin. -/

import D5.S3.Quantum.Divergence.Qubit.SignedProfile
import D5.S3.Quantum.Divergence.ForwardHockeyStickIntegral
import D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity
import D5.S3.Quantum.Information.FullwoodParzygnatSubadditivityRefutation
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

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

section Integral

open MeasureTheory Set
open scoped Matrix.Norms.L2Operator
open D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity (cfc_log_diagonal)

private theorem cut_mono (i : Fin 6) : timeCut i.castSucc ≤ timeCut i.succ := by
  fin_cases i <;> norm_num [timeCut, Fin.castSucc, Fin.succ]

private theorem cut_lower (i : Fin 6) : (4 / 3 : ℝ) ≤ timeCut i.castSucc := by
  fin_cases i <;> norm_num [timeCut, Fin.castSucc]

private theorem envelope_integrable (i : Fin 6) (X Y Z : ℝ) :
    IntervalIntegrable (fun t => envelope i t X Y Z / t) volume
      (timeCut i.castSucc) (timeCut i.succ) := by
  let K := Icc (timeCut i.castSucc) (timeCut i.succ)
  have ht (t : ℝ) (h : t ∈ K) : t ≠ 0 := by linarith [h.1, cut_lower i]
  have hw (t : ℝ) (h : t ∈ K) : w t ≠ 0 := by dsimp [w]; linarith [h.1, cut_lower i]
  apply ContinuousOn.intervalIntegrable_of_Icc (cut_mono i)
  apply ContinuousOn.div _ continuous_id.continuousOn ht
  fin_cases i
  all_goals
    simp only [envelope, Matrix.cons_val_zero', Matrix.cons_val_succ',
      b, c, d, w]
  · have hd (t : ℝ) (h : t ∈ K) : 28 - 12 * t ≠ 0 := by
      have hr : t ≤ (113 / 81 : ℝ) := h.2
      linarith
    fun_prop (disch := first | apply hd | assumption)
  all_goals
    fun_prop (disch := first | apply hw | assumption)

private theorem continuous_trace (ψ : Fin 3 → Fin 2 → ℂ)
    (hψ : ∀ i, star (ψ i) ⬝ᵥ ψ i = 1) :
    Continuous (fun t => (contrast (weights t) ψ)⁺.trace.re) := by
  simp_rw [trace_posPart_contrast _ _ hψ, sum_weights, gap_formula]
  dsimp [b, c, d, w]
  fun_prop

/-- Integrating the actual excess trace divided by the time parameter is bounded by
the sum of the six affine interval integrals. The preparations may be dependent. -/
private theorem integral_excess_profile_le (ψ : Fin 3 → Fin 2 → ℂ)
    (hψ : ∀ i, star (ψ i) ⬝ᵥ ψ i = 1) :
    (∫ t in (4 / 3 : ℝ)..(7 / 3),
      ((contrast (weights t) ψ)⁺.trace.re - (contrast (weights t) benchmark)⁺.trace.re) / t) ≤
      ∑ i : Fin 6, ∫ t in timeCut i.castSucc..timeCut i.succ,
        envelope i t (1 - overlap ψ 0 1) (overlap ψ 0 2) (overlap ψ 1 2) / t := by
  let f (t : ℝ) := ((contrast (weights t) ψ)⁺.trace.re -
    (contrast (weights t) benchmark)⁺.trace.re) / t
  have hf (i : Fin 6) :
      IntervalIntegrable f volume (timeCut i.castSucc) (timeCut i.succ) := by
    apply ContinuousOn.intervalIntegrable_of_Icc (cut_mono i)
    apply ContinuousOn.div
      ((continuous_trace ψ hψ).sub (continuous_trace benchmark benchmark_unit)).continuousOn
      continuous_id.continuousOn
    intro t ht
    change t ≠ 0
    linarith [ht.1, cut_lower i]
  have hle (i : Fin 6) : (∫ t in timeCut i.castSucc..timeCut i.succ, f t) ≤
      ∫ t in timeCut i.castSucc..timeCut i.succ,
        envelope i t (1 - overlap ψ 0 1) (overlap ψ 0 2) (overlap ψ 1 2) / t := by
    refine intervalIntegral.integral_mono_on (cut_mono i) (hf i) (envelope_integrable i _ _ _) ?_
    intro t ht
    exact div_le_div_of_nonneg_right (excess_profile_le_envelope ψ hψ i t ht)
      (by linarith [ht.1, cut_lower i])
  have hsplit : (∑ i : Fin 6, ∫ t in timeCut i.castSucc..timeCut i.succ, f t) =
      ∫ t in (4 / 3 : ℝ)..(7 / 3), f t := by
    let a (i : ℕ) := if h : i < 7 then timeCut ⟨i, h⟩ else 0
    change _ = ∫ t in a 0..a 6, f t
    rw [← intervalIntegral.sum_integral_adjacent_intervals (a := a) (n := 6) (f := f)
      (fun k h => by
        have hk := hf (⟨k, h⟩ : Fin 6)
        simpa [a, Nat.lt_trans h (by decide : 6 < 7), Nat.succ_lt_succ h] using hk)]
    rw [← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun i _ => by
      simp only [a, dif_pos (Nat.lt_trans i.isLt (by decide : 6 < 7)),
        dif_pos (Nat.succ_lt_succ i.isLt)]
      rfl
  change (∫ t in (4 / 3 : ℝ)..(7 / 3), f t) ≤ _
  rw [← hsplit]
  exact Finset.sum_le_sum (fun i _ => hle i)

#print axioms integral_excess_profile_le

private def primitive (A B C m n t : ℝ) : ℝ :=
  A * t + B * Real.log t + C * Real.log (m * t + n)

private theorem hasDerivAt_primitive (A B C m n t : ℝ) (ht : t ≠ 0)
    (hmt : m * t + n ≠ 0) :
    HasDerivAt (primitive A B C m n)
      (A + B / t + C * m / (m * t + n)) t := by
  have hlin : HasDerivAt (fun u : ℝ => m * u + n) m t := by
    simpa using (((hasDerivAt_id t).const_mul m).add_const n)
  have hlog := (Real.hasDerivAt_log hmt).comp t hlin
  convert (((hasDerivAt_id t).const_mul A).add
    ((Real.hasDerivAt_log ht).const_mul B)).add (hlog.const_mul C) using 1
  · rfl
  · simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]

private abbrev k : ℝ := 53 / 55
private abbrev ell : ℝ := 24 / 25
private abbrev h : ℝ := 97 / 100

-- The first piece uses log (7 - 3t). Each other piece uses log (69t - 85).
private def linear (i : Fin 6) (X Y Z : ℝ) : ℝ :=
  ![-363 * X + 66 * Z,
    -(330 / 23) * X - h * 81 * Y + (60 / 23) * Z,
    -(330 / 23) * X + (264 / 23) * Y + (60 / 23) * Z,
    -k * (330 / 23) * X + ell * (264 / 23) * Y,
    -k * (330 / 23) * X + (12 + k * (330 / 23)) * Y,
    12 * X] i

private def logarithmic (i : Fin 6) (X Y Z : ℝ) : ℝ :=
  ![(1936 / 7) * X - 88 * Z,
    (440 / 17) * X + h * 113 * Y - (140 / 17) * Z,
    (440 / 17) * X - (2464 / 85) * Y - (140 / 17) * Z,
    k * (440 / 17) * X - ell * (2464 / 85) * Y,
    k * (440 / 17) * X - (28 + k * (440 / 17)) * Y,
    -28 * X] i

private def affineLogarithmic (i : Fin 6) (X Y Z : ℝ) : ℝ :=
  ![-(1089 / 7) * X,
    -(4620 / 8993) * X + (9120 / 8993) * Z,
    -(4620 / 8993) * X + (46816 / 44965) * Y + (9120 / 8993) * Z,
    -k * (4620 / 8993) * X + ell * (46816 / 44965) * Y,
    -k * (4620 / 8993) * X + k * (4620 / 8993) * Y,
    0] i

private abbrev slope (i : Fin 6) : ℝ := if i = 0 then -3 else 69
private abbrev intercept (i : Fin 6) : ℝ := if i = 0 then 7 else -85

private theorem affine_pos (i : Fin 6) {t : ℝ}
    (ht : t ∈ Icc (timeCut i.castSucc) (timeCut i.succ)) :
    0 < slope i * t + intercept i := by
  have hlo : (4 / 3 : ℝ) ≤ t := (cut_lower i).trans ht.1
  by_cases hi : i = 0
  · subst i
    have hup : t ≤ (113 / 81 : ℝ) := ht.2
    norm_num [slope, intercept]
    linarith
  · simp only [slope, intercept, if_neg hi]
    linarith

private theorem integral_envelope (i : Fin 6) (X Y Z : ℝ) :
    (∫ t in timeCut i.castSucc..timeCut i.succ, envelope i t X Y Z / t) =
      linear i X Y Z * (timeCut i.succ - timeCut i.castSucc) +
        logarithmic i X Y Z * Real.log (timeCut i.succ / timeCut i.castSucc) +
        affineLogarithmic i X Y Z * Real.log
          ((slope i * timeCut i.succ + intercept i) /
            (slope i * timeCut i.castSucc + intercept i)) := by
  let A := linear i X Y Z
  let B := logarithmic i X Y Z
  let C := affineLogarithmic i X Y Z
  let p := timeCut i.castSucc
  let q := timeCut i.succ
  have hpq : p ≤ q := cut_mono i
  have hp : 0 < p := (by norm_num : (0 : ℝ) < 4 / 3).trans_le (cut_lower i)
  have haₚ := affine_pos i (t := p) ⟨le_rfl, hpq⟩
  have ha_q := affine_pos i (t := q) ⟨hpq, le_rfl⟩
  have hderiv (t : ℝ) (ht : t ∈ uIcc p q) :
      HasDerivAt (primitive A B C (slope i) (intercept i)) (envelope i t X Y Z / t) t := by
    rw [uIcc_of_le hpq] at ht
    have ht₀ : t ≠ 0 := (hp.trans_le ht.1).ne'
    have ha := (affine_pos i ht).ne'
    convert hasDerivAt_primitive A B C (slope i) (intercept i) t ht₀ ha using 1
    have hw : 69 * t - 85 ≠ 0 := by linarith [cut_lower i, ht.1]
    fin_cases i
    all_goals
      dsimp [A, B, C]
      simp only [linear, logarithmic, affineLogarithmic, envelope, Matrix.cons_val_zero',
        Matrix.cons_val_succ', b, c, d, w]
      norm_num [slope, intercept] at ha ⊢
    · have hd : 28 - 12 * t ≠ 0 := by
        have hright : t ≤ (113 / 81 : ℝ) := ht.2
        linarith
      have hd' : 28 - t * 12 ≠ 0 := by convert hd using 1 <;> ring
      have hr' : 7 - t * 3 ≠ 0 := by convert ha using 1 <;> ring
      field_simp [ht₀, hd, ha]
      <;> ring_nf
      <;> field_simp [hd', hr']
      <;> ring
    all_goals
      have hw' : -85 + t * 69 ≠ 0 := by convert hw using 1 <;> ring
      simp only [← sub_eq_add_neg] at *
      field_simp [ht₀, hw]
      <;> ring_nf
      <;> field_simp [hw']
      <;> ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (envelope_integrable i X Y Z)
  rw [hFTC]
  change primitive A B C (slope i) (intercept i) q -
    primitive A B C (slope i) (intercept i) p = _
  change _ = A * (q - p) + B * Real.log (q / p) +
    C * Real.log ((slope i * q + intercept i) / (slope i * p + intercept i))
  rw [Real.log_div (hp.trans_le hpq).ne' hp.ne', Real.log_div ha_q.ne' haₚ.ne']
  unfold primitive
  ring

private def logSumFive (q : ℝ) : ℝ :=
  let z := (q - 1) / (q + 1)
  2 * ∑ i ∈ Finset.range 5, z ^ (2 * i + 1) / (2 * i + 1)

private def logRemainderFive (q : ℝ) : ℝ :=
  let z := (q - 1) / (q + 1)
  2 * z ^ 11 / (1 - z ^ 2)

private theorem log_bounds {q : ℝ} (hq : 1 ≤ q) :
    logSumFive q ≤ Real.log q ∧ Real.log q ≤ logSumFive q + logRemainderFive q := by
  let z := (q - 1) / (q + 1)
  have hq₁ : 0 < q + 1 := by linarith
  have hz : 0 ≤ z := div_nonneg (sub_nonneg.mpr hq) hq₁.le
  have hz₁ : z < 1 := (div_lt_iff₀ hq₁).2 (by linarith)
  have heq : (1 + z) / (1 - z) = q := by
    apply (div_eq_iff (by linarith : 1 - z ≠ 0)).2
    dsimp only [z]
    field_simp [hq₁.ne']
    <;> ring
  obtain hl := Real.sum_range_le_log_div hz hz₁ 5
  obtain hu := Real.log_div_le_sum_range_add hz hz₁ 5
  rw [heq] at hl hu
  change 2 * (∑ i ∈ Finset.range 5, z ^ (2 * i + 1) / (2 * i + 1)) ≤ Real.log q ∧
    Real.log q ≤ 2 * (∑ i ∈ Finset.range 5, z ^ (2 * i + 1) / (2 * i + 1)) +
      2 * z ^ 11 / (1 - z ^ 2)
  rw [mul_div_assoc]
  exact ⟨by linarith only [hl], by linarith only [hu]⟩

private def integratedEnvelope (X Y Z : ℝ) : ℝ :=
  ∑ i : Fin 6, (linear i X Y Z * (timeCut i.succ - timeCut i.castSucc) +
    logarithmic i X Y Z * Real.log (timeCut i.succ / timeCut i.castSucc) +
    affineLogarithmic i X Y Z * Real.log
      ((slope i * timeCut i.succ + intercept i) / (slope i * timeCut i.castSucc + intercept i)))

private theorem integrated_envelope_linear (X Y Z : ℝ) :
    integratedEnvelope X Y Z =
      integratedEnvelope 1 0 0 * X + integratedEnvelope 0 1 0 * Y +
        integratedEnvelope 0 0 1 * Z := by
  simp [integratedEnvelope, Fin.sum_univ_succ, linear, logarithmic, affineLogarithmic]
  ring

private theorem integrated_envelope_axes :
    integratedEnvelope 1 0 0 ≤ -(141 / 330) ∧
      integratedEnvelope 0 1 0 ≤ -(141 / 90) ∧
      integratedEnvelope 0 0 1 ≤ 141 * (3 / 1280) := by
  have H0 := log_bounds (q := (113 / 108)) (by norm_num)
  have L0 : (452565915 / 10000000000 : ℝ) ≤ Real.log (113 / 108) :=
    le_trans (by norm_num [logSumFive, Finset.sum_range_succ]) H0.1
  have U0 : Real.log (113 / 108) ≤ (452565916 / 10000000000 : ℝ) :=
    le_trans H0.2 (by norm_num [logSumFive, logRemainderFive, Finset.sum_range_succ])
  have H1 := log_bounds (q := (594 / 565)) (by norm_num)
  have L1 : (500535882 / 10000000000 : ℝ) ≤ Real.log (594 / 565) :=
    le_trans (by norm_num [logSumFive, Finset.sum_range_succ]) H1.1
  have U1 : Real.log (594 / 565) ≤ (500535883 / 10000000000 : ℝ) :=
    le_trans H1.2 (by norm_num [logSumFive, logRemainderFive, Finset.sum_range_succ])
  have H2 := log_bounds (q := (25 / 22)) (by norm_num)
  have L2 : (1278333715 / 10000000000 : ℝ) ≤ Real.log (25 / 22) :=
    le_trans (by norm_num [logSumFive, Finset.sum_range_succ]) H2.1
  have U2 : Real.log (25 / 22) ≤ (1278333716 / 10000000000 : ℝ) :=
    le_trans H2.2 (by norm_num [logSumFive, logRemainderFive, Finset.sum_range_succ])
  have H3 := log_bounds (q := (27 / 25)) (by norm_num)
  have L3 : (769610411 / 10000000000 : ℝ) ≤ Real.log (27 / 25) :=
    le_trans (by norm_num [logSumFive, Finset.sum_range_succ]) H3.1
  have U3 : Real.log (27 / 25) ≤ (769610412 / 10000000000 : ℝ) :=
    le_trans H3.2 (by norm_num [logSumFive, logRemainderFive, Finset.sum_range_succ])
  have H4 := log_bounds (q := (10 / 9)) (by norm_num)
  have L4 : (1053605156 / 10000000000 : ℝ) ≤ Real.log (10 / 9) :=
    le_trans (by norm_num [logSumFive, Finset.sum_range_succ]) H4.1
  have U4 : Real.log (10 / 9) ≤ (1053605157 / 10000000000 : ℝ) :=
    le_trans H4.2 (by norm_num [logSumFive, logRemainderFive, Finset.sum_range_succ])
  have H5 := log_bounds (q := (7 / 6)) (by norm_num)
  have L5 : (1541506798 / 10000000000 : ℝ) ≤ Real.log (7 / 6) :=
    le_trans (by norm_num [logSumFive, Finset.sum_range_succ]) H5.1
  have U5 : Real.log (7 / 6) ≤ (1541506799 / 10000000000 : ℝ) :=
    le_trans H5.2 (by norm_num [logSumFive, logRemainderFive, Finset.sum_range_succ])
  have H6 := log_bounds (q := (2187 / 1520)) (by norm_num)
  have L6 : (3638204056 / 10000000000 : ℝ) ≤ Real.log (2187 / 1520) :=
    le_trans (by norm_num [logSumFive, Finset.sum_range_succ]) H6.1
  have U6 : Real.log (2187 / 1520) ≤ (3638204189 / 10000000000 : ℝ) :=
    le_trans H6.2 (by norm_num [logSumFive, logRemainderFive, Finset.sum_range_succ])
  have H7 := log_bounds (q := (50 / 27)) (by norm_num)
  have L7 : (6161858072 / 10000000000 : ℝ) ≤ Real.log (50 / 27) :=
    le_trans (by norm_num [logSumFive, Finset.sum_range_succ]) H7.1
  have U7 : Real.log (50 / 27) ≤ (6161895160 / 10000000000 : ℝ) :=
    le_trans H7.2 (by norm_num [logSumFive, logRemainderFive, Finset.sum_range_succ])
  have H8 := log_bounds (q := (98 / 75)) (by norm_num)
  have L8 : (2674793650 / 10000000000 : ℝ) ≤ Real.log (98 / 75) :=
    le_trans (by norm_num [logSumFive, Finset.sum_range_succ]) H8.1
  have U8 : Real.log (98 / 75) ≤ (2674793656 / 10000000000 : ℝ) :=
    le_trans H8.2 (by norm_num [logSumFive, logRemainderFive, Finset.sum_range_succ])
  have H9 := log_bounds (q := (265 / 196)) (by norm_num)
  have L9 : (3016151665 / 10000000000 : ℝ) ≤ Real.log (265 / 196) :=
    le_trans (by norm_num [logSumFive, Finset.sum_range_succ]) H9.1
  have U9 : Real.log (265 / 196) ≤ (3016151684 / 10000000000 : ℝ) :=
    le_trans H9.2 (by norm_num [logSumFive, logRemainderFive, Finset.sum_range_succ])
  have H10 := log_bounds (q := (81 / 76)) (by norm_num)
  have L10 : (637158143 / 10000000000 : ℝ) ≤ Real.log (81 / 76) :=
    le_trans (by norm_num [logSumFive, Finset.sum_range_succ]) H10.1
  have U10 : Real.log (81 / 76) ≤ (637158144 / 10000000000 : ℝ) :=
    le_trans H10.2 (by norm_num [logSumFive, logRemainderFive, Finset.sum_range_succ])
  have hinv : Real.log (76 / 81) = -Real.log (81 / 76) := by
    rw [show (76 / 81 : ℝ) = (81 / 76 : ℝ)⁻¹ by norm_num, Real.log_inv]
  constructor
  · norm_num [integratedEnvelope, Fin.sum_univ_succ, timeCut, linear, logarithmic,
      affineLogarithmic, slope, intercept, Fin.castSucc, Fin.succ, h, k, ell, hinv]
    <;> linarith only [U0, U1, U2, U3, U4, L5, L6, L7, L8, L9, U10]
  constructor
  · norm_num [integratedEnvelope, Fin.sum_univ_succ, timeCut, linear, logarithmic,
      affineLogarithmic, slope, intercept, Fin.castSucc, Fin.succ, h, k, ell]
    linarith only [U1, L2, L3, L4, U7, U8, U9]
  · norm_num [integratedEnvelope, Fin.sum_univ_succ, timeCut, linear, logarithmic,
      affineLogarithmic, slope, intercept, Fin.castSucc, Fin.succ, h, k, ell]
    linarith only [L0, L1, L2, U6, U7]

open scoped InnerProductSpace in
private theorem overlap_tradeoff (ψ : Fin 3 → Fin 2 → ℂ)
    (hψ : ∀ i, star (ψ i) ⬝ᵥ ψ i = 1) :
    overlap ψ 1 2 ≤ 420 * ((1 - overlap ψ 0 1) / 330 + overlap ψ 0 2 / 90) := by
  let vec (i : Fin 3) : EuclideanSpace ℂ (Fin 2) := WithLp.toLp 2 (ψ i)
  have hinner (i j : Fin 3) : ⟪vec i, vec j⟫_ℂ = star (ψ i) ⬝ᵥ ψ j := by
    simp [vec, PiLp.inner_apply, dotProduct, mul_comm]
  have hunit (i : Fin 3) : ⟪vec i, vec i⟫_ℂ = 1 := (hinner i i).trans (hψ i)
  have hnorm (i : Fin 3) : ‖vec i‖ = 1 := by
    have h := norm_sq_eq_re_inner (𝕜 := ℂ) (vec i)
    rw [hunit] at h
    exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp (by simpa using h)
  have hov (i j : Fin 3) : overlap ψ i j = ‖⟪vec i, vec j⟫_ℂ‖ ^ 2 := by
    rw [hinner, overlap, Complex.normSq_eq_norm_sq]
  let a := ⟪vec 0, vec 1⟫_ℂ
  let r := vec 1 - a • vec 0
  have he : a • vec 0 + r = vec 1 := by dsimp only [r]; abel
  have hr : ⟪vec 0, r⟫_ℂ = 0 := by
    rw [show r = vec 1 - a • vec 0 by rfl, inner_sub_right, inner_smul_right, hunit, mul_one]
    exact sub_self _
  have hp : ⟪a • vec 0, r⟫_ℂ = 0 := by rw [inner_smul_left, hr, mul_zero]
  have hs := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hp
  rw [he, hnorm, norm_smul, hnorm, mul_one] at hs
  have hav : ‖a‖ ^ 2 = overlap ψ 0 1 := (hov 0 1).symm
  have hres : ‖r‖ ^ 2 = 1 - overlap ψ 0 1 := by nlinarith only [hs, hav]
  have hleft : ‖a‖ ≤ 1 := by
    simpa only [hnorm, one_mul] using norm_inner_le_norm (𝕜 := ℂ) (vec 0) (vec 1)
  have hright : ‖⟪r, vec 2⟫_ℂ‖ ≤ ‖r‖ := by
    simpa only [hnorm, mul_one] using norm_inner_le_norm (𝕜 := ℂ) r (vec 2)
  let B := ‖⟪vec 0, vec 2⟫_ℂ‖
  have htri : ‖⟪vec 1, vec 2⟫_ℂ‖ ≤ ‖r‖ + B := by
    rw [← he, inner_add_left, inner_smul_left]
    have h := norm_add_le (star a * ⟪vec 0, vec 2⟫_ℂ) ⟪r, vec 2⟫_ℂ
    rw [norm_mul, norm_star] at h
    exact h.trans (by
      have hab := mul_le_mul_of_nonneg_right hleft (norm_nonneg ⟪vec 0, vec 2⟫_ℂ)
      change _ ≤ ‖r‖ + ‖⟪vec 0, vec 2⟫_ℂ‖
      linarith only [hab, hright])
  have hsq := (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr htri
  rw [← hov 1 2] at hsq
  have hB : B ^ 2 = overlap ψ 0 2 := (hov 0 2).symm
  nlinarith only [hsq, hres, hB, sq_nonneg (3 * ‖r‖ - 11 * B)]

/-- The integrated excess profile satisfies the quantitative pure-qubit margin. -/
private theorem integral_excess_profile_le_margin (ψ : Fin 3 → Fin 2 → ℂ)
    (hψ : ∀ i, star (ψ i) ⬝ᵥ ψ i = 1) :
    (∫ t in (4 / 3 : ℝ)..(7 / 3),
      ((contrast (weights t) ψ)⁺.trace.re - (contrast (weights t) benchmark)⁺.trace.re) / t) ≤
      -(141 / 63360) * (3 * (1 - overlap ψ 0 1) + 11 * overlap ψ 0 2) := by
  let X := 1 - overlap ψ 0 1
  let Y := overlap ψ 0 2
  let Z := overlap ψ 1 2
  have hX : 0 ≤ X := sub_nonneg.mpr (normSq_inner _ _ (hψ 0) (hψ 1))
  have hY : 0 ≤ Y := Complex.normSq_nonneg _
  have hZ : 0 ≤ Z := Complex.normSq_nonneg _
  have hsum := integral_excess_profile_le ψ hψ
  simp_rw [integral_envelope] at hsum
  change _ ≤ integratedEnvelope X Y Z at hsum
  have hα := mul_le_mul_of_nonneg_right integrated_envelope_axes.1 hX
  have hβ := mul_le_mul_of_nonneg_right integrated_envelope_axes.2.1 hY
  have hγ := mul_le_mul_of_nonneg_right integrated_envelope_axes.2.2 hZ
  have hXY : Z ≤ 420 * (X / 330 + Y / 90) := overlap_tradeoff ψ hψ
  rw [integrated_envelope_linear] at hsum
  change _ ≤ -(141 / 63360) * (3 * X + 11 * Y)
  linarith only [hsum, hα, hβ, hγ, hXY]

#print axioms integral_excess_profile_le_margin

private abbrev inputWeights : Fin 3 → ℝ := ![88 / 141, 25 / 141, 28 / 141]
private abbrev referenceWeights : Fin 3 → ℝ := ![66 / 141, 15 / 141, 12 / 141]
private abbrev input (ψ : Fin 3 → Fin 2 → ℂ) := contrast inputWeights ψ
private abbrev reference (ψ : Fin 3 → Fin 2 → ℂ) := contrast referenceWeights ψ

private abbrev traceLog (A C : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  (A * (CFC.log A - CFC.log C)).trace.re

private abbrev C3 : ℝ := (113 / 141) * Real.log (113 / 81) + (28 / 141) * Real.log (7 / 3)

private theorem contrast_nonneg (a : Fin 3 → ℝ) (ψ : Fin 3 → Fin 2 → ℂ)
    (ha : ∀ i, 0 ≤ a i) : 0 ≤ contrast a ψ := by
  unfold contrast
  exact Finset.sum_nonneg fun i _ =>
    smul_nonneg (ha i) (Matrix.posSemidef_vecMulVec_self_star (ψ i)).nonneg

private theorem normalized_pencil (ψ : Fin 3 → Fin 2 → ℂ) (t : ℝ) :
    input ψ - t • reference ψ = (141 : ℝ)⁻¹ • contrast (weights t) ψ := by
  simp only [contrast, Fin.sum_univ_three, weights, Matrix.cons_val, b, c, d]
  module

private theorem ratio_bounds (ψ : Fin 3 → Fin 2 → ℂ) :
    (4 / 3 : ℝ) • reference ψ ≤ input ψ ∧ input ψ ≤ (7 / 3 : ℝ) • reference ψ := by
  constructor
  · apply sub_nonneg.mp
    rw [normalized_pencil]
    apply smul_nonneg (by norm_num) (contrast_nonneg _ _ ?_)
    intro i
    fin_cases i <;> norm_num [weights, b, c, d]
  · apply sub_nonpos.mp
    rw [normalized_pencil]
    apply smul_nonpos_of_nonneg_of_nonpos (by norm_num)
    apply neg_nonneg.mp
    have he : -contrast (weights (7 / 3)) ψ = contrast (fun i => -weights (7 / 3) i) ψ := by
      simp [contrast, Finset.sum_neg_distrib, neg_smul]
    rw [he]
    apply contrast_nonneg
    intro i
    fin_cases i <;> norm_num [weights, b, c, d]

private theorem forward_eq_scaled (ψ : Fin 3 → Fin 2 → ℂ) (t : ℝ)
    (hA : (input ψ).IsHermitian) (hC : (reference ψ).IsHermitian) :
    ForwardHockeyStickIntegral.forwardProfile hA hC t =
      (contrast (weights t) ψ)⁺.trace.re / 141 := by
  unfold ForwardHockeyStickIntegral.forwardProfile
  have hh := hA.sub (hC.smul (IsSelfAdjoint.all t))
  have hp : RHLinalg.hermPosPart hh = (input ψ - t • reference ψ)⁺ := by
    rw [CFC.posPart_def, cfcₙ_eq_cfc (hf0 := by simp), hh.cfc_eq]
    rfl
  rw [hp, normalized_pencil, CFC.posPart_smul_of_nonneg (by norm_num), RHLinalg.rtrace,
    Matrix.trace_smul]
  change ((141 : ℝ)⁻¹ • (contrast (weights t) ψ)⁺.trace).re = _
  rw [Complex.smul_re]
  simp only [smul_eq_mul, div_eq_mul_inv, mul_comm]

private theorem benchmark_diagonal :
    input benchmark = diagonal ![(113 / 141 : ℂ), 28 / 141] ∧
      reference benchmark = diagonal ![(81 / 141 : ℂ), 12 / 141] := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp only [input, reference, inputWeights, referenceWeights, contrast, Fin.sum_univ_three,
      Matrix.add_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply] <;>
    norm_num [benchmark, Matrix.diagonal_apply, Complex.real_smul, Complex.ofReal_div]

private theorem benchmark_entropy : traceLog (input benchmark) (reference benchmark) = C3 := by
  rw [benchmark_diagonal.1, benchmark_diagonal.2]
  rw [show (![(113 / 141 : ℂ), 28 / 141] : Fin 2 → ℂ) =
    fun i => ((![(113 / 141 : ℝ), 28 / 141] : Fin 2 → ℝ) i : ℂ) by ext i; fin_cases i <;> norm_num,
    show (![(81 / 141 : ℂ), 12 / 141] : Fin 2 → ℂ) =
    fun i => ((![(81 / 141 : ℝ), 12 / 141] : Fin 2 → ℝ) i : ℂ) by ext i; fin_cases i <;> norm_num]
  unfold traceLog
  rw [cfc_log_diagonal, cfc_log_diagonal, diagonal_sub, diagonal_mul_diagonal, trace_diagonal]
  simp only [Pi.sub_apply, Pi.mul_apply, ← Complex.ofReal_sub, ← Complex.ofReal_mul,
    ← Complex.ofReal_sum, Complex.ofReal_re, Fin.sum_univ_two]
  norm_num
  rw [← Real.log_div (by norm_num : (113 / 141 : ℝ) ≠ 0) (by norm_num),
    ← Real.log_div (by norm_num : (28 / 141 : ℝ) ≠ 0) (by norm_num)]
  norm_num [C3]

private theorem faithful_entropy_sub (ψ : Fin 3 → Fin 2 → ℂ)
    (hψ : ∀ i, star (ψ i) ⬝ᵥ ψ i = 1) (hC : (reference ψ).PosDef) :
    traceLog (input ψ) (reference ψ) - C3 =
      (∫ t in (4 / 3 : ℝ)..(7 / 3),
        ((contrast (weights t) ψ)⁺.trace.re - (contrast (weights t) benchmark)⁺.trace.re) / t) / 141 := by
  have hA (χ : Fin 3 → Fin 2 → ℂ) : (input χ).PosSemidef := by
    apply Matrix.nonneg_iff_posSemidef.mp
    apply contrast_nonneg
    intro i
    fin_cases i <;> norm_num [inputWeights]
  have hCb : (reference benchmark).PosDef := by
    rw [benchmark_diagonal.2]
    apply Matrix.posDef_diagonal_iff.mpr
    intro i
    fin_cases i <;> norm_num
  have mass (a : Fin 3 → ℝ) :
      RHLinalg.rtrace (contrast a ψ) = RHLinalg.rtrace (contrast a benchmark) := by
    apply congrArg Complex.re
    simp only [contrast, Matrix.trace_sum, Matrix.trace_smul, Matrix.trace_vecMulVec]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [dotProduct_comm (ψ i), hψ, dotProduct_comm (benchmark i), benchmark_unit]
  have he := (ForwardHockeyStickIntegral.integral_forwardProfile_sub_eq_umegaki_sub
    (hA ψ) hC (hA benchmark) hCb (mass inputWeights) (mass referenceWeights)
    (by norm_num : (0 : ℝ) < 4 / 3) (by norm_num : (4 / 3 : ℝ) ≤ 7 / 3)
    (ratio_bounds ψ).1 (ratio_bounds ψ).2
    (ratio_bounds benchmark).1 (ratio_bounds benchmark).2).2.2.2
  change traceLog (input ψ) (reference ψ) - traceLog (input benchmark) (reference benchmark) = _ at he
  rw [benchmark_entropy] at he
  simp_rw [forward_eq_scaled] at he
  rw [he, ← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro t _
  ring

open scoped InnerProductSpace in
private theorem projection_eq_of_overlap_one (ψ : Fin 3 → Fin 2 → ℂ)
    (hψ : ∀ i, star (ψ i) ⬝ᵥ ψ i = 1) (i : Fin 3) (h : overlap ψ 0 i = 1) :
    vecMulVec (ψ i) (star (ψ i)) = vecMulVec (ψ 0) (star (ψ 0)) := by
  let v (j : Fin 3) : EuclideanSpace ℂ (Fin 2) := WithLp.toLp 2 (ψ j)
  have hin (j l : Fin 3) : ⟪v j, v l⟫_ℂ = star (ψ j) ⬝ᵥ ψ l := by
    simp [v, PiLp.inner_apply, dotProduct, mul_comm]
  have hn (j : Fin 3) : ‖v j‖ = 1 := by
    have hsq := norm_sq_eq_re_inner (𝕜 := ℂ) (v j)
    rw [hin, hψ] at hsq
    exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp (by simpa using hsq)
  have hv (j : Fin 3) : v j ≠ 0 := by
    intro hz
    have := hn j
    norm_num [hz] at this
  have hh : ‖⟪v 0, v i⟫_ℂ‖ = ‖v 0‖ * ‖v i‖ := by
    rw [hn, hn, one_mul]
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    simpa only [hin, ← Complex.normSq_eq_norm_sq, overlap, one_pow] using h
  obtain ⟨a, _, ha⟩ := (norm_inner_eq_norm_iff (hv 0) (hv i)).1 hh
  have hnorm : ‖a‖ = 1 := by
    have hs := hn i
    rwa [ha, norm_smul, hn, mul_one] at hs
  have hstar : a * star a = 1 := by
    change a * (starRingEnd ℂ) a = 1
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm, one_pow, Complex.ofReal_one]
  have hvec (j : Fin 2) : ψ i j = a * ψ 0 j :=
    congrArg (fun z : EuclideanSpace ℂ (Fin 2) => z j) ha
  ext j l
  simp only [Matrix.vecMulVec_apply, Pi.star_apply, hvec, star_mul]
  calc
    _ = (a * star a) * (ψ 0 j * star (ψ 0 l)) := by ring
    _ = _ := by rw [hstar, one_mul]

private theorem singular_overlaps (ψ : Fin 3 → Fin 2 → ℂ)
    (hψ : ∀ i, star (ψ i) ⬝ᵥ ψ i = 1) (hC : ¬ (reference ψ).PosDef) :
    overlap ψ 0 1 = 1 ∧ overlap ψ 0 2 = 1 := by
  have hCps : (reference ψ).PosSemidef := Matrix.nonneg_iff_posSemidef.mp <|
    contrast_nonneg _ _ (fun i => by fin_cases i <;> norm_num [referenceWeights])
  have hdet : (reference ψ).det = 0 :=
    not_ne_iff.mp (mt hCps.posDef_iff_det_ne_zero.mpr hC)
  have hg := gapSq_eq_trace_det referenceWeights ψ hψ
  rw [hdet, gapSq, Finset.sum_filter, Fintype.sum_prod_type] at hg
  norm_num [referenceWeights, Fin.sum_univ_three] at hg
  have h01 := normSq_inner _ _ (hψ 0) (hψ 1)
  have h02 := normSq_inner _ _ (hψ 0) (hψ 2)
  have h12 := normSq_inner _ _ (hψ 1) (hψ 2)
  change overlap ψ 0 1 ≤ 1 at h01
  change overlap ψ 0 2 ≤ 1 at h02
  change overlap ψ 1 2 ≤ 1 at h12
  constructor <;> linarith only [hg, h01, h02, h12]

private theorem singular_entropy (ψ : Fin 3 → Fin 2 → ℂ)
    (hψ : ∀ i, star (ψ i) ⬝ᵥ ψ i = 1) (hC : ¬ (reference ψ).PosDef) :
    traceLog (input ψ) (reference ψ) = Real.log (47 / 31) := by
  let P := vecMulVec (ψ 0) (star (ψ 0))
  have hp (i : Fin 3) : vecMulVec (ψ i) (star (ψ i)) = P := by
    obtain ⟨h01, h02⟩ := singular_overlaps ψ hψ hC
    fin_cases i
    · rfl
    · exact projection_eq_of_overlap_one ψ hψ 1 h01
    · exact projection_eq_of_overlap_one ψ hψ 2 h02
  have hA : input ψ = P := by
    simp only [contrast, hp, ← Finset.sum_smul, Fin.sum_univ_three, inputWeights, Matrix.cons_val]
    norm_num
  have hC' : reference ψ = (31 / 47 : ℝ) • P := by
    simp only [contrast, hp, ← Finset.sum_smul, Fin.sum_univ_three, referenceWeights, Matrix.cons_val]
    norm_num
  have hi : P * P = P := by
    dsimp [P]
    rw [Matrix.vecMulVec_mul_vecMulVec, hψ]
    simp
  have hh := (Matrix.posSemidef_vecMulVec_self_star (ψ 0)).isHermitian
  have hlog (r : ℝ) : cfc Real.log (r • P) = Real.log r • P := by
    simpa using D5.S3.Quantum.Information.FullwoodParzygnatSubadditivityRefutation.projection_cfc
      P hh hi Real.log 0 r
  have htr : P.trace = 1 := by
    dsimp [P]
    rw [Matrix.trace_vecMulVec, dotProduct_comm, hψ]
  simp only [traceLog, hA, hC', CFC.log]
  rw [show cfc Real.log P = 0 by simpa using hlog 1, hlog, zero_sub, mul_neg,
    Matrix.mul_smul, hi, Matrix.trace_neg, Matrix.trace_smul, htr]
  simp only [Complex.neg_re, Complex.real_smul, mul_one, Complex.ofReal_re]
  rw [← Real.log_inv]
  norm_num

/-- Quantitative Fibonacci benchmark gap for each unit pure-qubit preparation triple. -/
theorem traceLog_le_benchmark_sub_margin (ψ : Fin 3 → Fin 2 → ℂ)
    (hψ : ∀ i, star (ψ i) ⬝ᵥ ψ i = 1) :
    let A := contrast ![(88 / 141 : ℝ), 25 / 141, 28 / 141] ψ
    let C := contrast ![(66 / 141 : ℝ), 15 / 141, 12 / 141] ψ
    (A * (CFC.log A - CFC.log C)).trace.re ≤
      ((113 / 141 : ℝ) * Real.log (113 / 81) + (28 / 141) * Real.log (7 / 3)) -
        (3 * (1 - overlap ψ 0 1) + 11 * overlap ψ 0 2) / 63360 := by
  change traceLog (input ψ) (reference ψ) ≤ C3 -
    (3 * (1 - overlap ψ 0 1) + 11 * overlap ψ 0 2) / 63360
  by_cases hc : (reference ψ).PosDef
  · have he := faithful_entropy_sub ψ hψ hc
    have hi := integral_excess_profile_le_margin ψ hψ
    linarith only [he, hi]
  · rw [singular_entropy ψ hψ hc, (singular_overlaps ψ hψ hc).1, (singular_overlaps ψ hψ hc).2]
    have H₁ := (log_bounds (q := 113 / 81) (by norm_num)).1
    have H₂ := (log_bounds (q := 7 / 3) (by norm_num)).1
    have H₃ := (log_bounds (q := 47 / 31) (by norm_num)).2
    have L₁ : (332 / 1000 : ℝ) ≤ Real.log (113 / 81) :=
      (by norm_num [logSumFive, Finset.sum_range_succ] : _ ≤ logSumFive _).trans H₁
    have L₂ : (847 / 1000 : ℝ) ≤ Real.log (7 / 3) :=
      (by norm_num [logSumFive, Finset.sum_range_succ] : _ ≤ logSumFive _).trans H₂
    have U₃ : Real.log (47 / 31) ≤ (417 / 1000 : ℝ) :=
      H₃.trans (by norm_num [logSumFive, logRemainderFive, Finset.sum_range_succ])
    dsimp [C3]
    linarith only [L₁, L₂, U₃]

#print axioms traceLog_le_benchmark_sub_margin

end Integral

namespace Benchmark

export _root_.D5.S3.Quantum.Divergence.Qubit.FibonacciClippedProfile
  (inputWeights referenceWeights C3)

end Benchmark

end D5.S3.Quantum.Divergence.Qubit.FibonacciClippedProfile
