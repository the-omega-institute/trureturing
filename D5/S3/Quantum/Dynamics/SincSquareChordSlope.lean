/- GID: D5/S3/Quantum/Dynamics/SincSquareChordSlope
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/SincSquareChordSlope
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Chord slopes of sinc^2 in the squared variable from a base in (0, pi/2] decrease. -/

/-
proof_shape: sincSq_chord_lt: content; escape_witness: the public conclusion itself (form 2;
preregistered fact E1 of issue #14487): for 0 < θ ≤ π/2 and θ < u < v,
(ψ θ - ψ v) (u² - θ²) < (ψ θ - ψ u) (v² - θ²) with ψ x = (sin x / x)², produced on the live path
by the strict antitonicity on (θ, ∞) of Γ u = (ψ θ - ψ u) / (u² - θ²), whose derivative is
-2 u T(θ, u) / (u² - θ²)² with T the tangent expression of tangent_pos; no Mathlib or frozen
declaration states it.
Private helpers:
proof_shape: sin_sub_mul_cos_pos: content (sin z - z cos z > 0 on (0, π], by monotonicity);
consumer: slopeNumeratorDeriv_pos.
proof_shape: slopeNumeratorDeriv_pos: content (the derivative of the numerator
n z = z²/2 cos z - 5z/2 sin z + 4 - 4 cos z is positive on (0, π]); consumer: slopeNumerator_pos.
proof_shape: slopeNumerator_pos: content (n > 0 on (0, 2π]: monotonicity on (0, π], Jordan's
inequality and sign bookkeeping on (π, 2π]); consumer: slopeRatio_strictMonoOn.
proof_shape: hasDerivAt_slopeRatio: bind-only (Mathlib derivative rules and normalisation:
q' u = n (2u) / u⁵); consumer: slopeRatio_strictMonoOn.
proof_shape: slopeRatio_strictMonoOn: content (q u = ψ' u / u is strictly increasing on (0, π]);
consumer: tangent_pos.
proof_shape: hasDerivAt_sincSq: bind-only (Mathlib derivative rules and normalisation:
ψ' u = u q u); consumer: tangent_pos, sincSq_chord_lt.
proof_shape: tangent_pos: content (the tangent inequality
ψ θ - ψ u + q u (u² - θ²) / 2 > 0 for 0 < θ < u, θ ≤ π/2); consumer: sincSq_chord_lt.
Definition: slopeRatio (private; q u = (u sin 2u - 1 + cos 2u) / u⁴); consumer:
hasDerivAt_slopeRatio, slopeRatio_strictMonoOn, hasDerivAt_sincSq, tangent_pos, sincSq_chord_lt.
admission_basis: escape-witness
Direct frozen dependencies: none (pinned Mathlib only).
utility: none; no declaration is a bounded enumeration, checker, numeric reduction or certified
instance: every statement quantifies over real intervals.
-/

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Dynamics.SincSquareChordSlope

open Real Set

/-- `sin z - z * cos z` is positive on `(0, π]`. -/
private theorem sin_sub_mul_cos_pos {z : ℝ} (hz : 0 < z) (hzπ : z ≤ π) :
    0 < sin z - z * cos z := by
  have hmono : StrictMonoOn (fun y : ℝ => sin y - y * cos y) (Icc 0 π) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc 0 π) (by fun_prop) fun x hx => ?_
    rw [interior_Icc] at hx
    have hd : HasDerivAt (fun y : ℝ => sin y - y * cos y) (x * sin x) x :=
      ((hasDerivAt_sin x).fun_sub ((hasDerivAt_id' x).fun_mul (hasDerivAt_cos x))).congr_deriv
        (by ring)
    rw [hd.deriv]
    exact mul_pos hx.1 (sin_pos_of_pos_of_lt_pi hx.1 hx.2)
  have h := hmono (left_mem_Icc.2 pi_pos.le) ⟨hz.le, hzπ⟩ hz
  simpa using h

/-- The derivative `3/2 sin z - 3z/2 cos z - z²/2 sin z` of the numerator
`z²/2 cos z - 5z/2 sin z + 4 - 4 cos z` is positive on `(0, π]`. -/
private theorem slopeNumeratorDeriv_pos {z : ℝ} (hz : 0 < z) (hzπ : z ≤ π) :
    0 < 3 / 2 * sin z - 3 * z / 2 * cos z - z ^ 2 / 2 * sin z := by
  have hmono : StrictMonoOn
      (fun y : ℝ => 3 / 2 * sin y - 3 * y / 2 * cos y - y ^ 2 / 2 * sin y) (Icc 0 π) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc 0 π) (by fun_prop) fun x hx => ?_
    rw [interior_Icc] at hx
    have hd : HasDerivAt (fun y : ℝ => 3 / 2 * sin y - 3 * y / 2 * cos y - y ^ 2 / 2 * sin y)
        (x / 2 * (sin x - x * cos x)) x :=
      ((((hasDerivAt_sin x).const_mul (3 / 2 : ℝ)).fun_sub
        ((((hasDerivAt_id' x).const_mul (3 : ℝ)).div_const 2).fun_mul (hasDerivAt_cos x))).fun_sub
        (((hasDerivAt_pow 2 x).div_const 2).fun_mul (hasDerivAt_sin x))).congr_deriv
        (by push_cast; ring)
    rw [hd.deriv]
    exact mul_pos (half_pos hx.1) (sin_sub_mul_cos_pos hx.1 hx.2.le)
  have h := hmono (left_mem_Icc.2 pi_pos.le) ⟨hz.le, hzπ⟩ hz
  simpa using h

/-- The numerator `n z = z²/2 cos z - 5z/2 sin z + 4 - 4 cos z` is positive on `(0, 2π]`. -/
private theorem slopeNumerator_pos {z : ℝ} (hz : 0 < z) (hz2π : z ≤ 2 * π) :
    0 < z ^ 2 / 2 * cos z - 5 * z / 2 * sin z + 4 - 4 * cos z := by
  rcases le_or_gt z π with hzπ | hzπ
  · have hmono : StrictMonoOn
        (fun y : ℝ => y ^ 2 / 2 * cos y - 5 * y / 2 * sin y + 4 - 4 * cos y) (Icc 0 π) := by
      refine strictMonoOn_of_deriv_pos (convex_Icc 0 π) (by fun_prop) fun x hx => ?_
      rw [interior_Icc] at hx
      have hd : HasDerivAt
          (fun y : ℝ => y ^ 2 / 2 * cos y - 5 * y / 2 * sin y + 4 - 4 * cos y)
          (3 / 2 * sin x - 3 * x / 2 * cos x - x ^ 2 / 2 * sin x) x :=
        ((((((hasDerivAt_pow 2 x).div_const 2).fun_mul (hasDerivAt_cos x)).fun_sub
          ((((hasDerivAt_id' x).const_mul (5 : ℝ)).div_const 2).fun_mul
            (hasDerivAt_sin x))).add_const 4).fun_sub
          ((hasDerivAt_cos x).const_mul (4 : ℝ))).congr_deriv (by push_cast; ring)
      rw [hd.deriv]
      exact slopeNumeratorDeriv_pos hx.1 hx.2.le
    have h := hmono (left_mem_Icc.2 pi_pos.le) ⟨hz.le, hzπ⟩ hz
    simpa using h
  · obtain ⟨w, rfl⟩ : ∃ w, z = w + π := ⟨z - π, by ring⟩
    have hw0 : 0 < w := by linarith
    have hwπ : w ≤ π := by linarith
    have hs0 : 0 ≤ sin w := sin_nonneg_of_nonneg_of_le_pi hw0.le hwπ
    have hπ9 : 9 < π * π := by nlinarith [pi_gt_three]
    have hZ : 0 ≤ (w + π) ^ 2 / 2 - 4 := by nlinarith [mul_pos hw0 pi_pos, mul_self_nonneg w]
    rw [cos_add_pi, sin_add_pi]
    rcases le_or_gt w (π / 2) with hw2 | hw2
    · have hs : 2 * w ≤ π * sin w := by
        have h := mul_le_sin hw0.le hw2
        rw [div_mul_eq_mul_div, div_le_iff₀ pi_pos] at h
        linarith
      have h1 : 0 ≤ ((w + π) ^ 2 / 2 - 4) * (1 - cos w) :=
        mul_nonneg hZ (by linarith [cos_le_one w])
      have h2 : 0 ≤ w * sin w := mul_nonneg hw0.le hs0
      have h3 : 0 ≤ w * (π / 2 - w) := mul_nonneg hw0.le (by linarith)
      have h4 : 0 ≤ w * (4 - π) := mul_nonneg hw0.le (by linarith [pi_lt_four])
      have h5 : π * π < 16 := by nlinarith [pi_pos, pi_lt_four]
      linarith [h1, h2, h3, h4, h5, hs]
    · have hc0 : cos w ≤ 0 := cos_nonpos_of_pi_div_two_le_of_le hw2.le (by linarith [pi_pos])
      have h1 : 0 ≤ ((w + π) ^ 2 / 2 - 4) * (-cos w) := mul_nonneg hZ (by linarith)
      have h2 : 0 ≤ (w + π) * sin w := mul_nonneg (by linarith [pi_pos]) hs0
      linarith [h1, h2]

/-- The ratio `q u = ψ' u / u` for `ψ u = (sin u / u) ^ 2`. -/
private def slopeRatio (u : ℝ) : ℝ := (u * sin (2 * u) - 1 + cos (2 * u)) / u ^ 4

/-- `q' u = n (2 u) / u ^ 5`. -/
private theorem hasDerivAt_slopeRatio {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt slopeRatio
      (((2 * u) ^ 2 / 2 * cos (2 * u) - 5 * (2 * u) / 2 * sin (2 * u) + 4 - 4 * cos (2 * u)) /
        u ^ 5) u := by
  have h2 : HasDerivAt (fun y : ℝ => 2 * y) (2 * 1) u := (hasDerivAt_id' u).const_mul 2
  have hnum : HasDerivAt (fun y : ℝ => y * sin (2 * y) - 1 + cos (2 * y))
      (1 * sin (2 * u) + u * (cos (2 * u) * (2 * 1)) + -sin (2 * u) * (2 * 1)) u :=
    ((((hasDerivAt_id' u).fun_mul h2.sin).sub_const 1).fun_add h2.cos)
  have hden : HasDerivAt (fun y : ℝ => y ^ 4) ((4 : ℕ) * u ^ (4 - 1)) u := hasDerivAt_pow 4 u
  have h := hnum.fun_div hden (pow_ne_zero 4 hu)
  refine h.congr_deriv ?_
  push_cast
  rw [div_eq_div_iff (pow_ne_zero 2 (pow_ne_zero 4 hu)) (pow_ne_zero 5 hu)]
  ring

/-- `q` is strictly increasing on `(0, π]`. -/
private theorem slopeRatio_strictMonoOn : StrictMonoOn slopeRatio (Ioc 0 π) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioc 0 π)
    (fun x hx => (hasDerivAt_slopeRatio hx.1.ne').continuousAt.continuousWithinAt)
    fun x hx => ?_
  rw [interior_Ioc] at hx
  rw [(hasDerivAt_slopeRatio hx.1.ne').deriv]
  exact div_pos (slopeNumerator_pos (by linarith [hx.1]) (by linarith [hx.2])) (pow_pos hx.1 5)

/-- `ψ' u = u * q u` for `ψ u = (sin u / u) ^ 2`. -/
private theorem hasDerivAt_sincSq {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (fun y : ℝ => (sin y / y) ^ 2) (u * slopeRatio u) u := by
  have h := ((hasDerivAt_sin u).fun_div (hasDerivAt_id' u) hu).fun_pow 2
  refine h.congr_deriv ?_
  unfold slopeRatio
  rw [sin_two_mul, cos_two_mul, cos_sq']
  push_cast
  field_simp
  ring

/-- The tangent inequality `ψ θ - ψ u + ψ' u * (u ^ 2 - θ ^ 2) / (2 * u) > 0`. -/
private theorem tangent_pos {θ u : ℝ} (hθ : 0 < θ) (hθ' : θ ≤ π / 2) (hu : θ < u) :
    0 < (sin θ / θ) ^ 2 - (sin u / u) ^ 2 + slopeRatio u * (u ^ 2 - θ ^ 2) / 2 := by
  have hu0 : 0 < u := hθ.trans hu
  rcases le_or_gt u π with huπ | huπ
  · have hd : ∀ x : ℝ, x ≠ 0 → HasDerivAt
        (fun y : ℝ => (sin y / y) ^ 2 - (sin u / u) ^ 2 + slopeRatio u * (u ^ 2 - y ^ 2) / 2)
        (x * (slopeRatio x - slopeRatio u)) x := fun x hx =>
      (((hasDerivAt_sincSq hx).sub_const ((sin u / u) ^ 2)).fun_add
        ((((hasDerivAt_pow 2 x).const_sub (u ^ 2)).const_mul (slopeRatio u)).div_const
          2)).congr_deriv (by push_cast; ring)
    have hanti : StrictAntiOn
        (fun y : ℝ => (sin y / y) ^ 2 - (sin u / u) ^ 2 + slopeRatio u * (u ^ 2 - y ^ 2) / 2)
        (Ioc 0 u) := by
      refine strictAntiOn_of_deriv_neg (convex_Ioc 0 u)
        (fun x hx => (hd x hx.1.ne').continuousAt.continuousWithinAt) fun x hx => ?_
      rw [interior_Ioc] at hx
      rw [(hd x hx.1.ne').deriv]
      exact mul_neg_of_pos_of_neg hx.1 (sub_neg.2
        (slopeRatio_strictMonoOn ⟨hx.1, hx.2.le.trans huπ⟩ ⟨hu0, huπ⟩ hx.2))
    have h := hanti ⟨hθ, hu.le⟩ ⟨hu0, le_rfl⟩ hu
    simp only [sub_self, mul_zero, zero_div, add_zero] at h
    exact h
  · have hψθ : (2 / π) ^ 2 ≤ (sin θ / θ) ^ 2 := by
      refine pow_le_pow_left₀ (by positivity) ?_ 2
      rw [le_div_iff₀ hθ]
      exact mul_le_sin hθ.le hθ'
    have hD0 : 0 ≤ u ^ 2 - θ ^ 2 := by nlinarith
    have hD1 : u ^ 2 - θ ^ 2 ≤ u ^ 2 := by nlinarith
    have hA : 1 - cos (2 * u) - u * sin (2 * u) ≤ 2 + u := by
      have h := mul_nonneg hu0.le
        (by linarith [neg_one_le_sin (2 * u)] : (0 : ℝ) ≤ 1 + sin (2 * u))
      linarith [neg_one_le_cos (2 * u)]
    have hAD : (1 - cos (2 * u) - u * sin (2 * u)) * (u ^ 2 - θ ^ 2) ≤ (2 + u) * u ^ 2 :=
      mul_le_mul hA hD1 hD0 (by linarith)
    have h1 : (sin u / u) ^ 2 ≤ 1 / u ^ 2 := by
      rw [div_pow]
      exact div_le_div_of_nonneg_right (sin_sq_le_one u) (by positivity)
    have hq : slopeRatio u * (u ^ 2 - θ ^ 2) / 2 =
        -((1 - cos (2 * u) - u * sin (2 * u)) * (u ^ 2 - θ ^ 2) / (2 * u ^ 4)) := by
      unfold slopeRatio
      field_simp
      ring
    have h2 : (1 - cos (2 * u) - u * sin (2 * u)) * (u ^ 2 - θ ^ 2) / (2 * u ^ 4) ≤
        (2 + u) * u ^ 2 / (2 * u ^ 4) :=
      div_le_div_of_nonneg_right hAD (by positivity)
    have h3 : 1 / u ^ 2 + (2 + u) * u ^ 2 / (2 * u ^ 4) < (2 / π) ^ 2 := by
      have e : 1 / u ^ 2 + (2 + u) * u ^ 2 / (2 * u ^ 4) = (4 + u) / (2 * u ^ 2) := by
        field_simp
        ring
      rw [e, div_pow, div_lt_div_iff₀ (by positivity) (by positivity)]
      have a1 : 0 < (u - π) * (u + π) := mul_pos (sub_pos.2 huπ) (by positivity)
      have a2 : 0 < u * (4 * u - π * π) :=
        mul_pos hu0 (by nlinarith [mul_pos pi_pos (sub_pos.2 pi_lt_four)])
      nlinarith [a1, a2]
    rw [hq]
    linarith

/-- **Strictly decreasing chord slope of `sinc²` in the squared variable.** With
`ψ x = (sin x / x) ^ 2`, a base point `θ ∈ (0, π / 2]` and `θ < u < v`, the chord slopes
`(ψ θ - ψ u) / (u ^ 2 - θ ^ 2)` and `(ψ θ - ψ v) / (v ^ 2 - θ ^ 2)` satisfy the strict inequality
`(ψ θ - ψ v) / (v ^ 2 - θ ^ 2) < (ψ θ - ψ u) / (u ^ 2 - θ ^ 2)`, stated here without division. -/
theorem sincSq_chord_lt {θ u v : ℝ} (hθ : 0 < θ) (hθ' : θ ≤ π / 2) (hu : θ < u) (huv : u < v) :
    ((sin θ / θ) ^ 2 - (sin v / v) ^ 2) * (u ^ 2 - θ ^ 2) <
      ((sin θ / θ) ^ 2 - (sin u / u) ^ 2) * (v ^ 2 - θ ^ 2) := by
  have hpos : ∀ x : ℝ, θ < x → 0 < x ^ 2 - θ ^ 2 := fun x hx => by
    nlinarith [mul_pos (sub_pos.2 hx) (add_pos (hθ.trans hx) hθ)]
  have hd : ∀ x : ℝ, θ < x → HasDerivAt
      (fun y : ℝ => ((sin θ / θ) ^ 2 - (sin y / y) ^ 2) / (y ^ 2 - θ ^ 2))
      (-(2 * x * ((sin θ / θ) ^ 2 - (sin x / x) ^ 2 + slopeRatio x * (x ^ 2 - θ ^ 2) / 2)) /
        (x ^ 2 - θ ^ 2) ^ 2) x := fun x hx =>
    (((hasDerivAt_sincSq (hθ.trans hx).ne').const_sub ((sin θ / θ) ^ 2)).fun_div
      ((hasDerivAt_pow 2 x).sub_const (θ ^ 2)) (hpos x hx).ne').congr_deriv (by push_cast; ring)
  have hanti : StrictAntiOn
      (fun y : ℝ => ((sin θ / θ) ^ 2 - (sin y / y) ^ 2) / (y ^ 2 - θ ^ 2)) (Ioi θ) := by
    refine strictAntiOn_of_deriv_neg (convex_Ioi θ)
      (fun x hx => (hd x hx).continuousAt.continuousWithinAt) fun x hx => ?_
    rw [interior_Ioi] at hx
    rw [(hd x hx).deriv]
    exact div_neg_of_neg_of_pos
      (neg_neg_of_pos (mul_pos (mul_pos two_pos (hθ.trans hx)) (tangent_pos hθ hθ' hx)))
      (pow_pos (hpos x hx) 2)
  have h : ((sin θ / θ) ^ 2 - (sin v / v) ^ 2) / (v ^ 2 - θ ^ 2) <
      ((sin θ / θ) ^ 2 - (sin u / u) ^ 2) / (u ^ 2 - θ ^ 2) :=
    hanti (mem_Ioi.2 hu) (mem_Ioi.2 (hu.trans huv)) huv
  rwa [div_lt_div_iff₀ (hpos v (hu.trans huv)) (hpos u hu)] at h

end D5.S3.Quantum.Dynamics.SincSquareChordSlope
