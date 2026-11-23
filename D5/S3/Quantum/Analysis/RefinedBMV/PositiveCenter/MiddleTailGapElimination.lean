/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/MiddleTailGapElimination
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Remove the upper marginal and gap decay from the paired mixed-derivative estimate. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.MiddleTailGapBounds

/-! The polynomial bounds for eliminating the gap in the paired mixed derivative. -/

namespace RefinedBMV.PositiveCenter

open private geometricValue geometricDerivative lossValue lossDerivative from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.MiddleTailJointScore
open private tail_add_gap from D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.TailFormula
open private CompactTaylorModel.CompactMiddleBox.gap_lower from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactMiddleBox

/-- The five signs required by the two-variable Bernstein comparison. -/
structure MiddleTailGapPolynomials where
  W : ℝ
  upperSlopeCoefficient : ℝ
  linearLoss : ℝ
  decayCoefficient : ℝ
  numerator : ℝ

/-- Read the coefficients before either of the two monotone substitutions. -/
noncomputable def middleTailGapPolynomials (h u q : ℝ) : MiddleTailGapPolynomials :=
  let f := upperTailGap h u
  let x := Real.exp (-u)
  let n := 3 + h
  let k := 3 + 2 * h
  let c := n * k / 2
  let e := Real.exp (-(k * u))
  let W := shortGapWeight h u
  let S := 2 * f * W
  let H := (1 + h) * f * (k * f - 4) + 2 - 2 * (f + 1) * e
  let A := n + (k * f - 1) * q
  let R := 1 + f * q
  let ρ := x * R
  let ell := 1 - q
  let η := q * (h + q)
  let Z := (2 + h) * S - H
  let M := (Z + q * S) * lossValue h u + S * lossDerivative h u
  let U := Z * geometricValue h u + S * geometricDerivative h u - (h + q) * M
  let V := η * (M + (h + q) * S * lossValue h u)
  let C := H * (1 - ρ) ^ 2 - ell * S * (1 - ρ ^ 2)
  let T := c * R * U - A * V
  let P := (c * R - A * (1 + (h + q))) * C +
    A * η * (S * (1 - ρ ^ 2) - 2 * f * x * (H * (1 - ρ) - S * ell * ρ))
  let β := (31 / 800 : ℝ) * (13 / 4) ^ 4
  ⟨W, C, U, T, c * P - 2 * β * q ^ 5 * T + c * S * A / 2000⟩

private theorem affine_score_upper
    {q ζ ζ₀ c S A R C U V P y : ℝ}
    (hq : 0 ≤ q) (hζ : 0 ≤ ζ) (hζ₀ : ζ₀ ≤ ζ)
    (hc : 0 < c) (hS : 0 < S) (hA : 0 < A)
    (hC : C ≤ 0) (hU : 0 ≤ U) (hT : 0 < c * R * U - A * V)
    (hy : c * R / A ≤ y) :
    P / (S * A) + (y - c * R / A) * C / S +
        2 * ζ * q / c * (-y * U + V) / S ≤
      (c * P - 2 * ζ₀ * q * (c * R * U - A * V)) / (c * S * A) := by
  let y₀ := c * R / A
  have hshift : (y - y₀) * C / S ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hy) hC) hS.le
  have hlin : -y * U + V ≤ -y₀ * U + V := by
    have H := mul_le_mul_of_nonneg_right hy hU
    linarith only [H]
  have hzero : -y₀ * U + V = -(c * R * U - A * V) / A := by
    dsimp only [y₀]
    field_simp [hA.ne'] <;> ring
  have hcoeff : 2 * q / c * (-y₀ * U + V) / S ≤ 0 := by
    rw [hzero]
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (by positivity)
        (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hT.le) hA.le)) hS.le
  calc
    _ ≤ P / (S * A) + 2 * ζ * q / c * (-y₀ * U + V) / S := by
      have H := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlin (show 0 ≤ 2 * ζ * q / c by positivity)) hS.le
      linarith only [H, hshift]
    _ = P / (S * A) + ζ * (2 * q / c * (-y₀ * U + V) / S) := by ring
    _ ≤ P / (S * A) + ζ₀ * (2 * q / c * (-y₀ * U + V) / S) :=
      add_le_add le_rfl (mul_le_mul_of_nonpos_right hζ₀ hcoeff)
    _ = _ := by rw [hzero]; field_simp [hc.ne', hS.ne', hA.ne'] <;> ring

private theorem lowerSlope_cancel {h f q : ℝ}
    (hR : 0 < 1 + f * q) (hr : 0 < h + q) (hA : 0 < 3 + h + ((3 + 2 * h) * f - 1) * q) :
    let R := 1 + f * q
    let A := 3 + h + ((3 + 2 * h) * f - 1) * q
    let c := (3 + h) * (3 + 2 * h) / 2
    1 + (h + q) / R + middleTailMarginalLower h (R / (h + q)) = c * R / A := by
  intro R A c
  have hRp : 0 < R := hR
  have hAp : 0 < A := hA
  have hform : (3 + 2 * h) * (R / (h + q)) - 1 = A / (h + q) := by
    field_simp [hr.ne']
    dsimp only [R, A]
    ring
  unfold middleTailMarginalLower
  dsimp only
  have hform₄ : (3 + 2 * h) * (R / (h + q)) - 4 = A / (h + q) - 3 := by
    linarith only [hform]
  rw [hform, hform₄]
  field_simp [hr.ne', hRp.ne', hAp.ne']
  dsimp only [R, A, c]
  ring

private theorem leading_score_affine {h f q x S H A c y : ℝ}
    (hS : 0 < S) (hA : 0 < A) (hR : 0 < 1 + f * q) :
    let R := 1 + f * q
    let r := h + q
    let ρ := x * R
    let η := q * r
    let ell := 1 - q
    let δ := f * η / R
    let b := y - 1 - r / R
    let C := H * (1 - ρ) ^ 2 - ell * S * (1 - ρ ^ 2)
    let P := (c * R - A * (1 + r)) * C +
      A * η * (S * (1 - ρ ^ 2) - 2 * f * x * (H * (1 - ρ) - S * ell * ρ))
    (1 - ρ ^ 2) * (η + δ * (ell - H / S) - b * ell) +
        b * (H / S) * (1 - ρ) ^ 2 + 2 * δ * ell * ρ ^ 2 =
      P / (S * A) + (y - c * R / A) * C / S := by
  intro R r ρ η ell δ b C P
  have hRp : 0 < R := hR
  calc
    _ = ((S * (1 - ρ ^ 2) * η +
        δ * ((1 + ρ ^ 2) * S * ell - (1 - ρ ^ 2) * H)) + b * C) / S := by
      dsimp only [C]
      field_simp [hS.ne'] <;> ring
    _ = _ := by
      dsimp only [P, b, δ, ρ, C]
      field_simp [hS.ne', hA.ne', hRp.ne']
      dsimp only [R, r, η, ell]
      ring

private theorem middleTail_reflectedSlope_scaled {p : ℕ} (hp : 0 < p)
    {t : ℝ} (ht : 0 < t) :
    let h : ℝ := 3 / (p : ℝ)
    let k := 3 + 2 * h
    let f := upperTailGap h t
    let e := Real.exp (-(k * t))
    reflectedHalfLogSlope (compositionMoment p 0) t =
      ((1 + h) * f * (k * f - 4) + 2 - 2 * (f + 1) * e) /
        (2 * f * shortGapWeight h t) := by
  intro h k f e
  have hh : 0 < h := by dsimp only [h]; positivity
  have hf : 0 < f := tail_gap_pos hh ht
  have hW := shortGapWeight_pos hh ht
  have hj : upperTailSlope h t = f⁻¹ - h := CompactGap.upperTailSlope_eq_inv_gap_sub_rate hh ht
  have hE : Real.exp (-(h * t)) = 1 - h * f := by
    have H := tail_gap_factor (t := t) hh
    change 1 - Real.exp (-(h * t)) = h * f at H
    linarith only [H]
  have hSlope := middleTail_reflectedSlope_eq hp ht
  change reflectedHalfLogSlope (compositionMoment p 0) t =
    ((1 - 2 * upperTailSlope h t) * (k * f - 1 + e) +
      k * (Real.exp (-(h * t)) - e)) / (2 * shortGapWeight h t) at hSlope
  rw [hSlope, hj, hE]
  field_simp [hf.ne', hW.ne']
  dsimp only [k]
  ring

private theorem middleTail_gap_profile {h u d : ℝ}
    (hh : 0 < h) (hu : 0 < u) (hd : 0 < d) :
    let f := upperTailGap h u
    let q := upperTailSlope h d
    let R := 1 + f * q
    let v := d + u
    let r := h + q
    upperTailGap h v = R / r ∧
    upperTailGap h d = 1 / r ∧
    upperTailSlope h v = r / R - h ∧
    Real.exp (-(h * d)) * f / (upperTailGap h d * upperTailGap h v) = f * (q * r) / R ∧
    upperTailGap h v * Real.exp (-u) / upperTailGap h d = Real.exp (-u) * R ∧
    Real.exp (-((1 + h) * d)) / upperTailGap h d = Real.exp (-d) * q := by
  intro f q R v r
  have hv : 0 < v := add_pos hd hu
  have hq : 0 < q := (upperTailSlope_bounds hh hd).1
  have hf : 0 < f := tail_gap_pos hh hu
  have hr : 0 < r := add_pos hh hq
  have hR : 0 < R := by dsimp only [R]; positivity
  have hfD := tail_gap_pos hh hd
  have hD : upperTailGap h d = 1 / r := by
    have H := CompactGap.upperTailSlope_eq_inv_gap_sub_rate hh hd
    change q = (upperTailGap h d)⁻¹ - h at H
    have H' : r = (upperTailGap h d)⁻¹ := by dsimp only [r]; linarith only [H]
    rw [H', one_div, inv_inv]
  have hE : Real.exp (-(h * d)) = q * upperTailGap h d := by
    rw [← (hasDerivAt_upperTailGap hh).deriv]
    exact (div_eq_iff hfD.ne').mp (upperTailGap_logDeriv hh hd)
  have hV : upperTailGap h v = R / r := by
    have H : upperTailGap h v = upperTailGap h d + Real.exp (-(h * d)) * f := by
      dsimp only [v]
      rw [add_comm d u]
      exact tail_add_gap hh d u
    rw [H, hE, hD]
    dsimp only [R]
    ring
  refine ⟨hV, hD, ?_, ?_, ?_, ?_⟩
  · rw [CompactGap.upperTailSlope_eq_inv_gap_sub_rate hh hv, hV, inv_div]
  · rw [hE, hD, hV]
    field_simp [hr.ne', hR.ne'] <;> ring
  · rw [hD, hV]
    field_simp [hr.ne'] <;> ring
  · rw [show -((1 + h) * d) = -d + -(h * d) by ring, Real.exp_add, hE]
    field_simp [hfD.ne'] <;> ring

/-- A proof of the Bernstein coefficient signs discharges the original mixed
kernel inequality on the central upper gap band. -/
theorem logKernel_mixed_neg_of_middleTail_polynomials {p : ℕ} (hp : 11 ≤ p) {u v : ℝ}
    (hu₀ : 1 / 2 ≤ u) (hu₁ : u ≤ 4) (hd₀ : 13 / 4 ≤ v - u) (hd₁ : v - u ≤ 7 / 2)
    (hcheck :
      let h : ℝ := 3 / (p : ℝ)
      let B := middleTailGapPolynomials h u (upperTailSlope h (v - u))
      B.upperSlopeCoefficient < 0 ∧ 0 < B.linearLoss ∧ 0 < B.decayCoefficient ∧ B.numerator < 0) :
    deriv (fun y ↦ deriv (fun x ↦ logKernel p x y) u) v < 0 := by
  let h : ℝ := 3 / (p : ℝ)
  let d := v - u
  let f := upperTailGap h u
  let x := Real.exp (-u)
  let n := 3 + h
  let k := 3 + 2 * h
  let c := n * k / 2
  let e := Real.exp (-(k * u))
  let W := shortGapWeight h u
  let S := 2 * f * W
  let H := (1 + h) * f * (k * f - 4) + 2 - 2 * (f + 1) * e
  let q := upperTailSlope h d
  let r := h + q
  let A := n + (k * f - 1) * q
  let R := 1 + f * q
  let ρ := x * R
  let ell := 1 - q
  let η := q * r
  let Z := (2 + h) * S - H
  let L := lossValue h u
  let L₁ := lossDerivative h u
  let D := geometricValue h u
  let D₁ := geometricDerivative h u
  let M := (Z + q * S) * L + S * L₁
  let U := Z * D + S * D₁ - r * M
  let V := η * (M + r * S * L)
  let C := H * (1 - ρ) ^ 2 - ell * S * (1 - ρ ^ 2)
  let T := c * R * U - A * V
  let P := (c * R - A * (1 + r)) * C +
    A * η * (S * (1 - ρ ^ 2) - 2 * f * x * (H * (1 - ρ) - S * ell * ρ))
  let β := (31 / 800 : ℝ) * (13 / 4) ^ 4
  let ζ := Real.exp (-d)
  let a := reflectedHalfLogSlope (compositionMoment p 0) u
  let b := reflectedHalfLogSlope (compositionMoment p 0) v
  let y := 1 + r / R + b
  have hp₀ : 0 < p := by omega
  have hpR : (11 : ℝ) ≤ p := by exact_mod_cast hp
  have hh : 0 < h := by dsimp only [h]; positivity
  have hhmax : h ≤ 3 / 11 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpR
  have hu : 0 < u := by linarith only [hu₀]
  have hd : 0 < d := by dsimp only [d]; linarith only [hd₀]
  have hv : 15 / 4 ≤ v := by linarith only [hu₀, hd₀]
  have hf : 0 < f := tail_gap_pos hh hu
  have hW : 0 < W := shortGapWeight_pos hh hu
  have hS : 0 < S := by dsimp only [S]; positivity
  have hc : 0 < c := by dsimp only [c, n, k]; positivity
  obtain ⟨hq, _, _, hζbound⟩ := middleTail_gap_bounds hh hhmax hd₀ hd₁
  change 0 < q at hq
  change β * q ^ 4 ≤ ζ at hζbound
  have hr : 0 < r := add_pos hh hq
  have hR : 0 < R := by dsimp only [R]; positivity
  have hfl : (11 : ℝ) / 25 ≤ f := by
    simpa only [show (1 / 2 : ℝ) / (1 + (3 / 11) * (1 / 2)) = 11 / 25 by norm_num]
      using CompactTaylorModel.CompactMiddleBox.gap_lower hh hhmax (by norm_num) hu₀
  have hkf : 1 ≤ k * f := by
    have Hk : 0 ≤ k - 3 := by dsimp only [k]; linarith only [hh]
    nlinarith only [hfl, mul_nonneg Hk hf.le]
  have hA : 0 < A := by
    dsimp only [A]
    have hn : 0 < n := by dsimp only [n]; positivity
    exact add_pos_of_pos_of_nonneg hn (mul_nonneg (sub_nonneg.mpr hkf) hq.le)
  change C < 0 ∧ 0 < U ∧ 0 < T ∧ c * P - 2 * β * q ^ 5 * T + c * S * A / 2000 < 0 at hcheck
  obtain ⟨hC, hU, hT, hN⟩ := hcheck
  have ha : a = H / S := middleTail_reflectedSlope_scaled hp₀ hu
  obtain ⟨hFv, hFd, hjv, hδ, hρ, hDecay⟩ := middleTail_gap_profile hh hu hd
  change upperTailGap h (d + u) = R / r at hFv
  change upperTailGap h d = 1 / r at hFd
  change upperTailSlope h (d + u) = r / R - h at hjv
  change Real.exp (-(h * d)) * f / (upperTailGap h d * upperTailGap h (d + u)) = f * η / R at hδ
  change upperTailGap h (d + u) * x / upperTailGap h d = ρ at hρ
  change Real.exp (-((1 + h) * d)) / upperTailGap h d = ζ * q at hDecay
  have hb := middleTailMarginalLower_le hp hv
  change middleTailMarginalLower h (upperTailGap h v) ≤ b at hb
  rw [← sub_add_cancel v u, hFv] at hb
  have hLow := lowerSlope_cancel (h := h) (f := f) (q := q) hR hr hA
  change 1 + r / R + middleTailMarginalLower h (R / r) = c * R / A at hLow
  have hy : c * R / A ≤ y := by
    dsimp only [y]
    linarith only [hb, hLow]
  have hyb : b = y - 1 - r / R := by dsimp only [y]; ring
  have hlead : middleTailLeadingScore h u d a b =
      P / (S * A) + (y - c * R / A) * C / S := by
    unfold middleTailLeadingScore
    dsimp only
    rw [ha, hδ, hρ, hyb]
    exact leading_score_affine (h := h) (f := f) (q := q) (x := x)
      (S := S) (H := H) (A := A) (c := c) (y := y) hS hA hR
  have hfactor : 2 * Real.exp (-((1 + h) * d)) / (c * upperTailGap h d) = 2 * ζ * q / c := by
    rw [div_mul_eq_div_div, show 2 * Real.exp (-((1 + h) * d)) / c / upperTailGap h d =
      2 * (Real.exp (-((1 + h) * d)) / upperTailGap h d) / c by ring, hDecay]
    ring
  have hz : 2 + h - a = Z / S := by
    rw [ha]
    dsimp only [Z]
    field_simp [hS.ne'] <;> ring
  have hyv : 1 + h + upperTailSlope h (d + u) + b = y := by
    rw [hjv]
    dsimp only [y]
    ring
  have hlin : middleTailLinearScore h u d a b = 2 * ζ * q / c * (-y * U + V) / S := by
    unfold middleTailLinearScore
    dsimp only
    rw [hfactor, hyv, hz, hFd]
    change 2 * ζ * q / c * (-y * (Z / S * D + D₁) +
      ((y + q) * (Z / S * L + L₁ + L * q) + L * η) / (1 / r)) = _
    field_simp [hc.ne', hS.ne', hr.ne']
    dsimp only [U, V, M, η]
    ring
  have hupper := affine_score_upper (P := P) hq.le (Real.exp_pos (-d)).le hζbound
    hc hS hA hC.le hU.le hT hy
  have hneg : (c * P - 2 * (β * q ^ 4) * q * T) / (c * S * A) < 0 := by
    have hPos : 0 < c * S * A := by positivity
    apply div_neg_of_neg_of_pos _ hPos
    have hEq : 2 * (β * q ^ 4) * q * T = 2 * β * q ^ 5 * T := by ring
    rw [hEq]
    exact (le_add_of_nonneg_right (show 0 ≤ c * S * A / 2000 by positivity)).trans_lt hN
  apply logKernel_mixed_neg_of_middleTail_scores hp hu₀ hu₁ hd₀
  change middleTailLeadingScore h u d a b + middleTailLinearScore h u d a b < 0
  rw [hlead, hlin]
  have hT' : c * R * U - A * V = T := rfl
  rw [hT'] at hupper
  exact hupper.trans_lt hneg

end RefinedBMV.PositiveCenter
