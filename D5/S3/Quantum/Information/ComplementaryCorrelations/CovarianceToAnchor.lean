/- GID: D5/S3/Quantum/Information/ComplementaryCorrelations/CovarianceToAnchor
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/ComplementaryCorrelations/CovarianceToAnchor
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A Bloch-vector estimate turns local covariance control into the joint Simpson bound. -/

import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
Omega original.

The scalar two-slot Simpson gap for qubit Bloch coordinates. The two
endpoint variances are V and W, the two midpoint variances are H and K,
the endpoint cross moment is c + id, and the midpoint cross moment is m.
-/

namespace Omega.CovarianceToAnchor

noncomputable section

/-- The local covariance hypotheses (1)–(3). -/
structure LocalCovariance (V W H K c d m : ℝ) : Prop where
  H_nonneg : 0 ≤ H
  H_le_V : H ≤ V
  K_nonneg : 0 ≤ K
  K_le_W : K ≤ W
  endpoint : c ^ 2 + d ^ 2 ≤ V * W
  midpoint : m ^ 2 ≤ H * K
  imag_Q : d ^ 2 ≤ (V - H) * (W + K)
  imag_R : d ^ 2 ≤ (W - K) * (V + H)

/-- The unscaled gap G of (4). The sign of the imaginary cross term is positive. -/
def simpsonGap (V W H K c d m t x y z : ℝ) : ℝ :=
  (2 / 3) *
    ((1 - z ^ 2) * V + (1 - x ^ 2) * W -
      t * (1 - z ^ 2 / (1 + t)) * H - t * (1 - x ^ 2 / (1 + t)) * K +
      x * z * (c + 2 * (t / (1 + t)) * m) + y * d)

/-- The denominator-free cubic P of (6). -/
def simpsonCubic (V W H K c d m t : ℝ) : ℝ :=
  let I := V - H
  let J := W - K
  let δ := I + J
  2 * t ^ 2 * δ * (V + W + t * δ) +
    4 * (1 - t) * (V + t * I) * (W + t * J) -
    (1 - t) * ((1 + t) * c + 2 * t * m) ^ 2 - (1 + t) * d ^ 2

private theorem cross_le {V W H K c d m : ℝ} (h : LocalCovariance V W H K c d m) :
    2 * c * m ≤ V * K + W * H := by
  have hV := h.H_nonneg.trans h.H_le_V
  have hW := h.K_nonneg.trans h.K_le_W
  have hc : c ^ 2 ≤ V * W :=
    (le_add_of_nonneg_right (sq_nonneg d)).trans h.endpoint
  have hProd := mul_le_mul hc h.midpoint (sq_nonneg m) (mul_nonneg hV hW)
  have hSquare : (2 * c * m) ^ 2 ≤ (V * K + W * H) ^ 2 := by
    calc
      (2 * c * m) ^ 2 = 4 * (c ^ 2 * m ^ 2) := by ring
      _ ≤ 4 * (V * W * (H * K)) := mul_le_mul_of_nonneg_left hProd (by norm_num)
      _ ≤ (V * K + W * H) ^ 2 := by nlinarith only [sq_nonneg (V * K - W * H)]
  exact (abs_le_of_sq_le_sq' hSquare
    (add_nonneg (mul_nonneg hV h.K_nonneg) (mul_nonneg hW h.H_nonneg))).2

/-- Equations (6), (8) and (9). Elevating to degree four gives five
nonnegative coefficients from (1)–(3) and (L) with coefficient 7/4. -/
theorem simpson_cubic_nonneg {V W H K c d m t : ℝ}
    (h : LocalCovariance V W H K c d m)
    (hL : (c + m) ^ 2 + (7 / 4) * d ^ 2 ≤ (3 * V - 2 * H) * (3 * W - 2 * K))
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ simpsonCubic V W H K c d m t := by
  let I := V - H
  let J := W - K
  let B₀ := 4 * V * W - c ^ 2 - d ^ 2
  let B₁ := 2 * V * W + V * J + W * I - m * c - c ^ 2 - d ^ 2
  let B₂ := (4 * V * W + 2 * V * I + 6 * V * J + 6 * W * I +
    2 * W * J + 4 * I * J - 4 * (c + m) ^ 2 - 5 * d ^ 2) / 6
  let B₃ := ((I + J) * (V + W + I + J) - d ^ 2) / 2
  let C₂ := 2 * B₁ + 3 * B₂
  let C₃ := 3 * B₂ + 2 * B₃
  have hV := h.H_nonneg.trans h.H_le_V
  have hW := h.K_nonneg.trans h.K_le_W
  have hI : 0 ≤ I := sub_nonneg.mpr h.H_le_V
  have hJ : 0 ≤ J := sub_nonneg.mpr h.K_le_W
  have hIV : I ≤ V := sub_le_self _ h.H_nonneg
  have hJW : J ≤ W := sub_le_self _ h.K_nonneg
  have hCM : 2 * c * m ≤ 2 * V * W - W * I - V * J := by
    calc
      2 * c * m ≤ V * K + W * H := cross_le h
      _ = 2 * V * W - W * I - V * J := by dsimp [I, J]; ring
  have hDiag : (c + m) ^ 2 + (7 / 4) * d ^ 2 ≤ (V + 2 * I) * (W + 2 * J) := by
    convert hL using 1 <;> dsimp [I, J] <;> ring
  have hd : d ^ 2 ≤ W * I + V * J := by
    have hQ : d ^ 2 ≤ I * (W + K) := h.imag_Q
    have hR : d ^ 2 ≤ J * (V + H) := h.imag_R
    have hIK := mul_le_mul_of_nonneg_left h.K_le_W hI
    have hJH := mul_le_mul_of_nonneg_left h.H_le_V hJ
    nlinarith only [hQ, hR, hIK, hJH]
  have hCross : 2 * c ^ 2 + 2 * c * m + d ^ 2 ≤ 4 * V * W - W * I - V * J := by
    nlinarith only [hCM, h.endpoint, sq_nonneg d]
  have hb₀ : 0 ≤ B₀ := by
    dsimp [B₀]
    nlinarith only [h.endpoint, mul_nonneg hV hW]
  have hb₁ : 0 ≤ B₁ := by
    dsimp [B₁]
    nlinarith only [h.endpoint, hCM, mul_nonneg hV hJ, mul_nonneg hW hI]
  have hb₃ : 0 ≤ B₃ := by
    dsimp [B₃]
    nlinarith only [hd, mul_nonneg hV hI, mul_nonneg hW hJ, sq_nonneg (I + J)]
  have hc₂ : 0 ≤ C₂ := by
    have hVI := mul_le_mul_of_nonneg_right hIV hI
    have hWJ := mul_le_mul_of_nonneg_right hJW hJ
    have hVJ := mul_le_mul_of_nonneg_right hIV hJ
    have hWI := mul_le_mul_of_nonneg_right hJW hI
    calc
      0 ≤ (I - J) ^ 2 := sq_nonneg _
      _ ≤ V * I + W * J + 2 * V * J + 2 * W * I - 6 * I * J := by
        nlinarith only [hVI, hWJ, hVJ, hWI]
      _ ≤ C₂ := by
        dsimp [C₂, B₁, B₂]
        nlinarith only [hDiag, hCross]
  have hc₃ : 0 ≤ C₃ := by
    have hVI := mul_le_mul_of_nonneg_right hIV hI
    have hWJ := mul_le_mul_of_nonneg_right hJW hJ
    calc
      0 ≤ I ^ 2 + J ^ 2 + 2 * (I - J) ^ 2 := by positivity
      _ ≤ 2 * V * I + 2 * W * J + I ^ 2 + J ^ 2 - 4 * I * J := by
        nlinarith only [hVI, hWJ]
      _ ≤ C₃ := by
        dsimp [C₃, B₂, B₃]
        nlinarith only [hDiag]
  let u : Set.Icc (0 : ℝ) 1 := ⟨t, ht0, ht1⟩
  have hCubic : simpsonCubic V W H K c d m t =
      B₀ * (1 - t) ^ 3 + 4 * B₁ * t * (1 - t) ^ 2 +
        6 * B₂ * t ^ 2 * (1 - t) + 4 * B₃ * t ^ 3 := by
    unfold simpsonCubic
    dsimp [B₀, B₁, B₂, B₃, I, J]
    ring
  rw [hCubic]
  have hElevated :
      B₀ * (1 - t) ^ 3 + 4 * B₁ * t * (1 - t) ^ 2 +
        6 * B₂ * t ^ 2 * (1 - t) + 4 * B₃ * t ^ 3 =
      B₀ * bernstein 4 0 u + ((B₀ + 4 * B₁) / 4) * bernstein 4 1 u +
        (C₂ / 3) * bernstein 4 2 u + (C₃ / 2) * bernstein 4 3 u +
        (4 * B₃) * bernstein 4 4 u := by
    norm_num [bernstein_apply, Nat.choose, u, C₂, C₃]
    ring
  rw [hElevated]
  have h₁ := div_nonneg (add_nonneg hb₀ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hb₁))
    (by norm_num : (0 : ℝ) ≤ 4)
  have h₂ := div_nonneg hc₂ (by norm_num : (0 : ℝ) ≤ 3)
  have h₃ := div_nonneg hc₃ (by norm_num : (0 : ℝ) ≤ 2)
  have h₄ := mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hb₃
  exact add_nonneg
    (add_nonneg
      (add_nonneg (add_nonneg (mul_nonneg hb₀ bernstein_nonneg) (mul_nonneg h₁ bernstein_nonneg))
        (mul_nonneg h₂ bernstein_nonneg))
      (mul_nonneg h₃ bernstein_nonneg))
    (mul_nonneg h₄ bernstein_nonneg)

/-- A two-coordinate consequence of the squared finite Cauchy–Schwarz bound. -/
private theorem dot_le_of_sq_le {a b u v A U : ℝ}
    (hA : 0 ≤ A) (hU : 0 ≤ U) (ha : a ^ 2 + b ^ 2 ≤ A ^ 2)
    (hu : u ^ 2 + v ^ 2 ≤ U ^ 2) : a * u + b * v ≤ A * U := by
  have hCS : (a * u + b * v) ^ 2 ≤ (a ^ 2 + b ^ 2) * (u ^ 2 + v ^ 2) := by
    simpa [Fin.sum_univ_two] using
      (Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 2)) ![a, b] ![u, v])
  have hBound := mul_le_mul ha hu (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg A)
  have hSquare : (a * u + b * v) ^ 2 ≤ (A * U) ^ 2 := by
    rw [mul_pow]
    exact hCS.trans hBound
  exact (abs_le_of_sq_le_sq' hSquare (mul_nonneg hA hU)).2

/-- A homogeneous Bloch-direction bound from the trace and anisotropy estimates. -/
private theorem orientation_nonneg {A U a b d R x y z : ℝ}
    (hR : R = x ^ 2 + y ^ 2 + z ^ 2) (hA : 0 ≤ A) (hTrace : R * U ≤ A)
    (hNorm : R ^ 2 * (a ^ 2 + b ^ 2) + R * d ^ 2 ≤ A ^ 2) :
    0 ≤ A - (U * (x ^ 2 + z ^ 2) + a * (z ^ 2 - x ^ 2) - 2 * b * x * z) / 2 + y * d := by
  have hR0 : 0 ≤ R := by rw [hR]; positivity
  rcases hR0.eq_or_lt with hzero | hRpos
  · have hx : x = 0 := sq_eq_zero_iff.mp (le_antisymm (by
      linarith only [hR, hzero, sq_nonneg y, sq_nonneg z]) (sq_nonneg x))
    have hy : y = 0 := sq_eq_zero_iff.mp (le_antisymm (by
      linarith only [hR, hzero, sq_nonneg x, sq_nonneg z]) (sq_nonneg y))
    have hz : z = 0 := sq_eq_zero_iff.mp (le_antisymm (by
      linarith only [hR, hzero, sq_nonneg x, sq_nonneg y]) (sq_nonneg z))
    simpa [hx, hy, hz] using hA
  let s := Real.sqrt (a ^ 2 + b ^ 2)
  let r := Real.sqrt R
  have hs : s ^ 2 = a ^ 2 + b ^ 2 := Real.sq_sqrt (by positivity)
  have hr : r ^ 2 = R := Real.sq_sqrt hR0
  have hAngle : a * (z ^ 2 - x ^ 2) - 2 * b * x * z ≤ s * (x ^ 2 + z ^ 2) := by
    have hB : (z ^ 2 - x ^ 2) ^ 2 + (-2 * x * z) ^ 2 ≤ (x ^ 2 + z ^ 2) ^ 2 := by
      apply le_of_eq
      ring
    have hh := dot_le_of_sq_le (show 0 ≤ s from Real.sqrt_nonneg _)
      (add_nonneg (sq_nonneg x) (sq_nonneg z)) hs.ge hB
    nlinarith only [hh]
  have hNorm' : (R * s) ^ 2 + (r * d) ^ 2 ≤ A ^ 2 := by
    rw [mul_pow, mul_pow, hs, hr]
    exact hNorm
  have hY : (R - y ^ 2) ^ 2 + (-2 * r * y) ^ 2 ≤ (R + y ^ 2) ^ 2 := by
    apply le_of_eq
    calc
      _ = (R - y ^ 2) ^ 2 + 4 * r ^ 2 * y ^ 2 := by ring
      _ = (R + y ^ 2) ^ 2 := by rw [hr]; ring
  have hDot := dot_le_of_sq_le hA (add_nonneg hR0 (sq_nonneg y)) hNorm' hY
  have hPolar : (R * s) * (R - y ^ 2) - 2 * R * y * d ≤ A * (R + y ^ 2) := by
    calc
      _ = (R * s) * (R - y ^ 2) - 2 * r ^ 2 * y * d := by rw [hr]
      _ = (R * s) * (R - y ^ 2) + (r * d) * (-2 * r * y) := by ring
      _ ≤ _ := hDot
  have hScaledAngle := mul_le_mul_of_nonneg_left hAngle hR0
  have hScaledTrace := mul_le_mul_of_nonneg_right hTrace (add_nonneg (sq_nonneg x) (sq_nonneg z))
  have hPerp : x ^ 2 + z ^ 2 = R - y ^ 2 := by linarith only [hR]
  rw [hPerp] at hScaledAngle hScaledTrace
  have hQuadratic :
      R * (U * (x ^ 2 + z ^ 2) + a * (z ^ 2 - x ^ 2) - 2 * b * x * z) ≤
        A * (R - y ^ 2) + (R * s) * (R - y ^ 2) := by
    calc
      _ = (R * U) * (R - y ^ 2) +
          R * (a * (z ^ 2 - x ^ 2) - 2 * b * x * z) := by rw [hPerp]; ring
      _ ≤ _ := by nlinarith only [hScaledAngle, hScaledTrace]
  apply nonneg_of_mul_nonneg_right _ hRpos
  nlinarith only [hQuadratic, hPolar]

/-- The complete scalar Simpson gap from (1)–(3) and (L), with the closed
Bloch constraint. This includes t = 0, t = 1, and either slot variance zero. -/
theorem simpson_gap_nonneg {V W H K c d m t x y z : ℝ}
    (h : LocalCovariance V W H K c d m)
    (hL : (c + m) ^ 2 + (7 / 4) * d ^ 2 ≤ (3 * V - 2 * H) * (3 * W - 2 * K))
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hBloch : x ^ 2 + y ^ 2 + z ^ 2 = 1 - t ^ 2) :
    0 ≤ simpsonGap V W H K c d m t x y z := by
  let κ := t / (1 + t)
  let R := 1 - t ^ 2
  let A := V + W - t * (H + K)
  let U := V + W - κ * (H + K)
  let a := V - W - κ * (H - K)
  let b := c + 2 * κ * m
  let δ := V - H + (W - K)
  have htDen : 1 + t ≠ 0 := ne_of_gt (by linarith only [ht0])
  have hδ : 0 ≤ δ := add_nonneg (sub_nonneg.mpr h.H_le_V) (sub_nonneg.mpr h.K_le_W)
  have hA : 0 ≤ A := by
    have htM := mul_le_mul_of_nonneg_right ht1 (add_nonneg h.H_nonneg h.K_nonneg)
    dsimp [A]
    nlinarith only [htM, h.H_le_V, h.K_le_W]
  have hTraceEq : R * U = A - t ^ 2 * δ := by
    dsimp [R, U, A, κ, δ]
    field_simp [htDen] <;> ring
  have hTrace : R * U ≤ A :=
    hTraceEq.le.trans (sub_le_self _ (mul_nonneg (sq_nonneg _) hδ))
  have ha : R * a = (1 - t) * ((1 + t) * (V - W) - t * (H - K)) := by
    dsimp [R, a, κ]
    field_simp [htDen] <;> ring
  have hb : R * b = (1 - t) * ((1 + t) * c + 2 * t * m) := by
    dsimp [R, b, κ]
    field_simp [htDen] <;> ring
  have hQ : A ^ 2 - (R ^ 2 * (a ^ 2 + b ^ 2) + R * d ^ 2) =
      t ^ 4 * δ ^ 2 + (1 - t) * simpsonCubic V W H K c d m t := by
    calc
      _ = A ^ 2 - ((R * a) ^ 2 + (R * b) ^ 2 + R * d ^ 2) := by ring
      _ = _ := by
        rw [ha, hb]
        unfold simpsonCubic
        dsimp [A, R, δ]
        ring
  have hQ0 : 0 ≤ t ^ 4 * δ ^ 2 + (1 - t) * simpsonCubic V W H K c d m t :=
    add_nonneg (mul_nonneg (pow_nonneg ht0 _) (sq_nonneg δ))
      (mul_nonneg (sub_nonneg.mpr ht1) (simpson_cubic_nonneg h hL ht0 ht1))
  have hNorm : R ^ 2 * (a ^ 2 + b ^ 2) + R * d ^ 2 ≤ A ^ 2 := by
    rw [← sub_nonneg, hQ]
    exact hQ0
  have hGap := orientation_nonneg hBloch.symm hA hTrace hNorm
  have hGapEq : simpsonGap V W H K c d m t x y z =
      (2 / 3) *
        (A - (U * (x ^ 2 + z ^ 2) + a * (z ^ 2 - x ^ 2) - 2 * b * x * z) / 2 + y * d) := by
    unfold simpsonGap
    dsimp [A, U, a, b, κ]
    field_simp [htDen] <;> ring
  rw [hGapEq]
  exact mul_nonneg (by norm_num) hGap

end

end Omega.CovarianceToAnchor

#print axioms Omega.CovarianceToAnchor.simpson_cubic_nonneg
#print axioms Omega.CovarianceToAnchor.simpson_gap_nonneg
