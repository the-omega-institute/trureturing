/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMRadialScalars
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMRadialScalars
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact signed radial factors for the original Laurent channels. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalFourMActualChart

/-! Laurent and physical channel factors at the original detector weight. -/

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMRadialScalars

private theorem neg_one_zpow_even_shift (p q : ℤ) :
    (-1 : ℂ) ^ (p + 2 * q) = (-1 : ℂ) ^ p := by
  rw [zpow_add₀ (by norm_num), zpow_mul]
  norm_num

/-- The three radial factors have one common nonzero factor once the
original B differential is multiplied by its signed monomial. -/
theorem radial_factors (H K L s N : ℤ) (hN : N = H + K + L - s - 2)
    {x : ℂ} (hx : x ≠ 0) (h₁ : 1 - x ≠ 0) :
    let common := x ^ (-s - 5) * (1 - x) ^ (3 : ℕ)
    x ^ (N - L - 3) * (1 - x) ^ (3 - H - K) =
      common * ((1 - x) / x) ^ (-H - K) ∧
    (-1 : ℂ) ^ (H + N) * x ^ (-K - L - 3) * (1 - x) ^ (3 : ℕ) =
      common * x ^ (s + 2) * ((-1 : ℂ) ^ (s + 2) * (-x) ^ (-K - L)) ∧
    (-1 : ℂ) ^ (K + N) * x ^ (N - K - 3) * (1 - x) ^ (3 : ℕ) =
      common * ((-1 : ℂ) ^ (s + 2) * (-x⁻¹) ^ (-H - L)) := by
  dsimp only
  have hB : (-1 : ℂ) ^ (H + N) = (-1 : ℂ) ^ (s + 2 + (-K - L)) := by
    rw [show H + N = s + 2 + (-K - L) + 2 * (H + K + L - s - 2) by omega,
      neg_one_zpow_even_shift]
  have hD : (-1 : ℂ) ^ (K + N) = (-1 : ℂ) ^ (s + 2 + (-H - L)) := by
    rw [show K + N = s + 2 + (-H - L) + 2 * (H + K + L - s - 2) by omega,
      neg_one_zpow_even_shift]
  have hAexp : N - L - 3 = (-s - 5) + -(-H - K) := by omega
  have hDexp : N - K - 3 = (-s - 5) + -(-H - L) := by omega
  have hNeg (z : ℂ) (p : ℤ) : (-z) ^ p = (-1 : ℂ) ^ p * z ^ p := by
    simpa only [neg_one_mul] using (mul_zpow (a := (-1 : ℂ)) (b := z) p)
  constructor
  · rw [hAexp, zpow_add₀ hx, show 3 - H - K = 3 + (-H - K) by omega,
      zpow_add₀ h₁, div_eq_mul_inv, mul_zpow, inv_zpow, ← zpow_neg,
      show (3 : ℤ) = (3 : ℕ) by norm_num, zpow_natCast]
    ring
  · constructor
    · rw [hB, zpow_add₀ (by norm_num), hNeg x (-K - L)]
      rw [show -K - L - 3 = ((-s - 5) + (s + 2)) + (-K - L) by omega,
        zpow_add₀ hx, zpow_add₀ hx]
      ring
    · rw [hD, zpow_add₀ (by norm_num), hDexp, zpow_add₀ hx,
        hNeg x⁻¹ (-H - L), inv_zpow, ← zpow_neg]
      ring


open Complex
open OriginalFourMActualChart (Chart Puncture parameter scaleRoot chosen_roots)
open private rootB rootZ rootB_sq rootZ_sq scale_ne from
  D5.S3.VertexAlgebra.TwistedGround.OriginalFourMActualChart

private theorem odd_inverse_power {z : ℂ} (hz : z ≠ 0) (H : ℤ) :
    (z⁻¹) ^ (2 * H - 3) = z * (z ^ (2 : ℕ)) ^ (1 - H) := by
  rw [inv_zpow, ← zpow_neg, ← zpow_natCast, ← zpow_mul]
  conv_rhs => lhs; rw [← zpow_one z]
  rw [← zpow_add₀ hz]
  congr 1
  norm_num
  ring

private theorem neg_one_zpow_flip (p : ℤ) : (-1 : ℂ) ^ (1 - p) = -((-1 : ℂ) ^ p) := by
  rw [show 1 - p = (1 + p) + 2 * (-p) by ring, neg_one_zpow_even_shift,
    zpow_add₀ (by norm_num), zpow_one, neg_one_mul]

private noncomputable def inverseScaleProduct (c : Chart) (x : ℝ) (H K L N : ℤ) : ℂ :=
  (scaleRoot c x .P)⁻¹ ^ (2 * H - 3) * (scaleRoot c x .Q)⁻¹ ^ (2 * K - 3) *
    (scaleRoot c x .R)⁻¹ ^ (2 * L - 3) * (scaleRoot c x .S)⁻¹ ^ (2 * N - 3)

/-- The original four scale roots and cubic factor yield the two radial
channel prefactors. The sign on the B detector is the odd relative sign. -/
theorem radial_chart_factors {x : ℝ} (hx : 0 < x) (hx₁ : x < 1) (H K L N : ℤ) :
    ((-1 : ℂ) ^ K * (1 - parameter .A (x : ℂ)) ^ (3 : ℕ) *
      inverseScaleProduct .A x H K L N =
      -I * ((x : ℂ) ^ (N - L - 3) * (1 - (x : ℂ)) ^ (3 - H - K))) ∧
    ((-1 : ℂ) ^ L * (-(1 - parameter .B (x : ℂ)) ^ (3 : ℕ)) *
      inverseScaleProduct .B x H K L N =
      -I * ((-1 : ℂ) ^ (H + N) * (x : ℂ) ^ (3 - K - L) *
        (1 - (x : ℂ)) ^ (3 : ℕ))) := by
  let X : ℂ := x
  let Y : ℂ := 1 - X
  have hX : X ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hY : Y ≠ 0 := sub_ne_zero.mpr (ofReal_ne_one.mpr hx₁.ne).symm
  have hrX : rootZ x ^ 2 = X := rootZ_sq hx
  have hrY : rootB x ^ 2 = Y := rootB_sq hx₁
  have hz : rootZ x ≠ 0 := fun h => hX (by rw [← hrX, h]; norm_num)
  have hA : 1 - parameter .A (x : ℂ) = X⁻¹ := by simp [parameter, X]
  have hB : 1 - parameter .B (x : ℂ) = Y := rfl
  have hodd (c : Chart) (p : Puncture) (J : ℤ) :
      (scaleRoot c x p)⁻¹ ^ (2 * J - 3) =
        scaleRoot c x p * (scaleRoot c x p ^ (2 : ℕ)) ^ (1 - J) :=
    odd_inverse_power (fun h => scale_ne hx hx₁ c p (by
      rw [← (chosen_roots hx hx₁ c p).1, h, zero_pow (by decide)])) J
  have hneg (z : ℂ) (d : ℤ) : (-z) ^ d = (-1 : ℂ) ^ d * z ^ d := by
    simpa only [neg_one_mul] using mul_zpow (a := (-1 : ℂ)) (b := z) d
  constructor
  · unfold inverseScaleProduct
    simp only [hodd]
    rw [hA]
    simp only [scaleRoot, mul_pow, I_sq, hrX, hrY, inv_pow, neg_one_mul, inv_zpow]
    rw [hneg Y (1 - K), neg_one_zpow_flip, ← zpow_neg]
    calc
      _ = -I * (X ^ (-(3 : ℤ)) * X ^ (1 - L) * X ^ (-(1 - N)) *
          (Y ^ (1 : ℤ) * Y ^ (1 - H) * Y ^ (1 - K))) := by
        rw [← hrY, zpow_one, show X ^ (-(3 : ℤ)) = (X ^ (3 : ℕ))⁻¹ by rfl]
        have hsign : (-1 : ℂ) ^ K * (-1 : ℂ) ^ K = 1 := by
          rw [← zpow_add₀ (by norm_num), show K + K = 0 + 2 * K by ring,
            neg_one_zpow_even_shift, zpow_zero]
        have hinv : rootZ x * (rootZ x)⁻¹ = 1 := mul_inv_cancel₀ hz
        linear_combination (-I * ((X ^ 3)⁻¹ * X ^ (1 - L) * X ^ (-(1 - N))) *
          ((rootB x) ^ 2 * ((rootB x) ^ 2) ^ (1 - H) * ((rootB x) ^ 2) ^ (1 - K))) *
          (congrArg₂ (· * ·) hsign hinv)
      _ = _ := by
        rw [← zpow_add₀ hX, ← zpow_add₀ hX, ← zpow_add₀ hY, ← zpow_add₀ hY]
        congr 2 <;> first | rfl | (ring_nf <;> rfl)
  · unfold inverseScaleProduct
    simp only [hodd]
    rw [hB]
    simp only [scaleRoot, mul_pow, I_sq, hrX, neg_one_mul]
    rw [hneg X (1 - L)]
    have hsign : (-1 : ℂ) ^ L * ((-1 : ℂ) ^ (1 - H) *
        (-1 : ℂ) ^ (1 - L) * (-1 : ℂ) ^ (1 - N)) =
        -((-1 : ℂ) ^ (H + N)) := by
      simp only [← zpow_add₀ (show (-1 : ℂ) ≠ 0 by norm_num)]
      rw [show L + (1 - H + (1 - L) + (1 - N)) = (1 - (H + N)) + 2 * 1 by ring,
        neg_one_zpow_even_shift, neg_one_zpow_flip]
    calc
      _ = I * ((-1 : ℂ) ^ L * ((-1 : ℂ) ^ (1 - H) *
          (-1 : ℂ) ^ (1 - L) * (-1 : ℂ) ^ (1 - N))) *
          (X ^ (1 : ℤ) * X ^ (1 - K) * X ^ (1 - L)) * Y ^ (3 : ℕ) := by
        rw [zpow_one, ← hrX]
        linear_combination
          -(((-1 : ℂ) ^ L) * Y ^ (3 : ℕ) * ((-1 : ℂ) ^ (1 - H) *
            (rootZ x ^ 2) ^ (1 - K) * ((-1 : ℂ) ^ (1 - L) *
              (rootZ x ^ 2) ^ (1 - L)) * (-1 : ℂ) ^ (1 - N))) *
          I * rootZ x ^ 2 * (Complex.I_sq : I ^ 2 = -1)
      _ = _ := by
        rw [hsign, ← zpow_add₀ hX, ← zpow_add₀ hX,
          show 1 + (1 - K) + (1 - L) = 3 - K - L by ring]
        ring

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMRadialScalars
