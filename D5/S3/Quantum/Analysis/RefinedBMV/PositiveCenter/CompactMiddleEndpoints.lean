/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactMiddleEndpoints
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Two polynomial endpoint tests for the square-root term of the middle-gap kernel. -/

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Removing the single square root from the middle-gap sign test. -/

namespace RefinedBMV.PositiveCenter

private theorem affine_lt_zero_of_endpoints {a b t l r : ℝ}
    (hl : l ≤ t) (hr : t ≤ r) (hleft : a + b * l < 0) (hright : a + b * r < 0) :
    a + b * t < 0 := by
  rcases le_total 0 b with hb | hb
  · linarith only [mul_le_mul_of_nonneg_left hr hb, hright]
  · linarith only [mul_le_mul_of_nonpos_left hl hb, hleft]

/-- A polynomial affine in each slope is negative throughout the rectangle if it is
negative at the four pairs of slope endpoints. -/
theorem bilinear_lt_zero_of_corners {a b c d α β α₀ α₁ β₀ β₁ : ℝ}
    (ha₀ : α₀ ≤ α) (ha₁ : α ≤ α₁) (hb₀ : β₀ ≤ β) (hb₁ : β ≤ β₁)
    (h₀₀ : a + b * α₀ + c * β₀ + d * α₀ * β₀ < 0)
    (h₀₁ : a + b * α₀ + c * β₁ + d * α₀ * β₁ < 0)
    (h₁₀ : a + b * α₁ + c * β₀ + d * α₁ * β₀ < 0)
    (h₁₁ : a + b * α₁ + c * β₁ + d * α₁ * β₁ < 0) :
    a + b * α + c * β + d * α * β < 0 := by
  have h₀ : a + c * β₀ + (b + d * β₀) * α < 0 :=
    affine_lt_zero_of_endpoints ha₀ ha₁ (by nlinarith only [h₀₀]) (by nlinarith only [h₁₀])
  have h₁ : a + c * β₁ + (b + d * β₁) * α < 0 :=
    affine_lt_zero_of_endpoints ha₀ ha₁ (by nlinarith only [h₀₁]) (by nlinarith only [h₁₁])
  have h : a + b * α + (c + d * α) * β < 0 :=
    affine_lt_zero_of_endpoints hb₀ hb₁ (by nlinarith only [h₀]) (by nlinarith only [h₁])
  nlinarith only [h]

/-- The upper endpoint differs from the geometric mean by a nonnegative square. -/
theorem sqrt_mul_le_middle_endpoint {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.sqrt (x * y) ≤ ((x + y) ^ 2 / 2 - (x - y) ^ 2 / 4) / (x + y) := by
  apply (le_div_iff₀ (add_pos hx hy)).2
  nlinarith only [sq_nonneg ((x + y) / 2 - Real.sqrt (x * y)), Real.sq_sqrt (mul_pos hx hy).le]

/-- The cleared polynomial tests imply negativity at the actual radical, including a common
margin. The relation for `B` allows evaluation without a subtraction of nearly equal roots. -/
theorem middle_radical_lt_of_endpoints {x y w J W M R B μ : ℝ}
    (hx : 0 < x) (hy : 0 < y)
    (hB : (x + y) ^ 2 / 2 - (x - y) ^ 2 / 4 - (x + y) * W = w * B)
    (h0 : w * M - J * W + μ < 0)
    (h1 : w * ((y ^ 2 * x) * ((x + y) * M + B * J) +
        ((x + y) ^ 2 / 2 - (x - y) ^ 2 / 4) * R) + (y ^ 2 * x) * (x + y) * μ < 0) :
    w * M - J * W + Real.sqrt (x * y) * (J + w * R / (y ^ 2 * x)) < -μ := by
  let H := y ^ 2 * x
  let S := x + y
  let A := S ^ 2 / 2 - (x - y) ^ 2 / 4
  have hH : 0 < H := mul_pos (pow_pos hy 2) hx
  have hS : 0 < S := add_pos hx hy
  have hendpoint : w * M - J * W + μ + (J + w * R / H) * (A / S) < 0 := by
    apply (mul_lt_mul_iff_left₀ (mul_pos hH hS)).mp
    simp only [mul_zero, zero_mul]
    calc
      _ = H * (S * (w * M - J * W + μ) + A * J) + A * w * R := by
        field_simp [hH.ne', hS.ne']
        <;> ring
      _ = w * (H * (S * M + B * J) + A * R) + H * S * μ := by
        change A - S * W = w * B at hB
        have h := congrArg (fun z : ℝ ↦ H * J * z) hB
        nlinarith only [h]
      _ < 0 := h1
  have hroot : Real.sqrt (x * y) ≤ A / S := sqrt_mul_le_middle_endpoint hx hy
  have h := affine_lt_zero_of_endpoints (Real.sqrt_nonneg _) hroot
    (by simpa only [mul_zero, add_zero] using h0) hendpoint
  change w * M - J * W + Real.sqrt (x * y) * (J + w * R / H) < -μ
  linarith only [h, mul_comm (J + w * R / H) (Real.sqrt (x * y))]

end RefinedBMV.PositiveCenter
