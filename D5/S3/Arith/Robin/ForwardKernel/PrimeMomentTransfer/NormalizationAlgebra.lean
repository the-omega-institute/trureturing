/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/NormalizationAlgebra
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/NormalizationAlgebra
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive variance scales give exact cubic and fourth moment normalization identities. -/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Exact changes of normalization for cubic and fourth interval moments. -/

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer

noncomputable section
set_option autoImplicit false

/-- The cubic and fourth powers of the standard deviation are the moment normalizers. -/
theorem normalizer_powers (H L : ℝ) (hH : 0 < H) (hL : 0 < L) :
    0 < (H * L) ^ (3 / 2 : ℝ) ∧ 0 < (H * L) ^ 2 ∧
    (Real.sqrt (H * L)) ^ 3 = (H * L) ^ (3 / 2 : ℝ) ∧
    (Real.sqrt (H * L)) ^ 4 = (H * L) ^ 2 := by
  have hHL : 0 < H * L := mul_pos hH hL
  refine ⟨Real.rpow_pos_of_pos hHL _, pow_pos hHL _, ?_, ?_⟩
  · rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hHL.le]
    norm_num
  · rw [show (Real.sqrt (H * L)) ^ 4 = ((Real.sqrt (H * L)) ^ 2) ^ 2 by ring,
      Real.sq_sqrt hHL.le]

/-- The cubic formal error becomes the modulus plus the square-root scale error. -/
theorem cubic_formal_ratio (H L E : ℝ) (hH : 0 < H) (hL : 0 < L) :
    (E * (H * L) ^ (3 / 2 : ℝ) + H * L ^ 2) / (H * L) ^ (3 / 2 : ℝ) =
      E + Real.sqrt (L / H) := by
  have hQ := (normalizer_powers H L hH hL).1
  have hpow : (H * L) ^ (3 / 2 : ℝ) = (H * L) * Real.sqrt (H * L) := by
    calc
      _ = (H * L) ^ ((1 : ℝ) + 1 / 2) := by norm_num
      _ = _ := by rw [Real.rpow_add (mul_pos hH hL), Real.rpow_one, Real.sqrt_eq_rpow]
  rw [add_div, mul_div_cancel_right₀ E hQ.ne']
  congr 1
  calc
    H * L ^ 2 / (H * L) ^ (3 / 2 : ℝ) = L / Real.sqrt (H * L) := by
      rw [hpow]
      field_simp
    _ = Real.sqrt L / Real.sqrt H := by
      rw [Real.sqrt_mul hH.le, div_mul_eq_div_div, div_right_comm, Real.div_sqrt]
    _ = Real.sqrt (L / H) := (Real.sqrt_div hL.le H).symm

/-- The fourth formal error becomes the modulus plus the inverse logarithmic scale. -/
theorem fourth_formal_ratio (H L E : ℝ) (hH : 0 < H) (hL : 0 < L) :
    (E * H ^ 2 * L ^ 2 + H ^ 2 * L) / (H * L) ^ 2 = E + 1 / L := by
  field_simp

/-- The arithmetic cubic remainder has the normalized powers of the sampling and length scales. -/
theorem arithmetic_ratio_three (N H ε : ℝ) (hN : 0 < N) (hH : 0 < H)
    (hL : 0 < Real.log N) :
    (N ^ (1 / 2 + ε) * H ^ 3) / (N * (H * Real.log N) ^ (3 / 2 : ℝ)) =
      N ^ (-1 / 2 + ε) * H ^ (3 / 2 : ℝ) * (Real.log N) ^ (-3 / 2 : ℝ) := by
  have hn : N ^ (1 / 2 + ε) / N = N ^ (-1 / 2 + ε) := by
    rw [← Real.rpow_sub_one hN.ne']
    congr 1
    ring
  have hh : H ^ 3 / H ^ (3 / 2 : ℝ) = H ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_natCast H 3, ← Real.rpow_sub hH]
    norm_num
  rw [Real.mul_rpow hH.le hL.le,
    show N * (H ^ (3 / 2 : ℝ) * (Real.log N) ^ (3 / 2 : ℝ)) =
      (N * H ^ (3 / 2 : ℝ)) * (Real.log N) ^ (3 / 2 : ℝ) by ring,
    div_mul_eq_div_div, mul_div_mul_comm, hn, hh,
    show (-3 / 2 : ℝ) = -(3 / 2 : ℝ) by ring, Real.rpow_neg hL.le]
  rfl

/-- The arithmetic fourth remainder has a squared length and an inverse squared logarithm. -/
theorem arithmetic_ratio_four (N H ε : ℝ) (hN : 0 < N) (hH : 0 < H)
    (hL : 0 < Real.log N) :
    (N ^ (1 / 2 + ε) * H ^ 4) / (N * (H * Real.log N) ^ 2) =
      N ^ (-1 / 2 + ε) * H ^ 2 * (Real.log N) ^ (-2 : ℝ) := by
  have hn : N ^ (1 / 2 + ε) / N = N ^ (-1 / 2 + ε) := by
    rw [← Real.rpow_sub_one hN.ne']
    congr 1
    ring
  rw [← hn, show (-2 : ℝ) = -(2 : ℝ) by ring, Real.rpow_neg hL.le,
    Real.rpow_two]
  field_simp

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
