/- GID: D5/S3/Quantum/FusionSpinChainOffsetIdentity
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The Fibonacci fusion-chain dimension has an exact integer offset identity. -/

/- Escape audit unfinished under https://github.com/the-omega-institute/trureturing/issues/27348:
   the delivered head has DTR-Unregistered/DTR-Undeclared readings and makes no
   declared_validated claim. -/

import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.FusionSpinChainOffsetIdentity

/- The integer lift of the window algebra dimension D(n) = F_(2n-1). -/
def fusionDim (n : ℤ) : ℤ := Int.fib (2 * n - 1)

/-- The exact offset identity from the Fibonacci fusion-chain cut data. -/
theorem exact_offset_identity {n k : ℤ} (h : |k| < n) :
    fusionDim (n + k) * fusionDim (n - k) - fusionDim n ^ 2 =
      Int.fib (2 * |k|) ^ 2 := by
  have hkn : -n < k := by
    have hkabs : -k ≤ |k| := neg_le_abs k
    omega
  have hkp : k < n := by
    have hkabs : k ≤ |k| := le_abs_self k
    omega
  have hnkpos : 0 < n - k := by omega
  have hxpos : 0 ≤ 2 * (n - k) - 1 := by omega
  have hxodd : Odd (2 * (n - k) - 1) := by
    refine ⟨n - k - 1, by ring⟩
  have hxoddNat : Odd (2 * (n - k) - 1).natAbs := hxodd.natAbs
  have hc := Int.fib_add_sq_sub_fib_mul_fib_add_two_mul
    (2 * (n - k) - 1) (2 * k)
  rw [hxoddNat.neg_one_pow] at hc
  have hidx1 : 2 * (n - k) - 1 + 2 * k = 2 * n - 1 := by ring
  have hidx2 : 2 * (n - k) - 1 + 2 * (2 * k) = 2 * (n + k) - 1 := by ring
  rw [hidx1, hidx2] at hc
  have hfk : Int.fib (2 * k) ^ 2 = Int.fib (2 * |k|) ^ 2 := by
    by_cases hk : 0 ≤ k
    · rw [abs_of_nonneg hk]
    · have hk' : k < 0 := lt_of_not_ge hk
      rw [abs_of_neg hk']
      have hneg : 2 * -k = -(2 * k) := by ring
      rw [hneg, Int.fib_neg]
      have heven : Even (2 * k) := ⟨k, by ring⟩
      simp [heven]
  dsimp [fusionDim]
  nlinarith [hc, hfk]

end D5.S3.Quantum.FusionSpinChainOffsetIdentity
