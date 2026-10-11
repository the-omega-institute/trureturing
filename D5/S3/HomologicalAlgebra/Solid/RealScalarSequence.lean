/- GID: D5/S3/HomologicalAlgebra/Solid/RealScalarSequence
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/RealScalarSequence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import D5.S3.HomologicalAlgebra.Solid.Definitions

/-!
The actual continuous real scalar null sequence needed by the binary
cancellation argument for the bounded-real quotient. This is a function
into topological R, not an assertion about modules over discrete R.
New proofs, Apache-2.0. The scalar sequence is in Rodriguez Camargo,
Notes on Solid Geometry, Proposition 3.2.5.
-/

noncomputable section
open CategoryTheory LightProfinite OnePoint Filter Topology

namespace LightCondensed.Solid

/-- Dyadic weights on the breadth-first binary tree. -/
def realBinaryWeight (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ Nat.log2 (n + 1)

@[simp] theorem realBinaryWeight_zero : realBinaryWeight 0 = 1 := by
  change (1 / 2 : ℝ) ^ Nat.log2 1 = 1
  rw [Nat.log2_def 1]
  norm_num

theorem realBinaryWeight_left (n : ℕ) :
    realBinaryWeight (2 * n + 1) = realBinaryWeight n / 2 := by
  have hn : 2 ≤ 2 * n + 1 + 1 := by omega
  have hd : (2 * n + 1 + 1) / 2 = n + 1 := by omega
  simp only [realBinaryWeight, Nat.log2_def (2 * n + 1 + 1), if_pos hn, hd,
    pow_succ]
  ring

theorem realBinaryWeight_right (n : ℕ) :
    realBinaryWeight (2 * n + 2) = realBinaryWeight n / 2 := by
  have hn : 2 ≤ 2 * n + 2 + 1 := by omega
  have hd : (2 * n + 2 + 1) / 2 = n + 1 := by omega
  simp only [realBinaryWeight, Nat.log2_def (2 * n + 2 + 1), if_pos hn, hd,
    pow_succ]
  ring

theorem realBinaryWeight_children (n : ℕ) :
    realBinaryWeight (2 * n + 1) + realBinaryWeight (2 * n + 2) = realBinaryWeight n := by
  rw [realBinaryWeight_left, realBinaryWeight_right]
  ring

/-- The binary depth tends to infinity; no bounded-index argument is used. -/
theorem realBinaryDepth_tendsto :
    Tendsto (fun n : ℕ => Nat.log2 (n + 1)) atTop atTop := by
  apply tendsto_atTop.2
  intro k
  refine eventually_atTop.2 ⟨2 ^ k, ?_⟩
  intro n hn
  exact (Nat.le_log2 (Nat.succ_ne_zero n)).2 (by omega)

theorem realBinaryWeight_tendsto : Tendsto realBinaryWeight atTop (𝓝 (0 : ℝ)) := by
  exact (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).comp realBinaryDepth_tendsto

/-- The scalar map on the actual convergent sequence, with value zero at infinity. -/
def realBinaryScalar : C(ℕ∪{∞}, ℝ) where
  toFun := OnePoint.rec 0 realBinaryWeight
  continuous_toFun := by
    rw [OnePoint.continuous_iff_from_nat]
    exact realBinaryWeight_tendsto

@[simp] theorem realBinaryScalar_infty : realBinaryScalar ∞ = 0 := rfl

@[simp] theorem realBinaryScalar_nat (n : ℕ) :
    realBinaryScalar (n : ℕ∪{∞}) = realBinaryWeight n := rfl

end LightCondensed.Solid
