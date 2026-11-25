/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveFourth/LowPairObstruction
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The entire low adjacent pair of gaps has a negative unnormalized trace sum. -/

import Mathlib.Algebra.Ring.GeomSum
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.NoncommRing

/-! An exact integral witness for the low adjacent pair in the four-copy trace sum. -/

namespace RefinedBMV.LowPairObstruction

open Matrix

private abbrev Mat := Matrix (Fin 3) (Fin 3) ℤ

private def nodes : Fin 3 → ℤ := ![0, 3, 4]

private def A : Mat := diagonal nodes

private def factor : Mat :=
  diagonal ![4^32, 4^32, 3^32] * !![1, 0, 0; 1, 1, 0; 16, -17, 1]

private def B : Mat := factor * factorᵀ

private def geom (x y : ℤ) (s : ℕ) : ℤ :=
  if x = y then (s + 1 : ℕ) * x^s else (x^(s+1) - y^(s+1)) / (x - y)

private def leftSum (s : ℕ) : Mat := fun i j ↦ B i j * geom (nodes i) (nodes j) s

private def tailPower (s : ℕ) : Mat := diagonal fun i ↦ (nodes i)^(256-s)

private theorem geom_eq_sum (x y : ℤ) (s : ℕ) :
    geom x y s = ∑ i ∈ Finset.range (s+1), x^i * y^(s-i) := by
  by_cases h : x = y
  · subst y
    rw [geom, if_pos rfl]
    have hsum :
        (∑ i ∈ Finset.range (s+1), x^i * x^(s-i)) =
          ∑ _ ∈ Finset.range (s+1), x^s := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← pow_add, Nat.add_sub_cancel' (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hi))]
    rw [hsum]
    simp [nsmul_eq_mul]
  · rw [geom, if_neg h]
    have he := geom_sum₂_mul x y (s+1)
    rw [Nat.add_sub_cancel] at he
    rw [← he, Int.mul_ediv_cancel _ (sub_ne_zero.mpr h)]

private theorem leftSum_eq (s : ℕ) :
    leftSum s = ∑ i ∈ Finset.range (s+1), A^i * B * A^(s-i) := by
  ext i j
  change B i j * geom (nodes i) (nodes j) s = _
  rw [geom_eq_sum, Finset.mul_sum, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  simp only [A, diagonal_pow, diagonal_mul, mul_diagonal]
  ring

private theorem tailPower_eq (s : ℕ) : tailPower s = A^(256-s) := by
  simp [tailPower, A, diagonal_pow]

private theorem trace_term (s i j : ℕ) (hs : s ≤ 256) (hj : j ≤ s) :
    trace ((A^i * B * A^(s-i)) * B * A^(256-s) * (A^j * B * A^(s-j)) *
        A^(256-s) * B) =
      trace (A^i * B * A^(s-i) * B * A^(256-s+j) * B * A^(256-j) * B) := by
  have hpow : A^(s-j) * A^(256-s) = A^(256-j) := by
    rw [← pow_add]
    congr 1
    omega
  congr 1
  calc
    _ = A^i * B * A^(s-i) * B * (A^(256-s) * A^j) * B *
        (A^(s-j) * A^(256-s)) * B := by noncomm_ring
    _ = _ := by rw [hpow, ← pow_add]

private theorem trace_block_eq (s : ℕ) (hs : s ≤ 256) :
    trace (leftSum s * B * tailPower s * leftSum s * tailPower s * B) =
      ∑ i ∈ Finset.range (s+1), ∑ j ∈ Finset.range (s+1),
        trace (A^i * B * A^(s-i) * B * A^(256-s+j) * B * A^(256-j) * B) := by
  simp only [leftSum_eq, tailPower_eq, Matrix.sum_mul, Matrix.mul_sum, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact trace_term s i j hs (Nat.le_of_lt_succ (Finset.mem_range.mp hj))

set_option maxRecDepth 50000 in
set_option maxHeartbeats 20000000 in
set_option exponentiation.threshold 2048 in
/-- The exact trace of the 707264 compositions with the specified low adjacent pair. -/
theorem low_adjacent_pair_trace_negative :
    ∑ s ∈ Finset.range 128,
      trace (leftSum s * B * tailPower s * leftSum s * tailPower s * B) < 0 := by
  decide +kernel

/-- The actual ordered word sum on the canonical low adjacent pair is negative. -/
theorem low_adjacent_pair_words_negative :
    (∑ s ∈ Finset.range 128, ∑ i ∈ Finset.range (s+1), ∑ j ∈ Finset.range (s+1),
      trace (A^i * B * A^(s-i) * B * A^(256-s+j) * B * A^(256-j) * B)) < 0 := by
  have hsum : (∑ s ∈ Finset.range 128,
      trace (leftSum s * B * tailPower s * leftSum s * tailPower s * B)) = _ := by
    apply Finset.sum_congr rfl
    intro s hs
    exact trace_block_eq s (by have := Finset.mem_range.mp hs; omega)
  rw [← hsum]
  exact low_adjacent_pair_trace_negative

#print axioms low_adjacent_pair_words_negative

end RefinedBMV.LowPairObstruction
