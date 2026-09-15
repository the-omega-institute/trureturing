/- GID: D5/S1/Recurrence/CrossingMatrixDeterminant
   generality: I
   mirror-B: D5/B/S1/Recurrence/CrossingMatrixDeterminant
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Positive powers of crossing matrices have a negative determinant obstruction. -/

import Mathlib
import D5.S0.Observation.MatrixTracePowerSum

open Matrix

namespace D5.S1.Recurrence.CrossingMatrixDeterminant

/-- The crossing matrix `C_k = !![4k+1, 1; 4k, 1]`. -/
def crossingMatrix (k : ℕ) : Matrix (Fin 2) (Fin 2) ℤ := !![4 * k + 1, 1; 4 * k, 1]

/-- The companion crossing matrix `D_k = !![2k+1, 2; 2k(k+1), 2k+1]`. -/
def dMatrix (k : ℕ) : Matrix (Fin 2) (Fin 2) ℤ := !![2 * k + 1, 2; 2 * k * (k + 1), 2 * k + 1]

/-- Escape witness (generic): any integer `2×2` matrix with trace `4k+2` and determinant `1`
has `trace (M^n) > 2` for `k, n > 0`, via the real Vieta pair and AM-GM. -/
theorem two_lt_trace_pow (M : Matrix (Fin 2) (Fin 2) ℤ) (k n : ℕ)
    (htr : M.trace = 4 * k + 2) (hdet : M.det = 1) (hk : 0 < k) (hn : 0 < n) :
    2 < (M ^ n).trace := by
  set MR : Matrix (Fin 2) (Fin 2) ℝ := M.map (Int.castRingHom ℝ) with hMR
  obtain ⟨a, b, hab_sum, hab_prod, ha1⟩ :
      ∃ a b : ℝ, a + b = 4 * (k : ℝ) + 2 ∧ a * b = 1 ∧ 1 < a := by
    refine ⟨(2 * (k : ℝ) + 1) + Real.sqrt ((2 * (k : ℝ) + 1) ^ 2 - 1),
            (2 * (k : ℝ) + 1) - Real.sqrt ((2 * (k : ℝ) + 1) ^ 2 - 1), ?_, ?_, ?_⟩
    · ring
    · have hnn : (0 : ℝ) ≤ (2 * (k : ℝ) + 1) ^ 2 - 1 := by
        nlinarith [Nat.cast_nonneg (α := ℝ) k, sq_nonneg (k : ℝ)]
      have hsq : Real.sqrt ((2 * (k : ℝ) + 1) ^ 2 - 1) ^ 2 = (2 * (k : ℝ) + 1) ^ 2 - 1 :=
        Real.sq_sqrt hnn
      linear_combination -hsq
    · have h0 : (0 : ℝ) ≤ Real.sqrt ((2 * (k : ℝ) + 1) ^ 2 - 1) := Real.sqrt_nonneg _
      have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      nlinarith [h0, hk1]
  have htrMR : Matrix.trace MR = a + b := by
    rw [hab_sum, hMR, ← AddMonoidHom.map_trace, htr]
    push_cast [Int.coe_castRingHom]; ring
  have hdetMR : Matrix.det MR = a * b := by
    rw [hab_prod, hMR,
      show M.map ⇑(Int.castRingHom ℝ) = (Int.castRingHom ℝ).mapMatrix M from rfl,
      ← RingHom.map_det, hdet, map_one]
  have h1 : Matrix.trace (MR ^ n) = a ^ n + b ^ n :=
    D5.S0.Observation.MatrixTracePowerSum.trace_pow_eq_add_pow MR a b htrMR hdetMR n
  have key : ((Matrix.trace (M ^ n) : ℤ) : ℝ) = a ^ n + b ^ n := by
    have h2 : MR ^ n = (M ^ n).map (Int.castRingHom ℝ) := by rw [hMR, Matrix.map_pow]
    rw [← h1, h2, ← AddMonoidHom.map_trace]
    simp
  have ha0 : 0 < a := lt_trans one_pos ha1
  have ht0 : 0 < a ^ n := pow_pos ha0 n
  have ht1 : 1 < a ^ n := one_lt_pow₀ ha1 hn.ne'
  have h1t : a ^ n * b ^ n = 1 := by rw [← mul_pow, hab_prod, one_pow]
  have hstrict : 0 < (a ^ n - 1) ^ 2 := pow_pos (sub_pos.mpr ht1) 2
  have hreal : (2 : ℝ) < a ^ n + b ^ n := by nlinarith [h1t, ht0, hstrict]
  have : (2 : ℝ) < ((Matrix.trace (M ^ n) : ℤ) : ℝ) := by rw [key]; exact hreal
  exact_mod_cast this

/-- TR.3 obstruction (full clause): for `k, n > 0`, the crossing matrix `C_k` satisfies
`det(C_k^n - I) = 2 - trace(C_k^n) < 0`, and both `C_k^n - I` and the companion `D_k^n - I`
are nonsingular (`det ≠ 0`). The strict sign is the escape-witness `two_lt_trace_pow`; both
companions share the characteristic data `trace = 4k+2, det = 1`. -/
theorem crossing_det_pow_sub_one (k n : ℕ) (hk : 0 < k) (hn : 0 < n) :
    (crossingMatrix k ^ n - 1).det = 2 - (crossingMatrix k ^ n).trace ∧
      (crossingMatrix k ^ n - 1).det < 0 ∧
      (crossingMatrix k ^ n - 1).det ≠ 0 ∧ (dMatrix k ^ n - 1).det ≠ 0 := by
  have det_sub_one : ∀ M : Matrix (Fin 2) (Fin 2) ℤ,
      (M - 1).det = M.det - M.trace + 1 := by
    intro M
    simp [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.sub_apply]
    ring
  have hCtrace : (crossingMatrix k).trace = 4 * k + 2 := by
    simp [crossingMatrix, Matrix.trace_fin_two]; ring
  have hCdet : (crossingMatrix k).det = 1 := by simp [crossingMatrix, Matrix.det_fin_two]
  have hDtrace : (dMatrix k).trace = 4 * k + 2 := by
    simp [dMatrix, Matrix.trace_fin_two]; ring
  have hDdet : (dMatrix k).det = 1 := by simp [dMatrix, Matrix.det_fin_two]; ring
  have hCdetn : (crossingMatrix k ^ n).det = 1 := by rw [Matrix.det_pow, hCdet, one_pow]
  have hDdetn : (dMatrix k ^ n).det = 1 := by rw [Matrix.det_pow, hDdet, one_pow]
  have hCtr : 2 < (crossingMatrix k ^ n).trace :=
    two_lt_trace_pow _ k n hCtrace hCdet hk hn
  have hDtr : 2 < (dMatrix k ^ n).trace :=
    two_lt_trace_pow _ k n hDtrace hDdet hk hn
  have heqC : (crossingMatrix k ^ n - 1).det = 2 - (crossingMatrix k ^ n).trace := by
    rw [det_sub_one, hCdetn]; ring
  have heqD : (dMatrix k ^ n - 1).det = 2 - (dMatrix k ^ n).trace := by
    rw [det_sub_one, hDdetn]; ring
  refine ⟨heqC, ?_, ?_, ?_⟩
  · rw [heqC]; omega
  · rw [heqC]; omega
  · rw [heqD]; omega

#print axioms crossing_det_pow_sub_one

end D5.S1.Recurrence.CrossingMatrixDeterminant
