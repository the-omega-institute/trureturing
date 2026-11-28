import OmegaBuild.Commands
import OmegaMath.Combinatorics.Graph.HilbertTetrahedronGeometry
import OmegaMath.Combinatorics.Graph.HilbertTriangleInsertionAlgebra
import OmegaMath.Combinatorics.Graph.HilbertChildFace

compile_only_with_mathlib

/-! Omega original.

# Variance and centered residual arrays for three candidates
-/

open scoped InnerProductSpace

namespace HilbertTriangleInsertion

open HilbertTetrahedronGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A three-candidate radius is controlled by both a specified short edge and the total energy. -/
theorem center_bounds (y : Fin 3 → E) (hdiam : ∀ i j, ‖y i - y j‖ ^ 2 ≤ B) :
    ∃ c q, 0 ≤ q ∧ (∀ i, ‖y i - c‖ ^ 2 ≤ q) ∧
      (∀ i j, i ≠ j → q * (4 * B - ‖y i - y j‖ ^ 2) ≤ B ^ 2) ∧
      (B / 4 < q → q * (6 * B -
        (‖y 0 - y 1‖ ^ 2 + ‖y 1 - y 2‖ ^ 2 + ‖y 2 - y 0‖ ^ 2)) ≤ B ^ 2) := by
  obtain ⟨c⟩ := exists_candidate_data y
  let a := c.w 0
  let b := c.w 1
  let d := c.w 2
  let x := ‖y 0 - y 1‖ ^ 2
  let v := ‖y 1 - y 2‖ ^ 2
  let z := ‖y 2 - y 0‖ ^ 2
  have h₀ := c.w_nonneg 0
  have h₁ := c.w_nonneg 1
  have h₂ := c.w_nonneg 2
  have hB : 0 ≤ B := (sq_nonneg _).trans (hdiam 0 1)
  have hs : a + b + d = 1 := by
    have h := c.w_sum
    rw [Fin.sum_univ_three] at h
    exact h
  have hq : c.q = a * b * x + b * d * v + d * a * z := by
    have h := FiniteHilbertJung.pair_sq y c.w c.w_sum
    rw [c.variance_eq] at h
    simp only [Fin.sum_univ_three, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add, add_zero] at h
    rw [norm_sub_rev (y 1) (y 0), norm_sub_rev (y 0) (y 2), norm_sub_rev (y 2) (y 1)] at h
    change a * b * x + a * d * z + (b * a * x + b * d * v) + (d * a * z + d * b * v) = 2 * c.q at h
    nlinarith only [h]
  have hx : x ≤ B := hdiam 0 1
  have hv : v ≤ B := hdiam 1 2
  have hz : z ≤ B := hdiam 2 0
  have hx₀ : 0 ≤ x := sq_nonneg _
  have hv₀ : 0 ≤ v := sq_nonneg _
  have hz₀ : 0 ≤ z := sq_nonneg _
  refine ⟨c.c, c.q, c.q_nonneg, c.norm_sq_le, ?_, ?_⟩
  · have e0 := one_edge_variance h₀ h₁ h₂ hs hx₀ hx hv hz hB hq
    have e1 := one_edge_variance h₁ h₂ h₀ (by linarith only [hs]) hv₀ hv hz hx hB
      (show c.q = b * d * v + d * a * z + a * b * x by linarith only [hq])
    have e2 := one_edge_variance h₂ h₀ h₁ (by linarith only [hs]) hz₀ hz hx hv hB
      (show c.q = d * a * z + a * b * x + b * d * v by linarith only [hq])
    intro i j hij
    fin_cases i <;> fin_cases j <;> first
      | exact (hij rfl).elim
      | exact e0
      | exact e1
      | exact e2
      | (rw [norm_sub_rev]; first | exact e0 | exact e1 | exact e2)
  · intro hlarge
    have hrow (i : Fin 3) : ∑ j, c.w j * ‖y i - y j‖ ^ 2 = 2 * c.q := by
      have h := c.three_contacts hB hdiam hlarge i
      have hslack : c.slack i = 0 := by linarith only [c.slack_eq i, h]
      rw [c.weighted_row, hslack, sub_zero]
    have row₀ := hrow 0
    have row₁ := hrow 1
    have row₂ := hrow 2
    simp only [Fin.sum_univ_three, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0),
      mul_zero, zero_add, add_zero] at row₀ row₁ row₂
    rw [norm_sub_rev (y 0) (y 2)] at row₀
    rw [norm_sub_rev (y 1) (y 0)] at row₁
    rw [norm_sub_rev (y 2) (y 1)] at row₂
    exact contact_sum_bound h₀ h₁ h₂ hs hx hv hz hB row₀ row₁ row₂

/-- Removing the opposite means preserves the sum of the arrays. The
remaining Cauchy–Schwarz term is bounded by the product at zero holonomy. -/
theorem centered_minkowski (a b c x y z : E) (hs : (a + b + c) + (x + y + z) = 0)
    {T : ℝ} (hT : ‖x‖ ^ 2 + ‖y‖ ^ 2 + ‖z‖ ^ 2 ≤ T) (hTC : T ≤ C)
    (hQ : ‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 - (2 / 3) * ‖a + b + c‖ ^ 2 ≤ C) :
    ‖a + x‖ ^ 2 + ‖b + y‖ ^ 2 + ‖c + z‖ ^ 2 ≤ C + T + 2 * Real.sqrt (C * T) := by
  let u := ‖a + b + c‖ ^ 2 / 3
  let m : E := (1 / 3 : ℝ) • (a + b + c)
  let n : E := (1 / 3 : ℝ) • (x + y + z)
  have hcancel : m + n = 0 := by dsimp [m,n]; rw [← smul_add, hs, smul_zero]
  have hu : 0 ≤ u := by positivity
  have hn : ‖x + y + z‖ ^ 2 / 3 = u := by
    rw [← neg_eq_iff_add_eq_zero] at hs
    rw [← hs, norm_neg]
  let A := ‖a - m‖ ^ 2 + ‖b - m‖ ^ 2 + ‖c - m‖ ^ 2
  let D := ‖x - n‖ ^ 2 + ‖y - n‖ ^ 2 + ‖z - n‖ ^ 2
  have hA : A ≤ C + u := by
    have hh := HilbertChildFace.centered_energy a b c
    change A = ‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 - u at hh
    dsimp [u] at hh ⊢
    linarith only [hh, hQ]
  have hD : D ≤ T - u := by
    have hh := HilbertChildFace.centered_energy x y z
    rw [hn] at hh
    change D = ‖x‖ ^ 2 + ‖y‖ ^ 2 + ‖z‖ ^ 2 - u at hh
    linarith only [hh, hT]
  have hD₀ : 0 ≤ D := by dsimp [D]; positivity
  have hC₀ : 0 ≤ C := by norm_num [C]
  have hprod : A * D ≤ C * T := by
    refine (mul_le_mul hA hD hD₀ (add_nonneg hC₀ hu)).trans ?_
    nlinarith only [mul_nonneg hu (sub_nonneg.mpr hTC), sq_nonneg u]
  have he (f g : E) : f + g = (f - m) + (g - n) := by
    rw [show (f - m) + (g - n) = (f + g) - (m + n) by abel, hcancel, sub_zero]
  have hcs := HilbertChildFace.cauchy_three (a - m) (b - m) (c - m) (x - n) (y - n) (z - n)
  have hr := Real.sqrt_le_sqrt hprod
  rw [he a x, he b y, he c z, norm_add_sq_real, norm_add_sq_real, norm_add_sq_real]
  change _ ≤ Real.sqrt (A * D) at hcs
  dsimp [A, D] at hA hD ⊢
  linarith only [hA, hD, hcs, hr]

end HilbertTriangleInsertion
