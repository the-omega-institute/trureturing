/- GID: D5/S3/ConceptDynamics/GraphColoring/JacoDegreeShift
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/GraphColoring/JacoDegreeShift
   mirror-E: none(waiver:structural-proof)
   anchors: [lake/module/D5.S3.ConceptDynamics.GraphColoring.JacoAdditionLaw]
   utility: none
   digest: Every Jaco maximum degree is b_n or b_n - 1, and order n + Delta_n has maximum degree n or n - 1 accordingly. -/

import D5.S3.ConceptDynamics.GraphColoring.JacoAdditionLaw

/-! The maximum degree against the Beatty outdegree, and the shifted order `n + Δ_n`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.GraphColoring.JacoDegreeShift

/-
proof_shape:
  result: content
escape_witness: the identity (n + Delta_n + 2) / phi = n + 2 - (1 + frac n) / phi, from
  phi^-2 = 1 - phi^-1, together with frac n != 1 / phi from the irrationality of phi, fixes
  both floors on either side of the threshold 1 / phi.
admission_basis: escape-witness
-/

open D5.S3.ConceptDynamics.GraphColoring.JacoDomPathDiameterRefutation
open D5.S3.ConceptDynamics.GraphColoring.JacoEndpointBeatty
open D5.S3.ConceptDynamics.GraphColoring.JacoAdditionLaw

private theorem g_sq : Real.goldenRatio⁻¹ ^ 2 = 1 - Real.goldenRatio⁻¹ := by
  rw [Real.inv_goldenRatio, Real.goldenConj]
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith

/-- For every order `n`, `Δ_n` is `b_n` or `b_n - 1`, the first case holding exactly when the golden
fractional part of `(n + 2) / φ` lies below `1 / φ`; in the first case the order
`n + Δ_n` has maximum degree `n`, in the second `n - 1`. -/
theorem result (n : ℕ) :
    ((jaco n).maxDegree = beattyOut n ∨ (jaco n).maxDegree + 1 = beattyOut n) ∧
    ((jaco n).maxDegree = beattyOut n ↔ frac n < Real.goldenRatio⁻¹) ∧
    ((jaco n).maxDegree + 1 = beattyOut n ↔ Real.goldenRatio⁻¹ < frac n) ∧
    ((jaco n).maxDegree = beattyOut n →
      (jaco (n + (jaco n).maxDegree)).maxDegree = n) ∧
    ((jaco n).maxDegree + 1 = beattyOut n →
      (jaco (n + (jaco n).maxDegree)).maxDegree + 1 = n) := by
  have hp := Real.goldenRatio_pos
  set g := Real.goldenRatio⁻¹ with hg
  have hg0 : 0 < g := inv_pos.mpr hp
  have hg1 : g < 1 := inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have hgsq := g_sq
  set y : ℝ := ((n : ℝ) + 2) / Real.goldenRatio with hy
  set F : ℤ := ⌊y⌋ with hF
  have hx : frac n = y - F := by rw [frac, Int.fract]
  have hx0 : 0 ≤ frac n := Int.fract_nonneg _
  have hx1 : frac n < 1 := Int.fract_lt_one _
  have hD : ((jaco n).maxDegree : ℤ) = F - 1 := delta_eq_floor n
  -- b_n = ⌊y - g⌋
  have hb : (beattyOut n : ℤ) = ⌊y - g⌋ := by
    have hpos : (0 : ℝ) ≤ ((n : ℝ) + 1) / Real.goldenRatio := by positivity
    rw [beattyOut, Int.natCast_floor_eq_floor hpos]
    congr 1
    rw [hy, hg]; field_simp; ring
  -- x ≠ g by irrationality of φ
  have hne : frac n ≠ g := by
    intro h
    have hirr : Irrational (((n + 1 : ℕ) : ℝ) * g) :=
      Real.goldenRatio_irrational.inv.natCast_mul (by omega)
    apply hirr.ne_int F
    have : ((n : ℝ) + 2) * g = y := by rw [hy, div_eq_mul_inv]
    push_cast
    linarith
  -- shifted order
  have hshift : ((n + (jaco n).maxDegree : ℕ) : ℝ) + 2 =
      ((n : ℝ) + 2 - (1 + frac n) * g) * Real.goldenRatio := by
    have hDr : ((jaco n).maxDegree : ℝ) = (F : ℝ) - 1 := by exact_mod_cast hD
    have hyg : y = ((n : ℝ) + 2) * g := by rw [hy, div_eq_mul_inv]
    have hgp : g * Real.goldenRatio = 1 := inv_mul_cancel₀ hp.ne'
    push_cast
    rw [hDr, hx, hyg]
    have : ((n : ℝ) + 2 - (1 + ((n + 2) * g - F)) * g) * Real.goldenRatio =
        ((n : ℝ) + 2) * Real.goldenRatio - (1 + (n + 2) * g - F) * (g * Real.goldenRatio) := by ring
    rw [this, hgp]
    have hphi : Real.goldenRatio = 1 + g := by
      rw [hg, Real.inv_goldenRatio, Real.goldenConj, Real.goldenRatio]; ring
    rw [hphi]
    nlinarith [hgsq]
  have hshiftD : ((jaco (n + (jaco n).maxDegree)).maxDegree : ℤ) =
      ⌊(n : ℝ) + 2 - (1 + frac n) * g⌋ - 1 := by
    have := delta_eq_floor (n + (jaco n).maxDegree)
    rw [delta, hshift, mul_div_assoc, div_self hp.ne', mul_one] at this
    exact this
  have hone : (1 + g) * g = 1 := by nlinarith [hgsq]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hbD : (beattyOut n : ℤ) = F - 1 := by
      rw [hb, Int.floor_eq_iff]; push_cast; constructor <;> linarith
    have t1 : 0 < (1 + frac n) * g := mul_pos (by linarith) hg0
    have t2 : (1 + frac n) * g < 1 := by
      have := mul_lt_mul_of_pos_right (show 1 + frac n < 1 + g by linarith) hg0
      linarith
    have hsh : ⌊(n : ℝ) + 2 - (1 + frac n) * g⌋ = (n : ℤ) + 1 := by
      rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    have h1 : (jaco n).maxDegree = beattyOut n := by omega
    refine ⟨Or.inl h1, ⟨fun _ => hlt, fun _ => h1⟩, ⟨fun h => by omega, fun h => absurd h (by linarith)⟩,
      fun _ => by omega, fun h => by omega⟩
  · have hbD : (beattyOut n : ℤ) = F := by
      rw [hb, Int.floor_eq_iff]; constructor <;> linarith
    have t1 : 1 < (1 + frac n) * g := by
      have := mul_lt_mul_of_pos_right (show 1 + g < 1 + frac n by linarith) hg0
      linarith
    have t2 : (1 + frac n) * g < 2 := by
      have := mul_lt_mul_of_pos_right (show 1 + frac n < 2 by linarith) hg0
      linarith
    have hsh : ⌊(n : ℝ) + 2 - (1 + frac n) * g⌋ = (n : ℤ) := by
      rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
    have h1 : (jaco n).maxDegree + 1 = beattyOut n := by omega
    refine ⟨Or.inr h1, ⟨fun h => by omega, fun h => absurd h (by linarith)⟩, ⟨fun _ => hgt, fun _ => h1⟩,
      fun h => by omega, fun _ => by omega⟩

#print axioms result

end D5.S3.ConceptDynamics.GraphColoring.JacoDegreeShift
