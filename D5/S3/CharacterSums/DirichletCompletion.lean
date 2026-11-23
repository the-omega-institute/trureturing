/- GID: D5/S3/CharacterSums/DirichletCompletion
   generality: G
   mirror-B: D5/B/S3/CharacterSums/DirichletCompletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Conductor-normalized Dirichlet completions satisfy symmetry and global growth bounds. -/

import D5.S3.CharacterSums.NonprincipalCharacterGrowth
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Calculus.Deriv.Star

/-! # Conductor-normalized Dirichlet completions -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Complex Set Filter Topology MeasureTheory
open scoped ComplexConjugate

namespace D5.S3.CharacterSums.DirichletCompletion

/-- The conductor-normalized completion. -/
def completion {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  Complex.exp (((Real.log (q : ℝ) / 2 : ℝ) : ℂ) * s) * χ.completedLFunction s

/-- Nonprincipal completions are entire, without a primitivity hypothesis. -/
theorem differentiable_completion {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hne : χ ≠ 1) : Differentiable ℂ (completion χ) := by
  exact ((differentiable_const _).mul differentiable_id).cexp.mul
    (DirichletCharacter.differentiable_completedLFunction hne)

/-- The conductor factor removes the variable power in the functional equation. -/
theorem completion_one_sub {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (s : ℂ) :
    completion χ (1 - s) = χ.rootNumber * completion χ⁻¹ s := by
  have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hc : Complex.exp (((Real.log (q : ℝ) / 2 : ℝ) : ℂ) * (1 - s)) *
      (q : ℂ) ^ (s - 1 / 2) =
      Complex.exp (((Real.log (q : ℝ) / 2 : ℝ) : ℂ) * s) := by
    rw [Complex.cpow_def_of_ne_zero hq,
      ← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg q),
      ← Complex.exp_add]
    congr 1
    push_cast
    ring
  dsimp only [completion]
  rw [hχ.completedLFunction_one_sub]
  calc
    _ = (Complex.exp (((Real.log (q : ℝ) / 2 : ℝ) : ℂ) * (1 - s)) *
        (q : ℂ) ^ (s - 1 / 2)) * χ.rootNumber * χ⁻¹.completedLFunction s := by ring
    _ = _ := by rw [hc]; ring

/-- The completion is nonzero on the closed right half-plane, except at a principal pole. -/
theorem completion_ne_zero_of_one_le_re {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hχs : χ ≠ 1 ∨ s ≠ 1) (hs : 1 ≤ s.re) :
    completion χ s ≠ 0 := by
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs; linarith
  have hL := χ.LFunction_ne_zero_of_one_le_re hχs hs
  apply mul_ne_zero (Complex.exp_ne_zero _)
  intro h
  exact hL (by rw [χ.LFunction_eq_completed_div_gammaFactor s (.inl hs0), h, zero_div])

/-- Primitive root numbers are nonzero for every positive modulus. -/
theorem rootNumber_ne_zero {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) : χ.rootNumber ≠ 0 := by
  intro h
  have he := completion_one_sub hχ (-1)
  rw [h, zero_mul] at he
  have hn := completion_ne_zero_of_one_le_re χ (s := 2) (.inr (by norm_num))
    (by norm_num)
  exact hn (by convert he using 1 <;> norm_num)

/-- Nonprincipal primitive completions are also nonzero on the closed left half-plane. -/
theorem completion_ne_zero_of_re_le_zero {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hne : χ ≠ 1)
    {s : ℂ} (hs : s.re ≤ 0) : completion χ s ≠ 0 := by
  have hni : χ⁻¹ ≠ 1 := inv_ne_one.mpr hne
  have hn := completion_ne_zero_of_one_le_re χ⁻¹ (s := 1 - s) (.inl hni)
    (by simp only [sub_re, one_re]; linarith)
  have he := completion_one_sub hχ (1 - s)
  rw [sub_sub_cancel] at he
  rw [he]
  exact mul_ne_zero (rootNumber_ne_zero hχ) hn

end D5.S3.CharacterSums.DirichletCompletion
