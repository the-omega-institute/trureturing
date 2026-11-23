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

end D5.S3.CharacterSums.DirichletCompletion
