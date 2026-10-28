/- GID: D5/S3/Quantum/Fibers/NonnegativeConjugationSpan
   generality: G
   mirror-B: D5/B/S3/Quantum/Fibers/NonnegativeConjugationSpan
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Every commutator jet belongs to the span of actual nonnegative-time conjugations. -/

import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.NoncommRing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Topology Matrix.Norms.Operator
open Set NormedSpace

namespace D5.S3.Quantum.Fibers.NonnegativeConjugationSpan

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Conjugation in the fixed real frame; only its nonnegative-time values enter the span. -/
def conjugate (A X : Matrix n n ℝ) (t : ℝ) : Matrix n n ℝ :=
  exp (t • (-A)) * X * exp (t • A)

/-- The infinitesimal Heisenberg generator, with the actual conjugation sign. -/
def commutator (A X : Matrix n n ℝ) : Matrix n n ℝ := X * A - A * X

/-- Linear combinations of actual nonnegative waits on the supplied effect. -/
def observationSpan (A X : Matrix n n ℝ) : Submodule ℝ (Matrix n n ℝ) :=
  Submodule.span ℝ (conjugate A X '' Ici 0)

private theorem conjugate_derivative (A X : Matrix n n ℝ) (t : ℝ) :
    HasDerivAt (conjugate A X) (conjugate A (commutator A X) t) t := by
  have h := ((hasDerivAt_exp_smul_const (-A) t).mul_const X).mul
    (hasDerivAt_exp_smul_const' A t)
  convert h using 1 <;> try rfl
  dsimp [conjugate, commutator]
  noncomm_ring

/-- All iterated right derivatives are in the finite-dimensional closed span of actual waits.
The conclusion does not treat derivatives as additional executable measurements. -/
theorem commutator_jets_in_nonnegative_span (A X : Matrix n n ℝ) (k : ℕ)
    (t : ℝ) (ht : 0 ≤ t) :
    conjugate A ((commutator A)^[k] X) t ∈ observationSpan A X := by
  induction k generalizing t with
  | zero => exact Submodule.subset_span ⟨t, ht, rfl⟩
  | succ k ih =>
    let f : ℝ → Matrix n n ℝ := conjugate A ((commutator A)^[k] X)
    have hs : Ici (0 : ℝ) ⊆ closure (Ici 0 ∩ Ici 0) := by
      simpa only [inter_self] using (subset_closure : Ici (0 : ℝ) ⊆ closure (Ici 0))
    have hd := range_derivWithin_subset_closure_span_image f hs ⟨t, rfl⟩
    have hsub : Submodule.span ℝ (f '' Ici 0) ≤ observationSpan A X := by
      apply Submodule.span_le.mpr
      rintro _ ⟨u, hu, rfl⟩
      exact ih u hu
    have hclosed : IsClosed (observationSpan A X : Set (Matrix n n ℝ)) :=
      (observationSpan A X).closed_of_finiteDimensional
    have hm : derivWithin f (Ici 0) t ∈ observationSpan A X :=
      (closure_minimal hsub hclosed) hd
    have he := (conjugate_derivative A ((commutator A)^[k] X) t).hasDerivWithinAt.derivWithin
      (uniqueDiffOn_Ici 0 t ht)
    change derivWithin (conjugate A ((commutator A)^[k] X)) (Ici 0) t ∈ observationSpan A X at hm
    rw [he] at hm
    simpa only [Function.iterate_succ_apply'] using hm

end D5.S3.Quantum.Fibers.NonnegativeConjugationSpan
