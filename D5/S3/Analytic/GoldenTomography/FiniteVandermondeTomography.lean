/- GID: D5/S3/Analytic/GoldenTomography/FiniteVandermondeTomography
   generality: G
   mirror-B: D5/B/S3/Analytic/GoldenTomography/FiniteVandermondeTomography
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Pairwise distinct finite phase nodes make the corresponding Vandermonde moment readout injective. -/

import Mathlib.LinearAlgebra.Vandermonde

/-!
For `n` hidden amplitudes and `n` pairwise distinct phase nodes, the first `n`
moments form a square Vandermonde system.  This module packages the exact
finite tomography statement.  It does not provide a uniform lower bound on the
smallest singular value, so numerical stability remains a separate question.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Analytic.GoldenTomography.FiniteVandermondeTomography

open Matrix

universe u

variable {K : Type u} [Field K]

/-- The first `n` moments of a finite amplitude vector at prescribed nodes. -/
def finiteMomentReadout {n : ℕ} (nodes amplitudes : Fin n → K) : Fin n → K :=
  Matrix.vandermonde nodes *ᵥ amplitudes

/-- Pairwise distinct nodes give a nonzero Vandermonde determinant. -/
theorem vandermonde_det_ne_zero_of_injective
    {n : ℕ} {nodes : Fin n → K} (hNodes : Function.Injective nodes) :
    Matrix.det (Matrix.vandermonde nodes) ≠ 0 := by
  intro hZero
  rw [Matrix.det_vandermonde_eq_zero_iff] at hZero
  obtain ⟨i, j, hij, hne⟩ := hZero
  exact hne (hNodes hij)

/-- The Vandermonde matrix associated with distinct nodes is nonsingular. -/
theorem vandermonde_nonsingular_of_injective
    {n : ℕ} {nodes : Fin n → K} (hNodes : Function.Injective nodes) :
    (Matrix.vandermonde nodes).Nonsingular := by
  exact Matrix.nonsingular_iff_det_ne_zero.mpr
    (vandermonde_det_ne_zero_of_injective hNodes)

/-- The finite moment map is injective whenever its phase nodes are pairwise
distinct. -/
theorem finite_moment_readout_injective
    {n : ℕ} {nodes : Fin n → K} (hNodes : Function.Injective nodes) :
    Function.Injective (finiteMomentReadout nodes) := by
  unfold finiteMomentReadout
  have hNonsingular := vandermonde_nonsingular_of_injective hNodes
  exact Matrix.mulVec_injective_iff.mpr hNonsingular.linearIndependent_col

/-- Equality of the first `n` moments is therefore equivalent to equality of
the hidden amplitude vectors. -/
theorem finite_moments_eq_iff
    {n : ℕ} {nodes : Fin n → K} (hNodes : Function.Injective nodes)
    {a b : Fin n → K} :
    finiteMomentReadout nodes a = finiteMomentReadout nodes b ↔ a = b := by
  exact (finite_moment_readout_injective hNodes).eq_iff

/-- The theorem has an inhabited nontrivial instance with two distinct complex
nodes. -/
example :
    Function.Injective
      (finiteMomentReadout (fun i : Fin 2 => (i.1 : ℂ))) := by
  apply finite_moment_readout_injective
  intro i j hij
  apply Fin.ext
  exact_mod_cast hij

#print axioms vandermonde_det_ne_zero_of_injective
#print axioms vandermonde_nonsingular_of_injective
#print axioms finite_moment_readout_injective
#print axioms finite_moments_eq_iff

end D5.S3.Analytic.GoldenTomography.FiniteVandermondeTomography
