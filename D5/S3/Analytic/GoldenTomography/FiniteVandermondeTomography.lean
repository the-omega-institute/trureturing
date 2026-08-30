/- GID: D5/S3/Analytic/GoldenTomography/FiniteVandermondeTomography
   generality: G
   mirror-B: D5/B/S3/Analytic/GoldenTomography/FiniteVandermondeTomography
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Distinct finite phase nodes make the Vandermonde moment readout
     injective. -/
/- Library-search audit trail (2026-08-31):
   * Repository searches for this theorem name and finite moment tomography
     found no existing owner.
   * Pinned Mathlib already owns `Matrix.vandermonde`,
     `Matrix.det_vandermonde_eq_zero_iff`, and
     `Matrix.eq_zero_of_mulVec_eq_zero`; this node consumes them.
   * No second determinant formula or matrix inverse is introduced.
   * The new interface is the finite observer statement that distinct nodes
     make the moment readout injective.
   * A uniform singular-value or condition-number bound remains outside this
     theorem and is represented by the two-node conditioning consumer. -/

import Mathlib.LinearAlgebra.Vandermonde

/-!
For `n` hidden amplitudes and `n` pairwise distinct phase nodes, the first `n`
moments form a square Vandermonde system. This module packages the exact finite
tomography statement. It does not provide a uniform lower bound on the smallest
singular value, so numerical stability remains a separate question.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Analytic.GoldenTomography.FiniteVandermondeTomography

open scoped Matrix

universe u

variable {K : Type u} [Field K]

/-- The first `n` moments of a finite amplitude vector at prescribed nodes. -/
def finiteMomentReadout {n : ℕ}
    (nodes amplitudes : Fin n → K) : Fin n → K :=
  Matrix.vandermonde nodes *ᵥ amplitudes

/-- Pairwise distinct nodes give a nonzero Vandermonde determinant. -/
theorem vandermonde_det_ne_zero_of_injective
    {n : ℕ} {nodes : Fin n → K}
    (hNodes : Function.Injective nodes) :
    Matrix.det (Matrix.vandermonde nodes) ≠ 0 := by
  intro hZero
  rw [Matrix.det_vandermonde_eq_zero_iff] at hZero
  obtain ⟨i, j, hij, hne⟩ := hZero
  exact hne (hNodes hij)

/-- The Vandermonde bilinear form associated with distinct nodes is
nondegenerate. -/
theorem vandermonde_nondegenerate_of_injective
    {n : ℕ} {nodes : Fin n → K}
    (hNodes : Function.Injective nodes) :
    (Matrix.vandermonde nodes).Nondegenerate := by
  exact Matrix.nondegenerate_of_det_ne_zero
    (vandermonde_det_ne_zero_of_injective hNodes)

/-- The finite moment map is injective whenever its phase nodes are pairwise
distinct. -/
theorem finite_moment_readout_injective
    {n : ℕ} {nodes : Fin n → K}
    (hNodes : Function.Injective nodes) :
    Function.Injective (finiteMomentReadout nodes) := by
  intro a b hMoments
  apply sub_eq_zero.mp
  apply Matrix.eq_zero_of_mulVec_eq_zero
    (vandermonde_det_ne_zero_of_injective hNodes)
  rw [Matrix.mulVec_sub]
  unfold finiteMomentReadout at hMoments
  rw [hMoments, sub_self]

/-- Equality of the first `n` moments is equivalent to equality of the hidden
amplitude vectors. -/
theorem finite_moments_eq_iff
    {n : ℕ} {nodes : Fin n → K}
    (hNodes : Function.Injective nodes) {a b : Fin n → K} :
    finiteMomentReadout nodes a = finiteMomentReadout nodes b ↔ a = b := by
  exact (finite_moment_readout_injective hNodes).eq_iff

/-- The theorem has an inhabited instance over one rational node. -/
example :
    Function.Injective
      (finiteMomentReadout (fun _ : Fin 1 => (0 : ℚ))) := by
  apply finite_moment_readout_injective
  intro i j _
  exact Subsingleton.elim i j

#print axioms vandermonde_det_ne_zero_of_injective
#print axioms vandermonde_nondegenerate_of_injective
#print axioms finite_moment_readout_injective
#print axioms finite_moments_eq_iff

end D5.S3.Analytic.GoldenTomography.FiniteVandermondeTomography
