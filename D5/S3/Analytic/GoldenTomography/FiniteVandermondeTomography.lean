/- GID: D5/S3/Analytic/GoldenTomography/FiniteVandermondeTomography
   generality: G
   mirror-B: D5/B/S3/Analytic/GoldenTomography/FiniteVandermondeTomography
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Distinct finite phase nodes make a matching finite moment window
     faithful. -/

import Mathlib

/-!
This owner closes exact finite tomography. It reuses Mathlib's Vandermonde
determinant and determinant-kernel API. It does not claim numerical stability
or an infinite-family reconstruction theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Analytic.GoldenTomography.FiniteVandermondeTomography

open Matrix

universe u

variable {K : Type u} [Field K]

/-- The first `n` scalar moments of amplitudes placed at `n` phase nodes. -/
def finiteMomentReadout {n : ℕ}
    (nodes amplitudes : Fin n → K) : Fin n → K :=
  Matrix.vecMul amplitudes (Matrix.vandermonde nodes)

/-- Component form of the finite moment readout. -/
theorem finite_moment_readout_apply {n : ℕ}
    (nodes amplitudes : Fin n → K) (moment : Fin n) :
    finiteMomentReadout nodes amplitudes moment =
      ∑ mode : Fin n, amplitudes mode * nodes mode ^ (moment : ℕ) := by
  rfl

/-- Pairwise distinct nodes give a nonzero Vandermonde determinant. -/
theorem vandermonde_det_ne_zero_of_injective
    {n : ℕ} {nodes : Fin n → K} (hNodes : Function.Injective nodes) :
    Matrix.det (Matrix.vandermonde nodes) ≠ 0 := by
  intro hZero
  rw [Matrix.det_vandermonde_eq_zero_iff] at hZero
  obtain ⟨i, j, hij, hne⟩ := hZero
  exact hne (hNodes hij)

/-- The finite moment map is injective whenever its nodes are pairwise
 distinct. -/
theorem finite_moment_readout_injective
    {n : ℕ} {nodes : Fin n → K} (hNodes : Function.Injective nodes) :
    Function.Injective (finiteMomentReadout nodes) := by
  intro left right hMoments
  have hDet : Matrix.det (Matrix.vandermonde nodes) ≠ 0 :=
    vandermonde_det_ne_zero_of_injective hNodes
  have hDifference :
      (left - right) ᵥ* Matrix.vandermonde nodes = 0 := by
    rw [Matrix.sub_vecMul]
    exact sub_eq_zero.mpr hMoments
  have hZero : left - right = 0 :=
    Matrix.eq_zero_of_vecMul_eq_zero hDet hDifference
  exact sub_eq_zero.mp hZero

/-- Equality of the first `n` moments is equivalent to equality of the hidden
 amplitudes. -/
theorem finite_moments_eq_iff
    {n : ℕ} {nodes : Fin n → K} (hNodes : Function.Injective nodes)
    {left right : Fin n → K} :
    finiteMomentReadout nodes left = finiteMomentReadout nodes right ↔
      left = right :=
  (finite_moment_readout_injective hNodes).eq_iff

#print axioms finite_moment_readout_apply
#print axioms vandermonde_det_ne_zero_of_injective
#print axioms finite_moment_readout_injective
#print axioms finite_moments_eq_iff

end D5.S3.Analytic.GoldenTomography.FiniteVandermondeTomography
