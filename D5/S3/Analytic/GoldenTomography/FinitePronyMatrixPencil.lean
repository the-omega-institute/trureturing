/- GID: D5/S3/Analytic/GoldenTomography/FinitePronyMatrixPencil
   generality: G
   mirror-B: D5/B/S3/Analytic/GoldenTomography/FinitePronyMatrixPencil
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: For separated active modes, the finite Hankel matrix pencil is similar to diagonal modal transport and has the Prony annihilator as characteristic polynomial. -/

import D5.S3.Analytic.GoldenTomography.FinitePronyShiftedHankelTransport
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Finite Prony matrix pencil

Let `H₀` and `H₁` be consecutive square Hankel sections of a finite exponential
moment sequence. The fixed Vandermonde observation map intertwines a canonical
state-space transport with diagonal multiplication by the Prony nodes. If the
nodes are distinct and all weights are nonzero, `H₀` is nonsingular and the
matrix pencil `H₀⁻¹ H₁` equals that canonical transport.

Consequently the pencil is similar to `diagonal nodes`, and its characteristic
polynomial is exactly the Prony annihilator `product_j (X - q_j)`. This is the
exact noiseless spectral-identification theorem underlying matrix-pencil,
ESPRIT-type, and finite Koopman methods.

The theorem does not quantify conditioning, choose eigenvectors numerically,
handle repeated confluent modes, or establish noisy spectral convergence.
-/

/- Library-search audit trail (2026-09-04):
   * The frozen `FinitePronyHankelReconstruction` owner supplies
     `pronyVandermonde`, `pronyHankel`, `pronyAnnihilator`, the square
     Vandermonde transpose identity, and the Vandermonde nonvanishing
     determinant; all are imported and reused, none re-proved.
   * `FinitePronyShiftedHankelTransport` supplies the shifted sections and
     their uniform factorization.
   * Current-tree searches for a Prony matrix-pencil theorem, Hankel pencil
     similarity, and characteristic-polynomial recovery found no declaration
     on `dev`.
   * Pinned Mathlib supplies nonsingular matrix inverses,
     `Matrix.charpoly_mul_comm`, and the characteristic polynomial of a
     diagonal matrix. These standard owners are reused directly. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Analytic.GoldenTomography.FinitePronyMatrixPencil

open Matrix
open D5.S3.Analytic.GoldenTomography.FiniteVandermondeTomography
open D5.S3.Analytic.GoldenTomography.FinitePronyHankelReconstruction
open D5.S3.Analytic.GoldenTomography.FinitePronyShiftedHankelTransport

universe u

variable {K : Type u} [Field K]

/-- The hidden modal transport represented in the observed Hankel coordinates. -/
def finitePronyModalTransport {m : ℕ}
    (nodes : Fin m → K) : Matrix (Fin m) (Fin m) K :=
  let observation := pronyVandermonde (n := m) nodes
  observationᵀ⁻¹ * Matrix.diagonal nodes * observationᵀ

/-- The consecutive finite Hankel matrix pencil. -/
def finitePronyMatrixPencil {m : ℕ}
    (nodes weights : Fin m → K) : Matrix (Fin m) (Fin m) K :=
  (finitePronyShiftedHankel (n := m) nodes weights 0)⁻¹ *
    finitePronyShiftedHankel (n := m) nodes weights 1

/-- Distinct nodes make the square Prony observation matrix nonsingular. -/
theorem finite_prony_vandermonde_det_ne_zero {m : ℕ}
    {nodes : Fin m → K} (hNodes : Function.Injective nodes) :
    Matrix.det (pronyVandermonde (n := m) nodes) ≠ 0 := by
  rw [square_pronyVandermonde_eq_transpose,
    Matrix.det_transpose]
  exact vandermonde_det_ne_zero_of_injective hNodes

/-- The fixed observation map intertwines the observed transport with diagonal
multiplication by the modal nodes. -/
theorem finite_prony_modal_transport_intertwining {m : ℕ}
    {nodes : Fin m → K} (hNodes : Function.Injective nodes) :
    (pronyVandermonde (n := m) nodes)ᵀ *
        finitePronyModalTransport nodes =
      Matrix.diagonal nodes *
        (pronyVandermonde (n := m) nodes)ᵀ := by
  have hDetTranspose :
      Matrix.det ((pronyVandermonde (n := m) nodes)ᵀ) ≠ 0 := by
    rw [Matrix.det_transpose]
    exact finite_prony_vandermonde_det_ne_zero hNodes
  have hUnitTranspose :
      IsUnit (Matrix.det ((pronyVandermonde (n := m) nodes)ᵀ)) :=
    isUnit_iff_ne_zero.mpr hDetTranspose
  simp only [finitePronyModalTransport]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ hUnitTranspose, Matrix.one_mul]

/-- The zero-shift Hankel section transports to the one-shift section through
the canonical observed modal transport. -/
theorem finite_prony_hankel_intertwines_modal_transport {m : ℕ}
    {nodes : Fin m → K} (weights : Fin m → K)
    (hNodes : Function.Injective nodes) :
    finitePronyShiftedHankel (n := m) nodes weights 0 *
        finitePronyModalTransport nodes =
      finitePronyShiftedHankel (n := m) nodes weights 1 := by
  have hIntertwining := finite_prony_modal_transport_intertwining hNodes
  have hfun :
      (fun mode =>
        finitePronyShiftedWeights nodes weights 0 mode * nodes mode) =
        finitePronyShiftedWeights nodes weights 1 := by
    funext mode
    simp [finitePronyShiftedWeights]
  rw [finite_prony_shifted_hankel_factorization (n := m) nodes weights 0,
    finite_prony_shifted_hankel_factorization (n := m) nodes weights 1,
    ← hfun, ← Matrix.diagonal_mul_diagonal]
  simp only [Matrix.mul_assoc]
  rw [hIntertwining]

/-- Distinct nodes and nonzero weights make the square zero-shift Hankel section
nonsingular. -/
theorem finite_prony_square_hankel_det_ne_zero {m : ℕ}
    {nodes weights : Fin m → K}
    (hNodes : Function.Injective nodes)
    (hWeights : ∀ mode, weights mode ≠ 0) :
    Matrix.det
        (finitePronyShiftedHankel (n := m) nodes weights 0) ≠ 0 := by
  have hDetV := finite_prony_vandermonde_det_ne_zero hNodes
  have hDetD :
      Matrix.det
        (Matrix.diagonal (finitePronyShiftedWeights nodes weights 0)) ≠ 0 := by
    rw [Matrix.det_diagonal]
    refine Finset.prod_ne_zero_iff.mpr fun mode _ => ?_
    simp [finitePronyShiftedWeights, hWeights mode]
  rw [finite_prony_shifted_hankel_factorization (n := m) nodes weights 0,
    Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  exact mul_ne_zero (mul_ne_zero hDetV hDetD) hDetV

/-- In the separated active-mode regime, the consecutive Hankel pencil equals
the observed modal transport. -/
theorem finite_prony_matrix_pencil_eq_modal_transport {m : ℕ}
    {nodes weights : Fin m → K}
    (hNodes : Function.Injective nodes)
    (hWeights : ∀ mode, weights mode ≠ 0) :
    finitePronyMatrixPencil nodes weights =
      finitePronyModalTransport nodes := by
  have hHankelUnit :
      IsUnit
        (Matrix.det
          (finitePronyShiftedHankel (n := m) nodes weights 0)) :=
    isUnit_iff_ne_zero.mpr
      (finite_prony_square_hankel_det_ne_zero hNodes hWeights)
  have hTransport :=
    finite_prony_hankel_intertwines_modal_transport weights hNodes
  unfold finitePronyMatrixPencil
  rw [← hTransport]
  exact Matrix.nonsing_inv_mul_cancel_left
    (A := finitePronyShiftedHankel (n := m) nodes weights 0)
    (finitePronyModalTransport nodes) hHankelUnit

/-- The observed modal transport has the same characteristic polynomial as the
diagonal hidden transport. -/
theorem finite_prony_modal_transport_charpoly {m : ℕ}
    {nodes : Fin m → K} (hNodes : Function.Injective nodes) :
    (finitePronyModalTransport nodes).charpoly =
      pronyAnnihilator nodes := by
  have hDetTranspose :
      Matrix.det ((pronyVandermonde (n := m) nodes)ᵀ) ≠ 0 := by
    rw [Matrix.det_transpose]
    exact finite_prony_vandermonde_det_ne_zero hNodes
  have hUnitTranspose :
      IsUnit (Matrix.det ((pronyVandermonde (n := m) nodes)ᵀ)) :=
    isUnit_iff_ne_zero.mpr hDetTranspose
  show
    ((pronyVandermonde (n := m) nodes)ᵀ⁻¹ * Matrix.diagonal nodes *
        (pronyVandermonde (n := m) nodes)ᵀ).charpoly =
      pronyAnnihilator nodes
  calc
    ((pronyVandermonde (n := m) nodes)ᵀ⁻¹ * Matrix.diagonal nodes *
        (pronyVandermonde (n := m) nodes)ᵀ).charpoly =
        ((pronyVandermonde (n := m) nodes)ᵀ *
          ((pronyVandermonde (n := m) nodes)ᵀ⁻¹ *
            Matrix.diagonal nodes)).charpoly :=
      Matrix.charpoly_mul_comm
        ((pronyVandermonde (n := m) nodes)ᵀ⁻¹ * Matrix.diagonal nodes)
        ((pronyVandermonde (n := m) nodes)ᵀ)
    _ = (Matrix.diagonal nodes).charpoly := by
      rw [← Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ hUnitTranspose, Matrix.one_mul]
    _ = pronyAnnihilator nodes := by
      rw [Matrix.charpoly_diagonal]
      rfl

/-- Exact spectral identification: the characteristic polynomial of the finite
Hankel matrix pencil is the Prony annihilator whose roots are precisely the
indexed modal nodes, with multiplicity. -/
theorem finite_prony_matrix_pencil_charpoly {m : ℕ}
    {nodes weights : Fin m → K}
    (hNodes : Function.Injective nodes)
    (hWeights : ∀ mode, weights mode ≠ 0) :
    (finitePronyMatrixPencil nodes weights).charpoly =
      pronyAnnihilator nodes := by
  rw [finite_prony_matrix_pencil_eq_modal_transport hNodes hWeights]
  exact finite_prony_modal_transport_charpoly hNodes

-- A one-mode active family inhabits the exact matrix-pencil regime.
example :
    (finitePronyMatrixPencil
        (fun _ : Fin 1 => (2 : ℂ))
        (fun _ : Fin 1 => (3 : ℂ))).charpoly =
      pronyAnnihilator (fun _ : Fin 1 => (2 : ℂ)) := by
  apply finite_prony_matrix_pencil_charpoly
  · intro left right h
    exact Subsingleton.elim left right
  · intro mode
    norm_num

#print axioms finite_prony_modal_transport_intertwining
#print axioms finite_prony_hankel_intertwines_modal_transport
#print axioms finite_prony_square_hankel_det_ne_zero
#print axioms finite_prony_matrix_pencil_eq_modal_transport
#print axioms finite_prony_modal_transport_charpoly
#print axioms finite_prony_matrix_pencil_charpoly

end D5.S3.Analytic.GoldenTomography.FinitePronyMatrixPencil
