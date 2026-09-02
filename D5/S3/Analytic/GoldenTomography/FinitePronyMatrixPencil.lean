/- GID: D5/S3/Analytic/GoldenTomography/FinitePronyMatrixPencil
   generality: G
   mirror-B: D5/B/S3/Analytic/GoldenTomography/FinitePronyMatrixPencil
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: For separated active modes, the finite Hankel matrix pencil is similar to diagonal modal transport and has the Prony annihilator as characteristic polynomial. -/

import D5.S3.Analytic.GoldenTomography.FinitePronyAnnihilatorRecurrence
import D5.S3.Analytic.GoldenTomography.FinitePronyHankelRank
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

/- Library-search audit trail (2026-09-03):
   * Current-tree searches for a Prony matrix-pencil theorem, Hankel pencil
     similarity, and characteristic-polynomial recovery found no declaration on
     `dev`.
   * The local prerequisites are the newly separated owners for shifted Hankel
     factorization, exact rank, and the reciprocal Prony annihilator.
   * Pinned Mathlib supplies nonsingular matrix inverses,
     `Matrix.charpoly_mul_comm`, and the characteristic polynomial of a diagonal
     matrix. These standard owners are reused directly. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Analytic.GoldenTomography.FinitePronyMatrixPencil

open Matrix
open D5.S3.Analytic.GoldenTomography.FiniteVandermondeTomography
open D5.S3.Analytic.GoldenTomography.FinitePronyAnnihilatorRecurrence
open D5.S3.Analytic.GoldenTomography.FinitePronyShiftedHankelTransport
open D5.S3.Analytic.GoldenTomography.FinitePronyHankelRank

/-- The hidden modal transport represented in the observed Hankel coordinates. -/
def finitePronyModalTransport {m : ℕ}
    (nodes : Fin m → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  let observation := finitePronyVandermonde (n := m) nodes
  observationᵀ⁻¹ * Matrix.diagonal nodes * observationᵀ

/-- The consecutive finite Hankel matrix pencil. -/
def finitePronyMatrixPencil {m : ℕ}
    (nodes weights : Fin m → ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  (finitePronyShiftedHankel (n := m) nodes weights 0)⁻¹ *
    finitePronyShiftedHankel (n := m) nodes weights 1

/-- Distinct nodes make the square Prony observation matrix nonsingular. -/
theorem finite_prony_vandermonde_det_ne_zero {m : ℕ}
    {nodes : Fin m → ℂ} (hNodes : Function.Injective nodes) :
    Matrix.det (finitePronyVandermonde (n := m) nodes) ≠ 0 := by
  rw [square_finitePronyVandermonde_eq_transpose,
    Matrix.det_transpose]
  exact vandermonde_det_ne_zero_of_injective hNodes

/-- The fixed observation map intertwines the observed transport with diagonal
multiplication by the modal nodes. -/
theorem finite_prony_modal_transport_intertwining {m : ℕ}
    {nodes : Fin m → ℂ} (hNodes : Function.Injective nodes) :
    (finitePronyVandermonde (n := m) nodes)ᵀ *
        finitePronyModalTransport nodes =
      Matrix.diagonal nodes *
        (finitePronyVandermonde (n := m) nodes)ᵀ := by
  have hDetTranspose :
      Matrix.det ((finitePronyVandermonde (n := m) nodes)ᵀ) ≠ 0 := by
    rw [Matrix.det_transpose]
    exact finite_prony_vandermonde_det_ne_zero hNodes
  have hUnitTranspose :
      IsUnit (Matrix.det ((finitePronyVandermonde (n := m) nodes)ᵀ)) :=
    isUnit_iff_ne_zero.mpr hDetTranspose
  simp only [finitePronyModalTransport]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ hUnitTranspose, Matrix.one_mul]

/-- The zero-shift Hankel section transports to the one-shift section through
the canonical observed modal transport. -/
theorem finite_prony_hankel_intertwines_modal_transport {m : ℕ}
    {nodes : Fin m → ℂ} (weights : Fin m → ℂ)
    (hNodes : Function.Injective nodes) :
    finitePronyShiftedHankel (n := m) nodes weights 0 *
        finitePronyModalTransport nodes =
      finitePronyShiftedHankel (n := m) nodes weights 1 := by
  have hIntertwining := finite_prony_modal_transport_intertwining hNodes
  rw [finite_prony_hankel_factorization]
  rw [finite_prony_shifted_hankel_factorization]
  calc
    (finitePronyVandermonde (n := m) nodes *
          Matrix.diagonal weights *
          (finitePronyVandermonde (n := m) nodes)ᵀ) *
        finitePronyModalTransport nodes =
      finitePronyVandermonde (n := m) nodes *
        Matrix.diagonal weights *
          ((finitePronyVandermonde (n := m) nodes)ᵀ *
            finitePronyModalTransport nodes) := by
      simp [Matrix.mul_assoc]
    _ = finitePronyVandermonde (n := m) nodes *
        Matrix.diagonal weights *
          (Matrix.diagonal nodes *
            (finitePronyVandermonde (n := m) nodes)ᵀ) := by
      rw [hIntertwining]
    _ = finitePronyVandermonde (n := m) nodes *
        (Matrix.diagonal weights * Matrix.diagonal nodes) *
          (finitePronyVandermonde (n := m) nodes)ᵀ := by
      simp [Matrix.mul_assoc]
    _ = finitePronyVandermonde (n := m) nodes *
        Matrix.diagonal (fun mode => weights mode * nodes mode) *
          (finitePronyVandermonde (n := m) nodes)ᵀ := by
      rw [Matrix.diagonal_mul_diagonal]
    _ = finitePronyVandermonde (n := m) nodes *
        Matrix.diagonal (finitePronyShiftedWeights nodes weights 1) *
          (finitePronyVandermonde (n := m) nodes)ᵀ := by
      congr 2
      funext mode
      simp [finitePronyShiftedWeights]

/-- Distinct nodes and nonzero weights make the square zero-shift Hankel section
nonsingular. -/
theorem finite_prony_square_hankel_det_ne_zero {m : ℕ}
    {nodes weights : Fin m → ℂ}
    (hNodes : Function.Injective nodes)
    (hWeights : ∀ mode, weights mode ≠ 0) :
    Matrix.det
        (finitePronyShiftedHankel (n := m) nodes weights 0) ≠ 0 := by
  have hDetV := finite_prony_vandermonde_det_ne_zero hNodes
  have hDetD : Matrix.det (Matrix.diagonal weights) ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun mode _ => hWeights mode
  rw [finite_prony_hankel_factorization,
    Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  exact mul_ne_zero (mul_ne_zero hDetV hDetD) hDetV

/-- In the separated active-mode regime, the consecutive Hankel pencil equals
the observed modal transport. -/
theorem finite_prony_matrix_pencil_eq_modal_transport {m : ℕ}
    {nodes weights : Fin m → ℂ}
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
    {nodes : Fin m → ℂ} (hNodes : Function.Injective nodes) :
    (finitePronyModalTransport nodes).charpoly =
      finitePronyAnnihilator nodes := by
  let observation : Matrix (Fin m) (Fin m) ℂ :=
    finitePronyVandermonde (n := m) nodes
  have hDetTranspose : Matrix.det observationᵀ ≠ 0 := by
    rw [Matrix.det_transpose]
    exact finite_prony_vandermonde_det_ne_zero hNodes
  have hUnitTranspose : IsUnit (Matrix.det observationᵀ) :=
    isUnit_iff_ne_zero.mpr hDetTranspose
  change
    (observationᵀ⁻¹ * Matrix.diagonal nodes * observationᵀ).charpoly =
      finitePronyAnnihilator nodes
  calc
    (observationᵀ⁻¹ * Matrix.diagonal nodes * observationᵀ).charpoly =
        (observationᵀ *
          (observationᵀ⁻¹ * Matrix.diagonal nodes)).charpoly :=
      Matrix.charpoly_mul_comm
        (observationᵀ⁻¹ * Matrix.diagonal nodes) observationᵀ
    _ = (Matrix.diagonal nodes).charpoly := by
      rw [← Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ hUnitTranspose, Matrix.one_mul]
    _ = finitePronyAnnihilator nodes := by
      rw [Matrix.charpoly_diagonal]
      rfl

/-- Exact spectral identification: the characteristic polynomial of the finite
Hankel matrix pencil is the Prony annihilator whose roots are precisely the
indexed modal nodes, with multiplicity. -/
theorem finite_prony_matrix_pencil_charpoly {m : ℕ}
    {nodes weights : Fin m → ℂ}
    (hNodes : Function.Injective nodes)
    (hWeights : ∀ mode, weights mode ≠ 0) :
    (finitePronyMatrixPencil nodes weights).charpoly =
      finitePronyAnnihilator nodes := by
  rw [finite_prony_matrix_pencil_eq_modal_transport hNodes hWeights]
  exact finite_prony_modal_transport_charpoly hNodes

-- A one-mode active family inhabits the exact matrix-pencil regime.
example :
    (finitePronyMatrixPencil
        (fun _ : Fin 1 => (2 : ℂ))
        (fun _ : Fin 1 => (3 : ℂ))).charpoly =
      finitePronyAnnihilator (fun _ : Fin 1 => (2 : ℂ)) := by
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
