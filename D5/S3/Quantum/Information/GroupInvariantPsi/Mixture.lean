/- GID: D5/S3/Quantum/Information/GroupInvariantPsi/Mixture
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/GroupInvariantPsi/Mixture
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Permutation]
   utility: none
   digest: Permutation tensor averages of diagonal states are finite classical mixtures. -/

import D5.S3.Quantum.Information.GroupInvariantPsi.Defs
import D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity
import Mathlib.LinearAlgebra.Matrix.Permutation

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

namespace D5.S3.Quantum.Information.GroupInvariantPsi.Mixture
open Defs

/-- The unitary representation associated with an action on basis labels. -/
def permutationRepresentation {d : ℕ} {G : Type*} [Group G]
    (σ : G →* Equiv.Perm (Fin d)) :
    G →* unitary (Matrix (Fin d) (Fin d) ℂ) where
  toFun g := ⟨(σ g)⁻¹.permMatrix ℂ, by
    rw [Unitary.mem_iff]
    constructor <;>
      simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_permMatrix,
        ← Matrix.permMatrix_mul, inv_mul_cancel, mul_inv_cancel, Matrix.permMatrix_one]⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' g h := by
    apply Subtype.ext
    change ((σ (g * h))⁻¹).permMatrix ℂ =
      ((σ g)⁻¹).permMatrix ℂ * ((σ h)⁻¹).permMatrix ℂ
    rw [map_mul, _root_.mul_inv_rev, Matrix.permMatrix_mul]

/-- Probability of a word in the uniform mixture of tensor-product distributions. -/
def mixtureWeight {d : ℕ} {G : Type*} [Group G] [Fintype G]
    (σ : G →* Equiv.Perm (Fin d)) (p : Fin d → ℝ) (n : ℕ)
    (w : Fin n → Fin d) : ℝ :=
  (Fintype.card G : ℝ)⁻¹ * ∑ g : G, ∏ j, p ((σ g)⁻¹ (w j))

/-- Classical trace overlap of the two word mixtures. -/
def mixtureTrace {d : ℕ} {G : Type*} [Group G] [Fintype G]
    (σ : G →* Equiv.Perm (Fin d)) (p q : Fin d → ℝ) (n : ℕ) (s : ℝ) : ℝ :=
  ∑ w : Fin n → Fin d, mixtureWeight σ p n w ^ s * mixtureWeight σ q n w ^ (1 - s)

/-- The tensor twirl is diagonal with the classical mixture probabilities. -/
theorem twirlPower_diag {d : ℕ} {G : Type*} [Group G] [Fintype G]
    (σ : G →* Equiv.Perm (Fin d)) (p : Fin d → ℝ) (n : ℕ) :
    twirlPower (permutationRepresentation σ) (Matrix.diagonal fun i => (p i : ℂ)) n =
      Matrix.diagonal fun w => (mixtureWeight σ p n w : ℂ) := by
  classical
  have ht (e : Equiv.Perm (Fin d)) :
      tensorPower (e.permMatrix ℂ) n =
        Equiv.Perm.permMatrix ℂ (Equiv.piCongrRight fun _ : Fin n => e) := by
    ext x y
    simp only [tensorPower, D5.S3.Quantum.Recovery.ProductPrefixRigidity.productMap,
      Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
      Option.mem_def, Option.some.injEq, Fintype.prod_boole]
    congr 1
    exact propext funext_iff.symm
  have hc (g : G) :
      tensorPower ((permutationRepresentation σ) g : Matrix (Fin d) (Fin d) ℂ) n *
        tensorPower (Matrix.diagonal fun i => (p i : ℂ)) n *
        (tensorPower ((permutationRepresentation σ) g : Matrix (Fin d) (Fin d) ℂ) n).conjTranspose =
      Matrix.diagonal (fun w => ((∏ j, p ((σ g)⁻¹ (w j)) : ℝ) : ℂ)) := by
    change tensorPower (((σ g)⁻¹).permMatrix ℂ) n * _ *
      (tensorPower (((σ g)⁻¹).permMatrix ℂ) n).conjTranspose = _
    simp only [ht]
    rw [Matrix.conjTranspose_permMatrix, PEquiv.toMatrix_toPEquiv_mul,
      PEquiv.mul_toMatrix_toPEquiv]
    ext x y
    simp only [Matrix.submatrix_apply, tensorPower,
      D5.S3.Quantum.Recovery.ProductPrefixRigidity.productMap, Matrix.diagonal_apply,
      Equiv.piCongrRight_apply, Pi.map_apply, Equiv.Perm.inv_def,
      Equiv.symm_symm, id_eq]
    by_cases h : x = y
    · subst y
      simp
    · have hxy : ¬ ∀ j, (σ g).symm (x j) = (σ g).symm (y j) := by
        intro hh
        exact h (funext fun j => (σ g).symm.injective (hh j))
      simp only [Fintype.prod_ite_zero, hxy, h, ite_false]
  simp only [twirlPower, hc]
  ext x y
  by_cases h : x = y
  · subst y
    simp [mixtureWeight, Matrix.sum_apply, Complex.ofReal_mul,
      Complex.ofReal_inv, Complex.ofReal_sum]
  · simp [Matrix.sum_apply, h]

/-- The trace product of real spectral powers of diagonal matrices. -/
theorem trace_pow_diag {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p q : ι → ℝ) (s : ℝ) :
    (Matrix.trace
      (D5.S3.Quantum.Matrix.SpectralPower.mpow (Matrix.diagonal fun i => (p i : ℂ)) s *
        D5.S3.Quantum.Matrix.SpectralPower.mpow
          (Matrix.diagonal fun i => (q i : ℂ)) (1 - s))).re =
      ∑ i, p i ^ s * q i ^ (1 - s) := by
  simp only [D5.S3.Quantum.Matrix.SpectralPower.mpow,
    D5.S3.Quantum.Dynamics.EntropyProductionCoherenceDeletionIdentity.cfc_diagonal,
    Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Complex.re_sum,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

end D5.S3.Quantum.Information.GroupInvariantPsi.Mixture
