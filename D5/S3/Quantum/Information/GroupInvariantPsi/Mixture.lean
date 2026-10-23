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
