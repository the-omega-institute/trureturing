/- GID: D5/S3/Quantum/Algebra/WeylReconstruction
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/WeylReconstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The actual finite Weyl matrices linearly span the full matrix algebra, with exact trace coefficients. -/

import D5.S3.Quantum.Algebra.WeylDisplacementTrace
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.Tactic

/-!
The imported node proves the pairing formula but explicitly does not claim a
basis. Here the coefficient-to-matrix map is an endomorphism of the actual
matrix space. Trace orthogonality proves injectivity; finite dimensionality
then proves surjectivity. No spanning assumption, abstract Weyl frame, or
supplied reconstruction certificate is used.
This is the finite matrix-algebra bridge. It is not a metaplectic representation
and does not yet prove the operator-norm leakage inequalities.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Algebra.WeylReconstruction

open D5.S3.Quantum.Algebra.WeylDisplacement
open D5.S3.Quantum.Algebra.WeylDisplacementTrace
open scoped BigOperators

variable {M : ℕ} [NeZero M]

noncomputable def word (M : ℕ) [NeZero M] (p : ZMod M × ZMod M) :
    Matrix (ZMod M) (ZMod M) ℂ := displacement M p.1 p.2

private theorem dimension_ne_zero : (M : ℂ) ≠ 0 := by
  exact_mod_cast (NeZero.ne M)

private theorem word_pairing (q p : ZMod M × ZMod M) :
    Matrix.trace (star (word M q) * word M p) =
      if p = q then (M : ℂ) else 0 := by
  simpa only [word, Prod.ext_iff, and_comm, eq_comm] using
    displacement_trace_orthogonal (M := M) q.1 q.2 p.1 p.2

/-- Each coefficient is recovered by a concrete trace against a Weyl adjoint. -/
theorem coefficient_extraction (c : ZMod M × ZMod M → ℂ)
    (q : ZMod M × ZMod M) :
    Matrix.trace (star (word M q) * (∑ p, c p • word M p)) = (M : ℂ) * c q := by
  classical
  simp only [Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum,
    Matrix.trace_smul, smul_eq_mul, word_pairing]
  simp [mul_ite, mul_comm]

/-- Orthogonality is promoted to linear independence of the actual Weyl family. -/
theorem word_linearIndependent : LinearIndependent ℂ (word M) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc q
  have ht := congrArg (fun A : Matrix (ZMod M) (ZMod M) ℂ =>
    Matrix.trace (star (word M q) * A)) hc
  rw [coefficient_extraction] at ht
  have hz : (M : ℂ) * c q = 0 := by simpa using ht
  exact (mul_eq_zero.mp hz).resolve_left dimension_ne_zero

/-- Coefficients are stored in a matrix with exactly the same finite dimension
as the target; injective endomorphism implies surjective without a guessed basis. -/
noncomputable def synthesis (M : ℕ) [NeZero M] :
    Matrix (ZMod M) (ZMod M) ℂ →ₗ[ℂ] Matrix (ZMod M) (ZMod M) ℂ where
  toFun c := ∑ p : ZMod M × ZMod M, c p.1 p.2 • word M p
  map_add' c d := by
    classical
    simp only [Matrix.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' z c := by
    classical
    simp only [RingHom.id_apply, Matrix.smul_apply, smul_eq_mul,
      mul_smul, Finset.smul_sum]

@[simp]
theorem synthesis_apply (c : Matrix (ZMod M) (ZMod M) ℂ) :
    synthesis M c = ∑ p : ZMod M × ZMod M, c p.1 p.2 • word M p := rfl

theorem synthesis_injective : Function.Injective (synthesis M) := by
  intro c d h
  ext i j
  have ht := congrArg (fun A : Matrix (ZMod M) (ZMod M) ℂ =>
    Matrix.trace (star (word M (i, j)) * A)) h
  simp only [synthesis_apply, coefficient_extraction] at ht
  exact mul_left_cancel₀ dimension_ne_zero ht

/-- Every finite matrix admits a Weyl expansion; the coefficient map is constructed. -/
theorem synthesis_surjective : Function.Surjective (synthesis M) :=
  LinearMap.surjective_of_injective synthesis_injective

/-- Exact reconstruction in arbitrary finite dimension, not just qubits. -/
theorem weyl_reconstruction (A : Matrix (ZMod M) (ZMod M) ℂ) :
    A = ∑ p : ZMod M × ZMod M,
      ((M : ℂ)⁻¹ * Matrix.trace (star (word M p) * A)) • word M p := by
  classical
  obtain ⟨c, hc⟩ := synthesis_surjective (M := M) A
  have hcoeff (p : ZMod M × ZMod M) :
      (M : ℂ)⁻¹ * Matrix.trace (star (word M p) * A) = c p.1 p.2 := by
    rw [← hc, synthesis_apply, coefficient_extraction,
      ← mul_assoc, inv_mul_cancel₀ dimension_ne_zero, one_mul]
  simp_rw [hcoeff]
  exact hc.symm

/-- A complex-linear map on the complete matrix algebra is determined by the
finite Weyl family. This is the faithful extension step for algebra closure. -/
theorem linear_maps_equal_of_weyl
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F G : Matrix (ZMod M) (ZMod M) ℂ →ₗ[ℂ] E)
    (h : ∀ p : ZMod M × ZMod M, F (word M p) = G (word M p)) : F = G := by
  classical
  apply LinearMap.ext
  intro A
  obtain ⟨c, rfl⟩ := synthesis_surjective (M := M) A
  simp only [synthesis_apply, map_sum, map_smul, h]

/-- Vanishing of a linear leakage map on all Weyl words means vanishing on
all local matrices; no arbitrary observation subspace is substituted. -/
theorem linear_map_zero_iff_weyl
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F : Matrix (ZMod M) (ZMod M) ℂ →ₗ[ℂ] E) :
    F = 0 ↔ ∀ p : ZMod M × ZMod M, F (word M p) = 0 := by
  constructor
  · intro h p
    rw [h]
    rfl
  · intro h
    exact linear_maps_equal_of_weyl F 0 h

#print axioms word_linearIndependent
#print axioms synthesis_surjective
#print axioms weyl_reconstruction
#print axioms linear_map_zero_iff_weyl

end D5.S3.Quantum.Algebra.WeylReconstruction
