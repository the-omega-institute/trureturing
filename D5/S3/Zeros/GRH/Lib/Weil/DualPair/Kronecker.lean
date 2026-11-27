/- GID: D5/S3/Zeros/GRH/Lib/Weil/DualPair/Kronecker
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Weil/DualPair/Kronecker
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Weil.DualPair.Kronecker. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Weil/DualPair/Kronecker.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.General.LinearAlgebra.ExtendColumns
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Theta kernels of unitary dual pairs: functoriality, seesaw, growth, rapid decay (known
result; see Lib.Weil.DualPair.KernelDecay).

This file: The Kronecker product map U(S)×U(T) → unitary group of Hom(S,T). -/

open Matrix Kronecker

scoped[Kronecker] attribute [simp] conjTranspose_kronecker det_kronecker' transpose_map
  conjTranspose_transpose_eq_transpose_conjTranspose

scoped[Kronecker] attribute [simp ←] mul_kronecker_mul transpose_mul

variable {m n R : Type*} [Fintype m] [Fintype n]

/-- The Kronecker product x ⊗ y of invertible matrices x and y over a commutative semiring, as
an invertible matrix with inverse x⁻¹ ⊗ y⁻¹. -/
@[local simp] noncomputable def kroneckerGL [CommSemiring R] (x : GL m R) (y : GL n R) :
    GL (m × n) R := ⟨x ⊗ₖ y, ↑x⁻¹ ⊗ₖ ↑y⁻¹, by simp, by simp⟩

/-- For SK = 1 and J = T ⊗ Kᵀ, the homomorphism (g, h) ↦ h ⊗ (g⁻¹)ᵀ from U(S) × U(T) to U(J):
the action x ↦ hxg⁻¹ on matrices. -/
@[simps! apply_coe_val] noncomputable def U.kron [CommRing R] [StarRing R] {S K : Matrix n n R}
    {T : Matrix m m R} {J} (hS : S * K = 1) (h : J = T ⊗ₖ Kᵀ) : U S × U T →* U J := .mk'
  (fun p ↦ ⟨kroneckerGL p.2 (transposeGL p.1⁻¹), by simpa [U, inv_eq_right_inv hS, h,
                 conjTranspose_nonsing_inv] using! congr($(p.2.2) ⊗ₖ $(p.1.2)⁻¹ᵀ)⟩) (by aesop)

lemma map_kronecker {a b c d R S} [Ring R] [Ring S] (f : R →+* S) (A : Matrix a b R)
    (B : Matrix c d R) : (A ⊗ₖ B).map f = A.map f ⊗ₖ B.map f := by aesop
