/- GID: D5/S3/Quantum/Matrix/PartialTransposeTrace
   generality: I
   mirror-B: D5/B/S3/Quantum/Matrix/PartialTransposeTrace
   mirror-E: none(waiver:finite-trace-algebra)
   anchors: []
   utility: none
   digest: Partial transpose is self-adjoint for finite matrix trace pairing in unequal product dimensions. -/

/-
proof_shape: partial_transpose_trace_duality: bind-only
Consumer: UniformRankFourNecessary.core_nonnegative.
Finite-sum reindexing and the existing outer-product trace identities organize
the trace step of the product-local rank-four construction. This consumed
helper supplies no standalone escape witness or first-freeze admission basis.
The private trace-pairing identity is consumed by the vector identity.
Disclosure: https://github.com/the-omega-institute/trureturing/issues/17734
-/

import D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation
import Mathlib.LinearAlgebra.Matrix.Trace

set_option autoImplicit false
set_option Elab.async false

open Matrix
namespace D5.S3.Quantum.Matrix.PartialTransposeTrace
open D5.S3.Quantum.Dynamics.KickedIsingNegativityRefutation (partialTranspose)

variable {A B : Type} [Fintype A] [Fintype B]

private theorem trace_pairing (M N : Matrix (A × B) (A × B) ℂ) :
    (partialTranspose M * N).trace = (M * partialTranspose N).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Fintype.sum_prod_type, partialTranspose]
  apply Finset.sum_congr rfl
  intro a ha
  calc
    (∑ b : B, ∑ c : A, ∑ d : B, M (a,d) (c,b) * N (c,d) (a,b)) =
        ∑ c : A, ∑ b : B, ∑ d : B, M (a,d) (c,b) * N (c,d) (a,b) :=
      Finset.sum_comm
    _ = ∑ c : A, ∑ d : B, ∑ b : B, M (a,d) (c,b) * N (c,d) (a,b) := by
      apply Finset.sum_congr rfl
      intro c hc
      exact Finset.sum_comm
    _ = ∑ d : B, ∑ c : A, ∑ b : B, M (a,d) (c,b) * N (c,d) (a,b) :=
      Finset.sum_comm

/-- Quadratic testing of a partial transpose equals trace pairing with the
partial transpose of the rank-one outer product. The vector need not be
normalized and the local finite types need not have equal cardinality. -/
theorem partial_transpose_trace_duality
    (M : Matrix (A × B) (A × B) ℂ) (v : A × B → ℂ) :
    star v ⬝ᵥ (partialTranspose M *ᵥ v) =
      (M * partialTranspose (vecMulVec v (star v))).trace := by
  rw [← trace_pairing, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec,
    dotProduct_comm]

end D5.S3.Quantum.Matrix.PartialTransposeTrace
