/- GID: D5/S3/Quantum/Recovery/CanonicalEntanglementFidelity
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/CanonicalEntanglementFidelity
   mirror-E: none(waiver:linked-issue-audit)
   anchors: []
   utility: none
   digest: Positive-root purification and reference-first channel entanglement fidelity. -/

import D5.S3.Quantum.Recovery.ReferencePetzChannel
import D5.S3.Quantum.Information.PartialTraceMutualInformation

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Information.PartialTraceMutualInformation

namespace D5.S3.Quantum.Recovery.CanonicalEntanglementFidelity

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- Reference first, channel input second: the input index is the matrix row. -/
def vector (rho : Matrix A A ℂ) (p : A × A) : ℂ :=
  cfc Real.sqrt rho p.2 p.1

def pure (rho : Matrix A A ℂ) : Matrix (A × A) (A × A) ℂ :=
  Matrix.vecMulVec (vector rho) (star (vector rho))

/-- The actual channel acts on each reference-indexed block. -/
def referenceExtension (channel : QuantumChannel A A)
    (T : Matrix (A × A) (A × A) ℂ) : Matrix (A × A) (A × A) ℂ :=
  fun p q => CStarMatrix.ofMatrix.symm (channel.toCompletelyPositiveMap
    (CStarMatrix.ofMatrix (fun i j => T (p.1, i) (q.1, j)))) p.2 q.2

/-- Squared fidelity with the pure canonical reference: no further square,
square root, or output trace normalization. The density domain is certified
by `canonical_purification` whenever rho is positive with trace one. -/
def fidelity (rho : Matrix A A ℂ) (channel : QuantumChannel A A) : ℝ :=
  (star (vector rho) ⬝ᵥ
    (referenceExtension channel (pure rho) *ᵥ vector rho)).re

theorem canonical_purification (rho : Matrix A A ℂ)
    (hp : rho.PosSemidef) (ht : Matrix.trace rho = 1) :
    (pure rho).PosSemidef ∧ Matrix.trace (pure rho) = 1 ∧
      partialTraceLeft (pure rho) = rho := by
  have hadj : (cfc Real.sqrt rho)ᴴ = cfc Real.sqrt rho :=
    (cfc_predicate Real.sqrt rho : IsSelfAdjoint (cfc Real.sqrt rho)).star_eq
  have hs : cfc Real.sqrt rho = CFC.sqrt rho := by
    rw [CFC.sqrt_eq_real_sqrt _ hp.nonneg, cfcₙ_eq_cfc]
  have hm : partialTraceLeft (pure rho) = rho := by
    calc
      _ = cfc Real.sqrt rho * (cfc Real.sqrt rho)ᴴ := by
        ext i j
        simp [partialTraceLeft, pure, vector, Matrix.mul_apply,
          Matrix.vecMulVec_apply, Matrix.conjTranspose_apply]
      _ = rho := by rw [hadj, hs, CFC.sqrt_mul_sqrt_self _ hp.nonneg]
  exact ⟨Matrix.posSemidef_vecMulVec_self_star _,
    (trace_partialTraceLeft (pure rho)).symm.trans (congrArg Matrix.trace hm |>.trans ht), hm⟩

/-- Simultaneously flipping both factors of the vector and matrix preserves
the complex pure-state overlap. This is an equality of the actual sums. -/
theorem overlap_factor_flip (v : A × A → ℂ)
    (T : Matrix (A × A) (A × A) ℂ) :
    star (v ∘ Prod.swap) ⬝ᵥ
        (T.submatrix Prod.swap Prod.swap *ᵥ (v ∘ Prod.swap)) =
      star v ⬝ᵥ (T *ᵥ v) := by
  have hi (p : A × A) :
      (∑ q : A × A, T (Prod.swap p) (Prod.swap q) * v (Prod.swap q)) =
        ∑ q : A × A, T (Prod.swap p) q * v q := by
    exact (Equiv.prodComm A A).sum_comp (fun q => T (Prod.swap p) q * v q)
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply,
    Function.comp_apply, Matrix.submatrix_apply]
  simp_rw [hi]
  exact (Equiv.prodComm A A).sum_comp
    (fun p => star (v p) * ∑ q : A × A, T p q * v q)

end D5.S3.Quantum.Recovery.CanonicalEntanglementFidelity
