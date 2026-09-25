/- GID: D5/S3/ConceptDynamics/Coding/ResponseFactorization
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/ResponseFactorization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A numbered finite response decomposition yields the corresponding matrix product and one explicit SSE step.
-/

import D5.S3.ConceptDynamics.Coding.ResponseQuotientKernel
import D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier
import Mathlib.Data.Fintype.BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Coding.ResponseFactorization

open D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap
open D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier

/- A response step keeps the numbered intermediate fibre.  The edge
   decomposition is the finite-path witness; it is stronger than a bare
   equality of matrix entries. -/
structure NumberedResponseStep {q r : ℕ} (C : CountMat q q) where
  left : CountMat q r
  right : CountMat r q
  decompose : ∀ i k, Fin (C i k) ≃
    Σ j : Fin r, Fin (left i j) × Fin (right j k)

variable {q r : ℕ} {C : CountMat q q}

theorem matrix_eq_of_numbered_response_step
    (s : NumberedResponseStep C) : C = s.left * s.right := by
  ext i k
  have hcard := Fintype.card_congr (s.decompose i k)
  simpa [Matrix.mul_apply, Fintype.card_sigma, Fintype.card_prod] using hcard.symm

/- The finite-path witness therefore produces an actual one-step SSE, with
   the swapped product as its target rather than a separately assumed chain. -/
theorem response_step_is_sse (s : NumberedResponseStep C) :
    Nonempty (ExchangeChain ℕ C (s.right * s.left) 1) := by
  have hC : C = s.left * s.right := matrix_eq_of_numbered_response_step s
  rw [hC]
  exact ⟨ExchangeChain.cons s.left s.right (ExchangeChain.nil _)⟩

#print axioms matrix_eq_of_numbered_response_step
#print axioms response_step_is_sse

end D5.S3.ConceptDynamics.Coding.ResponseFactorization
