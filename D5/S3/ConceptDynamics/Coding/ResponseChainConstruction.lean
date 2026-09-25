/- GID: D5/S3/ConceptDynamics/Coding/ResponseChainConstruction
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/ResponseChainConstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A finite sequence of numbered response decompositions constructs the matrix chain and its additive-window path conjugacy.
-/

import D5.S3.ConceptDynamics.Coding.ResponseFactorization
import D5.S3.ConceptDynamics.Coding.CountedExchangeChain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Coding.ResponseChainConstruction

open D5.S3.ConceptDynamics.Coding.CountedMatrixOverlap
open D5.S3.ConceptDynamics.Coding.CountedExchangeChain
open D5.S3.ConceptDynamics.Coding.RectangularNilpotenceBarrier
open D5.S3.ConceptDynamics.Coding.ResponseFactorization

/- Unlike an ExchangeChain, this witness stores the numbered finite edge
   decomposition at every step.  The swapped product is therefore computed
   from actual finite fibres at each constructor. -/
inductive NumberedResponseChain :
    {n m : ℕ} → CountMat n n → CountMat m m → ℕ → Prop where
  | nil {n : ℕ} (A : CountMat n n) : NumberedResponseChain A A 0
  | cons {n r m L : ℕ} {A : CountMat n n}
      (step : NumberedResponseStep A) {B : CountMat m m}
      (tail : NumberedResponseChain (step.right * step.left) B L) :
      NumberedResponseChain A B (L + 1)

variable {n m : ℕ} {A : CountMat n n} {B : CountMat m m}

def NumberedResponseChain.toExchangeChain {L : ℕ} :
    NumberedResponseChain A B L → ExchangeChain ℕ A B L
  | .nil A => .nil A
  | .cons step tail =>
      have hA : A = step.left * step.right :=
        matrix_eq_of_numbered_response_step step
      hA ▸ .cons step.left step.right (tail.toExchangeChain)

theorem numbered_response_chain_has_window_conjugacy {L : ℕ}
    (chain : NumberedResponseChain A B L) :
    Nonempty (WindowConjugacy A B L) := by
  exact chain_has_window_conjugacy chain.toExchangeChain

#print axioms NumberedResponseChain.toExchangeChain
#print axioms numbered_response_chain_has_window_conjugacy

end D5.S3.ConceptDynamics.Coding.ResponseChainConstruction
