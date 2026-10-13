/- GID: D5/S3/Quantum/Entanglement/EJM/EJMCoefficientTreeBounds
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMCoefficientTreeBounds
   mirror-E: none(waiver:actual-coefficient-tree-interpreter)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/EJM/EJMAmplitudeCertificates.actual_F1_abs_bound; instance=D5/S3/Quantum/Entanglement/EJM/EJMCertificateData.triangleCoefficients
   digest: A recursive coefficient-tree check bounds every actual lookup, including missing keys. -/

/-
Library search: EJMCertificateData owns the actual tree and lookup interpreter;
Mathlib owns absolute-value order. No existing consumer derives a uniform
lookup amplitude from a recursive check of every stored coefficient.
admission_basis: escape-witness
checked_get_abs_bound: proof_shape: content; escape_witness: the universal
lookup bound is derived by structural induction over arbitrary trees using
the actual get interpreter, including all equality and ordering branches.
This implication is neither assumed by the checker nor supplied by an existing
frozen or Mathlib theorem. The conclusion itself is the non-binding content.
The checker soundness is consumed by EJMAmplitudeCertificates on the original
complete triangle coefficient tree, and then by EJMNoiseRegion.actual_noise_box.
The concrete checker instance, kernel acceptance receipt and actual soundness
application are delivered in that same batch; they are not separately frozen.
The theorem applies to arbitrary trees: no sortedness, dictionary completeness
or assertion about which keys are reachable from outcome events is needed.
Four-slot source registration remains unfinished under issue #16309.
-/

import D5.S3.Quantum.Entanglement.EJM.EJMCertificateData
import Mathlib.Algebra.Order.Group.Abs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false

namespace D5.S3.Quantum.Entanglement.EJM.EJMCoefficientTreeBounds
open D5.S3.Quantum.Entanglement.EJM.EJMCertificateData (CoefficientTree)

/-- Check every stored value and the zero returned by an empty lookup. -/
def checkAbsBound (bound : ℤ) : CoefficientTree → Bool
  | .empty => decide (0 ≤ bound)
  | .node _ value left right =>
      decide (|value| ≤ bound) && (checkAbsBound bound left && checkAbsBound bound right)

/-- Acceptance bounds the original tree interpreter at every key. -/
theorem checked_get_abs_bound (bound : ℤ) (tree : CoefficientTree) :
    checkAbsBound bound tree = true → ∀ query, |tree.get query| ≤ bound := by
  induction tree with
  | empty =>
      intro accepted query
      change decide (0 ≤ bound) = true at accepted
      simpa only [CoefficientTree.get, abs_zero] using
        (of_decide_eq_true accepted : 0 ≤ bound)
  | node key value left right leftIH rightIH =>
      intro accepted query
      change (decide (|value| ≤ bound) &&
        (checkAbsBound bound left && checkAbsBound bound right)) = true at accepted
      obtain ⟨valueAccepted, childrenAccepted⟩ := Bool.and_eq_true_iff.mp accepted
      obtain ⟨leftAccepted, rightAccepted⟩ := Bool.and_eq_true_iff.mp childrenAccepted
      by_cases sameKey : query = key
      · rw [CoefficientTree.get, if_pos sameKey]
        exact of_decide_eq_true valueAccepted
      · by_cases smallerKey : query < key
        · rw [CoefficientTree.get, if_neg sameKey, if_pos smallerKey]
          exact leftIH leftAccepted query
        · rw [CoefficientTree.get, if_neg sameKey, if_neg smallerKey]
          exact rightIH rightAccepted query

#print axioms checked_get_abs_bound

end D5.S3.Quantum.Entanglement.EJM.EJMCoefficientTreeBounds
