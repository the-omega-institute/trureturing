/- GID: D5/S3/QuantumBounds/GramRealizability
   generality: G
   mirror-B: D5/B/S3/QuantumBounds/GramRealizability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Positive Hilbert-space operators are exactly adjoint-square Gram operators. -/

import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/- Library-search audit trail (2026-09-03):
   * Six-way repository search found finite Gram identities and positivity results,
     but no theorem characterizing every positive Hilbert-space operator by an
     adjoint-square factorization; no in-flight lane owns this GID or atom.
   * Pinned Mathlib supplies `ContinuousLinearMap.isPositive_adjoint_comp_self`,
     `ContinuousLinearMap.nonneg_iff_isPositive`, `CFC.sqrt_nonneg`, and
     `CFC.sqrt_mul_sqrt_self`. These are used directly.
   * The source alternates between a sesquilinear form `Q(x,y)` and an operator
     equation. Here `Q` is explicitly a continuous endomorphism and its form is
     `inner ℂ (Q x) y`. The canonical realization uses the same Hilbert space. -/

noncomputable section

open scoped CStarAlgebra InnerProductSpace

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.QuantumBounds.GramRealizability

/-- A continuous operator on a complex Hilbert space is positive exactly when
it has an adjoint-square factorization. The factorization realizes its
associated sesquilinear form as a Gram pairing, and in the positive direction
the witness is the canonical positive square root. -/
theorem gram_realizability
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    (Q : V →L[ℂ] V) :
    0 ≤ Q ↔
      ∃ O : V →L[ℂ] V,
        Q = O.adjoint ∘L O ∧
          ∀ x y : V, inner ℂ (Q x) y = inner ℂ (O x) (O y) := by
  constructor
  · intro hQ
    let O : V →L[ℂ] V := CFC.sqrt Q
    have hOself : O.adjoint = O := by
      exact (CFC.sqrt_nonneg Q).isSelfAdjoint.adjoint_eq
    have hfactor : Q = O.adjoint ∘L O := by
      rw [hOself]
      exact (CFC.sqrt_mul_sqrt_self Q hQ).symm
    refine ⟨O, hfactor, fun x y => ?_⟩
    rw [hfactor, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_inner_left]
  · rintro ⟨O, hfactor, _⟩
    rw [hfactor, ContinuousLinearMap.nonneg_iff_isPositive]
    exact ContinuousLinearMap.isPositive_adjoint_comp_self O

#print axioms gram_realizability

end D5.S3.QuantumBounds.GramRealizability
