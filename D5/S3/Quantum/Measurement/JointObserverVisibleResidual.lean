/- GID: D5/S3/Quantum/Measurement/JointObserverVisibleResidual
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/JointObserverVisibleResidual
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Joint effect families add visible directions and intersect invisible residuals. -/

import D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition
import Mathlib.Analysis.InnerProductSpace.Orthogonal

/- Library-search audit trail (2026-08-27):
   * Repository search found the canonical real Hermitian carrier `HermitianSpace`,
     its Hilbert--Schmidt inner-product instances, and `identityHermitian`; all are
     imported and reused. No D5 theorem states both joint-observer clauses.
   * `FutureWordOrthogonalResidual.visibleEffectSubspace` handles a finite generic
     effect family without the identity effect or the joint-family law.
   * Pinned Mathlib provides the exact component theorems `Submodule.span_union`
     and `Submodule.inf_orthogonal`; both are applied directly below. -/

noncomputable section

open scoped InnerProductSpace Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Measurement.JointObserverVisibleResidual

open D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition
open D5.S3.Quantum.Measurement.BasisMeasurementProjection

attribute [local instance]
  D5.S3.Quantum.Measurement.BasisMeasurementProjection.matrixNormedAddCommGroup
  D5.S3.Quantum.Measurement.BasisMeasurementProjection.matrixComplexInnerProductSpace
  D5.S3.Quantum.Measurement.BasisMeasurementProjection.matrixRealInnerProductSpace

/-- The observer formed from two effect families sees the sum of their real
Hermitian spans, while its orthogonal invisible residual is their intersection. -/
theorem joint_observer_visible_and_residual (d : Nat)
    (effectsOne effectsTwo : Set (HermitianSpace d)) :
    Submodule.span ℝ
        (Set.insert (identityHermitian d) (effectsOne ∪ effectsTwo)) =
          Submodule.span ℝ (Set.insert (identityHermitian d) effectsOne) ⊔
            Submodule.span ℝ (Set.insert (identityHermitian d) effectsTwo) ∧
      (Submodule.span ℝ
          (Set.insert (identityHermitian d) (effectsOne ∪ effectsTwo)))ᗮ =
        (Submodule.span ℝ (Set.insert (identityHermitian d) effectsOne))ᗮ ⊓
          (Submodule.span ℝ (Set.insert (identityHermitian d) effectsTwo))ᗮ := by
  have visibleUnion :
      Submodule.span ℝ
          (Set.insert (identityHermitian d) (effectsOne ∪ effectsTwo)) =
        Submodule.span ℝ (Set.insert (identityHermitian d) effectsOne) ⊔
          Submodule.span ℝ (Set.insert (identityHermitian d) effectsTwo) := by
    rw [← Submodule.span_union]
    exact congrArg (Submodule.span ℝ)
      (Set.insert_union_distrib (identityHermitian d) effectsOne effectsTwo)
  constructor
  · exact visibleUnion
  · rw [visibleUnion]
    exact (Submodule.inf_orthogonal _ _).symm

#print axioms joint_observer_visible_and_residual

end D5.S3.Quantum.Measurement.JointObserverVisibleResidual
