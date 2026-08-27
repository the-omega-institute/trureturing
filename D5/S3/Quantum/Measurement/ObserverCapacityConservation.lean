/- GID: D5/S3/Quantum/Measurement/ObserverCapacityConservation
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/ObserverCapacityConservation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Quantum observer capacity and invisible residual conserve dimension under refinement. -/

import D5.S3.Quantum.Measurement.JointObserverVisibleResidual

/- Library-search audit trail (2026-08-27):
   * Exact family primitives `HermitianSpace`, `identityHermitian`, and
     `hermitian_space_finrank` construct the source's real full Hermitian carrier.
     `JointObserverVisibleResidual` uses the same identity-plus-effects span.
   * Repository searches found no theorem packaging the capacity-residual identity
     with both refinement inequalities on this carrier.
   * Exact pinned-Mathlib hits `Submodule.finrank_add_finrank_orthogonal`,
     `Submodule.finrank_mono`, `Submodule.orthogonal_le`, `Submodule.span_mono`,
     and `finrank_span_singleton` supply the proof. No sibling definition is added. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Measurement.ObserverCapacityConservation

open D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition
open D5.S3.Quantum.Measurement.BasisMeasurementProjection

attribute [local instance]
  D5.S3.Quantum.Measurement.BasisMeasurementProjection.matrixNormedAddCommGroup
  D5.S3.Quantum.Measurement.BasisMeasurementProjection.matrixComplexInnerProductSpace
  D5.S3.Quantum.Measurement.BasisMeasurementProjection.matrixRealInnerProductSpace

/-- On the canonical real Hermitian carrier, the dimension of the visible
identity-plus-effect span minus one and the dimension of its orthogonal residual
sum to `d^2-1`. Enlarging the effect family increases the former and decreases
the latter. -/
theorem observer_capacity_conservation (d : Nat) [NeZero d] :
    (∀ effects : Set (HermitianSpace d),
      (Module.finrank ℝ
            (Submodule.span ℝ (Set.insert (identityHermitian d) effects)) - 1) +
          Module.finrank ℝ
            (Submodule.span ℝ (Set.insert (identityHermitian d) effects))ᗮ =
        d ^ 2 - 1) ∧
      (∀ coarseEffects fineEffects : Set (HermitianSpace d),
        coarseEffects ⊆ fineEffects ->
          (Module.finrank ℝ
                (Submodule.span ℝ
                  (Set.insert (identityHermitian d) coarseEffects)) - 1 ≤
            Module.finrank ℝ
                (Submodule.span ℝ
                  (Set.insert (identityHermitian d) fineEffects)) - 1) ∧
          Module.finrank ℝ
              (Submodule.span ℝ
                (Set.insert (identityHermitian d) fineEffects))ᗮ ≤
            Module.finrank ℝ
              (Submodule.span ℝ
                (Set.insert (identityHermitian d) coarseEffects))ᗮ) := by
  constructor
  · intro effects
    let visible := Submodule.span ℝ (Set.insert (identityHermitian d) effects)
    have identityNonzero : identityHermitian d ≠ 0 := by
      intro identityZero
      have valueZero : (1 : Matrix (Fin d) (Fin d) ℂ) = 0 :=
        congrArg Subtype.val identityZero
      exact one_ne_zero valueZero
    have scalarLineLe : ℝ ∙ identityHermitian d ≤ visible := by
      apply Submodule.span_le.mpr
      intro scalarIdentity scalarIdentityMem
      rw [Set.mem_singleton_iff] at scalarIdentityMem
      subst scalarIdentity
      exact Submodule.subset_span (Set.mem_insert _ effects)
    have visiblePositive : 1 ≤ Module.finrank ℝ visible := by
      calc
        1 = Module.finrank ℝ (ℝ ∙ identityHermitian d) :=
          (finrank_span_singleton identityNonzero).symm
        _ ≤ Module.finrank ℝ visible := Submodule.finrank_mono scalarLineLe
    have dimensionSplit := visible.finrank_add_finrank_orthogonal
    rw [hermitian_space_finrank d] at dimensionSplit
    change (Module.finrank ℝ visible - 1) + Module.finrank ℝ visibleᗮ = d ^ 2 - 1
    omega
  · intro coarseEffects fineEffects refines
    let coarseVisible :=
      Submodule.span ℝ (Set.insert (identityHermitian d) coarseEffects)
    let fineVisible :=
      Submodule.span ℝ (Set.insert (identityHermitian d) fineEffects)
    have visibleRefines : coarseVisible ≤ fineVisible := by
      apply Submodule.span_mono
      intro effect effectMem
      rcases Set.mem_insert_iff.mp effectMem with effectIdentity | effectCoarse
      · exact Set.mem_insert_iff.mpr (Or.inl effectIdentity)
      · exact Set.mem_insert_iff.mpr (Or.inr (refines effectCoarse))
    have capacityMonotone :
        Module.finrank ℝ coarseVisible ≤ Module.finrank ℝ fineVisible :=
      Submodule.finrank_mono visibleRefines
    change
      (Module.finrank ℝ coarseVisible - 1 ≤ Module.finrank ℝ fineVisible - 1) ∧
        Module.finrank ℝ fineVisibleᗮ ≤ Module.finrank ℝ coarseVisibleᗮ
    constructor
    · omega
    · exact Submodule.finrank_mono (Submodule.orthogonal_le visibleRefines)

#print axioms observer_capacity_conservation

end D5.S3.Quantum.Measurement.ObserverCapacityConservation
