/- GID: D5/S3/ObserverMemory/Dynamics/ObservableKrylovPermanentStability
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Dynamics/ObservableKrylovPermanentStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Equality of consecutive observable Krylov stages persists at every later stage. -/

import D5.S3.ObserverMemory.Dynamics.ObservableKrylovGrowthBound

/- Library-search audit trail (2026-08-27):
   * The exact family primitive `observableKrylov` is imported and reused. Searches
     by construction body and permanent-stability shape found no theorem on that
     canonical linear-observer tower.
   * The related frozen operator-system permanence theorem has a different matrix
     carrier and closure primitive, so it is not an exact hit for this statement.
   * Pinned Mathlib supplies `Function.iterate_fixed`, but the canonical Krylov
     family has no iteration-step primitive to which it applies directly. The proof
     instead establishes adjoint invariance from the source stage equality. -/

noncomputable section

namespace D5.S3.ObserverMemory.Dynamics.ObservableKrylovPermanentStability

open D5.S3.ObserverMemory.Dynamics.ObservableKrylovGrowthBound

set_option autoImplicit false
set_option relaxedAutoImplicit false

variable {K V Y : Type*} [RCLike K]
  [NormedAddCommGroup V] [InnerProductSpace K V] [FiniteDimensional K V]
  [NormedAddCommGroup Y] [InnerProductSpace K Y] [FiniteDimensional K Y]

private theorem observable_krylov_adjoint_invariant
    (T : V →ₗ[K] V) (C : V →ₗ[K] Y) (m : Nat)
    (hStable : observableKrylov T C m = observableKrylov T C (m + 1)) :
    forall v, v ∈ observableKrylov T C m ->
      T.adjoint v ∈ observableKrylov T C m := by
  intro v hv
  refine Submodule.span_induction
    (p := fun v _ => T.adjoint v ∈ observableKrylov T C m)
    ?_ ?_ ?_ ?_ hv
  · intro v hv
    rcases hv with ⟨k, hk, y, rfl⟩
    have hnext :
        (T.adjoint ^ (k + 1)) (C.adjoint y) ∈
          observableKrylov T C (m + 1) :=
      Submodule.subset_span ⟨k + 1, Nat.succ_le_succ hk, y, rfl⟩
    rw [<- hStable] at hnext
    simpa [pow_succ'] using hnext
  · simp
  · intro u v _ _ hu hv
    simpa only [map_add] using (observableKrylov T C m).add_mem hu hv
  · intro a v _ hv
    simpa only [map_smul] using (observableKrylov T C m).smul_mem a hv

private theorem observable_krylov_generator_mem_of_stable
    (T : V →ₗ[K] V) (C : V →ₗ[K] Y) (m : Nat)
    (hStable : observableKrylov T C m = observableKrylov T C (m + 1)) :
    forall k : Nat, forall y : Y,
      (T.adjoint ^ k) (C.adjoint y) ∈ observableKrylov T C m := by
  have hInvariant := observable_krylov_adjoint_invariant T C m hStable
  intro k
  induction k with
  | zero =>
      intro y
      exact Submodule.subset_span ⟨0, Nat.zero_le m, y, by simp⟩
  | succ k ih =>
      intro y
      simpa [pow_succ'] using
        hInvariant ((T.adjoint ^ k) (C.adjoint y)) (ih y)

/-- If two consecutive stages of the observable Krylov tower agree, then every
later stage agrees with the first stable stage. -/
theorem observable_krylov_once_stable_permanently
    (T : V →ₗ[K] V) (C : V →ₗ[K] Y) (m : Nat)
    (hStable : observableKrylov T C m = observableKrylov T C (m + 1)) :
    forall r : Nat,
      observableKrylov T C (m + r) = observableKrylov T C m := by
  have hgenerators :=
    observable_krylov_generator_mem_of_stable T C m hStable
  intro r
  apply le_antisymm
  · rw [observableKrylov, Submodule.span_le]
    rintro v ⟨k, _, y, rfl⟩
    exact hgenerators k y
  · rw [observableKrylov, Submodule.span_le]
    rintro v ⟨k, hk, y, rfl⟩
    exact Submodule.subset_span
      ⟨k, hk.trans (Nat.le_add_right m r), y, rfl⟩

#print axioms observable_krylov_once_stable_permanently

end D5.S3.ObserverMemory.Dynamics.ObservableKrylovPermanentStability
