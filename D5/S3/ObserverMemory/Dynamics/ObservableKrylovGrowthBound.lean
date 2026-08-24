/- GID: D5/S3/ObserverMemory/Dynamics/ObservableKrylovGrowthBound
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Dynamics/ObservableKrylovGrowthBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Strict growth of the finite observable Krylov tower is bounded by missing rank. -/

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Order.Interval.Set.Nat

/- Library-search audit trail (2026-08-25):
   * Required-family searches under `D5/S3/Observer`, `D5/S3/Entropy`, and
     `D5/S3/ObserverMemory` found no existing construction of the finite
     observable Krylov tower and no strict-growth rank bound.
   * Pinned-Mathlib search found no theorem packaging the strict-chain count.
     Exact component hits `Submodule.finrank_lt_finrank_of_lt`,
     `LinearMap.finrank_range_adjoint`, `Set.ncard_le_ncard_of_injOn`, and
     `Set.ncard_Ico_nat` are applied directly below.
   * Repository searches found only finite observation-partition stabilization
     bounds, whose carriers are finite types rather than finite-dimensional
     inner-product spaces. -/

noncomputable section

namespace D5.S3.ObserverMemory.Dynamics.ObservableKrylovGrowthBound

open Module

set_option autoImplicit false
set_option relaxedAutoImplicit false

variable {𝕜 V Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y] [FiniteDimensional 𝕜 Y]

/-- The observables generated through time `m`: the span of
`(T*)^k (C* y)` for `k <= m`. -/
def observableKrylov (T : V →ₗ[𝕜] V) (C : V →ₗ[𝕜] Y) (m : ℕ) :
    Submodule 𝕜 V :=
  Submodule.span 𝕜
    {v | ∃ k ≤ m, ∃ y : Y, v = (T.adjoint ^ k) (C.adjoint y)}

private theorem observableKrylov_mono (T : V →ₗ[𝕜] V) (C : V →ₗ[𝕜] Y) :
    Monotone (observableKrylov T C) := by
  intro m n hmn
  apply Submodule.span_mono
  rintro v ⟨k, hkm, y, rfl⟩
  exact ⟨k, hkm.trans hmn, y, rfl⟩

private theorem observableKrylov_zero (T : V →ₗ[𝕜] V) (C : V →ₗ[𝕜] Y) :
    observableKrylov T C 0 = C.adjoint.range := by
  apply le_antisymm
  · rw [observableKrylov, Submodule.span_le]
    rintro v ⟨k, hk, y, rfl⟩
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
    subst k
    exact ⟨y, by simp⟩
  · rintro v ⟨y, rfl⟩
    apply Submodule.subset_span
    exact ⟨0, le_rfl, y, by simp⟩

private theorem strict_growth_count_le_finrank_gap
    (O : ℕ -> Submodule 𝕜 V) (hmono : Monotone O) :
    Set.encard {m : ℕ | O m < O (m + 1)} ≤
      (Module.finrank 𝕜 V - Module.finrank 𝕜 (O 0) : ℕ) := by
  let rankAt : ℕ -> ℕ := fun m => Module.finrank 𝕜 (O m)
  have hmaps : ∀ m ∈ {m : ℕ | O m < O (m + 1)},
      rankAt m ∈ Set.Ico (rankAt 0) (Module.finrank 𝕜 V) := by
    intro m hm
    constructor
    · exact Submodule.finrank_mono (hmono (Nat.zero_le m))
    · have hstrict : rankAt m < rankAt (m + 1) :=
        Submodule.finrank_lt_finrank_of_lt hm
      have htop : rankAt (m + 1) ≤ Module.finrank 𝕜 V := by
        simpa only [rankAt, finrank_top] using
          (Submodule.finrank_mono (show O (m + 1) ≤ (⊤ : Submodule 𝕜 V) from le_top))
      exact hstrict.trans_le htop
  have hinjective : Set.InjOn rankAt {m : ℕ | O m < O (m + 1)} := by
    intro m hm n hn heq
    apply le_antisymm
    · apply Nat.le_of_not_gt
      intro hnm
      have hchain : O (n + 1) ≤ O m := hmono (Nat.succ_le_iff.mpr hnm)
      have hstrict : rankAt n < rankAt (n + 1) :=
        Submodule.finrank_lt_finrank_of_lt hn
      have hlt : rankAt n < rankAt m :=
        hstrict.trans_le (Submodule.finrank_mono hchain)
      exact hlt.ne heq.symm
    · apply Nat.le_of_not_gt
      intro hmn
      have hchain : O (m + 1) ≤ O n := hmono (Nat.succ_le_iff.mpr hmn)
      have hstrict : rankAt m < rankAt (m + 1) :=
        Submodule.finrank_lt_finrank_of_lt hm
      have hlt : rankAt m < rankAt n :=
        hstrict.trans_le (Submodule.finrank_mono hchain)
      exact hlt.ne heq
  calc
    Set.encard {m : ℕ | O m < O (m + 1)} ≤
        Set.encard (Set.Ico (rankAt 0) (Module.finrank 𝕜 V)) :=
      Set.encard_le_encard_of_injOn hmaps hinjective
    _ = (Set.Ico (rankAt 0) (Module.finrank 𝕜 V)).ncard :=
      (Set.finite_Ico (rankAt 0) (Module.finrank 𝕜 V)).cast_ncard_eq.symm
    _ = (Module.finrank 𝕜 V - Module.finrank 𝕜 (O 0) : ℕ) := by
      simp [rankAt]

/-- The number of strict inclusions in the observable Krylov tower is at most
the ambient dimension minus the rank of the initial readout. -/
theorem observable_krylov_strict_growth_bound
    (T : V →ₗ[𝕜] V) (C : V →ₗ[𝕜] Y) :
    Set.encard {m : ℕ |
      observableKrylov T C m < observableKrylov T C (m + 1)} ≤
      (Module.finrank 𝕜 V - Module.finrank 𝕜 C.range : ℕ) := by
  rw [← C.finrank_range_adjoint, ← observableKrylov_zero T C]
  exact strict_growth_count_le_finrank_gap
    (observableKrylov T C) (observableKrylov_mono T C)

#print axioms observable_krylov_strict_growth_bound

end D5.S3.ObserverMemory.Dynamics.ObservableKrylovGrowthBound
