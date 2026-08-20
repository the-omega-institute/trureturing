/- GID: D5/S3/Observer/WindowAlgebra/UpdateKernelCharacterization
   generality: G
   mirror-B: D5/B/S3/Observer/WindowAlgebra/UpdateKernelCharacterization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Identify update kernels and cyclic constants. -/

import D5.S3.Observer.ObserverMetric

/- Library-search audit trail (2026-08-20):
   * Exact local hits: `D5.S3.Observer.ObserverMetric.updateDefect_eq_zero_iff_invariant`
     proves the pointwise zero-defect/invariance equivalence, and
     `D5.S3.Observer.ObserverMetric.invariant_iff_const_on_cyclic_window` proves the
     finite cyclic-window constant characterization. Both are applied below.
   * Pinned Mathlib searches for an update-difference kernel/fixed-submodule theorem
     found only generic `LinearMap.mem_ker` and submodule extensionality; no exact
     theorem packages this source statement.
   * Repository searches for `ker.*update`, `update.*ker`, and fixed-observable
     submodules found no duplicate declaration.
-/

namespace D5.S3.Observer.WindowAlgebra.UpdateKernelCharacterization

open D5.S3.Observer.ObserverMetric

noncomputable section

/-- The observable difference produced by one update step. -/
def updateDifference {index : Type*} (tau : Equiv.Perm index) :
    (index → ℂ) →ₗ[ℂ] (index → ℂ) where
  toFun := updateDefect tau
  map_add' := by
    intro f g
    funext i
    simp only [updateDefect, Pi.add_apply]
    ring
  map_smul' := by
    intro c f
    funext i
    simp [updateDefect, Pi.smul_apply, mul_sub]

/-- The submodule of observables fixed by the supplied update permutation. -/
def invariantObservables {index : Type*} (tau : Equiv.Perm index) :
    Submodule ℂ (index → ℂ) where
  carrier := {f | ∀ i, f (tau i) = f i}
  zero_mem' := by
    intro i
    simp
  add_mem' := by
    intro f g hf hg i
    simp only [Pi.add_apply]
    rw [hf i, hg i]
  smul_mem' := by
    intro c f hf i
    simp only [Pi.smul_apply]
    rw [hf i]

/-- Zero update difference, the fixed-observable kernel, and the cyclic constants. -/
theorem update_difference_kernel_fixed_observables {index : Type*}
    (tau : Equiv.Perm index) (f : index → ℂ) :
    (updateDifference tau f = 0 ↔ Function.comp f tau = f) ∧
      LinearMap.ker (updateDifference tau) = invariantObservables tau ∧
      (∀ {M : ℕ} [NeZero M] (g : ZMod M → ℂ),
        g ∈ LinearMap.ker (updateDifference (Equiv.addRight (1 : ZMod M))) ↔
          ∃ c : ℂ, g = Function.const (ZMod M) c) := by
  have hzero : updateDifference tau f = 0 ↔ ∀ i, f (tau i) = f i := by
    change updateDefect tau f = 0 ↔ ∀ i, f (tau i) = f i
    exact updateDefect_eq_zero_iff_invariant tau f
  have hcomp : updateDifference tau f = 0 ↔ Function.comp f tau = f := by
    constructor
    · intro h
      funext i
      exact (hzero.mp h) i
    · intro h
      apply hzero.mpr
      intro i
      exact congrFun h i
  have hker : LinearMap.ker (updateDifference tau) = invariantObservables tau := by
    ext g
    constructor
    · intro hg
      have hg' : updateDefect tau g = 0 := by
        simpa [updateDifference] using hg
      change ∀ i, g (tau i) = g i
      exact (updateDefect_eq_zero_iff_invariant tau g).mp hg'
    · intro hg
      change ∀ i, g (tau i) = g i at hg
      simpa [updateDifference] using
        (updateDefect_eq_zero_iff_invariant tau g).mpr hg
  refine ⟨hcomp, hker, ?_⟩
  intro M _ g
  rw [LinearMap.mem_ker]
  simpa [updateDifference] using invariant_iff_const_on_cyclic_window g

end

end D5.S3.Observer.WindowAlgebra.UpdateKernelCharacterization
