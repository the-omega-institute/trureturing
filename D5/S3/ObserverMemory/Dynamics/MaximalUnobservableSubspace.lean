/- GID: D5/S3/ObserverMemory/Dynamics/MaximalUnobservableSubspace
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Dynamics/MaximalUnobservableSubspace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The all-future readout kernel is the maximal invariant hidden subspace. -/

import D5.S3.ObserverMemory.Dynamics.ObservableKrylovGrowthBound

/- Library-search audit trail (2026-08-25):
   * Required-family and whole-repository searches found no existing linear
     all-future kernel construction or packaged maximal invariant-subspace
     theorem.
   * Exact family hit `ObservableKrylovGrowthBound` supplies the canonical
     finite-dimensional real-or-complex inner-product carrier used here.
   * Exact pinned-Mathlib component hits `Submodule.mem_iInf`,
     `LinearMap.mem_ker`, `pow_succ`, and `pow_succ'` discharge the source's
     zero-coordinate, shift-invariance, and iterate-induction arguments. -/

namespace D5.S3.ObserverMemory.Dynamics.MaximalUnobservableSubspace

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The intersection of every future readout kernel lies in the current
readout kernel, is invariant under the evolution, and contains every other
invariant subspace of the current readout kernel. -/
theorem future_kernel_is_maximal_invariant
    {𝕜 V Y : Type*} [RCLike 𝕜]
    [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    [FiniteDimensional 𝕜 V]
    [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y]
    [FiniteDimensional 𝕜 Y]
    (T : V →ₗ[𝕜] V) (C : V →ₗ[𝕜] Y) :
    let hidden := ⨅ k : ℕ, LinearMap.ker (C.comp (T ^ k))
    hidden ≤ LinearMap.ker C ∧
      Set.MapsTo T hidden hidden ∧
      ∀ M : Submodule 𝕜 V,
        M ≤ LinearMap.ker C -> Set.MapsTo T M M -> M ≤ hidden := by
  dsimp only
  constructor
  · calc
      (⨅ k : ℕ, LinearMap.ker (C.comp (T ^ k))) ≤
          LinearMap.ker (C.comp (T ^ 0)) := iInf_le _ 0
      _ = LinearMap.ker C := by
        ext x
        simp [LinearMap.mem_ker, LinearMap.comp_apply]
  constructor
  · intro x hx
    change x ∈ (⨅ k : ℕ, LinearMap.ker (C.comp (T ^ k))) at hx
    change T x ∈ (⨅ k : ℕ, LinearMap.ker (C.comp (T ^ k)))
    have hxall := (Submodule.mem_iInf _).mp hx
    apply (Submodule.mem_iInf _).mpr
    intro k
    rw [LinearMap.mem_ker] at ⊢
    have hnext := hxall (k + 1)
    rw [LinearMap.mem_ker] at hnext
    simpa [LinearMap.comp_apply, pow_succ] using hnext
  · intro M hkernel hinvariant
    apply le_iInf
    intro k x hx
    rw [LinearMap.mem_ker, LinearMap.comp_apply]
    apply hkernel
    induction k with
    | zero => simpa using hx
    | succ k ih =>
        simpa [pow_succ'] using hinvariant ih

#print axioms future_kernel_is_maximal_invariant

end D5.S3.ObserverMemory.Dynamics.MaximalUnobservableSubspace
