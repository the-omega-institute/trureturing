/- GID: D5/S3/Observer/LinearMemory/DualGramKernels
   generality: G
   mirror-B: D5/B/S3/Observer/LinearMemory/DualGramKernels
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The two Gram kernels equal the observation and adjoint kernels. -/

import D5.S3.Observer.LinearMemory.DualGramVisibleRanges

/- Library-search audit trail (2026-08-28):
   * The exact family companion `DualGramVisibleRanges` fixes the canonical
     `PiLp` protocol carrier and constructs the indexed observation map from
     `LinearMap.pi`; the public statement below uses that same construction.
   * D5 and fresh origin/dev searches found no frozen theorem exposing both
     Gram-kernel clauses.
   * Exact pinned-Mathlib hits `LinearMap.ker_adjoint_comp_self` and
     `LinearMap.ker_self_comp_adjoint` prove the two public conjuncts directly. -/

namespace D5.S3.Observer.LinearMemory.DualGramKernels

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- For an indexed family of scalar protocol readouts, construct the observation
map coordinatewise. The kernel of each Gram operator is exactly the kernel of
the corresponding observation direction. -/
theorem dual_gram_kernels
    {K V ι : Type*} [RCLike K]
    [NormedAddCommGroup V] [InnerProductSpace K V]
    [FiniteDimensional K V] [Fintype ι]
    (readout : ι -> V →ₗ[K] K) :
    let observation : V →ₗ[K] PiLp 2 (fun _ : ι => K) :=
      (WithLp.linearEquiv 2 K (ι -> K)).symm.toLinearMap.comp
        (LinearMap.pi readout)
    (observation.adjoint ∘ₗ observation).ker = observation.ker ∧
      (observation ∘ₗ observation.adjoint).ker = observation.adjoint.ker := by
  dsimp only
  exact ⟨LinearMap.ker_adjoint_comp_self _,
    LinearMap.ker_self_comp_adjoint _⟩

#print axioms dual_gram_kernels

end D5.S3.Observer.LinearMemory.DualGramKernels
