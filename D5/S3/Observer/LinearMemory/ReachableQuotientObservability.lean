/- GID: D5/S3/Observer/LinearMemory/ReachableQuotientObservability
   generality: G
   mirror-B: D5/B/S3/Observer/LinearMemory/ReachableQuotientObservability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Zero future output identifies the zero reachable-state quotient class. -/

import D5.S3.Observer.Linear.ReachableObservableQuotientDescent

/- Library-search audit trail (2026-08-28):
   * Exact repository searches found no theorem stating observability of the
     reachable subspace modulo its all-future hidden part.
   * The frozen `reachable_observable_quotient_descent` supplies the canonical
     source family and its reachable, hidden, and residual constructions.
   * Body-shape searches for the iterated-input span and future-kernel
     intersection found that frozen module as the canonical D5 family owner.
   * Pinned Mathlib supplies the exact component lemmas
     `Submodule.mem_iInf` and `Submodule.Quotient.mk_eq_zero`; both are applied
     directly below. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.LinearMemory.ReachableQuotientObservability

/-- On the reachable-state quotient by the all-future hidden subspace, a
representative whose every future output vanishes represents the zero class. -/
theorem reachable_quotient_observability
    {K State Input Output : Type*} [Field K]
    [AddCommGroup State] [Module K State]
    [AddCommGroup Input] [Module K Input]
    [AddCommGroup Output] [Module K Output]
    (A : State →ₗ[K] State) (B : Input →ₗ[K] State)
    (C : State →ₗ[K] Output) :
    let reachable : Submodule K State :=
      Submodule.span K
        (Set.range fun input : Nat × Input => (A ^ input.1) (B input.2))
    let hidden : Submodule K State :=
      ⨅ k : Nat, LinearMap.ker (C.comp (A ^ k))
    let residual : Submodule K reachable := hidden.comap reachable.subtype
    ∀ x : reachable,
      (∀ k : Nat, C ((A ^ k) x) = 0) → residual.mkQ x = 0 := by
  dsimp only
  intro x futureZero
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  change (x : State) ∈ ⨅ k : Nat, LinearMap.ker (C.comp (A ^ k))
  apply (Submodule.mem_iInf _).mpr
  intro k
  rw [LinearMap.mem_ker, LinearMap.comp_apply]
  exact futureZero k

#print axioms reachable_quotient_observability

end D5.S3.Observer.LinearMemory.ReachableQuotientObservability
