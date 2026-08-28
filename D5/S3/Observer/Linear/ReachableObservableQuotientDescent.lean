/- GID: D5/S3/Observer/Linear/ReachableObservableQuotientDescent
   generality: G
   mirror-B: D5/B/S3/Observer/Linear/ReachableObservableQuotientDescent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Reachable-state dynamics, inputs, and outputs descend to the observable quotient. -/

import Mathlib.LinearAlgebra.Quotient.Basic

/- Library-search audit trail (2026-08-28):
   * Repository searches for reachable/observable linear quotients and for
     induced dynamics, input, and output maps found adjacent future-kernel and
     generic quotient descents, but no theorem exposing all source clauses on
     the reachable-subspace quotient.
   * Body-shape searches for spans of iterated input ranges and intersections
     of future readout kernels found no canonical D5 primitive to import.
   * Pinned Mathlib supplies the exact component constructors
     `Submodule.mapQ`, `Submodule.liftQ`, and `Submodule.mkQ`; their computation
     and quotient-surjectivity lemmas are applied directly below. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Linear.ReachableObservableQuotientDescent

/-- For a linear control system, the span of all iterated input directions and
the intersection of all future output kernels are invariant. Consequently the
reachable subspace modulo its unobservable part uniquely carries the induced
dynamics, control input, and current output maps. -/
theorem reachable_observable_quotient_descent
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
    Set.MapsTo A reachable reachable ∧
      Set.MapsTo A hidden hidden ∧
      LinearMap.range B ≤ reachable ∧
      residual ≤ LinearMap.ker (C.domRestrict reachable) ∧
      (∃! inducedDynamics : (reachable ⧸ residual) →ₗ[K] (reachable ⧸ residual),
        ∀ x : reachable, ∀ hx : A x ∈ reachable,
          inducedDynamics (residual.mkQ x) =
            residual.mkQ (⟨A x, hx⟩ : reachable)) ∧
      (∃! descendedInput : Input →ₗ[K] (reachable ⧸ residual),
        ∀ u : Input, ∀ hu : B u ∈ reachable,
          descendedInput u = residual.mkQ (⟨B u, hu⟩ : reachable)) ∧
      ∃! descendedOutput : (reachable ⧸ residual) →ₗ[K] Output,
        ∀ x : reachable,
          descendedOutput (residual.mkQ x) = C x := by
  dsimp only
  let reachable : Submodule K State :=
    Submodule.span K
      (Set.range fun input : Nat × Input => (A ^ input.1) (B input.2))
  let hidden : Submodule K State :=
    ⨅ k : Nat, LinearMap.ker (C.comp (A ^ k))
  let residual : Submodule K reachable := hidden.comap reachable.subtype
  have reachableInvariant : Set.MapsTo A reachable reachable := by
    intro x hx
    have mapped : Submodule.map A reachable ≤ reachable := by
      rw [Submodule.map_span_le]
      intro y hy
      rcases hy with ⟨⟨k, u⟩, rfl⟩
      apply Submodule.subset_span
      refine ⟨⟨k + 1, u⟩, ?_⟩
      simp [pow_succ']
    exact mapped ⟨x, hx, rfl⟩
  have hiddenInvariant : Set.MapsTo A hidden hidden := by
    intro x hx
    apply (Submodule.mem_iInf _).mpr
    intro k
    have hnext := (Submodule.mem_iInf _).mp hx (k + 1)
    rw [LinearMap.mem_ker] at hnext ⊢
    simpa [LinearMap.comp_apply, pow_succ] using hnext
  have inputRange : LinearMap.range B ≤ reachable := by
    intro x hx
    rcases hx with ⟨u, rfl⟩
    apply Submodule.subset_span
    refine ⟨⟨0, u⟩, ?_⟩
    simp
  have outputKernel : residual ≤ LinearMap.ker (C.domRestrict reachable) := by
    intro x hx
    rw [LinearMap.mem_ker]
    have hzero := (Submodule.mem_iInf _).mp hx 0
    simpa [LinearMap.mem_ker, LinearMap.comp_apply] using hzero
  refine ⟨reachableInvariant, hiddenInvariant, inputRange, outputKernel,
    ?_, ?_, ?_⟩
  · let restrictedA : reachable →ₗ[K] reachable :=
      (A.domRestrict reachable).codRestrict reachable fun x =>
        reachableInvariant x.2
    have residualInvariant : residual ≤ residual.comap restrictedA := by
      intro x hx
      exact hiddenInvariant hx
    let inducedDynamics : (reachable ⧸ residual) →ₗ[K] (reachable ⧸ residual) :=
      residual.mapQ residual restrictedA residualInvariant
    have inducedDynamicsCommutes :
        ∀ x : reachable, ∀ hx : A x ∈ reachable,
          inducedDynamics (residual.mkQ x) =
            residual.mkQ (⟨A x, hx⟩ : reachable) := by
      intro x hx
      change
        (residual.mapQ residual restrictedA residualInvariant)
            (residual.mkQ x) = residual.mkQ (⟨A x, hx⟩ : reachable)
      rw [Submodule.mkQ_apply, Submodule.mapQ_apply]
      rfl
    refine ⟨inducedDynamics, inducedDynamicsCommutes, ?_⟩
    intro other otherCommutes
    apply LinearMap.ext
    intro quotientState
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective residual quotientState
    exact (otherCommutes x (reachableInvariant x.2)).trans
      (inducedDynamicsCommutes x (reachableInvariant x.2)).symm
  · let restrictedB : Input →ₗ[K] reachable :=
      B.codRestrict reachable fun u => inputRange ⟨u, rfl⟩
    let descendedInput : Input →ₗ[K] (reachable ⧸ residual) :=
      residual.mkQ.comp restrictedB
    have descendedInputCommutes :
        ∀ u : Input, ∀ hu : B u ∈ reachable,
          descendedInput u = residual.mkQ (⟨B u, hu⟩ : reachable) := by
      intro u hu
      rfl
    refine ⟨descendedInput, descendedInputCommutes, ?_⟩
    intro other otherCommutes
    apply LinearMap.ext
    intro u
    exact (otherCommutes u (inputRange ⟨u, rfl⟩)).trans
      (descendedInputCommutes u (inputRange ⟨u, rfl⟩)).symm
  · let descendedOutput : (reachable ⧸ residual) →ₗ[K] Output :=
      residual.liftQ (C.domRestrict reachable) outputKernel
    have descendedOutputCommutes :
        ∀ x : reachable,
          descendedOutput (residual.mkQ x) = C x := by
      intro x
      rfl
    refine ⟨descendedOutput, descendedOutputCommutes, ?_⟩
    intro other otherCommutes
    apply LinearMap.ext
    intro quotientState
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective residual quotientState
    exact (otherCommutes x).trans (descendedOutputCommutes x).symm

#print axioms reachable_observable_quotient_descent

end D5.S3.Observer.Linear.ReachableObservableQuotientDescent
