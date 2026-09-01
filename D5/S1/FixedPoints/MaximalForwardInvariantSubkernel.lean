/- GID: D5/S1/FixedPoints/MaximalForwardInvariantSubkernel
   generality: G
   mirror-B: D5/B/S1/FixedPoints/MaximalForwardInvariantSubkernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every equivalence relation has a greatest forward-invariant subrelation. -/

import D5.S1.Dynamics.KnasterTarski
import Mathlib.Logic.Function.Iterate

/- Library-search audit trail (2026-09-01):
   * Repository searches for `gfp`, greatest fixed points, invariant relations,
     equivalence kernels, and subkernels found the general Knaster-Tarski wrapper
     `knaster_tarski_extremal_fixed_points`. The observer-specific theorem
     `finite_future_maximal_congruence` has the same shape only when the ambient
     relation is the equality kernel of a readout, so it is not an exact general hit.
   * Pinned Mathlib provides `OrderHom.gfp`, `OrderHom.map_gfp`,
     `OrderHom.le_gfp`, and `OrderHom.isGreatest_gfp`; no declaration packages
     forward invariance, equivalence, ambient containment, and maximality together.
   * A NyxID-proxied GitHub code search for `forwardInvariantKernel` could not run:
     the proxy returned `error_code=1000` (`API key is failed`), and the discovered
     GitHub OAuth bindings were pending or expired. No third-party result is claimed. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.FixedPoints.MaximalForwardInvariantSubkernel

open D5.S1.Dynamics.KnasterTarski

/-- The pairs whose entire forward orbit remains in the ambient relation. -/
def forwardInvariantSubkernel {X : Type*} (F : X → X) (Kq : Set (X × X)) :
    Set (X × X) :=
  {pair | ∀ n, ((F^[n]) pair.1, (F^[n]) pair.2) ∈ Kq}

/-- Retain the ambient relation and pull a candidate relation back one step. -/
def subkernelRefinementOperator {X : Type*} (F : X → X) (Kq : Set (X × X)) :
    Set (X × X) →o Set (X × X) where
  toFun relation :=
    {pair | pair ∈ Kq ∧ (F pair.1, F pair.2) ∈ relation}
  monotone' := by
    intro first second h pair hp
    exact And.intro hp.1 (h hp.2)

/-- The forward-orbit subkernel is an equivalence relation, lies in the ambient
equivalence relation, is forward invariant, and contains every relation with
the latter two properties. It is exactly the refinement operator's greatest
fixed point. -/
theorem maximal_forward_invariant_subkernel
    {X : Type*} (F : X → X) (Kq : Set (X × X))
    (hKq : Equivalence (fun x y => (x, y) ∈ Kq)) :
    let Kinfinity := forwardInvariantSubkernel F Kq
    (Kinfinity = (subkernelRefinementOperator F Kq).gfp) ∧
      Equivalence (fun x y => (x, y) ∈ Kinfinity) ∧
      Kinfinity ≤ Kq ∧
      (∀ pair, pair ∈ Kinfinity → (F pair.1, F pair.2) ∈ Kinfinity) ∧
      ∀ relation : Set (X × X),
        relation ≤ Kq →
        (∀ pair, pair ∈ relation → (F pair.1, F pair.2) ∈ relation) →
        relation ≤ Kinfinity := by
  dsimp only
  let operator := subkernelRefinementOperator F Kq
  have fixedPoint :
      operator (forwardInvariantSubkernel F Kq) = forwardInvariantSubkernel F Kq := by
    ext pair
    change
      (pair ∈ Kq ∧
          ∀ n, ((F^[n]) (F pair.1), (F^[n]) (F pair.2)) ∈ Kq) ↔
        ∀ n, ((F^[n]) pair.1, (F^[n]) pair.2) ∈ Kq
    constructor
    · intro h n
      cases n with
      | zero => simpa using h.1
      | succ n =>
          simpa [Function.iterate_succ_apply] using h.2 n
    · intro h
      exact And.intro (by simpa using h 0) (fun n => by
        simpa [Function.iterate_succ_apply] using h (n + 1))
  have equivalence :
      Equivalence (fun x y => (x, y) ∈ forwardInvariantSubkernel F Kq) := by
    constructor
    · intro x n
      exact hKq.refl _
    · intro x y h n
      exact hKq.symm (h n)
    · intro x y z hxy hyz n
      exact hKq.trans (hxy n) (hyz n)
  have below : forwardInvariantSubkernel F Kq ≤ Kq := by
    intro pair h
    simpa using h 0
  have invariant :
      ∀ pair, pair ∈ forwardInvariantSubkernel F Kq →
        (F pair.1, F pair.2) ∈ forwardInvariantSubkernel F Kq := by
    intro pair h n
    simpa [Function.iterate_succ_apply] using h (n + 1)
  have maximal :
      ∀ relation : Set (X × X),
        relation ≤ Kq →
        (∀ pair, pair ∈ relation → (F pair.1, F pair.2) ∈ relation) →
        relation ≤ forwardInvariantSubkernel F Kq := by
    intro relation relationBelow relationInvariant pair hp n
    have iterated : ((F^[n]) pair.1, (F^[n]) pair.2) ∈ relation := by
      induction n with
      | zero => simpa using hp
      | succ n ih =>
          simpa only [Function.iterate_succ_apply'] using relationInvariant _ ih
    exact relationBelow iterated
  have extrema := knaster_tarski_extremal_fixed_points operator
  have greatestFixedPoint :
      forwardInvariantSubkernel F Kq = operator.gfp := by
    apply le_antisymm
    · exact extrema.2.2 fixedPoint
    · apply maximal operator.gfp
      · intro pair hp
        have hp' : pair ∈ operator operator.gfp := by
          rw [extrema.2.1]
          exact hp
        exact hp'.1
      · intro pair hp
        have hp' : pair ∈ operator operator.gfp := by
          rw [extrema.2.1]
          exact hp
        exact hp'.2
  exact And.intro greatestFixedPoint <|
    And.intro equivalence <|
      And.intro below <|
        And.intro invariant maximal

#print axioms maximal_forward_invariant_subkernel

end D5.S1.FixedPoints.MaximalForwardInvariantSubkernel
