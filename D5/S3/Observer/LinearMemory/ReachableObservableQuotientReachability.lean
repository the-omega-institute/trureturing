/- GID: D5/S3/Observer/LinearMemory/ReachableObservableQuotientReachability
   generality: G
   mirror-B: D5/B/S3/Observer/LinearMemory/ReachableObservableQuotientReachability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Canonical input iterates span the reachable-observable quotient. -/

import D5.S3.Observer.LinearMemory.ZeroMemoryCriterion
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Span.Basic

/- Library-search audit trail (2026-08-28):
   * Body-shape searches for `span {A^k (B u)}` and names containing
     `reachableSubspace` found no existing D5 primitive. The source's reachable
     span is therefore introduced once below.
   * `ZeroMemoryCriterion.eventualKernel` is the canonical D5 all-future
     unobservable subspace and is imported rather than redeclared.
   * Pinned Mathlib supplies `Submodule.span_induction` and the canonical
     quotient map `Submodule.mkQ`; no exact whole-theorem hit was found. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.LinearMemory.ReachableObservableQuotientReachability

open D5.S3.Observer.LinearMemory.ZeroMemoryCriterion

/-- The source's reachable subspace, generated from input directions and all
of their nonnegative-time iterates. -/
def reachableSubspace
    {K V U : Type*} [Semiring K]
    [AddCommMonoid V] [Module K V]
    [AddCommMonoid U] [Module K U]
    (A : V →ₗ[K] V) (B : U →ₗ[K] V) : Submodule K V :=
  Submodule.span K {x | ∃ k : ℕ, ∃ u : U, x = (A ^ k) (B u)}

/-- A canonical reachable generator, regarded as an element of the reachable
subspace rather than merely as an ambient state. -/
def reachableGenerator
    {K V U : Type*} [Semiring K]
    [AddCommMonoid V] [Module K V]
    [AddCommMonoid U] [Module K U]
    (A : V →ₗ[K] V) (B : U →ₗ[K] V) (k : ℕ) (u : U) :
    reachableSubspace A B :=
  ⟨(A ^ k) (B u), Submodule.subset_span ⟨k, u, rfl⟩⟩

/-- After quotienting the reachable subspace by its forever-unobservable
part, the canonical images of the input iterates still span every state. -/
theorem reachable_observable_quotient_is_reachable
    {K V U Y : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V]
    [AddCommGroup U] [Module K U]
    [AddCommGroup Y] [Module K Y]
    (A : V →ₗ[K] V) (B : U →ₗ[K] V) (C : V →ₗ[K] Y) :
    let R := reachableSubspace A B
    let invisible := (eventualKernel C A).comap R.subtype
    Submodule.span K
      {state : R ⧸ invisible |
        ∃ k : ℕ, ∃ u : U,
          state = Submodule.Quotient.mk (reachableGenerator A B k u)} = ⊤ := by
  dsimp only
  let R := reachableSubspace A B
  let invisible := (eventualKernel C A).comap R.subtype
  let generated : Submodule K (R ⧸ invisible) :=
    Submodule.span K
      {state : R ⧸ invisible |
        ∃ k : ℕ, ∃ u : U,
          state = Submodule.Quotient.mk (reachableGenerator A B k u)}
  change generated = ⊤
  apply eq_top_iff.mpr
  intro state _
  obtain ⟨representative, rfl⟩ := invisible.mkQ_surjective state
  change Submodule.Quotient.mk representative ∈ generated
  have representativeReachable : (representative : V) ∈ reachableSubspace A B :=
    representative.property
  refine Submodule.span_induction (p := fun value valueReachable =>
      Submodule.Quotient.mk (⟨value, valueReachable⟩ : R) ∈ generated)
    ?_ ?_ ?_ ?_ representativeReachable
  · intro value generator
    rcases generator with ⟨k, u, rfl⟩
    apply Submodule.subset_span
    refine ⟨k, u, ?_⟩
    congr
  · change invisible.mkQ (0 : R) ∈ generated
    rw [map_zero]
    exact generated.zero_mem
  · intro x y hx hy quotientX quotientY
    change invisible.mkQ ((⟨x, hx⟩ : R) + (⟨y, hy⟩ : R)) ∈ generated
    rw [map_add]
    exact generated.add_mem quotientX quotientY
  · intro scalar x hx quotientX
    change invisible.mkQ (scalar • (⟨x, hx⟩ : R)) ∈ generated
    rw [map_smul]
    exact generated.smul_mem scalar quotientX

#print axioms reachable_observable_quotient_is_reachable

end D5.S3.Observer.LinearMemory.ReachableObservableQuotientReachability
