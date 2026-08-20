/- GID: D5/S3/Observer/Dynamics/AnchoredFlowEquivalence
   generality: G
   mirror-B: D5/B/S3/Observer/Dynamics/AnchoredFlowEquivalence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Anchored flow identity is characterized by enriched topological conjugacy. -/

import Mathlib.Dynamics.Flow
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Homeomorph.Lemmas

/- Library-search audit trail (2026-08-18):
   * Repository searches found generic semiconjugacy results but no anchored equivalence theorem
     carrying readout, cocycle, ledger, conjugacy-class, and stabilizer clauses.
   * Pinned Mathlib and Loogle returned the exact compact-to-Hausdorff result
     `isHomeomorph_iff_continuous_bijective`; it is applied directly below.
   * Pinned Mathlib also provides `Flow.IsSemiconjugacy` and
     `Function.semiconj_iff_comp_eq`, but neither includes the enriched anchored structure.
   * LeanSearch's attempted public API endpoint returned no searchable result. -/

namespace D5.S3.Observer.Dynamics.AnchoredFlowEquivalence

noncomputable section

universe uX uY uQ uV uL

/-- A pointed continuous real flow equipped with a readout, additive memory cocycle, and ledger. -/
structure AnchoredFlow
    (X : Type uX) (Q : Type uQ) (V : Type uV) (L : Type uL)
    [TopologicalSpace X] [AddCommMonoid V] where
  anchor : X
  dynamics : Flow ℝ X
  readout : X → Q
  cocycle : ℝ → X → V
  cocycle_zero : ∀ x, cocycle 0 x = 0
  cocycle_add : ∀ s t x,
    cocycle (s + t) x = cocycle s (dynamics t x) + cocycle t x
  ledger : X → L

variable {X : Type uX} {Y : Type uY} {Q : Type uQ} {V : Type uV} {L : Type uL}
variable [TopologicalSpace X] [CompactSpace X] [ConnectedSpace X] [T2Space X]
variable [TopologicalSpace Y] [CompactSpace Y] [ConnectedSpace Y] [T2Space Y]
variable [AddCommMonoid V]

/-- Equivalence constructed from semantic primitives: a continuous bijection preserving every
anchored dynamical, readout, cocycle, and ledger component. -/
def primitiveEquivalent
    (A : AnchoredFlow X Q V L) (B : AnchoredFlow Y Q V L) : Prop :=
  ∃ f : X → Y,
    Continuous f ∧
      Function.Bijective f ∧
      f A.anchor = B.anchor ∧
      (∀ t x, f (A.dynamics t x) = B.dynamics t (f x)) ∧
      B.readout ∘ f = A.readout ∧
      (∀ t x, B.cocycle t (f x) = A.cocycle t x) ∧
      B.ledger ∘ f = A.ledger

/-- The observer identity of `A`, viewed among enriched anchored flows on another carrier. -/
def observerIdentity (A : AnchoredFlow X Q V L) : Set (AnchoredFlow Y Q V L) :=
  {B | primitiveEquivalent A B}

/-- Membership in an observer identity class is exactly enriched pointed-flow conjugacy. The
anchor is an internal carrier point, and every enriched anchored self-conjugacy lies in its
stabilizer. -/
theorem anchored_flow_equivalence
    (A : AnchoredFlow X Q V L) (B : AnchoredFlow Y Q V L) :
    B ∈ observerIdentity A ↔
      (∃ h : X ≃ₜ Y,
        h A.anchor = B.anchor ∧
          (∀ t x, h (A.dynamics t x) = B.dynamics t (h x)) ∧
          B.readout ∘ h = A.readout ∧
          (∀ t x, B.cocycle t (h x) = A.cocycle t x) ∧
          B.ledger ∘ h = A.ledger) ∧
      (∀ g : X ≃ₜ X,
        (g A.anchor = A.anchor ∧
          (∀ t x, g (A.dynamics t x) = A.dynamics t (g x)) ∧
          A.readout ∘ g = A.readout ∧
          (∀ t x, A.cocycle t (g x) = A.cocycle t x) ∧
          A.ledger ∘ g = A.ledger) →
        g A.anchor = A.anchor) := by
  constructor
  · rintro ⟨f, hfcont, hfbij, hanchor, hflow, hreadout, hcocycle, hledger⟩
    have hfhome : IsHomeomorph f :=
      isHomeomorph_iff_continuous_bijective.mpr ⟨hfcont, hfbij⟩
    let e : X ≃ Y := Equiv.ofBijective f hfbij
    let h : X ≃ₜ Y :=
      e.toHomeomorphOfContinuousOpen hfcont hfhome.isOpenMap
    refine ⟨⟨h, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · exact hanchor
    · exact hflow
    · exact hreadout
    · exact hcocycle
    · exact hledger
    · intro g hg
      exact hg.1
  · rintro ⟨⟨h, hanchor, hflow, hreadout, hcocycle, hledger⟩, _⟩
    exact ⟨h, h.continuous, h.bijective, hanchor, hflow, hreadout, hcocycle, hledger⟩

/-- A one-point flow with trivial readout and ledger and zero memory inhabits the identity class. -/
example :
    let A : AnchoredFlow Unit Unit ℤ Unit :=
      { anchor := ()
        dynamics := Flow.id ℝ Unit
        readout := fun _ => ()
        cocycle := fun _ _ => 0
        cocycle_zero := fun _ => rfl
        cocycle_add := fun _ _ _ => by simp
        ledger := fun _ => () }
    A ∈ observerIdentity A := by
  dsimp [observerIdentity, primitiveEquivalent]
  exact ⟨id, continuous_id, Function.bijective_id, rfl, fun _ _ => rfl, rfl,
    fun _ _ => rfl, rfl⟩

#print axioms anchored_flow_equivalence

end

end D5.S3.Observer.Dynamics.AnchoredFlowEquivalence
