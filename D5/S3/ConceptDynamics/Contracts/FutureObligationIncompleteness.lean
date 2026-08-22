/- GID: D5/S3/ConceptDynamics/Contracts/FutureObligationIncompleteness
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Contracts/FutureObligationIncompleteness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A noninjective interface misses a separating future Boolean obligation. -/

import D5.S0.Rewriting.Quotients.InformedDisclosureDefect
import D5.S3.ConceptDynamics.ConceptFiberDecomposition

/- Library-search audit trail (2026-08-22):
   * Exact repository primitive hit `ConceptFiberDecomposition.Concept` is the
     canonical readout carrier and is imported rather than redeclared.
   * A cross-lane search found no existing Boolean collision-obligation
     primitive. `collisionObligation` is therefore constructed directly from
     equality to the source collision's first object.
   * Exact repository theorem hit
     `InformedDisclosureDefect.informed_disclosure_defect` proves that an
     interface collision separated by an obligation blocks factorization; it
     is applied directly in both public directions.
   * Exact pinned-Mathlib hit `Function.not_injective_iff` supplies the source
     collision and is applied directly. No theorem packages both public halves. -/

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Contracts.FutureObligationIncompleteness

open D5.S0.Rewriting.Quotients.InformedDisclosureDefect
open D5.S3.ConceptDynamics.ConceptFiberDecomposition

/-- The Boolean future obligation that accepts exactly the distinguished
object of a collision. -/
def collisionObligation {X : Type*} (distinguished : X) : Concept X Bool :=
  by
    classical
    exact fun object => if object = distinguished then true else false

/-- A nonfaithful interface exposes a collision and the named Boolean
obligation separating that collision cannot factor through the interface.
Independently, completeness for every Boolean obligation forces faithfulness. -/
theorem nonfaithful_interface_future_incomplete
    {X B : Type*} (interface : Concept X B) :
    ((¬Function.Injective interface) ->
      ∃ x y : X,
        x ≠ y ∧ interface x = interface y ∧
          collisionObligation x x ≠ collisionObligation x y ∧
          ¬∃ factor : B -> Bool,
            collisionObligation x = factor ∘ interface) ∧
      ((∀ obligation : Concept X Bool,
        ∃ factor : B -> Bool, obligation = factor ∘ interface) ->
        Function.Injective interface) := by
  constructor
  · intro notFaithful
    obtain ⟨x, y, sameInterface, differentObjects⟩ :=
      Function.not_injective_iff.mp notFaithful
    have separated :
        collisionObligation x x ≠ collisionObligation x y := by
      have yNeX : y ≠ x := Ne.symm differentObjects
      simp [collisionObligation, yNeX]
    refine ⟨x, y, differentObjects, sameInterface, separated, ?_⟩
    exact (informed_disclosure_defect (Decision := Bool)
      interface (collisionObligation x)
      sameInterface separated).2
  · intro complete x y sameInterface
    by_contra differentObjects
    have separated :
        collisionObligation x x ≠ collisionObligation x y := by
      have yNeX : y ≠ x := Ne.symm differentObjects
      simp [collisionObligation, yNeX]
    obtain ⟨factor, factorization⟩ := complete (collisionObligation x)
    exact (informed_disclosure_defect (Decision := Bool)
      interface (collisionObligation x)
      sameInterface separated).2 ⟨factor, factorization⟩

/- The current-object carrier is inhabited. -/
example : Bool := false

/- A constant interface on two objects realizes the nonfaithful premise. -/
example : ¬Function.Injective (fun _ : Bool => ()) := by
  intro injective
  exact Bool.false_ne_true (injective rfl)

/- The identity interface realizes completeness for all Boolean obligations. -/
example :
    ∀ obligation : Concept Bool Bool,
      ∃ factor : Bool -> Bool, obligation = factor ∘ (id : Bool -> Bool) := by
  intro obligation
  exact ⟨obligation, rfl⟩

#print axioms nonfaithful_interface_future_incomplete

end D5.S3.ConceptDynamics.Contracts.FutureObligationIncompleteness
