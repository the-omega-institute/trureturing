/- GID: D5/S3/Observer/Budget/ResponseCompletenessCardinality
   generality: G
   mirror-B: D5/B/S3/Observer/Budget/ResponseCompletenessCardinality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Response completeness forces enough protocol response classes for every table. -/

import D5.S3.Observer.Completion.DoubleExtensionalQuotientUniversality
import Mathlib.SetTheory.Cardinal.Finite

/- Library-search audit trail (2026-08-28):
   * No exact D5 theorem states the response-completeness lower bound on the
     protocol-column kernel quotient.
   * `FiniteInternalProtocolNoGo` proves only the later impossibility corollary
     under the additional internal-cardinality bound.
   * The canonical D5 primitive `protocolBehavior` is imported for evaluation
     columns rather than redeclared by body shape.
   * Exact pinned-Mathlib hits `Setoid.quotientKerEquivRange` and `Nat.card_fun`
     identify the quotient with the realized response tables and count all tables. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Budget.ResponseCompletenessCardinality

open D5.S3.Observer.Completion.DoubleExtensionalQuotientUniversality

universe u

/-- A response-complete finite evaluation realizes every state-indexed response
table. Hence distinct tables occupy distinct equivalence classes of protocols
under equality of their complete response columns. -/
theorem response_complete_card_lower_bound
    {X P Lambda : Type u}
    [Fintype X] [Fintype Lambda]
    (evaluation : X -> P -> Lambda)
    (responseComplete : forall table : X -> Lambda,
      exists protocol : P, forall state : X,
        evaluation state protocol = table state) :
    Fintype.card Lambda ^ Fintype.card X <=
      Nat.card
        (Quotient (Setoid.ker (protocolBehavior evaluation))) := by
  classical
  have behaviorSurjective :
      Function.Surjective (protocolBehavior evaluation) := by
    intro table
    obtain ⟨protocol, hprotocol⟩ := responseComplete table
    exact ⟨protocol, funext hprotocol⟩
  have rangeIsUniversal :
      Set.range (protocolBehavior evaluation) = Set.univ :=
    Set.range_eq_univ.mpr behaviorSurjective
  have quotientCardEqRange :
      Nat.card (Quotient (Setoid.ker (protocolBehavior evaluation))) =
        Nat.card (Set.range (protocolBehavior evaluation)) :=
    Nat.card_congr
      (Setoid.quotientKerEquivRange (protocolBehavior evaluation))
  have rangeCardEqTables :
      Nat.card (Set.range (protocolBehavior evaluation)) =
        Nat.card (X -> Lambda) := by
    rw [rangeIsUniversal]
    exact Nat.card_congr (Equiv.Set.univ (X -> Lambda))
  calc
    Fintype.card Lambda ^ Fintype.card X = Nat.card (X -> Lambda) := by
      simpa only [Nat.card_eq_fintype_card] using
        (Nat.card_fun : Nat.card (X -> Lambda) =
          Nat.card Lambda ^ Nat.card X).symm
    _ = Nat.card (Set.range (protocolBehavior evaluation)) :=
      rangeCardEqTables.symm
    _ <= Nat.card
        (Quotient (Setoid.ker (protocolBehavior evaluation))) :=
      le_of_eq quotientCardEqRange.symm

#print axioms response_complete_card_lower_bound

end D5.S3.Observer.Budget.ResponseCompletenessCardinality
