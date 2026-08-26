/- GID: D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/RetrospectiveLookupFailure
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DefinitionEscapeAdjudication/RetrospectiveLookupFailure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite table copying has zero retrospective loss but fails non-anticipation. -/

import Mathlib

open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DefinitionEscape.Adjudication

universe u

/- Library-search audit trail (2026-08-26):
   * `rg -n -i 'ObservedAnswer|PostdictiveFit|NonAnticipating|retrospective loss|
     prospective gain|table copy|lookup copy|zero loss' D5 --glob '*.lean'`
     found no declaration of the finite table-copy loss identity or the
     dependency-contamination predicate.  `LookupProgramUpperBound` is about
     description complexity and does not express either claim.
   * The same shape search in pinned Mathlib found only generic Finset sums and
     set membership primitives; no adjudication or non-anticipation theorem.
   * The proof below therefore uses only the finite sum's zero law and direct
     set membership, while the Bool/Nat example supplies a concrete non-vacuous
     lookup table and a one-unit wrong-copy loss.
-/

/-- A pointwise comparator and the observed answer at every finite record. -/
structure CopyComparison (Z Answer : Type u) where
  observedAnswer : Z → Answer
  pointwiseLoss : Answer → Answer → Nat
  selfLoss : ∀ answer, pointwiseLoss answer answer = 0

/-- The lookup copier returns the observed answer at the queried record. -/
def tableCopy {Z Answer : Type u} (comparison : CopyComparison Z Answer) :
    Z → Answer :=
  comparison.observedAnswer

/-- Total retrospective loss is the unregularized finite sum of pointwise loss. -/
def retrospectiveLoss {Z Answer : Type u} [Fintype Z] [DecidableEq Z]
    (comparison : CopyComparison Z Answer) (candidate : Z → Answer) : Nat :=
  ∑ z : Z, comparison.pointwiseLoss (candidate z) (comparison.observedAnswer z)

/-- A commitment records which records its construction depends on and which
    records were frozen before it was formed. -/
structure CopyCommitment (Z : Type u) where
  evidenceDependencies : Set Z
  frozenBefore : Z → Prop

/-- Incorporating the table copier puts every finite record in the commitment's
    dependency closure. -/
def IncorporatesTableCopy {Z : Type u} (commitment : CopyCommitment Z) : Prop :=
  (Set.univ : Set Z) ⊆ commitment.evidenceDependencies

/-- Non-anticipation requires both prior freezing and absence from the
    commitment's evidence dependency closure. -/
def NonAnticipating {Z : Type u} (commitment : CopyCommitment Z) (z : Z) : Prop :=
  commitment.frozenBefore z ∧ z ∉ commitment.evidenceDependencies

/-- A positive prospective gain is deliberately a separate future-evaluation
    quantity; retrospective fit supplies no equation relating the two. -/
def PositiveProspectiveGain {Z Answer : Type u}
    (prospectiveGain : (Z → Answer) → Nat) (candidate : Z → Answer) : Prop :=
  0 < prospectiveGain candidate

/-- A finite lookup copier has zero retrospective loss, but every copied record
is dependency-contaminated and zero retrospective loss alone does not entail a
positive prospective gain. -/
theorem lookup_copy_zero_loss_and_nonanticipating_failure
    {Z Answer : Type u} [Fintype Z] [DecidableEq Z]
    (comparison : CopyComparison Z Answer)
    (commitment : CopyCommitment Z)
    (usesCopy : IncorporatesTableCopy commitment) :
    retrospectiveLoss comparison (tableCopy comparison) = 0 ∧
      (∀ z, ¬ NonAnticipating commitment z) ∧
      ¬ (retrospectiveLoss comparison (tableCopy comparison) = 0 →
        ∀ prospectiveGain : (Z → Answer) → Nat,
          PositiveProspectiveGain prospectiveGain (tableCopy comparison)) := by
  constructor
  · classical
    simp [retrospectiveLoss, tableCopy, comparison.selfLoss]
  constructor
  · intro z hNonAnticipating
    exact hNonAnticipating.2 (usesCopy (Set.mem_univ z))
  · intro implication
    have positive := implication (by
      classical
      simp [retrospectiveLoss, tableCopy, comparison.selfLoss]) (fun _ => 0)
    simpa [PositiveProspectiveGain] using positive

/-- A concrete two-record table has zero lookup loss while a constant wrong
copy incurs exactly one unit of retrospective loss. -/
example :
    ∃ comparison : CopyComparison Bool Nat,
      ∃ wrong : Bool → Nat,
        retrospectiveLoss comparison (tableCopy comparison) = 0 ∧
          retrospectiveLoss comparison wrong = 1 := by
  let comparison : CopyComparison Bool Nat :=
    { observedAnswer := fun z => if z then 1 else 0
      pointwiseLoss := fun predicted observed => if predicted = observed then 0 else 1
      selfLoss := by intro answer; simp }
  let wrong : Bool → Nat := fun _ => 0
  refine ⟨comparison, wrong, ?_, ?_⟩
  · simp [retrospectiveLoss, tableCopy, comparison]
  · simp [retrospectiveLoss, comparison, wrong]

/-- A concrete commitment containing the full table makes both records fail the
non-anticipation predicate, including when it was frozen beforehand. -/
example :
    ∃ commitment : CopyCommitment Bool,
      IncorporatesTableCopy commitment ∧
        (∀ z, ¬ NonAnticipating commitment z) := by
  let commitment : CopyCommitment Bool :=
    { evidenceDependencies := Set.univ
      frozenBefore := fun _ => True }
  refine ⟨commitment, Set.Subset.rfl, ?_⟩
  intro z hNonAnticipating
  exact hNonAnticipating.2 (Set.mem_univ z)

#print axioms lookup_copy_zero_loss_and_nonanticipating_failure

end D5.S3.ConceptDynamics.DefinitionEscape.Adjudication
