/- GID: D5/S3/ConceptDynamics/Aggregation/AgendaPower
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Aggregation/AgendaPower
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every candidate in the fixed majority cycle wins under a suitable agenda. -/

import D5.S3.ConceptDynamics.Aggregation.MajorityCycleNotScalarOrder
import Mathlib.Tactic.FinCases

/- Library-search audit trail (2026-08-23):
   * Repository searches for agenda, pairwise elimination, sequential elimination, and
     majority-cycle procedures found no agenda evaluator or agenda-power theorem.
   * Exact repository hits `preferenceRank`, `prefers`, `majorityPrefers`, and
     `condorcet_cycle_vote_counts` in `MajorityCycleNotScalarOrder` provide the fixed
     preference profile and majority rule imported here without redeclaration.
   * Pinned-Mathlib searches for agenda power and sequential majority elimination were
     misses; the finite proof below is computation over the canonical profile. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Aggregation.AgendaPower

open D5.S3.ConceptDynamics.Aggregation.MajorityCycleNotScalarOrder

/-- A sequential agenda names the first comparison and the remaining finalist. -/
structure Agenda where
  first : Fin 3
  second : Fin 3
  final : Fin 3
  deriving DecidableEq

/-- A valid three-candidate agenda uses each candidate exactly once. -/
def ValidAgenda (agenda : Agenda) : Prop :=
  agenda.first ≠ agenda.second ∧
    agenda.first ≠ agenda.final ∧
      agenda.second ≠ agenda.final

/-- A pairwise contest returns its relation-preferred entrant, with the second entrant
as the fallback when the first does not defeat it. -/
def pairwiseWinner {Candidate : Type*} (relation : Candidate → Candidate → Prop)
    [DecidableRel relation] (first second : Candidate) : Candidate :=
  if relation first second then first else second

/-- Sequential pairwise elimination compares the first two entrants, then compares
their winner with the remaining finalist. -/
def sequentialWinner (relation : Fin 3 → Fin 3 → Prop)
    [DecidableRel relation] (agenda : Agenda) : Fin 3 :=
  pairwiseWinner relation
    (pairwiseWinner relation agenda.first agenda.second)
    agenda.final

/-- With the canonical preferences and majority rule fixed, every candidate can be made
the winner by a valid comparison order; two such orders have different outcomes. -/
theorem agenda_power :
    (∀ desired : Fin 3, ∃ agenda : Agenda,
      ValidAgenda agenda ∧ sequentialWinner majorityPrefers agenda = desired) ∧
    ∃ agenda agenda' : Agenda,
      ValidAgenda agenda ∧ ValidAgenda agenda' ∧ agenda ≠ agenda' ∧
        sequentialWinner majorityPrefers agenda ≠
          sequentialWinner majorityPrefers agenda' := by
  constructor
  · intro desired
    fin_cases desired
    · exact ⟨⟨1, 2, 0⟩, by simp [ValidAgenda], by decide⟩
    · exact ⟨⟨2, 0, 1⟩, by simp [ValidAgenda], by decide⟩
    · exact ⟨⟨0, 1, 2⟩, by simp [ValidAgenda], by decide⟩
  · exact ⟨⟨0, 1, 2⟩, ⟨1, 2, 0⟩,
      by simp [ValidAgenda], by simp [ValidAgenda], by decide, by decide⟩

/-- The three comparison orders from the source produce candidates 2, 0, and 1. -/
example :
    sequentialWinner majorityPrefers ⟨0, 1, 2⟩ = 2 ∧
      sequentialWinner majorityPrefers ⟨1, 2, 0⟩ = 0 ∧
        sequentialWinner majorityPrefers ⟨2, 0, 1⟩ = 1 := by
  decide

#print axioms agenda_power

end D5.S3.ConceptDynamics.Aggregation.AgendaPower
