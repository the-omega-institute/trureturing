/- GID: D5/S3/ConceptDynamics/InformationEscape/Arena
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/Arena
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite arenas expose a decidable nondegeneracy boundary and distinct-state witnesses. -/

import Mathlib.Data.Fintype.EquivFin

/- Library-search audit trail (2026-09-04):
   * Repository searches for `Arena`, `Nondegenerate`, and finite-state
     distinctness found no existing information-escape arena owner under `D5`.
   * Pinned Mathlib exact hits `Fintype.exists_pair_of_one_lt_card` and
     `Fintype.one_lt_card_iff_nontrivial` connect finite cardinality with a
     distinct pair. The former is applied directly below.
   * No existing declaration combines stored `Fintype` and `DecidableEq`
     structures with the seal's separately decidable cardinality boundary. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InformationEscape

universe u

/-- A finite state space with computational equality. -/
structure Arena where
  State : Type u
  stateFintype : Fintype State
  stateDecidableEq : DecidableEq State

namespace Arena

/-- The number of states in an arena. -/
def card (arena : Arena) : Nat := by
  letI := arena.stateFintype
  exact Fintype.card arena.State

/-- The seal-level requirement that an arena contain at least two states. -/
def Nondegenerate (arena : Arena) : Prop :=
  2 <= arena.card

instance instDecidableNondegenerate (arena : Arena) : Decidable arena.Nondegenerate := by
  unfold Nondegenerate card
  letI := arena.stateFintype
  infer_instance

/-- A nondegenerate finite arena contains a pair of distinct states. -/
theorem exists_ne_of_nondegenerate (arena : Arena) (nondegenerate : arena.Nondegenerate) :
    exists x y : arena.State, x ≠ y := by
  letI := arena.stateFintype
  apply Fintype.exists_pair_of_one_lt_card
  exact nondegenerate

/-- Package an existing finite decidable type as an arena. -/
def ofFintype (X : Type u) [Fintype X] [DecidableEq X] : Arena where
  State := X
  stateFintype := inferInstance
  stateDecidableEq := inferInstance

end Arena

end D5.S3.ConceptDynamics.InformationEscape
