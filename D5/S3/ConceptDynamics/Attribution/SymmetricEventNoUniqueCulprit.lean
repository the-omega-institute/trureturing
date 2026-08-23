/- GID: D5/S3/ConceptDynamics/Attribution/SymmetricEventNoUniqueCulprit
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Attribution/SymmetricEventNoUniqueCulprit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A fully permutation-symmetric event cannot admit an equivariant unique culprit. -/

import Mathlib.Data.Fin.Basic
import Mathlib.Logic.Equiv.Basic

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'symmetric_event_admits_no_equivariant_culprit' D5
     Golden/Frozen/accepted` returned no matches.
   * Structural repository searches for `Equiv.Perm`, equivariance, swaps, fixed points, and
     symmetry found orbit and equivariant-map results, but no common-fixed-point obstruction
     for `Fin n` together with the two requested witnesses.
   * Pinned Mathlib provides `Fin.nontrivial_iff_two_le`, `exists_ne`, `Equiv.swap`, and
     `Equiv.swap_apply_left`; the proof below reuses these basic declarations directly.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Attribution.SymmetricEventNoUniqueCulprit

/-- A culprit rule is equivariant when relabeling an event relabels the selected culprit. -/
def IsEquivariantCulprit {n : Nat} {Event : Type*}
    (act : Equiv.Perm (Fin n) -> Event -> Event) (culprit : Event -> Fin n) : Prop :=
  forall sigma event, culprit (act sigma event) = sigma (culprit event)

/-- An event is completely symmetric when every permutation of subject labels fixes it. -/
def IsCompletelySymmetric {n : Nat} {Event : Type*}
    (act : Equiv.Perm (Fin n) -> Event -> Event) (event : Event) : Prop :=
  forall sigma, act sigma event = event

/-- With at least two subjects, a completely symmetric event has no equivariant unique
culprit: the selected label would have to be fixed by every permutation. -/
theorem symmetric_event_admits_no_equivariant_culprit
    {n : Nat} (hn : 2 <= n) {Event : Type*}
    (act : Equiv.Perm (Fin n) -> Event -> Event) (culprit : Event -> Fin n) (event : Event)
    (equivariant : IsEquivariantCulprit act culprit)
    (symmetric : IsCompletelySymmetric act event) : False := by
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  obtain ⟨other, other_ne⟩ := exists_ne (culprit event)
  have selected_eq_other : culprit event = other := by
    calc
      culprit event = culprit (act (Equiv.swap (culprit event) other) event) :=
        congrArg culprit (symmetric (Equiv.swap (culprit event) other)).symm
      _ = Equiv.swap (culprit event) other (culprit event) :=
        equivariant (Equiv.swap (culprit event) other) event
      _ = other := Equiv.swap_apply_left (culprit event) other
  exact other_ne selected_eq_other.symm

/-- The action on the one-point event type is completely symmetric. -/
def trivialEventAction (n : Nat) : Equiv.Perm (Fin n) -> Unit -> Unit :=
  fun _ _ => ()

/-- A concrete completely symmetric event shows that the symmetry premise is satisfiable. -/
theorem trivial_event_is_completely_symmetric (n : Nat) :
    IsCompletelySymmetric (trivialEventAction n) () := by
  intro sigma
  rfl

/-- An anchored event carries a subject label along under each relabeling. -/
def anchoredEventAction {n : Nat} : Equiv.Perm (Fin n) -> Fin n -> Fin n :=
  fun sigma event => sigma event

/-- Once events carry a transported anchor, an equivariant single-culprit rule exists. -/
theorem anchored_event_admits_equivariant_culprit (n : Nat) :
    exists culprit : Fin n -> Fin n, IsEquivariantCulprit anchoredEventAction culprit := by
  refine ⟨id, ?_⟩
  intro sigma event
  rfl

example : IsCompletelySymmetric (trivialEventAction 2) () := by
  exact trivial_event_is_completely_symmetric 2

example : exists culprit : Fin 2 -> Fin 2,
    IsEquivariantCulprit anchoredEventAction culprit := by
  exact anchored_event_admits_equivariant_culprit 2

#print axioms symmetric_event_admits_no_equivariant_culprit

end D5.S3.ConceptDynamics.Attribution.SymmetricEventNoUniqueCulprit
