/- GID: D5/S0/Computability/GuardedWall
   generality: G
   mirror-B: D5/B/S0/Computability/GuardedWall
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Guarded statements never enter a forbidden positive configuration. -/

import Mathlib.Data.Set.Basic

namespace D5.S0.Computability.GuardedWall

universe u v

/-- If every gatekeeper remains positive, a wall statement cannot become positive
when their joint positive configuration is forbidden and forbidden configurations
never occur. -/
theorem wall_never_positive
    {Time : Type u} {Statement : Type v}
    (positive : Time -> Statement -> Prop)
    (wall gatekeepers : Set Statement)
    (forbidden : Time -> Statement -> Prop)
    (gatekeepers_positive : forall t g, g ∈ gatekeepers -> positive t g)
    (joint_positive_forbidden : forall t w,
      w ∈ wall -> positive t w ->
        (forall g, g ∈ gatekeepers -> positive t g) -> forbidden t w)
    (consistent : forall t w, w ∈ wall -> Not (forbidden t w)) :
    forall t w, w ∈ wall -> Not (positive t w) := by
  intro t w hw hpositive
  exact (consistent t w hw)
    (joint_positive_forbidden t w hw hpositive (gatekeepers_positive t))

/-- A one-step Boolean ledger witnesses that the hypotheses and wall membership
of `wall_never_positive` are simultaneously inhabited. -/
theorem boolean_guarded_wall_witness :
    let positive : Unit -> Bool -> Prop := fun _ statement => statement = true
    let wall : Set Bool := fun statement => statement = false
    let gatekeepers : Set Bool := fun statement => statement = true
    let forbidden : Unit -> Bool -> Prop := fun _ statement => statement = false ∧ statement = true
    (forall t g, g ∈ gatekeepers -> positive t g) ∧
      (forall t w, w ∈ wall -> positive t w ->
        (forall g, g ∈ gatekeepers -> positive t g) -> forbidden t w) ∧
      (forall t w, w ∈ wall -> Not (forbidden t w)) ∧
      false ∈ wall ∧ Not (positive () false) := by
  dsimp
  constructor
  · intro _ g hg
    exact hg
  constructor
  · intro _ w hw hpositive _
    exact ⟨hw, hpositive⟩
  constructor
  · intro _ w _ hforbidden
    exact Bool.noConfusion (hforbidden.1.symm.trans hforbidden.2)
  exact ⟨rfl, Bool.false_ne_true⟩

end D5.S0.Computability.GuardedWall
