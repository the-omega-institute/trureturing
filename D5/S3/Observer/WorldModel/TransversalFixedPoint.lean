/- GID: D5/S3/Observer/WorldModel/TransversalFixedPoint
   generality: G
   mirror-B: D5/B/S3/Observer/WorldModel/TransversalFixedPoint
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A coherent family of states across semiconjugate world models forms a
     transversal fixed point whenever one anchor state is fixed. -/

import D5.S3.Observer.Bridges.FixedPointSemiconjugacy

/-!
A world-model diagram in this module is intentionally weaker than a category:
it contains typed state spaces, one self-map per model, and pairwise observer
bridges that semiconjugate the dynamics.  Identity and composition laws for the
bridges are not assumed.  A coherent section is therefore an explicit datum.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.WorldModel.TransversalFixedPoint

universe u v

open D5.S3.Observer.Bridges.FixedPointSemiconjugacy

/-- A typed family of world models connected by dynamics-preserving observer
bridges. -/
structure WorldModelDiagram (Index : Type u) where
  State : Index → Type v
  step : ∀ i, State i → State i
  bridge : ∀ i j, State i → State j
  bridge_semiconj : ∀ i j, Function.Semiconj (bridge i j) (step i) (step j)

namespace WorldModelDiagram

variable {Index : Type u} (model : WorldModelDiagram Index)

/-- A choice of one state in every world model. -/
abbrev Section := ∀ i, model.State i

/-- Every bridge sends the selected state in its source model to the selected
state in its target model. -/
def IsCoherentSection (state : model.Section) : Prop :=
  ∀ i j, model.bridge i j (state i) = state j

/-- Every selected state is fixed by its local model dynamics. -/
def IsFixedSection (state : model.Section) : Prop :=
  ∀ i, Function.IsFixedPt (model.step i) (state i)

/-- Transport one anchor state through all outgoing bridges. -/
def transportFrom (anchor : Index) (state : model.State anchor) : model.Section :=
  fun target => model.bridge anchor target state

/-- A fixed anchor transports to a fixed state in every target world model. -/
theorem transport_from_fixed_is_fixed
    {anchor : Index} {state : model.State anchor}
    (hFixed : Function.IsFixedPt (model.step anchor) state) :
    model.IsFixedSection (model.transportFrom anchor state) := by
  intro target
  exact fixed_point_maps (model.bridge_semiconj anchor target) hFixed

/-- A coherent section that is fixed at one anchor is fixed in every model. -/
theorem coherent_section_fixed_from_anchor
    {state : model.Section} {anchor : Index}
    (hCoherent : model.IsCoherentSection state)
    (hFixed : Function.IsFixedPt (model.step anchor) (state anchor)) :
    model.IsFixedSection state := by
  intro target
  have hTransported :
      Function.IsFixedPt (model.step target)
        (model.bridge anchor target (state anchor)) :=
    fixed_point_maps (model.bridge_semiconj anchor target) hFixed
  simpa [hCoherent anchor target] using hTransported

/-- For a coherent section, fixedness at any two anchors is equivalent when the
bridge in one direction is injective. -/
theorem fixed_at_anchor_iff_fixed_at_target_of_injective
    {state : model.Section} {anchor target : Index}
    (hCoherent : model.IsCoherentSection state)
    (hInjective : Function.Injective (model.bridge anchor target)) :
    Function.IsFixedPt (model.step anchor) (state anchor) ↔
      Function.IsFixedPt (model.step target) (state target) := by
  rw [← hCoherent anchor target]
  exact fixed_point_iff_of_injective
    (model.bridge_semiconj anchor target) hInjective

/-- The transported section is fixed even when the outgoing bridges do not form
a coherent categorical family among themselves. -/
example {anchor : Index} {state : model.State anchor}
    (hFixed : Function.IsFixedPt (model.step anchor) state) :
    ∀ target,
      Function.IsFixedPt (model.step target)
        (model.bridge anchor target state) := by
  exact model.transport_from_fixed_is_fixed hFixed

#print axioms transport_from_fixed_is_fixed
#print axioms coherent_section_fixed_from_anchor
#print axioms fixed_at_anchor_iff_fixed_at_target_of_injective

end WorldModelDiagram

end D5.S3.Observer.WorldModel.TransversalFixedPoint
