/- GID: D5/S3/Observer/Naturality/ObserverWorldCovariance
   generality: G
   mirror-B: D5/B/S3/Observer/Naturality/ObserverWorldCovariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Covariant observers on transitive axes have equivalent output worlds. -/

import Mathlib.Algebra.Group.Action.Pretransitive
import Mathlib.Data.Set.Function
import Mathlib.Logic.Equiv.Basic

/- Library-search audit trail (2026-08-29):
   * Repository name and body-shape searches found no theorem restricting an
     output equivalence to the ranges of a covariant observer family.
   * Pinned Mathlib exact component hits `MulAction.exists_smul_eq` and
     `Equiv.subtypeEquiv` supply the transitive axis witness and the actual
     equivalence between range subtypes; no packaged observer-world theorem
     was found. -/

namespace D5.S3.Observer.Naturality.ObserverWorldCovariance

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- If observers transform through output equivalences and the group acts
transitively on axes, their output ranges are equivalent. The public
computation rule identifies that equivalence with the selected transition map
on every observed state. -/
theorem observer_world_covariance
    {G Axis State Output : Type*} [Group G]
    [MulAction G Axis] [MulAction G State]
    [MulAction.IsPretransitive G Axis]
    (observer : Axis -> State -> Output)
    (transport : G -> Output ≃ Output)
    (covariant : forall (g : G) (axis : Axis) (state : State),
      observer (g • axis) (g • state) = transport g (observer axis state))
    (a b : Axis) :
    exists g : G, exists worldEquiv :
        Set.range (observer a) ≃ Set.range (observer b),
      g • a = b /\
        forall state : State,
          (worldEquiv ⟨observer a state, ⟨state, rfl⟩⟩ : Output) =
            transport g (observer a state) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G a b
  have hrange : forall output : Output,
      output ∈ Set.range (observer a) <->
        transport g output ∈ Set.range (observer b) := by
    intro output
    constructor
    · rintro ⟨state, rfl⟩
      refine ⟨g • state, ?_⟩
      simpa only [hg] using covariant g a state
    · rintro ⟨state, hstate⟩
      refine ⟨g⁻¹ • state, ?_⟩
      apply (transport g).injective
      calc
        transport g (observer a (g⁻¹ • state)) =
            observer b state := by
          simpa only [hg, smul_inv_smul] using
            (covariant g a (g⁻¹ • state)).symm
        _ = transport g output := hstate
  let worldEquiv : Set.range (observer a) ≃ Set.range (observer b) :=
    (transport g).subtypeEquiv hrange
  refine ⟨g, worldEquiv, hg, ?_⟩
  intro state
  rfl

#print axioms observer_world_covariance

end D5.S3.Observer.Naturality.ObserverWorldCovariance
