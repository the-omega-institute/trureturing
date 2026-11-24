/- GID: D5/S0/History/ResidualDiscrepancy
   generality: G
   mirror-B: D5/B/S0/History/ResidualDiscrepancy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A discrepancy is residual exactly when observed and expected readings differ. -/

module
prelude
public import OmegaMath.Algebra.Group.Basic

noncomputable section

namespace D5.S0.History.ResidualDiscrepancy

open Omega

/-- The discrepancy between an observed reading and its expected reading. -/
@[expose] public def residualDiscrepancy {A : Type u} (group : AddGroup A)
    (expected observed : A) : A :=
  group.sub observed expected

/-- A discrepancy is residual when it does not vanish. -/
@[expose] public def IsResidual {A : Type u} (group : AddGroup A)
    (expected observed : A) : Prop :=
  Not (Eq (residualDiscrepancy group expected observed) group.zero)

/-- A discrepancy is residual exactly when the observed and expected readings differ. -/
public theorem residual_iff_observed_ne_expected {A : Type u} (group : AddGroup A)
    (laws : group.Laws) (expected observed : A) :
    Iff (IsResidual group expected observed) (Not (Eq observed expected)) :=
  sub_ne_zero group laws

end D5.S0.History.ResidualDiscrepancy
