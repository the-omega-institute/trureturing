/- GID: D5/S0/Conventions/SingleEyeInvariant
   generality: G
   mirror-B: D5/B/S0/Conventions/SingleEyeInvariant
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Single-eyed observers admit invariants depending only on one coordinate. -/

module
prelude
public import OmegaInit.Prelude

namespace D5.S0.Conventions.SingleEyeInvariant

open Omega

universe u v

/-- An observer admits only invariants whose dependency sets lie in one coordinate. -/
@[expose] public def IsSingleEyed {Coordinate : Type u} {Invariant : Type v}
    (coordinate : Coordinate)
    (admitted : Invariant → Prop)
    (dependency : Invariant → Coordinate → Prop) : Prop :=
  ∀ invariant, admitted invariant → ∀ input, dependency invariant input → Eq input coordinate

/-- A singleton family is single-eyed at its sole coordinate. -/
example : IsSingleEyed Nat.zero (fun value : Bool => Eq value .false)
    (fun _ input => Eq input Nat.zero) :=
  fun _ _ _ h => h

/-- An admitted invariant depending on two coordinates is not single-eyed at zero. -/
example : Not (IsSingleEyed Nat.zero (fun value : Bool => Eq value .false)
    (fun _ input => Or (Eq input Nat.zero) (Eq input Nat.one))) :=
  fun h =>
    have one_eq_zero := h .false Eq.refl Nat.one (Or.inr Eq.refl)
    Eq.subst (Nat.rec (motive := fun _ => Prop) False (fun _ _ => True))
      one_eq_zero True.intro

end D5.S0.Conventions.SingleEyeInvariant
