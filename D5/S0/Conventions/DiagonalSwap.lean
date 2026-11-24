/- GID: D5/S0/Conventions/DiagonalSwap
   generality: G
   mirror-B: D5/B/S0/Conventions/DiagonalSwap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Boolean swap changes every value selected along a self-application diagonal. -/

module
prelude
public import OmegaInit.Core

namespace D5.S0.Conventions.DiagonalSwap

open Omega

/-- Applying the Boolean swap to a value selected on the self-application
diagonal changes that value. -/
public theorem swap_changes_self_diagonal {Index : Type u} (assignment : Index → Index → Bool) :
    ∀ index, Not (Eq (Bool.rec .true .false (assignment index index)) (assignment index index)) :=
  fun index =>
    have distinct : Not (Eq Bool.false Bool.true) :=
      fun h => Eq.subst (Bool.rec True False) h True.intro
    Bool.rec (motive := fun b => Not (Eq (Bool.rec .true .false b) b))
      (fun h => distinct h.symm) distinct (assignment index index)

/-- A concrete inhabited index domain for the diagonal statement. -/
example : Exists (fun _ : Bool => True) := Exists.intro .false True.intro

/-- Boolean-valued binary assignments exist on an inhabited index domain. -/
example : Exists (fun _ : Bool → Bool → Bool => True) :=
  Exists.intro (fun _ _ => .false) True.intro

end D5.S0.Conventions.DiagonalSwap
