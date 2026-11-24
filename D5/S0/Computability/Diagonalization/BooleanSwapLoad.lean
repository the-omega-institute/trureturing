/- GID: D5/S0/Computability/Diagonalization/BooleanSwapLoad
   generality: G
   mirror-B: D5/B/S0/Computability/Diagonalization/BooleanSwapLoad
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Boolean negation is exactly the operation that carries universal self-diagonal escape. -/

module
prelude
public import OmegaInit.Core

namespace D5.S0.Computability.Diagonalization.BooleanSwapLoad

open Omega

/-- An operation disagrees with every Boolean self-diagonal value exactly when it agrees
pointwise with Boolean negation. The identity operation fails on a constant diagonal. -/
public theorem boolean_swap_carries_diagonal_escape (sigma : Bool → Bool) :
    let swap := Bool.rec (motive := fun _ => Bool) .true .false
    And
      (Iff
        (∀ (History : Type) (V : History → History → Bool) (h : History),
          Not (Eq (sigma (V h h)) (V h h)))
        (∀ b, Eq (sigma b) (swap b)))
      (Not (∀ (History : Type) (V : History → History → Bool) (h : History),
        Not (Eq ((fun b : Bool => b) (V h h)) (V h h)))) :=
  let swap := Bool.rec (motive := fun _ => Bool) .true .false
  have falseNeTrue : Not (Eq Bool.false Bool.true) :=
    fun h => Eq.subst (Bool.rec (motive := fun _ => Prop) True False) h True.intro
  have swapNeSelf : ∀ b, Not (Eq (swap b) b) :=
    Bool.rec (fun h => falseNeTrue h.symm) falseNeTrue
  And.intro
    (Iff.intro
      (fun escape b =>
        have changes : Not (Eq (sigma b) b) := escape Bool (fun _ _ => b) .false
        Bool.rec
          (motive := fun value => Not (Eq (sigma value) value) → Eq (sigma value) (swap value))
          (Bool.rec (motive := fun value => Not (Eq value Bool.false) → Eq value Bool.true)
            (fun h => False.elim (h Eq.refl)) (fun _ => Eq.refl) (sigma .false))
          (Bool.rec (motive := fun value => Not (Eq value Bool.true) → Eq value Bool.false)
            (fun _ => Eq.refl) (fun h => False.elim (h Eq.refl)) (sigma .true))
          b changes)
      (fun agrees _ V h same => swapNeSelf (V h h) ((agrees (V h h)).symm.trans same)))
    (fun identityEscapes => identityEscapes Bool (fun _ _ => .false) .false Eq.refl)

/-- The minimal binary carrier is inhabited. -/
example : Bool := .false

/-- Boolean negation satisfies the universal diagonal premise. -/
example :
    let swap := Bool.rec (motive := fun _ => Bool) .true .false
    ∀ (History : Type) (V : History → History → Bool) (h : History),
      Not (Eq (swap (V h h)) (V h h)) :=
  (boolean_swap_carries_diagonal_escape
    (Bool.rec (motive := fun _ => Bool) .true .false)).left.mpr (fun _ => Eq.refl)

end D5.S0.Computability.Diagonalization.BooleanSwapLoad
