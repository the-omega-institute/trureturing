/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude

public import OmegaInit.Core

/-!
Omega original.

Order comparison with diagonal upper bounds gives a functional-calculus
inequality in a corner. The second diagonal component may depend on the
perturbation and needs no uniform bound or limiting value.
-/

noncomputable section
@[expose] public section
namespace Omega.CornerCompression

/-- Monotonicity on a doubled carrier controls its calculus in a corner.
The premises are positivity, diagonal calculus, diagonal domination, and
closedness of order along the prescribed first-corner perturbations. -/
theorem corner_calculus_le {A : Type u} {B : Type v} {S : Type w} {F : Type x}
    (le : A → A → Prop) (leDouble : B → B → Prop)
    (positive : A → Prop) (positiveDouble : B → Prop)
    (small : S → Prop) (continuous : F → Prop)
    (apply : F → A → A) (applyDouble : F → B → B)
    (corner : B → A) (shift : A → S → A) (diagonal : A → A → B)
    (corner_mono : ∀ {X Y}, leDouble X Y → le (corner X) (corner Y))
    (corner_positive : ∀ {X}, positiveDouble X → positive (corner X))
    (diagonal_calculus : ∀ f, continuous f → ∀ a b,
      positive a → positive b → Eq (corner (applyDouble f (diagonal a b))) (apply f a))
    (sandwich : ∀ X, positiveDouble X → ∀ ε, small ε →
      Exists (fun b => And (positive (shift (corner X) ε))
        (And (positive b) (And (positiveDouble (diagonal (shift (corner X) ε) b))
          (leDouble X (diagonal (shift (corner X) ε) b))))))
    (limit_closed : ∀ f, continuous f → ∀ a, positive a → ∀ z,
      (∀ ε, small ε → le z (apply f (shift a ε))) → le z (apply f a))
    (f : F) (hf : continuous f)
    (monotone : ∀ X Y, positiveDouble X → positiveDouble Y →
      leDouble X Y → leDouble (applyDouble f X) (applyDouble f Y))
    (X : B) (hX : positiveDouble X) : le (corner (applyDouble f X)) (apply f (corner X)) :=
  limit_closed f hf (corner X) (corner_positive hX) (corner (applyDouble f X))
    (fun ε hε => Exists.elim (sandwich X hX ε hε)
      (fun b properties =>
        Eq.subst (motive := fun y => le (corner (applyDouble f X)) y)
          (diagonal_calculus f hf (shift (corner X) ε) b
            properties.left properties.right.left)
          (corner_mono (monotone X (diagonal (shift (corner X) ε) b)
            hX properties.right.right.left properties.right.right.right))))
end Omega.CornerCompression
